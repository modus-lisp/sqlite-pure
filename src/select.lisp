;;;; select.lisp — the query engine.
;;;;
;;;; A SELECT compiles to (lambda (parent-env) rows) where each row is a
;;;; list of values.  Joins are nested loops over LEVELs; each level's
;;;; access path is a full scan, a rowid lookup/range, or an index prefix
;;;; seek, chosen from the WHERE/ON conjuncts.  Every conjunct is still
;;;; evaluated as a filter, so an access path can only ever narrow the
;;;; candidate rows, never change the answer.

(in-package #:sqlite-pure)

(defvar *ctes* '() "alist name -> CTE for the statement being compiled.")

(defstruct cte name columns sel (rows nil) (done nil) recursive-rows affinities env)

;;; ------------------------------------------------------------------
;;; Rows of stored tables

(defun column-default-value (col)
  (let ((d (column-default col)))
    (if d
        (apply-affinity (funcall (compile-expr d (make-scope)) nil) (column-affinity col))
        :null)))

(defun table-record-to-row (table rowid vals)
  "Vector of the table's column values in declaration order + rowid."
  (let* ((cols (table-columns table))
         (n (length cols))
         (row (make-array (1+ n))))
    (if (table-without-rowid table)
        (let* ((pk (table-pk table))
               (rest (loop for i below n unless (member i pk) collect i))
               (order (append pk rest)))
          (loop for ci in order
                do (setf (svref row ci)
                         (if vals (pop vals) (column-default-value (aref cols ci)))))
          (setf (svref row n) :null))
        (progn
          (dotimes (i n)
            (let ((v (if vals (pop vals) (column-default-value (aref cols i)))))
              (setf (svref row i)
                    (cond ((eql i (table-rowid-alias table)) rowid)
                          ((and (integerp v) (eq (column-affinity (aref cols i)) :real))
                           (safe-double v))
                          (t v)))))
          (setf (svref row n) rowid)))
    row))

(defun fetch-row (table rowid &optional wanted)
  (let ((payload (table-lookup (table-owner table) (table-root table) rowid)))
    (when payload
      (table-record-to-row table rowid (decode-record payload 0 (length payload) nil wanted)))))

(defun map-table-rows (table fn &key start wanted)
  "Call FN on every row of TABLE.  WANTED (a bit vector) limits which
columns are decoded; the others read as NULL."
  (if (table-without-rowid table)
      (map-index (table-owner table) (table-root table)
                 (lambda (vals) (funcall fn (table-record-to-row table nil vals))))
      (map-table (table-owner table) (table-root table)
                 (lambda (rowid payload)
                   (funcall fn (table-record-to-row
                                table rowid (decode-record payload 0 (length payload) nil wanted))))
                 :start start)))

;;; ------------------------------------------------------------------
;;; Index keys

(defun index-key-cmp (collations descs)
  "Comparator of an index entry against a (possibly shorter) probe."
  (lambda (entry probe)
    (loop for p in probe
          for e in entry
          for i from 0
          for coll = (or (nth i collations) :binary)
          for c = (compare-values e p coll)
          do (unless (zerop c) (return (if (nth i descs) (- c) c)))
          finally (return 0))))

(defun index-collations (index) (mapcar #'second (index-columns index)))
(defun index-descs (index) (mapcar #'third (index-columns index)))

;;; ------------------------------------------------------------------
;;; FROM sources

(defstruct fsrc
  src table
  rows-fn         ; for derived sources: (lambda (env)) -> list of row vectors
  tvf             ; table-valued function: (builder . arg-asts), args compiled late
  join            ; :first :inner :left :cross :comma
  on using natural)

(defun make-table-src (table &optional alias)
  (let ((cols (table-columns table)))
    (make-src :name (or alias (table-name table))
              :columns (map 'vector #'column-name cols)
              :affinities (map 'vector #'column-affinity cols)
              :collations (map 'vector #'column-collation cols)
              :table table
              :rowid-p (not (table-without-rowid table))
              :used (make-array (length cols) :element-type 'bit :initial-element 0))))

(defun rows-to-vectors (rows)
  (mapcar (lambda (r) (let ((v (make-array (1+ (length r)))))
                        (replace v r)
                        (setf (svref v (length r)) :null)
                        v))
          rows))

(defun derived-src (name columns affinities collations)
  (make-src :name name :columns (coerce columns 'vector)
            :affinities (coerce affinities 'vector)
            :collations (coerce collations 'vector)
            :rowid-p nil))

(defun select-derived-source (sel alias scope &optional rename)
  (multiple-value-bind (fn cols correlated) (compile-select sel scope)
    (let* ((names (if rename
                      (progn (unless (= (length rename) (length cols))
                               (sql-error "expected ~d columns for ~a but got ~d"
                                          (length rename) alias (length cols)))
                             rename)
                      (mapcar #'first cols)))
           (src (derived-src alias names (mapcar #'second cols) (mapcar #'third cols)))
           (cache nil))
      (make-fsrc :src src
                 :rows-fn (lambda (env)
                            (if cache
                                (cdr cache)
                                (let ((rows (rows-to-vectors (funcall fn env))))
                                  (unless correlated (setf cache (cons t rows)))
                                  rows)))))))

(defun cte-source (cte alias)
  (let* ((src (derived-src (or alias (cte-name cte)) (cte-columns cte)
                           (or (cte-affinities cte) (make-list (length (cte-columns cte))))
                           (make-list (length (cte-columns cte)) :initial-element :binary))))
    (make-fsrc :src src
               :rows-fn (lambda (env)
                          (declare (ignore env))
                          (if (eq (cte-done cte) :working)
                              (cte-recursive-rows cte)
                              (progn (unless (cte-done cte) (materialize-cte cte))
                                     (cte-rows cte)))))))

(defun make-fsrc-for (item scope)
  (destructuring-bind (&key source join on using natural) item
    (let ((fs
            (ecase (car source)
              (:table
               (destructuring-bind (name alias &optional schema) (cdr source)
                 (let ((cte (and (null (fourth source)) (cdr (assoc name *ctes* :test #'name=)))))
                   (cond
                     (cte (cte-source cte alias))
                     (t (let ((table (lookup-table *db* name t schema)))
                          (if (table-view-select table)
                              (let ((*ctes* '()))
                                (select-derived-source (table-view-select table) (or alias name)
                                                       (make-scope)
                                                       (table-view-columns table)))
                              (make-fsrc :src (make-table-src table alias) :table table))))))))
              (:subquery
               (select-derived-source (second source) (third source) scope))
              (:join-group
               (select-derived-source
                (make-sel :cores (list (make-select-core :cols (list (list :star nil))
                                                         :from (second source))))
                (third source) scope))
              (:tvf
               (destructuring-bind (name args alias) (cdr source)
                 (unless (or (name= name "json_each") (name= name "json_tree"))
                   (sql-error "no such table-valued function: ~a" name))
                 (let ((fs (json-table-source name nil alias)))
                   (setf (fsrc-tvf fs)
                         (cons (lambda (fns) (fsrc-rows-fn (json-table-source name fns alias))) args))
                   fs))))))
      (setf (fsrc-join fs) join (fsrc-on fs) on (fsrc-using fs) using (fsrc-natural fs) natural)
      fs)))

;;; ------------------------------------------------------------------
;;; Conjuncts and their source references

(defun split-conjuncts (e)
  (cond ((null e) '())
        ((and (eq (car e) :binary) (eq (second e) :and))
         (append (split-conjuncts (third e)) (split-conjuncts (fourth e))))
        (t (list e))))

(defun expr-refs (e scope)
  "Source indexes (depth 0) referenced by E, or :ALL if E contains a
subquery (whose references we do not chase)."
  (let ((refs '()))
    (labels ((walk (x)
               (when (consp x)
                 (case (car x)
                   (:col (multiple-value-bind (depth si) (resolve-column scope (second x) (third x))
                           (cond ((and depth (= depth 0)) (pushnew si refs))
                                 ((and (null depth) (null (second x))
                                       (alias-expr scope (third x)))
                                  (walk (alias-expr scope (third x)))))))
                   (:srccol (pushnew (second x) refs))
                   ((:subquery :exists) (return-from expr-refs :all))
                   (:in (walk (second x))
                    (if (eq (car (third x)) :list)
                        (mapc #'walk (second (third x)))
                        (return-from expr-refs :all)))
                   (:fn (mapc #'walk (third x)) (walk (sixth x)))
                   (:case (walk (second x))
                    (loop for (w th) in (third x) do (walk w) (walk th))
                    (walk (fourth x)))
                   (:lit nil)
                   (t (mapc #'walk (cdr x)))))))
      (walk e))
    refs))

(defun max-ref (refs nlevels)
  (cond ((eq refs :all) (1- nlevels))
        ((null refs) 0)
        (t (reduce #'max refs))))

;;; ------------------------------------------------------------------
;;; Access paths

(defstruct level
  index            ; position in the source list
  fsrc
  iterate          ; (lambda (env fn)) calls fn with each candidate row
  match            ; list of compiled ON conjuncts (LEFT JOIN)
  filters          ; list of compiled conjuncts
  left-p
  nullrow)

(defun rowid-probe (v)
  "Normalise a value compared with a rowid: an integer, or NIL for 'no
row can match'."
  (let ((n (apply-comparison-affinity v :numeric)))
    (cond ((integerp n) n)
          ((and (floatp n) (not (float-infinity-p n)) (= n (ftruncate n))
                (i64-p (truncate n)))
           (truncate n))
          (t nil))))

(defun probe-usable-p (col-aff other-aff)
  "Can an index on a column with COL-AFF be seeked with an equality
against an expression of OTHER-AFF without the comparison converting
the column side?"
  (case col-aff
    ((:integer :real :numeric) t)
    (:text (member other-aff '(nil :text :blob)))
    (t (member other-aff '(nil :blob)))))

(defun convert-probe (v col-aff other-aff)
  (let ((aff (comparison-affinity col-aff other-aff)))
    (apply-comparison-affinity v aff)))

(defun equality-candidates (conjuncts li scope)
  "From CONJUNCTS find (col-index other-expr) pairs of the form
source[LI].col = expr where expr references only earlier sources."
  (let ((out '()))
    (dolist (c conjuncts (nreverse out))
      (when (and (eq (car c) :binary) (member (second c) '(:eq :is)))
        (dolist (pair (list (list (third c) (fourth c)) (list (fourth c) (third c))))
          (destructuring-bind (a b) pair
            (let ((a* (if (eq (car a) :collate) (second a) a)))
              (multiple-value-bind (depth si ci)
                  (case (car a*)
                    (:col (resolve-column scope (second a*) (third a*)))
                    (:srccol (values 0 (second a*) (third a*))))
                (when (and depth (= depth 0) (= si li))
                  (let ((refs (expr-refs b scope)))
                    (when (and (listp refs) (every (lambda (r) (< r li)) refs))
                      (push (list ci b (binary-collation a b scope) (second c)) out))))))))))))

(defun range-candidates (conjuncts li scope)
  "rowid <op> expr conjuncts for source LI: list of (op expr)."
  (let ((out '()))
    (dolist (c conjuncts out)
      (when (and (eq (car c) :binary) (member (second c) '(:lt :le :gt :ge)))
        (flet ((try (a b op)
                 (multiple-value-bind (depth si ci)
                     (case (car a)
                       (:col (resolve-column scope (second a) (third a)))
                       (:srccol (values 0 (second a) (third a))))
                   (when (and depth (= depth 0) (= si li))
                     (let ((table (src-table (nth li (scope-srcs scope)))))
                       (when (and table (or (eq ci :rowid) (eql ci (table-rowid-alias table))))
                         (let ((refs (expr-refs b scope)))
                           (when (and (listp refs) (every (lambda (r) (< r li)) refs))
                             (push (list op b) out)))))))))
          (try (third c) (fourth c) (second c))
          (try (fourth c) (third c)
               (ecase (second c) (:lt :gt) (:le :ge) (:gt :lt) (:ge :le))))))))

(defun plan-table-access (fs li conjuncts scope)
  "Return an iterate function for a stored table."
  (let* ((table (fsrc-table fs))
         (src (fsrc-src fs))
         (eqs (equality-candidates conjuncts li scope)))
    ;; 1. rowid equality
    (unless (table-without-rowid table)
      (let ((hit (find-if (lambda (c) (and (or (eq (first c) :rowid)
                                               (eql (first c) (table-rowid-alias table)))
                                           (eq (fourth c) :eq)))
                          eqs)))
        (when hit
          (let ((f (compile-expr (second hit) scope)))
            (return-from plan-table-access
              (lambda (env fn)
                (let* ((v (funcall f env))
                       (r (and (not (eq v :null)) (rowid-probe v)))
                       (row (and r (fetch-row table r (src-wanted src)))))
                  (when row (funcall fn row)))))))))
    ;; 2. index prefix equality
    (let ((best nil) (best-k 0))
      (dolist (idx (table-indexes table))
        (unless (index-where idx)
          (let ((k 0) (probes '()))
            (loop for (ci coll) in (index-columns idx)
                  for hit = (and (integerp ci)
                                 (find-if (lambda (c)
                                            (and (eql (first c) ci)
                                                 (eq (fourth c) :eq)
                                                 (eq (third c) coll)
                                                 (probe-usable-p
                                                  (column-affinity (aref (table-columns table) ci))
                                                  (expr-affinity (second c) scope))))
                                          eqs))
                  while hit
                  do (incf k) (push hit probes))
            (when (or (> k best-k)
                      (and (= k best-k) (plusp k) best (index-unique idx)
                           (not (index-unique (first best)))))
              (setf best (list idx (nreverse probes)) best-k k)))))
      (when best
        (destructuring-bind (idx probes) best
          (let* ((fns (mapcar (lambda (c) (compile-expr (second c) scope)) probes))
                 (affs (mapcar (lambda (c)
                                 (list (column-affinity (aref (table-columns table) (first c)))
                                       (expr-affinity (second c) scope)))
                               probes))
                 (cmp (index-key-cmp (index-collations idx) (index-descs idx)))
                 (pk-index (index-pk-index idx)))
            (return-from plan-table-access
              (lambda (env fn)
                (let ((probe (loop for f in fns
                                   for (ca oa) in affs
                                   for v = (funcall f env)
                                   when (eq v :null) do (return-from nil nil)
                                   collect (convert-probe v ca oa))))
                  (when (= (length probe) (length fns))
                    (catch :index-done
                      (map-index (table-owner table) (index-root idx)
                                 (lambda (vals)
                                   (unless (zerop (funcall cmp vals probe))
                                     (throw :index-done nil))
                                   (let ((row (cond (pk-index (table-record-to-row table nil vals))
                                                    ((table-without-rowid table)
                                                     (fetch-wr-row table (last vals (length (table-pk table)))))
                                                    (t (fetch-row table (car (last vals)) (src-wanted src))))))
                                     (when row (funcall fn row))))
                                 :probe probe :cmp cmp))))))))))
    ;; 3. rowid range
    (unless (table-without-rowid table)
      (let ((ranges (range-candidates conjuncts li scope)))
        (when ranges
          (let ((lows (loop for (op e) in ranges when (member op '(:gt :ge))
                            collect (cons op (compile-expr e scope))))
                (highs (loop for (op e) in ranges when (member op '(:lt :le))
                             collect (cons op (compile-expr e scope)))))
            (return-from plan-table-access
              (lambda (env fn)
                (let ((start nil) (stop nil) (stop-op nil) (empty nil))
                  (loop for (op . f) in lows
                        for v = (apply-comparison-affinity (funcall f env) :numeric)
                        do (cond ((eq v :null) (setf empty t))
                                 ((or (integerp v) (floatp v))
                                  (let ((s (if (eq op :gt)
                                               (if (integerp v) (1+ v) (ceiling* v t))
                                               (if (integerp v) v (ceiling* v nil)))))
                                    (setf start (if start (max start s) s))))
                                 (t (setf empty t))))  ; rowid > 'text' never holds
                  (loop for (op . f) in highs
                        for v = (apply-comparison-affinity (funcall f env) :numeric)
                        do (cond ((eq v :null) (setf empty t))
                                 ((or (integerp v) (floatp v))
                                  (when (or (null stop) (< v stop)) (setf stop v stop-op op)))
                                 (t nil)))  ; rowid < 'text' always holds
                  (unless empty
                    (catch :range-done
                      (map-table-rows table
                                      (lambda (row)
                                        (let ((r (svref row (1- (length row)))))
                                          (when (and stop (if (eq stop-op :lt) (>= r stop) (> r stop)))
                                            (throw :range-done nil)))
                                        (funcall fn row))
                                      :start (and start (clamp-i64 start))
                                      :wanted (src-wanted src)))))))))))
    ;; 4. full scan
    (lambda (env fn)
      (declare (ignore env))
      (map-table-rows table fn :wanted (src-wanted src)))))

(defun ceiling* (x strict)
  "Smallest integer > X (STRICT) or >= X."
  (cond ((float-infinity-p x) (if (plusp x) (1+ +i64-max+) +i64-min+))
        (t (let ((c (ceiling (rational x))))
             (if (and strict (= c (rational x))) (1+ c) c)))))

;;; ------------------------------------------------------------------
;;; Aggregate detection

(defun aggregate-call-p (e)
  (and (eq (car e) :fn)
       (let ((name (string-downcase-ascii (second e))))
         (and (gethash name *aggregates*)
              (not (and (member name '("min" "max") :test #'string=)
                        (/= (length (third e)) 1)))))))

(defun contains-aggregate-p (e)
  (labels ((walk (x)
             (when (consp x)
               (case (car x)
                 ((:subquery :exists) nil)
                 (:in (walk (second x))
                  (when (eq (car (third x)) :list) (some #'walk (second (third x)))))
                 (:fn (or (aggregate-call-p x) (some #'walk (third x))))
                 (:winfn (or (some #'walk (third x))
                             (let ((spec (seventh x)))
                               (and (eq (car spec) :spec)
                                    (or (some #'walk (getf (cdr spec) :partition))
                                        (some (lambda (o) (walk (first o))) (getf (cdr spec) :order)))))))
                 (:lit nil)
                 (:case (or (walk (second x))
                            (loop for (w th) in (third x) thereis (or (walk w) (walk th)))
                            (walk (fourth x))))
                 (t (some #'walk (cdr x)))))))
    (walk e)))

;;; ------------------------------------------------------------------
;;; Compiling a SELECT core

(defun expand-result-columns (core scope)
  "List of (ast name) for the result columns."
  (let ((out '()))
    (dolist (c (select-core-cols core) (nreverse out))
      (ecase (car c)
        (:star
         (let ((tname (second c)) (any nil))
           (loop for s in (scope-srcs scope)
                 for si from 0
                 do (when (or (null tname) (and (src-name s) (name= tname (src-name s))))
                      (setf any t)
                      (loop for name across (src-columns s)
                            for ci from 0
                            do (unless (and (null tname) (member ci (src-hidden s)))
                                 (push (list (list :srccol si ci) name) out)))))
           (unless any
             (if tname (sql-error "no such table: ~a" tname) (sql-error "no tables specified")))))
        (:expr
         (destructuring-bind (e alias text) (cdr c)
           (push (list e (or alias (result-column-name e scope text))) out)))))))

(defun result-column-name (e scope text)
  (let ((e* e))
    (case (car e*)
      (:col (multiple-value-bind (depth si ci s) (resolve-column scope (second e*) (third e*))
              (declare (ignore si))
              (cond ((and depth (integerp ci)) (svref (src-columns s) ci))
                    ((and depth (eq ci :rowid))
                     (let ((tb (src-table s)))
                       (if (and tb (table-rowid-alias tb))
                           (column-name (aref (table-columns tb) (table-rowid-alias tb)))
                           (third e*))))
                    (t (or text (third e*))))))
      (t (or text "?")))))

(defun apply-joins (fsrcs scope)
  "Turn USING/NATURAL into ON conditions and hide the duplicate columns.
Return the per-source ON expressions."
  (loop for fs in fsrcs
        for i from 0
        collect (let ((on (fsrc-on fs))
                      (src (fsrc-src fs))
                      (names (fsrc-using fs)))
                  (when (fsrc-natural fs)
                    (setf names
                          (loop for name across (src-columns src)
                                when (loop for s in (subseq (scope-srcs scope) 0 i)
                                           thereis (position name (src-columns s) :test #'name=))
                                  collect name)))
                  (dolist (name names)
                    (let ((ri (or (position name (src-columns src) :test #'name=)
                                  (sql-error "cannot join using column ~a - column not present in both tables" name)))
                          (left nil))
                      (loop for s in (subseq (scope-srcs scope) 0 i)
                            for si from 0
                            do (let ((ci (position name (src-columns s) :test #'name=)))
                                 (when (and ci (not (member ci (src-hidden s))) (null left))
                                   (setf left (list si ci)))))
                      (unless left
                        (sql-error "cannot join using column ~a - column not present in both tables" name))
                      (push ri (src-hidden src))
                      (let ((cond (list :binary :eq (cons :srccol left) (list :srccol i ri))))
                        (setf on (if on (list :binary :and on cond) cond)))))
                  on)))

(defun build-levels (fsrcs scope where &optional (ons nil ons-p))
  "Plan the nested loops.  Return (values levels final-filters)."
  (let* ((n (length fsrcs))
         (ons (if ons-p ons (apply-joins fsrcs scope)))
         (where-conjs (split-conjuncts where))
         (levels '())
         (finals '()))
    ;; table-valued function arguments may name earlier FROM items
    (dolist (fs fsrcs)
      (when (fsrc-tvf fs)
        (destructuring-bind (builder . args) (fsrc-tvf fs)
          (setf (fsrc-rows-fn fs) (funcall builder (mapcar (lambda (a) (compile-expr a scope)) args))))))
    ;; INNER/CROSS ON conditions behave as WHERE conjuncts
    (loop for fs in fsrcs
          for on in ons
          do (unless (eq (fsrc-join fs) :left)
               (setf where-conjs (append where-conjs (split-conjuncts on)))))
    (let ((placed (make-array (max n 1) :initial-element '())))
      (dolist (c where-conjs)
        (if (zerop n)
            (push c finals)
            (push c (aref placed (max-ref (expr-refs c scope) n)))))
      (loop for fs in fsrcs
            for on in ons
            for i from 0
            do (let* ((left (eq (fsrc-join fs) :left))
                      (match-asts (when left (split-conjuncts on)))
                      (filter-asts (reverse (aref placed i)))
                      ;; conjuncts usable for choosing the access path: never
                      ;; WHERE terms for the inner table of a LEFT JOIN
                      (access-asts (if left match-asts filter-asts))
                      (iterate (if (fsrc-table fs)
                                   (plan-table-access fs i access-asts scope)
                                   (let ((rf (fsrc-rows-fn fs)))
                                     (lambda (env fn)
                                       (dolist (row (funcall rf env)) (funcall fn row)))))))
                 (push (make-level :index i :fsrc fs :iterate iterate :left-p left
                                   :match (mapcar (lambda (c) (compile-expr c scope)) match-asts)
                                   :filters (mapcar (lambda (c) (compile-expr c scope)) filter-asts)
                                   :nullrow (make-array (1+ (src-ncols (fsrc-src fs)))
                                                        :initial-element :null))
                       levels))))
    (values (nreverse levels)
            (mapcar (lambda (c) (compile-expr c scope)) finals))))

(defun all-true (fns env)
  (dolist (f fns t)
    (unless (eq (truth (funcall f env)) t) (return nil))))

(defun run-levels (levels env emit)
  (labels ((run (lvs)
             (if (null lvs)
                 (funcall emit)
                 (let* ((lv (car lvs))
                        (i (level-index lv))
                        (rows (env-rows env))
                        (matched nil))
                   (funcall (level-iterate lv) env
                            (lambda (row)
                              (setf (svref rows i) row)
                              (when (all-true (level-match lv) env)
                                (setf matched t)
                                (when (all-true (level-filters lv) env)
                                  (run (cdr lvs))))))
                   (when (and (level-left-p lv) (not matched))
                     (setf (svref rows i) (level-nullrow lv))
                     (when (all-true (level-filters lv) env)
                       (run (cdr lvs))))))))
    (run levels)))

;;; ------------------------------------------------------------------
;;; ORDER BY support

(defun sort-rows (items keyspecs)
  "ITEMS are (keys . row); KEYSPECS list of (desc collation nulls)."
  (stable-sort items
               (lambda (a b)
                 (loop for ka in (car a)
                       for kb in (car b)
                       for (desc coll nulls) in keyspecs
                       do (let* ((nulls-first (if nulls (eq nulls :first) (not desc)))
                                 (c (cond ((and (eq ka :null) (eq kb :null)) 0)
                                          ((eq ka :null) (if nulls-first -1 1))
                                          ((eq kb :null) (if nulls-first 1 -1))
                                          (t (let ((c (compare-values ka kb coll)))
                                               (if desc (- c) c))))))
                            (unless (zerop c) (return (minusp c))))
                       finally (return nil)))))

(defun eval-limit (e env)
  (if (null e)
      nil
      (let ((v (funcall (compile-expr e (make-scope)) env)))
        (let ((n (value-to-integer (apply-comparison-affinity v :numeric))))
          (unless (integerp n) (sql-error "datatype mismatch"))
          n))))

(defun compile-core (core scope &key order limit offset limit-one)
  "Compile one SELECT core.  Return (values fn columns) where columns is a
list of (name affinity collation), fn (lambda (parent-env)) -> rows."
  (when (and (consp core) (eq (car core) :values))
    (return-from compile-core (compile-values-core (second core) scope order limit offset)))
  (let ((fast (multiple-value-list (count-star-fast-path core order limit offset))))
    (when (first fast) (return-from compile-core (values-list fast))))
  (let* ((fsrcs (mapcar (lambda (item) (make-fsrc-for item scope))
                        (select-core-from core)))
         (cscope (make-scope :srcs (mapcar #'fsrc-src fsrcs) :parent scope))
         (ons (apply-joins fsrcs cscope))
         (rcols (expand-result-columns core cscope))
         (_ (setf (scope-aliases cscope)
                  (loop for c in (select-core-cols core)
                        when (and (eq (car c) :expr) (third c))
                          collect (cons (third c) (second c)))))
         (group (select-core-group core))
         (having (select-core-having core))
         (agg-p (or group having
                    (some (lambda (rc) (contains-aggregate-p (first rc))) rcols)
                    (some (lambda (o) (contains-aggregate-p (first o))) order))))
    (declare (ignore _))
    (when (and having (not group) (not agg-p))
      (sql-error "a GROUP BY clause is required before HAVING"))
    (multiple-value-bind (levels finals) (build-levels fsrcs cscope (select-core-where core) ons)
      (let* ((nsrc (length fsrcs))
             (columns (loop for (e name) in rcols
                            collect (list name (expr-affinity e cscope)
                                          (or (expr-collation e cscope) :binary))))
             ;; group-by expressions are compiled before switching to aggregate mode
             (group-fns (mapcar (lambda (g)
                                  (let ((g (resolve-group-term g rcols)))
                                    (compile-expr g cscope)))
                                group))
             (group-colls (mapcar (lambda (g) (or (expr-collation (resolve-group-term g rcols) cscope)
                                                  :binary))
                                  group))
             (_2 (progn
                   (when agg-p (setf (scope-agg-p cscope) t))
                   (setf (scope-windows cscope) (make-array 0 :adjustable t :fill-pointer t)
                         (scope-window-defs cscope) (select-core-windows core))))
             (out-fns (mapcar (lambda (rc) (compile-expr (first rc) cscope)) rcols))
             (having-fn (and having (compile-expr having cscope)))
             (order-specs (compile-order-terms order rcols cscope))
             (distinct (select-core-distinct core))
             (out-colls (mapcar #'third columns))
             (aggs (coerce (scope-aggs cscope) 'list))
             (wins (scope-windows cscope)))
        (declare (ignore _2))
        (values
         (lambda (parent-env)
           (let* ((env (make-env :rows (make-array nsrc) :parent parent-env))
                  (lim (eval-limit limit parent-env))
                  (off (or (eval-limit offset parent-env) 0))
                  (lim (if limit-one 1 lim))
                  (results '())
                  (count 0)
                  (seen (and distinct (make-hash-table :test #'equal)))
                  (sorting (and order-specs t))
                  (windowed '()))
             (when (and lim (< lim 0)) (setf lim nil))
             (when (< off 0) (setf off 0))
             (flet ((output* (e)
                      ;; produce one result row from environment E
                      (let ((row (mapcar (lambda (f) (funcall f e)) out-fns)))
                        (when (or (null seen)
                                  (let ((k (group-key row out-colls)))
                                    (unless (gethash k seen)
                                      (setf (gethash k seen) t))))
                          (if sorting
                              (push (cons (mapcar (lambda (spec)
                                                    (let ((f (first spec)))
                                                      (if (integerp f) (nth f row) (funcall f e))))
                                                  order-specs)
                                          row)
                                    results)
                              (progn
                                (incf count)
                                (when (> count off) (push row results))
                                (when (and lim (>= (- count off) lim))
                                  (throw :select-done nil))))))))
              (flet ((output (e)
                       (if (plusp (length wins))
                           (push (make-env :rows (copy-seq (env-rows e)) :parent (env-parent e)
                                           :agg (env-agg e))
                                 windowed)
                           (output* e))))
               (catch :select-done
                 (when (plusp (length wins))
                   ;; all rows first; the window pass happens below
                   (setf lim nil off 0))
                 (when (and lim (zerop lim) (not sorting)) (throw :select-done nil))
                 (if (not agg-p)
                     (run-levels levels env
                                 (lambda () (when (all-true finals env) (output env))))
                     (let ((groups (make-hash-table :test #'equal))
                           (order-of-groups '()))
                       (run-levels
                        levels env
                        (lambda ()
                          (when (all-true finals env)
                            (let* ((key (group-key (mapcar (lambda (f) (funcall f env)) group-fns)
                                                   group-colls))
                                   (g (or (gethash key groups)
                                          (let ((g (cons (copy-seq (env-rows env))
                                                         (mapcar #'agg-instantiate aggs))))
                                            (push key order-of-groups)
                                            (setf (gethash key groups) g)))))
                              (let ((rep-changed nil))
                                (loop for a in (cdr g)
                                      do (when (agg-step a env) (setf rep-changed t)))
                                ;; bare columns come from the group's first row,
                                ;; or from the row that set a lone min()/max()
                                (when (and rep-changed (single-minmax-p aggs))
                                  (replace (car g) (env-rows env))))))))
                       (when (and (null group) (zerop (hash-table-count groups)))
                         (setf (gethash nil groups)
                               (cons (coerce (loop for fs in fsrcs
                                                   collect (make-array (1+ (src-ncols (fsrc-src fs)))
                                                                       :initial-element :null))
                                             'vector)
                                     (mapcar #'agg-instantiate aggs))
                               order-of-groups (list nil)))
                       ;; SQLite emits groups in GROUP BY key order
                       (let ((keys (reverse order-of-groups)))
                         (when group
                           (setf keys (mapcar #'cdr
                                              (sort-rows (mapcar (lambda (k) (cons (group-sort-key (gethash k groups) group-fns env) k)) keys)
                                                         (mapcar (lambda (c) (list nil c nil)) group-colls)))))
                         (dolist (k keys)
                           (let* ((g (gethash k groups))
                                  (e (make-env :rows (car g) :parent parent-env
                                               :agg (coerce (mapcar #'agg-final (cdr g)) 'vector))))
                             (when (or (null having-fn) (eq (truth (funcall having-fn e)) t))
                               (output e))))))))
               (when (plusp (length wins))
                 (setf windowed (nreverse windowed))
                 (compute-windows wins windowed)
                 (setf lim (eval-limit limit parent-env)
                       off (max 0 (or (eval-limit offset parent-env) 0)))
                 (when (and lim (< lim 0)) (setf lim nil))
                 (when limit-one (setf lim 1))
                 (catch :select-done
                   (when (and lim (zerop lim) (not sorting)) (throw :select-done nil))
                   (dolist (e windowed) (output* e))))))
             (if sorting
                 (let ((sorted (mapcar #'cdr (sort-rows (nreverse results)
                                                        (mapcar #'cdr order-specs)))))
                   (setf sorted (nthcdr off sorted))
                   (if lim (subseq sorted 0 (min lim (length sorted))) sorted))
                 (nreverse results))))
         columns
         cscope)))))

(defun count-star-fast-path (core order limit offset)
  "SELECT count(*) FROM <table>: count cells without decoding any record."
  (let ((cols (select-core-cols core))
        (from (select-core-from core)))
    (when (and (null order) (null limit) (null offset)
               (null (select-core-where core)) (null (select-core-group core))
               (null (select-core-having core)) (null (select-core-windows core))
               (= (length cols) 1) (eq (car (first cols)) :expr)
               (equal (butlast (second (first cols)) 0) (second (first cols)))
               (let ((e (second (first cols))))
                 (and (eq (car e) :fn) (name= (second e) "count") (fifth e)
                      (null (sixth e)) (null (third e))))
               (= (length from) 1)
               (eq (car (getf (first from) :source)) :table)
               (null (cdr (assoc (second (getf (first from) :source)) *ctes* :test #'name=))))
      (let ((table (lookup-table *db* (second (getf (first from) :source)) nil
                                 (fourth (getf (first from) :source)))))
        (when (and table (not (table-view-select table)))
          (let ((c (first cols)))
            (values (lambda (parent-env)
                      (declare (ignore parent-env))
                      (list (list (btree-count (table-owner table) (table-root table)))))
                    (list (list (or (third c) (fourth c) "count(*)") nil :binary))
                    nil)))))))

(defun group-sort-key (g group-fns parent-env)
  (let ((e (make-env :rows (car g) :parent parent-env)))
    (mapcar (lambda (f) (funcall f e)) group-fns)))

(defun single-minmax-p (aggs)
  (and aggs (null (cdr aggs))
       (member (agg-name (car aggs)) '("min" "max") :test #'string=)))

(defun resolve-group-term (g rcols)
  "GROUP BY accepts result-column numbers."
  (if (and (eq (car g) :lit) (integerp (second g)))
      (let ((k (second g)))
        (unless (<= 1 k (length rcols))
          (sql-error "GROUP BY term out of range - should be between 1 and ~d" (length rcols)))
        (first (nth (1- k) rcols)))
      g))

(defun compile-order-terms (order rcols scope)
  "Return list of (fn-or-column-index desc collation nulls)."
  (loop for (e desc coll nulls) in order
        for k from 1
        collect (let* ((idx (order-term-column e rcols k))
                       (collation (cond (coll (collation-keyword coll))
                                        (idx (or (expr-collation (first (nth idx rcols)) scope) :binary))
                                        (t (or (expr-collation e scope) :binary)))))
                  (list (or idx (compile-expr e scope)) desc collation nulls))))

(defun ordinal (k)
  (format nil "~d~a" k (if (<= 11 (mod k 100) 13)
                           "th"
                           (case (mod k 10) (1 "st") (2 "nd") (3 "rd") (t "th")))))

(defun order-term-column (e rcols &optional (k 1))
  "Index of the result column an ORDER BY term names, or NIL."
  (cond ((and (eq (car e) :lit) (integerp (second e)))
         (let ((v (second e)))
           (unless (<= 1 v (length rcols))
             (sql-error "~a ORDER BY term out of range - should be between 1 and ~d"
                        (ordinal k) (length rcols)))
           (1- v)))
        ((and (eq (car e) :col) (null (second e)))
         (position-if (lambda (rc) (and (not (eq (car (first rc)) :srccol))
                                        (name= (second rc) (third e))
                                        (not (equal (first rc) e))))
                      rcols))
        (t nil)))

(defun compile-values-core (rows scope order limit offset)
  (let* ((n (length (first rows)))
         (fns (mapcar (lambda (r)
                        (unless (= (length r) n)
                          (sql-error "all VALUES must have the same number of terms"))
                        (mapcar (lambda (e) (compile-expr e scope)) r))
                      rows))
         (columns (loop for i from 1 to n
                        collect (list (format nil "column~d" i) nil :binary))))
    (when order (sql-error "ORDER BY on VALUES is not supported without a SELECT"))
    (values (lambda (parent-env)
              (let ((out (mapcar (lambda (r) (mapcar (lambda (f) (funcall f parent-env)) r)) fns))
                    (lim (eval-limit limit parent-env))
                    (off (or (eval-limit offset parent-env) 0)))
                (setf out (nthcdr (max 0 off) out))
                (if (and lim (>= lim 0)) (subseq out 0 (min lim (length out))) out)))
            columns
            (make-scope :parent scope))))

;;; ------------------------------------------------------------------
;;; Whole SELECT statements: CTEs and compound operators

(defun materialize-cte (cte)
  (let ((sel (cte-sel cte))
        (*ctes* (cons (cons (cte-name cte) cte) (cte-env cte))))
    (if (not (and (cte-recursive-rows cte) (eq (cte-recursive-rows cte) :recursive)))
        (multiple-value-bind (fn cols) (compile-select sel (make-scope))
          (unless (cte-columns cte) (setf (cte-columns cte) (mapcar #'first cols)))
          (setf (cte-rows cte) (rows-to-vectors (funcall fn nil))
                (cte-done cte) t))
        (run-recursive-cte cte))))

(defun run-recursive-cte (cte)
  (let* ((sel (cte-sel cte))
         (cores (sel-cores sel))
         (ops (sel-ops sel))
         (op (car (last ops)))
         (anchor (make-sel :cores (butlast cores) :ops (butlast ops)))
         (recur (make-sel :cores (last cores)
                          :order (sel-order sel) :limit nil :offset nil))
         (limit (eval-limit (sel-limit sel) nil))
         (all '()) (count 0)
         (seen (and (eq op :union) (make-hash-table :test #'equal))))
    (unless (member op '(:union :union-all))
      (sql-error "recursive CTE must use UNION or UNION ALL"))
    (let ((anchor-fn (compile-select anchor (make-scope))))
      (setf (cte-done cte) :working
            (cte-recursive-rows cte) '())
      (let ((recur-fn (compile-select recur (make-scope)))
            (queue (funcall anchor-fn nil)))
        (flet ((admit (rows)
                 (loop for r in rows
                       when (or (null seen)
                                (let ((k (group-key r)))
                                  (unless (gethash k seen) (setf (gethash k seen) t))))
                         collect r)))
          (setf queue (admit queue))
          (catch :cte-done
            (loop while queue
                  do (let ((row (pop queue)))
                       (push row all)
                       (incf count)
                       (when (and limit (>= limit 0) (>= count limit)) (throw :cte-done nil))
                       (setf (cte-recursive-rows cte) (rows-to-vectors (list row)))
                       (setf queue (append queue (admit (funcall recur-fn nil))))))))
        (setf (cte-rows cte) (rows-to-vectors (nreverse all))
              (cte-done cte) t)))))

(defun register-ctes (sel)
  "Push this SELECT's WITH clause onto *CTES*."
  (dolist (w (sel-with sel))
    (destructuring-bind (name cols csel) w
      (let ((cte (make-cte :name name :columns cols :sel csel :env *ctes*)))
        (when (and (sel-recursive sel) (cte-references-self-p csel name))
          (setf (cte-recursive-rows cte) :recursive)
          ;; recursive CTEs need their column names up front
          (unless cols
            (let ((*ctes* *ctes*))
              (multiple-value-bind (fn c)
                  (compile-select (make-sel :cores (list (first (sel-cores csel)))) (make-scope))
                (declare (ignore fn))
                (setf (cte-columns cte) (mapcar #'first c))))))
        (unless (cte-columns cte)
          (let ((*ctes* *ctes*))
            (multiple-value-bind (fn c) (compile-select csel (make-scope))
              (declare (ignore fn))
              (setf (cte-columns cte) (mapcar #'first c)
                    (cte-affinities cte) (mapcar #'second c)))))
        (push (cons name cte) *ctes*)))))

(defun cte-references-self-p (sel name)
  (labels ((walk (x)
             (cond ((sel-p x) (or (some #'walk (sel-cores x))))
                   ((select-core-p x)
                    (or (some #'walk (select-core-from x))
                        (walk (select-core-where x))
                        (some #'walk (select-core-cols x))))
                   ((consp x)
                    (if (and (eq (car x) :table) (stringp (second x)) (name= (second x) name))
                        t
                        (or (walk (car x)) (walk (cdr x)))))
                   (t nil))))
    (walk sel)))

(defun compile-select (sel scope &key limit-one)
  "Return (values fn columns correlated-p)."
  (let ((*ctes* *ctes*))
    (register-ctes sel)
    (let ((cores (sel-cores sel)))
      (if (null (cdr cores))
          (multiple-value-bind (fn cols cscope)
              (compile-core (first cores) scope :order (sel-order sel)
                                                :limit (sel-limit sel) :offset (sel-offset sel)
                                                :limit-one limit-one)
            (values fn cols (and cscope (scope-outer-ref cscope))))
          (compile-compound sel scope)))))

(defun compile-subselect (sel scope &key limit-one)
  (compile-select sel scope :limit-one limit-one))

(defun compile-compound (sel scope)
  (let* ((compiled (mapcar (lambda (core)
                             (multiple-value-list (compile-core core scope)))
                           (sel-cores sel)))
         (cols (second (first compiled)))
         (n (length cols))
         (colls (mapcar #'third cols))
         (correlated (some (lambda (c) (and (third c) (scope-outer-ref (third c)))) compiled)))
    (dolist (c compiled)
      (unless (= (length (second c)) n)
        (sql-error "SELECTs to the left and right of ~a do not have the same number of result columns"
                   (case (first (sel-ops sel)) (:union-all "UNION ALL") (:union "UNION")
                         (:intersect "INTERSECT") (t "EXCEPT")))))
    (let ((order (loop for (e desc coll nulls) in (sel-order sel)
                       collect (let ((idx (cond ((and (eq (car e) :lit) (integerp (second e)))
                                                 (1- (second e)))
                                                ((eq (car e) :col)
                                                 (position (third e) cols :key #'first :test #'name=))
                                                ((eq (car e) :collate)
                                                 (and (eq (car (second e)) :col)
                                                      (position (third (second e)) cols :key #'first :test #'name=))))))
                                 (unless (and idx (< -1 idx n))
                                   (sql-error "ORDER BY term does not match any column in the result set"))
                                 (list idx desc
                                       (cond (coll (collation-keyword coll))
                                             ((eq (car e) :collate) (collation-keyword (third e)))
                                             (t (nth idx colls)))
                                       nulls)))))
      (values
       (lambda (parent-env)
         (let ((rows (funcall (first (first compiled)) parent-env))
               (distinct-sorted nil))
           (loop for op in (sel-ops sel)
                 for c in (rest compiled)
                 do (let ((next (funcall (first c) parent-env)))
                      (ecase op
                        (:union-all (setf rows (append rows next)))
                        (:union (setf rows (dedupe-rows (append rows next) colls)
                                      distinct-sorted t))
                        (:intersect
                         (let ((h (make-hash-table :test #'equal)))
                           (dolist (r next) (setf (gethash (group-key r colls) h) t))
                           (setf rows (dedupe-rows (remove-if-not (lambda (r) (gethash (group-key r colls) h)) rows)
                                                   colls)
                                 distinct-sorted t)))
                        (:except
                         (let ((h (make-hash-table :test #'equal)))
                           (dolist (r next) (setf (gethash (group-key r colls) h) t))
                           (setf rows (dedupe-rows (remove-if (lambda (r) (gethash (group-key r colls) h)) rows)
                                                   colls)
                                 distinct-sorted t))))))
           (when (and distinct-sorted (null order))
             ;; SQLite's set operators produce rows in key order
             (setf rows (mapcar #'cdr (sort-rows (mapcar (lambda (r) (cons r r)) rows)
                                                 (mapcar (lambda (c) (list nil c nil)) colls)))))
           (when order
             (setf rows (mapcar #'cdr
                                (sort-rows (mapcar (lambda (r)
                                                     (cons (mapcar (lambda (o) (nth (first o) r)) order) r))
                                                   rows)
                                           (mapcar #'cdr order)))))
           (let ((lim (eval-limit (sel-limit sel) parent-env))
                 (off (or (eval-limit (sel-offset sel) parent-env) 0)))
             (setf rows (nthcdr (max 0 off) rows))
             (if (and lim (>= lim 0)) (subseq rows 0 (min lim (length rows))) rows))))
       cols
       correlated))))

(defun dedupe-rows (rows colls)
  (let ((h (make-hash-table :test #'equal)))
    (loop for r in rows
          for k = (group-key r colls)
          unless (gethash k h)
            collect (progn (setf (gethash k h) t) r))))

(defun select-first-affinity (sel scope)
  (ignore-errors
   (let ((core (first (sel-cores sel))))
     (when (and (select-core-p core) (eq (car (first (select-core-cols core))) :expr))
       (let ((*ctes* *ctes*))
         (register-ctes sel)
         (let* ((fsrcs (mapcar (lambda (item) (make-fsrc-for item scope)) (select-core-from core)))
                (cscope (make-scope :srcs (mapcar #'fsrc-src fsrcs) :parent scope)))
           (expr-affinity (second (first (select-core-cols core))) cscope)))))))

(defun select-first-collation (sel scope)
  (ignore-errors
   (let ((core (first (sel-cores sel))))
     (when (and (select-core-p core) (eq (car (first (select-core-cols core))) :expr))
       (let ((*ctes* *ctes*))
         (register-ctes sel)
         (let* ((fsrcs (mapcar (lambda (item) (make-fsrc-for item scope)) (select-core-from core)))
                (cscope (make-scope :srcs (mapcar #'fsrc-src fsrcs) :parent scope)))
           (expr-collation (second (first (select-core-cols core))) cscope)))))))
