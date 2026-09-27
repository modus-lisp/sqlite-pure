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

(defvar *order-hint* nil
  "For the first FROM item: (:rowid dir) or (:index index dir) if iterating
that way would produce the rows in ORDER BY order.")
(defvar *order-satisfied* nil
  "Set by the planner when it adopted *ORDER-HINT*.")


(defstruct cte name columns sel (rows nil) (done nil) recursive-rows affinities env
  error                      ; the error a reference to it raises, if its definition is bad
  declared                   ; the column names given in WITH name(...), if any
  checked)                   ; its shape has been checked (on first use)

;;; ------------------------------------------------------------------
;;; Rows of stored tables

(defun column-default-value (col)
  (let ((d (column-default col)))
    (if d
        (apply-affinity (funcall (compile-expr d (make-scope)) nil) (column-affinity col))
        :null)))

(defun record-column-order (table)
  "Column indexes in the order the record stores them: the primary key
first for WITHOUT ROWID tables, and never a VIRTUAL generated column."
  (let* ((cols (table-columns table))
         (n (length cols))
         (all (if (table-without-rowid table)
                  (append (table-pk table)
                          (loop for i below n unless (member i (table-pk table)) collect i))
                  (loop for i below n collect i))))
    (remove-if (lambda (i) (column-virtual-p (aref cols i))) all)))

(defun table-record-to-row (table rowid vals)
  "Vector of the table's column values in declaration order + rowid."
  (let* ((cols (table-columns table))
         (n (length cols))
         (row (make-array (1+ n) :initial-element :null)))
    (dolist (i (record-column-order table))
      (let ((v (if vals (pop vals) (column-default-value (aref cols i)))))
        (setf (svref row i)
              (cond ((eql i (table-rowid-alias table)) rowid)
                    ((and (integerp v) (eq (column-affinity (aref cols i)) :real))
                     (safe-double v))
                    (t v)))))
    (setf (svref row n) (if (table-without-rowid table) :null rowid))
    (when (table-virtual-p table)
      (compute-generated table row :virtual-only t))
    row))

(defun fetch-row (table rowid &optional wanted)
  (when (table-virtual-p table) (setf wanted nil))
  (let ((payload (table-lookup (table-owner table) (table-root table) rowid)))
    (when payload
      (table-record-to-row table rowid (decode-record payload 0 (length payload) nil wanted)))))

(defun map-table-rows (table fn &key start wanted)
  "Call FN on every row of TABLE.  WANTED (a bit vector) limits which
columns are decoded; the others read as NULL."
  (when (table-virtual-p table) (setf wanted nil))
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
  on using natural
  index-hint      ; NOT INDEXED -> :not; INDEXED BY i -> the INDEX
  vtab-args       ; t('query', ...) on an FTS5 table: the argument ASTs
  label           ; EXPLAIN QUERY PLAN: what a non-table source's loop is called
  scan-index)     ; EQP: thunk -> the index (or :rowid) a full scan reads in order, if any

(defun make-table-src (table &optional alias)
  (let ((cols (table-columns table)))
    (make-src :name (or alias (table-name table))
              :columns (map 'vector #'column-name cols)
              :affinities (map 'vector #'column-affinity cols)
              :collations (map 'vector #'column-collation cols)
              :table table
              :star-hidden (loop for c across cols for i from 0 when (column-hidden c) collect i)
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

(defun eqp-derived-kind ()
  (if *eqp-coroutine-ok* "CO-ROUTINE" "MATERIALIZE"))

(defun eqp-describe-cte (cte)
  "EXPLAIN QUERY PLAN: how CTE is computed (once per statement)."
  (unless (member cte *eqp-ctes-done*)
    (push cte *eqp-ctes-done*)
    (let ((kind (if (> (- (gethash (string-downcase-ascii (cte-name cte)) *eqp-cte-uses* 0)
                          (eqp-table-refs (cte-sel cte) (cte-name cte)))   ; its own recursion
                       1)
                    "MATERIALIZE"
                    (eqp-derived-kind)))
          (*ctes* (cons (cons (cte-name cte) cte) (cte-env cte)))
          (*eqp-coroutine-ok* nil))
      (with-eqp-node ((format nil "~a ~a" kind (cte-name cte)) +eqp-materialize+)
        (if (eq (cte-recursive-rows cte) :recursive)
            (let ((sel (cte-sel cte)))
              (with-eqp-node ("SETUP")
                (compile-select (make-sel :cores (butlast (sel-cores sel)) :ops (butlast (sel-ops sel)))
                                (make-scope)))
              (with-eqp-node ("RECURSIVE STEP")
                (compile-select (make-sel :cores (last (sel-cores sel))) (make-scope))))
            (compile-select (cte-sel cte) (make-scope)))))))

(defun check-cte-shape (cte)
  "What expanding a CTE checks, in SQLite's order: the leftmost SELECT's
width against the declared columns, then a recursive CTE's terms against
each other."
  (unless (cte-checked cte)
    (setf (cte-checked cte) t)
    (let* ((sel (cte-sel cte))
           (*ctes* (cons (cons (cte-name cte) cte) (cte-env cte)))
           (*eqp* nil)                  ; checking is not part of the plan
           (width (lambda (core)
                    (length (nth-value 1 (compile-select (make-sel :cores (list core)) (make-scope)))))))
      (when (cte-declared cte)
        (let ((n (funcall width (first (sel-cores sel)))))
          (unless (= n (length (cte-declared cte)))
            (setf (cte-checked cte) nil)
            (sql-error "table ~a has ~d values for ~d columns" (cte-name cte) n (length (cte-declared cte))))))
      (when (eq (cte-recursive-rows cte) :recursive)
        (let ((anchor (length (nth-value 1 (compile-select (make-sel :cores (butlast (sel-cores sel))
                                                                     :ops (butlast (sel-ops sel)))
                                                           (make-scope)))))
              (recur (let ((saved (cte-done cte)))
                       ;; compile the recursive term as the recursion would see it
                       (setf (cte-done cte) :working)
                       (unwind-protect (funcall width (car (last (sel-cores sel))))
                         (setf (cte-done cte) saved)))))
          (unless (= anchor recur)
            (setf (cte-checked cte) nil)
            (sql-error "SELECTs to the left and right of ~a do not have the same number of result columns"
                       (if (eq (car (last (sel-ops sel))) :union) "UNION" "UNION ALL"))))))))

(defun cte-source (cte alias)
  (when (cte-error cte) (sql-error (cte-error cte) (cte-name cte)))
  (check-cte-shape cte)
  (when *eqp* (eqp-describe-cte cte))
  (let* ((src (derived-src (or alias (cte-name cte)) (cte-columns cte)
                           (or (cte-affinities cte) (make-list (length (cte-columns cte))))
                           (make-list (length (cte-columns cte)) :initial-element :binary))))
    (make-fsrc :src src
               :label (or alias (cte-name cte))
               :rows-fn (lambda (env)
                          (declare (ignore env))
                          (case (cte-done cte)
                            ;; inside this CTE's own recursive step: the current row
                            (:working (cte-recursive-rows cte))
                            ;; another reference while a scan streams it: a copy of
                            ;; its own, computed in full
                            (:streaming (let ((copy (copy-cte cte)))
                                          (setf (cte-done copy) nil (cte-rows copy) nil
                                                (cte-recursive-rows copy) :recursive)
                                          (materialize-cte copy)
                                          (cte-rows copy)))
                            ((t) (cte-rows cte))
                            (t (if (eq (cte-recursive-rows cte) :recursive)
                                   ;; SQLite runs a recursive query as a co-routine:
                                   ;; rows reach the outer scan as they are made, so an
                                   ;; outer LIMIT ends an unbounded recursion
                                   (lambda (fn) (materialize-cte cte fn))
                                   (progn (materialize-cte cte) (cte-rows cte)))))))))

(defun eqp-labelled (fs label)
  (setf (fsrc-label fs) label)
  fs)

(defun make-fsrc-for (item scope)
  (destructuring-bind (&key source join on using natural) item
    (let ((fs
            (ecase (car source)
              (:table
               (destructuring-bind (name alias &optional schema hint) (cdr source)
                 (declare (ignore hint))
                 (let ((cte (and (null (fourth source)) (cdr (assoc name *ctes* :test #'name=)))))
                   (cond
                     (cte (cte-source cte alias))
                     ((and (pragma-vtab-spec name) (null (lookup-table *db* name nil schema)))
                      (pragma-table-source name '() alias))
                     ((and (name= name "dbstat") (null (lookup-table *db* name nil schema)))
                      (dbstat-fsrc alias '()))
                     (t (let ((table (lookup-table *db* name t schema)))
                          (if (table-view-select table)
                              (let ((*ctes* '()))
                                (with-eqp-node ((format nil "~a ~a" (eqp-derived-kind) (or alias name))
                                                +eqp-materialize+)
                                  (let ((*eqp-coroutine-ok* nil))
                                    (eqp-labelled
                                     (select-derived-source (table-view-select table) (or alias name)
                                                            (make-scope)
                                                            (table-view-columns table))
                                     (or alias name)))))
                              (let ((hint (fifth source)))
                                (make-fsrc :src (make-table-src table alias) :table table
                                           :index-hint
                                           (cond ((eq hint :not) :not)
                                                 (hint (or (find (second hint) (table-indexes table)
                                                                 :key #'index-name :test #'name=)
                                                           (sql-error "no such index: ~a" (second hint))))))))))))))
              (:subquery
               (let ((label (or (third source)
                                (format nil "(subquery-~a)" (eqp-sel-id (second source))))))
                 (with-eqp-node ((format nil "~a ~a" (eqp-derived-kind) label) +eqp-materialize+)
                   (let ((*eqp-coroutine-ok* nil))
                     (eqp-labelled (select-derived-source (second source) (third source) scope) label)))))
              (:join-group
               (let ((*eqp-coroutine-ok* nil))
                 (select-derived-source
                  (make-sel :cores (list (make-select-core :cols (list (list :star nil))
                                                           :from (second source))))
                  (third source) scope)))
              (:tvf
               (destructuring-bind (name args alias) (cdr source)
                 (cond
                   ((or (name= name "json_each") (name= name "json_tree"))
                    (let ((fs (json-table-source name nil alias)))
                      (setf (fsrc-label fs) (format nil "~a VIRTUAL TABLE INDEX ~d:" (or alias (string-downcase-ascii name))
                                                    (case (length args) (0 0) (1 1) (t 3))))
                      (setf (fsrc-tvf fs)
                            (cons (lambda (fns) (fsrc-rows-fn (json-table-source name fns alias))) args))
                      fs))
                   ((and (name= name "dbstat") (null (lookup-table *db* name nil)))
                    (dbstat-fsrc alias args))
                   ((pragma-vtab-spec name)
                    (let ((fs (pragma-table-source name nil alias)))
                      (setf (fsrc-label fs) (format nil "~a VIRTUAL TABLE INDEX 0:" (or alias (string-downcase-ascii name))))
                      (when (> (length args) (length (third (pragma-vtab-spec name))))
                        (sql-error "too many arguments on ~a() - max ~d"
                                   (string-downcase-ascii name) (length (third (pragma-vtab-spec name)))))
                      (setf (fsrc-tvf fs)
                            (cons (lambda (fns) (fsrc-rows-fn (pragma-table-source name fns alias))) args))
                      fs))
                   ((let ((tb (lookup-table *db* name nil)))
                      (and tb (fts5-p (table-vtab tb))))
                    (let ((tb (lookup-table *db* name nil)))
                      (when (> (length args) 2)
                        (sql-error "too many arguments on ~a() - max 2" name))
                      (make-fsrc :src (make-table-src tb alias) :table tb :vtab-args args)))
                   ((lookup-table *db* name nil) (sql-error "'~a' is not a function" name))
                   (t (sql-error "no such table: ~a" name))))))))
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
  match            ; list of compiled ON conjuncts (LEFT/RIGHT/FULL JOIN)
  filters          ; list of compiled conjuncts
  left-p           ; unmatched rows of the earlier sources survive (LEFT, FULL)
  right-p          ; unmatched rows of this source survive (RIGHT, FULL)
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
                    (when (or (and (listp refs) (every (lambda (r) (< r li)) refs))
                              (uncorrelated-subquery-p b scope))
                      (push (list ci b (binary-collation a b scope) (second c)) out))))))))))))

(defun uncorrelated-subquery-p (e scope)
  "Is E a scalar subquery that refers to nothing outside itself (so it can
be evaluated before any loop)?"
  (and (eq (car e) :subquery)
       (ignore-errors
        (not (third (multiple-value-list
                     (without-eqp (compile-subselect (second e) scope :limit-one t))))))))

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

(defvar *minmax-hint* nil
  "For a lone min()/max() over one table: (column-index :min|:max).")

(defun index-allowed-p (fs idx)
  "May FS's loop use IDX (NOT INDEXED / INDEXED BY)?"
  (let ((h (fsrc-index-hint fs)))
    (cond ((null h) t)
          ((eq h :not) (index-pk-index idx))     ; a WITHOUT ROWID table is its key
          (t (or (eq h idx) (index-pk-index idx))))))

(defun in-candidates (conjuncts li scope)
  "col IN (...) conjuncts on source LI whose right side is known before
LI's loop: list of (column-index rhs x-ast)."
  (let ((out '()))
    (dolist (c conjuncts (nreverse out))
      (when (and (eq (car c) :in) (not (fourth c)))
        (let* ((x (second c)) (rhs (third c))
               (x* (if (eq (car x) :collate) (second x) x)))
          (multiple-value-bind (depth si ci)
              (case (car x*)
                (:col (resolve-column scope (second x*) (third x*)))
                (:srccol (values 0 (second x*) (third x*))))
            (when (and depth (= depth 0) (= si li)
                       (case (car rhs)
                         (:list (every (lambda (e) (let ((r (expr-refs e scope)))
                                                     (and (listp r) (every (lambda (k) (< k li)) r))))
                                       (second rhs)))
                         (:select t)))
              (push (list ci rhs x) out))))))))

(defun in-values-fn (rhs scope)
  "(lambda (env)) -> the IN operand's values, or NIL if they cannot be
known before the loop (a subquery correlated with anything)."
  (ecase (car rhs)
    (:list (let ((fns (mapcar (lambda (e) (compile-expr e scope)) (second rhs))))
             (lambda (env) (mapcar (lambda (f) (funcall f env)) fns))))
    (:select (multiple-value-bind (fn cols correlated)
                 (without-eqp (compile-subselect (second rhs) scope))
               (when (and (not correlated) (= (length cols) 1))
                 (let ((cache nil))
                   (lambda (env)
                     (or cache (setf cache (list* :done (mapcar #'first (funcall fn env))))))))))))

(defun plan-table-access (fs li conjuncts scope)
  "Return an iterate function for a stored table."
  (when (table-vtab (fsrc-table fs))
    (return-from plan-table-access (vtab-plan-access fs li conjuncts scope)))
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
            (eqp-table-note (format nil "SEARCH ~a USING INTEGER PRIMARY KEY (rowid=?)" (src-name src)))
            (return-from plan-table-access
              (lambda (env fn)
                (let* ((v (funcall f env))
                       (r (and (not (eq v :null)) (rowid-probe v)))
                       (row (and r (fetch-row table r (src-wanted src)))))
                  (when row (funcall fn row)))))))))
    ;; 1b. rowid IN (...)
    (unless (table-without-rowid table)
      (let* ((hit (find-if (lambda (c) (or (eq (first c) :rowid) (eql (first c) (table-rowid-alias table))))
                           (in-candidates conjuncts li scope)))
             (vf (and hit (in-values-fn (second hit) scope))))
        (when vf
          (eqp-table-note (format nil "SEARCH ~a USING INTEGER PRIMARY KEY (rowid=?)" (src-name src)))
          (return-from plan-table-access
            (lambda (env fn)
              (let ((vals (funcall vf env)))
                (when (eq (car vals) :done) (setf vals (cdr vals)))
                (dolist (r (sort (remove-duplicates
                                  (loop for v in vals
                                        for r = (and (not (eq v :null)) (rowid-probe v))
                                        when r collect r))
                                 #'<))
                  (let ((row (fetch-row table r (src-wanted src))))
                    (when row (funcall fn row))))))))))
    ;; 2. index prefix equality
    (let ((best nil) (best-k 0))
      (dolist (idx (table-indexes table))
        (unless (or (index-where idx) (not (index-allowed-p fs idx)))
          (let ((k 0) (probes '()))
            (loop for (ci coll) in (index-columns idx)
                  for hit = (and (integerp ci)
                                 (find-if (lambda (c)
                                            (and (eql (first c) ci)
                                                 (eq (fourth c) :eq)
                                                 (collation= (third c) coll)
                                                 (probe-usable-p
                                                  (column-affinity (aref (table-columns table) ci))
                                                  (expr-affinity (second c) scope))))
                                          eqs))
                  while hit
                  do (incf k) (push hit probes))
            ;; on a tie the newest index wins, as in SQLite (whose list is
            ;; newest first), unless only the earlier one is unique
            (when (or (> k best-k)
                      (and (= k best-k) (plusp k) best
                           (or (index-unique idx) (not (index-unique (first best))))))
              (setf best (list idx (nreverse probes)) best-k k)))))
      (when best
        (destructuring-bind (idx probes) best
          (let* ((fns (mapcar (lambda (c) (compile-expr (second c) scope)) probes))
                 (affs (mapcar (lambda (c)
                                 (list (column-affinity (aref (table-columns table) (first c)))
                                       (expr-affinity (second c) scope)))
                               probes))
                 (cmp (index-key-cmp (index-collations idx) (index-descs idx)))
                 (pk-index (index-pk-index idx))
                 (covers :unknown))
            (flet ((covering-p ()
                     (when (eq covers :unknown)
                       (setf covers (and (not pk-index) (index-covers-p table idx (src-wanted src)))))
                     covers))
              (eqp-table-note
               (lambda ()
                 (format nil "SEARCH ~a USING ~a (~{~a=?~^ AND ~})"
                         (src-name src)
                         (cond (pk-index "PRIMARY KEY")
                               ((covering-p) (format nil "COVERING INDEX ~a" (index-name idx)))
                               (t (format nil "INDEX ~a" (index-name idx))))
                         (mapcar (lambda (c) (column-name (aref (table-columns table) (first c)))) probes))))
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
                                                    ((covering-p) (row-from-index table idx vals))
                                                    (t (fetch-row table (car (last vals)) (src-wanted src))))))
                                     (when row (funcall fn row))))
                                 :probe probe :cmp cmp)))))))))))
    ;; 2b. IN (...) on an index's first column
    (let ((ins (in-candidates conjuncts li scope)))
      (dolist (idx (reverse (table-indexes table)))    ; newest first
        (let* ((ic (first (index-columns idx)))
               (hit (and (not (index-where idx)) (index-allowed-p fs idx) (not (index-pk-index idx))
                         (not (table-without-rowid table))
                         (find-if (lambda (c)
                                    (and (eql (first c) (first ic))
                                         (collation= (or (expr-collation (third c) scope) :binary) (second ic))
                                         (or (eq (car (second c)) :list)
                                             (probe-usable-p (column-affinity (aref (table-columns table) (first ic)))
                                                             (select-first-affinity (second (second c)) scope)))))
                                  ins)))
               (vf (and hit (in-values-fn (second hit) scope))))
          (when vf
            (let* ((col-aff (column-affinity (aref (table-columns table) (first ic))))
                   (other-aff (if (eq (car (second hit)) :list)
                                  nil
                                  (select-first-affinity (second (second hit)) scope)))
                   (cmp (index-key-cmp (list (second ic)) (list (third ic))))
                   (covers :unknown))
              (flet ((covering-p ()
                       (when (eq covers :unknown)
                         (setf covers (index-covers-p table idx (src-wanted src))))
                       covers))
                (eqp-table-note (lambda ()
                                  (format nil "SEARCH ~a USING ~:[~;COVERING ~]INDEX ~a (~a=?)"
                                          (src-name src) (covering-p) (index-name idx)
                                          (column-name (aref (table-columns table) (first ic))))))
                (return-from plan-table-access
                  (lambda (env fn)
                    (let* ((vals (funcall vf env))
                           (vals (if (eq (car vals) :done) (cdr vals) vals))
                           (probes (sort (loop for v in vals
                                               unless (eq v :null)
                                                 collect (list (convert-probe v col-aff other-aff)))
                                         (lambda (a b) (minusp (funcall cmp a b)))))
                           (last nil))
                      (dolist (probe probes)
                        (unless (and last (zerop (funcall cmp last probe)))
                          (setf last probe)
                          (catch :index-done
                            (map-index (table-owner table) (index-root idx)
                                       (lambda (ivals)
                                         (unless (zerop (funcall cmp ivals probe))
                                           (throw :index-done nil))
                                         (let ((row (if (covering-p)
                                                        (row-from-index table idx ivals)
                                                        (fetch-row table (car (last ivals)) (src-wanted src)))))
                                           (when row (funcall fn row))))
                                       :probe probe :cmp cmp)))))))))))))
    ;; 3. rowid range
    (unless (table-without-rowid table)
      (let ((ranges (range-candidates conjuncts li scope)))
        (when ranges
          (let ((lows (loop for (op e) in ranges when (member op '(:gt :ge))
                            collect (cons op (compile-expr e scope))))
                (highs (loop for (op e) in ranges when (member op '(:lt :le))
                             collect (cons op (compile-expr e scope)))))
            (eqp-table-note (format nil "SEARCH ~a USING INTEGER PRIMARY KEY (~{~a~^ AND ~})" (src-name src)
                                    (append (when lows (list "rowid>?")) (when highs (list "rowid<?")))))
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
    ;; 4. full scan -- in the order ORDER BY wants, when we can
    (let* ((hint (and (= li 0) *order-hint*))
           (hint (if (and hint (eq (first hint) :index) (not (index-allowed-p fs (second hint))))
                     nil hint))
           (forced (and (index-p (fsrc-index-hint fs)) (fsrc-index-hint fs))))
      (when (and forced (not (and hint (eq (first hint) :index) (eq (second hint) forced))))
        ;; INDEXED BY with nothing to seek: scan that index
        (setf hint (list :index forced :asc))
        (setf *order-hint* nil))
      (let ((*eqp* *eqp*))
      (when (and (= li 0) *minmax-hint* (null conjuncts))
        (let ((mm (minmax-access fs *minmax-hint*)))
          (when mm (return-from plan-table-access mm))
          (setf *eqp* nil)))             ; its note is made; scan as usual
      (cond
        ((and hint (eq (first hint) :rowid) (not (table-without-rowid table)))
         (setf *order-satisfied* t)
         (eqp-table-note (format nil "SCAN ~a" (src-name src)))
         (setf (fsrc-scan-index fs) (lambda () :rowid))
         (if (eq (second hint) :desc)
             (lambda (env fn)
               (declare (ignore env))
               (map-table-reverse (table-owner table) (table-root table)
                                  (lambda (rowid payload)
                                    (funcall fn (table-record-to-row
                                                 table rowid
                                                 (decode-record payload 0 (length payload) nil
                                                                (and (not (table-virtual-p table))
                                                                     (src-wanted src))))))))
             (lambda (env fn)
               (declare (ignore env))
               (map-table-rows table fn :wanted (src-wanted src)))))
        ((and hint (eq (first hint) :index))
         (when *order-hint* (setf *order-satisfied* t))
         (destructuring-bind (idx dir) (rest hint)
           (let* ((owner (table-owner table))
                  (pk-index (index-pk-index idx))
                  (covers :unknown))
             (flet ((covering-p ()
                      (when (eq covers :unknown)
                        (setf covers (and (not pk-index) (index-covers-p table idx (src-wanted src)))))
                      covers))
             (setf (fsrc-scan-index fs) (lambda () idx))
             (eqp-table-note (lambda ()
                               (if pk-index
                                   (format nil "SCAN ~a" (src-name src))
                                   (format nil "SCAN ~a USING ~:[~;COVERING ~]INDEX ~a"
                                           (src-name src) (covering-p) (index-name idx)))))
             (lambda (env fn)
               (declare (ignore env))
               (funcall (if (eq dir :desc) #'map-index-reverse #'map-index)
                        owner (index-root idx)
                        (lambda (vals)
                          (let ((row (cond (pk-index (table-record-to-row table nil vals))
                                           ((table-without-rowid table)
                                            (fetch-wr-row table (last vals (length (table-pk table)))))
                                           ((covering-p) (row-from-index table idx vals))
                                           (t (fetch-row table (car (last vals)) (src-wanted src))))))
                            (when row (funcall fn row))))))))))
        (t
         (setf (fsrc-scan-index fs)
               (lambda () (or (covering-index table (src-wanted src) fs)
                              (if (table-without-rowid table)
                                  (find-if #'index-pk-index (table-indexes table))
                                  :rowid))))
         (eqp-table-note (lambda ()
                           (let ((idx (covering-index table (src-wanted src) fs)))
                             (format nil "SCAN ~a~@[ USING COVERING INDEX ~a~]"
                                     (src-name src) (and idx (index-name idx))))))
         (lambda (env fn)
           (declare (ignore env))
           ;; Like SQLite, scan a covering index instead of the table when
           ;; one holds every column the query reads (this decides the row
           ;; order an unordered query, or group_concat, sees).
           (let ((idx (covering-index table (src-wanted src) fs)))
             (if idx
                 (map-index (table-owner table) (index-root idx)
                            (lambda (vals) (funcall fn (row-from-index table idx vals))))
                 (map-table-rows table fn :wanted (src-wanted src)))))))))))

(defun minmax-candidate (core rcols having order scope fsrcs)
  "(column :min|:max) when the query's only aggregate is min/max of a
column of its single table, with no WHERE or GROUP BY."
  (let ((fs (first fsrcs)))
    (when (and fs (null (cdr fsrcs)) (fsrc-table fs) (not (table-vtab (fsrc-table fs)))
               (null (select-core-where core)) (null (select-core-group core))
               (not (select-core-distinct core)))
      (let ((calls '()))
        (labels ((walk (x)
                   (when (consp x)
                     (case (car x)
                       ((:subquery :exists) nil)
                       (:fn (if (aggregate-call-p x) (push x calls) (mapc #'walk (cdr x))))
                       (:winfn (push x calls))
                       (t (mapc #'walk (cdr x)))))))
          (mapc (lambda (rc) (walk (first rc))) rcols)
          (walk having)
          (mapc (lambda (o) (walk (first o))) order))
        (let ((c (and calls (null (cdr calls)) (first calls))))
          (when (and c (eq (car c) :fn)
                     (member (string-downcase-ascii (second c)) '("min" "max") :test #'string=)
                     (= (length (third c)) 1) (not (fourth c)))
            (let ((a (first (third c))))
              (when (eq (car a) :col)
                (multiple-value-bind (depth si ci) (resolve-column scope (second a) (third a))
                  (when (and depth (= depth 0) (= si 0))
                    (list ci (if (string-equal (second c) "min") :min :max))))))))))))

(defun minmax-access (fs hint)
  "A lone min(col)/max(col): read one end of the rowid order or of an index
led by COL (SQLite's min/max optimisation).  NIL if neither exists."
  (destructuring-bind (ci kind) hint
    (let* ((table (fsrc-table fs))
           (src (fsrc-src fs))
           (owner (table-owner table))
           (rowid-p (and (not (table-without-rowid table))
                         (or (eq ci :rowid) (eql ci (table-rowid-alias table)))))
           (idx (and (not rowid-p) (integerp ci) (not (table-without-rowid table))
                     (find-if (lambda (idx)
                                (let ((ic (first (index-columns idx))))
                                  (and (null (index-where idx)) (index-allowed-p fs idx)
                                       (eql (first ic) ci)
                                       (collation= (second ic) (column-collation (aref (table-columns table) ci))))))
                              (reverse (table-indexes table))))))
      (cond
        (rowid-p
         (eqp-table-note (format nil "SEARCH ~a" (src-name src)))
         (lambda (env fn)
           (declare (ignore env))
           (catch :minmax
             (funcall (if (eq kind :max) #'map-table-reverse #'map-table) owner (table-root table)
                      (lambda (rowid payload)
                        (funcall fn (table-record-to-row table rowid
                                                         (decode-record payload 0 (length payload) nil
                                                                        (src-wanted src))))
                        (throw :minmax nil))))))
        (idx
         (let ((desc (third (first (index-columns idx)))) (covers :unknown))
           (flet ((covering-p ()
                    (when (eq covers :unknown) (setf covers (index-covers-p table idx (src-wanted src))))
                    covers))
             (eqp-table-note (lambda () (format nil "SEARCH ~a USING ~:[~;COVERING ~]INDEX ~a"
                                                (src-name src) (covering-p) (index-name idx))))
             (lambda (env fn)
               (declare (ignore env))
               (let ((from-end (if desc (eq kind :min) (eq kind :max))))
                 (catch :minmax
                   ;; NULLs sort first: max takes the last entry (NULL only if
                   ;; all are), min the first non-NULL one
                   (funcall (if from-end #'map-index-reverse #'map-index) owner (index-root idx)
                            (lambda (vals)
                              (unless (and (eq kind :min) (eq (first vals) :null))
                                (let ((row (if (covering-p)
                                               (row-from-index table idx vals)
                                               (fetch-row table (car (last vals)) (src-wanted src)))))
                                  (when row (funcall fn row)))
                                (throw :minmax nil))))))))))
        (t
         ;; no index: every row is read, but SQLite still calls the loop a SEARCH
         (eqp-table-note (format nil "SEARCH ~a" (src-name src)))
         nil)))))

(defun row-from-index (table idx vals)
  "A table row built from an index entry (the columns it lacks read NULL)."
  (let* ((cols (table-columns table))
         (n (length cols))
         (row (make-array (1+ n) :initial-element :null)))
    (loop for (ci) in (index-columns idx)
          for v in vals
          do (setf (svref row ci)
                   (if (and (integerp v) (eq (column-affinity (aref cols ci)) :real))
                       (safe-double v)
                       v)))
    (let ((rowid (car (last vals))))
      (setf (svref row n) rowid)
      (when (table-rowid-alias table)
        (setf (svref row (table-rowid-alias table)) rowid)))
    row))

(defun index-covers-p (table idx wanted)
  "Does IDX (of a rowid table) hold every WANTED column?"
  (let ((cols (mapcar #'first (index-columns idx))))
    (and wanted (not (table-without-rowid table)) (not (table-virtual-p table))
         (null (index-where idx))
         (every #'integerp cols)
         (loop for i below (length wanted)
               always (or (zerop (sbit wanted i))
                          (eql i (table-rowid-alias table))
                          (member i cols))))))

(defun column-size-estimate (type)
  "SQLite's Column.szEst: a column's size, an integer being 1, from its
declared type (sqlite3AddColumn and sqlite3AffinityType)."
  (let ((type (or type "")))
    (cond
      ((zerop (length type)) 1)
      ;; the standard names: TEXT and BLOB are 5, the rest (ANY, INT,
      ;; INTEGER, REAL) are 1
      ((and (>= (length type) 3)
            (member type '("ANY" "BLOB" "INT" "INTEGER" "REAL" "TEXT") :test #'string-equal))
       (if (member type '("BLOB" "TEXT") :test #'string-equal) 5 1))
      (t
       (let ((h 0) (aff :numeric) (zchar nil) (n (length type)))
         (loop for i below n
               do (setf h (logand #xffffffff (+ (ash h 8) (char-code (char-downcase (char type i))))))
                  (let ((next (1+ i)))
                    (flet ((is (s) (= h (reduce (lambda (a c) (+ (ash a 8) (char-code c))) s :initial-value 0))))
                      (cond ((is "char") (setf aff :text zchar next))
                            ((or (is "clob") (is "text")) (setf aff :text))
                            ((and (is "blob") (member aff '(:numeric :real)))
                             (setf aff :blob)
                             (when (and (< next n) (char= (char type next) #\()) (setf zchar next)))
                            ((and (member aff '(:numeric))
                                  (or (is "real") (is "floa") (is "doub")))
                             (setf aff :real))
                            ((= (logand h #xffffff) (reduce (lambda (a c) (+ (ash a 8) (char-code c))) "int" :initial-value 0))
                             (setf aff :integer)
                             (return))))))
         (let ((v 0))
           (when (member aff '(:text :blob))
             (if zchar
                 (let ((d (position-if #'digit-char-p type :start zchar)))
                   (when d (setf v (min (parse-integer type :start d :junk-allowed t) #x7fffffff))))
                 (setf v 16)))
           (min 255 (1+ (floor v 4)))))))))

(defun log-est (x)
  "sqlite3LogEst: 10*log2(X), roughly, as SQLite computes it."
  (let ((a #(0 2 3 5 6 7 8 9)) (y 40))
    (if (< x 8)
        (progn (when (< x 2) (return-from log-est 0))
               (loop while (< x 8) do (decf y 10) (setf x (ash x 1))))
        (let ((i (- (integer-length x) 4)))
          (incf y (* i 10))
          (setf x (ash x (- i)))))
    (+ (aref a (logand x 7)) y -10)))

(defun table-row-width (table)
  "estimateTableWidth: szTabRow."
  (log-est (* 4 (+ (loop for c across (table-columns table) sum (column-size-estimate (column-type c)))
                   (if (table-rowid-alias table) 0 1)))))

(defun index-row-width (table idx)
  "estimateIndexWidth: szIdxRow (the key columns and the rowid)."
  (let ((cols (table-columns table)))
    (log-est (* 4 (+ 1 (loop for (c) in (index-columns idx)
                             sum (if (integerp c) (column-size-estimate (column-type (aref cols c))) 1)))))))

(defun covering-index (table wanted &optional fs)
  "The index of a rowid table SQLite would scan instead of the table: one
holding every WANTED column whose estimated row is narrower than the
table's, the cheapest by SQLite's cost (rows + 1 + 15*szIdxRow/szTabRow),
the newest on ties; or NIL."
  (when (and wanted (not (table-without-rowid table)) (not (table-virtual-p table)))
    (let ((best nil) (best-cost nil) (tab-w (table-row-width table)))
      (dolist (idx (table-indexes table) best)
        (let ((cols (mapcar #'first (index-columns idx))))
          (when (and (null (index-where idx))
                     (or (null fs) (index-allowed-p fs idx))
                     (every #'integerp cols)
                     (loop for i below (length wanted)
                           always (or (zerop (sbit wanted i))
                                      (eql i (table-rowid-alias table))
                                      (member i cols))))
            (let ((w (index-row-width table idx)))
              ;; INDEXED BY forces the index, however wide
              (when (or (< w tab-w) (and fs (eq (fsrc-index-hint fs) idx)))
                (let ((cost (floor (* 15 w) tab-w)))
                  (when (or (null best) (<= cost best-cost))
                    (setf best idx best-cost cost)))))))))))

(defun order-term-source-column (e rcols scope)
  "The (depth-0) column of source 0 an ORDER BY term sorts by, or NIL."
  (let ((e (if (and (int32-literal-p e) (<= 1 (second e) (length rcols)))
               (first (nth (1- (second e)) rcols))
               e)))
    (when (and (eq (car e) :col) (null (second e)))
      (let ((a (alias-expr scope (third e))))
        (when (and a (not (resolve-column scope nil (third e)))) (setf e a))))
    (case (car e)
      (:srccol (and (= (second e) 0) (third e)))
      (:col (multiple-value-bind (depth si ci) (resolve-column scope (second e) (third e))
              (and depth (= depth 0) (= si 0) ci)))
      (t nil))))

(defun compute-order-hint (order rcols scope fsrcs)
  "Can the rows of this single-table query be produced in ORDER BY order?"
  (let* ((fs (first fsrcs))
         (table (and fs (null (cdr fsrcs)) (fsrc-table fs))))
    (when (and table order (or (not (table-vtab table)) (fts3-p (table-vtab table)) (dbstat-p (table-vtab table)))
               (every (lambda (o) (null (fourth o))) order))    ; default NULLS placement
      (let ((cols (mapcar (lambda (o) (order-term-source-column (first o) rcols scope)) order))
            (colls (mapcar (lambda (o)
                             (let ((c (third o)))
                               (if c (collation-keyword c)
                                   (or (expr-collation (first o) scope) :binary))))
                           order))
            (descs (mapcar #'second order)))
        (when (every #'identity cols)
          (cond
            ;; ORDER BY rowid
            ((and (null (cdr cols))
                  (not (table-without-rowid table))
                  (or (eq (first cols) :rowid) (eql (first cols) (table-rowid-alias table))
                      ;; an FTS3/4 table's docid (xBestIndex consumes ORDER BY docid)
                      (and (fts3-p (table-vtab table)) (eql (first cols) (- (length (table-columns table)) 2)))))
             (list :rowid (if (first descs) :desc :asc)))
            ;; dbstat returns rows ordered by (name, path)
            ((and (dbstat-p (table-vtab table)) (notany #'identity descs)
                  (or (equal cols '(0)) (equal cols '(0 1))))
             (list :dbstat))
            ((table-vtab table) nil)
            (t
             (dolist (idx (table-indexes table) nil)
               (let ((icols (index-columns idx)))
                 (when (and (null (index-where idx))
                            (<= (length cols) (length icols))
                            (loop for c in cols for coll in colls for (ic icoll) in icols
                                  always (and (eql c ic) (collation= coll icoll))))
                   (let ((flips (loop for d in descs for (nil nil idesc) in icols
                                      collect (if (eq (and d t) (and idesc t)) :same :flip))))
                     (when (or (every (lambda (f) (eq f :same)) flips)
                               (every (lambda (f) (eq f :flip)) flips))
                       (return (list :index idx (if (eq (first flips) :same) :asc :desc)))))))))))))))

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
         (and (nth-value 1 (find-sql-function name))
              (not (and (member name '("min" "max") :test #'string=)
                        (/= (length (third e)) 1)))))))

(defun contains-window-p (e)
  (labels ((walk (x)
             (and (consp x)
                  (or (eq (car x) :winfn)
                      (some #'walk (cdr x))))))
    (walk e)))

(defun contains-aggregate-p (e)
  (labels ((walk (x)
             (when (consp x)
               (case (car x)
                 ((:subquery :exists) nil)
                 (:in (or (walk (second x))
                          (and (eq (car (third x)) :list) (some #'walk (second (third x))))))
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
                            do (unless (and (null tname) (or (member ci (src-hidden s))
                                                             (member ci (src-star-hidden s))))
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
                      (when (member (fsrc-join fs) '(:right :full))
                        (push (cons (cons (first left) (second left)) (cons i ri))
                              (scope-coalesce scope)))
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
    ;; INNER/CROSS ON conditions behave as WHERE conjuncts, except that a
    ;; RIGHT/FULL JOIN does not delay them (they belong to its left side)
    (let ((inner-ons (loop for fs in fsrcs
                           for on in ons
                           unless (member (fsrc-join fs) '(:left :right :full))
                             append (split-conjuncts on))))
      (setf where-conjs (append (mapcar (lambda (c) (cons :where c)) where-conjs)
                                (mapcar (lambda (c) (cons :on c)) inner-ons))))
    (let ((placed (make-array (max n 1) :initial-element '()))
          ;; WHERE applies to the joined row: never before a RIGHT/FULL JOIN
          ;; has decided which of its rows matched
          (floor-level (or (position-if (lambda (fs) (member (fsrc-join fs) '(:right :full)))
                                        fsrcs :from-end t)
                           0)))
      (dolist (tagged where-conjs)
        (destructuring-bind (kind . c) tagged
          (if (zerop n)
              (push c finals)
              (push c (aref placed (max (if (eq kind :where) floor-level 0)
                                        (max-ref (expr-refs c scope) n)))))))
      (loop for fs in fsrcs
            for on in ons
            for i from 0
            do (let* ((outer (member (fsrc-join fs) '(:left :right :full)))
                      (left (member (fsrc-join fs) '(:left :full)))
                      (right (member (fsrc-join fs) '(:right :full)))
                      (match-asts (when outer (split-conjuncts on)))
                      (filter-asts (reverse (aref placed i)))
                      ;; conjuncts usable for choosing the access path: never
                      ;; WHERE terms for the inner table of a LEFT JOIN
                      (access-asts (cond (right nil) (left match-asts) (t filter-asts)))
                      (iterate (if (fsrc-table fs)
                                   (let ((*eqp-left* (and left t)))
                                     (plan-table-access fs i access-asts scope))
                                   (let ((rf (fsrc-rows-fn fs)))
                                     (let ((*eqp-left* (and left t)))
                                       (eqp-table-note (format nil "SCAN ~a" (or (fsrc-label fs)
                                                                                 (src-name (fsrc-src fs))
                                                                                 "(subquery)"))))
                                     (lambda (env fn)
                                       (let ((rows (funcall rf env)))
                                         ;; a streaming source hands over a mapper
                                         (if (functionp rows)
                                             (funcall rows fn)
                                             (dolist (row rows) (funcall fn row)))))))))
                 (push (make-level :index i :fsrc fs :iterate iterate :left-p (and left t)
                                   :right-p (and right t)
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
  (let ((materialized (make-hash-table :test #'eq)))
    ;; A RIGHT/FULL JOIN source is read once, so that the rows no earlier
    ;; row matched can be emitted at the end.
    (dolist (lv levels)
      (when (level-right-p lv)
        (let ((rows '()))
          (funcall (level-iterate lv) env (lambda (row) (push row rows)))
          (setf (gethash lv materialized)
                (cons (coerce (nreverse rows) 'vector)
                      (make-array (length rows) :initial-element nil))))))
    (labels ((run (lvs)
               (if (null lvs)
                   (funcall emit)
                   (let* ((lv (car lvs))
                          (i (level-index lv))
                          (rows (env-rows env))
                          (matched nil)
                          (mat (gethash lv materialized)))
                     (flet ((try (row k)
                              (setf (svref rows i) row)
                              (when (all-true (level-match lv) env)
                                (setf matched t)
                                (when k (setf (aref (cdr mat) k) t))
                                (when (all-true (level-filters lv) env)
                                  (run (cdr lvs))))))
                       (if mat
                           (loop for row across (car mat) for k from 0 do (try row k))
                           (funcall (level-iterate lv) env (lambda (row) (try row nil)))))
                     (when (and (level-left-p lv) (not matched))
                       (setf (svref rows i) (level-nullrow lv))
                       (when (all-true (level-filters lv) env)
                         (run (cdr lvs))))))))
      (run levels)
      ;; the unmatched rows of each RIGHT/FULL source, with every earlier
      ;; source NULL
      (loop for (lv . rest) on levels
            for mat = (gethash lv materialized)
            when mat
              do (loop for row across (car mat)
                       for hit across (cdr mat)
                       unless hit
                         do (let ((rows (env-rows env)))
                              (dolist (earlier levels)
                                (when (eq earlier lv) (return))
                                (setf (svref rows (level-index earlier)) (level-nullrow earlier)))
                              (setf (svref rows (level-index lv)) row)
                              (when (loop for x in levels
                                          always (all-true (level-filters x) env)
                                          until (eq x lv))
                                (run rest))))))))

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
  (let* ((fsrcs (let ((items (select-core-from core)))
                  (loop for item in items
                        for i from 0
                        collect (let ((*eqp-coroutine-ok*
                                        (and (zerop i)
                                             (or (null (cdr items))
                                                 (member (getf (second items) :join)
                                                         '(:left :right :full :cross))))))
                                  (make-fsrc-for item scope)))))
         (_0 (unless fsrcs (eqp-note "SCAN CONSTANT ROW")))
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
    (declare (ignore _ _0))
    (when (and having (not group) (not agg-p))
      (sql-error "a GROUP BY clause is required before HAVING"))
    (multiple-value-bind (levels finals order-done)
        (let ((*order-hint* (and (not agg-p) (not (select-core-distinct core))
                                 (not (select-core-windows core))
                                 (notany (lambda (rc) (contains-window-p (first rc))) rcols)
                                 (compute-order-hint order rcols cscope fsrcs)))
              (*minmax-hint* (and agg-p (minmax-candidate core rcols having order cscope fsrcs)))
              (*order-satisfied* nil))
          (multiple-value-bind (l f) (build-levels fsrcs cscope (select-core-where core) ons)
            (values l f *order-satisfied*)))
      (let* ((nsrc (length fsrcs))
             (columns (loop for (e name) in rcols
                            collect (list name (expr-affinity e cscope)
                                          (or (expr-collation e cscope) :binary))))
             ;; group-by expressions are compiled before switching to aggregate mode
             (group-fns (loop for g in group for k from 1
                              collect (compile-expr (resolve-group-term g rcols k) cscope)))
             (group-colls (mapcar (lambda (g) (or (expr-collation (resolve-group-term g rcols) cscope)
                                                  :binary))
                                  group))
             (_2 (progn
                   (when agg-p (setf (scope-agg-p cscope) t))
                   (setf (scope-windows cscope) (make-array 0 :adjustable t :fill-pointer t)
                         (scope-window-defs cscope) (select-core-windows core))))
             ;; EQP: subqueries evaluated per group come after GROUP BY
             (*eqp-rank* (if agg-p 4 2))
             (out-fns (mapcar (lambda (rc) (compile-expr (first rc) cscope)) rcols))
             (having-fn (and having (compile-expr having cscope)))
             (order-specs (compile-order-terms order rcols cscope))
             (distinct (select-core-distinct core))
             (out-colls (mapcar #'third columns))
             (aggs (coerce (scope-aggs cscope) 'list))
             (wins (scope-windows cscope)))
        (declare (ignore _2))
        (when *eqp*
          (when group
            (eqp-note (lambda ()
                        (unless (eqp-scan-order-p fsrcs (mapcar (lambda (g) (resolve-group-term g rcols)) group)
                                                  cscope)
                          "USE TEMP B-TREE FOR GROUP BY"))
                      +eqp-group+))
          (when distinct
            (eqp-note (lambda ()
                        (unless (eqp-scan-order-p fsrcs (mapcar #'first rcols) cscope :any-order t)
                          "USE TEMP B-TREE FOR DISTINCT"))
                      +eqp-distinct+))
          (when (and order-specs (not order-done)
                     ;; SELECT DISTINCT x ORDER BY x: SQLite turns it into a GROUP BY
                     (not (and distinct (not agg-p) (= (length order) (length rcols))
                               (loop for (e) in order for rc in rcols for spec in order-specs for i from 0
                                     always (or (eql (first spec) i) (equal e (first rc)))))))
            (eqp-note "USE TEMP B-TREE FOR ORDER BY" +eqp-order+)))
        (values
         (lambda (parent-env)
           (let* ((env (make-env :rows (make-array nsrc) :parent parent-env))
                  (lim (eval-limit limit parent-env))
                  (off (or (eval-limit offset parent-env) 0))
                  (lim (if limit-one 1 lim))
                  (results '())
                  (count 0)
                  (seen (and distinct (make-hash-table :test #'equal)))
                  (sorting (and order-specs (not order-done)))
                  (pending 0)
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
                              (progn
                                (push (cons (mapcar (lambda (spec)
                                                      (let ((f (first spec)))
                                                        (if (integerp f) (nth f row) (funcall f e))))
                                                    order-specs)
                                            row)
                                      results)
                                ;; ORDER BY ... LIMIT: keep only the best LIMIT+OFFSET
                                (when (and lim (> (incf pending) (+ 256 (* 2 (+ lim off)))))
                                  (let ((keep (+ lim off)))
                                    (setf results
                                          (reverse (let ((sorted (sort-rows (nreverse results)
                                                                            (mapcar #'cdr order-specs))))
                                                     (subseq sorted 0 (min keep (length sorted)))))
                                          pending 0))))
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

(defun count-index (table)
  "The index SQLite counts instead of a rowid table: the narrowest full
index by estimated row width, if narrower than the table (newest on ties),
or NIL."
  (unless (table-without-rowid table)
    (let ((best nil) (best-w nil) (tab-w (table-row-width table)))
      (dolist (idx (table-indexes table) best)
        (let ((w (index-row-width table idx)))
          (when (and (null (index-where idx)) (< w tab-w)
                     (or (null best) (<= w best-w)))
            (setf best idx best-w w)))))))

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
        (when (and table (not (table-view-select table)) (not (table-vtab table)))
          (let* ((c (first cols))
                 (idx (count-index table))
                 (root (if idx (index-root idx) (table-root table))))
            (eqp-note (format nil "SCAN ~a~@[ USING COVERING INDEX ~a~]"
                              (or (third (getf (first from) :source)) (table-name table))
                              (and idx (index-name idx))))
            (values (lambda (parent-env)
                      (declare (ignore parent-env))
                      ;; as SQLite: count the entries of the smallest index
                      (list (list (btree-count (table-owner table) root))))
                    (list (list (or (third c) (fourth c) "count(*)") nil :binary))
                    nil)))))))

(defun group-sort-key (g group-fns parent-env)
  (let ((e (make-env :rows (car g) :parent parent-env)))
    (mapcar (lambda (f) (funcall f e)) group-fns)))

(defun single-minmax-p (aggs)
  (and aggs (null (cdr aggs))
       (member (agg-name (car aggs)) '("min" "max") :test #'string=)))

(defun int32-literal-p (e)
  "sqlite3ExprIsInteger: an integer literal that fits in 32 bits."
  (and (eq (car e) :lit) (integerp (second e)) (<= -2147483648 (second e) 2147483647)))

(defun resolve-group-term (g rcols &optional (pos 1))
  "GROUP BY accepts result-column numbers.  POS is the term's place in the
GROUP BY list, for the error."
  (if (int32-literal-p g)
      (let ((k (second g)))
        (unless (<= 1 k (length rcols))
          (sql-error "~a GROUP BY term out of range - should be between 1 and ~d"
                     (ordinal pos) (length rcols)))
        (first (nth (1- k) rcols)))
      g))

(defun eqp-scan-order-p (fsrcs exprs scope &key any-order)
  "EQP: does the single table's full scan deliver rows ordered (grouped) by
EXPRS, so that SQLite would need no temp b-tree?"
  (let ((fs (first fsrcs)))
    (when (and fs (null (cdr fsrcs)) (fsrc-table fs) (fsrc-scan-index fs))
      (let* ((table (fsrc-table fs))
             (cols (mapcar (lambda (e)
                             (case (car e)
                               (:srccol (and (= (second e) 0) (third e)))
                               (:col (multiple-value-bind (depth si ci) (resolve-column scope (second e) (third e))
                                       (and depth (= depth 0) (= si 0) ci)))))
                           exprs))
             (idx (funcall (fsrc-scan-index fs))))
        (when (every #'identity cols)
          (let ((cols (mapcar (lambda (c) (if (eql c (table-rowid-alias table)) :rowid c)) cols)))
            (cond ((eq idx :rowid) (member :rowid cols))
                  ((index-p idx)
                   (let ((icols (mapcar #'first (index-columns idx))))
                     (and (<= (length cols) (length icols))
                          (if any-order
                              (subsetp (subseq icols 0 (length cols)) cols)
                              (equal (subseq icols 0 (length cols)) cols))))))))))))

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
  (cond ((int32-literal-p e)
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
    (eqp-note (if (cdr rows) (format nil "SCAN ~d CONSTANT ROWS" (length rows)) "SCAN CONSTANT ROW"))
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

(defun materialize-cte (cte &optional emit)
  "Compute CTE's rows.  A recursive CTE may EMIT each row as it is made."
  (let ((sel (cte-sel cte))
        (*ctes* (cons (cons (cte-name cte) cte) (cte-env cte))))
    (if (not (and (cte-recursive-rows cte) (eq (cte-recursive-rows cte) :recursive)))
        (multiple-value-bind (fn cols) (compile-select sel (make-scope))
          (unless (cte-columns cte) (setf (cte-columns cte) (mapcar #'first cols)))
          (setf (cte-rows cte) (rows-to-vectors (funcall fn nil))
                (cte-done cte) t))
        (run-recursive-cte cte emit))))

(defun run-recursive-cte (cte &optional emit)
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
          (let ((finished nil))
            (unwind-protect
                 (progn
                   (catch :cte-done
                     (loop while queue
                           do (let ((row (pop queue)))
                                (push row all)
                                (incf count)
                                (when emit
                                  ;; the outer scan runs while this row is current;
                                  ;; a reference it makes to the CTE is not the
                                  ;; recursive step's
                                  (setf (cte-done cte) :streaming)
                                  (funcall emit (first (rows-to-vectors (list row))))
                                  (setf (cte-done cte) :working))
                                (when (and limit (>= limit 0) (>= count limit)) (throw :cte-done nil))
                                (setf (cte-recursive-rows cte) (rows-to-vectors (list row)))
                                (setf queue (append queue (admit (funcall recur-fn nil)))))))
                   (setf finished t))
              (if finished
                  (setf (cte-rows cte) (rows-to-vectors (nreverse all))
                        (cte-done cte) t)
                  ;; the outer scan stopped early: nothing is cached
                  (setf (cte-done cte) nil (cte-rows cte) nil)))))))))

(defun register-ctes (sel)
  "Push this SELECT's WITH clause onto *CTES*."
  (let ((*eqp* nil))
    (register-ctes-1 sel)))

(defun register-ctes-1 (sel)
  (dolist (w (sel-with sel))
    (destructuring-bind (name cols csel) w
      (let ((cte (make-cte :name name :columns cols :declared cols :sel csel :env *ctes*)))
        ;; resolveFromTermToCte: RECURSIVE is optional; a CTE recurses when it
        ;; is a UNION [ALL] whose last term names it directly in its FROM, and
        ;; any other reference to itself is an error (raised only if used)
        (let* ((cores (sel-cores csel))
               (last-core (car (last cores)))
               (direct (and (sel-ops csel)
                            (member (car (last (sel-ops csel))) '(:union :union-all))
                            (select-core-p last-core)
                            (count-if (lambda (item)
                                        (let ((s (getf item :source)))
                                          (and (eq (car s) :table) (stringp (second s))
                                               (null (fourth s)) (name= (second s) name))))
                                      (select-core-from last-core)))))
          (cond ((and direct (> direct 1))
                 (setf (cte-error cte) "multiple references to recursive table: ~a"))
                ((and direct (= direct 1))
                 (cond ((some (lambda (c) (plusp (cte-self-references c name))) (butlast cores))
                        (setf (cte-error cte) "circular reference: ~a"))
                       ((> (cte-self-references last-core name) 1)
                        (setf (cte-error cte) "multiple recursive references: ~a"))))
                ((plusp (cte-self-references csel name))
                 (setf (cte-error cte) "circular reference: ~a"))))
        (when (and (null (cte-error cte)) (cte-references-self-p csel name))
          (setf (cte-recursive-rows cte) :recursive)
          ;; recursive CTEs need their column names up front
          (unless cols
            (let ((*ctes* *ctes*))
              (multiple-value-bind (fn c)
                  (compile-select (make-sel :cores (list (first (sel-cores csel)))) (make-scope))
                (declare (ignore fn))
                (setf (cte-columns cte) (mapcar #'first c))))))
        (unless (or (cte-columns cte) (cte-error cte))
          (let ((*ctes* *ctes*))
            (multiple-value-bind (fn c) (compile-select csel (make-scope))
              (declare (ignore fn))
              (setf (cte-columns cte) (mapcar #'first c)
                    (cte-affinities cte) (mapcar #'second c)))))
        (push (cons name cte) *ctes*)))))

(defun cte-self-references (x name)
  "How many times X (a SELECT, a core, or an AST) names table NAME,
unqualified, at any depth."
  (cond ((sel-p x) (reduce #'+ (sel-cores x) :key (lambda (c) (cte-self-references c name))))
        ((select-core-p x)
         (+ (reduce #'+ (select-core-from x) :key (lambda (c) (cte-self-references c name)))
            (cte-self-references (select-core-where x) name)
            (cte-self-references (select-core-group x) name)
            (cte-self-references (select-core-having x) name)
            (reduce #'+ (select-core-cols x) :key (lambda (c) (cte-self-references c name)))))
        ((consp x)
         (if (and (eq (car x) :table) (stringp (second x)) (name= (second x) name)
                  (consp (cdr x)) (consp (cddr x)) (null (fourth x)))
             1
             (+ (cte-self-references (car x) name) (cte-self-references (cdr x) name))))
        (t 0)))

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
  (let* ((compiled (with-eqp-node ("COMPOUND QUERY")
                     (loop for core in (sel-cores sel)
                           for op in (cons nil (sel-ops sel))
                           collect (with-eqp-node ((if op
                                                       (ecase op
                                                         (:union-all "UNION ALL")
                                                         (:union "UNION USING TEMP B-TREE")
                                                         (:intersect "INTERSECT USING TEMP B-TREE")
                                                         (:except "EXCEPT USING TEMP B-TREE"))
                                                       "LEFT-MOST SUBQUERY"))
                                     (multiple-value-list (compile-core core scope))))))
         (_ (when (sel-order sel) (eqp-note "USE TEMP B-TREE FOR ORDER BY" +eqp-order+)))
         (cols (second (first compiled)))
         (n (length cols))
         (colls (mapcar #'third cols))
         (correlated (some (lambda (c) (and (third c) (scope-outer-ref (third c)))) compiled)))
    (declare (ignore _))
    (dolist (c compiled)
      (unless (= (length (second c)) n)
        (sql-error "SELECTs to the left and right of ~a do not have the same number of result columns"
                   (case (first (sel-ops sel)) (:union-all "UNION ALL") (:union "UNION")
                         (:intersect "INTERSECT") (t "EXCEPT")))))
    (let ((order (loop for (e desc coll nulls) in (sel-order sel)
                       collect (let ((idx (cond ((int32-literal-p e)
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
                        (:union (setf rows (union-rows rows next colls (and order t))
                                      distinct-sorted t))
                        (:intersect
                         (let ((h (make-hash-table :test #'equal)))
                           (dolist (r next) (setf (gethash (group-key r colls) h) t))
                           (setf rows (dedupe-rows (remove-if-not (lambda (r) (gethash (group-key r colls) h)) rows)
                                                   colls (if order :first :last))
                                 distinct-sorted t)))
                        (:except
                         (let ((h (make-hash-table :test #'equal)))
                           (dolist (r next) (setf (gethash (group-key r colls) h) t))
                           (setf rows (dedupe-rows (remove-if (lambda (r) (gethash (group-key r colls) h)) rows)
                                                   colls (if order :first :last))
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

(defun dedupe-rows (rows colls &optional (keep :first))
  "One row per distinct key, in first-appearance order; KEEP says whether
the :first or :last of a set of equal rows (say 0 and 0.0) survives."
  (let ((h (make-hash-table :test #'equal)) (order '()))
    (dolist (r rows)
      (let ((k (group-key r colls)))
        (if (nth-value 1 (gethash k h))
            (when (eq keep :last) (setf (gethash k h) r))
            (progn (push k order) (setf (gethash k h) r)))))
    (mapcar (lambda (k) (gethash k h)) (nreverse order))))

(defun union-rows (left right colls merge)
  "UNION.  With ORDER BY SQLite merges two sorted streams and, for equal
keys, emits the right operand's (first) row; otherwise it inserts every
row into an ephemeral index, where the last equal row wins."
  (if (not merge)
      (dedupe-rows (append left right) colls :last)
      (let ((rh (make-hash-table :test #'equal)))
        (dolist (r (dedupe-rows right colls)) (setf (gethash (group-key r colls) rh) r))
        (let ((out (mapcar (lambda (r) (or (gethash (group-key r colls) rh) r))
                           (dedupe-rows left colls)))
              (seen (make-hash-table :test #'equal)))
          (dolist (r out) (setf (gethash (group-key r colls) seen) t))
          (append out (remove-if (lambda (r) (gethash (group-key r colls) seen))
                                 (dedupe-rows right colls)))))))

(defun select-first-affinity (sel scope)
  (without-eqp (select-first-affinity-1 sel scope)))

(defun select-first-affinity-1 (sel scope)
  (ignore-errors
   (let ((core (first (sel-cores sel))))
     (when (and (select-core-p core) (eq (car (first (select-core-cols core))) :expr))
       (let ((*ctes* *ctes*))
         (register-ctes sel)
         (let* ((fsrcs (mapcar (lambda (item) (make-fsrc-for item scope)) (select-core-from core)))
                (cscope (make-scope :srcs (mapcar #'fsrc-src fsrcs) :parent scope)))
           (expr-affinity (second (first (select-core-cols core))) cscope)))))))

(defun select-first-collation (sel scope)
  (without-eqp (select-first-collation-1 sel scope)))

(defun select-first-collation-1 (sel scope)
  (ignore-errors
   (let ((core (first (sel-cores sel))))
     (when (and (select-core-p core) (eq (car (first (select-core-cols core))) :expr))
       (let ((*ctes* *ctes*))
         (register-ctes sel)
         (let* ((fsrcs (mapcar (lambda (item) (make-fsrc-for item scope)) (select-core-from core)))
                (cscope (make-scope :srcs (mapcar #'fsrc-src fsrcs) :parent scope)))
           (expr-collation (second (first (select-core-cols core))) cscope)))))))
