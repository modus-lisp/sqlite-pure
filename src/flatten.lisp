;;;; flatten.lisp — the query flattener (flattenSubquery in SQLite's select.c).
;;;;
;;;; A subquery or view in FROM that satisfies SQLite's restrictions is merged
;;;; into the query that uses it: its FROM items take its place in the outer
;;;; FROM list, its WHERE clause is ANDed in front of the outer one (as part
;;;; of the ON clause when it is the right side of a LEFT JOIN), and every
;;;; outer reference to one of its columns becomes a copy of the expression
;;;; that computes that column.  The planner then sees the inner tables
;;;; directly, as SQLite's does, and the merged items may be flattened in
;;;; turn.
;;;;
;;;; The merged items keep their names for EXPLAIN QUERY PLAN but are
;;;; renamed, for column resolution, to an internal alias no SQL can spell,
;;;; and are invisible to unqualified names: the only references to them
;;;; are the rewritten expressions, qualified with that alias.
;;;;
;;;; A subquery is left alone (run as a co-routine or materialized, as
;;;; before) when SQLite would not flatten it, and also when it or the
;;;; query using it has something this rewrite does not handle yet: a
;;;; compound, LIMIT, an ORDER BY that must be kept, outer joins or USING /
;;;; NATURAL inside it, a CTE, subqueries in its expressions or the outer
;;;; query's, or a column it cannot name without compiling.

(in-package #:sqlite-pure)

(defvar *flatten-counter* 0)

(defun flatten-tag ()
  (format nil "~c~d" (code-char 1) (incf *flatten-counter*)))

(defun expr-has-select-p (e)
  "Does E contain a subquery (scalar, EXISTS or IN)?"
  (and (consp e)
       (or (member (car e) '(:subquery :exists))
           (and (eq (car e) :in) (consp (third e)) (eq (car (third e)) :select))
           (some #'expr-has-select-p (cdr e)))))

(defun map-cols (fn e)
  "E with every (:col q n) node replaced by (FN node); FN returns the
replacement or the node itself.  Subqueries are not entered."
  (cond ((atom e) e)
        ((eq (car e) :col) (funcall fn e))
        ((member (car e) '(:subquery :exists)) e)
        (t (let ((new (mapcar (lambda (x) (map-cols fn x)) e)))
             (if (every #'eq new e) e new)))))

;;; ------------------------------------------------------------------
;;; What a FROM item's columns are, without compiling it

(defun item-name (item)
  "The name an item is qualified by, or NIL."
  (let ((source (getf item :source)))
    (case (car source)
      (:table (or (third source) (second source)))
      (:subquery (third source))
      (:tvf (fourth source))
      (t nil))))

(defun item-cte (item)
  (let ((source (getf item :source)))
    (and (eq (car source) :table) (null (fourth source))
         (cdr (assoc (second source) *ctes* :test #'name=)))))

(defun item-view (item)
  "The view ITEM names, if it names one (and not a CTE)."
  (let ((source (getf item :source)))
    (and (eq (car source) :table)
         (not (item-cte item))
         (let ((tb (lookup-table *db* (second source) nil (fourth source))))
           (and tb (table-view-select tb) tb)))))

(defun item-src (item)
  "A SRC with ITEM's column names and collations, made without compiling
it, or NIL when that cannot be known."
  (when (or (getf item :using) (getf item :natural)) (return-from item-src nil))
  (let* ((source (getf item :source))
         (s (case (car source)
              (:table
               (destructuring-bind (name alias &optional schema hint) (cdr source)
                 (declare (ignore hint))
                 (let ((label (or alias name)))
                   (cond ((item-cte item) nil)
                         (t (let ((tb (lookup-table *db* name nil schema)))
                              (cond ((null tb) nil)
                                    ((table-view-select tb)
                                     (let ((info (let ((*ctes* '())) (sel-column-info (table-view-select tb))))
                                           (names (table-view-columns tb)))
                                       (when (and info (or (null names) (= (length names) (length info))))
                                         (derived-src label (or names (mapcar #'car info))
                                                      (mapcar (constantly nil) info) (mapcar #'cdr info)))))
                                    (t (make-table-src tb label)))))))))
              (:subquery (let ((info (sel-column-info (second source))))
                           (and info (derived-src (third source) (mapcar #'car info)
                                                  (mapcar (constantly nil) info) (mapcar #'cdr info)))))
              (t nil))))
    (when (and s (getf item :invisible)) (setf (src-invisible s) t))
    s))

(defun resolve-in-items (q n items srcs)
  "Where column N (qualified by Q) of ITEMS is: (values k ci), K the item
and CI the column index or :ROWID; :AMBIGUOUS, or NIL."
  (let ((hits '()))
    (loop for it in items for s in srcs for k from 0
          do (when (if q (and (item-name it) (name= q (item-name it))) (not (src-invisible s)))
               (let ((ci (position n (src-columns s) :test #'name=)))
                 (cond (ci (push (cons k ci) hits))
                       ((and (rowid-name-p n) (src-rowid-p s) (or q (null (cdr items))))
                        (push (cons k :rowid) hits))))))
    (cond ((null hits) nil)
          ((cdr hits) :ambiguous)
          (t (values (car (first hits)) (cdr (first hits)))))))

(defun star-columns (q items srcs)
  "(k . column-name) for each column a * (qualified by Q) stands for, or
:UNKNOWN."
  (let ((out '()) (any nil))
    (loop for it in items for s in srcs for k from 0
          do (when (if q (and (item-name it) (name= q (item-name it))) (not (src-invisible s)))
               (setf any t)
               (loop for name across (src-columns s) for ci from 0
                     unless (and (null q) (member ci (src-star-hidden s)))
                       do (push (cons k name) out))))
    (if any (nreverse out) :unknown)))

(defun sel-column-info (sel)
  "For each result column of SEL's first SELECT: (name . collation), or
NIL when they cannot be known without compiling it."
  (let ((core (first (sel-cores sel))))
    (unless (select-core-p core) (return-from sel-column-info nil))
    (let* ((items (select-core-from core))
           (srcs (loop for it in items collect (or (item-src it) (return-from sel-column-info nil))))
           (out '()))
      (dolist (c (select-core-cols core)
                 (let ((out (nreverse out)))
                   (mapcar #'cons (dedupe-names (mapcar #'car out)) (mapcar #'cdr out))))
        (ecase (car c)
          (:star (let ((cols (star-columns (second c) items srcs)))
                   (when (eq cols :unknown) (return-from sel-column-info nil))
                   (loop for (k . name) in cols
                         do (let* ((s (nth k srcs)) (ci (position name (src-columns s) :test #'name=)))
                              (push (cons name (svref (src-collations s) ci)) out)))))
          (:expr (destructuring-bind (e alias text &optional name) (cdr c)
                   (push (cons (or alias name (column-expr-name e items srcs) text
                                   (return-from sel-column-info nil))
                               (column-expr-collation e items srcs))
                         out))))))))

(defun column-expr-name (e items srcs)
  "RESULT-COLUMN-NAME for a column reference: its declared name."
  (when (eq (car e) :col)
    (multiple-value-bind (k ci) (resolve-in-items (second e) (third e) items srcs)
      (cond ((and (integerp k) (integerp ci)) (svref (src-columns (nth k srcs)) ci))
            (t nil)))))

(defun column-expr-collation (e items srcs)
  "The collation a result column has: its expression's, or BINARY."
  (case (car e)
    (:icollate (third e))
    (:collate (collation-keyword (third e)))
    (:col (multiple-value-bind (k ci) (resolve-in-items (second e) (third e) items srcs)
            (if (and (integerp k) (integerp ci))
                (svref (src-collations (nth k srcs)) ci)
                :binary)))
    (t :binary)))

;;; ------------------------------------------------------------------
;;; The flattener

(defun outer-aggregate-names (exprs)
  (let ((out '()))
    (labels ((walk (x)
               (when (consp x)
                 (case (car x)
                   ((:subquery :exists) nil)
                   (:fn (when (aggregate-call-p x) (push (string-downcase-ascii (second x)) out))
                    (mapc #'walk (cdr x)))
                   (t (mapc #'walk (cdr x)))))))
      (mapc #'walk exprs))
    out))

(defun left-join-simplifies-p (core i)
  "The LEFT JOIN simplification sqlite3Select makes as it walks the FROM
clause, before it tries to flatten item I: can the WHERE clause (with the
inner joins' ON clauses) be true only if item I's row is not the NULL row?"
  (let* ((items (select-core-from core))
         (srcs (loop for it in items collect (or (item-src it) (return-from left-join-simplifies-p nil))))
         (scope (make-scope :srcs srcs))
         (cond (select-core-where core)))
    (loop for it in items
          do (when (and (getf it :on) (not (member (getf it :join) '(:left :right :full))))
               (setf cond (if cond (list :binary :and cond (getf it :on)) (getf it :on)))))
    (ignore-errors (implies-non-null-row-p cond i scope))))

(defun flatten-subqueries (core order &optional limit)
  "Apply the flattener to CORE's FROM items until none applies, then the
LEFT JOIN simplification SQLite's flattening loop makes on every item (so
it is known before sources are compiled).  Returns (values core order
limit): a subquery's LIMIT (and ORDER BY) can become the outer query's."
  (loop
    (multiple-value-bind (new-core new-order new-limit) (flatten-one core order limit)
      (if new-core
          (setf core new-core order new-order limit new-limit)
          (return))))
  (loop for i from 1 below (length (select-core-from core))
        do (when (and (eq (getf (nth i (select-core-from core)) :join) :left)
                      (left-join-simplifies-p core i))
             (let ((items (copy-list (select-core-from core)))
                   (c (copy-list (nth i (select-core-from core)))))
               (setf (getf c :was-left) t (getf c :join) :inner
                     (nth i items) c
                     core (let ((k (copy-select-core core))) (setf (select-core-from k) items) k)))))
  (values core order limit))

(defun flatten-one (core order limit)
  "Flatten the first FROM subquery of CORE that can be; NIL if none."
  (loop for i from 0 below (length (select-core-from core))
        do (let ((r (multiple-value-list (try-flatten core order i limit))))
             (when (first r) (return-from flatten-one (values-list r)))))
  nil)

(defun expand-outer-stars (core)
  "CORE with each * in its result list written out as the columns it
stands for (SQLite expands them before it flattens), or NIL."
  (let* ((items (select-core-from core))
         (srcs (loop for it in items collect (or (item-src it) (return-from expand-outer-stars nil)))))
    (let ((cols (loop for c in (select-core-cols core)
                      append (if (eq (car c) :star)
                                 (let ((cols (star-columns (second c) items srcs)))
                                   (when (eq cols :unknown) (return-from expand-outer-stars nil))
                                   (loop for (k . name) in cols
                                         collect (let ((q (item-name (nth k items))))
                                                   (unless q (return-from expand-outer-stars nil))
                                                   (list :expr (list :col q name) nil nil name))))
                                 (list c)))))
      (let ((k (copy-select-core core))) (setf (select-core-cols k) cols) k))))

(defun try-flatten (core order i limit)
  (let* ((items (select-core-from core))
         (item (nth i items))
         (source (getf item :source))
         (view (item-view item))
         (sel (cond ((eq (car source) :subquery) (second source))
                    ((and view (null (fourth source))) (table-view-select view))
                    (t (return-from try-flatten nil)))))
    (flet ((no () (return-from try-flatten nil)))
      (let ((sub (and (null (sel-ops sel)) (null (sel-with sel)) (first (sel-cores sel)))))
        ;; the subquery itself
        (unless (and (select-core-p sub)
                     (select-core-from sub)                     ; (7)
                     (not (select-core-distinct sub))           ; (4)
                     (null (select-core-group sub))             ; aggregate
                     (null (select-core-having sub))
                     (null (select-core-windows sub))           ; (25)
                     (null (sel-offset sel)))                   ; (14)
          (no))
        (when (some (lambda (c) (and (eq (car c) :expr)
                                     (or (contains-aggregate-p (second c))
                                         (contains-window-p (second c))
                                         (expr-has-select-p (second c)))))
                    (select-core-cols sub))
          (no))
        (when (or (expr-has-select-p (select-core-where sub))
                  (some (lambda (it) (expr-has-select-p (getf it :on))) (select-core-from sub)))
          (no))
        (when (some (lambda (it) (not (member (getf it :join) '(:first :inner :comma :cross :left))))
                    (select-core-from sub))
          (no))
        ;; the LEFT JOIN simplification sqlite3Select makes before it tries
        (when (and (eq (getf item :join) :left) (left-join-simplifies-p core i))
          (let ((c (copy-list item)))
            (setf (getf c :was-left) t (getf c :join) :inner item c
                  items (append (subseq items 0 i) (list c) (nthcdr (1+ i) items))
                  core (let ((k (copy-select-core core))) (setf (select-core-from k) items) k))))
        (let* ((outer-cols (select-core-cols core))
               (outer-exprs (append (loop for c in outer-cols when (eq (car c) :expr) collect (second c))
                                    (list (select-core-where core) (select-core-having core))
                                    (select-core-group core)
                                    (mapcar #'first order)
                                    (loop for it in items collect (getf it :on)))))
          ;; its ORDER BY: dropped when it does nothing; else it becomes
          ;; the outer query's.  Either way SQLite has resolved it first.
          (when (sel-order sel)
            (check-order-by-names (sel-order sel) sub (sel-column-info sel)))
          (let ((agg-p (or (select-core-group core) (select-core-having core)
                           (some #'contains-aggregate-p outer-exprs))))
            ;; its LIMIT becomes the outer query's
            (when (and (sel-limit sel)
                       (or limit *core-in-compound*                 ; (13), (15)
                           (cdr items) agg-p                        ; (8), (9)
                           (select-core-where core)                 ; (19)
                           (select-core-distinct core)))            ; (21)
              (no))
            (when (sel-order sel)
              (if (and (or order (cdr items))
                       (null (sel-limit sel))
                       (every (lambda (n) (member n '("count" "min" "max") :test #'string=))
                              (outer-aggregate-names outer-exprs)))
                  (setf sel (let ((c (copy-sel sel))) (setf (sel-order c) nil) c))
                  (progn
                    (when (or order agg-p) (no))                  ; (11), (16)
                    ;; SF_ComplexResult: keep a co-routine that runs an
                    ;; expensive result set on its rows only
                    (when (and (zerop i)
                               (some (lambda (c) (and (eq (car c) :expr) (expr-has-function-p (second c))))
                                     outer-cols)
                               (or (null (cdr items))
                                   (member (getf (second items) :join) '(:left :right :full :cross))))
                      (no))))))
          ;; the outer query
          (when (or (select-core-windows core) (some #'contains-window-p outer-exprs)) (no))  ; (25)
          (when (some #'expr-has-select-p outer-exprs) (no))
          (when (member (getf item :join) '(:right :full)) (no))                   ; (26)
          (when (some (lambda (it) (member (getf it :join) '(:right :full))) (nthcdr (1+ i) items))
            (no))                                                                   ; LTORJ, (3)
          (when (eq (getf item :join) :left)                                       ; (3)
            (unless (and (null (cdr (select-core-from sub)))                        ; (3a)
                         (let ((it (first (select-core-from sub))))
                           (not (and (eq (car (getf it :source)) :table)          ; (3b)
                                     (let ((tb (lookup-table *db* (second (getf it :source)) nil
                                                             (fourth (getf it :source)))))
                                       (and tb (table-vtab tb))))))
                         (not (select-core-distinct core)))                        ; (3d)
              (no)))
          (when (some (lambda (it) (or (getf it :using) (getf it :natural))) (nthcdr i items))
            (no))
          (when (some (lambda (c) (eq (car c) :star)) outer-cols)
            ;; an unnamed subquery gets a name its * columns can use
            (when (and (eq (car source) :subquery) (null (third source)))
              (let ((c (copy-list item)))
                (setf source (list :subquery sel (flatten-tag))
                      (getf c :source) source
                      item c
                      items (append (subseq items 0 i) (list c) (nthcdr (1+ i) items))
                      core (let ((k (copy-select-core core))) (setf (select-core-from k) items) k))))
            (setf core (or (expand-outer-stars core) (no))))
          (let ((r (multiple-value-list
                    (if view
                        ;; a view's own names are not the outer query's CTEs:
                        ;; merged into the outer query, a table the view names
                        ;; must not be taken for one
                        (let ((*ctes* (progn
                                        (when (some (lambda (it)
                                                      (let ((src (getf it :source)))
                                                        (and (eq (car src) :table) (null (fourth src))
                                                             (assoc (second src) *ctes* :test #'name=))))
                                                    (select-core-from sub))
                                          (no))
                                        '())))
                          (build-flattened core order i sel sub (or (third source) (second source))
                                           (table-view-columns view) t limit))
                        (build-flattened core order i sel sub (third source) nil nil limit)))))
            (values-list r)))))))

(defun build-flattened (core order i sel sub alias rename view-p limit)
  (let* ((items (select-core-from core))
         (item (nth i items))
         (sub-items (select-core-from sub))
         (sub-srcs (loop for it in sub-items collect (or (item-src it) (return-from build-flattened nil))))
         (tags (loop repeat (length sub-items) collect (flatten-tag)))
         (info (sel-column-info sel))
         (sub-names (and info (or rename (mapcar #'car info)))))
    (flet ((no () (return-from build-flattened nil)))
      (unless (and info (= (length sub-names) (length info))) (no))
      (when (and view-p (some #'item-cte sub-items)) (no))
      (labels ((inner-ref (e)
                 ;; an inner column, qualified with its item's internal alias
                 (multiple-value-bind (k ci) (resolve-in-items (second e) (third e) sub-items sub-srcs)
                   (declare (ignore ci))
                   (if (integerp k)
                       (list :col (nth k tags) (third e))
                       (no))))              ; correlated, an alias, or an error: leave it
               (fix (e) (and e (map-cols #'inner-ref e))))
        (let* ((sub-exprs
                 (loop for c in (select-core-cols sub)
                       append (if (eq (car c) :star)
                                  (loop for (k . name) in (star-columns (second c) sub-items sub-srcs)
                                        collect (list :col (nth k tags) name))
                                  (list (fix (second c))))))
               (sub-colls (mapcar #'cdr info))
               (sub-where (fix (select-core-where sub)))
               (other-items (append (subseq items 0 i) (nthcdr (1+ i) items)))
               (aliases (loop for c in (select-core-cols core)
                              when (and (eq (car c) :expr) (third c)) collect (third c))))
          (unless (= (length sub-exprs) (length sub-names)) (no))
          (labels ((sub-index (n) (position n sub-names :test #'name=))
                   (replacement (k)
                     ;; a fresh copy each time (sqlite3ExprDup): nodes are
                     ;; told apart by identity (constant propagation)
                     (let ((e (copy-tree (nth k sub-exprs))))
                       ;; the column's collation stays implicit, as it was;
                       ;; :SUBST: it was resolved as a subquery column
                       (if (eq (car e) :col)
                           (list :col (second e) (third e) :subst)
                           (list :icollate
                                 ;; the right side of a LEFT JOIN: NULL when unmatched
                                 (if (eq (getf item :join) :left) (list :ifnullrow (first tags) e) e)
                                 (nth k sub-colls)))))
                   (outer-ref (e &optional top-group)
                     (destructuring-bind (q n &rest more) (cdr e)
                       (declare (ignore more))
                       (cond
                         (q (if (and alias (name= q alias))
                                (let ((k (sub-index n)))
                                  (if k (replacement k) e))
                                e))
                         ((or (not (sub-index n)) (getf item :invisible)) e)
                         ;; a bare ORDER BY / GROUP BY name that is a result alias
                         ((and top-group (member n aliases :test #'name=)) e)
                         (t
                          (dolist (it other-items)
                            (let ((s (item-src it)))
                              (when (or (null s)
                                        (and (not (src-invisible s))
                                             (position n (src-columns s) :test #'name=)))
                                (no))))   ; unknown, or ambiguous
                          (replacement (sub-index n))))))
                   (outer (e) (and e (retag-outer-on (map-cols #'outer-ref e))))
                   (retag-outer-on (e)
                     ;; an ON term of this item (moved into WHERE when an
                     ;; enclosing flattening merged it) now belongs to the
                     ;; first of the items that replace it
                     (cond ((atom e) e)
                           ((and (eq (car e) :outer-on) alias (equal (second e) alias))
                            (list :outer-on (first tags) (retag-outer-on (third e))))
                           ((member (car e) '(:subquery :exists)) e)
                           (t (let ((new (mapcar #'retag-outer-on e)))
                                (if (every #'eq new e) e new)))))
                   (outer-top (e)
                     (if (and (consp e) (eq (car e) :col) (null (second e)))
                         (outer-ref e t)
                         (outer e))))
            (let* ((new-cols
                     (loop for c in (select-core-cols core)
                           collect (destructuring-bind (kind e al text &optional name) c
                                     ;; the result keeps the name it had
                                     (let ((name (or name
                                                     (and (null al) (eq (car e) :col)
                                                          (or (null (second e))
                                                              (and alias (name= (second e) alias)))
                                                          (let ((k (sub-index (third e))))
                                                            (and k (nth k sub-names)))))))
                                       (list kind (outer e) al text name)))))
                   (sub-where (if (and sub-where (eq (getf item :join) :left))
                                  ;; part of the LEFT JOIN's ON clause
                                  (list :outer-on (first tags) sub-where)
                                  sub-where))
                   ;; the subquery's own ON clauses: SQLite has moved them into its
                   ;; WHERE clause, after its terms (a LEFT JOIN's still marked)
                   (sub-where (let ((w sub-where))
                                (loop for it in (rest sub-items)
                                      for tag in (rest tags)
                                      do (let ((on (fix (getf it :on))))
                                           (when on
                                             (let ((term (if (eq (getf it :join) :left)
                                                             (list :outer-on tag on)
                                                             on)))
                                               (setf w (if w (list :binary :and w term) term))))))
                                w))
                   (new-where (let ((w (outer (select-core-where core))))
                                (cond ((and sub-where w) (list :binary :and sub-where w))
                                      (t (or sub-where w)))))
                   (spliced
                     (loop for it in sub-items
                           for tag in tags
                           for k from 0
                           collect (let ((source (getf it :source)))
                                     (list :source (ecase (car source)
                                                     (:table (list* :table (second source) tag
                                                                    (cdddr source)))
                                                     (:subquery (list :subquery (second source) tag)))
                                           :join (if (zerop k) (getf item :join) (getf it :join))
                                           ;; the subquery's own ON clauses went into WHERE
                                           :on (if (zerop k) (outer (getf item :on)) nil)
                                           :display (or (getf it :display) (item-name it))
                                           :invisible t))))
                   (new-items (append (subseq items 0 i)
                                      spliced
                                      (mapcar (lambda (it)
                                                (if (getf it :on)
                                                    (let ((c (copy-list it)))
                                                      (setf (getf c :on) (outer (getf it :on)))
                                                      c)
                                                    it))
                                              (nthcdr (1+ i) items)))))
              (values (make-select-core :distinct (select-core-distinct core)
                                        :cols new-cols
                                        :from new-items
                                        :where new-where
                                        :group (mapcar #'outer-top (select-core-group core))
                                        :having (outer (select-core-having core))
                                        :windows (select-core-windows core))
                      (if (sel-order sel)
                          ;; the subquery's ORDER BY, now the outer query's
                          (loop for (e . rest) in (sel-order sel)
                                collect (cons (let ((k (cond ((int32-literal-p e) (1- (second e)))
                                                             ((and (eq (car e) :col) (null (second e)))
                                                              (position (third e) (select-core-cols sub)
                                                                        :key (lambda (c) (and (eq (car c) :expr) (third c)))
                                                                        :test #'equal-name-or-nil)))))
                                                (if (and k (< -1 k (length sub-exprs)))
                                                    (copy-tree (nth k sub-exprs))
                                                    (fix e)))
                                              rest))
                          (mapcar (lambda (o) (cons (outer-top (first o)) (rest o))) order))
                      (or limit (sel-limit sel))))))))))

(defun equal-name-or-nil (a b)
  (and a b (name= a b)))

(defun expr-has-function-p (e)
  "EP_HasFunc | EP_Subquery: a function call or subquery anywhere in E."
  (and (consp e)
       (or (member (car e) '(:fn :winfn :subquery :exists))
           (and (eq (car e) :in) (consp (third e)) (eq (car (third e)) :select))
           (some #'expr-has-function-p (cdr e)))))

;;; ------------------------------------------------------------------
;;; WHERE-term push-down (pushDownWhereTerms in SQLite's select.c)
;;;
;;; A FROM subquery that is not flattened gets a copy of each WHERE (or ON)
;;; term that constrains only it, rewritten in terms of its own columns: the
;;; subquery then filters (and can use an index) before its rows reach the
;;; outer query.  The terms stay in the outer WHERE clause as well.

(defparameter +volatile-functions+
  '("random" "randomblob" "changes" "total_changes" "last_insert_rowid")
  "Built-in functions SQLite does not treat as constant for given arguments.")

(defun pushable-term-p (e si scope)
  "sqlite3ExprIsTableConstant: does E read nothing but source SI (a
constant-propagated column counts as its constant), with no subquery and
no function whose result may vary?"
  (labels ((ok (x)
             (cond ((atom x) t)
                   ((not (keywordp (car x))) (every #'ok x))   ; a list of nodes
                   ((fixed-col-p x) t)
                   (t (case (car x)
                        (:col (multiple-value-bind (depth s) (resolve-column scope (second x) (third x))
                                (and depth (= depth 0) (eql s si))))
                        (:srccol (eql (second x) si))
                        ((:subquery :exists :winfn :raise :outer-on) nil)
                        (:in (and (ok (second x))
                                  (let ((rhs (third x)))
                                    (and (eq (car rhs) :list) (every #'ok (second rhs))))))
                        (:fn (let* ((lname (string-downcase-ascii (second x)))
                                    (c (and *db* (conn *db*))))
                               (and (not (aggregate-call-p x))
                                    (not (member lname +volatile-functions+ :test #'string=))
                                    (not (and c (gethash lname (db-user-functions c))))
                                    (every #'ok (third x))
                                    (ok (fifth x)))))
                        (t (every #'ok (cdr x))))))))
    (ok e)))

(defun core-result-asts (core)
  "CORE's result expressions with any * written out, or NIL."
  (let* ((items (select-core-from core))
         (srcs (loop for it in items collect (or (item-src it) (return-from core-result-asts nil)))))
    (loop for c in (select-core-cols core)
          append (if (eq (car c) :star)
                     (let ((cols (star-columns (second c) items srcs)))
                       (when (eq cols :unknown) (return-from core-result-asts nil))
                       (loop for (k . name) in cols
                             collect (let ((q (item-name (nth k items))))
                                       (unless q (return-from core-result-asts nil))
                                       (list :col q name))))
                     (list (second c))))))

(defun core-aggregate-p (core)
  (or (select-core-group core) (select-core-having core)
      (some (lambda (c) (and (eq (car c) :expr) (contains-aggregate-p (second c))))
            (select-core-cols core))))

(defun push-down-into (fs si scope terms)
  "FS compiled again with TERMS (outer terms on source SI) added to each
of its SELECTs, or NIL when SQLite would not push into it."
  (let* ((sel (fsrc-derived-sel fs))
         (cores (sel-cores sel)))
    (unless (and (every #'select-core-p cores)
                 (every (lambda (op) (eq op :union-all)) (sel-ops sel))  ; (9)
                 (null (sel-limit sel)) (null (sel-offset sel))          ; (3)
                 (null (sel-with sel))
                 (notany (lambda (c) (or (select-core-windows c)          ; (6)
                                         (some (lambda (x) (and (eq (car x) :expr)
                                                                (contains-window-p (second x))))
                                               (select-core-cols c))))
                         cores))
      (return-from push-down-into nil))
    (let* ((results (loop for c in cores collect (or (core-result-asts c) (return-from push-down-into nil))))
           ;; each arm's own collations, to compare with the compound's
           (natural (loop for c in cores
                          collect (let* ((items (select-core-from c))
                                         (srcs (loop for it in items
                                                     collect (or (item-src it) (return-from push-down-into nil)))))
                                    (mapcar (lambda (e) (column-expr-collation e items srcs))
                                            (nth (position c cores) results)))))
           (info (or (sel-column-info sel) (return-from push-down-into nil)))
           (colls (mapcar #'cdr info))
           (new-cores
             (loop for core in cores
                   for res in results
                   for nat in natural
                   collect (let ((k (copy-select-core core)))
                             (dolist (term terms)
                               (let ((new (map-cols
                                           (lambda (x)
                                             (multiple-value-bind (s ci) (column-ref x scope)
                                               (if (eql s si)
                                                   (let ((e (copy-tree (nth ci res))))
                                                     ;; substExpr: a column keeps its own collation
                                                     ;; only if it is the compound column's
                                                     (if (and (eq (car e) :col)
                                                              (eq (nth ci nat) (nth ci colls)))
                                                         (list :col (second e) (third e) :subst)
                                                         (list :icollate
                                                               (if (eq (car e) :col)
                                                                   (list :col (second e) (third e) :subst)
                                                                   e)
                                                               (nth ci colls))))
                                                   x)))
                                           (wrap-pushed-fixed term))))
                                 (if (core-aggregate-p core)
                                     (setf (select-core-having k) (sql-and (select-core-having k) new))
                                     (setf (select-core-where k) (sql-and (select-core-where k) new)))))
                             k))))
      (let ((new-sel (copy-sel sel)))
        (setf (sel-cores new-sel) new-cores)
        (funcall (fsrc-rebuild fs) new-sel)))))

(defun push-down-where-terms (fsrcs scope where ons)
  "pushDownWhereTerms for each subquery source of FSRCS, in FROM order;
a source that takes terms is recompiled in place (FSRCS and SCOPE's
sources are updated)."
  (let ((conjuncts
          (append (mapcar (lambda (c)
                            (if (eq (car c) :outer-on)
                                (cons (third c) (position (second c) fsrcs
                                                          :key (lambda (fs) (src-name (fsrc-src fs)))
                                                          :test #'equal))
                                (cons c nil)))
                          (split-conjuncts where))
                  (loop for fs in fsrcs for on in ons for i from 0
                        append (let ((outer (and (member (fsrc-join fs) '(:left :right :full)) i)))
                                 (mapcar (lambda (c) (cons c outer)) (split-conjuncts on)))))))
    (loop for fs in fsrcs
          for i from 0
          do (when (and (fsrc-rebuild fs)
                        (not (member (fsrc-join fs) '(:right :full)))
                        (notany (lambda (g) (member (fsrc-join g) '(:right :full))) (nthcdr (1+ i) fsrcs)))
               ;; SQLite takes the terms last to first
               (let ((terms (loop for (e . outer) in (reverse conjuncts)
                                  when (and (if (eq (fsrc-join fs) :left) (eql outer i) (null outer))
                                            (pushable-term-p e i scope))
                                    collect e)))
                 (when terms
                   (let ((new (push-down-into fs i scope terms)))
                     (when new
                       (let ((old-src (fsrc-src fs)) (new-src (fsrc-src new)))
                         (setf (fsrc-join new) (fsrc-join fs) (fsrc-on new) (fsrc-on fs)
                               (fsrc-using new) (fsrc-using fs) (fsrc-natural new) (fsrc-natural fs)
                               (src-name new-src) (src-name old-src)
                               (src-display new-src) (src-display old-src)
                               (src-invisible new-src) (src-invisible old-src)
                               (src-hidden new-src) (src-hidden old-src)
                               (src-used new-src) (src-used old-src))
                         (setf (nth i fsrcs) new
                               (nth i (scope-srcs scope)) new-src))))))))))

;;; ------------------------------------------------------------------
;;; HAVING terms that belong in WHERE (havingToWhere in SQLite's select.c)

(defun expr-equiv-p (a b scope)
  "sqlite3ExprCompare(a, b) < 2, near enough: the same column, or the same
expression tree."
  (cond ((and (consp a) (consp b)
              (member (car a) '(:col :srccol)) (member (car b) '(:col :srccol)))
         (multiple-value-bind (sa ca) (column-ref a scope)
           (multiple-value-bind (sb cb) (column-ref b scope)
             (and sa (eql sa sb) (eql ca cb)))))
        ((and (consp a) (consp b) (not (keywordp (car a))))
         (and (listp b) (= (length a) (length b))
              (every (lambda (x y) (expr-equiv-p x y scope)) a b)))
        ((and (consp a) (consp b))
         (and (eq (car a) (car b)) (= (length a) (length b))
              (if (eq (car a) :fn)
                  (and (name= (second a) (second b))
                       (every (lambda (x y) (expr-equiv-p x y scope)) (cddr a) (cddr b)))
                  (every (lambda (x y) (expr-equiv-p x y scope)) (cdr a) (cdr b)))))
        (t (equal a b))))

(defun constant-or-group-by-p (e groups scope)
  "sqlite3ExprIsConstantOrGroupBy: E reads nothing but GROUP BY terms
(compared with BINARY collation) and constants."
  (labels ((ok (x)
             (cond ((atom x) t)
                   ((not (keywordp (car x))) (every #'ok x))   ; a list of nodes
                   ((some (lambda (g) (expr-equiv-p x g scope)) groups) t)
                   (t (case (car x)
                        (:col (let ((a (and (null (second x))
                                            (null (column-ref x scope))
                                            (alias-expr scope (third x)))))
                                (and a (ok a))))
                        (:srccol nil)
                        ((:subquery :exists :winfn :raise) nil)
                        (:in (and (ok (second x))
                                  (let ((rhs (third x)))
                                    (and (eq (car rhs) :list) (every #'ok (second rhs))))))
                        (:fn (let* ((lname (string-downcase-ascii (second x)))
                                    (c (and *db* (conn *db*))))
                               (and (not (aggregate-call-p x))
                                    (not (member lname +volatile-functions+ :test #'string=))
                                    (not (and c (gethash lname (db-user-functions c))))
                                    (every #'ok (third x))
                                    (ok (fifth x)))))
                        (t (every #'ok (cdr x))))))))
    (ok e)))

(defun having-to-where (core rcols scope)
  "CORE with each top-level HAVING term that reads only GROUP BY terms and
constants moved to the end of the WHERE clause (its place in HAVING taking
TRUE), as SQLite does before planning an aggregate query."
  (let ((having (select-core-having core))
        (group (select-core-group core)))
    (if (not (and having group))
        core
        (let* ((groups (loop for g in group
                             for r = (let ((r (ignore-errors (resolve-group-term g rcols))))
                                       ;; a result alias stands for its expression
                                       (if (and (consp r) (eq (car r) :col) (null (second r))
                                                (null (column-ref r scope)) (alias-expr scope (third r)))
                                           (alias-expr scope (third r))
                                           r))
                             when (and r (member (or (ignore-errors (expr-collation r scope)) :binary)
                                                 '(:binary)))
                               collect r))
               (moved '()))
          (labels ((walk (x)
                     (if (and (consp x) (eq (car x) :binary) (eq (second x) :and))
                         (list :binary :and (walk (third x)) (walk (fourth x)))
                         (if (and (not (always-false-p x))
                                  (constant-or-group-by-p x groups scope))
                             (progn (push x moved) '(:lit 1))
                             x))))
            (let ((new-having (walk having)))
              (if (null moved)
                  core
                  (let ((k (copy-select-core core)))
                    (setf (select-core-having k) new-having
                          (select-core-where k)
                          (reduce #'sql-and (reverse moved) :initial-value (select-core-where core)))
                    k))))))))

(defun check-order-by-names (order sub info)
  "The errors resolving SUB's ORDER BY would raise, raised: a bare name
that is not an AS alias of SUB but an ambiguous column of its FROM."
  (let* ((items (select-core-from sub))
         (srcs (loop for it in items collect (or (item-src it) (return-from check-order-by-names nil))))
         (aliases (loop for c in (select-core-cols sub)
                        when (and (eq (car c) :expr) (third c)) collect (third c))))
    (declare (ignore info))
    (dolist (o order)
      (let ((e (first o)))
        (unless (or (int32-literal-p e)
                    (and (eq (car e) :col) (null (second e))
                         (member (third e) aliases :test #'name=)))
          (map-cols (lambda (x)
                      (when (eq (resolve-in-items (second x) (third x) items srcs) :ambiguous)
                        (sql-error-at (third x) "ambiguous column name: ~@[~a.~]~a" (second x) (third x)))
                      x)
                    e))))))

(defun wrap-pushed-fixed (e)
  "E with each column constant propagation fixed standing as its constant,
still marked as a column of the outer query (see PUSHED-FIXED-EQ-P)."
  (cond ((or (null *fixed-cols*) (atom e)) e)
        ((gethash e *fixed-cols*) (list :pushed-fixed (gethash e *fixed-cols*)))
        ((member (car e) '(:subquery :exists)) e)
        (t (let ((new (mapcar #'wrap-pushed-fixed e)))
             (if (every #'eq new e) e new)))))
