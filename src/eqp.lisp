;;;; eqp.lisp — EXPLAIN QUERY PLAN.
;;;;
;;;; The statement is compiled, not run, with *EQP* collecting a tree of
;;;; plan notes as the compiler makes its decisions: how each table is
;;;; read (the access path the planner chose), subqueries and how they are
;;;; evaluated, and the sorts it needs.  The wording is SQLite 3.40's, so
;;;; where this library plans a query the way SQLite does the output is the
;;;; same; where it plans differently, the output says what this library
;;;; does.  Siblings are ordered as SQLite orders them (materialised
;;;; sources, the loops, subqueries, then GROUP BY / DISTINCT / ORDER BY).
;;;; Rows are (id parent notused detail); ids are just preorder numbers
;;;; (SQLite's are bytecode addresses).

(in-package #:sqlite-pure)

(defstruct eqp-node
  detail                 ; string, or a thunk returning a string or NIL (omit)
  (rank 1)
  (seq 0)
  (children '()))

(defvar *ctes*)                         ; defined in select.lisp; special here too
(defvar *eqp* nil "True while EXPLAIN QUERY PLAN is collecting.")
(defvar *eqp-parent* nil "The node new notes go under.")
(defvar *eqp-seq* 0)
(defvar *eqp-rank* 2 "Rank of expression subqueries noted now (2: before GROUP BY, 4: after).")
(defvar *eqp-sel-ids* nil "SEL / core -> SQLite's select id (parse-completion order).")
(defvar *eqp-cte-uses* nil "CTE name -> number of references in the statement.")
(defvar *eqp-ctes-done* nil "CTEs already described.")
(defvar *eqp-noted* nil "Subqueries already described (a probe may compile one twice).")
(defvar *eqp-left* nil "The loop being planned is the inner side of a LEFT JOIN.")
(defvar *eqp-coroutine-ok* nil "A FROM subquery here would be a co-routine in SQLite.")

;; ranks
(defconstant +eqp-materialize+ 0)
(defconstant +eqp-loop+ 1)
(defconstant +eqp-group+ 3)
(defconstant +eqp-distinct+ 5)
(defconstant +eqp-order+ 6)

(defun eqp-note (detail &optional (rank +eqp-loop+))
  "Record a plan note under the current parent; returns the node."
  (when *eqp*
    (let ((n (make-eqp-node :detail detail :rank rank :seq (incf *eqp-seq*))))
      (push n (eqp-node-children *eqp-parent*))
      n)))

(defmacro with-eqp-node ((detail &optional (rank '+eqp-loop+)) &body body)
  "Run BODY with its notes nested under a new note."
  `(let ((*eqp-parent* (or (eqp-note ,detail ,rank) *eqp-parent*)))
     ,@body))

(defmacro without-eqp (&body body)
  `(let ((*eqp* nil)) ,@body))

(defun eqp-table-note (detail)
  "A loop's access-path note, marked if it is a LEFT JOIN's inner loop."
  (let ((left *eqp-left*))
    (eqp-note (if (functionp detail)
                  (lambda () (let ((d (funcall detail))) (if left (concatenate 'string d " LEFT-JOIN") d)))
                  (if left (concatenate 'string detail " LEFT-JOIN") detail)))))

(defun eqp-table-refs (x name)
  "How many times X refers to a table called NAME."
  (let ((n 0))
    (labels ((walk (y)
               (cond ((sel-p y)
                      (dolist (w (sel-with y)) (walk (third w)))
                      (mapc #'walk (sel-cores y)))
                     ((select-core-p y)
                      (walk (select-core-cols y)) (walk (select-core-from y))
                      (walk (select-core-where y)) (walk (select-core-group y))
                      (walk (select-core-having y)))
                     ((consp y)
                      (when (and (eq (car y) :table) (stringp (second y)) (name= (second y) name))
                        (incf n))
                      (walk (car y)) (walk (cdr y))))))
      (walk x))
    n))

(defun eqp-sel-id (x) (and *eqp-sel-ids* (gethash x *eqp-sel-ids*)))

;;; ------------------------------------------------------------------
;;; Select ids: SQLite numbers each SELECT as its parse completes, so inner
;;; and earlier ones first; a compound's id is its last core's.

(defun eqp-number (st)
  (let ((ids (make-hash-table :test #'eq)) (uses (make-hash-table :test #'equal)) (n 0))
    (labels ((walk (x)
               (cond ((sel-p x)
                      (dolist (w (sel-with x)) (walk (third w)))
                      (let ((last nil))
                        (dolist (core (sel-cores x))
                          (walk core)
                          (setf last (setf (gethash core ids) (incf n))))
                        (walk (sel-order x)) (walk (sel-limit x)) (walk (sel-offset x))
                        (setf (gethash x ids) last)))
                     ((select-core-p x)
                      (walk (select-core-cols x)) (walk (select-core-from x))
                      (walk (select-core-where x)) (walk (select-core-group x))
                      (walk (select-core-having x)))
                     ((consp x)
                      (when (and (eq (car x) :table) (stringp (second x)))
                        (incf (gethash (string-downcase-ascii (second x)) uses 0)))
                      (walk (car x)) (walk (cdr x))))))
      (walk st))
    (values ids uses)))

;;; ------------------------------------------------------------------
;;; Rendering

(defun eqp-rows (root)
  (let ((rows '()) (id 0))
    (labels ((emit (node parent)
               (dolist (c (stable-sort (reverse (eqp-node-children node)) #'< :key #'eqp-node-rank))
                 (let ((d (eqp-node-detail c)))
                   (when (functionp d) (setf d (funcall d)))
                   (when d
                     (let ((me (incf id)))
                       (push (list me parent 0 d) rows)
                       (emit c me)))))))
      (emit root 0))
    (nreverse rows)))

(defun explain-query-plan (db st text)
  "EXPLAIN QUERY PLAN: the plan rows of statement ST."
  (declare (ignore text))
  (let* ((root (make-eqp-node))
         (*eqp* t) (*eqp-parent* root) (*eqp-seq* 0) (*eqp-rank* 2)
         (*eqp-ctes-done* '()) (*eqp-left* nil) (*eqp-noted* (make-hash-table :test #'eq)) (*eqp-coroutine-ok* nil)
         (*db* db) (*encoding* (db-encoding db)))
    (multiple-value-bind (ids uses) (eqp-number st)
      (let ((*eqp-sel-ids* ids) (*eqp-cte-uses* uses))
        (case (car st)
          (:select (compile-select (second st) (make-scope)))
          (:insert (eqp-insert st))
          (:update (eqp-update-delete st t))
          (:delete (eqp-update-delete st nil))
          (:create-table (let ((sel (getf (cdr st) :as-select)))
                           (when sel (compile-select sel (make-scope)))))
          (t nil))
        ;; details are rendered here: some are only known once compiled
        (values (eqp-rows root) '("id" "parent" "notused" "detail"))))))

(defun eqp-insert (st)
  (destructuring-bind (&key with source &allow-other-keys) (cdr st)
    (let ((*ctes* *ctes*))
      (when with (without-eqp (register-ctes (make-sel :with (first with) :recursive (second with)))))
      (when (sel-p source)
        (let ((cores (sel-cores source)))
          ;; a single VALUES row is not a loop
          (unless (and (null (cdr cores)) (consp (first cores)) (eq (car (first cores)) :values)
                       (null (cdr (second (first cores)))))
            (compile-select source (make-scope))))))))

(defun eqp-update-delete (st updatep)
  (destructuring-bind (&key with table schema alias where sets from &allow-other-keys) (cdr st)
    (let ((*ctes* *ctes*))
      (when with (without-eqp (register-ctes (make-sel :with (first with) :recursive (second with)))))
      (let ((tb (lookup-table *db* table t schema)))
        (unless (or (table-view-select tb)
                    ;; DELETE FROM t alone empties the b-trees: no loop
                    (and (not updatep) (null where) (null (getf (cdr st) :returning))
                         (not (table-has-triggers-p tb)) (not (table-vtab tb))
                         (not (and (fk-enabled-p) (referencing-keys tb)))))
          (let* ((target (let ((f (make-fsrc :src (make-table-src tb alias) :table tb :join :first)))
                           (setf (src-used (fsrc-src f)) :all)   ; writes read whole rows
                           f))
                 (others (and updatep
                              (loop for item in from
                                    for k from 0
                                    collect (let ((fs (make-fsrc-for item (make-scope))))
                                              (when (zerop k) (setf (fsrc-join fs) :comma))
                                              fs))))
                 (fsrcs (cons target others))
                 (scope (make-scope :srcs (mapcar #'fsrc-src fsrcs))))
            (build-levels fsrcs scope where (apply-joins fsrcs scope))
            (dolist (s sets) (compile-expr (second s) scope))))))))
