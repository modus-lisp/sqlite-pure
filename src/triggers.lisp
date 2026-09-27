;;;; triggers.lisp — row triggers: BEFORE / AFTER / INSTEAD OF, on
;;;; INSERT / UPDATE [OF cols] / DELETE, with WHEN, NEW/OLD and RAISE().
;;;;
;;;; A trigger body runs with NEW and OLD as an enclosing scope, so every
;;;; statement compiled inside it can say NEW.x; the columns are hidden from
;;;; unqualified lookup, as in SQLite.  Triggers fire newest first.  With
;;;; recursive_triggers off a trigger never re-fires itself; with it on,
;;;; recursion is bounded at SQLite's default depth of 1000.

(in-package #:sqlite-pure)

(defvar *outer-scope* nil "Scope enclosing top-level statement compilation (NEW/OLD in triggers).")
(defvar *outer-env* nil "Environment matching *OUTER-SCOPE*.")

(defconstant +max-trigger-depth+ 1000)

(defun replace-delete (table row)
  "Delete ROW to make way for a REPLACE; with recursive_triggers on, as a
DELETE that fires the table's delete triggers."
  (let ((rec (and (db-recursive-triggers (conn *db*)) (table-has-triggers-p table))))
    (unless (and rec (eq :ignore (fire-triggers table :delete :before row nil)))
      (fk-parent-delete table row)
      (delete-row table row)
      (when rec (fire-triggers table :delete :after row nil)))))

(defun root-scope () (or *outer-scope* (make-scope)))

(defun trigger-scope (table)
  (let ((new (make-table-src table "new"))
        (old (make-table-src table "old"))
        (all (loop for i below (length (table-columns table)) collect i)))
    (setf (src-hidden new) all (src-hidden old) all)
    (make-scope :srcs (list new old))))

(defun null-row (table)
  (make-array (1+ (length (table-columns table))) :initial-element :null))

(defun trigger-dbs (table)
  "Databases whose triggers may fire on TABLE: its own, and TEMP."
  (let ((own (or (table-owner table) *db*)) (tmp (temp-db *db*)))
    (if (and tmp (not (eq tmp own))) (list own tmp) (list own))))

(defun triggers-for (table event timing)
  (let ((out '()))
    (dolist (d (trigger-dbs table))
      (let ((order (mapcar #'third (schema-rows (db-schema* d)))))
        (maphash (lambda (k v) (declare (ignore k))
                   (destructuring-bind (tbl . ast) v
                     (when (and (name= tbl (table-name table))
                                (eq (getf (cdr ast) :event) event)
                                (eq (getf (cdr ast) :timing) timing))
                       (push (cons (or (position (getf (cdr ast) :name) order :test #'name=) 0) ast)
                             out))))
                 (schema-triggers (db-schema* d)))))
    ;; newest first: by position in sqlite_schema, descending
    (mapcar #'cdr (sort out #'> :key #'car))))

(defun table-has-triggers-p (table)
  (let ((hit nil))
    (dolist (d (trigger-dbs table))
      (maphash (lambda (k v) (declare (ignore k))
                 (when (name= (car v) (table-name table)) (setf hit t)))
               (schema-triggers (db-schema* d))))
    hit))

(defun run-trigger-statement (st)
  (case (car st)
    (:insert (exec-insert st))
    (:update (exec-update st))
    (:delete (exec-delete st))
    (:select (multiple-value-bind (fn) (compile-select (second st) *outer-scope*)
               (funcall fn *outer-env*)))
    (t (sql-error "unsupported statement in trigger"))))

(defun fire-triggers (table event timing old new &optional changed-columns)
  "Run matching triggers.  Return :IGNORE if a RAISE(IGNORE) asked to skip
the current row."
  (let ((triggers (triggers-for table event timing)))
    (when triggers
      (let* ((scope (trigger-scope table))
             (env (make-env :rows (vector (or new (null-row table)) (or old (null-row table))))))
        (dolist (tr triggers)
          (let ((name (getf (cdr tr) :name))
                (cols (getf (cdr tr) :columns)))
            (when (and (or (not (member name *active-triggers* :test #'name=))
                           (and (db-recursive-triggers (conn *db*))
                                (or (< (length *active-triggers*) +max-trigger-depth+)
                                    (sql-error "too many levels of trigger recursion"))))
                       (or (null cols) (not (eq event :update))
                           (some (lambda (c) (member c changed-columns :test #'name=)) cols)))
              (let ((*active-triggers* (cons name *active-triggers*))
                    (*outer-scope* scope)
                    (*outer-env* env)
                    (*ctes* '()))
                (let ((when-expr (getf (cdr tr) :when)))
                  (when (or (null when-expr)
                            (eq (truth (funcall (compile-expr when-expr scope) env)) t))
                    (let ((r (catch :raise-ignore
                               (dolist (st (getf (cdr tr) :body))
                                 (let ((*db* *db*)) (run-trigger-statement st)))
                               nil)))
                      (when (eq r :ignore)
                        (return-from fire-triggers :ignore)))))))))))
    nil))
