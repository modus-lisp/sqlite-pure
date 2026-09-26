;;;; triggers.lisp — row triggers: BEFORE / AFTER / INSTEAD OF, on
;;;; INSERT / UPDATE [OF cols] / DELETE, with WHEN, NEW/OLD and RAISE().
;;;;
;;;; A trigger body runs with NEW and OLD as an enclosing scope, so every
;;;; statement compiled inside it can say NEW.x; the columns are hidden from
;;;; unqualified lookup, as in SQLite.  Triggers fire newest first, and (as
;;;; with recursive_triggers off) a trigger never re-fires itself.

(in-package #:sqlite-pure)

(defvar *outer-scope* nil "Scope enclosing top-level statement compilation (NEW/OLD in triggers).")
(defvar *outer-env* nil "Environment matching *OUTER-SCOPE*.")

(defun root-scope () (or *outer-scope* (make-scope)))

(defun trigger-scope (table)
  (let ((new (make-table-src table "new"))
        (old (make-table-src table "old"))
        (all (loop for i below (length (table-columns table)) collect i)))
    (setf (src-hidden new) all (src-hidden old) all)
    (make-scope :srcs (list new old))))

(defun null-row (table)
  (make-array (1+ (length (table-columns table))) :initial-element :null))

(defun triggers-for (table event timing)
  (let ((out '()))
    (maphash (lambda (k v) (declare (ignore k))
               (destructuring-bind (tbl . ast) v
                 (when (and (name= tbl (table-name table))
                            (eq (getf (cdr ast) :event) event)
                            (eq (getf (cdr ast) :timing) timing))
                   (push ast out))))
             (schema-triggers (db-schema* *db*)))
    ;; newest first: sort by position in sqlite_schema, descending
    (let ((order (mapcar #'third (schema-rows (db-schema* *db*)))))
      (sort out #'> :key (lambda (ast) (or (position (getf (cdr ast) :name) order :test #'name=) 0))))))

(defun table-has-triggers-p (table)
  (let ((hit nil))
    (maphash (lambda (k v) (declare (ignore k))
               (when (name= (car v) (table-name table)) (setf hit t)))
             (schema-triggers (db-schema* *db*)))
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
            (when (and (not (member name *active-triggers* :test #'name=))
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
