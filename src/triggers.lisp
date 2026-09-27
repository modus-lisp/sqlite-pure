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

(defun replace-delete (table row &optional found-by)
  "Delete ROW to make way for a REPLACE; with recursive_triggers on, as a
DELETE that fires the table's delete triggers.  FOUND-BY is the index whose
conflict found ROW (its entry is removed last, as SQLite does)."
  (let ((rec (and (db-recursive-triggers (conn *db*)) (table-has-triggers-p table))))
    (unless (and rec (eq :ignore (fire-triggers table :delete :before row nil)))
      (fk-parent-delete table row)
      (delete-row table row found-by)
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

(defun check-trigger-programs (table event &optional changed-columns)
  "What sqlite3_prepare does when it codes the triggers a statement may
fire: compile each WHEN clause and look up every function a trigger body
calls, so a missing function (or column in WHEN) fails the statement even
when no row reaches the trigger."
  (dolist (timing '(:before :after :instead-of))
    (dolist (tr (triggers-for table event timing))
      (let ((cols (getf (cdr tr) :columns)))
        (when (or (null cols) (not (eq event :update))
                  (some (lambda (c) (member c changed-columns :test #'name=)) cols))
          (let ((scope (trigger-scope table)) (when-expr (getf (cdr tr) :when)))
            (when when-expr
              (let ((*outer-scope* scope) (*ctes* '()))
                (compile-expr when-expr scope)))
            (check-functions-called (getf (cdr tr) :body))))))))

(defun check-functions-called (ast)
  "Signal \"no such function\" for the first call in AST (statements,
expressions, and the structures a SELECT parses into) to an unknown
function, or a known scalar function with the wrong number of arguments."
  (let ((seen (make-hash-table :test #'eq)))
    (labels ((walk (x)
               (cond ((consp x)
                      (unless (gethash x seen)
                        (setf (gethash x seen) t)
                        (when (and (eq (car x) :fn) (stringp (second x)) (listp (third x)))
                          (check-call (second x) (third x)))
                        (loop for tail = x then (cdr tail)
                              while (consp tail) do (walk (car tail))
                              finally (walk tail))))
                     ((typep x 'structure-object)
                      (unless (gethash x seen)
                        (setf (gethash x seen) t)
                        #+sbcl
                        (dolist (s (sb-mop:class-slots (class-of x)))
                          (walk (slot-value x (sb-mop:slot-definition-name s))))))
                     ((and (vectorp x) (not (stringp x)) (not (typep x '(vector (unsigned-byte 8)))))
                      (map nil #'walk x))))
             (check-call (name args)
               (let ((lname (string-downcase-ascii name)))
                 (unless (string= lname "match")
                   (multiple-value-bind (scalar agg) (find-sql-function lname)
                     (cond ((and (null scalar) (null agg))
                            (sql-error "no such function: ~a" name))
                           ((and scalar (null agg)
                                 (not (<= (first scalar) (length args) (or (second scalar) (length args)))))
                            (sql-error "wrong number of arguments to function ~a()" name))))))))
      (walk ast))))

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
