;;;; fkeys.lisp — foreign key enforcement (PRAGMA foreign_keys = ON).
;;;;
;;;; Child side: a new or changed child row whose key is all non-NULL must
;;;; name an existing parent row.  Parent side: deleting a parent row, or
;;;; changing its key, applies each referencing key's ON DELETE / ON UPDATE
;;;; action (CASCADE, SET NULL, SET DEFAULT, RESTRICT, NO ACTION).  A
;;;; DEFERRABLE INITIALLY DEFERRED key is not checked per row: a violation
;;;; is noted, and COMMIT re-verifies the whole key before committing.

(in-package #:sqlite-pure)

(defun fk-enabled-p () (db-foreign-keys (conn *db*)))

(defun fk-violation () (conflict-fail :abort "FOREIGN KEY constraint failed"))

(defun fk-parent-table (table fk)
  (or (find-table-in (table-owner table) (fkey-parent fk))
      (sql-error "no such table: ~a.~a" (db-name (table-owner table)) (fkey-parent fk))))

(defun fk-parent-columns (parent fk)
  "Indexes of the parent columns FK refers to."
  (let ((names (fkey-parent-cols fk)))
    (if names
        (mapcar (lambda (n) (or (find-column parent n)
                                (sql-error "foreign key mismatch - \"~a\" referencing \"~a\""
                                           (fkey-parent fk) (fkey-parent fk))))
                names)
        (cond ((table-pk parent) (table-pk parent))
              (t (sql-error "foreign key mismatch - referencing \"~a\"" (fkey-parent fk)))))))

(defun rows-matching (table cols vals)
  "Rows of TABLE whose columns COLS equal VALS (with the columns' affinity
and collation, as a WHERE clause would compare)."
  (scan-table-rows table nil
                   (reduce (lambda (a b) (list :binary :and a b))
                           (loop for ci in cols
                                 for v in vals
                                 collect (list :binary :eq
                                               (list :col nil (column-name (aref (table-columns table) ci)))
                                               (list :lit v))))))

(defun fk-key (row cols) (mapcar (lambda (ci) (svref row ci)) cols))

(defun fk-check-child (table row &optional old)
  "Verify ROW's foreign keys (only those whose columns changed from OLD)."
  (when (fk-enabled-p)
    (dolist (fk (table-fkeys table))
      (let ((key (fk-key row (fkey-child-cols fk))))
        (unless (or (member :null key)
                    (and old (every #'values-equal-p key (fk-key old (fkey-child-cols fk)))))
          (let* ((parent (fk-parent-table table fk))
                 (pcols (fk-parent-columns parent fk)))
            (unless (rows-matching parent pcols key)
              (if (fkey-deferred fk)
                  (setf (db-fk-deferred (conn *db*)) t)
                  (fk-violation)))))))))

(defun referencing-keys (table)
  "(child-table . fkey) for every foreign key that names TABLE."
  (let ((out '()))
    (maphash (lambda (k child) (declare (ignore k))
               (dolist (fk (table-fkeys child))
                 (when (name= (fkey-parent fk) (table-name table))
                   (push (cons child fk) out))))
             (schema-tables (db-schema* (table-owner table))))
    out))

(defun fk-child-update (child crow new-key-vals fk)
  "Rewrite the foreign key columns of child row CROW."
  (let ((new (copy-seq crow)))
    (loop for ci in (fkey-child-cols fk)
          for v in new-key-vals
          do (setf (svref new ci) v))
    (let ((ctx (make-write-ctx :table child :checks-fns (compile-checks child))))
      (update-one ctx crow new))))

(defun fk-parent-change (table row new-row action-of)
  "ROW of parent TABLE is being deleted (NEW-ROW NIL) or its key changed."
  (when (fk-enabled-p)
    (loop for (child . fk) in (referencing-keys table)
          do (let* ((pcols (fk-parent-columns table fk))
                    (key (fk-key row pcols)))
               (unless (or (member :null key)
                           (and new-row (every #'values-equal-p key (fk-key new-row pcols))))
                 (let ((children (rows-matching child (fkey-child-cols fk) key)))
                   (when children
                     (ecase (funcall action-of fk)
                       ((:restrict :no-action)
                        (if (and (fkey-deferred fk) (eq (funcall action-of fk) :no-action))
                            (setf (db-fk-deferred (conn *db*)) t)
                            (fk-violation)))
                       (:cascade
                        (if new-row
                            (let ((nk (fk-key new-row pcols)))
                              (dolist (c children) (fk-child-update child c nk fk)))
                            (dolist (c children) (fk-delete-row child c))))
                       (:set-null
                        (dolist (c children)
                          (fk-child-update child c (make-list (length pcols) :initial-element :null) fk)))
                       (:set-default
                        (dolist (c children)
                          (fk-child-update child c
                                           (mapcar (lambda (ci)
                                                     (column-default-value (aref (table-columns child) ci)))
                                                   (fkey-child-cols fk))
                                           fk)))))))))))

(defun fk-parent-delete (table row)
  (fk-parent-change table row nil #'fkey-on-delete))

(defun fk-parent-update (table old new)
  (fk-parent-change table old new #'fkey-on-update))

(defun fk-delete-row (table row)
  "Delete ROW, applying the actions of keys that reference it (CASCADE)."
  (fk-parent-delete table row)
  (when (or (table-without-rowid table)
            (table-lookup (table-owner table) (table-root table) (svref row (length (table-columns table)))))
    (delete-row table row)))

(defun fk-check-deferred (db)
  "At COMMIT: if a deferred key was violated, verify every deferred key."
  (when (and (db-foreign-keys db) (db-fk-deferred db))
    (let ((*db* db))
      (dolist (d (conn-dbs db))
        (maphash (lambda (k child) (declare (ignore k))
                   (dolist (fk (table-fkeys child))
                     (when (fkey-deferred fk)
                       (let* ((parent (fk-parent-table child fk))
                              (pcols (fk-parent-columns parent fk)))
                         (map-table-rows child
                                         (lambda (row)
                                           (let ((key (fk-key row (fkey-child-cols fk))))
                                             (unless (or (member :null key)
                                                         (rows-matching parent pcols key))
                                               (constraint-error "FOREIGN KEY constraint failed")))))))))
                 (schema-tables (db-schema* d)))))
    (setf (db-fk-deferred db) nil)))
