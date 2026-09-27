;;;; vacuum.lisp — VACUUM and VACUUM INTO: rebuild the database densely.
;;;;
;;;; The schema and every row are copied into a fresh in-memory database
;;;; (same page size, encoding, user_version and application_id); its
;;;; pages then replace the originals through an ordinary journaled
;;;; commit, and the file is truncated (on SBCL).  Rowids are preserved.

(in-package #:sqlite-pure)

(defun build-compact-copy (db &optional into)
  "A new in-memory database holding DB's schema and contents, built as
sqlite3RunVacuum builds vacuum_db: in one transaction, the tables' CREATE
statements, then the indexes', then each table's rows copied in rowid order
and each index filled in index order through a bulk-load cursor (the
INSERT ... SELECT transfer optimisation), then the views', triggers' and
virtual tables' schema rows."
  (let ((new (%make-db :encoding (db-encoding db) :pending-page-size (db-page-size db)
                       :pending-autovacuum
                       (let ((p (db-pending-autovacuum db)))
                         (cond ((member p '(:full :incremental)) p)
                               ((eq p :none) nil)
                               ((autovacuum-p db) (if (incremental-p db) :incremental :full))))))
        (rows (schema-rows (db-schema* db))))
    ;; sqlite3RunVacuum sets SQLITE_WriteSchema: sqlite_stat1 and the like
    ;; are recreated like any other table
    (setf (db-writable-schema new) t)
    (flet ((run (sql) (let ((*db* new)) (run-sql new sql '()))))
      (run "BEGIN")
      ;; tables (sqlite_sequence is created by AUTOINCREMENT tables)
      (dolist (r rows)
        (destructuring-bind (rowid type name tbl root sql &rest ignore) r
          (declare (ignore rowid tbl ignore))
          (when (and (equal type "table") (stringp sql) (not (name= name "sqlite_sequence"))
                     (not (eql root 0)))
            (run sql))))
      ;; indexes
      (dolist (r rows)
        (destructuring-bind (rowid type name tbl root sql &rest ignore) r
          (declare (ignore rowid name tbl root ignore))
          (when (and (equal type "index") (stringp sql))
            (run sql))))
      ;; contents: every table of the new schema, in its order
      (let ((*db* new))
        (dolist (r (schema-rows (db-schema* new)))
          (destructuring-bind (rowid type name tbl root &rest ignore) r
            (declare (ignore rowid tbl ignore))
            (when (and (equal type "table") (integerp root) (plusp root))
              (let ((src (find-table-in db name)) (target (find-table-in new name)))
                (when src
                  (unless (table-without-rowid target)
                    ;; (xferOptimization: a table with no INTEGER PRIMARY KEY
                    ;; and no index gets new rowids, 1, 2, ..., except for
                    ;; VACUUM INTO)
                    (let ((pending '())
                          (renumber (and (not into) (null (table-rowid-alias target))
                                         (null (remove-if #'index-pk-index (table-indexes target))))))
                      (map-table db (table-root src) (lambda (rid payload) (push (cons rid payload) pending)))
                      (loop for e in (nreverse pending)
                            for k from 1
                            do (table-insert new (table-root target) (if renumber k (car e)) (cdr e)))))
                  (dolist (idx (sqlite-index-list target))
                    (let ((sidx (if (index-pk-index idx)
                                    (find-if #'index-pk-index (table-indexes src))
                                    (find (index-name idx) (table-indexes src) :key #'index-name :test #'name=)))
                          (entries '()))
                      (when sidx
                        (let ((*db* db))
                          (map-index db (if (index-pk-index sidx) (table-root src) (index-root sidx))
                                     (lambda (vals) (push vals entries))))
                        (let ((*index-cmp* (index-full-cmp target idx)))
                          (dolist (vals (nreverse entries))
                            (index-insert new (if (index-pk-index idx) (table-root target) (index-root idx))
                                          vals :bulk t)))))))))))
        ;; views, triggers, virtual tables: their schema rows, as INSERT copies them
        (dolist (r rows)
          (destructuring-bind (rowid type name tbl root sql &rest ignore) r
            (declare (ignore rowid ignore))
            (when (or (member type '("view" "trigger") :test #'equal)
                      (and (equal type "table") (eql root 0)))
              (add-schema-row type name tbl root sql))))
        (setf (db-schema new) nil))
      (let ((h (read-page db 1)) (nh (let ((*db* new)) (page-for-write new 1))))
        (dolist (off (list +hdr-user-version+ +hdr-application-id+ 48))
          (put-u32 nh off (get-u32 h off)))
        ;; as SQLite: the schema cookie moves on, so other connections
        ;; re-read the (renumbered) schema
        (put-u32 nh +hdr-schema-cookie+ (1+ (get-u32 h +hdr-schema-cookie+))))
      (run "COMMIT"))
    new))

(defun vacuum-into (db path)
  (let ((copy (build-compact-copy db t)))
    (when (probe-file path)
      (with-open-file (s path :element-type '(unsigned-byte 8) :if-does-not-exist nil)
        (when (and s (plusp (file-length s)))
          (sql-error "output file already exists"))))
    (with-open-file (out path :element-type '(unsigned-byte 8) :direction :output
                              :if-exists :supersede :if-does-not-exist :create)
      (loop for pg from 1 to (db-page-count copy)
            do (write-sequence (read-page copy pg) out)))))

(defun vacuum-in-place (db)
  (when (db-explicit (conn db)) (sql-error "cannot VACUUM from within a transaction"))
  ;; a database with no pages yet: VACUUM just creates page 1
  (when (zerop (db-page-count db))
    ;; (as SQLite's copy of an empty vacuum_db: schema cookie 1, file
    ;; format and encoding not yet set)
    (let ((*db* db))
      (run-in-write-txn db (lambda ()
                             (let ((h (page-for-write db 1)))
                               (put-u32 h +hdr-schema-cookie+ 1)
                               (put-u32 h +hdr-schema-format+ 0)
                               (put-u32 h +hdr-text-encoding+ 0)))))
    (return-from vacuum-in-place nil))
  (let* ((copy (build-compact-copy db))
         (n (db-page-count copy)))
    (let ((*db* db))
      (run-in-write-txn
       db
       (lambda ()
         (loop for pg from 1 to n
               do (replace (page-for-write db pg) (read-page copy pg)))
         ;; keep the change counter moving forward
         (let ((h (page-for-write db 1)) (old (get-u32 (gethash 1 (db-journal db) (read-page db 1))
                                                       +hdr-change-counter+)))
           (put-u32 h +hdr-change-counter+ old))
         (setf (db-page-count db) n))))
    (truncate-file db)
    ;; a file's cache can go; an in-memory database's cache is its content
    (if (db-stream db)
        (clrhash (db-cache db))
        (let ((n (db-page-count db)))
          (loop for pg being the hash-keys of (db-cache db)
                when (> pg n) collect pg into gone
                finally (dolist (p gone) (remhash p (db-cache db))))))
    (setf (db-schema db) nil)
    nil))

(defun truncate-file (db)
  "Shrink the file to the page count (SBCL: ftruncate; elsewhere the
trailing pages stay, and are ignored because the header says so)."
  #+sbcl
  (when (db-stream db)
    (finish-output (db-stream db))
    (sb-posix:ftruncate (sb-sys:fd-stream-fd (db-stream db))
                        (* (db-page-count db) (db-page-size db))))
  #-sbcl (declare (ignore db))
  nil)
