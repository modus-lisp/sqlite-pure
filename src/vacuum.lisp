;;;; vacuum.lisp — VACUUM and VACUUM INTO: rebuild the database densely.
;;;;
;;;; The schema and every row are copied into a fresh in-memory database
;;;; (same page size, encoding, user_version and application_id); its
;;;; pages then replace the originals through an ordinary journaled
;;;; commit, and the file is truncated (on SBCL).  Rowids are preserved.

(in-package #:sqlite-pure)

(defun build-compact-copy (db)
  "A new in-memory database holding DB's schema and contents."
  (let ((new (%make-db :encoding (db-encoding db) :pending-page-size (db-page-size db)
                       :pending-autovacuum
                       (let ((p (db-pending-autovacuum db)))
                         (cond ((member p '(:full :incremental)) p)
                               ((eq p :none) nil)
                               ((autovacuum-p db) (if (incremental-p db) :incremental :full))))))
        (rows (schema-rows (db-schema* db))))
    (flet ((run (sql) (let ((*db* new)) (run-sql new sql '()))))
      ;; tables (sqlite_sequence is created by AUTOINCREMENT tables)
      (dolist (r rows)
        (destructuring-bind (rowid type name tbl root sql &rest ignore) r
          (declare (ignore rowid tbl ignore))
          (when (and (equal type "table") (stringp sql) (not (name= name "sqlite_sequence"))
                     (not (eql root 0)))
            (run sql))))
      ;; contents, rowids included
      (dolist (r rows)
        (destructuring-bind (rowid type name &rest ignore) r
          (declare (ignore rowid ignore))
          (when (equal type "table")
            (let* ((tb (find-table-in db name))
                   (target (find-table-in new name)))
              (when (and target (not (table-view-select tb)) (not (table-vtab tb)))
                (with-transaction (new)
                  (let ((*db* db) (*encoding* (db-encoding db)))
                    (map-table-rows
                     tb
                     (lambda (row)
                       (let ((out (copy-seq row)))
                         (let ((*db* new) (*encoding* (db-encoding new)))
                           (write-row target out))))))))))))
      ;; indexes, views, triggers, in their original order
      (dolist (r rows)
        (destructuring-bind (rowid type name tbl root sql &rest ignore) r
          (declare (ignore rowid))
          (cond ((and (member type '("index" "view" "trigger") :test #'equal) (stringp sql))
                 (run sql))
                ;; virtual tables: the schema row itself, as SQLite copies it
                ((and (equal type "table") (eql root 0))
                 (let ((*db* new))
                   (with-transaction (new) (add-schema-row type name tbl 0 sql))
                   (setf (db-schema new) nil))))))
      (let ((h (read-page db 1)) (nh (let ((*db* new)) (page-for-write new 1))))
        (dolist (off (list +hdr-user-version+ +hdr-application-id+ 48))
          (put-u32 nh off (get-u32 h off)))
        ;; as SQLite: the schema cookie moves on, so other connections
        ;; re-read the (renumbered) schema
        (put-u32 nh +hdr-schema-cookie+ (1+ (get-u32 h +hdr-schema-cookie+)))
        (let ((*db* new)) (commit-write new))))
    new))

(defun vacuum-into (db path)
  (let ((copy (build-compact-copy db)))
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
    (clrhash (db-cache db))
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
