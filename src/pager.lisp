;;;; pager.lisp — pages, the database header, the freelist, and
;;;; transactions with a SQLite-compatible rollback journal.
;;;;
;;;; Every page lives in CACHE as an octet vector.  A write transaction
;;;; records each page's pre-transaction image in JOURNAL before its first
;;;; modification; COMMIT writes those images to "<db>-journal" in SQLite's
;;;; own format, then the dirty pages, then deletes the journal.  A crash in
;;;; between leaves a hot journal that both this library and SQLite itself
;;;; roll back on the next open.
;;;;
;;;; A nested STATEMENT journal gives statement-level atomicity inside an
;;;; explicit transaction: a failing INSERT undoes only its own pages.

(in-package #:sqlite-pure)

(defconstant +default-page-size+ 4096)

;;; B-tree page types (btree.lisp owns the rest of the page format, but
;;; the pager must lay down an empty page 1).
(defconstant +interior-index+ 2)
(defconstant +interior-table+ 5)
(defconstant +leaf-index+ 10)
(defconstant +leaf-table+ 13)

(defun init-btree-page (b off type usable)
  (fill b 0 :start off :end (+ off 12))
  (setf (aref b off) type)
  (put-u16 b (+ off 5) (if (= usable 65536) 0 usable)))
(defparameter *cache-limit* 4096 "Clean pages kept before the cache is trimmed.")
(defparameter *sqlite-version-number* 3040001)
(defvar *crash-after-pages* nil
  "Testing hook: abandon COMMIT after writing this many database pages.")

(defstruct (db (:constructor %make-db))
  (path nil)
  (stream nil)
  (inode nil)                ; the file's INODE: locks shared with this process's other connections
  (mutex #+sbcl (sb-thread:make-mutex :name "sqlite-pure connection") #-sbcl nil)
  (readonly nil)
  (page-size +default-page-size+)
  (usable-size +default-page-size+)
  (page-count 0)
  (cache (make-hash-table))
  (dirty (make-hash-table))
  ;; write transaction state
  (txn nil)                  ; nil, or the kind of the open write transaction
  (explicit nil)             ; inside BEGIN ... COMMIT
  (orig-page-count 0)
  (journal (make-hash-table)) ; pgno -> original octets
  (stmt-journal nil)          ; pgno -> octets or :new, while a statement runs
  (savepoints '())            ; innermost first: (name journal page-count)
  (savepoint-txn nil)         ; the outermost SAVEPOINT began the transaction
  (stmt-page-count 0)
  ;; schema and bookkeeping
  (schema nil)
  (encoding :utf-8)
  (last-insert-rowid 0)
  (changes 0)
  (total-changes 0)
  (pending-page-size nil)
  (pending-autovacuum nil)   ; :full or :incremental for a new database (or the next VACUUM)
  (lock :none)               ; :none :shared :reserved :exclusive
  (wal nil)
  ;; several databases per connection (TEMP, ATTACH)
  (name "main")
  (conn nil)                 ; the connection (main database), or NIL if this is it
  (attached '())             ; on the main database: alist name -> db, "temp" included
  (foreign-keys nil)         ; PRAGMA foreign_keys (on the connection)
  (recursive-triggers nil)   ; PRAGMA recursive_triggers (on the connection)
  (writable-schema nil)      ; PRAGMA writable_schema: sqlite_ names may be created
  (case-sensitive-like nil)  ; PRAGMA case_sensitive_like: NIL (never set), :ON or :OFF
  (busy-timeout nil)         ; seconds to wait for a lock (on the connection); NIL: *BUSY-TIMEOUT*
  ;; user-defined SQL functions, aggregates and collations (on the connection)
  (user-functions (make-hash-table :test #'equal))   ; name -> (min max fn)
  (user-aggregates (make-hash-table :test #'equal))  ; name -> (min max ctor)
  (user-collations (make-hash-table :test #'equal))  ; NAME -> (compare . key)
  (user-tokenizers (make-hash-table :test #'equal))  ; name -> function, for FTS3/4/5
  (fk-deferred nil)          ; a deferred foreign key was violated in this transaction
  (stmt-cache (make-hash-table :test #'equal))
  (vtab-state nil)           ; plist: virtual-table transaction bookkeeping (FTS3)
  (safety-level 3)           ; PRAGMA synchronous + 1: 1 OFF, 2 NORMAL, 3 FULL, 4 EXTRA
  (secure-delete t)          ; PRAGMA secure_delete: T, NIL or :fast (SQLite as commonly built: on)
  (freed-in-txn (make-hash-table)) ; pages put on the freelist in this transaction
  (closed nil))

(defmethod print-object ((db db) s)
  (print-unreadable-object (db s :type t)
    (format s "~a ~d pages" (or (db-path db) ":memory:") (db-page-count db))))

(defun database-path (db) (db-path db))

(defun conn (db) (or (db-conn db) db))

(defun conn-dbs (db)
  "Every database of DB's connection: main first, then temp and attached."
  (let ((c (conn db)))
    (cons c (mapcar #'cdr (db-attached c)))))

(defun temp-db (db &optional create)
  "The connection's TEMP database (an in-memory database), made on demand."
  (let* ((c (conn db))
         (hit (cdr (assoc "temp" (db-attached c) :test #'name=))))
    (or hit
        (when create
          (let ((tdb (%make-db :name "temp" :conn c :encoding (db-encoding c))))
            (setf (db-attached c) (cons (cons "temp" tdb) (db-attached c)))
            tdb)))))

(defun schema-db (db name &optional (errorp t))
  "The database called NAME (main, temp, or an attachment) on DB's connection."
  (let ((c (conn db)))
    (cond ((name= name "main") c)
          ((name= name "temp") (temp-db c t))
          (t (or (cdr (assoc name (db-attached c) :test #'name=))
                 (and errorp (sql-error "unknown database ~a" name)))))))

(defun memory-db-p (db) (null (db-stream db)))

(defun fsync-only (stream db &optional (min-level 2))
  #+sbcl (when (>= (db-safety-level db) min-level)
           (sb-posix:fsync (sb-sys:fd-stream-fd stream)))
  #-sbcl (declare (ignore stream db min-level))
  nil)

(defun sync-stream (stream db &optional (min-level 2))
  "Write STREAM out and, unless PRAGMA synchronous is below MIN-LEVEL
(1 OFF, 2 NORMAL, 3 FULL), fsync it (SBCL; elsewhere finish-output is all
there is)."
  (finish-output stream)
  #+sbcl (when (>= (db-safety-level db) min-level)
           (sb-posix:fsync (sb-sys:fd-stream-fd stream)))
  #-sbcl (declare (ignore db min-level))
  nil)

;;; ------------------------------------------------------------------
;;; Header fields (all on page 1)

(defconstant +hdr-page-size+ 16)
(defconstant +hdr-reserved+ 20)
(defconstant +hdr-change-counter+ 24)
(defconstant +hdr-page-count+ 28)
(defconstant +hdr-freelist-trunk+ 32)
(defconstant +hdr-freelist-count+ 36)
(defconstant +hdr-schema-cookie+ 40)
(defconstant +hdr-schema-format+ 44)
(defconstant +hdr-text-encoding+ 56)
(defconstant +hdr-user-version+ 60)
(defconstant +hdr-application-id+ 68)
(defconstant +hdr-version-valid-for+ 92)
(defconstant +hdr-version-number+ 96)

(defparameter +magic+ (ascii-octets (format nil "SQLite format 3~c" (code-char 0))))

(defun header-u32 (db off)
  (if (zerop (db-page-count db)) 0 (get-u32 (read-page db 1) off)))

(defun set-header-u32 (db off v)
  (put-u32 (page-for-write db 1) off v))

;;; ------------------------------------------------------------------
;;; Page I/O

(defun page-offset (db pgno) (* (1- pgno) (db-page-size db)))

(defvar *bt* nil "The database whose b-trees are being changed (btree-edit).")
(defvar *mps* nil "pgno -> MPAGE for the b-tree operation in progress (btree-edit).")

(defun trim-cache (db)
  ;; never a page the b-tree operation in progress holds: it may yet change it
  (let ((cache (db-cache db)) (dirty (db-dirty db)) (victims '())
        (held (and (eq *bt* db) *mps*)))
    (maphash (lambda (k v) (declare (ignore v))
               (unless (or (gethash k dirty) (= k 1) (and held (gethash k held))) (push k victims)))
             cache)
    (dolist (k victims) (remhash k cache))))

(defun read-page (db pgno)
  (when (db-wal db) (setf (wal-fresh (db-wal db)) nil))   ; the snapshot is now in use
  (when (or (< pgno 1) (> pgno (max (db-page-count db) 1)))
    (corrupt "page ~d out of range (database has ~d)" pgno (db-page-count db)))
  (or (gethash pgno (db-cache db))
      (let ((b (make-octets (db-page-size db))))
        (let ((s (db-stream db)))
          (unless (and (db-wal db) (wal-read-page db pgno b))
            (when (and s (<= (* pgno (db-page-size db)) (file-length s)))
              (file-position s (page-offset db pgno))
              (read-sequence b s))))
        (when (> (hash-table-count (db-cache db)) *cache-limit*)
          (trim-cache db))
        (setf (gethash pgno (db-cache db)) b))))

(defun ensure-write-txn (db)
  (when (db-readonly db)
    (error 'sqlite-error :code :readonly :message "attempt to write a readonly database"))
  (unless (db-txn db)
    (lock-reserved db)                  ; before any page is dirtied
    (begin-write db :auto)))

(defun page-for-write (db pgno)
  "The page's octets, journaled and marked dirty; mutate them in place."
  (ensure-write-txn db)
  (let ((b (read-page db pgno)))
    (when (and (<= pgno (db-orig-page-count db))
               (not (nth-value 1 (gethash pgno (db-journal db)))))
      (setf (gethash pgno (db-journal db)) (copy-seq b)))
    (let ((sj (db-stmt-journal db)))
      (when (and sj (not (nth-value 1 (gethash pgno sj))))
        (setf (gethash pgno sj)
              (if (> pgno (db-stmt-page-count db)) :new (copy-seq b)))))
    (dolist (sp (db-savepoints db))
      (destructuring-bind (name journal page-count) sp
        (declare (ignore name))
        (unless (nth-value 1 (gethash pgno journal))
          (setf (gethash pgno journal) (if (> pgno page-count) :new (copy-seq b))))))
    (setf (gethash pgno (db-dirty db)) t)
    b))

;;; ------------------------------------------------------------------
;;; Opening

(defun pending-byte-page (db)
  (1+ (floor #x40000000 (db-page-size db))))

(defun init-header (db)
  "Create page 1 of a brand-new database."
  (let ((ps (or (db-pending-page-size db) +default-page-size+)))
    (setf (db-page-size db) ps (db-usable-size db) ps
          (db-page-count db) 1)
    (let ((b (make-octets ps)))
      (setf (gethash 1 (db-cache db)) b)
      (replace b +magic+)
      (put-u16 b +hdr-page-size+ (if (= ps 65536) 1 ps))
      (setf (aref b 18) 1 (aref b 19) 1 (aref b 20) 0
            (aref b 21) 64 (aref b 22) 32 (aref b 23) 32)
      (put-u32 b +hdr-schema-format+ 4)
      (when (member (db-pending-autovacuum db) '(:full :incremental))
        (put-u32 b 52 1)
        (put-u32 b 64 (if (eq (db-pending-autovacuum db) :incremental) 1 0)))
      (put-u32 b +hdr-text-encoding+ (ecase (db-encoding db) (:utf-8 1) (:utf-16le 2) (:utf-16be 3)))
      (put-u32 b +hdr-page-count+ 1)
      (init-btree-page b 100 +leaf-table+ ps)
      (setf (gethash 1 (db-dirty db)) t)
      ;; a statement or savepoint rolled back must remove the new page 1
      (when (db-stmt-journal db) (setf (gethash 1 (db-stmt-journal db)) :new))
      (dolist (sp (db-savepoints db)) (setf (gethash 1 (second sp)) :new)))))

(defun parse-header (db b)
  (unless (every #'= +magic+ (subseq b 0 16))
    (corrupt "file is not a database"))
  (let* ((raw (get-u16 b +hdr-page-size+))
         (ps (if (= raw 1) 65536 raw)))
    (unless (and (>= ps 512) (= (logcount ps) 1))
      (corrupt "bad page size ~d" ps))
    (when (> (aref b 18) 2)
      (sql-error "unsupported file format (write version ~d)" (aref b 18)))
    (setf (db-page-size db) ps
          (db-usable-size db) (- ps (aref b +hdr-reserved+))
          (db-encoding db) (case (get-u32 b +hdr-text-encoding+)
                             ((0 1) :utf-8) (2 :utf-16le) (3 :utf-16be)
                             (t (corrupt "bad text encoding"))))
    ps))

(defun open-file-stream (path readonly)
  (handler-case
      (if readonly
          (open path :element-type '(unsigned-byte 8) :direction :input)
          (open path :element-type '(unsigned-byte 8) :direction :io
                     :if-exists :overwrite :if-does-not-exist :create))
    (file-error ()
      (error 'sqlite-error :code :cantopen :message "unable to open database file"))))

(defun journal-path (db) (concatenate 'string (db-path db) "-journal"))

(defun load-database (db)
  (let ((s (db-stream db)))
    ;; A journal left behind is rolled back by LOCK-SHARED, under the
    ;; locking protocol, not here: it may belong to a live writer.
    (let ((len (file-length s)))
      (cond ((< len 100) (setf (db-page-count db) 0))
            (t
             (let ((h (make-octets 100)))
               (file-position s 0)
               (read-sequence h s)
               (let ((ps (parse-header db h)))
                 (setf (db-page-count db)
                       (let ((hdr-count (get-u32 h +hdr-page-count+)))
                         (if (and (plusp hdr-count)
                                  (= (get-u32 h +hdr-change-counter+)
                                     (get-u32 h +hdr-version-valid-for+)))
                             hdr-count
                             (ceiling len ps))))
                 (when (> (aref h 18) 1)
                   ;; WAL mode: join the shared wal-index
                   (wal-open db)))))))))

(defun open-database (path &key readonly)
  "Open (creating if necessary) the database at PATH.  PATH may be
\":memory:\" for a transient in-memory database."
  (let ((path (if (pathnamep path) (namestring path) path)))
    (if (or (null path) (string= path ":memory:") (string= path ""))
        (%make-db)
        (let ((db (%make-db :path path :readonly readonly)))
          (when (and readonly (not (probe-file path)))
            (sql-error "unable to open database file ~a" path))
          (setf (db-stream db) (open-file-stream path readonly))
          (attach-inode db)
          (handler-bind ((error (lambda (c) (declare (ignore c))
                                  (unlock-to db :none)
                                  (detach-inode db))))
            (load-database db))
          db))))

(defun close-database (db)
  (with-connection-mutex (db) (%close-database db)))

(defun %close-database (db)
  (unless (db-closed db)
    (dolist (a (db-attached db)) (%close-database (cdr a)))
    (when (db-txn db) (rollback-write db))
    (when (db-wal db) (wal-close db))
    (unlock-to db :none)
    (when (db-stream db) (detach-inode db))
    (setf (db-closed db) t))
  nil)

(defmacro with-database ((var path &rest keys) &body body)
  `(let ((,var (open-database ,path ,@keys)))
     (unwind-protect (progn ,@body)
       (close-database ,var))))

;;; ------------------------------------------------------------------
;;; Transactions

(defun begin-write (db kind)
  (setf (db-txn db) kind
        (db-orig-page-count db) (db-page-count db))
  (clrhash (db-journal db))
  (clrhash (db-freed-in-txn db))
  (when (zerop (db-page-count db))
    (init-header db)))

(defun statement-begin (db)
  (setf (db-stmt-journal db) (make-hash-table)
        (db-stmt-page-count db) (db-page-count db)))

(defun statement-end (db)
  (setf (db-stmt-journal db) nil))

(defun statement-rollback (db)
  (let ((sj (db-stmt-journal db)))
    (when sj
      (maphash (lambda (pgno img)
                 (if (eq img :new)
                     (progn (remhash pgno (db-cache db)) (remhash pgno (db-dirty db)))
                     (setf (gethash pgno (db-cache db)) img)))
               sj)
      (setf (db-page-count db) (db-stmt-page-count db)
            (db-stmt-journal db) nil
            (db-schema db) nil))))

(defun restore-journal (db journal page-count)
  (maphash (lambda (pgno img)
             (if (eq img :new)
                 (progn (remhash pgno (db-cache db)) (remhash pgno (db-dirty db)))
                 (setf (gethash pgno (db-cache db)) (copy-seq img))))
           journal)
  (setf (db-page-count db) page-count
        (db-schema db) nil))

(defun savepoint-push (db name)
  (push (list name (make-hash-table) (db-page-count db)) (db-savepoints db)))

(defun savepoint-outermost-p (db name)
  "True if NAME is the outermost open savepoint (signals if unknown)."
  (let ((k (or (position name (db-savepoints db) :key #'first :test #'name=)
               (sql-error "no such savepoint: ~a" name))))
    (= k (1- (length (db-savepoints db))))))

(defun savepoint-pop (db name)
  "RELEASE on one database: forget NAME and everything inside it."
  (let ((k (position name (db-savepoints db) :key #'first :test #'name=)))
    (when k (setf (db-savepoints db) (nthcdr (1+ k) (db-savepoints db))))))

(defun savepoint-restore (db name)
  "ROLLBACK TO on one database: undo everything since NAME; NAME stays open."
  (let ((k (position name (db-savepoints db) :key #'first :test #'name=)))
    (when k
      (destructuring-bind (spname journal page-count) (nth k (db-savepoints db))
        (restore-journal db journal page-count)
        (setf (db-savepoints db)
              (cons (list spname (make-hash-table) page-count)
                    (nthcdr (1+ k) (db-savepoints db))))))))

(defun rollback-write (db)
  (setf (db-savepoints db) '() (db-savepoint-txn db) nil)
  (when (db-txn db)
    (maphash (lambda (pgno img) (setf (gethash pgno (db-cache db)) img))
             (db-journal db))
    (let ((orig (db-orig-page-count db)))
      (maphash (lambda (pgno v) (declare (ignore v))
                 (when (> pgno orig) (remhash pgno (db-cache db))))
               (db-dirty db))
      (when (zerop orig) (remhash 1 (db-cache db)))
      (setf (db-page-count db) orig))
    (clrhash (db-dirty db))
    (clrhash (db-journal db))
    (clrhash (db-freed-in-txn db))
    (setf (db-txn db) nil (db-stmt-journal db) nil (db-schema db) nil)
    (unlock-to db :shared)))

(defun journal-checksum (nonce page)
  (let ((sum nonce))
    (loop for i from (- (length page) 200) above 0 by 200
          do (setf sum (ldb (byte 32 0) (+ sum (aref page i)))))
    sum))

(defun write-journal (db)
  (let* ((ps (db-page-size db))
         (pages (sort (loop for k being the hash-keys of (db-journal db) collect k) #'<))
         (nonce (random #x100000000 (sql-random-state)))
         (hdr (make-octets 512)))
    (replace hdr #(#xd9 #xd5 #x05 #xf9 #x20 #xa1 #x63 #xd7))
    (put-u32 hdr 8 (length pages))
    (put-u32 hdr 12 nonce)
    (put-u32 hdr 16 (db-orig-page-count db))
    (put-u32 hdr 20 512)
    (put-u32 hdr 24 ps)
    (with-open-file (j (journal-path db) :element-type '(unsigned-byte 8)
                                         :direction :output :if-exists :supersede)
      (write-sequence hdr j)
      (let ((b4 (make-octets 4)))
        (dolist (p pages)
          (let ((img (gethash p (db-journal db))))
            (put-u32 b4 0 p) (write-sequence b4 j)
            (write-sequence img j)
            (put-u32 b4 0 (journal-checksum nonce img)) (write-sequence b4 j))))
      (sync-stream j db))))

(defun delete-journal (db)
  (let ((p (probe-file (journal-path db))))
    (when p (delete-file p))))

(defun commit-write (db)
  (when (db-txn db)
    (when (plusp (hash-table-count (db-dirty db)))
      (when (and (autovacuum-p db) (not (incremental-p db)))
        (autovacuum-commit db))
      (let ((h (page-for-write db 1)))
        (let ((cc (ldb (byte 32 0) (1+ (get-u32 h +hdr-change-counter+)))))
          (put-u32 h +hdr-change-counter+ cc)
          (put-u32 h +hdr-version-valid-for+ cc))
        (put-u32 h +hdr-page-count+ (db-page-count db))
        (put-u32 h +hdr-version-number+ *sqlite-version-number*))
      (let ((s (db-stream db)))
        (when (and s (db-wal db))
          (wal-commit db (sort (loop for k being the hash-keys of (db-dirty db) collect k) #'<))
          (setf s nil))
        (when s
          (let ((journaled (plusp (hash-table-count (db-journal db)))))
            (when journaled (write-journal db))
            (lock-exclusive db)
            (let ((pages (sort (loop for k being the hash-keys of (db-dirty db) collect k)
                               #'<))
                  (written 0))
              (dolist (p pages)
                (when (and *crash-after-pages* (>= written *crash-after-pages*))
                  (finish-output s)
                  (error "simulated crash during commit"))
                (incf written)
                (file-position s (page-offset db p))
                (write-sequence (gethash p (db-cache db)) s)))
            (sync-stream s db)
            (when (< (db-page-count db) (floor (file-length s) (db-page-size db)))
              (truncate-file db))
            (when journaled (delete-journal db))))))
    (clrhash (db-dirty db))
    (clrhash (db-journal db))
    (setf (db-txn db) nil (db-stmt-journal db) nil)
    (unlock-to db :shared))
  (setf (db-savepoints db) '() (db-savepoint-txn db) nil))

(defun recover-hot-journal (db)
  "Play back a rollback journal left by an interrupted commit."
  (let ((jp (journal-path db)))
    (with-open-file (j jp :element-type '(unsigned-byte 8) :if-does-not-exist nil)
      (when (and j (>= (file-length j) 28) (not (db-readonly db)))
        (let ((hdr (make-octets 28)))
          (read-sequence hdr j)
          (when (every #'= hdr #(#xd9 #xd5 #x05 #xf9 #x20 #xa1 #x63 #xd7))
            (let* ((nrec (get-u32 hdr 8))
                   (nonce (get-u32 hdr 12))
                   (orig-size (get-u32 hdr 16))
                   (sector (max 512 (get-u32 hdr 20)))
                   (ps (get-u32 hdr 24))
                   (reclen (+ ps 8))
                   (avail (floor (- (file-length j) sector) reclen))
                   (n (if (= nrec #xffffffff) avail (min nrec avail)))
                   (s (db-stream db)))
              (when (and (>= ps 512) (plusp orig-size))
                (file-position j sector)
                (let ((b4 (make-octets 4)) (img (make-octets ps)))
                  (dotimes (i n)
                    (read-sequence b4 j)
                    (let ((pgno (get-u32 b4 0)))
                      (read-sequence img j)
                      (read-sequence b4 j)
                      (unless (= (get-u32 b4 0) (journal-checksum nonce img))
                        (return))
                      (when (<= pgno orig-size)
                        (file-position s (* (1- pgno) ps))
                        (write-sequence img s)))))
                (sync-stream s db)
                (delete-file jp)))))))))

;;; ------------------------------------------------------------------
;;; Freelist
