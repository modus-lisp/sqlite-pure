;;;; wal.lisp — write-ahead-log databases.
;;;;
;;;; Reading: committed frames of "<db>-wal" override pages of the main
;;;; file; READ-PAGE finds them through an index of frame offsets.
;;;;
;;;; Writing is done in an EXCLUSIVE session.  SQLite's WAL connections
;;;; share an index in "<db>-shm" that every writer must keep current; rather
;;;; than maintain it, the first write takes an exclusive lock on the main
;;;; file and a write lock on the -shm "dead-man switch" byte, which any
;;;; attached SQLite connection holds a read lock on.  If either is taken,
;;;; the write fails with "database is locked" and nothing is touched.
;;;; Commits append checksummed frames (the last one carrying the new page
;;;; count); a crash leaves a valid log that SQLite recovers.  Closing the
;;;; database (or PRAGMA wal_checkpoint) copies the log into the main file
;;;; and removes -wal and -shm, as SQLite's last connection does.

(in-package #:sqlite-pure)

(defconstant +wal-magic-be+ #x377f0683)
(defconstant +wal-shm-dms+ 128 "The -shm byte SQLite connections read-lock while attached.")

(defstruct (wal (:conc-name wal-))
  path stream
  (big t)                ; checksum byte order (from the header's magic)
  (salt1 0) (salt2 0) (s1 0) (s2 0)
  (end 0)                ; file offset of the next frame; 0 = no valid header yet
  (frames (make-hash-table))   ; pgno -> offset of its newest committed page image
  (ckpt-seq 0)
  session                ; the exclusive write session is held
  shm)                   ; -shm stream holding the DMS lock

(defun wal-file-path (db) (concatenate 'string (db-path db) "-wal"))
(defun shm-file-path (db) (concatenate 'string (db-path db) "-shm"))

(defun wal-checksum (big b start end s1 s2)
  (loop for i from start below end by 8
        do (flet ((w (k) (if big (get-u32 b k)
                             (logior (aref b k) (ash (aref b (+ k 1)) 8)
                                     (ash (aref b (+ k 2)) 16) (ash (aref b (+ k 3)) 24)))))
             (setf s1 (ldb (byte 32 0) (+ s1 (w i) s2))
                   s2 (ldb (byte 32 0) (+ s2 (w (+ i 4)) s1)))))
  (values s1 s2))

(defun load-wal (db)
  "Index the committed frames of DB's log, if it has one."
  (let* ((path (wal-file-path db))
         (w (make-wal :path path))
         (s (open path :element-type '(unsigned-byte 8)
                       :direction (if (db-readonly db) :input :io)
                       :if-exists (if (db-readonly db) nil :overwrite)
                       :if-does-not-exist nil)))
    (setf (db-wal db) w (wal-stream w) s)
    (when (and s (>= (file-length s) 32))
      (let ((hdr (make-octets 32)))
        (file-position s 0)
        (read-sequence hdr s)
        (let ((magic (get-u32 hdr 0)))
          (when (member magic '(#x377f0682 #x377f0683))
            (let* ((big (= magic +wal-magic-be+))
                   (ps (get-u32 hdr 8))
                   (frame-len (+ 24 ps))
                   (fh (make-octets 24))
                   (page (make-octets ps))
                   (pending '()))
              (multiple-value-bind (s1 s2) (wal-checksum big hdr 0 24 0 0)
                (when (and (= s1 (get-u32 hdr 24)) (= s2 (get-u32 hdr 28)) (= ps (db-page-size db)))
                  (setf (wal-big w) big (wal-salt1 w) (get-u32 hdr 16) (wal-salt2 w) (get-u32 hdr 20)
                        (wal-ckpt-seq w) (get-u32 hdr 12)
                        (wal-s1 w) s1 (wal-s2 w) s2 (wal-end w) 32)
                  (loop with pos = 32
                        while (<= (+ pos frame-len) (file-length s))
                        do (file-position s pos)
                           (read-sequence fh s)
                           (read-sequence page s)
                           (unless (and (= (get-u32 fh 8) (wal-salt1 w)) (= (get-u32 fh 12) (wal-salt2 w)))
                             (return))
                           (multiple-value-setq (s1 s2) (wal-checksum big fh 0 8 s1 s2))
                           (multiple-value-setq (s1 s2) (wal-checksum big page 0 ps s1 s2))
                           (unless (and (= s1 (get-u32 fh 16)) (= s2 (get-u32 fh 20)))
                             (return))
                           (push (cons (get-u32 fh 0) (+ pos 24)) pending)
                           (incf pos frame-len)
                           (let ((commit-size (get-u32 fh 4)))
                             (when (plusp commit-size)
                               ;; a commit: everything up to here counts
                               (dolist (f (reverse pending))
                                 (setf (gethash (car f) (wal-frames w)) (cdr f))
                                 (remhash (car f) (db-cache db)))
                               (setf pending '()
                                     (db-page-count db) commit-size
                                     (wal-s1 w) s1 (wal-s2 w) s2 (wal-end w) pos)))))))))))
    w))

(defun wal-read-page (db pgno buffer)
  "Fill BUFFER with PGNO's newest committed image from the log; true if
the log has one."
  (let* ((w (db-wal db))
         (off (and w (gethash pgno (wal-frames w)))))
    (when off
      (file-position (wal-stream w) off)
      (read-sequence buffer (wal-stream w))
      t)))

;;; ------------------------------------------------------------------
;;; The exclusive write session

#+sbcl
(defun fd-lock (stream type start len)
  (handler-case
      (progn (sb-posix:fcntl (sb-sys:fd-stream-fd stream) sb-posix:f-setlk
                             (make-instance 'sb-posix:flock :type type :whence sb-posix:seek-set
                                                            :start start :len len))
             t)
    (sb-posix:syscall-error (e)
      (if (member (sb-posix:syscall-errno e) (list sb-posix:eagain sb-posix:eacces))
          nil
          (error e)))))

#-sbcl
(defun fd-lock (stream type start len)
  (declare (ignore stream type start len))
  t)

(defun wal-begin-session (db)
  "Take the locks that make this connection the only one on the file."
  (let ((w (db-wal db)))
    (unless (wal-session w)
      (let ((s (db-stream db))
            (shm (open (shm-file-path db) :element-type '(unsigned-byte 8) :direction :io
                                          :if-exists :overwrite :if-does-not-exist :create)))
        (flet ((busy ()
                 (fd-lock s +un+ +pending-byte+ (+ 2 +shared-size+))
                 (close shm)
                 (error 'sqlite-error :code :busy :message "database is locked")))
          (unless (and (busy-wait-quietly (lambda () (fd-lock shm +wr+ +wal-shm-dms+ 1)))
                       (fd-lock s +rd+ +shared-first+ +shared-size+)
                       (fd-lock s +wr+ +reserved-byte+ 1)
                       (fd-lock s +wr+ +pending-byte+ 1)
                       (fd-lock s +wr+ +shared-first+ +shared-size+))
            (busy)))
        (setf (wal-shm w) shm (wal-session w) t)
        ;; another process may have committed before we got here
        (load-wal-again db)))))

(defun busy-wait-quietly (thunk)
  (handler-case (busy-wait thunk)
    (sqlite-error () nil)))

(defun load-wal-again (db)
  (let ((old (db-wal db)))
    (when (wal-stream old) (close (wal-stream old)))
    (clrhash (db-cache db))
    (setf (db-schema db) nil)
    (let ((len (file-length (db-stream db))))
      (let ((h (make-octets 100)))
        (file-position (db-stream db) 0)
        (read-sequence h (db-stream db))
        (setf (db-page-count db)
              (if (= (get-u32 h +hdr-change-counter+) (get-u32 h +hdr-version-valid-for+))
                  (get-u32 h +hdr-page-count+)
                  (ceiling len (db-page-size db))))))
    (let ((new (load-wal db)))
      (setf (wal-session new) (wal-session old) (wal-shm new) (wal-shm old)))))

;;; ------------------------------------------------------------------
;;; Commit and checkpoint

(defun wal-ensure-stream (db)
  (let ((w (db-wal db)))
    (or (wal-stream w)
        (setf (wal-stream w)
              (open (wal-path w) :element-type '(unsigned-byte 8) :direction :io
                                 :if-exists :overwrite :if-does-not-exist :create)))))

(defun wal-start-log (db)
  "Write a fresh log header (new salts, next checkpoint sequence)."
  (let* ((w (db-wal db))
         (s (wal-ensure-stream db))
         (h (make-octets 32)))
    (setf (wal-big w) t
          (wal-salt1 w) (ldb (byte 32 0) (1+ (wal-salt1 w)))
          (wal-salt2 w) (random #x100000000))
    (put-u32 h 0 +wal-magic-be+)
    (put-u32 h 4 3007000)
    (put-u32 h 8 (db-page-size db))
    (put-u32 h 12 (wal-ckpt-seq w))
    (put-u32 h 16 (wal-salt1 w))
    (put-u32 h 20 (wal-salt2 w))
    (multiple-value-bind (s1 s2) (wal-checksum t h 0 24 0 0)
      (put-u32 h 24 s1) (put-u32 h 28 s2)
      (setf (wal-s1 w) s1 (wal-s2 w) s2))
    (file-position s 0)
    (write-sequence h s)
    (setf (wal-end w) 32)
    (clrhash (wal-frames w))))

(defun wal-commit (db pages)
  "Append PAGES (dirty page numbers, sorted) as one committed transaction."
  (wal-begin-session db)
  (let* ((w (db-wal db))
         (ps (db-page-size db))
         (fh (make-octets 24)))
    (when (zerop (wal-end w)) (wal-start-log db))
    (let ((s (wal-ensure-stream db))
          (s1 (wal-s1 w)) (s2 (wal-s2 w))
          (pos (wal-end w))
          (offsets '()))
      (loop for (p . more) on pages
            for img = (gethash p (db-cache db))
            do (fill fh 0)
               (put-u32 fh 0 p)
               (put-u32 fh 4 (if more 0 (db-page-count db)))
               (put-u32 fh 8 (wal-salt1 w))
               (put-u32 fh 12 (wal-salt2 w))
               (multiple-value-setq (s1 s2) (wal-checksum t fh 0 8 s1 s2))
               (multiple-value-setq (s1 s2) (wal-checksum t img 0 ps s1 s2))
               (put-u32 fh 16 s1)
               (put-u32 fh 20 s2)
               (file-position s pos)
               (write-sequence fh s)
               (write-sequence img s)
               (push (cons p (+ pos 24)) offsets)
               (incf pos (+ 24 ps)))
      (finish-output s)
      ;; only now is the transaction in the log
      (dolist (o offsets) (setf (gethash (car o) (wal-frames w)) (cdr o)))
      (setf (wal-s1 w) s1 (wal-s2 w) s2 (wal-end w) pos))))

(defun wal-checkpoint (db)
  "Copy the log into the main file and empty the log.  Returns the number
of pages copied."
  (let ((w (db-wal db)))
    (if (or (null w) (zerop (hash-table-count (wal-frames w))))
        0
        (progn
          (wal-begin-session db)
          (let* ((s (db-stream db))
                 (buf (make-octets (db-page-size db)))
                 (pages (sort (loop for k being the hash-keys of (wal-frames w) collect k) #'<)))
            (dolist (p pages)
              (when (<= p (db-page-count db))
                (wal-read-page db p buf)
                (file-position s (page-offset db p))
                (write-sequence buf s)))
            (finish-output s)
            (truncate-file db)
            ;; the next commit starts a new log generation
            (incf (wal-ckpt-seq w))
            (setf (wal-end w) 0)
            (clrhash (wal-frames w))
            (let ((ws (wal-stream w)))
              (when ws
                (file-position ws 0)
                (write-sequence (make-octets 32) ws)   ; invalidate the old header
                (finish-output ws)))
            (length pages))))))

(defun wal-close (db)
  "At close: checkpoint and remove -wal and -shm, if we hold the session."
  (let ((w (db-wal db)))
    (when w
      (when (wal-session w)
        (wal-checkpoint db)
        (when (wal-stream w) (close (wal-stream w)) (setf (wal-stream w) nil))
        (let ((p (probe-file (wal-path w)))) (when p (delete-file p)))
        (let ((p (probe-file (shm-file-path db)))) (when p (delete-file p)))
        (close (wal-shm w))
        (fd-lock (db-stream db) +un+ +pending-byte+ (+ 2 +shared-size+))
        (setf (wal-session w) nil))
      (when (wal-stream w) (close (wal-stream w))))))

;;; ------------------------------------------------------------------
;;; PRAGMA journal_mode

(defun set-journal-mode (db mode)
  "Switch between WAL and rollback-journal modes; returns the mode name."
  (cond
    ((memory-db-p db) "memory")
    ((string= mode "wal")
     (unless (db-wal db)
       (when (db-explicit (conn db)) (sql-error "cannot change into wal mode from within a transaction"))
       (let ((*db* db))
         (run-in-write-txn db (lambda ()
                                (let ((h (page-for-write db 1)))
                                  (setf (aref h 18) 2 (aref h 19) 2)))))
       (setf (db-wal db) (make-wal :path (wal-file-path db))))
     "wal")
    (t
     (when (db-wal db)
       (when (db-explicit (conn db)) (sql-error "cannot change out of wal mode from within a transaction"))
       (wal-begin-session db)
       (let ((*db* db))
         (run-in-write-txn db (lambda ()
                                (let ((h (page-for-write db 1)))
                                  (setf (aref h 18) 1 (aref h 19) 1)))))
       (wal-close db)
       (setf (db-wal db) nil))
     (if (member mode '("delete" "persist" "truncate" "off" "memory") :test #'string=)
         "delete"
         "delete"))))
