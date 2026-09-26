;;;; locking.lisp — SQLite's rollback-journal locking protocol, and page
;;;; cache validation.
;;;;
;;;; SQLite (unix VFS) locks byte ranges with POSIX advisory locks at a
;;;; fixed offset past the end of any real data:
;;;;   PENDING  0x40000000        RESERVED 0x40000001
;;;;   SHARED   0x40000002 .. +510
;;;; SHARED = read lock on one byte of the shared range (acquired while
;;;; holding a read lock on PENDING); RESERVED = write lock on RESERVED;
;;;; EXCLUSIVE = write lock on PENDING and on the whole shared range.
;;;; Speaking the same protocol lets this library and SQLite processes
;;;; share a database file safely.  Locks need fcntl(2), so they are taken
;;;; on SBCL (via sb-posix); elsewhere they are no-ops.
;;;;
;;;; Independently of locks, every read transaction re-reads the header's
;;;; change counter and drops the page cache if another process committed.

(in-package #:sqlite-pure)

(defconstant +pending-byte+ #x40000000)
(defconstant +reserved-byte+ (1+ +pending-byte+))
(defconstant +shared-first+ (+ +pending-byte+ 2))
(defconstant +shared-size+ 510)

(defvar *busy-timeout* 5 "Seconds to wait for a lock before \"database is locked\".")

(defun lockable-p (db)
  (and (db-stream db) (not (db-wal db))))

#+sbcl
(defun posix-lock (db type start len)
  "Try one fcntl(F_SETLK); true on success, NIL if another process holds
a conflicting lock."
  (handler-case
      (progn
        (sb-posix:fcntl (sb-sys:fd-stream-fd (db-stream db)) sb-posix:f-setlk
                        (make-instance 'sb-posix:flock :type type :whence sb-posix:seek-set
                                                       :start start :len len))
        t)
    (sb-posix:syscall-error (e)
      (if (member (sb-posix:syscall-errno e) (list sb-posix:eagain sb-posix:eacces))
          nil
          (error e)))))

#-sbcl
(defun posix-lock (db type start len)
  (declare (ignore db type start len))
  t)

(defconstant +rd+ #+sbcl sb-posix:f-rdlck #-sbcl 0)
(defconstant +wr+ #+sbcl sb-posix:f-wrlck #-sbcl 1)
(defconstant +un+ #+sbcl sb-posix:f-unlck #-sbcl 2)

(defun busy-wait (thunk)
  "Call THUNK until it returns true or *BUSY-TIMEOUT* expires."
  (let ((deadline (+ (get-internal-real-time)
                     (* *busy-timeout* internal-time-units-per-second))))
    (loop
      (when (funcall thunk) (return t))
      (when (> (get-internal-real-time) deadline)
        (error 'sqlite-error :code :busy :message "database is locked"))
      (sleep 0.005))))

(defun lock-shared (db)
  (when (and (lockable-p db) (eq (db-lock db) :none))
    (busy-wait
               (lambda ()
                 (and (posix-lock db +rd+ +pending-byte+ 1)
                      (prog1 (posix-lock db +rd+ +shared-first+ +shared-size+)
                        (posix-lock db +un+ +pending-byte+ 1)))))
    (setf (db-lock db) :shared)
    (when (probe-file (journal-path db))
      (handle-hot-journal db))
    (validate-cache db)))

(defun lock-reserved (db)
  (when (lockable-p db)
    (lock-shared db)
    (when (eq (db-lock db) :shared)
      (busy-wait (lambda () (posix-lock db +wr+ +reserved-byte+ 1)))
      (setf (db-lock db) :reserved))))

(defun lock-exclusive (db)
  (when (lockable-p db)
    (lock-reserved db)
    (unless (eq (db-lock db) :exclusive)
      ;; PENDING stops new readers; then wait for the current ones to go
      (busy-wait (lambda () (posix-lock db +wr+ +pending-byte+ 1)))
      (busy-wait (lambda () (posix-lock db +wr+ +shared-first+ +shared-size+)))
      (setf (db-lock db) :exclusive))))

(defun unlock-to (db level)
  "Drop to :SHARED or :NONE."
  (when (and (lockable-p db) (not (eq (db-lock db) :none)))
    (ecase level
      (:shared
       (unless (eq (db-lock db) :shared)
         (posix-lock db +rd+ +shared-first+ +shared-size+)
         (posix-lock db +un+ +pending-byte+ 2)
         (setf (db-lock db) :shared)))
      (:none
       (posix-lock db +un+ +pending-byte+ (+ 2 +shared-size+))
       (setf (db-lock db) :none)))))

(defun handle-hot-journal (db)
  "A journal exists.  If no process is committing it (nobody holds
RESERVED), it is hot: roll it back under an exclusive lock."
  (unless (db-readonly db)
    (when (posix-lock db +wr+ +reserved-byte+ 1)
      (unwind-protect
           (progn
             (busy-wait (lambda () (posix-lock db +wr+ +pending-byte+ 1)))
             (busy-wait (lambda () (posix-lock db +wr+ +shared-first+ +shared-size+)))
             (recover-hot-journal db)
             (clrhash (db-cache db))
             (setf (db-schema db) nil))
        (posix-lock db +rd+ +shared-first+ +shared-size+)
        (posix-lock db +un+ +pending-byte+ 2)))))

(defun validate-cache (db)
  "Drop cached pages if the file changed since we last looked."
  (let ((s (db-stream db)))
    (when (and s (not (db-txn db)))
      (let ((len (file-length s)))
        (if (< len 100)
            (progn (clrhash (db-cache db))
                   (setf (db-page-count db) 0 (db-schema db) nil))
            (let ((h (make-octets 100)))
              (file-position s 0)
              (read-sequence h s)
              (let ((cached (gethash 1 (db-cache db))))
                (unless (and cached (every #'= (subseq cached 0 100) h))
                  (clrhash (db-cache db))
                  (setf (db-schema db) nil)
                  (let ((ps (parse-header db h)))
                    (setf (db-page-count db)
                          (let ((hdr-count (get-u32 h +hdr-page-count+)))
                            (if (and (plusp hdr-count)
                                     (= (get-u32 h +hdr-change-counter+)
                                        (get-u32 h +hdr-version-valid-for+)))
                                hdr-count
                                (ceiling len ps)))))))))))))
