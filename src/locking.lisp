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

(defvar *lock-mutex* #+sbcl (sb-thread:make-mutex :name "sqlite-pure file locks") #-sbcl nil)

(defmacro with-lock-mutex (&body body)
  #+sbcl `(sb-thread:with-recursive-lock (*lock-mutex*) ,@body)
  #-sbcl `(progn ,@body))

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

(defstruct lock-queue
  (waiters 0)           ; connections of this process waiting for the lock
  (handoff nil))        ; released while they waited: theirs before anyone new

(defvar *lock-waiting* nil "Inside BUSY-WAIT, after a first attempt failed.")

(defun busy-wait (thunk &optional queue)
  "Call THUNK until it returns true or *BUSY-TIMEOUT* expires.  With QUEUE
(a LOCK-QUEUE: the lock THUNK is after), count this connection among its
waiters while it waits, so that a lock let go goes to a waiter rather than
straight back to the connection that let go of it."
  (when (funcall thunk) (return-from busy-wait t))
  (let ((deadline (+ (get-internal-real-time)
                     (* *busy-timeout* internal-time-units-per-second))))
    (when queue (with-lock-mutex (incf (lock-queue-waiters queue))))
    (unwind-protect
         (let ((*lock-waiting* t))
           (loop
             ;; >=: a zero timeout is one attempt, as SQLite with no busy
             ;; handler -- not a second one whenever the clock has not ticked
             (when (>= (get-internal-real-time) deadline)
               (error 'sqlite-error :code :busy :message "database is locked"))
             (sleep 0.005)
             (when (funcall thunk) (return t))))
      (when queue (with-lock-mutex (decf (lock-queue-waiters queue)))))))

(defun turned-away-p (queue)
  "A lock just let go with connections waiting for it: not to a newcomer."
  (and (lock-queue-handoff queue) (not *lock-waiting*)))

(defun hand-off (queue)
  (setf (lock-queue-handoff queue) (plusp (lock-queue-waiters queue))))

;;; ------------------------------------------------------------------
;;; Connections of one process to one file (unixInodeInfo)
;;;
;;; POSIX locks belong to the process, not to a descriptor: two connections
;;; of this process would never block each other, and closing either's
;;; descriptor would drop both's locks.  So, as SQLite does, the process
;;; keeps one record per file: the strongest lock any of its connections
;;; holds and how many hold SHARED; connections are arbitrated here, and
;;; fcntl is called only when the process's own lock changes.  A descriptor
;;; closed while the process holds locks on the file is closed later.

(defstruct (inode (:constructor make-inode (key)) (:include lock-queue))
  key
  (lock :none)          ; the strongest lock of this process's connections
  (nshared 0)           ; connections holding SHARED or more
  (nconn 0)             ; connections open on the file
  (deferred '()))       ; descriptors to close once no lock is held

(defvar *inodes* (make-hash-table :test 'equal))

(defun lock-rank (level)
  (ecase level (:none 0) (:shared 1) (:reserved 2) (:pending 3) (:exclusive 4)))

(defun file-key (stream path)
  "What identifies the file STREAM is open on: its device and inode."
  #+sbcl (handler-case (let ((st (sb-posix:fstat (sb-sys:fd-stream-fd stream))))
                         (list (sb-posix:stat-dev st) (sb-posix:stat-ino st)))
           (error () (list (namestring (truename path)))))
  #-sbcl (progn stream (list (namestring (truename path)))))

(defun attach-inode (db)
  "Join DB (just opened) to its file's record."
  (with-lock-mutex
    (let* ((key (file-key (db-stream db) (db-path db)))
           (ino (or (gethash key *inodes*) (setf (gethash key *inodes*) (make-inode key)))))
      (incf (inode-nconn ino))
      (setf (db-inode db) ino))))

(defun detach-inode (db)
  "DB is closing (its locks already released): close its descriptor, or
keep it until the process holds no lock on the file."
  (with-lock-mutex
    (let ((ino (db-inode db)) (s (db-stream db)))
      (cond ((null ino) (close s))
            (t (decf (inode-nconn ino))
               (if (eq (inode-lock ino) :none)
                   (close s)
                   (push s (inode-deferred ino)))
               (when (and (zerop (inode-nconn ino)) (eq (inode-lock ino) :none))
                 (remhash (inode-key ino) *inodes*)))))))

(defun %lock (db level)
  "One attempt (unixLock) to raise DB's lock to LEVEL (:SHARED :RESERVED
or :EXCLUSIVE); true on success.  A failed EXCLUSIVE leaves PENDING."
  (with-lock-mutex
    (let* ((ino (db-inode db)) (mine (db-lock db)) (process (inode-lock ino)))
      (cond
        ((>= (lock-rank mine) (lock-rank level)) t)
        ;; fairness: the lock was just let go with others waiting for it
        ((and (eq mine :none) (turned-away-p ino)) nil)
        ;; another connection of this process holds a lock in the way
        ((and (not (eq mine process))
              (or (>= (lock-rank process) (lock-rank :pending))
                  (> (lock-rank level) (lock-rank :shared))))
         nil)
        ;; SHARED beside another connection's SHARED or RESERVED
        ((and (eq level :shared) (member process '(:shared :reserved)))
         (incf (inode-nshared ino))
         (setf (db-lock db) :shared (inode-handoff ino) nil)
         t)
        (t
         ;; PENDING before SHARED (then released) and before EXCLUSIVE
         (when (or (eq level :shared)
                   (and (eq level :exclusive) (< (lock-rank mine) (lock-rank :pending))))
           (unless (posix-lock db (if (eq level :shared) +rd+ +wr+) +pending-byte+ 1)
             (return-from %lock nil)))
         (cond
           ((eq level :shared)
            (let ((got (posix-lock db +rd+ +shared-first+ +shared-size+)))
              (posix-lock db +un+ +pending-byte+ 1)
              (when got
                (setf (inode-lock ino) :shared (inode-nshared ino) 1 (db-lock db) :shared
                      (inode-handoff ino) nil))
              got))
           ;; EXCLUSIVE while another connection of this process reads (the
           ;; same file attached to this connection again does not count:
           ;; this statement is the only one it could be reading for)
           ((and (eq level :exclusive)
                 (> (inode-nshared ino) (1+ (count-if (lambda (d) (and (not (eq d db))
                                                                         (eq (db-inode d) ino)
                                                                         (not (eq (db-lock d) :none))))
                                                        (conn-dbs db)))))
            (setf (db-lock db) :pending (inode-lock ino) :pending)
            nil)
           (t
            (let ((got (if (eq level :reserved)
                           (posix-lock db +wr+ +reserved-byte+ 1)
                           (posix-lock db +wr+ +shared-first+ +shared-size+))))
              (cond (got (setf (db-lock db) level (inode-lock ino) level))
                    ((eq level :exclusive) (setf (db-lock db) :pending (inode-lock ino) :pending)))
              got))))))))

(defun %unlock (db level)
  "Lower DB's lock to LEVEL (:SHARED or :NONE) (unixUnlock)."
  (with-lock-mutex
    (let ((ino (db-inode db)) (mine (db-lock db)))
      (when (> (lock-rank mine) (lock-rank level))
        (when (> (lock-rank mine) (lock-rank :shared))
          (posix-lock db +rd+ +shared-first+ +shared-size+)
          (posix-lock db +un+ +pending-byte+ 2)
          (setf (inode-lock ino) :shared (db-lock db) :shared))
        (when (eq level :none)
          (decf (inode-nshared ino))
          (when (zerop (inode-nshared ino))
            (posix-lock db +un+ +pending-byte+ (+ 2 +shared-size+))
            (setf (inode-lock ino) :none)
            (hand-off ino)
            (mapc #'close (inode-deferred ino))
            (setf (inode-deferred ino) '()))
          (setf (db-lock db) :none))))))

(defun lock-shared (db)
  (when (db-wal db) (return-from lock-shared (wal-begin-read db)))
  (when (and (lockable-p db) (eq (db-lock db) :none))
    (busy-wait (lambda () (%lock db :shared)) (db-inode db))
    (when (probe-file (journal-path db))
      (handle-hot-journal db))
    (validate-cache db)))

(defvar *read-before-statement* '()
  "The databases whose locks this connection held before the running
statement began: an explicit transaction has read them.")

(defun lock-reserved (db)
  "RESERVED, for a write the statement did not announce (see WRITE-LOCK)."
  (when (db-wal db) (return-from lock-reserved (wal-begin-write db)))
  (when (lockable-p db)
    (lock-shared db)
    (when (eq (db-lock db) :shared)
      (if (member db *read-before-statement*)
          (unless (%lock db :reserved) (busy-error))
          (busy-wait (lambda () (%lock db :reserved)) (db-inode db))))))

(defun read-transaction-p (db)
  "Does DB hold a read transaction (a WAL snapshot, or a lock)?"
  (if (db-wal db)
      (and (wal-read-lock (db-wal db)) t)
      (not (eq (db-lock db) :none))))

(defun busy-error ()
  (error 'sqlite-error :code :busy :message "database is locked"))

(defun write-lock (db)
  "sqlite3BtreeBeginTrans for writing, at the start of a writing statement
(or BEGIN IMMEDIATE): RESERVED, SHARED with it.  Inside a transaction that
has read the database already, one attempt -- \"database is locked\" at
once, as waiting while holding SHARED could deadlock a writer waiting for
readers.  Otherwise wait with the busy timeout, letting SHARED go between
attempts: nothing has been read yet."
  (cond ((db-wal db)
         (cond ((db-readonly db))
               ((member db *read-before-statement*) (wal-begin-write db))
               ;; a snapshot gone stale while we waited (BUSY_SNAPSHOT):
               ;; nothing has been read under it, so take a new one and retry
               (t (busy-wait
                   (lambda ()
                     (handler-case (progn (wal-begin-write db) t)
                       (sqlite-error (c)
                         (unless (eq (sqlite-error-code c) :busy) (error c))
                         (wal-end-read db)
                         (wal-begin-read db)
                         nil)))))))
        ((or (not (lockable-p db)) (db-readonly db)))
        ((>= (lock-rank (db-lock db)) (lock-rank :reserved)))
        ((member db *read-before-statement*)
         (lock-shared db)
         (unless (%lock db :reserved) (busy-error)))
        (t
         (busy-wait (lambda ()
                      (lock-shared db)
                      (or (%lock db :reserved)
                          (progn (%unlock db :none) nil)))
                    (db-inode db)))))

(defun lock-exclusive (db)
  (when (lockable-p db)
    (lock-reserved db)
    (unless (eq (db-lock db) :exclusive)
      ;; PENDING stops new readers; then wait for the current ones to go
      (busy-wait (lambda () (%lock db :exclusive)) (db-inode db)))))

(defun unlock-to (db level)
  "Drop to :SHARED or :NONE."
  (when (db-wal db) (return-from unlock-to (wal-unlock db level)))
  (when (lockable-p db)
    (%unlock db level)))

(defun reserved-lock-held-p (db)
  "Does any connection, of this process or another, hold RESERVED or more
(unixCheckReservedLock)?"
  (with-lock-mutex
    (or (> (lock-rank (inode-lock (db-inode db))) (lock-rank :shared))
        #+sbcl
        (let ((fl (make-instance 'sb-posix:flock :type +wr+ :whence sb-posix:seek-set
                                                 :start +reserved-byte+ :len 1)))
          (sb-posix:fcntl (sb-sys:fd-stream-fd (db-stream db)) sb-posix:f-getlk fl)
          (/= (sb-posix:flock-type fl) +un+)))))

(defun handle-hot-journal (db)
  "A journal exists.  If no connection is committing it (nobody holds
RESERVED), it is hot: roll it back under an exclusive lock."
  (unless (or (db-readonly db) (reserved-lock-held-p db))
    (unwind-protect
         (progn
           (busy-wait (lambda () (%lock db :exclusive)))
           ;; the journal may have gone while we waited
           (when (probe-file (journal-path db))
             (recover-hot-journal db))
           (clrhash (db-cache db))
           (setf (db-schema db) nil))
      (%unlock db :shared))))

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
