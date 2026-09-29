;;;; threads.lisp — several connections, and several threads, of one process
;;;; on one database file: the in-process half of SQLite's locking (one lock
;;;; per file per process, arbitrated between its connections), the WAL
;;;; index's in-process locks, connections shared by threads, and
;;;; descriptors closed while the process still holds locks.

(in-package #:sqlite-pure.test)

(defvar *threads-failures* 0)

(defun tcheck (name ok &optional detail)
  (format t "~&~:[FAIL~;ok  ~] ~a~@[  ~a~]~%" ok name (unless ok detail))
  (unless ok (incf *threads-failures*))
  ok)

(defun spawn (fn) (sb-thread:make-thread fn))
(defun join-all (threads) (mapcar #'sb-thread:join-thread threads))

(defmacro with-busy-timeout ((db seconds) &body body)
  `(progn (setf (sqlite-pure::db-busy-timeout ,db) ,seconds) ,@body))

(defun busy-p (thunk)
  "Does THUNK signal \"database is locked\"?"
  (handler-case (progn (funcall thunk) nil)
    (sqlp:sqlite-error (c) (eq (sqlp:sqlite-error-code c) :busy))))

(defun fresh (path &optional wal)
  (dolist (suffix '("" "-journal" "-wal" "-shm"))
    (let ((p (probe-file (concatenate 'string path suffix)))) (when p (delete-file p))))
  (sqlp:with-database (db path)
    (when wal (sqlp:execute db "PRAGMA journal_mode=WAL"))
    (sqlp:execute db "CREATE TABLE t(k INTEGER PRIMARY KEY, thread, v)")))

(defun writers (path n m)
  "N threads, each on its own connection, each committing M transactions
of two rows (v and -v), half of them autocommit single rows instead;
return the rows inserted, as counted by the threads."
  (let ((threads
          (loop for i below n
                collect (let ((i i))
                          (spawn (lambda ()
                                   (sqlp:with-database (db path)
                                     (with-busy-timeout (db 30)
                                       (let ((rows 0))
                                         (dotimes (j m rows)
                                           (if (evenp j)
                                               (sqlp:with-transaction (db)
                                                 (sqlp:execute db "INSERT INTO t(thread, v) VALUES (?, ?)" i j)
                                                 (sqlp:execute db "INSERT INTO t(thread, v) VALUES (?, ?)" i (- j))
                                                 (incf rows 2))
                                               (progn
                                                 (sqlp:execute db "INSERT INTO t(thread, v) VALUES (?, 0)" i)
                                                 (incf rows)))))))))))))
    (reduce #'+ (join-all threads))))

(defun readers-see-consistent (path n seconds)
  "N reader threads: every snapshot has sum(v) = 0 (each transaction adds
v and -v together).  Returns the number of snapshots seen and the number
that were inconsistent."
  (let* ((deadline (+ (get-internal-real-time) (* seconds internal-time-units-per-second)))
         (threads
           (loop repeat n
                 collect (spawn (lambda ()
                                  (sqlp:with-database (db path)
                                    (with-busy-timeout (db 30)
                                      (let ((seen 0) (bad 0))
                                        (loop while (< (get-internal-real-time) deadline)
                                              do (let ((s (sqlp:query-value db "SELECT coalesce(sum(v), 0) FROM t")))
                                                   (incf seen)
                                                   (unless (eql s 0) (incf bad))))
                                        (list seen bad)))))))))
    (let ((r (join-all threads)))
      (values (reduce #'+ r :key #'first) (reduce #'+ r :key #'second)))))

(defun contention (path wal)
  (fresh path wal)
  (let* ((reader-results nil)
         (reader (spawn (lambda ()
                          (setf reader-results
                                (multiple-value-list (readers-see-consistent path 3 3))))))
         (inserted (writers path 6 60)))
    (sb-thread:join-thread reader)
    (sqlp:with-database (db path)
      (let ((mode (if wal "wal" "rollback")))
        (tcheck (format nil "~a: 6 writer threads, every row there" mode)
                (eql (sqlp:query-value db "SELECT count(*) FROM t") inserted)
                (list (sqlp:query-value db "SELECT count(*) FROM t") inserted))
        (tcheck (format nil "~a: sum(v) = 0" mode) (eql (sqlp:query-value db "SELECT sum(v) FROM t") 0))
        (tcheck (format nil "~a: integrity" mode)
                (equal (sqlp:query-value db "PRAGMA integrity_check") "ok"))
        (tcheck (format nil "~a: readers saw only whole transactions (~d snapshots)" mode (first reader-results))
                (and (plusp (first reader-results)) (zerop (second reader-results)))
                reader-results)))))

(defun shared-connection (path)
  (fresh path)
  (sqlp:with-database (db path)
    (with-busy-timeout (db 30)
      (join-all (loop for i below 8
                      collect (let ((i i))
                                (spawn (lambda ()
                                         (dotimes (j 50)
                                           (sqlp:execute db "INSERT INTO t(thread, v) VALUES (?, ?)" i j)
                                           (sqlp:query-value db "SELECT count(*) FROM t")))))))
      (tcheck "one connection, 8 threads: every row there"
              (eql (sqlp:query-value db "SELECT count(*) FROM t") 400))
      (tcheck "one connection, 8 threads: integrity"
              (equal (sqlp:query-value db "PRAGMA integrity_check") "ok")))))

(defun busy-rules (path)
  "SQLite's answers when two connections of one process meet."
  (fresh path)
  (sqlp:with-database (a path)
    (sqlp:with-database (b path)
      (with-busy-timeout (a 0)
        (with-busy-timeout (b 0)
          (sqlp:execute a "BEGIN IMMEDIATE")
          (tcheck "RESERVED held: another connection's write is locked out"
                  (busy-p (lambda () (sqlp:execute b "INSERT INTO t(v) VALUES (1)"))))
          (tcheck "RESERVED held: another connection still reads"
                  (not (busy-p (lambda () (sqlp:query-value b "SELECT count(*) FROM t")))))
          (sqlp:execute b "BEGIN")
          (sqlp:query-value b "SELECT count(*) FROM t")      ; b now holds SHARED in a read transaction
          (sqlp:execute a "INSERT INTO t(v) VALUES (1)")
          (tcheck "a reader's SHARED keeps a writer from committing"
                  (busy-p (lambda () (sqlp:execute a "COMMIT"))))
          (tcheck "a read transaction cannot take the write lock from under a writer (BUSY at once)"
                  (let ((start (get-internal-real-time)))
                    (with-busy-timeout (b 5)
                      (and (busy-p (lambda () (sqlp:execute b "INSERT INTO t(v) VALUES (2)")))
                           (< (- (get-internal-real-time) start) internal-time-units-per-second)))))
          (sqlp:execute b "COMMIT")
          (tcheck "the reader gone, the writer commits"
                  (not (busy-p (lambda () (sqlp:execute a "COMMIT")))))
          (tcheck "the other connection sees the commit"
                  (eql (sqlp:query-value b "SELECT count(*) FROM t") 1))
          (sqlp:execute a "BEGIN EXCLUSIVE")
          (tcheck "EXCLUSIVE held: another connection cannot even read"
                  (busy-p (lambda () (sqlp:query-value b "SELECT count(*) FROM t"))))
          (sqlp:execute a "ROLLBACK")
          (tcheck "EXCLUSIVE gone: it reads again"
                  (not (busy-p (lambda () (sqlp:query-value b "SELECT count(*) FROM t"))))))))))

(defun closing-keeps-locks (path sqlite3)
  "A connection closed while another of this process holds a lock must not
drop that lock (POSIX would, on closing any descriptor of the file)."
  (fresh path)
  (sqlp:with-database (a path)
    (sqlp:execute a "BEGIN IMMEDIATE")
    (sqlp:execute a "INSERT INTO t(v) VALUES (1)")
    (let ((b (sqlp:open-database path)))
      (sqlp:query-value b "SELECT count(*) FROM t")
      (sqlp:close-database b))
    (let ((out (with-output-to-string (s)
                 (sb-ext:run-program sqlite3 (list path "INSERT INTO t(v) VALUES (9);")
                                     :output s :error s :search t))))
      (tcheck "a connection closed beside a writer leaves its RESERVED lock in place"
              (search "locked" out) out))
    (sqlp:execute a "COMMIT"))
  (let ((out (with-output-to-string (s)
               (sb-ext:run-program sqlite3 (list path "INSERT INTO t(v) VALUES (9); SELECT count(*) FROM t;")
                                   :output s :error s :search t))))
    (tcheck "and once it commits, another process writes" (search "2" out) out)))

(defun run-threads (dir sqlite3)
  (setf *threads-failures* 0)
  (ensure-directories-exist (concatenate 'string dir "/"))
  (let ((path (concatenate 'string dir "/threads.db")))
    (busy-rules path)
    (closing-keeps-locks path sqlite3)
    (shared-connection path)
    (contention path nil)
    (contention path t))
  (format t "~&threads: ~:[~d failed~;passed~*~]~%" (zerop *threads-failures*) *threads-failures*)
  (zerop *threads-failures*))
