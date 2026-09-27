;;;; test/wal.lisp — WAL-mode databases shared with live SQLite connections.
;;;; SBCL only (run-program).

(in-package #:sqlite-pure.test)

(defun py-out (script)
  "Run a Python snippet; return its stdout as a trimmed string."
  (string-trim '(#\Newline #\Space)
               (with-output-to-string (o)
                 (sb-ext:run-program "python3" (list "-c" script) :search t :output o :error o))))

(defun sqlite-says (path sql)
  (py-out (format nil "import sqlite3; c=sqlite3.connect('~a', timeout=0.2)
try:
    print(repr(c.execute(\"~a\").fetchall()))
except Exception as e:
    print('ERR', e)" path sql)))

;;; A peer: a Python process holding one SQLite connection open, running
;;; the statements we send it one line at a time (autocommit unless BEGIN).
(defparameter *peer-script* "
import sqlite3, sys
c = sqlite3.connect(sys.argv[1], timeout=float(sys.argv[2]), isolation_level=None)
for line in sys.stdin:
    q = line.rstrip('\\n')
    if q == 'QUIT':
        break
    try:
        print(repr(c.execute(q).fetchall()))
    except Exception as e:
        print('ERR', e)
    sys.stdout.flush()
c.close()
print('CLOSED')
sys.stdout.flush()
")

(defun peer-start (path &optional (timeout 0.3))
  (sb-ext:run-program "python3" (list "-u" "-c" *peer-script* path (princ-to-string timeout))
                      :search t :input :stream :output :stream :error nil :wait nil))

(defun peer (proc sql)
  (let ((in (sb-ext:process-input proc)))
    (write-line sql in)
    (finish-output in)
    (read-line (sb-ext:process-output proc) nil "EOF")))

(defun peer-stop (proc)
  (prog1 (peer proc "QUIT")
    (sb-ext:process-wait proc)
    (sb-ext:process-close proc)))

(defun remove-db-files (path)
  (dolist (suffix '("" "-wal" "-shm" "-journal"))
    (let ((p (probe-file (format nil "~a~a" path suffix)))) (when p (delete-file p)))))

(defun file-size (path)
  (let ((p (probe-file path)))
    (if p (with-open-file (s p :element-type '(unsigned-byte 8)) (file-length s)) 0)))

(defun run-wal (dir)
  (let ((ok t) (sqlite-pure::*busy-timeout* 0.3))
    (flet ((check (name got want)
             (let ((pass (equal got want)))
               (format t "~:[FAIL~;ok  ~] ~a~@[~%       want ~s~%       got  ~s~]~%"
                       pass name (unless pass want) (unless pass got))
               (unless pass (setf ok nil))))
           (locked-p (thunk)
             (handler-case (progn (funcall thunk) nil)
               (s:sqlite-error (e) (and (search "locked" (s:sqlite-error-message e)) t)))))
      (ensure-directories-exist (format nil "~a/" dir))
      (let ((path (format nil "~a/w.db" dir)))
        (remove-db-files path)
        (py-out (format nil "import sqlite3; c=sqlite3.connect('~a'); c.execute('pragma journal_mode=wal'); c.execute('create table t(a integer primary key, b)'); c.executemany('insert into t(b) values (?)', [('x'*i,) for i in range(300)]); c.commit(); c.close()" path))
        ;; 1. side by side with a live SQLite connection
        (let ((p (peer-start path)))
          (check "peer attached" (peer p "select count(*) from t") "[(300,)]")
          (s:with-database (db path)
            (check "reports wal" (s:query-value db "PRAGMA journal_mode") "wal")
            (check "reads what SQLite wrote" (s:query-value db "SELECT count(*) FROM t") 300)
            (s:execute db "INSERT INTO t(b) VALUES ('mine')")
            (check "SQLite sees our commit" (peer p "select b from t where a = 301") "[('mine',)]")
            (peer p "insert into t(b) values ('theirs')")
            (check "we see SQLite's commit" (s:query-value db "SELECT b FROM t WHERE a = 302") "theirs")
            (s:with-transaction (db) (s:execute db "UPDATE t SET b = upper(b) WHERE a % 10 = 0"))
            (ignore-errors (s:with-transaction (db) (s:execute db "DELETE FROM t") (error "abandon")))
            (check "rollback kept rows" (peer p "select count(*) from t") "[(302,)]")
            (check "and our update" (peer p "select b from t where a = 10") (format nil "[('~a',)]" (make-string 9 :initial-element #\X)))
            ;; a SQLite reader's snapshot survives our writes and our checkpoint
            (peer p "begin")
            (check "peer snapshot" (peer p "select count(*) from t") "[(302,)]")
            (dotimes (i 5) (s:execute db "INSERT INTO t(b) VALUES ('later')"))
            (let ((ck (s:query db "PRAGMA wal_checkpoint")))
              (check "checkpoint stops at the reader" (< (third (first ck)) (second (first ck))) t))
            (check "peer snapshot intact" (peer p "select count(*), sum(length(b)) from t")
                   (peer p "select count(*), sum(length(b)) from t where a <= 302"))
            (check "peer still at 302" (peer p "select count(*) from t") "[(302,)]")
            (peer p "commit")
            (check "peer sees them after" (peer p "select count(*) from t") "[(307,)]")
            ;; our snapshot survives SQLite's writes and SQLite's checkpoint
            (s:execute db "BEGIN")
            (let ((before (s:query-value db "SELECT sum(length(b)) FROM t")))
              (peer p "insert into t(b) values ('zzzzzzzz')")
              (peer p "delete from t where a < 50")
              (check "SQLite checkpoints around our reader" (search "[(0," (peer p "pragma wal_checkpoint")) 0)
              (check "our snapshot intact" (s:query-value db "SELECT sum(length(b)) FROM t") before)
              (check "a stale snapshot cannot write"
                     (locked-p (lambda () (s:execute db "INSERT INTO t(b) VALUES ('no')"))) t)
              (s:execute db "ROLLBACK"))
            (check "fresh transaction sees them" (s:query-value db "SELECT count(*) FROM t") 259)
            ;; the write lock
            (peer p "begin immediate")
            (check "SQLite holds the write lock" (locked-p (lambda () (s:execute db "INSERT INTO t(b) VALUES ('w')"))) t)
            (check "but we can read" (s:query-value db "SELECT count(*) FROM t") 259)
            (peer p "commit")
            (s:execute db "INSERT INTO t(b) VALUES ('w')")
            (s:execute db "BEGIN IMMEDIATE")
            (s:execute db "INSERT INTO t(b) VALUES ('w2')")
            (check "we hold the write lock" (peer p "insert into t(b) values ('no')") "ERR database is locked")
            (s:execute db "COMMIT")
            (check "peer count" (peer p "select count(*) from t") "[(261,)]")
            ;; the log restarts once checkpointed, rather than growing
            (let ((sizes '()))
              (dotimes (i 12)
                (s:execute db "UPDATE t SET b = b || '.' WHERE a = 100")
                (peer p "pragma wal_checkpoint")
                (push (file-size (format nil "~a-wal" path)) sizes))
              ;; a restarted log is rewritten from the start: the file stops growing
              (check "log restarted (file stops growing)" (= (first sizes) (car (last sizes))) t)
              (check "and consistent" (peer p "select length(b) from t where a = 100") "[(111,)]"))
            (check "integrity (SQLite, while attached)" (peer p "pragma integrity_check") "[('ok',)]")
            (check "integrity (ours)" (s:query-value db "PRAGMA integrity_check") "ok"))
          (check "log kept while SQLite is attached" (and (probe-file (format nil "~a-wal" path)) t) t)
          (check "peer reads after we left" (peer p "select count(*) from t") "[(261,)]")
          (check "peer closes" (peer-stop p) "CLOSED"))
        (check "SQLite removed the log" (probe-file (format nil "~a-wal" path)) nil)
        ;; 2. many writers at once: SQLite and us, interleaved, with checkpoints
        (let* ((n 150)
               (writer (sb-ext:run-program
                        "python3"
                        (list "-c" (format nil "import sqlite3
c=sqlite3.connect('~a', timeout=10, isolation_level=None)
for i in range(~d):
    c.execute('insert into t(b) values (?)', ('py%d' % i,))
    if i % 25 == 0: c.execute('pragma wal_checkpoint')
    if i % 7 == 0: c.execute('select count(*) from t').fetchall()
c.close()" path n))
                        :search t :output nil :error nil :wait nil)))
          (let ((sqlite-pure::*busy-timeout* 10))
            (s:with-database (db path)
              (dotimes (i n)
                (s:execute db "INSERT INTO t(b) VALUES (?)" (format nil "lisp~d" i))
                (when (zerop (mod i 30)) (s:query db "PRAGMA wal_checkpoint"))
                (when (zerop (mod i 11)) (s:query db "SELECT count(*) FROM t")))
              (sb-ext:process-wait writer)
              (check "all rows from both writers" (s:query-value db "SELECT count(*) FROM t") (+ 261 n n))
              (check "both writers' rows" (s:query db "SELECT count(*) FROM t WHERE b LIKE 'py%' OR b LIKE 'lisp%'")
                     `((,(* 2 n))))))
          (check "SQLite agrees" (sqlite-says path "select count(*) from t") (format nil "[(~d,)]" (+ 261 n n)))
          (check "integrity after the storm" (sqlite-says path "pragma integrity_check") "[('ok',)]"))
        ;; 3. last one out cleans up
        (s:with-database (db path) (s:execute db "INSERT INTO t(b) VALUES ('last')"))
        (check "no -wal after the last close" (probe-file (format nil "~a-wal" path)) nil)
        (check "no -shm after the last close" (probe-file (format nil "~a-shm" path)) nil)
        (check "SQLite reads it" (sqlite-says path "select b from t order by a desc limit 1") "[('last',)]")
        ;; 4. a crash: another process commits twice, starts a third, dies
        (sb-ext:run-program "sbcl" (list "--noinform" "--non-interactive"
                                         "--eval" "(require :asdf)"
                                         "--eval" (format nil "(push #p\"~a\" asdf:*central-registry*)"
                                                          (namestring (asdf:system-source-directory "sqlite-pure")))
                                         "--eval" "(handler-bind ((warning #'muffle-warning)) (asdf:load-system \"sqlite-pure\"))"
                                         "--eval" (format nil "(let ((db (sqlp:open-database \"~a\")))
                                                     (sqlp:execute db \"INSERT INTO t(b) VALUES ('c1')\")
                                                     (sqlp:execute db \"INSERT INTO t(b) VALUES ('c2')\")
                                                     (sqlp:execute db \"BEGIN\")
                                                     (sqlp:execute db \"INSERT INTO t(b) VALUES ('uncommitted')\")
                                                     (sb-ext:exit :abort t))" path))
                            :search t :output nil :error nil)
        (check "log left behind" (and (probe-file (format nil "~a-wal" path)) t) t)
        (check "SQLite recovers committed work only"
               (sqlite-says path "select b from t order by a desc limit 2") "[('c2',), ('c1',)]")
        (check "integrity after recovery" (sqlite-says path "pragma integrity_check") "[('ok',)]")
        ;; 5. our own recovery: a log and index SQLite left
        (let ((src (format nil "~a/s.db" dir)) (cp (format nil "~a/cp.db" dir)))
          (remove-db-files src) (remove-db-files cp)
          (py-out (format nil "import sqlite3, shutil
c=sqlite3.connect('~a'); c.execute('pragma journal_mode=wal'); c.execute('pragma wal_autocheckpoint=0')
c.execute('create table t(a integer primary key, b)'); c.executemany('insert into t(b) values (?)', [(i,) for i in range(5000)]); c.commit()
c.execute('update t set b = b * 2 where a < 100'); c.commit()
shutil.copy('~a', '~a'); shutil.copy('~a-wal', '~a-wal')" src src cp src cp))
          (s:with-database (db cp)
            (check "rebuilds the index from SQLite's log" (s:query-value db "SELECT sum(b) FROM t")
                   (+ (* 5000 4999/2) (* 98 99/2)))
            (let ((p (peer-start cp)))
              (check "SQLite reads through our rebuilt index" (peer p "select sum(b) from t")
                     (format nil "[(~d,)]" (+ (* 5000 4999/2) (* 98 99/2))))
              (s:execute db "DELETE FROM t WHERE a > 400")
              (s:execute db "INSERT INTO t(b) VALUES (-1)")
              (check "SQLite reads the continued log" (peer p "select count(*), sum(b) from t")
                     (format nil "[(401, ~d)]" (+ (* 400 399/2) (* 98 99/2) -1)))
              (peer-stop p)))
          (check "integrity" (sqlite-says cp "pragma integrity_check") "[('ok',)]"))
        ;; 6. switching modes
        (let ((m (format nil "~a/m.db" dir)))
          (remove-db-files m)
          (s:with-database (db m)
            (s:execute db "CREATE TABLE t(x)")
            (check "to wal" (s:query-value db "PRAGMA journal_mode = WAL") "wal")
            (s:execute db "INSERT INTO t VALUES (1), (2)")
            (let ((p (peer-start m)))
              (check "SQLite joins" (peer p "select sum(x) from t") "[(3,)]")
              (check "cannot leave WAL while SQLite is attached"
                     (locked-p (lambda () (s:query db "PRAGMA journal_mode = DELETE"))) t)
              (check "still wal" (s:query-value db "PRAGMA journal_mode") "wal")
              (peer-stop p)))
          (check "SQLite sees wal mode" (sqlite-says m "pragma journal_mode") "[('wal',)]")
          (check "and the rows" (sqlite-says m "select sum(x) from t") "[(3,)]")
          (s:with-database (db m)
            (s:execute db "INSERT INTO t VALUES (3)")
            (check "back to delete" (s:query-value db "PRAGMA journal_mode = DELETE") "delete")
            (s:execute db "INSERT INTO t VALUES (4)"))
          (check "SQLite sees delete mode" (sqlite-says m "pragma journal_mode") "[('delete',)]")
          (check "and all rows" (sqlite-says m "select sum(x) from t") "[(10,)]")
          (check "no log files" (list (probe-file (format nil "~a-wal" m)) (probe-file (format nil "~a-shm" m)))
                 '(nil nil)))))
    (format t "wal: ~:[FAILED~;passed~]~%" ok)
    ok))
