;;;; test/locking.lisp — this library and SQLite processes sharing a file.
;;;; SBCL only (uses run-program).

(in-package #:sqlite-pure.test)

(defvar *py* "python3")

(defun py (script &key wait)
  "Run a Python snippet; with WAIT NIL return the process (running)."
  (sb-ext:run-program *py* (list "-c" script) :search t :wait wait
                                             :output *standard-output* :error *standard-output*))

(defun check (name ok)
  (format t "~:[FAIL~;ok  ~] ~a~%" ok name)
  ok)

(defun run-locking (dir)
  (let* ((path (format nil "~a/lock.db" dir))
         (sqlite-pure::*busy-timeout* 1)
         (results '()))
    (ensure-directories-exist path)
    (when (probe-file path) (delete-file path))
    (s:with-database (db path)
      (s:execute db "CREATE TABLE t(a)")
      (s:execute db "INSERT INTO t VALUES (1)"))
    (s:with-database (db path)
      ;; 1. another process changes the file between our statements
      (s:query db "SELECT count(*) FROM t")
      (py (format nil "import sqlite3; c=sqlite3.connect('~a'); c.execute('insert into t values (2)'); c.commit()" path) :wait t)
      (push (check "sees another process's commit" (= 2 (s:query-value db "SELECT count(*) FROM t"))) results)
      ;; 2. SQLite holds RESERVED (BEGIN IMMEDIATE): we can read, we cannot write
      (let ((p (py (format nil "import sqlite3,time; c=sqlite3.connect('~a', isolation_level=None); c.execute('begin immediate'); c.execute('insert into t values (3)'); time.sleep(2.5); c.execute('rollback')" path))))
        (sleep 0.7)
        (push (check "reads while SQLite holds RESERVED" (= 2 (s:query-value db "SELECT count(*) FROM t"))) results)
        (push (check "write refused while SQLite holds RESERVED"
                     (handler-case (progn (s:execute db "INSERT INTO t VALUES (9)") nil)
                       (s:sqlite-error (e) (search "locked" (s:sqlite-error-message e)))))
              results)
        (sb-ext:process-wait p))
      ;; 3. SQLite holds EXCLUSIVE: we cannot even read
      (let ((p (py (format nil "import sqlite3,time; c=sqlite3.connect('~a', isolation_level=None); c.execute('begin exclusive'); time.sleep(2.5); c.execute('commit')" path))))
        (sleep 0.7)
        (push (check "read refused while SQLite holds EXCLUSIVE"
                     (handler-case (progn (s:query db "SELECT count(*) FROM t") nil)
                       (s:sqlite-error (e) (search "locked" (s:sqlite-error-message e)))))
              results)
        (sb-ext:process-wait p))
      ;; 4. we hold a write transaction: SQLite can read the old data, not write
      (s:execute db "BEGIN")
      (s:execute db "INSERT INTO t VALUES (4)")
      (py (format nil "import sqlite3; c=sqlite3.connect('~a', timeout=0.3)
print('py-count', c.execute('select count(*) from t').fetchone()[0])
try:
    c.execute('insert into t values (5)'); c.commit(); print('py-write ok')
except sqlite3.OperationalError as e: print('py-write', e)" path) :wait t)
      (s:execute db "COMMIT")
      (py (format nil "import sqlite3; c=sqlite3.connect('~a'); print('py-count-after', c.execute('select count(*) from t').fetchone()[0])" path) :wait t))
    ;; 5. two processes insert concurrently
    (let ((p (py (format nil "import sqlite3
c=sqlite3.connect('~a', timeout=10, isolation_level=None)
for i in range(300):
    c.execute('insert into t values (?)', (1000+i,))" path))))
      (s:with-database (db path)
        (let ((sqlite-pure::*busy-timeout* 10))
          (dotimes (i 300) (s:execute db "INSERT INTO t VALUES (?)" (+ 5000 i)))))
      (sb-ext:process-wait p)
      (s:with-database (db path)
        (push (check "concurrent inserts all landed"
                     (= 603 (s:query-value db "SELECT count(*) FROM t"))) results)
        (push (check "integrity after concurrent writers"
                     (equal '(("ok")) (s:query db "PRAGMA integrity_check"))) results)))
    (py (format nil "import sqlite3; c=sqlite3.connect('~a'); print('sqlite integrity:', c.execute('pragma integrity_check').fetchone()[0], 'rows:', c.execute('select count(*) from t').fetchone()[0])" path) :wait t)
    (every #'identity results)))
