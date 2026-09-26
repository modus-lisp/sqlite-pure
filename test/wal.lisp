;;;; test/wal.lisp — writing WAL-mode databases, checked by SQLite processes.
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

(defun run-wal (dir)
  (let ((ok t) (sqlite-pure::*busy-timeout* 0.3))
    (flet ((check (name got want)
             (let ((pass (equal got want)))
               (format t "~:[FAIL~;ok  ~] ~a~@[~%       want ~s~%       got  ~s~]~%"
                       pass name (unless pass want) (unless pass got))
               (unless pass (setf ok nil)))))
      (ensure-directories-exist (format nil "~a/" dir))
      (let ((path (format nil "~a/w.db" dir)))
        (dolist (suffix '("" "-wal" "-shm"))
          (let ((p (probe-file (format nil "~a~a" path suffix)))) (when p (delete-file p))))
        (py-out (format nil "import sqlite3; c=sqlite3.connect('~a'); c.execute('pragma journal_mode=wal'); c.execute('create table t(a integer primary key, b)'); c.executemany('insert into t(b) values (?)', [('x'*i,) for i in range(300)]); c.commit(); c.close()" path))
        ;; 1. a session: writes, a rollback, reads of our own writes
        (s:with-database (db path)
          (check "reports wal" (s:query-value db "PRAGMA journal_mode") "wal")
          (s:execute db "INSERT INTO t(b) VALUES ('mine')")
          (s:with-transaction (db) (s:execute db "UPDATE t SET b = upper(b) WHERE a % 10 = 0"))
          (ignore-errors (s:with-transaction (db) (s:execute db "DELETE FROM t") (error "abandon")))
          (check "rollback kept rows" (s:query-value db "SELECT count(*) FROM t") 301)
          (check "sees own writes" (s:query-value db "SELECT b FROM t WHERE a = 301") "mine")
          (check "SQLite locked out during the session"
                 (and (search "database is locked" (sqlite-says path "select count(*) from t")) t) t)
          (check "-wal holds the commits" (and (probe-file (format nil "~a-wal" path)) t) t))
        (check "no -wal after close" (probe-file (format nil "~a-wal" path)) nil)
        (check "SQLite reads it" (sqlite-says path "select count(*), sum(length(b)) from t")
               "[(301, 44854)]")
        (check "SQLite integrity" (sqlite-says path "pragma integrity_check") "[('ok',)]")
        (check "still WAL mode" (sqlite-says path "pragma journal_mode") "[('wal',)]")
        ;; 2. a crash: another process commits twice, starts a third, dies
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
               (sqlite-says path "select b from t where a > 301 order by a") "[('c1',), ('c2',)]")
        (check "integrity after recovery" (sqlite-says path "pragma integrity_check") "[('ok',)]")
        ;; 3. continue a log SQLite left: copy the files while SQLite has frames outstanding
        (let ((src (format nil "~a/s.db" dir)) (cp (format nil "~a/cp.db" dir)))
          (dolist (f (list src cp))
            (dolist (suffix '("" "-wal" "-shm"))
              (let ((p (probe-file (format nil "~a~a" f suffix)))) (when p (delete-file p)))))
          (py-out (format nil "import sqlite3, shutil
c=sqlite3.connect('~a'); c.execute('pragma journal_mode=wal'); c.execute('pragma wal_autocheckpoint=0')
c.execute('create table t(a integer primary key, b)'); c.executemany('insert into t(b) values (?)', [(i,) for i in range(500)]); c.commit()
c.execute('update t set b = b * 2 where a < 100'); c.commit()
shutil.copy('~a', '~a'); shutil.copy('~a-wal', '~a-wal')" src src cp src cp))
          (s:with-database (db cp)
            (check "reads SQLite's log" (s:query-value db "SELECT sum(b) FROM t") (+ (* 500 499/2) (* 98 99/2)))
            (s:execute db "DELETE FROM t WHERE a > 400")
            (s:execute db "INSERT INTO t(b) VALUES (-1)"))
          (check "SQLite reads the continued log" (sqlite-says cp "select count(*), sum(b) from t")
                 (format nil "[(401, ~d)]" (+ (* 400 399/2) (* 98 99/2) -1)))
          (check "integrity" (sqlite-says cp "pragma integrity_check") "[('ok',)]"))
        ;; 4. switching modes
        (let ((m (format nil "~a/m.db" dir)))
          (dolist (suffix '("" "-wal" "-shm"))
            (let ((p (probe-file (format nil "~a~a" m suffix)))) (when p (delete-file p))))
          (s:with-database (db m)
            (s:execute db "CREATE TABLE t(x)")
            (check "to wal" (s:query-value db "PRAGMA journal_mode = WAL") "wal")
            (s:execute db "INSERT INTO t VALUES (1), (2)"))
          (check "SQLite sees wal mode" (sqlite-says m "pragma journal_mode") "[('wal',)]")
          (check "and the rows" (sqlite-says m "select sum(x) from t") "[(3,)]")
          (s:with-database (db m)
            (s:execute db "INSERT INTO t VALUES (3)")
            (check "back to delete" (s:query-value db "PRAGMA journal_mode = DELETE") "delete"))
          (check "SQLite sees delete mode" (sqlite-says m "pragma journal_mode") "[('delete',)]")
          (check "and all rows" (sqlite-says m "select sum(x) from t") "[(6,)]")
          (check "no log files" (list (probe-file (format nil "~a-wal" m)) (probe-file (format nil "~a-shm" m)))
                 '(nil nil)))))
    (format t "wal: ~:[FAILED~;passed~]~%" ok)
    ok))
