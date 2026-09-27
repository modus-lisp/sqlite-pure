;;;; test/rtree.lisp — r-trees shared with SQLite through the file: each side
;;;; modifies trees the other built.  A plain mirror table, changed by the
;;;; same statements, is the reference.  SBCL only (run-program).

(in-package #:sqlite-pure.test)

(defun py (script)
  (string-trim '(#\Newline #\Space)
               (with-output-to-string (o)
                 (sb-ext:run-program "python3" (list "-c" script) :search t :output o :error o))))

(defparameter *boxes*
  '((0 100 0 100) (10 20 30 40) (500 510 500 510) (-5 3 -5 3) (250 750 900 1100) (999 999 0 2000)))

(defun box-counts-sql (table)
  (format nil "~{(SELECT count(*) FROM ~a WHERE x0 >= ~d AND x1 <= ~d AND y0 >= ~d AND y1 <= ~d)~^, ~}"
          (loop for (a b c d) in *boxes* append (list table a b c d))))

(defun overlap-counts-sql (table)
  (format nil "~{(SELECT count(*) FROM ~a WHERE x1 >= ~d AND x0 <= ~d AND y1 >= ~d AND y0 <= ~d)~^, ~}"
          (loop for (a b c d) in *boxes* append (list table a b c d))))

(defun run-rtree-interop (dir)
  (let ((ok t))
    (flet ((check (name got want)
             (let ((pass (equal got want)))
               (format t "~:[FAIL~;ok  ~] ~a~@[~%       want ~s~%       got  ~s~]~%"
                       pass name (unless pass want) (unless pass got))
               (unless pass (setf ok nil))))
           (sqlite (path sql)
             (py (format nil "import sqlite3; c=sqlite3.connect('~a')~%print(repr(c.execute(\"~a\").fetchall()))" path sql)))
           (ours (db sql) (s:query db sql)))
      (ensure-directories-exist (format nil "~a/" dir))
      ;; 1. SQLite builds and churns a tree; we query it and change it
      (let ((path (format nil "~a/a.db" dir)))
        (when (probe-file path) (delete-file path))
        (py (format nil "import sqlite3, random
random.seed(7)
c=sqlite3.connect('~a')
c.execute('create virtual table rt using rtree(id, x0, x1, y0, y1, +tag)')
c.execute('create table m(id integer primary key, x0, x1, y0, y1, tag)')
for i in range(1, 6001):
    x=random.randint(0, 1000); y=random.randint(0, 1000); w=random.randint(0, 30); h=random.randint(0, 30)
    for t in ('rt', 'm'): c.execute('insert into %s values(?,?,?,?,?,?)' % t, (i, x, x+w, y, y+h, 'r%d' % i))
for t in ('rt', 'm'): c.execute('delete from %s where id %% 7 = 3' % t)
c.commit()" path))
        (s:with-database (db path)
          (check "we read SQLite's tree: containment counts"
                 (ours db (format nil "SELECT ~a" (box-counts-sql "rt")))
                 (ours db (format nil "SELECT ~a" (box-counts-sql "m"))))
          (check "overlap counts" (ours db (format nil "SELECT ~a" (overlap-counts-sql "rt")))
                 (ours db (format nil "SELECT ~a" (overlap-counts-sql "m"))))
          (check "every row agrees"
                 (ours db "SELECT count(*) FROM rt JOIN m USING (id) WHERE rt.x0 = m.x0 AND rt.x1 = m.x1 AND rt.y0 = m.y0 AND rt.y1 = m.y1 AND rt.tag = m.tag")
                 (ours db "SELECT count(*) FROM m"))
          (dolist (sql '("DELETE FROM ~a WHERE id % 5 = 1"
                         "UPDATE ~a SET x0 = x0 + 2000, x1 = x1 + 2000 WHERE id % 11 = 2"
                         "DELETE FROM ~a WHERE x0 BETWEEN 300 AND 420"))
            (s:execute db (format nil sql "rt")) (s:execute db (format nil sql "m")))
          (s:execute db "WITH RECURSIVE n(i) AS (SELECT 7000 UNION ALL SELECT i + 1 FROM n WHERE i < 9000) INSERT INTO rt SELECT i, i % 1000, i % 1000 + 5, (i * 37) % 1000, (i * 37) % 1000 + 9, 'ours' FROM n")
          (s:execute db "INSERT INTO m SELECT * FROM rt WHERE id >= 7000")
          (check "our rtreecheck" (ours db "SELECT rtreecheck('rt')") '(("ok"))))
        (check "SQLite's rtreecheck of our changes" (sqlite path "select rtreecheck('rt')") "[('ok',)]")
        (check "SQLite integrity_check" (sqlite path "pragma integrity_check") "[('ok',)]")
        (check "SQLite's answers match the mirror"
               (sqlite path (format nil "select ~a" (box-counts-sql "rt")))
               (sqlite path (format nil "select ~a" (box-counts-sql "m"))))
        (check "SQLite: every row agrees"
               (sqlite path "select count(*) from rt join m using (id) where rt.x0 = m.x0 and rt.x1 = m.x1 and rt.y0 = m.y0 and rt.y1 = m.y1 and rt.tag = m.tag")
               (sqlite path "select count(*) from m"))
        (check "and nothing extra" (sqlite path "select count(*) from rt") (sqlite path "select count(*) from m")))
      ;; 2. we build a tree; SQLite changes it; we read it back
      (let ((path (format nil "~a/b.db" dir)))
        (when (probe-file path) (delete-file path))
        (s:with-database (db path)
          (s:execute db "CREATE VIRTUAL TABLE rt USING rtree(id, x0, x1, y0, y1, +tag)")
          (s:execute db "CREATE TABLE m(id INTEGER PRIMARY KEY, x0, x1, y0, y1, tag)")
          (s:with-transaction (db)
            (dotimes (k 5000)
              (let* ((i (1+ k)) (x (mod (* i 7919) 1000)) (y (mod (* i 104729) 1000))
                     (w (mod i 23)) (h (mod i 19)))
                (s:execute db "INSERT INTO rt VALUES (?, ?, ?, ?, ?, ?)" i x (+ x w) y (+ y h) (format nil "t~d" i))
                (s:execute db "INSERT INTO m VALUES (?, ?, ?, ?, ?, ?)" i x (+ x w) y (+ y h) (format nil "t~d" i)))))
          (s:execute db "DELETE FROM rt WHERE id % 4 = 0")
          (s:execute db "DELETE FROM m WHERE id % 4 = 0"))
        (check "SQLite's rtreecheck of our tree" (sqlite path "select rtreecheck('rt')") "[('ok',)]")
        (check "SQLite reads our tree" (sqlite path (format nil "select ~a" (overlap-counts-sql "rt")))
               (sqlite path (format nil "select ~a" (overlap-counts-sql "m"))))
        (py (format nil "import sqlite3
c=sqlite3.connect('~a')
for t in ('rt', 'm'):
    c.execute('delete from %s where id %% 3 = 0' % t)
    c.execute('update %s set y0 = y0 - 500, y1 = y1 - 500 where id %% 10 = 1' % t)
    c.execute('insert into %s select id + 10000, x0, x1, y0, y1, tag from %s where id < 900' % (t, t))
c.commit()" path))
        (check "SQLite's rtreecheck after its changes" (sqlite path "select rtreecheck('rt')") "[('ok',)]")
        (s:with-database (db path)
          (check "we read SQLite's changes"
                 (ours db (format nil "SELECT ~a" (box-counts-sql "rt")))
                 (ours db (format nil "SELECT ~a" (box-counts-sql "m"))))
          (check "every row agrees (ours)"
                 (ours db "SELECT count(*) FROM rt JOIN m USING (id) WHERE rt.x0 = m.x0 AND rt.x1 = m.x1 AND rt.y0 = m.y0 AND rt.y1 = m.y1 AND rt.tag = m.tag")
                 (ours db "SELECT count(*) FROM m"))
          (s:execute db "DELETE FROM rt WHERE id > 100")
          (s:execute db "DELETE FROM m WHERE id > 100")
          (check "our rtreecheck after shrinking" (ours db "SELECT rtreecheck('rt')") '(("ok")))
          (s:execute db "VACUUM"))
        (check "SQLite after our shrink + VACUUM" (sqlite path "select rtreecheck('rt'), (select count(*) from rt), (select count(*) from m)")
               (sqlite path "select 'ok', (select count(*) from m), (select count(*) from m)"))
        (check "integrity" (sqlite path "pragma integrity_check") "[('ok',)]"))
      ;; 3. auto-vacuum: dropping an r-tree moves roots
      (let ((path (format nil "~a/c.db" dir)))
        (when (probe-file path) (delete-file path))
        (s:with-database (db path)
          (s:execute db "PRAGMA auto_vacuum = FULL")
          (s:execute db "CREATE TABLE a(x)")
          (s:execute db "CREATE VIRTUAL TABLE r1 USING rtree(id, a, b)")
          (s:execute db "CREATE TABLE z(y)")
          (s:execute db "CREATE VIRTUAL TABLE r2 USING rtree(id, a, b)")
          (s:execute db "WITH RECURSIVE n(i) AS (SELECT 1 UNION ALL SELECT i+1 FROM n WHERE i < 500) INSERT INTO r2 SELECT i, i, i+1 FROM n")
          (s:execute db "INSERT INTO z VALUES (1), (2)")
          (s:execute db "DROP TABLE r1"))
        (check "auto-vacuum drop: integrity" (sqlite path "pragma integrity_check") "[('ok',)]")
        (check "auto-vacuum drop: r2 intact" (sqlite path "select rtreecheck('r2'), count(*), sum(a) from r2") "[('ok', 500, 125250.0)]")
        (check "auto-vacuum drop: z intact" (sqlite path "select sum(y) from z") "[(3,)]")))
    (format t "rtree interop: ~:[FAILED~;passed~]~%" ok)
    ok))

;;; Structure: the same statements must leave the shadow tables byte for
;;; byte as SQLite leaves them (test/rtree-fuzz.py drives this).

(defun rtree-shadow-dump (db table)
  (handler-case
      (format nil "~{~a~}~{~a~}~{~a~}"
              (mapcar (lambda (r) (format nil "~d:~a;" (first r) (second r)))
                      (s:query db (format nil "SELECT nodeno, hex(data) FROM ~a_node ORDER BY 1" table)))
              (mapcar (lambda (r) (format nil "~d>~d;" (first r) (second r)))
                      (s:query db (format nil "SELECT nodeno, parentnode FROM ~a_parent ORDER BY 1" table)))
              (mapcar (lambda (r) (format nil "~d@~d;" (first r) (second r)))
                      (s:query db (format nil "SELECT rowid, nodeno FROM ~a_rowid ORDER BY 1" table))))
    (s:sqlite-error () "")))

(defun rtree-step-dumps (sql-path out-path table)
  "Run each line of SQL-PATH; after each, write ERR (if it failed) and the dump."
  (s:with-database (db ":memory:")
    (with-open-file (in sql-path)
      (with-open-file (out out-path :direction :output :if-exists :supersede)
        (loop for line = (read-line in nil) while line
              unless (zerop (length (string-trim " " line)))
                do (let ((err (handler-case (progn (s:execute db line) "")
                                (s:sqlite-error () "ERR"))))
                     (format out "~a~a~%" err (rtree-shadow-dump db table))))))))
