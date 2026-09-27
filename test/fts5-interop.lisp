;;;; test/fts5-interop.lisp — FTS5 indexes shared with SQLite through the
;;;; file: large, multi-page, multi-segment indexes built by either side
;;;; (SQLite's include doclist indexes and incremental merges left half
;;;; done), queried and modified by the other, checked with SQLite's own
;;;; 'integrity-check'.  SBCL only (run-program).

(in-package #:sqlite-pure.test)

(defun py-run (script)
  (let ((out (string-trim '(#\Newline #\Space)
                          (with-output-to-string (o)
                            (sb-ext:run-program "python3" (list "-c" script) :search t :output o :error o)))))
    (when (search "Error" out) (format t "  python: ~a~%" out))
    out))

(defparameter *fts-words*
  '("alpha" "beta" "gamma" "delta" "epsilon" "zeta" "eta" "theta" "iota" "kappa" "lambda" "mu"
    "common" "rare" "sqlite" "lisp" "index" "segment" "merge" "page" "token" "phrase" "near" "prefix"))

(defparameter *fts-queries*
  '("common" "alpha" "alpha OR rare" "common AND lisp" "common NOT alpha" "\"alpha beta\"" "seg*" "pre*"
    "NEAR(sqlite lisp, 3)" "a:rare" "b:common" "{a b}:token" "^alpha" "rare*" "zeta OR eta OR theta"))

(defun fts-query-sql (q)
  (format nil "SELECT rowid, printf('%.17g', bm25(ft)), highlight(ft, 0, '[', ']') FROM ft WHERE ft MATCH '~a' ORDER BY rowid"
          (sqlite-pure::substitute-string "'" "''" q)))

(defun run-fts5-interop (dir)
  (let ((ok t))
    (flet ((check (name got want)
             (let ((pass (equal got want)))
               (format t "~:[FAIL~;ok  ~] ~a~@[~%       want ~a~%       got  ~a~]~%"
                       pass name (unless pass (subseq want 0 (min 300 (length want))))
                       (unless pass (subseq got 0 (min 300 (length got)))))
               (unless pass (setf ok nil))))
           (sqlite (path sql)
             (py-run (format nil "import sqlite3; c=sqlite3.connect('~a')~%try:~%  print(repr(c.execute(\"~a\").fetchall()))~%except Exception as e: print('ERR', e)"
                             path (sqlite-pure::substitute-string "\"" "\\\"" sql))))
           (ours (path sql)
             (s:with-database (db path)
               (let ((rows (handler-case (s:query db sql) (s:sqlite-error (e) (format nil "ERR ~a" (s:sqlite-error-message e))))))
                 (py-repr rows)))))
      (ensure-directories-exist (format nil "~a/" dir))
      ;; 1. SQLite builds a big index in many transactions, small pages
      (let ((path (format nil "~a/a.db" dir)))
        (when (probe-file path) (delete-file path))
        (py-run (format nil "import sqlite3, random
random.seed(11)
W=~a
c=sqlite3.connect('~a', isolation_level=None)
c.execute(\"create virtual table ft using fts5(a, b, prefix='2')\")
c.execute(\"insert into ft(ft, rank) values('pgsz', 128)\")
for t in range(60):
    c.execute('begin')
    for i in range(40):
        c.execute('insert into ft(a, b) values(?, ?)', (' '.join(random.choice(W) for _ in range(random.randint(1, 12))), ' '.join(['common'] * random.randint(0, 3) + [random.choice(W) for _ in range(random.randint(0, 8))])))
    c.execute('commit')
    if t % 7 == 3: c.execute('delete from ft where rowid % 11 = ' + str(t % 11))
    if t % 13 == 5: c.execute(\"update ft set b = 'updated common ' || b where rowid % 17 = 2\")
c.execute(\"insert into ft(ft, rank) values('merge', 30)\")
" (py-list *fts-words*) path))
        (check "SQLite built it (rows, several segments, doclist indexes)"
               (sqlite path "select (select count(*) > 1000 from ft), (select count(distinct id>>37) > 1 from ft_data where id > 10), (select count(*) > 0 from ft_data where (id>>36)&1)")
               "[(1, 1, 1)]")
        (dolist (q *fts-queries*)
          (check (format nil "we read SQLite's index: ~a" q) (ours path (fts-query-sql q)) (sqlite path (fts-query-sql q))))
        ;; we modify it
        (s:with-database (db path)
          (s:execute db "BEGIN")
          (loop for i from 1 to 300
                do (s:execute db "INSERT INTO ft(a, b) VALUES (?, ?)"
                              (format nil "~{~a~^ ~}" (loop repeat (1+ (mod (* i 7) 11)) collect (nth (mod (* i 13) 24) *fts-words*)))
                              (format nil "common lisp ~a" (nth (mod i 24) *fts-words*))))
          (s:execute db "COMMIT")
          (s:execute db "DELETE FROM ft WHERE rowid % 5 = 0")
          (s:execute db "UPDATE ft SET a = 'rewritten alpha beta' WHERE rowid % 9 = 4")
          (s:execute db "INSERT INTO ft(ft) VALUES ('integrity-check')"))
        (check "SQLite's integrity-check of our changes" (sqlite path "insert into ft(ft) values('integrity-check')") "[]")
        (dolist (q *fts-queries*)
          (check (format nil "both agree after our changes: ~a" q) (ours path (fts-query-sql q)) (sqlite path (fts-query-sql q))))
        (s:with-database (db path) (s:execute db "INSERT INTO ft(ft) VALUES ('optimize')"))
        (check "SQLite's integrity-check after our optimize" (sqlite path "insert into ft(ft) values('integrity-check')") "[]")
        (check "one segment" (sqlite path "select count(distinct id>>37) from ft_data where id > 10") "[(1,)]")
        (check "agree after optimize" (ours path (fts-query-sql "common OR alpha")) (sqlite path (fts-query-sql "common OR alpha"))))
      ;; 2. we build a big index; SQLite checks it, modifies it; we read back
      (let ((path (format nil "~a/b.db" dir)))
        (when (probe-file path) (delete-file path))
        (s:with-database (db path)
          (s:execute db "CREATE VIRTUAL TABLE ft USING fts5(a, b, prefix='2')")
          (s:execute db "INSERT INTO ft(ft, rank) VALUES ('pgsz', 64)")
          (dotimes (tx 40)
            (s:with-transaction (db)
              (dotimes (i 30)
                (let ((k (+ (* tx 30) i)))
                  (s:execute db "INSERT INTO ft(a, b) VALUES (?, ?)"
                             (format nil "~{~a~^ ~}" (loop for j below (1+ (mod k 9)) collect (nth (mod (+ k (* j 5)) 24) *fts-words*)))
                             (format nil "common ~a ~a" (nth (mod (* k 3) 24) *fts-words*) k)))))
            (when (= (mod tx 6) 2) (s:execute db (format nil "DELETE FROM ft WHERE rowid % 13 = ~d" (mod tx 13))))))
        (check "our index is non-trivial" (sqlite path "select count(*) > 800, (select count(*) > 50 from ft_data) from ft") "[(1, 1)]")
        (check "SQLite's integrity-check of our index" (sqlite path "insert into ft(ft) values('integrity-check')") "[]")
        (dolist (q *fts-queries*)
          (check (format nil "SQLite reads our index: ~a" q) (sqlite path (fts-query-sql q)) (ours path (fts-query-sql q))))
        (py-run (format nil "import sqlite3
c=sqlite3.connect('~a', isolation_level=None)
c.execute('begin')
for i in range(500): c.execute('insert into ft(a, b) values(?, ?)', ('sqlite wrote alpha %d' % i, 'common near lisp'))
c.execute('commit')
c.execute('delete from ft where rowid % 4 = 1')
c.execute(\"insert into ft(ft, rank) values('merge', 50)\")
" path))
        (s:with-database (db path) (s:execute db "INSERT INTO ft(ft) VALUES ('integrity-check')"))
        (dolist (q *fts-queries*)
          (check (format nil "we read SQLite's changes: ~a" q) (ours path (fts-query-sql q)) (sqlite path (fts-query-sql q))))))
    (format t "fts5 interop: ~:[FAILED~;passed~]~%" ok)
    ok))

(defun py-list (xs) (format nil "[~{'~a'~^, ~}]" xs))

(defun py-repr (rows)
  "Rows rendered as Python's repr would render them."
  (if (stringp rows)
      rows
      (format nil "[~{~a~^, ~}]"
              (mapcar (lambda (r)
                        (format nil "(~{~a~^, ~}~:[~;,~])" (mapcar #'py-value r) (= (length r) 1)))
                      rows))))

(defun py-value (v)
  (cond ((eq v :null) "None")
        ((integerp v) (princ-to-string v))
        ((stringp v) (format nil "'~a'" (sqlite-pure::substitute-string "'" "\\'" v)))
        (t (princ-to-string v))))
