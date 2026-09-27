;;;; test/fts3-interop.lisp — FTS3/4 indexes shared with SQLite through the
;;;; file: large, multi-level segment b-trees (small pages), prefix indexes,
;;;; incremental merges left half done, external content, language ids and
;;;; order=desc, built by either side, queried and modified by the other,
;;;; and checked with SQLite's own 'integrity-check'.  Needs
;;;; test/fts5-interop.lisp (for its Python helpers).  SBCL only.

(in-package #:sqlite-pure.test)

(defparameter *fts3-queries*
  '("common" "alpha" "alpha OR rare" "common AND lisp" "common NOT alpha" "\"alpha beta\"" "seg*" "pre*"
    "sqlite NEAR/3 lisp" "a:rare" "b:common" "^alpha" "rare*" "zeta OR eta OR theta" "common -alpha"
    "(alpha OR beta) NOT (gamma OR delta)" "\"common lisp\" NEAR merge" "p*" "i*" "near"))

(defun fts3-query-sql (q &optional (table "ft"))
  (format nil "SELECT docid, offsets(~a), snippet(~a, '[', ']', '..', -1, 6), hex(matchinfo(~a, 'pcnalsxyb')) FROM ~a WHERE ~a MATCH '~a'"
          table table table table table (sqlite-pure::substitute-string "'" "''" q)))

(defun fts3-shadow-dump-sql (table)
  (format nil "SELECT 'segdir', level, idx, start_block, leaves_end_block, end_block, hex(root) FROM ~a_segdir UNION ALL SELECT 'seg', blockid, hex(block), NULL, NULL, NULL, NULL FROM ~a_segments UNION ALL SELECT 'stat', id, hex(value), NULL, NULL, NULL, NULL FROM ~a_stat ORDER BY 1, 2, 3"
          table table table))

(defun run-fts3-interop (dir)
  (let ((ok t))
    (flet ((check (name got want)
             (let ((pass (equal got want)))
               (format t "~:[FAIL~;ok  ~] ~a~@[~%       want ~a~%       got  ~a~]~%"
                       pass name (unless pass (subseq want 0 (min 400 (length want))))
                       (unless pass (subseq got 0 (min 400 (length got)))))
               (unless pass (setf ok nil))))
           (sqlite (path sql)
             (py-run (format nil "import sqlite3; c=sqlite3.connect('~a')~%try:~%  print(repr(c.execute(\"~a\").fetchall()))~%except Exception as e: print('ERR', e)"
                             path (sqlite-pure::substitute-string "\"" "\\\"" sql))))
           (ours (path sql)
             (s:with-database (db path)
               (let ((rows (handler-case (s:query db sql) (s:sqlite-error (e) (format nil "ERR ~a" (s:sqlite-error-message e))))))
                 (py-repr rows)))))
      (ensure-directories-exist (format nil "~a/" dir))
      ;; 1. SQLite builds a big FTS4 index: small pages (deep segment
      ;;    b-trees), a prefix index, many transactions, deletes and updates,
      ;;    and an incremental merge left unfinished
      (let ((path (format nil "~a/a.db" dir)))
        (when (probe-file path) (delete-file path))
        (py-run (format nil "import sqlite3, random
random.seed(21)
W=~a
c=sqlite3.connect('~a', isolation_level=None)
c.execute('pragma page_size=512')
c.execute(\"create virtual table ft using fts4(a, b, prefix='2')\")
for t in range(50):
    c.execute('begin')
    for i in range(30):
        c.execute('insert into ft(a, b) values(?, ?)', (' '.join(random.choice(W) for _ in range(random.randint(1, 12))), ' '.join(['common'] * random.randint(0, 3) + [random.choice(W) for _ in range(random.randint(0, 8))])))
    c.execute('commit')
    if t % 7 == 3: c.execute('delete from ft where docid % 11 = ' + str(t % 11))
    if t % 13 == 5: c.execute(\"update ft set b = 'updated common ' || b where docid % 17 = 2\")
c.execute(\"insert into ft(ft) values('merge=3,4')\")
c.execute(\"insert into ft(ft) values('merge=2,4')\")
" (py-list *fts-words*) path))
        (check "SQLite built it (rows, several levels, an unfinished merge)"
               (sqlite path "select (select count(*) > 1000 from ft), (select count(distinct level) > 1 from ft_segdir), (select count(*) from ft_stat where id = 1), (select count(*) > 0 from ft_segdir where start_block > 0)")
               "[(1, 1, 1, 1)]")
        (dolist (q *fts3-queries*)
          (check (format nil "we read SQLite's index: ~a" q) (ours path (fts3-query-sql q)) (sqlite path (fts3-query-sql q))))
        ;; we modify it: a transaction of inserts, deletes, updates, more merging
        (s:with-database (db path)
          (s:execute db "BEGIN")
          (loop for i from 1 to 300
                do (s:execute db "INSERT INTO ft(a, b) VALUES (?, ?)"
                              (format nil "~{~a~^ ~}" (loop repeat (1+ (mod (* i 7) 11)) collect (nth (mod (* i 13) 24) *fts-words*)))
                              (format nil "common lisp ~a" (nth (mod i 24) *fts-words*))))
          (s:execute db "COMMIT")
          (s:execute db "DELETE FROM ft WHERE docid % 5 = 0")
          (s:execute db "UPDATE ft SET a = 'rewritten alpha beta' WHERE docid % 9 = 4")
          (s:execute db "INSERT INTO ft(ft) VALUES ('merge=5,4')")
          (s:execute db "INSERT INTO ft(ft) VALUES ('integrity-check')"))
        (check "SQLite's integrity-check of our changes" (sqlite path "insert into ft(ft) values('integrity-check')") "[]")
        (dolist (q *fts3-queries*)
          (check (format nil "both agree after our changes: ~a" q) (ours path (fts3-query-sql q)) (sqlite path (fts3-query-sql q))))
        ;; SQLite carries on (its merge picks up the hint we left)
        (py-run (format nil "import sqlite3
c=sqlite3.connect('~a', isolation_level=None)
for i in range(20): c.execute(\"insert into ft(a, b) values('late common', 'lisp')\")
c.execute(\"insert into ft(ft) values('merge=50,2')\")
c.execute(\"insert into ft(ft) values('optimize')\")
" path))
        (check "our integrity-check after SQLite's merges"
               (ours path "INSERT INTO ft(ft) VALUES ('integrity-check')") "[]")
        (dolist (q '("common" "late" "lisp NOT alpha"))
          (check (format nil "both agree at the end: ~a" q) (ours path (fts3-query-sql q)) (sqlite path (fts3-query-sql q)))))
      ;; 2. the same operations on each side give the same shadow tables
      (let ((pa (format nil "~a/b1.db" dir)) (pb (format nil "~a/b2.db" dir))
            (script (list "PRAGMA page_size=1024"
                          "CREATE VIRTUAL TABLE ft USING fts4(a, b, prefix='1,3')"
                          "INSERT INTO ft(ft) VALUES('automerge=2')")))
        (dolist (p (list pa pb)) (when (probe-file p) (delete-file p)))
        (loop for t0 below 40
              do (setf script
                       (append script
                               (list "BEGIN")
                               (loop for i below (+ 5 (mod (* t0 7) 23))
                                     collect (format nil "INSERT INTO ft(a, b) VALUES ('~{~a~^ ~}', 'common ~a')"
                                                     (loop repeat (1+ (mod (+ i t0) 9)) for k from i collect (nth (mod (* k 7) 24) *fts-words*))
                                                     (nth (mod (+ i (* t0 3)) 24) *fts-words*)))
                               (list "COMMIT")
                               (when (= (mod t0 6) 5) (list "DELETE FROM ft WHERE docid % 13 = 1"))
                               (when (= (mod t0 9) 4) (list "UPDATE ft SET b = b || ' more' WHERE docid % 7 = 3"))
                               (when (= t0 30) (list "INSERT INTO ft(ft) VALUES('merge=20,3')")))))
        (py-run (format nil "import sqlite3
c=sqlite3.connect('~a', isolation_level=None)
for s in ~a: c.execute(s)
" pb (format nil "[~{\"~a\"~^, ~}]" script)))
        (s:with-database (db pa) (dolist (st script) (s:execute db st)))
        (check "same shadow tables from the same statements (automerge, prefix, transactions)"
               (sqlite pa (fts3-shadow-dump-sql "ft")) (sqlite pb (fts3-shadow-dump-sql "ft")))
        (check "SQLite's integrity-check of ours" (sqlite pa "insert into ft(ft) values('integrity-check')") "[]")
        (dolist (q *fts3-queries*)
          (check (format nil "we read ours as SQLite reads it: ~a" q) (ours pa (fts3-query-sql q)) (sqlite pa (fts3-query-sql q)))))
      ;; 3. external content, language ids, order=desc, FTS3
      (let ((path (format nil "~a/c.db" dir)))
        (when (probe-file path) (delete-file path))
        (s:with-database (db path)
          (s:execute db "CREATE TABLE docs(id INTEGER PRIMARY KEY, title, body)")
          (s:execute db "CREATE VIRTUAL TABLE ext USING fts4(content=docs, title, body)")
          (s:execute db "CREATE VIRTUAL TABLE lang USING fts4(a, languageid=lid, order=desc)")
          (s:execute db "CREATE VIRTUAL TABLE old USING fts3(a, b, tokenize=porter)")
          (s:execute db "BEGIN")
          (loop for i from 1 to 400
                do (let ((ti (format nil "~a ~a" (nth (mod i 24) *fts-words*) (nth (mod (* i 5) 24) *fts-words*)))
                         (bo (format nil "~{~a~^ ~}" (loop repeat (1+ (mod i 13)) for k from i collect (nth (mod (* k 11) 24) *fts-words*)))))
                     (s:execute db "INSERT INTO docs VALUES (?, ?, ?)" i ti bo)
                     (s:execute db "INSERT INTO ext(docid, title, body) VALUES (?, ?, ?)" i ti bo)
                     (s:execute db "INSERT INTO lang(a, lid) VALUES (?, ?)" bo (mod i 3))
                     (s:execute db "INSERT INTO old(a, b) VALUES (?, ?)" ti bo)))
          (s:execute db "COMMIT")
          (s:execute db "DELETE FROM lang WHERE docid % 10 = 3")
          (s:execute db "DELETE FROM old WHERE docid % 10 = 3"))
        (dolist (tb '("ext" "lang" "old"))
          (check (format nil "SQLite's integrity-check of our ~a" tb)
                 (sqlite path (format nil "insert into ~a(~a) values('integrity-check')" tb tb)) "[]"))
        (dolist (q '("common" "alpha OR beta" "seg* NOT gamma" "\"alpha beta\""))
          (dolist (tb '("ext" "old"))
            (check (format nil "~a agrees: ~a" tb q) (ours path (fts3-query-sql q tb)) (sqlite path (fts3-query-sql q tb)))))
        (dolist (l '(0 1 2))
          (let ((sql (format nil "SELECT docid, offsets(lang) FROM lang WHERE lang MATCH 'common OR alpha' AND lid = ~d" l)))
            (check (format nil "lang ~d agrees" l) (ours path sql) (sqlite path sql))))
        (py-run (format nil "import sqlite3
c=sqlite3.connect('~a', isolation_level=None)
c.execute(\"insert into lang(a, lid) values('fresh common words', 1)\")
c.execute(\"delete from old where docid % 7 = 2\")
c.execute(\"insert into ext(ext) values('rebuild')\")
" path))
        (dolist (tb '("ext" "lang" "old"))
          (check (format nil "our integrity-check of SQLite's changes to ~a" tb)
                 (ours path (format nil "INSERT INTO ~a(~a) VALUES('integrity-check')" tb tb)) "[]")))
      ok)))
