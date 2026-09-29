;;;; cl-sqlite-compat.lisp — cl-sqlite's API exercised case by case, each
;;;; result printed.  test/run-cl-sqlite-compat.sh runs it once with the real
;;;; cl-sqlite (over libsqlite3) and once with sqlite-pure/cl-sqlite, and the
;;;; two transcripts must be identical.  Expects the SQLITE package loaded
;;;; and *DB-FILE* set.

(defpackage :cl-sqlite-compat (:use :cl :sqlite :iter))
(in-package :cl-sqlite-compat)

(defvar *db-file*)

(defun describe-error (c)
  (list :error (type-of c) (sqlite-error-code c) (sqlite-error-message c)
        (sqlite-error-sql c)
        (handler-case (princ-to-string c) (error () :unprintable))))

(defmacro check (name &body body)
  `(format t "~&~a: ~s~%" ',name
           (handler-case (multiple-value-list (progn ,@body))
             (sqlite-error (c) (describe-error c))
             (error (c) (list :lisp-error (type-of c))))))

(defmacro with-db ((db) &body body)
  ;; (disconnecting can fail in cl-sqlite, which leaks a statement's handle
  ;; on some of the errors below; that is not part of the comparison)
  `(let ((,db (connect ":memory:")))
     (unwind-protect (progn ,@body)
       (ignore-errors (disconnect ,db)))))

(defun run ()
  ;; values both ways
  (with-db (db)
    (execute-non-query db "create table v(x)")
    (dolist (v (list nil 0 -1 42 (1- (expt 2 63)) (- (expt 2 63)) 1.5d0 -0.25d0 1.5f0 1/4
                     "" "text" (format nil "~c~c" (code-char 233) (code-char 8364))
                     (coerce #(1 2 255) '(vector (unsigned-byte 8))) #(0 1 2)
                     (make-array 0 :element-type '(unsigned-byte 8))))
      (execute-non-query db "delete from v")
      (check bind-and-read
        (execute-non-query db "insert into v values (?)" v)
        (execute-one-row-m-v db "select x, typeof(x) from v")))
    (check bind-t (execute-single db "select ?" t))
    (check bind-keyword (execute-single db "select ?" :foo))
    (check bind-bignum (execute-single db "select ?" (expt 2 64)))
    (check bind-too-many (execute-single db "select ?" 1 2))
    (check bind-too-few (execute-single db "select ?, ?" 1))
    (check results
      (execute-to-list db "select 1, 2.5, 'a', x'00ff', null, -0.0, 9223372036854775807")))
  ;; statements, names, parameters
  (with-db (db)
    (execute-non-query db "create table t(id integer primary key, name text not null unique, age integer check (age >= 0))")
    (let ((s (prepare-statement db "select id, name as n, age + 1, count(*) over () from t where age > ?1 and name <> :nm and id <> @x and id <> $y and age <> ?")))
      (check column-names (statement-column-names s))
      (check parameter-names (statement-bind-parameter-names s))
      (finalize-statement s))
    (check names-insert (statement-column-names (prepare-statement db "insert into t(name, age) values (?, ?)")))
    (check names-pragma
      (let ((s (prepare-statement db "pragma table_info(t)")))
        (list (statement-column-names s) (step-statement s) (statement-column-names s))))
    (check names-star (statement-column-names (prepare-statement db "select * from t")))
    (check names-eqp (statement-column-names (prepare-statement db "explain query plan select * from t")))
    (check names-returning (statement-column-names (prepare-statement db "insert into t(name, age) values ('r', 1) returning id, name")))
    (dolist (row '(("joe" 18) ("dvk" 22) ("qwe" 30)))
      (apply #'execute-non-query db "insert into t(name, age) values (?, ?)" row))
    (check last-rowid (last-insert-rowid db))
    (check to-list (execute-to-list db "select * from t order by id"))
    (check to-list/named (execute-to-list/named db "select name from t where age > :a order by 1" ":a" 20))
    (check single (execute-single db "select name from t where id = ?" 2))
    (check single/named (execute-single/named db "select name from t where id = :id" ":id" 2))
    (check single-none (execute-single db "select name from t where id = ?" 99))
    (check m-v (execute-one-row-m-v db "select id, name, age from t where id = ?" 1))
    (check m-v-none (execute-one-row-m-v db "select id, name, age from t where id = ?" 99))
    (check m-v/named (execute-one-row-m-v/named db "select id, name from t where name = :n" ":n" "qwe"))
    (check non-query-select (execute-non-query db "select * from t"))
    (check non-query/named (execute-non-query/named db "update t set age = :a where id = :id" ":a" 23 ":id" 2))
    ;; stepping by hand
    (let ((s (prepare-statement db "select name from t where age < ? order by id")))
      (bind-parameter s 1 25)
      (check step-1 (step-statement s) (statement-column-value s 0))
      (check step-2 (step-statement s) (statement-column-value s 0))
      (check step-end (step-statement s))
      (check step-again (step-statement s) (statement-column-value s 0))
      (reset-statement s)
      (check after-reset (step-statement s) (statement-column-value s 0))
      (reset-statement s)
      (clear-statement-bindings s)
      (check after-clear (step-statement s))
      ;; binding needs a statement that has been reset (or never stepped)
      (check bind-while-done (bind-parameter s 1 100))
      (check bind-bad-index-while-done (bind-parameter s 5 1))
      (reset-statement s)
      (check rebind
        (bind-parameter s 1 100)
        (loop while (step-statement s) collect (statement-column-value s 0)))
      (reset-statement s)
      (check bind-while-running (step-statement s) (bind-parameter s 1 100))
      (reset-statement s)
      (check clear-while-running (step-statement s) (clear-statement-bindings s)
             (loop while (step-statement s) collect (statement-column-value s 0)))
      (reset-statement s)
      (check bind-bad-index (bind-parameter s 5 1))
      (check bind-zero (bind-parameter s 0 1))
      (check bind-bad-name (bind-parameter s ":nope" 1))
      (check value-before-step (statement-column-value s 0))
      (check value-past-end (step-statement s) (statement-column-value s 3))
      (finalize-statement s)
      (check cached (eq s (prepare-statement db "select name from t where age < ? order by id"))))
    ;; errors
    (check syntax-error (prepare-statement db "selec 1"))
    (check syntax-error-2 (prepare-statement db "select * from t where"))
    (check no-such-table (prepare-statement db "select * from nope"))
    (check no-such-column (prepare-statement db "select nope from t"))
    ;; (cl-sqlite leaks the first statement's handle here, and its connection
    ;; then cannot close: a connection of its own)
    (let ((db2 (connect ":memory:")))
      (check two-statements (prepare-statement db2 "select 1; select 2"))
      (ignore-errors (disconnect db2)))
    (check trailing-semicolon (execute-single db "select 7;"))
    (check not-null (execute-non-query db "insert into t(name, age) values (null, 1)"))
    (check unique (execute-non-query db "insert into t(name, age) values ('joe', 1)"))
    (check check-constraint (execute-non-query db "insert into t(name, age) values ('neg', -1)"))
    (check pk (execute-non-query db "insert into t(id, name) values (1, 'dup')"))
    (check manual-step-error
      (let ((s (prepare-statement db "insert into t(name, age) values ('joe', 1)")))
        (list (handler-case (step-statement s) (sqlite-error (c) (describe-error c)))
              (handler-case (reset-statement s) (sqlite-error (c) (describe-error c)))
              (handler-case (reset-statement s) (sqlite-error (c) (describe-error c))))))
    (check prepare-insert-missing (prepare-statement db "insert into nope values (1)"))
    (check prepare-insert-bad-column (prepare-statement db "insert into t(nope) values (1)"))
    (check prepare-update-missing (prepare-statement db "update nope set x = 1"))
    (check prepare-update-bad-column (prepare-statement db "update t set nope = 1"))
    (check prepare-delete-missing (prepare-statement db "delete from nope"))
    (check prepare-where-bad-column (prepare-statement db "delete from t where nope = 1"))
    (check prepare-create-exists (prepare-statement db "create table t(x)"))
    (check prepare-drop-missing (prepare-statement db "drop table nope"))
    (check constraint-class
      (handler-case (execute-non-query db "insert into t(name) values ('joe')")
        (sqlite-constraint-error () :constraint-error)))
    (check runtime-error (execute-single db "select abs(-9223372036854775808)"))
    (check misuse-agg (execute-single db "select count(*) from t group by sum(id)"))
    ;; transactions
    (check txn-commit
      (with-transaction db (execute-non-query db "insert into t(name, age) values ('tx', 5)"))
      (execute-single db "select count(*) from t where name = 'tx'"))
    (check txn-rollback
      (ignore-errors
        (with-transaction db
          (execute-non-query db "insert into t(name, age) values ('tx2', 5)")
          (error "abort")))
      (execute-single db "select count(*) from t where name = 'tx2'"))
    (check txn-value (with-transaction db (values 1 2 3)))
    (check nested-txn (with-transaction db (with-transaction db 1)))
    ;; iterate
    (check iter-query
      (iter (for (id name) in-sqlite-query "select id, name from t where age < ? order by id"
                 on-database db with-parameters (25))
            (collect (list id name))))
    (check iter-query-1
      (iter (for name in-sqlite-query "select name from t order by name" on-database db)
            (collect name)))
    (check iter-query/named
      (iter (for (id) in-sqlite-query/named "select id from t where age > :a order by id"
                 on-database db with-parameters (":a" 20))
            (collect id)))
    (check iter-statement
      (let ((s (prepare-statement db "select id from t order by id desc")))
        (prog1 (iter (for (id) on-sqlite-statement s) (collect id))
          (finalize-statement s))))
    (check iter-generate
      (iter (generate name in-sqlite-query "select name from t order by id" on-database db)
            (repeat 2)
            (collect (next name)))))
  ;; files, disconnecting, busy
  (when (probe-file *db-file*) (delete-file *db-file*))
  (check file-db
    (with-open-database (db *db-file*)
      (execute-non-query db "create table f(x)")
      (execute-non-query db "insert into f values (1)"))
    (with-open-database (db (pathname *db-file*))
      (execute-to-list db "select * from f")))
  (check busy
    (with-open-database (a *db-file*)
      (with-open-database (b *db-file* :busy-timeout 50)
        (execute-non-query a "begin immediate")
        (execute-non-query a "insert into f values (2)")
        (prog1 (handler-case (execute-non-query b "insert into f values (3)")
                 (sqlite-error (c) (list (sqlite-error-code c) (sqlite-error-message c))))
          (execute-non-query a "commit")))))
  (check busy-read
    (with-open-database (db *db-file*) (execute-to-list db "select * from f order by x")))
  (check disconnect-with-statement
    (let ((db (connect *db-file*)))
      (prepare-statement db "select * from f")
      (disconnect db)
      :ok))
  (check cannot-open (connect "/nonexistent-dir/x.db"))
  (when (probe-file *db-file*) (delete-file *db-file*)))
