;;;; api.lisp — the public entry points, statement dispatch, transactions
;;;; and PRAGMAs.

(in-package #:sqlite-pure)

(defmacro with-sql-floats (&body body)
  "Run BODY with IEEE semantics (overflow -> infinity) instead of traps."
  #+sbcl `(sb-int:with-float-traps-masked (:overflow :invalid :divide-by-zero :inexact :underflow)
            ,@body)
  #-sbcl `(progn ,@body))

(defun write-statement-p (st)
  (case (car st)
    ((:insert :update :delete :create-table :create-index :create-view
      :create-trigger :create-virtual :drop :alter :reindex)
     t)
    (:pragma (and (getf (cdr st) :value)
                  (member (getf (cdr st) :name)
                          '("user_version" "application_id" "schema_version")
                          :test #'name=)))
    (t nil)))

(defun statement-write-dbs (db st)
  "The databases the writing statement ST writes (its OP_Transaction): an
INSERT, UPDATE, DELETE, ALTER or DROP TABLE its table's; a CREATE the one
it names (main by default, temp for TEMP); anything unresolved, every
database.  Every database in WAL mode besides, as before."
  (let* ((all (conn-dbs db))
         (args (cdr st))
         (schema (getf args :schema))
         (target
           (let ((*db* db))
             (ignore-errors
              (case (car st)
                ((:insert :update :delete :alter)
                 (table-owner (lookup-table db (getf args :table) nil schema)))
                (:drop
                 (if (member (getf args :kind) '(:table :view))
                     (let ((tb (lookup-table db (getf args :name) nil schema)))
                       (if tb (table-owner tb) (and schema (schema-db db schema nil))))
                     (object-db (getf args :kind) (getf args :name) schema)))
                ((:create-table :create-view :create-trigger :create-index :create-virtual)
                 (cond ((getf args :temp) (temp-db db t))
                       (schema (schema-db db schema nil))
                       ((eq (car st) :create-index)
                        (table-owner (lookup-table db (getf args :table) nil nil)))
                       ((eq (car st) :create-trigger)
                        (table-owner (lookup-table db (getf args :table) nil nil)))
                       (t (conn db)))))))))
    (if target
        (remove-duplicates (cons target (remove-if-not #'db-wal all)))
        all)))

(defun commit-all (db) (dolist (d (conn-dbs db)) (commit-write d)))
(defun rollback-all (db)
  (setf (db-fk-deferred (conn db)) nil)
  (dolist (d (conn-dbs db)) (rollback-write d)))

(defun run-in-write-txn (db thunk)
  "Run THUNK as one atomic statement (across every attached database)."
  ;; The flags live in a cons rather than in variables assigned inside
  ;; HANDLER-BIND: some compilers (modus, as of 2026-09) mis-scope such
  ;; assignments.
  (let ((state (list nil nil)))          ; (ok keep)
    (progn
      (cond
        ((db-explicit db)
         (let ((started (conn-dbs db)))
           (dolist (d started) (statement-begin d))
           (unwind-protect
                (handler-bind ((sqlite-conflict
                                 (lambda (c)
                                   (case (conflict-action c)
                                     (:rollback (rollback-all db) (fts3-end-transaction db nil)
                                      (setf (db-explicit db) nil (first state) t))
                                     (:fail (setf (first state) t))))))
                  (multiple-value-prog1 (funcall thunk) (setf (first state) t)))
             (dolist (d (conn-dbs db))
               (if (and (not (first state)) (member d started)) (statement-rollback d) (statement-end d))))))
        (t
         (unwind-protect
              (handler-bind ((sqlite-conflict
                               (lambda (c) (when (eq (conflict-action c) :fail) (setf (second state) t)))))
                (multiple-value-prog1 (funcall thunk) (setf (first state) t)))
           (if (or (first state) (second state))
               (handler-bind ((error (lambda (c) (declare (ignore c)) (rollback-all db))))
                 (fk-check-deferred db)
                 (commit-all db))
               (progn (rollback-all db) (fts3-end-transaction db nil)))))))))

(defun exec-ast (db st text)
  "Execute one parsed statement.  Return (values rows column-names)."
  (let ((*db* db) (*encoding* (db-encoding db)))
    (case (car st)
      (:select
       (multiple-value-bind (fn cols) (compile-select (second st) (make-scope))
         (values (funcall fn nil) (mapcar #'first cols))))
      (:begin
       (when (db-explicit db) (sql-error "cannot start a transaction within a transaction"))
       ;; IMMEDIATE and EXCLUSIVE lock every database now
       (let ((kind (second st)))
         (unless (eq kind :deferred)
           (handler-bind ((error (lambda (c) (declare (ignore c))
                                   (dolist (d (conn-dbs db))
                                     (unless (db-txn d) (unlock-to d :none))))))
             (dolist (d (conn-dbs db))
               (write-lock d)
               (when (and (eq kind :exclusive) (not (db-wal d)) (not (db-readonly d)))
                 (lock-exclusive d))))))
       (setf (db-explicit db) t)
       (values nil nil))
      (:commit
       (unless (db-explicit db) (sql-error "cannot commit - no transaction is active"))
       (fts3-end-transaction db t)
       (fk-check-deferred db)
       (commit-all db)
       (setf (db-explicit db) nil (db-savepoint-txn db) nil)
       (values nil nil))
      (:rollback
       (unless (db-explicit db) (sql-error "cannot rollback - no transaction is active"))
       (rollback-all db)
       (fts3-end-transaction db nil)
       (setf (db-explicit db) nil)
       (values nil nil))
      (:savepoint
       (fts3-sync-all db)
       (unless (db-explicit db) (setf (db-explicit db) t (db-savepoint-txn db) t))
       (dolist (d (conn-dbs db)) (savepoint-push d (second st)))
       (values nil nil))
      (:release
       (let ((outermost (savepoint-outermost-p db (second st))))
         (dolist (d (conn-dbs db)) (savepoint-pop d (second st)))
         (when (and outermost (db-savepoint-txn db))
           (fts3-end-transaction db t)
           (commit-all db)
           (setf (db-explicit db) nil (db-savepoint-txn db) nil)))
       (values nil nil))
      (:rollback-to
       (savepoint-outermost-p db (second st))   ; signals if unknown
       (dolist (d (conn-dbs db)) (savepoint-restore d (second st)))
       (fts3-rollback-to db)
       (values nil nil))
      (:attach (exec-attach db (second st) (third st)) (values nil nil))
      (:detach (exec-detach db (second st)) (values nil nil))
      (:noop (values nil nil))
      (:vacuum
       (destructuring-bind (schema into) (cdr st)
         (let ((target (if schema (schema-db db schema) db)))
           (if into
               (vacuum-into target (value-to-text (funcall (compile-expr into (make-scope)) nil)))
               (vacuum-in-place target))))
       (values nil nil))
      (:pragma (exec-pragma db st))
      (:explain-qp (explain-query-plan db (second st) text))
      (t
       (unless (write-statement-p st) (sql-error "unsupported statement"))
       (let ((journal (and (db-explicit (conn db)) (fts3-statement-journal-p st))))
       (run-in-write-txn
        db
        (lambda ()
          (when journal (fts3-sync-all db))
          (let ((*index-expr-cache* nil) (*fts5-touched* '()) (flushed nil))
           (unwind-protect
                (multiple-value-prog1
            (ecase (car st)
              (:insert (exec-insert st))
              (:update (exec-update st))
              (:delete (exec-delete st))
              (:create-table (exec-create-table st text))
              (:create-index (exec-create-index st text))
              (:create-view (exec-create-view st text))
              (:create-trigger (exec-create-trigger st text))
              (:create-virtual (exec-create-virtual st))
              (:drop (exec-drop st))
              (:alter (exec-alter st))
              (:reindex (exec-reindex st))
              (:pragma (exec-pragma db st)))
                  ;; FTS5 writes are buffered per statement; FTS3 per transaction
                  (fts5-flush-touched)
                  (unless (db-explicit (conn db)) (fts3-end-transaction db t))
                  (setf flushed t))
             (unless flushed
               (fts5-discard-touched)
               (fts3-statement-end db nil journal)))))))))))

(defun bind-params (params nparam)
  (declare (ignore nparam))
  (map 'simple-vector #'lisp-to-sql params))

(defun parse-sql-cached (db sql)
  "PARSE-SQL, memoised per connection (ASTs are never mutated)."
  (let ((cache (db-stmt-cache db)))
    (let ((hit (gethash sql cache)))
      (if hit
          (values-list hit)
          (let ((r (multiple-value-list (parse-sql sql))))
            (when (> (hash-table-count cache) 500) (clrhash cache))
            (setf (gethash sql cache) r)
            (values-list r))))))

(defun check-open (db)
  (when (db-closed db) (sql-error "database is closed")))

(defun run-sql (db sql params)
  "Run every statement in SQL; return the rows and column names of the last."
  (check-open db)
  (multiple-value-bind (stmts nparam names) (parse-sql-cached db sql)
    (run-parsed db sql stmts (bind-params params nparam) names)))

(defun run-parsed (db sql stmts params names)
  "Run the parsed STMTS of SQL with PARAMS (a vector of SQL values) and
named parameters NAMES; return the rows and column names of the last."
  (with-connection-mutex (db) (%run-parsed db sql stmts params names)))

(defun %run-parsed (db sql stmts params names)
  (check-open db)
  (with-sql-floats
    (progn
      (let ((*params* params)
            (*param-names* names)
            (*executing-sql* sql)
            (*busy-timeout* (or (db-busy-timeout (conn db)) *busy-timeout*))
            (rows nil) (cols nil))
        (dolist (s stmts)
          (let ((*json-values* (make-hash-table :test #'eq))
                (*fts5-cursors* (make-hash-table))
                (*read-before-statement*
                  (and (db-explicit db) (remove-if-not #'read-transaction-p (conn-dbs db)))))
            (unwind-protect
                 (progn
                   ;; (BEGIN, SAVEPOINT and the rest take no read lock)
                   (unless (member (car (car s)) '(:begin :commit :rollback :savepoint
                                                  :release :rollback-to))
                     (dolist (d (conn-dbs db)) (lock-shared d)))
                   ;; a writing statement takes the write lock before it
                   ;; reads (OP_Transaction), so what it reads cannot go
                   ;; stale underneath it
                   (when (write-statement-p (car s))
                     (dolist (d (statement-write-dbs db (car s)))
                       (write-lock d)))
                   (multiple-value-setq (rows cols) (exec-ast db (car s) (cdr s))))
              ;; outside a transaction every statement is its own read transaction
              (unless (db-explicit db)
                (dolist (d (conn-dbs db))
                  (unless (db-txn d) (unlock-to d :none)))))))
        (values rows cols)))))

;; generated from SQLite 3.40.1 src/pragma.h: name, NoColumns flags, result column names
(defparameter +pragma-columns+
  '(("activate_extensions" () ("activate_extensions"))
    ("analysis_limit" () ("analysis_limit"))
    ("application_id" (:nocolumns1) ("application_id"))
    ("auto_vacuum" (:nocolumns1) ("auto_vacuum"))
    ("automatic_index" (:nocolumns1) ("automatic_index"))
    ("busy_timeout" () ("timeout"))
    ("cache_size" (:nocolumns1) ("cache_size"))
    ("cache_spill" (:nocolumns1) ("cache_spill"))
    ("case_sensitive_like" (:nocolumns) ("case_sensitive_like"))
    ("cell_size_check" (:nocolumns1) ("cell_size_check"))
    ("checkpoint_fullfsync" (:nocolumns1) ("checkpoint_fullfsync"))
    ("collation_list" () ("seq" "name"))
    ("compile_options" () ("compile_options"))
    ("count_changes" (:nocolumns1) ("count_changes"))
    ("data_store_directory" (:nocolumns1) ("data_store_directory"))
    ("data_version" () ("data_version"))
    ("database_list" () ("seq" "name" "file"))
    ("default_cache_size" (:nocolumns1) ("cache_size"))
    ("defer_foreign_keys" (:nocolumns1) ("defer_foreign_keys"))
    ("empty_result_callbacks" (:nocolumns1) ("empty_result_callbacks"))
    ("encoding" (:nocolumns1) ("encoding"))
    ("foreign_key_check" () ("table" "rowid" "parent" "fkid"))
    ("foreign_key_list" () ("id" "seq" "table" "from" "to" "on_update" "on_delete" "match"))
    ("foreign_keys" (:nocolumns1) ("foreign_keys"))
    ("freelist_count" () ("freelist_count"))
    ("full_column_names" (:nocolumns1) ("full_column_names"))
    ("fullfsync" (:nocolumns1) ("fullfsync"))
    ("function_list" () ("name" "builtin" "type" "enc" "narg" "flags"))
    ("hard_heap_limit" () ("hard_heap_limit"))
    ("ignore_check_constraints" (:nocolumns1) ("ignore_check_constraints"))
    ("incremental_vacuum" (:nocolumns) ("incremental_vacuum"))
    ("index_info" () ("seqno" "cid" "name"))
    ("index_list" () ("seq" "name" "unique" "origin" "partial"))
    ("index_xinfo" () ("seqno" "cid" "name" "desc" "coll" "key"))
    ("integrity_check" () ("integrity_check"))
    ("journal_mode" () ("journal_mode"))
    ("journal_size_limit" () ("journal_size_limit"))
    ("legacy_alter_table" (:nocolumns1) ("legacy_alter_table"))
    ("lock_proxy_file" (:nocolumns1) ("lock_proxy_file"))
    ("lock_status" () ("database" "status"))
    ("locking_mode" () ("locking_mode"))
    ("max_page_count" () ("max_page_count"))
    ("mmap_size" () ("mmap_size"))
    ("module_list" () ("name"))
    ("optimize" () ("optimize"))
    ("page_count" () ("page_count"))
    ("page_size" (:nocolumns1) ("page_size"))
    ("parser_trace" (:nocolumns1) ("parser_trace"))
    ("pragma_list" () ("name"))
    ("query_only" (:nocolumns1) ("query_only"))
    ("quick_check" () ("quick_check"))
    ("read_uncommitted" (:nocolumns1) ("read_uncommitted"))
    ("recursive_triggers" (:nocolumns1) ("recursive_triggers"))
    ("reverse_unordered_selects" (:nocolumns1) ("reverse_unordered_selects"))
    ("schema_version" (:nocolumns1) ("schema_version"))
    ("secure_delete" () ("secure_delete"))
    ("short_column_names" (:nocolumns1) ("short_column_names"))
    ("shrink_memory" (:nocolumns) ("shrink_memory"))
    ("soft_heap_limit" () ("soft_heap_limit"))
    ("sql_trace" (:nocolumns1) ("sql_trace"))
    ("stats" () ("tbl" "idx" "wdth" "hght" "flgs"))
    ("synchronous" (:nocolumns1) ("synchronous"))
    ("table_info" () ("cid" "name" "type" "notnull" "dflt_value" "pk"))
    ("table_list" () ("schema" "name" "type" "ncol" "wr" "strict"))
    ("table_xinfo" () ("cid" "name" "type" "notnull" "dflt_value" "pk" "hidden"))
    ("temp_store" (:nocolumns1) ("temp_store"))
    ("temp_store_directory" (:nocolumns1) ("temp_store_directory"))
    ("threads" () ("threads"))
    ("trusted_schema" (:nocolumns1) ("trusted_schema"))
    ("user_version" (:nocolumns1) ("user_version"))
    ("vdbe_addoptrace" (:nocolumns1) ("vdbe_addoptrace"))
    ("vdbe_debug" (:nocolumns1) ("vdbe_debug"))
    ("vdbe_eqp" (:nocolumns1) ("vdbe_eqp"))
    ("vdbe_listing" (:nocolumns1) ("vdbe_listing"))
    ("vdbe_trace" (:nocolumns1) ("vdbe_trace"))
    ("wal_autocheckpoint" () ("wal_autocheckpoint"))
    ("wal_checkpoint" () ("busy" "log" "checkpointed"))
    ("writable_schema" (:nocolumns1) ("writable_schema"))))

(defun pragma-result-columns (name value)
  "The columns sqlite3Pragma names when it prepares PRAGMA NAME (with VALUE,
or none): none for a pragma that returns nothing, or that returns nothing
when given a value; else its result columns (or its own name)."
  (let ((e (assoc (string-downcase-ascii name) +pragma-columns+ :test #'string=)))
    (when (and e
               (not (member :nocolumns (second e)))
               (not (and value (member :nocolumns1 (second e)))))
      (third e))))

(defun statement-columns (db st text)
  "Prepare the parsed statement ST (of TEXT) as sqlite3_prepare would,
without running it: a query is compiled and a writing statement makes its
checks (a missing table or column, a name already taken ... is reported
now), and the result column names are returned -- a query's, a RETURNING
list's, EXPLAIN QUERY PLAN's four; NIL for other statements."
  (with-connection-mutex (db) (%statement-columns db st text)))

(defun %statement-columns (db st text)
  (check-open db)
  (let ((exec (case (car st)
                (:insert #'exec-insert) (:update #'exec-update) (:delete #'exec-delete)
                (:create-table (lambda (st) (exec-create-table st text)))
                (:create-index (lambda (st) (exec-create-index st text)))
                (:create-view (lambda (st) (exec-create-view st text)))
                (:create-trigger (lambda (st) (exec-create-trigger st text)))
                (:drop #'exec-drop))))
    (case (car st)
      (:explain-qp (list "id" "parent" "notused" "detail"))
      (:pragma (destructuring-bind (&key name value &allow-other-keys) (cdr st)
                 (pragma-result-columns name value)))
      ((:select :insert :update :delete :create-table :create-index :create-view
        :create-trigger :drop)
       (with-sql-floats
         (let ((*db* db) (*encoding* (db-encoding db)) (*params* #()) (*param-names* nil)
               (*executing-sql* text)
               (*busy-timeout* (or (db-busy-timeout (conn db)) *busy-timeout*))
               (*prepare-only* t) (*index-expr-cache* nil) (*fts5-touched* '()))
           (unwind-protect
                (progn
                  (dolist (d (conn-dbs db)) (lock-shared d))
                  (if (eq (car st) :select)
                      (multiple-value-bind (fn cols) (compile-select (second st) (make-scope))
                        (declare (ignore fn))
                        (mapcar #'first cols))
                      ;; each stops at PREPARED-HERE, before it writes; one
                      ;; that returns first had nothing to do (IF [NOT] EXISTS)
                      (let ((r (catch :prepared (funcall exec st) :ran)))
                        (if (eq r :ran) nil r))))
             (unless (db-explicit db)
               (dolist (d (conn-dbs db))
                 (unless (db-txn d) (unlock-to d :none)))))))))))

(defun execute (db sql &rest params)
  "Execute SQL (one or more statements) with positional PARAMS.  Returns
the rows of the last statement if it produced any, else its change count."
  (multiple-value-bind (rows cols) (run-sql db sql params)
    (if cols rows (db-changes db))))

(defun execute-script (db sql)
  (run-sql db sql '())
  nil)

(defun query (db sql &rest params)
  "Return (values rows column-names); each row is a list of values."
  (run-sql db sql params))

(defun query-row (db sql &rest params)
  (first (run-sql db sql params)))

(defun query-value (db sql &rest params)
  (first (first (run-sql db sql params))))

(defmacro do-query ((vars db sql &rest params) &body body)
  "Evaluate BODY with VARS bound to the columns of each result row."
  (let ((row (gensym "ROW")))
    `(dolist (,row (query ,db ,sql ,@params))
       (destructuring-bind (&optional ,@vars &rest ignore) ,row
         (declare (ignore ignore))
         ,@body))))

(defun last-insert-rowid (db) (db-last-insert-rowid db))

;;; ------------------------------------------------------------------
;;; User-defined functions, aggregates and collations

(defun arity-range (arity)
  (if (or (null arity) (minusp arity)) (values 0 nil) (values arity arity)))

(defun define-function (db name function &key (arity -1))
  "Make FUNCTION callable from SQL as NAME on DB's connection.  It receives
the arguments as Lisp values (:null, integer, double-float, string or octet
vector) and returns one; NIL returns NULL, T returns 1.  ARITY -1 accepts
any number of arguments.  A user function shadows a built-in of that name."
  (multiple-value-bind (min max) (arity-range arity)
    (let ((c (conn db)) (n (string-downcase-ascii name)))
      (remhash n (db-user-aggregates c))
      (setf (gethash n (db-user-functions c))
            (list min max (lambda (args) (lisp-to-sql (apply function args)))))
      (clrhash (db-stmt-cache c))
      name)))

(defun define-aggregate (db name step &key (initial nil) (final #'identity) (arity -1))
  "Define an aggregate NAME: the state starts as INITIAL, each row sets it
to (STEP state arg...), and the result is (FINAL state).  Rows where STEP's
arguments are all passed as SQL values (NULLs included)."
  (multiple-value-bind (min max) (arity-range arity)
    (let ((c (conn db)) (n (string-downcase-ascii name)))
      (remhash n (db-user-functions c))
      (setf (gethash n (db-user-aggregates c))
            (list min max
                  (lambda ()
                    (let ((state (if (functionp initial) (funcall initial) initial)))
                      (values (lambda (args) (setf state (apply step state args)) nil)
                              (lambda () (lisp-to-sql (funcall final state))))))))
      (clrhash (db-stmt-cache c))
      name)))

(defun define-collation (db name compare &key key)
  "Define collation NAME.  (COMPARE a b) orders two strings: a negative
number, zero or a positive number (or a generalized boolean meaning
\"a is less than b\").  KEY, if given, maps a string to a canonical form
such that strings equal under COMPARE have EQUAL keys; GROUP BY, DISTINCT
and UNION use it (without it, grouping falls back to exact text)."
  (setf (gethash (string-upcase-ascii name) (db-user-collations (conn db)))
        (cons compare key))
  name)

(defun undefine-function (db name)
  (let ((c (conn db)) (n (string-downcase-ascii name)))
    (remhash n (db-user-functions c))
    (remhash n (db-user-aggregates c))
    (clrhash (db-stmt-cache c))
    nil))
(defun changes (db) (db-changes db))
(defun in-transaction-p (db) (db-explicit db))

(defun begin-transaction (db) (execute db "BEGIN"))
(defun commit (db) (execute db "COMMIT"))
(defun rollback (db) (execute db "ROLLBACK"))

(defvar *savepoint-counter* 0)

(defun call-with-transaction (db thunk)
  (if (in-transaction-p db)
      ;; nested: a savepoint, so an inner failure undoes only the inner work
      (let ((name (format nil "sqlp_sp_~d" (incf *savepoint-counter*)))
            (ok nil))
        (execute db (format nil "SAVEPOINT ~a" name))
        (unwind-protect (multiple-value-prog1 (funcall thunk) (setf ok t))
          (when (in-transaction-p db)
            (unless ok (execute db (format nil "ROLLBACK TO ~a" name)))
            (execute db (format nil "RELEASE ~a" name)))))
      (let ((ok nil))
        (begin-transaction db)
        (unwind-protect (multiple-value-prog1 (funcall thunk) (setf ok t))
          (when (in-transaction-p db)
            (if ok (commit db) (rollback db)))))))

(defmacro with-transaction ((db) &body body)
  "Run BODY in a transaction: committed on normal exit, rolled back on a
non-local exit.  Nested uses become savepoints."
  `(call-with-transaction ,db (lambda () ,@body)))

;;; ------------------------------------------------------------------
;;; PRAGMA

;;; pragma_NAME(arg, schema): the eponymous table-valued functions over the
;;; pragmas that return rows.  (name columns hidden-columns), as in 3.40.
(defparameter +pragma-vtabs+
  (let ((as '("arg" "schema")) (s '("schema")))
    `(("table_info" ("cid" "name" "type" "notnull" "dflt_value" "pk") ,as)
      ("table_xinfo" ("cid" "name" "type" "notnull" "dflt_value" "pk" "hidden") ,as)
      ("index_list" ("seq" "name" "unique" "origin" "partial") ,as)
      ("index_info" ("seqno" "cid" "name") ,as)
      ("index_xinfo" ("seqno" "cid" "name" "desc" "coll" "key") ,as)
      ("foreign_key_list" ("id" "seq" "table" "from" "to" "on_update" "on_delete" "match") ,as)
      ("table_list" ("schema" "name" "type" "ncol" "wr" "strict") ,as)
      ("integrity_check" ("integrity_check") ,as)
      ("quick_check" ("quick_check") ,as)
      ("database_list" ("seq" "name" "file") ())
      ("collation_list" ("seq" "name") ())
      ("user_version" ("user_version") ())
      ("application_id" ("application_id") ())
      ("schema_version" ("schema_version") ())
      ("freelist_count" ("freelist_count") ())
      ("encoding" ("encoding") ())
      ("foreign_keys" ("foreign_keys") ())
      ("page_size" ("page_size") ,s)
      ("page_count" ("page_count") ,s)
      ("journal_mode" ("journal_mode") ,s)
      ("auto_vacuum" ("auto_vacuum") ,s))))

(defun pragma-vtab-spec (name)
  (and (> (length name) 7) (name= (subseq name 0 7) "pragma_")
       (assoc (subseq name 7) +pragma-vtabs+ :test #'name=)))

(defun pragma-table-source (name arg-fns alias)
  "An FSRC for pragma_NAME with argument closures ARG-FNS (arg, then schema)."
  (destructuring-bind (pname cols hidden) (pragma-vtab-spec name)
    (let* ((all (append cols hidden))
           (src (derived-src (or alias (string-downcase-ascii name)) all
                             (make-list (length all) :initial-element nil)
                             (make-list (length all) :initial-element :binary))))
      (setf (src-star-hidden src) (loop for i from (length cols) below (length all) collect i))
      (make-fsrc
       :src src
       :rows-fn (lambda (env)
                  (let* ((vals (mapcar (lambda (f) (funcall f env)) arg-fns))
                         (arg (if (member "arg" hidden :test #'string=) (pop vals) nil))
                         (schema (pop vals))
                         (db (if (and schema (not (eq schema :null)))
                                 (schema-db *db* (value-to-text schema) nil)
                                 *db*)))
                    (if (or (null db) (eq arg :null))
                        '()
                        (let ((rows (exec-pragma db (list :pragma :name pname :value arg))))
                          (rows-to-vectors
                           (mapcar (lambda (r)
                                     (append (subseq (append r (make-list (length cols) :initial-element :null))
                                                     0 (length cols))
                                             (if (member "arg" hidden :test #'string=)
                                                 (list (if arg arg :null) (or schema :null))
                                                 (and hidden (list (or schema :null))))))
                                   rows))))))))))

(defun pragma-rows (names rows) (values rows names))

(defun safety-level-of (value)
  "getSafetyLevel(value, 0, 1): a number, or on/off/no/yes/true/false/extra/full."
  (let ((z (if (stringp value) value (value-to-text value))))
    (if (and (plusp (length z)) (digit-char-p (char z 0)))
        (ldb (byte 8 0) (parse-integer z :junk-allowed t))
        (let ((hit (assoc z '(("on" . 1) ("no" . 0) ("off" . 0) ("false" . 0) ("yes" . 1)
                              ("true" . 1) ("extra" . 3) ("full" . 2))
                          :test #'string-equal)))
          (if hit (cdr hit) 1)))))

(defun pragma-boolean (value)
  (let ((v (if (stringp value) (string-downcase-ascii value) value)))
    (not (member v '(0 "0" "off" "false" "no") :test #'equal))))

(defun exec-pragma (db st)
  (destructuring-bind (&key name value schema) (cdr st)
    ;; PRAGMA schema.name: the named database, which must exist
    (when schema
      (setf db (schema-db db schema nil))
      (unless db (sql-error "unknown database ~a" schema)))
    (let ((n (string-downcase-ascii name)))
      (flet ((header-int (off) (header-u32 db off))
             (int-value () (value-to-integer (if (stringp value) (or (text-numeric-value value) 0) value))))
        (cond
          ((string= n "user_version")
           (if value
               (progn (set-header-u32 db +hdr-user-version+ (ldb (byte 32 0) (int-value)))
                      (values nil nil))
               (pragma-rows '("user_version") (list (list (to-signed32 (header-int +hdr-user-version+)))))))
          ((string= n "application_id")
           (if value
               (progn (set-header-u32 db +hdr-application-id+ (ldb (byte 32 0) (int-value)))
                      (values nil nil))
               (pragma-rows '("application_id") (list (list (to-signed32 (header-int +hdr-application-id+)))))))
          ((string= n "schema_version")
           (if value
               (progn (set-header-u32 db +hdr-schema-cookie+ (int-value)) (values nil nil))
               (pragma-rows '("schema_version") (list (list (header-int +hdr-schema-cookie+))))))
          ((string= n "page_size")
           (when value
             (let ((ps (int-value)))
               (when (and (zerop (db-page-count db)) (>= ps 512) (<= ps 65536) (= (logcount ps) 1))
                 (setf (db-pending-page-size db) ps (db-page-size db) ps (db-usable-size db) ps))))
           (if value (values nil nil) (pragma-rows '("page_size") (list (list (db-page-size db))))))
          ((string= n "page_count") (pragma-rows '("page_count") (list (list (db-page-count db)))))
          ((string= n "freelist_count")
           (pragma-rows '("freelist_count") (list (list (header-int +hdr-freelist-count+)))))
          ((string= n "encoding")
           (pragma-rows '("encoding") (list (list (ecase (db-encoding db)
                                                     (:utf-8 "UTF-8") (:utf-16le "UTF-16le")
                                                     (:utf-16be "UTF-16be"))))))
          ((string= n "journal_mode")
           (pragma-rows '("journal_mode")
                        (list (list (cond (value (set-journal-mode db (string-downcase-ascii (value-to-text value))))
                                          ((memory-db-p db) "memory")
                                          ((db-wal db) "wal")
                                          (t "delete"))))))
          ((string= n "auto_vacuum")
           (if value
               (let* ((v (string-downcase-ascii (value-to-text value)))
                      (created nil)
                      (mode (cond ((member v '("1" "full") :test #'string=) :full)
                                  ((member v '("2" "incremental") :test #'string=) :incremental)
                                  (t nil))))
                 ;; takes effect now on a database without tables, else at VACUUM
                 (setf (db-pending-autovacuum db) (or mode :none))
                 ;; on a new database SQLite writes page 1 now (its setMeta6
                 ;; program), before the file format or encoding is set
                 (when (and mode (zerop (db-page-count db)) (not (memory-db-p db)))
                   (setf created t)
                   (let ((*db* db))
                     (run-in-write-txn db (lambda ()
                                            (let ((h (page-for-write db 1)))
                                              (put-u32 h +hdr-schema-format+ 0)
                                              (put-u32 h +hdr-text-encoding+ 0))))))
                 (when (and (not created) (plusp (db-page-count db))
                            (<= (length (schema-rows (db-schema* db))) 0))
                   (let ((*db* db))
                     (run-in-write-txn db (lambda ()
                                            (let ((h (page-for-write db 1)))
                                              (put-u32 h 52 (if mode 1 0))
                                              (put-u32 h 64 (if (eq mode :incremental) 1 0)))))))
                 (when (eq (db-pending-autovacuum db) :none)
                   (setf (db-pending-autovacuum db) (if (zerop (db-page-count db)) nil :none)))
                 (values nil nil))
               (pragma-rows '("auto_vacuum")
                            (list (list (cond ((not (autovacuum-p db)) 0)
                                              ((incremental-p db) 2)
                                              (t 1)))))))
          ((string= n "incremental_vacuum")
           (when (and (autovacuum-p db) (incremental-p db))
             (let ((*db* db) (k (if value (value-to-integer value) 0)))
               (run-in-write-txn db (lambda () (incremental-vacuum db (if (integerp k) k 0))))))
           (values nil nil))
          ((string= n "wal_checkpoint")
           (pragma-rows '("busy" "log" "checkpointed")
                        (list (cond ((null (db-wal db)) (list 0 -1 -1))
                                    ((db-explicit (conn db)) (sql-error "database table is locked"))
                                    (t (wal-unlock db :none)
                                       (multiple-value-list (wal-checkpoint db)))))))
          ((string= n "foreign_keys")
           (if value
               (progn (setf (db-foreign-keys (conn db)) (pragma-boolean value))
                      (values nil nil))
               (pragma-rows '("foreign_keys") (list (list (if (db-foreign-keys (conn db)) 1 0))))))
          ((string= n "writable_schema")
           (if value
               (progn (setf (db-writable-schema (conn db)) (pragma-boolean value))
                      (values nil nil))
               (pragma-rows '("writable_schema")
                            (list (list (if (db-writable-schema (conn db)) 1 0))))))
          ((string= n "recursive_triggers")
           (if value
               (progn (setf (db-recursive-triggers (conn db)) (pragma-boolean value))
                      (values nil nil))
               (pragma-rows '("recursive_triggers")
                            (list (list (if (db-recursive-triggers (conn db)) 1 0))))))
          ((string= n "foreign_key_list") (pragma-foreign-key-list db value))
          ((string= n "synchronous")
           (if value
               (let ((lv (logand (1+ (safety-level-of value)) 7)))
                 (setf (db-safety-level db) (if (zerop lv) 1 lv))
                 (values nil nil))
               (pragma-rows '("synchronous") (list (list (1- (db-safety-level db)))))))
          ((string= n "case_sensitive_like")
           ;; LIKE becomes case-sensitive (like() re-registered with
           ;; SQLITE_FUNC_CASE); nothing is returned either way
           (when value
             (let ((v (value-to-text value)))
               (setf (db-case-sensitive-like (conn db))
                     (if (if (and (plusp (length v)) (digit-char-p (char v 0)))
                             (/= 0 (or (parse-integer v :junk-allowed t) 0))
                             (member v '("on" "yes" "true") :test #'string-equal))
                         :on :off))))
           (values nil nil))
          ((string= n "secure_delete")
           ;; 0, 1 or FAST (2); a value sets it (for every database when no
           ;; schema is named) and the result is the setting, either way
           (when value
             (let* ((v (value-to-text value))
                    ;; sqlite3GetBoolean: a number, on/yes/true, else false
                    (b (cond ((string-equal v "fast") :fast)
                             ((and (plusp (length v)) (digit-char-p (char v 0)))
                              (/= 0 (or (parse-integer v :junk-allowed t) 0)))
                             (t (and (member v '("on" "yes" "true") :test #'string-equal) t)))))
               (if (eq db (conn db))
                   (dolist (d (conn-dbs db)) (setf (db-secure-delete d) b))
                   (setf (db-secure-delete db) b))))
           (pragma-rows '("secure_delete")
                        (list (list (case (db-secure-delete db) (:fast 2) ((nil) 0) (t 1))))))
          ((member n '("cache_size" "temp_store" "locking_mode"
                       "busy_timeout"
                       "count_changes" "legacy_file_format"
                       "ignore_check_constraints" "defer_foreign_keys" "mmap_size" "optimize"
                       "shrink_memory" "automatic_index")
                   :test #'string=)
           (if value (values nil nil) (pragma-rows (list n) (list (list 0)))))
          ((string= n "table_info") (pragma-table-info db value nil))
          ((string= n "table_xinfo") (pragma-table-info db value t))
          ((string= n "index_list") (pragma-index-list db value))
          ((string= n "index_info") (pragma-index-info db value nil))
          ((string= n "index_xinfo") (pragma-index-info db value t))
          ((string= n "database_list")
           (pragma-rows '("seq" "name" "file")
                        (let ((next 2))
                          ;; seq: main 0, temp 1, attachments from 2
                          (loop for d in (temp-first-list db)
                                collect (list (cond ((eq d (conn db)) 0)
                                                    ((name= (db-name d) "temp") 1)
                                                    (t (prog1 next (incf next))))
                                              (db-name d) (or (db-path d) ""))))))
          ((string= n "table_list") (pragma-table-list db value))
          ((member n '("integrity_check" "quick_check") :test #'string=)
           (let ((problems (integrity-check db)))
             (pragma-rows (list n) (if problems (mapcar #'list problems) (list (list "ok"))))))
          ((string= n "collation_list")
           (pragma-rows '("seq" "name") '((0 "RTRIM") (1 "NOCASE") (2 "BINARY"))))
          ((string= n "compile_options")
           (pragma-rows '("compile_options") (mapcar #'list *compile-options*)))
          ((string= n "function_list")
           (let ((names '()))
             (maphash (lambda (k v) (declare (ignore v)) (push k names)) *functions*)
             (maphash (lambda (k v) (declare (ignore v)) (pushnew k names :test #'string=)) *aggregates*)
             (pragma-rows '("name") (mapcar #'list (sort names #'string<)))))
          (t (values nil nil)))))))

(defun temp-first-list (db)
  "main, temp, then attachments: PRAGMA database_list order."
  (let* ((all (conn-dbs db))
         (tmp (find "temp" all :key #'db-name :test #'name=)))
    (append (list (first all)) (and tmp (list tmp))
            (remove tmp (rest all)))))

(defun exec-attach (db file-expr name)
  (let* ((c (conn db))
         (file (value-to-text (funcall (compile-expr file-expr (make-scope)) nil))))
    (when (or (name= name "main") (name= name "temp")
              (assoc name (db-attached c) :test #'name=))
      (sql-error "database ~a is already in use" name))
    (when (db-explicit c) (sql-error "cannot ATTACH database within transaction"))
    ;; an attachment is opened with the connection's flags: read-only
    ;; stays read-only
    (let ((d (open-database file :readonly (db-readonly c))))
      (setf (db-name d) name (db-conn d) c)
      (setf (db-attached c) (append (db-attached c) (list (cons name d)))))))

(defun exec-detach (db name)
  (let* ((c (conn db))
         (hit (assoc name (db-attached c) :test #'name=)))
    (when (or (null hit) (name= name "temp"))
      (sql-error "no such database: ~a" name))
    (when (db-explicit c) (sql-error "cannot DETACH database within transaction"))
    (close-database (cdr hit))
    (setf (db-attached c) (remove hit (db-attached c)))))

(defun to-signed32 (u) (if (logbitp 31 u) (- u (expt 2 32)) u))

(defun pragma-table-info (db name xinfo)
  (let* ((*db* db) (tb (lookup-table db (value-to-text name) nil)))
    (if (null tb)
        (values nil nil)
        (let ((cols (if (table-view-select tb) (view-column-info tb) (table-columns tb))))
          (values
           (loop with cid = -1
                 for c across cols
                 for i from 0
                 unless (and (or (column-generated c) (column-hidden c)) (not xinfo))
                 collect (append
                          (list (incf cid) (column-name c) (or (column-type c) "")
                                (if (column-not-null c) 1 0)
                                (if (column-default c) (default-text (column-default c)) :null)
                                (let ((pos (position i (table-pk tb))))
                                  (if pos (1+ pos) 0)))
                          (when xinfo (list (cond ((column-hidden c) 1)
                                                  ((column-virtual-p c) 2)
                                                  ((column-generated c) 3)
                                                  (t 0))))))
           (append '("cid" "name" "type" "notnull" "dflt_value" "pk")
                   (when xinfo '("hidden"))))))))

(defun pragma-foreign-key-list (db name)
  (let* ((*db* db) (tb (lookup-table db (value-to-text name) nil)))
    (if (null tb)
        (values nil nil)
        (flet ((act (a) (substitute #\Space #\- (string-upcase (symbol-name a)))))
          (values
           (loop for fk in (reverse (table-fkeys tb))
                 for id from 0
                 append (loop for ci in (fkey-child-cols fk)
                              for seq from 0
                              collect (list id seq (fkey-parent fk)
                                            (column-name (aref (table-columns tb) ci))
                                            (or (nth seq (fkey-parent-cols fk)) :null)
                                            (act (fkey-on-update fk)) (act (fkey-on-delete fk))
                                            "NONE")))
           '("id" "seq" "table" "from" "to" "on_update" "on_delete" "match"))))))

(defun view-column-info (tb)
  (multiple-value-bind (fn cols) (compile-select (table-view-select tb) (make-scope))
    (declare (ignore fn))
    (coerce (loop for (nm) in cols
                  for i from 0
                  collect (make-column :name (or (nth i (table-view-columns tb)) nm) :type ""))
            'vector)))

(defun default-text (e)
  (case (car e)
    (:lit (let ((v (second e)))
            (cond ((stringp v) (format nil "'~a'" (substitute-string "'" "''" v)))
                  ((eq v :null) "NULL")
                  ((floatp v) (format-real v))
                  ((blobp v) (funcall (third (gethash "quote" *functions*)) (list v)))
                  (t (format nil "~a" v)))))
    (:unary (if (eq (second e) :neg) (format nil "-~a" (default-text (third e))) (default-text (third e))))
    (t "?")))

(defun pragma-index-list (db name)
  (let* ((*db* db) (tb (lookup-table db (value-to-text name) nil)))
    (if (null tb)
        (values nil nil)
        (values
         (loop for idx in (sqlite-index-list tb)
               for seq from 0
               collect (list seq (index-name idx) (if (index-unique idx) 1 0)
                             (cond ((index-pk-index idx) "pk")
                                   ((not (index-auto idx)) "c")
                                   ((let ((u (find (mapcar (lambda (c) (list (first c) (second c) (third c)))
                                                           (index-columns idx))
                                                   (table-unique-constraints tb) :key #'first :test #'equal)))
                                      (and u (third u)))
                                    "pk")
                                   (t "u"))
                             (if (index-where idx) 1 0)))
         '("seq" "name" "unique" "origin" "partial")))))

(defun pragma-index-info (db name xinfo)
  (let* ((*db* db) (idx (lookup-index db (value-to-text name))))
    (if (null idx)
        (values nil nil)
        (let ((tb (lookup-table db (index-table idx))))
          (values
           (append
            (loop for (c coll desc) in (index-columns idx)
                  for i from 0
                  collect (append (list i (if (integerp c) c -2)
                                        (if (integerp c) (column-name (aref (table-columns tb) c)) :null))
                                  (when xinfo (list (if desc 1 0) (collation-name coll) 1))))
            ;; xinfo also lists the key suffix every index entry carries
            (when xinfo
              (let ((n (length (index-columns idx)))
                    (used (mapcar #'first (index-columns idx))))
                (cond
                  ((not (table-without-rowid tb)) (list (list n -1 :null 0 "BINARY" 0)))
                  ((index-pk-index idx)
                   (loop for col across (table-columns tb) for ci from 0
                         unless (member ci used)
                           collect (list n ci (column-name col) 0 "BINARY" 0) and do (incf n)))
                  (t (loop for (c coll desc) in (index-pk-tail tb idx)
                           collect (list n c (column-name (aref (table-columns tb) c))
                                         (if desc 1 0) (collation-name coll) 0)
                           do (incf n)))))))
           (append '("seqno" "cid" "name") (when xinfo '("desc" "coll" "key"))))))))

(defun pragma-table-list (db &optional only)
  "Every table and view of every database (or just those named ONLY)."
  (let ((*db* db) (rows '())
        (only (and only (value-to-text only)))
        (dbs (temp-first-list db)))
    (flet ((add (schema name type ncol wr strict)
             (when (or (null only) (name= only name))
               (push (list schema name type ncol wr strict) rows))))
      (dolist (d (if (find "temp" dbs :key #'db-name :test #'name=)
                     dbs
                     (list* (first dbs) :temp (rest dbs))))
        (if (eq d :temp)
            (add "temp" "sqlite_temp_schema" "table" 5 0 0)
            (let ((schema (if (eq d (conn db)) "main" (db-name d)))
                  (tabs '()))
              (maphash (lambda (k tb)
                         (declare (ignore k))
                         (unless (member (table-name tb) '("sqlite_master" "sqlite_schema"
                                                           "sqlite_temp_master" "sqlite_temp_schema")
                                         :test #'name=)
                           (pushnew tb tabs)))
                       (schema-tables (db-schema* d)))
              (dolist (tb (sort tabs #'string< :key #'table-name))
                (add schema (table-name tb)
                     (cond ((table-view-select tb) "view")
                           ((table-vtab tb) "virtual")
                           ((rtree-shadow-p d (table-name tb)) "shadow")
                           (t "table"))
                     (length (if (table-view-select tb) (view-column-info tb) (table-columns tb)))
                     (if (table-without-rowid tb) 1 0)
                     (if (table-strict tb) 1 0)))
              (add schema (if (name= schema "temp") "sqlite_temp_schema" "sqlite_schema")
                   "table" 5 0 0)))))
    (values (nreverse rows)
            '("schema" "name" "type" "ncol" "wr" "strict"))))
