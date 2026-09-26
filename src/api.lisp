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
      :create-trigger :drop :alter)
     t)
    (:pragma (and (getf (cdr st) :value)
                  (member (getf (cdr st) :name)
                          '("user_version" "application_id" "schema_version")
                          :test #'name=)))
    (t nil)))

(defun commit-all (db) (dolist (d (conn-dbs db)) (commit-write d)))
(defun rollback-all (db)
  (setf (db-fk-deferred (conn db)) nil)
  (dolist (d (conn-dbs db)) (rollback-write d)))

(defun run-in-write-txn (db thunk)
  "Run THUNK as one atomic statement (across every attached database)."
  (cond
    ((db-explicit db)
     (let ((ok nil) (started (conn-dbs db)))
       (dolist (d started) (statement-begin d))
       (unwind-protect
            (handler-bind ((sqlite-conflict
                             (lambda (c)
                               (case (conflict-action c)
                                 (:rollback (rollback-all db) (setf (db-explicit db) nil ok t))
                                 (:fail (setf ok t))))))
              (multiple-value-prog1 (funcall thunk) (setf ok t)))
         (dolist (d (conn-dbs db))
           (if (and (not ok) (member d started)) (statement-rollback d) (statement-end d))))))
    (t
     (let ((ok nil) (keep nil))
       (unwind-protect
            (handler-bind ((sqlite-conflict
                             (lambda (c) (when (eq (conflict-action c) :fail) (setf keep t)))))
              (multiple-value-prog1 (funcall thunk) (setf ok t)))
         (if (or ok keep)
             (handler-bind ((error (lambda (c) (declare (ignore c)) (rollback-all db))))
               (fk-check-deferred db)
               (commit-all db))
             (rollback-all db)))))))

(defun exec-ast (db st text)
  "Execute one parsed statement.  Return (values rows column-names)."
  (let ((*db* db) (*encoding* (db-encoding db)))
    (case (car st)
      (:select
       (multiple-value-bind (fn cols) (compile-select (second st) (make-scope))
         (values (funcall fn nil) (mapcar #'first cols))))
      (:begin
       (when (db-explicit db) (sql-error "cannot start a transaction within a transaction"))
       (setf (db-explicit db) t)
       (values nil nil))
      (:commit
       (unless (db-explicit db) (sql-error "cannot commit - no transaction is active"))
       (fk-check-deferred db)
       (commit-all db)
       (setf (db-explicit db) nil (db-savepoint-txn db) nil)
       (values nil nil))
      (:rollback
       (unless (db-explicit db) (sql-error "cannot rollback - no transaction is active"))
       (rollback-all db)
       (setf (db-explicit db) nil)
       (values nil nil))
      (:savepoint
       (unless (db-explicit db) (setf (db-explicit db) t (db-savepoint-txn db) t))
       (dolist (d (conn-dbs db)) (savepoint-push d (second st)))
       (values nil nil))
      (:release
       (let ((outermost (savepoint-outermost-p db (second st))))
         (dolist (d (conn-dbs db)) (savepoint-pop d (second st)))
         (when (and outermost (db-savepoint-txn db))
           (commit-all db)
           (setf (db-explicit db) nil (db-savepoint-txn db) nil)))
       (values nil nil))
      (:rollback-to
       (savepoint-outermost-p db (second st))   ; signals if unknown
       (dolist (d (conn-dbs db)) (savepoint-restore d (second st)))
       (values nil nil))
      (:attach (exec-attach db (second st) (third st)) (values nil nil))
      (:detach (exec-detach db (second st)) (values nil nil))
      (:noop (values nil nil))
      (:pragma (exec-pragma db st))
      (t
       (unless (write-statement-p st) (sql-error "unsupported statement"))
       (run-in-write-txn
        db
        (lambda ()
          (let ((*index-expr-cache* nil))
            (ecase (car st)
              (:insert (exec-insert st))
              (:update (exec-update st))
              (:delete (exec-delete st))
              (:create-table (exec-create-table st text))
              (:create-index (exec-create-index st text))
              (:create-view (exec-create-view st text))
              (:create-trigger (exec-create-trigger st text))
              (:drop (exec-drop st))
              (:alter (exec-alter st))
              (:pragma (exec-pragma db st))))))))))

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
  (with-sql-floats
    (multiple-value-bind (stmts nparam names) (parse-sql-cached db sql)
      (let ((*params* (bind-params params nparam))
            (*param-names* names)
            (rows nil) (cols nil))
        (dolist (s stmts)
          (let ((*json-values* (make-hash-table :test #'eq)))
            (unwind-protect
                 (progn
                   (dolist (d (conn-dbs db)) (lock-shared d))
                   (multiple-value-setq (rows cols) (exec-ast db (car s) (cdr s))))
              ;; outside a transaction every statement is its own read transaction
              (unless (db-explicit db)
                (dolist (d (conn-dbs db))
                  (unless (db-txn d) (unlock-to d :none)))))))
        (values rows cols)))))

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

(defun pragma-rows (names rows) (values rows names))

(defun exec-pragma (db st)
  (destructuring-bind (&key name value) (cdr st)
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
           (pragma-rows '("journal_mode") (list (list (if (memory-db-p db) "memory" "delete")))))
          ((string= n "foreign_keys")
           (if value
               (progn (setf (db-foreign-keys (conn db))
                            (let ((v (if (stringp value) (string-downcase-ascii value) value)))
                              (not (member v '(0 "0" "off" "false" "no") :test #'equal))))
                      (values nil nil))
               (pragma-rows '("foreign_keys") (list (list (if (db-foreign-keys (conn db)) 1 0))))))
          ((string= n "foreign_key_list") (pragma-foreign-key-list db value))
          ((member n '("synchronous" "cache_size" "temp_store" "locking_mode"
                       "busy_timeout" "recursive_triggers" "case_sensitive_like" "auto_vacuum"
                       "secure_delete" "count_changes" "legacy_file_format" "writable_schema"
                       "ignore_check_constraints" "defer_foreign_keys" "mmap_size" "optimize"
                       "wal_checkpoint" "shrink_memory" "automatic_index")
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
          ((string= n "table_list") (pragma-table-list db))
          ((member n '("integrity_check" "quick_check") :test #'string=)
           (let ((problems (integrity-check db)))
             (pragma-rows (list n) (if problems (mapcar #'list problems) (list (list "ok"))))))
          ((string= n "collation_list")
           (pragma-rows '("seq" "name") '((0 "RTRIM") (1 "NOCASE") (2 "BINARY"))))
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
    (let ((d (open-database file)))
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
                 unless (and (column-generated c) (not xinfo))
                 collect (append
                          (list (incf cid) (column-name c) (or (column-type c) "")
                                (if (column-not-null c) 1 0)
                                (if (column-default c) (default-text (column-default c)) :null)
                                (let ((pos (position i (table-pk tb))))
                                  (if pos (1+ pos) 0)))
                          (when xinfo (list (cond ((column-virtual-p c) 2)
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
         (loop for idx in (reverse (remove-if #'index-pk-index (table-indexes tb)))
               for seq from 0
               collect (list seq (index-name idx) (if (index-unique idx) 1 0)
                             (cond ((not (index-auto idx)) "c")
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
           (loop for (c coll desc) in (index-columns idx)
                 for i from 0
                 collect (append (list i (if (integerp c) c -2)
                                       (if (integerp c) (column-name (aref (table-columns tb) c)) :null))
                                 (when xinfo (list (if desc 1 0) (symbol-name coll) 1))))
           (append '("seqno" "cid" "name") (when xinfo '("desc" "coll" "key"))))))))

(defun pragma-table-list (db)
  (let ((*db* db) (rows '()))
    (maphash (lambda (k tb)
               (unless (string= k "sqlite_master")
                 (push (list "main" (table-name tb)
                             (if (table-view-select tb) "view" "table")
                             (length (table-columns tb))
                             (if (table-without-rowid tb) 1 0) 0)
                       rows)))
             (schema-tables (db-schema* db)))
    (values (sort rows #'string< :key #'second)
            '("schema" "name" "type" "ncol" "wr" "strict"))))
