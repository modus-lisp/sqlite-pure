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

(defun run-in-write-txn (db thunk)
  "Run THUNK as one atomic statement."
  (cond
    ((db-explicit db)
     (ensure-write-txn db)
     (statement-begin db)
     (let ((ok nil))
       (unwind-protect
            (handler-bind ((sqlite-conflict
                             (lambda (c)
                               (case (conflict-action c)
                                 (:rollback (rollback-write db) (setf (db-explicit db) nil ok t))
                                 (:fail (setf ok t))))))
              (multiple-value-prog1 (funcall thunk) (setf ok t)))
         (if ok (statement-end db) (statement-rollback db)))))
    (t
     (let ((ok nil) (keep nil))
       (unwind-protect
            (handler-bind ((sqlite-conflict
                             (lambda (c) (when (eq (conflict-action c) :fail) (setf keep t)))))
              (multiple-value-prog1 (funcall thunk) (setf ok t)))
         (if (or ok keep) (commit-write db) (rollback-write db)))))))

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
       (commit-write db)
       (setf (db-explicit db) nil)
       (values nil nil))
      (:rollback
       (unless (db-explicit db) (sql-error "cannot rollback - no transaction is active"))
       (rollback-write db)
       (setf (db-explicit db) nil)
       (values nil nil))
      ((:savepoint :release :rollback-to)
       (sql-error "SAVEPOINT is not supported"))
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
          (multiple-value-setq (rows cols) (exec-ast db (car s) (cdr s))))
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

(defmacro with-transaction ((db) &body body)
  "Run BODY in a transaction: committed on normal exit, rolled back on a
non-local exit."
  (let ((d (gensym "DB")) (ok (gensym "OK")))
    `(let ((,d ,db) (,ok nil))
       (begin-transaction ,d)
       (unwind-protect (multiple-value-prog1 (progn ,@body) (setf ,ok t))
         (when (in-transaction-p ,d)
           (if ,ok (commit ,d) (rollback ,d)))))))

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
          ((member n '("foreign_keys" "synchronous" "cache_size" "temp_store" "locking_mode"
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
           (pragma-rows '("seq" "name" "file") (list (list 0 "main" (or (db-path db) "")))))
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

(defun to-signed32 (u) (if (logbitp 31 u) (- u (expt 2 32)) u))

(defun pragma-table-info (db name xinfo)
  (let* ((*db* db) (tb (lookup-table db (value-to-text name) nil)))
    (if (null tb)
        (values nil nil)
        (let ((cols (if (table-view-select tb) (view-column-info tb) (table-columns tb))))
          (values
           (loop for c across cols
                 for i from 0
                 collect (append
                          (list i (column-name c) (or (column-type c) "")
                                (if (column-not-null c) 1 0)
                                (if (column-default c) (default-text (column-default c)) :null)
                                (let ((pos (position i (table-pk tb))))
                                  (if pos (1+ pos) 0)))
                          (when xinfo (list 0))))
           (append '("cid" "name" "type" "notnull" "dflt_value" "pk")
                   (when xinfo '("hidden"))))))))

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
