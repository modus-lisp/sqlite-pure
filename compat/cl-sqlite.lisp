;;;; cl-sqlite.lisp — the API of cl-sqlite (the SQLITE package: CONNECT,
;;;; EXECUTE-TO-LIST, PREPARE-STATEMENT, STEP-STATEMENT, the iterate drivers,
;;;; ...) over sqlite-pure, so that code written for cl-sqlite runs unchanged
;;;; with no libsqlite3.  Load the system "sqlite-pure/cl-sqlite" in place of
;;;; "sqlite"; the two define the same package and cannot be loaded together.
;;;;
;;;; As in cl-sqlite, NULL is NIL, integers are integers, REALs are
;;;; DOUBLE-FLOATs, TEXT is a string and a BLOB is an (unsigned-byte 8)
;;;; vector.  A statement runs when it is first stepped; its rows are then
;;;; handed out one STEP-STATEMENT at a time.

(defpackage :sqlite.cache
  (:use :cl)
  (:export :mru-cache :get-from-cache :put-to-cache :purge-cache))

(defpackage :sqlite
  (:use :cl :iter)
  (:export :sqlite-error
           :sqlite-constraint-error
           :sqlite-error-db-handle
           :sqlite-error-code
           :sqlite-error-message
           :sqlite-error-sql
           :sqlite-handle
           :connect
           :set-busy-timeout
           :disconnect
           :sqlite-statement
           :prepare-statement
           :finalize-statement
           :step-statement
           :reset-statement
           :clear-statement-bindings
           :statement-column-value
           :statement-column-names
           :statement-bind-parameter-names
           :bind-parameter
           :execute-non-query
           :execute-to-list
           :execute-single
           :execute-single/named
           :execute-one-row-m-v/named
           :execute-to-list/named
           :execute-non-query/named
           :execute-one-row-m-v
           :last-insert-rowid
           :with-transaction
           :with-open-database))

;;; ------------------------------------------------------------------
;;; The statement cache (cl-sqlite's SQLITE.CACHE): statements finalized
;;; with FINALIZE-STATEMENT wait here, keyed by their SQL, to be handed out
;;; again by PREPARE-STATEMENT.

(in-package :sqlite.cache)

(defclass mru-cache ()
  ((objects :initform (make-hash-table :test 'equal) :reader objects)
   (order :initform '() :accessor order)          ; ids, most recently put first
   (cache-size :initarg :cache-size :initform 100 :reader cache-size)
   (destructor :initarg :destructor :initform #'identity :reader destructor)))

(defun get-from-cache (cache id)
  (let ((stack (gethash id (objects cache))))
    (when stack
      (let ((object (pop (gethash id (objects cache)))))
        (setf (order cache) (remove id (order cache) :count 1 :test #'equal))
        object))))

(defun put-to-cache (cache id object)
  (push object (gethash id (objects cache)))
  (push id (order cache))
  ;; over the limit: destroy the least recently put
  (when (> (length (order cache)) (cache-size cache))
    (let* ((victim (car (last (order cache))))
           (stack (gethash victim (objects cache)))
           (object (car (last stack))))
      (setf (order cache) (butlast (order cache))
            (gethash victim (objects cache)) (butlast stack))
      (funcall (destructor cache) object))))

(defun purge-cache (cache)
  (maphash (lambda (id stack)
             (declare (ignore id))
             (map nil (destructor cache) stack))
           (objects cache))
  (clrhash (objects cache))
  (setf (order cache) '()))

;;; ------------------------------------------------------------------
;;; Conditions

(in-package :sqlite)

(define-condition sqlite-error (simple-error)
  ((handle     :initform nil :initarg :db-handle
               :reader sqlite-error-db-handle)
   (error-code :initform nil :initarg :error-code
               :reader sqlite-error-code)
   (error-msg  :initform nil :initarg :error-msg
               :reader sqlite-error-message)
   (statement  :initform nil :initarg :statement
               :reader sqlite-error-statement)
   (sql        :initform nil :initarg :sql
               :reader sqlite-error-sql)))

(define-condition sqlite-constraint-error (sqlite-error)
  ())

(defun sqlite-error (error-code message &key statement
                                             (db-handle (and statement (db statement)))
                                             (sql-text (and statement (sql statement)))
                                             error-msg)
  (error (if (eq error-code :constraint) 'sqlite-constraint-error 'sqlite-error)
         :format-control (if (listp message) (first message) message)
         :format-arguments (if (listp message) (rest message))
         :db-handle db-handle
         :error-code error-code
         :error-msg error-msg
         :statement statement
         :sql sql-text))

(defmethod print-object :after ((obj sqlite-error) stream)
  (unless *print-escape*
    (when (or (and (sqlite-error-code obj)
                   (not (eq (sqlite-error-code obj) :ok)))
              (sqlite-error-message obj))
      (format stream "~&Code ~A: ~A."
              (or (sqlite-error-code obj) :ok)
              (or (sqlite-error-message obj) "no message")))
    (when (sqlite-error-db-handle obj)
      (format stream "~&Database: ~A"
              (database-path (sqlite-error-db-handle obj))))
    (when (sqlite-error-sql obj)
      (format stream "~&SQL: ~A" (sqlite-error-sql obj)))))

(defun result-code (c)
  "The SQLite result code (cl-sqlite's keyword) of sqlite-pure's error C."
  (let ((code (sqlp:sqlite-error-code c)))
    (case code
      ((:parse nil) :error)
      (t code))))

(defmacro with-sqlite-errors ((message &rest keys) &body body)
  "Run BODY; an error of sqlite-pure's becomes cl-sqlite's SQLITE-ERROR
with MESSAGE, its result code, and its text as the error message."
  (let ((c (gensym "C")))
    `(handler-case (progn ,@body)
       (sqlp:sqlite-error (,c)
         (sqlite-error (result-code ,c) ,message :error-msg (sqlp:sqlite-error-message ,c) ,@keys)))))

;;; ------------------------------------------------------------------
;;; Connections

(defclass sqlite-handle ()
  ((handle :accessor handle)
   (database-path :accessor database-path)
   (cache :accessor cache)
   (statements :initform nil :accessor sqlite-handle-statements))
  (:documentation "Class that encapsulates the connection to the database. Use connect and disconnect."))

(defmethod initialize-instance :after ((object sqlite-handle) &key (database-path ":memory:") &allow-other-keys)
  (handler-case
      (setf (handle object) (sqlp:open-database database-path)
            (database-path object) database-path)
    ((or sqlp:sqlite-error file-error) ()
      (sqlite-error :cantopen (list "Could not open sqlite3 database ~A" database-path))))
  ;; SQLite waits for no lock unless given a busy timeout
  (setf (sqlp::db-busy-timeout (handle object)) 0)
  (setf (cache object) (make-instance 'sqlite.cache:mru-cache
                                      :cache-size 16 :destructor #'really-finalize-statement)))

(defun connect (database-path &key busy-timeout)
  "Connect to the sqlite database at the given DATABASE-PATH. Returns the SQLITE-HANDLE connected to the database. Use DISCONNECT to disconnect.
   Operations will wait for locked databases for up to BUSY-TIMEOUT milliseconds; if BUSY-TIMEOUT is NIL, then operations on locked databases will fail immediately."
  (let ((db (make-instance 'sqlite-handle
                           :database-path (etypecase database-path
                                            (string database-path)
                                            (pathname (namestring database-path))))))
    (when busy-timeout
      (set-busy-timeout db busy-timeout))
    db))

(defun set-busy-timeout (db milliseconds)
  "Sets the maximum amount of time to wait for a locked database."
  (setf (sqlp::db-busy-timeout (handle db)) (/ (max 0 milliseconds) 1000))
  :ok)

(defun disconnect (handle)
  "Disconnects the given HANDLE from the database. All further operations on the handle are invalid."
  (sqlite.cache:purge-cache (cache handle))
  (dolist (statement (copy-list (sqlite-handle-statements handle)))
    (really-finalize-statement statement))
  (with-sqlite-errors ("Could not close sqlite3 database." :db-handle handle)
    (sqlp:close-database (handle handle)))
  (slot-makunbound handle 'handle))

;;; ------------------------------------------------------------------
;;; Statements

(defclass sqlite-statement ()
  ((db :reader db :initarg :db)
   (handle :accessor handle)            ; the parsed statement: (ast . text)
   (sql :reader sql :initarg :sql)
   (columns-count :accessor resultset-columns-count)
   (columns-names :accessor resultset-columns-names :reader statement-column-names)
   (parameters-count :accessor parameters-count)
   (parameters-names :accessor parameters-names :reader statement-bind-parameter-names)
   (names :accessor names)              ; sqlite-pure's alist name -> index
   (bindings :accessor bindings)        ; a vector of SQL values
   (rows :initform nil :accessor rows)  ; the rows not yet stepped to
   (row :initform nil :accessor row)    ; the current row
   (state :initform :ready :accessor state)    ; :ready :running :done
   (failure :initform nil :accessor failure))  ; (code message) of a failed step
  (:documentation "Class that represents the prepared statement."))

(defmethod initialize-instance :after ((object sqlite-statement) &key &allow-other-keys)
  (let ((db (db object)) (sql (sql object)))
    (multiple-value-bind (stmts nparam names)
        (with-sqlite-errors ("Could not prepare an sqlite statement." :db-handle db :sql-text sql)
          (sqlp::parse-sql-cached (handle db) sql))
      (when (cdr stmts)
        (sqlite-error nil "SQL string contains more than one SQL statement." :sql-text sql))
      (let* ((st (first stmts))
             (columns (and st
                           (with-sqlite-errors ("Could not prepare an sqlite statement."
                                                :db-handle db :sql-text sql)
                             (sqlp::statement-columns (handle db) (car st) (cdr st))))))
        (setf (handle object) st
              (names object) names
              (bindings object) (make-array nparam :initial-element :null)
              (resultset-columns-count object) (length columns)
              (resultset-columns-names object) columns
              (parameters-count object) nparam
              (parameters-names object)
              (loop for i from 1 to nparam
                    collect (car (rassoc i names))))))))

(defun prepare-statement (db sql)
  "Prepare the statement to the DB that will execute the commands that are in SQL.

Returns the SQLITE-STATEMENT.

SQL must contain exactly one statement.
SQL may have some positional (not named) parameters specified with question marks.

Example:

 select name from users where id = ?"
  (or (let ((statement (sqlite.cache:get-from-cache (cache db) sql)))
        (when statement
          (clear-statement-bindings statement))
        statement)
      (let ((statement (make-instance 'sqlite-statement :db db :sql sql)))
        (push statement (sqlite-handle-statements db))
        statement)))

(defun really-finalize-statement (statement)
  (setf (sqlite-handle-statements (db statement))
        (delete statement (sqlite-handle-statements (db statement))))
  (slot-makunbound statement 'handle))

(defun finalize-statement (statement)
  "Finalizes the statement and signals that associated resources may be released.
Note: does not immediately release resources because statements are cached."
  (reset-statement statement)
  (sqlite.cache:put-to-cache (cache (db statement)) (sql statement) statement))

(defun run-statement (statement)
  "Run STATEMENT with its bindings: its rows are then stepped through.  A
failure is signalled now and again by the next RESET-STATEMENT (as
sqlite3_reset returns the error of the step before it)."
  (let ((st (handle statement)))
    (setf (rows statement)
          (when st
            (multiple-value-bind (rows cols)
                (handler-case
                    (sqlp::run-parsed (handle (db statement)) (sql statement) (list st)
                                      (copy-seq (bindings statement)) (names statement))
                  (sqlp:sqlite-error (c)
                    (setf (state statement) :done
                          (failure statement) (list (result-code c) (sqlp:sqlite-error-message c)))
                    (sqlite-error (result-code c) "Error while stepping an sqlite statement."
                                  :statement statement :error-msg (sqlp:sqlite-error-message c))))
              ;; a PRAGMA or RETURNING names its columns as it runs
              (when (and cols (null (resultset-columns-names statement)))
                (setf (resultset-columns-names statement) cols
                      (resultset-columns-count statement) (length cols)))
              rows))
          (state statement) :running)))

(defun step-statement (statement)
  "Steps to the next row of the resultset of STATEMENT.
Returns T is successfully advanced to the next row and NIL if there are no more rows."
  (when (eq (state statement) :done)
    ;; stepping again after the end starts over (sqlite3_step's auto-reset)
    (setf (failure statement) nil)
    (reset-statement statement))
  (when (eq (state statement) :ready)
    (run-statement statement))
  (if (rows statement)
      (progn (setf (row statement) (pop (rows statement))) t)
      (progn (setf (row statement) nil (state statement) :done) nil)))

(defun reset-statement (statement)
  "Resets the STATEMENT and prepare it to be called again."
  (setf (rows statement) nil (row statement) nil (state statement) :ready)
  (let ((failure (failure statement)))
    (when failure
      (setf (failure statement) nil)
      (sqlite-error (first failure) "Error while resetting an sqlite statement."
                    :statement statement :error-msg (second failure))))
  nil)

(defun clear-statement-bindings (statement)
  "Sets all binding values to NULL."
  (fill (bindings statement) :null)
  nil)

(defun sql-to-lisp (v)
  (cond ((eq v :null) nil)
        ((typep v '(simple-array (unsigned-byte 8) (*))) (copy-seq v))
        (t v)))

(defun statement-column-value (statement column-number)
  "Returns the COLUMN-NUMBER-th column's value of the current row of the STATEMENT. Columns are numbered from zero.
Returns:
 * NIL for NULL
 * INTEGER for integers
 * DOUBLE-FLOAT for floats
 * STRING for text
 * (SIMPLE-ARRAY (UNSIGNED-BYTE 8)) for BLOBs"
  (let ((row (row statement)))
    (and row (sql-to-lisp (nth column-number row)))))

(defun row-values (statement)
  (mapcar #'sql-to-lisp (row statement)))

(defun statement-parameter-index (statement parameter-name)
  (or (cdr (assoc parameter-name (names statement) :test #'string=)) 0))

(defun bind-parameter (statement parameter value)
  "Sets the PARAMETER-th parameter in STATEMENT to the VALUE.
PARAMETER may be parameter index (starting from 1) or parameters name.
Supported types:
 * NULL. Passed as NULL
 * INTEGER. Passed as an 64-bit integer
 * STRING. Passed as a string
 * FLOAT. Passed as a double
 * (VECTOR (UNSIGNED-BYTE 8)) and VECTOR that contains integers in range [0,256). Passed as a BLOB"
  (let* ((index (etypecase parameter
                  (integer parameter)
                  (string (statement-parameter-index statement parameter))))
         (v (typecase value
              (null :null)
              ;; (cl-sqlite hands it to sqlite3_bind_int64 through CFFI)
              (integer (if (typep value '(signed-byte 64))
                           value
                           (error 'type-error :datum value :expected-type '(signed-byte 64))))
              (double-float value)
              (real (coerce value 'double-float))
              (string (coerce value 'simple-string))
              ((vector (unsigned-byte 8))
               (coerce value '(simple-array (unsigned-byte 8) (*))))
              (vector (map '(simple-array (unsigned-byte 8) (*)) #'identity value))
              (t (sqlite-error nil
                               (list "Do not know how to pass value ~A of type ~A to sqlite."
                                     value (type-of value))
                               :statement statement)))))
    ;; sqlite3_bind_*: only a statement not yet stepped (or reset since)
    (unless (eq (state statement) :ready)
      (sqlite-error :misuse (list "Error when binding parameter ~A to value ~A." parameter value)
                    :statement statement :error-msg "bad parameter or other API misuse"))
    (unless (<= 1 index (length (bindings statement)))
      (sqlite-error :range (list "Error when binding parameter ~A to value ~A." parameter value)
                    :statement statement :error-msg "column index out of range"))
    (setf (aref (bindings statement) (1- index)) v)
    nil))

;;; ------------------------------------------------------------------
;;; Executing SQL

(defmacro with-prepared-statement (statement-var (db sql parameters-var) &body body)
  (let ((i-var (gensym "I")) (value-var (gensym "VALUE")))
    `(let ((,statement-var (prepare-statement ,db ,sql)))
       (unwind-protect
            (progn
              (loop for ,i-var from 1
                    for ,value-var in ,parameters-var
                    do (bind-parameter ,statement-var ,i-var ,value-var))
              ,@body)
         (finalize-statement ,statement-var)))))

(defmacro with-prepared-statement/named (statement-var (db sql parameters-var) &body body)
  (let ((name-var (gensym "NAME")) (value-var (gensym "VALUE")))
    `(let ((,statement-var (prepare-statement ,db ,sql)))
       (unwind-protect
            (progn
              (loop for (,name-var ,value-var) on ,parameters-var by #'cddr
                    do (bind-parameter ,statement-var (string ,name-var) ,value-var))
              ,@body)
         (finalize-statement ,statement-var)))))

(defun execute-non-query (db sql &rest parameters)
  "Executes the query SQL to the database DB with given PARAMETERS. Returns nothing.

Example:

\(execute-non-query db \"insert into users (user_name, real_name) values (?, ?)\" \"joe\" \"Joe the User\")

See BIND-PARAMETER for the list of supported parameter types."
  (with-prepared-statement statement (db sql parameters)
    (step-statement statement)))

(defun execute-non-query/named (db sql &rest parameters)
  "Executes the query SQL to the database DB with given PARAMETERS. Returns nothing.

PARAMETERS is a list of alternating parameter names and values.

Example:

\(execute-non-query db \"insert into users (user_name, real_name) values (:name, :real_name)\" \":name\" \"joe\" \":real_name\" \"Joe the User\")

See BIND-PARAMETER for the list of supported parameter types."
  (with-prepared-statement/named statement (db sql parameters)
    (step-statement statement)))

(defun all-rows (stmt)
  (loop while (step-statement stmt) collect (row-values stmt)))

(defun execute-to-list (db sql &rest parameters)
  "Executes the query SQL to the database DB with given PARAMETERS. Returns the results as list of lists.

Example:

\(execute-to-list db \"select id, user_name, real_name from users where user_name = ?\" \"joe\")
=>
\((1 \"joe\" \"Joe the User\")
 (2 \"joe\" \"Another Joe\"))

See BIND-PARAMETER for the list of supported parameter types."
  (with-prepared-statement stmt (db sql parameters)
    (all-rows stmt)))

(defun execute-to-list/named (db sql &rest parameters)
  "Executes the query SQL to the database DB with given PARAMETERS. Returns the results as list of lists.

PARAMETERS is a list of alternating parameters names and values.

Example:

\(execute-to-list db \"select id, user_name, real_name from users where user_name = :user_name\" \":user_name\" \"joe\")
=>
\((1 \"joe\" \"Joe the User\")
 (2 \"joe\" \"Another Joe\"))

See BIND-PARAMETER for the list of supported parameter types."
  (with-prepared-statement/named stmt (db sql parameters)
    (all-rows stmt)))

(defun first-row-values (stmt)
  (if (step-statement stmt)
      (values-list (row-values stmt))
      (values-list (make-list (resultset-columns-count stmt)))))

(defun execute-one-row-m-v (db sql &rest parameters)
  "Executes the query SQL to the database DB with given PARAMETERS. Returns the first row as multiple values.

Example:
\(execute-one-row-m-v db \"select id, user_name, real_name from users where id = ?\" 1)
=>
\(values 1 \"joe\" \"Joe the User\")

See BIND-PARAMETER for the list of supported parameter types."
  (with-prepared-statement stmt (db sql parameters)
    (first-row-values stmt)))

(defun execute-one-row-m-v/named (db sql &rest parameters)
  "Executes the query SQL to the database DB with given PARAMETERS. Returns the first row as multiple values.

PARAMETERS is a list of alternating parameters names and values.

Example:
\(execute-one-row-m-v db \"select id, user_name, real_name from users where id = :id\" \":id\" 1)
=>
\(values 1 \"joe\" \"Joe the User\")

See BIND-PARAMETER for the list of supported parameter types."
  (with-prepared-statement/named stmt (db sql parameters)
    (first-row-values stmt)))

(defun execute-single (db sql &rest parameters)
  "Executes the query SQL to the database DB with given PARAMETERS. Returns the first column of the first row as single value.

Example:
\(execute-single db \"select user_name from users where id = ?\" 1)
=>
\"joe\"

See BIND-PARAMETER for the list of supported parameter types."
  (with-prepared-statement stmt (db sql parameters)
    (and (step-statement stmt) (statement-column-value stmt 0))))

(defun execute-single/named (db sql &rest parameters)
  "Executes the query SQL to the database DB with given PARAMETERS. Returns the first column of the first row as single value.

PARAMETERS is a list of alternating parameters names and values.

Example:
\(execute-single db \"select user_name from users where id = :id\" \":id\" 1)
=>
\"joe\"

See BIND-PARAMETER for the list of supported parameter types."
  (with-prepared-statement/named stmt (db sql parameters)
    (and (step-statement stmt) (statement-column-value stmt 0))))

(defun last-insert-rowid (db)
  "Returns the auto-generated ID of the last inserted row on the database connection DB."
  (sqlp:last-insert-rowid (handle db)))

(defmacro with-transaction (db &body body)
  "Wraps the BODY inside the transaction."
  (let ((ok (gensym "TRANSACTION-COMMIT-"))
        (db-var (gensym "DB-")))
    `(let (,ok
           (,db-var ,db))
       (execute-non-query ,db-var "begin transaction")
       (unwind-protect
            (multiple-value-prog1
                (progn ,@body)
              (setf ,ok t))
         (if ,ok
             (execute-non-query ,db-var "commit transaction")
             (execute-non-query ,db-var "rollback transaction"))))))

(defmacro with-open-database ((db path &key busy-timeout) &body body)
  `(let ((,db (connect ,path :busy-timeout ,busy-timeout)))
     (unwind-protect
          (progn ,@body)
       (disconnect ,db))))

;;; ------------------------------------------------------------------
;;; iterate drivers:
;;;   (for (a b) in-sqlite-query "..." on-database db [with-parameters (x y)])
;;;   (for (a b) in-sqlite-query/named "..." on-database db [with-parameters (":x" x)])
;;;   (for (a b) on-sqlite-statement statement)

(defmacro-driver (for vars in-sqlite-query query-expression on-database db &optional with-parameters parameters)
  (let ((statement (gensym "STATEMENT-"))
        (kwd (if generate 'generate 'for))
        (n (if (symbolp vars) 1 (length vars))))
    `(progn (with ,statement = (prepare-statement ,db ,query-expression))
            (finally-protected (when ,statement (finalize-statement ,statement)))
            ,@(when parameters
                `((initially ,@(loop for i from 1
                                     for value in parameters
                                     collect `(bind-parameter ,statement ,i ,value)))))
            (,kwd ,(if (symbolp vars) `(values ,vars) `(values ,@vars))
                  next (if (step-statement ,statement)
                           (values ,@(loop for i below n
                                           collect `(statement-column-value ,statement ,i)))
                           (terminate))))))

(defmacro-driver (for vars in-sqlite-query/named query-expression on-database db &optional with-parameters parameters)
  (let ((statement (gensym "STATEMENT-"))
        (kwd (if generate 'generate 'for))
        (n (if (symbolp vars) 1 (length vars))))
    `(progn (with ,statement = (prepare-statement ,db ,query-expression))
            (finally-protected (when ,statement (finalize-statement ,statement)))
            ,@(when parameters
                `((initially ,@(loop for (name value) on parameters by #'cddr
                                     collect `(bind-parameter ,statement ,name ,value)))))
            (,kwd ,(if (symbolp vars) `(values ,vars) `(values ,@vars))
                  next (if (step-statement ,statement)
                           (values ,@(loop for i below n
                                           collect `(statement-column-value ,statement ,i)))
                           (terminate))))))

(defmacro-driver (for vars on-sqlite-statement statement)
  (let ((statement-var (gensym "STATEMENT-"))
        (kwd (if generate 'generate 'for))
        (n (if (symbolp vars) 1 (length vars))))
    `(progn (with ,statement-var = ,statement)
            (,kwd ,(if (symbolp vars) `(values ,vars) `(values ,@vars))
                  next (if (step-statement ,statement-var)
                           (values ,@(loop for i below n
                                           collect `(statement-column-value ,statement-var ,i)))
                           (terminate))))))
