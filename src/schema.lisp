;;;; schema.lisp — the catalogue, read from sqlite_schema (page 1).

(in-package #:sqlite-pure)

(defstruct column
  name type affinity (collation :binary) not-null default pk unique
  generated stored gen-fn hidden)

(defun column-virtual-p (c) (and (column-generated c) (not (column-stored c))))

(defstruct table
  name root sql
  owner                  ; the database (pager) the table lives in
  columns                ; vector of COLUMN
  rowid-alias            ; index of the INTEGER PRIMARY KEY column, or NIL
  without-rowid
  pk                     ; list of column indexes making the PRIMARY KEY
  pk-spec                ; list of (column-index collation desc) for the PRIMARY KEY
  autoincrement
  checks                 ; list of (name . expr)
  indexes                ; list of INDEX
  strict
  vtab                   ; an RTREE, or (:unknown module), for CREATE VIRTUAL TABLE
  view-select            ; SEL, for views
  view-columns
  (unique-constraints '()) ; list of (col-idxs collations conflict) in declaration order
  (fkeys '())            ; list of FKEY, declaration order
  pk-conflict)

(defstruct fkey
  child-cols             ; column indexes in the child table
  parent                 ; parent table name
  parent-cols            ; parent column names, or NIL for its primary key
  (on-delete :no-action) (on-update :no-action)
  deferred)

(defstruct index
  name table root sql unique
  columns                ; list of (colidx-or-expr collation desc)
  where                  ; partial index predicate or NIL
  auto
  conflict
  pk-index)              ; the implicit index that backs a WITHOUT ROWID table

(defstruct schema
  (tables (make-hash-table :test #'equalp))   ; name (downcased) -> TABLE
  (indexes (make-hash-table :test #'equalp))
  (triggers (make-hash-table :test #'equalp)) ; name -> (table . ast)
  (rows '()))                                 ; raw sqlite_schema rows

(defun schema-key (name) (string-downcase-ascii name))

(defparameter +schema-table-sql+
  "CREATE TABLE sqlite_schema(type text,name text,tbl_name text,rootpage integer,sql text)")

(defun make-schema-table ()
  (let ((tb (table-from-ast "sqlite_schema"
                            (car (first (parse-sql +schema-table-sql+))) 1 +schema-table-sql+)))
    tb))

(defun find-column (table name)
  (position name (table-columns table) :key #'column-name :test #'name=))

(defun rowid-name-p (name)
  (member name '("rowid" "oid" "_rowid_") :test #'name=))

(defun table-virtual-p (table)
  "True if some column is a VIRTUAL generated column (not in the record)."
  (some #'column-virtual-p (table-columns table)))

(defun table-column-names (table)
  (map 'list #'column-name (table-columns table)))

;;; ------------------------------------------------------------------
;;; Building TABLE from a CREATE TABLE AST

(defun collate-of (c) (if (column-collation c) (column-collation c) :binary))

(defun expr-column-name (e)
  "If E (maybe under COLLATE) is a bare column reference, its name."
  (let ((e (if (eq (car e) :collate) (second e) e)))
    (when (eq (car e) :col) (third e))))

(defun table-from-ast (name ast root sql)
  (destructuring-bind (&key columns constraints without-rowid strict &allow-other-keys) (cdr ast)
    (let* ((cols (coerce
                  (loop for cd in columns
                        collect (let ((ty (getf cd :type)))
                                  (make-column :name (getf cd :name)
                                               :type ty
                                               :affinity (type-affinity ty)
                                               :collation (if (getf cd :collate)
                                                              (collation-keyword (getf cd :collate))
                                                              :binary)
                                               :not-null (getf cd :not-null)
                                               :default (getf cd :default)
                                               :pk (getf cd :primary-key)
                                               :unique (getf cd :unique)
                                               :generated (getf cd :generated)
                                               :stored (getf cd :stored))))
                  'vector))
           (tb (progn
                 (when strict
                   (loop for c across cols
                         for ty = (string-upcase-ascii (or (column-type c) ""))
                         do (unless (member ty '("INT" "INTEGER" "REAL" "TEXT" "BLOB" "ANY") :test #'string=)
                              (sql-error (if (string= ty "")
                                             "missing datatype for ~a.~a"
                                             "unknown datatype for ~a.~a: \"~a\"")
                                         name (column-name c) (column-type c)))
                            ;; STRICT ANY converts nothing
                            (when (string= ty "ANY") (setf (column-affinity c) :blob))))
                 (loop for (c . rest) on (coerce cols 'list)
                       do (when (find (column-name c) rest :key #'column-name :test #'name=)
                            (sql-error "duplicate column name: ~a" (column-name c))))
                 (make-table :name name :root root :sql sql :columns cols
                           :without-rowid without-rowid :strict strict)))
           (pk-set nil) (uniques '()))
      (labels ((colidx (nm)
                 (or (position nm cols :key #'column-name :test #'name=)
                     (sql-error "no such column: ~a" nm)))
               (index-cols (items)
                 (loop for (e coll desc) in items
                       for nm = (or (expr-column-name e)
                                    (sql-error "expressions prohibited in PRIMARY KEY and UNIQUE constraints"))
                       for ci = (colidx nm)
                       collect (list ci (if coll (collation-keyword coll)
                                            (collate-of (aref cols ci)))
                                     desc))))
        ;; column constraints, in column order
        (loop for cd in columns
              for i from 0
              do (when (getf cd :primary-key)
                   (when pk-set (sql-error "table ~s has more than one primary key" name))
                   (setf pk-set (list (list i (collate-of (aref cols i))
                                            (eq (getf cd :primary-key) :desc)))
                         (table-pk-conflict tb) (getf cd :pk-conflict)
                         (table-autoincrement tb) (getf cd :autoincrement))
                   (push (list :pk pk-set (getf cd :pk-conflict)) uniques))
                 (when (getf cd :unique)
                   (push (list :unique (list (list i (collate-of (aref cols i)) nil))
                               (getf cd :unique-conflict))
                         uniques))
                 (dolist (ck (reverse (getf cd :checks)))
                   (push (cons (second ck) (first ck)) (table-checks tb)))
                 (let ((ref (getf cd :references)))
                   (when ref
                     (push (make-fkey :child-cols (list i) :parent (getf ref :table)
                                      :parent-cols (getf ref :columns)
                                      :on-delete (getf ref :on-delete) :on-update (getf ref :on-update)
                                      :deferred (getf ref :deferred))
                           (table-fkeys tb)))))
        (dolist (tc constraints)
          (case (car tc)
            (:primary-key
             (when pk-set (sql-error "table ~s has more than one primary key" name))
             (destructuring-bind (items conflict autoinc) (cdr tc)
               (setf pk-set (index-cols items)
                     (table-pk-conflict tb) conflict)
               (when autoinc (setf (table-autoincrement tb) t))
               (push (list :pk pk-set conflict) uniques)))
            (:unique
             (push (list :unique (index-cols (second tc)) (third tc)) uniques))
            (:check (push (cons (third tc) (second tc)) (table-checks tb)))
            (:foreign-key
             (destructuring-bind (child-names ref) (cdr tc)
               (push (make-fkey :child-cols (mapcar #'colidx child-names) :parent (getf ref :table)
                                :parent-cols (getf ref :columns)
                                :on-delete (getf ref :on-delete) :on-update (getf ref :on-update)
                                :deferred (getf ref :deferred))
                     (table-fkeys tb)))))))
      (setf (table-fkeys tb) (nreverse (table-fkeys tb)))
      (setf (table-checks tb) (nreverse (table-checks tb)))
      (setf (table-pk tb) (mapcar #'first pk-set)
            (table-pk-spec tb) pk-set)
      ;; INTEGER PRIMARY KEY (not DESC, exactly one column) aliases the rowid
      (when (and pk-set (null (cdr pk-set)) (not without-rowid))
        (let* ((ci (first (first pk-set)))
               (c (aref cols ci)))
          (when (and (string= (string-upcase-ascii (or (column-type c) "")) "INTEGER")
                     (not (eq (column-pk c) :desc)))
            (setf (table-rowid-alias tb) ci))))
      (when (and (table-autoincrement tb) (null (table-rowid-alias tb)))
        (sql-error "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"))
      (when (and without-rowid (null pk-set))
        (sql-error "PRIMARY KEY missing on table ~a" name))
      ;; implicit unique indexes, in declaration order, duplicates merged
      (let ((seen '()))
        (dolist (u (nreverse uniques))
          (destructuring-bind (kind cols conflict) u
            ;; a WITHOUT ROWID key has no b-tree of its own but takes its
            ;; place in the sqlite_autoindex_<table>_<N> numbering; a UNIQUE
            ;; on the same columns declared earlier becomes the key
            (cond ((and (eq kind :pk) (table-rowid-alias tb)))
                  ((member cols seen :test #'equal)
                   (when (and (eq kind :pk) without-rowid)
                     (setf (third (find cols (table-unique-constraints tb) :key #'first :test #'equal)) t)))
                  (t (push cols seen)
                     (push (list cols conflict (eq kind :pk)) (table-unique-constraints tb))))))
        (setf (table-unique-constraints tb) (nreverse (table-unique-constraints tb))))
      (when without-rowid
        ;; NOT NULL is implied for WITHOUT ROWID primary keys
        (dolist (ci (table-pk tb)) (setf (column-not-null (aref cols ci)) t)))
      tb)))

;;; ------------------------------------------------------------------
;;; Loading

(defun index-from-ast (ast root sql table)
  (destructuring-bind (&key name unique columns where &allow-other-keys) (cdr ast)
    (make-index :name name :table (table-name table) :root root :sql sql :unique unique
                :where where
                :columns (loop for (e coll desc) in columns
                               for nm = (expr-column-name e)
                               for ci = (and nm (find-column table nm))
                               collect (list (or ci
                                                 (if (and nm (rowid-name-p nm)) :rowid e))
                                             (cond (coll (collation-keyword coll))
                                                   (ci (collate-of (aref (table-columns table) ci)))
                                                   (t :binary))
                                             desc)))))

(defun load-schema (db)
  (let ((schema (make-schema))
        (rows '()))
    (setf (gethash "sqlite_schema" (schema-tables schema)) (make-schema-table)
          (gethash "sqlite_master" (schema-tables schema)) (gethash "sqlite_schema" (schema-tables schema)))
    (when (plusp (db-page-count db))
      (let ((*encoding* (db-encoding db)))
        (map-table db 1 (lambda (rowid payload)
                          (push (cons rowid (decode-record payload)) rows)))))
    ;; (a CREATE's placeholder row, not yet filled in, is not a schema entry)
    (setf rows (remove-if-not (lambda (r) (stringp (third r))) (nreverse rows))
          (schema-rows schema) rows)
    ;; tables and views first, then indexes and triggers
    (dolist (r rows)
      (destructuring-bind (rowid type name tbl root sql &rest ignore) r
        (declare (ignore rowid tbl ignore))
        (cond ((and (equal type "table") (stringp sql))
               (let ((ast (car (first (parse-sql sql)))))
                 (setf (gethash (schema-key name) (schema-tables schema))
                       (if (eq (car ast) :create-virtual)
                           (virtual-table-from-ast name ast sql schema)
                           (table-from-ast name ast root sql)))))
              ((and (equal type "view") (stringp sql))
               (let ((ast (car (first (parse-sql sql)))))
                 (setf (gethash (schema-key name) (schema-tables schema))
                       (make-table :name name :root 0 :sql sql
                                   :view-select (getf (cdr ast) :select)
                                   :view-columns (getf (cdr ast) :columns)
                                   :columns #())))))))
    ;; FTS4 tables that take their columns from their content= table
    (dolist (r rows)
      (destructuring-bind (rowid type name tbl root sql &rest ignore) r
        (declare (ignore rowid tbl root ignore))
        (when (and (equal type "table") (stringp sql))
          (let ((tb (gethash (schema-key name) (schema-tables schema))))
            (when (and tb (consp (table-vtab tb)) (eq (first (table-vtab tb)) :unknown)
                       (fts3-module-p (second (table-vtab tb))))
              (setf (gethash (schema-key name) (schema-tables schema))
                    (virtual-table-from-ast name (car (first (parse-sql sql))) sql schema)))))))
    (dolist (r rows)
      (destructuring-bind (rowid type name tbl root sql &rest ignore) r
        (declare (ignore rowid ignore))
        (let ((table (gethash (schema-key tbl) (schema-tables schema))))
          (cond ((and (equal type "index") table)
                 (let ((idx (if (stringp sql)
                                (index-from-ast (car (first (parse-sql sql))) root sql table)
                                (auto-index-for table name root))))
                   (when idx
                     (setf (gethash (schema-key name) (schema-indexes schema)) idx)
                     (setf (table-indexes table) (append (table-indexes table) (list idx))))))
                ((and (equal type "trigger") (stringp sql))
                 (setf (gethash (schema-key name) (schema-triggers schema))
                       (cons tbl (car (first (parse-sql sql))))))))))
    (maphash (lambda (k tb) (declare (ignore k)) (setf (table-owner tb) db))
             (schema-tables schema))
    ;; A WITHOUT ROWID table is its own primary-key index.
    (maphash (lambda (k tb) (declare (ignore k))
               (when (table-without-rowid tb)
                 (setf (table-indexes tb)
                       (cons (make-index :name (format nil "sqlite_autoindex_~a_~d" (table-name tb)
                                                       (1+ (position-if #'third (table-unique-constraints tb))))
                                         :table (table-name tb) :root (table-root tb)
                                         :unique t :auto t :pk-index t
                                         :conflict (table-pk-conflict tb)
                                         :columns (mapcar #'copy-list (table-pk-spec tb)))
                             (table-indexes tb)))))
             (schema-tables schema))
    schema))

(defun index-pk-tail (table index)
  "sqlite3CreateIndex, WITHOUT ROWID: the primary-key columns a secondary
INDEX stores after its own, as (column collation desc) -- each one that is
not already a key column with the same collation (isDupColumn).  A UNIQUE
constraint's index was made before the primary key, and takes its columns
ascending whatever their order (convertToWithoutRowidTable, bAscKeyBug)."
  (loop for (ci coll desc) in (table-pk-spec table)
        unless (find-if (lambda (k) (and (eql (first k) ci) (collation= (second k) coll)))
                        (index-columns index))
          collect (list ci coll (and desc (not (index-auto index))))))

(defun auto-index-for (table name root)
  "The index behind sqlite_autoindex_<table>_<N>."
  (let* ((prefix (format nil "sqlite_autoindex_~a_" (table-name table)))
         (n (and (> (length name) (length prefix))
                 (parse-integer name :start (length prefix) :junk-allowed t)))
         (u (and n (nth (1- n) (table-unique-constraints table)))))
    (when (and u (not (and (third u) (table-without-rowid table))))
      (destructuring-bind (cols conflict pk) u
        (declare (ignore pk))
        (make-index :name name :table (table-name table) :root root :unique t :auto t
                    :conflict conflict
                    :columns cols)))))

(defun db-schema* (db)
  (or (db-schema db)
      (setf (db-schema db) (load-schema db))))

(defun find-table-in (db name)
  "NAME in DB's own schema only."
  (gethash (schema-key name) (schema-tables (db-schema* db))))

(defun temp-first (dbs)
  (append (remove-if-not (lambda (x) (name= (db-name x) "temp")) dbs)
          (remove-if (lambda (x) (name= (db-name x) "temp")) dbs)))

(defun lookup-table (db name &optional (errorp t) schema)
  "Resolve a table name as SQLite does: in SCHEMA if given, else TEMP, then
main, then attached databases in order."
  (or (cond
        (schema (let ((d (schema-db db schema nil)))
                  (and d (if (member name '("sqlite_temp_master" "sqlite_temp_schema")
                                     :test #'name=)
                             (find-table-in d "sqlite_schema")
                             (find-table-in d name)))))
        ((member name '("sqlite_temp_master" "sqlite_temp_schema") :test #'name=)
         (find-table-in (temp-db db t) "sqlite_schema"))
        ((member name '("sqlite_master" "sqlite_schema") :test #'name=)
         (find-table-in (conn db) name))
        (t (loop for d in (temp-first (conn-dbs db))
                 thereis (find-table-in d name))))
      (and errorp (sql-error "no such table: ~@[~a.~]~a" schema name))))

(defun lookup-index (db name &optional schema)
  (loop for d in (if schema (list (schema-db db schema)) (temp-first (conn-dbs db)))
        thereis (gethash (schema-key name) (schema-indexes (db-schema* d)))))

(defun table-triggers (db table event timing)
  (let ((out '()))
    (maphash (lambda (k v) (declare (ignore k))
               (destructuring-bind (tbl . ast) v
                 (when (and (name= tbl (table-name table))
                            (eq (getf (cdr ast) :event) event)
                            (eq (getf (cdr ast) :timing) timing))
                   (push ast out))))
             (schema-triggers (db-schema* db)))
    out))
