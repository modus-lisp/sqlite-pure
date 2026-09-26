;;;; ddl.lisp — CREATE / DROP / ALTER, and maintenance of sqlite_schema.

(in-package #:sqlite-pure)

(defun schema-table () (lookup-table *db* "sqlite_schema"))

(defun bump-schema-cookie ()
  (set-header-u32 *db* +hdr-schema-cookie+ (1+ (header-u32 *db* +hdr-schema-cookie+)))
  (setf (db-schema *db*) nil))

(defun add-schema-row (type name tbl root sql)
  (let* ((st (schema-table))
         (rowid (1+ (or (table-max-rowid *db* 1) 0))))
    (table-insert *db* 1 rowid (encode-record (list type name tbl root (or sql :null))))
    rowid))

(defun schema-rows-where (pred)
  (remove-if-not pred (schema-rows (db-schema* *db*))))

(defun delete-schema-rows (pred)
  (dolist (r (schema-rows-where pred))
    (table-delete *db* 1 (first r))))

(defun rewrite-schema-row (r &key (type (second r)) (name (third r)) (tbl (fourth r))
                                  (root (fifth r)) (sql (sixth r)))
  (table-insert *db* 1 (first r) (encode-record (list type name tbl root (or sql :null)))))

(defun name-in-use-p (name)
  (let ((s (db-schema* *db*)))
    (or (gethash (schema-key name) (schema-tables s))
        (gethash (schema-key name) (schema-indexes s))
        (gethash (schema-key name) (schema-triggers s)))))

(defun check-new-name (name kind)
  (when (and (>= (length name) 7) (name= (subseq name 0 7) "sqlite_"))
    (sql-error "object name reserved for internal use: ~a" name))
  (when (name-in-use-p name)
    (sql-error "~a ~a already exists"
               (let ((s (db-schema* *db*)))
                 (cond ((gethash (schema-key name) (schema-indexes s)) "index")
                       ((gethash (schema-key name) (schema-triggers s)) "trigger")
                       ((table-view-select (gethash (schema-key name) (schema-tables s))) "view")
                       (t (string-downcase (string kind)))))
               name)))

;;; SQL text as SQLite stores it: "CREATE TABLE " + the text from the name on.

(defun stored-create-sql (text keyword)
  (let* ((toks (tokenize text))
         (i (position-if (lambda (tk) (kw-tok-p tk keyword)) toks)))
    (if (null i)
        text
        (let ((unique (loop for k below i thereis (kw-tok-p (aref toks k) "UNIQUE"))))
          (incf i)
          (when (kw-tok-p (aref toks i) "IF") (incf i 3))
          (format nil "CREATE ~:[~;UNIQUE ~]~a ~a" unique keyword
                  (subseq text (tok-pos (aref toks i))))))))

(defun quote-ident (name)
  (if (and (plusp (length name))
           (ident-start-p (char name 0))
           (every #'ident-char-p name)
           (not (reserved-p name)))
      name
      (format nil "\"~a\"" (substitute-string "\"" "\"\"" name))))

;;; ------------------------------------------------------------------
;;; CREATE TABLE

(defun create-table-from-ast (ast sql)
  (let* ((name (getf (cdr ast) :name))
         (tb (table-from-ast name ast 0 sql))
         (root (create-btree *db* (if (table-without-rowid tb) +leaf-index+ +leaf-table+))))
    (add-schema-row "table" name name root sql)
    (loop for u in (table-unique-constraints tb)
          for k from 1
          do (add-schema-row "index" (format nil "sqlite_autoindex_~a_~d" name k) name
                             (create-btree *db* +leaf-index+) nil))
    (when (and (table-autoincrement tb) (null (lookup-table *db* "sqlite_sequence" nil)))
      (let ((seq-sql "CREATE TABLE sqlite_sequence(name,seq)"))
        (add-schema-row "table" "sqlite_sequence" "sqlite_sequence"
                        (create-btree *db* +leaf-table+) seq-sql)))
    (bump-schema-cookie)))

(defun affinity-type-name (aff)
  (case aff (:integer "INT") (:real "REAL") (:numeric "NUM") (:text "TEXT") (t "")))

(defun exec-create-table (st text)
  (destructuring-bind (&key name temp if-not-exists as-select &allow-other-keys) (cdr st)
    (declare (ignore temp))
    (when (lookup-table *db* name nil)
      (if if-not-exists
          (return-from exec-create-table nil)
          (sql-error "table ~a already exists" name)))
    (check-new-name name :table)
    (if as-select
        (multiple-value-bind (fn cols) (compile-select as-select (make-scope))
          (let* ((rows (funcall fn nil))
                 (names (dedupe-names (mapcar #'first cols)))
                 ;; SQLite 3.40's layout: CREATE TABLE t(a INT,b TEXT,c)
                 (sql (format nil "CREATE TABLE ~a(~{~a~^,~})" (quote-ident name)
                              (loop for n in names
                                    for c in cols
                                    for ty = (affinity-type-name (second c))
                                    collect (format nil "~a~:[ ~a~;~*~]" (quote-ident n)
                                                    (string= ty "") ty)))))
            (create-table-from-ast (car (first (parse-sql sql))) sql)
            (let ((tb (lookup-table *db* name))
                  (ctx nil))
              (setf ctx (make-write-ctx :table tb))
              (dolist (r rows)
                (let ((row (make-array (1+ (length r)))))
                  (replace row r)
                  (setf (svref row (length r)) :null)
                  (apply-row-affinity tb row)
                  (finalize-rowid tb row)
                  (write-row tb row))))))
        (create-table-from-ast st (stored-create-sql text "TABLE")))
    nil))

(defun dedupe-names (names)
  (let ((seen '()))
    (loop for n in names
          collect (let ((cand n) (k 0))
                    (loop while (member cand seen :test #'name=)
                          do (setf cand (format nil "~a:~d" n (incf k))))
                    (push cand seen)
                    cand))))

;;; ------------------------------------------------------------------
;;; CREATE INDEX

(defun populate-index (table idx)
  (let ((*index-cmp* (index-full-cmp table idx))
        (unique-cmp (index-key-cmp (index-collations idx) (index-descs idx)))
        (seen (make-hash-table :test #'equal)))
    (declare (ignore unique-cmp))
    (map-table-rows table
                    (lambda (row)
                      (when (index-applies-p table idx row)
                        (let ((key (index-key table idx row)))
                          (when (index-unique idx)
                            (let ((prefix (subseq key 0 (length (index-columns idx)))))
                              (unless (member :null prefix)
                                (let ((k (group-key prefix (index-collations idx))))
                                  (when (gethash k seen)
                                    (constraint-error "UNIQUE constraint failed: ~a"
                                                      (constraint-columns-text table idx)))
                                  (setf (gethash k seen) t)))))
                          (index-insert *db* (index-root idx) key)))))))

(defun exec-create-index (st text)
  (destructuring-bind (&key name table if-not-exists &allow-other-keys) (cdr st)
    (when (lookup-index *db* name)
      (if if-not-exists
          (return-from exec-create-index nil)
          (sql-error "index ~a already exists" name)))
    (check-new-name name :index)
    (let ((tb (lookup-table *db* table)))
      (when (table-view-select tb) (sql-error "views may not be indexed"))
      (when (= (table-root tb) 1) (sql-error "table ~a may not be indexed" table))
      (let* ((sql (stored-create-sql text "INDEX"))
             (idx (index-from-ast st 0 sql tb)))
        (dolist (c (index-columns idx))
          (let ((e (first c)))
            (when (and (consp e) (eq (car e) :col))
              (sql-error "no such column: ~a" (third e)))))
        (setf (index-root idx) (create-btree *db* +leaf-index+))
        (populate-index tb idx)
        (add-schema-row "index" name (table-name tb) (index-root idx) sql)
        (bump-schema-cookie)))
    nil))

(defun exec-create-view (st text)
  (destructuring-bind (&key name if-not-exists select &allow-other-keys) (cdr st)
    (when (lookup-table *db* name nil)
      (if if-not-exists
          (return-from exec-create-view nil)
          (sql-error "view ~a already exists" name)))
    (check-new-name name :view)
    ;; validate the body now, as SQLite does
    (compile-select select (make-scope))
    (add-schema-row "view" name name 0 (stored-create-sql text "VIEW"))
    (bump-schema-cookie)
    nil))

(defun exec-create-trigger (st text)
  (destructuring-bind (&key name if-not-exists table &allow-other-keys) (cdr st)
    (when (gethash (schema-key name) (schema-triggers (db-schema* *db*)))
      (if if-not-exists
          (return-from exec-create-trigger nil)
          (sql-error "trigger ~a already exists" name)))
    (let ((tb (lookup-table *db* table)))
      (add-schema-row "trigger" name (table-name tb) 0 (stored-create-sql text "TRIGGER"))
      (bump-schema-cookie))
    nil))

;;; ------------------------------------------------------------------
;;; DROP

(defun exec-drop (st)
  (destructuring-bind (&key kind name if-exists) (cdr st)
    (ecase kind
      ((:table :view)
       (let ((tb (lookup-table *db* name nil)))
         (when (or (null tb) (if (eq kind :view)
                                 (null (table-view-select tb))
                                 (table-view-select tb)))
           (if (or if-exists (and tb nil))
               (return-from exec-drop nil)
               (if (and tb (eq kind :table))
                   (sql-error "use DROP VIEW to delete view ~a" name)
                   (if tb
                       (sql-error "use DROP TABLE to delete table ~a" name)
                       (sql-error "no such ~(~a~): ~a" kind name)))))
         (when (= (table-root tb) 1) (sql-error "table ~a may not be dropped" name))
         (when (and (eq kind :table) (name= name "sqlite_sequence"))
           (sql-error "table sqlite_sequence may not be dropped"))
         (unless (table-view-select tb)
           (dolist (idx (table-indexes tb))
             (unless (index-pk-index idx) (clear-btree *db* (index-root idx))))
           (clear-btree *db* (table-root tb))
           (when (and (table-autoincrement tb) (sequence-table))
             (let ((seq (sequence-table)))
               (dolist (row (scan-table-rows seq nil nil))
                 (when (and (stringp (svref row 0)) (name= (svref row 0) name))
                   (delete-row seq row))))))
         (delete-schema-rows (lambda (r) (and (stringp (fourth r)) (name= (fourth r) name))))
         (bump-schema-cookie)))
      (:index
       (let ((idx (lookup-index *db* name)))
         (unless idx
           (if if-exists (return-from exec-drop nil) (sql-error "no such index: ~a" name)))
         (when (index-auto idx)
           (sql-error "index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped"))
         (clear-btree *db* (index-root idx))
         (delete-schema-rows (lambda (r) (and (equal (second r) "index") (name= (third r) name))))
         (bump-schema-cookie)))
      (:trigger
       (unless (gethash (schema-key name) (schema-triggers (db-schema* *db*)))
         (if if-exists (return-from exec-drop nil) (sql-error "no such trigger: ~a" name)))
       (delete-schema-rows (lambda (r) (and (equal (second r) "trigger") (name= (third r) name))))
       (bump-schema-cookie)))
    nil))

;;; ------------------------------------------------------------------
;;; ALTER TABLE

(defun replace-token-text (sql pred new &optional always-quote)
  "Replace identifier tokens of SQL satisfying PRED with NEW (quoted)."
  (let ((toks (tokenize sql)) (out (make-string-output-stream)) (pos 0))
    (loop for tk across toks
          do (when (and (eq (tok-kind tk) :id) (funcall pred tk))
               (write-string sql out :start pos :end (tok-pos tk))
               (write-string (if always-quote
                                 (format nil "\"~a\"" (substitute-string "\"" "\"\"" new))
                                 (quote-ident new))
                             out)
               (setf pos (tok-end tk))))
    (write-string sql out :start pos)
    (get-output-stream-string out)))

(defun exec-alter (st)
  (destructuring-bind (&key table rename-to rename-column to add-column drop-column sql) (cdr st)
    (let ((tb (lookup-table *db* table)))
      (when (table-view-select tb) (sql-error "cannot alter view ~a" table))
      (when (and (>= (length table) 7) (name= (subseq table 0 7) "sqlite_"))
        (sql-error "table ~a may not be altered" table))
      (cond
        (rename-to
         (when (name-in-use-p rename-to)
           (unless (name= rename-to table)
             (sql-error "there is already another table or index with this name: ~a" rename-to)))
         (dolist (r (schema-rows (db-schema* *db*)))
           (when (and (stringp (fourth r)) (name= (fourth r) table))
             (let* ((type (second r))
                    (nm (third r))
                    (rsql (sixth r))
                    (new-name (cond ((equal type "table") rename-to)
                                    ((and (equal type "index")
                                          (let ((pre (format nil "sqlite_autoindex_~a_" table)))
                                            (and (> (length nm) (length pre))
                                                 (name= (subseq nm 0 (length pre)) pre))))
                                     (format nil "sqlite_autoindex_~a_~a" rename-to
                                             (subseq nm (+ 17 (length table)))))
                                    (t nm)))
                    (new-sql (when (stringp rsql)
                               (let ((seen-on (not (equal type "table"))) (done nil))
                                 (declare (ignorable seen-on))
                                 (replace-token-text
                                  rsql
                                  (lambda (tk)
                                    (and (name= (tok-value tk) table)
                                         (or (not (equal type "table")) (not done))
                                         (setf done t)))
                                  rename-to t)))))
               (rewrite-schema-row r :name new-name :tbl rename-to :sql new-sql))))
         (when (sequence-table)
           (let ((seq (sequence-table)))
             (dolist (row (scan-table-rows seq nil nil))
               (when (and (stringp (svref row 0)) (name= (svref row 0) table))
                 (let ((new (copy-seq row)))
                   (setf (svref new 0) rename-to)
                   (write-row seq new))))))
         (bump-schema-cookie))
        (add-column
         (when (find-column tb (getf add-column :name))
           (sql-error "duplicate column name: ~a" (getf add-column :name)))
         (when (getf add-column :primary-key) (sql-error "Cannot add a PRIMARY KEY column"))
         (when (getf add-column :unique) (sql-error "Cannot add a UNIQUE column"))
         (when (and (getf add-column :not-null)
                    (let ((d (getf add-column :default)))
                      (or (null d) (equal d '(:lit :null)))))
           (sql-error "Cannot add a NOT NULL column with default value NULL"))
         (let* ((r (find-if (lambda (r) (and (equal (second r) "table") (name= (third r) table)))
                            (schema-rows (db-schema* *db*))))
                (old (sixth r))
                (close (table-sql-close-paren old))
                (new (concatenate 'string
                                  (string-right-trim '(#\Space #\Tab #\Newline) (subseq old 0 close))
                                  ", " sql (subseq old close))))
           (rewrite-schema-row r :sql new))
         (bump-schema-cookie))
        (rename-column
         (let ((ci (or (find-column tb rename-column)
                       (sql-error "no such column: \"~a\"" rename-column))))
           (declare (ignore ci))
           (when (find-column tb to) (sql-error "duplicate column name: ~a" to))
           (dolist (r (schema-rows (db-schema* *db*)))
             (when (and (stringp (fourth r)) (name= (fourth r) table) (stringp (sixth r)))
               (rewrite-schema-row
                r :sql (replace-token-text (sixth r)
                                           (lambda (tk) (name= (tok-value tk) rename-column))
                                           to))))
           (bump-schema-cookie)))
        (drop-column
         (drop-column-impl tb drop-column))))
    nil))

(defun table-sql-close-paren (sql)
  "Offset of the parenthesis closing the column list of CREATE TABLE."
  (let ((depth 0))
    (loop for tk across (tokenize sql)
          do (when (eq (tok-kind tk) :op)
               (cond ((string= (tok-value tk) "(") (incf depth))
                     ((string= (tok-value tk) ")")
                      (decf depth)
                      (when (zerop depth) (return-from table-sql-close-paren (tok-pos tk)))))))
    (length sql)))

(defun drop-column-impl (tb name)
  (when (table-without-rowid tb)
    (sql-error "DROP COLUMN on WITHOUT ROWID tables is not supported"))
  (let* ((ci (or (find-column tb name) (sql-error "no such column: \"~a\"" name)))
         (col (aref (table-columns tb) ci)))
    (when (or (column-pk col) (member ci (table-pk tb)))
      (sql-error "cannot drop PRIMARY KEY column: \"~a\"" name))
    (when (column-unique col) (sql-error "cannot drop UNIQUE column: \"~a\"" name))
    (dolist (idx (table-indexes tb))
      (when (member ci (index-columns idx) :key #'first)
        (sql-error "error in index ~a after drop column: no such column: ~a" (index-name idx) name)))
    (when (<= (length (table-columns tb)) 1)
      (sql-error "cannot drop column \"~a\": no other columns exist" name))
    ;; Remove the column definition from the SQL text: the tokens from the
    ;; column's name to the next top-level comma (or the closing paren).
    (let* ((r (find-if (lambda (r) (and (equal (second r) "table") (name= (third r) (table-name tb))))
                       (schema-rows (db-schema* *db*))))
           (sql (sixth r))
           (toks (tokenize sql))
           (depth 0) (col-index -1) (start nil) (end nil) (prev-comma nil))
      (loop for k from 0 below (length toks)
            for tk = (aref toks k)
            do (cond ((and (eq (tok-kind tk) :op) (string= (tok-value tk) "("))
                      (incf depth)
                      (when (= depth 1) (setf col-index 0 start (tok-end tk) prev-comma (tok-pos tk))))
                     ((and (eq (tok-kind tk) :op) (string= (tok-value tk) ")"))
                      (when (and (= depth 1) (= col-index ci)) (setf end (tok-pos tk)) (return))
                      (decf depth))
                     ((and (= depth 1) (eq (tok-kind tk) :op) (string= (tok-value tk) ","))
                      (when (= col-index ci) (setf end (tok-pos tk)) (return))
                      (incf col-index)
                      (setf start (tok-end tk) prev-comma (tok-pos tk)))))
      (let ((new (if (= ci 0)
                     (concatenate 'string (subseq sql 0 start)
                                  (string-left-trim " " (subseq sql (min (length sql) (1+ end)))))
                     (concatenate 'string (subseq sql 0 prev-comma) (subseq sql end)))))
        ;; rewrite every row without the column
        (let ((rows (scan-table-rows tb nil nil)))
          (rewrite-schema-row r :sql new)
          (setf (db-schema *db*) nil)
          (let ((ntb (lookup-table *db* (table-name tb))))
            (dolist (row rows)
              (let ((nrow (concatenate 'vector (subseq row 0 ci) (subseq row (1+ ci)))))
                (table-insert *db* (table-root ntb) (svref nrow (1- (length nrow)))
                              (encode-record (table-record ntb nrow))))))))
      (bump-schema-cookie))))
