;;;; fts3.lisp — the FTS3 and FTS4 virtual tables: CREATE VIRTUAL TABLE t
;;;; USING fts3(...) / fts4(...), their reads and writes, special commands
;;;; ('optimize', 'rebuild', 'integrity-check', 'merge=', 'automerge='),
;;;; the functions snippet(), offsets(), matchinfo() and optimize(), and
;;;; the fts4aux and fts3tokenize tables.
;;;;
;;;; A table declares its columns, then three hidden ones: one named after
;;;; the table (the MATCH target and special-command column; it reads as
;;;; NULL but carries the cursor the auxiliary functions use), docid (the
;;;; rowid) and the language id.  Rows live in <t>_content (unless
;;;; content= names another table or is empty), sizes in <t>_docsize and
;;;; totals in <t>_stat (FTS4), the index in <t>_segments / <t>_segdir.
;;;;
;;;; Writes are buffered as SQLite buffers them: pending terms are written
;;;; out at the end of a transaction, when docids would go backwards, and
;;;; when a statement that SQLite gives a statement journal starts inside a
;;;; transaction, so the segments come out as SQLite's do.

(in-package #:sqlite-pure)

;;; ------------------------------------------------------------------
;;; CREATE VIRTUAL TABLE ... USING fts3/fts4(...)

(defun fts3-module-p (module)
  (member module '("fts3" "fts4") :test #'name=))

(defun fts3-special-column (arg)
  "fts3IsSpecialColumn: (values key value) if ARG has an '=', else NIL."
  (let ((p (position #\= arg)))
    (when p (values (subseq arg 0 p) (fts3-dequote (subseq arg (1+ p)))))))

(defun f3-content-columns (db content)
  "Column names of the content= table (DB is a database or, while the
schema loads, the schema)."
  (let ((tb (if (schema-p db)
                (gethash (schema-key content) (schema-tables db))
                (lookup-table db content nil))))
    (unless tb (sql-error "no such table: main.~a" content))
    (if (table-view-select tb)
        (if (schema-p db)
            (sql-error "no such table: main.~a" content)
            (let ((*db* db))
              (mapcar #'first (nth-value 1 (without-eqp
                                             (compile-select (second (car (first (parse-sql (format nil "SELECT * FROM ~a" (quote-ident content))))))
                                                             (make-scope)))))))
        (table-column-names tb))))

(defun fts3-spec (module name args db)
  "Parse fts3/fts4 arguments as fts3InitVtab does; returns an FTS3."
  (let* ((fts4 (char-equal (char module 3) #\4))
         (cols '()) (tokenize nil) (tokenizer-set nil)
         (no-docsize nil) (desc nil) (prefix nil) (compress nil) (uncompress nil)
         (content nil) (languageid nil) (notindexed '()))
    (dolist (z args)
      (cond
        ((and (not tokenizer-set) (> (length z) 8) (string-equal z "tokenize" :end1 8)
              (not (fts3-id-char-p (char-code (char z 8)))))
         (setf tokenize (subseq z 9) tokenizer-set t))
        ((and fts4 (position #\= z))
         (multiple-value-bind (key val) (fts3-special-column z)
           (let ((k (string-downcase-ascii key)))
             (cond ((string= k "matchinfo")
                    (unless (string-equal val "fts3") (sql-error "unrecognized matchinfo: ~a" val))
                    (setf no-docsize t))
                   ((string= k "prefix") (setf prefix val))
                   ((string= k "compress") (setf compress val))
                   ((string= k "uncompress") (setf uncompress val))
                   ((string= k "order")
                    (unless (or (string-equal val "asc") (string-equal val "desc"))
                      (sql-error "unrecognized order: ~a" val))
                    (setf desc (and (plusp (length val)) (char-equal (char val 0) #\d))))
                   ((string= k "content") (setf content val))
                   ((string= k "languageid") (setf languageid val))
                   ((string= k "notindexed") (setf notindexed (append notindexed (list val))))
                   (t (sql-error "unrecognized parameter: ~a" z))))))
        (t (push z cols))))
    (setf cols (nreverse cols))
    (when content
      (setf compress nil uncompress nil)
      (when (null cols)
        (progn
          (setf cols (f3-content-columns db content))
          (when languageid
            (let ((p (position languageid cols :test #'string-equal)))
              (when p (setf cols (append (subseq cols 0 p) (subseq cols (1+ p))))))))))
    (when (null cols) (setf cols (list "content")))
    (let* ((tokenizer (make-fts3-tokenizer-from tokenize))
           (prefixes (fts3-prefix-parameter prefix))
           (names (mapcar (lambda (c)
                            (multiple-value-bind (a b) (fts3-next-token c 0)
                              (if a (fts3-dequote (subseq c a b)) "")))
                          cols))
           (notidx (mapcar (lambda (n) (and (member n notindexed :test #'string-equal) t)) names)))
      (dolist (ni notindexed)
        (unless (member ni names :test #'string-equal)
          (sql-error "no such column: ~a" ni)))
      (when (and (null compress) uncompress) (sql-error "missing compress parameter in fts4 constructor"))
      (when (and compress (null uncompress)) (sql-error "missing uncompress parameter in fts4 constructor"))
      (make-fts3 :name name :module (string-downcase-ascii module) :fts4-p fts4
                 :columns names :notindexed notidx :tokenizer tokenizer
                 :content content :languageid languageid
                 :compress compress :uncompress uncompress :desc-p desc
                 :prefixes prefixes
                 :has-stat fts4 :has-docsize (and fts4 (not no-docsize))
                 :pending (coerce (loop repeat (length prefixes) collect (make-hash-table :test #'equal)) 'vector)))))

(defun fts3-prefix-parameter (param)
  "fts3PrefixParameter: a vector of prefix lengths, 0 first."
  (let ((out (list 0)))
    (when (and param (plusp (length param)))
      (let ((n (1+ (count #\, param))) (p 0))
        (dotimes (i n)
          (let ((start p) (v 0))
            (loop while (and (< p (length param)) (digit-char-p (char param p)))
                  do (setf v (+ (* v 10) (digit-char-p (char param p))))
                     (when (> v #x7fffffff) (sql-error "error parsing prefix parameter: ~a" param))
                     (incf p))
            (when (= p start) (sql-error "error parsing prefix parameter: ~a" param))
            (when (> v 10000000) (setf v 0))
            (unless (zerop v) (push v out))
            (incf p)))))
    (coerce (nreverse out) 'vector)))

(defun fts3-declaration (f)
  "The declared columns (SQLite's CREATE TABLE x('a', ..., 't' HIDDEN, docid
HIDDEN, '__langid' HIDDEN); the last three are marked hidden separately)."
  (format nil "CREATE TABLE x(~{~a, ~}~a, docid, ~a)"
          (mapcar #'quote-ident (f3-columns f))
          (quote-ident (f3-name f))
          (quote-ident (or (f3-languageid f) "__langid"))))

(defun sql-quote-string (s) (format nil "'~a'" (substitute-string "'" "''" s)))

(defun fts3-table-from-ast (name ast sql db)
  (destructuring-bind (&key module args &allow-other-keys) (cdr ast)
    (let* ((f (fts3-spec module name args db))
           (tb (table-from-ast name (car (first (parse-sql (fts3-declaration f)))) 0 sql))
           (n (length (f3-columns f))))
      (dotimes (i 3) (setf (column-hidden (aref (table-columns tb) (+ n i))) t))
      (setf (table-vtab tb) f)
      tb)))

(defun fts3-shadow-suffixes (f)
  (append (unless (f3-content f) '("content"))
          '("segments" "segdir")
          (when (f3-has-docsize f) '("docsize"))
          (when (or (f3-has-stat f) (and (f3-db f) (f3-shadow f "stat" nil))) '("stat"))))

(defun exec-create-fts3 (st)
  (destructuring-bind (&key name schema if-not-exists module args sql &allow-other-keys) (cdr st)
    (let ((*db* (ddl-target schema nil)))
      (when (find-table-in *db* name)
        (if if-not-exists
            (return-from exec-create-fts3 nil)
            (sql-error "table ~a already exists" name)))
      (check-new-name name :table)
      (let* ((f (fts3-spec module name args *db*))
             (q (substitute-string "'" "''" name)))
        (ensure-write-txn *db*)
        (add-table-schema-row "table" name name 0 (concatenate 'string "CREATE VIRTUAL TABLE " sql))
        (flet ((ddl (text) (create-table-from-ast (car (first (parse-sql text))) text)))
          (unless (f3-content f)
            (ddl (format nil "CREATE TABLE '~a_content'(docid INTEGER PRIMARY KEY~{, 'c~d~a'~}~@[, langid~])"
                         q (loop for c in (f3-columns f) for i from 0
                                 append (list i (substitute-string "'" "''" c)))
                         (f3-languageid f))))
          (ddl (format nil "CREATE TABLE '~a_segments'(blockid INTEGER PRIMARY KEY, block BLOB)" q))
          (ddl (format nil "CREATE TABLE '~a_segdir'(level INTEGER,idx INTEGER,start_block INTEGER,leaves_end_block INTEGER,end_block INTEGER,root BLOB,PRIMARY KEY(level, idx))" q))
          (when (f3-has-docsize f)
            (ddl (format nil "CREATE TABLE '~a_docsize'(docid INTEGER PRIMARY KEY, size BLOB)" q)))
          (when (f3-has-stat f)
            (ddl (format nil "CREATE TABLE '~a_stat'(id INTEGER PRIMARY KEY, value BLOB)" q))))
        (bump-schema-cookie)
        nil))))

(defun fts3-create-stat-table (f)
  (let ((*db* (f3-db f)))
    (unless (f3-shadow f "stat" nil)
      (let ((text (format nil "CREATE TABLE '~a_stat'(id INTEGER PRIMARY KEY, value BLOB)"
                          (substitute-string "'" "''" (f3-name f)))))
        (create-table-from-ast (car (first (parse-sql text))) text)
        (bump-schema-cookie)))
    (setf (f3-has-stat f) t)))

(defun fts3-of (table)
  "TABLE's FTS3 object, bound to the database it lives in."
  (let ((f (table-vtab table)))
    (setf (f3-db f) (table-owner table)
          (f3-pgsz f) (db-page-size (table-owner table))
          (f3-node-size f) (- (db-page-size (table-owner table)) 35))
    (unless (f3-fts4-p f)
      (setf (f3-has-stat f) (and (f3-shadow f "stat" nil) t)))
    f))

;;; ------------------------------------------------------------------
;;; Content

(defun f3-sql-rows (sql params)
  (let ((*params* (coerce params 'simple-vector)) (*param-names* nil) (*ctes* nil))
    (without-eqp
      (funcall (compile-select (second (car (first (parse-sql sql)))) (make-scope)) nil))))

(defun f3-external-select (f &optional where)
  (let ((db (f3-db f)))
    (format nil "SELECT rowid~{, ~a~}~@[, ~a~] FROM ~a.~a AS x~@[ ~a~]"
            (mapcar #'quote-ident (f3-columns f))
            (and (f3-languageid f) (quote-ident (f3-languageid f)))
            (quote-ident (db-name db)) (quote-ident (f3-content f)) where)))

(defun f3-apply-uncompress (f v)
  (if (and (f3-uncompress f) (not (eq v :null)))
      (call-sql-function (f3-uncompress f) (list v))
      v))

(defun call-sql-function (name args)
  (first (first (f3-sql-rows (format nil "SELECT ~a(~{?~*~^,~})" (quote-ident name) args) args))))

(defun f3-content-row-to (f row)
  "A %_content row vector -> (docid values langid)."
  (let ((n (f3-ncol f)))
    (list (svref row (1- (length row)))
          (loop for i from 1 to n
                collect (f3-apply-uncompress f (if (< i (1- (length row))) (svref row i) :null)))
          (if (f3-languageid f) (let ((v (svref row (1+ n)))) (if (integerp v) v (f3-int-of v))) 0))))

(defun f3-read-row (f docid)
  "(docid values langid) for DOCID, or NIL if there is no such row."
  (cond ((null (f3-content f))
         (let ((row (fetch-row (f3-shadow f "content") docid)))
           (and row (f3-content-row-to f row))))
        ((string= (f3-content f) "") (sql-error "SQL logic error"))
        (t (let ((r (first (f3-sql-rows (f3-external-select f "WHERE rowid = ?1") (list docid)))))
             (and r (list (f3-int-of (first r))
                          (subseq (rest r) 0 (f3-ncol f))
                          (if (f3-languageid f) (f3-int-of (nth (1+ (f3-ncol f)) r)) 0)))))))

(defun f3-map-content (f fn &key desc (lo nil) (hi nil))
  "Call FN with (docid values langid) for content rows in rowid order."
  (cond ((null (f3-content f))
         (let ((rows '()))
           (map-table-rows (f3-shadow f "content")
                           (lambda (row)
                             (let ((id (svref row (1- (length row)))))
                               (when (and (or (null lo) (>= id lo)) (or (null hi) (<= id hi)))
                                 (push (f3-content-row-to f (copy-seq row)) rows)))))
           (dolist (r (if desc rows (nreverse rows))) (funcall fn r))))
        ((string= (f3-content f) "") (sql-error "SQL logic error"))
        (t (dolist (r (f3-sql-rows (f3-external-select
                                    f (format nil "~aORDER BY rowid ~a"
                                              (if (or lo hi)
                                                  (format nil "WHERE rowid BETWEEN ~d AND ~d "
                                                          (or lo +fts3-smallest-int64+) (or hi +fts3-largest-int64+))
                                                  "")
                                              (if desc "DESC" "ASC")))
                                   '()))
             (funcall fn (list (f3-int-of (first r)) (subseq (rest r) 0 (f3-ncol f))
                               (if (f3-languageid f) (f3-int-of (nth (1+ (f3-ncol f)) r)) 0)))))))

(defun f3-map-content-unordered (f fn)
  "The content rows as SELECT %s returns them (rebuild, integrity-check)."
  (cond ((null (f3-content f)) (f3-map-content f fn))
        ((string= (f3-content f) "") (sql-error "SQL logic error"))
        (t (dolist (r (f3-sql-rows (f3-external-select f) '()))
             (funcall fn (list (f3-int-of (first r)) (subseq (rest r) 0 (f3-ncol f))
                               (if (f3-languageid f) (f3-int-of (nth (1+ (f3-ncol f)) r)) 0)))))))

(defun f3-cursor-load-row (cs)
  "The current row's content (fts3CursorSeek): (docid values langid)."
  (or (cs-row cs)
      (setf (cs-row cs)
            (let* ((f (cs-fts cs)) (r (f3-read-row f (cs-prev-id cs))))
              (or r
                  (if (null (f3-content f))
                      (corrupt "database disk image is malformed")
                      (list (cs-prev-id cs) (make-list (f3-ncol f) :initial-element :null) 0)))))))

;;; ------------------------------------------------------------------
;;; Transactions: when pending terms are written out

(defun f3-conn-state (db)
  "The connection's FTS3 transaction bookkeeping (a cons: serial . tables)."
  (let ((c (conn db)))
    (or (getf (db-vtab-state c) :fts3)
        (setf (getf (db-vtab-state c) :fts3) (list 0)))))

(defun f3-touch (f)
  "Note that F is written in the current transaction (xBegin)."
  (let ((st (f3-conn-state (f3-db f))))
    (unless (member f (cdr st))
      (push f (cdr st))
      (setf (f3-leaf-add f) 0))))

(defun f3-sync (f)
  "fts3SyncMethod: write out the pending terms; maybe merge."
  (let* ((*db* (f3-db f)) (c (conn *db*)) (last (db-last-insert-rowid c)))
    (f3-pending-flush f)
    (when (and (> (f3-leaf-add f) 4) (/= (f3-autoincrmerge f) 0) (/= (f3-autoincrmerge f) #xff))
      (let* ((mx (let ((m nil))
                   (dolist (r (f3-all-segdir-rows f) (or m 0))
                     (let ((l (svref r 0)))
                       (when (integerp l) (setf m (max (or m 0) (mod l 1024))))))))
             (a (* (f3-leaf-add f) mx)))
        (incf a (floor a 2))
        (when (> a 64) (f3-incrmerge f a (f3-autoincrmerge f)))))
    (setf (db-last-insert-rowid c) last)))

(defun fts3-sync-all (db)
  "Write out the pending terms of every FTS3 table written in the
transaction (xSync, xSavepoint)."
  (let ((st (f3-conn-state db)))
    (dolist (f (reverse (cdr st))) (f3-sync f))))

(defun fts3-end-transaction (db commit)
  (let ((st (f3-conn-state db)))
    (when commit (fts3-sync-all db))
    (unless commit (dolist (f (cdr st)) (f3-pending-clear f)))
    (setf (cdr st) nil)))

(defun fts3-rollback-to (db)
  (dolist (f (cdr (f3-conn-state db))) (f3-pending-clear f)))

(defun fts3-statement-journal-p (st)
  "Would SQLite open a statement journal for ST (so that, inside a
transaction, the virtual tables see xSavepoint)?  An approximation of
isMultiWrite && mayAbort."
  (flet ((vtab-p (name schema) (let ((tb (ignore-errors (lookup-table *db* name nil schema))))
                                 (and tb (table-vtab tb))))
         (constrained-p (name schema)
           (let ((tb (ignore-errors (lookup-table *db* name nil schema))))
             (and tb (or (some #'index-unique (table-indexes tb))
                         (some #'column-not-null (table-columns tb))
                         (table-checks tb)))))
         (rowid-eq-p (where)
           (and where (eq (car where) :binary) (eq (second where) :eq)
                (let ((cols (remove-if-not (lambda (x) (eq (car x) :col)) (list (third where) (fourth where)))))
                  (and (= (length cols) 1)
                       (let ((n (third (first cols))))
                         (and (stringp n) (or (rowid-name-p n) (name= n "docid")))))))))
    (case (car st)
      (:insert
       (destructuring-bind (&key table schema source &allow-other-keys) (cdr st)
         (let ((multi (and (sel-p source)
                           (not (let ((cores (sel-cores source)))
                                  (and (null (cdr cores)) (consp (first cores)) (eq (car (first cores)) :values)
                                       (null (cdr (second (first cores))))))))))
           (and multi (or (vtab-p table schema) (constrained-p table schema))))))
      ((:update :delete)
       (destructuring-bind (&key table schema where sets &allow-other-keys) (cdr st)
         (if (vtab-p table schema)
             (not (rowid-eq-p where))
             (and (eq (car st) :update)
                  (let ((tb (ignore-errors (lookup-table *db* table nil schema))))
                    (and tb (some (lambda (s)
                                    (let* ((cn (first s)) (ci (and (stringp cn) (find-column tb cn))))
                                      (or (and (stringp cn) (rowid-name-p cn))
                                          (and ci (let ((col (aref (table-columns tb) ci)))
                                                    (or (column-not-null col)
                                                        (some (lambda (ix) (and (index-unique ix)
                                                                                (member ci (index-columns ix))))
                                                              (table-indexes tb))))))))
                                  sets)))))))
      ((:create-table :create-index :create-view :create-trigger :create-virtual :drop :alter) t)
      (t nil))))

(defun fts3-statement-begin (db st)
  (when (and (db-explicit (conn db)) (cdr (f3-conn-state db))
             (let ((*db* db)) (fts3-statement-journal-p st)))
    (fts3-sync-all db)
    t))

(defun fts3-statement-end (db ok journal)
  "After a statement: outside a transaction, it was one (xSync or
xRollback); inside, a failed statement with a statement journal rolls
the pending terms back."
  (let ((c (conn db)))
    (cond ((not (db-explicit c)) (fts3-end-transaction db ok))
          ((and (not ok) journal) (fts3-rollback-to db)))))

;;; ------------------------------------------------------------------
;;; Writing (sqlite3Fts3UpdateMethod)

(defun f3-value-bytes (v)
  (cond ((eq v :null) 0)
        ((blobp v) (length v))
        (t (length (utf8-encode (value-to-text v))))))

(defun f3-value-int (v)
  "sqlite3_value_int64."
  (cond ((integerp v) v)
        ((eq v :null) 0)
        ((floatp v) (if (or (float-nan-p v) (float-infinity-p v)) 0 (max +fts3-smallest-int64+ (min +fts3-largest-int64+ (truncate v)))))
        (t (f3-int-of v))))

(defun f3-delete-all (f content-too)
  (f3-pending-clear f)
  (when (and content-too (null (f3-content f))) (f3-clear-table (f3-shadow f "content")))
  (f3-clear-table (f3-shadow f "segments"))
  (let ((tb (f3-shadow f "segdir")))
    (dolist (r (f3-all-segdir-rows f)) (delete-row tb r)))
  (when (f3-has-docsize f) (f3-clear-table (f3-shadow f "docsize")))
  (when (f3-has-stat f) (f3-clear-table (f3-shadow f "stat"))))

(defun f3-delete-terms (f rowid sz)
  "fts3DeleteTerms: queue the deletion of ROWID's terms; true if it exists."
  (let ((r (if (integerp rowid) (f3-read-row f rowid)
               (let ((id (rowid-probe rowid))) (and id (f3-read-row f id))))))
    (when r
      (destructuring-bind (docid values langid) r
        (f3-pending-terms-docid f t langid docid)
        (loop for v in values for i from 0 for notidx in (f3-notindexed f)
              do (unless notidx
                   (incf (aref sz i) (f3-pending-terms-add f langid (fts3-text-bytes v) -1))
                   (incf (aref sz (f3-ncol f)) (f3-value-bytes v)))))
      t)))

(defun f3-delete-by-rowid (f rowid nchng szdel)
  "fts3DeleteByRowid: returns the new change count."
  (if (f3-delete-terms f rowid szdel)
      (let ((empty (and (null (f3-content f))
                        (let ((id (rowid-probe rowid)) (other nil))
                          (map-table-rows (f3-shadow f "content")
                                          (lambda (row) (unless (eql (svref row (1- (length row))) id) (setf other t))))
                          (not other)))))
        (if empty
            (progn (f3-delete-all f t)
                   (fill szdel 0)
                   0)
            (let ((id (rowid-probe rowid)))
              (when (and (null (f3-content f)) id) (shadow-del (f3-shadow f "content") id))
              (when (and (f3-has-docsize f) id) (shadow-del (f3-shadow f "docsize") id))
              (1- nchng))))
      nchng))

(defun f3-insert-data (f ctx old-rowid new-rowid cols docid langid)
  "fts3InsertData: store the content row; returns the docid."
  (if (f3-content f)
      (let ((r (if (eq docid :null) new-rowid docid)))
        (unless (integerp r) (f3-constraint ctx))
        r)
      (let* ((tb (f3-shadow f "content"))
             (key (if (eq docid :null) new-rowid docid)))
        (unless (eq docid :null)
          (when (and (eq old-rowid :null) (not (eq new-rowid :null)))
            (sql-error "SQL logic error")))
        (let ((id (cond ((eq key :null) (new-rowid tb))
                        (t (let ((x (apply-affinity key :integer)))
                             (unless (integerp x)
                               (error 'sqlite-error :code :mismatch :message "datatype mismatch"))
                             x)))))
          (when (table-lookup (table-owner tb) (table-root tb) id)
            (f3-constraint ctx))
          (let ((row (make-array (+ 2 (f3-ncol f) (if (f3-languageid f) 1 0)))))
            (setf (svref row 0) :null)
            (loop for v in cols for i from 1
                  do (setf (svref row i)
                           (if (and (f3-compress f) (not (eq v :null)))
                               (call-sql-function (f3-compress f) (list v))
                               v)))
            (when (f3-languageid f) (setf (svref row (1+ (f3-ncol f))) (f3-value-int langid)))
            (setf (svref row (1- (length row))) id)
            (write-row tb row))
          id))))

(defun f3-constraint (ctx)
  (let ((action (resolve-action ctx nil)))
    (conflict-fail (if (eq action :replace) :abort action) "constraint failed")))

(defun fts3-update (ctx f old-rowid new-rowid cols tabcol docid langid)
  "sqlite3Fts3UpdateMethod: OLD-ROWID :null for an INSERT; COLS NIL for a DELETE."
  (let* ((n (f3-ncol f))
         (insert-p (and cols t)))
    (f3-touch f)
    (when (and insert-p (eq old-rowid :null) (not (eq tabcol :null)))
      (fts3-special-insert f tabcol)
      (return-from fts3-update :special))
    (when (and insert-p (< (f3-value-int langid) 0))
      (f3-constraint ctx))
    (let ((szdel (make-array (1+ n) :initial-element 0))
          (szins (make-array (1+ n) :initial-element 0))
          (nchng 0) (insert-done nil) (rowid nil))
      (when (and insert-p (null (f3-content f)))
        (let ((newid (if (eq docid :null) new-rowid docid)))
          (when (and (not (eq newid :null))
                     (or (eq old-rowid :null) (/= (f3-value-int old-rowid) (f3-value-int newid))))
            (if (eq (resolve-action ctx nil) :replace)
                (setf nchng (f3-delete-by-rowid f newid nchng szdel))
                (setf rowid (f3-insert-data f ctx old-rowid new-rowid cols docid langid) insert-done t)))))
      (unless (eq old-rowid :null)
        (setf nchng (f3-delete-by-rowid f old-rowid nchng szdel)))
      (when insert-p
        (let ((lid (f3-value-int langid)))
          (unless insert-done
            (setf rowid (f3-insert-data f ctx old-rowid new-rowid cols docid langid)))
          (f3-pending-terms-docid f nil lid rowid)
          (loop for v in cols for i from 0 for notidx in (f3-notindexed f)
                do (unless notidx
                     (incf (aref szins i) (f3-pending-terms-add f lid (fts3-text-bytes v) i))
                     (incf (aref szins n) (f3-value-bytes v))))
          (when (f3-has-docsize f) (f3-insert-docsize f rowid szins))
          (incf nchng)))
      (when (f3-fts4-p f) (f3-update-doc-totals f szins szdel nchng))
      rowid)))

(defmacro f3-ignoring (form)
  "SQLite drops a row whose xUpdate reports a constraint under OR IGNORE."
  `(handler-case ,form
     (sqlite-conflict (c) (if (eq (conflict-action c) :ignore) :ignored (error c)))))

(defun fts3-vtab-insert (ctx row)
  (let* ((tb (wc-table ctx)) (f (fts3-of tb)) (n (f3-ncol f))
         (rowid (let ((v (svref row (+ n 3))))
                  (if (eq v :null) :null (fts5-rowid-value v))))
         (id (f3-ignoring
              (fts3-update ctx f :null (or rowid :null) (loop for i below n collect (svref row i))
                           (svref row n) (svref row (+ n 1)) (svref row (+ n 2))))))
    (case id
      (:ignored nil)
      (:special                         ; xUpdate leaves the rowid 0
       (setf (db-last-insert-rowid (conn *db*)) 0)
       (incf (wc-changes ctx)))
      (t (setf (db-last-insert-rowid (conn *db*)) id)
         (incf (wc-changes ctx))
         ;; RETURNING sees the values as given (and rowid -1), as in SQLite
         (when (eq (svref row (+ n 3)) :null) (setf (svref row (+ n 3)) -1))
         (collect-returning ctx row)))
    t))

(defun fts3-vtab-update (ctx old new)
  (let* ((f (fts3-of (wc-table ctx))) (n (f3-ncol f))
         (newrow (let ((v (svref new (+ n 3)))) (if (eq v :null) :null (fts5-rowid-value v)))))
    (unless (eq :ignored (f3-ignoring (fts3-update ctx f (svref old (+ n 3)) newrow
                                                   (loop for i below n collect (svref new i))
                                                   (svref new n) (svref new (+ n 1)) (svref new (+ n 2)))))
      (incf (wc-changes ctx)))
    t))

(defun fts3-vtab-delete (table row)
  (let* ((f (fts3-of table)) (n (f3-ncol f))
         (ctx (make-write-ctx :table table)))
    (fts3-update ctx f (svref row (+ n 3)) :null nil :null :null :null)
    t))

;;; ------------------------------------------------------------------
;;; Special commands: INSERT INTO t(t) VALUES('...')

(defun fts3-special-insert (f v)
  (let* ((s (value-to-text v)) (n (length (utf8-encode s))))
    (cond
      ((and (= n 8) (string-equal s "optimize")) (f3-optimize f nil))
      ((and (= n 7) (string-equal s "rebuild")) (fts3-rebuild f))
      ((and (= n 15) (string-equal s "integrity-check"))
       (unless (fts3-integrity-ok-p f) (corrupt "database disk image is malformed")))
      ((and (> n 6) (string-equal s "merge=" :end1 6)) (fts3-do-incrmerge f (subseq s 6)))
      ((and (> n 10) (string-equal s "automerge=" :end1 10)) (fts3-do-automerge f (subseq s 10)))
      (t (sql-error "SQL logic error")))))

(defun fts3-rebuild (f)
  (f3-delete-all f nil)
  (let* ((n (f3-ncol f)) (ins (make-array (1+ n) :initial-element 0)) (nentry 0))
    (f3-map-content-unordered
     f (lambda (r)
         (destructuring-bind (docid values langid) r
           (let ((sz (make-array (1+ n) :initial-element 0)))
             (f3-pending-terms-docid f nil langid docid)
             (loop for v in values for i from 0 for notidx in (f3-notindexed f)
                   do (unless notidx
                        (incf (aref sz i) (f3-pending-terms-add f langid (fts3-text-bytes v) i))
                        (incf (aref sz n) (f3-value-bytes v))))
             (when (f3-has-docsize f) (f3-insert-docsize f (f3-prev-docid f) sz))
             (incf nentry)
             (dotimes (i (1+ n)) (incf (aref ins i) (aref sz i)))))))
    (when (f3-fts4-p f)
      (f3-update-doc-totals f ins (make-array (1+ n) :initial-element 0) nentry))))

(defun fts3-integrity-ok-p (f)
  (let ((ck1 0) (ck2 0))
    (dolist (langid (f3-all-langids f))
      (when (integerp langid)
        (dotimes (i (f3-nindex f))
          (setf ck1 (logxor ck1 (f3-checksum-index f langid i))))))
    (f3-map-content-unordered
     f (lambda (r)
         (destructuring-bind (docid values langid) r
           (loop for v in values for col from 0 for notidx in (f3-notindexed f)
                 do (unless notidx
                      (let ((b (fts3-text-bytes v)))
                        (when b
                          (loop for (term nil nil pos) across (fts3-tokenize (f3-tokenizer f) b)
                                do (setf ck2 (logxor ck2 (f3-checksum-entry term langid 0 docid col pos)))
                                   (loop for i from 1 below (f3-nindex f)
                                         for np = (aref (f3-prefixes f) i)
                                         do (when (<= np (length term))
                                              (setf ck2 (logxor ck2 (f3-checksum-entry (subseq term 0 np) langid i docid col pos)))))))))))))
    (= ck1 ck2)))

(defun fts3-do-incrmerge (f param)
  (multiple-value-bind (nmerge i) (f3-parse-getint param 0)
    (let ((nmin 8))
      (when (and (< i (length param)) (char= (char param i) #\,) (< (1+ i) (length param)))
        (multiple-value-setq (nmin i) (f3-parse-getint param (1+ i))))
      (when (or (< i (length param)) (< nmin 2)) (sql-error "SQL logic error"))
      (unless (f3-has-stat f) (fts3-create-stat-table f))
      (f3-incrmerge f nmerge nmin))))

(defun fts3-do-automerge (f param)
  (let ((v (f3-parse-getint param 0)))
    (when (or (= v 1) (> v +fts3-merge-count+)) (setf v 8))
    (setf (f3-autoincrmerge f) v)
    (unless (f3-has-stat f) (fts3-create-stat-table f))
    (f3-stat-put f 2 v)))

;;; ------------------------------------------------------------------
;;; Reading

(defun fts3-match-conjuncts (conjuncts li scope n)
  "(kind col-or-nil expr): kind :match (col NIL = the table column) or :langid."
  (let ((out '()))
    (flet ((colof (x)
             (multiple-value-bind (depth si ci)
                 (case (car x)
                   (:col (resolve-column scope (second x) (third x)))
                   (:srccol (values 0 (second x) (third x))))
               (and depth (= depth 0) (= si li) ci))))
      (dolist (c conjuncts (nreverse out))
        (cond ((and (eq (car c) :fn) (string= (second c) "match") (= (length (third c)) 2))
               (destructuring-bind (q x) (third c)
                 (let ((ci (colof x)))
                   (when (and (integerp ci) (<= ci n))
                     (push (list :match (if (= ci n) nil ci) q c) out)))))
              ((and (eq (car c) :binary) (eq (second c) :eq))
               (let ((a (colof (third c))) (b (colof (fourth c))))
                 (cond ((eql a (+ n 2)) (push (list :langid nil (fourth c)) out))
                       ((eql b (+ n 2)) (push (list :langid nil (third c)) out))))))))))

(defvar *fts3-cursor-counter* 0)

(defun fts3-open-query (f query col langid &key desc min max)
  "A cursor positioned on the first row matching QUERY (column COL, or NIL
for all), or at EOF."
  (let* ((expr (and query (f3-parse-query f query (or col (f3-ncol f)))))
         (cs (make-f3cursor :fts f :expr expr :langid langid :desc desc
                            :min-docid (or min +fts3-smallest-int64+)
                            :max-docid (or max +fts3-largest-int64+)
                            :id (incf *fts3-cursor-counter*))))
    (when expr (f3-eval-start cs))
    (f3-eval-next cs)
    cs))

(defun fts3-docid-bound (v default)
  (let ((x (if (eq v :null) v (apply-comparison-affinity v :numeric))))
    (if (integerp x) x default)))

(defun fts3-plan-access (fs li conjuncts scope)
  (let* ((table (fsrc-table fs))
         (src (fsrc-src fs))
         (n (- (length (table-columns table)) 3))
         (matches (fts3-match-conjuncts conjuncts li scope n))
         (m (car (last (remove :langid matches :key #'first))))
         (_ (dolist (x matches)
              ;; SQLite's xBestIndex takes the last MATCH; the others stay
              ;; calls of a function that does not exist
              (when (and (eq (first x) :match) (not (eq x m)))
                (setf (gethash (fourth x) *fts3-unusable-matches*) t))))
         (qfn (and m (compile-expr (third m) scope)))
         (qcol (and m (second m)))
         (langid-fn (let ((l (find :langid matches :key #'first))) (and l (compile-expr (third l) scope))))
         (rowid-eq (and (null m)
                        (find-if (lambda (c) (and (eq (fourth c) :eq) (member (first c) (list :rowid (1+ n)))))
                                 (equality-candidates conjuncts li scope))))
         (rowid-fn (and rowid-eq (compile-expr (second rowid-eq) scope)))
         (ranges (loop for c in conjuncts
                       append (fts3-docid-ranges c li scope n)))
         (ge (find-if (lambda (r) (member (first r) '(:gt :ge))) ranges))
         (le (find-if (lambda (r) (member (first r) '(:lt :le))) ranges))
         (ge-fn (and ge (compile-expr (second ge) scope)))
         (le-fn (and le (compile-expr (second le) scope)))
         ;; ORDER BY docid (alone): the cursor runs in that order (idxStr)
         (order (let ((h (and (= li 0) *order-hint*)))
                  (when (and h (eq (first h) :rowid))
                    (setf *order-satisfied* t)
                    (second h))))
         (idxnum (+ (cond (m (+ 2 (or qcol n))) (rowid-eq 1) (t 0))
                    (if (and m langid-fn) #x10000 0)
                    (if ge #x20000 0) (if le #x40000 0))))
    (declare (ignore _))
    (eqp-table-note (format nil "SCAN ~a VIRTUAL TABLE INDEX ~d:~@[~a~]" (src-name src) idxnum
                            (and order (if (eq order :desc) "DESC" "ASC"))))
    (lambda (env fn)
      (let* ((f (fts3-of table))
             (wanted (src-wanted src))
             (need-content (or (null wanted) (loop for i below n thereis (plusp (sbit wanted i)))
                               (and (f3-languageid f) (plusp (sbit wanted (+ n 2))))))
             (desc (if order (eq order :desc) (f3-desc-p f)))
             (lo (and ge-fn (fts3-docid-bound (funcall ge-fn env) nil)))
             (hi (and le-fn (fts3-docid-bound (funcall le-fn env) nil))))
        (flet ((emit (docid values langid cs)
                 (let ((row (make-array (+ n 4))))
                   (loop for v in values for i from 0 do (setf (svref row i) v))
                   (setf (svref row n) cs
                         (svref row (+ n 1)) docid
                         (svref row (+ n 2)) langid
                         (svref row (+ n 3)) docid)
                   (funcall fn row))))
          (cond
            (m
             (let* ((qv (funcall qfn env))
                    (lid (if langid-fn (f3-value-int (funcall langid-fn env)) 0))
                    (cs (fts3-open-query f (if (eq qv :null) nil (value-to-text qv)) qcol lid
                                         :desc desc :min lo :max hi)))
               (when (null (cs-expr cs)) (setf (cs-eof cs) t))
               (loop until (cs-eof cs)
                     do (let ((r (if need-content (f3-cursor-load-row cs)
                                     (list (cs-prev-id cs) (make-list n :initial-element :null) 0))))
                          (emit (cs-prev-id cs) (second r) (cs-langid cs) cs))
                        (f3-eval-next cs))))
            (rowid-fn
             (let ((id (rowid-probe (funcall rowid-fn env))))
               (when id
                 (let ((r (f3-read-row f id)))
                   (when r (emit id (second r) (third r)
                                 (make-f3cursor :fts f :prev-id id :row r)))))))
            (t
             (f3-map-content f (lambda (r)
                                 (emit (first r) (second r) (third r)
                                       (make-f3cursor :fts f :prev-id (first r) :row r)))
                             :desc desc :lo lo :hi hi))))))))

(defun fts3-docid-ranges (c li scope n)
  "(op expr) when C bounds this source's docid/rowid."
  (when (and (eq (car c) :binary) (member (second c) '(:lt :le :gt :ge)))
    (flet ((colp (x)
             (multiple-value-bind (depth si ci)
                 (case (car x)
                   (:col (resolve-column scope (second x) (third x)))
                   (:srccol (values 0 (second x) (third x))))
               (and depth (= depth 0) (= si li) (or (eq ci :rowid) (eql ci (1+ n)))))))
      (cond ((colp (third c)) (list (list (second c) (fourth c))))
            ((colp (fourth c)) (list (list (ecase (second c) (:lt :gt) (:le :ge) (:gt :lt) (:ge :le)) (third c))))))))

;;; MATCH as a filter: true when the row is among the query's matches
(defun fts3-column-target (x scope)
  "If X is an FTS3/4 table's column: (values table column-index depth src-index)."
  (when (eq (car x) :col)
    (multiple-value-bind (depth si ci s) (resolve-column scope (second x) (third x))
      (when (and depth s (src-table s) (fts3-p (table-vtab (src-table s))) (integerp ci))
        (values (src-table s) ci depth si)))))

(defvar *fts3-unusable-matches* (make-hash-table :test #'eq :weakness :key))

(defun compile-fts3-match (x q scope &optional e)
  (multiple-value-bind (table ci depth si) (fts3-column-target x scope)
    (when (and table e (gethash e *fts3-unusable-matches*))
      (return-from compile-fts3-match
        (lambda (env) (declare (ignore env))
          (sql-error "unable to use function MATCH in the requested context"))))
    (when table
      (let* ((n (- (length (table-columns table)) 3))
             (col (cond ((= ci n) nil) ((< ci n) ci)
                        (t (sql-error "unable to use function MATCH in the requested context"))))
             (rowid-fn (compile-column-access depth si :rowid))
             (langid-fn (compile-column-access depth si (+ n 2)))
             (qf (compile-expr q scope))
             (cache nil))
        (lambda (env)
          (let* ((qv (funcall qf env))
                 (key (list (if (eq qv :null) nil (value-to-text qv)) col
                            (f3-value-int (funcall langid-fn env)))))
            (unless (equal (car cache) key)
              (let* ((f (fts3-of table))
                     (cs (fts3-open-query f (first key) col (third key)))
                     (h (make-hash-table)))
                (when (cs-expr cs)
                  (loop until (cs-eof cs) do (setf (gethash (cs-prev-id cs) h) t) (f3-eval-next cs)))
                (setf cache (cons key h))))
            (if (gethash (funcall rowid-fn env) (cdr cache)) 1 0)))))))

(defun compile-fts3-hidden-column (e scope)
  "The table-named column of an FTS3/4 table reads as NULL."
  (multiple-value-bind (table ci) (fts3-column-target e scope)
    (when (and table (= ci (- (length (table-columns table)) 3)))
      (lambda (env) (declare (ignore env)) :null))))

(defun compile-fts3-function (name args scope)
  "snippet/offsets/matchinfo/optimize whose first argument is an FTS3/4
table's table-named column: (lambda (env)) reading the cursor, or NIL."
  (when (and args (member name '("snippet" "offsets" "matchinfo" "optimize") :test #'string=))
    (multiple-value-bind (table ci depth si) (fts3-column-target (first args) scope)
      (when (and table (= ci (- (length (table-columns table)) 3)))
        (let ((cfn (compile-column-access depth si ci))
              (afns (mapcar (lambda (a) (compile-expr a scope)) (rest args))))
          (cond
            ((string= name "snippet")
             (when (> (length args) 6) (sql-error "wrong number of arguments to function snippet()")))
            ((string= name "matchinfo")
             (unless (<= 1 (length args) 2) (sql-error "wrong number of arguments to function matchinfo()")))
            (t (unless (= (length args) 1) (sql-error "wrong number of arguments to function ~a()" name))))
          (lambda (env)
            (fts3-call-function name (funcall cfn env) (mapcar (lambda (a) (funcall a env)) afns))))))))

(defun fts3-call-function (name cs args)
  (unless (f3cursor-p cs) (sql-error "illegal first argument to ~a" name))
  (let ((*db* (f3-db (cs-fts cs))))
    (flet ((text (v) (if (eq v :null) nil (value-to-text v))))
      (cond
        ((string= name "snippet")
         (let ((start (if (>= (length args) 1) (text (first args)) "<b>"))
               (end (if (>= (length args) 2) (text (second args)) "</b>"))
               (ell (if (>= (length args) 3) (text (third args)) "<b>...</b>"))
               (col (if (>= (length args) 4) (f3-value-int (fourth args)) -1))
               (ntok (if (>= (length args) 5) (f3-value-int (fifth args)) 15)))
           (cond ((or (null start) (null end) (null ell)) (sql-error "out of memory"))
                 ((zerop ntok) "")
                 (t (let ((col (ldb (byte 32 0) col)) (ntok (ldb (byte 32 0) ntok)))
                      (f3-snippet cs start end ell
                                  (if (logbitp 31 col) (- col (expt 2 32)) col)
                                  (if (logbitp 31 ntok) (- ntok (expt 2 32)) ntok)))))))
        ((string= name "offsets") (f3-offsets cs))
        ((string= name "matchinfo")
         (f3-matchinfo cs (if args (or (text (first args)) "") "pcx")))
        (t (if (f3-optimize (cs-fts cs) t) "Index already optimal" "Index optimized"))))))

;;; ------------------------------------------------------------------
;;; fts4aux: CREATE VIRTUAL TABLE a USING fts4aux([db,] fts-table)

(defstruct (fts4aux (:conc-name faux-)) schema table)

(defun fts4aux-spec (args)
  (let ((n (length args)))
    (cond ((= n 1) (make-fts4aux :table (fts3-dequote (first args))))
          ((and (= n 2) (string-equal (first args) "temp"))
           (make-fts4aux :schema (second args) :table (fts3-dequote (second args))))
          (t (sql-error "invalid arguments to fts4aux constructor")))))

(defun fts4aux-table-from-ast (name ast sql)
  (destructuring-bind (&key args &allow-other-keys) (cdr ast)
    (let* ((v (fts4aux-spec args))
           (tb (table-from-ast name (car (first (parse-sql "CREATE TABLE x(term, col, documents, occurrences, languageid HIDDEN)")))
                               0 sql)))
      (setf (column-hidden (aref (table-columns tb) 4)) t)
      (setf (table-vtab tb) v)
      tb)))

(defun fts4aux-plan-access (fs li conjuncts scope)
  (let* ((table (fsrc-table fs)) (v (table-vtab table))
         (eqs (equality-candidates conjuncts li scope))
         (term-eq (find-if (lambda (c) (and (eql (first c) 0) (eq (fourth c) :eq))) eqs))
         (lang-eq (find-if (lambda (c) (and (eql (first c) 4) (eq (fourth c) :eq))) eqs))
         (ranges (loop for c in conjuncts
                       when (and (eq (car c) :binary) (member (second c) '(:lt :le :gt :ge)))
                         append (multiple-value-bind (depth si ci)
                                    (and (eq (car (third c)) :col) (resolve-column scope (second (third c)) (third (third c))))
                                  (when (and depth (= depth 0) (= si li) (eql ci 0))
                                    (list (list (second c) (fourth c)))))))
         (ge (and (not term-eq) (find-if (lambda (r) (member (first r) '(:gt :ge))) ranges)))
         (le (and (not term-eq) (find-if (lambda (r) (member (first r) '(:lt :le))) ranges)))
         (eq-fn (and term-eq (compile-expr (second term-eq) scope)))
         (ge-fn (and ge (compile-expr (second ge) scope)))
         (le-fn (and le (compile-expr (second le) scope)))
         (lang-fn (and lang-eq (compile-expr (second lang-eq) scope))))
    (eqp-table-note (format nil "SCAN ~a VIRTUAL TABLE INDEX ~d:" (src-name (fsrc-src fs))
                            (if term-eq 1 (+ (if ge 2 0) (if le 4 0)))))
    (lambda (env fn)
      (let* ((db (if (faux-schema v) (schema-db (table-owner table) (faux-schema v)) (table-owner table)))
             (target (find-table-in db (faux-table v))))
        (unless (and target (fts3-p (table-vtab target)))
          (sql-error "SQL logic error"))
        (let* ((f (fts3-of target))
               (langid (if lang-fn (max 0 (f3-value-int (funcall lang-fn env))) 0))
               (start (let ((x (cond (eq-fn (funcall eq-fn env)) (ge-fn (funcall ge-fn env)))))
                        (and x (not (eq x :null)) (text-to-bstring (value-to-text x)))))
               (stop (and le-fn (let ((x (funcall le-fn env))) (text-to-bstring (if (eq x :null) "" (value-to-text x))))))
               (scan (not eq-fn))
               (saved-pending (f3-pending f)) (saved-desc (f3-desc-p f)))
          ;; fts4aux reads the segments with a table object of its own: no
          ;; pending terms, and doclists read as ascending
          (setf (f3-pending f) (coerce (loop repeat (f3-nindex f) collect (make-hash-table :test #'equal)) 'vector)
                (f3-desc-p f) nil)
          (unwind-protect
               (let* ((m (f3-seg-reader-cursor f langid 0 :all start nil scan))
                      (rowid 0))
                 (f3-msr-start-filter f m (logior +f3f-require-pos+ +f3f-ignore-empty+ (if scan +f3f-scan+ 0)) start 0)
                 (loop while (f3-msr-step f m)
                       do (let ((term (msr-term m)))
                            (when (and stop
                                       (let* ((n (min (length stop) (length term)))
                                              (mc (loop for i below n
                                                        for a = (char-code (char stop i)) for b = (char-code (char term i))
                                                        unless (= a b) return (if (< a b) -1 1)
                                                        finally (return 0))))
                                         (or (< mc 0) (and (= mc 0) (> (length term) (length stop))))))
                              (return))
                            (let ((stats (fts4aux-stats (msr-doclist-buf m) (msr-doclist-off m) (msr-ndoclist m)))
                                  (tt (utf8-decode-lenient (bstring-to-bytes term))))
                              (loop for (ndoc . nocc) across stats
                                    for i from 0
                                    do (when (or (zerop i) (plusp ndoc))
                                         (let ((row (make-array 6)))
                                           (setf (svref row 0) tt
                                                 (svref row 1) (if (zerop i) "*" (1- i))
                                                 (svref row 2) ndoc (svref row 3) nocc
                                                 (svref row 4) langid (svref row 5) (incf rowid))
                                           (funcall fn row))))))))
            (setf (f3-pending f) saved-pending (f3-desc-p f) saved-desc)))))))

(defun fts4aux-stats (buf off n)
  "fts3auxNextMethod's counting: vector of (ndoc . nocc), index 0 for '*'."
  (let ((stats (make-array 2 :adjustable t :initial-contents (list (cons 0 0) (cons 0 0))))
        (i off) (end (+ off n)) (state 0) (col 0))
    (flet ((grow (k) (loop while (< (length stats) k) do (vector-push-extend (cons 0 0) stats))))
      (setf stats (make-array 2 :adjustable t :fill-pointer 2 :initial-contents (list (cons 0 0) (cons 0 0))))
      (loop while (< i end)
            do (multiple-value-bind (v o) (f3-get-varint buf i)
                 (setf i o)
                 (case state
                   (0 (incf (car (aref stats 0))) (setf state 1 col 0))
                   (1 (when (> v 1) (incf (car (aref stats 1))))
                      (setf state 2)
                      (cond ((= v 0) (setf state 0))
                            ((= v 1) (setf state 3))
                            (t (incf (cdr (aref stats (1+ col)))) (incf (cdr (aref stats 0))))))
                   (2 (cond ((= v 0) (setf state 0))
                            ((= v 1) (setf state 3))
                            (t (incf (cdr (aref stats (1+ col)))) (incf (cdr (aref stats 0))))))
                   (t (setf col v)
                      (when (< col 1) (corrupt "database disk image is malformed"))
                      (grow (+ col 2))
                      (incf (car (aref stats (1+ col))))
                      (setf state 2))))))
    stats))

;;; ------------------------------------------------------------------
;;; fts3tokenize: CREATE VIRTUAL TABLE t USING fts3tokenize(tokenizer, arg...)

(defstruct (fts3tok (:conc-name ftok-)) tokenizer)

(defun fts3tok-spec (args)
  (let ((words (mapcar #'fts3-dequote args)))
    (make-fts3tok
     :tokenizer (if words
                    (let ((name (first words)))
                      (unless (or (member name '("simple" "porter" "unicode61") :test #'string=)
                                  (user-tokenizer-function name nil))
                        (sql-error "unknown tokenizer: ~a" name))
                      (make-fts3-tokenizer-from
                       (format nil "~a~{ ~a~}" name (mapcar (lambda (a) (format nil "\"~a\"" (substitute-string "\"" "\"\"" a)))
                                                          (rest words)))))
                    (make-fts3-tokenizer-from nil)))))

(defun fts3tok-table-from-ast (name ast sql)
  (destructuring-bind (&key args &allow-other-keys) (cdr ast)
    (let ((tb (table-from-ast name (car (first (parse-sql "CREATE TABLE x(input, token, start, end, position)"))) 0 sql)))
      (setf (table-vtab tb) (fts3tok-spec args))
      tb)))

(defun fts3tok-plan-access (fs li conjuncts scope)
  (let* ((v (table-vtab (fsrc-table fs)))
         (input (find-if (lambda (c) (and (eql (first c) 0) (eq (fourth c) :eq)))
                         (equality-candidates conjuncts li scope)))
         (ifn (and input (compile-expr (second input) scope))))
    (eqp-table-note (format nil "SCAN ~a VIRTUAL TABLE INDEX ~d:" (src-name (fsrc-src fs)) (if input 1 0)))
    (lambda (env fn)
      (unless ifn (sql-error "SQL logic error"))     ; xFilter without an input
      (progn
        (let ((x (funcall ifn env)))
          (unless (eq x :null)
            (let ((text (value-to-text x)) (rowid 0))
              (loop for (term start end pos) across (fts3-tokenize (ftok-tokenizer v) (utf8-encode text))
                    do (funcall fn (vector text (utf8-decode-lenient (bstring-to-bytes term))
                                           start end pos (incf rowid)))))))))))

;;; The functions FTS3 overloads, called on anything but an FTS3/4 table
(defsqlfun "offsets" (1 1) (args)
  (declare (ignore args))
  (sql-error "unable to use function offsets in the requested context"))
(defsqlfun "matchinfo" (1 2) (args)
  (declare (ignore args))
  (sql-error "unable to use function matchinfo in the requested context"))
(defsqlfun "optimize" (1 1) (args)
  (declare (ignore args))
  (sql-error "unable to use function optimize in the requested context"))
