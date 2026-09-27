;;;; fts5.lisp — the FTS5 virtual table: CREATE VIRTUAL TABLE t USING
;;;; fts5(...), its reads and writes, special commands, and the auxiliary
;;;; functions bm25(), highlight() and snippet().
;;;;
;;;; Besides its declared columns the table has two hidden ones: one named
;;;; after the table (MATCH target, command column for special INSERTs, and
;;;; the handle auxiliary functions take) and "rank".  Its data lives in
;;;; <t>_data and <t>_idx (the index, fts5-index.lisp), <t>_content (the row
;;;; values; absent for content='' and external content tables),
;;;; <t>_docsize (tokens per column per row; absent with columnsize=0) and
;;;; <t>_config.

(in-package #:sqlite-pure)

;;; ------------------------------------------------------------------
;;; CREATE VIRTUAL TABLE ... USING fts5(...)

(defun fts5-dequote (s)
  (let ((s (string-trim '(#\Space #\Tab #\Newline #\Return) s)))
    (if (and (>= (length s) 2) (member (char s 0) '(#\' #\" #\` #\[)))
        (let ((close (if (char= (char s 0) #\[) #\] (char s 0))) (out (make-string-output-stream)))
          (loop for i from 1 below (1- (length s))
                do (let ((c (char s i)))
                     (write-char c out)
                     (when (and (char= c close) (char/= close #\]) (< (1+ i) (1- (length s)))
                                (char= (char s (1+ i)) close))
                       (incf i))))
          (get-output-stream-string out))
        s)))

(defun fts5-top-level-equals (arg)
  "Position of an '=' outside quotes in ARG, or NIL."
  (let ((q nil))
    (loop for i below (length arg)
          for c = (char arg i)
          do (cond (q (when (char= c q) (setf q nil)))
                   ((member c '(#\' #\" #\`)) (setf q c))
                   ((char= c #\[) (setf q #\]))
                   ((char= c #\=) (return i))))))

(defun fts5-spec (name args)
  "Parse fts5(...) arguments as sqlite3Fts5ConfigParse; returns an FTS5."
  (let ((fts (make-fts5 :name name)) (cols '()) (unindexed '()) (prefixes '()) (tokenize nil))
    (dolist (arg args)
      (let ((eq (fts5-top-level-equals arg)))
        (if eq
            (let ((k (string-downcase-ascii (fts5-dequote (subseq arg 0 eq))))
                  (v (fts5-dequote (subseq arg (1+ eq)))))
              (cond
                ((string= k "prefix")
                 (let ((parts (remove "" (split-on (substitute #\Space #\, v) #\Space) :test #'string=)))
                   (when (null parts) (sql-error "malformed prefix=... directive"))
                   (dolist (p parts)
                     (unless (every #'digit-char-p p) (sql-error "malformed prefix=... directive"))
                     (let ((n (parse-integer p)))
                       (unless (<= 1 n 999) (sql-error "prefix length out of range (max 999)"))
                       (setf prefixes (append prefixes (list n)))))))
                ((string= k "tokenize") (setf tokenize v))
                ((string= k "content")
                 (setf (fts-content fts) (if (string= v "") :none v)))
                ((string= k "content_rowid") (setf (fts-content-rowid fts) v))
                ((string= k "columnsize")
                 (cond ((string= v "0") (setf (fts-columnsize fts) nil))
                       ((string= v "1") (setf (fts-columnsize fts) t))
                       (t (sql-error "malformed columnsize=... directive"))))
                ((string= k "detail")
                 (setf (fts-detail fts)
                       (cond ((string-equal v "full") :full)
                             ((string-equal v "column") :column)
                             ((string-equal v "none") :none)
                             (t (sql-error "malformed detail=... directive")))))
                (t (sql-error "unrecognized option: \"~a\"" k))))
            (let* ((words (fts5-split-words arg))
                   (cname (if (member (char (string-trim " " arg) 0) '(#\' #\" #\` #\[))
                              (first words) (first words))))
              (when (or (string-equal cname "rank") (string-equal cname "rowid"))
                (sql-error "reserved fts5 column name: ~a" cname))
              (when (member cname cols :test #'string-equal)
                (sql-error "vtable constructor failed: ~a" name))
              (let ((unidx nil))
                (dolist (opt (rest words))
                  (if (string-equal opt "unindexed")
                      (setf unidx t)
                      (sql-error "unrecognized column option: ~a" opt)))
                (push cname cols) (push unidx unindexed))))))
    (when (null cols) (sql-error "vtable constructor failed: ~a" name))
    (setf (fts-columns fts) (nreverse cols)
          (fts-unindexed fts) (nreverse unindexed)
          (fts-prefixes fts) prefixes
          (fts-tokenize-spec fts) tokenize
          (fts-tokenizer fts) (make-fts5-tokenizer-from (and tokenize (fts5-split-words tokenize))))
    fts))

(defun split-on (s ch)
  (loop with start = 0
        for i = (position ch s :start start)
        collect (subseq s start i)
        while i do (setf start (1+ i))))

(defun fts5-declaration (fts)
  (format nil "CREATE TABLE x(~{~a~^,~}, ~a HIDDEN, rank HIDDEN)"
          (mapcar #'quote-ident (fts-columns fts)) (quote-ident (fts-name fts))))

(defun fts5-table-from-ast (name ast sql)
  (destructuring-bind (&key args &allow-other-keys) (cdr ast)
    (let* ((fts (fts5-spec name args))
           (tb (table-from-ast name (car (first (parse-sql
                                                  (format nil "CREATE TABLE x(~{~a~^,~},~a,rank)"
                                                          (mapcar #'quote-ident (fts-columns fts))
                                                          (quote-ident name)))))
                               0 sql))
           (n (length (fts-columns fts))))
      (setf (column-hidden (aref (table-columns tb) n)) t
            (column-hidden (aref (table-columns tb) (1+ n))) t
            (table-vtab tb) fts)
      tb)))

(defun fts5-shadow-suffixes (fts)
  (append '("data" "idx")
          (when (eq (fts-content fts) :normal) '("content"))
          (when (fts-columnsize fts) '("docsize"))
          '("config")))

(defun exec-create-fts5 (st)
  (destructuring-bind (&key name schema if-not-exists args sql &allow-other-keys) (cdr st)
    (let ((*db* (ddl-target schema nil)))
      (when (find-table-in *db* name)
        (if if-not-exists
            (return-from exec-create-fts5 nil)
            (sql-error "table ~a already exists" name)))
      (check-new-name name :table)
      (let* ((fts (fts5-spec name args))
             (q (substitute-string "'" "''" name)))
        (ensure-write-txn *db*)
        (add-schema-row "table" name name 0 (concatenate 'string "CREATE VIRTUAL TABLE " sql))
        (dolist (suffix (fts5-shadow-suffixes fts))
          (let ((ddl (cond
                       ((string= suffix "data") (format nil "CREATE TABLE '~a_data'(id INTEGER PRIMARY KEY, block BLOB)" q))
                       ((string= suffix "idx") (format nil "CREATE TABLE '~a_idx'(segid, term, pgno, PRIMARY KEY(segid, term)) WITHOUT ROWID" q))
                       ((string= suffix "content")
                        (format nil "CREATE TABLE '~a_content'(id INTEGER PRIMARY KEY~{, c~d~})" q
                                (loop for i below (length (fts-columns fts)) collect i)))
                       ((string= suffix "docsize") (format nil "CREATE TABLE '~a_docsize'(id INTEGER PRIMARY KEY, sz BLOB)" q))
                       (t (format nil "CREATE TABLE '~a_config'(k PRIMARY KEY, v) WITHOUT ROWID" q)))))
            (create-table-from-ast (car (first (parse-sql ddl))) ddl)))
        (bump-schema-cookie)
        (let* ((tb (find-table-in *db* name)) (f (fts5-of tb)))
          (fts-data-put f +fts5-averages-id+ (make-octets 0))
          (fts-data-put f +fts5-structure-id+ (make-octets 7))
          (let* ((ctb (fts-shadow f "config"))
                 (*index-cmp* (index-full-cmp ctb (find-if #'index-pk-index (table-indexes ctb)))))
            (index-insert (table-owner ctb) (table-root ctb) (list "version" 4))))
        nil))))

(defun fts5-of (table)
  "TABLE's FTS5 object, bound to the database it lives in."
  (let ((f (table-vtab table)))
    (setf (fts-db f) (table-owner table))
    (fts-load-config f)
    f))

;;; ------------------------------------------------------------------
;;; Rows: content, docsize

(defun fts5-row-values (fts rowid)
  "The row's column values, or NIL if there is no such row."
  (let ((n (length (fts-columns fts))))
    (case (fts-content fts)
      (:normal (let ((r (shadow-get (fts-shadow fts "content") rowid)))
                 (and r (subseq (append r (make-list n :initial-element :null)) 0 n))))
      (:none (make-list n :initial-element :null))
      (t (let* ((ext (lookup-table (fts-db fts) (fts-content fts) t))
                (row (fts5-external-row ext fts rowid)))
           (and row (mapcar (lambda (c) (let ((ci (find-column ext c)))
                                          (if ci (svref row ci) (sql-error "no such column: ~a" c))))
                            (fts-columns fts))))))))

(defun fts5-external-row (ext fts rowid)
  (let ((rc (fts-content-rowid fts)))
    (if (or (rowid-name-p rc) (eql (find-column ext rc) (table-rowid-alias ext)))
        (fetch-row ext rowid)
        (let ((ci (or (find-column ext rc) (sql-error "no such column: ~a" rc))) (hit nil))
          (map-table-rows ext (lambda (row) (when (eql (svref row ci) rowid) (setf hit row))))
          hit))))

(defun fts5-docsize (fts rowid)
  "Tokens per column of ROWID (a vector)."
  (let ((n (length (fts-columns fts))))
    (if (fts-columnsize fts)
        (let ((r (shadow-get (fts-shadow fts "docsize") rowid))
              (v (make-array n :initial-element 0)))
          (when (and r (blobp (first r)))
            (let ((b (first r)) (off 0))
              (dotimes (i n)
                (when (< off (length b))
                  (multiple-value-bind (x o) (read-fts-varint b off) (setf (aref v i) x off o))))))
          v)
        (let ((vals (fts5-row-values fts rowid)))
          (coerce (loop for v in vals for i from 0
                        collect (if (nth i (fts-unindexed fts)) 0 (length (fts5-tokenize-value fts v))))
                  'vector)))))

(defun fts5-tokenize-value (fts v)
  (if (eq v :null) #() (fts5-tokenize (fts-tokenizer fts) (value-to-text v))))

(defun fts5-index-row (fts rowid values delete-p)
  "Write (or, with DELETE-P, delete) ROWID's tokens.  Returns token counts."
  (fts-begin-write fts delete-p rowid)
  (coerce
   (loop for v in values
         for col from 0
         for unidx in (fts-unindexed fts)
         collect (if unidx
                     0
                     (let ((toks (fts5-tokenize-value fts v)))
                       (loop for tk across toks
                             for pos from 0
                             do (fts-pending-write fts rowid col pos (first tk) delete-p))
                       (length toks))))
   'vector))

(defvar *fts5-touched* nil "FTS5 tables written by the current statement.")

(defun fts5-touch (fts)
  (fts-ensure-totals fts)
  (pushnew fts *fts5-touched*))

(defun fts5-insert-row (fts rowid values)
  (fts5-touch fts)
  (when (eq (fts-content fts) :normal)
    (shadow-put (fts-shadow fts "content") rowid values))
  (let ((sizes (fts5-index-row fts rowid values nil)))
    (when (fts-columnsize fts)
      (let ((b (new-buf))) (loop for x across sizes do (buf-varint b x))
        (shadow-put (fts-shadow fts "docsize") rowid (list (coerce b '(simple-array (unsigned-byte 8) (*)))))))
    (let ((tt (fts-totals fts)))
      (incf (car tt))
      (loop for x across sizes for i from 0 do (incf (aref (cdr tt) i) x)))))

(defun fts5-delete-row (fts rowid &optional values)
  "Remove ROWID; VALUES are its old column values (read from the content
when not given).  True if the row existed."
  (fts5-touch fts)
  (let ((vals (or values (fts5-row-values fts rowid))))
    (when vals
      (let ((sizes (fts5-index-row fts rowid vals t)))
        (when (fts-columnsize fts) (shadow-del (fts-shadow fts "docsize") rowid))
        (when (eq (fts-content fts) :normal) (shadow-del (fts-shadow fts "content") rowid))
        (let ((tt (fts-totals fts)))
          (decf (car tt))
          (loop for x across sizes for i from 0 do (decf (aref (cdr tt) i) x))))
      t)))

(defun fts5-row-exists-p (fts rowid)
  (case (fts-content fts)
    (:normal (and (shadow-get (fts-shadow fts "content") rowid) t))
    (t (and (fts-columnsize fts) (shadow-get (fts-shadow fts "docsize") rowid) t))))

(defun fts5-new-rowid (fts)
  (let ((tb (fts-shadow fts (if (eq (fts-content fts) :normal) "content"
                                (if (fts-columnsize fts) "docsize" "data")))))
    (1+ (or (and (not (string= (table-name tb) (format nil "~a_data" (fts-name fts))))
                 (table-max-rowid (table-owner tb) (table-root tb)))
            0))))

(defun fts5-flush-touched ()
  (dolist (f *fts5-touched*)
    (let ((*db* (fts-db f)))
      (fts-flush f)
      (setf (fts-totals f) nil (fts-config-loaded f) nil))))

(defun fts5-discard-touched ()
  (dolist (f *fts5-touched*)
    (clrhash (fts-pending f))
    (setf (fts-pending-rowid f) nil (fts-pending-bytes f) 0 (fts-totals f) nil (fts-config-loaded f) nil)))

;;; ------------------------------------------------------------------
;;; INSERT / UPDATE / DELETE

(defun fts5-rowid-value (v)
  (cond ((eq v :null) nil)
        ((integerp v) v)
        (t (let ((x (apply-affinity v :integer)))
             (if (integerp x) x (error 'sqlite-error :code :mismatch :message "datatype mismatch"))))))

(defun fts5-vtab-insert (ctx row)
  (let* ((tb (wc-table ctx))
         (fts (fts5-of tb))
         (n (length (fts-columns fts)))
         (cmd (svref row n)))
    (if (not (eq cmd :null))
        (fts5-special-command fts (value-to-text cmd) (svref row (1+ n)) row)
        (let* ((values (loop for i below n collect (svref row i)))
               (rowid (fts5-rowid-value (svref row (+ n 2)))))
          (when (and rowid (fts5-row-exists-p fts rowid))
            ;; FTS5 honours OR REPLACE only
            (case (resolve-action ctx nil)
              (:replace (fts5-delete-row fts rowid))
              (:ignore (conflict-fail :abort "constraint failed"))
              (t (conflict-fail (resolve-action ctx nil) "constraint failed"))))
          (let ((rowid (or rowid (fts5-new-rowid fts))))
            (fts5-insert-row fts rowid values)
            (setf (db-last-insert-rowid (conn *db*)) rowid)
            (incf (wc-changes ctx))
            (setf (svref row (+ n 2)) rowid)
            (collect-returning ctx row)
            t)))))

(defun fts5-vtab-delete (table row)
  (let* ((fts (fts5-of table)) (n (length (fts-columns fts))))
    (when (eq (fts-content fts) :none)
      (sql-error "cannot DELETE from contentless fts5 table: ~a" (fts-name fts)))
    (fts5-delete-row fts (svref row (+ n 2)))))

(defun fts5-vtab-update (ctx old new)
  (let* ((fts (fts5-of (wc-table ctx))) (n (length (fts-columns fts))))
    (when (eq (fts-content fts) :none)
      (sql-error "cannot UPDATE contentless fts5 table: ~a" (fts-name fts)))
    (let ((orowid (svref old (+ n 2)))
          (nrowid (fts5-rowid-value (svref new (+ n 2)))))
      (when (and nrowid (/= nrowid orowid) (fts5-row-exists-p fts nrowid))
        (case (resolve-action ctx nil)
          (:replace (fts5-delete-row fts nrowid))
          (:ignore (conflict-fail :abort "constraint failed"))
          (t (conflict-fail (resolve-action ctx nil) "constraint failed"))))
      (fts5-delete-row fts orowid)
      (fts5-insert-row fts (or nrowid orowid) (loop for i below n collect (svref new i)))
      (incf (wc-changes ctx))
      t)))

(defun fts5-special-command (fts cmd arg row)
  (let ((c (string-downcase-ascii cmd)) (n (length (fts-columns fts))))
    (fts5-touch fts)
    (cond
      ((string= c "delete")
       (when (eq (fts-content fts) :normal)
         (sql-error "SQL logic error"))
       (let ((rowid (fts5-rowid-value (svref row (+ n 2)))))
         (when rowid
           (fts5-delete-row fts rowid (loop for i below n collect (svref row i))))))
      ((string= c "delete-all")
       (when (eq (fts-content fts) :normal)
         (sql-error "'delete-all' may only be used with a contentless or external content fts5 table"))
       (fts5-clear-index fts))
      ((string= c "rebuild")
       (when (eq (fts-content fts) :none)
         (sql-error "'rebuild' may not be used with a contentless fts5 table"))
       (fts5-clear-index fts)
       (fts5-map-content fts (lambda (rowid values) (fts5-insert-index-only fts rowid values))))
      ((string= c "optimize") (fts-optimize fts))
      ((string= c "integrity-check") (fts5-integrity-check fts))
      ((string= c "merge")
       (fts-flush fts)
       (let* ((k (value-to-integer arg))
              (nmin (if (and (integerp k) (< k 0)) 2 (fts-usermerge fts)))
              (s (fts-read-structure fts)))
         (loop (let ((best nil) (bestn 0))
                 (loop for i below (fst-nlevel s)
                       do (let ((c (length (cdr (fst-level s i)))))
                            (when (or (plusp (car (fst-level s i))) (> c bestn)) (setf best i bestn c))))
                 (unless (and best (or (plusp (car (fst-level s best))) (>= bestn nmin))) (return))
                 (fts-merge-level fts s best)
                 (fts-promote s (1+ best))))
         (fts-write-structure fts s)))
      ((member c '("automerge" "crisismerge" "usermerge" "pgsz" "rank" "hashsize") :test #'string=)
       (fts-set-config fts c arg))
      (t (sql-error "SQL logic error")))
    t))

(defun fts5-insert-index-only (fts rowid values)
  "Index a content row (rebuild): index, docsize and totals, not content."
  (let ((sizes (fts5-index-row fts rowid values nil)))
    (when (fts-columnsize fts)
      (let ((b (new-buf))) (loop for x across sizes do (buf-varint b x))
        (shadow-put (fts-shadow fts "docsize") rowid (list (coerce b '(simple-array (unsigned-byte 8) (*)))))))
    (let ((tt (fts-totals fts)))
      (incf (car tt))
      (loop for x across sizes for i from 0 do (incf (aref (cdr tt) i) x)))))

(defun fts5-clear-index (fts)
  (clrhash (fts-pending fts))
  (setf (fts-pending-rowid fts) nil)
  (dolist (g (fst-segments (fts-read-structure fts)))
    (fts-remove-segment fts (fseg-id g)))
  (let ((s (make-fstruct)))
    (fts-write-structure fts s))
  (when (fts-columnsize fts)
    (let ((tb (fts-shadow fts "docsize")) (ids '()))
      (map-table (table-owner tb) (table-root tb) (lambda (r p) (declare (ignore p)) (push r ids)))
      (dolist (r ids) (shadow-del tb r))))
  (setf (fts-totals fts) (cons 0 (make-array (length (fts-columns fts)) :initial-element 0))))

(defun fts5-map-content (fts fn)
  "Call FN with (rowid values) for each content row, in rowid order."
  (case (fts-content fts)
    (:normal (let ((tb (fts-shadow fts "content")) (n (length (fts-columns fts))))
               (map-table-rows tb (lambda (row)
                                    (funcall fn (svref row (length (table-columns tb)))
                                             (loop for i from 1 to n collect (svref row i)))))))
    (:none nil)
    (t (let* ((ext (lookup-table (fts-db fts) (fts-content fts) t))
              (rc (fts-content-rowid fts))
              (rci (if (rowid-name-p rc) :rowid (or (find-column ext rc) (sql-error "no such column: ~a" rc))))
              (cis (mapcar (lambda (c) (or (find-column ext c) (sql-error "no such column: ~a" c))) (fts-columns fts)))
              (rows '()))
         (map-table-rows ext (lambda (row) (push row rows)))
         (dolist (row (sort rows #'< :key (lambda (r) (if (eq rci :rowid) (svref r (length (table-columns ext))) (svref r rci)))))
           (funcall fn (if (eq rci :rowid) (svref row (length (table-columns ext))) (svref row rci))
                    (mapcar (lambda (ci) (svref row ci)) cis)))))))

(defun fts5-integrity-check (fts)
  "Compare the index (and docsize, totals) with what the content implies."
  (fts-flush fts)
  (let ((expected (make-hash-table :test #'equal))
        (nrow 0)
        (totals (make-array (length (fts-columns fts)) :initial-element 0))
        (bad nil))
    (when (eq (fts-content fts) :normal)
      (fts5-map-content
       fts
       (lambda (rowid values)
         (incf nrow)
         (loop for v in values for col from 0 for unidx in (fts-unindexed fts)
               do (unless unidx
                    (let ((toks (fts5-tokenize-value fts v)))
                      (incf (aref totals col) (length toks))
                      (loop for tk across toks for pos from 0
                            do (flet ((note (key)
                                        (push (+ (ash col 32) pos) (gethash (cons key rowid) expected))))
                                 (note (fts-term-key #\0 (first tk)))
                                 (loop for n in (fts-prefixes fts) for i from 1
                                       do (let ((k (prefix-key i (first tk) n))) (when k (note k)))))))))
         (when (fts-columnsize fts)
           (let ((ds (fts5-docsize fts rowid)))
             (loop for v in values for col from 0 for unidx in (fts-unindexed fts)
                   do (unless (= (aref ds col) (if unidx 0 (length (fts5-tokenize-value fts v))))
                        (setf bad t)))))))
      ;; every indexed (term, row) must be expected, with the same positions
      (let ((s (fts-read-structure fts)) (seen 0) (all-keys (make-hash-table :test #'equal)))
        (maphash (lambda (k v) (declare (ignore v)) (setf (gethash (car k) all-keys) t)) expected)
        (dolist (seg (fst-segments s))
          (sr-scan (make-segr :fts fts :seg seg)
                   (lambda (term parts) (declare (ignore parts)) (setf (gethash term all-keys) t) nil)))
        (loop for key being the hash-keys of all-keys
              do (dolist (e (fts-term-entries fts key s))
                   (let ((want (gethash (cons key (car e)) expected)))
                     (incf seen)
                     (cond ((null want) (setf bad t))
                           ((eq (fts-detail fts) :full)
                            (unless (equal (decode-positions fts (cdr e)) (sort (remove-duplicates want) #'<))
                              (setf bad t)))))))
        (unless (= seen (hash-table-count expected)) (setf bad t)))
      (let ((tt (fts-read-totals fts)))
        (unless (and (= (car tt) nrow) (equalp (cdr tt) totals)) (setf bad t))))
    (when bad (error 'sqlite-corrupt-error :message "database disk image is malformed"))))

;;; ------------------------------------------------------------------
;;; Reading

(defstruct (fts5-row (:conc-name frow-))
  fts rowid values result)

(defvar *fts5-cursors* (make-hash-table) "Cursor number -> FTS5-ROW, for auxiliary functions.")
(defvar *fts5-cursor-counter* 0)

(defun fts5-register-row (info)
  (let ((id (incf *fts5-cursor-counter*)))
    (setf (gethash id *fts5-cursors*) info)
    id))

(defun fts5-match-conjuncts (conjuncts li scope n)
  "MATCH-ing conjuncts on source LI: list of (kind column-or-nil expr-ast):
kind :match (the table or a column) or :rank."
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
                   (when (integerp ci)
                     (cond ((= ci n) (push (list :match nil q) out))
                           ((= ci (1+ n)) (push (list :rank nil q) out))
                           ((< ci n) (push (list :match ci q) out)))))))
              ((and (eq (car c) :binary) (eq (second c) :eq))
               (let ((a (colof (third c))) (b (colof (fourth c))))
                 (cond ((eql a n) (push (list :match nil (fourth c)) out))
                       ((eql b n) (push (list :match nil (third c)) out))))))))))

(defun fts5-query-result (fts queries)
  "Evaluate QUERIES (list of (text colset)), ANDed."
  (fts-flush fts)
  (let ((trees '()) (phr '()) (s (fts-read-structure fts)))
    (dolist (q queries)
      (multiple-value-bind (tree phrases) (fts5-parse-query fts (first q) (second q))
        (push tree trees)
        (setf phr (append phr (coerce phrases 'list)))))
    (let* ((phrases (coerce phr 'vector))
           (tree (reduce (lambda (a b) (fq-combine :and a b)) (nreverse trees))))
      ;; renumber phrases across queries
      (loop for p across phrases for i from 0 do (setf (fph-index p) i))
      (fts5-check-detail fts tree)
      (let ((r (fts5-evaluate fts tree phrases s)))
        (setf (fres-tree r) tree)
        r))))

(defun fts5-plan-access (fs li conjuncts scope)
  (let* ((table (fsrc-table fs))
         (src (fsrc-src fs))
         (n (- (length (table-columns table)) 2))
         (matches (fts5-match-conjuncts conjuncts li scope n))
         (tvf (fsrc-vtab-args fs))
         (qfns (append (mapcar (lambda (a) (list nil (compile-expr a scope))) (and tvf (list (first tvf))))
                       (loop for (kind col q) in matches
                             when (eq kind :match) collect (list col (compile-expr q scope)))))
         (rank-fn (let ((r (or (and tvf (second tvf))
                               (third (find :rank matches :key #'first)))))
                    (and r (compile-expr r scope))))
         (rowid-eq (find-if (lambda (c) (and (eq (fourth c) :eq) (member (first c) '(:rowid))))
                            (equality-candidates conjuncts li scope)))
         (rowid-fn (and rowid-eq (compile-expr (second rowid-eq) scope))))
    (eqp-table-note (format nil "SCAN ~a VIRTUAL TABLE INDEX 0:~@[M~]" (src-name src) (and qfns t)))
    (lambda (env fn)
     (block fts5-iterate
      (let* ((fts (fts5-of table))
             (wanted (src-wanted src))
             (want-rank (or (null wanted) (plusp (sbit wanted (1+ n)))))
             (only (and rowid-fn (rowid-probe (funcall rowid-fn env))))
             (result (and qfns
                          (fts5-query-result
                           fts (mapcar (lambda (q)
                                         (let ((v (funcall (second q) env)))
                                           (list (if (eq v :null) "" (value-to-text v))
                                                 (and (first q) (list (first q))))))
                                       qfns))))
             (rank-spec (let ((r (and rank-fn (funcall rank-fn env))))
                          (if (and r (not (eq r :null)))
                              (or (parse-rank-spec (value-to-text r))
                                  (sql-error "parse error in rank function: ~a" (value-to-text r)))
                              (parse-rank-spec (or (fts-rank fts) "bm25()"))))))
        (when (and rowid-fn (null only)) (return-from fts5-iterate nil))
        (flet ((emit (rowid values)
                 (let* ((info (make-fts5-row :fts fts :rowid rowid :values values :result result))
                        (row (make-array (+ n 3))))
                   (loop for v in values for i from 0 do (setf (svref row i) v))
                   (setf (svref row n) (fts5-register-row info)
                         (svref row (1+ n)) (if (and result want-rank) (fts5-rank info rank-spec) :null)
                         (svref row (+ n 2)) rowid)
                   (funcall fn row))))
          (cond
            (result
             (dolist (rowid (fres-rowids result))
               (when (or (null only) (= rowid only))
                 (let ((vals (fts5-row-values fts rowid)))
                   (when vals (emit rowid vals))))))
            (only (let ((vals (fts5-row-values fts only)))
                    (when (and vals (or (not (eq (fts-content fts) :none)) (fts5-row-exists-p fts only)))
                      (emit only vals))))
            ((eq (fts-content fts) :none)
             (when (fts-columnsize fts)
               (let ((tb (fts-shadow fts "docsize")) (nn (length (fts-columns fts))))
                 (map-table (table-owner tb) (table-root tb)
                            (lambda (r p) (declare (ignore p))
                              (emit r (make-list nn :initial-element :null)))))))
            (t (fts5-map-content fts #'emit)))))))))

;;; MATCH as a filter: true when the row is among the query's matches
(defun compile-fts5-match (x q scope)
  "X MATCH Q where X is an FTS5 table's column: (lambda (env)) or NIL."
  (multiple-value-bind (depth si ci s)
      (case (car x)
        (:col (resolve-column scope (second x) (third x)))
        (t nil))
    (when (and depth s (src-table s) (fts5-p (table-vtab (src-table s))) (integerp ci))
      (let* ((table (src-table s))
             (n (- (length (table-columns table)) 2))
             (col (cond ((= ci n) nil) ((< ci n) ci) (t (return-from compile-fts5-match
                                                            (lambda (env) (declare (ignore env)) 1)))))
             (rowid-fn (compile-column-access depth si :rowid))
             (qf (compile-expr q scope))
             (cache nil))
        (lambda (env)
          (let* ((qv (funcall qf env))
                 (key (list (if (eq qv :null) "" (value-to-text qv)) (and col (list col)))))
            (unless (equal (car cache) key)
              (let ((r (fts5-query-result (fts5-of table) (list key))))
                (setf cache (cons key (let ((h (make-hash-table)))
                                        (dolist (id (fres-rowids r) h) (setf (gethash id h) t)))))))
            (if (gethash (funcall rowid-fn env) (cdr cache)) 1 0)))))))

;;; ------------------------------------------------------------------
;;; rank and bm25

(defun parse-rank-spec (text)
  "'fn(arg, ...)' -> (name . literal-args), or NIL if malformed."
  (ignore-errors
   (let* ((p (position #\( text))
          (name (string-trim " " (subseq text 0 p)))
          (inner (subseq text (1+ p) (position #\) text :from-end t))))
     (when (and (plusp (length name)) (every (lambda (c) (or (alphanumericp c) (char= c #\_))) name))
       (cons (string-downcase-ascii name)
             (if (string= (string-trim " " inner) "")
                 '()
                 (first (let ((*db* (%make-db))) (query-rows-of (format nil "SELECT ~a" inner))))))))))

(defun query-rows-of (sql)
  (multiple-value-bind (fn) (compile-select (second (car (first (parse-sql sql)))) (make-scope))
    (funcall fn nil)))

(defun fts5-rank (info spec)
  (let ((name (car spec)) (args (cdr spec)))
    (cond ((string= name "bm25") (fts5-bm25 info args))
          (t (sql-error "no such function: ~a" name)))))

(defstruct (fts5-idf (:conc-name fidf-)) idf avgdl)

(defun fts5-result-idf (info)
  (let* ((r (frow-result info)) (fts (frow-fts info)))
    (or (getf (fres-cache r) :idf)
        (let* ((tt (fts-read-totals fts))
               (nrow (car tt))
               (ntok (reduce #'+ (cdr tt)))
               (s (fts-read-structure fts))
               (idf (map 'vector
                         (lambda (p)
                           (let* ((nhit (fts5-phrase-hits fts p (fts5-phrase-colset (fres-tree r) p) s))
                                  (x (log (/ (+ (- nrow nhit) 0.5d0) (+ nhit 0.5d0)))))
                             (if (<= x 0d0) 1d-6 x)))
                         (fres-phrases r))))
          (setf (getf (fres-cache r) :idf)
                (make-fts5-idf :idf idf :avgdl (if (zerop nrow) 0d0 (/ (coerce ntok 'double-float) nrow))))))))

(defun fts5-phrase-colset (tree phrase)
  (labels ((walk (e)
             (cond ((eq e :eof) nil)
                   ((fnear-p e) (when (member phrase (fnr-phrases e)) (return-from fts5-phrase-colset (fnr-colset e))))
                   (t (walk (second e)) (walk (third e))))))
    (walk tree)
    nil))

(defun fts5-instances (info)
  "(phrase col offset) of every instance in the row, in position order."
  (if (and (frow-result info) (not (eq (fts-detail (frow-fts info)) :full)))
      (fts5-instances-by-tokenizing info)
      (fts5-instances-from-index info)))

(defun fts5-instances-by-tokenizing (info)
  "Without positions in the index (detail=column/none), SQLite finds the
instances by tokenizing the row (sqlite3Fts5ExprPopulatePoslists): every
phrase live at this row, in every column its column filter allows."
  (let* ((fts (frow-fts info)) (r (frow-result info))
         (v (gethash (frow-rowid info) (fres-instances r)))
         (out '()))
    (when v
      (loop for p across (fres-phrases r)
            for i from 0
            do (when (aref v i)
                 (let* ((cs (fts5-phrase-colset (fres-tree r) p))
                        (term (first (fph-terms p)))
                        (tb (utf8-encode (first term))))
                   (loop for col below (length (fts-columns fts))
                         do (when (or (null cs) (and (listp cs) (member col cs)))
                              (loop for tk across (fts5-tokenize-value fts (nth col (frow-values info)))
                                    for pos from 0
                                    do (let ((kb (utf8-encode (first tk))))
                                         (when (and (or (= (length tb) (length kb))
                                                        (and (< (length tb) (length kb)) (second term)))
                                                    (not (mismatch tb kb :end2 (length tb))))
                                           (push (list i col pos) out))))))))))
    (stable-sort (nreverse out)
                 (lambda (a b) (or (< (second a) (second b))
                                   (and (= (second a) (second b))
                                        (or (< (third a) (third b))
                                            (and (= (third a) (third b)) (< (first a) (first b))))))))))

(defun fts5-instances-from-index (info)
  (let* ((r (frow-result info)))
    (when r
      (let* ((v (gethash (frow-rowid info) (fres-instances r)))
             (lists (and v (map 'vector #'copy-list v)))
             (out '()))
        (when lists
          (loop (let ((best nil))
                  (dotimes (i (length lists))
                    (when (and (aref lists i) (or (null best) (< (first (aref lists i)) (first (aref lists best)))))
                      (setf best i)))
                  (unless best (return))
                  (let ((p (pop (aref lists best))))
                    (if (eq (fts-detail (frow-fts info)) :full)
                        (push (list best (ash p -32) (logand p #xffffffff)) out)
                        (push (list best p 0) out))))))
        (nreverse out)))))

(defun fts5-bm25 (info weights)
  (let ((r (frow-result info)))
    (if (null r)
        -0d0
        (let* ((k1 1.2d0) (b 0.75d0)
               (idf (fts5-result-idf info))
               (nph (length (fres-phrases r)))
               (freq (make-array nph :initial-element 0d0))
               (d (coerce (reduce #'+ (fts5-docsize (frow-fts info) (frow-rowid info))) 'double-float))
               (score 0d0))
          (dolist (inst (fts5-instances info))
            (destructuring-bind (ip ic io) inst
              (declare (ignore io))
              (incf (aref freq ip) (if (< ic (length weights)) (value-to-real (nth ic weights)) 1d0))))
          (dotimes (i nph)
            (incf score (* (aref (fidf-idf idf) i)
                           (/ (* (aref freq i) (+ k1 1d0))
                              (+ (aref freq i) (* k1 (+ (- 1 b) (/ (* b d) (fidf-avgdl idf)))))))))
          (* -1d0 score)))))

;;; ------------------------------------------------------------------
;;; highlight() and snippet() (fts5_aux.c)

(defun fts5-cursor-info (v fname)
  (or (and (integerp v) (gethash v *fts5-cursors*))
      (sql-error "no such cursor: ~d" (let ((x (value-to-integer v))) (if (integerp x) x 0)))
      fname))

(defun fts5-phrase-size (info ip)
  (length (fph-terms (aref (fres-phrases (frow-result info)) ip))))

(defun fts5-cinst (info col)
  "Coalesced (start end) token ranges of instances in COL (fts5CInstIter)."
  (let ((out '()) (start -1) (end -1))
    (dolist (inst (fts5-instances info))
      (destructuring-bind (ip ic io) inst
        (when (= ic col)
          (let ((e (+ io -1 (fts5-phrase-size info ip))))
            (cond ((< start 0) (setf start io end e))
                  ((<= io end) (when (> e end) (setf end e)))
                  (t (push (list start end) out) (setf start io end e)))))))
    (when (>= start 0) (push (list start end) out))
    (nreverse out)))

(defun fts5-column-text (info col)
  (let ((v (nth col (frow-values info))))
    (if (or (null v) (eq v :null)) nil (value-to-text v))))

(defun fts5-highlight-range (info col text open close range-start range-end)
  "The highlighting pass (fts5HighlightCb), over [RANGE-START, RANGE-END]
tokens, or all when RANGE-END is negative.  Returns (values bytes-out)."
  (let* ((bytes (utf8-encode text))
         (out (new-buf))
         (toks (fts5-tokenize (fts-tokenizer (frow-fts info)) text))
         (iter (fts5-cinst info col))
         (cur-start -1) (cur-end -1)
         (ioff 0))
    (flet ((next-inst ()
             (if iter
                 (destructuring-bind (s e) (pop iter) (setf cur-start s cur-end e))
                 (setf cur-start -1 cur-end -1)))
           (app (b s e) (when (and b (< s e)) (buf-bytes out b s e)))
           (app-str (s) (when s (buf-bytes out (utf8-encode s)))))
      (next-inst)
      ;; snippet: skip instances before the range
      (loop while (and (>= cur-start 0) (< cur-start range-start)) do (next-inst))
      (loop for tk across toks
            for ipos from 0
            do (destructuring-bind (tok s e) tk
                 (declare (ignore tok))
                 (block this
                   ;; a range end of 0 or less means no range, as in SQLite
                   (when (> range-end 0)
                     (when (or (< ipos range-start) (> ipos range-end)) (return-from this))
                     (when (and (plusp range-start) (= ipos range-start)) (setf ioff s)))
                   (when (= ipos cur-start)
                     (app bytes ioff s) (app-str open) (setf ioff s))
                   (when (= ipos cur-end)
                     (when (and (> range-end 0) (< cur-start range-start)) (app-str open))
                     (app bytes ioff e) (app-str close) (setf ioff e)
                     (next-inst))
                   (when (and (> range-end 0) (= ipos range-end))
                     (app bytes ioff e) (setf ioff e)
                     (when (and (>= ipos cur-start) (< ipos cur-end)) (app-str close))))))
      (values out ioff bytes))))

(defun fts5-highlight (info col open close)
  (let ((text (fts5-column-text info col)))
    (if (null text)
        :null
        (multiple-value-bind (out ioff bytes) (fts5-highlight-range info col text open close 0 0)
          (buf-bytes out bytes ioff (length bytes))
          (utf8-decode (coerce out '(simple-array (unsigned-byte 8) (*))))))))

(defun fts5-sentence-starts (fts text)
  (let ((bytes (utf8-encode text)) (out '()))
    (loop for tk across (fts5-tokenize (fts-tokenizer fts) text)
          for ipos from 0
          do (if (zerop ipos)
                 (push 0 out)
                 (let ((i (1- (second tk))) (c nil))
                   (loop while (>= i 0)
                         do (setf c (code-char (aref bytes i)))
                            (unless (member c '(#\Space #\Tab #\Newline #\Return)) (return))
                            (decf i))
                   (when (and (/= i (1- (second tk))) (member c '(#\. #\:)))
                     (push ipos out)))))
    (coerce (nreverse out) 'vector)))

(defun fts5-snippet-score (info col ipos ntoken ndocsize seen)
  "(values score adjusted-start)."
  (let ((score 0) (ifirst -1) (ilast 0) (iend (+ ipos ntoken)))
    (dolist (inst (fts5-instances info))
      (destructuring-bind (ip ic io) inst
        (when (and (= ic col) (>= io ipos) (< io iend))
          (incf score (if (aref seen ip) 1 1000))
          (setf (aref seen ip) t)
          (when (< ifirst 0) (setf ifirst io))
          (setf ilast (+ io (fts5-phrase-size info ip))))))
    (let ((iadj (- ifirst (truncate (- ntoken (- ilast ifirst)) 2))))
      (when (> (+ iadj ntoken) ndocsize) (setf iadj (- ndocsize ntoken)))
      (when (< iadj 0) (setf iadj 0))
      (values score iadj))))

(defun fts5-snippet (info icol open close ellips ntoken)
  (let* ((fts (frow-fts info))
         (ncol (length (fts-columns fts)))
         (nphrase (if (frow-result info) (length (fres-phrases (frow-result info))) 0))
         (best-col (if (>= icol 0) icol 0))
         (best-start 0) (best-score 0) (col-size 0)
         (insts (fts5-instances info)))
    (dotimes (i ncol)
      (when (or (< icol 0) (= icol i))
        (let* ((text (or (fts5-column-text info i) ""))
               (starts (fts5-sentence-starts fts text))
               (ndocsize (aref (fts5-docsize fts (frow-rowid info)) i)))
          (dolist (inst insts)
            (destructuring-bind (ip ic io) inst
              (declare (ignore ip))
              (when (= ic i)
                (multiple-value-bind (score adj)
                    (fts5-snippet-score info i io ntoken ndocsize (make-array nphrase :initial-element nil))
                  (when (> score best-score)
                    (setf best-score score best-col i best-start adj col-size ndocsize)))
                (when (and (plusp (length starts)) (> ndocsize ntoken))
                  (let ((jj 0))
                    (loop while (and (< jj (1- (length starts))) (not (> (aref starts (1+ jj)) io)))
                          do (incf jj))
                    (when (< (aref starts jj) io)
                      (let ((score (fts5-snippet-score info i (aref starts jj) ntoken ndocsize
                                                       (make-array nphrase :initial-element nil))))
                        (incf score (if (zerop (aref starts jj)) 120 100))
                        (when (> score best-score)
                          (setf best-score score best-col i best-start (aref starts jj)
                                col-size ndocsize))))))))))))
    (let ((text (fts5-column-text info best-col)))
      (when (zerop col-size) (setf col-size (aref (fts5-docsize fts (frow-rowid info)) best-col)))
      (if (null text)
          :null
          (let ((range-end (+ best-start ntoken -1)))
            (multiple-value-bind (out ioff bytes)
                (fts5-highlight-range info best-col text open close best-start range-end)
              (let ((final (new-buf)))
                (when (plusp best-start) (buf-bytes final (utf8-encode (or ellips ""))))
                (buf-bytes final out)
                (if (>= range-end (1- col-size))
                    (buf-bytes final bytes ioff (length bytes))
                    (buf-bytes final (utf8-encode (or ellips ""))))
                (utf8-decode (coerce final '(simple-array (unsigned-byte 8) (*)))))))))))

(defun fts5-arg-text (v) (if (eq v :null) nil (value-to-text v)))

(defsqlfun "bm25" (1 nil) (args)
  (let ((info (fts5-cursor-info (first args) "bm25")))
    (fts5-bm25 info (rest args))))

(defsqlfun "highlight" (1 nil) (args)
  (unless (= (length args) 4) (sql-error "wrong number of arguments to function highlight()"))
  (let ((info (fts5-cursor-info (first args) "highlight")))
    (fts5-highlight info (value-to-integer (second args)) (fts5-arg-text (third args)) (fts5-arg-text (fourth args)))))

(defsqlfun "snippet" (1 nil) (args)
  (unless (= (length args) 6) (sql-error "wrong number of arguments to function snippet()"))
  (let ((info (fts5-cursor-info (first args) "snippet")))
    (fts5-snippet info (let ((c (value-to-integer (second args)))) (if (integerp c) c 0))
                  (fts5-arg-text (third args)) (fts5-arg-text (fourth args)) (fts5-arg-text (fifth args))
                  (let ((k (value-to-integer (sixth args)))) (if (integerp k) k 0)))))
