;;;; dml.lisp — INSERT, UPDATE, DELETE: rows, indexes and constraints.

(in-package #:sqlite-pure)

(define-condition sqlite-conflict (sqlite-constraint-error)
  ((action :initarg :action :initform :abort :reader conflict-action)))

(defun conflict-fail (action fmt &rest args)
  (error 'sqlite-conflict :action action :message (apply #'format nil fmt args)))

;;; ------------------------------------------------------------------
;;; Index keys and comparators

(defun eval-on-row (fn table row)
  "Evaluate compiled FN (compiled against TABLE-SCOPE) on ROW."
  (declare (ignore table))
  (funcall fn (row-env row)))

(defun table-scope (table &optional alias)
  (make-scope :srcs (list (make-table-src table alias)) :parent *outer-scope*))

(defun row-env (&rest rows)
  (make-env :rows (coerce rows 'vector) :parent *outer-env*))

(defvar *index-expr-cache* nil)

(defun index-expr-fn (table e)
  (let ((key (cons table e)))
    (or (cdr (assoc key *index-expr-cache* :test #'equal))
        (let ((f (compile-expr e (table-scope table))))
          (push (cons key f) *index-expr-cache*)
          f))))

(defun index-key (table index row)
  "The full entry stored in INDEX for ROW (row vector with rowid last)."
  (let* ((n (length (table-columns table)))
         (rowid (svref row n))
         (vals (loop for (c) in (index-columns index)
                     collect (cond ((integerp c) (svref row c))
                                   ((eq c :rowid) rowid)
                                   (t (eval-on-row (index-expr-fn table c) table row))))))
    (cond ((index-pk-index index) (wr-record table row))
          ((table-without-rowid table)
           (append vals (loop for ci in (table-pk table)
                              unless (member ci (index-columns index) :key #'first)
                                collect (svref row ci))))
          (t (append vals (list rowid))))))

(defun index-full-cmp (table index)
  "Comparator for whole entries of INDEX."
  (let* ((colls (index-collations index))
         (descs (index-descs index))
         (nkey (length colls)))
    (cond ((index-pk-index index)
           (let ((cmp (index-key-cmp colls descs)))
             (lambda (a b) (funcall cmp (subseq a 0 nkey) (subseq b 0 (min nkey (length b)))))))
          ((table-without-rowid table)
           (let ((tail-colls (loop for ci in (table-pk table)
                                   unless (member ci (index-columns index) :key #'first)
                                     collect (collate-of (aref (table-columns table) ci)))))
             (index-key-cmp (append colls tail-colls) descs)))
          (t (index-key-cmp colls descs)))))

(defun index-applies-p (table index row)
  (or (null (index-where index))
      (eq (truth (eval-on-row (index-expr-fn table (index-where index)) table row)) t)))

(defun wr-record (table row)
  "Stored record of a WITHOUT ROWID table: primary key first."
  (mapcar (lambda (ci) (svref row ci)) (record-column-order table)))

(defun table-record (table row)
  (mapcar (lambda (i) (if (eql i (table-rowid-alias table)) :null (svref row i)))
          (record-column-order table)))

(defun compute-generated (table row &key virtual-only)
  "Fill ROW's generated columns from their expressions (twice over, so a
column may use one declared after it)."
  (let ((cols (table-columns table)))
    (when (some #'column-generated cols)
      (dotimes (pass 2)
        (loop for c across cols
              for i from 0
              do (when (and (column-generated c) (or (not virtual-only) (column-virtual-p c)))
                   (let ((f (or (column-gen-fn c)
                                (setf (column-gen-fn c)
                                      (compile-expr (column-generated c)
                                                    (make-scope :srcs (list (make-table-src table))))))))
                     (setf (svref row i)
                           (apply-affinity (funcall f (make-env :rows (vector row)))
                                           (column-affinity c))))))))))

(defun check-strict (table row)
  (when (table-strict table)
    (loop for c across (table-columns table)
          for i from 0
          for v = (svref row i)
          for ty = (string-upcase-ascii (or (column-type c) ""))
          do (unless (or (eq v :null) (string= ty "ANY")
                         (cond ((member ty '("INT" "INTEGER") :test #'string=) (integerp v))
                               ((string= ty "REAL") (floatp v))
                               ((string= ty "TEXT") (stringp v))
                               ((string= ty "BLOB") (blobp v))))
               (conflict-fail :abort "cannot store ~a value in ~a column ~a.~a"
                              (string-upcase (type-name-of v)) ty
                              (table-name table) (column-name c))))))

;;; ------------------------------------------------------------------
;;; Low-level row writes (no constraint checks)

(defun insert-index-entries (table row)
  (dolist (idx (table-indexes table))
    (unless (index-pk-index idx)
      (when (index-applies-p table idx row)
        (let ((*index-cmp* (index-full-cmp table idx)))
          (index-insert (table-owner table) (index-root idx) (index-key table idx row)))))))

(defun delete-index-entries (table row)
  (dolist (idx (table-indexes table))
    (unless (index-pk-index idx)
      (when (index-applies-p table idx row)
        (let ((*index-cmp* (index-full-cmp table idx)))
          (index-delete (table-owner table) (index-root idx) (index-key table idx row)))))))

(defun write-row (table row)
  "Store ROW (a full row vector, rowid last) and its index entries."
  (let ((n (length (table-columns table))))
    (if (table-without-rowid table)
        (let* ((pkidx (find-if #'index-pk-index (table-indexes table)))
               (*index-cmp* (index-full-cmp table pkidx)))
          (index-insert (table-owner table) (table-root table) (wr-record table row)))
        (table-insert (table-owner table) (table-root table) (svref row n)
                      (encode-record (table-record table row))))
    (insert-index-entries table row)))

(defun delete-row (table row)
  (delete-index-entries table row)
  (if (table-without-rowid table)
      (let* ((pkidx (find-if #'index-pk-index (table-indexes table)))
             (*index-cmp* (index-full-cmp table pkidx)))
        (index-delete (table-owner table) (table-root table) (wr-record table row)))
      (table-delete (table-owner table) (table-root table) (svref row (length (table-columns table))))))

;;; ------------------------------------------------------------------
;;; Conflict detection

(defun find-index-conflicts (table index row)
  "Rows (vectors) other than ROW that share INDEX's key with ROW."
  (let* ((n (length (table-columns table)))
         (key (subseq (index-key table index row) 0 (length (index-columns index))))
         (hits '()))
    (when (member :null key) (return-from find-index-conflicts nil))
    (let ((cmp (index-key-cmp (index-collations index) (index-descs index))))
      (catch :probe-done
        (map-index (table-owner table) (index-root index)
                   (lambda (vals)
                     (unless (zerop (funcall cmp vals key)) (throw :probe-done nil))
                     (let ((other (cond ((index-pk-index index) (table-record-to-row table nil vals))
                                        ((table-without-rowid table)
                                         (fetch-wr-row table (last vals (length (table-pk table)))))
                                        (t (fetch-row table (car (last vals)))))))
                       (when (and other (not (same-row-p table other row)))
                         (push other hits))))
                   :probe key :cmp cmp)))
    n
    hits))

(defun fetch-wr-row (table pk-vals)
  (let* ((pkidx (find-if #'index-pk-index (table-indexes table)))
         (cmp (index-key-cmp (index-collations pkidx) (index-descs pkidx)))
         (found nil))
    (catch :probe-done
      (map-index (table-owner table) (table-root table)
                 (lambda (vals)
                   (when (zerop (funcall cmp vals pk-vals))
                     (setf found (table-record-to-row table nil vals)))
                   (throw :probe-done nil))
                 :probe pk-vals :cmp cmp))
    found))

(defvar *self-row* nil "During UPDATE, the pre-image of the row being changed.")

(defun same-row-p (table a b)
  (declare (ignore b))
  (and *self-row*
       (if (table-without-rowid table)
           (let ((n (length (table-columns table))))
             (declare (ignore n))
             (every (lambda (ci) (values-equal-p (svref a ci) (svref *self-row* ci)))
                    (table-pk table)))
           (eql (svref a (length (table-columns table)))
                (svref *self-row* (length (table-columns table)))))))

(defun constraint-columns-text (table index)
  (format nil "~{~a~^, ~}"
          (mapcar (lambda (c)
                    (format nil "~a.~a" (table-name table)
                            (cond ((integerp (first c)) (column-name (aref (table-columns table) (first c))))
                                  ((eq (first c) :rowid) "rowid")
                                  (t "<expr>"))))
                  (index-columns index))))

;;; ------------------------------------------------------------------
;;; Rowids

(defun sequence-table (&optional (db *db*))
  "sqlite_sequence of DB (a table's owner)."
  (find-table-in db "sqlite_sequence"))

(defun sequence-value (table)
  (let ((seq (sequence-table (table-owner table))))
    (if (null seq)
        0
        (let ((v 0))
          (map-table-rows seq (lambda (row)
                                (when (and (stringp (svref row 0)) (name= (svref row 0) (table-name table)))
                                  (setf v (value-to-integer (svref row 1))))))
          v))))

(defun update-sequence (table rowid)
  (let ((seq (sequence-table (table-owner table))))
    (when seq
      (let ((existing nil))
        (map-table-rows seq (lambda (row)
                              (when (and (stringp (svref row 0)) (name= (svref row 0) (table-name table)))
                                (setf existing row))))
        (cond ((null existing)
               (let ((r (vector (table-name table) rowid
                                (1+ (or (table-max-rowid (table-owner seq) (table-root seq)) 0)))))
                 (write-row seq r)))
              ((< (value-to-integer (svref existing 1)) rowid)
               (let ((r (copy-seq existing)))
                 (setf (svref r 1) rowid)
                 (write-row seq r))))))))

(defun new-rowid (table)
  (let ((mx (or (table-max-rowid (table-owner table) (table-root table)) 0)))
    (when (table-autoincrement table)
      (setf mx (max mx (sequence-value table))))
    (if (< mx +i64-max+)
        (1+ mx)
        (if (table-autoincrement table)
            (error 'sqlite-error :code :full :message "database or disk is full")
            ;; SQLite probes random rowids when the maximum is taken
            (loop repeat 100
                  for r = (1+ (random +i64-max+))
                  unless (table-lookup (table-owner table) (table-root table) r) return r
                  finally (error 'sqlite-error :code :full :message "database or disk is full"))))))

;;; ------------------------------------------------------------------
;;; Checks

(defstruct (write-ctx (:conc-name wc-))
  table conflict checks-fns returning-fns returning-scope upsert (changes 0) returned)

(defun compile-checks (table)
  (let ((scope (table-scope table)))
    (mapcar (lambda (c) (cons (car c) (compile-expr (cdr c) scope))) (table-checks table))))

(defun resolve-action (ctx constraint-conflict)
  (or (wc-conflict ctx) constraint-conflict :abort))

(defun check-not-null (ctx row)
  "Return :IGNORE to skip the row, else T."
  (let ((table (wc-table ctx)))
    (loop for col across (table-columns table)
          for i from 0
          do (when (and (column-not-null col) (eq (svref row i) :null)
                        (not (eql i (table-rowid-alias table))))
               (let ((action (resolve-action ctx nil)))
                 (case action
                   (:ignore (return-from check-not-null :ignore))
                   (:replace
                    (let ((d (column-default-value col)))
                      (if (eq d :null)
                          (conflict-fail :abort "NOT NULL constraint failed: ~a.~a"
                                         (table-name table) (column-name col))
                          (setf (svref row i) d))))
                   (t (conflict-fail action "NOT NULL constraint failed: ~a.~a"
                                     (table-name table) (column-name col))))))))
  t)

(defun check-checks (ctx row)
  (let ((table (wc-table ctx)))
    (dolist (c (wc-checks-fns ctx) t)
      (let ((v (truth (eval-on-row (cdr c) table row))))
        (when (null v)
          (let ((action (resolve-action ctx nil)))
            (when (eq action :ignore) (return :ignore))
            (conflict-fail (if (eq action :replace) :abort action)
                           "CHECK constraint failed: ~a"
                           (or (car c) (table-name table)))))))))

(defun resolve-uniqueness (ctx row)
  "Find uniqueness conflicts for ROW and act on them.  Return :IGNORE,
(:UPSERT existing-row clause), or T."
  (let* ((table (wc-table ctx))
         (n (length (table-columns table)))
         (rowid (svref row n)))
    ;; rowid (INTEGER PRIMARY KEY)
    (unless (table-without-rowid table)
      (let ((existing (fetch-row table rowid)))
        (when (and existing (not (same-row-p table existing row)))
          (let ((up (matching-upsert ctx :rowid)))
            (when up (return-from resolve-uniqueness (list :upsert existing up))))
          (let ((action (resolve-action ctx (table-pk-conflict table))))
            (case action
              (:ignore (return-from resolve-uniqueness :ignore))
              (:replace (fk-parent-delete table existing) (delete-row table existing))
              (t (conflict-fail action "UNIQUE constraint failed: ~a"
                                (if (table-rowid-alias table)
                                    (format nil "~a.~a" (table-name table)
                                            (column-name (aref (table-columns table)
                                                               (table-rowid-alias table))))
                                    (format nil "~a.rowid" (table-name table))))))))))
    ;; unique indexes (the WITHOUT ROWID primary key among them)
    (dolist (idx (table-indexes table) t)
      (when (and (index-unique idx) (index-applies-p table idx row))
        (let ((others (find-index-conflicts table idx row)))
          (when others
            (let ((up (matching-upsert ctx idx)))
              (when up (return-from resolve-uniqueness (list :upsert (first others) up))))
            (let ((action (resolve-action ctx (index-conflict idx))))
              (case action
                (:ignore (return-from resolve-uniqueness :ignore))
                (:replace (dolist (o others) (fk-parent-delete table o) (delete-row table o)))
                (t (conflict-fail action "UNIQUE constraint failed: ~a"
                                  (if (index-pk-index idx)
                                      (constraint-columns-text table idx)
                                      (constraint-columns-text table idx))))))))))))

(defun matching-upsert (ctx target)
  "The ON CONFLICT clause (if any) that handles a conflict on TARGET
(an INDEX, or :ROWID)."
  (let ((table (wc-table ctx)))
    (dolist (u (wc-upsert ctx))
      (let ((cols (getf u :target)))
        (when (or (null cols)
                  (let ((names (mapcar (lambda (e) (string-downcase-ascii (or (expr-column-name e) ""))) cols)))
                    (if (eq target :rowid)
                        (and (table-rowid-alias table) (null (cdr names))
                             (string= (car names)
                                      (string-downcase-ascii
                                       (column-name (aref (table-columns table) (table-rowid-alias table))))))
                        (equal (sort (copy-list names) #'string<)
                               (sort (mapcar (lambda (c)
                                               (if (integerp (first c))
                                                   (string-downcase-ascii
                                                    (column-name (aref (table-columns table) (first c))))
                                                   ""))
                                             (index-columns target))
                                     #'string<)))))
          (return u))))))

;;; ------------------------------------------------------------------
;;; Preparing a row

(defun apply-row-affinity (table row)
  (loop for col across (table-columns table)
        for i from 0
        do (setf (svref row i) (apply-affinity (svref row i) (column-affinity col)))))

(defun finalize-rowid (table row)
  "Settle the rowid slot from the INTEGER PRIMARY KEY column (if any)."
  (let* ((n (length (table-columns table)))
         (alias (table-rowid-alias table)))
    (unless (table-without-rowid table)
      (let ((v (if alias (svref row alias) (svref row n))))
        (cond ((eq v :null)
               (let ((r (new-rowid table)))
                 (setf (svref row n) r)
                 (when alias (setf (svref row alias) r))))
              (t
               (let ((r (let ((x (apply-affinity v :integer)))
                          (if (integerp x) x
                              (if (and (floatp x) (= x (ftruncate x)) (i64-p (truncate x)))
                                  (truncate x)
                                  (error 'sqlite-error :code :mismatch :message "datatype mismatch"))))))
                 (setf (svref row n) r)
                 (when alias (setf (svref row alias) r)))))))))

(defun insert-prepared-row (ctx row)
  "Constraint-check and store ROW.  Return :IGNORE if skipped."
  (let ((table (wc-table ctx)))
    (check-strict table row)
    (when (eq (check-not-null ctx row) :ignore) (return-from insert-prepared-row :ignore))
    (when (eq (check-checks ctx row) :ignore) (return-from insert-prepared-row :ignore))
    (let ((u (resolve-uniqueness ctx row)))
      (cond ((eq u :ignore) :ignore)
            ((and (consp u) (eq (car u) :upsert))
             (run-upsert ctx (second u) (third u) row))
            (t
             (write-row table row)
             (fk-check-child table row)
             (unless (table-without-rowid table)
               (setf (db-last-insert-rowid (conn *db*)) (svref row (length (table-columns table)))))
             (incf (wc-changes ctx))
             (collect-returning ctx row)
             t)))))

(defun collect-returning (ctx row)
  (when (wc-returning-fns ctx)
    (let ((env (row-env row)))
      (push (mapcar (lambda (f) (funcall f env)) (wc-returning-fns ctx)) (wc-returned ctx)))))

(defun run-upsert (ctx existing clause proposed)
  (let ((table (wc-table ctx)))
    (if (eq (getf clause :action) :nothing)
        :ignore
        (let* ((src (make-table-src table))
               (exsrc (make-table-src table "excluded"))
               (scope (make-scope :srcs (list src exsrc) :parent *outer-scope*))
               (env (row-env existing proposed))
               (where (getf clause :update-where)))
          (setf (src-rowid-p exsrc) nil
                (src-hidden exsrc) (loop for i below (length (table-columns table)) collect i))
          (when (and where (not (eq (truth (funcall (compile-expr where scope) env)) t)))
            (return-from run-upsert :ignore))
          (let ((new (copy-seq existing)))
            (dolist (s (getf clause :sets))
              (destructuring-bind (cols e) s
                (let ((v (funcall (compile-expr e scope) env)))
                  (dolist (c cols)
                    (let ((ci (or (find-column table c) (sql-error "no such column: ~a" c))))
                      (setf (svref new ci) v))))))
            (let ((uctx (copy-write-ctx ctx)))
              (setf (wc-conflict uctx) nil (wc-upsert uctx) nil (wc-changes uctx) 0
                    (wc-returned uctx) nil)
              (update-one uctx existing new)
              (incf (wc-changes ctx) (wc-changes uctx))
              (setf (wc-returned ctx) (append (wc-returned uctx) (wc-returned ctx))))
            t)))))

(defun update-one (ctx old new)
  "Replace row OLD by NEW (a full row vector, rowid slot possibly stale)."
  (let* ((table (wc-table ctx))
         (n (length (table-columns table)))
         (alias (table-rowid-alias table)))
    (apply-row-affinity table new)
    (compute-generated table new)
    (check-strict table new)
    (unless (table-without-rowid table)
      (cond (alias
             (let ((v (svref new alias)))
               (if (eq v :null)
                   (setf (svref new alias) (svref old n) (svref new n) (svref old n))
                   (finalize-rowid table new))))
            (t (unless (integerp (svref new n)) (finalize-rowid table new)))))
    (let ((*self-row* old))
      (when (eq (check-not-null ctx new) :ignore) (return-from update-one :ignore))
      (when (eq (check-checks ctx new) :ignore) (return-from update-one :ignore))
      (let ((u (resolve-uniqueness ctx new)))
        (when (eq u :ignore) (return-from update-one :ignore))))
    (delete-row table old)
    (write-row table new)
    (fk-check-child table new old)
    (fk-parent-update table old new)
    (incf (wc-changes ctx))
    (collect-returning ctx new)
    t))

;;; ------------------------------------------------------------------
;;; Statements

(defun view-as-table (table)
  "A TABLE whose columns are the view's result columns."
  (let ((copy (copy-table table)))
    (setf (table-columns copy)
          (map 'vector (lambda (c) (setf (column-affinity c) :blob (column-collation c) :binary) c)
               (view-column-info table)))
    copy))

(defun writable-table (name &optional event schema)
  (let ((table (lookup-table *db* name t schema)))
    (when (table-view-select table)
      (if (and event (triggers-for table event :instead-of))
          (return-from writable-table (view-as-table table))
          (sql-error "cannot modify ~a because it is a view" name)))
    (when (and (= (table-root table) 1))
      (sql-error "table ~a may not be modified" name))
    table))

(defun compile-returning (cols table alias)
  (when cols
    (let* ((scope (table-scope table alias))
           (out '()) (names '()))
      (dolist (c cols)
        (if (eq (car c) :star)
            (loop for col across (table-columns table)
                  for i from 0
                  do (push (compile-expr (list :srccol 0 i) scope) out)
                     (push (column-name col) names))
            (progn (push (compile-expr (second c) scope) out)
                   (push (or (third c) (result-column-name (second c) scope nil)
                             "?")
                         names))))
      (values (nreverse out) (nreverse names)))))

(defun make-ctx-for (table conflict returning alias &optional upsert)
  (multiple-value-bind (rfns rnames) (compile-returning returning table alias)
    (values (make-write-ctx :table table :conflict conflict
                            :checks-fns (compile-checks table)
                            :returning-fns rfns :upsert upsert)
            rnames)))

(defun exec-insert (st)
  (destructuring-bind (&key with conflict table schema alias columns source upsert returning) (cdr st)
    (let* ((*ctes* *ctes*)
           (tb (progn (when with (register-ctes (make-sel :with (first with)
                                                          :recursive (second with))))
                      (writable-table table :insert schema)))
           (view (table-view-select tb))
           (triggers (table-has-triggers-p tb))
           (ncols (length (table-columns tb)))
           (targets (if columns
                        (mapcar (lambda (c)
                                  (let ((ci (or (find-column tb c)
                                                (and (rowid-name-p c) (not (table-without-rowid tb)) :rowid)
                                                (sql-error "table ~a has no column named ~a" table c))))
                                    (when (and (integerp ci) (column-generated (aref (table-columns tb) ci)))
                                      (sql-error "cannot INSERT into generated column \"~a\"" c))
                                    ci))
                                columns)
                        (loop for i below ncols
                              unless (column-generated (aref (table-columns tb) i)) collect i)))
           (rows (cond ((eq source :default) (list '()))
                       (t (let ((sel source))
                            (multiple-value-bind (fn cols) (compile-select sel (root-scope))
                              (unless (= (length cols) (length targets))
                                (if columns
                                    (sql-error "~d values for ~d columns" (length cols) (length targets))
                                    (sql-error "table ~a has ~d columns but ~d values were supplied"
                                               table (length targets) (length cols))))
                              (funcall fn *outer-env*)))))))
      (multiple-value-bind (ctx rnames) (make-ctx-for tb conflict returning alias upsert)
        (dolist (vals rows)
          (let ((row (make-array (1+ ncols) :initial-element :unset)))
            (setf (svref row ncols) :null)
            (loop for v in vals
                  for ti in targets
                  do (if (eq ti :rowid)
                         (setf (svref row ncols) v)
                         (setf (svref row ti) v)))
            (dotimes (i ncols)
              (when (eq (svref row i) :unset)
                (setf (svref row i) (column-default-value (aref (table-columns tb) i)))))
            (apply-row-affinity tb row)
            (compute-generated tb row)
            (cond
              (view
               (fire-triggers tb :insert :instead-of nil row)
               (incf (wc-changes ctx)))
              ((and triggers
                    (eq :ignore (fire-triggers tb :insert :before nil (before-insert-image tb row)))))
              (t
               (finalize-rowid tb row)
               ;; SQLite advances the AUTOINCREMENT counter as soon as a rowid
               ;; is chosen, even if the row is then ignored.
               (when (table-autoincrement tb)
                 (update-sequence tb (svref row ncols)))
               (when (and (eq (insert-prepared-row ctx row) t) triggers)
                 (fire-triggers tb :insert :after nil row))))))
        (setf (db-changes (conn *db*)) (wc-changes ctx))
        (incf (db-total-changes (conn *db*)) (wc-changes ctx))
        (values (reverse (wc-returned ctx)) rnames)))))

(defun before-insert-image (table row)
  "NEW as a BEFORE INSERT trigger sees it: an unassigned rowid reads -1."
  (let* ((n (length (table-columns table)))
         (img (copy-seq row))
         (alias (table-rowid-alias table)))
    (unless (table-without-rowid table)
      (let ((v (if alias (svref img alias) (svref img n))))
        (when (eq v :null)
          (setf (svref img n) -1)
          (when alias (setf (svref img alias) -1)))
        (when (and alias (integerp v)) (setf (svref img n) v))))
    img))

(defun scan-view-rows (table alias where)
  "Rows of a view (as vectors) satisfying WHERE."
  (let* ((fs (let ((*ctes* '()))
               (select-derived-source (table-view-select table) (or alias (table-name table))
                                      (make-scope) (table-view-columns table))))
         (scope (make-scope :srcs (list (fsrc-src fs)) :parent *outer-scope*))
         (env (make-env :rows (make-array 1) :parent *outer-env*))
         (out '()))
    (multiple-value-bind (levels finals) (build-levels (list fs) scope where)
      (run-levels levels env (lambda ()
                               (when (all-true finals env)
                                 (push (svref (env-rows env) 0) out)))))
    (nreverse out)))

(defun scan-table-rows (table alias where)
  "All rows of TABLE (vectors) satisfying WHERE."
  (when (table-view-select table)
    (return-from scan-table-rows (scan-view-rows table alias where)))
  (let* ((fs (let ((f (make-fsrc :src (make-table-src table alias) :table table :join :first)))
               ;; DML needs whole rows (indexes, triggers, RETURNING)
               (setf (src-used (fsrc-src f)) :all)
               f))
         (scope (make-scope :srcs (list (fsrc-src fs)) :parent *outer-scope*))
         (env (make-env :rows (make-array 1) :parent *outer-env*))
         (out '()))
    (multiple-value-bind (levels finals) (build-levels (list fs) scope where)
      (run-levels levels env (lambda ()
                               (when (all-true finals env)
                                 (push (svref (env-rows env) 0) out)))))
    (nreverse out)))

(defun exec-update (st)
  (destructuring-bind (&key with conflict table schema alias sets from where returning) (cdr st)
    (when from
      (return-from exec-update (exec-update-from st)))
    (let* ((*ctes* *ctes*)
           (tb (progn (when with (register-ctes (make-sel :with (first with) :recursive (second with))))
                      (writable-table table :update schema)))
           (view (table-view-select tb))
           (triggers (table-has-triggers-p tb))
           (changed (loop for (cols) in sets append cols))
           (scope (table-scope tb alias))
           (assigns (loop for (cols e) in sets
                          collect (cons (mapcar (lambda (c)
                                                  (let ((ci (or (find-column tb c)
                                                                (and (rowid-name-p c) (not (table-without-rowid tb)) :rowid)
                                                                (sql-error "no such column: ~a" c))))
                                                    (when (and (integerp ci) (column-generated (aref (table-columns tb) ci)))
                                                      (sql-error "cannot UPDATE generated column \"~a\"" c))
                                                    ci))
                                                cols)
                                        (compile-expr e scope))))
           (rows (scan-table-rows tb alias where)))
      (multiple-value-bind (ctx rnames) (make-ctx-for tb conflict returning alias)
        (dolist (old rows)
          (let ((new (copy-seq old))
                (env (row-env old)))
            (dolist (a assigns)
              (let ((v (funcall (cdr a) env)))
                (dolist (ci (car a))
                  (if (eq ci :rowid)
                      (setf (svref new (length (table-columns tb))) v)
                      (setf (svref new ci) v)))))
            (cond
              (view (fire-triggers tb :update :instead-of old new changed)
                    (incf (wc-changes ctx)))
              ;; the row may have been removed by an earlier REPLACE or trigger
              ((not (or (table-without-rowid tb)
                        (table-lookup (table-owner tb) (table-root tb) (svref old (length (table-columns tb)))))))
              ((and triggers (eq :ignore (fire-triggers tb :update :before old new changed))))
              (t (when (and (eq (update-one ctx old new) t) triggers)
                   (fire-triggers tb :update :after old new changed))))))
        (setf (db-changes (conn *db*)) (wc-changes ctx))
        (incf (db-total-changes (conn *db*)) (wc-changes ctx))
        (values (reverse (wc-returned ctx)) rnames)))))

(defun exec-update-from (st)
  "UPDATE t SET ... FROM <sources> WHERE ...: join, then update each target
row once, from the last joined row that matched it."
  (destructuring-bind (&key with conflict table schema alias sets from where returning) (cdr st)
    (let* ((*ctes* *ctes*)
           (tb (progn (when with (register-ctes (make-sel :with (first with) :recursive (second with))))
                      (writable-table table nil schema)))
           (target (let ((f (make-fsrc :src (make-table-src tb alias) :table tb :join :first)))
                     (setf (src-used (fsrc-src f)) :all)
                     f))
           (others (loop for item in from
                         for k from 0
                         collect (let ((fs (make-fsrc-for item (root-scope))))
                                   (when (zerop k) (setf (fsrc-join fs) :comma))
                                   fs)))
           (fsrcs (cons target others))
           (scope (make-scope :srcs (mapcar #'fsrc-src fsrcs) :parent *outer-scope*))
           (ons (apply-joins fsrcs scope))
           (assigns (loop for (cols e) in sets
                          collect (cons (mapcar (lambda (c)
                                                  (let ((ci (or (find-column tb c)
                                                                (sql-error "no such column: ~a" c))))
                                                    (when (column-generated (aref (table-columns tb) ci))
                                                      (sql-error "cannot UPDATE generated column \"~a\"" c))
                                                    ci))
                                                cols)
                                        (compile-expr e scope))))
           (env (make-env :rows (make-array (length fsrcs)) :parent *outer-env*))
           (matches (make-hash-table :test #'equal))
           (order '()))
      (multiple-value-bind (levels finals) (build-levels fsrcs scope where ons)
        (run-levels levels env
                    (lambda ()
                      (when (all-true finals env)
                        (let* ((row (svref (env-rows env) 0))
                               (key (if (table-without-rowid tb)
                                        (group-key (mapcar (lambda (ci) (svref row ci)) (table-pk tb)))
                                        (svref row (length (table-columns tb))))))
                          (unless (nth-value 1 (gethash key matches)) (push key order))
                          (setf (gethash key matches) (copy-seq (env-rows env))))))))
      (multiple-value-bind (ctx rnames) (make-ctx-for tb conflict returning alias)
        (dolist (key (nreverse order))
          (let* ((rows (gethash key matches))
                 (old (svref rows 0))
                 (new (copy-seq old))
                 (e (make-env :rows rows :parent *outer-env*)))
            (dolist (a assigns)
              (let ((v (funcall (cdr a) e)))
                (dolist (ci (car a)) (setf (svref new ci) v))))
            (update-one ctx old new)))
        (setf (db-changes (conn *db*)) (wc-changes ctx))
        (incf (db-total-changes (conn *db*)) (wc-changes ctx))
        (values (reverse (wc-returned ctx)) rnames)))))

(defun exec-delete (st)
  (destructuring-bind (&key with table schema alias where returning) (cdr st)
    (let* ((*ctes* *ctes*)
           (tb (progn (when with (register-ctes (make-sel :with (first with) :recursive (second with))))
                      (writable-table table :delete schema)))
           (view (table-view-select tb))
           (triggers (table-has-triggers-p tb)))
      (multiple-value-bind (ctx rnames) (make-ctx-for tb nil returning alias)
        (if (and (null where) (null returning) (not triggers) (not view)
                 (not (and (fk-enabled-p) (referencing-keys tb))))
            ;; truncate: drop every page but the roots
            (let ((n 0))
              (map-table-rows tb (lambda (row) (declare (ignore row)) (incf n)))
              (clear-btree (table-owner tb) (table-root tb) :keep-root t)
              (dolist (idx (table-indexes tb))
                (unless (index-pk-index idx)
                  (clear-btree (table-owner tb) (index-root idx) :keep-root t)))
              (setf (wc-changes ctx) n))
            (dolist (row (scan-table-rows tb alias where))
              (cond
                (view (fire-triggers tb :delete :instead-of row nil)
                      (incf (wc-changes ctx)))
                ((and triggers (eq :ignore (fire-triggers tb :delete :before row nil))))
                ((and triggers (not (table-without-rowid tb))
                      (not (table-lookup (table-owner tb) (table-root tb) (svref row (length (table-columns tb)))))))
                (t (fk-parent-delete tb row)
                   (delete-row tb row)
                   (incf (wc-changes ctx))
                   (collect-returning ctx row)
                   (when triggers (fire-triggers tb :delete :after row nil))))))
        (setf (db-changes (conn *db*)) (wc-changes ctx))
        (incf (db-total-changes (conn *db*)) (wc-changes ctx))
        (values (reverse (wc-returned ctx)) rnames)))))
