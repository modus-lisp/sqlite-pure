;;;; where.lisp — the query planner: a port of SQLite 3.40's where.c.
;;;;
;;;; For a FROM clause and its WHERE/ON conjuncts this builds what SQLite
;;;; builds: the WHERE terms (with their commuted, BETWEEN and IS NOT NULL
;;;; children), every candidate WhereLoop for every source (full scans,
;;;; covering-index scans, rowid and index lookups with equality, IN, range
;;;; and IS NULL constraints, automatic indexes) costed in LogEst units by
;;;; SQLite's formulas, and the path solver that picks a join order and one
;;;; loop per source, accounting for the cost of sorting when an ORDER BY,
;;;; GROUP BY or DISTINCT is not satisfied by the order the loops deliver.
;;;; The chosen plan is then run as nested loops (select.lisp) and described
;;;; for EXPLAIN QUERY PLAN in SQLite's words.
;;;;
;;;; Every conjunct is still evaluated as a filter at the loop where its
;;;; sources are all bound, so an access path only narrows the candidate
;;;; rows; what the plan decides is how much work is done and, where the
;;;; statement leaves it open, the order in which rows appear.

(in-package #:sqlite-pure)

(defvar *or-branch-plan* nil
  "Planning one disjunct of a MULTI-INDEX OR (WHERE_OR_SUBCLAUSE): no
automatic indexes.")

(defvar *where-trace* (sb-ext:posix-getenv "SQLP_WHERETRACE")
  "Print every WhereLoop, like SQLite's .wheretrace (for comparing costs).")

;;; ------------------------------------------------------------------
;;; LogEst: 10*log2(x) as SQLite estimates it

(defparameter +log-est-add-table+
  #(10 10 9 9 8 8 7 7 7 6 6 6 5 5 5 4 4 4 4 3 3 3 3 3 3 2 2 2 2 2 2 2))

(defun log-est-add (a b)
  "sqlite3LogEstAdd: the LogEst of the sum of the values A and B stand for."
  (if (>= a b)
      (cond ((> a (+ b 49)) a) ((> a (+ b 31)) (1+ a)) (t (+ a (svref +log-est-add-table+ (- a b)))))
      (cond ((> b (+ a 49)) b) ((> b (+ a 31)) (1+ b)) (t (+ b (svref +log-est-add-table+ (- b a)))))))

(defun est-log (n)
  "estLog: LogEst of the logarithm of the row count N (a LogEst)."
  (if (<= n 10) 0 (- (log-est n) 33)))

;;; WhereLoop.wsFlags
(defconstant +where-column-eq+    #x1)
(defconstant +where-column-range+ #x2)
(defconstant +where-column-in+    #x4)
(defconstant +where-column-null+  #x8)
(defconstant +where-constraint+   #xf)
(defconstant +where-top-limit+    #x10)
(defconstant +where-btm-limit+    #x20)
(defconstant +where-both-limit+   #x30)
(defconstant +where-idx-only+     #x40)
(defconstant +where-ipk+          #x100)
(defconstant +where-indexed+      #x200)
(defconstant +where-virtualtable+ #x400)
(defconstant +where-onerow+       #x1000)
(defconstant +where-multi-or+     #x2000)
(defconstant +where-auto-index+   #x4000)
(defconstant +where-unq-wanted+   #x10000)
(defconstant +where-partialidx+   #x20000)
(defconstant +where-transcons+    #x200000)
(defconstant +where-selfcull+     #x800000)
(defconstant +where-viewscan+     #x2000000)

(defmacro flag-p (flags bit) `(logtest ,flags ,bit))

;;; sqlite3WhereBegin's wctrlFlags that planning looks at
(defconstant +wf-groupby+     #x40)
(defconstant +wf-distinctby+  #x80)
(defconstant +wf-want-distinct+ #x100)
(defconstant +wf-sortbygroup+ #x200)
(defconstant +wf-orderby-limit+ #x800)
(defconstant +wf-onepass-desired+ #x4)
(defconstant +wf-use-limit+   #x4000)
(defconstant +wf-orderby-min+ #x1)
(defconstant +wf-orderby-max+ #x2)



;;; ------------------------------------------------------------------
;;; Sources and indexes as the planner sees them

(defstruct (wsrc (:conc-name ws-))
  i fsrc table
  kind            ; :btree (a stored table), :derived (subquery, view, CTE), :vtab
  mask join       ; bit for this FROM position; :first :inner :comma :cross :left :right :full
  row-est         ; Table.nRowLogEst
  sz-row          ; Table.szTabRow
  probes          ; list of WIDX in the order SQLite tries them
  col-used        ; bit vector of columns the query reads, or :ALL
  view-p          ; view or subquery: WHERE_VIEWSCAN, cheaper automatic indexes
  auto-ok         ; automatic indexes may be built on it
  indexed-by not-indexed
  auto-partial    ; terms an automatic index on it is restricted by
  (extra-prereq 0)) ; sources a table-valued function's arguments read

(defstruct (widx (:conc-name wx-))
  index           ; the INDEX, or NIL for the rowid (IPK) pseudo-index
  ipk pk          ; rowid pseudo-index; a WITHOUT ROWID table's key
  auto            ; an automatic index (built by EXPLAIN only for its name)
  cols            ; vector: column index, :ROWID, or an expression AST
  n-key n-col
  colls descs     ; vectors
  row-est         ; aiRowLogEst
  unique uniq-not-null on-error
  sz-row partial name
  alias)          ; the table's INTEGER PRIMARY KEY column, which reads as the rowid

(defun ws-rowid-table-p (ws)
  (or (eq (ws-kind ws) :derived)
      (and (ws-table ws) (not (table-without-rowid (ws-table ws))))))

(defun column-szest (table ci)
  (column-size-estimate (column-type (aref (table-columns table) ci))))

(defun make-probes (table row-est sz-tab)
  "The rowid pseudo-index (for rowid tables) and the real indexes, in
SQLite's pIndex order."
  (let ((out '()))
    (dolist (idx (sqlite-index-list table))
      (push (index-widx table idx row-est) out))
    (let ((real (nreverse out)))
      (if (table-without-rowid table)
          real
          (cons (make-widx :ipk t :cols (vector :rowid) :n-key 1 :n-col 1
                           :colls (vector :binary) :descs (vector nil)
                           :row-est (vector row-est 0) :unique t :uniq-not-null t
                           :on-error :replace :sz-row sz-tab :name nil)
                real)))))

(defun index-widx (table idx row-est)
  (let* ((key (index-columns idx))
         (n-key (length key))
         (cols (mapcar #'first key))
         (colls (mapcar #'second key))
         (descs (mapcar #'third key))
         (pk (index-pk-index idx)))
    ;; the columns after the key: the rowid, or the WITHOUT ROWID primary key
    (cond ((not (table-without-rowid table))
           (setf cols (append cols (list :rowid)) colls (append colls (list :binary))
                 descs (append descs (list nil))))
          (pk
           (loop for i below (length (table-columns table))
                 unless (member i (table-pk table))
                   do (setf cols (append cols (list i)) colls (append colls (list :binary))
                            descs (append descs (list nil)))))
          (t
           (dolist (p (table-pk table))
             (unless (member p (subseq cols 0 n-key))
               (setf cols (append cols (list p))
                     colls (append colls (list (column-collation (aref (table-columns table) p))))
                     descs (append descs (list nil)))))))
    (let* ((unique (or pk (index-unique idx)))
           ;; sized for every column and zeroed, as sqlite3AllocateIndexObject does
           (a (make-array (1+ (length cols)) :initial-element 0))
           (x (max row-est 99)))
      ;; sqlite3DefaultRowEst
      (when (index-where idx) (decf x 10))
      (setf (aref a 0) x)
      (loop for k from 1 to n-key
            do (setf (aref a k) (if (<= k 5) (nth (1- k) '(33 32 30 28 26)) 23)))
      (when unique (setf (aref a n-key) 0))
      (make-widx :index idx :pk pk :alias (table-rowid-alias table)
                 :cols (coerce cols 'vector) :n-key n-key :n-col (length cols)
                 :colls (coerce colls 'vector) :descs (coerce descs 'vector)
                 :row-est a :unique unique
                 :uniq-not-null (and unique
                                     (or pk
                                         (loop for c in (subseq cols 0 n-key)
                                               always (or (eq c :rowid)
                                                          (and (integerp c)
                                                               (column-not-null (aref (table-columns table) c)))))))
                 :on-error (if unique :abort nil)
                 :sz-row (log-est (* 4 (loop for c in cols
                                             sum (if (integerp c) (column-szest table c) 1))))
                 :partial (index-where idx)
                 :name (index-name idx)))))

(defun widx-col (wx j) (svref (wx-cols wx) j))

(defun widx-key-col (wx j)
  "Column J of WX as terms and ORDER BY name it: the INTEGER PRIMARY KEY
column is the rowid."
  (let ((c (svref (wx-cols wx) j)))
    (if (and (integerp c) (eql c (wx-alias wx))) :rowid c)))

(defun widx-covers-p (ws wx)
  "Does index WX hold every column the query reads from WS?"
  (let ((used (ws-col-used ws)) (table (ws-table ws)))
    (cond ((wx-ipk wx) t)
          ((wx-pk wx) t)
          ((eq used :all) nil)
          (t (loop for ci below (length used)
                   always (or (zerop (sbit used ci))
                              (eql ci (table-rowid-alias table))
                              ;; a UNIQUE constraint's index in a WITHOUT ROWID
                              ;; table gets the key columns appended after its
                              ;; colNotIdxed is computed: they do not count
                              (find ci (wx-cols wx)
                                    :end (and (table-without-rowid table) (wx-index wx)
                                              (index-auto (wx-index wx))
                                              (wx-n-key wx)))))))))

;;; ------------------------------------------------------------------
;;; WHERE-clause constant propagation (propagateConstants in select.c)

(defun substitute-fixed (e)
  "E with every fixed column node replaced by its constant (as the code
SQLite generates for an EP_FixedCol column reads the constant)."
  (cond ((or (null *fixed-cols*) (zerop (hash-table-count *fixed-cols*)) (atom e)) e)
        ((gethash e *fixed-cols*))
        ((member (car e) '(:subquery :exists)) e)
        (t (let ((new (mapcar #'substitute-fixed e)))
             (if (every #'eq new e) e new)))))

(defun fixed-col-p (node)
  "Is NODE a column that constant propagation fixed (EP_FixedCol)?"
  (and *fixed-cols* (gethash node *fixed-cols*)))

(defun propagate-constants (conjunct-trees scope)
  "For each COLUMN = <literal> among the top-level AND terms of the WHERE
clause (and the inner joins' ON clauses), mark the other references to
that column in those clauses as fixed.  A fixed column is still read and
compared as before (its value is the literal wherever the clause holds);
what changes is that the planner no longer counts it as a use of its
table.  Returns the set of fixed column nodes."
  (let ((fixed (make-hash-table :test #'eq)))
    (let ((*fixed-cols* fixed))
      (loop
        (let ((consts '()) (has-blob nil) (changes 0))
          (labels ((col-aff (e) (expr-affinity e scope))
                   (insert (col value e)
                     (unless (or (fixed-col-p col)
                                 ;; constInsert: a value with an affinity -- and
                                 ;; any column has one -- is not propagated
                                 (member (car (skip-collate value)) '(:col :srccol))
                                 (expr-affinity value scope)
                                 (not (eq (binary-collation (third e) (fourth e) scope) :binary)))
                       (multiple-value-bind (s c) (column-ref col scope)
                         (when (and s (not (find-if (lambda (k) (and (= (first k) s) (eql (second k) c))) consts)))
                           (when (member (col-aff col) '(:blob nil)) (setf has-blob t))
                           (setf consts (append consts (list (list s c col (col-aff col) value))))))))
                   (find-consts (e)
                     (cond ((null e))
                           ((eq (car e) :outer-on))
                           ((and (eq (car e) :binary) (eq (second e) :and))
                            (find-consts (fourth e)) (find-consts (third e)))
                           ((and (eq (car e) :binary) (eq (second e) :eq))
                            (let ((l (third e)) (r (fourth e)))
                              (when (and (member (car r) '(:col :srccol)) (constant-or-fixed-p l))
                                (insert r l e))
                              (when (and (member (car l) '(:col :srccol)) (constant-or-fixed-p r))
                                (insert l r e))))))
                   (constant-or-fixed-p (e)
                     (cond ((member (car e) '(:col :srccol)) (fixed-col-p e))
                           (t (parse-constant-p e))))
                   (rewrite-one (e ignore-blob)
                     (when (and (member (car e) '(:col :srccol)) (not (fixed-col-p e)))
                       (multiple-value-bind (s c) (column-ref e scope)
                         (when s
                           (dolist (k consts)
                             (when (and (not (eq (third k) e)) (= (first k) s) (eql (second k) c))
                               (unless (and ignore-blob (member (fourth k) '(:blob nil)))
                                 ;; the node now reads as the constant, with its
                                 ;; own column's affinity and collation
                                 (setf (gethash e fixed)
                                       (list :affine (fifth k) (col-aff e)
                                             (or (expr-collation e scope) :binary)))
                                 (incf changes))
                               (return)))))))
                   (walk (e)
                     (when (consp e)
                       (case (car e)
                         ((:subquery :exists :outer-on) nil)
                         ((:col :srccol) (rewrite-one e has-blob))
                         (t
                          (when (and has-blob (eq (car e) :binary)
                                     (member (second e) '(:eq :lt :le :gt :ge :is)))
                            (rewrite-one (third e) nil)
                            (unless (eq (col-aff (third e)) :text)
                              (rewrite-one (fourth e) nil)))
                          (when (and (eq (car e) :in) (not (eq (car (third e)) :select)))
                            nil)
                          (mapc #'walk (cdr e)))))))
            (dolist (tree conjunct-trees) (find-consts tree))
            (when consts
              (dolist (tree conjunct-trees) (walk tree))))
          (when (zerop changes) (return)))))
    fixed))

;;; ------------------------------------------------------------------
;;; WHERE terms (whereexpr.c)

(defstruct (wterm (:conc-name wt-))
  expr            ; the comparison, as analyzed
  origin          ; the conjunct evaluated as a filter (NIL for virtual terms)
  op              ; :eq :is :lt :le :gt :ge :in :isnull, or NIL
  equiv           ; WO_EQUIV: col = col with matching affinity and collation
  src col         ; the column side: FROM position and column (:ROWID or index)
  rhs             ; the other operand; for :IN the (:list ...) or (:select ...)
  coll aff        ; comparison collation and affinity
  (prereq-right 0) (prereq-all 0)
  virtual parent vnull
  (truth 1)       ; truthProb: <= 0 from likelihood(), else 1
  heurtruth
  outer-on inner-on  ; FROM position of the join whose ON clause this is from
  constraint-mask ; the tables a folded x IS NULL still mentions
  base            ; one of the original (non-virtual) conjuncts
  copied          ; TERM_COPIED: col = col with a commuted virtual copy
  or-wc           ; an OR term: its disjuncts, a WCLAUSE (WhereOrInfo)
  (indexable 0)   ; ... and the tables every disjunct can index
  and-wc)         ; a disjunct of several ANDed terms: them (WhereAndInfo)

(defstruct (wclause (:conc-name wc-))
  (terms (make-array 0 :adjustable t :fill-pointer t))
  scope nsrc
  outer           ; pOuter: the clause an OR disjunct's terms are nested in
  (op :and))      ; :or for an OR term's disjuncts

(defun skip-collate (e)
  (loop while (and (consp e) (member (car e) '(:collate :icollate))) do (setf e (second e)))
  e)

(defun likelihood-wrapper (e)
  "(values inner probability-int) when E is likely(X)/unlikely(X)/likelihood(X,P)."
  (when (and (consp e) (eq (car e) :fn) (stringp (second e)))
    (let ((n (string-downcase-ascii (second e))) (args (third e)))
      (cond ((and (string= n "likely") (= (length args) 1)) (values (first args) 125829120))
            ((and (string= n "unlikely") (= (length args) 1)) (values (first args) 8388608))
            ((and (string= n "likelihood") (= (length args) 2)
                  (eq (car (second args)) :lit) (realp (second (second args))))
             (values (first args) (truncate (* (second (second args)) 134217728.0d0))))))))

(defvar *usage-cache* nil)

(defun subquery-correlated-p (sel scope)
  (let ((key sel))
    (multiple-value-bind (v hit) (and *usage-cache* (gethash key *usage-cache*))
      (if hit
          v
          (let ((c (ignore-errors
                    (third (multiple-value-list (without-eqp (compile-subselect sel scope)))))))
            (when *usage-cache* (setf (gethash key *usage-cache*) c))
            c)))))

(defun expr-usage (e scope nsrc)
  "Bitmask of the FROM sources E reads (sqlite3WhereExprUsage); a
correlated subquery counts as reading all of them."
  (let ((m 0) (all (1- (ash 1 nsrc))))
    (labels ((walk (x)
               (when (consp x)
                 (case (car x)
                   (:col (multiple-value-bind (depth si) (resolve-column scope (second x) (third x))
                           (cond ((fixed-col-p x) nil)
                                 ((and depth (= depth 0)) (setf m (logior m (ash 1 si))))
                                 ((and (null depth) (null (second x)) (alias-expr scope (third x)))
                                  (walk (alias-expr scope (third x)))))))
                   (:srccol (unless (fixed-col-p x) (setf m (logior m (ash 1 (second x))))))
                   ;; IF_NULL_ROW reads its table's row
                   (:ifnullrow (let ((si (position (second x) (scope-srcs scope)
                                                   :key #'src-name :test #'equal)))
                                 (when si (setf m (logior m (ash 1 si))))
                                 (walk (third x))))
                   ((:subquery :exists) (when (subquery-correlated-p (second x) scope)
                                          (setf m all)))
                   (:in (walk (second x))
                    (let ((rhs (third x)))
                      (if (eq (car rhs) :list)
                          (mapc #'walk (second rhs))
                          (when (or (not (eq (car rhs) :select))
                                    (subquery-correlated-p (second rhs) scope))
                            (setf m all)))))
                   (:fn (mapc #'walk (third x)) (walk (fifth x)) (walk (sixth x)))
                   (:case (walk (second x))
                    (loop for (w th) in (third x) do (walk w) (walk th))
                    (walk (fourth x)))
                   (:lit nil)
                   (t (mapc #'walk (cdr x)))))))
      (walk e))
    m))

(defun column-ref (e scope)
  "(values src col) when E (COLLATE skipped) is a column of this FROM
clause; col is :ROWID for the rowid and for an INTEGER PRIMARY KEY column."
  (let ((e (skip-collate e)))
    (multiple-value-bind (depth si ci)
        (case (car e)
          (:col (resolve-column scope (second e) (third e)))
          (:srccol (values 0 (second e) (third e))))
      (when (and depth (= depth 0))
        (let* ((s (nth si (scope-srcs scope)))
               (table (src-table s)))
          (values si (if (and table (integerp ci) (eql ci (table-rowid-alias table)))
                         :rowid
                         ci)))))))

(defun null-literal-p (e) (and (consp e) (eq (car e) :lit) (eq (second e) :null)))

(defun integer-literal-value (e)
  "sqlite3ExprIsInteger: the value of an integer literal (or its negation)."
  (cond ((and (eq (car e) :lit) (integerp (second e)) (typep (second e) '(signed-byte 32))) (second e))
        ((and (eq (car e) :unary) (eq (second e) :neg))
         (let ((v (integer-literal-value (third e)))) (and v (- v))))
        ((and (eq (car e) :unary) (eq (second e) :pos)) (integer-literal-value (third e)))))

(defun numeric-aff-p (a) (member a '(:numeric :integer :real)))

(defun term-cmp-affinity (lhs rhs scope)
  "comparisonAffinity: the affinity the comparison applies."
  (let ((a (expr-affinity lhs scope)))
    (cond ((eq (car rhs) :list) (or a :blob))
          ((eq (car rhs) :select) (comparison-affinity (select-first-affinity (second rhs) scope) a))
          (rhs (comparison-affinity (expr-affinity rhs scope) a))
          (t (or a :blob)))))

(defun index-affinity-ok-p (term idx-aff)
  "sqlite3IndexAffinityOk."
  (let ((aff (wt-aff term)))
    (cond ((member aff '(nil :blob)) t)
          ((eq aff :text) (eq idx-aff :text))
          (t (numeric-aff-p idx-aff)))))

(defun commute-op (op)
  (case op (:lt :gt) (:le :ge) (:gt :lt) (:ge :le) (t op)))

(defun add-wterm (wc term)
  (vector-push-extend term (wc-terms wc))
  term)

(defun term-is-equivalence-p (lhs rhs op outer scope)
  "termIsEquivalence."
  (and (member op '(:eq :is))
       (not outer)
       (let ((a1 (expr-affinity lhs scope)) (a2 (expr-affinity rhs scope)))
         (or (eq a1 a2) (and (numeric-aff-p a1) (numeric-aff-p a2))))
       (let ((c (binary-collation lhs rhs scope)))
         (or (eq c :binary)
             (collation= (or (expr-collation lhs scope) :binary)
                         (or (expr-collation rhs scope) :binary))))))

(defun make-child-term (wc e parent)
  "A virtual term (a BETWEEN half) inserted and analyzed at once."
  (let ((term (make-wterm :expr e :virtual t :parent parent
                          :outer-on (wt-outer-on parent) :inner-on (wt-inner-on parent))))
    (add-wterm wc term)
    (analyze-term wc term)
    term))

(defun operand-can-be-null-p (x scope)
  "sqlite3ExprCanBeNull as the planner sees it: after outer-join
simplification, a column of a table an outer join can still make NULL
can be NULL whatever its declaration."
  (loop while (and (consp x) (eq (car x) :unary) (member (second x) '(:pos :neg)))
        do (setf x (third x)))
  (case (car x)
    (:lit (eq (second x) :null))
    ((:col :srccol)
     (multiple-value-bind (si ci) (column-ref x scope)
       (or (null si)
           (let ((n (length *wsrcs*)))
             (or (member (ws-join (svref *wsrcs* si)) '(:left :full))
                 (loop for k from (1+ si) below n
                       thereis (member (ws-join (svref *wsrcs* k)) '(:right :full)))))
           (column-can-be-null-p si ci scope))))
    (t t)))

(defun analyze-term (wc term)
  "exprAnalyze: fill in TERM (already in the clause) and append its
virtual children."
  (let* ((scope (wc-scope wc)) (n (wc-nsrc wc))
         (e (wt-expr term))
         (outer-on (wt-outer-on term))
         (extra-right 0))
    (multiple-value-bind (inner prob) (likelihood-wrapper e)
      (when inner
        (setf e inner (wt-truth term) (- (log-est (max 1 prob)) 270))))
    ;; x IS NULL / x IS NOT NULL are parsed as IS against a NULL literal
    (when (and (eq (car e) :binary) (member (second e) '(:is :isnot)) (null-literal-p (fourth e)))
      (setf e (list :isnull (third e) (eq (second e) :isnot))))
    (setf (wt-expr term) e)
    (let* ((kind (car e))
           (lhs (case kind (:binary (third e)) ((:in :isnull :between) (second e))))
           (prereq-left (if lhs (expr-usage lhs scope n) 0)))
      (multiple-value-bind (op rhs)
          (cond ((and (eq kind :binary) (member (second e) '(:eq :lt :le :gt :ge :is)))
                 (values (second e) (fourth e)))
                ((and (eq kind :in) (not (fourth e))) (values :in (third e)))
                ((and (eq kind :isnull) (not (third e))) (values :isnull nil))
                (t (values nil nil)))
        (let* ((prereq-right (cond ((eq op :in)
                                    (if (eq (car rhs) :list)
                                        (reduce #'logior (second rhs) :key (lambda (x) (expr-usage x scope n))
                                                :initial-value 0)
                                        (if (and (eq (car rhs) :select)
                                                 (not (subquery-correlated-p (second rhs) scope)))
                                            0
                                            (1- (ash 1 n)))))
                                   (rhs (expr-usage rhs scope n))
                                   (t 0)))
               (prereq-all (if op (logior prereq-left prereq-right) (expr-usage e scope n))))
          (when outer-on
            (let ((x (ash 1 outer-on)))
              (setf prereq-all (logior prereq-all x) extra-right (1- x))))
          (when (and (wt-inner-on term) (>= (ash prereq-all -1) (ash 1 (wt-inner-on term))))
            (setf (wt-inner-on term) nil))
          (setf (wt-prereq-right term) prereq-right
                (wt-prereq-all term) prereq-all)
          (when op
            (let ((ok (zerop (logand prereq-right prereq-left))))
              (multiple-value-bind (lsrc lcol) (column-ref lhs scope)
                (when lsrc
                  (setf (wt-src term) lsrc (wt-col term) lcol
                        (wt-op term) (and ok op)
                        (wt-rhs term) rhs
                        (wt-coll term) (if (and rhs (not (eq op :in)))
                                           (binary-collation lhs rhs scope)
                                           (or (expr-collation lhs scope) :binary))
                        (wt-aff term) (term-cmp-affinity lhs rhs scope))))
              ;; x IS NULL where x cannot be NULL once outer joins are
              ;; simplified: FALSE, needing no table -- though, its operand
              ;; kept, it still reads x's table (sqlite3ExprIsTableConstraint)
              (when (and (eq op :isnull) (not outer-on) (not (operand-can-be-null-p lhs scope)))
                (setf (wt-constraint-mask term) prereq-all
                      (wt-op term) nil
                      (wt-prereq-all term) 0))
              ;; col op col: a commuted copy lets the right column drive an index
              (when (and rhs (not (member op '(:in :isnull))) (not (fixed-col-p (skip-collate rhs))))
                (multiple-value-bind (rsrc rcol) (column-ref rhs scope)
                  (when rsrc
                    (let ((equiv (and (wt-src term)
                                      (term-is-equivalence-p lhs rhs op outer-on scope)))
                          (new (if (wt-src term)
                                   (add-wterm wc (make-wterm :expr e :virtual t :parent term
                                                             :truth (wt-truth term) :outer-on outer-on
                                                             :inner-on (wt-inner-on term)))
                                   term)))
                      (when equiv (setf (wt-equiv term) t))
                      (unless (eq new term) (setf (wt-copied term) t))
                      (setf (wt-src new) rsrc (wt-col new) rcol
                            (wt-op new) (and ok (commute-op op))
                            (wt-rhs new) lhs
                            (wt-equiv new) equiv
                            (wt-coll new) (binary-collation lhs rhs scope)
                            (wt-aff new) (term-cmp-affinity lhs rhs scope)
                            (wt-prereq-right new) (logior prereq-left extra-right)
                            (wt-prereq-all new) prereq-all)))))
              ;; x IS NULL on a column that cannot be NULL is FALSE
              (when (and (eq op :isnull) (wt-src term) (not outer-on)
                         (not (column-can-be-null-p (wt-src term) (wt-col term) scope)))
                (setf (wt-op term) nil (wt-prereq-all term) 0))))))
      (cond
        ;; BETWEEN: two virtual range terms (in an AND clause)
        ((and (eq kind :between) (not (fifth e)) (eq (wc-op wc) :and))
         (make-child-term wc (list :binary :ge (second e) (third e)) term)
         (make-child-term wc (list :binary :le (second e) (fourth e)) term))
        ;; x OR y OR ...: WhereOrInfo, and perhaps x IN (...) or x>=A
        ((and (eq kind :binary) (eq (second e) :or) (eq (wc-op wc) :and))
         (analyze-or-term wc term))
        ;; x IS NOT NULL: a virtual x>NULL (TERM_VNULL) an index can use
        ((and (eq kind :isnull) (third e) (not outer-on))
         (multiple-value-bind (src col) (column-ref (second e) scope)
           (when (and src (integerp col) (not (eq (car (second e)) :collate)))
             (add-wterm wc (make-wterm :expr (list :binary :gt (second e) (list :lit :null))
                                       :op :gt :src src :col col :rhs (list :lit :null)
                                       :virtual t :parent term :vnull t
                                       :coll (or (expr-collation (second e) scope) :binary)
                                       :aff (expr-affinity (second e) scope)
                                       :prereq-right 0 :prereq-all (wt-prereq-all term)
                                       :outer-on outer-on :inner-on (wt-inner-on term)))))))
      (setf (wt-prereq-right term) (logior (wt-prereq-right term) extra-right))
      term)))

(defun column-can-be-null-p (si ci scope)
  (let* ((s (nth si (scope-srcs scope))) (table (src-table s)))
    (not (and table (or (eq ci :rowid)
                        (and (integerp ci) (column-not-null (aref (table-columns table) ci))))))))

(defun analyze-where (conjuncts scope nsrc)
  "sqlite3WhereSplit + sqlite3WhereExprAnalyze.  CONJUNCTS: list of
(ast outer-on inner-on), the WHERE conjuncts then each join's ON conjuncts.
Every base term is inserted first, then they are analyzed last to first,
each appending its virtual children."
  (let ((wc (make-wclause :scope scope :nsrc nsrc)))
    (dolist (c conjuncts)
      (destructuring-bind (e outer inner) c
        (add-wterm wc (make-wterm :expr e :origin e :outer-on outer :inner-on inner :base t))))
    (loop for i from (1- (length conjuncts)) downto 0
          do (analyze-term wc (aref (wc-terms wc) i)))
    wc))

(defun term-rhs-column (term)
  "whereRightSubexprIsColumn: (src . col) when the value side is a column."
  (let ((rhs (wt-rhs term)))
    (when (and rhs (not (eq (car rhs) :list)) (not (eq (car rhs) :select))
               (not (fixed-col-p (skip-collate rhs))))
      (multiple-value-bind (s c) (column-ref rhs (wc-scope *wc*))
        (and s (cons s c))))))

(defvar *wc* nil "The WHERE clause being planned.")

(defun where-scan (src col ops &optional wx j)
  "whereScanInit/whereScanNext: the terms of the form X op <expr>, where X
is column COL of source SRC (or column J of index WX) or a column
known equal to it through col=col terms.  Returns (term . via-equivalence)
pairs in SQLite's order."
  (let ((idx-aff nil) (idx-coll nil)
        (equivs (list (cons src col)))
        (out '()))
    (when wx
      (let ((c (widx-key-col wx j)))
        (setf col c
              equivs (list (cons src c)))
        (when (integerp c)
          (let ((table (ws-table (svref *wsrcs* src))))
            (setf idx-aff (column-affinity (aref (table-columns table) c))
                  idx-coll (svref (wx-colls wx) j))))
        (when (wx-auto wx) (setf idx-coll nil))))
    (when (consp col) (return-from where-scan nil))  ; indexes on expressions: not yet
    (let ((i-equiv 0))
      (loop
        (when (>= i-equiv (length equivs)) (return))
        (destructuring-bind (cur . c) (nth i-equiv equivs)
          (loop for wc = *wc* then (wc-outer wc)
                while wc
                do (loop for term across (wc-terms wc)
                do (when (and (eql (wt-src term) cur) (eql (wt-col term) c)
                              (or (zerop i-equiv) (not (wt-outer-on term))))
                     (when (and (wt-equiv term) (< (length equivs) 11))
                       (let ((x (term-rhs-column term)))
                         (when (and x (not (member x equivs :test #'equal)))
                           (setf equivs (append equivs (list x))))))
                     (when (and (wt-op term) (member (wt-op term) ops))
                       (block check
                         (when (and idx-coll (not (eq (wt-op term) :isnull)))
                           (unless (index-affinity-ok-p term idx-aff) (return-from check))
                           (unless (collation= (wt-coll term) idx-coll) (return-from check)))
                         ;; X = <the column scanned for> (the raw right
                         ;; operand: a constant-propagated column still counts)
                         (when (member (wt-op term) '(:eq :is))
                           (let ((rhs (wt-rhs term)))
                             (when (and (consp rhs) (member (car rhs) '(:col :srccol)))
                               (multiple-value-bind (s c) (column-ref rhs (wc-scope *wc*))
                                 (when (and s (equal (cons s c) (first equivs)))
                                   (return-from check))))))
                         (push (cons term (plusp i-equiv)) out)))))))
        (incf i-equiv)))
    (nreverse out)))

(defvar *wsrcs* nil "Vector of WSRC for the FROM clause being planned.")

(defun where-find-term (src col not-ready ops)
  "sqlite3WhereFindTerm: prefer a term with a constant right side."
  (let ((result nil))
    (dolist (p (where-scan src col ops) result)
      (let ((term (car p)))
        (when (zerop (logand (wt-prereq-right term) not-ready))
          (when (and (zerop (wt-prereq-right term)) (member (wt-op term) '(:eq :is)))
            (return term))
          (unless result (setf result term)))))))

;;; ------------------------------------------------------------------
;;; WhereLoops

(defstruct (wloop (:conc-name wl-))
  src mask (prereq 0)
  (flags 0)
  wx                ; WIDX (NIL for virtual tables)
  (n-eq 0) (n-btm 0) (n-top 0)
  (lterms '())      ; terms used, in order: n-eq equality terms, then btm, then top
  (r-setup 0) (r-run 0) (n-out 0)
  (sort-idx 0)
  vtab)             ; virtual table plan (see vtab-where-loop)

(defun copy-wloop* (l)
  (let ((c (copy-wloop l))) (setf (wl-lterms c) (copy-list (wl-lterms l))) c))

(defstruct (wbuilder (:conc-name wb-))
  (loops '())       ; pWInfo->pLoops, in order
  (sort-idx 0)      ; pNew->iSortIdx: one template loop is reused for every
                    ; table and index, and this field is only set on some paths
  order-by          ; list of OBTERM (ORDER BY, GROUP BY or DISTINCT list), or NIL
  (flags 0)         ; wctrlFlags
  limit             ; iLimit (LogEst) for WHERE_USE_LIMIT
  or-set            ; pOrSet: (vector of (prereq r-run n-out)), in an OR sub-build
  main)             ; ... and the builder whose loops the sub-build adjusts against

(defun loop-cheaper-proper-subset-p (x y)
  "whereLoopCheaperProperSubset."
  (and (< (length (wl-lterms x)) (length (wl-lterms y)))
       (not (and (> (wl-r-run x) (wl-r-run y)) (> (wl-n-out x) (wl-n-out y))))
       (every (lambda (tm) (or (null tm) (member tm (wl-lterms y)))) (wl-lterms x))
       (not (and (flag-p (wl-flags x) +where-idx-only+)
                 (not (flag-p (wl-flags y) +where-idx-only+))))))

(defun loop-adjust-cost (loops tmpl)
  "whereLoopAdjustCost."
  (when (flag-p (wl-flags tmpl) +where-indexed+)
    (dolist (p loops)
      (when (and (eql (wl-src p) (wl-src tmpl)) (flag-p (wl-flags p) +where-indexed+))
        (cond ((loop-cheaper-proper-subset-p p tmpl)
               (setf (wl-r-run tmpl) (min (wl-r-run p) (wl-r-run tmpl))
                     (wl-n-out tmpl) (min (1- (wl-n-out p)) (wl-n-out tmpl))))
              ((loop-cheaper-proper-subset-p tmpl p)
               (setf (wl-r-run tmpl) (max (wl-r-run p) (wl-r-run tmpl))
                     (wl-n-out tmpl) (max (1+ (wl-n-out p)) (wl-n-out tmpl)))))))))

(defun loop-find-lesser (loops tmpl)
  "whereLoopFindLesser over the list LOOPS: :DISCARD, a loop to replace, or
NIL (append)."
  (dolist (p loops nil)
    (when (and (eql (wl-src p) (wl-src tmpl)) (eql (wl-sort-idx p) (wl-sort-idx tmpl)))
      (when (and (flag-p (wl-flags p) +where-auto-index+)
                 (flag-p (wl-flags tmpl) +where-indexed+)
                 (flag-p (wl-flags tmpl) +where-column-eq+)
                 (= (logand (wl-prereq p) (wl-prereq tmpl)) (wl-prereq tmpl)))
        (return p))
      (when (and (= (logand (wl-prereq p) (wl-prereq tmpl)) (wl-prereq p))
                 (<= (wl-r-setup p) (wl-r-setup tmpl))
                 (<= (wl-r-run p) (wl-r-run tmpl))
                 (<= (wl-n-out p) (wl-n-out tmpl)))
        (return :discard))
      (when (and (= (logand (wl-prereq p) (wl-prereq tmpl)) (wl-prereq tmpl))
                 (>= (wl-r-run p) (wl-r-run tmpl))
                 (>= (wl-n-out p) (wl-n-out tmpl)))
        (return p)))))

(defun loop-insert (b tmpl)
  "whereLoopInsert."
  (when (wb-or-set b)
    ;; an OR disjunct's sub-build keeps only the costs (whereOrInsert)
    (loop-adjust-cost (wb-loops (wb-main b)) tmpl)
    (when (wl-lterms tmpl)
      (when *where-trace*
        (format *error-output* "~&       or: ")
        (trace-loop tmpl))
      (or-set-insert b (wl-prereq tmpl) (wl-r-run tmpl) (wl-n-out tmpl)))
    (return-from loop-insert nil))
  (loop-adjust-cost (wb-loops b) tmpl)
  (let ((p (loop-find-lesser (wb-loops b) tmpl)))
    (when *where-trace*
      (format *error-output* "~&  ~a " (cond ((eq p :discard) "   skip:") ((null p) "    add:") (t "replace:")))
      (trace-loop tmpl))
    (cond ((eq p :discard))
          ((null p) (setf (wb-loops b) (append (wb-loops b) (list (copy-wloop* tmpl)))))
          (t
           ;; replace P, and drop any later loop the template also beats
           (let* ((pos (position p (wb-loops b)))
                  (tail (nthcdr (1+ pos) (wb-loops b)))
                  (keep '()))
             (loop while tail
                   do (let ((q (loop-find-lesser tail tmpl)))
                        (cond ((or (null q) (eq q :discard))
                               (setf keep (append keep tail) tail nil))
                              (t (let ((qpos (position q tail)))
                                   (setf keep (append keep (subseq tail 0 qpos))
                                         tail (nthcdr (1+ qpos) tail)))))))
             (setf (wb-loops b) (append (subseq (wb-loops b) 0 pos)
                                        (list (copy-wloop* tmpl))
                                        keep)))))))

(defun term-used-by-loop-p (term loop)
  (dolist (x (wl-lterms loop) nil)
    (when (and x (or (eq x term) (eq (wt-parent x) term))) (return t))))

(defun loop-output-adjust (lp n-row)
  "whereLoopOutputAdjust."
  (let* ((not-allowed (lognot (logior (wl-prereq lp) (wl-mask lp))))
         (reduce 0))
    (loop for term across (wc-terms *wc*)
          while (wt-base term)
          do (when (and (zerop (logand (wt-prereq-all term) not-allowed))
                        (logtest (wt-prereq-all term) (wl-mask lp))
                        (not (term-used-by-loop-p term lp)))
               (when (= (wl-mask lp) (wt-prereq-all term))
                 (when (or (member (wt-op term) '(:in :eq :lt :le :gt :ge))
                           (not (member (ws-join (svref *wsrcs* (wl-src lp))) '(:left))))
                   (setf (wl-flags lp) (logior (wl-flags lp) +where-selfcull+))))
               (if (<= (wt-truth term) 0)
                   (incf (wl-n-out lp) (wt-truth term))
                   (progn
                     (decf (wl-n-out lp))
                     (when (member (wt-op term) '(:eq :is))
                       (let* ((v (and (wt-rhs term) (integer-literal-value (wt-rhs term))))
                              (k (if (and v (<= -1 v 1)) 10 20)))
                         (when (< reduce k)
                           (setf (wt-heurtruth term) t reduce k))))))))
    (when (> (wl-n-out lp) (- n-row reduce))
      (setf (wl-n-out lp) (- n-row reduce)))))

(defun constraint-compatible-with-outer-join-p (term ws)
  "constraintCompatibleWithOuterJoin: only a term from this LEFT JOIN's
own ON clause can constrain its right-hand table."
  (and (eql (wt-outer-on term) (ws-i ws))
       t))

(defun index-column-not-null-p (ws wx j)
  (let ((c (widx-col wx j)))
    (cond ((eq c :rowid) t)
          ((integerp c) (column-not-null (aref (table-columns (ws-table ws)) c)))
          (t nil))))

(defun range-adjust (term n)
  "whereRangeAdjust."
  (cond ((null term) n)
        ((<= (wt-truth term) 0) (+ n (wt-truth term)))
        ((not (wt-vnull term)) (- n 20))
        (t n)))

(defun range-scan-est (lower upper lp)
  "whereRangeScanEst without STAT4."
  (let* ((n-out (wl-n-out lp))
         (n-new (range-adjust upper (range-adjust lower n-out))))
    (when (and lower (plusp (wt-truth lower)) upper (plusp (wt-truth upper)))
      (decf n-new 20))
    (decf n-out (+ (if lower 1 0) (if upper 1 0)))
    (when (< n-new 10) (setf n-new 10))
    (when (< n-new n-out) (setf n-out n-new))
    (setf (wl-n-out lp) n-out)))

(defun in-term-count (term)
  "log(number of IN values): 46 (25 rows) for a subquery."
  (let ((rhs (wt-rhs term)))
    (if (eq (car rhs) :list)
        (log-est (max 1 (length (second rhs))))
        46)))

(defun add-btree-index (b ws wx tmpl n-in-mul)
  "whereLoopAddBtreeIndex: extend TMPL (which matches n-eq columns of WX)
by one more constraint on the next index column, insert, and recurse."
  (let* ((saved (copy-wloop* tmpl))
         (ops (if (flag-p (wl-flags tmpl) +where-btm-limit+)
                  '(:lt :le)
                  '(:eq :in :gt :ge :lt :le :isnull :is)))
         (r-size (svref (wx-row-est wx) 0))
         (r-log-size (est-log r-size))
         (sz-tab (ws-sz-row ws))
         (j (wl-n-eq tmpl)))
    (dolist (p (where-scan (ws-i ws) nil ops wx j))
      (destructuring-bind (term . via-equiv) p
        (block one
          (let ((op (wt-op term)) (n-in 0))
            (when (and (or (eq op :isnull) (wt-vnull term))
                       (index-column-not-null-p ws wx j))
              (return-from one))
            (when (logtest (wt-prereq-right term) (ws-mask ws)) (return-from one))
            (when (and (member (ws-join ws) '(:left :right :full))
                       (not (constraint-compatible-with-outer-join-p term ws)))
              (return-from one))
            (let ((new (copy-wloop* saved)))
              (setf (wl-lterms new) (append (wl-lterms saved) (list term))
                    (wl-prereq new) (logand (logior (wl-prereq saved) (wt-prereq-right term))
                                            (lognot (ws-mask ws))))
              (let ((lower nil) (upper nil))
                (case op
                  (:in
                   (setf n-in (if (eq (car (wt-rhs term)) :list)
                                  (log-est (max 1 (length (second (wt-rhs term)))))
                                  ;; a subquery counts once however many columns use it
                                  (if (find-if (lambda (x) (and x (eq (wt-expr x) (wt-expr term))))
                                               (wl-lterms saved))
                                      0 46)))
                   (setf (wl-flags new) (logior (wl-flags new) +where-column-in+)))
                  ((:eq :is)
                   (let ((icol (widx-col wx j)))
                     (setf (wl-flags new) (logior (wl-flags new) +where-column-eq+))
                     (when (or (eq icol :rowid)
                               (and (integerp icol) (zerop n-in-mul) (= j (1- (wx-n-key wx)))))
                       (setf (wl-flags new)
                             (logior (wl-flags new)
                                     (if (or (eq icol :rowid) (wx-uniq-not-null wx)
                                             (and (= (wx-n-key wx) 1) (wx-on-error wx) (eq op :eq)))
                                         +where-onerow+
                                         +where-unq-wanted+))))
                     (when via-equiv (setf (wl-flags new) (logior (wl-flags new) +where-transcons+)))))
                  (:isnull (setf (wl-flags new) (logior (wl-flags new) +where-column-null+)))
                  ((:gt :ge)
                   (setf (wl-flags new) (logior (wl-flags new) +where-column-range+ +where-btm-limit+)
                         (wl-n-btm new) 1
                         lower term upper nil))
                  ((:lt :le)
                   (setf (wl-flags new) (logior (wl-flags new) +where-column-range+ +where-top-limit+)
                         (wl-n-top new) 1
                         upper term
                         lower (and (flag-p (wl-flags new) +where-btm-limit+)
                                    (car (last (wl-lterms saved)))))))
                ;; rows visited
                (if (flag-p (wl-flags new) +where-column-range+)
                    (range-scan-est lower upper new)
                    (let ((n-eq (incf (wl-n-eq new))))
                      (if (and (<= (wt-truth term) 0) (integerp (widx-col wx j)))
                          (progn (incf (wl-n-out new) (wt-truth term))
                                 (decf (wl-n-out new) n-in))
                          (progn
                            (incf (wl-n-out new) (- (svref (wx-row-est wx) n-eq)
                                                    (svref (wx-row-est wx) (1- n-eq))))
                            (when (eq op :isnull) (incf (wl-n-out new) 10))))))
                ;; cost: the index seek and scan, plus table lookups
                (let ((r-cost-idx (+ (wl-n-out new) 1 (floor (* 15 (wx-sz-row wx)) sz-tab))))
                  (setf (wl-r-run new) (log-est-add r-log-size r-cost-idx))
                  (unless (logtest (wl-flags new) (logior +where-idx-only+ +where-ipk+))
                    (setf (wl-r-run new) (log-est-add (wl-r-run new) (+ (wl-n-out new) 16)))))
                (let ((n-out-unadjusted (wl-n-out new)))
                  (incf (wl-r-run new) (+ n-in-mul n-in))
                  (incf (wl-n-out new) (+ n-in-mul n-in))
                  (let ((ins (copy-wloop* new)))
                    (loop-output-adjust ins r-size)
                    (loop-insert b ins))
                  (setf (wl-n-out new) (if (flag-p (wl-flags new) +where-column-range+)
                                           (wl-n-out saved)
                                           n-out-unadjusted)))
                (when (and (not (flag-p (wl-flags new) +where-top-limit+))
                           (< (wl-n-eq new) (wx-n-col wx))
                           (or (< (wl-n-eq new) (wx-n-key wx)) (not (wx-pk wx))))
                  (add-btree-index b ws wx new (+ n-in-mul n-in)))))))))))

(defun index-might-help-with-order-by-p (b ws wx)
  "indexMightHelpWithOrderBy."
  (dolist (ob (wb-order-by b) nil)
    (when (eql (ob-src ob) (ws-i ws))
      (let ((c (ob-col ob)))
        (when (eq c :rowid) (return t))
        (when (and c (find c (wx-cols wx) :end (wx-n-key wx))) (return t))))))

(defun term-can-drive-index-p (term ws not-ready)
  "termCanDriveIndex."
  (and (eql (wt-src term) (ws-i ws))
       (member (wt-op term) '(:eq :is))
       (or (not (member (ws-join ws) '(:left :right :full)))
           (constraint-compatible-with-outer-join-p term ws))
       (zerop (logand (wt-prereq-right term) not-ready))
       (integerp (wt-col term))
       (index-affinity-ok-p term (svref (src-affinities (fsrc-src (ws-fsrc ws))) (wt-col term)))))

(defun partial-index-usable-p (ws wx)
  "whereUsablePartialIndex: some term implies the index's WHERE clause."
  (let ((conds (split-conjuncts (wx-partial wx))))
    (every (lambda (c)
             (loop for term across (wc-terms *wc*)
                   thereis (and (or (null (wt-outer-on term)) (eql (wt-outer-on term) (ws-i ws)))
                                (or (not (member (ws-join ws) '(:left :right :full)))
                                    (wt-outer-on term))
                                (not (wt-vnull term))
                                (expr-implies-p (wt-expr term) c (ws-i ws)))))
           conds)))

(defun expr-implies-p (e p si)
  "sqlite3ExprImpliesExpr, the cases that matter: E is P, or P is
x IS NOT NULL and E is a comparison of x that cannot be true for NULL."
  (or (equal (canonical-expr e si) (canonical-expr p si))
      (let ((notnull (cond ((and (eq (car p) :isnull) (third p)) (second p))
                           ((and (eq (car p) :binary) (eq (second p) :isnot) (null-literal-p (fourth p)))
                            (third p)))))
        (and notnull
             (let ((x (canonical-expr notnull si)))
               (or (and (eq (car e) :binary) (member (second e) '(:eq :lt :le :gt :ge :ne))
                        (or (equal (canonical-expr (third e) si) x)
                            (equal (canonical-expr (fourth e) si) x)))
                   (and (member (car e) '(:between :in)) (not (car (last e)))
                        (equal (canonical-expr (second e) si) x))))))))

(defun canonical-expr (e si)
  "E with column references of the source SI reduced to (:c name) so that
an index definition's WHERE compares equal to a query's."
  (cond ((atom e) e)
        ((eq (car e) :col)
         (let ((s (nth si (scope-srcs (wc-scope *wc*)))))
           (list :c (string-upcase-ascii (third e))
                 (and (second e) (not (name= (second e) (src-name s))) (second e)))))
        ((eq (car e) :srccol)
         (let ((s (nth (second e) (scope-srcs (wc-scope *wc*)))))
           (list :c (string-upcase-ascii (if (eq (third e) :rowid) "rowid" (svref (src-columns s) (third e)))) nil)))
        (t (mapcar (lambda (x) (canonical-expr x si)) e))))

(defun pushed-fixed-eq-p (term)
  "A pushed-down copy of col = X whose column the outer query fixed: still
an == term on a column, of a cursor the subquery does not have."
  (let ((e (or (wt-origin term) (wt-expr term))))
    (and (eq (car e) :binary) (member (second e) '(:eq :is))
         (eq (car (skip-collate (third e))) :pushed-fixed))))

(defun term-covered-by-index-p (term ws wx)
  "sqlite3ExprCoveredByIndex: every column of WS the term reads is in WX."
  (let ((scope (wc-scope *wc*)) (ok t))
    (labels ((walk (x)
               (when (consp x)
                 (case (car x)
                   ((:col :srccol)
                    (multiple-value-bind (s c) (column-ref x scope)
                      (when (and s (= s (ws-i ws)) (integerp c) (not (find c (wx-cols wx))))
                        (setf ok nil))))
                   ((:subquery :exists) (setf ok nil))
                   (t (mapc #'walk (cdr x)))))))
      (walk (or (wt-origin term) (wt-expr term))))
    ok))

(defun add-btree-loops (b ws m-prereq)
  "whereLoopAddBtree."
  (let* ((r-size (ws-row-est ws))
         (sz-tab (ws-sz-row ws))
         (mask (ws-mask ws)))
    ;; automatic indexes (never for an OR disjunct)
    (when (and (ws-auto-ok ws) (null (wb-or-set b)) (not *or-branch-plan*)
               (not (ws-indexed-by ws)) (not (ws-not-indexed ws))
               (ws-rowid-table-p ws)
               (not (member (ws-join ws) '(:right :full))))
      (let ((r-log-size (est-log r-size)))
        (loop for term across (wc-terms *wc*)
              do (unless (logtest (wt-prereq-right term) mask)
                   (when (term-can-drive-index-p term ws 0)
                     (let ((lp (make-wloop :src (ws-i ws) :mask mask :n-eq 1 :lterms (list term)
                                           :sort-idx (wb-sort-idx b)
                                           :r-setup (max 0 (+ r-log-size r-size (if (ws-view-p ws) -10 28)))
                                           :n-out 43
                                           :r-run (log-est-add r-log-size 43)
                                           :flags +where-auto-index+
                                           :prereq (logior m-prereq (wt-prereq-right term)))))
                       (loop-insert b lp)))))))
    ;; the rowid and every index (or just the INDEXED BY one)
    (let ((sort-idx 1))
      (dolist (wx (ws-probes ws))
        (block probe
          (when (and (wx-partial wx) (not (partial-index-usable-p ws wx)))
            (incf sort-idx)
            (return-from probe))
          (let* ((r-size (svref (wx-row-est wx) 0))
                 (help (index-might-help-with-order-by-p b ws wx))
                 (tmpl (make-wloop :src (ws-i ws) :mask mask :prereq m-prereq :wx wx
                                   :n-out r-size)))
            (setf (wb-sort-idx b) 0)
            (if (wx-ipk wx)
                (progn
                  (setf (wl-flags tmpl) +where-ipk+
                        (wb-sort-idx b) (if help sort-idx 0))
                  (let ((lp (copy-wloop* tmpl)))
                    (setf (wl-sort-idx lp) (wb-sort-idx b)
                          (wl-r-run lp) (+ r-size 16))
                    (when (ws-view-p ws) (setf (wl-flags lp) (logior (wl-flags lp) +where-viewscan+)))
                    (loop-output-adjust lp r-size)
                    (loop-insert b lp)))
                (let ((covering (widx-covers-p ws wx)))
                  (setf (wl-flags tmpl) (if covering
                                            (logior +where-idx-only+ +where-indexed+)
                                            +where-indexed+))
                  (when (or help
                            (not (ws-rowid-table-p ws))
                            (wx-partial wx)
                            (ws-indexed-by ws)
                            (and covering (< (wx-sz-row wx) sz-tab)
                                 (not (logtest (wb-flags b) +wf-onepass-desired+))))
                    (setf (wb-sort-idx b) (if help sort-idx 0))
                    (let ((lp (copy-wloop* tmpl)))
                      (setf (wl-sort-idx lp) (wb-sort-idx b)
                            (wl-r-run lp) (+ r-size 1 (floor (* 15 (wx-sz-row wx)) sz-tab)))
                      (unless covering
                        (let ((n-lookup (+ r-size 16)))
                          ;; pWInfo->sWC: the whole WHERE clause, even in an OR sub-build
                          (loop for term across (wc-terms (root-wc *wc*))
                                do (unless (term-covered-by-index-p term ws wx) (return))
                                   (if (<= (wt-truth term) 0)
                                       (incf n-lookup (wt-truth term))
                                       (progn (decf n-lookup)
                                              (when (or (member (wt-op term) '(:eq :is))
                                                        (pushed-fixed-eq-p term))
                                                (decf n-lookup 19)))))
                          (setf (wl-r-run lp) (log-est-add (wl-r-run lp) n-lookup))))
                      (loop-output-adjust lp r-size)
                      (loop-insert b lp)))))
            (setf (wl-sort-idx tmpl) (wb-sort-idx b))
            (add-btree-index b ws wx tmpl 0))
          (incf sort-idx))))))

;;; ------------------------------------------------------------------
;;; Virtual tables (a single loop each, for now)

(defun add-vtab-loops (b ws m-prereq)
  (loop-insert b (make-wloop :src (ws-i ws) :mask (ws-mask ws) :prereq m-prereq
                             :flags +where-virtualtable+
                             :r-run 200 :n-out 46
                             :vtab (list :ordered (and (zerop (ws-i ws)) *vtab-order-ok*)))))

(defvar *vtab-order-ok* nil "The first source is a virtual table that yields ORDER BY order.")

(defun add-all-loops (b)
  "whereLoopAddAll: prerequisites keep CROSS and outer joins in FROM order."
  (let ((m-prereq 0) (m-prior 0)
        (fixed (some (lambda (ws) (member (ws-join ws) '(:right :full))) *wsrcs*)))
    (loop for ws across *wsrcs*
          do (if (or fixed (member (ws-join ws) '(:left :right :full :cross)))
                 (setf m-prereq (logior m-prereq m-prior))
                 (setf m-prereq 0))
             (let ((m-prereq (logior m-prereq (ws-extra-prereq ws))))
               (if (eq (ws-kind ws) :vtab)
                   (add-vtab-loops b ws m-prereq)
                   (progn (add-btree-loops b ws m-prereq)
                          (add-or-loops b ws m-prereq))))
             (setf m-prior (logior m-prior (ws-mask ws))))))

;;; ------------------------------------------------------------------
;;; ORDER BY, GROUP BY and DISTINCT lists

(defstruct (obterm (:conc-name ob-))
  expr src col    ; col: a column of source SRC (:ROWID or an index), or NIL
  coll desc bignull
  (mask 0) const)

(defun loop-in-path-p (lp path-loops) (member lp path-loops))

(defun satisfies-order-by (b obs path-loops n-loop last flags)
  "wherePathSatisfiesOrderBy: how many leading terms of OBS the loops
PATH-LOOPS (N-LOOP of them) followed by LAST deliver in order.  Returns
(values n rev-mask); n is -1 when it cannot be known yet."
  (let* ((n-ob (length obs))
         (ob-done (1- (ash 1 n-ob)))
         (ob-sat 0) (rev-mask 0)
         (order-distinct t) (order-distinct-mask 0) (ready 0)
         (eq-ops (if (logtest flags (logior +wf-orderby-limit+ +wf-orderby-min+ +wf-orderby-max+))
                     '(:eq :is :isnull :in)
                     '(:eq :is :isnull)))
         (lp nil))
    (declare (ignorable b))
    (when (> n-ob 63) (return-from satisfies-order-by (values 0 0)))
    (loop for i-loop from 0 to n-loop
          while (and order-distinct (/= ob-sat ob-done))
          do (when (> i-loop 0) (setf ready (logior ready (wl-mask lp))))
             (block this-loop
               (if (< i-loop n-loop)
                   (progn (setf lp (nth i-loop path-loops))
                          (when (logtest flags +wf-orderby-limit+) (return-from this-loop)))
                   (setf lp last))
               (when (flag-p (wl-flags lp) +where-virtualtable+)
                 (when (and (getf (wl-vtab lp) :ordered)
                            (/= (logand flags (logior +wf-distinctby+ +wf-sortbygroup+)) +wf-distinctby+))
                   (setf ob-sat ob-done))
                 (loop-finish))
               (let ((src (wl-src lp)))
                 ;; ORDER BY terms fixed by X=? or X IS NULL on outer loops
                 (loop for ob in obs for i from 0
                       do (unless (logbitp i ob-sat)
                            (when (and (eql (ob-src ob) src) (ob-col ob))
                              (let ((term (where-find-term src (ob-col ob) (lognot ready) eq-ops)))
                                (when term
                                  (block chk
                                    (when (eq (wt-op term) :in)
                                      (unless (member term (wl-lterms lp)) (return-from chk)))
                                    (when (and (member (wt-op term) '(:eq :is)) (integerp (ob-col ob)))
                                      (unless (collation= (ob-coll ob) (wt-coll term)) (return-from chk)))
                                    (setf ob-sat (logior ob-sat (ash 1 i)))))))))
                 (unless (flag-p (wl-flags lp) +where-onerow+)
                   (let* ((wx (wl-wx lp))
                          (ipk (flag-p (wl-flags lp) +where-ipk+))
                          (n-key (if ipk 0 (and wx (wx-n-key wx))))
                          (n-col (if ipk 1 (and wx (wx-n-col wx))))
                          (rev nil) (rev-set nil) (distinct-columns nil))
                     (when (and (not ipk) (or (null wx) (wx-auto wx)))
                       (return-from satisfies-order-by (values 0 0)))
                     (unless ipk (setf order-distinct (and (wx-unique wx) t)))
                     (loop for j from 0 below n-col
                           do (let ((once t))
                                (block col
                                  (when (< j (wl-n-eq lp))
                                    (let ((op (wt-op (nth j (wl-lterms lp)))))
                                      (cond ((member op eq-ops)
                                             (when (member op '(:isnull :is)) (setf order-distinct nil))
                                             (return-from col))
                                            ((eq op :in)
                                             (let ((x (wt-expr (nth j (wl-lterms lp)))))
                                               (loop for i from (1+ j) below (wl-n-eq lp)
                                                     when (eq (wt-expr (nth i (wl-lterms lp))) x)
                                                       do (setf once nil) (return)))))))
                                  (let* ((icol (if ipk :rowid (widx-key-col wx j)))
                                         (rev-idx (if ipk nil (svref (wx-descs wx) j)))
                                         (match nil) (mi nil))
                                    (when order-distinct
                                      (when (or (and (integerp icol) (>= j (wl-n-eq lp))
                                                     (not (column-not-null (aref (table-columns (ws-table (svref *wsrcs* src))) icol))))
                                                (consp icol))
                                        (setf order-distinct nil)))
                                    (loop for ob in obs for i from 0
                                          while once
                                          do (unless (logbitp i ob-sat)
                                               (unless (logtest flags (logior +wf-groupby+ +wf-distinctby+))
                                                 (setf once nil))
                                               (when (and (eql (ob-src ob) src) (eql (ob-col ob) icol) icol
                                                          (or (eq icol :rowid)
                                                              (collation= (ob-coll ob) (svref (wx-colls wx) j))))
                                                 (setf match t mi i)
                                                 (return))))
                                    (when (and match (not (logtest flags +wf-groupby+)))
                                      (let ((want (and (ob-desc (nth mi obs)) t)))
                                        (if rev-set
                                            (unless (eq (not (eq rev rev-idx)) want)
                                              (setf match nil))
                                            (progn
                                              (setf rev (not (eq (and rev-idx t) want)))
                                              (setf rev (and rev t))
                                              (when rev (setf rev-mask (logior rev-mask (ash 1 i-loop))))
                                              (setf rev-set t)))))
                                    ;; NULLS FIRST/LAST against the index order: only the
                                    ;; min()/max() optimization takes it (at j = nEq)
                                    (when (and match (ob-bignull (nth mi obs)))
                                      (unless (and (= j (wl-n-eq lp))
                                                   (logtest flags (logior +wf-orderby-min+ +wf-orderby-max+)))
                                        (setf match nil)))
                                    (if match
                                        (progn
                                          (when (eq icol :rowid) (setf distinct-columns t))
                                          (setf ob-sat (logior ob-sat (ash 1 mi))))
                                        (progn
                                          (when (or (= j 0) (< j n-key)) (setf order-distinct nil))
                                          (return)))))))
                     (when distinct-columns (setf order-distinct t))))
                 ;; other terms that only read order-distinct loops
                 (when order-distinct
                   (setf order-distinct-mask (logior order-distinct-mask (wl-mask lp)))
                   (loop for ob in obs for i from 0
                         do (unless (logbitp i ob-sat)
                              (let ((m (ob-mask ob)))
                                (unless (and (zerop m) (not (ob-const ob)))
                                  (when (zerop (logand m (lognot order-distinct-mask)))
                                    (setf ob-sat (logior ob-sat (ash 1 i))))))))))))
    (cond ((= ob-sat ob-done) (values n-ob rev-mask))
          ((not order-distinct)
           (loop for i from (1- n-ob) above 0
                 do (let ((m (1- (ash 1 i))))
                      (when (= (logand ob-sat m) m) (return-from satisfies-order-by (values i rev-mask)))))
           (values 0 rev-mask))
          (t (values -1 rev-mask)))))

(defun sorting-cost (b n-row n-ob n-sorted)
  "whereSortingCost."
  (let* ((r-scale (- (log-est (floor (* (- n-ob n-sorted) 100) n-ob)) 66))
         (r-sort (+ n-row r-scale 16)))
    (cond ((and (logtest (wb-flags b) +wf-use-limit+) (wb-limit b) (< (wb-limit b) n-row))
           (setf n-row (wb-limit b)))
          ((logtest (wb-flags b) +wf-want-distinct+)
           (when (> n-row 10) (decf n-row 10))))
    (+ r-sort (est-log n-row))))

;;; ------------------------------------------------------------------
;;; The path solver

(defstruct (wpath (:conc-name wp-))
  (mask 0) (rev 0) (n-row 0) (r-cost 0) (r-unsorted 0) (is-ordered 0) (loops '()))

(defun path-solver (b n-row-est)
  "wherePathSolver.  Returns the cheapest WPATH."
  (let* ((n-loop (length *wsrcs*))
         (mx-choice (cond ((<= n-loop 1) 1) ((= n-loop 2) 5) (t 10)))
         (obs (wb-order-by b))
         (n-ob (if (or (null obs) (zerop n-row-est)) 0 (length obs)))
         (sort-costs (make-array (max 1 n-ob) :initial-element 0))
         (from (list (make-wpath :n-row (min *query-loop* 48)
                                 :is-ordered (if (plusp n-ob) (if (plusp n-loop) -1 n-ob) 0)))))
    (dotimes (i-loop n-loop)
      (let ((to (make-array mx-choice :initial-element nil))
            (n-to 0) (mx-i 0) (mx-cost 0) (mx-unsorted 0))
        (dolist (pf from)
          (dolist (lp (wb-loops b))
            (block cand
              (when (logtest (wl-prereq lp) (lognot (wp-mask pf))) (return-from cand))
              (when (logtest (wl-mask lp) (wp-mask pf)) (return-from cand))
              (when (and (flag-p (wl-flags lp) +where-auto-index+) (< (wp-n-row pf) 3))
                (return-from cand))
              (let* ((r-unsorted (log-est-add (log-est-add (wl-r-setup lp) (+ (wl-r-run lp) (wp-n-row pf)))
                                              (wp-r-unsorted pf)))
                     (n-out (+ (wp-n-row pf) (wl-n-out lp)))
                     (mask-new (logior (wp-mask pf) (wl-mask lp)))
                     (is-ordered (wp-is-ordered pf))
                     (rev-mask (wp-rev pf))
                     (r-cost 0))
                (when (< is-ordered 0)
                  (multiple-value-setq (is-ordered rev-mask)
                    (satisfies-order-by b obs (wp-loops pf) i-loop lp (wb-flags b))))
                (if (and (>= is-ordered 0) (< is-ordered n-ob))
                    (progn
                      (when (zerop (aref sort-costs is-ordered))
                        (setf (aref sort-costs is-ordered) (sorting-cost b n-row-est n-ob is-ordered)))
                      (setf r-cost (+ (log-est-add r-unsorted (aref sort-costs is-ordered)) 5)))
                    (progn (setf r-cost r-unsorted) (decf r-unsorted 2)))
                (when (and (zerop i-loop) (flag-p (wl-flags lp) +where-viewscan+))
                  (incf r-cost -10) (incf n-out -30))
                (let ((jj (loop for k below n-to
                                for p = (aref to k)
                                when (and (= (wp-mask p) mask-new)
                                          (eq (< (wp-is-ordered p) 0) (< is-ordered 0)))
                                  return k)))
                  (if (null jj)
                      (progn
                        (when (and (>= n-to mx-choice)
                                   (or (> r-cost mx-cost) (and (= r-cost mx-cost) (>= r-unsorted mx-unsorted))))
                          (return-from cand))
                        (setf jj (if (< n-to mx-choice) (prog1 n-to (incf n-to)) mx-i)))
                      (let ((p (aref to jj)))
                        (when (or (< (wp-r-cost p) r-cost)
                                  (and (= (wp-r-cost p) r-cost)
                                       (or (< (wp-n-row p) n-out)
                                           (and (= (wp-n-row p) n-out) (<= (wp-r-unsorted p) r-unsorted)))))
                          (return-from cand))))
                  (setf (aref to jj)
                        (make-wpath :mask mask-new :rev rev-mask :n-row n-out :r-cost r-cost
                                    :r-unsorted r-unsorted :is-ordered is-ordered
                                    :loops (append (wp-loops pf) (list lp))))
                  (when (>= n-to mx-choice)
                    (setf mx-i 0 mx-cost (wp-r-cost (aref to 0)) mx-unsorted (wp-n-row (aref to 0)))
                    (loop for k from 1 below mx-choice
                          for p = (aref to k)
                          do (when (or (> (wp-r-cost p) mx-cost)
                                       (and (= (wp-r-cost p) mx-cost) (> (wp-r-unsorted p) mx-unsorted)))
                               (setf mx-cost (wp-r-cost p) mx-unsorted (wp-r-unsorted p) mx-i k)))))))))
        (setf from (loop for k below n-to collect (aref to k)))))
    (when (null from) (sql-error "no query solution"))
    (let ((best (first from)))
      (dolist (p (rest from) best)
        (when (> (wp-r-cost best) (wp-r-cost p)) (setf best p))))))

;;; ------------------------------------------------------------------
;;; Planning a FROM clause

(defstruct (wplan (:conc-name plan-))
  loops           ; one WLOOP per source, in execution order
  (n-row 0)       ; nRowOut
  (n-ob-sat 0)    ; leading ORDER BY / GROUP BY terms delivered in order
  (rev 0)         ; bit per loop position: run it in reverse
  distinct        ; :unique :ordered :unordered
  sorted          ; GROUP BY delivered sorted (WHERE_SORTBYGROUP)
  wc wsrcs)

(defun short-cut (b &optional (ws (svref *wsrcs* 0)) (ready 0))
  "whereShortCut: one table, looked up by rowid or a whole unique key.
READY: tables a term may read and still count as constant (the outer
loops of an OR disjunct's sub-plan)."
  (declare (ignorable b))
  (let* ((table (ws-table ws))
         (si (ws-i ws)) (mask (ws-mask ws)))
    (when (or (not (eq (ws-kind ws) :btree)) (ws-indexed-by ws) (ws-not-indexed ws))
      (return-from short-cut nil))
    (flet ((const-term (src col ops &optional wx j)
             (loop for (term . via) in (where-scan src col ops wx j)
                   when (zerop (logandc2 (wt-prereq-right term) ready)) return (values term via))))
      (let ((lp nil))
        (unless (table-without-rowid table)
          (multiple-value-bind (term via) (const-term si :rowid '(:eq :is))
            (when term
              (setf lp (make-wloop :src si :mask mask :wx (first (ws-probes ws))
                                   :flags (logior +where-column-eq+ +where-ipk+ +where-onerow+
                                                  (if via +where-transcons+ 0))
                                   :lterms (list term) :n-eq 1 :r-run 33)))))
        (unless lp
          (dolist (wx (ws-probes ws))
            (unless (or (wx-ipk wx) (not (wx-unique wx)) (wx-partial wx) (> (wx-n-key wx) 3))
              (let ((ops (if (wx-uniq-not-null wx) '(:eq :is) '(:eq)))
                    (terms '()) (via-any nil))
                (when (loop for j below (wx-n-key wx)
                            always (multiple-value-bind (term via) (const-term si nil ops wx j)
                                     (when term (push term terms) (when via (setf via-any t)))
                                     term))
                  (setf lp (make-wloop :src si :mask mask :wx wx
                                       :flags (logior +where-column-eq+ +where-onerow+ +where-indexed+
                                                      (if (widx-covers-p ws wx) +where-idx-only+ 0)
                                                      (if via-any +where-transcons+ 0))
                                       :lterms (nreverse terms) :n-eq (wx-n-key wx) :r-run 39))
                  (return))))))
        (when lp
          (setf (wl-n-out lp) 1)
          (make-wplan :loops (list lp) :n-row 1
                      :n-ob-sat (length (wb-order-by b))
                      :distinct (and (logtest (wb-flags b) +wf-want-distinct+) :unique)))))))

(defun distinct-redundant-p (dlist)
  "isDistinctRedundant: one table, and the DISTINCT list includes its
rowid or a whole UNIQUE NOT NULL key (or those key columns are fixed by
X=? terms)."
  (when (= (length *wsrcs*) 1)
    (let ((ws (svref *wsrcs* 0)))
      (when (some (lambda (ob) (and (eql (ob-src ob) 0) (eq (ob-col ob) :rowid))) dlist)
        (return-from distinct-redundant-p t))
      (when (eq (ws-kind ws) :btree)
        (dolist (wx (ws-probes ws) nil)
          (when (and (not (wx-ipk wx)) (wx-unique wx) (not (wx-partial wx))
                     (loop for j below (wx-n-key wx)
                           always (or (where-scan-first 0 wx j '(:eq))
                                      (and (find-if (lambda (ob) (and (eql (ob-src ob) 0)
                                                                      (eql (ob-col ob) (widx-col wx j))
                                                                      (collation= (ob-coll ob) (svref (wx-colls wx) j))))
                                                    dlist)
                                           (index-column-not-null-p ws wx j)))))
            (return t)))))))

(defun where-scan-first (src wx j ops)
  (car (first (where-scan src nil ops wx j))))

(defun trace-loops (b)
  (dolist (lp (wb-loops b))
    (format *error-output* "~&  loop ")
    (trace-loop lp)))

(defun trace-loop (lp)
    (let ((ws (svref *wsrcs* (wl-src lp))))
      (format *error-output* "~a ~a f ~6,'0x N ~d eq ~d cost ~d,~d,~d prereq ~b~%"
              (src-label (fsrc-src (ws-fsrc ws)))
              (let ((wx (wl-wx lp))) (cond ((null wx) "-") ((wx-ipk wx) "IPK") (t (wx-name wx))))
              (wl-flags lp) (length (wl-lterms lp)) (wl-n-eq lp)
              (wl-r-setup lp) (wl-r-run lp) (wl-n-out lp) (wl-prereq lp))
      (when (and *wc* (wl-lterms lp))
        (format *error-output* "        terms ~{~a~^ ~}~%"
                (mapcar (lambda (term) (or (position term (wc-terms *wc*)) "?")) (wl-lterms lp))))))

(defun plan-where (wsrcs scope conjuncts &key order-by (flags 0) limit distinct-list)
  "Plan the loops for WSRCS (a vector of WSRC) under CONJUNCTS (see
ANALYZE-WHERE).  ORDER-BY: OBTERMs that the planner should try to deliver
in order (an ORDER BY, or a GROUP BY with +WF-GROUPBY+).  Returns a WPLAN."
  (let* ((n (length wsrcs))
         (*wsrcs* wsrcs)
         (*wc* (analyze-where conjuncts scope n))
         (b (make-wbuilder :order-by order-by :flags flags :limit limit))
         (distinct nil))
    (when (logtest flags +wf-want-distinct+)
      (cond ((distinct-redundant-p distinct-list) (setf distinct :unique))
            ((null order-by)
             (setf (wb-flags b) (logior (wb-flags b) +wf-distinctby+)
                   (wb-order-by b) distinct-list))))
    (let ((plan (and (= n 1) (short-cut b))))
      (unless plan
        (when *where-trace*
          (loop for term across (wc-terms *wc*) for k from 0
                do (format *error-output* "~&  TERM-~d ~a.~a ~(~a~)~:[~; equiv~]~:[~; virtual~] right ~b all ~b~@[ outer ~a~]  ~s~%"
                           k (wt-src term) (wt-col term) (wt-op term) (wt-equiv term) (wt-virtual term)
                           (wt-prereq-right term) (wt-prereq-all term) (wt-outer-on term)
                           (or (wt-origin term) (wt-expr term)))))
        (add-all-loops b)
        (when *where-trace* (trace-loops b))
        (let* ((path (path-solver b 0))
               ;; wherePathSolver's nRowEst: 0 on the first call, whose
               ;; result is final unless there is an order to deliver
               (n-row-est (if (wb-order-by b) (1+ (wp-n-row path)) 0)))
          (when (wb-order-by b)
            (setf path (path-solver b n-row-est)))
          (setf plan (make-wplan :loops (wp-loops path) :n-row (wp-n-row path)))
          (let* ((loops (wp-loops path)) (nl (length loops)) (last (car (last loops))))
            (when (and (logtest (wb-flags b) +wf-want-distinct+)
                       (not (logtest (wb-flags b) +wf-distinctby+))
                       (null distinct) distinct-list
                       (/= n-row-est 0))
              (when (= (satisfies-order-by b distinct-list (butlast loops) (1- nl) last +wf-distinctby+)
                       (length distinct-list))
                (setf distinct :ordered)))
            (when (wb-order-by b)
              (let ((sat (wp-is-ordered path)))
                (setf (plan-n-ob-sat plan) (max 0 sat))
                (cond ((logtest (wb-flags b) +wf-distinctby+)
                       (when (= sat (length (wb-order-by b))) (setf distinct :ordered)))
                      (t (setf (plan-rev plan) (wp-rev path))))
                (when (and (logtest (wb-flags b) +wf-sortbygroup+)
                           (= (plan-n-ob-sat plan) (length (wb-order-by b))) (plusp nl))
                  (multiple-value-bind (k rev)
                      (satisfies-order-by b (wb-order-by b) (butlast loops) (1- nl) last 0)
                    (when (= k (length (wb-order-by b)))
                      (setf (plan-sorted plan) t (plan-rev plan) rev)))))))))
      (setf (plan-distinct plan) (or distinct (plan-distinct plan)
                                     (and (logtest flags +wf-want-distinct+) :unordered))
            (plan-wc plan) *wc* (plan-wsrcs plan) wsrcs)
      plan)))

;;; ------------------------------------------------------------------
;;; EXPLAIN QUERY PLAN

(defun wx-column-name (ws wx j)
  (let ((c (widx-col wx j)))
    (cond ((eq c :rowid) "rowid")
          ((consp c) "<expr>")
          (t (svref (src-columns (fsrc-src (ws-fsrc ws))) c)))))

(defun explain-loop (lp ws name &optional (wflags 0))
  "sqlite3WhereExplainOneScan."
  (let* ((flags (wl-flags lp))
         (search (or (logtest flags +where-both-limit+)
                     (and (not (flag-p flags +where-virtualtable+)) (plusp (wl-n-eq lp)))
                     (logtest wflags (logior +wf-orderby-min+ +wf-orderby-max+))))
         (out (make-string-output-stream)))
    (format out "~:[SCAN~;SEARCH~] ~a" search name)
    (cond ((not (logtest flags (logior +where-ipk+ +where-virtualtable+)))
           (let* ((wx (wl-wx lp))
                  (fmt (cond ((and (not (ws-rowid-table-p ws)) wx (wx-pk wx))
                              (and search "PRIMARY KEY"))
                             ((flag-p flags +where-partialidx+) "AUTOMATIC PARTIAL COVERING INDEX")
                             ((flag-p flags +where-auto-index+) "AUTOMATIC COVERING INDEX")
                             ((flag-p flags +where-idx-only+) (format nil "COVERING INDEX ~a" (wx-name wx)))
                             (t (format nil "INDEX ~a" (wx-name wx))))))
             (when fmt
               (format out " USING ~a" fmt)
               (let ((n-eq (wl-n-eq lp)))
                 (when (or (plusp n-eq) (logtest flags +where-both-limit+))
                   (write-string " (" out)
                   (dotimes (i n-eq)
                     (format out "~:[~; AND ~]~a=?" (plusp i) (wx-column-name ws wx i)))
                   (let ((and-p (plusp n-eq)))
                     (when (flag-p flags +where-btm-limit+)
                       (format out "~:[~; AND ~]~a>?" and-p (wx-column-name ws wx n-eq))
                       (setf and-p t))
                     (when (flag-p flags +where-top-limit+)
                       (format out "~:[~; AND ~]~a<?" and-p (wx-column-name ws wx n-eq))))
                   (write-string ")" out))))))
          ((and (flag-p flags +where-ipk+) (logtest flags +where-constraint+))
           (write-string " USING INTEGER PRIMARY KEY (rowid" out)
           (cond ((logtest flags (logior +where-column-eq+ +where-column-in+)) (write-string "=?)" out))
                 ((= (logand flags +where-both-limit+) +where-both-limit+)
                  (write-string ">? AND rowid<?)" out))
                 ((flag-p flags +where-btm-limit+) (write-string ">?)" out))
                 (t (write-string "<?)" out)))))
    (get-output-stream-string out)))

;;; ------------------------------------------------------------------
;;; Running a loop

(defun finalize-auto-index (lp ws not-ready)
  "constructAutomaticIndex's choices: every term that can drive the index
at this point of the join (in WHERE order, one per column) becomes a key
column; the other columns the query reads follow, then the rowid; terms
that constrain only this table make it a partial index."
  (let ((keys '()) (key-cols '()) (partial '()))
    (loop for term across (wc-terms *wc*)
          do (when (and (not (wt-virtual term)) (wt-origin term)
                        (table-constraint-term-p term ws))
               (push term partial))
             (when (term-can-drive-index-p term ws not-ready)
               (unless (member (wt-col term) key-cols)
                 (push term keys) (push (wt-col term) key-cols))))
    (setf keys (nreverse keys) key-cols (nreverse key-cols) partial (nreverse partial))
    (let* ((used (ws-col-used ws))
           (ncols (src-ncols (fsrc-src (ws-fsrc ws))))
           (alias (let ((tb (ws-table ws))) (and tb (table-rowid-alias tb))))
           ;; the INTEGER PRIMARY KEY is the rowid, never in colUsed
           (extra (loop for i below ncols
                        when (and (not (member i key-cols)) (not (eql i alias))
                                  (or (eq used :all) (null used) (= 1 (sbit used i))))
                          collect i))
           (cols (append key-cols extra (list :rowid))))
      (setf (wl-wx lp) (make-widx :auto t :name "auto-index"
                                  :cols (coerce cols 'vector)
                                  :colls (coerce (append (mapcar #'wt-coll keys)
                                                         (mapcar (constantly :binary) extra)
                                                         (list :binary))
                                                 'vector)
                                  :descs (make-array (length cols) :initial-element nil)
                                  :n-key (length cols) :n-col (length cols))
            (wl-n-eq lp) (length keys)
            (wl-lterms lp) keys
            (wl-flags lp) (logior (wl-flags lp) +where-column-eq+ +where-idx-only+ +where-indexed+
                                  (if partial +where-partialidx+ 0)))
      partial)))

(defun table-constraint-term-p (term ws)
  "sqlite3ExprIsTableConstraint: the term reads only this source."
  (and (zerop (logandc2 (or (wt-constraint-mask term) (wt-prereq-all term)) (ws-mask ws)))   ; a constant term counts
       (if (eq (ws-join ws) :left)
           (eql (wt-outer-on term) (ws-i ws))
           (not (wt-outer-on term)))
       (not (member (ws-join ws) '(:right :full)))
       (not (expr-has-subquery-p (wt-origin term)))))

(defun expr-has-subquery-p (e)
  (and (consp e)
       (or (member (car e) '(:subquery :exists))
           (and (eq (car e) :in) (eq (car (third e)) :select))
           (some #'expr-has-subquery-p (cdr e)))))

(defun probe-values (term scope col-aff)
  "(lambda (env)) -> the values TERM compares the column with: a list
(one value for = and IS, all of them for IN, NULL for IS NULL), each with
the comparison's affinity applied; NIL when no row can match."
  (let ((op (wt-op term)) (rhs (wt-rhs term)))
    (case op
      (:isnull (lambda (env) (declare (ignore env)) (list :null)))
      (:in
       (let ((vf (in-values-fn rhs scope))
             (other (if (eq (car rhs) :list) nil (select-first-affinity (second rhs) scope))))
         (if vf
             (lambda (env)
               (let ((vals (funcall vf env)))
                 (when (eq (car vals) :done) (setf vals (cdr vals)))
                 (loop for v in vals unless (eq v :null)
                       collect (convert-probe v col-aff other))))
             ;; a correlated IN list: evaluate it through the filter instead
             (let ((f (compile-expr (list :subquery (second rhs)) scope)))
               (declare (ignore f))
               nil))))
      (t
       (let ((f (compile-expr (substitute-fixed rhs) scope)) (other (expr-affinity rhs scope)) (is (eq op :is)))
         (lambda (env)
           (let ((v (funcall f env)))
             (cond ((eq v :null) (if is (list :null) nil))
                   (t (list (convert-probe v col-aff other)))))))))))

(defun bound-fn (term scope col-aff)
  "(lambda (env)) -> (values op value) for a range bound; value :NULL for
x>NULL (all non-NULL values) and NIL when no row can match."
  (when term
    (let ((op (wt-op term)))
      (if (wt-vnull term)
          (lambda (env) (declare (ignore env)) (values op :null))
          (let ((f (compile-expr (substitute-fixed (wt-rhs term)) scope)) (other (expr-affinity (wt-rhs term) scope)))
            (lambda (env)
              (let ((v (funcall f env)))
                (if (eq v :null) (values op nil) (values op (convert-probe v col-aff other))))))))))

(defun value-in-bounds-p (v lo-op lo hi-op hi coll)
  (and (not (eq v :null))
       (or (null lo-op) (eq lo :null)
           (let ((c (compare-values v lo coll))) (if (eq lo-op :gt) (plusp c) (>= c 0))))
       (or (null hi-op)
           (let ((c (compare-values v hi coll))) (if (eq hi-op :lt) (minusp c) (<= c 0))))))

(defun cartesian (lists)
  (if (null lists) (list '())
      (loop for x in (first lists)
            nconc (mapcar (lambda (rest) (cons x rest)) (cartesian (rest lists))))))

(defun loop-bounds (lp)
  "(values lower-term upper-term) of a range loop."
  (let ((range (nthcdr (wl-n-eq lp) (wl-lterms lp))) (flags (wl-flags lp)))
    (values (and (flag-p flags +where-btm-limit+) (first range))
            (and (flag-p flags +where-top-limit+) (car (last range))))))

(defun loop-iterate (lp ws scope rev)
  "(lambda (env fn)) calling FN with each row the loop LP visits."
  (let* ((fs (ws-fsrc ws))
         (table (ws-table ws))
         (src (fsrc-src fs))
         (wanted (src-wanted src))
         (flags (wl-flags lp)))
    (cond
      ;; a derived source (subquery, view, CTE): its rows, maybe through an
      ;; automatic index
      ((eq (ws-kind ws) :derived)
       (let ((rf (fsrc-rows-fn fs)))
         (flet ((each (env fn)
                  (let ((rows (funcall rf env)))
                    (if (functionp rows)
                        (funcall rows fn)
                        (dolist (row rows) (funcall fn row))))))
           (if (flag-p flags +where-auto-index+)
               (auto-index-iterate lp ws scope rev #'each)
               (if rev
                   (lambda (env fn) (let ((acc '())) (each env (lambda (r) (push r acc))) (mapc fn acc)))
                   #'each)))))
      ((flag-p flags +where-auto-index+)
       (auto-index-iterate lp ws scope rev
                           (lambda (env fn) (declare (ignore env)) (map-table-rows table fn :wanted wanted))))
      ((flag-p flags +where-ipk+) (ipk-iterate lp ws scope rev))
      (t (index-iterate lp ws scope rev)))))

(defun ipk-iterate (lp ws scope rev)
  (let* ((table (ws-table ws)) (src (fsrc-src (ws-fsrc ws))) (wanted (src-wanted src))
         (flags (wl-flags lp)))
    (flet ((scan (fn start stop stop-op)
             ;; rowids from START (inclusive) to STOP, in order or reversed
             (if rev
                 (catch :range-done
                   (map-table-reverse (table-owner table) (table-root table)
                                      (lambda (rowid payload)
                                        (when (and start (< rowid start)) (throw :range-done nil))
                                        (unless (and stop (if (eq stop-op :lt) (>= rowid stop) (> rowid stop)))
                                          (funcall fn (table-record-to-row
                                                       table rowid
                                                       (decode-record payload 0 (length payload) nil
                                                                      (and (not (table-virtual-p table)) wanted))))))))
                 (catch :range-done
                   (map-table-rows table
                                   (lambda (row)
                                     (let ((r (svref row (1- (length row)))))
                                       (when (and stop (if (eq stop-op :lt) (>= r stop) (> r stop)))
                                         (throw :range-done nil)))
                                     (funcall fn row))
                                   :start (and start (clamp-i64 start)) :wanted wanted)))))
      (cond
        ((logtest flags (logior +where-column-eq+ +where-column-in+))
         (let ((vf (probe-values (first (wl-lterms lp)) scope :integer)))
           (lambda (env fn)
             (let ((ids (sort (remove-duplicates
                               (loop for v in (and vf (funcall vf env))
                                     for r = (and (not (eq v :null)) (rowid-probe v))
                                     when r collect r))
                              (if rev #'> #'<))))
               (dolist (r ids)
                 (let ((row (fetch-row table r wanted)))
                   (when row (funcall fn row))))))))
        ((logtest flags +where-both-limit+)
         (multiple-value-bind (lo hi) (loop-bounds lp)
           (let ((lf (bound-fn lo scope :integer)) (hf (bound-fn hi scope :integer)))
             (lambda (env fn)
               (let ((start nil) (stop nil) (stop-op nil))
                 (block none
                   (when lf
                     (multiple-value-bind (op v) (funcall lf env)
                       (let ((v (and v (apply-comparison-affinity v :numeric))))
                         (cond ((or (null v) (eq v :null)) (return-from none))
                               ((or (integerp v) (floatp v))
                                (setf start (if (eq op :gt)
                                                (if (integerp v) (1+ v) (ceiling* v t))
                                                (if (integerp v) v (ceiling* v nil)))))
                               (t (return-from none))))))
                   (when hf
                     (multiple-value-bind (op v) (funcall hf env)
                       (let ((v (and v (apply-comparison-affinity v :numeric))))
                         (cond ((null v) (return-from none))
                               ((or (integerp v) (floatp v)) (setf stop v stop-op op))
                               (t nil)))))
                   (scan fn start stop stop-op)))))))
        (t (lambda (env fn) (declare (ignore env)) (scan fn nil nil nil)))))))

(defun row-from-widx (table wx vals)
  "A table row from an index entry: every column the entry holds (the key,
then the rowid or the primary key); the rest read NULL."
  (let* ((cols (table-columns table))
         (n (length cols))
         (row (make-array (1+ n) :initial-element :null)))
    (loop for c across (wx-cols wx)
          for v in vals
          do (cond ((eq c :rowid)
                    (setf (svref row n) v)
                    (when (table-rowid-alias table) (setf (svref row (table-rowid-alias table)) v)))
                   ((integerp c)
                    (setf (svref row c)
                          (if (and (integerp v) (eq (column-affinity (aref cols c)) :real)) (safe-double v) v)))))
    row))

(defun index-entry-row (table wx covering vals wanted)
  (cond ((wx-pk wx) (table-record-to-row table nil vals))
        (covering (row-from-widx table wx vals))
        ;; each key column where the entry holds it (a key column already in
        ;; the index is not repeated at the end)
        ((table-without-rowid table)
         (fetch-wr-row table (wr-entry-pk table (wx-index wx) vals)))
        (t (fetch-row table (car (last vals)) wanted))))

(defun index-iterate (lp ws scope rev)
  (let* ((table (ws-table ws)) (src (fsrc-src (ws-fsrc ws))) (wanted (src-wanted src))
         (wx (wl-wx lp)) (idx (wx-index wx))
         (n-eq (wl-n-eq lp))
         (covering (flag-p (wl-flags lp) +where-idx-only+))
         (colls (coerce (wx-colls wx) 'list))
         (descs (coerce (wx-descs wx) 'list))
         (cmp (index-key-cmp colls descs))
         (col-affs (loop for j below (wx-n-col wx)
                         collect (let ((c (widx-col wx j)))
                                   (cond ((eq c :rowid) :integer)
                                         ((integerp c) (column-affinity (aref (table-columns table) c)))))))
         (eq-fns (loop for term in (subseq (wl-lterms lp) 0 n-eq)
                       for j from 0
                       collect (probe-values term scope (nth j col-affs)))))
    (declare (ignorable idx))
    (multiple-value-bind (lo hi) (loop-bounds lp)
      (let ((lf (bound-fn lo scope (nth n-eq col-affs)))
            (hf (bound-fn hi scope (nth n-eq col-affs)))
            (rcoll (or (nth n-eq colls) :binary))
            (rdesc (nth n-eq descs)))
        (lambda (env fn)
          (block run
            ;; the equality prefixes, in the order the loop visits them
            (let* ((lists (loop for f in eq-fns for j from 0
                                collect (let* ((c (nth j colls))
                                               (vals (if f (funcall f env) (return-from run)))
                                               (sorted (sort (remove-duplicates vals :test (lambda (a b) (zerop (compare-values a b c))))
                                                             (lambda (a b) (minusp (compare-values a b c))))))
                                          (when (null sorted) (return-from run))
                                          (if (not (eq (and rev t) (and (nth j descs) t))) (reverse sorted) sorted))))
                   (lo-op nil) (lo-v nil) (hi-op nil) (hi-v nil))
              (when lf
                (multiple-value-setq (lo-op lo-v) (funcall lf env))
                (when (null lo-v) (return-from run)))
              (when hf
                (multiple-value-setq (hi-op hi-v) (funcall hf env))
                (when (null hi-v) (return-from run)))
              (dolist (prefix (cartesian lists))
                (let ((hits '()))
                  (catch :index-done
                    (flet ((visit (vals)
                             (unless (zerop (funcall cmp vals prefix)) (throw :index-done nil))
                             (if (or lf hf)
                                 (let ((v (nth n-eq vals)))
                                   (when (value-in-bounds-p v lo-op lo-v hi-op hi-v rcoll)
                                     (push vals hits))
                                   ;; past the upper bound of an ascending column: done
                                   (when (and hf (not rdesc) (not (eq v :null))
                                              (let ((c (compare-values v hi-v rcoll)))
                                                (if (eq hi-op :lt) (>= c 0) (> c 0))))
                                     (throw :index-done nil)))
                                 (push vals hits))))
                      ;; seek to the lower bound of an ascending range column
                      (let ((probe (if (and lo-v (not (eq lo-v :null)) (not rdesc))
                                       (append prefix (list lo-v))
                                       prefix)))
                        (if probe
                            (map-index (table-owner table) (index-root* wx table) #'visit :probe probe :cmp cmp)
                            (map-index (table-owner table) (index-root* wx table) #'visit)))))
                  (dolist (vals (if rev hits (nreverse hits)))
                    (let ((row (index-entry-row table wx covering vals wanted)))
                      (when row (funcall fn row)))))))))))))

(defun index-root* (wx table)
  (if (wx-pk wx) (table-root table) (index-root (wx-index wx))))

(defun auto-index-iterate (lp ws scope rev source-fn)
  "An automatic index: built from the source's rows the first time the loop
runs, then searched."
  (let* ((wx (wl-wx lp))
         (n-eq (wl-n-eq lp))
         (cols (coerce (wx-cols wx) 'list))
         (colls (coerce (wx-colls wx) 'list))
         (key-cmp (index-key-cmp colls nil))
         (affs (src-affinities (fsrc-src (ws-fsrc ws))))
         (partial-fns (mapcar (lambda (term) (compile-expr (substitute-fixed (wt-origin term)) scope))
                              (ws-auto-partial ws)))
         (eq-fns (loop for term in (wl-lterms lp)
                       collect (probe-values term scope (svref affs (wt-col term)))))
         (si (ws-i ws))
         (entries nil))
    (declare (ignorable n-eq))
    (lambda (env fn)
      (unless entries
        (let ((acc '()) (seq 0))
          (funcall source-fn env
                   (lambda (row)
                     (let ((saved (svref (env-rows env) si)))
                       (setf (svref (env-rows env) si) row)
                       (when (every (lambda (f) (eq (truth (funcall f env)) t)) partial-fns)
                         (push (cons (loop for c in cols
                                           collect (if (eq c :rowid)
                                                       (let ((r (svref row (1- (length row)))))
                                                         (if (eq r :null) (incf seq) r))
                                                       (svref row c)))
                                     row)
                               acc))
                       (setf (svref (env-rows env) si) saved))))
          (setf entries (coerce (stable-sort (nreverse acc) (lambda (a b) (minusp (funcall key-cmp (car a) (car b)))))
                                'vector))))
      (block run
        (let ((lists (loop for f in eq-fns for c in colls
                           collect (let ((vals (and f (funcall f env))))
                                     (when (null vals) (return-from run))
                                     (sort (remove-duplicates vals :test (lambda (a b) (zerop (compare-values a b c))))
                                           (lambda (a b) (minusp (compare-values a b c))))))))
          (dolist (prefix (if rev (reverse (cartesian lists)) (cartesian lists)))
            (let* ((n (length entries))
                   (start (let ((lo 0) (hi n))
                            (loop while (< lo hi)
                                  do (let ((mid (floor (+ lo hi) 2)))
                                       (if (minusp (funcall key-cmp (car (svref entries mid)) prefix))
                                           (setf lo (1+ mid))
                                           (setf hi mid))))
                            lo))
                   (end (loop for k from start below n
                              while (zerop (funcall key-cmp (car (svref entries k)) prefix))
                              finally (return k))))
              (if rev
                  (loop for k from (1- end) downto start do (funcall fn (cdr (svref entries k))))
                  (loop for k from start below end do (funcall fn (cdr (svref entries k))))))))))))

;;; ------------------------------------------------------------------
;;; From FROM items to planned levels



(defun refs-available-p (refs li)
  "Are the sources REFS (a list) all bound outside the loop for source LI?"
  (if *avail-mask*
      (every (lambda (r) (logbitp r *avail-mask*)) refs)
      (every (lambda (r) (< r li)) refs)))

(defun make-wsrc-for (fs i scope nsrc)
  (let* ((table (fsrc-table fs))
         (hint (fsrc-index-hint fs))
         (src (fsrc-src fs)))
    (cond
      ((null table)
       (let ((row-est (or (fsrc-row-est fs) 200)))
         (make-wsrc :i i :fsrc fs :kind :derived :mask (ash 1 i) :join (fsrc-join fs)
                    :row-est row-est :sz-row 1 :view-p t
                    :extra-prereq (if (fsrc-tvf fs)
                                      (logand (reduce #'logior (cdr (fsrc-tvf fs))
                                                      :key (lambda (a) (expr-usage a scope nsrc))
                                                      :initial-value 0)
                                              (lognot (ash 1 i)))
                                      0)
                    :auto-ok (and (not (fsrc-correlated fs)) (not (fsrc-recursive-ref fs)) (null (fsrc-tvf fs)))
                    :col-used (src-used src)
                    :probes (list (make-widx :ipk t :cols (vector :rowid) :n-key 1 :n-col 1
                                             :colls (vector :binary) :descs (vector nil)
                                             :row-est (vector row-est 0) :unique t :uniq-not-null t
                                             :on-error :replace :sz-row 1)))))
      ((table-vtab table)
       (make-wsrc :i i :fsrc fs :table table :kind :vtab :mask (ash 1 i) :join (fsrc-join fs)
                  :row-est 200 :sz-row 1 :col-used (src-used src)))
      (t
       (let* ((row-est 200)
              (sz (table-row-width table))
              (probes (cond ((index-p hint) (list (index-widx table hint row-est)))
                            ((and (eq hint :not) (not (table-without-rowid table)))
                             (list (first (make-probes table row-est sz))))
                            (t (make-probes table row-est sz)))))
         (make-wsrc :i i :fsrc fs :table table :kind :btree :mask (ash 1 i) :join (fsrc-join fs)
                    :row-est row-est :sz-row sz :probes probes :col-used (src-used src)
                    :auto-ok t :indexed-by (index-p hint) :not-indexed (eq hint :not)))))))




(defun source-display-name (fs)
  (if (fsrc-table fs)
      (src-label (fsrc-src fs))
      (or (fsrc-label fs) (src-label (fsrc-src fs)) "(subquery)")))

(defun omit-noop-joins (loops plan fsrcs req)
  "whereOmitNoopJoin: drop, innermost first, each LEFT JOIN loop (not the
first) whose table the result set and ORDER BY never read and no term but
its own ON clause mentions, when it matches at most one row or the query is
DISTINCT.  The reverse-scan bits stay where they were, as in SQLite."
  (let ((used (getf req :noop-used)))
    (when (and used (>= (length loops) 2))
      (let ((v (coerce loops 'vector)))
        (loop for k from (1- (length v)) downto 1
              do (let* ((lp (aref v k)) (i (wl-src lp)) (bit (ash 1 i)))
                   (when (and (eq (fsrc-join (nth i fsrcs)) :left)
                              (or (logtest (or (getf req :flags) 0) +wf-want-distinct+)
                                  (flag-p (wl-flags lp) +where-onerow+))
                              (not (logtest used bit))
                              (loop for term across (wc-terms (plan-wc plan))
                                    never (and (logtest (wt-prereq-all term) bit)
                                               (not (eql (wt-outer-on term) i)))))
                     (setf v (remove lp v)))))
        (setf loops (coerce v 'list)))))
  loops)

(defun plan-levels (fsrcs scope where ons)
  "Plan FSRCS and return (values levels final-filters)."
  (let* ((n (length fsrcs))
         (conjuncts
           (append (mapcar (lambda (c)
                             (if (eq (car c) :outer-on)
                                 (list (third c)
                                       (position (second c) fsrcs :key (lambda (fs) (src-name (fsrc-src fs)))
                                                                  :test #'equal)
                                       nil)
                                 (list c nil nil)))
                           (split-conjuncts where))
                   (loop for fs in fsrcs for on in ons for i from 0
                         append (let ((outer (member (fsrc-join fs) '(:left :right :full))))
                                  (mapcar (lambda (c) (list c (and outer i) (and (not outer) i)))
                                          (split-conjuncts on))))))
         (*usage-cache* (make-hash-table :test #'eq))
         (wsrcs (coerce (loop for fs in fsrcs for i from 0 collect (make-wsrc-for fs i scope n)) 'vector))
         (*vtab-order-ok* (and (plusp n) (eq (ws-kind (svref wsrcs 0)) :vtab)
                               *order-hint* (member (first *order-hint*) '(:rowid :dbstat)) t))
         (req *plan-request*)
         (plan (plan-where wsrcs scope conjuncts
                           :order-by (getf req :order-by) :flags (or (getf req :flags) 0)
                           :limit (getf req :limit) :distinct-list (getf req :distinct-list)))
         (*wsrcs* wsrcs) (*wc* (plan-wc plan))
         (loops (omit-noop-joins (plan-loops plan) plan fsrcs req))
         (pos (make-array n :initial-element nil))
         (fixed (some (lambda (fs) (member (fsrc-join fs) '(:right :full))) fsrcs))
         (floor-level (if fixed
                          (or (position-if (lambda (fs) (member (fsrc-join fs) '(:right :full)))
                                           fsrcs :from-end t)
                              0)
                          0))
         (placed (make-array (max n 1) :initial-element '()))
         (matches (make-array (max n 1) :initial-element '()))
         (finals '()))
    (setf *plan-result* plan)
    (loop for lp in loops for k from 0 do (setf (aref pos (wl-src lp)) k))
    ;; where each conjunct is evaluated
    (dolist (c conjuncts)
      (destructuring-bind (e outer inner) c
        (cond ((zerop n) (push e finals))
              (outer (when (aref pos outer)      ; else its join was omitted
                       (push e (aref matches (aref pos outer)))))
              (t (let* ((m (expr-usage e scope n))
                        (at (loop for i below n when (logbitp i m) maximize (aref pos i))))
                   (push e (aref placed (max (if (null inner) floor-level 0) (or at 0)))))))))
    (let ((levels '()) (bound 0)
          ;; an omitted join is ready from the start (whereOmitNoopJoin)
          (not-ready (reduce #'logior loops :key (lambda (lp) (ash 1 (wl-src lp))) :initial-value 0)))
      (loop for lp in loops for k from 0
            do (let* ((i (wl-src lp)) (ws (svref wsrcs i)) (fs (ws-fsrc ws))
                      (left (member (fsrc-join fs) '(:left :full)))
                      (right (member (fsrc-join fs) '(:right :full)))
                      (filter-asts (reverse (aref placed k)))
                      (match-asts (reverse (aref matches k)))
                      (rev (logbitp k (plan-rev plan))))
                 (when (flag-p (wl-flags lp) +where-auto-index+)
                   (setf (ws-auto-partial ws) (finalize-auto-index lp ws not-ready)))
                 (let ((iterate
                         (let ((*eqp-left* (and left t)) (*avail-mask* bound))
                           (cond
                             ((eq (ws-kind ws) :vtab)
                              (vtab-plan-access fs i (mapcar #'substitute-fixed
                                                             (cond (right nil) (left match-asts) (t filter-asts)))
                                                scope))
                             ((flag-p (wl-flags lp) +where-multi-or+)
                              (explain-multi-or lp ws (source-display-name fs) bound)
                              (setf (fsrc-scan-index fs) (lambda () nil))
                              (multi-or-iterate lp ws scope bound))
                             (t
                              (let ((node (eqp-table-note (explain-loop lp ws (source-display-name fs)
                                                                        (or (getf req :flags) 0)))))
                                (when (zerop k)
                                  (setf *eqp-first-loop*
                                        (list node *eqp-parent* fs
                                              (flag-p (wl-flags lp) +where-auto-index+)
                                              ;; constant terms WhereBegin codes first
                                              (some (lambda (term) (and (wt-base term) (not (wt-virtual term))
                                                                        (zerop (wt-prereq-all term))))
                                                    (wc-terms *wc*))))))
                              (setf (fsrc-scan-index fs)
                                    (let ((wx (wl-wx lp)))
                                      (lambda () (cond ((flag-p (wl-flags lp) +where-ipk+) :rowid)
                                                       ((and wx (wx-index wx))) (t nil)))))
                              (loop-iterate lp ws scope rev))))))
                   (push (make-level :index i :fsrc fs :iterate iterate :left-p (and left t)
                                     :right-p (and right t)
                                     :match (mapcar (lambda (c) (compile-expr (substitute-fixed c) scope)) match-asts)
                                     :filters (mapcar (lambda (c) (compile-expr (substitute-fixed c) scope)) filter-asts)
                                     :nullrow (make-null-row (1+ (src-ncols (fsrc-src fs)))))
                         levels))
                 (setf bound (logior bound (ash 1 i))
                       not-ready (logand not-ready (lognot (ash 1 i))))))
      (values (nreverse levels)
              (mapcar (lambda (c) (compile-expr (substitute-fixed c) scope)) finals)))))
