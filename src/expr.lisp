;;;; expr.lisp — compiling expression ASTs to closures.
;;;;
;;;; A compiled expression is (lambda (env) value).  ENV holds, for each
;;;; FROM source of the current query level, the current row: a simple
;;;; vector of column values with the rowid in the last slot.  Correlated
;;;; subqueries reach outer levels through ENV-PARENT.

(in-package #:sqlite-pure)

(defvar *db* nil "The database a statement is running against.")
(defvar *active-triggers* '() "Names of the triggers currently executing.")
(defvar *params* #() "Bound parameter values, 1-based by position.")
(defvar *param-names* nil "alist name -> index for named parameters.")

(defstruct env rows parent agg win)

(defvar *functions* (make-hash-table :test #'equal)
  "name -> (min-args max-args fn); fn receives a list of argument values.")
(defvar *aggregates* (make-hash-table :test #'equal)
  "name -> (min-args max-args constructor); constructor returns (values step final).")

(defstruct src
  name                   ; alias or table name (for qualification)
  columns                ; simple-vector of column names
  affinities             ; simple-vector
  collations             ; simple-vector
  hidden                 ; list of column indexes hidden from unqualified * and lookup
  table                  ; TABLE or NIL
  (rowid-p t)
  (used nil))            ; bit vector of referenced columns, or :ALL

(defun mark-used (s ci)
  "Record that compiled code reads column CI of source S."
  (when (and s (integerp ci))
    (let ((u (src-used s)))
      (when (typep u 'simple-bit-vector)
        (setf (sbit u ci) 1)))))

(defun src-wanted (s)
  "The columns a scan of S must decode: a bit vector, or NIL for all."
  (let ((u (src-used s))) (if (eq u :all) nil u)))

(defstruct scope
  srcs parent
  agg-p                  ; compiling in aggregate context
  (aggs (make-array 0 :adjustable t :fill-pointer t))
  aliases                ; alist result-alias -> AST, fallback for resolution
  outer-ref              ; set when a column resolves to an enclosing scope
  in-agg-arg
  windows                ; window functions of this query level (NIL: not allowed here)
  window-defs)           ; alist from the WINDOW clause

(defun src-ncols (s) (length (src-columns s)))

;;; ------------------------------------------------------------------
;;; Name resolution

(defun resolve-column (scope table name)
  "Return (values depth src-index col-index src) or NIL.  COL-INDEX is
:ROWID for the rowid."
  (loop for sc = scope then (scope-parent sc)
        for depth from 0
        while sc
        do (let ((hits '()))
             (loop for s in (scope-srcs sc)
                   for si from 0
                   do (when (or (null table) (and (src-name s) (name= table (src-name s))))
                        (let ((ci (position name (src-columns s) :test #'name=)))
                          (cond ((and ci (or table (not (member ci (src-hidden s)))))
                                 (push (list si ci s) hits))
                                ((and (null ci) (rowid-name-p name) (src-rowid-p s)
                                      (or table (null (cdr (scope-srcs sc)))))
                                 (push (list si :rowid s) hits))))))
             (when hits
               (when (cdr hits)
                 (sql-error "ambiguous column name: ~@[~a.~]~a" table name))
               (destructuring-bind (si ci s) (car hits)
                 (return-from resolve-column (values depth si ci s))))))
  nil)

(defun mark-correlated (scope depth)
  (loop repeat depth
        for sc = scope then (scope-parent sc)
        while sc do (setf (scope-outer-ref sc) t)))

(defun alias-expr (scope name)
  (cdr (assoc name (scope-aliases scope) :test #'name=)))

;;; ------------------------------------------------------------------
;;; Static properties: affinity and collation

(defun expr-affinity (e scope)
  (case (car e)
    (:col (multiple-value-bind (depth si ci s) (resolve-column scope (second e) (third e))
            (declare (ignore depth si))
            (cond ((null s) (let ((a (and (null (second e)) (alias-expr scope (third e)))))
                              (and a (expr-affinity a scope))))
                  ((eq ci :rowid) :integer)
                  (t (svref (src-affinities s) ci)))))
    (:srccol (let ((s (nth (second e) (scope-srcs scope))) (ci (third e)))
               (if (eq ci :rowid) :integer (svref (src-affinities s) ci))))
    (:cast (type-affinity (third e)))
    (:collate (expr-affinity (second e) scope))
    (:subquery (select-first-affinity (second e) scope))
    (t nil)))

(defun expr-collation (e scope)
  "Return (values collation explicit-p); collation NIL when none."
  (case (car e)
    (:collate (values (collation-keyword (third e)) t))
    (:srccol (let ((s (nth (second e) (scope-srcs scope))) (ci (third e)))
               (values (if (eq ci :rowid) :binary (svref (src-collations s) ci)) nil)))
    (:col (multiple-value-bind (depth si ci s) (resolve-column scope (second e) (third e))
            (declare (ignore depth si))
            (cond ((and s (integerp ci)) (values (svref (src-collations s) ci) nil))
                  ((and (null s) (null (second e)) (alias-expr scope (third e)))
                   (expr-collation (alias-expr scope (third e)) scope))
                  (t (values nil nil)))))
    ((:binary)
     (if (member (second e) '(:concat :add :sub :mul :div :mod :bitand :bitor :shl :shr))
         (multiple-value-bind (c x) (expr-collation (third e) scope)
           (if x (values c x)
               (multiple-value-bind (c2 x2) (expr-collation (fourth e) scope)
                 (if x2 (values c2 x2) (values nil nil)))))
         (values nil nil)))
    ((:unary) (if (eq (second e) :not) (values nil nil) (expr-collation (third e) scope)))
    (t (values nil nil))))

(defun binary-collation (a b scope)
  (multiple-value-bind (ca xa) (expr-collation a scope)
    (multiple-value-bind (cb xb) (expr-collation b scope)
      (cond (xa ca) (xb cb) (ca ca) (cb cb) (t :binary)))))

(defun comparison-affinity (a1 a2)
  (flet ((numeric (a) (member a '(:integer :real :numeric))))
    (cond ((and a1 a2)
           (if (or (numeric a1) (numeric a2)) :numeric :blob))
          (t (or a1 a2)))))

(defun apply-comparison-affinity (v aff)
  (case aff
    ((:numeric :integer :real) (if (stringp v) (numeric-affinity-value v) v))
    (:text (if (or (integerp v) (floatp v)) (value-to-text v) v))
    (t v)))

;;; ------------------------------------------------------------------
;;; Arithmetic

(defun num-result (n)
  (if (and (integerp n) (not (i64-p n))) (safe-double n) n))

(defun sql-arith (op a b)
  (let ((x (value-to-number a)) (y (value-to-number b)))
    (when (or (eq x :null) (eq y :null)) (return-from sql-arith :null))
    (case op
      (:add (if (and (integerp x) (integerp y)) (num-result (+ x y))
                (float-op #'+ x y)))
      (:sub (if (and (integerp x) (integerp y)) (num-result (- x y))
                (float-op #'- x y)))
      (:mul (if (and (integerp x) (integerp y)) (num-result (* x y))
                (float-op #'* x y)))
      (:div (cond ((and (integerp x) (integerp y))
                   (if (zerop y) :null (num-result (truncate x y))))
                  ((zerop y) :null)
                  (t (float-op #'/ x y))))
      (:mod (cond ((and (integerp x) (integerp y))
                   (if (zerop y) :null (rem x y)))
                  ;; SQLite takes the integer value of each original operand
                  ;; (text: its integer prefix), then the remainder as REAL
                  (t (let ((ix (value-to-integer a)) (iy (value-to-integer b)))
                       (cond ((zerop iy) :null)
                             (t (float (rem ix (if (= iy -1) 1 iy)) 1d0))))))))))

(defun float-op (fn x y)
  (let ((fx (float x 1d0)) (fy (float y 1d0)))
    (handler-case
        (let ((r (funcall fn fx fy)))
          (if (float-nan-p r) :null r))
      (arithmetic-error ()
        ;; overflow: compute exactly and saturate to infinity
        (let ((ex (if (float-infinity-p fx) fx (rational fx)))
              (ey (if (float-infinity-p fy) fy (rational fy))))
          (if (or (floatp ex) (floatp ey))
              :null
              (safe-double (funcall fn ex ey))))))))

(defun sql-negate (v)
  (let ((x (value-to-number v)))
    (cond ((eq x :null) :null)
          ((integerp x) (num-result (- x)))
          (t (- x)))))

(defun wrap-i64 (n) (to-signed64 n))

(defun sql-bitop (op a b)
  (let ((x (value-to-integer a)) (y (value-to-integer b)))
    (when (or (eq x :null) (eq y :null)) (return-from sql-bitop :null))
    (ecase op
      (:bitand (logand x y))
      (:bitor (logior x y))
      ((:shl :shr)
       (let ((n (if (eq op :shl) y (- y))))
         (cond ((>= n 64) 0)
               ((<= n -64) (if (minusp x) -1 0))
               (t (wrap-i64 (ash x n)))))))))

;;; ------------------------------------------------------------------
;;; LIKE and GLOB

(defvar *like-matches-blobs* nil
  "NIL: LIKE and GLOB are false when either operand is a BLOB, as with
SQLite's recommended SQLITE_LIKE_DOESNT_MATCH_BLOBS build option (which
the Debian/Ubuntu libsqlite3 uses).  T: match the blob's bytes as text.")

(defun c-string (s)
  "S up to its first NUL: SQLite's pattern matchers see C strings."
  (let ((z (position (code-char 0) s))) (if z (subseq s 0 z) s)))

(defun like-match (pattern string escape)
  "SQL LIKE: % and _, ASCII case-insensitive."
  (let ((pn (length pattern)) (sn (length string)))
    (labels ((m (pj si)
               (loop
                 (when (>= pj pn) (return (= si sn)))
                 (let ((pc (char pattern pj)))
                   (cond ((and escape (char= pc escape))
                          (incf pj)
                          (when (>= pj pn) (return nil))
                          (unless (and (< si sn)
                                       (char= (ascii-char-fold (char pattern pj))
                                              (ascii-char-fold (char string si))))
                            (return nil))
                          (incf pj) (incf si))
                         ((char= pc #\%)
                          (loop while (and (< pj pn) (member (char pattern pj) '(#\% #\_))
                                           (not (and escape (char= (char pattern pj) escape))))
                                do (when (char= (char pattern pj) #\_)
                                     (when (>= si sn) (return-from m nil))
                                     (incf si))
                                   (incf pj))
                          (when (>= pj pn) (return t))
                          (loop for k from si to sn
                                do (when (m pj k) (return-from m t)))
                          (return nil))
                         ((char= pc #\_)
                          (when (>= si sn) (return nil))
                          (incf pj) (incf si))
                         (t
                          (unless (and (< si sn)
                                       (char= (ascii-char-fold pc) (ascii-char-fold (char string si))))
                            (return nil))
                          (incf pj) (incf si)))))))
      (m 0 0))))

(defun glob-match (pattern string)
  (let ((pn (length pattern)) (sn (length string)))
    (labels ((m (pj si)
               (loop
                 (when (>= pj pn) (return (= si sn)))
                 (let ((pc (char pattern pj)))
                   (case pc
                     (#\* (loop while (and (< pj pn) (member (char pattern pj) '(#\* #\?)))
                                do (when (char= (char pattern pj) #\?)
                                     (when (>= si sn) (return-from m nil))
                                     (incf si))
                                   (incf pj))
                      (when (>= pj pn) (return t))
                      (loop for k from si to sn do (when (m pj k) (return-from m t)))
                      (return nil))
                     (#\? (when (>= si sn) (return nil)) (incf pj) (incf si))
                     (#\[
                      (when (>= si sn) (return nil))
                      (let ((c (char string si)) (j (1+ pj)) (invert nil) (matched nil))
                        (when (and (< j pn) (char= (char pattern j) #\^)) (setf invert t) (incf j))
                        (when (and (< j pn) (char= (char pattern j) #\]))
                          (when (char= c #\]) (setf matched t))
                          (incf j))
                        (loop while (and (< j pn) (char/= (char pattern j) #\]))
                              do (if (and (< (+ j 2) pn) (char= (char pattern (1+ j)) #\-)
                                          (char/= (char pattern (+ j 2)) #\]))
                                     (progn (when (char<= (char pattern j) c (char pattern (+ j 2)))
                                              (setf matched t))
                                            (incf j 3))
                                     (progn (when (char= c (char pattern j)) (setf matched t))
                                            (incf j))))
                        (when (>= j pn) (return nil))
                        (unless (if invert (not matched) matched) (return nil))
                        (setf pj (1+ j)) (incf si)))
                     (t (unless (and (< si sn) (char= pc (char string si))) (return nil))
                        (incf pj) (incf si)))))))
      (m 0 0))))

;;; ------------------------------------------------------------------
;;; Compilation

(defun bool (x) (if x 1 0))

(defun truth (v)
  "Three-valued truth of V: T, NIL or :NULL."
  (value-truthy v))

(defun param-value (key)
  (let ((idx (if (integerp key)
                 key
                 (or (cdr (assoc key *param-names* :test #'string=))
                     (sql-error "unknown parameter ~a" key)))))
    (if (<= 1 idx (length *params*))
        (svref *params* (1- idx))
        :null)))

(defun lisp-to-sql (v)
  "Normalise a Lisp value supplied as a parameter."
  (cond ((or (eq v :null) (null v)) :null)
        ((eq v t) 1)
        ((integerp v) (if (i64-p v) v (safe-double v)))
        ((floatp v) (float v 1d0))
        ((rationalp v) (safe-double v))
        ((stringp v) (coerce v 'simple-string))
        ((typep v '(vector (unsigned-byte 8))) (coerce v 'blob))
        ((symbolp v) (string v))
        (t (sql-error "cannot bind value ~s" v))))

(defun compile-column-access (depth si ci)
  (let ((slot (if (eq ci :rowid) -1 ci)))
    (flet ((get-row (env)
             (let ((e env))
               (loop repeat depth do (setf e (env-parent e)))
               (svref (env-rows e) si))))
      (if (= slot -1)
          (lambda (env) (let ((row (get-row env))) (svref row (1- (length row)))))
          (lambda (env) (svref (get-row env) slot))))))

(defun compile-expr (e scope)
  (ecase (car e)
    (:lit (let ((v (second e))) (lambda (env) (declare (ignore env)) v)))
    (:param (let ((k (second e))) (lambda (env) (declare (ignore env)) (param-value k))))
    (:col
     (multiple-value-bind (depth si ci s) (resolve-column scope (second e) (third e))
       (cond (depth
              (mark-used s ci)
              (when (plusp depth) (mark-correlated scope depth))
              (compile-column-access depth si ci))
             ((and (null (second e)) (alias-expr scope (third e)))
              (compile-expr (alias-expr scope (third e)) scope))
             ;; SQLite treats an unresolvable double-quoted name as a string
             ((and (null (second e)) (stringp (third e)) (eq (fourth e) :quoted))
              (let ((s (third e))) (lambda (env) (declare (ignore env)) s)))
             (t (sql-error "no such column: ~@[~a.~]~a" (second e) (third e))))))
    (:srccol (mark-used (nth (second e) (scope-srcs scope)) (third e))
             (compile-column-access 0 (second e) (third e)))
    (:star (sql-error "misuse of *"))
    (:unary (compile-unary e scope))
    (:binary (compile-binary e scope))
    (:collate (compile-expr (second e) scope))
    (:isnull
     (let ((f (compile-expr (second e) scope)) (neg (third e)))
       (lambda (env) (bool (if neg (not (eq (funcall f env) :null)) (eq (funcall f env) :null))))))
    (:between (compile-between e scope))
    (:in (compile-in e scope))
    (:like (compile-like e scope))
    (:case (compile-case e scope))
    (:cast (let ((f (compile-expr (second e) scope)) (ty (third e)))
             (lambda (env) (cast-value (funcall f env) ty))))
    (:fn (compile-function e scope))
    (:winfn (if (scope-windows scope)
                (compile-window-call e scope)
                (sql-error "misuse of window function ~a()" (second e))))
    (:subquery (compile-scalar-subquery (second e) scope))
    (:exists (compile-exists (second e) scope))
    (:rowvalue (sql-error "row value misused"))
    (:raise (compile-raise e scope))))

(defun compile-unary (e scope)
  (let ((f (compile-expr (third e) scope)))
    (ecase (second e)
      (:neg (lambda (env) (sql-negate (funcall f env))))
      (:pos f)
      (:bitnot (lambda (env) (let ((v (value-to-integer (funcall f env))))
                               (if (eq v :null) :null (lognot v)))))
      (:not (lambda (env) (let ((tv (truth (funcall f env))))
                            (if (eq tv :null) :null (bool (not tv)))))))))

(defun compile-comparison (op a b scope)
  "Compile A <op> B with SQLite's affinity and collation rules."
  (when (or (eq (car a) :rowvalue) (eq (car b) :rowvalue))
    (return-from compile-comparison (compile-rowvalue-comparison op a b scope)))
  (let* ((fa (compile-expr a scope))
         (fb (compile-expr b scope))
         (aff (comparison-affinity (expr-affinity a scope) (expr-affinity b scope)))
         (coll (binary-collation a b scope))
         (test (ecase op
                 (:eq #'zerop) (:ne (lambda (c) (/= c 0)))
                 (:lt #'minusp) (:le (lambda (c) (<= c 0)))
                 (:gt #'plusp) (:ge (lambda (c) (>= c 0)))
                 (:is #'zerop) (:isnot (lambda (c) (/= c 0))))))
    (if (member op '(:is :isnot))
        (lambda (env)
          (let ((x (funcall fa env)) (y (funcall fb env)))
            (bool (cond ((and (eq x :null) (eq y :null)) (eq op :is))
                        ((or (eq x :null) (eq y :null)) (eq op :isnot))
                        (t (funcall test (compare-values (apply-comparison-affinity x aff)
                                                         (apply-comparison-affinity y aff)
                                                         coll)))))))
        (lambda (env)
          (let ((x (funcall fa env)) (y (funcall fb env)))
            (if (or (eq x :null) (eq y :null))
                :null
                (bool (funcall test (compare-values (apply-comparison-affinity x aff)
                                                    (apply-comparison-affinity y aff)
                                                    coll)))))))))

(defun compile-rowvalue-comparison (op a b scope)
  (let ((as (if (eq (car a) :rowvalue) (cdr a) (sql-error "row value misused")))
        (bs (cond ((eq (car b) :rowvalue) (cdr b))
                  ((eq (car b) :subquery) nil)
                  (t (sql-error "row value misused")))))
    (unless bs (sql-error "row value subqueries are not supported"))
    (unless (= (length as) (length bs)) (sql-error "row value misused"))
    (let ((pairs (loop for x in as for y in bs
                       collect (list (compile-expr x scope) (compile-expr y scope)
                                     (comparison-affinity (expr-affinity x scope) (expr-affinity y scope))
                                     (binary-collation x y scope)))))
      (lambda (env)
        ;; Lexicographic comparison with NULL propagation.
        (let ((result 0) (unknown nil))
          (loop for (fa fb aff coll) in pairs
                do (let ((x (funcall fa env)) (y (funcall fb env)))
                     (if (or (eq x :null) (eq y :null))
                         (progn (setf unknown t)
                                (when (member op '(:eq :ne)) nil)
                                (unless (member op '(:eq :ne :is :isnot)) (return)))
                         (let ((c (compare-values (apply-comparison-affinity x aff)
                                                  (apply-comparison-affinity y aff) coll)))
                           (unless (zerop c) (setf result c unknown nil) (return))))))
          (cond ((and unknown (zerop result)) :null)
                (t (bool (ecase op
                           ((:eq :is) (zerop result)) ((:ne :isnot) (/= result 0))
                           (:lt (minusp result)) (:le (<= result 0))
                           (:gt (plusp result)) (:ge (>= result 0)))))))))))

(defun compile-binary (e scope)
  (destructuring-bind (op a b) (cdr e)
    (case op
      (:and (let ((fa (compile-expr a scope)) (fb (compile-expr b scope)))
              (lambda (env)
                (let ((x (truth (funcall fa env))))
                  (if (null x)
                      0
                      (let ((y (truth (funcall fb env))))
                        (cond ((null y) 0)
                              ((or (eq x :null) (eq y :null)) :null)
                              (t 1))))))))
      (:or (let ((fa (compile-expr a scope)) (fb (compile-expr b scope)))
             (lambda (env)
               (let ((x (truth (funcall fa env))))
                 (if (eq x t)
                     1
                     (let ((y (truth (funcall fb env))))
                       (cond ((eq y t) 1)
                             ((or (eq x :null) (eq y :null)) :null)
                             (t 0))))))))
      ((:eq :ne :lt :le :gt :ge :is :isnot) (compile-comparison op a b scope))
      (:concat (let ((fa (compile-expr a scope)) (fb (compile-expr b scope)))
                 (lambda (env)
                   (let ((x (funcall fa env)) (y (funcall fb env)))
                     (if (or (eq x :null) (eq y :null))
                         :null
                         (concatenate 'string (value-to-text x) (value-to-text y)))))))
      ((:add :sub :mul :div :mod)
       (let ((fa (compile-expr a scope)) (fb (compile-expr b scope)))
         (lambda (env) (sql-arith op (funcall fa env) (funcall fb env)))))
      ((:bitand :bitor :shl :shr)
       (let ((fa (compile-expr a scope)) (fb (compile-expr b scope)))
         (lambda (env) (sql-bitop op (funcall fa env) (funcall fb env))))))))

(defun compile-between (e scope)
  (destructuring-bind (x lo hi negated) (cdr e)
    (let ((ge (compile-comparison :ge x lo scope))
          (le (compile-comparison :le x hi scope)))
      (lambda (env)
        (let* ((a (truth (funcall ge env)))
               (b (if (null a) nil (truth (funcall le env))))
               (r (cond ((or (null a) (null b)) nil)
                        ((or (eq a :null) (eq b :null)) :null)
                        (t t))))
          (cond ((eq r :null) :null)
                (negated (bool (not r)))
                (t (bool r))))))))

(defun in-result (x candidates aff coll negated)
  "SQL IN over a list of candidate values."
  (if (eq x :null)
      (if (null candidates) (bool negated) :null)
      (let ((xv (apply-comparison-affinity x aff))
            (saw-null nil))
        (dolist (c candidates)
          (if (eq c :null)
              (setf saw-null t)
              (when (zerop (compare-values xv (apply-comparison-affinity c aff) coll))
                (return-from in-result (bool (not negated))))))
        (if saw-null :null (bool negated)))))

(defun compile-in (e scope)
  (destructuring-bind (x rhs negated) (cdr e)
    (let ((fx (compile-expr x scope))
          (xaff (expr-affinity x scope)))
      (ecase (car rhs)
        (:list
         (let* ((items (second rhs))
                (fns (mapcar (lambda (i) (compile-expr i scope)) items))
                (colls (mapcar (lambda (i) (binary-collation x i scope)) items))
                ;; IN (list) compares with the left operand's affinity only
                (affs (mapcar (lambda (i) (declare (ignore i)) xaff) items)))
           (lambda (env)
             (let ((v (funcall fx env)))
               (if (eq v :null)
                   (if items :null (bool negated))
                   (block scan
                     (let ((saw-null nil))
                       (loop for f in fns for coll in colls for aff in affs
                             do (let ((c (funcall f env)))
                                  (if (eq c :null)
                                      (setf saw-null t)
                                      (when (zerop (compare-values (apply-comparison-affinity v aff)
                                                                   (apply-comparison-affinity c aff)
                                                                   coll))
                                        (return-from scan (bool (not negated)))))))
                       (if saw-null :null (bool negated)))))))))
        ((:select :table)
         (let* ((sel (if (eq (car rhs) :select)
                         (second rhs)
                         (make-sel :cores (list (make-select-core
                                                 :cols (list (list :star nil))
                                                 :from (list (list :source (list :table (second rhs) nil nil)
                                                                   :join :first)))))))
                (sub (multiple-value-list (compile-subselect sel scope)))
                (correlated (second sub))
                (sub (first sub))
                (saff (select-first-affinity sel scope))
                (aff (comparison-affinity xaff saff))
                (coll (multiple-value-bind (c x?) (expr-collation x scope)
                        (declare (ignore x?))
                        (or c (select-first-collation sel scope) :binary)))
                (cache nil))
           (lambda (env)
             (let ((vals (if (and cache (car cache))
                             (cdr cache)
                             (let ((rows (funcall sub env)))
                               (when (and rows (/= (length (first rows)) 1))
                                 (sql-error "sub-select returns ~d columns - expected 1"
                                            (length (first rows))))
                               (let ((vs (mapcar #'first rows)))
                                 (unless correlated
                                   (setf cache (cons t vs)))
                                 vs)))))
               (in-result (funcall fx env) vals aff coll negated)))))))))

(defun compile-like (e scope)
  (destructuring-bind (kind x pat esc negated) (cdr e)
    (let ((fx (compile-expr x scope))
          (fp (compile-expr pat scope))
          (fe (and esc (compile-expr esc scope))))
      (lambda (env)
        (let ((s (funcall fx env)) (p (funcall fp env))
              (ec (and fe (funcall fe env))))
          (cond
            ((and (not *like-matches-blobs*) (or (blobp s) (blobp p))) (bool negated))
            ((or (eq s :null) (eq p :null) (eq ec :null))
              :null)
            (t
              (let* ((ss (c-string (value-to-text s))) (ps (c-string (value-to-text p)))
                     (m (if (eq kind :glob)
                            (glob-match ps ss)
                            (let ((escs (and ec (value-to-text ec))))
                              (when (and escs (/= (length escs) 1))
                                (sql-error "ESCAPE expression must be a single character"))
                              (like-match ps ss (and escs (char escs 0)))))))
                (bool (if negated (not m) m))))))))))

(defun compile-case (e scope)
  (destructuring-bind (base whens else) (cdr e)
    (let ((fe (if else (compile-expr else scope) (lambda (env) (declare (ignore env)) :null))))
      (if base
          (let ((tests (loop for (w th) in whens
                             collect (cons (compile-comparison :eq base w scope)
                                           (compile-expr th scope)))))
            (lambda (env)
              (loop for (tf . thf) in tests
                    do (when (eq (truth (funcall tf env)) t) (return (funcall thf env)))
                    finally (return (funcall fe env)))))
          (let ((tests (loop for (w th) in whens
                             collect (cons (compile-expr w scope) (compile-expr th scope)))))
            (lambda (env)
              (loop for (tf . thf) in tests
                    do (when (eq (truth (funcall tf env)) t) (return (funcall thf env)))
                    finally (return (funcall fe env)))))))))

(defun compile-raise (e scope)
  (declare (ignore scope))
  (destructuring-bind (kind msg) (cdr e)
    (let ((k (string-upcase-ascii kind))
          (m (and msg (second msg))))
      (unless *active-triggers*
        (sql-error "RAISE() may only be used within a trigger-program"))
      (lambda (env)
        (declare (ignore env))
        (cond ((string= k "IGNORE") (throw :raise-ignore :ignore))
              (t (conflict-fail (cond ((string= k "ROLLBACK") :rollback)
                                      ((string= k "FAIL") :fail)
                                      (t :abort))
                                "~a" (or m "raise"))))))))

;;; ------------------------------------------------------------------
;;; Subqueries (the select engine provides COMPILE-SUBSELECT)

(defun compile-scalar-subquery (sel scope)
  (multiple-value-bind (sub correlated) (compile-subselect sel scope :limit-one t)
   (let ((cache nil))
    (lambda (env)
      (if cache
          (cdr cache)
          (let* ((rows (funcall sub env))
                 (v (if rows (first (first rows)) :null)))
            (when (and rows (/= (length (first rows)) 1))
              (sql-error "sub-select returns ~d columns - expected 1" (length (first rows))))
            (unless correlated (setf cache (cons t v)))
            v))))))

(defun compile-exists (sel scope)
  (multiple-value-bind (sub correlated) (compile-subselect sel scope :limit-one t)
    (let ((cache nil))
      (lambda (env)
        (if cache
            (cdr cache)
            (let ((v (bool (funcall sub env))))
              (unless correlated (setf cache (cons t v)))
              v))))))
