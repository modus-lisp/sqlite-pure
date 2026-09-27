;;;; fts3-expr.lisp — the FTS3/4 MATCH query language (fts3_expr.c), in the
;;;; "enhanced" syntax SQLite is normally built with: implicit AND, AND, OR,
;;;; NOT, NEAR and NEAR/n, "phrases", prefix*, ^first (FTS4), col:term and
;;;; parentheses.  Keywords are case-sensitive.  The tree is rebalanced as
;;;; SQLite rebalances it, since the evaluator (fts3-eval.lisp) walks it.

(in-package #:sqlite-pure)

(defstruct (f3token (:conc-name tk-))
  term                    ; byte string
  prefix-p first-p
  deferred                ; the deferred-token record, or NIL
  segcsr)                 ; F3MSR while loading

(defstruct (f3phrase (:conc-name ph-))
  ;; the phrase's doclist (Fts3Doclist)
  all (nall 0) next-docid (docid 0) free-list list-buf (list-off 0) (nlist 0)
  incr (doclist-token 0)
  or-poslist (or-docid 0)
  (tokens #())
  (column 0))

(defstruct (f3expr (:conc-name fx-))
  type (near 10)          ; :near :not :and :or :phrase
  parent left right phrase
  (docid 0) eof start deferred
  (iphrase 0) mi)

(defun fx-type-rank (x)
  (ecase (fx-type x) (:near 1) (:not 2) (:and 3) (:or 4) (:phrase 5)))

(defconstant +fts3-max-expr-depth+ 12)

(defstruct (f3parse (:conc-name pc-))
  tokenizer columns default-col fts4-p (nest 0) text)

(defun f3-space-p (b) (member b '(32 9 10 13 11 12)))

(defun f3-parse-error ()
  (throw :f3-parse :error))

(defun f3-get-next-token (pc col z start n)
  "getNextToken: (values expr-or-nil consumed status) where status is :ok or :done."
  (let ((i 0))
    (loop while (< i n)
          do (let ((c (aref z (+ start i))))
               (when (or (= c 40) (= c 41) (= c 34)) (return)))
             (incf i))
    (let ((toks (fts3-tokenize (pc-tokenizer pc) (subseq z start (+ start i)))))
      (if (plusp (length toks))
          (destructuring-bind (term tstart tend pos) (aref toks 0)
            (declare (ignore pos))
            (let* ((tok (make-f3token :term term))
                   (ph (make-f3phrase :tokens (vector tok) :column col))
                   (x (make-f3expr :type :phrase :phrase ph))
                   (iend tend) (istart tstart))
              (when (and (< iend n) (= (aref z (+ start iend)) 42))
                (setf (tk-prefix-p tok) t)
                (incf iend))
              (loop (if (and (pc-fts4-p pc) (> istart 0) (= (aref z (+ start istart -1)) 94))
                        (progn (setf (tk-first-p tok) t) (decf istart))
                        (return)))
              (values x iend :ok)))
          (values nil i (if (plusp i) :ok :done))))))

(defun f3-get-next-string (pc z start n)
  "getNextString: the phrase in Z[START, START+N)."
  (let* ((sub (subseq z start (+ start n)))
         (toks (fts3-tokenize (pc-tokenizer pc) sub))
         (tokens (map 'vector
                      (lambda (tk)
                        (destructuring-bind (term b e pos) tk
                          (declare (ignore pos))
                          (make-f3token :term term
                                        :prefix-p (and (< e n) (= (aref sub e) 42))
                                        :first-p (and (> b 0) (= (aref sub (1- b)) 94)))))
                      toks)))
    (make-f3expr :type :phrase
                 :phrase (make-f3phrase :tokens tokens :column (pc-default-col pc)))))

(defparameter +f3-keywords+ '(("OR" :or) ("AND" :and) ("NOT" :not) ("NEAR" :near)))

(defun f3-get-next-node (pc z start n)
  "getNextNode: (values expr consumed status), status :ok or :done."
  (let ((s start) (nin n))
    (loop while (and (> nin 0) (f3-space-p (aref z s))) do (incf s) (decf nin))
    (when (zerop nin) (return-from f3-get-next-node (values nil 0 :done)))
    ;; keywords
    (loop for (kw type) in +f3-keywords+
          do (let ((kn (length kw)))
               (when (and (>= nin kn)
                          (loop for i below kn always (= (aref z (+ s i)) (char-code (char kw i)))))
                 (let ((near 10) (nkey kn))
                   (when (and (eq type :near) (< (+ s 5) (length z))
                              (= (aref z (+ s 4)) 47) (<= 48 (aref z (+ s 5)) 57))
                     (let ((j (+ s 5)) (v 0) (overflow nil))
                       (loop while (and (< j (length z)) (<= 48 (aref z j) 57))
                             do (setf v (+ (* v 10) (- (aref z j) 48)))
                                (when (> v #x7fffffff) (setf overflow t))
                                (incf j))
                       ;; sqlite3Fts3ReadInt returns -1 on overflow
                       (if overflow
                           (setf nkey (+ nkey 1 -1))
                           (setf near v nkey (+ nkey 1 (- j s 5))))))
                   (let ((next (if (< (+ s nkey) (length z)) (aref z (+ s nkey)) 0)))
                     (when (or (f3-space-p next) (= next 34) (= next 40) (= next 41) (= next 0))
                       (return-from f3-get-next-node
                         (values (make-f3expr :type type :near near) (+ (- s start) nkey) :ok))))))))
    ;; a quoted phrase
    (when (= (aref z s) 34)
      (let ((ii 1))
        (loop while (and (< ii nin) (/= (aref z (+ s ii)) 34)) do (incf ii))
        (when (= ii nin) (f3-parse-error))
        (return-from f3-get-next-node
          (values (f3-get-next-string pc z (1+ s) (1- ii)) (+ (- s start) ii 1) :ok))))
    ;; parentheses
    (when (= (aref z s) 40)
      (incf (pc-nest pc))
      (when (> (pc-nest pc) 1000) (f3-parse-error))
      (multiple-value-bind (x consumed) (f3-expr-parse pc z (1+ s) (1- nin))
        (return-from f3-get-next-node (values x (+ (- s start) 1 consumed) :ok))))
    (when (= (aref z s) 41)
      (decf (pc-nest pc))
      (return-from f3-get-next-node (values nil (+ (- s start) 1) :done)))
    ;; a term, perhaps with a column filter
    (let ((col (pc-default-col pc)) (collen 0))
      (loop for name in (pc-columns pc)
            for ci from 0
            do (let* ((nb (utf8-encode name)) (ns (length nb)))
                 (when (and (> nin ns) (= (aref z (+ s ns)) 58)
                            (loop for i below ns
                                  always (= (ascii-lower (aref z (+ s i))) (ascii-lower (aref nb i)))))
                   (setf col ci collen (+ (- s start) ns 1))
                   (return))))
      (multiple-value-bind (x consumed status)
          (f3-get-next-token pc col z (+ start collen) (- n collen))
        (values x (+ consumed collen) status)))))

(defun ascii-lower (b) (if (<= 65 b 90) (+ b 32) b))

(defun f3-insert-binary-operator (head prev new)
  "insertBinaryOperator; returns the new head."
  (let ((split prev))
    (loop while (and (fx-parent split) (<= (fx-type-rank (fx-parent split)) (fx-type-rank new)))
          do (setf split (fx-parent split)))
    (if (fx-parent split)
        (progn (setf (fx-right (fx-parent split)) new
                     (fx-parent new) (fx-parent split)))
        (setf head new))
    (setf (fx-left new) split (fx-parent split) new)
    head))

(defun f3-expr-parse (pc z start n)
  "fts3ExprParse: (values expr consumed)."
  (let ((ret nil) (prev nil) (nin n) (pos start) (require-phrase t))
    (loop
      (multiple-value-bind (p nbyte status) (f3-get-next-node pc z pos nin)
        (when (eq status :done)
          (decf nin nbyte) (incf pos nbyte)
          (return))
        (when p
          (let* ((type (fx-type p))
                 (phrase-p (or (eq type :phrase) (fx-left p))))
            (when (and (not phrase-p) require-phrase) (f3-parse-error))
            (when (and phrase-p (not require-phrase))
              (let ((and-node (make-f3expr :type :and)))
                (setf ret (f3-insert-binary-operator ret prev and-node))
                (setf prev and-node)))
            (when (and prev
                       (or (and (eq type :near) (not phrase-p) (not (eq (fx-type prev) :phrase)))
                           (and (not (eq type :phrase)) phrase-p (eq (fx-type prev) :near))))
              (f3-parse-error))
            (if phrase-p
                (if ret
                    (setf (fx-right prev) p (fx-parent p) prev)
                    (setf ret p))
                (setf ret (f3-insert-binary-operator ret prev p)))
            (setf require-phrase (not phrase-p)))
          (setf prev p))
        (decf nin nbyte) (incf pos nbyte)))
    (when (and ret require-phrase) (f3-parse-error))
    (values ret (- n nin))))

;;; Rebalancing (fts3ExprBalance)

(defun f3-expr-balance (root max-depth)
  (when (zerop max-depth) (throw :f3-parse :error))
  (let ((type (fx-type root)))
    (case type
      ((:and :or)
       (let ((leaves (make-array max-depth :initial-element nil))
             (free nil)
             (p root))
         (loop while (eq (fx-type p) type) do (setf p (fx-left p)))
         (loop
           (let ((parent (fx-parent p)))
             (setf (fx-parent p) nil)
             (if parent (setf (fx-left parent) nil) (setf root nil))
             (setf p (f3-expr-balance p (1- max-depth)))
             (loop for lvl from 0 below max-depth
                   while p
                   do (if (null (aref leaves lvl))
                          (setf (aref leaves lvl) p p nil)
                          (let ((node free))
                            (setf free (fx-parent free))
                            (setf (fx-left node) (aref leaves lvl) (fx-right node) p
                                  (fx-parent (fx-left node)) node (fx-parent (fx-right node)) node
                                  (fx-parent node) nil)
                            (setf p node (aref leaves lvl) nil))))
             (when p (throw :f3-parse :too-big))
             (unless parent (return))
             (setf p (fx-right parent))
             (loop while (eq (fx-type p) type) do (setf p (fx-left p)))
             ;; remove PARENT from the tree; it becomes a free node
             (setf (fx-parent (fx-right parent)) (fx-parent parent))
             (if (fx-parent parent)
                 (setf (fx-left (fx-parent parent)) (fx-right parent))
                 (setf root (fx-right parent)))
             (setf (fx-parent parent) free free parent)))
         (setf p nil)
         (dotimes (i max-depth)
           (when (aref leaves i)
             (if (null p)
                 (setf p (aref leaves i) (fx-parent p) nil)
                 (let ((node free))
                   (setf free (fx-parent free))
                   (setf (fx-right node) p (fx-left node) (aref leaves i)
                         (fx-parent (fx-left node)) node (fx-parent (fx-right node)) node
                         (fx-parent node) nil)
                   (setf p node)))))
         p))
      (:not
       (let ((l (fx-left root)) (r (fx-right root)))
         (setf (fx-left root) nil (fx-right root) nil (fx-parent l) nil (fx-parent r) nil)
         (setf l (f3-expr-balance l (1- max-depth)) r (f3-expr-balance r (1- max-depth)))
         (setf (fx-left root) l (fx-parent l) root (fx-right root) r (fx-parent r) root)
         root))
      (t root))))

(defun f3-expr-depth-ok (x depth)
  (or (null x)
      (and (>= depth 0)
           (f3-expr-depth-ok (fx-left x) (1- depth))
           (f3-expr-depth-ok (fx-right x) (1- depth)))))

(defun f3-parse-query (f query default-col)
  "sqlite3Fts3ExprParse: the balanced expression tree for QUERY (a string),
or NIL for an empty query."
  (let* ((z (utf8-encode query))
         (pc (make-f3parse :tokenizer (f3-tokenizer f) :columns (f3-columns f)
                           :default-col default-col :fts4-p (f3-fts4-p f) :text query))
         (result
           (catch :f3-parse
             (let ((x (f3-expr-parse pc (f3-padded z 0 (length z) 8) 0 (length z))))
               (when (/= (pc-nest pc) 0) (f3-parse-error))
               (when x
                 (setf x (f3-expr-balance x +fts3-max-expr-depth+))
                 (unless (f3-expr-depth-ok x +fts3-max-expr-depth+) (throw :f3-parse :too-big)))
               (list x)))))
    (case result
      (:error (sql-error "malformed MATCH expression: [~a]" query))
      (:too-big (sql-error "FTS expression tree is too large (maximum depth ~d)" +fts3-max-expr-depth+))
      (t (first result)))))

(defun f3-expr-phrases (x)
  "The query's phrases in matchinfo order (the right side of NOT excluded)."
  (let ((out '()))
    (labels ((walk (e)
               (if (eq (fx-type e) :phrase)
                   (push e out)
                   (progn (walk (fx-left e))
                          (unless (eq (fx-type e) :not) (walk (fx-right e)))))))
      (when x (walk x)))
    (nreverse out)))
