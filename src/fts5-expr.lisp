;;;; fts5-expr.lisp — the FTS5 query language: parsing and evaluation.
;;;;
;;;; Grammar (SQLite 3.40's fts5parse.y, precedence NOT > AND > OR):
;;;;   expr     := expr AND expr | expr OR expr | expr NOT expr
;;;;             | ( expr ) | colset : ( expr ) | cnearset+    (implicit AND)
;;;;   cnearset := nearset | colset : nearset
;;;;   nearset  := phrase | ^ phrase | NEAR ( phrase+ [, N] )
;;;;   phrase   := string [*] { + string [*] }
;;;;   colset   := name | - name | { name+ } | - { name+ }
;;;; A string is a bareword ([A-Za-z0-9_], or any non-ASCII byte) or a
;;;; "quoted" one; each is run through the table's tokenizer, and may yield
;;;; several terms.  Only upper-case AND, OR, NOT and NEAR are operators.
;;;;
;;;; A query evaluates to the ascending list of matching rowids; for each
;;;; row it also records every phrase's matching positions (the
;;;; "instances" bm25(), highlight() and snippet() see), trimmed by NEAR as
;;;; SQLite trims them.

(in-package #:sqlite-pure)

(defstruct (fphrase (:conc-name fph-))
  index                  ; 0-based, in query order
  terms                  ; list of (token prefix-p)
  caret)

(defstruct (fnear (:conc-name fnr-))
  phrases (distance 10) colset)   ; colset: list of column indexes, or NIL = all

;;; ------------------------------------------------------------------
;;; Lexing

(defun fts5-bareword-char-p (c)
  (let ((k (char-code c)))
    (or (>= k #x80) (<= 48 k 57) (<= 65 k 90) (<= 97 k 122) (= k 95) (= k #x1a))))

(defun fts5-lex (q)
  "List of (kind text) tokens; kind :string :lp :rp :lcp :rcp :colon :comma
:plus :star :minus :caret :and :or :not :eof."
  (let ((out '()) (i 0) (n (length q)))
    (loop
      (loop while (and (< i n) (member (char q i) '(#\Space #\Tab #\Newline #\Return))) do (incf i))
      (when (>= i n) (push (list :eof "") out) (return (nreverse out)))
      (let ((c (char q i)))
        (case c
          (#\( (push (list :lp "(") out) (incf i))
          (#\) (push (list :rp ")") out) (incf i))
          (#\{ (push (list :lcp "{") out) (incf i))
          (#\} (push (list :rcp "}") out) (incf i))
          (#\: (push (list :colon ":") out) (incf i))
          (#\, (push (list :comma ",") out) (incf i))
          (#\+ (push (list :plus "+") out) (incf i))
          (#\* (push (list :star "*") out) (incf i))
          (#\- (push (list :minus "-") out) (incf i))
          (#\^ (push (list :caret "^") out) (incf i))
          (#\Nul (push (list :eof "") out) (return (nreverse out)))
          (#\"
           (let ((j (1+ i)) (s (make-string-output-stream)))
             (loop
               (when (>= j n) (sql-error "unterminated string"))
               (let ((d (char q j)))
                 (cond ((and (char= d #\") (< (1+ j) n) (char= (char q (1+ j)) #\"))
                        (write-char #\" s) (incf j 2))
                       ((char= d #\") (incf j) (return))
                       (t (write-char d s) (incf j)))))
             (push (list :string (get-output-stream-string s) :quoted) out)
             (setf i j)))
          (t
           (unless (fts5-bareword-char-p c)
             (sql-error "fts5: syntax error near \"~a\"" c))
           (let ((j i))
             (loop while (and (< j n) (fts5-bareword-char-p (char q j))) do (incf j))
             (let ((w (subseq q i j)))
               (push (cond ((string= w "OR") (list :or w))
                           ((string= w "NOT") (list :not w))
                           ((string= w "AND") (list :and w))
                           (t (list :string w)))
                     out))
             (setf i j))))))))

;;; ------------------------------------------------------------------
;;; Parsing

(defvar *fq-toks*)
(defvar *fq-fts*)
(defvar *fq-phrases*)

(defun fq-peek (&optional (k 0)) (or (nth k *fq-toks*) (list :eof "")))
(defun fq-next () (or (pop *fq-toks*) (list :eof "")))
(defun fq-kind (&optional (k 0)) (first (fq-peek k)))
(defun fq-error () (sql-error "fts5: syntax error near \"~a\"" (second (fq-peek))))
(defun fq-expect (kind) (if (eq (fq-kind) kind) (fq-next) (fq-error)))

(defun fts5-parse-query (fts q &optional colset)
  "Parse Q.  Returns (values tree phrases)."
  (let ((trimmed (string-left-trim '(#\Space #\Tab #\Newline #\Return) q)))
    (when (and (plusp (length trimmed)) (char= (char trimmed 0) #\*))
      (sql-error "unknown special query: ~a" (subseq trimmed 1))))
  (let* ((*fq-toks* (fts5-lex q))
         (*fq-fts* fts)
         (*fq-phrases* '()))
    (when (eq (fq-kind) :eof) (fq-error))
    (let ((tree (fq-or)))
      (unless (eq (fq-kind) :eof) (fq-error))
      (when colset (setf tree (fq-apply-colset tree colset)))
      (values tree (coerce (reverse *fq-phrases*) 'vector)))))

(defun fq-or ()
  (let ((e (fq-and)))
    (loop while (eq (fq-kind) :or)
          do (fq-next) (setf e (fq-combine :or e (fq-and))))
    e))

(defun fq-and ()
  (let ((e (fq-not)))
    (loop while (eq (fq-kind) :and)
          do (fq-next) (setf e (fq-combine :and e (fq-not))))
    e))

(defun fq-not ()
  (let ((e (fq-unary)))
    (loop while (eq (fq-kind) :not)
          do (fq-next) (setf e (fq-combine :not e (fq-unary))))
    e))

(defun fq-combine (op a b)
  "Build a node; an empty nearset matches nothing (sqlite3Fts5ParseNode)."
  (flet ((eofp (x) (eq x :eof)))
    (ecase op
      (:and (if (or (eofp a) (eofp b)) :eof (list :and a b)))
      (:or (cond ((eofp a) b) ((eofp b) a) (t (list :or a b))))
      (:not (cond ((eofp a) :eof) ((eofp b) a) (t (list :not a b)))))))

(defun fq-colset-start-p ()
  "Does a colset (followed by a colon) start here?"
  (case (fq-kind)
    (:lcp t)
    (:minus t)
    (:string (eq (fq-kind 1) :colon))
    (t nil)))

(defun fq-unary ()
  (cond
    ((eq (fq-kind) :lp)
     (fq-next) (let ((e (fq-or))) (fq-expect :rp) e))
    ((and (fq-colset-start-p) (let ((save *fq-toks*))
                                (prog1 (progn (fq-colset) (and (eq (fq-kind) :colon) (eq (fq-kind 1) :lp)))
                                  (setf *fq-toks* save))))
     (let ((cs (fq-colset)))
       (fq-expect :colon) (fq-expect :lp)
       (let ((e (fq-or))) (fq-expect :rp) (fq-apply-colset e cs))))
    (t (fq-exprlist))))

(defun fq-exprlist ()
  "Juxtaposed nearsets: an implicit AND in which empty ones are dropped."
  (let ((e (fq-cnearset)))
    (loop while (member (fq-kind) '(:string :caret :lcp :minus))
          do (let ((f (fq-cnearset)))
               (setf e (cond ((eq e :eof) f) ((eq f :eof) e) (t (list :and e f))))))
    e))

(defun fq-cnearset ()
  (if (fq-colset-start-p)
      (let ((cs (fq-colset)))
        (fq-expect :colon)
        (fq-apply-colset (fq-nearset) cs))
      (fq-nearset)))

(defun fq-column-index (name)
  (or (position name (fts-columns *fq-fts*) :test #'name=)
      (sql-error "no such column: ~a" name)))

(defun fq-colset ()
  (let ((invert nil) (cols '()))
    (when (eq (fq-kind) :minus) (fq-next) (setf invert t))
    (case (fq-kind)
      (:lcp (fq-next)
       (unless (eq (fq-kind) :string) (fq-error))
       (loop while (eq (fq-kind) :string)
             do (pushnew (fq-column-index (second (fq-next))) cols))
       (fq-expect :rcp))
      (:string (push (fq-column-index (second (fq-next))) cols))
      (t (fq-error)))
    (if invert
        (loop for i below (length (fts-columns *fq-fts*)) unless (member i cols) collect i)
        (sort cols #'<))))

(defun fq-apply-colset (e cs)
  "Restrict every nearset under E to the columns CS (intersecting)."
  (cond ((eq e :eof) :eof)
        ((fnear-p e)
         (setf (fnr-colset e) (if (fnr-colset e) (intersection (fnr-colset e) cs) (copy-list cs)))
         (when (null (fnr-colset e)) (setf (fnr-colset e) :none))
         e)
        (t (list (first e) (fq-apply-colset (second e) cs) (fq-apply-colset (third e) cs)))))

(defun fq-nearset ()
  (cond
    ((eq (fq-kind) :caret)
     (fq-next)
     (let ((p (fq-phrase)))
       (when p
         (when (fph-terms p) (setf (fph-caret p) t)))
       (fq-make-near (and p (list p)) 10)))
    ((and (eq (fq-kind) :string) (eq (fq-kind 1) :lp))
     (let ((w (fq-next)))
       (unless (and (string= (second w) "NEAR") (not (third w)))
         (setf *fq-toks* (cons w *fq-toks*))
         (fq-error))
       (fq-next)
       (let ((phrases '()) (dist 10))
         (loop (let ((p (fq-phrase))) (when p (push p phrases)))
               (unless (eq (fq-kind) :string) (return)))
         (when (eq (fq-kind) :comma)
           (fq-next)
           (let ((d (fq-expect :string)))
             (unless (every #'digit-char-p (second d))
               (sql-error "expected integer, got \"~a\"" (second d)))
             (setf dist (parse-integer (second d)))))
         (fq-expect :rp)
         (fq-make-near (nreverse phrases) dist))))
    ((eq (fq-kind) :string)
     (let ((p (fq-phrase))) (fq-make-near (and p (list p)) 10)))
    (t (fq-error))))

(defun fq-make-near (phrases dist)
  (if (null phrases) :eof (make-fnear :phrases phrases :distance dist)))

(defun fq-phrase ()
  "phrase := string [*] { + string [*] }; NIL if it has no tokens."
  (let ((terms '()))
    (loop
      (let ((s (fq-expect :string))
            (star nil))
        (when (eq (fq-kind) :star) (fq-next) (setf star t))
        (let ((toks (map 'list #'first (fts5-tokenize (fts-tokenizer *fq-fts*) (second s)))))
          (loop for (tok . more) on toks
                do (push (list tok (and star (null more))) terms))))
      (if (eq (fq-kind) :plus) (fq-next) (return)))
    (when terms
      (let ((p (make-fphrase :index (length *fq-phrases*) :terms (nreverse terms))))
        (push p *fq-phrases*)
        p))))

;;; ------------------------------------------------------------------
;;; Evaluation

(defstruct (fts5-result (:conc-name fres-))
  rowids                 ; ascending list of matching rowids
  (instances (make-hash-table))   ; rowid -> vector (per phrase) of position lists
  phrases                ; vector of FPHRASE
  tree                   ; the parsed query
  (cache '()))           ; plist: :idf

(defun fts5-check-detail (fts tree)
  (labels ((walk (e)
             (cond ((eq e :eof) nil)
                   ((fnear-p e)
                    (unless (eq (fts-detail fts) :full)
                      (when (> (length (fnr-phrases e)) 1)
                        (sql-error "fts5: ~a queries are not supported (detail!=full)" "NEAR"))
                      (dolist (p (fnr-phrases e))
                        (when (> (length (fph-terms p)) 1)
                          (sql-error "fts5: phrase queries are not supported (detail!=full)"))))
                    (when (and (eq (fts-detail fts) :none) (fnr-colset e))
                      (sql-error "fts5: column queries are not supported (detail=none)")))
                   (t (walk (second e)) (walk (third e))))))
    (walk tree)))

(defun fts5-term-postings (fts token prefix-p s)
  "rowid -> positions (ascending) for TOKEN (all terms it prefixes, if PREFIX-P)."
  (let ((h (make-hash-table))
        (pidx (and prefix-p (position (length token) (fts-prefixes fts)))))
    (flet ((add (key)
             (dolist (e (fts-term-entries fts key s))
               (destructuring-bind (rowid . pl) e
                 (let ((pos (if (eq (fts-detail fts) :none) '() (decode-positions fts pl))))
                   (setf (gethash rowid h)
                         (if (nth-value 1 (gethash rowid h))
                             (merge 'list (gethash rowid h) pos #'<)
                             pos)))))))
      (cond ((not prefix-p) (add (fts-term-key #\0 token)))
            (pidx (add (fts-term-key (code-char (+ 49 pidx)) token)))
            (t (dolist (k (fts-prefix-terms fts (fts-term-key #\0 token) s)) (add k)))))
    (maphash (lambda (k v) (setf (gethash k h) (remove-duplicates v))) h)
    h))

(defun fts5-phrase-postings (fts phrase colset s cache)
  "rowid -> start positions of PHRASE (respecting COLSET and ^)."
  (let* ((terms (fph-terms phrase))
         (lists (mapcar (lambda (tm)
                          (let ((key (list (first tm) (second tm))))
                            (or (gethash key cache)
                                (setf (gethash key cache) (fts5-term-postings fts (first tm) (second tm) s)))))
                        terms))
         (out (make-hash-table))
         (full (eq (fts-detail fts) :full)))
    (maphash
     (lambda (rowid pos0)
       (when (every (lambda (h) (nth-value 1 (gethash rowid h))) (rest lists))
         (let ((starts
                 (if (not full)
                     (if (eq (fts-detail fts) :column) pos0 '(0))
                     (loop for p in pos0
                           when (and (loop for h in (rest lists)
                                           for k from 1
                                           always (member (+ p k) (gethash rowid h)))
                                     (or (not (fph-caret phrase)) (zerop (logand p #xffffffff))))
                             collect p))))
           (when (and colset (not (eq (fts-detail fts) :none)))
             (setf starts (remove-if-not (lambda (p) (member (if full (ash p -32) p) colset)) starts)))
           (when (or starts (and (not full) (not (eq (fts-detail fts) :column)) (null colset)))
             (setf (gethash rowid out) starts)))))
     (first lists))
    out))

(defun near-match (phrases poslists distance)
  "fts5ExprNearIsMatch: (values matched-p trimmed-poslists)."
  (let* ((n (length phrases))
         (eof (ash 1 62))
         (readers (map 'vector (lambda (pl) (let ((v (append pl (list eof eof)))) (cons (first v) (rest v))))
                       poslists))
         (outs (make-array n :initial-element '())))
    ;; reader: (current . rest) where (first rest) is the lookahead
    (flet ((cur (i) (car (aref readers i)))
           (look (i) (first (cdr (aref readers i))))
           (adv (i) (let ((r (aref readers i)))
                      (setf (aref readers i) (cons (first (cdr r)) (rest (cdr r))))
                      (= (car (aref readers i)) eof))))
      (block scan
        (loop
          (let ((imax (cur 0)))
            (loop
              (let ((match t))
                (dotimes (i n)
                  (let ((imin (- imax (length (fph-terms (nth i phrases))) distance)))
                    (when (or (< (cur i) imin) (> (cur i) imax))
                      (setf match nil)
                      (loop while (< (cur i) imin) do (when (adv i) (return-from scan)))
                      (when (> (cur i) imax) (setf imax (cur i))))))
                (when match (return))))
            (dotimes (i n)
              (unless (and (aref outs i) (= (first (aref outs i)) (cur i)))
                (push (cur i) (aref outs i))))
            (let ((iadv 0) (imin (look 0)))
              (dotimes (i n)
                (when (< (look i) imin) (setf imin (look i) iadv i)))
              (when (adv iadv) (return-from scan)))))))
    (values (not (null (aref outs 0)))
            (map 'list #'reverse outs))))

(defun fts5-evaluate (fts tree phrases &optional (s (fts-read-structure fts)))
  (let ((cache (make-hash-table :test #'equal))
        (result (make-fts5-result :phrases phrases))
        (nphr (length phrases)))
    (labels ((near-rows (nr)
               ;; rowid -> list of (phrase . positions)
               (if (eq (fnr-colset nr) :none)
                   (make-hash-table)
                   (let* ((cs (fnr-colset nr))
                          (maps (mapcar (lambda (p) (fts5-phrase-postings fts p cs s cache)) (fnr-phrases nr)))
                          (out (make-hash-table)))
                     (maphash
                      (lambda (rowid pl0)
                        (when (every (lambda (m) (nth-value 1 (gethash rowid m))) (rest maps))
                          (let ((pls (cons pl0 (mapcar (lambda (m) (gethash rowid m)) (rest maps)))))
                            (if (= (length pls) 1)
                                (setf (gethash rowid out) (list (cons (first (fnr-phrases nr)) pl0)))
                                (multiple-value-bind (ok trimmed)
                                    (near-match (fnr-phrases nr) pls (fnr-distance nr))
                                  (when ok
                                    (setf (gethash rowid out)
                                          (mapcar #'cons (fnr-phrases nr) trimmed))))))))
                      (first maps))
                     out)))
             (ev (e)
               ;; -> hash rowid -> list of (phrase . positions) contributing instances
               (cond ((eq e :eof) (make-hash-table))
                     ((fnear-p e) (near-rows e))
                     (t (let ((a (ev (second e))) (b (ev (third e))) (out (make-hash-table)))
                          (ecase (first e)
                            (:and (maphash (lambda (r v) (multiple-value-bind (w found) (gethash r b)
                                                           (when found (setf (gethash r out) (append v w)))))
                                           a))
                            (:or (maphash (lambda (r v) (setf (gethash r out) v)) a)
                                 (maphash (lambda (r v) (setf (gethash r out) (append (gethash r out) v))) b))
                            (:not (maphash (lambda (r v) (unless (nth-value 1 (gethash r b)) (setf (gethash r out) v)))
                                           a)))
                          out)))))
      (let ((rows (ev tree)))
        (setf (fres-rowids result) (sort (loop for k being the hash-keys of rows collect k) #'<))
        (maphash (lambda (rowid contribs)
                   (let ((v (make-array nphr :initial-element '())))
                     (dolist (c contribs)
                       (setf (aref v (fph-index (car c))) (cdr c)))
                     (setf (gethash rowid (fres-instances result)) v)))
                 rows)))
    result))

(defun fts5-phrase-hits (fts phrase colset &optional (s (fts-read-structure fts)))
  "Number of rows the phrase alone matches (for bm25's IDF)."
  (hash-table-count (fts5-phrase-postings fts phrase (if (eq colset :none) nil colset) s (make-hash-table :test #'equal))))
