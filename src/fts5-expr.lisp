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
  (when (eq (fts-detail *fq-fts*) :none)
    (sql-error "fts5: column queries are not supported (detail=none)"))
  (cond ((eq e :eof) :eof)
        ((fnear-p e)
         (setf (fnr-colset e) (cond ((eq (fnr-colset e) :none) :none)
                                    ((fnr-colset e) (intersection (fnr-colset e) cs))
                                    (t (copy-list cs))))
         (when (null (fnr-colset e)) (setf (fnr-colset e) :none))
         e)
        (t (list (first e) (fq-apply-colset (second e) cs) (fq-apply-colset (third e) cs)))))

(defun fq-nearset ()
  (cond
    ((eq (fq-kind) :caret)
     (fq-next)
     (let ((p (fq-phrase)))
       (when (and p (fph-terms p)) (setf (fph-caret p) t))
       (fq-make-near (and p (list p)) 10)))
    ((and (eq (fq-kind) :string) (eq (fq-kind 1) :lp))
     (let ((w (fq-next)))
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
         ;; the word before the parenthesis is checked only now, as SQLite does
         (unless (and (string= (second w) "NEAR") (not (third w)))
           (sql-error "fts5: syntax error near \"~a\"" (second w)))
         (fq-make-near (nreverse phrases) dist))))
    ((eq (fq-kind) :string)
     (let ((p (fq-phrase))) (fq-make-near (and p (list p)) 10)))
    (t (fq-error))))

(defun fq-make-near (phrases dist)
  ;; detail=column/none support neither phrases nor NEAR (checked as the
  ;; nearset is built, so the first offender in parse order is reported)
  (when (and phrases (not (eq (fts-detail *fq-fts*) :full)))
    (let ((p (first phrases)))
      (when (or (cdr phrases) (cdr (fph-terms p)) (fph-caret p))
        (sql-error "fts5: ~a queries are not supported (detail!=full)"
                   (if (cdr phrases) "NEAR" "phrase")))))
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
                        (when (or (> (length (fph-terms p)) 1) (fph-caret p))
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

;;; ------------------------------------------------------------------
;;; The expression iterator (fts5_expr.c): nodes step through rowids in
;;; ascending order the way SQLite's do, so that the phrase position lists
;;; left behind at each matching row -- what bm25(), highlight() and
;;; snippet() see -- are the ones SQLite would leave.

(defstruct (titer (:constructor make-titer (entries))) entries (i 0))
(defun titer-eof (it) (>= (titer-i it) (length (titer-entries it))))
(defun titer-rowid (it) (car (aref (titer-entries it) (titer-i it))))
(defun titer-data (it) (cdr (aref (titer-entries it) (titer-i it))))
(defun titer-next (it) (incf (titer-i it)))
(defun titer-next-from (it from)
  (let ((v (titer-entries it)) (lo (titer-i it)) (hi (length (titer-entries it))))
    (loop while (< lo hi)
          do (let ((mid (floor (+ lo hi) 2)))
               (if (< (car (aref v mid)) from) (setf lo (1+ mid)) (setf hi mid))))
    (setf (titer-i it) lo)))

(defstruct (xnode (:conc-name xn-))
  type                   ; :term :string :and :or :not :eof
  near children (eof nil) (rowid 0) (nomatch nil))

(defstruct (xphrase (:conc-name xp-)) phrase iters (poslist '()) node)

(defvar *xphrases*)      ; FPHRASE -> XPHRASE

(defun xp (phrase) (gethash phrase *xphrases*))

(defun fts5-term-iterator (fts term colset s cache)
  "The index iterator for TERM (token prefix-p), filtered to COLSET: rows
whose filtered position list is empty stay (with empty data), as SQLite's do."
  (let* ((key (list (first term) (second term)))
         (h (or (gethash key cache)
                (setf (gethash key cache) (fts5-term-postings fts (first term) (second term) s))))
         (full (eq (fts-detail fts) :full))
         (entries '()))
    (maphash (lambda (rowid pos)
               (push (cons rowid
                           (cond ((eq (fts-detail fts) :none) (list t))
                                 ((null colset) pos)
                                 (full (remove-if-not (lambda (p) (member (ash p -32) colset)) pos))
                                 (t (remove-if-not (lambda (c) (member c colset)) pos))))
                     entries))
             h)
    (make-titer (coerce (sort entries #'< :key #'car) 'vector))))

(defun build-xnode (fts e s cache)
  (cond
    ((eq e :eof) (make-xnode :type :eof))
    ((fnear-p e)
     (let* ((phrases (fnr-phrases e))
            (single (and (null (cdr phrases))
                         (null (cdr (fph-terms (first phrases))))
                         (not (fph-caret (first phrases)))))
            (node (make-xnode :type (cond ((eq (fnr-colset e) :none) :eof) (single :term) (t :string))
                              :near e)))
       (unless (eq (fnr-colset e) :none)
         (dolist (p phrases)
           (setf (gethash p *xphrases*)
                 (make-xphrase :phrase p :node node
                               :iters (mapcar (lambda (tm) (fts5-term-iterator fts tm (fnr-colset e) s cache))
                                              (fph-terms p))))))
       node))
    (t (let ((kids (mapcar (lambda (x) (build-xnode fts x s cache)) (rest e))))
         (make-xnode :type (first e)
                     :children (if (eq (first e) :not)
                                   kids
                                   (loop for k in kids
                                         append (if (eq (xn-type k) (first e)) (xn-children k) (list k)))))))))

(defun xn-set-eof (n)
  (setf (xn-eof n) t (xn-nomatch n) nil)
  (dolist (c (xn-children n)) (xn-set-eof c)))

(defun xn-zero-poslist (n)
  (if (member (xn-type n) '(:term :string))
      (dolist (p (fnr-phrases (xn-near n))) (setf (xp-poslist (xp p)) '()))
      (dolist (c (xn-children n)) (xn-zero-poslist c))))

(defun xn-near-init (n)
  "fts5ExprNearInitAll: EOF if any term has no rows."
  (setf (xn-eof n) nil)
  (dolist (p (fnr-phrases (xn-near n)))
    (dolist (it (xp-iters (xp p)))
      (when (titer-eof it) (setf (xn-eof n) t) (return-from xn-near-init)))))

(defun xn-first (fts n)
  (setf (xn-eof n) nil (xn-nomatch n) nil)
  (case (xn-type n)
    ((:term :string) (xn-near-init n))
    (:eof (setf (xn-eof n) t))
    (t (let ((neof 0))
         (dolist (c (xn-children n)) (xn-first fts c) (when (xn-eof c) (incf neof)))
         (setf (xn-rowid n) (xn-rowid (first (xn-children n))))
         (ecase (xn-type n)
           (:and (when (plusp neof) (xn-set-eof n)))
           (:or (when (= neof (length (xn-children n))) (xn-set-eof n)))
           (:not (setf (xn-eof n) (xn-eof (first (xn-children n)))))))))
  (xn-test fts n))

(defun xn-test (fts n)
  (unless (xn-eof n)
    (case (xn-type n)
      (:term (xn-test-term fts n))
      (:string (xn-test-string fts n))
      (:and (xn-test-and fts n))
      (:or (xn-test-or n))
      (:not (xn-test-not fts n)))))

(defun xn-test-term (fts n)
  (let* ((p (first (fnr-phrases (xn-near n))))
         (it (first (xp-iters (xp p)))))
    (declare (ignore fts))
    (setf (xp-poslist (xp p)) (titer-data it)
          (xn-rowid n) (titer-rowid it)
          (xn-nomatch n) (null (titer-data it)))))

(defun xn-test-string (fts n)
  (let* ((near (xn-near n))
         (ilast (titer-rowid (first (xp-iters (xp (first (fnr-phrases near))))))))
    (loop
      (let ((match t))
        (dolist (p (fnr-phrases near))
          (dolist (it (xp-iters (xp p)))
            (unless (or (titer-eof it) (= (titer-rowid it) ilast))
              (setf match nil)
              (when (> ilast (titer-rowid it))
                (titer-next-from it ilast)
                (when (titer-eof it) (setf (xn-eof n) t) (return-from xn-test-string)))
              (setf ilast (titer-rowid it)))))
        (when match (return))))
    (setf (xn-rowid n) ilast
          (xn-nomatch n) (not (xn-near-test fts n)))))

(defun xn-phrase-is-match (fts p)
  "fts5ExprPhraseIsMatch: the phrase's positions at the current row."
  (declare (ignore fts))
  (let* ((x (xp p))
         (lists (mapcar #'titer-data (xp-iters x)))
         (out '()))
    (setf (xp-poslist x) '())
    (unless (some #'null lists)
      (let ((readers (coerce lists 'vector)) (nterm (length lists)))
        (block scan
          (loop
            (let ((ipos (first (aref readers 0))))
              (loop
                (let ((match t))
                  (dotimes (i nterm)
                    (let ((iadj (+ ipos i)))
                      (unless (eql (first (aref readers i)) iadj)
                        (setf match nil)
                        (loop while (< (first (aref readers i)) iadj)
                              do (pop (aref readers i))
                                 (when (null (aref readers i)) (return-from scan)))
                        (when (> (first (aref readers i)) iadj)
                          (setf ipos (- (first (aref readers i)) i))))))
                  (when match (return))))
              (when (or (not (fph-caret p)) (zerop (logand ipos #xffffffff)))
                (push ipos out))
              (dotimes (i nterm)
                (pop (aref readers i))
                (when (null (aref readers i)) (return-from scan))))))))
    (setf (xp-poslist x) (nreverse out))
    (not (null (xp-poslist x)))))

(defun xn-near-test (fts n)
  (let* ((near (xn-near n)) (phrases (fnr-phrases near)))
    (if (not (eq (fts-detail fts) :full))
        (let* ((p (first phrases)) (it (first (xp-iters (xp p)))))
          (setf (xp-poslist (xp p))
                (and (not (titer-eof it)) (= (titer-rowid it) (xn-rowid n)) (titer-data it)))
          (not (null (xp-poslist (xp p)))))
        (let ((all t))
          (dolist (p phrases)
            (if (or (cdr (fph-terms p)) (fnr-colset near) (fph-caret p))
                (unless (xn-phrase-is-match fts p) (setf all nil) (return))
                (setf (xp-poslist (xp p)) (titer-data (first (xp-iters (xp p)))))))
          (and all
               (or (null (cdr phrases))
                   (multiple-value-bind (ok trimmed)
                       (near-match phrases (mapcar (lambda (p) (xp-poslist (xp p))) phrases)
                                   (fnr-distance near))
                     (loop for p in phrases for tl in trimmed do (setf (xp-poslist (xp p)) tl))
                     ok)))))))

(defun xn-test-and (fts n)
  (let ((ilast (xn-rowid n)) (match nil))
    (loop until match
          do (setf (xn-nomatch n) nil match t)
             (dolist (c (xn-children n))
               (when (> ilast (xn-rowid c))
                 (xn-next fts c t ilast))
               (cond ((xn-eof c) (xn-set-eof n) (setf match t) (return))
                     ((/= ilast (xn-rowid c)) (setf match nil ilast (xn-rowid c))))
               (when (xn-nomatch c) (setf (xn-nomatch n) t))))
    (when (and (xn-nomatch n) (not (eq n *xroot*)))
      (xn-zero-poslist n))
    (setf (xn-rowid n) ilast)))

(defvar *xroot* nil)

(defun xn-compare (a b)
  (cond ((xn-eof b) -1) ((xn-eof a) 1)
        (t (signum (- (xn-rowid a) (xn-rowid b))))))

(defun xn-test-or (n)
  (let ((next (first (xn-children n))))
    (dolist (c (rest (xn-children n)))
      (let ((cmp (xn-compare next c)))
        (when (or (> cmp 0) (and (= cmp 0) (not (xn-nomatch c))))
          (setf next c))))
    (setf (xn-rowid n) (xn-rowid next) (xn-eof n) (xn-eof next) (xn-nomatch n) (xn-nomatch next))))

(defun xn-test-not (fts n)
  (destructuring-bind (p1 p2) (xn-children n)
    (loop until (xn-eof p1)
          do (let ((cmp (xn-compare p1 p2)))
               (when (> cmp 0)
                 (xn-next fts p2 t (xn-rowid p1))
                 (setf cmp (xn-compare p1 p2)))
               (when (or (/= cmp 0) (xn-nomatch p2)) (return))
               (xn-next fts p1 nil 0)))
    (setf (xn-eof n) (xn-eof p1) (xn-nomatch n) (xn-nomatch p1) (xn-rowid n) (xn-rowid p1))
    (when (xn-eof p1) (xn-zero-poslist p2))))

(defun xn-next (fts n from-valid from)
  (ecase (xn-type n)
    (:term
     (let ((it (first (xp-iters (xp (first (fnr-phrases (xn-near n))))))))
       (if from-valid (titer-next-from it from) (titer-next it))
       (if (titer-eof it)
           (setf (xn-eof n) t (xn-nomatch n) nil)
           (xn-test-term fts n))))
    (:string
     (setf (xn-nomatch n) nil)
     (let ((it (first (xp-iters (xp (first (fnr-phrases (xn-near n))))))))
       (if from-valid (titer-next-from it from) (titer-next it))
       (setf (xn-eof n) (titer-eof it))
       (unless (xn-eof n) (xn-test-string fts n))))
    (:and
     (xn-next fts (first (xn-children n)) from-valid from)
     (xn-test-and fts n))
    (:or
     (let ((ilast (xn-rowid n)))
       (dolist (c (xn-children n))
         (unless (xn-eof c)
           (when (or (= (xn-rowid c) ilast) (and from-valid (< (xn-rowid c) from)))
             (xn-next fts c from-valid from)))))
     (xn-test-or n))
    (:not
     (xn-next fts (first (xn-children n)) from-valid from)
     (xn-test-not fts n))
    (:eof (setf (xn-eof n) t))))

(defun fts5-evaluate (fts tree phrases &optional (s (fts-read-structure fts)))
  (let* ((cache (make-hash-table :test #'equal))
         (result (make-fts5-result :phrases phrases))
         (*xphrases* (make-hash-table :test #'eq))
         (root (build-xnode fts tree s cache))
         (*xroot* root)
         (rowids '()))
    (xn-first fts root)
    (loop while (and (not (xn-eof root)) (xn-nomatch root)) do (xn-next fts root nil 0))
    (loop until (xn-eof root)
          do (let ((r (xn-rowid root)) (v (make-array (length phrases) :initial-element nil)))
               (push r rowids)
               (loop for p across phrases for i from 0
                     do (let ((x (xp p)))
                          (when (and x (not (xn-eof (xp-node x))) (= (xn-rowid (xp-node x)) r))
                            (setf (aref v i) (xp-poslist x)))))
               (setf (gethash r (fres-instances result)) v))
             (loop do (xn-next fts root nil 0)
                   while (and (not (xn-eof root)) (xn-nomatch root))))
    (setf (fres-rowids result) (nreverse rowids))
    result))

(defun fts5-phrase-hits (fts phrase colset &optional (s (fts-read-structure fts)))
  "Number of rows the phrase alone matches (for bm25's IDF)."
  (hash-table-count (fts5-phrase-postings fts phrase (if (eq colset :none) nil colset) s (make-hash-table :test #'equal))))
