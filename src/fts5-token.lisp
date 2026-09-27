;;;; fts5-token.lisp — FTS5 tokenizers: unicode61 (the default), ascii,
;;;; porter and trigram, as SQLite 3.40 tokenizes.
;;;;
;;;; A tokenizer turns a string into a vector of (token start end): the
;;;; folded token text and its byte offsets in the UTF-8 encoding of the
;;;; input, which highlight() and snippet() splice around.

(in-package #:sqlite-pure)

(defstruct (fts5-tokenizer (:conc-name ftok-))
  kind                   ; :unicode61 :ascii :porter :trigram
  (remove-diacritics 1)
  (token-chars '())      ; codepoints forced to be token characters
  (separators '())       ; ... forced to be separators
  (case-sensitive nil)   ; trigram
  parent)                ; porter: the tokenizer it wraps

;;; ------------------------------------------------------------------
;;; Character data (fts5-unicode-data.lisp)

(defun in-ranges-p (ranges cp)
  "Is CP in RANGES, a vector of inclusive (lo hi) pairs in order?"
  (let ((lo 0) (hi (1- (floor (length ranges) 2))))
    (loop while (<= lo hi)
          do (let ((mid (floor (+ lo hi) 2)))
               (cond ((< cp (aref ranges (* 2 mid))) (setf hi (1- mid)))
                     ((> cp (aref ranges (1+ (* 2 mid)))) (setf lo (1+ mid)))
                     (t (return-from in-ranges-p t)))))
    nil))

(defvar *u61-folds* (make-array 3 :initial-element nil))

(defun u61-fold-table (rd)
  (or (aref *u61-folds* rd)
      (setf (aref *u61-folds* rd)
            (let ((h (make-hash-table)))
              (dolist (run (ecase rd (0 +u61-fold-0+) (1 +u61-fold-1+) (2 +u61-fold-2+)) h)
                (destructuring-bind (start count step delta) run
                  (dotimes (i count)
                    (let ((cp (+ start (* i step))))
                      (setf (gethash cp h) (and delta (+ cp delta)))))))))))

(defun u61-fold (cp rd)
  "CP folded (and stripped of its diacritic, per RD); NIL if it vanishes."
  (multiple-value-bind (v found) (gethash cp (u61-fold-table rd))
    (if found v cp)))

(defun u61-token-char-p (tok cp)
  (cond ((member cp (ftok-token-chars tok)) t)
        ((member cp (ftok-separators tok)) nil)
        (t (not (in-ranges-p +u61-separators+ cp)))))

(defun u61-start-char-p (tok cp)
  (and (u61-token-char-p tok cp)
       (or (member cp (ftok-token-chars tok))
           (not (in-ranges-p +u61-no-start+ cp)))))

(defun utf8-len (cp)
  (cond ((< cp #x80) 1) ((< cp #x800) 2) ((< cp #x10000) 3) (t 4)))

;;; ------------------------------------------------------------------
;;; Tokenizing

(defun fts5-tokenize (tok text)
  "Vector of (token start end) for TEXT (a string)."
  (ecase (ftok-kind tok)
    (:unicode61 (tokenize-unicode61 tok text))
    (:ascii (tokenize-ascii tok text))
    (:porter (let ((out (fts5-tokenize (ftok-parent tok) text)))
               (map 'vector (lambda (e) (list (porter-stem (first e)) (second e) (third e))) out)))
    (:trigram (tokenize-trigram tok text))))

(defun tokenize-unicode61 (tok text)
  (let ((out (make-array 16 :adjustable t :fill-pointer 0))
        (rd (ftok-remove-diacritics tok))
        (n (length text))
        (i 0) (off 0)
        (buf (make-string-output-stream)))
    (loop
      ;; skip separators (a token begins only with a character that can start one)
      (loop while (and (< i n) (not (u61-start-char-p tok (char-code (char text i)))))
            do (incf off (utf8-len (char-code (char text i)))) (incf i))
      (when (>= i n) (return))
      (let ((start off))
        (loop while (and (< i n) (u61-token-char-p tok (char-code (char text i))))
              do (let* ((cp (char-code (char text i)))
                        (f (if (< cp #x80)
                               (if (<= 65 cp 90) (+ cp 32) cp)
                               (u61-fold cp rd))))
                   (when f (write-char (code-char f) buf))
                   (incf off (utf8-len cp))
                   (incf i)))
        (let ((s (get-output-stream-string buf)))
          (vector-push-extend (list s start off) out))))
    out))

(defun ascii-token-char-p (tok cp)
  (cond ((>= cp #x80) t)
        ((member cp (ftok-token-chars tok)) t)
        ((member cp (ftok-separators tok)) nil)
        (t (or (<= 48 cp 57) (<= 65 cp 90) (<= 97 cp 122)))))

(defun tokenize-ascii (tok text)
  ;; byte-oriented, as SQLite: after a token, the next byte is skipped unseen
  (let* ((bytes (utf8-encode text))
         (n (length bytes))
         (out (make-array 16 :adjustable t :fill-pointer 0))
         (is 0))
    (loop
      (loop while (and (< is n) (< (aref bytes is) #x80)
                       (not (ascii-token-char-p tok (aref bytes is))))
            do (incf is))
      (when (>= is n) (return))
      (let ((ie (1+ is)))
        (loop while (and (< ie n) (or (>= (aref bytes ie) #x80) (ascii-token-char-p tok (aref bytes ie))))
              do (incf ie))
        (let ((b (subseq bytes is ie)))
          (dotimes (k (length b)) (when (<= 65 (aref b k) 90) (incf (aref b k) 32)))
          (vector-push-extend (list (utf8-decode-lenient b) is ie) out))
        (setf is (1+ ie))))
    out))

(defun utf8-decode-lenient (bytes)
  (handler-case (utf8-decode bytes)
    (error () (map 'string #'code-char bytes))))

(defun tokenize-trigram (tok text)
  (let* ((n (length text))
         (out (make-array 16 :adjustable t :fill-pointer 0))
         (offs (make-array (1+ n))))
    (let ((o 0))
      (dotimes (i n) (setf (aref offs i) o) (incf o (utf8-len (char-code (char text i)))))
      (setf (aref offs n) o))
    (flet ((fold (c) (if (ftok-case-sensitive tok)
                         c
                         (let ((f (u61-fold (char-code c) 0))) (if f (code-char f) c)))))
      (loop for i from 0 to (- n 3)
            do (when (find #\Nul text :start i :end (+ i 3)) (return))
               (vector-push-extend (list (map 'string #'fold (subseq text i (+ i 3)))
                                         (aref offs i) (aref offs (+ i 3)))
                                   out)))
    out))

;;; ------------------------------------------------------------------
;;; The porter stemmer, step for step as fts5_tokenize.c (on UTF-8 bytes)

(defun porter-vowel-p (c y-is-vowel)
  (or (member c '(#\a #\e #\i #\o #\u)) (and y-is-vowel (char= c #\y))))

(defun porter-gobble-vc (s start end prev-cons)
  "Offset (relative to START) just past the first vowel-then-consonant, or 0."
  (let ((cons prev-cons) (i start))
    (loop while (< i end)
          do (setf cons (not (porter-vowel-p (char s i) cons)))
             (unless cons (return))
             (incf i))
    (incf i)
    (loop while (< i end)
          do (setf cons (not (porter-vowel-p (char s i) cons)))
             (when cons (return-from porter-gobble-vc (- (1+ i) start)))
             (incf i))
    0))

(defun porter-m>0 (s n) (plusp (porter-gobble-vc s 0 n nil)))
(defun porter-m>1 (s n)
  (let ((k (porter-gobble-vc s 0 n nil)))
    (and (plusp k) (plusp (porter-gobble-vc s k n t)))))
(defun porter-m=1 (s n)
  (let ((k (porter-gobble-vc s 0 n nil)))
    (and (plusp k) (zerop (porter-gobble-vc s k n t)))))
(defun porter-ostar (s n)
  (if (member (char s (1- n)) '(#\w #\x #\y))
      nil
      (let ((mask 0) (cons nil))
        (dotimes (i n)
          (setf cons (not (porter-vowel-p (char s i) cons))
                mask (+ (ash mask 1) (if cons 1 0))))
        (= (logand mask 7) 5))))
(defun porter-m>1-s-or-t (s n)
  (and (member (char s (1- n)) '(#\s #\t)) (porter-m>1 s n)))
(defun porter-has-vowel (s n)
  (loop for i below n thereis (porter-vowel-p (char s i) (> i 0))))

(defmacro porter-rules (s n key &rest cases)
  "Each case: (char (suffix replacement condition)...).  The first suffix
that matches is the only one tried, whether or not its condition holds."
  `(case ,key
     ,@(loop for (ch . rules) in cases
             collect `(,ch
                       (cond
                         ,@(loop for (suffix repl test) in rules
                                 collect `((and (> ,n ,(length suffix))
                                                (string= ,suffix ,s :start2 (- ,n ,(length suffix)) :end2 ,n))
                                           (when ,(if test `(,test ,s (- ,n ,(length suffix))) t)
                                             (replace ,s ,repl :start1 (- ,n ,(length suffix)))
                                             (setf ,n (+ (- ,n ,(length suffix)) ,(length repl)))))))))))

(defun porter-stem (token)
  (let* ((bytes (utf8-encode token)))
    (if (or (> (length bytes) 64) (< (length bytes) 3))
        token
        (let* ((s (make-string 80 :initial-element (code-char 0)))
               (n (length bytes)))
          (dotimes (i n) (setf (char s i) (code-char (aref bytes i))))
          (flet ((at (k) (if (>= k 0) (char s k) (code-char 0))))
            ;; step 1a
            (when (char= (at (1- n)) #\s)
              (cond ((char= (at (- n 2)) #\e)
                     (if (or (and (> n 4) (char= (at (- n 4)) #\s) (char= (at (- n 3)) #\s))
                             (and (> n 3) (char= (at (- n 3)) #\i)))
                         (decf n 2)
                         (decf n 1)))
                    ((char/= (at (- n 2)) #\s) (decf n 1))))
            ;; step 1b
            (let ((step1b nil))
              (case (at (- n 2))
                (#\e (cond ((and (> n 3) (string= "eed" s :start2 (- n 3) :end2 n))
                            (when (porter-m>0 s (- n 3))
                              (replace s "ee" :start1 (- n 3)) (decf n 1)))
                           ((and (> n 2) (string= "ed" s :start2 (- n 2) :end2 n))
                            (when (porter-has-vowel s (- n 2))
                              (decf n 2) (setf step1b t)))))
                (#\n (when (and (> n 3) (string= "ing" s :start2 (- n 3) :end2 n))
                       (when (porter-has-vowel s (- n 3))
                         (decf n 3) (setf step1b t)))))
              (when step1b
                (let ((b2 nil))
                  (case (at (- n 2))
                    (#\a (when (and (> n 2) (string= "at" s :start2 (- n 2) :end2 n))
                           (replace s "ate" :start1 (- n 2)) (incf n) (setf b2 t)))
                    (#\b (when (and (> n 2) (string= "bl" s :start2 (- n 2) :end2 n))
                           (replace s "ble" :start1 (- n 2)) (incf n) (setf b2 t)))
                    (#\i (when (and (> n 2) (string= "iz" s :start2 (- n 2) :end2 n))
                           (replace s "ize" :start1 (- n 2)) (incf n) (setf b2 t))))
                  (unless b2
                    (let ((c (at (1- n))))
                      (cond ((and (not (porter-vowel-p c nil)) (not (member c '(#\l #\s #\z)))
                                  (char= c (at (- n 2))))
                             (decf n))
                            ((and (porter-m=1 s n) (porter-ostar s n))
                             (setf (char s n) #\e) (incf n))))))))
            ;; step 1c
            (when (and (char= (at (1- n)) #\y) (porter-has-vowel s (1- n)))
              (setf (char s (1- n)) #\i))
            ;; step 2
            (porter-rules s n (at (- n 2))
              (#\a ("ational" "ate" porter-m>0) ("tional" "tion" porter-m>0))
              (#\c ("enci" "ence" porter-m>0) ("anci" "ance" porter-m>0))
              (#\e ("izer" "ize" porter-m>0))
              (#\g ("logi" "log" porter-m>0))
              (#\l ("bli" "ble" porter-m>0) ("alli" "al" porter-m>0) ("entli" "ent" porter-m>0)
                   ("eli" "e" porter-m>0) ("ousli" "ous" porter-m>0))
              (#\o ("ization" "ize" porter-m>0) ("ation" "ate" porter-m>0) ("ator" "ate" porter-m>0))
              (#\s ("alism" "al" porter-m>0) ("iveness" "ive" porter-m>0) ("fulness" "ful" porter-m>0)
                   ("ousness" "ous" porter-m>0))
              (#\t ("aliti" "al" porter-m>0) ("iviti" "ive" porter-m>0) ("biliti" "ble" porter-m>0)))
            ;; step 3
            (porter-rules s n (at (- n 2))
              (#\a ("ical" "ic" porter-m>0))
              (#\s ("ness" "" porter-m>0))
              (#\t ("icate" "ic" porter-m>0) ("iciti" "ic" porter-m>0))
              (#\u ("ful" "" porter-m>0))
              (#\v ("ative" "" porter-m>0))
              (#\z ("alize" "al" porter-m>0)))
            ;; step 4
            (porter-rules s n (at (- n 2))
              (#\a ("al" "" porter-m>1))
              (#\c ("ance" "" porter-m>1) ("ence" "" porter-m>1))
              (#\e ("er" "" porter-m>1))
              (#\i ("ic" "" porter-m>1))
              (#\l ("able" "" porter-m>1) ("ible" "" porter-m>1))
              (#\n ("ant" "" porter-m>1) ("ement" "" porter-m>1) ("ment" "" porter-m>1) ("ent" "" porter-m>1))
              (#\o ("ion" "" porter-m>1-s-or-t) ("ou" "" porter-m>1))
              (#\s ("ism" "" porter-m>1))
              (#\t ("ate" "" porter-m>1) ("iti" "" porter-m>1))
              (#\u ("ous" "" porter-m>1))
              (#\v ("ive" "" porter-m>1))
              (#\z ("ize" "" porter-m>1)))
            ;; step 5a
            (when (and (char= (at (1- n)) #\e)
                       (or (porter-m>1 s (1- n))
                           (and (porter-m=1 s (1- n)) (not (porter-ostar s (1- n))))))
              (decf n))
            ;; step 5b
            (when (and (> n 1) (char= (at (1- n)) #\l) (char= (at (- n 2)) #\l) (porter-m>1 s (1- n)))
              (decf n))
            (utf8-decode-lenient (map '(vector (unsigned-byte 8)) #'char-code (subseq s 0 n))))))))

;;; ------------------------------------------------------------------
;;; tokenize = '...' option

(defun fts5-split-words (s)
  "Barewords and quoted strings ('..', \"..\", [..], `..`) of an option value."
  (let ((out '()) (i 0) (n (length s)))
    (loop
      (loop while (and (< i n) (member (char s i) '(#\Space #\Tab #\Newline #\Return))) do (incf i))
      (when (>= i n) (return (nreverse out)))
      (let ((c (char s i)))
        (if (member c '(#\' #\" #\` #\[))
            (let ((close (if (char= c #\[) #\] c)) (w (make-string-output-stream)))
              (incf i)
              (loop
                (when (>= i n) (sql-error "parse error in tokenize directive"))
                (let ((d (char s i)))
                  (cond ((and (char= d close) (< (1+ i) n) (char= (char s (1+ i)) close) (char/= c #\[))
                         (write-char d w) (incf i 2))
                        ((char= d close) (incf i) (return))
                        (t (write-char d w) (incf i)))))
              (push (get-output-stream-string w) out))
            (let ((start i))
              (loop while (and (< i n) (not (member (char s i) '(#\Space #\Tab #\Newline #\Return))))
                    do (incf i))
              (push (subseq s start i) out)))))))

(defun make-fts5-tokenizer-from (words)
  "WORDS: the tokenize option, split: name then name-specific arguments."
  (let ((name (string-downcase-ascii (or (first words) "unicode61"))))
    (flet ((pairs (args)
             (when (oddp (length args)) (sql-error "error in tokenizer constructor"))
             (loop for (k v) on args by #'cddr collect (cons (string-downcase-ascii k) v))))
      (cond
        ((string= name "unicode61")
         (let ((tok (make-fts5-tokenizer :kind :unicode61)))
           (dolist (kv (pairs (rest words)) tok)
             (destructuring-bind (k . v) kv
               (cond ((string= k "remove_diacritics")
                      (unless (member v '("0" "1" "2") :test #'string=)
                        (sql-error "error in tokenizer constructor"))
                      (setf (ftok-remove-diacritics tok) (parse-integer v)))
                     ((string= k "tokenchars")
                      (setf (ftok-token-chars tok) (append (map 'list #'char-code v) (ftok-token-chars tok))
                            (ftok-separators tok) (set-difference (ftok-separators tok) (map 'list #'char-code v))))
                     ((string= k "separators")
                      (setf (ftok-separators tok) (append (map 'list #'char-code v) (ftok-separators tok))
                            (ftok-token-chars tok) (set-difference (ftok-token-chars tok) (map 'list #'char-code v))))
                     ((string= k "categories") nil)
                     (t (sql-error "error in tokenizer constructor")))))))
        ((string= name "ascii")
         (let ((tok (make-fts5-tokenizer :kind :ascii)))
           (dolist (kv (pairs (rest words)) tok)
             (destructuring-bind (k . v) kv
               (cond ((string= k "tokenchars")
                      (setf (ftok-token-chars tok) (append (map 'list #'char-code v) (ftok-token-chars tok))))
                     ((string= k "separators")
                      (setf (ftok-separators tok) (append (map 'list #'char-code v) (ftok-separators tok))))
                     (t (sql-error "error in tokenizer constructor")))))))
        ((string= name "porter")
         (make-fts5-tokenizer :kind :porter :parent (make-fts5-tokenizer-from (rest words))))
        ((string= name "trigram")
         (let ((tok (make-fts5-tokenizer :kind :trigram)))
           (dolist (kv (pairs (rest words)) tok)
             (destructuring-bind (k . v) kv
               (cond ((string= k "case_sensitive")
                      (unless (member v '("0" "1") :test #'string=)
                        (sql-error "error in tokenizer constructor"))
                      (setf (ftok-case-sensitive tok) (string= v "1")))
                     (t (sql-error "error in tokenizer constructor")))))))
        (t (sql-error "no such tokenizer: ~a" (first words)))))))
