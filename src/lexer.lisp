;;;; lexer.lisp — SQL tokenizer.
;;;;
;;;; Tokens are (KIND VALUE POS . QUOTED).  Keywords are not distinguished
;;;; from identifiers here: SQLite lets most keywords serve as names, so the
;;;; parser decides from context.

(in-package #:sqlite-pure)

(defstruct (tok (:constructor make-tok (kind value pos &optional quoted)))
  kind value pos quoted end)

(defun parse-error-at (sql pos fmt &rest args)
  (error 'sqlite-parse-error :offset pos
         :message (format nil "~? (near ~s)" fmt args
                          (subseq sql (min pos (length sql)) (min (length sql) (+ pos 20))))))

(defun unrecognized-token (sql start end)
  "SQLite's TK_ILLEGAL report: the offending token's whole text."
  (error 'sqlite-parse-error :offset start
         :message (format nil "unrecognized token: \"~a\"" (subseq sql start (min end (length sql))))))

(defun ident-start-p (c)
  (or (alpha-char-p c) (char= c #\_) (> (char-code c) 127)))
(defun ident-char-p (c)
  (or (alphanumericp c) (char= c #\_) (char= c #\$) (> (char-code c) 127)))

(defun tokenize (sql)
  (let ((toks '()) (i 0) (n (length sql)))
    (labels ((peekc (&optional (k 0)) (let ((j (+ i k))) (when (< j n) (char sql j))))
             (emit (kind value start &optional quoted)
               (push (make-tok kind value start quoted) toks))
             (read-quoted (close &optional tok-start)
               ;; I points at the opening quote.
               (let ((start i) (out (make-string-output-stream)))
                 (incf i)
                 (loop
                   (when (>= i n) (unrecognized-token sql (or tok-start start) n))
                   (let ((c (char sql i)))
                     (cond ((char= c close)
                            (if (and (< (1+ i) n) (char= (char sql (1+ i)) close))
                                (progn (write-char c out) (incf i 2))
                                (progn (incf i) (return (get-output-stream-string out)))))
                           (t (write-char c out) (incf i))))))))
      (loop
        (loop while (and (< i n) (whitespace-char-p (char sql i))) do (incf i))
        (when (>= i n) (return))
        (let ((c (char sql i)) (start i) (before toks))
          (cond
            ;; comments
            ((and (char= c #\-) (eql (peekc 1) #\-))
             (loop while (and (< i n) (char/= (char sql i) #\Newline)) do (incf i)))
            ((and (char= c #\/) (eql (peekc 1) #\*))
             (let ((end (search "*/" sql :start2 (+ i 2))))
               (setf i (if end (+ end 2) n))))
            ;; strings and quoted identifiers
            ((char= c #\') (emit :string (read-quoted #\') start))
            ((char= c #\") (emit :id (read-quoted #\") start #\"))
            ((char= c #\`) (emit :id (read-quoted #\`) start t))
            ((char= c #\[)
             (let ((end (position #\] sql :start i)))
               (unless end (unrecognized-token sql i n))
               (emit :id (subseq sql (1+ i) end) start t)
               (setf i (1+ end))))
            ;; blob literal
            ((and (char-equal c #\x) (eql (peekc 1) #\'))
             (incf i)
             (let ((hex (read-quoted #\' start)))
               (unless (and (evenp (length hex)) (every (lambda (h) (digit-char-p h 16)) hex))
                 (unrecognized-token sql start i))
               (let ((b (make-octets (floor (length hex) 2))))
                 (dotimes (k (length b))
                   (setf (aref b k) (parse-integer hex :start (* 2 k) :end (+ 2 (* 2 k)) :radix 16)))
                 (emit :blob b start))))
            ;; numbers
            ((or (digit-char-p c) (and (char= c #\.) (peekc 1) (digit-char-p (peekc 1))))
             (if (and (char= c #\0) (member (peekc 1) '(#\x #\X))
                      (peekc 2) (digit-char-p (peekc 2) 16))
                 (let ((j (+ i 2)))
                   (loop while (and (< j n) (digit-char-p (char sql j) 16)) do (incf j))
                   (let ((v (parse-integer sql :start (+ i 2) :end j :radix 16)))
                     (when (> v #xffffffffffffffff)
                       (error 'sqlite-parse-error :offset start
                              :message (format nil "hex literal too big: ~a" (subseq sql start j))))
                     (emit :integer (to-signed64 v) start)
                     (setf i j)))
                 (multiple-value-bind (r end int-syntax dbl) (scan-number sql i)
                   (when (and (< end n) (ident-char-p (char sql end)))
                     (unrecognized-token sql start (or (position-if-not #'ident-char-p sql :start end) n)))
                   (cond ((and int-syntax (i64-p r)) (emit :integer r start))
                         (int-syntax (emit :bigint (cons r dbl) start))
                         (t (emit :float dbl start)))
                   (setf i end))))
            ;; parameters
            ((char= c #\?)
             (let ((j (1+ i)))
               (loop while (and (< j n) (digit-char-p (char sql j))) do (incf j))
               (emit :param (if (> j (1+ i)) (parse-integer sql :start (1+ i) :end j) nil) start)
               (setf i j)))
            ((member c '(#\: #\@ #\$))
             (let ((j (1+ i)))
               (loop while (and (< j n) (ident-char-p (char sql j))) do (incf j))
               (when (= j (1+ i)) (unrecognized-token sql start j))
               (emit :param (subseq sql i j) start)
               (setf i j)))
            ;; identifiers / keywords
            ((ident-start-p c)
             (let ((j i))
               (loop while (and (< j n) (ident-char-p (char sql j))) do (incf j))
               (emit :id (subseq sql i j) start)
               (setf i j)))
            ;; operators
            (t
             (let ((two (and (< (1+ i) n) (subseq sql i (+ i 2))))
                   (three (and (< (+ i 2) n) (subseq sql i (+ i 3)))))
               (cond ((and three (string= three "->>")) (emit :op "->>" start) (incf i 3))
                     ((and two (member two '("||" "<=" ">=" "==" "!=" "<>" "<<" ">>" "->")
                                       :test #'string=))
                      (emit :op two start) (incf i 2))
                     ((find c "+-*/%<>=(),;.&|~")
                      (emit :op (string c) start) (incf i))
                     (t (unrecognized-token sql start (1+ i)))))))
          (unless (eq toks before) (setf (tok-end (car toks)) i)))))
    (push (make-tok :eof nil n) toks)
    (coerce (nreverse toks) 'vector)))
