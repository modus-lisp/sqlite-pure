;;;; values.lisp — SQLite's value semantics: storage classes, comparison
;;;; and collation, type affinity, CAST, and text<->number conversion,
;;;; matched against SQLite 3.40 behaviour.

(in-package #:sqlite-pure)

(deftype blob () '(simple-array (unsigned-byte 8) (*)))

(declaim (inline blobp))
(defun blobp (v) (typep v '(vector (unsigned-byte 8))))

(defun storage-class-rank (v)
  (cond ((eq v :null) 0)
        ((or (integerp v) (floatp v)) 1)
        ((stringp v) 2)
        (t 3)))

(defun type-name-of (v)
  (cond ((eq v :null) "null")
        ((integerp v) "integer")
        ((floatp v) "real")
        ((stringp v) "text")
        (t "blob")))

;;; ------------------------------------------------------------------
;;; Numbers

(defun compare-numbers (a b)
  (cond ((and (integerp a) (integerp b)) (cond ((< a b) -1) ((> a b) 1) (t 0)))
        (t
         ;; Compare exactly: an integer against a double must not round.
         (flet ((key (x)
                  (cond ((integerp x) x)
                        ((float-infinity-p x) (if (plusp x) :inf :-inf))
                        (t (rational x)))))
           (let ((ka (key a)) (kb (key b)))
             (cond ((eql ka kb) 0)
                   ((or (eq ka :-inf) (eq kb :inf)) -1)
                   ((or (eq ka :inf) (eq kb :-inf)) 1)
                   ((< ka kb) -1)
                   ((> ka kb) 1)
                   (t 0)))))))

(defun safe-double (r)
  "Convert rational R to a double, overflowing to infinity."
  (cond ((> (abs r) most-positive-double-float)
         (if (plusp r) (double-positive-infinity) (double-negative-infinity)))
        (t (coerce r 'double-float))))

(defun clamp-i64 (n)
  (max +i64-min+ (min +i64-max+ n)))

(defun real-to-integer (x)
  "SQLite's REAL->INTEGER: truncate, saturating at the 64-bit limits."
  (cond ((float-infinity-p x) (if (plusp x) +i64-max+ +i64-min+))
        (t (clamp-i64 (truncate x)))))

;;; Scanning numeric text in the manner of sqlite3AtoF.

(defun whitespace-char-p (c)
  (member c '(#\Space #\Tab #\Newline #\Return #\Page #.(code-char 11))))

(defun scan-number (s &optional (start 0))
  "Scan a decimal numeric literal in S from START (after optional leading
whitespace).  Return (values rational end integer-syntax-p) or NIL if no
digits were found."
  (let ((i start) (n (length s)) (sign 1) (mant 0) (scale 0) (digits 0)
        (int-syntax t))
    (loop while (and (< i n) (whitespace-char-p (char s i))) do (incf i))
    (when (and (< i n) (member (char s i) '(#\+ #\-)))
      (when (char= (char s i) #\-) (setf sign -1))
      (incf i))
    (loop while (and (< i n) (digit-char-p (char s i)))
          do (setf mant (+ (* mant 10) (digit-char-p (char s i)))) (incf i) (incf digits))
    (when (and (< i n) (char= (char s i) #\.))
      (let ((j (1+ i)) (frac-digits 0))
        (loop while (and (< j n) (digit-char-p (char s j)))
              do (setf mant (+ (* mant 10) (digit-char-p (char s j))))
                 (decf scale) (incf j) (incf frac-digits))
        (when (or (plusp digits) (plusp frac-digits))
          (setf i j int-syntax nil)
          (incf digits frac-digits))))
    (when (zerop digits) (return-from scan-number nil))
    (when (and (< i n) (char-equal (char s i) #\e))
      (let ((j (1+ i)) (esign 1) (e 0) (edigits 0))
        (when (and (< j n) (member (char s j) '(#\+ #\-)))
          (when (char= (char s j) #\-) (setf esign -1))
          (incf j))
        (loop while (and (< j n) (digit-char-p (char s j)))
              do (when (< e 100000) (setf e (+ (* e 10) (digit-char-p (char s j)))))
                 (incf j) (incf edigits))
        (when (plusp edigits)
          (setf i j int-syntax nil)
          (incf scale (* esign e)))))
    (values (* sign mant (expt 10 scale)) i int-syntax)))

(defun rational-to-sql-number (r int-syntax)
  "Integer if it was written as one and fits, else a double."
  (if (and int-syntax (i64-p r)) r (safe-double r)))

(defun text-numeric-value (s)
  "If the whole of S (modulo surrounding whitespace) is a numeric literal,
return its value (integer or double), else NIL."
  (multiple-value-bind (r end int-syntax) (scan-number s)
    (when (and r
               (loop for k from end below (length s)
                     always (whitespace-char-p (char s k))))
      (rational-to-sql-number r int-syntax))))

(defun text-numeric-prefix (s)
  "Numeric value of the longest numeric prefix of S (0 if none): the
conversion used for arithmetic on text."
  (multiple-value-bind (r end int-syntax) (scan-number s)
    (declare (ignore end))
    (if r (rational-to-sql-number r int-syntax) 0)))

(defun text-integer-prefix (s)
  "CAST(text AS INTEGER): the leading integer, saturating."
  (let ((i 0) (n (length s)) (sign 1) (v 0) (any nil))
    (loop while (and (< i n) (whitespace-char-p (char s i))) do (incf i))
    (when (and (< i n) (member (char s i) '(#\+ #\-)))
      (when (char= (char s i) #\-) (setf sign -1))
      (incf i))
    (loop while (and (< i n) (digit-char-p (char s i)))
          do (setf v (+ (* v 10) (digit-char-p (char s i))) any t) (incf i))
    (if any (clamp-i64 (* sign v)) 0)))

;;; ------------------------------------------------------------------
;;; Formatting reals as SQLite does ("%!.15g")

(defun format-real (x)
  (cond ((float-nan-p x) "NaN")
        ((float-infinity-p x) (if (plusp x) "Inf" "-Inf"))
        ((zerop x) "0.0")
        (t
         (let* ((neg (minusp x))
                (r (abs (rational x)))
                (e (let ((e (floor (log (abs x) 10))))
                     ;; correct the floating estimate exactly
                     (loop while (> (expt 10 e) r) do (decf e))
                     (loop while (<= (expt 10 (1+ e)) r) do (incf e))
                     e))
                (d (round (/ r (expt 10 (- e 14))))))
           (when (>= d (expt 10 15)) (setf d (round d 10)) (incf e))
           (let* ((digits (string-right-trim "0" (format nil "~d" d)))
                  (digits (if (string= digits "") "0" digits))
                  (body
                    (if (or (< e -4) (>= e 15))
                        (format nil "~a.~a~ae~a~2,'0d"
                                (char digits 0)
                                (if (> (length digits) 1) (subseq digits 1) "")
                                (if (> (length digits) 1) "" "0")
                                (if (minusp e) "-" "+")
                                (abs e))
                        (cond ((minusp e)
                               (format nil "0.~a~a"
                                       (make-string (- (- e) 1) :initial-element #\0)
                                       digits))
                              ((>= e (1- (length digits)))
                               (format nil "~a~a.0" digits
                                       (make-string (- e (1- (length digits)))
                                                    :initial-element #\0)))
                              (t (format nil "~a.~a" (subseq digits 0 (1+ e))
                                         (subseq digits (1+ e))))))))
             (if neg (concatenate 'string "-" body) body))))))

;;; ------------------------------------------------------------------
;;; Conversions

(defun blob-to-text (b) (utf8-decode b))

(defun value-to-text (v)
  (cond ((stringp v) v)
        ((integerp v) (format nil "~d" v))
        ((floatp v) (format-real v))
        ((blobp v) (blob-to-text v))
        (t nil)))

(defun value-to-blob (v)
  (cond ((blobp v) v)
        ((eq v :null) :null)
        (t (utf8-encode (value-to-text v)))))

(defun value-to-number (v)
  "Numeric value for arithmetic: NULL stays NULL."
  (cond ((or (integerp v) (floatp v)) v)
        ((stringp v) (text-numeric-prefix v))
        ((blobp v) (text-numeric-prefix (blob-to-text v)))
        (t :null)))

(defun value-to-integer (v)
  (cond ((integerp v) v)
        ((floatp v) (real-to-integer v))
        ((stringp v) (text-integer-prefix v))
        ((blobp v) (text-integer-prefix (blob-to-text v)))
        (t :null)))

(defun value-to-real (v)
  (cond ((floatp v) v)
        ((integerp v) (safe-double v))
        ((stringp v) (let ((n (text-numeric-prefix v))) (if (floatp n) n (safe-double n))))
        ((blobp v) (value-to-real (blob-to-text v)))
        (t :null)))

(defun value-truthy (v)
  "SQL boolean: NIL for false, :null for unknown, T for true."
  (cond ((eq v :null) :null)
        ((integerp v) (/= v 0))
        ((floatp v) (/= v 0))
        (t (let ((n (value-to-number v))) (and (not (eq n :null)) (/= n 0))))))

;;; ------------------------------------------------------------------
;;; Affinity.  Affinities are :integer :real :numeric :text :blob; NIL
;;; means "no affinity" (an expression that is not a column or CAST).

(defun type-affinity (declared-type)
  "Column affinity from a declared type name, per SQLite's five rules."
  (let ((ty (string-upcase-ascii (or declared-type ""))))
    (cond ((search "INT" ty) :integer)
          ((or (search "CHAR" ty) (search "CLOB" ty) (search "TEXT" ty)) :text)
          ((or (search "BLOB" ty) (string= ty "")) :blob)
          ((or (search "REAL" ty) (search "FLOA" ty) (search "DOUB" ty)) :real)
          (t :numeric))))

(defun numeric-affinity-value (v)
  "Apply NUMERIC affinity."
  (cond ((stringp v)
         (let ((n (text-numeric-value v)))
           (cond ((null n) v)
                 ((integerp n) n)
                 ;; a real that is exactly an in-range integer becomes one
                 ((and (not (float-infinity-p n))
                       (= n (ftruncate n))
                       (< (abs n) 9.223372036854775d18))
                  (truncate n))
                 (t n))))
        ((floatp v)
         (if (and (not (float-infinity-p v))
                  (= v (ftruncate v))
                  (< (abs v) 9.223372036854775d18))
             (truncate v)
             v))
        (t v)))

(defun apply-affinity (v aff)
  (case aff
    ((:integer :numeric) (numeric-affinity-value v))
    (:real (let ((n (numeric-affinity-value v)))
             (if (integerp n) (safe-double n) n)))
    (:text (if (or (integerp v) (floatp v)) (value-to-text v) v))
    (t v)))

(defun cast-value (v type-name)
  (if (eq v :null)
      :null
      (ecase (type-affinity type-name)
        (:integer (value-to-integer v))
        (:real (value-to-real v))
        (:text (value-to-text v))
        (:blob (value-to-blob v))
        (:numeric
         (cond ((integerp v) v)
               ((floatp v) v)
               (t (let* ((s (if (blobp v) (blob-to-text v) v))
                         (n (text-numeric-prefix s)))
                    (if (and (floatp n) (not (float-infinity-p n))
                             (= n (ftruncate n)) (< (abs n) 9.223372036854775d18))
                        (truncate n)
                        n))))))))

;;; ------------------------------------------------------------------
;;; Collation and comparison

(defun rtrim-spaces (s) (string-right-trim " " s))

(defun compare-strings (a b collation)
  (let ((a (if (eq collation :rtrim) (rtrim-spaces a) a))
        (b (if (eq collation :rtrim) (rtrim-spaces b) b)))
    (let ((n (min (length a) (length b))))
      (dotimes (i n (cond ((< (length a) (length b)) -1)
                          ((> (length a) (length b)) 1)
                          (t 0)))
        (let ((ca (char a i)) (cb (char b i)))
          (when (eq collation :nocase)
            (setf ca (ascii-char-fold ca) cb (ascii-char-fold cb)))
          (cond ((char< ca cb) (return -1))
                ((char> ca cb) (return 1))))))))

(defun compare-blobs (a b)
  (let ((n (min (length a) (length b))))
    (dotimes (i n (cond ((< (length a) (length b)) -1)
                        ((> (length a) (length b)) 1)
                        (t 0)))
      (let ((x (aref a i)) (y (aref b i)))
        (cond ((< x y) (return -1))
              ((> x y) (return 1)))))))

(defun compare-values (a b &optional (collation :binary))
  "Total order used by ORDER BY, indexes, MIN/MAX: NULL < numbers < text < blob."
  (let ((ra (storage-class-rank a)) (rb (storage-class-rank b)))
    (cond ((/= ra rb) (if (< ra rb) -1 1))
          ((= ra 0) 0)
          ((= ra 1) (compare-numbers a b))
          ((= ra 2) (compare-strings a b collation))
          (t (compare-blobs a b)))))

(defun values-equal-p (a b &optional (collation :binary))
  (= 0 (compare-values a b collation)))

(defun collation-keyword (name)
  (let ((n (string-upcase-ascii name)))
    (cond ((string= n "BINARY") :binary)
          ((string= n "NOCASE") :nocase)
          ((string= n "RTRIM") :rtrim)
          (t (sql-error "no such collation sequence: ~a" name)))))

;;; Keys for hashing (GROUP BY, DISTINCT, IN lists).  Numerically equal
;;; integers and reals share a key.

(defun group-key-1 (v collation)
  (cond ((eq v :null) :null)
        ((floatp v) (if (and (not (float-infinity-p v)) (= v (ftruncate v))
                             (i64-p (truncate v)))
                        (truncate v)
                        v))
        ((stringp v) (case collation
                       (:nocase (string-downcase-ascii v))
                       (:rtrim (rtrim-spaces v))
                       (t v)))
        ((blobp v) (cons :blob (coerce v 'list)))
        (t v)))

(defun group-key (vals &optional collations)
  (loop for v in vals
        for i from 0
        collect (group-key-1 v (if collations (nth i collations) :binary))))
