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
;;;
;;; SQLite 3.40 does not round decimal text to the nearest double.  It
;;; accumulates at most ~18 significant digits into a 64-bit integer
;;; (silently dropping the rest), then scales by powers of ten in x87
;;; "long double" (64-bit significand) and finally rounds to double.  The
;;; functions below reproduce that bit for bit with exact rationals.

(defun whitespace-char-p (c)
  (member c '(#\Space #\Tab #\Newline #\Return #\Page #.(code-char 11))))

(defun round-significand (r bits)
  "Round the rational R to BITS significant bits (nearest, ties to even)."
  (if (zerop r)
      0
      (let* ((a (abs r))
             (e (- (integer-length (numerator a)) (integer-length (denominator a)) bits)))
        ;; settle E so that 2^(bits-1) <= a/2^e < 2^bits
        (loop while (>= (/ a (expt 2 e)) (expt 2 bits)) do (incf e))
        (loop while (< (/ a (expt 2 e)) (expt 2 (1- bits))) do (decf e))
        (* (signum r) (round (/ a (expt 2 e))) (expt 2 e)))))

(defun ld (r) (round-significand r 64))

(defparameter +double-1e308+ (rational 1d308))

(defun sqlite-atof-result (sign s d e esign)
  "The double sqlite3AtoF computes from significand S (an integer), the
decimal-point shift D, and exponent E with sign ESIGN."
  (let ((e (+ (* e esign) d)))
    (if (minusp e) (setf esign -1 e (- e)) (setf esign 1))
    (if (zerop s)
        (if (minusp sign) -0d0 0d0)
        (progn
          (loop while (plusp e)
                do (if (plusp esign)
                       (if (>= s (floor +i64-max+ 10)) (return) (setf s (* s 10)))
                       (if (/= 0 (mod s 10)) (return) (setf s (floor s 10))))
                   (decf e))
          (setf s (* sign s))
          (cond
            ((zerop e) (float s 1d0))
            ((> e 307)
             (if (< e 342)
                 (let ((scale 1))
                   (loop while (/= 0 (mod e 308)) do (setf scale (ld (* scale 10))) (decf e))
                   (if (minusp esign)
                       (safe-double (/ (rational (safe-double (ld (/ s scale)))) +double-1e308+))
                       (safe-double (* (rational (safe-double (ld (* s scale)))) +double-1e308+))))
                 (if (minusp esign)
                     (if (minusp s) -0d0 0d0)
                     (if (minusp s) (double-negative-infinity) (double-positive-infinity)))))
            (t
             (let ((scale 1))
               (loop while (/= 0 (mod e 22)) do (setf scale (ld (* scale 10))) (decf e))
               (loop while (plusp e) do (setf scale (ld (* scale (expt 10 22)))) (decf e 22))
               (safe-double (ld (if (minusp esign) (/ s scale) (* s scale)))))))))))

(defun scan-number (s &optional (start 0))
  "Scan a decimal numeric literal in S from START (after optional leading
whitespace).  Return (values rational end integer-syntax-p double) where
DOUBLE is the value SQLite's sqlite3AtoF would produce, or NIL if no digits
were found."
  (let ((i start) (n (length s)) (sign 1) (mant 0) (scale 0) (digits 0)
        (int-syntax t)
        ;; sqlite3AtoF's own accumulators
        (as 0) (ad 0) (ae 0) (aesign 1)
        (limit (floor (- +i64-max+ 9) 10)))
    (loop while (and (< i n) (whitespace-char-p (char s i))) do (incf i))
    (when (and (< i n) (member (char s i) '(#\+ #\-)))
      (when (char= (char s i) #\-) (setf sign -1))
      (incf i))
    (loop while (and (< i n) (digit-char-p (char s i)))
          do (let ((dg (digit-char-p (char s i))))
               (setf mant (+ (* mant 10) dg))
               (if (>= as limit) (incf ad) (setf as (+ (* as 10) dg))))
             (incf i) (incf digits))
    (when (and (< i n) (char= (char s i) #\.))
      (let ((j (1+ i)) (frac-digits 0) (as2 as) (ad2 ad))
        (loop while (and (< j n) (digit-char-p (char s j)))
              do (let ((dg (digit-char-p (char s j))))
                   (setf mant (+ (* mant 10) dg))
                   (when (< as2 limit) (setf as2 (+ (* as2 10) dg)) (decf ad2)))
                 (decf scale) (incf j) (incf frac-digits))
        (when (or (plusp digits) (plusp frac-digits))
          (setf i j int-syntax nil as as2 ad ad2)
          (incf digits frac-digits))))
    (when (zerop digits) (return-from scan-number nil))
    (when (and (< i n) (char-equal (char s i) #\e))
      (let ((j (1+ i)) (esign 1) (e 0) (edigits 0))
        (when (and (< j n) (member (char s j) '(#\+ #\-)))
          (when (char= (char s j) #\-) (setf esign -1))
          (incf j))
        (loop while (and (< j n) (digit-char-p (char s j)))
              do (setf e (if (< e 10000) (+ (* e 10) (digit-char-p (char s j))) 10000))
                 (incf j) (incf edigits))
        (when (plusp edigits)
          (setf i j int-syntax nil ae e aesign esign)
          (incf scale (* esign e)))))
    (values (* sign mant (expt 10 scale)) i int-syntax
            (sqlite-atof-result sign as ad ae aesign))))

(defun rational-to-sql-number (r int-syntax &optional dbl)
  "Integer if it was written as one and fits, else a double (SQLite's)."
  (if (and int-syntax (i64-p r)) r (or dbl (safe-double r))))

(defun text-numeric-value (s)
  "If the whole of S (modulo surrounding whitespace) is a numeric literal,
return its value (integer or double), else NIL."
  (multiple-value-bind (r end int-syntax dbl) (scan-number s)
    (when (and r
               (loop for k from end below (length s)
                     always (whitespace-char-p (char s k))))
      (rational-to-sql-number r int-syntax dbl))))

(defun text-numeric-prefix (s)
  "Numeric value of the longest numeric prefix of S (0 if none): the
conversion used for arithmetic on text."
  (multiple-value-bind (r end int-syntax dbl) (scan-number s)
    (declare (ignore end))
    (if r (rational-to-sql-number r int-syntax dbl) 0)))

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
  (when (and (eq collation :binary) (not (eq *encoding* :utf-8)))
    ;; BINARY is memcmp over the database's own encoding; for UTF-16 that
    ;; is not code-point order.
    (return-from compare-strings (compare-blobs (encode-text a) (encode-text b))))
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
