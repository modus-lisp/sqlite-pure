;;;; util.lisp — conditions, octets, big-endian integers, SQLite varints,
;;;; UTF-8/16, and IEEE-754 doubles, all portable CL.

(in-package #:sqlite-pure)

(defvar *db* nil "The database a statement is running against.")

;;; ------------------------------------------------------------------
;;; Conditions

(define-condition sqlite-error (error)
  ((message :initarg :message :reader sqlite-error-message)
   (code :initarg :code :initform :error :reader sqlite-error-code)
   ;; character offset of the offending token in the SQL, when known
   (offset :initarg :offset :initform nil :reader sqlite-error-offset))
  (:report (lambda (c s) (format s "SQLite ~(~a~): ~a"
                                 (sqlite-error-code c) (sqlite-error-message c)))))

(define-condition sqlite-constraint-error (sqlite-error) ()
  (:default-initargs :code :constraint))
(define-condition sqlite-parse-error (sqlite-error) ()
  (:default-initargs :code :parse))
(define-condition sqlite-corrupt-error (sqlite-error) ()
  (:default-initargs :code :corrupt))

(defun sql-error (fmt &rest args)
  (error 'sqlite-error :message (apply #'format nil fmt args)))

(defvar *executing-sql* nil "The SQL text of the statement(s) being run.")

(defun sql-error-at (name fmt &rest args)
  "SQL-ERROR pointing at the reference NAME (a column-name string from the
parser) when it was parsed from the SQL being run."
  (let ((loc (and (boundp '*ident-positions*) (stringp name)
                  (gethash name (symbol-value '*ident-positions*)))))
    (if (and loc *executing-sql* (equal (car loc) *executing-sql*))
        (error 'sqlite-error :message (apply #'format nil fmt args) :offset (cdr loc))
        (apply #'sql-error fmt args))))
(defun corrupt (fmt &rest args)
  (error 'sqlite-corrupt-error :message (apply #'format nil fmt args)))
(defun constraint-error (fmt &rest args)
  (error 'sqlite-constraint-error :message (apply #'format nil fmt args)))

;;; ------------------------------------------------------------------
;;; SQL NULL.  Lisp NIL is not used for NULL so that an empty result, a
;;; false boolean and a missing value stay distinguishable.

(defconstant +null+ :null)
(declaim (inline null-value-p))
(defun null-value-p (v) (eq v :null))

;;; ------------------------------------------------------------------
;;; Octets

(deftype octets () '(simple-array (unsigned-byte 8) (*)))

(declaim (inline make-octets))
(defun make-octets (n &optional (init 0))
  (make-array n :element-type '(unsigned-byte 8) :initial-element init))

(defun octets-subseq (v start &optional (end (length v)))
  (let ((r (make-octets (- end start))))
    (replace r v :start2 start :end2 end)
    r))

(defun octets-concat (&rest vs)
  (let* ((n (reduce #'+ vs :key #'length))
         (r (make-octets n))
         (p 0))
    (dolist (v vs r)
      (replace r v :start1 p)
      (incf p (length v)))))

(deftype octet-index () '(integer 0 #.(1- array-dimension-limit)))

(declaim (inline get-u8 get-u16 get-u24 get-u32))
(defun get-u8 (b off)
  (declare (type octets b) (type octet-index off) (optimize speed))
  (aref b off))
(defun get-u16 (b off)
  (declare (type octets b) (type octet-index off) (optimize speed))
  (logior (ash (aref b off) 8) (aref b (1+ off))))
(defun get-u24 (b off)
  (declare (type octets b) (type octet-index off) (optimize speed))
  (logior (ash (aref b off) 16) (ash (aref b (+ off 1)) 8) (aref b (+ off 2))))
(defun get-u32 (b off)
  (declare (type octets b) (type octet-index off) (optimize speed))
  (logior (ash (aref b off) 24) (ash (aref b (+ off 1)) 16)
          (ash (aref b (+ off 2)) 8) (aref b (+ off 3))))

(defun get-uint (b off n)
  "Big-endian unsigned integer of N bytes."
  (let ((v 0))
    (dotimes (i n v) (setf v (logior (ash v 8) (aref b (+ off i)))))))

(defun get-sint (b off n)
  "Big-endian two's-complement integer of N bytes."
  (let ((v (get-uint b off n))
        (bits (* 8 n)))
    (if (logbitp (1- bits) v) (- v (ash 1 bits)) v)))

(declaim (inline put-u8 put-u16 put-u32))
(defun put-u8 (b off v) (setf (aref b off) (ldb (byte 8 0) v)))
(defun put-u16 (b off v)
  (setf (aref b off) (ldb (byte 8 8) v)
        (aref b (1+ off)) (ldb (byte 8 0) v)))
(defun put-u32 (b off v)
  (setf (aref b off) (ldb (byte 8 24) v)
        (aref b (+ off 1)) (ldb (byte 8 16) v)
        (aref b (+ off 2)) (ldb (byte 8 8) v)
        (aref b (+ off 3)) (ldb (byte 8 0) v)))

(defun put-uint (b off n v)
  (loop for i from (1- n) downto 0
        for p from off
        do (setf (aref b p) (ldb (byte 8 (* 8 i)) v))))

;;; ------------------------------------------------------------------
;;; 64-bit integer helpers

(defconstant +i64-min+ (- (expt 2 63)))
(defconstant +i64-max+ (1- (expt 2 63)))

(declaim (inline i64-p))
(defun i64-p (x) (and (integerp x) (<= +i64-min+ x +i64-max+)))

(defun to-signed64 (u)
  (let ((u (ldb (byte 64 0) u)))
    (if (logbitp 63 u) (- u (expt 2 64)) u)))

;;; ------------------------------------------------------------------
;;; Varints: 1-9 bytes, big-endian 7-bit groups, the ninth byte whole.

(defun get-varint (b off)
  "Return (values unsigned-value byte-length)."
  (declare (type octets b) (type octet-index off) (optimize speed))
  (let ((byte (aref b off)))
    (when (< byte #x80) (return-from get-varint (values byte 1))))
  (let ((v 0))
    (declare (type (unsigned-byte 56) v))
    (loop for i of-type fixnum from 0 below 8
          for byte of-type (unsigned-byte 8) = (aref b (+ off i))
          do (setf v (logior (ash v 7) (logand byte #x7f)))
             (unless (logbitp 7 byte)
               (return-from get-varint (values v (1+ i)))))
    (values (logior (ash v 8) (aref b (+ off 8))) 9)))

(defun get-varint-signed (b off)
  (multiple-value-bind (v n) (get-varint b off)
    (values (to-signed64 v) n)))

(defun varint-length (v)
  (let ((u (ldb (byte 64 0) v)))
    (cond ((> u #x00ffffffffffffff) 9)
          (t (loop for n from 1
                   for lim = (ash 1 (* 7 n))
                   when (< u lim) return n)))))

(defun put-varint (b off v)
  "Write V (signed or unsigned, 64-bit) at OFF; return byte count."
  (let ((u (ldb (byte 64 0) v)))
    (if (> u #x00ffffffffffffff)
        (progn
          (setf (aref b (+ off 8)) (ldb (byte 8 0) u))
          (setf u (ash u -8))
          (loop for i from 7 downto 0
                do (setf (aref b (+ off i)) (logior #x80 (ldb (byte 7 0) u))
                         u (ash u -7)))
          9)
        (let ((n (varint-length u)))
          (loop for i from (1- n) downto 0
                for first = t then nil
                do (setf (aref b (+ off i))
                         (logior (if first 0 #x80) (ldb (byte 7 0) u))
                         u (ash u -7)))
          n))))

(defun varint-octets (v)
  (let ((b (make-octets 9)))
    (octets-subseq b 0 (put-varint b 0 v))))

;;; ------------------------------------------------------------------
;;; UTF-8 / UTF-16.  Malformed input decodes to U+FFFD rather than
;;; signalling: SQLite itself stores whatever bytes it is given.

;;; Invalid UTF-8 in stored text decodes byte by byte to U+DC80..U+DCFF
;;; ("surrogate escapes"), and those characters encode back to the same
;;; bytes, so text round-trips exactly as SQLite's does.

(declaim (inline escaped-byte-p))
(defun escaped-byte-p (code) (<= #xdc80 code #xdcff))

(defun utf8-length (s)
  (loop for c across s
        for code = (char-code c)
        sum (cond ((< code #x80) 1) ((< code #x800) 2)
                  ((escaped-byte-p code) 1)
                  ((< code #x10000) 3) (t 4))))

(defun utf8-encode-into (s b off)
  (loop for c across s
        for code = (char-code c)
        do (cond ((< code #x80) (setf (aref b off) code) (incf off))
                 ((< code #x800)
                  (setf (aref b off) (logior #xc0 (ash code -6))
                        (aref b (+ off 1)) (logior #x80 (logand code #x3f)))
                  (incf off 2))
                 ((escaped-byte-p code)
                  (setf (aref b off) (- code #xdc00))
                  (incf off 1))
                 ((< code #x10000)
                  (setf (aref b off) (logior #xe0 (ash code -12))
                        (aref b (+ off 1)) (logior #x80 (logand (ash code -6) #x3f))
                        (aref b (+ off 2)) (logior #x80 (logand code #x3f)))
                  (incf off 3))
                 (t
                  (setf (aref b off) (logior #xf0 (ash code -18))
                        (aref b (+ off 1)) (logior #x80 (logand (ash code -12) #x3f))
                        (aref b (+ off 2)) (logior #x80 (logand (ash code -6) #x3f))
                        (aref b (+ off 3)) (logior #x80 (logand code #x3f)))
                  (incf off 4))))
  off)

(defun utf8-encode (s)
  (if (and (simple-string-p s) (every (lambda (c) (< (char-code c) #x80)) s))
      (let ((b (make-octets (length s))))
        (dotimes (i (length s) b) (setf (aref b i) (char-code (schar s i)))))
      (let ((b (make-octets (utf8-length s))))
        (utf8-encode-into s b 0)
        b)))

(defun safe-code-char (code)
  (or (and (< code char-code-limit)
           (not (<= #xd800 code #xdfff))
           (code-char code))
      (code-char #xfffd)))

(defun utf8-decode (b &optional (start 0) (end (length b)))
  (declare (type octets b) (type octet-index start end) (optimize speed))
  (when (loop for i of-type octet-index from start below end always (< (aref b i) #x80))
    ;; pure ASCII: the common case
    (let ((out (make-string (- end start))))
      (loop for i of-type octet-index from start below end
            for k of-type octet-index from 0
            do (setf (schar out k) (code-char (aref b i))))
      (return-from utf8-decode out)))
  (let ((out (make-string (- end start)))
        (n 0)
        (i start))
    (flet ((cont (k) (and (< k end) (= (logand (aref b k) #xc0) #x80))))
      (loop while (< i end)
            do (let ((c (aref b i)))
                 (multiple-value-bind (code len)
                     (cond ((< c #x80) (values c 1))
                           ((and (>= c #xc2) (< c #xe0) (cont (+ i 1)))
                            (values (logior (ash (logand c #x1f) 6)
                                            (logand (aref b (+ i 1)) #x3f))
                                    2))
                           ((and (>= c #xe0) (< c #xf0) (cont (+ i 1)) (cont (+ i 2)))
                            (values (logior (ash (logand c #x0f) 12)
                                            (ash (logand (aref b (+ i 1)) #x3f) 6)
                                            (logand (aref b (+ i 2)) #x3f))
                                    3))
                           ((and (>= c #xf0) (< c #xf5) (cont (+ i 1)) (cont (+ i 2))
                                 (cont (+ i 3)))
                            (values (logior (ash (logand c #x07) 18)
                                            (ash (logand (aref b (+ i 1)) #x3f) 12)
                                            (ash (logand (aref b (+ i 2)) #x3f) 6)
                                            (logand (aref b (+ i 3)) #x3f))
                                    4))
                           (t (values (+ #xdc00 c) 1)))
                   (setf (char out n) (if (and (>= code #xdc80) (<= code #xdcff))
                                          (or (code-char code) (code-char #xfffd))
                                          (safe-code-char code)))
                   (incf n)
                   (incf i len)))))
    (if (= n (length out)) out (subseq out 0 n))))

(defun utf16-decode (b start end big-endian)
  (let ((out (make-string-output-stream))
        (i start))
    (flet ((unit (k) (if big-endian
                         (logior (ash (aref b k) 8) (aref b (1+ k)))
                         (logior (aref b k) (ash (aref b (1+ k)) 8)))))
      (loop while (< (1+ i) end)
            do (let ((u (unit i)))
                 (incf i 2)
                 (if (and (<= #xd800 u #xdbff) (< (1+ i) end)
                          (<= #xdc00 (unit i) #xdfff))
                     (progn
                       (write-char (safe-code-char
                                    (+ #x10000 (ash (- u #xd800) 10) (- (unit i) #xdc00)))
                                   out)
                       (incf i 2))
                     (write-char (safe-code-char u) out)))))
    (get-output-stream-string out)))

(defun utf16-encode (s big-endian)
  (let ((units '()))
    (loop for c across s
          for code = (char-code c)
          do (if (>= code #x10000)
                 (let ((v (- code #x10000)))
                   (push (+ #xd800 (ash v -10)) units)
                   (push (+ #xdc00 (logand v #x3ff)) units))
                 (push code units)))
    (setf units (nreverse units))
    (let ((b (make-octets (* 2 (length units)))))
      (loop for u in units
            for k from 0 by 2
            do (if big-endian
                   (setf (aref b k) (ash u -8) (aref b (1+ k)) (logand u #xff))
                   (setf (aref b k) (logand u #xff) (aref b (1+ k)) (ash u -8))))
      b)))

(defun ascii-octets (s)
  (map 'octets #'char-code s))

;;; ------------------------------------------------------------------
;;; IEEE-754 binary64, portably.

(defun double-positive-infinity ()
  #+sbcl sb-ext:double-float-positive-infinity
  #+ccl ccl::double-float-positive-infinity
  #-(or sbcl ccl) most-positive-double-float)

(defun double-negative-infinity ()
  #+sbcl sb-ext:double-float-negative-infinity
  #+ccl ccl::double-float-negative-infinity
  #-(or sbcl ccl) most-negative-double-float)

(defun float-infinity-p (x)
  (and (floatp x)
       #+sbcl (sb-ext:float-infinity-p x)
       #-sbcl (or (= x (double-positive-infinity))
                  (= x (double-negative-infinity)))))

(defun float-nan-p (x)
  (and (floatp x) (/= x x)))

(defun double-from-bits (u)
  (let ((sign (ldb (byte 1 63) u))
        (exp (ldb (byte 11 52) u))
        (frac (ldb (byte 52 0) u)))
    (let ((mag (cond ((= exp 2047)
                      (if (zerop frac) (double-positive-infinity) :nan))
                     ((zerop exp) (scale-float (float frac 1d0) -1074))
                     (t (scale-float (float (+ frac (ash 1 52)) 1d0) (- exp 1075))))))
      (cond ((eq mag :nan) :null)       ; SQLite never stores NaN; read it as NULL
            ((= sign 1) (if (zerop mag) -0d0 (- mag)))
            (t mag)))))

(defun bits-from-double (x)
  (let ((x (float x 1d0)))
    (cond ((float-infinity-p x)
           (if (plusp x) #x7ff0000000000000 #xfff0000000000000))
          ((zerop x) (if (minusp (float-sign x)) (ash 1 63) 0))
          (t
           (multiple-value-bind (m e s) (integer-decode-float x)
             (loop while (and (< m (ash 1 52)) (> e -1074))
                   do (setf m (ash m 1)) (decf e))
             (let ((signbit (if (minusp s) 1 0)))
               (if (>= m (ash 1 52))
                   (logior (ash signbit 63) (ash (+ e 1075) 52) (- m (ash 1 52)))
                   (logior (ash signbit 63) m))))))))

;;; ------------------------------------------------------------------
;;; Small string helpers

(defun string-upcase-ascii (s)
  (map 'string (lambda (c) (if (char<= #\a c #\z) (char-upcase c) c)) s))
(defun string-downcase-ascii (s)
  (map 'string (lambda (c) (if (char<= #\A c #\Z) (char-downcase c) c)) s))

(declaim (inline ascii-char-fold))
(defun ascii-char-fold (c) (if (char<= #\A c #\Z) (char-downcase c) c))

(defun name= (a b)
  "SQL identifier equality: ASCII case-insensitive, as SQLite folds."
  (and (= (length a) (length b))
       (every (lambda (x y) (char= (ascii-char-fold x) (ascii-char-fold y))) a b)))

(defun ascii-search (needle haystack)
  (search needle haystack
          :test (lambda (x y) (char= (ascii-char-fold x) (ascii-char-fold y)))))

;;; ------------------------------------------------------------------
;;; Randomness

(defvar *sql-random-state* nil
  "(pid . random-state): SQLite seeds its PRNG from the OS in each process;
a state saved in a Lisp core would repeat the same numbers in every process
started from it, so it is made afresh whenever the process changes.")

(defun sql-random-state ()
  (let ((pid #+sbcl (sb-unix:unix-getpid) #-sbcl 0))
    (unless (eql (car *sql-random-state*) pid)
      (setf *sql-random-state* (cons pid (make-random-state t))))
    (cdr *sql-random-state*)))
