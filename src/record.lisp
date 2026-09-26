;;;; record.lisp — the SQLite record format: a varint header of serial
;;;; types followed by the column bodies.
;;;;
;;;; Lisp representation of SQL values:
;;;;   NULL    :null
;;;;   INTEGER integer (signed 64-bit)
;;;;   REAL    double-float
;;;;   TEXT    string
;;;;   BLOB    (simple-array (unsigned-byte 8) (*))

(in-package #:sqlite-pure)

(defvar *encoding* :utf-8 "Text encoding of the database being read/written.")

(defun encode-text (s)
  (ecase *encoding*
    (:utf-8 (utf8-encode s))
    (:utf-16le (utf16-encode s nil))
    (:utf-16be (utf16-encode s t))))

(defun decode-text (b start end)
  (ecase *encoding*
    (:utf-8 (utf8-decode b start end))
    (:utf-16le (utf16-decode b start end nil))
    (:utf-16be (utf16-decode b start end t))))

(defun serial-type-length (st)
  (cond ((< st 5) (svref #(0 1 2 3 4) st))
        ((= st 5) 6)
        ((< st 8) 8)
        ((< st 12) 0)
        (t (floor (- st 12) 2))))

(defun decode-value (b off st)
  (case st
    (0 :null)
    (1 (get-sint b off 1))
    (2 (get-sint b off 2))
    (3 (get-sint b off 3))
    (4 (get-sint b off 4))
    (5 (get-sint b off 6))
    (6 (get-sint b off 8))
    (7 (double-from-bits (get-uint b off 8)))
    (8 0)
    (9 1)
    ((10 11) (corrupt "reserved serial type ~d" st))
    (t (let ((n (floor (- st 12) 2)))
         (if (evenp st)
             (octets-subseq b off (+ off n))
             (decode-text b off (+ off n)))))))

(defun decode-record (b &optional (start 0) (end (length b)) limit)
  "Decode the record in B[START,END) into a list of values.  With LIMIT,
decode at most that many columns."
  (multiple-value-bind (hsize n) (get-varint b start)
    (let ((hp (+ start n))
          (hend (+ start hsize))
          (dp (+ start hsize))
          (vals '())
          (count 0))
      (when (> hend end) (corrupt "record header overflows payload"))
      (loop while (and (< hp hend) (or (null limit) (< count limit)))
            do (multiple-value-bind (st k) (get-varint b hp)
                 (incf hp k)
                 (let ((len (serial-type-length st)))
                   (when (> (+ dp len) end) (corrupt "record body overflows payload"))
                   (push (decode-value b dp st) vals)
                   (incf dp len)
                   (incf count))))
      (nreverse vals))))

(defun int-serial-type (v)
  (cond ((= v 0) 8)
        ((= v 1) 9)
        ((<= -128 v 127) 1)
        ((<= -32768 v 32767) 2)
        ((<= -8388608 v 8388607) 3)
        ((<= -2147483648 v 2147483647) 4)
        ((<= -140737488355328 v 140737488355327) 5)
        (t 6)))

(defun value-serial-type (v)
  "Return (values serial-type body-octets-or-nil)."
  (cond ((eq v :null) (values 0 nil))
        ((integerp v) (values (int-serial-type v) nil))
        ((floatp v) (values 7 nil))
        ((stringp v) (let ((b (encode-text v))) (values (+ 13 (* 2 (length b))) b)))
        ((typep v '(vector (unsigned-byte 8)))
         (values (+ 12 (* 2 (length v))) v))
        (t (sql-error "cannot store value ~s" v))))

(defun encode-record (values)
  (let* ((types '()) (bodies '()) (hlen 0) (blen 0))
    (dolist (v values)
      (multiple-value-bind (st body) (value-serial-type v)
        (push st types) (push body bodies)
        (incf hlen (varint-length st))
        (incf blen (if body (length body) (serial-type-length st)))))
    (setf types (nreverse types) bodies (nreverse bodies))
    (let* ((hsize (loop with h = (1+ hlen)
                        for next = (+ hlen (varint-length h))
                        until (= next h) do (setf h next)
                        finally (return h)))
           (b (make-octets (+ hsize blen)))
           (hp (put-varint b 0 hsize))
           (dp hsize))
      (loop for st in types
            for body in bodies
            for v in values
            do (incf hp (put-varint b hp st))
               (cond (body (replace b body :start1 dp) (incf dp (length body)))
                     ((= st 7) (put-uint b dp 8 (bits-from-double v)) (incf dp 8))
                     ((<= 1 st 6)
                      (let ((n (serial-type-length st)))
                        (put-uint b dp n (ldb (byte (* 8 n) 0) v))
                        (incf dp n)))))
      b)))
