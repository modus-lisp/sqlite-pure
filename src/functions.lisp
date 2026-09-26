;;;; functions.lisp — built-in scalar and aggregate functions.

(in-package #:sqlite-pure)


(defmacro defsqlfun (name (min max) lambda-list &body body)
  `(setf (gethash ,name *functions*)
         (list ,min ,max (lambda ,lambda-list ,@body))))

(defmacro defaggregate (name (min max) &body body)
  "BODY returns (values step-fn final-fn); step-fn takes the argument list
and may return true when this row became the aggregate's witness (min/max)."
  `(setf (gethash ,name *aggregates*)
         (list ,min ,max (lambda () ,@body))))

;;; ------------------------------------------------------------------
;;; Compilation of calls

(defstruct agg
  name ctor arg-fns distinct filter-fn order
  step-fn final-fn seen)

(defun agg-instantiate (spec)
  (let ((a (copy-agg spec)))
    (multiple-value-bind (step final) (funcall (agg-ctor spec))
      (setf (agg-step-fn a) step (agg-final-fn a) final
            (agg-seen a) (and (agg-distinct spec) (make-hash-table :test #'equal))))
    (when (agg-order spec) (setf (agg-seen a) (or (agg-seen a) (make-hash-table :test #'equal))))
    a))

(defun agg-step (a env)
  (when (or (null (agg-filter-fn a)) (eq (truth (funcall (agg-filter-fn a) env)) t))
    (let ((args (mapcar (lambda (f) (funcall f env)) (agg-arg-fns a))))
      (cond ((agg-order a)
             ;; ordered aggregate: buffer (keys . args), feed at the end
             (push (cons (mapcar (lambda (spec) (funcall (first spec) env)) (agg-order a)) args)
                   (gethash :buffer (agg-seen a)))
             nil)
            ((and (agg-distinct a)
                  (let ((k (group-key args)))
                    (if (gethash k (agg-seen a)) t (progn (setf (gethash k (agg-seen a)) t) nil))))
             nil)
            (t (funcall (agg-step-fn a) args))))))

(defun agg-final (a)
  (when (agg-order a)
    (let ((items (sort-rows (reverse (gethash :buffer (agg-seen a)))
                            (mapcar #'cdr (agg-order a))))
          (seen (make-hash-table :test #'equal)))
      (dolist (it items)
        (let ((args (cdr it)))
          (unless (and (agg-distinct a)
                       (let ((k (group-key args)))
                         (prog1 (gethash k seen) (setf (gethash k seen) t))))
            (funcall (agg-step-fn a) args))))))
  (funcall (agg-final-fn a)))

(defun compile-function (e scope)
  (destructuring-bind (name args distinct star filter &optional order) (cdr e)
    (let* ((lname (string-downcase-ascii name))
           (agg (gethash lname *aggregates*))
           (scalar (gethash lname *functions*))
           (nargs (length args)))
      (when (and star (not (string= lname "count")))
        (sql-error "wrong number of arguments to function ~a()" name))
      (cond
        ;; aggregate use
        ((and agg (not (and scalar (/= nargs 1) (member lname '("min" "max") :test #'string=))))
         (unless (scope-agg-p scope)
           (if (scope-in-agg-arg scope)
               (sql-error "misuse of aggregate function ~a()" name)
               (sql-error "misuse of aggregate: ~a()" name)))
         (destructuring-bind (min max ctor) agg
           (unless (or star (<= min nargs (or max nargs)))
             (sql-error "wrong number of arguments to function ~a()" name))
           (when (and distinct (/= nargs 1))
             (sql-error "DISTINCT aggregates must have exactly one argument"))
           (setf (scope-agg-p scope) nil (scope-in-agg-arg scope) t)
           (let ((spec (unwind-protect
                            (make-agg :name lname :ctor ctor
                                      :arg-fns (mapcar (lambda (a) (compile-expr a scope)) args)
                                      :distinct distinct
                                      :filter-fn (and filter (compile-expr filter scope))
                                      :order (and order (compile-order-terms order nil scope)))
                         (setf (scope-agg-p scope) t (scope-in-agg-arg scope) nil))))
             (let ((k (vector-push-extend spec (scope-aggs scope))))
               (lambda (env) (svref (env-agg env) k))))))
        (scalar
         (when filter (sql-error "FILTER may not be used with non-aggregate ~a()" name))
         (destructuring-bind (min max fn) scalar
           (unless (<= min nargs (or max nargs))
             (sql-error "wrong number of arguments to function ~a()" name))
           (cond
             ;; lazily evaluated forms
             ((member lname '("coalesce" "ifnull") :test #'string=)
              (let ((fns (mapcar (lambda (a) (compile-expr a scope)) args)))
                (lambda (env)
                  (dolist (f fns :null)
                    (let ((v (funcall f env))) (unless (eq v :null) (return v)))))))
             ((string= lname "iif")
              (destructuring-bind (c a b) (mapcar (lambda (x) (compile-expr x scope)) args)
                (lambda (env) (if (eq (truth (funcall c env)) t) (funcall a env) (funcall b env)))))
             ((member lname '("likely" "unlikely" "likelihood") :test #'string=)
              (compile-expr (first args) scope))
             (t (let ((fns (mapcar (lambda (a) (compile-expr a scope)) args)))
                  (lambda (env) (funcall fn (mapcar (lambda (f) (funcall f env)) fns))))))))
        (agg (sql-error "misuse of aggregate function ~a()" name))
        (t (sql-error "no such function: ~a" name))))))

;;; ------------------------------------------------------------------
;;; Helpers

(defmacro with-null-args ((&rest vars) &body body)
  "Return NULL if any of VARS is NULL."
  `(if (or ,@(mapcar (lambda (v) `(eq ,v :null)) vars)) :null (progn ,@body)))

(defun text-of (v) (value-to-text v))

;;; ------------------------------------------------------------------
;;; Scalar functions

(defsqlfun "abs" (1 1) (args)
  (let ((v (first args)))
    (cond ((eq v :null) :null)
          ((integerp v) (if (= v +i64-min+) (sql-error "integer overflow") (abs v)))
          ((floatp v) (abs v))
          (t (let ((n (value-to-number v))) (if (integerp n) (abs (float n 1d0)) (abs n)))))))

(defsqlfun "typeof" (1 1) (args) (type-name-of (first args)))

(defsqlfun "length" (1 1) (args)
  (let ((v (first args)))
    (cond ((eq v :null) :null)
          ((stringp v) (let ((z (position (code-char 0) v))) (or z (length v))))
          ((blobp v) (length v))
          (t (length (value-to-text v))))))

(defsqlfun "octet_length" (1 1) (args)
  (let ((v (first args)))
    (cond ((eq v :null) :null)
          ((blobp v) (length v))
          (t (utf8-length (value-to-text v))))))

(defsqlfun "lower" (1 1) (args)
  (with-null-args ((first args)) (string-downcase-ascii (text-of (first args)))))
(defsqlfun "upper" (1 1) (args)
  (with-null-args ((first args)) (string-upcase-ascii (text-of (first args)))))

(defun trim-chars (args)
  (if (cdr args) (coerce (text-of (second args)) 'list) '(#\Space)))

(defsqlfun "trim" (1 2) (args)
  (with-null-args ((first args) (if (cdr args) (second args) 0))
    (string-trim (trim-chars args) (text-of (first args)))))
(defsqlfun "ltrim" (1 2) (args)
  (with-null-args ((first args) (if (cdr args) (second args) 0))
    (string-left-trim (trim-chars args) (text-of (first args)))))
(defsqlfun "rtrim" (1 2) (args)
  (with-null-args ((first args) (if (cdr args) (second args) 0))
    (string-right-trim (trim-chars args) (text-of (first args)))))

(defun sql-substr (x start &optional (len nil len-p))
  (let* ((blob (blobp x))
         (s (if blob x (text-of x)))
         (n (length s))
         (start (value-to-integer start))
         (len (and len-p (value-to-integer len))))
    ;; SQLite semantics: 1-based; 0 behaves as "just before the first";
    ;; negative counts from the end; negative length takes chars before.
    (let (b e)
      (cond ((> start 0) (setf b (1- start)))
            ((< start 0) (setf b (+ n start)))
            (t (setf b -1)))
      (if (not len-p)
          (setf e n)
          (if (>= len 0)
              (setf e (+ b len))
              (setf e b b (+ b len))))
      (when (and (not len-p) (< b 0)) (setf b 0))
      (setf b (max 0 b) e (min n (max 0 e)))
      (if (>= b e)
          (if blob (make-octets 0) "")
          (subseq s b e)))))

(defsqlfun "substr" (2 3) (args)
  (if (some (lambda (a) (eq a :null)) args) :null (apply #'sql-substr args)))
(defsqlfun "substring" (2 3) (args)
  (if (some (lambda (a) (eq a :null)) args) :null (apply #'sql-substr args)))

(defsqlfun "instr" (2 2) (args)
  (destructuring-bind (a b) args
    (with-null-args (a b)
      (if (and (blobp a) (blobp b))
          (1+ (or (search b a) -1))
          (1+ (or (search (text-of b) (text-of a)) -1))))))

(defsqlfun "replace" (3 3) (args)
  (destructuring-bind (s from to) args
    (with-null-args (s from to)
      (let ((s (text-of s)) (from (text-of from)) (to (text-of to)))
        (if (string= from "")
            s
            (with-output-to-string (out)
              (loop with start = 0
                    for pos = (search from s :start2 start)
                    do (write-string s out :start start :end (or pos (length s)))
                       (if pos
                           (progn (write-string to out) (setf start (+ pos (length from))))
                           (return)))))))))

(defsqlfun "coalesce" (2 nil) (args) (or (find-if-not (lambda (v) (eq v :null)) args) :null))
(defsqlfun "ifnull" (2 2) (args) (or (find-if-not (lambda (v) (eq v :null)) args) :null))
(defsqlfun "iif" (3 3) (args) (declare (ignore args)) :null)
(defsqlfun "likely" (1 1) (args) (first args))
(defsqlfun "unlikely" (1 1) (args) (first args))
(defsqlfun "likelihood" (2 2) (args) (first args))

(defsqlfun "nullif" (2 2) (args)
  (destructuring-bind (a b) args
    (if (and (not (eq a :null)) (not (eq b :null)) (zerop (compare-values a b))) :null a)))

(defun scalar-minmax (args sign)
  (if (some (lambda (a) (eq a :null)) args)
      :null
      (reduce (lambda (a b) (if (funcall sign (compare-values b a)) b a)) args)))

(defsqlfun "max" (1 nil) (args) (scalar-minmax args #'plusp))
(defsqlfun "min" (1 nil) (args) (scalar-minmax args #'minusp))

(defsqlfun "hex" (1 1) (args)
  (let* ((v (first args))
         (b (if (blobp v) v (utf8-encode (if (eq v :null) "" (text-of v))))))
    (with-output-to-string (s)
      (loop for x across b do (format s "~2,'0X" x)))))

(defsqlfun "unhex" (1 2) (args)
  (let ((v (first args)) (ignore (if (cdr args) (text-of (second args)) "")))
    (with-null-args (v)
      (let* ((s (remove-if (lambda (c) (find c ignore)) (text-of v))))
        (if (or (oddp (length s)) (notevery (lambda (c) (digit-char-p c 16)) s))
            :null
            (let ((b (make-octets (floor (length s) 2))))
              (dotimes (i (length b) b)
                (setf (aref b i) (parse-integer s :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))))))))

(defsqlfun "quote" (1 1) (args)
  (let ((v (first args)))
    (cond ((eq v :null) "NULL")
          ((integerp v) (format nil "~d" v))
          ((floatp v) (let ((s (format-real v)))
                        ;; quote() uses enough digits to round-trip
                        (let ((r (format-real-roundtrip v))) (declare (ignore s)) r)))
          ((stringp v) (with-output-to-string (o)
                         (write-char #\' o)
                         (loop for c across v do (when (char= c #\') (write-char #\' o)) (write-char c o))
                         (write-char #\' o)))
          (t (with-output-to-string (o)
               (write-string "X'" o)
               (loop for x across v do (format o "~2,'0X" x))
               (write-char #\' o))))))

(defun format-real-roundtrip (x)
  "%!.17g, shortened to the fewest digits that round-trip (SQLite's quote())."
  (cond ((float-infinity-p x) (if (plusp x) "9.0e+999" "-9.0e+999"))
        (t (let ((best nil))
             (loop for p from 15 to 17
                   do (let ((s (format-real-digits x p)))
                        (when (= (value-to-real s) x) (setf best s) (return))))
             (or best (format-real-digits x 17))))))

(defun format-real-digits (x p)
  "Like FORMAT-REAL but with P significant digits."
  (if (zerop x) "0.0"
      (let* ((neg (minusp x)) (r (abs (rational x)))
             (e (let ((e (floor (log (abs x) 10))))
                  (loop while (> (expt 10 e) r) do (decf e))
                  (loop while (<= (expt 10 (1+ e)) r) do (incf e))
                  e))
             (d (round (/ r (expt 10 (- e (1- p)))))))
        (when (>= d (expt 10 p)) (setf d (round d 10)) (incf e))
        (let* ((digits (string-right-trim "0" (format nil "~d" d)))
               (digits (if (string= digits "") "0" digits))
               (body (if (or (< e -4) (>= e p))
                         (format nil "~a.~a~ae~a~2,'0d" (char digits 0)
                                 (if (> (length digits) 1) (subseq digits 1) "")
                                 (if (> (length digits) 1) "" "0")
                                 (if (minusp e) "-" "+") (abs e))
                         (cond ((minusp e) (format nil "0.~a~a" (make-string (- (- e) 1) :initial-element #\0) digits))
                               ((>= e (1- (length digits)))
                                (format nil "~a~a.0" digits (make-string (- e (1- (length digits))) :initial-element #\0)))
                               (t (format nil "~a.~a" (subseq digits 0 (1+ e)) (subseq digits (1+ e))))))))
          (if neg (concatenate 'string "-" body) body)))))

(defsqlfun "char" (0 nil) (args)
  (map 'string (lambda (v) (safe-code-char (max 0 (let ((n (value-to-integer v))) (if (eq n :null) 0 n))))) args))

(defsqlfun "unicode" (1 1) (args)
  (let ((v (first args)))
    (with-null-args (v)
      (let ((s (text-of v))) (if (plusp (length s)) (char-code (char s 0)) :null)))))

(defsqlfun "zeroblob" (1 1) (args)
  (let ((n (value-to-integer (first args)))) (make-octets (if (integerp n) (max 0 n) 0))))

(defvar *sql-random-state* (make-random-state t))

(defsqlfun "random" (0 0) (args)
  (declare (ignore args))
  (to-signed64 (random (expt 2 64) *sql-random-state*)))

(defsqlfun "randomblob" (1 1) (args)
  (let* ((n (max 1 (let ((n (value-to-integer (first args)))) (if (integerp n) n 1))))
         (b (make-octets n)))
    (dotimes (i n b) (setf (aref b i) (random 256 *sql-random-state*)))))

(defsqlfun "round" (1 2) (args)
  (let ((x (first args)) (digits (if (cdr args) (second args) 0)))
    (with-null-args (x digits)
      (let ((n (value-to-real x))
            (d (value-to-integer digits)))
        (sql-round n (max 0 (min 30 (if (integerp d) d 0))))))))

(defsqlfun "sign" (1 1) (args)
  (let ((v (first args)))
    (if (or (eq v :null) (and (not (integerp v)) (not (floatp v))
                              (null (text-numeric-value (text-of v)))))
        :null
        (let ((n (if (or (integerp v) (floatp v)) v (text-numeric-value (text-of v)))))
          (cond ((plusp n) 1) ((minusp n) -1) (t 0))))))

(defsqlfun "last_insert_rowid" (0 0) (args) (declare (ignore args)) (db-last-insert-rowid *db*))
(defsqlfun "changes" (0 0) (args) (declare (ignore args)) (db-changes *db*))
(defsqlfun "total_changes" (0 0) (args) (declare (ignore args)) (db-total-changes *db*))
(defsqlfun "sqlite_version" (0 0) (args) (declare (ignore args)) "3.40.1")
(defsqlfun "sqlite_source_id" (0 0) (args) (declare (ignore args)) "sqlite-pure")

(defsqlfun "glob" (2 2) (args)
  (destructuring-bind (pat s) args
    (with-null-args (pat s) (bool (glob-match (text-of pat) (text-of s))))))

(defsqlfun "like" (2 3) (args)
  (destructuring-bind (pat s &optional esc) args
    (with-null-args (pat s)
      (bool (like-match (text-of pat) (text-of s)
                        (and esc (not (eq esc :null)) (char (text-of esc) 0)))))))

(defsqlfun "concat" (1 nil) (args)
  (apply #'concatenate 'string (mapcar (lambda (a) (if (eq a :null) "" (text-of a))) args)))

(defsqlfun "concat_ws" (2 nil) (args)
  (let ((sep (first args)))
    (with-null-args (sep)
      (format nil (concatenate 'string "~{~a~^" (substitute-string "~" "~~" (text-of sep)) "~}")
              (mapcar #'text-of (remove :null (rest args)))))))

(defun substitute-string (old new s)
  (with-output-to-string (out)
    (loop with start = 0
          for pos = (search old s :start2 start)
          do (write-string s out :start start :end (or pos (length s)))
             (if pos (progn (write-string new out) (setf start (+ pos (length old)))) (return)))))

(defsqlfun "soundex" (1 1) (args)
  (let* ((v (first args))
         (s (if (eq v :null) "" (text-of v)))
         (codes "01230120022455012623010202")
         (start (position-if #'alpha-char-p s)))
    (if (null start)
        "?000"
        (let ((out (list (char-upcase (char s start))))
              (last (char codes (- (char-code (char-upcase (char s start))) 65))))
          (loop for i from (1+ start) below (length s)
                for c = (char-upcase (char s i))
                while (< (length out) 4)
                do (when (char<= #\A c #\Z)
                     (let ((code (char codes (- (char-code c) 65))))
                       (when (and (char/= code #\0) (char/= code last))
                         (push code out))
                       (setf last code))))
          (let ((r (coerce (nreverse out) 'string)))
            (concatenate 'string r (make-string (- 4 (length r)) :initial-element #\0)))))))

;;; ------------------------------------------------------------------
;;; Aggregates

(defaggregate "count" (0 1)
  (let ((n 0))
    (values (lambda (args)
              (when (or (null args) (not (eq (first args) :null))) (incf n))
              nil)
            (lambda () n))))

(defaggregate "sum" (1 1)
  ;; As SQLite 3.40: an exact integer sum until a REAL arrives, and a
  ;; double accumulator of every value alongside.
  (let ((isum 0) (fsum 0d0) (any nil) (real nil) (overflow nil))
    (values (lambda (args)
              (let ((v (first args)))
                (unless (eq v :null)
                  (setf any t)
                  (let ((n (value-to-number v)))
                    (setf fsum (+ fsum (float n 1d0)))
                    (if (integerp n)
                        (unless real
                          (incf isum n)
                          (unless (i64-p isum) (setf overflow t)))
                        (setf real t)))))
              nil)
            (lambda ()
              (cond ((not any) :null)
                    (real fsum)
                    (overflow (sql-error "integer overflow"))
                    (t isum))))))

(defaggregate "total" (1 1)
  (let ((sum 0d0))
    (values (lambda (args)
              (let ((v (first args)))
                (unless (eq v :null) (setf sum (+ sum (float (value-to-number v) 1d0)))))
              nil)
            (lambda () sum))))

(defaggregate "avg" (1 1)
  (let ((sum 0d0) (n 0))
    (values (lambda (args)
              (let ((v (first args)))
                (unless (eq v :null)
                  (setf sum (+ sum (float (value-to-number v) 1d0)))
                  (incf n)))
              nil)
            (lambda () (if (zerop n) :null (/ sum n))))))

(defun make-minmax (sign)
  (let ((best :none))
    (values (lambda (args)
              (let ((v (first args)))
                (unless (eq v :null)
                  (when (or (eq best :none) (funcall sign (compare-values v best)))
                    (setf best v)
                    t))))
            (lambda () (if (eq best :none) :null best)))))

(defaggregate "max" (1 1) (make-minmax #'plusp))
(defaggregate "min" (1 1) (make-minmax #'minusp))

(defun make-group-concat ()
  (let ((parts '()))
    (values (lambda (args)
              (let ((v (first args))
                    (sep (if (cdr args) (second args) ",")))
                (unless (eq v :null)
                  (push (cons (if parts (if (eq sep :null) "" (text-of sep)) "") (text-of v)) parts)))
              nil)
            (lambda ()
              (if (null parts)
                  :null
                  (with-output-to-string (s)
                    (dolist (p (reverse parts))
                      (write-string (car p) s) (write-string (cdr p) s))))))))

(defaggregate "group_concat" (1 2) (make-group-concat))
(defaggregate "string_agg" (2 2) (make-group-concat))
