;;;; functions.lisp — built-in scalar and aggregate functions.

(in-package #:sqlite-pure)


(defmacro defsqlfun (name (min max) lambda-list &body body)
  (let ((decls (loop while (and (consp (car body)) (eq (caar body) 'declare))
                     collect (pop body))))
    `(setf (gethash ,name *functions*)
           (list ,min ,max (lambda ,lambda-list ,@decls (block nil ,@body))))))

(defmacro defaggregate (name (min max) &body body)
  "BODY returns (values step-fn final-fn); step-fn takes the argument list
and may return true when this row became the aggregate's witness (min/max)."
  `(setf (gethash ,name *aggregates*)
         (list ,min ,max (lambda () ,@body))))

;;; ------------------------------------------------------------------
;;; Compilation of calls

(defstruct agg
  name ctor arg-fns distinct filter-fn order
  (collation :binary)    ; of the (first) argument: min/max and DISTINCT compare with it
  step-fn final-fn seen)

(defvar *agg-collation* :binary "The collation of the aggregate being instantiated.")

(defun agg-instantiate (spec)
  (let ((a (copy-agg spec)))
    (multiple-value-bind (step final) (let ((*agg-collation* (agg-collation spec)))
                                        (funcall (agg-ctor spec)))
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
                  (let ((k (group-key args (list (agg-collation a)))))
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
                       (let ((k (group-key args (list (agg-collation a)))))
                         (prog1 (gethash k seen) (setf (gethash k seen) t))))
            (funcall (agg-step-fn a) args))))))
  (funcall (agg-final-fn a)))

(defun find-sql-function (lname)
  "(values scalar-def aggregate-def) for LNAME: a user definition on the
connection shadows the built-in of that name."
  (let* ((c (and *db* (conn *db*)))
         (us (and c (gethash lname (db-user-functions c))))
         (ua (and c (gethash lname (db-user-aggregates c)))))
    (cond (us (values us nil))
          (ua (values nil ua))
          (t (values (gethash lname *functions*) (gethash lname *aggregates*))))))

(defun compile-function (e scope)
  (destructuring-bind (name args distinct star filter &optional order) (cdr e)
    (let* ((lname (string-downcase-ascii name))
           (scalar (nth-value 0 (find-sql-function lname)))
           (agg (nth-value 1 (find-sql-function lname)))
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
                                      :collation (or (and args (expr-collation (first args) scope)) :binary)
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

(defun value-int32 (v)
  "sqlite3_value_int: the 64-bit integer value truncated to 32 bits."
  (let ((n (value-to-integer v)))
    (if (integerp n)
        (let ((u (ldb (byte 32 0) n))) (if (logbitp 31 u) (- u (expt 2 32)) u))
        0)))

(defun sql-substr (x start &optional (len nil len-p))
  "substrFunc from SQLite's func.c, argument quirks included."
  (let* ((blob (blobp x))
         (s (if blob x (c-string (text-of x))))
         (n (length s))
         (p1 (value-int32 start))
         (p2 (if len-p (value-int32 len) 1000000000))
         (neg nil))
    (when (and blob (zerop n)) (return-from sql-substr :null))
    (when (minusp p2) (setf p2 (- p2) neg t))
    (cond ((minusp p1)
           (incf p1 n)
           (when (minusp p1) (incf p2 p1) (when (minusp p2) (setf p2 0)) (setf p1 0)))
          ((plusp p1) (decf p1))
          ((plusp p2) (decf p2)))
    (when neg
      (decf p1 p2)
      (when (minusp p1) (incf p2 p1) (setf p1 0)))
    (let* ((b (min p1 n))
           (e (min n (+ b (max 0 p2)))))
      (subseq s b e))))

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

(defun scalar-minmax (args maxp)
  ;; minmaxFunc: among equal values min() keeps the last, max() the first
  (if (some (lambda (a) (eq a :null)) args)
      :null
      (reduce (lambda (best v)
                (let ((c (compare-values best v)))
                  (if (if maxp (minusp c) (>= c 0)) v best)))
              args)))

(defsqlfun "max" (1 nil) (args) (scalar-minmax args t))
(defsqlfun "min" (1 nil) (args) (scalar-minmax args nil))

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
          ((floatp v)
           ;; SQLite 3.40: "%!.15g", or "%!.20e" when that does not read back
           ;; (through SQLite's own AtoF) as the same double
           (let ((s (format-real v)))
             (if (eql (text-numeric-value s) (if (zerop v) 0d0 v))
                 s
                 (sql-float-text v :exp 20 :alt2 t))))
          ((stringp v) (with-output-to-string (o)
                         (write-char #\' o)
                         (loop for c across v do (when (char= c #\') (write-char #\' o)) (write-char c o))
                         (write-char #\' o)))
          (t (with-output-to-string (o)
               (write-string "X'" o)
               (loop for x across v do (format o "~2,'0X" x))
               (write-char #\' o))))))

(defsqlfun "char" (0 nil) (args)
  (map 'string (lambda (v) (safe-code-char (max 0 (let ((n (value-to-integer v))) (if (eq n :null) 0 n))))) args))

(defsqlfun "unicode" (1 1) (args)
  (let ((v (first args)))
    (with-null-args (v)
      (let ((s (c-string (text-of v))))
        (if (zerop (length s))
            :null
            (let ((code (char-code (char s 0))))
              ;; an invalid byte, as SQLite's UTF-8 reader sees it
              (if (<= #xdc80 code #xdcff)
                  (if (>= (- code #xdc00) #xc0) #xfffd (- code #xdc00))
                  code)))))))

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
        (declare (ignore d))
        (sql-round n (max 0 (min 30 (value-int32 digits))))))))

(defsqlfun "sign" (1 1) (args)
  (let ((v (first args)))
    (if (or (eq v :null) (blobp v)
            (and (not (integerp v)) (not (floatp v))
                 (null (text-numeric-value (text-of v)))))
        :null
        (let ((n (if (or (integerp v) (floatp v)) v (text-numeric-value (text-of v)))))
          (cond ((plusp n) 1) ((minusp n) -1) (t 0))))))

(defsqlfun "last_insert_rowid" (0 0) (args) (declare (ignore args)) (db-last-insert-rowid *db*))
(defsqlfun "changes" (0 0) (args) (declare (ignore args)) (db-changes *db*))
(defsqlfun "total_changes" (0 0) (args) (declare (ignore args)) (db-total-changes *db*))
(defsqlfun "sqlite_version" (0 0) (args) (declare (ignore args)) "3.40.1")
(defsqlfun "sqlite_source_id" (0 0) (args) (declare (ignore args)) "sqlite-pure")

(defparameter *compile-options*
  '("DEFAULT_CACHE_SIZE=-2000" "DEFAULT_FILE_FORMAT=4" "DEFAULT_JOURNAL_SIZE_LIMIT=-1"
    "DEFAULT_MMAP_SIZE=0" "DEFAULT_PAGE_SIZE=4096" "DEFAULT_PCACHE_INITSZ=20"
    "DEFAULT_SECTOR_SIZE=4096" "DEFAULT_SYNCHRONOUS=2" "DEFAULT_WAL_AUTOCHECKPOINT=1000"
    "DEFAULT_WAL_SYNCHRONOUS=2" "DEFAULT_WORKER_THREADS=0" "ENABLE_DBSTAT_VTAB" "ENABLE_FTS3"
    "ENABLE_FTS3_PARENTHESIS" "ENABLE_FTS4" "ENABLE_FTS5" "ENABLE_GEOPOLY"
    "ENABLE_MATH_FUNCTIONS" "ENABLE_RTREE" "MAX_ATTACHED=10" "MAX_COLUMN=2000"
    "MAX_COMPOUND_SELECT=500" "MAX_DEFAULT_PAGE_SIZE=8192" "MAX_EXPR_DEPTH=1000"
    "MAX_FUNCTION_ARG=127" "MAX_LENGTH=1000000000" "MAX_LIKE_PATTERN_LENGTH=50000"
    "MAX_MMAP_SIZE=0" "MAX_PAGE_COUNT=1073741823" "MAX_PAGE_SIZE=65536"
    "MAX_SQL_LENGTH=1000000000" "MAX_TRIGGER_DEPTH=1000" "MAX_VARIABLE_NUMBER=32766"
    "MAX_VDBE_OP=250000000" "MAX_WORKER_THREADS=8" "SECURE_DELETE" "TEMP_STORE=1"
    "THREADSAFE=0")
  "What PRAGMA compile_options reports: SQLite 3.40.1's defaults, the
extensions this library implements, and its own defaults (secure_delete on;
connections are not shared between threads).")

(defun compile-option-used-p (name)
  "sqlite3_compileoption_used: NAME, with or without SQLITE_, is a prefix of
an option that ends there (case-insensitively)."
  (let* ((z (if (and (>= (length name) 7) (string-equal name "SQLITE_" :end1 7)) (subseq name 7) name))
         (n (length z)))
    (some (lambda (opt)
            (and (>= (length opt) n) (string-equal z opt :end2 n)
                 (or (= n (length opt))
                     (let ((c (char opt n))) (not (or (alphanumericp c) (char= c #\_) (char= c #\$)))))))
          *compile-options*)))

(defsqlfun "sqlite_compileoption_used" (1 1) (args)
  (let ((v (first args)))
    (if (eq v :null) :null (if (compile-option-used-p (value-to-text v)) 1 0))))

(defsqlfun "sqlite_compileoption_get" (1 1) (args)
  (let ((n (value-to-integer (first args))))
    (if (and (integerp n) (<= 0 n) (< n (length *compile-options*)))
        (nth n *compile-options*)
        :null)))

(defsqlfun "glob" (2 2) (args)
  (destructuring-bind (pat s) args
    (when (and (not *like-matches-blobs*) (or (blobp pat) (blobp s)))
      (return-from nil 0))
    (with-null-args (pat s) (bool (glob-match (c-string (text-of pat)) (c-string (text-of s)))))))

(defsqlfun "like" (2 3) (args)
  (destructuring-bind (pat s &optional esc) args
    (when (and (not *like-matches-blobs*) (or (blobp pat) (blobp s)))
      (return-from nil 0))
    (with-null-args (pat s)
      (bool (like-match (c-string (text-of pat)) (c-string (text-of s))
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

(defun sum-operand (v)
  "sqlite3_value_numeric_type semantics: an INTEGER only if the value is
one after numeric affinity; anything else is summed as a REAL."
  (cond ((integerp v) v)
        ((floatp v) v)
        ((stringp v) (let ((n (numeric-affinity-value v)))
                       (if (integerp n) n (value-to-real v))))
        (t (value-to-real v))))

(defaggregate "sum" (1 1)
  ;; As SQLite 3.40: an exact integer sum until a REAL arrives, and a
  ;; double accumulator of every value alongside.
  (let ((isum 0) (fsum 0d0) (any nil) (real nil) (overflow nil))
    (values (lambda (args)
              (let ((v (first args)))
                (unless (eq v :null)
                  (setf any t)
                  (let ((n (sum-operand v)))
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
  (let ((best :none) (coll *agg-collation*))
    (values (lambda (args)
              (let ((v (first args)))
                (unless (eq v :null)
                  (when (or (eq best :none) (funcall sign (compare-values v best coll)))
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
