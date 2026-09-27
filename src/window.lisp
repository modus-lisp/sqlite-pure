;;;; window.lisp — window functions.
;;;;
;;;; A SELECT core with window functions first produces all of its rows
;;;; (after WHERE, GROUP BY and HAVING) as environments; each window
;;;; function then partitions and orders those rows, computes one value per
;;;; row, and stores it in the row's ENV-WIN vector, where the compiled call
;;;; reads it back.  DISTINCT, ORDER BY and LIMIT apply afterwards.

(in-package #:sqlite-pure)

(defstruct wspec
  name              ; lowercased function name
  arg-fns           ; compiled arguments
  agg               ; AGG template for aggregate window functions
  partition-fns partition-colls
  order             ; list of (fn desc collation nulls)
  frame)            ; (unit start end) or NIL for the default

(defparameter +window-only-functions+
  '("row_number" "rank" "dense_rank" "percent_rank" "cume_dist" "ntile"
    "lag" "lead" "first_value" "last_value" "nth_value"))

(defun resolve-window-spec (spec scope)
  "Merge a spec with its base window (WINDOW w AS ...; OVER (w ...))."
  (if (eq (car spec) :ref)
      (or (cdr (assoc (second spec) (scope-window-defs scope) :test #'name=))
          (sql-error "no such window: ~a" (second spec)))
      (destructuring-bind (&key base partition order frame) (cdr spec)
        (if base
            (let ((b (or (cdr (assoc base (scope-window-defs scope) :test #'name=))
                         (sql-error "no such window: ~a" base))))
              (list :spec :base nil
                          :partition (or partition (getf (cdr b) :partition))
                          :order (or order (getf (cdr b) :order))
                          :frame (or frame (getf (cdr b) :frame))))
            spec))))

(defun compile-window-call (e scope)
  (destructuring-bind (name args distinct star filter over) (cdr e)
    (let* ((lname (string-downcase-ascii name))
           (spec (resolve-window-spec over scope))
           (aggdef (nth-value 1 (find-sql-function lname)))
           (winfn (member lname +window-only-functions+ :test #'string=)))
      (unless (or aggdef winfn)
        (sql-error "~a() may not be used as a window function" name))
      (when (and star (not (string= lname "count")))
        (sql-error "wrong number of arguments to function ~a()" name))
      (when (and distinct (not aggdef))
        (sql-error "DISTINCT is not supported for window functions"))
      (let* ((arg-fns (mapcar (lambda (a) (compile-expr a scope)) args))
             (ws (make-wspec
                  :name lname
                  :arg-fns arg-fns
                  :agg (and aggdef (not winfn)
                            (destructuring-bind (min max ctor) aggdef
                              (unless (or star (<= min (length args) (or max (length args))))
                                (sql-error "wrong number of arguments to function ~a()" name))
                              (make-agg :name lname :ctor ctor :arg-fns arg-fns :distinct distinct
                                        :collation (or (and args (expr-collation (first args) scope)) :binary)
                                        :filter-fn (and filter (compile-expr filter scope)))))
                  :partition-fns (mapcar (lambda (x) (compile-expr x scope)) (getf (cdr spec) :partition))
                  :partition-colls (mapcar (lambda (x) (or (expr-collation x scope) :binary))
                                           (getf (cdr spec) :partition))
                  :order (compile-order-terms (getf (cdr spec) :order) nil scope)
                  :frame (let ((f (getf (cdr spec) :frame)))
                           (when f
                             (destructuring-bind (unit start end &optional exclude) f
                               (list unit (compile-bound start) (compile-bound end) exclude)))))))
        (when winfn (check-window-arity lname (length args)))
        (let ((k (vector-push-extend ws (scope-windows scope))))
          (lambda (env) (svref (env-win env) k)))))))

(defun compile-bound (b)
  (if (second b)
      (list (first b) (let ((f (compile-expr (second b) (make-scope))))
                        (let ((v (funcall f nil)))
                          (unless (and (or (integerp v) (floatp v)) (>= v 0))
                            (sql-error "frame starting offset must be a non-negative number"))
                          v)))
      b))

(defun check-window-arity (name n)
  (let ((ok (cond ((member name '("row_number" "rank" "dense_rank" "percent_rank" "cume_dist")
                           :test #'string=) (= n 0))
                  ((string= name "ntile") (= n 1))
                  ((member name '("lag" "lead") :test #'string=) (<= 1 n 3))
                  ((member name '("first_value" "last_value") :test #'string=) (= n 1))
                  ((string= name "nth_value") (= n 2)))))
    (unless ok (sql-error "wrong number of arguments to function ~a()" name))))

;;; ------------------------------------------------------------------
;;; Evaluation

(defun compute-windows (wspecs envs)
  "Fill ENV-WIN of every environment in ENVS."
  (let ((nwin (length wspecs)))
    (dolist (e envs) (setf (env-win e) (make-array nwin :initial-element :null)))
    (loop for ws across wspecs
          for k from 0
          do (dolist (part (window-partitions ws envs))
               (compute-window-partition ws k part)))))

(defun window-partitions (ws envs)
  "Lists of (env . order-keys) per partition, each sorted by ORDER BY."
  (let ((table (make-hash-table :test #'equal)) (order '()))
    (dolist (e envs)
      (let ((key (group-key (mapcar (lambda (f) (funcall f e)) (wspec-partition-fns ws))
                            (wspec-partition-colls ws))))
        (unless (nth-value 1 (gethash key table)) (push key order))
        (push (cons (mapcar (lambda (o) (funcall (first o) e)) (wspec-order ws)) e)
              (gethash key table))))
    (loop for key in (nreverse order)
          collect (let ((items (nreverse (gethash key table))))
                    (coerce (sort-rows items (mapcar #'cdr (wspec-order ws))) 'vector)))))

(defun order-keys-equal (a b ws)
  (loop for x in a for y in b
        for (nil nil coll) in (wspec-order ws)
        always (or (and (eq x :null) (eq y :null))
                   (and (not (eq x :null)) (not (eq y :null))
                        (zerop (compare-values x y coll))))))

(defun compute-window-partition (ws k part)
  (let* ((n (length part))
         (peer-start (make-array n))
         (peer-end (make-array n))
         (group-no (make-array n)))
    ;; peers: rows whose ORDER BY keys are equal (all rows, without ORDER BY)
    (let ((g 0))
      (loop with start = 0
            for i from 0 below n
            do (when (and (> i 0) (not (order-keys-equal (car (aref part i)) (car (aref part (1- i))) ws)))
                 (loop for j from start below i do (setf (aref peer-end j) (1- i)))
                 (setf start i)
                 (incf g))
               (setf (aref peer-start i) start (aref group-no i) g)
            finally (loop for j from start below n do (setf (aref peer-end j) (1- n)))))
    (flet ((env-at (i) (cdr (aref part i)))
           (store (i v) (setf (svref (env-win (cdr (aref part i))) k) v))
           (arg (i j) (funcall (nth j (wspec-arg-fns ws)) (cdr (aref part i)))))
      (let ((name (wspec-name ws)))
        (cond
          ((string= name "row_number") (dotimes (i n) (store i (1+ i))))
          ((string= name "rank") (dotimes (i n) (store i (1+ (aref peer-start i)))))
          ((string= name "dense_rank") (dotimes (i n) (store i (1+ (aref group-no i)))))
          ((string= name "percent_rank")
           (dotimes (i n) (store i (if (<= n 1) 0d0 (/ (float (aref peer-start i) 1d0) (1- n))))))
          ((string= name "cume_dist")
           (dotimes (i n) (store i (/ (float (1+ (aref peer-end i)) 1d0) n))))
          ((string= name "ntile")
           (dotimes (i n)
             (let ((b (value-to-integer (arg i 0))))
               (unless (and (integerp b) (plusp b))
                 (sql-error "argument of ntile must be a positive integer"))
               (store i (ntile-bucket i n b)))))
          ((member name '("lag" "lead") :test #'string=)
           (let ((nargs (length (wspec-arg-fns ws))))
             (dotimes (i n)
               (let* ((off (if (> nargs 1) (value-to-integer (arg i 1)) 1))
                      (j (if (string= name "lag") (- i off) (+ i off))))
                 (store i (cond ((not (integerp off)) :null)
                                ((< -1 j n) (arg j 0))
                                ((> nargs 2) (arg i 2))
                                (t :null)))))))
          ((member name '("first_value" "last_value" "nth_value") :test #'string=)
           (dotimes (i n)
             (let ((rows (frame-rows ws part i peer-start peer-end group-no)))
               (store i (cond ((null rows) :null)
                              ((string= name "first_value") (arg (first rows) 0))
                              ((string= name "last_value") (arg (car (last rows)) 0))
                              (t (let ((m (value-to-integer (arg i 1))))
                                   (unless (and (integerp m) (plusp m))
                                     (sql-error "second argument to nth_value must be a positive integer"))
                                   (let ((j (nth (1- m) rows)))
                                     (if j (arg j 0) :null)))))))))
          (t (compute-window-aggregate ws part #'store #'env-at peer-start peer-end group-no)))))))

(defun ntile-bucket (i n b)
  "SQLite's ntile: the first N mod B buckets get one extra row."
  (let* ((size (floor n b))
         (big (mod n b)))
    (if (< i (* big (1+ size)))
        (1+ (floor i (1+ size)))
        (1+ (+ big (floor (- i (* big (1+ size))) (max size 1)))))))

(defun frame-bounds (ws part i peer-start peer-end group-no)
  "Inclusive (values lo hi) of row I's frame."
  (let* ((n (length part))
         (frame (or (wspec-frame ws)
                    (if (wspec-order ws)
                        '(:range (:unbounded-preceding) (:current-row))
                        '(:range (:unbounded-preceding) (:unbounded-following))))))
    (destructuring-bind (unit start end &optional exclude) frame
      (declare (ignore exclude))
      (flet ((bound (b startp)
               (ecase (first b)
                 (:unbounded-preceding 0)
                 (:unbounded-following (1- n))
                 (:current-row (ecase unit
                                 (:rows i)
                                 ((:range :groups) (if startp (aref peer-start i) (aref peer-end i)))))
                 ((:preceding :following)
                  (let ((off (second b)) (sign (if (eq (first b) :preceding) -1 1)))
                    (ecase unit
                      (:rows (+ i (* sign (truncate off))))
                      (:groups
                       (let ((g (+ (aref group-no i) (* sign (truncate off)))))
                         (if startp
                             (or (position-if (lambda (x) (>= x g)) group-no) n)
                             (or (position-if (lambda (x) (<= x g)) group-no :from-end t) -1))))
                      (:range (range-bound ws part i off sign startp))))))))
        (let ((lo (max 0 (bound start t)))
              (hi (min (1- n) (bound end nil))))
          (values lo hi))))))

(defun frame-exclude (ws)
  (fourth (wspec-frame ws)))

(defun frame-rows (ws part i peer-start peer-end group-no)
  "The row indices in row I's frame, in order, after its EXCLUDE clause."
  (multiple-value-bind (lo hi) (frame-bounds ws part i peer-start peer-end group-no)
    (let ((ex (frame-exclude ws)))
      (loop for j from lo to hi
            unless (case ex
                     (:current-row (= j i))
                     (:group (<= (aref peer-start i) j (aref peer-end i)))
                     (:ties (and (/= j i) (<= (aref peer-start i) j (aref peer-end i)))))
              collect j))))

(defun range-bound (ws part i off sign startp)
  "RANGE n PRECEDING/FOLLOWING: compare the single numeric ORDER BY key."
  (let* ((order (wspec-order ws)))
    (unless (= (length order) 1)
      (sql-error "RANGE with offset PRECEDING/FOLLOWING requires exactly one ORDER BY term"))
    (let* ((desc (second (first order)))
           (n (length part))
           (key (lambda (j) (first (car (aref part j)))))
           (v (funcall key i)))
      (if (or (eq v :null) (not (or (integerp v) (floatp v))))
          ;; NULL (or non-numeric) keys: the frame is the peer group
          (let ((j i))
            (if startp
                (progn (loop while (and (> j 0) (equal (funcall key (1- j)) v)) do (decf j)) j)
                (progn (loop while (and (< j (1- n)) (equal (funcall key (1+ j)) v)) do (incf j)) j)))
          (let* ((target (if desc (- v (* sign off)) (+ v (* sign off))))
                 (inside (lambda (j)
                           (let ((x (funcall key j)))
                             (and (or (integerp x) (floatp x))
                                  (if startp
                                      (if desc (<= x target) (>= x target))
                                      (if desc (>= x target) (<= x target))))))))
            (if startp
                (or (loop for j from 0 below n when (funcall inside j) return j) n)
                (or (loop for j from (1- n) downto 0 when (funcall inside j) return j) -1)))))))

(defun compute-window-aggregate (ws part store env-at peer-start peer-end group-no)
  (let* ((n (length part))
         (tmpl (wspec-agg ws))
         (frame (wspec-frame ws))
         (from-start (and (null (fourth frame))
                          (or (null frame) (eq (first (second frame)) :unbounded-preceding)))))
    (if from-start
        ;; the frame only ever grows: step an accumulator forward
        (let ((acc (agg-instantiate tmpl)) (upto -1))
          (dotimes (i n)
            (multiple-value-bind (lo hi) (frame-bounds ws part i peer-start peer-end group-no)
              (declare (ignore lo))
              (loop while (< upto hi)
                    do (incf upto) (agg-step acc (funcall env-at upto)))
              (funcall store i (agg-final-value acc)))))
        (dotimes (i n)
          (let ((acc (agg-instantiate tmpl)))
            (dolist (j (frame-rows ws part i peer-start peer-end group-no))
              (agg-step acc (funcall env-at j)))
            (funcall store i (agg-final-value acc)))))))

(defun agg-final-value (a)
  "The aggregate's current value, without consuming it."
  (funcall (agg-final-fn a)))
