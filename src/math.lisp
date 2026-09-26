;;;; math.lisp — SQLite's math functions (SQLITE_ENABLE_MATH_FUNCTIONS,
;;;; built into the common distribution packages).  A non-numeric argument
;;;; gives NULL, as does a domain error.

(in-package #:sqlite-pure)

(defun math-arg (v)
  "The double value of V if it is numeric (after numeric affinity), else NIL."
  (cond ((integerp v) (safe-double v))
        ((floatp v) v)
        ((stringp v) (let ((n (numeric-affinity-value v)))
                       (and (or (integerp n) (floatp n)) (float n 1d0))))
        (t nil)))

(defun math-result (x)
  (cond ((or (null x) (complexp x)) :null)
        ((float-nan-p x) :null)
        (t (float x 1d0))))

(defmacro defmath1 (name (x) &body body)
  `(defsqlfun ,name (1 1) (args)
     (let ((,x (math-arg (first args))))
       (if (null ,x) :null (math-result (ignore-errors (progn ,@body)))))))

(defmacro defmath2 (name (x y) &body body)
  `(defsqlfun ,name (2 2) (args)
     (let ((,x (math-arg (first args))) (,y (math-arg (second args))))
       (if (or (null ,x) (null ,y)) :null (math-result (ignore-errors (progn ,@body)))))))

(defun inf-or (f x)
  "F of X, overflowing to infinity instead of signalling."
  (handler-case (funcall f x)
    (floating-point-overflow () (double-positive-infinity))))

(defmath1 "acos" (x) (when (<= -1 x 1) (acos x)))
(defmath1 "asin" (x) (when (<= -1 x 1) (asin x)))
(defmath1 "atan" (x) (atan x))
(defmath1 "acosh" (x) (when (>= x 1) (acosh x)))
(defmath1 "asinh" (x) (asinh x))
(defmath1 "atanh" (x) (cond ((< -1 x 1) (atanh x))
                            ((= x 1) (double-positive-infinity))
                            ((= x -1) (double-negative-infinity))))
(defmath1 "cos" (x) (cos x))
(defmath1 "sin" (x) (sin x))
(defmath1 "tan" (x) (tan x))
(defmath1 "cosh" (x) (inf-or #'cosh x))
(defmath1 "sinh" (x) (handler-case (sinh x)
                       (floating-point-overflow ()
                         (if (plusp x) (double-positive-infinity) (double-negative-infinity)))))
(defmath1 "tanh" (x) (tanh x))
(defmath1 "exp" (x) (if (> x 709.8d0) (double-positive-infinity) (exp x)))
(defmath1 "ln" (x) (when (plusp x) (log x)))
(defmath1 "log10" (x) (when (plusp x) (log x 10d0)))
(defmath1 "log2" (x) (when (plusp x) (log x 2d0)))
(defmath1 "sqrt" (x) (when (>= x 0) (sqrt x)))
(defmath1 "degrees" (x) (* x (/ 180d0 pi)))
(defmath1 "radians" (x) (* x (/ pi 180d0)))

(defsqlfun "pi" (0 0) (args) (declare (ignore args)) (float pi 1d0))

(defsqlfun "log" (1 2) (args)
  ;; log(X) is the base-10 logarithm; log(B, X) is base B
  (let ((vals (mapcar #'math-arg args)))
    (if (some #'null vals)
        :null
        (math-result
         (ignore-errors
          (if (cdr vals)
              (destructuring-bind (b x) vals
                (when (and (plusp b) (/= b 1) (plusp x)) (/ (log x) (log b))))
              (when (plusp (first vals)) (log (first vals) 10d0))))))))

(defun sql-pow (x y)
  (cond ((and (zerop x) (minusp y)) (double-positive-infinity))
        ((and (minusp x) (/= y (ftruncate y))) nil)
        (t (handler-case (expt x (if (= y (ftruncate y)) (truncate y) y))
             (floating-point-overflow () (double-positive-infinity))))))

(defmath2 "pow" (x y) (sql-pow x y))
(defmath2 "power" (x y) (sql-pow x y))
(defmath2 "atan2" (y x) (atan y x))
(defmath2 "mod" (x y) (unless (zerop y) (rem x y)))

(defmacro defrounding (name fn)
  `(defsqlfun ,name (1 1) (args)
     (let* ((v (first args))
            (n (if (stringp v) (numeric-affinity-value v) v)))
       (cond ((integerp n) n)
             ((floatp n) (if (float-infinity-p n) n (float (,fn n) 1d0)))
             (t :null)))))

(defrounding "ceil" fceiling)
(defrounding "ceiling" fceiling)
(defrounding "floor" ffloor)
(defrounding "trunc" ftruncate)
