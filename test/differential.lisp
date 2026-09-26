;;;; test/differential.lisp — replay test/cases/*.test against sqlite-pure
;;;; and compare every statement's outcome with what real SQLite produced
;;;; (test/expected.sexp, written by test/gen-expected.py).

(defpackage #:sqlite-pure.test
  (:use #:cl)
  (:local-nicknames (#:s #:sqlite-pure))
  (:export #:run #:run-differential))

(in-package #:sqlite-pure.test)

(defvar *verbose* nil)

(defun read-expected (path)
  (with-open-file (in path :external-format :utf-8)
    (let ((*read-default-float-format* 'double-float)
          (*package* (find-package '#:sqlite-pure.test)))
      (loop for form = (read in nil :eof)
            until (eq form :eof)
            collect form))))

(defun decode-expected (v)
  (cond ((and (consp v) (eq (car v) :f)) (sqlite-pure::text-numeric-value (second v)))
        ((and (consp v) (eq (car v) :blob))
         (let* ((h (second v)) (b (make-array (floor (length h) 2) :element-type '(unsigned-byte 8))))
           (dotimes (i (length b) b)
             (setf (aref b i) (parse-integer h :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))))
        ((eq v :inf) (sqlite-pure::double-positive-infinity))
        ((eq v :-inf) (sqlite-pure::double-negative-infinity))
        (t v)))

(defun value= (a b)
  (cond ((and (integerp a) (integerp b)) (= a b))
        ((and (floatp a) (floatp b))
         (or (= a b)
             (and (not (zerop b)) (< (abs (/ (- a b) b)) 1d-14))))
        ((and (stringp a) (stringp b)) (string= a b))
        ((and (vectorp a) (vectorp b)) (equalp a b))
        (t (eq a b))))

(defun row= (a b)
  (and (= (length a) (length b)) (every #'value= a b)))

(defun row-sort-key (row) (format nil "~s" row))

(defun ordered-statement-p (sql)
  (search "order by" (string-downcase sql)))

(defun compare-rows (got want ordered)
  (if ordered
      (and (= (length got) (length want)) (every #'row= got want))
      (let ((g (sort (copy-list got) #'string< :key #'row-sort-key))
            (w (sort (copy-list want) #'string< :key #'row-sort-key)))
        (and (= (length g) (length w)) (every #'row= g w)))))

(defvar *message-mismatches* 0)

(defun run-case (case)
  "Return NIL on success, or a description of the first divergence."
  (destructuring-bind (name &rest steps) case
    (declare (ignore name))
    (let ((db (s:open-database ":memory:"))
          (failure nil))
      (unwind-protect
           (dolist (step steps)
             (destructuring-bind (sql kind &rest more) step
               (multiple-value-bind (result err)
                   (handler-case (multiple-value-list (s:query db sql))
                     (s:sqlite-error (e) (values nil e))
                     (error (e) (values nil (list :lisp-error e))))
                 (let ((problem
                         (ecase kind
                           (:ok (when err (format nil "unexpected error: ~a" err)))
                           (:error (if err
                                       (progn
                                         (unless (and (typep err 's:sqlite-error)
                                                      (string= (s:sqlite-error-message err) (first more)))
                                           (incf *message-mismatches*)
                                           (when *verbose*
                                             (format t "    msg: want ~s got ~a~%" (first more) err)))
                                         nil)
                                       (format nil "expected error ~s, got ~s" (first more) (first result))))
                           (:rows
                            (if err
                                (format nil "unexpected error: ~a" err)
                                (let ((want (mapcar (lambda (r) (mapcar #'decode-expected r)) (second more)))
                                      (got (first result))
                                      (cols (second result)))
                                  (cond ((not (compare-rows got want (ordered-statement-p sql)))
                                         (let* ((ordered (ordered-statement-p sql))
                                                (w (if ordered want (sort (copy-list want) #'string< :key #'row-sort-key)))
                                                (g (if ordered got (sort (copy-list got) #'string< :key #'row-sort-key)))
                                                (k (or (loop for a in w for b in g for i from 0
                                                             unless (row= b a) return i)
                                                       (min (length w) (length g)))))
                                           (format nil "rows differ (~d vs ~d rows) at row ~d~%      want ~s~%      got  ~s"
                                                   (length want) (length got) k (nth k w) (nth k g))))
                                        ((not (equal cols (first more)))
                                         (format nil "column names differ: want ~s got ~s"
                                                 (first more) cols)))))))))
                   (when (and problem (not failure))
                     (setf failure (format nil "~a~%    in: ~a" problem sql)))))))
        (s:close-database db))
      failure)))

(defun run-differential (&key (path (asdf:system-relative-pathname "sqlite-pure" "test/expected.sexp"))
                              (verbose nil) only)
  (let ((*verbose* verbose) (*message-mismatches* 0)
        (pass 0) (fail 0) (failures '()))
    (dolist (case (read-expected path))
      (when (or (null only) (search only (first case)))
        (let ((f (handler-case (run-case case)
                   (error (e) (format nil "harness error: ~a" e)))))
          (if f
              (progn (incf fail) (push (cons (first case) f) failures))
              (incf pass)))))
    (dolist (f (reverse failures))
      (format t "FAIL ~a~%    ~a~%" (car f) (cdr f)))
    (format t "~&differential: ~d passed, ~d failed (~d error-message wording differences)~%"
            pass fail *message-mismatches*)
    (zerop fail)))

(defun run () (run-differential))
