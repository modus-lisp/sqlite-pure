;;;; test/floats.lisp — replay test/floats-gen.py's cases (see there).

(in-package #:sqlite-pure.test)

(defun hex64 (x) (format nil "~(~16,'0x~)" (sqlite-pure::bits-from-double x)))

(defun run-floats (dir)
  (let ((db (s:open-database ":memory:")) (bad 0) (n 0))
    (with-open-file (in (format nil "~a/atof.txt" dir))
      (loop for line = (read-line in nil) while line
            do (let* ((sp (position #\Space line))
                      (got (hex64 (s:query-value db (format nil "select ~a" (subseq line 0 sp))))))
                 (incf n)
                 (unless (string= got (subseq line (1+ sp)))
                   (incf bad)
                   (when (< bad 5) (format t "atof ~a: got ~a~%" line got))))))
    (with-open-file (in (format nil "~a/format.txt" dir))
      (loop for line = (read-line in nil) while line
            do (let* ((t1 (position #\Tab line)) (t2 (position #\Tab line :start (1+ t1)))
                      (x (sqlite-pure::double-from-bits (parse-integer line :end t1 :radix 16)))
                      (v (s:query-value db (format nil "select ~a" (subseq line (1+ t1) t2)) x))
                      (got (if (floatp v) (format nil "R~a" (hex64 v)) (format nil "'~a'" v))))
                 (incf n)
                 (unless (string= got (subseq line (1+ t2)))
                   (incf bad)
                   (when (< bad 10) (format t "format ~a: got ~a~%" line got))))))
    (format t "floats: ~d of ~d differ~%" bad n)
    (zerop bad)))
