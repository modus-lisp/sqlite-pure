;;;; test/geopoly.lisp — our half of test/geopoly-check.py: run each line of
;;;; a file of SQL statements against a database and write one line per
;;;; statement, the first result row with every value in an exact canonical
;;;; form (floats as their IEEE bits), so the two sides compare bit for bit.

(in-package #:sqlite-pure.test)

(defun geo-canon (v)
  (cond ((eq v :null) "n")
        ((integerp v) (format nil "i:~d" v))
        ((floatp v) (format nil "f:~16,'0x" (sqlite-pure::bits-from-double v)))
        ((stringp v) (format nil "s:~{~2,'0x~}" (coerce (sqlite-pure::utf8-encode v) 'list)))
        (t (format nil "b:~{~2,'0x~}" (coerce v 'list)))))

(defun geo-run-file (db-path in-path out-path)
  (s:with-database (db db-path)
    (with-open-file (in in-path)
      (with-open-file (out out-path :direction :output :if-exists :supersede)
        (loop for l = (read-line in nil) while l
              do (format out "~{~a~^	~}~%"
                         (handler-case (mapcar #'geo-canon (first (s:query db l)))
                           (s:sqlite-error (e) (list (format nil "ERR ~a" (s:sqlite-error-message e)))))))))))
