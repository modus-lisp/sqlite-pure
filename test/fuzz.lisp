;;;; test/fuzz.lisp — the sqlite-pure half of test/fuzz.py (see there).

(in-package #:sqlite-pure.test)

(defun canon (v)
  (cond ((eq v :null) "N")
        ((integerp v) (format nil "I~d" v))
        ((floatp v) (format nil "R~(~16,'0x~)" (sqlite-pure::bits-from-double v)))
        ((stringp v) (format nil "T~(~{~2,'0x~}~)" (coerce (sqlite-pure::utf8-encode v) 'list)))
        (t (format nil "B~(~{~2,'0x~}~)" (coerce v 'list)))))

(defun dump-database (db out)
  (dolist (row (s:query db "select name, sql from sqlite_schema where type='table' order by name"))
    (destructuring-bind (name sql) row
      (let* ((wr (search "WITHOUT ROWID" (string-upcase sql)))
             (cols (mapcar #'second (s:query db (format nil "pragma table_info(\"~a\")" name))))
             (sel (format nil "~:[rowid, ~;~]~{\"~a\"~^, ~}" wr cols)))
        (format out "table ~a~%" name)
        (dolist (r (s:query db (format nil "select ~a from \"~a\" order by ~a" sel name
                                       (if wr "1, 2" "rowid"))))
          (format out "~{~a~^ ~}~%" (mapcar #'canon r)))))))

(defun run-fuzz-side (dir)
  (let ((sub (format nil "~a/sub.db" dir))
        (errors 0) (count 0))
    (when (probe-file sub) (delete-file sub))
    (s:with-database (db sub)
      (with-open-file (in (format nil "~a/work.sql" dir) :external-format :utf-8)
        (loop for line = (read-line in nil)
              while line
              do (incf count)
                 (handler-case (s:execute db line)
                   (s:sqlite-error () (incf errors))))))
    (s:with-database (db (format nil "~a/ref.db" dir) :readonly t)
      (with-open-file (out (format nil "~a/sub-read-ref.txt" dir) :direction :output
                                                                   :if-exists :supersede
                                                                   :external-format :utf-8)
        (dump-database db out)))
    (format t "lisp: ~d statements, ~d rejected~%" count errors)))
