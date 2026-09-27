;;;; test/file-identity.lisp — our half of test/file-identity.py: run each
;;;; line of a file of SQL statements against a database file and write, per
;;;; statement, an error marker and the MD5 of the whole file.  SBCL only.

(in-package #:sqlite-pure.test)

(require :sb-md5)

(defun file-step-hashes (sql-path db-path out-path)
  (when (probe-file db-path) (delete-file db-path))
  (s:with-database (db db-path)
    (with-open-file (in sql-path)
      (with-open-file (out out-path :direction :output :if-exists :supersede)
        (loop for line = (read-line in nil) while line
              unless (zerop (length (string-trim " " line)))
                do (let ((err (handler-case (progn (s:execute db line) "")
                                (s:sqlite-error () "ERR"))))
                     (format out "~a~(~{~2,'0x~}~)~%" err
                             (coerce (sb-md5:md5sum-file db-path) 'list))))))))
