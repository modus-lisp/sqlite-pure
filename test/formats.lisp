;;;; test/formats.lisp — the Lisp half of test/formats.py.

(in-package #:sqlite-pure.test)

(defun write-file-text (path text)
  (with-open-file (out path :direction :output :if-exists :supersede :external-format :utf-8)
    (write-string text out)))

(defun dump-to-string (db) (with-output-to-string (o) (dump-database db o)))

(defun copy-file* (from to)
  (with-open-file (in from :element-type '(unsigned-byte 8))
    (with-open-file (out to :element-type '(unsigned-byte 8) :direction :output :if-exists :supersede)
      (let ((buf (make-array 65536 :element-type '(unsigned-byte 8))))
        (loop for n = (read-sequence buf in) while (plusp n) do (write-sequence buf out :end n))))))

(defun run-formats-side (dir)
  ;; 1. read every database SQLite made
  (dolist (name '("ps512" "ps1024" "ps65536" "utf16le" "utf16be" "autovac" "freelist" "wal"))
    (let ((path (format nil "~a/~a.db" dir name)))
      (handler-case
          (s:with-database (db path :readonly t)
            (write-file-text (format nil "~a/~a.lisp.txt" dir name) (dump-to-string db)))
        (error (e) (format t "read ~a: ~a~%" name e)))))
  ;; 2. modify copies of them and let SQLite judge the result
  (dolist (name '("ps512" "ps1024" "ps65536" "utf16le" "utf16be" "freelist"))
    (let ((src (format nil "~a/~a.db" dir name))
          (dst (format nil "~a/w-~a.db" dir name)))
      (copy-file* src dst)
      (handler-case
          (s:with-database (db dst)
            (s:with-transaction (db)
              (s:execute db "UPDATE a SET t = t || '?' WHERE id % 4 = 1")
              (s:execute db "DELETE FROM a WHERE id % 5 = 2")
              (s:execute db "INSERT INTO a(t, b, r, i) SELECT t || 'x', b, r * 2, i / 3 FROM a WHERE id % 9 = 0")
              (s:execute db "INSERT OR REPLACE INTO w VALUES ('k3', 'new'), ('zz', randomblob(3000) IS NOT NULL)")
              (s:execute db "CREATE INDEX a_r ON a(r)"))
            (s:execute db "DELETE FROM w WHERE k < 'k2'"))
        (error (e) (format t "write ~a: ~a~%" name e)))))
  ;; 3. auto_vacuum must refuse writes
  (s:with-database (db (format nil "~a/autovac.db" dir))
    (handler-case (progn (s:execute db "DELETE FROM a") (format t "autovac: write was NOT refused~%"))
      (s:sqlite-error (e) (format t "autovac refused: ~a~%" (s:sqlite-error-message e)))))
  ;; 4. a crash in the middle of COMMIT leaves a hot journal SQLite rolls back
  (let ((src (format nil "~a/ps1024.db" dir))
        (dst (format nil "~a/w-crash.db" dir)))
    (copy-file* src dst)
    (s:with-database (db dst)
      (write-file-text (format nil "~a/w-crash.expected.txt" dir) (dump-to-string db))
      (handler-case
          (let ((sqlite-pure::*crash-after-pages* 7))
            (s:execute db "UPDATE a SET t = 'clobbered', b = NULL"))
        (error (e) (format t "crash simulated: ~a~%" e)))))
  ;; 5. ... and one this library rolls back itself
  (let ((src (format nil "~a/ps1024.db" dir))
        (dst (format nil "~a/w-crash-self.db" dir)))
    (copy-file* src dst)
    (let ((before nil))
      (s:with-database (db dst)
        (setf before (dump-to-string db))
        (handler-case
            (let ((sqlite-pure::*crash-after-pages* 5))
              (s:execute db "DELETE FROM a WHERE id > 10"))
          (error () nil)))
      (format t "journal left behind: ~a~%" (and (probe-file (format nil "~a-journal" dst)) t))
      (s:with-database (db dst)
        (format t "self recovery: ~:[FAIL~;ok~]~%" (string= before (dump-to-string db))))
      (write-file-text (format nil "~a/w-crash-self.expected.txt" dir) before))))
