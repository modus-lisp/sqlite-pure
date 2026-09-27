;;;; test/fts3-tokens.lisp — our FTS3/4 tokenizers against SQLite's fts3tokenize.
(in-package #:sqlite-pure.test)

(defun bstring-hex (s)
  (format nil "~{~2,'0X~}" (map 'list #'char-code s)))

(defun run-fts3-token-oracle (path)
  (with-open-file (s path :external-format :utf-8)
    (let ((texts (read s)) (ok t))
      (loop for entry = (read s nil)
            while entry
            do (destructuring-bind (cfg &rest want) entry
                 (let ((tok (sqlite-pure::make-fts3-tokenizer-from cfg))
                       (bad 0))
                   (loop for text in texts
                         for w in want
                         do (let ((got (map 'list (lambda (tk) (list (bstring-hex (first tk)) (second tk) (third tk) (fourth tk)))
                                            (sqlite-pure::fts3-tokenize tok (sqlite-pure::utf8-encode text)))))
                              (unless (equal got w)
                                (when (< bad 4)
                                  (format t "  ~a: ~s~%    want ~s~%    got  ~s~%" cfg text w got))
                                (incf bad))))
                   (format t "~:[FAIL~;ok  ~] ~a (~d texts~@[, ~d differ~])~%"
                           (zerop bad) cfg (length texts) (and (plusp bad) bad))
                   (unless (zerop bad) (setf ok nil)))))
      ok)))
