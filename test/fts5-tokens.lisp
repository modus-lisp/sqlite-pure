;;;; test/fts5-tokens.lisp — our FTS5 tokenizers against SQLite's.
(in-package #:sqlite-pure.test)

(defun run-token-oracle (path)
  (with-open-file (s path :external-format :utf-8)
    (let ((texts (read s)) (ok t))
      (loop for entry = (read s nil)
            while entry
            do (destructuring-bind (cfg &rest want) entry
                 (let ((tok (sqlite-pure::make-fts5-tokenizer-from (sqlite-pure::fts5-split-words cfg)))
                       (bad 0))
                   (loop for text in texts
                         for w in want
                         do (let ((got (map 'list #'first (sqlite-pure::fts5-tokenize tok text))))
                              (unless (equal got w)
                                (when (< bad 4)
                                  (format t "  ~a: ~s~%    want ~s~%    got  ~s~%" cfg text w got))
                                (incf bad))))
                   (format t "~:[FAIL~;ok  ~] ~a (~d texts~@[, ~d differ~])~%"
                           (zerop bad) cfg (length texts) (and (plusp bad) bad))
                   (unless (zerop bad) (setf ok nil)))))
      ok)))
