;;;; extend-fts.lisp — Lisp extensions to full-text search: tokenizers
;;;; (for FTS3, FTS4 and FTS5 tables) and FTS5 auxiliary functions, the
;;;; counterparts of SQLite's fts3_tokenizer() / fts5_api C interfaces.

(in-package #:sqlite-pure)

;;; ------------------------------------------------------------------
;;; Tokenizers

(defun define-tokenizer (db name function)
  "Make FUNCTION available as the tokenizer NAME to FTS3/FTS4 (tokenize=NAME
arg ...) and FTS5 (tokenize='NAME arg ...') tables on DB's connection.
FUNCTION is called with the text (a string) and the list of arguments
(strings) and returns a sequence of tokens, each (token start end) or
(token start end position): the token text, its character offsets in the
text (END exclusive), and for FTS3/FTS4 optionally its position (by
default tokens are numbered 0, 1, 2 ...; FTS5 always numbers them so).
Several tokens may share a position.  FTS5 looks the name up without
regard to case, FTS3/FTS4 with it, as SQLite does."
  (let ((c (conn db)))
    (setf (gethash name (db-user-tokenizers c)) function)
    ;; tables loaded before the tokenizer existed load again
    (dolist (d (conn-dbs c)) (setf (db-schema d) nil))
    (clrhash (db-stmt-cache c))
    name))

(defun user-tokenizer-function (name case-insensitive)
  (when (and (boundp '*db*) *db* name)
    (let ((h (db-user-tokenizers (conn *db*))))
      (or (gethash name h)
          (and case-insensitive
               (loop for k being the hash-keys of h using (hash-value v)
                     when (string-equal k name) return v))))))

(defun user-tokenize (name case-insensitive args text)
  "Run the user tokenizer NAME: a vector of (token byte-start byte-end position)."
  (let ((fn (or (user-tokenizer-function name case-insensitive)
                (sql-error "no such tokenizer: ~a" name)))
        (offsets (let ((v (make-array (1+ (length text)))) (b 0))
                   ;; byte offset of each character position
                   (dotimes (i (length text) (progn (setf (aref v (length text)) b) v))
                     (setf (aref v i) b)
                     (incf b (utf8-len (char-code (char text i))))))))
    (let ((out (make-array 16 :adjustable t :fill-pointer 0)) (i 0))
      (map nil (lambda (tk)
                 (destructuring-bind (token start end &optional pos) tk
                   (unless (and (stringp token) (integerp start) (integerp end)
                                (<= 0 start end (length text)))
                     (sql-error "tokenizer ~a returned a bad token: ~s" name tk))
                   (vector-push-extend (list token (aref offsets start) (aref offsets end) (or pos i)) out)
                   (incf i)))
           (funcall fn text args))
      out)))

;;; ------------------------------------------------------------------
;;; FTS5 auxiliary functions

(defstruct (fts5-api (:constructor %make-fts5-api (info)))
  "What an FTS5 auxiliary function sees of the current row and query."
  info)

(defun define-fts5-function (db name function)
  "Define NAME as an FTS5 auxiliary function: in SELECT NAME(t, arg ...)
FROM t WHERE t MATCH ..., FUNCTION is called with an FTS5-API object for
the current row and the remaining arguments, and returns a value.  The
object is read with FTS5-API-ROWID, -COLUMN-COUNT, -COLUMN-TEXT,
-COLUMN-SIZE, -ROW-COUNT, -COLUMN-TOTAL-SIZE, -PHRASE-COUNT,
-PHRASE-SIZE, -INSTANCES and -TOKENIZE."
  (define-function db name
    (lambda (cursor &rest args)
      (apply function (%make-fts5-api (fts5-cursor-info cursor name)) args))))

(defun api-fts (api) (frow-fts (fts5-api-info api)))

(defun fts5-api-rowid (api) (frow-rowid (fts5-api-info api)))

(defun fts5-api-column-count (api) (length (fts-columns (api-fts api))))

(defun fts5-api-column-text (api column)
  "The text of COLUMN (0-based) in the current row, or :NULL."
  (let ((v (nth column (frow-values (fts5-api-info api)))))
    (if (or (null v) (eq v :null)) :null (value-to-text v))))

(defun fts5-api-column-size (api column)
  "Tokens in COLUMN of the current row."
  (aref (fts5-docsize (api-fts api) (fts5-api-rowid api)) column))

(defun fts5-api-row-count (api)
  (car (fts-read-totals (api-fts api))))

(defun fts5-api-column-total-size (api column)
  "Tokens in COLUMN over the whole table."
  (aref (cdr (fts-read-totals (api-fts api))) column))

(defun fts5-api-phrase-count (api)
  (let ((r (frow-result (fts5-api-info api)))) (if r (length (fres-phrases r)) 0)))

(defun fts5-api-phrase-size (api phrase)
  "Tokens in PHRASE (0-based) of the query."
  (fts5-phrase-size (fts5-api-info api) phrase))

(defun fts5-api-instances (api)
  "Phrase matches in the current row: a list of (phrase column offset), in
the order SQLite's xInst reports them."
  (copy-list (fts5-instances (fts5-api-info api))))

(defun fts5-api-tokenize (api text)
  "TEXT tokenized with the table's tokenizer: a list of (token start end),
character offsets."
  (let* ((b (utf8-encode text))
         (char-of (let ((v (make-array (1+ (length b)) :initial-element 0)) (ci 0) (i 0))
                    (loop while (< i (length b))
                          do (setf (aref v i) ci)
                             (incf i (utf8-len (char-code (char text ci))))
                             (incf ci))
                    (setf (aref v (length b)) ci)
                    v)))
    (map 'list (lambda (tk) (list (first tk) (aref char-of (second tk)) (aref char-of (third tk))))
         (fts5-tokenize (fts-tokenizer (api-fts api)) text))))
