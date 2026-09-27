;;;; package.lisp — the one package.  Internals are unexported; the API is the
;;;; handful of entry points below.

(defpackage #:sqlite-pure
  (:use #:cl)
  (:nicknames #:sqlp)
  (:export
   ;; connections
   #:open-database #:close-database #:with-database #:database-path
   ;; statements
   #:execute #:execute-script #:query #:query-row #:query-value #:do-query
   #:last-insert-rowid #:changes
   ;; extending SQL
   #:define-function #:define-aggregate #:define-collation #:undefine-function
   #:define-tokenizer #:define-fts5-function
   #:fts5-api-rowid #:fts5-api-column-count #:fts5-api-column-text #:fts5-api-column-size
   #:fts5-api-row-count #:fts5-api-column-total-size #:fts5-api-phrase-count
   #:fts5-api-phrase-size #:fts5-api-instances #:fts5-api-tokenize
   ;; transactions
   #:with-transaction #:begin-transaction #:commit #:rollback #:in-transaction-p
   ;; values
   #:+null+ #:null-value-p
   ;; errors
   #:sqlite-error #:sqlite-error-message #:sqlite-error-code
   #:sqlite-constraint-error #:sqlite-parse-error #:sqlite-corrupt-error))
