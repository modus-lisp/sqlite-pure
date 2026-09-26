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
   ;; transactions
   #:with-transaction #:begin-transaction #:commit #:rollback #:in-transaction-p
   ;; values
   #:+null+ #:null-value-p
   ;; errors
   #:sqlite-error #:sqlite-error-message #:sqlite-error-code
   #:sqlite-constraint-error #:sqlite-parse-error #:sqlite-corrupt-error))
