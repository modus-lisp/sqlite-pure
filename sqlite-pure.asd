;;;; sqlite-pure.asd

(defsystem "sqlite-pure"
  :description "A from-scratch SQLite in pure Common Lisp — no FFI, no libsqlite3.
                Reads and writes the SQLite 3 file format (b-trees, overflow
                pages, freelist, rollback journal) and runs SQL on it."
  :version "0.0.1"
  :author "ynniv"
  :license "MIT"
  :depends-on ((:feature :sbcl (:require :sb-posix)))
  :serial t
  :components
  ((:module "src"
    :serial t
    :components
    ((:file "package")
     (:file "util")
     (:file "pager")
     (:file "locking")
     (:file "record")
     (:file "btree")
     (:file "values")
     (:file "lexer")
     (:file "parser")
     (:file "schema")
     (:file "expr")
     (:file "select")
     (:file "window")
     (:file "functions")
     (:file "printf")
     (:file "math")
     (:file "datetime")
     (:file "json")
     (:file "triggers")
     (:file "dml")
     (:file "ddl")
     (:file "integrity")
     (:file "api"))))
  :in-order-to ((test-op (test-op "sqlite-pure/test"))))
