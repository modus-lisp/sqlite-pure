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
     (:file "wal")
     (:file "record")
     (:file "btree")
     (:file "autovacuum")
     (:file "btree-edit")
     (:file "values")
     (:file "lexer")
     (:file "parser")
     (:file "schema")
     (:file "eqp")
     (:file "expr")
     (:file "select")
     (:file "where")
     (:file "where-or")
     (:file "flatten")
     (:file "window")
     (:file "functions")
     (:file "printf")
     (:file "math")
     (:file "datetime")
     (:file "json")
     (:file "triggers")
     (:file "fkeys")
     (:file "dml")
     (:file "ddl")
     (:file "rtree")
     (:file "fts3-unicode-data")
     (:file "fts3-token")
     (:file "fts5-unicode-data")
     (:file "fts5-token")
     (:file "fts5-index")
     (:file "fts5-expr")
     (:file "fts5")
     (:file "fts3-index")
     (:file "fts3-expr")
     (:file "fts3-eval")
     (:file "fts3-snippet")
     (:file "fts3")
     (:file "dbstat")
     (:file "geopoly")
     (:file "extend-fts")
     (:file "integrity")
     (:file "api")
     (:file "vacuum"))))
  :in-order-to ((test-op (test-op "sqlite-pure/test"))))

(defsystem "sqlite-pure/test"
  :depends-on ("sqlite-pure")
  :components ((:module "test" :components ((:file "differential"))))
  :perform (test-op (o c) (uiop:symbol-call :sqlite-pure.test :run)))

(defsystem "sqlite-pure/cl-sqlite"
  :description "cl-sqlite's API (the SQLITE package) over sqlite-pure: a drop-in
                replacement for the \"sqlite\" system, with no libsqlite3"
  :depends-on ("sqlite-pure" "iterate")
  :components ((:module "compat" :components ((:file "cl-sqlite")))))

(defsystem "sqlite-pure/shell"
  :description "sqlp: an sqlite3-compatible command-line shell for sqlite-pure"
  :depends-on ("sqlite-pure" "sb-posix")
  :components ((:module "shell" :components ((:file "shell")))))
