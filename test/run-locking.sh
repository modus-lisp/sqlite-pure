#!/bin/sh
# test/run-locking.sh — sharing a database file with SQLite processes.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/locking.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-locking \"${TMPDIR:-/tmp}/sqlite-pure-locking\") 0 1))" 2>&1 | grep -av '^;'
