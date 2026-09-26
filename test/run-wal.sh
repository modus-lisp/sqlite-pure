#!/bin/sh
# test/run-wal.sh — writing WAL databases alongside SQLite processes.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
dir=${TMPDIR:-/tmp}/sqlite-pure-wal
sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/wal.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-wal \"$dir\") 0 1))" 2>&1 | grep -av '^;'
rm -rf "$dir"
