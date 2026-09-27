#!/bin/sh
# test/run-fts3-interop.sh — FTS3/4 indexes built and modified alternately by SQLite and by us.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
dir=${TMPDIR:-/tmp}/sqlite-pure-fts3
sbcl --noinform --no-userinit --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/fts5-interop.lisp" --load "$here/test/fts3-interop.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-fts3-interop \"$dir\") 0 1))" 2>&1 | grep -av '^;'
rm -rf "$dir"
