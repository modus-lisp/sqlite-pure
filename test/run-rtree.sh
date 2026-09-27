#!/bin/sh
# test/run-rtree.sh — r-trees modified alternately by SQLite and by us.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
dir=${TMPDIR:-/tmp}/sqlite-pure-rtree
sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/rtree.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-rtree-interop \"$dir\") 0 1))" 2>&1 | grep -av '^;'
rm -rf "$dir"
