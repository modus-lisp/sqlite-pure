#!/bin/sh
# test/run-formats.sh — foreign file formats, write-back, and crash recovery.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
dir=${TMPDIR:-/tmp}/sqlite-pure-formats
python3 "$here/test/formats.py" make "$dir"
sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/fuzz.lisp" --load "$here/test/formats.lisp" \
  --eval "(sqlite-pure.test::run-formats-side \"$dir\")" 2>&1 | grep -v '^;'
python3 "$here/test/formats.py" check "$dir"
