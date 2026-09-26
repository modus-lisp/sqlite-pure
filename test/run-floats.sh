#!/bin/sh
# test/run-floats.sh [SEED] — decimal<->double conversions, bit for bit.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
dir=${TMPDIR:-/tmp}/sqlite-pure-floats
python3 "$here/test/floats-gen.py" "${1:-1}" "$dir"
sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/floats.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-floats \"$dir\") 0 1))" 2>&1 | grep -av '^;'
