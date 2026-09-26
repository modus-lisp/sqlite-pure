#!/bin/sh
# test/run-tests.sh — the differential SQL suite (committed expectations).
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
exec sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/api.lisp" \
  --eval '(uiop:quit (if (and (sqlite-pure.test:run) (sqlite-pure.test::run-api)) 0 1))'
