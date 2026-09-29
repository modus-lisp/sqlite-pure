#!/bin/sh
# test/run-threads.sh — connections and threads of one process on one file.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
lib=$("$here/test/build-oracle.sh")
dir=$(mktemp -d "${TMPDIR:-/tmp}/sqlite-pure-threads.XXXXXX")
status=0
sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/threads.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-threads \"$dir\" \"$lib/sqlite3\") 0 1))" 2>&1 | grep -av '^;' || status=1
rm -rf -- "${dir:?}"
exit $status
