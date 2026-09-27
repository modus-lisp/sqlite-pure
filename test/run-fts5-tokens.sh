#!/bin/sh
# test/run-fts5-tokens.sh [SEED] [N] — our FTS5 tokenizers against SQLite's, text by text.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
f=${TMPDIR:-/tmp}/sqlite-pure-tokens.sexp
python3 "$here/test/fts5-tokens.py" ${1:-1} ${2:-400} "$f"
sbcl --noinform --no-userinit --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/fts5-tokens.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-token-oracle \"$f\") 0 1))" 2>&1 | grep -av '^;'
rm -f "$f"
