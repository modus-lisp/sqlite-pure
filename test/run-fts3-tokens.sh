#!/bin/sh
# test/run-fts3-tokens.sh [SEED] [N] — our FTS3/4 tokenizers against SQLite's fts3tokenize.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
f=${TMPDIR:-/tmp}/sqlite-pure-fts3-tokens.sexp
python3 "$here/test/fts3-tokens.py" ${1:-1} ${2:-400} "$f"
sbcl --noinform --no-userinit --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" --load "$here/test/fts3-tokens.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-fts3-token-oracle \"$f\") 0 1))" 2>&1 | grep -av '^;'
rm -f "$f"
