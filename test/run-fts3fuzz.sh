#!/bin/sh
# test/run-fts3fuzz.sh [FIRST-SEED] [SEEDS] [QUERIES] — random FTS3/4 queries vs SQLite.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
first=${1:-1}; n=${2:-3}; q=${3:-100}
dir=${TMPDIR:-/tmp}/sqlite-pure-fts3fuzz
rm -rf "$dir"; mkdir -p "$dir"
seed=$first
while [ $seed -lt $((first + n)) ]; do
  python3 "$here/test/fts3fuzz.py" $seed $q "$dir/f$seed.test"
  seed=$((seed + 1))
done
python3 "$here/test/gen-expected.py" "$dir/*.test" "$dir/expected.sexp"
sbcl --noinform --no-userinit --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test::run-differential :path \"$dir/expected.sexp\" :verbose (uiop:getenv \"VERBOSE\")) 0 1))" 2>&1 | grep -av '^;'
rm -rf "$dir"
