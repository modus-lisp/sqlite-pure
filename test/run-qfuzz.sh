#!/bin/sh
# test/run-qfuzz.sh [FIRST-SEED] [SEEDS] [QUERIES] — random queries vs SQLite.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
first=${1:-1}; n=${2:-3}; q=${3:-200}
dir=${TMPDIR:-/tmp}/sqlite-pure-qfuzz
rm -rf "$dir"; mkdir -p "$dir"
seed=$first
while [ $seed -lt $((first + n)) ]; do
  python3 "$here/test/qfuzz.py" $seed $q "$dir/q$seed.test"
  seed=$((seed + 1))
done
python3 "$here/test/gen-expected.py" "$dir/*.test" "$dir/expected.sexp"
exec sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
  --load "$here/test/differential.lisp" \
  --eval "(uiop:quit (if (sqlite-pure.test:run-differential :path \"$dir/expected.sexp\") 0 1))"
