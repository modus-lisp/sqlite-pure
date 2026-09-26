#!/bin/sh
# test/run-fuzz.sh [FIRST-SEED] [COUNT] — file-format fuzz against real SQLite.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
first=${1:-1}; count=${2:-10}
work=${TMPDIR:-/tmp}/sqlite-pure-fuzz
fails=0
seed=$first
while [ $seed -lt $((first + count)) ]; do
  dir=$work/$seed
  python3 "$here/test/fuzz.py" gen $seed "$dir"
  sbcl --noinform --non-interactive \
    --eval '(require :asdf)' \
    --eval "(push #p\"$here/\" asdf:*central-registry*)" \
    --eval '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))' \
    --load "$here/test/differential.lisp" --load "$here/test/fuzz.lisp" \
    --eval "(sqlite-pure.test::run-fuzz-side \"$dir\")" 2>&1 | grep -v '^;'
  python3 "$here/test/fuzz.py" check "$dir" || fails=$((fails + 1))
  seed=$((seed + 1))
done
echo "fuzz: $count seeds, $fails failed"
[ $fails -eq 0 ]
