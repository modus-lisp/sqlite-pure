#!/bin/sh
# test/run-slt.sh [-j N] FILE-OR-DIR... — run sqllogictest files (see
# test/slt.lisp).  SLT_DIR is the corpus (default: fetched from the
# github.com/gregrahn/sqllogictest mirror into $TMPDIR).  With no arguments,
# runs the whole corpus.  -j N shards the files over N processes.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
jobs=1
if [ "$1" = "-j" ]; then jobs=$2; shift 2; fi
if [ -z "$SLT_DIR" ]; then
  SLT_DIR=${TMPDIR:-/tmp}/sqllogictest-master
  if [ ! -d "$SLT_DIR/test" ]; then
    (cd "$(dirname "$SLT_DIR")" && curl -sSfL https://github.com/gregrahn/sqllogictest/archive/refs/heads/master.tar.gz | tar xz)
  fi
fi
[ $# -eq 0 ] && set -- "$SLT_DIR/test"
list=$(mktemp)
for a in "$@"; do
  if [ -d "$a" ]; then find "$a" -name '*.test' | sort; else echo "$a"; fi
done > "$list"
run() {
  sbcl --dynamic-space-size 4096 --noinform --no-userinit --non-interactive \
    --eval '(require :sb-md5)' --eval '(require :sb-posix)' --eval '(require :asdf)' \
    --eval "(push #p\"$here/\" asdf:*central-registry*)" \
    --eval '(let ((*error-output* (make-broadcast-stream))) (asdf:load-system "sqlite-pure/shell"))' \
    --eval "(let ((*error-output* (make-broadcast-stream))) (load (compile-file \"$here/test/slt.lisp\" :output-file (format nil \"/tmp/slt-~a.fasl\" (sb-posix:getpid)))))" \
    --eval "(setf sqlite-pure.slt::*known* (sqlite-pure.slt::load-known \"$here/test/slt-known.txt\"))" \
    --eval "(let ((s (sqlite-pure.slt:run-files (with-open-file (i \"$1\") (loop for l = (read-line i nil) while l collect l))))) (format t \"TOTAL ok ~d failed ~d skipped ~d known ~d~%\" (sqlite-pure.slt::stats-ok s) (sqlite-pure.slt::stats-failed s) (sqlite-pure.slt::stats-skipped s) (sqlite-pure.slt::stats-known s)))" 2>&1 | grep -av '^;'
}
if [ "$jobs" -le 1 ]; then
  run "$list"
else
  split -n r/"$jobs" "$list" "$list.part."
  for p in "$list".part.*; do run "$p" > "$p.out" & done
  wait
  cat "$list".part.*.out | grep -v '^TOTAL'
  cat "$list".part.*.out | awk '/^TOTAL/ {ok+=$3; f+=$5; s+=$7; k+=$9} END {printf "TOTAL ok %d failed %d skipped %d known %d\n", ok, f, s, k}'
  rm -f "$list".part.*
fi
rm -f "$list"
