#!/bin/sh
# test/run-cl-sqlite-compat.sh — sqlite-pure/cl-sqlite as a drop-in for
# cl-sqlite: test/cl-sqlite-compat.lisp run with the real cl-sqlite (from
# Quicklisp, over SQLite 3.40.1 built by test/build-oracle.sh) and with this
# library must print the same transcript; then cl-sqlite's own test suite
# (fetched with it) runs against this library.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
lib=$("$here/test/build-oracle.sh")
work=$(mktemp -d "${TMPDIR:-/tmp}/cl-sqlite-compat.XXXXXX")
run() {  # run SYSTEM OUT: load SYSTEM, run the cases, transcript to OUT
  LD_LIBRARY_PATH=$lib sbcl --noinform --no-userinit --non-interactive \
    --eval '(require :asdf)' --eval '(load (merge-pathnames "quicklisp/setup.lisp" (user-homedir-pathname)))' \
    --eval "(push #p\"$here/\" asdf:*central-registry*)" \
    --eval "(let ((*error-output* (make-broadcast-stream))) (handler-bind ((warning #'muffle-warning)) (ql:quickload \"$1\" :silent t)))" \
    --eval "(load \"$here/test/cl-sqlite-compat.lisp\")" \
    --eval "(setf cl-sqlite-compat::*db-file* \"$work/db.sqlite\")" \
    --eval '(cl-sqlite-compat::run)' > "$2" 2>&1
}
run sqlite "$work/cl-sqlite.out"
run sqlite-pure/cl-sqlite "$work/sqlite-pure.out"
n=$(grep -c ': ' "$work/cl-sqlite.out" || true)
if diff "$work/cl-sqlite.out" "$work/sqlite-pure.out"; then
  echo "cl-sqlite compat: $n cases, 0 differ"
else
  echo "cl-sqlite compat: $n cases, transcripts differ (kept in $work)"; status=1; keep=1
fi
# cl-sqlite's own tests, against this library
src=$(sbcl --noinform --no-userinit --non-interactive --eval '(load (merge-pathnames "quicklisp/setup.lisp" (user-homedir-pathname)))' \
  --eval '(let ((*standard-output* (make-broadcast-stream))) (ql:quickload "sqlite" :silent t))' \
  --eval '(princ (namestring (asdf:system-source-directory "sqlite")))' 2>/dev/null | tail -1)
sbcl --noinform --no-userinit --non-interactive \
  --eval '(require :asdf)' --eval '(load (merge-pathnames "quicklisp/setup.lisp" (user-homedir-pathname)))' \
  --eval '(let ((*error-output* (make-broadcast-stream))) (ql:quickload (list "fiveam" "bordeaux-threads") :silent t))' \
  --eval "(push #p\"$here/\" asdf:*central-registry*)" \
  --eval "(let ((*error-output* (make-broadcast-stream))) (handler-bind ((warning #'muffle-warning)) (asdf:load-system \"sqlite-pure/cl-sqlite\")))" \
  --eval "(load \"${src}sqlite-tests.lisp\")" \
  --eval '(let ((r (fiveam:run (quote sqlite-tests::sqlite-suite)))) (fiveam:explain! r) (uiop:quit (if (fiveam:results-status r) 0 1)))' \
  > "$work/suite.out" 2>&1 || { status=1; keep=1; }
grep -E "Did|Pass:|Fail:" "$work/suite.out"
grep -A3 "Failure Details" "$work/suite.out" | grep -v "Failure Details" || true
[ -n "$keep" ] || rm -rf -- "${work:?}"
exit ${status:-0}
