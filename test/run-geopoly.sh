#!/bin/sh
# test/run-geopoly.sh — geopoly bit for bit against SQLite 3.40.1 built with
# GEOPOLY (test/build-oracle.sh), and the committed geopoly expectations
# (test/expected-ext.sexp) regenerated from it and checked.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
work=${TMPDIR:-/tmp}/sqlite-pure-geopoly
lib=$("$here/test/build-oracle.sh")
LD_LIBRARY_PATH=$lib python3 "$here/test/gen-expected.py" "$here/test/cases-ext/*.test" "$work.sexp"
cmp -s "$work.sexp" "$here/test/expected-ext.sexp" || echo "note: test/expected-ext.sexp differs from a fresh run of the oracle"
LD_LIBRARY_PATH=$lib python3 "$here/test/geopoly-check.py" "$work"
rm -rf "$work" "$work.sexp"
