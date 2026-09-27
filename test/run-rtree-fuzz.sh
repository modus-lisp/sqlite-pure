#!/bin/sh
# test/run-rtree-fuzz.sh [FIRST N] — r-tree shadow tables byte for byte
# against SQLite after every statement of random workloads.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
work=${TMPDIR:-/tmp}/sqlite-pure-rtree-fuzz
python3 "$here/test/rtree-fuzz.py" "${1:-1}" "${2:-20}" "$work"
rm -rf "$work"
