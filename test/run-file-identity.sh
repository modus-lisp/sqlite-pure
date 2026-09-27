#!/bin/sh
# test/run-file-identity.sh [FIRST N] — the database file, byte for byte,
# against SQLite after every statement of random workloads.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
work=${TMPDIR:-/tmp}/sqlite-pure-file-identity
python3 "$here/test/file-identity.py" "${1:-1}" "${2:-20}" "$work"
rm -rf "$work"
