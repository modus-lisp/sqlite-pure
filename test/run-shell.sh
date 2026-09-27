#!/bin/sh
# test/run-shell.sh — bin/sqlp against SQLite's own sqlite3 shell: every
# case in test/shell/ must give the same stdout, stderr and exit status.
# SQLITE3 names the reference shell (default: built by build-oracle.sh).
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
ref=${SQLITE3:-$("$here/test/build-oracle.sh")/sqlite3}
"$here/bin/build-sqlp.sh" >/dev/null 2>&1
python3 "$here/test/shell-diff.py" "$ref" "$here/bin/sqlp" "$@"
