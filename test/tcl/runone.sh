#!/bin/sh
# test/tcl/runone.sh FILE — one SQLite *.test file in a fresh directory;
# prints its summary line (see test/run-tcl.sh).  Uses $SQLP_SERVER,
# $TCLSH, $SECS, and $KEEP (a directory to keep each file's output in).
f=$1
here=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
d=$(mktemp -d "${TMPDIR:-/tmp}/sqlp-tcl.XXXXXX")
out="$d/out.txt"
(cd "$d" && timeout "${SECS:-600}" "$TCLSH" "$here/test/tcl/run.tcl" "$f" > "$out" 2>&1)
rc=$?
summary=$(grep -a "errors out of" "$out" | tail -1)
errors=$(echo "$summary" | awk '{print $1}')
tests=$(echo "$summary" | awk '{print $5}')
stubs=$(grep -a "^STUBS:" "$out" | wc -w)
[ "$stubs" -gt 0 ] && stubs=$((stubs - 1))
status=ok
if [ $rc -eq 124 ]; then status=TIMEOUT; elif [ -z "$summary" ]; then status=CRASH; fi
printf '%-32s %-7s errors %5s  tests %5s  stubs %3s  %s\n' "$(basename "$f")" "$status" "${errors:--}" "${tests:--}" "$stubs" \
  "$(grep -a '^ERROR:' "$out" | head -1 | cut -c1-90)"
if [ -n "$KEEP" ]; then mkdir -p "$KEEP"; cp "$out" "$KEEP/$(basename "$f").out"; fi
rm -rf -- "${d:?}"
