#!/bin/sh
# test/run-tcl.sh [-j N] [-t SECS] [TESTFILE...] — SQLite's own TCL test
# suite (the *.test files and tester.tcl of the 3.40.1 source release,
# unmodified) run against this library through test/tcl/sqlite3.tcl.
# With no files, runs every test/*.test of the release.  Prints one line per
# file: errors, tests, how many testfixture-only commands it reached (a
# test that needs one is not meaningful here), and TIMEOUT / CRASH.
#
# Needs: $SQLITE_SRC (default: the sqlite-src-3400100 release, fetched into
# $TMPDIR) and Tcl 8.6 built statically under $TCL_PREFIX (default: built from
# source into $TMPDIR), from which test/tcl/testfixture.c is compiled.
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
tmp=${TMPDIR:-/tmp}
jobs=1; secs=600
while [ $# -gt 0 ]; do
  case $1 in
    -j) jobs=$2; shift 2 ;;
    -t) secs=$2; shift 2 ;;
    *) break ;;
  esac
done
src=${SQLITE_SRC:-$tmp/sqlite-src-3400100}
if [ ! -f "$src/test/tester.tcl" ]; then
  (cd "$tmp" && curl -sSfLO https://www.sqlite.org/2022/sqlite-src-3400100.zip && unzip -qo sqlite-src-3400100.zip)
fi
tcl=${TCL_PREFIX:-$tmp/sqlite-pure-tcl}
if [ ! -f "$tcl/lib/libtcl8.6.a" ]; then
  (cd "$tmp" && curl -sSfL -o tcl8.6.13-src.tar.gz https://prdownloads.sourceforge.net/tcl/tcl8.6.13-src.tar.gz \
     && tar xzf tcl8.6.13-src.tar.gz && cd tcl8.6.13/unix \
     && ./configure --prefix="$tcl" --disable-shared >/dev/null && make -j8 >/dev/null && make install >/dev/null)
fi
# a tclsh that loads test/tcl/sqlite3.tcl at startup: SQLite's testfixture,
# as far as the tests (and the child processes some of them start) can tell
tclsh="$tcl/bin/testfixture"
if [ ! -x "$tclsh" ] || [ "$here/test/tcl/testfixture.c" -nt "$tclsh" ]; then
  gcc -O2 -o "$tclsh" "$here/test/tcl/testfixture.c" -I"$tcl/include" "$tcl/lib/libtcl8.6.a" -lz -lm -ldl -lpthread
fi
export SQLP_SHIM="$here/test/tcl/sqlite3.tcl"
core=$("$here/test/tcl/build-server.sh")
export SQLP_SERVER="sbcl --core $core --noinform --no-userinit --disable-debugger --dynamic-space-size 2048"
[ $# -eq 0 ] && set -- "$src"/test/*.test
export TCLSH="$tclsh" SECS="$secs" KEEP
printf '%s\n' "$@" | xargs -P "$jobs" -n 1 "$here/test/tcl/runone.sh"
