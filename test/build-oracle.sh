#!/bin/sh
# test/build-oracle.sh [DIR] — build SQLite 3.40.1 as libsqlite3.so.0 with
# the extensions the system library may lack (GEOPOLY, RTREE, FTS3/4/5,
# DBSTAT, math functions), for Python's sqlite3 to load through
# LD_LIBRARY_PATH.  Uses $SQLITE_AMALGAMATION (a directory holding sqlite3.c)
# if set, else downloads the 3.40.1 amalgamation.  Prints DIR.
set -e
dir=${1:-${TMPDIR:-/tmp}/sqlite-pure-oracle}
mkdir -p "$dir"
if [ ! -f "$dir/libsqlite3.so.0" ]; then
  src=$SQLITE_AMALGAMATION
  if [ -z "$src" ]; then
    src="$dir/sqlite-amalgamation-3400100"
    if [ ! -f "$src/sqlite3.c" ]; then
      (cd "$dir" && curl -sSfLO https://www.sqlite.org/2022/sqlite-amalgamation-3400100.zip \
                 && unzip -qo sqlite-amalgamation-3400100.zip)
    fi
  fi
  gcc -O2 -fPIC -shared -o "$dir/libsqlite3.so.0" "$src/sqlite3.c" \
      -DSQLITE_ENABLE_GEOPOLY -DSQLITE_ENABLE_RTREE -DSQLITE_ENABLE_FTS3 \
      -DSQLITE_ENABLE_FTS3_PARENTHESIS -DSQLITE_ENABLE_FTS4 -DSQLITE_ENABLE_FTS5 \
      -DSQLITE_ENABLE_DBSTAT_VTAB -DSQLITE_ENABLE_MATH_FUNCTIONS \
      -DSQLITE_ENABLE_COLUMN_METADATA -DSQLITE_ENABLE_LOAD_EXTENSION \
      -DSQLITE_THREADSAFE=1 -lpthread -ldl -lm
fi
echo "$dir"
