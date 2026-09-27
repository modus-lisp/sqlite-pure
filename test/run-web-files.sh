#!/bin/sh
# test/run-web-files.sh — real-world SQLite databases from the web (Chinook,
# Northwind, Sakila, GeoPackages, an MBTiles file), each checked three ways
# against SQLite's own sqlite3 shell (SQLITE3, default: built by
# test/build-oracle.sh):
#   read   — both engines' .dump of the untouched file must be identical
#   write  — the same modifications (test/web-mods.py) applied by each engine
#            to its own copy: same output, sqlite3's integrity_check "ok" on
#            ours, identical content (timestamps from datetime('now') aside),
#            and whether the files are byte-identical
#   vacuum — then VACUUM on both, the same checks
set -e
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
ref=${SQLITE3:-$("$here/test/build-oracle.sh")/sqlite3}
sqlp="$here/bin/sqlp"
dir=${TMPDIR:-/tmp}/sqlite-pure-web
mkdir -p "$dir"
cd "$dir"
for u in https://github.com/lerocha/chinook-database/releases/download/v1.4.5/Chinook_Sqlite.sqlite \
         https://raw.githubusercontent.com/jpwhite3/northwind-SQLite3/main/dist/northwind.db \
         https://raw.githubusercontent.com/bradleygrant/sakila-sqlite3/main/sakila_master.db \
         https://raw.githubusercontent.com/ngageoint/geopackage-js/master/test/fixtures/rivers.gpkg \
         https://raw.githubusercontent.com/OSGeo/gdal/master/autotest/ogr/data/gpkg/2d_envelope.gpkg \
         https://raw.githubusercontent.com/mapbox/node-mbtiles/master/test/fixtures/plain_1.mbtiles; do
  f=$(basename "$u")
  [ -f "$f" ] || curl -sSfL -o "$f" "$u" || { echo "SKIP $f (download failed)"; rm -f "$f"; }
done
norm() { sed -E "s/'[0-9]{4}-[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2}:[0-9]{2}'/'TIMESTAMP'/g" "$1"; }
fails=0
for f in Chinook_Sqlite.sqlite northwind.db sakila_master.db rivers.gpkg 2d_envelope.gpkg plain_1.mbtiles; do
  [ -f "$f" ] || continue
  "$ref" -readonly "$f" .dump > ref.sql; "$sqlp" -readonly "$f" .dump > ours.sql
  if cmp -s ref.sql ours.sql; then r=same; else r=DIFFERENT; fails=$((fails+1)); fi
  python3 "$here/test/web-mods.py" "$f" > mods.sql
  cp "$f" w-ref.db; cp "$f" w-ours.db
  for phase in write vacuum; do
    if [ $phase = write ]; then
      "$ref" w-ref.db < mods.sql > o-ref.txt 2>&1 || true; "$sqlp" w-ours.db < mods.sql > o-ours.txt 2>&1 || true
    else
      echo VACUUM | "$ref" w-ref.db > o-ref.txt 2>&1 || true; echo VACUUM | "$sqlp" w-ours.db > o-ours.txt 2>&1 || true
    fi
    out=$(cmp -s o-ref.txt o-ours.txt && echo same-output || echo OUTPUT-DIFFERS)
    integ=$("$ref" w-ours.db "pragma integrity_check" | head -1)
    "$ref" w-ref.db .dump > d-ref.sql; "$ref" w-ours.db .dump > d-ours.sql
    norm d-ref.sql > n-ref.sql; norm d-ours.sql > n-ours.sql
    content=$(cmp -s n-ref.sql n-ours.sql && echo same-content || echo CONTENT-DIFFERS)
    bytes=$(cmp -s w-ref.db w-ours.db && echo byte-identical || echo "bytes-differ")
    [ "$out" = same-output ] && [ "$integ" = ok ] && [ "$content" = same-content ] || fails=$((fails+1))
    printf '%-22s read:%-9s %-6s %-14s integrity:%-3s %-15s %s\n' "$f" "$r" $phase $out "$integ" $content "$bytes"
  done
done
echo "web files: $fails failed checks"
[ $fails -eq 0 ]
