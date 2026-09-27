# sqlite-pure

A from-scratch **SQLite in pure Common Lisp** — no FFI, no libsqlite3. It
reads and writes the SQLite 3 file format and runs SQL against it: a
database written here opens in the `sqlite3` shell and passes its
`PRAGMA integrity_check`; a database written by SQLite opens here; and the
two can share one file at the same time, using SQLite's own locking
protocol.

The existing Common Lisp options (cl-sqlite, cl-dbi's driver) bind the C
library. This is portable CL with no dependencies beyond `sb-posix` on
SBCL (for file locks), which also means it can run where there is no libc
to link against.

Behaviour is matched against **SQLite 3.40** down to details: type
affinity, comparison and collation rules, error messages, which of two
equal rows a `UNION` keeps, which index a scan uses (it decides the order
`group_concat` sees), and decimal ↔ double conversion (SQLite's parser and
`printf` work in x87 long double and are not correctly rounded; that is
reproduced bit for bit — except, measured, about 1 literal in 6 000 whose
parse lands 1 ulp away).

## Use

```lisp
(asdf:load-system "sqlite-pure")

(sqlp:with-database (db "/tmp/demo.db")
  (sqlp:execute db "CREATE TABLE IF NOT EXISTS person(id INTEGER PRIMARY KEY, name TEXT, born INTEGER)")
  (sqlp:execute db "INSERT INTO person(name, born) VALUES (?, ?)" "Ada" 1815)
  (sqlp:with-transaction (db)
    (dolist (p '(("Grace" 1906) ("Alan" 1912)))
      (apply #'sqlp:execute db "INSERT INTO person(name, born) VALUES (?, ?)" p)))
  (sqlp:query db "SELECT name, 2024 - born AS age FROM person WHERE born > ? ORDER BY born" 1900))
;; => (("Grace" 118) ("Alan" 112)), ("name" "age")
```

| | |
|---|---|
| `open-database path &key readonly` | `":memory:"` for a transient database |
| `close-database db`, `with-database (var path) ...` | |
| `query db sql &rest params` | `(values rows column-names)`; each row a list |
| `query-row`, `query-value` | first row / first value |
| `execute db sql &rest params` | rows if the last statement returns any, else its change count |
| `execute-script db sql` | several statements, no parameters |
| `do-query ((a b) db sql &rest params) body` | iterate rows |
| `with-transaction (db) body` | commit on normal exit, roll back on unwind; nests as a savepoint |
| `last-insert-rowid`, `changes` | |

**Extending SQL.** Lisp closures can be registered per connection:

```lisp
(sqlp:define-function db "double" (lambda (x) (* 2 x)) :arity 1)
(sqlp:define-aggregate db "product" (lambda (acc x) (* acc x)) :initial 1 :arity 1)
(sqlp:define-collation db "reverse" (lambda (a b) (cond ((string> a b) -1) ((string< a b) 1) (t 0))))
(sqlp:query db "SELECT product(double(v)) FROM t")
```

Functions receive and return SQL values as below (`nil` → NULL, `t` → 1);
they shadow built-ins of the same name (`undefine-function` removes one).
Aggregates work in `GROUP BY`, with `DISTINCT`/`FILTER`, and as window
functions. A collation may be named in a schema before it is registered —
as in SQLite, using it is the error; give `:key` (a canonical form for
strings equal under the collation) for `GROUP BY`/`DISTINCT` to group by it.

**Tokenizers and FTS5 auxiliary functions** are Lisp functions too (the
counterparts of `fts3_tokenizer()` and `fts5_api`):

```lisp
;; tokens are (text start end [position]), offsets in characters
(sqlp:define-tokenizer db "words"
  (lambda (text args)
    (declare (ignore args))
    (loop for start = 0 then (1+ end)
          for end = (or (position #\Space text :start start) (length text))
          when (< start end) collect (list (string-downcase (subseq text start end)) start end)
          while (< end (length text)))))
(sqlp:execute db "CREATE VIRTUAL TABLE f USING fts5(body, tokenize='words')")   ; or fts4(body, tokenize=words)
(sqlp:define-fts5-function db "hits"
  (lambda (api) (length (sqlp:fts5-api-instances api))))
(sqlp:query db "SELECT rowid, hits(f) FROM f WHERE f MATCH 'lisp' ORDER BY hits(f) DESC")
```

The tokenizer gets the text and the table's tokenizer arguments; FTS5 may
wrap it (`tokenize='porter words'`) and `fts3tokenize` tables accept it.
An auxiliary function gets an API object for the current row and its
extra arguments, and reads it with `fts5-api-rowid`, `-column-count`,
`-column-text`, `-column-size`, `-row-count`, `-column-total-size`,
`-phrase-count`, `-phrase-size`, `-instances` (`(phrase column offset)`
triples, as `xInst` reports them) and `-tokenize`.

Parameters are `?`, `?NNN`, `:name`, `@name`, `$name` (named parameters are
numbered in order of first appearance, as SQLite does). Values map as
**NULL** ↔ `:null` (a Lisp `nil` parameter also binds NULL), **INTEGER** ↔
integer, **REAL** ↔ `double-float`, **TEXT** ↔ string, **BLOB** ↔
`(unsigned-byte 8)` vector. Errors are `sqlp:sqlite-error` (subclasses for
constraint, parse and corruption errors) carrying SQLite's own message.
`sqlp::*busy-timeout*` (seconds, default 5) bounds waiting for a lock.

## The shell: `bin/sqlp`

`bin/sqlp` is a command-line shell that behaves like SQLite's own `sqlite3`
(3.40), running on SBCL.  It takes the same options, uses the same prompts
and statement completion, and supports the same output modes: list, csv,
column, table, box, markdown, line, json, html, insert, quote, tabs, tcl,
ascii, count and off, with `--wrap`, `--wordwrap` and `--quote`.  Error
reports match too (`Parse error near line N: …` followed by the `^--- error
here` excerpt).  It supports the dot-commands people script against: `.backup`/`.save`, `.bail`, `.cd`,
`.changes`, `.databases`, `.dump` (with its options), `.echo`, `.eqp`,
`.exit`/`.quit`, `.fullschema`, `.headers`, `.help`, `.import` (CSV and ASCII,
with `--skip`, `--schema`, `-v`), `.indexes`, `.mode`, `.nullvalue`, `.once`,
`.open` (`--new`, `--readonly`), `.output`, `.parameter`, `.print`, `.prompt`,
`.read`, `.schema` (`--indent`, `--nosys`), `.separator`, `.shell`/`.system`,
`.show`, `.tables`, `.timeout`, `.timer` and `.width`.  `~/.sqliterc` and
`-init` are read as sqlite3 reads them.

```sh
bin/build-sqlp.sh                 # once: saves bin/sqlp.core (starts in milliseconds)
bin/sqlp demo.db                  # interactive
bin/sqlp -box demo.db "SELECT * FROM person"
bin/sqlp demo.db .dump > demo.sql
bin/build-sqlp.sh --executable    # a standalone bin/sqlp-bin
```

Without the saved core, `bin/sqlp` loads the system through ASDF on each
start.  Output is checked byte for byte against the real shell
(`test/run-shell.sh`).  What it does not have: `.load` (there are no C
extensions), `.sha3sum`, `.recover`, `.archive`, `.expert`, `.trace`,
`.stats`, `.lint` and the rest of the rarely-used commands; line editing
and history (run it under `rlwrap` for those); and `sqlite_stat1`, because
`ANALYZE` is accepted but does nothing.

## What is implemented

**File format.** Table and index b-trees (all four page types), overflow
chains, the freelist, page sizes 512–65536, UTF-8 and UTF-16 databases,
`WITHOUT ROWID` tables. Writes go through a rollback journal in SQLite's
format — a crash mid-commit leaves a hot journal that both this library and
SQLite roll back — or, for **WAL-mode** databases, append checksummed frames
to `-wal` (see below). `PRAGMA journal_mode = WAL / DELETE` switches modes.

**Byte-identical files.** Writing is a port of SQLite 3.40's `btree.c`:
cell space within a page (freeblocks, fragments, defragmentation), overflow
chains, the freelist (`allocateBtreePage` with its nearby / exact rules,
`freePage2`), `balance_quick`, `balance_deeper` and `balance_nonroot` with
`editPage`, and insert and delete with SQLite's cursor behaviour
(in-place overwrites, interior-cell promotion).  The statements drive the
b-trees in SQLite's order too: index entries in SQLite's index-list order,
`UPDATE` rewriting only the index entries it must and the row in place,
`REPLACE`'s deletions, `CREATE TABLE`'s placeholder schema row, `CREATE
INDEX`'s sorted bulk load, `DROP` order, `VACUUM`'s rebuild, and auto-vacuum's
relocations; `secure_delete` is on, as in SQLite as commonly built.  So the
same statements leave the same file, byte for byte — checked after every
statement of random workloads (`test/run-file-identity.sh`).  Where SQLite's
query planner would choose a different scan for an `UPDATE` or `DELETE`
(a covering index on a `WITHOUT ROWID` table, say) the rows are visited in
a different order and the pages can differ; FTS3/4/5 write their shadow
tables with the same contents but not yet in SQLite's statement order.
**Auto-vacuum.** `auto_vacuum = FULL` and `INCREMENTAL` databases are read and
written: pointer-map pages are kept current, table and index roots stay packed
at the front of the file (a `DROP` moves the last root into the freed slot and
retargets `sqlite_schema`), FULL mode relocates pages and truncates the file at
every commit, and `PRAGMA incremental_vacuum(N)` releases free pages on demand.
`PRAGMA auto_vacuum` sets the mode on a new file, or for the next `VACUUM`.

**Concurrency.** SQLite's POSIX byte-range locking protocol (SHARED /
RESERVED / PENDING / EXCLUSIVE, via `sb-posix` on SBCL), a busy timeout,
hot-journal recovery only under the lock, and page-cache validation against
the header change counter at every read transaction — so SQLite processes
and this library can use a file concurrently.

**WAL databases** are shared with SQLite processes the way SQLite shares
them among its own connections: through the wal-index in `-shm`, spoken
exactly (header copies and checksums, hash tables, reader marks, and the
WRITE / CKPT / RECOVER / READ locks).  Readers and a writer run at the same
time and each reader keeps its snapshot; a writer whose snapshot went stale
gets "database is locked", as in SQLite.  Checkpoints (`PRAGMA
wal_checkpoint`, passive) never pass a reader's mark; a wholly checkpointed
log is restarted instead of growing; a missing or damaged index is rebuilt
from the log; a crash leaves a log either side recovers; and the last
connection to close checkpoints and removes `-wal` and `-shm`.  Leaving WAL
mode needs the database to ourselves.  (fcntl locks belong to a process, so
two connections inside one Lisp do not exclude each other.)

**SQL.** `SELECT` with every join type (inner, `LEFT`, `RIGHT`, `FULL`,
cross, `USING`, `NATURAL`), `WHERE`/`GROUP BY`/`HAVING`/`ORDER BY` (`NULLS
FIRST/LAST`, `COLLATE`)/`LIMIT`/`OFFSET`, `DISTINCT`, aggregates (with
`DISTINCT` and `FILTER`), **window functions** (`OVER`, `PARTITION BY`,
`ROWS`/`RANGE`/`GROUPS` frames, `EXCLUDE`, named windows), subqueries (scalar, `IN`,
`EXISTS`, correlated, in `FROM`), `UNION [ALL]`/`INTERSECT`/`EXCEPT`,
`VALUES`, CTEs including `WITH RECURSIVE`, views, row values, table-valued
`json_each`/`json_tree` and `pragma_table_info(…)` & co. (with lateral references).
`INSERT` (`VALUES`, `SELECT`, `DEFAULT VALUES`, `OR REPLACE/IGNORE/ABORT/
FAIL/ROLLBACK`, upsert `ON CONFLICT … DO UPDATE/NOTHING`, `RETURNING`),
`UPDATE` (including `UPDATE … FROM`), `DELETE`.
`CREATE/DROP TABLE` (`PRIMARY KEY`, `UNIQUE`, `NOT NULL`, `CHECK`,
`DEFAULT`, `COLLATE`, `AUTOINCREMENT`, **generated columns**, **STRICT**,
**foreign keys** with `ON DELETE/UPDATE` actions and deferred checking),
`CREATE TABLE … AS`, indexes (unique, multi-column, `DESC`, collations,
partial, on expressions), views, **triggers** (`BEFORE`/`AFTER`/`INSTEAD
OF`, `WHEN`, `RAISE`, `PRAGMA recursive_triggers`), `ALTER TABLE` (rename table, rename/add/drop column),
`BEGIN`/`COMMIT`/`ROLLBACK`, `SAVEPOINT`/`RELEASE`/`ROLLBACK TO`, **`TEMP`
tables and `ATTACH`/`DETACH`**, `VACUUM` and `VACUUM INTO`, and the common
`PRAGMA`s (`table_info`, `table_xinfo`, `index_list`, `index_info`,
`foreign_key_list`, `foreign_keys`, `user_version`, `application_id`,
`integrity_check`, `page_size`, `page_count`, `freelist_count`,
`database_list`, `table_list`, `encoding`, …).

**Functions.** Core: `abs changes char coalesce concat concat_ws format
glob hex ifnull iif instr last_insert_rowid length like likely lower ltrim
max min nullif octet_length printf quote random randomblob replace round
rtrim sign soundex sqlite_version substr substring total_changes trim
typeof unhex unicode unlikely upper zeroblob`. Aggregates: `avg count
group_concat max min string_agg sum total`. Window: `row_number rank
dense_rank percent_rank cume_dist ntile lag lead first_value last_value
nth_value`. Date/time: `date time datetime julianday unixepoch strftime`
(with SQLite's modifiers). Math: `acos acosh asin asinh atan atan2 atanh
ceil ceiling cos cosh degrees exp floor ln log log10 log2 mod pi pow power
radians sin sinh sqrt tan tanh trunc`. JSON: `json json_valid json_quote
json_array json_object json_extract -> ->> json_type json_array_length
json_set json_insert json_replace json_remove json_patch json_group_array
json_group_object json_each json_tree`.

**Query planning.** A port of SQLite 3.40's query planner (`where.c`): the
WHERE/ON terms are analyzed as SQLite analyzes them (commuted copies,
`BETWEEN` and `IS NOT NULL` children, transitive `col = col` equivalences,
constant propagation, `LEFT JOIN` simplification, no-op `LEFT JOIN`
removal), every candidate loop — full scans, covering-index scans, rowid
and index lookups with `=`, `IN`, range and `IS NULL` constraints, automatic
(and partial automatic) indexes — is costed with SQLite's formulas, and the
path solver picks the join order and one loop per table, counting the cost
of any sort an `ORDER BY`, `GROUP BY` or `DISTINCT` would need. A lone
`min()`/`max()` reads one end of an index; `count(*)` counts the smallest
index; `INDEXED BY` and `NOT INDEXED` are honoured. A differential fuzzer
(`test/planfuzz.py`) compares plans and rows with sqlite3 over random
schemas, data and joins.
`ORDER BY` is satisfied from rowid or index order where possible (in either
direction, stopping early for `LIMIT`); otherwise `ORDER BY … LIMIT` keeps
only the best rows. Only referenced columns are decoded; `count(*)` comes
from cell counts. Every `WHERE` term is still evaluated as a filter, so a
plan can only narrow the candidate rows, never change the answer.

**R-trees.** `CREATE VIRTUAL TABLE t USING rtree(id, minX, maxX, ...)` and
`rtree_i32`, 1 to 5 dimensions plus `+auxiliary` columns, stored exactly as
SQLite 3.40 stores them (the `_node` / `_rowid` / `_parent` shadow tables,
fixed-size node blobs, float32 coordinates rounded outward), so either side
can modify a tree the other built.  Insertion and deletion are ports of
rtree.c's (least-enlargement descent, R*-tree split, forced reinsertion,
underfull-node removal and reinsertion, node numbering), so the same
statements leave the shadow tables byte for byte as SQLite leaves them;
queries prune by bounding box
using the `WHERE` clause's constraints on coordinates, and look up `id =`
directly.  Conflict handling, value coercions and error messages follow
SQLite's, and `rtreecheck()` and `rtreenode()` are provided.  A database holding
virtual tables of modules this library lacks opens; those tables report
"no such module", as in SQLite.

**Geopoly.** `CREATE VIRTUAL TABLE t USING geopoly(a, b, ...)` gives
`t(_shape, a, b, ...)`, stored as SQLite stores it (a 2-D float r-tree of
bounding boxes, the polygon in the `_rowid` table), and every function:
`geopoly_area`, `_blob`, `_json`, `_svg`, `_bbox`, `_group_bbox`,
`_contains_point`, `_within`, `_overlap`, `_xform`, `_regular`, `_ccw`.
They compute in float32 wherever SQLite does, so results agree to the
last bit, including SQLite's leniencies in parsing polygon JSON.
`WHERE geopoly_overlap(_shape, ?)` and `geopoly_within(_shape, ?)` search
the tree by bounding box, `rowid =` looks up directly, and `_shape` is
checked, converted from JSON and left alone by updates that do not set
it, as in SQLite.

**DBSTAT.** The `dbstat` table (eponymous, `dbstat('schema', aggregate)`,
or `CREATE VIRTUAL TABLE ... USING dbstat`) lists every page of every
b-tree and overflow chain — path, type, cells, payload, unused bytes,
offsets — or with `aggregate = 1` one row per b-tree, as SQLite's does.

**Durability.** Commits `fsync` where SQLite does (the rollback journal
before the database is written, the database before the journal is
removed, the WAL at commit under `synchronous=FULL`, the WAL before and
the database after a checkpoint); `PRAGMA synchronous` takes SQLite's
values (`OFF`, `NORMAL`, `FULL`, `EXTRA`, 0-3) with FULL the default.

**Full-text search (FTS5).** `CREATE VIRTUAL TABLE t USING fts5(...)` with
`UNINDEXED` columns, `prefix=`, `tokenize=`, `content=` (external content
and contentless `content=''`), `content_rowid=`, `columnsize=` and
`detail=full/column/none`, in SQLite 3.40's on-disk format: the
`_data` / `_idx` / `_content` / `_docsize` / `_config` shadow tables,
prefix-compressed leaves, doclists and position lists, delete markers,
the structure and averages records.  A statement's writes are flushed the
way SQLite flushes them, so a small index is byte-for-byte the one SQLite
writes; merges follow SQLite's automerge / crisismerge schedule and
promotion rules (whole-level merges where SQLite's are incremental), and
either side reads, writes and `integrity-check`s the other's indexes,
including half-finished incremental merges and doclist indexes.
Tokenizers: `unicode61` (character data extracted from SQLite itself;
`remove_diacritics`, `tokenchars`, `separators`), `ascii`, `porter` and
`trigram`.  The query language is FTS5's: implicit AND, `AND` / `OR` /
`NOT`, `"phrases"`, `+`, prefix `*`, `^`, `NEAR(... , N)` and column
filters (`col:`, `{a b}:`, `-col:`), with SQLite's error messages;
queries are evaluated by a port of SQLite's expression iterator, so
`bm25()`, `highlight()`, `snippet()` and the `rank` column (default or
`rank MATCH 'bm25(...)'`, or the `rank` config option) see exactly the
phrase instances SQLite's do.  `MATCH`, `t = 'query'`, `col MATCH` and
`t('query'[, 'rank'])` are accepted; `INSERT INTO t(t) VALUES (...)` runs
`optimize`, `merge`, `rebuild`, `delete`, `delete-all`, `integrity-check`
and the `automerge` / `crisismerge` / `usermerge` / `pgsz` / `rank` /
`hashsize` settings; `fts5vocab` tables (`row`, `col`, `instance`) are
there too.

**Full-text search (FTS3 and FTS4).** `CREATE VIRTUAL TABLE t USING
fts3(...)` / `fts4(...)` with `tokenize=` and, for FTS4, `prefix=`,
`content=` (external content, and contentless `content=''`),
`languageid=`, `notindexed=`, `order=desc`, `matchinfo=fts3` and
`compress=` / `uncompress=` (any SQL function, user-defined included), in
SQLite's on-disk format: the `_content` / `_segments` / `_segdir` /
`_docsize` / `_stat` shadow tables, segment b-trees with prefix-compressed
leaves and interior nodes, doclists and position lists, delete markers,
per-language and per-prefix-index levels.  Pending terms are written out
when SQLite writes them — at the end of a transaction, when docids go
backwards, and when a statement SQLite gives a statement journal starts —
and segments are merged 16 at a time, so the shadow tables come out
byte-for-byte as SQLite's do; `merge=X,Y` and `automerge=N` run SQLite's
incremental merge (appendable segments, the merge hint in `_stat`), so
either side can pick up a merge the other left half done, and each reads,
writes and `integrity-check`s the other's indexes.  Tokenizers: `simple`,
`porter` and `unicode61` (tables taken from SQLite's source;
`remove_diacritics=0/1/2`, `tokenchars=`, `separators=`).  Queries use the
enhanced syntax SQLite is normally built with: implicit AND, `AND`, `OR`,
`NOT`, `"phrases"`, prefix `*`, `^first` (FTS4), `col:term`, `NEAR` and
`NEAR/n`, parentheses, with SQLite's rebalancing and error messages.  The
evaluator is a port of SQLite's (whole and incremental doclists, deferred
tokens, NEAR trimming of position lists), so `snippet()`, `offsets()` and
`matchinfo()` (every format character: `p c n a l s x y b`) return what
SQLite returns for each row.  `docid`, `rowid` and the language id are
hidden columns; `MATCH` on the table or a column, `docid =` / ranges and
`ORDER BY docid` are used by the scan; `INSERT INTO t(t) VALUES (...)` runs
`optimize`, `rebuild`, `integrity-check`, `merge=` and `automerge=`, and
`optimize(t)` works too.  `fts4aux` and `fts3tokenize` tables are there.

**EXPLAIN QUERY PLAN** reports the plan this library chose, in SQLite
3.40's words and tree shape: `SEARCH t USING COVERING INDEX i (a=? AND
b=?)`, `SCAN t`, `LEFT-JOIN`, `CO-ROUTINE` / `MATERIALIZE`, `SETUP` /
`RECURSIVE STEP`, `(CORRELATED) SCALAR / LIST SUBQUERY n` (numbered as
SQLite numbers them), compound parts, `SCAN n CONSTANT ROWS`, R-tree and
table-valued `VIRTUAL TABLE INDEX` lines, and the `USE TEMP B-TREE FOR
GROUP BY / DISTINCT / ORDER BY` steps. Where the two planners choose alike
(most single-table and `FROM`-ordered queries) the output is identical;
where they differ (subquery flattening, the `OR` multi-index optimization,
`LIKE` prefixes, `sqlite_stat1` statistics) it describes what this library
does. Plain `EXPLAIN` (VDBE bytecode) has no
equivalent here.

## Not implemented

R-tree `MATCH` geometry callbacks, the ICU tokenizer, FTS5's
`*`-prefixed diagnostic queries, plain `EXPLAIN` (bytecode listings),
`ANALYZE` (accepted, writes no `sqlite_stat1`), and in the planner:
subquery flattening, the `OR` (multi-index) and `LIKE` optimizations,
skip-scans and Bloom filters.  `fsync` and file locks need SBCL (elsewhere
`finish-output` is the barrier and locks are no-ops, with cache
validation still applied).

## Performance (SBCL, one core)

About 60 000 inserts/s inside a transaction (indexed table), ~1.2 M rows/s
for a full scan with a filter, microsecond rowid and index lookups, and
`ORDER BY id DESC LIMIT 10` over 300 000 rows in 2 ms.

## Testing

Everything is checked against real SQLite (Python's `sqlite3`, SQLite 3.40):

| script | what |
|---|---|
| `test/run-tests.sh` (also `(asdf:test-system "sqlite-pure")`) | the Lisp API tests (`test/api.lisp`), and the **differential suite**: `test/cases/*.test` are SQL scripts; `test/gen-expected.py` records SQLite's rows or error for every statement; each is replayed here and compared, error messages included |
| `test/run-qfuzz.sh FIRST N Q` | **query fuzzer**: random expressions, joins, subqueries, compounds, windows and CTEs over random mixed-type data, compared statement by statement |
| `python3 test/planfuzz.py SQLITE3 bin/sqlp FIRST N [Q]` | **planner fuzzer**: random schemas (indexes, WITHOUT ROWID, INTEGER PRIMARY KEY), data and joins; `EXPLAIN QUERY PLAN` output and rows (in order) must match sqlite3. `PLANFUZZ_NO_SUBQ=1` / `PLANFUZZ_NO_OR=1` leave out FROM-subqueries and `OR` terms |
| `test/run-fuzz.sh FIRST N` | **file-format fuzzer**: random workloads (values up to 70 KB, index churn, `REPLACE`, rolled-back transactions, `WITHOUT ROWID`, `AUTOINCREMENT`) run by both engines into separate files; SQLite must pass `integrity_check` on the file written here, the contents must match, and this library must read SQLite's file identically |
| `test/run-formats.sh` | SQLite-made files in other shapes (page sizes, UTF-16LE/BE, WAL, auto_vacuum, heavy freelists) read here and modified here, plus crash recovery in both directions |
| `test/run-floats.sh SEED` | decimal → double and double → text, bit for bit, on random values |
| `test/run-fts3-interop.sh` | FTS3/4 indexes shared through the file: SQLite-built deep segment trees (small pages, prefix index, an unfinished incremental merge) queried and modified here and the merge finished by SQLite; the same statements on both sides giving identical shadow tables; external content, language ids, `order=desc`; every step checked by SQLite's `integrity-check` |
| `test/run-fts3fuzz.sh` | random documents (short and long, negative docids) and random FTS3/4 queries (every operator, NEAR/n, prefixes, `^`, column filters, malformed queries) on six table configurations against SQLite: docids, `snippet()`, `offsets()`, `matchinfo()` |
| `test/run-fts3-tokens.sh` | the `simple`, `porter` and `unicode61` tokenizers (with arguments) against SQLite's `fts3tokenize`: tokens, byte offsets, positions |
| `test/run-fts5-interop.sh` | FTS5 indexes shared through the file: SQLite-built multi-segment indexes (small pages, doclist indexes, unfinished merges) queried and modified here, ours queried and modified by SQLite, every step checked by SQLite's `integrity-check` |
| `test/run-fts5fuzz.sh` | random documents and random FTS5 queries (every operator, column filters, NEAR, prefixes, detail modes) against SQLite: rowids, `bm25()`, `highlight()`, `snippet()` |
| `test/run-fts5-tokens.sh` | every tokenizer configuration against SQLite's, token for token, over random text and a stemming word list |
| `test/run-geopoly.sh` | geopoly against SQLite 3.40.1 built with GEOPOLY (`test/build-oracle.sh` builds it from the amalgamation): 2000 random rows of every function compared bit for bit, and a table built by each side read and modified by the other; also regenerates `test/cases-ext` (run by `run-tests.sh` from the committed `test/expected-ext.sexp`) |
| `test/run-file-identity.sh [FIRST N]` | the whole database file, byte for byte, after every statement of random workloads (rowid, rowid-less and `WITHOUT ROWID` tables, every kind of index, overflow values, REPLACE / IGNORE / UPSERT, rowid-changing UPDATEs, DDL, rollbacks, auto-vacuum FULL and INCREMENTAL, VACUUM, three page sizes) run by SQLite and by this library |
| `test/run-rtree-fuzz.sh [FIRST N]` | random r-tree workloads (1-5 dimensions, `rtree_i32`, auxiliary columns, page sizes, REPLACE, rowid changes, rollbacks): after every statement the shadow tables must be byte for byte SQLite's |
| `test/run-rtree.sh` | r-trees modified alternately by SQLite and by us, checked against a plain mirror table and by SQLite's `rtreecheck()`; auto-vacuum root moves on DROP; VACUUM |
| `test/run-wal.sh` | WAL databases shared with live SQLite connections: each side reading the other's commits, snapshots surviving the other's writes and checkpoints, the write lock both ways, stale snapshots, log restart, two processes writing at once, last-one-out cleanup, crash recovery, rebuilding SQLite's index, mode switching; `FUZZ_WAL=1 test/run-fuzz.sh` runs the file fuzzer in WAL mode (and `FUZZ_AUTOVACUUM=FULL` or `INCREMENTAL` with auto-vacuum) |
| `test/run-locking.sh` | SQLite processes and this library on one file: lock conflicts both ways, stale-cache detection, concurrent writers |
| `test/run-slt.sh [-j N] [FILE…]` | **sqllogictest**, SQLite's engine-independent SQL correctness corpus (622 files, ~7.4 M records, every expected result produced by SQLite), run through the library directly; values rendered, sorted and hashed exactly as the corpus's own SQLite driver does. Records where the corpus (made by an older SQLite) disagrees with SQLite 3.40 itself are listed, with the reason, in `test/slt-known.txt` |
| `test/run-tcl.sh [-j N] [-t SECS] [FILE…]` | **SQLite's own TCL test suite** — the `test/*.test` files and `tester.tcl` of the 3.40.1 source release, unmodified — against this library: `test/tcl/sqlite3.tcl` implements tclsqlite's `[sqlite3]` command over `test/tcl/server.lisp` (one server process per database handle, callbacks for Tcl functions and collations), and `test/tcl/testfixture.c` is a tclsh that loads it. Test-only C hooks of SQLite's testfixture are stubbed and counted, so each file's line says how many it reached |
| `test/run-web-files.sh` | real databases from the web (Chinook, Northwind, Sakila, two GeoPackages, an MBTiles file): `.dump` identical to sqlite3's; the same modifications and a VACUUM by both engines give the same output and content, pass sqlite3's `integrity_check`, and (Chinook, Northwind) byte-identical files |
| `test/run-shell.sh [CASE…]` | `bin/sqlp` against SQLite's `sqlite3` shell (built by `test/build-oracle.sh`): every script in `test/shell/*.case` must give identical stdout, stderr and exit status. The scripts cover every output mode, the dot-commands, `.dump`, `.import`, error reports, statement completion, interactive prompts and the command-line options |

Current results (SQLite 3.40.1 as reference): **sqllogictest** — every
record of all 622 files passes (two records listed as 3.40-versus-corpus
differences), `select5.test`'s 18-way joins included.  **SQLite's TCL suite** — of the 628 files
that use no testfixture-only C hooks, 144 880 of 156 948 tests pass (92.3%);
over all 1042 files that run to the end, 188 220 of 215 098.

## Layout

```
src/
  util       conditions, octets, big-endian ints, varints, UTF-8/16, IEEE doubles
  pager      pages, header, freelist, transactions, savepoints, journals
  locking    SQLite's file locks and cache validation
  wal        write-ahead log and the shared wal-index (-shm)
  record     the record format
  btree      b-trees: reading (both directions)
  btree-edit b-trees: writing, a port of SQLite's (cells, freelist, balancing)
  values     storage classes, comparison, collation, affinity, CAST, SQLite's AtoF
  lexer, parser        SQL -> AST
  schema     sqlite_schema -> tables, columns, indexes, foreign keys, triggers
  expr       expression compiler (closures)
  select     query engine: sources, joins, aggregates, sorting, compounds, CTEs
  where      the query planner (a port of SQLite's where.c) and the loops it runs
  window     window functions
  functions, printf, math, datetime, json    built-in functions
  triggers   trigger execution
  fkeys      foreign key enforcement
  dml        INSERT / UPDATE / DELETE, constraints, conflicts, upsert, RETURNING
  ddl        CREATE / DROP / ALTER and sqlite_schema maintenance
  rtree      the R*Tree virtual table module
  geopoly    the Geopoly module and its functions
  dbstat     the DBSTAT virtual table
  extend-fts Lisp tokenizers and FTS5 auxiliary functions
  fts5-*     FTS5: tokenizers and their Unicode data, the index, the query language
  fts5       the FTS5 and fts5vocab virtual tables, bm25 / highlight / snippet
  fts3-*     FTS3/4: tokenizers and their Unicode data, the segment index and
             merges, the query parser, the evaluator, snippet / offsets / matchinfo
  fts3       the FTS3/FTS4, fts4aux and fts3tokenize virtual tables
  eqp        EXPLAIN QUERY PLAN
  integrity  PRAGMA integrity_check
  api        public API, statements, transactions, ATTACH, PRAGMAs
  vacuum     VACUUM
shell/       bin/sqlp, the sqlite3-compatible shell (system sqlite-pure/shell)
test/tcl/    the [sqlite3] Tcl command and testfixture for SQLite's TCL suite
bin/         sqlp launcher and build-sqlp.sh
test/        see above
```

## License

MIT
