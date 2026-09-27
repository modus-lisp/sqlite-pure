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

Parameters are `?`, `?NNN`, `:name`, `@name`, `$name` (named parameters are
numbered in order of first appearance, as SQLite does). Values map as
**NULL** ↔ `:null` (a Lisp `nil` parameter also binds NULL), **INTEGER** ↔
integer, **REAL** ↔ `double-float`, **TEXT** ↔ string, **BLOB** ↔
`(unsigned-byte 8)` vector. Errors are `sqlp:sqlite-error` (subclasses for
constraint, parse and corruption errors) carrying SQLite's own message.
`sqlp::*busy-timeout*` (seconds, default 5) bounds waiting for a lock.

## What is implemented

**File format.** Table and index b-trees (all four page types), overflow
chains, the freelist, page sizes 512–65536, UTF-8 and UTF-16 databases,
`WITHOUT ROWID` tables. Writes go through a rollback journal in SQLite's
format — a crash mid-commit leaves a hot journal that both this library and
SQLite roll back — or, for **WAL-mode** databases, append checksummed frames
to `-wal` (see below). `PRAGMA journal_mode = WAL / DELETE` switches modes. Pages split on insert and merge
through their parent on delete, keeping every leaf at the same depth.
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

**Query planning.** Each join level uses a rowid lookup, a rowid range, an
index prefix seek, or a scan, chosen from the `WHERE`/`ON` terms with
SQLite's rules for when an index may be used under affinity and collation.
`ORDER BY` is satisfied from rowid or index order where possible (in either
direction, stopping early for `LIMIT`); otherwise `ORDER BY … LIMIT` keeps
only the best rows. Only referenced columns are decoded; `count(*)` comes
from cell counts. Every `WHERE` term is still evaluated as a filter, so a
plan can only narrow the candidate rows, never change the answer.

## Not implemented

Virtual tables (FTS, R-tree), `EXPLAIN`. Durability depends on the Lisp's
`finish-output`; there is no portable `fsync`. File locks need SBCL
(elsewhere they are no-ops, and cache validation still applies).

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
| `test/run-fuzz.sh FIRST N` | **file-format fuzzer**: random workloads (values up to 70 KB, index churn, `REPLACE`, rolled-back transactions, `WITHOUT ROWID`, `AUTOINCREMENT`) run by both engines into separate files; SQLite must pass `integrity_check` on the file written here, the contents must match, and this library must read SQLite's file identically |
| `test/run-formats.sh` | SQLite-made files in other shapes (page sizes, UTF-16LE/BE, WAL, auto_vacuum, heavy freelists) read here and modified here, plus crash recovery in both directions |
| `test/run-floats.sh SEED` | decimal → double and double → text, bit for bit, on random values |
| `test/run-wal.sh` | WAL databases shared with live SQLite connections: each side reading the other's commits, snapshots surviving the other's writes and checkpoints, the write lock both ways, stale snapshots, log restart, two processes writing at once, last-one-out cleanup, crash recovery, rebuilding SQLite's index, mode switching; `FUZZ_WAL=1 test/run-fuzz.sh` runs the file fuzzer in WAL mode (and `FUZZ_AUTOVACUUM=FULL` or `INCREMENTAL` with auto-vacuum) |
| `test/run-locking.sh` | SQLite processes and this library on one file: lock conflicts both ways, stale-cache detection, concurrent writers |

## Layout

```
src/
  util       conditions, octets, big-endian ints, varints, UTF-8/16, IEEE doubles
  pager      pages, header, freelist, transactions, savepoints, journals
  locking    SQLite's file locks and cache validation
  wal        write-ahead log and the shared wal-index (-shm)
  record     the record format
  btree      b-trees: traversal (both directions), insert with splits, delete with merges
  values     storage classes, comparison, collation, affinity, CAST, SQLite's AtoF
  lexer, parser        SQL -> AST
  schema     sqlite_schema -> tables, columns, indexes, foreign keys, triggers
  expr       expression compiler (closures)
  select     query engine: sources, joins, planning, aggregates, sorting, compounds, CTEs
  window     window functions
  functions, printf, math, datetime, json    built-in functions
  triggers   trigger execution
  fkeys      foreign key enforcement
  dml        INSERT / UPDATE / DELETE, constraints, conflicts, upsert, RETURNING
  ddl        CREATE / DROP / ALTER and sqlite_schema maintenance
  integrity  PRAGMA integrity_check
  api        public API, statements, transactions, ATTACH, PRAGMAs
  vacuum     VACUUM
test/        see above
```

## License

MIT
