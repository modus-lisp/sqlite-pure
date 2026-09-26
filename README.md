# sqlite-pure

A from-scratch **SQLite in pure Common Lisp** — no FFI, no libsqlite3. It
reads and writes the SQLite 3 file format and runs SQL against it, so a
database written here opens in the `sqlite3` shell (and passes its
`PRAGMA integrity_check`), and a database written by SQLite opens here.

The existing Common Lisp options (cl-sqlite, cl-dbi's driver) are bindings to
the C library. This one is portable CL with no dependencies, which also means
it can run where there is no libc to link against.

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
| `with-transaction (db) body` | commit on normal exit, roll back on unwind |
| `last-insert-rowid`, `changes` | |

Parameters are `?`, `?NNN`, `:name`, `@name`, `$name` (named parameters are
numbered in order of first appearance, as SQLite does). Values map as
**NULL** ↔ `:null` (a Lisp `nil` parameter also binds NULL), **INTEGER** ↔
integer, **REAL** ↔ `double-float`, **TEXT** ↔ string, **BLOB** ↔
`(unsigned-byte 8)` vector. Errors are `sqlp:sqlite-error` (subclasses for
constraint, parse and corruption errors), with SQLite's own message text.

## What is implemented

**File format.** Table and index b-trees (interior/leaf, all four page
types), cell overflow chains, the freelist (trunk and leaf pages), page sizes
512–65536, UTF-8 and UTF-16 databases, `WITHOUT ROWID` tables, reading
WAL-mode databases (committed frames of `-wal` are applied; such a database
opens read-only). Writes use a rollback journal in SQLite's own format, so a
crash mid-commit leaves a hot journal that both this library and SQLite roll
back.

**SQL.** `SELECT` with joins (inner, left, cross, `USING`, `NATURAL`),
`WHERE`/`GROUP BY`/`HAVING`/`ORDER BY` (`NULLS FIRST/LAST`, `COLLATE`)/
`LIMIT`/`OFFSET`, `DISTINCT`, aggregates (with `DISTINCT` and `FILTER`),
subqueries (scalar, `IN`, `EXISTS`, correlated, in `FROM`), `UNION [ALL]`/
`INTERSECT`/`EXCEPT`, `VALUES`, common table expressions including
`WITH RECURSIVE`, views, row values. `INSERT` (`VALUES`, `SELECT`,
`DEFAULT VALUES`, `OR REPLACE/IGNORE/ABORT/FAIL/ROLLBACK`, upsert
`ON CONFLICT ... DO UPDATE/NOTHING`, `RETURNING`), `UPDATE`, `DELETE`.
`CREATE/DROP TABLE` (constraints: `PRIMARY KEY`, `UNIQUE`, `NOT NULL`,
`CHECK`, `DEFAULT`, `COLLATE`, `AUTOINCREMENT`), `CREATE TABLE ... AS`,
`CREATE/DROP INDEX` (unique, multi-column, `DESC`, collations, partial,
expressions), `CREATE/DROP VIEW`, triggers, `ALTER TABLE` (rename table,
rename/add/drop column), `BEGIN`/`COMMIT`/`ROLLBACK`, and the common
`PRAGMA`s (`table_info`, `index_list`, `index_info`, `user_version`,
`integrity_check`, `page_size`, ...).

**Semantics.** SQLite's type affinity rules, comparison affinity and
collation selection (`BINARY`, `NOCASE`, `RTRIM`), three-valued logic,
64-bit integer arithmetic overflowing to REAL, SQLite's REAL-to-text
formatting (`%!.15g` with its own digit generation), and the functions:
`abs changes char coalesce concat concat_ws date datetime format glob hex
ifnull iif instr julianday last_insert_rowid length like likely lower ltrim
max min nullif octet_length printf quote random randomblob replace round
rtrim sign soundex sqlite_version strftime substr substring time
total_changes trim typeof unhex unicode unixepoch unlikely upper zeroblob`
and the aggregates `avg count group_concat max min string_agg sum total`.

**Query planning.** Each join level uses a rowid lookup, a rowid range, an
index prefix seek, or a scan, chosen from the `WHERE`/`ON` conjuncts with
SQLite's rules for when an index may be used under affinity and collation.
Every conjunct is still evaluated as a filter, so the plan can only narrow
the candidate rows, never change the answer.

## Not implemented

Window functions, JSON functions, virtual tables (FTS, R-tree),
`ATTACH`, `SAVEPOINT`, `TEMP` tables (they are created in the main
database), foreign key enforcement (SQLite's default is off too), writing to
WAL-mode databases, file locking (one process at a time), `VACUUM`, and
`EXPLAIN`. Durability depends on the Lisp's `finish-output`; there is no
portable `fsync`.

## Testing

Everything is checked against real SQLite (Python's `sqlite3`, SQLite 3.40):

* **Differential SQL suite** — `test/cases/*.test` hold SQL scripts;
  `test/gen-expected.py` runs them through SQLite and records every
  statement's rows or error; `test/differential.lisp` replays them here and
  compares values, column names and error messages.
* **File-format fuzzer** — `test/run-fuzz.sh FIRST COUNT` generates random
  workloads (inserts/updates/deletes/replaces of values from a few bytes to
  70 KB, index churn, rolled-back transactions, `WITHOUT ROWID`,
  `AUTOINCREMENT`), runs each through both engines into separate files, and
  requires that (1) SQLite's `integrity_check` passes on the file written
  here, (2) both files hold identical contents, and (3) this library reads
  SQLite's file identically.

```sh
python3 test/gen-expected.py            # regenerate expectations
sh test/run-tests.sh                    # differential suite
sh test/run-fuzz.sh 1 20                # 20 fuzz seeds
```

## Layout

```
src/
  util       conditions, octets, big-endian ints, varints, UTF-8/16, IEEE doubles
  pager      pages, header, freelist, transactions, rollback + hot journal, WAL read
  record     the record format (serial types)
  btree      table/index b-trees: traversal, insert with splits, delete with collapse
  values     storage classes, comparison, collation, affinity, CAST
  lexer      tokens
  parser     SQL -> AST
  schema     sqlite_schema -> tables, columns, indexes, triggers
  expr       expression compiler (closures)
  select     query engine: sources, join planning, aggregates, sorting, compounds, CTEs
  functions  scalar and aggregate functions
  printf     printf() and SQLite's float formatting
  datetime   date and time functions (after SQLite's date.c)
  triggers   trigger execution
  dml        INSERT / UPDATE / DELETE, constraints, conflicts, upsert, RETURNING
  ddl        CREATE / DROP / ALTER and sqlite_schema maintenance
  integrity  PRAGMA integrity_check
  api        public API, statement dispatch, transactions, PRAGMAs
test/
  cases/*.test, gen-expected.py, expected.sexp, differential.lisp
  fuzz.py, fuzz.lisp, run-fuzz.sh
```

## License

MIT
