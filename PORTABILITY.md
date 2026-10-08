# Portability: what is SBCL-only

sqlite-pure is portable Common Lisp. On SBCL it uses a few system services: `sb-posix` for file locks, `fsync` and `ftruncate`, and `sb-thread` for mutexes. Every other implementation gets a `#-sbcl` fallback for each. The fallbacks let the library load and run, but they are **not** equivalent. On hosted modus (and any non-SBCL implementation) the gaps below are real.

## The gaps

| Service | SBCL | Elsewhere | Consequence elsewhere |
|---|---|---|---|
| File locks: `posix-lock` (`src/locking.lisp`), `fd-lock` (`src/wal.lisp`) | `fcntl(F_SETLK)` byte-range locks | always succeed | **No cross-process locking.** A process sharing a database with another process (another Lisp, the `sqlite3` shell, a Python program) can interleave writes and corrupt the file. Rollback-journal and WAL alike. |
| Lock-table mutex: `with-lock-mutex` (`src/locking.lisp`) | recursive mutex | `progn` | Threads in one image are not serialized while they update the process's lock table. |
| Connection mutex: `with-connection-mutex` (`src/util.lisp`) | recursive mutex per connection | `progn` | Two threads using one connection can run statements at once. SQLite's serialized mode is not provided. |
| `fsync`: `fsync-only`, `sync-stream` (`src/pager.lisp`) | `fsync` when `PRAGMA synchronous` asks | `finish-output` only | No durability barrier. A commit can be lost, or reordered with its journal, on power loss or a kernel crash. Process crashes are unaffected. |
| `ftruncate`: `stream-truncate` (`src/wal.lisp`), `VACUUM` (`src/vacuum.lisp`) | the file shrinks | the file keeps its length | Files never shrink; the trailing pages are ignored because the header says so. `-wal` files are not truncated. A disk-space cost, not a correctness one. |
| Process id: `sql-random-state` (`src/util.lisp`) | `getpid` | `0` | `random()` is not re-seeded per process when running from a saved core. |
| Float traps: `with-sql-floats` (`src/api.lisp`) | masked | `progn` | Correct as long as the implementation's floats already overflow to infinity rather than trap. |

## What is safe today, elsewhere

**One process, one thread per connection, the database used by nobody else.** Connections inside the process still coordinate through the lock table and the shared wal-index, so several connections in one single-threaded image behave as in SQLite. Both journal modes work: WAL was fixed on modus in `59a2e2e`.

## Closing the gaps

Each gap is a single call site behind a small function, so a port needs only the primitive itself:
- **modus:** its runtime already makes Linux syscalls. `fcntl(F_SETLK)` with a `struct flock`, `fsync`, `ftruncate` and `getpid` would close the first, fourth, fifth and sixth rows. The two mutexes need its thread mutex (or, for actors, the guarantee that a connection never crosses actors).
- **Other implementations:** the same four calls through their own POSIX layer.

Until a gap is closed, give the `#-sbcl` branch the conservative behavior: a lock that cannot be taken should not report success. The cross-process row is the important one. It is silent today, and its failure mode is a corrupt database rather than an error.
