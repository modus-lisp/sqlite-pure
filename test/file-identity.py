#!/usr/bin/env python3
"""The database file, byte for byte, against SQLite.  Random workloads --
rowid, WITHOUT ROWID and rowid-less tables, indexes (unique, multi-column,
partial, expression), values from tiny to several overflow pages, INSERT OR
REPLACE / IGNORE, UPSERT, UPDATE (rowid changes included), DELETE, CREATE and
DROP of tables and indexes, rolled-back transactions, auto-vacuum (FULL and
INCREMENTAL, with incremental_vacuum) and VACUUM, at three page sizes -- run
by SQLite and by this library into two files; after every statement the two
files must be identical.  Usage: file-identity.py FIRST N WORKDIR"""
import sqlite3, random, subprocess, sys, os, hashlib

here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
first, n, work = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
os.makedirs(work, exist_ok=True)

def gen(seed):
    random.seed(seed)
    opts = random.choice(['', '', 'av', 'vac'])
    out = ['PRAGMA page_size=%d;' % random.choice([512, 1024, 4096])]
    if opts == 'av':
        out.append('PRAGMA auto_vacuum=%s;' % random.choice(['FULL', 'INCREMENTAL']))
    tables = {}
    def val():
        r = random.random()
        if r < 0.3: return str(random.randint(-1000, 100000))
        if r < 0.5: return "'%s'" % ('v%d' % random.randint(0, 500) * random.randint(1, 4))
        if r < 0.65: return "zeroblob(%d)" % random.choice([10, 100, 600, 1500, 5000])
        if r < 0.8: return "printf('%%.*c', %d, 'x')" % random.randint(0, 3000)
        if r < 0.9: return repr(random.uniform(-100, 100))
        return 'NULL'
    def mk_table():
        name = 't%d' % len(tables)
        kind = random.random()
        if kind < 0.6:
            out.append('CREATE TABLE %s(a INTEGER PRIMARY KEY, b, c, d);' % name); tables[name] = 'rowid'
        elif kind < 0.8:
            out.append('CREATE TABLE %s(a, b, c, d);' % name); tables[name] = 'plain'
        else:
            out.append('CREATE TABLE %s(a, b, c, d, PRIMARY KEY(a, b)) WITHOUT ROWID;' % name); tables[name] = 'wr'
    mk_table()
    nid = 1
    for step in range(random.randint(25, 60)):
        t = random.choice(list(tables))
        wr = tables[t] == 'wr'
        r = random.random()
        if r < 0.3:
            rows = []
            for _ in range(random.randint(1, 60)):
                a = str(nid) if random.random() < 0.8 else str(random.randint(1, nid + 5))
                nid += random.randint(1, 4)
                rows.append('(%s, %s, %s, %s)' % (a, str(random.randint(0, 20)) if wr else val(), val(), val()))
            out.append('INSERT OR %s INTO %s VALUES %s;' % (random.choice(['REPLACE', 'IGNORE']), t, ', '.join(rows)))
        elif r < 0.38:
            out.append("WITH RECURSIVE q(i) AS (SELECT 1 UNION ALL SELECT i+1 FROM q WHERE i<%d) "
                       "INSERT OR IGNORE INTO %s SELECT %d+i, %s, printf('%%.*c', i*%d %% 2000, 'y'), i FROM q;"
                       % (random.randint(50, 400), t, nid, 'i%7' if wr else "'k'||(i*13%101)", random.randint(1, 97)))
            nid += 500
        elif r < 0.5:
            out.append('DELETE FROM %s WHERE a %% %d = %d;' % (t, random.randint(2, 9), random.randint(0, 2)))
        elif r < 0.62:
            col = random.choice(['c', 'd'] if wr else ['b', 'c', 'd'])
            out.append('UPDATE %s SET %s = %s WHERE a %% %d = %d;' % (t, col, val(), random.randint(2, 7), random.randint(0, 1)))
        elif r < 0.66:
            out.append(("UPDATE %s SET d = 7 WHERE a %% 3 = 0;" if wr else "UPDATE %s SET c = c || 'z' WHERE rowid %% 3 = 0;") % t)
        elif r < 0.7 and tables[t] == 'rowid':
            out.append('UPDATE %s SET a = a + 100000 WHERE a %% 11 = %d;' % (t, random.randint(0, 10)))
        elif r < 0.78 and not wr:
            # (secondary indexes on WITHOUT ROWID tables change SQLite's
            # choice of scan for DELETE/UPDATE: a query-planner question)
            kind = random.choice(['(b)', '(c, d)', '(d) WHERE d IS NOT NULL', '(length(c))', '(b, c)'])
            out.append('CREATE %sINDEX IF NOT EXISTS i%d ON %s%s;' % ('UNIQUE ' if random.random() < 0.2 else '', random.randint(0, 9), t, kind))
        elif r < 0.82:
            out.append('DROP INDEX IF EXISTS i%d;' % random.randint(0, 9))
        elif r < 0.86 and len(tables) < 4:
            mk_table()
        elif r < 0.88 and len(tables) > 1:
            d = random.choice(list(tables)); del tables[d]; out.append('DROP TABLE %s;' % d)
        elif r < 0.92:
            out += ['BEGIN;', 'INSERT OR IGNORE INTO %s VALUES (%d, %s, %s, %s);' % (t, nid, '1' if wr else val(), val(), val()),
                    'DELETE FROM %s WHERE a %% 13 = 5;' % t, random.choice(['COMMIT;', 'ROLLBACK;'])]
            nid += 1
        elif r < 0.94 and opts == 'av':
            out.append('PRAGMA incremental_vacuum(%d);' % random.randint(0, 20))
        elif r < 0.95 and opts == 'vac':
            out.append('VACUUM;')
        elif r < 0.97 and tables[t] == 'rowid':
            out.append("INSERT INTO %s VALUES (%d, 'u', 1, 2) ON CONFLICT(a) DO UPDATE SET c = excluded.c || c;" % (t, random.randint(1, nid)))
        else:
            out.append(('DELETE FROM %s WHERE b = %d;' % (t, random.randint(0, 20))) if wr else
                       ('DELETE FROM %s WHERE rowid IN (SELECT rowid FROM %s ORDER BY rowid DESC LIMIT %d);' % (t, t, random.randint(1, 30))))
    return out

def sqlite_hashes(stmts, path):
    if os.path.exists(path): os.remove(path)
    c = sqlite3.connect(path, isolation_level=None)
    res = []
    for s in stmts:
        try:
            # (a pragma whose result row has no columns is stepped only once
            # by execute(); executescript() runs it to the end, as SQLite's
            # shell would)
            if 'incremental_vacuum' in s: c.executescript(s)
            else: c.execute(s).fetchall()
            err = ''
        except Exception:
            err = 'ERR'
        res.append(err + hashlib.md5(open(path, 'rb').read()).hexdigest())
    c.close()
    return res

seeds = list(range(first, first + n))
for seed in seeds:
    open(os.path.join(work, 's%d.sql' % seed), 'w').write('\n'.join(gen(seed)) + '\n')
forms = ' '.join('(sqlite-pure.test::file-step-hashes "%s/s%d.sql" "%s/u%d.db" "%s/s%d.out")' % (work, s, work, s, work, s) for s in seeds)
subprocess.run(['sbcl', '--noinform', '--non-interactive', '--no-userinit',
                '--eval', '(require :asdf)',
                '--eval', '(push #p"%s/" asdf:*central-registry*)' % root,
                '--eval', '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))',
                '--load', os.path.join(here, 'differential.lisp'), '--load', os.path.join(here, 'file-identity.lisp'),
                '--eval', '(progn %s)' % forms], check=True, stdout=subprocess.DEVNULL)
failed = 0
for seed in seeds:
    stmts = gen(seed)
    want = sqlite_hashes(stmts, os.path.join(work, 'o%d.db' % seed))
    got = [l.rstrip('\n') for l in open(os.path.join(work, 's%d.out' % seed))]
    bad = next((i for i, (a, b) in enumerate(zip(want, got)) if a != b), None)
    if bad is None and len(want) != len(got): bad = min(len(want), len(got))
    if bad is None:
        print('ok   seed %d: %d statements, %d bytes' % (seed, len(stmts), os.path.getsize(os.path.join(work, 'o%d.db' % seed))))
    else:
        failed += 1
        print('FAIL seed %d: files differ after statement %d: %s' % (seed, bad + 1, stmts[bad][:120]))
print('file identity: %d of %d seeds failed' % (failed, len(seeds)))
sys.exit(1 if failed else 0)
