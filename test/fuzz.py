#!/usr/bin/env python3
"""File-format fuzzer: a random but deterministic workload of DDL/DML is
run by real SQLite (reference database) and by sqlite-pure (subject
database).  Then:

  1. SQLite runs PRAGMA integrity_check on the file sqlite-pure wrote;
  2. the two files' contents must be identical (compared through SQLite);
  3. sqlite-pure's reading of the *reference* file must match SQLite's.

Usage:  fuzz.py gen SEED DIR     write DIR/work.sql and DIR/ref.db
        fuzz.py check DIR        compare DIR/ref.db, DIR/sub.db, DIR/sub-read-ref.txt
"""
import sqlite3, random, sys, os, struct

def canon(v):
    if v is None: return 'N'
    if isinstance(v, int): return 'I%d' % v
    if isinstance(v, float): return 'R' + struct.pack('>d', v).hex()
    if isinstance(v, str): return 'T' + v.encode('utf-8').hex()
    return 'B' + bytes(v).hex()

def dump(con):
    lines = []
    tables = [r[0] for r in con.execute(
        "select name from sqlite_schema where type='table' order by name")]
    for t in tables:
        wr = con.execute("select sql from sqlite_schema where name=?", (t,)).fetchone()[0]
        order = 'rowid' if 'WITHOUT ROWID' not in wr.upper() else '1, 2'
        cols = [r[1] for r in con.execute('pragma table_info("%s")' % t)]
        sel = ', '.join('"%s"' % c for c in cols)
        if 'WITHOUT ROWID' not in wr.upper():
            sel = 'rowid, ' + sel
        lines.append('table ' + t)
        for row in con.execute('select %s from "%s" order by %s' % (sel, t, order)):
            lines.append(' '.join(canon(v) for v in row))
    return '\n'.join(lines) + '\n'

def rand_text(r):
    k = r.random()
    if k < 0.6: n = r.randint(0, 20)
    elif k < 0.9: n = r.randint(20, 3000)
    else: n = r.randint(3000, 40000)
    alphabet = 'abcdefghijklmnopqrstuvwxyz ' + 'éß日本😀'
    return ''.join(r.choice(alphabet) for _ in range(n))

def lit(v):
    if v is None: return 'NULL'
    if isinstance(v, int): return str(v)
    if isinstance(v, float): return repr(v)
    if isinstance(v, str): return "'" + v.replace("'", "''") + "'"
    return "x'" + bytes(v).hex() + "'"

def rand_value(r, kind):
    k = r.random()
    if k < 0.08: return None
    if kind == 'int' or (kind == 'any' and k < 0.35):
        return r.choice([r.randint(-5, 50), r.randint(-2**40, 2**40), r.randint(-2**63, 2**63 - 1)])
    if kind == 'real' or (kind == 'any' and k < 0.5):
        return r.choice([r.uniform(-1e6, 1e6), float(r.randint(-100, 100)), r.uniform(-1, 1) * 10 ** r.randint(-300, 300)])
    if kind == 'blob' or (kind == 'any' and k < 0.6):
        n = r.choice([0, 1, 10, 500, 5000, 70000]) if r.random() < 0.3 else r.randint(0, 64)
        return bytes(r.getrandbits(8) for _ in range(n))
    return rand_text(r)

SCHEMAS = [
    ('t1', 'CREATE TABLE t1(id INTEGER PRIMARY KEY, a TEXT, b INTEGER, c BLOB, d)',
     ['a:text', 'b:int', 'c:blob', 'd:any'], ['CREATE INDEX t1a ON t1(a)', 'CREATE INDEX t1bd ON t1(b, d DESC)']),
    ('t2', 'CREATE TABLE t2(k TEXT UNIQUE, v REAL, w NUMERIC, x)',
     ['k:text', 'v:real', 'w:any', 'x:any'], ['CREATE INDEX t2vw ON t2(v, w)']),
    ('t3', 'CREATE TABLE t3(p INTEGER, q TEXT, r, PRIMARY KEY (p, q)) WITHOUT ROWID',
     ['p:int', 'q:text', 'r:any'], ['CREATE INDEX t3r ON t3(r)']),
    ('t4', 'CREATE TABLE t4(id INTEGER PRIMARY KEY AUTOINCREMENT, s TEXT NOT NULL, n INTEGER CHECK (n IS NULL OR n > -1000000000000000000))',
     ['s:text', 'n:int'], []),
]

def gen(seed, outdir):
    r = random.Random(seed)
    stmts = []
    live = {}
    for name, ddl, cols, idxs in SCHEMAS:
        if r.random() < 0.85:
            stmts.append(ddl)
            live[name] = (cols, idxs)
            for i in idxs:
                if r.random() < 0.6:
                    stmts.append(i)
    names = list(live)
    for _ in range(r.randint(50, 400)):
        if not names: break
        t = r.choice(names)
        cols, idxs = live[t]
        op = r.random()
        if op < 0.5:
            nrows = r.choice([1, 1, 1, 3, 10, 40])
            rows = []
            for _ in range(nrows):
                vals = []
                for c in cols:
                    n, kind = c.split(':')
                    v = rand_value(r, kind)
                    if kind == 'text' and n in ('k', 'q', 'a') and r.random() < 0.7:
                        v = 'k%d' % r.randint(0, 300)
                    if n == 's' and v is None: v = 'x'
                    if n == 'p' and v is None and r.random() < 0.9: v = r.randint(0, 50)
                    vals.append(lit(v))
                rows.append('(' + ', '.join(vals) + ')')
            verb = r.choice(['INSERT', 'INSERT', 'INSERT OR REPLACE', 'INSERT OR IGNORE'])
            stmts.append('%s INTO %s(%s) VALUES %s' % (
                verb, t, ', '.join(c.split(':')[0] for c in cols), ', '.join(rows)))
        elif op < 0.75:
            c = r.choice(cols)
            n, kind = c.split(':')
            w = r.choice(cols).split(':')[0]
            stmts.append('UPDATE %s%s SET %s = %s WHERE %s %s' % (
                r.choice(['', ' OR REPLACE', ' OR IGNORE']), t, n, lit(rand_value(r, kind)), w,
                r.choice(['IS NULL', '> %d' % r.randint(-10, 40), "LIKE 'k1%'", '= %d' % r.randint(0, 50)])))
        elif op < 0.93:
            w = r.choice(cols).split(':')[0]
            if t != 't3' and r.random() < 0.4:
                lo = r.randint(0, 400)
                stmts.append('DELETE FROM %s WHERE rowid BETWEEN %d AND %d' % (t, lo, lo + r.randint(0, 60)))
            else:
                stmts.append('DELETE FROM %s WHERE %s %s' % (t, w,
                    r.choice(['IS NULL', '< %d' % r.randint(-10, 40), "LIKE 'k2%'", "GLOB '*a*'"])))
        elif op < 0.95:
            stmts.append('DELETE FROM %s' % t)
        elif op < 0.97 and idxs:
            i = r.choice(idxs)
            iname = i.split()[2]
            stmts.append('DROP INDEX IF EXISTS %s' % iname)
            stmts.append(i.replace('CREATE INDEX', 'CREATE INDEX IF NOT EXISTS'))
        else:
            stmts.append('BEGIN')
            stmts.append('INSERT INTO %s(%s) VALUES (%s)' % (
                t, cols[0].split(':')[0], lit('rolled-back' if 'text' in cols[0] else 123456)))
            stmts.append(r.choice(['ROLLBACK', 'COMMIT']))
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, 'work.sql'), 'w', encoding='utf-8') as f:
        for s in stmts:
            f.write(s + ';\n')
    ref = os.path.join(outdir, 'ref.db')
    if os.path.exists(ref): os.remove(ref)
    con = sqlite3.connect(ref, isolation_level=None)
    errs = 0
    for s in stmts:
        try: con.execute(s)
        except sqlite3.Error: errs += 1
    con.close()
    print('seed %d: %d statements, %d rejected by sqlite' % (seed, len(stmts), errs))

def check(outdir):
    ok = True
    sub = sqlite3.connect(os.path.join(outdir, 'sub.db'))
    ic = sub.execute('pragma integrity_check').fetchall()
    if ic != [('ok',)]:
        print('INTEGRITY FAIL', ic[:10]); ok = False
    ref = sqlite3.connect(os.path.join(outdir, 'ref.db'))
    a, b = dump(ref), dump(sub)
    if a != b:
        ok = False
        al, bl = a.splitlines(), b.splitlines()
        for i, (x, y) in enumerate(zip(al, bl)):
            if x != y:
                print('CONTENT DIFF at line %d\n  ref %s\n  sub %s' % (i, x[:200], y[:200])); break
        else:
            print('CONTENT DIFF: %d vs %d lines' % (len(al), len(bl)))
    lisp_view = open(os.path.join(outdir, 'sub-read-ref.txt'), encoding='utf-8').read()
    if lisp_view != a:
        ok = False
        al, bl = a.splitlines(), lisp_view.splitlines()
        for i, (x, y) in enumerate(zip(al, bl)):
            if x != y:
                print('READ DIFF at line %d\n  sqlite %s\n  lisp   %s' % (i, x[:200], y[:200])); break
        else:
            print('READ DIFF: %d vs %d lines' % (len(al), len(bl)))
    print('PASS' if ok else 'FAIL')
    return ok

if __name__ == '__main__':
    if sys.argv[1] == 'gen':
        gen(int(sys.argv[2]), sys.argv[3])
    else:
        sys.exit(0 if check(sys.argv[2]) else 1)
