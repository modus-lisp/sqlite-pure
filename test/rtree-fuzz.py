#!/usr/bin/env python3
"""R-tree structure against SQLite: random rtree / rtree_i32 tables (1-5
dimensions, auxiliary columns, three page sizes) under random inserts,
deletes, updates, REPLACEs, rowid changes, rolled-back transactions and DDL.
After every statement the _node, _parent and _rowid tables must be byte for
byte the ones SQLite leaves.  Usage: rtree-fuzz.py FIRST-SEED N WORKDIR"""
import sqlite3, random, subprocess, sys, os, hashlib

here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
first, n, work = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
os.makedirs(work, exist_ok=True)

def gen(seed):
    random.seed(seed)
    nd = random.randint(1, 5); intp = random.random() < 0.3; naux = random.randint(0, 2)
    cols = ['id'] + ['c%d' % i for i in range(2 * nd)] + ['+a%d' % i for i in range(naux)]
    out = ['PRAGMA page_size=%d;' % random.choice([512, 1024, 4096]),
           'CREATE VIRTUAL TABLE r USING %s(%s);' % ('rtree_i32' if intp else 'rtree', ', '.join(cols))]
    def box():
        v = []
        for d in range(nd):
            if intp:
                a = random.randint(-1000, 1000); b = a + random.randint(0, 50)
            else:
                a = round(random.uniform(-1000, 1000), random.randint(0, 3))
                b = round(a + random.uniform(0, random.choice([1, 10, 100])), random.randint(0, 3))
            v += [a, b]
        return v
    def vals(i):
        return ', '.join(str(x) for x in [i] + box() + ["'x%d'" % random.randint(0, 9)] * naux)
    nextid = 1
    for step in range(random.randint(30, 70)):
        r = random.random()
        if r < 0.35:
            rows = []
            for _ in range(random.randint(1, 120)):
                rows.append('(%s)' % vals(nextid if random.random() < 0.9 else 'NULL'))
                nextid += random.randint(1, 3)
            out.append('INSERT INTO r VALUES %s;' % ', '.join(rows))
        elif r < 0.5:
            out.append('DELETE FROM r WHERE id %% %d = %d;' % (random.randint(2, 9), random.randint(0, 1)))
        elif r < 0.6:
            out.append('DELETE FROM r WHERE id = %d;' % random.randint(1, nextid))
        elif r < 0.7:
            d = random.randint(0, nd - 1)
            out.append('UPDATE r SET c%d = c%d - %d, c%d = c%d + %d WHERE id %% %d = 1;'
                       % (2*d, 2*d, random.randint(1, 30), 2*d+1, 2*d+1, random.randint(1, 30), random.randint(3, 7)))
        elif r < 0.78:
            out.append('INSERT OR REPLACE INTO r VALUES (%s);' % vals(random.randint(1, nextid)))
        elif r < 0.84:
            out.append('DELETE FROM r WHERE c0 < %d;' % random.randint(-1000, -600))
        elif r < 0.9:
            out.append('UPDATE r SET id = id + 100000 WHERE id %% 11 = %d;' % random.randint(0, 10))
        elif r < 0.95:
            out += ['BEGIN;', 'INSERT INTO r VALUES (%s);' % vals(nextid),
                    'DELETE FROM r WHERE id % 13 = 5;', random.choice(['COMMIT;', 'ROLLBACK;'])]
            nextid += 1
        else:
            out.append('CREATE TABLE IF NOT EXISTS z%d(a);' % random.randint(0, 3))
    return out

def sqlite_dumps(stmts):
    c = sqlite3.connect(':memory:', isolation_level=None)
    res = []
    for s in stmts:
        try:
            c.execute(s); err = ''
        except Exception:
            err = 'ERR'
        try:
            d = ''.join('%d:%s;' % r for r in c.execute('SELECT nodeno, hex(data) FROM r_node ORDER BY 1'))
            d += ''.join('%d>%d;' % r for r in c.execute('SELECT nodeno, parentnode FROM r_parent ORDER BY 1'))
            d += ''.join('%d@%d;' % r for r in c.execute('SELECT rowid, nodeno FROM r_rowid ORDER BY 1'))
        except Exception:
            d = ''
        res.append(err + d)
    return res

seeds = list(range(first, first + n))
for seed in seeds:
    open(os.path.join(work, 's%d.sql' % seed), 'w').write('\n'.join(gen(seed)) + '\n')
forms = ' '.join('(sqlite-pure.test::rtree-step-dumps "%s/s%d.sql" "%s/s%d.out" "r")' % (work, s, work, s) for s in seeds)
subprocess.run(['sbcl', '--noinform', '--non-interactive', '--no-userinit',
                '--eval', '(require :asdf)',
                '--eval', '(push #p"%s/" asdf:*central-registry*)' % root,
                '--eval', '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))',
                '--load', os.path.join(here, 'differential.lisp'), '--load', os.path.join(here, 'rtree.lisp'),
                '--eval', '(progn %s)' % forms], check=True, stdout=subprocess.DEVNULL)
failed = 0
for seed in seeds:
    stmts = gen(seed)
    want = sqlite_dumps(stmts)
    got = [l.rstrip('\n') for l in open(os.path.join(work, 's%d.out' % seed))]
    bad = next((i for i, (a, b) in enumerate(zip(want, got)) if a != b), None)
    if bad is None and len(want) != len(got): bad = min(len(want), len(got))
    if bad is None:
        print('ok   seed %d: %d statements, %d nodes at the end' % (seed, len(stmts), want[-1].count(':')))
    else:
        failed += 1
        print('FAIL seed %d: tables differ after statement %d: %s' % (seed, bad + 1, stmts[bad][:100]))
print('rtree structure: %d of %d seeds failed' % (failed, len(seeds)))
sys.exit(1 if failed else 0)
