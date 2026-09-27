#!/usr/bin/env python3
"""Geopoly against SQLite, bit for bit.  Run through test/run-geopoly.sh,
which puts a geopoly-enabled libsqlite3 (test/build-oracle.sh) on
LD_LIBRARY_PATH.

  1. every geopoly function on random polygons (JSON text with awkward
     numbers, regular polygons) and random transform/point arguments;
     results must be identical, floats to the last bit
  2. a geopoly table built and churned by SQLite, queried and modified by
     us, then queried by SQLite again"""
import sqlite3, random, struct, subprocess, sys, os

here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
work = sys.argv[1]
os.makedirs(work, exist_ok=True)

def canon(v):
    if v is None: return 'n'
    if isinstance(v, int): return 'i:%d' % v
    if isinstance(v, float): return 'f:%016X' % struct.unpack('<Q', struct.pack('<d', v))[0]
    if isinstance(v, str): return 's:' + v.encode().hex().upper()
    return 'b:' + bytes(v).hex().upper()

def oracle(db, stmts):
    c = sqlite3.connect(db, isolation_level=None)
    out = []
    for s in stmts:
        try:
            rows = c.execute(s).fetchall()
            out.append([canon(x) for x in rows[0]] if rows else [])
        except Exception as e:
            out.append(['ERR %s' % e])
    c.close()
    return out

def ours(db, stmts):
    qf, of = os.path.join(work, 'q.sql'), os.path.join(work, 'u.txt')
    open(qf, 'w').write(''.join(s + '\n' for s in stmts))
    subprocess.run(['sbcl', '--noinform', '--non-interactive', '--no-userinit',
                    '--eval', '(require :asdf)',
                    '--eval', '(push #p"%s/" asdf:*central-registry*)' % root,
                    '--eval', '(handler-bind ((warning (function muffle-warning))) (asdf:load-system "sqlite-pure"))',
                    '--load', os.path.join(here, 'differential.lisp'),
                    '--load', os.path.join(here, 'geopoly.lisp'),
                    '--eval', '(sqlite-pure.test::geo-run-file "%s" "%s" "%s")' % (db, qf, of)],
                   check=True, stdout=subprocess.DEVNULL)
    return [[x for x in l.rstrip('\n').split('\t') if x] for l in open(of)]

failed = 0
def check(name, got, want):
    global failed
    bad = [i for i, (g, w) in enumerate(zip(got, want)) if g != w]
    if len(got) != len(want): bad.append(min(len(got), len(want)))
    print('%s %s%s' % ('ok  ' if not bad else 'FAIL', name, '' if not bad else ' (%d of %d differ)' % (len(bad), len(want))))
    for i in bad[:3]:
        print('       want', want[i] if i < len(want) else None)
        print('       got ', got[i] if i < len(got) else None)
    failed += bool(bad)

random.seed(1)
def num():
    r = random.random()
    if r < 0.3: return str(random.randint(-20, 20))
    if r < 0.6: return repr(round(random.uniform(-50, 50), random.randint(0, 6)))
    if r < 0.8: return '%.9g' % random.uniform(-1e4, 1e4)
    return '%se%d' % (random.choice(['1', '-2.5', '3.25', '0.1']), random.randint(-8, 8))
def poly():
    n = random.randint(3, 9)
    if random.random() < 0.5:
        return "geopoly_regular(%r,%r,%r,%d)" % (random.uniform(-5, 5), random.uniform(-5, 5), random.uniform(0.1, 4), n)
    pts = [(num(), num()) for _ in range(n)]
    pts.append(pts[0])
    return "'[" + ",".join("[%s,%s]" % p for p in pts) + "]'"

# 1. the functions
stmts = []
for i in range(2000):
    a, b = poly(), poly()
    stmts.append(("SELECT %d, geopoly_area(%s), geopoly_json(%s), geopoly_overlap(%s,%s), geopoly_within(%s,%s), "
                  "geopoly_contains_point(%s,%s,%s), geopoly_json(geopoly_ccw(%s)), "
                  "geopoly_json(geopoly_xform(%s,%s,%s,%s,%s,%s,%s)), geopoly_svg(%s), geopoly_json(geopoly_bbox(%s)), "
                  "hex(geopoly_blob(%s)), geopoly_contains_point(%s, %s, %s)")
                 % (i, a, a, a, b, a, b, a, num(), num(), a, a, num(), num(), num(), num(), num(), num(), b, b, b,
                    b, random.uniform(-6, 6), random.uniform(-6, 6)))
check('2000 random function calls, bit for bit', ours(':memory:', stmts), oracle(':memory:', stmts))

# 2. a table shared through the file
path = os.path.join(work, 'g.db')
if os.path.exists(path): os.remove(path)
c = sqlite3.connect(path)
c.execute('create virtual table g using geopoly(tag, n)')
for i in range(1, 3001):
    c.execute('insert into g(_shape, tag, n) values(geopoly_regular(?, ?, ?, ?), ?, ?)',
              (random.uniform(0, 1000), random.uniform(0, 1000), random.uniform(0.5, 20), random.randint(3, 12), 't%d' % i, i))
c.execute('delete from g where n % 7 = 3')
c.execute("update g set _shape = geopoly_xform(_shape, 1, 0, 0, 1, 50, -20), tag = 'moved' where n % 13 = 4")
c.commit(); c.close()
queries = ["SELECT count(*), sum(n) FROM g WHERE geopoly_overlap(_shape, geopoly_regular(%d, %d, %d, 7))" % (x, y, r)
           for x, y, r in [(500, 500, 120), (0, 0, 300), (990, 10, 40), (250, 750, 5)]]
queries += ["SELECT count(*), sum(n) FROM g WHERE geopoly_within(_shape, geopoly_regular(%d, %d, %d, 12))" % (x, y, r)
            for x, y, r in [(500, 500, 300), (200, 200, 100)]]
queries += ["SELECT count(*), sum(n), total(geopoly_area(_shape)) FROM g",
            "SELECT count(*) FROM g WHERE tag = 'moved'",
            "SELECT group_concat(n || ':' || hex(_shape), ',') FROM (SELECT n, _shape FROM g WHERE rowid IN (5, 77, 1500, 2999) ORDER BY n)",
            "SELECT hex(geopoly_group_bbox(_shape)) FROM g",
            "SELECT (SELECT count(*) FROM g_rowid), (SELECT count(*) FROM g_node) - (SELECT count(*) FROM g_parent)"]
check('we read the table SQLite built', ours(path, queries), oracle(path, queries))
changes = ["DELETE FROM g WHERE n % 5 = 1",
           "UPDATE g SET _shape = geopoly_xform(_shape, 1, 0, 0, 1, 3, 4), tag = 'ours' WHERE n % 11 = 2",
           "UPDATE g SET n = n + 100000 WHERE n % 17 = 3",
           "INSERT INTO g(_shape, tag, n) SELECT geopoly_regular(n % 900, n % 700, 5, 6), 'new', n + 10000 FROM g WHERE n < 600",
           "INSERT OR REPLACE INTO g(rowid, _shape, tag, n) VALUES (10, '[[1,1],[2,1],[2,2],[1,1]]', 'replaced', -1)"]
ours(path, changes)
check('SQLite reads our changes', oracle(path, queries), ours(path, queries))
print('geopoly: %d failed' % failed)
sys.exit(1 if failed else 0)
