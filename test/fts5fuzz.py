#!/usr/bin/env python3
"""FTS5 fuzzer: random documents and random MATCH queries, written as a
.test case file for gen-expected.py / test/differential.lisp.
    fts5fuzz.py SEED N-QUERIES OUT.test"""
import random, sys, os
seed, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
r = random.Random(seed)
VOCAB = ['alpha', 'beta', 'gamma', 'delta', 'Alpha', 'BETA', 'gam', 'gamut', 'del', 'éclair', 'eclair',
         'x', 'y', 'z', 'and', 'or', 'not', 'near', 'the', 'a', 'run', 'running', 'runs']
def doc():
    if r.random() < 0.08: return None
    words = [r.choice(VOCAB) for _ in range(r.randint(0, 14))]
    s = ''
    for w in words:
        s += w + r.choice([' ', ' ', ' ', ', ', '. ', ': ', '-'])
    return s.strip()
def q(v): return 'NULL' if v is None else "'" + v.replace("'", "''") + "'"
def term():
    w = r.choice(VOCAB[:12] + ['al', 'ga', 'de', 'ecl', 'r'])
    if r.random() < 0.25: w += '*'
    return w
def phrase():
    k = r.random()
    if k < 0.6: return term()
    if k < 0.8: return '"' + ' '.join(r.choice(VOCAB[:12]) for _ in range(r.randint(1, 3))) + '"'
    return ' + '.join(term() for _ in range(2))
def colset():
    k = r.random()
    if k < 0.5: return r.choice(['a', 'b'])
    if k < 0.7: return '{a b}'
    if k < 0.85: return '-a'
    return '-{b}'
def nearset():
    k = r.random()
    if k < 0.7: return phrase()
    if k < 0.8: return '^' + phrase()
    ps = ' '.join(phrase() for _ in range(r.randint(2, 3)))
    return 'NEAR(%s%s)' % (ps, '' if r.random() < 0.4 else ', %d' % r.randint(0, 4))
def expr(d):
    if d <= 0 or r.random() < 0.3:
        x = nearset()
        if r.random() < 0.2: x = colset() + ' : ' + x
        return x
    k = r.random()
    a, b = expr(d - 1), expr(d - 1)
    if k < 0.25: return '%s AND %s' % (a, b)
    if k < 0.5: return '%s OR %s' % (a, b)
    if k < 0.65: return '%s NOT %s' % (a, b)
    if k < 0.8: return '(%s) %s (%s)' % (a, r.choice(['AND', 'OR', 'NOT']), b)
    if k < 0.9: return '%s %s' % (a, b)
    return colset() + ' : (%s)' % a
lines = []
tables = [('t', 'fts5(a, b)'), ('p', "fts5(a, b, prefix='2 3', tokenize='porter')"),
          ('c', 'fts5(a, b, detail=column)'), ('n', 'fts5(a, b, detail=none)')]
docs = [(doc(), doc()) for _ in range(r.randint(8, 40))]
for name, spec in tables:
    lines.append('CREATE VIRTUAL TABLE %s USING %s;' % (name, spec))
    for i, (x, y) in enumerate(docs):
        lines.append('INSERT INTO %s(rowid, a, b) VALUES (%d, %s, %s);' % (name, i * 3 + 1, q(x), q(y)))
    lines.append('DELETE FROM %s WHERE rowid %% 7 = 1;' % name)
    lines.append("UPDATE %s SET a = b || ' ' || a WHERE rowid %% 5 = 2;" % name)
setup = lines
queries = []
for i in range(n):
    e = expr(r.randint(0, 3))
    name = r.choice(['t', 't', 'p', 'c', 'n'])
    ntok = r.randint(1, 8)
    if name in ('t', 'p'):
        queries.append("SELECT rowid, bm25(%s), highlight(%s, 0, '[', ']'), highlight(%s, 1, '<', '>'), "
                       "snippet(%s, -1, '[', ']', '..', %d) FROM %s WHERE %s MATCH %s ORDER BY rowid;"
                       % (name, name, name, name, ntok, name, name, q(e)))
    else:
        queries.append('SELECT rowid, bm25(%s) FROM %s WHERE %s MATCH %s ORDER BY rowid;' % (name, name, name, q(e)))
chunk = int(os.environ.get('FTS5FUZZ_CHUNK', '20'))
with open(out, 'w', encoding='utf-8') as f:
    for i in range(0, len(queries), chunk):
        f.write('== fts5fuzz%d-%d\n' % (seed, i))
        f.write('\n'.join(setup) + '\n' + '\n'.join(queries[i:i+chunk]) + '\n')
