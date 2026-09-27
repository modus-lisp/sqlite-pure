#!/usr/bin/env python3
"""FTS3/4 fuzzer: random documents and random MATCH queries, written as a
.test case file for gen-expected.py / test/differential.lisp.  Each query
row carries snippet(), offsets() and matchinfo() output.
    fts3fuzz.py SEED N-QUERIES OUT.test"""
import random, sys, os
seed, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
r = random.Random(seed)
VOCAB = ['alpha', 'beta', 'gamma', 'delta', 'Alpha', 'BETA', 'gam', 'gamut', 'del', 'éclair', 'eclair',
         'x', 'y', 'z', 'and', 'or', 'not', 'near', 'the', 'a', 'run', 'running', 'runs', 'AND', 'OR', 'NEAR']
def doc():
    if r.random() < 0.08: return None
    words = [r.choice(VOCAB) for _ in range(r.randint(0, 16))]
    s = ''
    for w in words:
        s += w + r.choice([' ', ' ', ' ', ', ', '. ', ': ', '-'])
    return s.strip()
def q(v): return 'NULL' if v is None else "'" + v.replace("'", "''") + "'"
def term():
    w = r.choice(VOCAB[:12] + ['al', 'ga', 'de', 'ecl', 'r', 'x'])
    if r.random() < 0.25: w += '*'
    if r.random() < 0.08: w = '^' + w
    return w
def phrase():
    k = r.random()
    if k < 0.6: p = term()
    elif k < 0.85: p = '"' + ' '.join(r.choice(VOCAB[:12] + ['r*', 'ga*']) for _ in range(r.randint(1, 3))) + '"'
    elif k < 0.9: p = '""'
    else: p = '"^' + r.choice(VOCAB[:12]) + ' ' + r.choice(VOCAB[:12]) + '"'
    if r.random() < 0.15: p = r.choice(['a', 'b', 'A']) + ':' + p
    return p
def nearchain():
    ps = [phrase() for _ in range(r.randint(2, 3))]
    s = ps[0]
    for p in ps[1:]:
        s += ' NEAR' + ('' if r.random() < 0.4 else '/%d' % r.randint(0, 4)) + ' ' + p
    return s
def expr(d):
    if d <= 0 or r.random() < 0.3:
        return nearchain() if r.random() < 0.2 else phrase()
    k = r.random()
    a, b = expr(d - 1), expr(d - 1)
    if k < 0.25: return '%s AND %s' % (a, b)
    if k < 0.5: return '%s OR %s' % (a, b)
    if k < 0.65: return '%s NOT %s' % (a, b)
    if k < 0.85: return '(%s) %s (%s)' % (a, r.choice(['AND', 'OR', 'NOT']), b)
    if k < 0.95: return '%s %s' % (a, b)
    return r.choice(['%s -%s', '(%s %s', '%s %s)', 'AND %s %s', '%s () %s']) % (a, b) if r.random() < 0.5 else '%s %s' % (a, b)
tables = [('t', 'fts3(a, b)', False), ('f', 'fts4(a, b)', True),
          ('p', "fts4(a, b, prefix='2,3', tokenize=porter)", True),
          ('d', 'fts4(a, b, order=desc)', True),
          ('u', 'fts4(a, b, tokenize=unicode61)', True)]
docs = [(doc(), doc()) for _ in range(r.randint(8, 40))]
def longdoc():
    return ' '.join(r.choice(VOCAB) + r.choice(['', '', ',', '.']) for _ in range(r.randint(20, 150)))
longdocs = [(longdoc(), longdoc() if r.random() < 0.7 else None) for _ in range(r.randint(3, 12))]
lines = []
lines.append('CREATE VIRTUAL TABLE l USING fts4(a, b);')
for i, (x, y) in enumerate(longdocs):
    lines.append('INSERT INTO l(docid, a, b) VALUES (%d, %s, %s);' % (i * 1000003 - 4000000, q(x), q(y)))
for name, spec, fts4 in tables:
    lines.append('CREATE VIRTUAL TABLE %s USING %s;' % (name, spec))
    for i, (x, y) in enumerate(docs):
        lines.append('INSERT INTO %s(docid, a, b) VALUES (%d, %s, %s);' % (name, i * 3 + 1, q(x), q(y)))
    lines.append('DELETE FROM %s WHERE docid %% 7 = 1;' % name)
    lines.append("UPDATE %s SET a = b || ' ' || a WHERE docid %% 5 = 2;" % name)
setup = lines
queries = []
for i in range(n):
    e = expr(r.randint(0, 3))
    name, spec, fts4 = r.choice(tables + [('l', 'fts4(a, b)', True)] * 2)
    ntok = r.choice([1, 2, 3, 5, 8, 15, -2, -5])
    col = r.choice([-1, -1, 0, 1])
    fmt = r.choice(['pcx', 'pcnalsxyb', 'y', 'b', 'sx', 'x', 'pc']) if fts4 else r.choice(['pcx', 'y', 'b', 'sx', 'x', 'pcsyb'])
    order = ' ORDER BY docid DESC' if r.random() < 0.1 else ''
    queries.append("SELECT docid, snippet(%s, '[', ']', '..', %d, %d), offsets(%s), hex(matchinfo(%s, '%s')) "
                   "FROM %s WHERE %s MATCH %s%s;" % (name, col, ntok, name, name, fmt, name, name, q(e), order))
chunk = int(os.environ.get('FTS3FUZZ_CHUNK', '20'))
with open(out, 'w', encoding='utf-8') as f:
    for i in range(0, len(queries), chunk):
        f.write('== fts3fuzz%d-%d\n' % (seed, i))
        f.write('\n'.join(setup) + '\n' + '\n'.join(queries[i:i+chunk]) + '\n')
