#!/usr/bin/env python3
"""SQL-semantics fuzzer: random expressions and queries over random
mixed-type data, written as a .test case file for gen-expected.py and
test/differential.lisp.

    qfuzz.py SEED N-QUERIES OUT.test
"""
import random, sys

def rnd_value(r):
    k = r.random()
    choices = [
        lambda: 'NULL',
        lambda: str(r.randint(-10, 10)),
        lambda: str(r.choice([0, 1, -1, 2**31, -2**31, 2**53 + 1, 2**62, 9223372036854775807, -9223372036854775808])),
        lambda: repr(r.choice([0.0, -0.0, 0.5, -1.5, 1e-300, 3.14159, 1e15, 1e16, 123456.789, 2.5, 1/3, 1e100, 99.99])),
        lambda: "'" + r.choice(['', 'a', 'abc', 'ABC', ' 12 ', '12', '1e3', '3.5', '-7', 'x1', '0x10', 'é', '日本', 'a%b', 'a_c', "it''s", '  ']) + "'",
        lambda: "x'" + r.choice(['', '00', '41', '3132', 'ff00']) + "'",
    ]
    return r.choice(choices)()

COLS_A = ['x', 'y', 'z', 'w', 'v', 'u']
FUNCS1 = ['abs', 'length', 'lower', 'upper', 'typeof', 'hex', 'quote', 'trim', 'unicode', 'round', 'sign', 'ltrim', 'rtrim']
FUNCS2 = ['coalesce', 'nullif', 'ifnull', 'max', 'min', 'instr', 'round', 'substr', 'glob', 'like']
BINOPS = ['+', '-', '*', '/', '%', '||', '&', '|', '<<', '>>', '=', '!=', '<', '<=', '>', '>=', 'IS', 'IS NOT', 'AND', 'OR']
TYPES = ['INTEGER', 'REAL', 'TEXT', 'BLOB', 'NUMERIC', 'INT', 'VARCHAR(5)', 'FLOAT']

def expr(r, depth, cols):
    if depth <= 0 or r.random() < 0.25:
        return r.choice(cols) if r.random() < 0.6 else rnd_value(r)
    k = r.random()
    if k < 0.35:
        return '(%s %s %s)' % (expr(r, depth - 1, cols), r.choice(BINOPS), expr(r, depth - 1, cols))
    if k < 0.45:
        return '%s(%s)' % (r.choice(FUNCS1), expr(r, depth - 1, cols))
    if k < 0.55:
        return '%s(%s, %s)' % (r.choice(FUNCS2), expr(r, depth - 1, cols), expr(r, depth - 1, cols))
    if k < 0.62:
        return 'CAST(%s AS %s)' % (expr(r, depth - 1, cols), r.choice(TYPES))
    if k < 0.68:
        return '(-%s)' % expr(r, depth - 1, cols)
    if k < 0.72:
        return '(NOT %s)' % expr(r, depth - 1, cols)
    if k < 0.78:
        return 'CASE %s WHEN %s THEN %s ELSE %s END' % tuple(expr(r, depth - 1, cols) for _ in range(4))
    if k < 0.83:
        return '(%s BETWEEN %s AND %s)' % tuple(expr(r, depth - 1, cols) for _ in range(3))
    if k < 0.88:
        return '(%s IN (%s, %s, %s))' % tuple(expr(r, depth - 1, cols) for _ in range(4))
    if k < 0.92:
        return '(%s LIKE %s)' % (expr(r, depth - 1, cols), r.choice(["'%a%'", "'_'", "'A%'", "'%1%'", "'%'"]))
    if k < 0.95:
        return '(%s IS NULL)' % expr(r, depth - 1, cols)
    if k < 0.98:
        return 'substr(%s, %s, %s)' % tuple(expr(r, depth - 1, cols) for _ in range(3))
    return "printf('%%s|%%d|%%.3f|%%5.2e', %s, %s, %s, %s)" % tuple(expr(r, depth - 1, cols) for _ in range(4))

def main():
    seed, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    r = random.Random(seed)
    lines = ['CREATE TABLE a(x INTEGER, y TEXT, z REAL, w BLOB, v NUMERIC, u);',
             'CREATE TABLE b(k, x INTEGER);',
             'CREATE INDEX a_x ON a(x);',
             'CREATE INDEX a_y ON a(y COLLATE NOCASE);',
             'CREATE INDEX b_k ON b(k);']
    for _ in range(r.randint(10, 30)):
        lines.append('INSERT INTO a VALUES (%s);' % ', '.join(rnd_value(r) for _ in COLS_A))
    for _ in range(r.randint(5, 15)):
        lines.append('INSERT INTO b VALUES (%s, %s);' % (rnd_value(r), rnd_value(r)))
    setup = lines
    lines = []
    queries = []
    for qi in range(n):
        lines = queries
        k = r.random()
        if k < 0.45:
            lines.append('SELECT %s, %s FROM a ORDER BY rowid;' % (expr(r, 3, COLS_A), expr(r, 3, COLS_A)))
        elif k < 0.7:
            lines.append('SELECT rowid FROM a WHERE %s ORDER BY rowid;' % expr(r, 3, COLS_A))
        elif k < 0.8:
            agg = r.choice(['count(%s)', 'sum(%s)', 'total(%s)', 'avg(%s)', 'min(%s)', 'max(%s)',
                            'group_concat(%s)', 'count(DISTINCT %s)'])
            e = expr(r, 2, COLS_A)
            if r.random() < 0.5:
                lines.append('SELECT %s FROM a;' % (agg % e))
            else:
                g = expr(r, 1, COLS_A)
                lines.append('SELECT %s, %s FROM a GROUP BY 1;' % (g, agg % e))
        elif k < 0.9:
            lines.append('SELECT a.rowid, b.rowid FROM a JOIN b ON %s ORDER BY 1, 2;'
                         % expr(r, 2, ['a.x', 'a.y', 'a.z', 'a.v', 'b.k', 'b.x']))
        else:
            c = r.choice(['x', 'y', 'v', 'u'])
            lines.append('SELECT DISTINCT %s FROM a ORDER BY 1;' % c if r.random() < 0.5
                         else 'SELECT %s FROM a ORDER BY %s, rowid;' % (c, c))
    with open(out, 'w', encoding='utf-8') as f:
        for i, q in enumerate(queries):
            f.write('== q%d-%d\n' % (seed, i))
            f.write('\n'.join(setup) + '\n' + q + '\n')

main()
