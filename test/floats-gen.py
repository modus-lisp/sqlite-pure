#!/usr/bin/env python3
"""Float round-trip checks against SQLite: `floats-gen.py SEED DIR` writes
DIR/atof.txt (decimal literals and the double SQLite parses them to) and
DIR/format.txt (doubles, a formatting expression, SQLite's result).
test/floats.lisp replays both."""
import sqlite3, struct, random, sys, os
seed, d = int(sys.argv[1]), sys.argv[2]
os.makedirs(d, exist_ok=True)
r = random.Random(seed)
c = sqlite3.connect(':memory:')
with open(os.path.join(d, 'atof.txt'), 'w') as f:
    for _ in range(3000):
        k = r.random()
        if k < 0.3: v = repr(r.uniform(-1, 1) * 10.0 ** r.randint(-300, 300))
        elif k < 0.5: v = '%.*e' % (r.randint(0, 25), r.uniform(1, 10) * 10.0 ** r.randint(-300, 300))
        elif k < 0.7: v = str(r.randint(0, 10**30)) + '.' + str(r.randint(0, 10**20))
        elif k < 0.85: v = str(r.randint(10**18, 10**25))
        else: v = "0." + "0" * r.randint(0, 20) + str(r.randint(1, 10**19)) + "e" + str(r.randint(-300, 300))
        x = c.execute('select ' + v).fetchone()[0]
        if isinstance(x, float): f.write('%s %s\n' % (v, struct.pack('>d', x).hex()))
fmts = ["CAST(? AS TEXT)", "printf('%.3f', ?)", "printf('%e', ?)", "printf('%g', ?)", "printf('%.15g', ?)",
        "printf('%!.20g', ?)", "printf('%.0f', ?)", "printf('%10.4e', ?)", "round(?, 3)", "round(?)",
        "quote(?)", "printf('%.12f', ?)", "? || ''"]
with open(os.path.join(d, 'format.txt'), 'w') as f:
    for _ in range(3000):
        k = r.random()
        if k < 0.4: x = r.uniform(-1, 1) * 10.0 ** r.randint(-30, 30)
        elif k < 0.6: x = float(r.randint(-10**6, 10**6)) / r.choice([2, 4, 8, 10, 100, 1000])
        elif k < 0.8: x = r.uniform(-1, 1) * 10.0 ** r.randint(-300, 300)
        else: x = struct.unpack('>d', struct.pack('>Q', r.getrandbits(64)))[0]
        if x != x or x in (float('inf'), float('-inf')): continue
        fm = r.choice(fmts)
        v = c.execute('select ' + fm, (x,)).fetchone()[0]
        f.write('%s\t%s\t%s\n' % (struct.pack('>d', x).hex(), fm,
                ('R' + struct.pack('>d', v).hex()) if isinstance(v, float) else repr(v)))
