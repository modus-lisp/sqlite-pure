#!/usr/bin/env python3
"""Foreign-format checks.  `formats.py make DIR` has SQLite write databases
in many shapes (page sizes, UTF-16, auto-vacuum, WAL with uncheckpointed
frames, heavy freelists) plus their canonical dumps; the Lisp side dumps
its reading of each (DIR/*.lisp.txt).  `formats.py check DIR` compares, and
also checks the databases the Lisp side *wrote* (DIR/w-*.db)."""
import sqlite3, os, sys, random, shutil
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fuzz.py')).read()
src = src.replace("if __name__ == '__main__':", "if False:")
g = {}; exec(compile(src, 'fuzz', 'exec'), g)
dump = g['dump']

def populate(con, n=400, seed=1):
    r = random.Random(seed)
    con.execute('CREATE TABLE a(id INTEGER PRIMARY KEY, t TEXT, b BLOB, r REAL, i INTEGER)')
    con.execute('CREATE INDEX a_t ON a(t)')
    con.execute('CREATE TABLE w(k TEXT PRIMARY KEY, v) WITHOUT ROWID')
    for i in range(n):
        t = ''.join(r.choice('abcdefgh日本é') for _ in range(r.choice([1, 5, 50, 700, 5000])))
        con.execute('INSERT INTO a(t, b, r, i) VALUES (?,?,?,?)',
                    (t, bytes(r.getrandbits(8) for _ in range(r.choice([0, 3, 900, 9000]))),
                     r.uniform(-1e9, 1e9), r.randint(-2**62, 2**62)))
        con.execute('INSERT OR REPLACE INTO w VALUES (?, ?)', ('k%d' % r.randint(0, 200), t[:100]))

def make(d):
    if os.path.isdir(d): shutil.rmtree(d)
    os.makedirs(d)
    specs = [
        ('ps512', ['PRAGMA page_size=512'], {}),
        ('ps1024', ['PRAGMA page_size=1024'], {}),
        ('ps65536', ['PRAGMA page_size=65536'], {}),
        ('utf16le', ['PRAGMA encoding="UTF-16le"'], {}),
        ('utf16be', ['PRAGMA encoding="UTF-16be"'], {}),
        ('autovac', ['PRAGMA auto_vacuum=FULL'], {}),
        ('freelist', [], {'delete': True}),
        ('wal', ['PRAGMA journal_mode=WAL'], {'wal': True}),
    ]
    for name, pragmas, opts in specs:
        path = os.path.join(d, name + '.db')
        con = sqlite3.connect(path, isolation_level=None)
        for p in pragmas: con.execute(p)
        if opts.get('wal'):
            con.execute('PRAGMA wal_autocheckpoint=0')
        con.execute('BEGIN'); populate(con); con.execute('COMMIT')
        if opts.get('delete'):
            con.execute('DELETE FROM a WHERE id % 3 = 0')
            con.execute('DELETE FROM w WHERE k > "k15"')
        if opts.get('wal'):
            # leave committed frames in the -wal file, plus a checkpointed prefix
            con.execute('PRAGMA wal_checkpoint(TRUNCATE)')
            con.execute('UPDATE a SET t = t || "!" WHERE id % 5 = 0')
            con.execute('DELETE FROM a WHERE id % 7 = 0')
            open(os.path.join(d, name + '.expected.txt'), 'w', encoding='utf-8').write(dump(con))
            shutil.copy(path, path + '.snap'); shutil.copy(path + '-wal', path + '.snap-wal')
            con.close()
            # restore the un-checkpointed state (closing checkpoints)
            shutil.copy(path + '.snap', path); shutil.copy(path + '.snap-wal', path + '-wal')
            continue
        open(os.path.join(d, name + '.expected.txt'), 'w', encoding='utf-8').write(dump(con))
        con.close()
    print('made', len(specs), 'databases')

def check(d):
    ok = True
    for f in sorted(os.listdir(d)):
        if f.endswith('.expected.txt') and not f.startswith('w-'):
            name = f[:-len('.expected.txt')]
            want = open(os.path.join(d, f), encoding='utf-8').read()
            got_path = os.path.join(d, name + '.lisp.txt')
            got = open(got_path, encoding='utf-8').read() if os.path.exists(got_path) else '<missing>'
            if got != want:
                ok = False; print('READ MISMATCH', name, len(got), len(want))
            else:
                print('read ok', name)
    for f in sorted(os.listdir(d)):
        if f.startswith('w-') and f.endswith('.db'):
            con = sqlite3.connect(os.path.join(d, f))
            ic = con.execute('PRAGMA integrity_check').fetchall()
            exp = os.path.join(d, f[:-3] + '.expected.txt')
            same = True
            if os.path.exists(exp):
                same = dump(con) == open(exp, encoding='utf-8').read()
            if ic != [('ok',)] or not same:
                ok = False; print('WRITE FAIL', f, ic[:3], 'content-same' if same else 'content-differs')
            else:
                print('write ok', f)
    print('PASS' if ok else 'FAIL')
    return ok

if sys.argv[1] == 'make': make(sys.argv[2])
else: sys.exit(0 if check(sys.argv[2]) else 1)
