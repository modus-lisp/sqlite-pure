#!/usr/bin/env python3
"""test/web-mods.py FILE: a modification script for a real-world database:
per table, delete some rows, rewrite text and integer columns, re-insert
copies with large values, and index a text column.  Deterministic."""
import sqlite3, sys, random
db = sqlite3.connect("file:%s?mode=ro" % sys.argv[1], uri=True)
random.seed(sys.argv[1])
out = []
tabs = db.execute("select name, sql from sqlite_schema where type='table' and name not like 'sqlite_%' and sql not like 'CREATE VIRTUAL%'").fetchall()
for name, sql in tabs:
    q = '"%s"' % name.replace('"', '""')
    cols = [r[1] for r in db.execute("pragma table_info(%s)" % q)]
    wr = "WITHOUT ROWID" in sql.upper()
    key = "rowid" if not wr else '"%s"' % cols[0]
    textcols = [c for c in cols if db.execute('select count(*) from %s where typeof("%s")=\'text\'' % (q, c)).fetchone()[0]]
    numcols = [c for c in cols if db.execute('select count(*) from %s where typeof("%s") in (\'integer\',\'real\')' % (q, c)).fetchone()[0]]
    if not wr:
        out.append("DELETE FROM %s WHERE rowid %% 7 = 3;" % q)
    for c in textcols[:2]:
        out.append('UPDATE %s SET "%s" = upper("%s") || \' (edited)\' WHERE typeof("%s")=\'text\' AND %s %% 5 = 1;' % (q, c, c, c, "rowid" if not wr else "length(%s)" % key))
    for c in numcols[:1]:
        out.append('UPDATE %s SET "%s" = "%s" * 2 WHERE typeof("%s")=\'integer\' AND rowid %% 3 = 0;' % (q, c, c, c) if not wr else "")
    if not wr:
        # re-insert copies of some rows under fresh rowids, with a bigger value
        tc = textcols[0] if textcols else None
        sel = ", ".join(('"%s" || printf(\'%%.2000c\', \'x\')' % c if c == tc else '"%s"' % c) for c in cols)
        out.append("INSERT OR IGNORE INTO %s(%s) SELECT %s FROM %s WHERE rowid %% 11 = 5;" % (q, ", ".join('"%s"' % c for c in cols), sel, q))
    if textcols:
        out.append('CREATE INDEX "zz_%s" ON %s("%s");' % (name.replace('"', ''), q, textcols[0]))
print("\n".join(l for l in out if l))
print("SELECT 'done', total_changes();")
