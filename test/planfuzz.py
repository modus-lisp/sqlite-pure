#!/usr/bin/env python3
"""Query-planner differential fuzzer: random schemas, data and queries run by
SQLite's sqlite3 shell and by bin/sqlp; the EXPLAIN QUERY PLAN output and the
rows of every query must match.  Row ORDER matters too, even without ORDER
BY: it is what the plan decides.

usage: planfuzz.py SQLITE3 SQLP FIRST-SEED N [QUERIES-PER-SEED]"""
import random, subprocess, sys, tempfile, os

TYPES = ["INTEGER", "INT", "TEXT", "REAL", "", "VARCHAR(10)", "NUMERIC", "BLOB"]

def gen_schema(r):
    tables = []
    out = []
    for t in range(r.randint(1, 4)):
        name = "t%d" % t
        ncol = r.randint(2, 5)
        cols = ["c%d" % i for i in range(ncol)]
        types = [r.choice(TYPES) for _ in cols]
        ipk = r.random() < 0.35
        wr = (not ipk) and r.random() < 0.12
        decl = []
        for i, (c, ty) in enumerate(zip(cols, types)):
            d = "%s %s" % (c, ty)
            if i == 0 and ipk:
                d = "%s INTEGER PRIMARY KEY" % c
                types[0] = "INTEGER"
            elif r.random() < 0.15:
                d += " NOT NULL DEFAULT 0"
            elif r.random() < 0.08:
                d += " UNIQUE"
            decl.append(d)
        if wr:
            decl.append("PRIMARY KEY(%s)" % cols[0])
        out.append("CREATE TABLE %s(%s)%s;" % (name, ", ".join(decl), " WITHOUT ROWID" if wr else ""))
        for k in range(r.randint(0, 3)):
            ic = r.sample(cols, r.randint(1, min(3, ncol)))
            parts = [c + (" DESC" if r.random() < 0.15 else "") for c in ic]
            uniq = "UNIQUE " if r.random() < 0.2 else ""
            out.append("CREATE %sINDEX IF NOT EXISTS %s_i%d ON %s(%s);" % (uniq, name, k, name, ", ".join(parts)))
        nrow = r.randint(0, 30)
        seen = set()
        for i in range(nrow):
            vals = []
            for j, ty in enumerate(types):
                if j == 0 and (ipk or wr):
                    v = i + 1
                elif r.random() < 0.12:
                    v = "NULL"
                elif ty in ("TEXT", "VARCHAR(10)") or r.random() < 0.15:
                    v = "'%s'" % r.choice(["a", "b", "c", "x", "y", "10", "2"])
                else:
                    v = r.randint(0, 8)
                vals.append(str(v))
            out.append("INSERT OR IGNORE INTO %s VALUES(%s);" % (name, ", ".join(vals)))
        tables.append((name, cols))
    return tables, out

def rand_value(r):
    return r.choice([str(r.randint(0, 8)), "'a'", "'x'", "'10'", "NULL", "2.5"])

def gen_query(r, tables):
    k = r.randint(1, min(3, len(tables)))
    picked = r.sample(tables, k)
    aliases = ["a", "b", "c", "d"]
    srcs = []
    for i, (name, cols) in enumerate(picked):
        if r.random() < 0.1 and not os.environ.get("PLANFUZZ_NO_SUBQ"):
            # a subquery in FROM
            sub_cols = r.sample(cols, r.randint(1, len(cols)))
            where = ""
            if r.random() < 0.5:
                where = " WHERE %s > %s" % (r.choice(sub_cols), rand_value(r))
            srcs.append(("(SELECT %s FROM %s%s)" % (", ".join(sub_cols), name, where), aliases[i], sub_cols))
        else:
            srcs.append((name, aliases[i], cols))
    def col(i=None):
        s = srcs[r.randrange(len(srcs))] if i is None else srcs[i]
        return "%s.%s" % (s[1], r.choice(s[2]))
    conds = []
    for _ in range(r.randint(0, 4)):
        kind = r.random()
        if kind < 0.3 and len(srcs) > 1:
            i, j = r.sample(range(len(srcs)), 2)
            conds.append("%s = %s" % (col(i), col(j)))
        elif kind < 0.55:
            conds.append("%s = %s" % (col(), rand_value(r)))
        elif kind < 0.7:
            conds.append("%s %s %s" % (col(), r.choice(["<", "<=", ">", ">="]), rand_value(r)))
        elif kind < 0.78:
            conds.append("%s IN (%s)" % (col(), ", ".join(rand_value(r) for _ in range(r.randint(1, 3)))))
        elif kind < 0.84:
            conds.append("%s IS %sNULL" % (col(), r.choice(["", "NOT "])))
        elif kind < 0.9:
            conds.append("%s BETWEEN %s AND %s" % (col(), r.randint(0, 3), r.randint(3, 8)))
        elif not os.environ.get("PLANFUZZ_NO_OR"):
            conds.append("(%s = %s OR %s > %s)" % (col(), rand_value(r), col(), rand_value(r)))
    # FROM with joins
    frm = "%s AS %s" % (srcs[0][0], srcs[0][1])
    for s in srcs[1:]:
        jt = r.random()
        if jt < 0.6:
            frm += ", %s AS %s" % (s[0], s[1])
        elif jt < 0.8:
            frm += " JOIN %s AS %s ON %s = %s" % (s[0], s[1], "%s.%s" % (s[1], r.choice(s[2])), col(0))
        elif jt < 0.93:
            frm += " LEFT JOIN %s AS %s ON %s = %s" % (s[0], s[1], "%s.%s" % (s[1], r.choice(s[2])), col(0))
        else:
            frm += " CROSS JOIN %s AS %s" % (s[0], s[1])
    shape = r.random()
    if shape < 0.15:
        g = col()
        q = "SELECT %s, count(*) FROM %s%s GROUP BY %s" % (g, frm, (" WHERE " + " AND ".join(conds)) if conds else "", g)
        if r.random() < 0.5:
            q += " ORDER BY %s%s" % (g, r.choice(["", " DESC"]))
    elif shape < 0.22:
        q = "SELECT %s(%s) FROM %s%s" % (r.choice(["min", "max"]), col(), frm, (" WHERE " + " AND ".join(conds)) if conds else "")
    else:
        sel = ", ".join(col() for _ in range(r.randint(1, 3)))
        q = "SELECT %s%s FROM %s" % ("DISTINCT " if r.random() < 0.12 else "", sel, frm)
        if conds:
            q += " WHERE " + " AND ".join(conds)
        if r.random() < 0.4:
            q += " ORDER BY " + ", ".join(col() + r.choice(["", " DESC"]) for _ in range(r.randint(1, 2)))
        if r.random() < 0.15:
            q += " LIMIT %d" % r.randint(1, 5)
    return q

def run(exe, script):
    with tempfile.NamedTemporaryFile("w", suffix=".sql", delete=False) as f:
        f.write(script)
        path = f.name
    try:
        p = subprocess.run([exe, ":memory:"], stdin=open(path), capture_output=True, timeout=300)
        return p.stdout.decode("utf-8", "replace") + p.stderr.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    finally:
        os.unlink(path)

def main():
    ref, ours, first, n = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    per = int(sys.argv[5]) if len(sys.argv) > 5 else 30
    total = fails = 0
    for seed in range(first, first + n):
        r = random.Random(seed)
        tables, schema = gen_schema(r)
        queries = [gen_query(r, tables) for _ in range(per)]
        script = "\n".join(schema) + "\n"
        for i, q in enumerate(queries):
            script += ".print ==%d EQP\nEXPLAIN QUERY PLAN %s;\n.print ==%d ROWS\n%s;\n" % (i, q, i, q)
        a, b = run(ref, script), run(ours, script)
        total += len(queries)
        if a != b:
            # report the first differing query
            sa, sb = a.split("\n"), b.split("\n")
            for k in range(min(len(sa), len(sb))):
                if sa[k] != sb[k]:
                    # find the query marker above k
                    m = k
                    while m > 0 and not sa[m].startswith("=="):
                        m -= 1
                    qi = int(sa[m][2:].split()[0]) if sa[m].startswith("==") else -1
                    fails += 1
                    print("seed %d query %d (%s)" % (seed, qi, sa[m][2:].strip()))
                    print("   ", queries[qi] if qi >= 0 else "?")
                    print("    sqlite3:", sa[k][:150])
                    print("    sqlp:   ", sb[k][:150])
                    break
            else:
                fails += 1
                print("seed %d: output lengths differ" % seed)
    print("planfuzz: %d seeds, %d queries, %d seeds differ" % (n, total, fails))
    sys.exit(1 if fails else 0)

main()
