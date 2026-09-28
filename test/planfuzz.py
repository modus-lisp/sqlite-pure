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
        out.append("CREATE VIEW v_%s AS SELECT * FROM %s;" % (name, name))
    return tables, out

def rand_value(r):
    return r.choice([str(r.randint(0, 8)), "'a'", "'x'", "'10'", "NULL", "2.5"])

def gen_subquery(r, name, cols, tables, depth=0):
    """A FROM subquery over NAME: returns (sql, column names)."""
    shape = r.random()
    if shape < 0.12:
        return "(SELECT * FROM %s)" % name, list(cols)
    if shape < 0.2 and depth == 0:
        inner, icols = gen_subquery(r, name, cols, tables, depth + 1)
        pick = r.sample(icols, r.randint(1, len(icols)))
        return "(SELECT %s FROM %s AS s%d)" % (", ".join(pick), inner, depth), pick
    if shape < 0.28 and depth == 0:
        return "v_%s" % name, list(cols)          # a view: SELECT * FROM name
    sub_cols = r.sample(cols, r.randint(1, len(cols)))
    exprs = list(sub_cols)
    names = list(sub_cols)
    if r.random() < 0.25:
        c = r.choice(cols)
        exprs.append(r.choice(["%s + 1" % c, "%s || 'z'" % c, "5", "%s COLLATE NOCASE" % c, "upper(%s)" % c]) + " AS e0")
        names.append("e0")
    frm = name
    if r.random() < 0.15 and len(tables) > 1:
        other = r.choice([t for t in tables if t[0] != name])
        if r.random() < 0.5:
            frm = "%s, %s AS j" % (name, other[0])
        else:
            frm = "%s LEFT JOIN %s AS j ON j.%s = %s.%s" % (name, other[0], r.choice(other[1]), name, r.choice(cols))
        exprs = ["%s.%s" % (name, e) if e in cols else e.replace(" AS e0", "").replace("(" , "(%s." % name, 1) + " AS e0" if "(" in e else ("%s.%s" % (name, e) if e.split(" ")[0] in cols else e) for e in exprs]
    tail = ""
    k = r.random()
    if k < 0.3:
        tail += " WHERE %s > %s" % ("%s.%s" % (name, r.choice(cols)), rand_value(r))
    if k > 0.85:
        return "(SELECT %s, count(*) AS n FROM %s GROUP BY %s)" % (sub_cols[0], name, sub_cols[0]), [sub_cols[0], "n"]
    if 0.75 < k <= 0.85:
        return "(SELECT DISTINCT %s FROM %s%s)" % (", ".join(sub_cols), name, tail), sub_cols
    if r.random() < 0.15:
        tail += " ORDER BY %s" % r.choice(sub_cols)
        if r.random() < 0.5:
            tail += " LIMIT %d" % r.randint(1, 20)
    return "(SELECT %s FROM %s%s)" % (", ".join(exprs), frm, tail), names

def gen_or(r, col):
    """An OR term: the shapes the OR optimizations look for."""
    def atom():
        k = r.random()
        if k < 0.45:
            return "%s = %s" % (col(), rand_value(r))
        if k < 0.65:
            return "%s %s %s" % (col(), r.choice(["<", "<=", ">", ">="]), rand_value(r))
        if k < 0.75:
            return "%s IS NULL" % col()
        if k < 0.85:
            return "%s BETWEEN %d AND %d" % (col(), r.randint(0, 3), r.randint(3, 8))
        if k < 0.93:
            return "(%s = %s AND %s = %s)" % (col(), rand_value(r), col(), rand_value(r))
        return "%s IN (%s, %s)" % (col(), rand_value(r), rand_value(r))
    k = r.random()
    if k < 0.3:
        c = col()      # one column: may become IN (...)
        return "(" + " OR ".join("%s = %s" % (c, rand_value(r)) for _ in range(r.randint(2, 3))) + ")"
    if k < 0.4:
        c = col(); v = rand_value(r)
        return "(%s = %s OR %s %s %s)" % (c, v, c, r.choice(["<", ">", "<=", ">="]), v)
    return "(" + " OR ".join(atom() for _ in range(r.randint(2, 3))) + ")"

def gen_query(r, tables):
    k = r.randint(1, min(3, len(tables)))
    picked = r.sample(tables, k)
    aliases = ["a", "b", "c", "d"]
    srcs = []
    for i, (name, cols) in enumerate(picked):
        if r.random() < 0.15 and not os.environ.get("PLANFUZZ_NO_SUBQ"):
            srcs.append((gen_subquery(r, name, cols, tables), aliases[i], None))
            srcs[-1] = (srcs[-1][0][0], aliases[i], srcs[-1][0][1])
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
            conds.append(gen_or(r, col))
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
        return (p.stdout.decode("utf-8", "replace"), p.stderr.decode("utf-8", "replace"))
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", "")
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
        (a, ea), (b, eb) = run(ref, script), run(ours, script)
        total += len(queries)
        if a == b and ea != eb:
            fails += 1
            la, lb = ea.split("\n"), eb.split("\n")
            k = next((j for j in range(min(len(la), len(lb))) if la[j] != lb[j]), min(len(la), len(lb)))
            print("seed %d: errors differ" % seed)
            print("    sqlite3:", (la[k] if k < len(la) else "<end>")[:150])
            print("    sqlp:   ", (lb[k] if k < len(lb) else "<end>")[:150])
        if a != b:
            # report the first query whose section differs
            def sections(out):
                d, cur = {}, None
                for line in out.split("\n"):
                    if line.startswith("==") and line[2:].split(" ")[0].isdigit():
                        cur = int(line[2:].split(" ")[0])
                    d.setdefault(cur, []).append(line)
                return d
            sa, sb = sections(a), sections(b)
            for qi in sorted(set(sa) | set(sb), key=lambda k: -1 if k is None else k):
                if sa.get(qi) != sb.get(qi):
                    la, lb = sa.get(qi, []), sb.get(qi, [])
                    k = next((j for j in range(min(len(la), len(lb))) if la[j] != lb[j]), min(len(la), len(lb)))
                    fails += 1
                    print("seed %d query %s" % (seed, qi))
                    print("   ", queries[qi] if qi is not None else "(schema)")
                    print("    sqlite3:", (la[k] if k < len(la) else "<end>")[:150])
                    print("    sqlp:   ", (lb[k] if k < len(lb) else "<end>")[:150])
                    break
    print("planfuzz: %d seeds, %d queries, %d seeds differ" % (n, total, fails))
    sys.exit(1 if fails else 0)

main()
