#!/usr/bin/env python3
"""Differential test of bin/sqlp against a real sqlite3 shell.

Every case in test/shell/*.case is run through both shells in a fresh
temporary directory, and stdout, stderr and the exit status must agree.
A case file is:  first line  "args: ..."  (shell-split, may be empty),
the rest is fed on stdin.  Usage: shell-diff.py SQLITE3 SQLP [CASE...]"""
import glob, os, shlex, subprocess, sys, tempfile, shutil

ref, ours = sys.argv[1], os.path.abspath(sys.argv[2])
cases = sys.argv[3:] or sorted(glob.glob(os.path.join(os.path.dirname(__file__), "shell", "*.case")))
here = os.path.dirname(os.path.abspath(__file__))
fails = 0

def run(exe, args, stdin, d):
    env = dict(os.environ, HOME=d)
    p = subprocess.run([exe] + args, input=stdin, capture_output=True, cwd=d, env=env, timeout=120)
    return p.returncode, p.stdout, p.stderr

for case in cases:
    text = open(case, "rb").read()
    first, _, body = text.partition(b"\n")
    assert first.startswith(b"args:"), case
    args = shlex.split(first[5:].decode())
    res = []
    for exe in (ref, ours):
        d = tempfile.mkdtemp(prefix="shdiff")
        try:
            for f in glob.glob(os.path.join(here, "shell", "*.csv")) + glob.glob(os.path.join(here, "shell", "*.sql")):
                shutil.copy(f, d)
            rc, out, err = run(exe, args, body, d)
            # the program's own name appears in some messages
            err = err.replace(exe.encode(), b"PROGRAM").replace(os.path.basename(exe).encode(), b"PROGRAM")
            out, err = out.replace(d.encode(), b"DIR"), err.replace(d.encode(), b"DIR")
            res.append((rc, out, err))
        finally:
            shutil.rmtree(d)
    name = os.path.basename(case)
    if res[0] == res[1]:
        print("ok  ", name)
    else:
        fails += 1
        print("FAIL", name)
        for label, i in (("rc", 0), ("stdout", 1), ("stderr", 2)):
            if res[0][i] != res[1][i]:
                print("  %s differs" % label)
                if i:
                    import difflib
                    for l in difflib.unified_diff(res[0][i].decode("utf-8", "replace").splitlines(),
                                                  res[1][i].decode("utf-8", "replace").splitlines(),
                                                  "sqlite3", "sqlp", lineterm="", n=1):
                        print("    " + l)
                else:
                    print("    sqlite3 %s  sqlp %s" % (res[0][0], res[1][0]))
print("shell: %d of %d cases differ" % (fails, len(cases)))
sys.exit(1 if fails else 0)
