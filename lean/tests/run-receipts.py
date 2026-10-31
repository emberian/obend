#!/usr/bin/env python3
"""Receipts end to end through `obend` (Obend.Receipt.Cli): produce, re-check with no producer state, tamper.

  * the 32-bit no-carry identity (x &&& y = 0 -> x + y = x ||| y) through lrat@1: `obend receipt cnf`
    writes the encoding, which is byte-identical to tests/judge/nocarry32.cnf; when CaDiCaL is on PATH
    it is re-run (`--lrat --binary=false`) and its fresh certificate used, else the recorded
    tests/judge/nocarry32.lrat; `obend lrat` accepts it; a proof with a needed clause deleted is refused.
  * the negotiation's admitted dispatch of the commitment to p2, chained to the identity receipt, at
    the `cited` and `full` settings of the dial: both verify, with the chain link.
  * teeth: an opening its pin does not read, a pin and opening both flipped (the recomputed verdict
    differs), a tampered rest (the pre root differs), a tampered certificate, a wrong predecessor, a
    statement changed after the certificate (its CNF digest differs) are each refused by name.

usage: python3 tests/run-receipts.py [OBEND_BINARY]      (from lean/, after `lake build obend`)
exit 0 when every check holds, 1 otherwise; a summary line last.
"""
import json, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
JUDGE = os.path.join(HERE, "judge")
OBEND = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LEAN, ".lake", "build", "bin", "obend")

failures = []
count = 0


def obend(*args):
    r = subprocess.run([OBEND, *args], capture_output=True, text=True, cwd=LEAN)
    return r.returncode, r.stdout + r.stderr


def check(name, ok, detail=""):
    global count
    count += 1
    if not ok:
        failures.append(name)
        print(f"FAIL {name}: {detail}")
    else:
        print(f"ok   {name}")


def write(path, obj):
    with open(path, "w") as f:
        json.dump(obj, f)


with tempfile.TemporaryDirectory() as d:
    cnf = os.path.join(d, "nc32.cnf")
    rc, out = obend("receipt", "cnf", "32", cnf)
    check("cnf written", rc == 0, out)
    with open(cnf) as a, open(os.path.join(JUDGE, "nocarry32.cnf")) as b:
        check("cnf is the recorded encoding", a.read() == b.read())
    lrat = os.path.join(d, "nc32.lrat")
    if shutil.which("cadical"):
        r = subprocess.run(["cadical", "-q", "--lrat", "--binary=false", cnf, lrat], capture_output=True, text=True)
        check("cadical refutes it", r.returncode == 20, r.stdout)
    else:
        shutil.copy(os.path.join(JUDGE, "nocarry32.lrat"), lrat)
    rc, out = obend("lrat", cnf, lrat)
    check("lrat accepts the certificate", rc == 0 and out.startswith("ok"), out)

    lines = open(lrat).read().splitlines()

    def hints(l):
        xs = l.split()[1:]
        return xs[xs.index("0") + 1 : -1]
    adds = [i for i, l in enumerate(lines) if l.split()[1] != "d"]
    # the first added clause that a later addition cites, deleted right after it is added
    at = next(i for i in adds if any(lines[i].split()[0] in hints(lines[j]) for j in adds if j > i))
    target = lines[at].split()[0]
    cut = lines[: at + 1] + [f"{target} d {target} 0"] + lines[at + 1 :]
    bad = os.path.join(d, "bad.lrat")
    with open(bad, "w") as f:
        f.write("\n".join(cut) + "\n")
    rc, out = obend("lrat", cnf, bad)
    check("a deleted needed clause is refused by name", rc == 3 and "missingHint" in out, out)

    ident = os.path.join(d, "identity.json")
    rc, out = obend("receipt", "identity", "32", lrat, ident)
    check("identity receipt written", rc == 0, out)
    rc, out = obend("verify", ident)
    check("identity receipt verifies", rc == 0 and "holds" in out, out)

    for dial, extra in (("cited", []), ("full", ["--full"])):
        neg = os.path.join(d, f"negotiation-{dial}.json")
        rc, out = obend("receipt", "negotiation", neg, *extra, "--prev", ident)
        check(f"negotiation receipt ({dial}) written", rc == 0, out)
        rc, out = obend("verify", neg, "--prev", ident)
        check(f"negotiation receipt ({dial}) verifies with its chain", rc == 0 and "chain: linked" in out, out)

    neg = os.path.join(d, "negotiation-cited.json")
    base = json.load(open(neg))

    def tamper(name, mutate, needle, prev=ident):
        r = json.loads(json.dumps(base))
        mutate(r)
        p = os.path.join(d, "t.json")
        write(p, r)
        rc, out = obend("verify", p, "--prev", prev)
        check(name, rc == 3 and needle in out, out)

    def flip_opening(r):
        r["openings"][0]["value"] = False
    tamper("an opening its pin does not read is refused", flip_opening, "not what its pin reads")

    def flip_both(r):
        for p in r["pins"]:
            if p["cell"] == "auth p2":
                p["pin"][1] = False
        for o in r["openings"]:
            if o["read"] == "auth p2":
                o["value"] = False
    tamper("flipped pins recompute another verdict", flip_both, "recheck")

    def spend(r):
        r["disclosure"]["rest"]["spent"] = ["cap"]
    tamper("a tampered rest is not the pre root", spend, "pre:")

    other = os.path.join(d, "other.json")
    o = json.load(open(ident))
    o["dated"] = 1
    write(other, o)
    tamper("a wrong predecessor breaks the chain", lambda r: None, "prev:", prev=other)

    def cert_cut(r):
        r["certificate"] = "\n".join(cut) + "\n"
    i = json.load(open(ident))
    cert_cut(i)
    p = os.path.join(d, "ti.json")
    write(p, i)
    rc, out = obend("verify", p)
    check("an identity receipt with a bad certificate is refused", rc == 3 and "missingHint" in out, out)

    i = json.load(open(ident))
    i["statement"]["hyp"] = {"const": True}
    write(p, i)
    rc, out = obend("verify", p)
    check("a statement changed after the certificate is refused", rc == 3 and "row:" in out, out)

print(f"{count - len(failures)}/{count} receipt checks hold")
sys.exit(1 if failures else 0)
