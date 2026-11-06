#!/usr/bin/env python3
"""A large vault, generated (nothing of it is committed), and what each command costs as it grows.

    python3 tests/vault/large.py --work DIR [--pages 2000] [--records 10000] [--bursts 10,100,1000,5000]
                                 [--every 500] [--batch 10]

From lean/, after `lake build obend`. DIR must not exist; it is kept.

1. Pages: PAGES account pages `acct/P0000.md`… (a balance, two links to other accounts), and one
   index page per hundred accounts whose law is over its links (`law cap: linked.balance <= 100`).
   One `obend open`.
2. History: one page edited and `obend open` run, until the log holds RECORDS records; the cost of
   every EVERY-th command is printed.
3. Rejoin bursts, for each size B: a declared fork (`obend fork`) goes away and comes back with B
   writes across min(B, 500) pages, BATCH writes to an `obend open`, each balance within the law over
   links as it stood when it forked; meanwhile the tip lowers that law's cap by 5 (raised again after) (so some of the
   fork's writes break the law as it stands at the tip) and writes three of the pages the fork wrote
   (conflicts, kept as candidates); then `obend merge` at the tip, whose cost is printed with its
   phases.

Every command runs with OBEND_COST pointing at DIR/cost.log; the lines printed are the binary's own.
"""
import os
import random
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
BIN = os.path.join(LEAN, ".lake", "build", "bin", "obend")
COST_LINE = re.compile(r"^cost: read (\d+) bytes, wrote (\d+) bytes, (\d+) ms, replayed (\d+) records, "
                       r"checkpoint (\d+) bytes \[(.*)\]$")


def arg(name, default):
    a = sys.argv[1:]
    return a[a.index(name) + 1] if name in a else default


WORK = os.path.abspath(arg("--work", ""))
PAGES = int(arg("--pages", "2000"))
RECORDS = int(arg("--records", "10000"))
BURSTS = [int(x) for x in arg("--bursts", "10,100,1000,5000").split(",") if x]
EVERY = int(arg("--every", "500"))
BATCH = int(arg("--batch", "10"))
COSTLOG = os.path.join(WORK, "cost.log")
ENV = dict(os.environ, OBEND_COST=COSTLOG, LC_ALL="C.UTF-8")
rng = random.Random(7)


def obend(cwd, *args, check=True):
    """Run obend, its PID in WORK/obend.pid while it runs (a stop is by that PID only)."""
    p = subprocess.Popen([BIN, *args], cwd=cwd, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    pidfile = os.path.join(WORK, "obend.pid")
    open(pidfile, "w").write(f"{p.pid}\n")
    out, err = p.communicate()
    os.remove(pidfile)
    r = subprocess.CompletedProcess(p.args, p.returncode, out, err)
    if check and r.returncode != 0:
        sys.exit(f"obend {' '.join(args)} in {cwd}: exit {r.returncode}\n{r.stdout}\n{r.stderr}")
    return r


def last_costs():
    """The cost lines and phase lines appended since the last call."""
    if not os.path.exists(COSTLOG):
        return []
    ls = open(COSTLOG).read().splitlines()
    os.remove(COSTLOG)
    return ls


def page(i, balance, note=""):
    a, b = (i * 7 + 1) % PAGES, (i * 13 + 5) % PAGES
    return (f"---\nbalance: {balance}\n---\n# Account {i}\n\nOwes [[acct/P{a:04d}]] and [[acct/P{b:04d}]].\n"
            + (f"\n{note}\n" if note else ""))


def index(k, cap):
    links = "".join(f"- [[acct/P{i:04d}]]\n" for i in range(k, min(k + 100, PAGES)))
    return f"---\nlaw cap: linked.balance <= {cap}\n---\n# Accounts {k}\n\n{links}"


def records(vault):
    r = obend(vault, "log")
    m = re.search(r"^log: (\d+) records, (\d+) bytes", r.stdout, re.M)
    last_costs()
    return int(m.group(1)), int(m.group(2))


def du(vault):
    return sum(os.path.getsize(os.path.join(vault, ".obend", f)) for f in ("log", "checkpoint")
               if os.path.exists(os.path.join(vault, ".obend", f)))


def main():
    if not WORK or os.path.exists(WORK):
        sys.exit("--work DIR (it must not exist)")
    vault = os.path.join(WORK, "vault")
    os.makedirs(os.path.join(vault, "acct"))
    balances = [rng.randint(0, 60) for _ in range(PAGES)]
    for i in range(PAGES):
        open(os.path.join(vault, "acct", f"P{i:04d}.md"), "w").write(page(i, balances[i]))
    for k in range(0, PAGES, 100):
        open(os.path.join(vault, f"Index{k // 100:02d}.md"), "w").write(index(k, 100))
    t = time.time()
    obend(vault, "open")
    print(f"pages: {PAGES} accounts, {(PAGES + 99) // 100} indexes; open in {time.time() - t:.2f} s")
    for l in last_costs():
        print("  " + l)
    sys.stdout.flush()

    n, _ = records(vault)
    edits = 0
    print(f"history: one page edited per command, cost every {EVERY} records")
    print("records\tlog bytes\tcheckpoint bytes\tcost of the command")
    while n < RECORDS:
        i = rng.randrange(PAGES)
        edits += 1
        open(os.path.join(vault, "acct", f"P{i:04d}.md"), "w").write(page(i, balances[i], f"Edit {edits}."))
        obend(vault, "open")
        ls = last_costs()
        n += 1
        if n % EVERY == 0 or n >= RECORDS:
            size = os.path.getsize(os.path.join(vault, ".obend", "log"))
            ck = os.path.join(vault, ".obend", "checkpoint")
            print(f"{n}\t{size}\t{os.path.getsize(ck) if os.path.exists(ck) else 0}\t" + " | ".join(ls))
            sys.stdout.flush()

    print("rejoin bursts: writes B across min(B, 500) pages; the merge's cost and phases")
    cap = 100
    for B in BURSTS:
        name = f"agent{B}"
        agent = os.path.join(WORK, name)
        obend(vault, "fork", agent)
        last_costs()
        touched = rng.sample(range(PAGES), min(B, 500, PAGES))
        bal = dict((i, balances[i]) for i in touched)
        t = time.time()
        for j in range(0, B, BATCH):
            for w in range(j, min(j + BATCH, B)):
                i = touched[w % len(touched)]
                bal[i] = rng.randint(0, cap)
                open(os.path.join(agent, "acct", f"P{i:04d}.md"), "w").write(page(i, bal[i], f"Agent write {w}."))
            obend(agent, "open")
        away = time.time() - t
        last_costs()
        for k in range(0, PAGES, 100):
            open(os.path.join(vault, f"Index{k // 100:02d}.md"), "w").write(index(k, cap - 5))
        for i in touched[:3]:
            open(os.path.join(vault, "acct", f"P{i:04d}.md"), "w").write(page(i, balances[i], "Written at the tip."))
        obend(vault, "open")
        last_costs()
        r = obend(vault, "merge", agent, check=False)
        ls = last_costs()
        outs = r.stdout.splitlines()
        merged = sum(1 for l in outs if ": merged from " in l or ": imported from " in l)
        refused = sum(1 for l in outs if "not merged" in l)
        conflicts = sum(1 for l in outs if "candidates" in l and f"@{name})" in l)
        print(f"burst {B}: {len(touched)} pages, {B // BATCH or 1} opens away ({away:.1f} s); merge exit "
              f"{r.returncode}: {merged} pages merged, {refused} refused, {conflicts} sections kept as candidates")
        for l in ls:
            print("  " + l)
        sys.stdout.flush()
        # the law as it was; the candidates stay as the merge kept them, and the next burst forks from here
        for k in range(0, PAGES, 100):
            open(os.path.join(vault, f"Index{k // 100:02d}.md"), "w").write(index(k, cap))
        obend(vault, "open")
        last_costs()


if __name__ == "__main__":
    main()
