#!/usr/bin/env python3
"""A large vault, generated (nothing of it is committed), and what each command costs as it grows.

    python3 tests/vault/large.py --work DIR [--pages 2000] [--records 10000] [--bursts 10,100,1000,5000]
                                 [--every 500] [--batch 10]
                                 [--binary PATH] [--no-git] [--from-vault SNAPSHOT] [--resume]

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
DIR/measurements.tsv retains EVERY command, including preparation and commands between printed
samples, with its wall time and named phase. By default a Git repository in the same markdown tree
measures `git status --porcelain --untracked-files=all -- '*.md'`, `git add -- '*.md'`, and `git commit`
after every command that changed markdown. This is a persistence baseline, not equivalent judging:
Git does not enforce the laws, keep refused writes, or explain a merge. An unchanged tree costs status
alone. Forks start with a seeded Git snapshot; seeding is excluded from both command timings.
`--from-vault` copies an already initialized, quiescent fixture and skips genesis. This allows paired
recovery and rejoin measurements from one identical snapshot; it is not an initial-open measurement.
Record counts come from the checkpoint header after a successful command. The benchmark does not
insert a full `obend log` replay merely to count records; log replay is a separate acceptance gate.
After a completed command failed, `--resume --work DIR` retains its evidence, uses the recorded
parameters and binary, and skips successful phases while reconstructing the deterministic RNG stream.
Never resume an active run. Existing tip balances above a tightened cap are clamped in the same turn:
restoring the cap after a previous burst can admit previously refused balances, which must be brought
within the next cap before that law can land. Refusals are never suppressed to make the benchmark pass.
"""
import csv
import hashlib
import json
import os
import platform
import random
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
BIN = os.path.join(LEAN, ".lake", "build", "bin", "obend")
COST_LINE = re.compile(r"^cost: read (\d+) bytes, wrote (\d+) bytes, (\d+) ms, replayed (\d+) records, "
                       r"checkpoint (\d+) bytes \[(.*)\]$")
PHASE_LINE = re.compile(r"^cost phases: read (\d+) ms, judge (\d+) ms, land (\d+) ms, write (\d+) ms, "
                        r"other (\d+) ms \[.*\]$")


def arg(name, default):
    a = sys.argv[1:]
    return a[a.index(name) + 1] if name in a else default


WORK = os.path.abspath(arg("--work", ""))
BIN = os.path.abspath(arg("--binary", BIN))
PAGES = int(arg("--pages", "2000"))
RECORDS = int(arg("--records", "10000"))
BURSTS = [int(x) for x in arg("--bursts", "10,100,1000,5000").split(",") if x]
EVERY = int(arg("--every", "500"))
BATCH = int(arg("--batch", "10"))
SOURCE = arg("--from-vault", "")
COSTLOG = os.path.join(WORK, "cost.log")
ENV = dict(os.environ, OBEND_COST=COSTLOG, LC_ALL="C.UTF-8")
rng = random.Random(7)
GIT = "--no-git" not in sys.argv
PHASE = "initial"
LAST_LINES = []
LAST_GIT = ""
LAST_WALL_MS = 0.0


def git(cwd, *args):
    return subprocess.run(["git", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null",
                           *args], cwd=cwd, capture_output=True, text=True, check=True)


def git_init(cwd, seed=False):
    if not GIT or os.path.isdir(os.path.join(cwd, ".git")):
        return
    git(cwd, "init", "-q", "-b", "baseline")
    git(cwd, "config", "user.name", "Vault benchmark")
    git(cwd, "config", "user.email", "vault-benchmark@example.invalid")
    with open(os.path.join(cwd, ".git", "info", "exclude"), "a") as f:
        f.write("\n.obend/\n")
    if seed:
        git(cwd, "add", "--", "*.md")
        git(cwd, "commit", "-q", "-m", "Fork snapshot")


def git_measure(cwd):
    if not GIT:
        return {}
    t = time.perf_counter_ns()
    status = git(cwd, "status", "--porcelain", "--untracked-files=all", "--", "*.md")
    t1 = time.perf_counter_ns()
    times = {"git_status_ms": (t1 - t) / 1e6, "git_add_ms": 0.0, "git_commit_ms": 0.0,
             "git_changed_files": len(status.stdout.splitlines())}
    if status.stdout:
        git(cwd, "add", "--", "*.md")
        t2 = time.perf_counter_ns()
        git(cwd, "commit", "-q", "-m", "Markdown change")
        t3 = time.perf_counter_ns()
        times.update(git_add_ms=(t2 - t1) / 1e6, git_commit_ms=(t3 - t2) / 1e6)
    return times


def record_measurement(cwd, args, elapsed, returncode, lines, git_cost, stdout="", stderr=""):
    row = dict(phase=PHASE, vault=os.path.relpath(cwd, WORK), command=" ".join(args),
               wall_ms=elapsed, exit=returncode, stdout_bytes=len(stdout.encode("utf-8")),
               stderr_bytes=len(stderr.encode("utf-8")), read=0, wrote=0, ms=0, replayed=0, checkpoint=0,
               read_ms=0, judge_ms=0, land_ms=0, write_ms=0, other_ms=0,
               git_status_ms="", git_add_ms="", git_commit_ms="", git_changed_files="")
    for line in lines:
        match = COST_LINE.match(line)
        if match:
            for key, value in zip(("read", "wrote", "ms", "replayed", "checkpoint"), match.groups()[:5]):
                row[key] += int(value)
        phases = PHASE_LINE.match(line)
        if phases:
            for key, value in zip(("read_ms", "judge_ms", "land_ms", "write_ms", "other_ms"), phases.groups()):
                row[key] += int(value)
    row.update(git_cost)
    path = os.path.join(WORK, "measurements.tsv")
    new = not os.path.exists(path)
    fields = list(row)
    if not new:
        with open(path, newline="", encoding="utf-8") as f:
            fields = next(csv.reader(f, delimiter="\t"))
    with open(path, "a", newline="", encoding="utf-8") as f:
        # A resumed older run retains its original schema; do not shift its columns.
        writer = csv.DictWriter(f, fieldnames=fields, delimiter="\t", extrasaction="ignore")
        if new:
            writer.writeheader()
        writer.writerow(row)


def obend(cwd, *args, check=True):
    """Run obend, its PID in WORK/obend.pid while it runs (a stop is by that PID only)."""
    global LAST_LINES, LAST_GIT, LAST_WALL_MS
    git_init(cwd)
    t = time.perf_counter_ns()
    p = subprocess.Popen([BIN, *args], cwd=cwd, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    pidfile = os.path.join(WORK, "obend.pid")
    open(pidfile, "w").write(f"{p.pid}\n")
    out, err = p.communicate()
    elapsed = (time.perf_counter_ns() - t) / 1e6
    LAST_WALL_MS = elapsed
    os.remove(pidfile)
    LAST_LINES = read_costs()
    git_cost = git_measure(cwd)
    record_measurement(cwd, args, elapsed, p.returncode, LAST_LINES, git_cost, out, err)
    LAST_GIT = ("git: status {git_status_ms:.3f} ms, add {git_add_ms:.3f} ms, "
                "commit {git_commit_ms:.3f} ms, {git_changed_files} changed files").format(**git_cost) if GIT else ""
    r = subprocess.CompletedProcess(p.args, p.returncode, out, err)
    if check and r.returncode != 0:
        sys.exit(f"obend {' '.join(args)} in {cwd}: exit {r.returncode}\n{r.stdout}\n{r.stderr}")
    if r.returncode in (0, 1) and not any(COST_LINE.match(line) for line in LAST_LINES):
        sys.exit(f"obend {' '.join(args)} produced no cost record; cannot measure this binary")
    return r


def read_costs():
    """Read and consume the binary's cost lines for one command."""
    if not os.path.exists(COSTLOG):
        return []
    ls = open(COSTLOG).read().splitlines()
    os.remove(COSTLOG)
    return ls


def last_costs():
    """The last command's binary costs and its same-tree Git comparison."""
    return LAST_LINES + [f"wall: {LAST_WALL_MS:.3f} ms"] + ([LAST_GIT] if LAST_GIT else [])


def page(i, balance, note=""):
    a, b = (i * 7 + 1) % PAGES, (i * 13 + 5) % PAGES
    return (f"---\nbalance: {balance}\n---\n# Account {i}\n\nOwes [[acct/P{a:04d}]] and [[acct/P{b:04d}]].\n"
            + (f"\n{note}\n" if note else ""))


def index(k, cap):
    links = "".join(f"- [[acct/P{i:04d}]]\n" for i in range(k, min(k + 100, PAGES)))
    return f"---\nlaw cap: linked.balance <= {cap}\n---\n# Accounts {k}\n\n{links}"


def records(vault):
    """The successful command's checkpoint count and logical log length (not a replay)."""
    with open(os.path.join(vault, ".obend", "checkpoint"), "rb") as f:
        header = f.readline(200).decode("ascii").split()
    if len(header) not in (6, 7) or header[:2] != ["obend-checkpoint", "1"]:
        raise ValueError(f"unrecognized checkpoint header in {vault}: {header}")
    return int(header[2]), int(header[4])


def log_bytes(vault):
    """Both the original log and the segmented log's manifest and blocks."""
    root = os.path.join(vault, ".obend")
    total = os.path.getsize(os.path.join(root, "log")) if os.path.isfile(os.path.join(root, "log")) else 0
    for path, _, files in os.walk(os.path.join(root, "log-segments")):
        total += sum(os.path.getsize(os.path.join(path, f)) for f in files)
    return total


def clamp_balance(text, cap):
    """Change only a generated account's frontmatter balance, retaining its pending body/candidates."""
    front = re.match(r"\A---\n(.*?)\n---\n", text, re.S)
    if not front:
        raise ValueError("generated account has no frontmatter")
    fields = re.sub(r"(?m)^(balance: )(\d+)$",
                    lambda m: m[1] + str(min(int(m[2]), cap)), front[1], count=1)
    return text[:front.start(1)] + fields + text[front.end(1):]


def main():
    global PHASE, PAGES, RECORDS, BURSTS, EVERY, BATCH, BIN, GIT
    resume = "--resume" in sys.argv
    if not WORK or (os.path.exists(WORK) and not resume):
        sys.exit("--work DIR (must not exist, unless resuming a stopped run with --resume)")
    manifest_path = os.path.join(WORK, "run.json")
    done = {}
    if resume:
        if os.path.exists(os.path.join(WORK, "obend.pid")):
            sys.exit("obend.pid still exists: finish or investigate that command before resuming")
        with open(manifest_path) as f:
            manifest = json.load(f)
        PAGES, RECORDS, BURSTS = manifest["pages"], manifest["records"], manifest["bursts"]
        EVERY, BATCH = manifest["every"], manifest["batch"]
        BIN = os.path.abspath(arg("--binary", manifest["binary"]))
        GIT = manifest["git_version"] is not None
        with open(os.path.join(WORK, "measurements.tsv"), newline="") as f:
            for row in csv.DictReader(f, delimiter="\t"):
                accepted = row["exit"] == "0" or (row["exit"] == "1" and row["phase"].endswith("/merge"))
                if accepted:
                    done[row["phase"]] = row
        if "unchanged" not in done:
            sys.exit("resume requires a completed initialized fixture and unchanged-open sample")
    if PAGES <= 0 or EVERY <= 0 or BATCH <= 0 or RECORDS < 1 or any(b <= 0 for b in BURSTS):
        sys.exit("pages, every, batch, records and burst sizes must be positive")
    if not os.path.isfile(BIN):
        sys.exit(f"binary not found: {BIN}")
    with open(BIN, "rb") as f:
        digest = hashlib.file_digest(f, "sha256").hexdigest()
    with open(__file__, "rb") as f:
        harness_digest = hashlib.file_digest(f, "sha256").hexdigest()
    vault = os.path.join(WORK, "vault")
    if resume:
        if digest != manifest["binary_sha256"]:
            sys.exit("resume binary differs: use a fresh fixture for a different binary")
        manifest.setdefault("resumes", []).append(dict(argv=sys.argv, at=time.time(),
                                                       harness_sha256=harness_digest, tip_clamp=True))
        print(f"resuming {WORK}; {len(done)} successful phases retained", flush=True)
    else:
        if SOURCE:
            shutil.copytree(SOURCE, vault, ignore=shutil.ignore_patterns(".git", "lock"))
            git_init(vault, seed=True)
        else:
            os.makedirs(os.path.join(vault, "acct"))
        manifest = dict(binary=BIN, binary_sha256=digest, machine=platform.uname()._asdict(),
                        git_version=git(vault, "--version").stdout.strip() if GIT else None,
                        pages=PAGES, records=RECORDS, bursts=BURSTS, every=EVERY, batch=BATCH,
                        seed=7, source_vault=os.path.abspath(SOURCE) if SOURCE else None, argv=sys.argv,
                        harness_sha256=harness_digest, tip_clamp=True)
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)
    balances = [rng.randint(0, 60) for _ in range(PAGES)]
    print(f"binary: {BIN}; seed: 7; pages: {PAGES}; target records: {RECORDS}; bursts: {BURSTS}", flush=True)
    if not resume:
        if SOURCE:
            print(f"copied initialized fixture: {os.path.abspath(SOURCE)} (genesis excluded)", flush=True)
        else:
            for i in range(PAGES):
                open(os.path.join(vault, "acct", f"P{i:04d}.md"), "w").write(page(i, balances[i]))
            for k in range(0, PAGES, 100):
                open(os.path.join(vault, f"Index{k // 100:02d}.md"), "w").write(index(k, 100))
            obend(vault, "open")
            print(f"pages: {PAGES} accounts, {(PAGES + 99) // 100} indexes; open in {LAST_WALL_MS / 1000:.2f} s")
            for l in last_costs():
                print("  " + l)
        PHASE = "unchanged"
        obend(vault, "open")
        print("unchanged open:")
        for l in last_costs():
            print("  " + l)
        manifest["history_start_count"] = records(vault)[0]
        with open(manifest_path, "w", encoding="utf-8") as f:
            json.dump(manifest, f, indent=2)
    start_count = manifest.get("history_start_count", 2)
    print(f"history: one page edited per command, cost every {EVERY} records")
    print("records\tlog bytes\tcheckpoint bytes\tcost of the command")
    for n in range(start_count + 1, RECORDS + 1):
        PHASE = f"history/{n}"
        i = rng.randrange(PAGES)
        if PHASE in done:
            continue
        open(os.path.join(vault, "acct", f"P{i:04d}.md"), "w").write(page(i, balances[i], f"Edit {n - start_count}."))
        obend(vault, "open")
        if n % EVERY == 0 or n >= RECORDS:
            ck = os.path.join(vault, ".obend", "checkpoint")
            print(f"{n}\t{log_bytes(vault)}\t{os.path.getsize(ck)}\t" + " | ".join(last_costs()), flush=True)

    print("rejoin bursts: writes B across min(B, 500) pages; the merge's cost and phases", flush=True)
    cap = 100
    for B in BURSTS:
        PHASE = f"burst/{B}/fork"
        name = f"agent{B}"
        agent = os.path.join(WORK, name)
        if PHASE not in done:
            obend(vault, "fork", agent)
        git_init(agent, seed=True)
        touched = rng.sample(range(PAGES), min(B, 500, PAGES))
        bal = dict((i, balances[i]) for i in touched)
        away_ms = 0.0
        for j in range(0, B, BATCH):
            PHASE = f"burst/{B}/away/{j}"
            for w in range(j, min(j + BATCH, B)):
                i = touched[w % len(touched)]
                bal[i] = rng.randint(0, cap)
                if PHASE not in done:
                    open(os.path.join(agent, "acct", f"P{i:04d}.md"), "w").write(page(i, bal[i], f"Agent write {w}."))
            if PHASE in done:
                away_ms += float(done[PHASE]["wall_ms"])
            else:
                obend(agent, "open")
                away_ms += LAST_WALL_MS
        PHASE = f"burst/{B}/tip"
        if PHASE not in done:
            for k in range(0, PAGES, 100):
                open(os.path.join(vault, f"Index{k // 100:02d}.md"), "w").write(index(k, cap - 5))
            for i in touched[:3]:
                open(os.path.join(vault, "acct", f"P{i:04d}.md"), "w").write(page(i, balances[i], "Written at the tip."))
            clamped = 0
            for i in range(PAGES):
                path = os.path.join(vault, "acct", f"P{i:04d}.md")
                text = open(path).read()
                tightened = clamp_balance(text, cap - 5)
                if tightened != text:
                    open(path, "w").write(tightened)
                    clamped += 1
            print(f"burst {B}: bringing {clamped} current balances within the tightened cap", flush=True)
            obend(vault, "open")
        PHASE = f"burst/{B}/merge"
        if PHASE not in done:
            r = obend(vault, "merge", agent, check=False)
            if r.returncode not in (0, 1):
                sys.exit(f"burst {B}: merge fault (exit {r.returncode})\n{r.stdout}\n{r.stderr}")
            outs = (r.stdout + r.stderr).splitlines()
            merged = sum(1 for l in outs if ": merged from " in l or ": imported from " in l)
            refused = sum(1 for l in outs if "not merged" in l)
            conflicts = sum(1 for l in outs if "candidates" in l and f"@{name})" in l)
            print(f"burst {B}: {len(touched)} pages, {(B + BATCH - 1) // BATCH} opens away "
                  f"({away_ms / 1000:.1f} s command wall); merge exit {r.returncode}: "
                  f"{merged} pages merged, {refused} refused, {conflicts} sections kept as candidates")
            for l in last_costs():
                print("  " + l)
            sys.stdout.flush()
        # Restoring the law may now admit balances refused under the tighter cap.
        PHASE = f"burst/{B}/restore"
        if PHASE not in done:
            for k in range(0, PAGES, 100):
                open(os.path.join(vault, f"Index{k // 100:02d}.md"), "w").write(index(k, cap))
            obend(vault, "open")


if __name__ == "__main__":
    main()
