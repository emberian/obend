#!/usr/bin/env python3
"""Execute lean/tests/vault/WALKTHROUGH.md: the acceptance test of `obend open`.

Every ```sh block runs, in order, under bash in one work directory, with the built `obend`
(lean/.lake/build/bin/obend) first on PATH. The ```text block that follows a ```sh block is its
expected output (stdout and stderr together), compared exactly. A ```sh block marked `refused`
must exit non-zero; exiting 1 or 2 it must say why on stderr (`obend` exits 1 when a command ran but a
write of it was refused, 2 when the command itself was refused, and says the refusal on stderr either
way; other codes report a fault, as `obend log` does a torn tail); any other must exit 0.

    python3 tests/vault/walkthrough.py            # from lean/, after `lake build obend`
    python3 tests/vault/walkthrough.py --work DIR # run in DIR (must not exist) and keep it
    python3 tests/vault/walkthrough.py --record   # rewrite the expected outputs (then read them!)
    python3 tests/vault/walkthrough.py --doc PATH # another walkthrough in the same form (tests/decisions/)
    python3 tests/vault/walkthrough.py --cost-baseline  # also make this run the walkthrough's cost baseline

Every command says what it cost (`OBEND_COST`, `Obend.Vault.Cost`): the bytes it read and wrote, its
time, the records it replayed and the checkpoint it read. The runner sums them per step into
tests/vault/COST.tsv (the rows of this walkthrough replaced) and compares each step with
tests/vault/COST.baseline.tsv: a step whose bytes, records or time more than double (beyond a floor:
4096 bytes, 16 records, 250 ms) is a failure, with the numbers.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
DOC = os.path.join(HERE, "WALKTHROUGH.md")
BIN = os.path.join(LEAN, ".lake", "build", "bin")

COST = os.path.join(HERE, "COST.tsv")
BASELINE = os.path.join(HERE, "COST.baseline.tsv")
COLUMNS = ["walkthrough", "step", "line", "commands", "read", "wrote", "ms", "replayed", "checkpoint"]
MEASURES = ["read", "wrote", "ms", "replayed", "checkpoint"]
FLOOR = {"read": 4096, "wrote": 4096, "ms": 250, "replayed": 16, "checkpoint": 4096}
COST_LINE = re.compile(r"^cost: read (\d+) bytes, wrote (\d+) bytes, (\d+) ms, replayed (\d+) records, "
                       r"checkpoint (\d+) bytes \[(.*)\]$")


def read_tsv(path):
    if not os.path.exists(path):
        return []
    rows = open(path, encoding="utf-8").read().splitlines()
    return [dict(zip(COLUMNS, r.split("\t"))) for r in rows[1:] if r]


def write_tsv(path, name, rows):
    """Replace the rows of walkthrough `name` in the table at `path` by `rows`."""
    kept = [r for r in read_tsv(path) if r["walkthrough"] != name]
    out = ["\t".join(COLUMNS)]
    for r in kept + rows:
        out.append("\t".join(str(r[c]) for c in COLUMNS))
    open(path, "w", encoding="utf-8").write("\n".join(out) + "\n")


def step_cost(path, name, step, line):
    """The cost lines the step's commands appended to `path`, summed; the file emptied."""
    row = {"walkthrough": name, "step": step, "line": line, "commands": []}
    for m in MEASURES:
        row[m] = 0
    if os.path.exists(path):
        for l in open(path, encoding="utf-8").read().splitlines():
            m = COST_LINE.match(l)
            if not m:
                continue
            for c, v in zip(MEASURES, m.groups()[:5]):
                row[c] += int(v)
            row["commands"].append(m.group(6))
        os.remove(path)
    row["commands"] = ",".join(row["commands"]) or "-"
    return row


def compare(rows, base):
    """The steps that more than doubled a measure against the baseline, as messages."""
    bad = []
    by = {(b["walkthrough"], b["step"]): b for b in base}
    for r in rows:
        b = by.get((r["walkthrough"], str(r["step"])))
        if b is None or b["commands"] != r["commands"]:
            continue
        for m in MEASURES:
            was, now = int(b[m]), int(r[m])
            if now > 2 * was and now - was > FLOOR[m]:
                bad.append(f"COST step {r['step']} (line {r['line']}, {r['commands']}): {m} {was} -> {now}")
    return bad


FENCE = re.compile(r"^```(\w*)(.*)$")


def blocks(text):
    """The document as a list of (kind, info, body, start, end) for fenced blocks."""
    lines = text.split("\n")
    out = []
    i = 0
    while i < len(lines):
        m = FENCE.match(lines[i])
        if m and m.group(1):
            j = i + 1
            while j < len(lines) and lines[j] != "```":
                j += 1
            out.append((m.group(1), m.group(2).strip(), "\n".join(lines[i + 1:j]), i, j))
            i = j + 1
        else:
            i += 1
    return out


def main():
    global DOC
    args = sys.argv[1:]
    if "--doc" in args:
        DOC = os.path.abspath(args[args.index("--doc") + 1])
    record = "--record" in args
    work = None
    if "--work" in args:
        work = os.path.abspath(args[args.index("--work") + 1])
        os.makedirs(work)
    else:
        work = tempfile.mkdtemp(prefix="obend-walkthrough-")
    if not os.path.exists(os.path.join(BIN, "obend")):
        sys.exit("build obend first: lake build obend")
    name = os.path.splitext(os.path.relpath(DOC, os.path.dirname(HERE)))[0]
    costlog = tempfile.mkstemp(prefix="obend-cost-")[1]
    os.remove(costlog)
    env = dict(os.environ, PATH=BIN + os.pathsep + os.environ["PATH"], LC_ALL="C.UTF-8",
               OBEND_ROOT=os.path.dirname(LEAN), OBEND_COST=costlog)
    costs = []
    text = open(DOC, encoding="utf-8").read()
    bs = blocks(text)
    lines = text.split("\n")
    edits = []
    failures = 0
    steps = 0
    for k, (kind, info, body, start, end) in enumerate(bs):
        if kind != "sh":
            continue
        steps += 1
        r = subprocess.run(["bash", "-c", body], cwd=work, env=env, capture_output=True, text=True)
        got = (r.stdout + r.stderr).rstrip("\n")
        costs.append(step_cost(costlog, name, steps, start + 1))
        want_fail = info == "refused"
        if (r.returncode != 0) != want_fail:
            failures += 1
            print(f"FAIL step {steps} (line {start + 1}): exit {r.returncode}, expected "
                  f"{'non-zero' if want_fail else '0'}\n{got}")
        elif want_fail and r.returncode in (1, 2) and not r.stderr.strip():
            failures += 1
            print(f"FAIL step {steps} (line {start + 1}): refused (exit {r.returncode}) without a word on stderr\n{got}")
        nxt = bs[k + 1] if k + 1 < len(bs) else None
        if nxt and nxt[0] == "text" and nxt[3] == end + 2:
            if record:
                edits.append((nxt[3], nxt[4], got))
            elif nxt[2] != got:
                failures += 1
                print(f"FAIL step {steps} (line {start + 1}): output differs\n--- expected\n{nxt[2]}\n--- got\n{got}")
            else:
                print(f"ok   step {steps} (line {start + 1})")
        else:
            print(f"ok   step {steps} (line {start + 1}) (no expected output)")
    if record:
        for s, e, got in reversed(edits):
            lines[s + 1:e] = got.split("\n") if got else []
        open(DOC, "w", encoding="utf-8").write("\n".join(lines))
        print(f"recorded {len(edits)} outputs into {DOC}")
    write_tsv(COST, name, costs)
    if "--cost-baseline" in args:
        write_tsv(BASELINE, name, costs)
        print(f"cost baseline: {len(costs)} steps of {name} into {BASELINE}")
    else:
        base = [b for b in read_tsv(BASELINE) if b["walkthrough"] == name]
        if not base:
            print(f"cost: no baseline for {name} (--cost-baseline makes one)")
        stale = sum(1 for r in costs for b in base if str(r["step"]) == b["step"] and r["commands"] != b["commands"])
        if stale:
            print(f"cost: {stale} step(s) of {name} run other commands than the baseline (not compared)")
        for msg in compare(costs, base):
            failures += 1
            print(msg)
    if failures:
        print(f"{failures} failure(s); work directory kept: {work}")
        sys.exit(1)
    print(f"walkthrough: {steps} steps ok")
    if "--work" not in args:
        shutil.rmtree(work)


if __name__ == "__main__":
    main()
