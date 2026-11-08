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
    python3 tests/vault/walkthrough.py --cost-samples 3 --work DIR  # independent fixtures; median time

Every command says what it cost (`OBEND_COST`, `Obend.Vault.Cost`): the bytes it read and wrote, its
time, the records it replayed and the checkpoint it read. The runner sums them per step into
tests/vault/COST.tsv (the rows of this walkthrough replaced) and compares each step with
tests/vault/COST.baseline.tsv: a step whose bytes, records or time more than double (beyond a floor:
4096 bytes, 16 records, 250 ms) is a failure, with the numbers. Missing baseline rows or changed
command sequences also fail: a changed walkthrough must be deliberately re-baselined, never silently
excluded from the performance gate. A failing functional walkthrough cannot replace its baseline.

With --cost-samples N (1 or an odd number at least 3), the entire walkthrough runs N times in
independent fresh fixtures. Every functional check must pass, with identical step and command
coverage. Time is the median per step; other cost metrics are the maximum per step. Comparison or
baseline replacement runs once on that aggregate, under the same thresholds. Multi-sample runs keep
every fixture, step transcript and cost table under --work DIR (or an announced temporary directory).
--record is incompatible with multiple samples.
"""
import json
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
    with open(path, encoding="utf-8") as table:
        rows = table.read().splitlines()
    return [dict(zip(COLUMNS, r.split("\t"))) for r in rows[1:] if r]


def write_tsv(path, name, rows):
    """Replace the rows of walkthrough `name` in the table at `path` by `rows`."""
    kept = [r for r in read_tsv(path) if r["walkthrough"] != name]
    out = ["\t".join(COLUMNS)]
    for r in kept + rows:
        out.append("\t".join(str(r[c]) for c in COLUMNS))
    with open(path, "w", encoding="utf-8") as table:
        table.write("\n".join(out) + "\n")


def step_cost(path, name, step, line, archive=None):
    """The cost lines the step's commands appended to `path`, summed; the file emptied."""
    row = {"walkthrough": name, "step": step, "line": line, "commands": []}
    for m in MEASURES:
        row[m] = 0
    if os.path.exists(path):
        with open(path, encoding="utf-8") as log:
            raw = log.read()
        if archive is not None:
            with open(archive, "a", encoding="utf-8") as saved:
                saved.write(raw)
        for l in raw.splitlines():
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
    """Require complete baseline coverage, then compare each step's measurements."""
    bad = []
    by = {(b["walkthrough"], b["step"]): b for b in base}
    for r in rows:
        b = by.get((r["walkthrough"], str(r["step"])))
        if b is None:
            bad.append(f"COST step {r['step']} (line {r['line']}): missing baseline; run --cost-baseline")
            continue
        if b["commands"] != r["commands"]:
            bad.append(f"COST step {r['step']} (line {r['line']}): commands changed "
                       f"{b['commands']} -> {r['commands']}; run --cost-baseline")
            continue
        for m in MEASURES:
            was, now = int(b[m]), int(r[m])
            if now > 2 * was and now - was > FLOOR[m]:
                bad.append(f"COST step {r['step']} (line {r['line']}, {r['commands']}): {m} {was} -> {now}")
    return bad


def cost_sample_count(value):
    """An explicit odd sample count has an unambiguous observed median."""
    try:
        count = int(value)
    except (TypeError, ValueError):
        raise ValueError("--cost-samples must be 1 or an odd integer at least 3") from None
    if count < 1 or count % 2 == 0:
        raise ValueError("--cost-samples must be 1 or an odd integer at least 3")
    return count


def aggregate_costs(samples):
    """Require identical coverage; retain median time and worst observed other costs."""
    cost_sample_count(len(samples))

    def coverage(rows):
        keys = [(r["walkthrough"], str(r["step"])) for r in rows]
        if len(keys) != len(set(keys)):
            raise ValueError("duplicate step in cost sample")
        return [(r["walkthrough"], str(r["step"]), str(r["line"]), r["commands"]) for r in rows]

    expected = coverage(samples[0])
    for number, rows in enumerate(samples[1:], 2):
        observed = coverage(rows)
        if observed != expected:
            for position in range(max(len(expected), len(observed))):
                want = expected[position] if position < len(expected) else "<no step>"
                got = observed[position] if position < len(observed) else "<missing step>"
                if want != got:
                    raise ValueError(f"sample {number} coverage differs at row {position + 1}: {want} -> {got}")
    result = []
    for position, row in enumerate(samples[0]):
        combined = dict(row)
        for metric in MEASURES:
            values = [int(rows[position][metric]) for rows in samples]
            combined[metric] = sorted(values)[len(values) // 2] if metric == "ms" else max(values)
        result.append(combined)
    return result


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


def run_document(text, name, work, record=False, evidence=None):
    """Run one complete document in one fresh fixture; never compare costs here."""
    if evidence is None:
        fd, costlog = tempfile.mkstemp(prefix="obend-cost-")
        os.close(fd)
        os.remove(costlog)
    else:
        costlog = os.path.join(evidence, "pending-cost.log")
    env = dict(os.environ, PATH=BIN + os.pathsep + os.environ["PATH"], LC_ALL="C.UTF-8",
               OBEND_ROOT=os.path.dirname(LEAN), OBEND_COST=costlog)

    def report(message):
        print(message)
        if evidence is not None:
            with open(os.path.join(evidence, "output.log"), "a", encoding="utf-8") as log:
                log.write(message + "\n")

    costs = []
    bs = blocks(text)
    edits = []
    failures = 0
    steps = 0
    for k, (kind, info, body, start, end) in enumerate(bs):
        if kind != "sh":
            continue
        steps += 1
        r = subprocess.run(["bash", "-c", body], cwd=work, env=env, capture_output=True, text=True)
        got = (r.stdout + r.stderr).rstrip("\n")
        row = step_cost(costlog, name, steps, start + 1,
                        os.path.join(evidence, "cost-raw.log") if evidence is not None else None)
        costs.append(row)
        if evidence is not None:
            with open(os.path.join(evidence, "steps.jsonl"), "a", encoding="utf-8") as log:
                log.write(json.dumps(dict(step=steps, line=start + 1, script=body, info=info,
                                          exit=r.returncode, stdout=r.stdout, stderr=r.stderr,
                                          cost=row), ensure_ascii=False) + "\n")
        want_fail = info == "refused"
        if (r.returncode != 0) != want_fail:
            failures += 1
            report(f"FAIL step {steps} (line {start + 1}): exit {r.returncode}, expected "
                  f"{'non-zero' if want_fail else '0'}\n{got}")
        elif want_fail and r.returncode in (1, 2) and not r.stderr.strip():
            failures += 1
            report(f"FAIL step {steps} (line {start + 1}): refused (exit {r.returncode}) without a word on stderr\n{got}")
        nxt = bs[k + 1] if k + 1 < len(bs) else None
        if nxt and nxt[0] == "text" and nxt[3] == end + 2:
            if record:
                edits.append((nxt[3], nxt[4], got))
            elif nxt[2] != got:
                failures += 1
                report(f"FAIL step {steps} (line {start + 1}): output differs\n--- expected\n{nxt[2]}\n--- got\n{got}")
            else:
                report(f"ok   step {steps} (line {start + 1})")
        else:
            report(f"ok   step {steps} (line {start + 1}) (no expected output)")
    if evidence is not None:
        write_tsv(os.path.join(evidence, "COST.tsv"), name, costs)
    return costs, failures, steps, edits


def main():
    args = sys.argv[1:]

    def option(flag, default=None):
        if flag not in args:
            return default
        position = args.index(flag) + 1
        if position == len(args) or args[position].startswith("--"):
            sys.exit(f"{flag} requires a value")
        return args[position]

    doc = os.path.abspath(option("--doc", DOC))
    record = "--record" in args
    try:
        samples = cost_sample_count(option("--cost-samples", "1"))
    except ValueError as error:
        sys.exit(str(error))
    if record and samples != 1:
        sys.exit("--record cannot be combined with multiple --cost-samples")
    if not os.path.exists(os.path.join(BIN, "obend")):
        sys.exit("build obend first: lake build obend")
    supplied_work = option("--work")
    if supplied_work is not None:
        work = os.path.abspath(supplied_work)
        os.makedirs(work)
    else:
        work = tempfile.mkdtemp(prefix="obend-walkthrough-")
    name = os.path.splitext(os.path.relpath(doc, os.path.dirname(HERE)))[0]
    with open(doc, encoding="utf-8") as source:
        text = source.read()
    lines = text.split("\n")
    failures = 0
    runs = []
    if samples > 1:
        print(f"cost sampling: {samples} independent complete walkthroughs; per-step median ms, "
              f"maximum read/wrote/replayed/checkpoint; every functional check required")
        print(f"sample evidence and fixtures kept: {work}")
    for number in range(1, samples + 1):
        evidence = None
        fixture = work
        if samples > 1:
            evidence = os.path.join(work, f"sample-{number:03d}")
            fixture = os.path.join(evidence, "fixture")
            os.makedirs(fixture)
            print(f"sample {number}/{samples}: {fixture}")
        costs, bad, steps, edits = run_document(text, name, fixture, record, evidence)
        failures += bad
        runs.append(costs)
        if samples > 1:
            print(f"sample {number}/{samples}: {steps} steps, {bad} functional failure(s)")
    try:
        costs = aggregate_costs(runs)
    except ValueError as error:
        failures += 1
        costs = None
        print(f"COST aggregation refused: {error}")
    if samples > 1 and costs is not None:
        write_tsv(os.path.join(work, "aggregate.tsv"), name, costs)
        print(f"cost aggregation: {samples} samples, {len(costs)} identical steps/commands; "
              "median ms and maximum other metrics")
    if record:
        for s, e, got in reversed(edits):
            lines[s + 1:e] = got.split("\n") if got else []
        with open(doc, "w", encoding="utf-8") as source:
            source.write("\n".join(lines))
        print(f"recorded {len(edits)} outputs into {doc}")
    if costs is not None:
        write_tsv(COST, name, costs)
    if "--cost-baseline" in args:
        if failures:
            print("cost baseline unchanged: functional or aggregation checks failed")
        else:
            write_tsv(BASELINE, name, costs)
            print(f"cost baseline: {len(costs)} steps of {name} into {BASELINE}")
    elif costs is not None:
        base = [b for b in read_tsv(BASELINE) if b["walkthrough"] == name]
        cost_failures = compare(costs, base)
        for msg in cost_failures:
            failures += 1
            print(msg)
        if not cost_failures:
            print(f"cost: all {len(costs)} steps compared against {BASELINE}")
    if failures:
        print(f"{failures} failure(s); work directory kept: {work}")
        sys.exit(1)
    print(f"walkthrough: {steps} steps ok" + (f" in all {samples} samples" if samples > 1 else ""))
    if supplied_work is None and samples == 1:
        shutil.rmtree(work)


if __name__ == "__main__":
    main()
