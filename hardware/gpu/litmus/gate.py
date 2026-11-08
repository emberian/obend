#!/usr/bin/env python3
"""The litmus gate's joins (hardware/gpu/verify_litmus.sh calls this; run with python3 -I).

  gate.py devices TABLE RESULTS_DIR     every outcome class a device observed has a model-allowed outcome;
                                        every model-allowed `weak` class is observed on some device or
                                        recorded in RESULTS_DIR/STRONGER.tsv, and no recorded test is observed
  gate.py dartagnan TABLE INDEX VERDICTS  Dartagnan's verdict (PASS: the `exists` outcome is reachable,
                                        FAIL: it is not) equals the model's (allowed / forbidden) on every file

TABLE is `obend-litmus-check table`'s output; INDEX is `obend-litmus-check dartagnan`'s index.tsv; VERDICTS
has one line per litmus file: file, Dartagnan's Result. Exit 1 with every disagreement on stderr.
"""
import os
import sys


def read_tsv(path):
    rows = []
    with open(path, encoding="utf-8") as f:
        header = None
        for line in f:
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            fields = line.split("\t")
            if header is None:
                header = fields
                continue
            rows.append(dict(zip(header, fields)))
    return rows


def model_classes(table):
    """test -> {class -> set of verdicts}"""
    out = {}
    for r in read_tsv(table):
        out.setdefault(r["test"], {}).setdefault(r["class"], set()).add(r["verdict"])
    return out


def devices(table, results_dir):
    model = model_classes(table)
    failures = []
    observed_weak = {}  # test -> [device]
    tables = sorted(f for f in os.listdir(results_dir) if f.endswith(".tsv") and f != "STRONGER.tsv")
    if not tables:
        failures.append(f"no result tables under {results_dir}")
    for name in tables:
        device = name[:-4]
        for r in read_tsv(os.path.join(results_dir, name)):
            test = r["test"]
            if test not in model:
                failures.append(f"{device}: {test} has no shape in the model")
                continue
            for item in r["outcomes"].split(";"):
                cls, count = item.split("=")
                count = int(count)
                if count == 0:
                    continue
                verdicts = model[test].get(cls, set())
                if "allowed" not in verdicts:
                    failures.append(
                        f"{device}: {test} showed the class {cls} ({count} instances) which the model forbids"
                    )
                if cls == "weak":
                    observed_weak.setdefault(test, []).append(device)
    stronger = {}
    stronger_path = os.path.join(results_dir, "STRONGER.tsv")
    if os.path.exists(stronger_path):
        for r in read_tsv(stronger_path):
            stronger[r["test"]] = r
    for test, classes in sorted(model.items()):
        if "allowed" not in classes.get("weak", set()):
            continue
        if test in observed_weak:
            if test in stronger:
                failures.append(
                    f"{test}: recorded in STRONGER.tsv but its weak outcome was observed on {', '.join(observed_weak[test])}"
                )
            continue
        if test not in stronger:
            failures.append(
                f"{test}: the model allows its weak outcome, no device showed it, and STRONGER.tsv does not record it"
            )
    for test in stronger:
        if test not in model:
            failures.append(f"STRONGER.tsv names {test}, which has no shape")
        elif "allowed" not in model[test].get("weak", set()):
            failures.append(f"STRONGER.tsv names {test}, whose weak outcome the model forbids (nothing to record)")
    return failures


def dartagnan(table, index, verdicts):
    model = {}
    for r in read_tsv(table):
        model[(r["test"], r["outcome"])] = r["verdict"]
    results = {}
    with open(verdicts, encoding="utf-8") as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) == 2:
                results[parts[0]] = parts[1]
    failures = []
    n = 0
    for r in read_tsv(index):
        n += 1
        want = model.get((r["test"], r["outcome"]))
        if want is None:
            failures.append(f"{r['file']}: not in the model's table")
            continue
        if want != r["verdict"]:
            failures.append(f"{r['file']}: index says {r['verdict']}, table says {want}")
        got = results.get(r["file"])
        if got is None:
            failures.append(f"{r['file']}: no Dartagnan verdict")
            continue
        expect = "PASS" if want == "allowed" else "FAIL"
        if got != expect:
            failures.append(f"{r['file']}: the model says {want}, Dartagnan says {got}")
    if n == 0:
        failures.append("empty index")
    return failures


def main(argv):
    if len(argv) >= 4 and argv[1] == "devices":
        failures = devices(argv[2], argv[3])
    elif len(argv) >= 5 and argv[1] == "dartagnan":
        failures = dartagnan(argv[2], argv[3], argv[4])
    else:
        print(__doc__, file=sys.stderr)
        return 2
    for f in failures:
        print(f"  {f}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
