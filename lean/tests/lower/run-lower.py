#!/usr/bin/env python3
"""Lean to Core4 end to end (Obend.Lower): `obend lower` on tests/lower/Programs.lean.

  * every first program (`double`, `fib` by structural recursion, `pointNorm` through `structure Point`
    and its methods, `shapeArea` through `inductive Shape` and a `match`, `addLit` through the kernel's
    `Nat.add` on literals, `sumTo` by `Nat.rec`, `small` through `if`/`Decidable`, `isEven` to `Bool`,
    `halvings` by well-founded recursion on a `Nat` measure, `ackTwo` by well-founded recursion on a
    lexicographic one)
    is read into the fragment, lowered, run on the demand machine at several arguments, and compared
    with `#eval` of the Lean original;
  * every one is accepted by Core4's checker at the type its Lean type lowers to; `fib` and
    `halvings` are read from their unfolding equations (`f.eq_def`, the reader reports it) and lowered
    to a simply typed `fix`; with `--kernel-recursion`, `fib` is read through `Nat.brecOn`, which runs
    but computes a type by recursion (`Nat.below`) and is refused by the checker;
  * `kTooth` (the K-like recursor of a field-less proposition on its erased proof, `lower_complete_fails`)
    runs to the value the kernel computes (`kTooth_three : kTooth 3 = 3 := rfl`);
  * every lowering's `lower@1` certificate is accepted by `obend lower --verify`;
  * `double` is emitted as a Leaf book and the book computes what the machine computes.

Teeth (each must be refused):
  * a certificate checked against another program's source (`otherSource`/`notTheLowering`);
  * a certificate whose lowered term is mutated (`Nat.add` turned to `subtract`);
  * `countDown` (`WellFounded.fix` used directly: `Acc.rec` on a proof) and `greeting` (a string) are
    outside the fragment.

usage: python3 tests/lower/run-lower.py [OBEND_BINARY]   (from lean/, after `lake build LowerPrograms obend`)
exit 0 when every check holds, 1 otherwise; a summary line last.
"""
import json, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
OBEND = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LEAN, ".lake", "build", "bin", "obend")
PROGRAMS = os.path.join(HERE, "Programs.lean")

failures = []
count = 0


def check(name, ok, detail=""):
    global count
    count += 1
    if ok:
        print(f"ok   {name}")
    else:
        failures.append(name)
        print(f"FAIL {name}: {detail}")


def obend(*args):
    r = subprocess.run([OBEND, *args], capture_output=True, text=True, cwd=LEAN)
    return r.returncode, r.stdout + r.stderr


CASES = {
    "double": [0, 1, 21, 1000],
    "fib": [0, 1, 2, 10, 15],
    "pointNorm": [0, 5, 77],
    "shapeArea": [0, 3, 10],
    "addLit": [0, 41],
    "sumTo": [0, 1, 10, 100],
    "small": [0, 2, 3, 10],
    "isEven": [0, 7, 10],
    "halvings": [0, 1, 10, 1000],
    "ackTwo": [0, 3, 5],
}
TYPED = set(CASES)


def lean_evals():
    """`#eval` of every case in the Lean original, in order."""
    src = open(PROGRAMS).read()
    lines = [f"#eval {name} {n}" for name, ns in CASES.items() for n in ns]
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "Evals.lean")
        with open(path, "w") as f:
            f.write(src + "\n" + "\n".join(lines) + "\n")
        r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True, cwd=LEAN)
    out = [l.strip() for l in r.stdout.splitlines() if l.strip()]
    return out


expected = lean_evals()
check("lean #eval of every case", len(expected) == sum(len(v) for v in CASES.values()), f"{expected[:5]}…")
pairs = [(name, n) for name, ns in CASES.items() for n in ns]
want = dict(zip(pairs, expected))

with tempfile.TemporaryDirectory() as out:
    for name, ns in CASES.items():
        rc, text = obend("lower", name, "--out", out)
        check(f"{name}: read and lowered", rc == 0 and "core4:" in text, text[-400:])
        accepted = "checked: accepted" in text
        if name in TYPED:
            check(f"{name}: accepted by checkAgainst", accepted, text[-400:])
        else:
            check(f"{name}: refused by the checker (outside the simply typed fragment)",
                  not accepted and "checked: refused" in text, text[-400:])
        check(f"{name}: lower@1 accepted at production", "lower@1: accepted" in text, text[-300:])
        for n in ns:
            rc, text = obend("lower", name, "--arg", str(n))
            m = re.search(rf"^machine: {name} {n} = (.*)$", text, re.M)
            got = m.group(1).strip() if m else None
            check(f"{name} {n}: machine {got} = #eval {want.get((name, n))}", got == want.get((name, n)), text[-300:])
        rc, text = obend("lower", "--verify", os.path.join(out, f"{name}.lower.json"),
                         os.path.join(out, f"{name}.source.json"))
        check(f"{name}: certificate verified", rc == 0 and "accepted" in text, text)

        rc, text = obend("lower", "fib", "--arg", "10", "--kernel-recursion")
    check("fib through Nat.brecOn: reported, runs, refused by the checker",
          "read through its kernel value" in text and "checked: refused" in text
          and re.search(r"^machine: fib 10 = 55$", text, re.M) is not None, text[-300:])
    rc, text = obend("lower", "fib")
    check("fib is read from fib.eq_def", "read from fib.eq_def" in text, text[-300:])
    rc, text = obend("lower", "kTooth", "--arg", "3")
    check("kTooth: Core4 computes what the kernel computes (3)", re.search(r"^machine: kTooth 3 = 3$", text, re.M)
          is not None and "checked: accepted" in text, text[-300:])

    # teeth on the certificate
    rc, text = obend("lower", "--verify", os.path.join(out, "double.lower.json"),
                     os.path.join(out, "addLit.source.json"))
    check("tooth: another program's source refuses the certificate", rc == 3 and "refused" in text, text)
    cert = json.load(open(os.path.join(out, "addLit.lower.json")))
    blob = json.dumps(cert)
    mutated = blob.replace('"add"', '"subtract"', 1)
    check("tooth: the certificate's term has an add to mutate", mutated != blob)
    bad = os.path.join(out, "mutated.lower.json")
    with open(bad, "w") as f:
        f.write(mutated)
    rc, text = obend("lower", "--verify", bad, os.path.join(out, "addLit.source.json"))
    check("tooth: a mutated lowered term is refused", rc == 3 and "refused" in text, text)

    # the composition: Lean to the Leaf book
    book = os.path.join(out, "double.book.json")
    rc, text = obend("lower", "double", "--arg", "21", "--emit", book)
    m1 = re.search(r"^machine: double 21 = (\S+)", text, re.M)
    m2 = re.search(r"^book: double 21 = (\S+)", text, re.M)
    check("double as a Leaf book: the book's answer is the machine's",
          rc == 0 and m1 and m2 and m1.group(1) == m2.group(1) == want[("double", 21)], text[-400:])
    check("the book is written", os.path.exists(book))

for name in ["countDown", "greeting"]:
    rc, text = obend("lower", name)
    check(f"tooth: {name} is outside the fragment", rc == 3 and "outside the fragment" in text, text[-300:])

print(f"{count - len(failures)}/{count} checks hold" + ("" if not failures else f"; failing: {', '.join(failures)}"))
sys.exit(1 if failures else 0)
