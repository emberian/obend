#!/usr/bin/env python3
"""The planted test of lean/tests/reasons/REASONS.md: drop the well-foundedness and require the
walkthrough to fail.

The mutant is a copy of `lean/` (an APFS clone with `cp -c` where the filesystem has one, so the build
directory comes along warm) in which `Obend/Reasons.lean`'s `stage` starts from every atom the program
can name instead of from none. `Γ` is then the greatest fixpoint of the reduct's consequence, not the
least, and a cycle of premises supports itself. Every theorem of the module that has a proof of more
than one line is replaced by `sorry` (the theorems are what catch the mutant at build time; this test
asks the walkthrough to catch it at run time too). The mutant's `obend` is built and the walkthrough
run with it; a mutant whose walkthrough passes is a failure of this test.

    python3 tests/reasons/reasons_planted.py      # from lean/, after `lake build obend`
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))

STAGE = """  | 0 => []
  | n + 1 => T P J (stage P J n)"""

GREATEST = """  | 0 => P.facts ++ P.rules.map (·.concl)
  | n + 1 => T P J (stage P J n)"""


def sorry_theorems(src):
    """Replace by `sorry` the proof of every theorem whose `:=` ends a line, and of every theorem proved
    by equations (`| 0 => …`)."""
    out = []
    pos = 0
    for m in re.finditer(r"^theorem \S+", src, re.M):
        if m.start() < pos:
            continue
        end = src.find("\n\n", m.start())
        end = len(src) if end < 0 else end
        body = src[m.start():end]
        p = re.search(r":=( by)?\n", body)
        q = body.find("\n  | ")
        if p is not None and (q < 0 or p.start() < q):
            head = body[:p.start()]
        elif q >= 0:
            head = body[:q] + " "
        else:
            continue
        out.append(src[pos:m.start()])
        out.append(head + ":= by\n  sorry")
        pos = end
    out.append(src[pos:])
    return "".join(out)


def mutate(src):
    if src.count(STAGE) != 1:
        sys.exit("planted: stage's definition not found")
    return sorry_theorems(src.replace(STAGE, GREATEST))


def clone(dst):
    flags = ["-c", "-R"] if sys.platform == "darwin" else ["-R", "--reflink=auto"]
    subprocess.run(["cp", *flags, LEAN, dst], check=True)


def main():
    tmp = tempfile.mkdtemp(prefix="obend-reasons-planted-")
    lean = os.path.join(tmp, "lean")
    try:
        clone(lean)
        path = os.path.join(lean, "Obend", "Reasons.lean")
        src = open(path, encoding="utf-8").read()
        open(path, "w", encoding="utf-8").write(mutate(src))
        b = subprocess.run(["lake", "build", "obend"], cwd=lean, capture_output=True, text=True)
        if b.returncode != 0:
            print(f"FAIL greatest-fixpoint: the mutant does not build\n{b.stdout[-2000:]}{b.stderr[-2000:]}")
            sys.exit(1)
        w = subprocess.run([sys.executable, os.path.join(lean, "tests", "vault", "walkthrough.py"),
                            "--doc", os.path.join(lean, "tests", "reasons", "REASONS.md")],
                           cwd=lean, capture_output=True, text=True)
        red = [l for l in w.stdout.splitlines() if l.startswith("FAIL")]
        if w.returncode == 0:
            print("FAIL greatest-fixpoint: the walkthrough passed with a cycle supporting itself")
            sys.exit(1)
        print(f"ok   greatest-fixpoint: the walkthrough is red ({len(red)} step(s)):")
        for l in red:
            print("       " + l)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print("planted: the mutant turns the walkthrough red")


if __name__ == "__main__":
    main()
