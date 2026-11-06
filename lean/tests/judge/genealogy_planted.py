#!/usr/bin/env python3
"""The planted test of lean/tests/judge/GENEALOGY.md: take succession's non-regression check out and
require the walkthrough to fail.

The mutant is a copy of `lean/` (an APFS clone with `cp -c` where the filesystem has one, a reflink
or a copy elsewhere, so the build directory comes along warm) in which `succeed`
(`Obend/Judge/Genealogy.lean`) no longer runs `nonRegression`, and the proofs that state the check
(`succeed_parts`, `succeed_self`, and the planted certificate `planted_refused`) are replaced by
`sorry`: the theorems are what would catch the mutant at build time; this test asks the walkthrough
to catch it at run time too. A mutant whose walkthrough passes is a failure of this test.

    python3 tests/judge/genealogy_planted.py      # from lean/, after `lake build obend`
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))

CHECK = "  both (nonRegression G G') <|\n"
SORRIED = ["succeed_parts", "succeed_self", "planted_refused"]


def sorry_theorem(src, name):
    """Replace the proof of theorem `name` (from its first `:= by` or `:= rfl` to the next blank line) by `sorry`."""
    start = re.search(r"^theorem " + re.escape(name) + r"\b", src, re.M)
    if not start:
        sys.exit("planted: theorem " + name + " not found")
    end = src.find("\n\n", start.start())
    body = src[start.start():end]
    m = re.search(r":= (by\n|rfl$)", body, re.M)
    if not m:
        sys.exit("planted: theorem " + name + " has no `:= by` or `:= rfl` proof")
    return src[:start.start()] + body[:m.start()] + ":= by\n  sorry" + src[end:]


def mutate(src):
    if src.count(CHECK) != 1:
        sys.exit("planted: succeed's non-regression line not found")
    src = src.replace(CHECK, "")
    for name in SORRIED:
        src = sorry_theorem(src, name)
    return src


def clone(dst):
    flags = ["-c", "-R"] if sys.platform == "darwin" else ["-R", "--reflink=auto"]
    subprocess.run(["cp", *flags, LEAN, dst], check=True)


def main():
    tmp = tempfile.mkdtemp(prefix="obend-genealogy-planted-")
    lean = os.path.join(tmp, "lean")
    try:
        clone(lean)
        path = os.path.join(lean, "Obend", "Judge", "Genealogy.lean")
        src = open(path, encoding="utf-8").read()
        open(path, "w", encoding="utf-8").write(mutate(src))
        b = subprocess.run(["lake", "build", "obend"], cwd=lean, capture_output=True, text=True)
        if b.returncode != 0:
            print(f"FAIL non-regression: the mutant does not build\n{b.stdout[-2000:]}{b.stderr[-2000:]}")
            sys.exit(1)
        w = subprocess.run([sys.executable, os.path.join(lean, "tests", "vault", "walkthrough.py"),
                            "--doc", os.path.join(lean, "tests", "judge", "GENEALOGY.md")],
                           cwd=lean, capture_output=True, text=True)
        red = [l for l in w.stdout.splitlines() if l.startswith("FAIL")]
        if w.returncode == 0:
            print("FAIL non-regression: the walkthrough passed with the check removed")
            sys.exit(1)
        print(f"ok   non-regression: the walkthrough is red ({len(red)} step(s)):")
        for l in red:
            print("       " + l)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print("planted: the mutant turns the walkthrough red")


if __name__ == "__main__":
    main()
