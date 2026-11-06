#!/usr/bin/env python3
"""The planted test of lean/tests/vault/FORMS.md: take the membrane's checks out, one at a time, and
require the walkthrough to fail.

Each mutant is a copy of `lean/` (an APFS clone with `cp -c` where the filesystem has one, so the
build directory comes along warm) in which `Obend/Vault/Form.lean` has one check removed and the one
proof that states it replaced by `sorry` (the theorems are what would catch the mutant at build
time; this test asks the walkthrough to catch it at run time too). The mutant's `obend` is built and
the walkthrough run with it; a mutant whose walkthrough passes is a failure of this test.

    python3 tests/vault/forms_planted.py      # from lean/, after `lake build obend`

Mutants:
  page-gate   `checkPage` admits every page: the fill may name a page outside the form, or one the
              final viewer may not write (the guessed hidden page lands; so does Dave's read-only fill)
  chain-gate  `resolveChain` takes an amplifying hop as granted (the forged hop lands)
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))

PAGE_DEF = """  | .page n =>
    if !f.scope.contains n then .error (.notInForm n holder)
    else if !mayWrite v n then .error (.notWritable n holder v.held)
    else .ok ()"""

CHAIN_DEF = """    | none => .error (.amplifies who g.holder cur.held g.held)"""


def sorry_theorem(src, name):
    """Replace the tactic proof of theorem `name` (its `:= by` up to the next blank line) by `sorry`."""
    start = re.search(r"^theorem " + re.escape(name) + r"\b", src, re.M)
    if not start:
        sys.exit("planted: theorem " + name + " not found")
    end = src.find("\n\n", start.start())
    body = src[start.start():end]
    if body.count(":= by\n") != 1:
        sys.exit("planted: theorem " + name + " is not one tactic proof")
    head = body.split(":= by\n")[0]
    return src[:start.start()] + head + ":= by\n  sorry" + src[end:]


def mutate(src, which):
    if which == "page-gate":
        if PAGE_DEF not in src:
            sys.exit("planted: checkPage's page case not found")
        src = src.replace(PAGE_DEF, "  | .page _ => .ok ()")
        return sorry_theorem(src, "checkPage_ok")
    if which == "chain-gate":
        if CHAIN_DEF not in src:
            sys.exit("planted: resolveChain's refusal not found")
        src = src.replace(CHAIN_DEF, "    | none => resolveChain scope (g.viewer scope) g.holder rest")
        return sorry_theorem(src, "resolveChain_attenuates")
    raise ValueError(which)


def clone(dst):
    flags = ["-c", "-R"] if sys.platform == "darwin" else ["-R", "--reflink=auto"]
    subprocess.run(["cp", *flags, LEAN, dst], check=True)


def main():
    failures = 0
    for which in ["page-gate", "chain-gate"]:
        tmp = tempfile.mkdtemp(prefix="obend-forms-planted-")
        lean = os.path.join(tmp, "lean")
        try:
            clone(lean)
            form = os.path.join(lean, "Obend", "Vault", "Form.lean")
            src = open(form, encoding="utf-8").read()
            open(form, "w", encoding="utf-8").write(mutate(src, which))
            b = subprocess.run(["lake", "build", "obend"], cwd=lean, capture_output=True, text=True)
            if b.returncode != 0:
                print(f"FAIL {which}: the mutant does not build\n{b.stdout[-2000:]}{b.stderr[-2000:]}")
                failures += 1
                continue
            w = subprocess.run([sys.executable, os.path.join(lean, "tests", "vault", "walkthrough.py"),
                                "--doc", os.path.join(lean, "tests", "vault", "FORMS.md")],
                               cwd=lean, capture_output=True, text=True)
            red = [l for l in w.stdout.splitlines() if l.startswith("FAIL")]
            if w.returncode == 0:
                print(f"FAIL {which}: the walkthrough passed with the check removed")
                failures += 1
            else:
                print(f"ok   {which}: the walkthrough is red ({len(red)} step(s)):")
                for l in red:
                    print("       " + l)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    if failures:
        sys.exit(1)
    print("planted: every mutant turns the walkthrough red")


if __name__ == "__main__":
    main()
