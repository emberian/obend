#!/usr/bin/env python3
"""Execute the two decisions walkthroughs: lean/tests/decisions/WALKTHROUGH.md (the project's
decisions ledger as a vault, one decision per page) and LEDGER.md (review/DECISIONS-20261031.md
itself under its kind, on a copy). Both name the environment `lean/.lake/build/census/environment.txt`
(the census's list of the library's names); when it is missing this runner writes it first from the
tier-1 library (`lake env lean tests/decisions/Environment.lean`).

The runner is tests/vault/walkthrough.py (every ```sh block run in order in one work directory
with the built `obend` on PATH, the ```text block after it its expected output), pointed at each
document in turn.

    python3 tests/decisions/walkthrough.py            # from lean/, after `lake build obend`
    python3 tests/decisions/walkthrough.py --record   # rewrite the expected outputs (then read them!)
    python3 tests/decisions/walkthrough.py --doc PATH # one document only
    python3 tests/decisions/walkthrough.py --work DIR # keep the work directories (DIR-1, DIR-2)
"""
import os
import runpy
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
RUNNER = os.path.join(os.path.dirname(HERE), "vault", "walkthrough.py")
ENVIRONMENT = os.path.join(LEAN, ".lake", "build", "census", "environment.txt")


def ensure_environment():
    if os.path.exists(ENVIRONMENT):
        return
    print("writing the environment: lake env lean tests/decisions/Environment.lean")
    r = subprocess.run(["lake", "env", "lean", "tests/decisions/Environment.lean"], cwd=LEAN)
    if r.returncode != 0 or not os.path.exists(ENVIRONMENT):
        sys.exit("the environment could not be written")


def main():
    ensure_environment()
    args = sys.argv[1:]
    if "--doc" in args:
        i = args.index("--doc")
        docs = [os.path.abspath(args[i + 1])]
        args = args[:i] + args[i + 2:]
    else:
        docs = [os.path.join(HERE, "WALKTHROUGH.md"), os.path.join(HERE, "LEDGER.md")]
    work = None
    if "--work" in args:
        i = args.index("--work")
        work = args[i + 1]
        args = args[:i] + args[i + 2:]
    failed = 0
    for n, doc in enumerate(docs, 1):
        print(f"== {os.path.relpath(doc, LEAN)}")
        extra = ["--work", f"{work}-{n}" if len(docs) > 1 else work] if work else []
        sys.argv = [RUNNER, "--doc", doc] + args + extra
        try:
            runpy.run_path(RUNNER, run_name="__main__")
        except SystemExit as e:
            if e.code:
                failed += 1
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
