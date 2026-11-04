#!/usr/bin/env python3
"""Execute lean/tests/decisions/WALKTHROUGH.md: the project's decisions ledger as an obend vault.

The same runner as tests/vault/walkthrough.py (every ```sh block run in order in one work
directory with the built `obend` on PATH, the ```text block after it its expected output), pointed
at this directory's WALKTHROUGH.md.

    python3 tests/decisions/walkthrough.py            # from lean/, after `lake build obend`
    python3 tests/decisions/walkthrough.py --record   # rewrite the expected outputs (then read them!)
"""
import os
import runpy
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.argv = [sys.argv[0], "--doc", os.path.join(HERE, "WALKTHROUGH.md")] + sys.argv[1:]
runpy.run_path(os.path.join(os.path.dirname(HERE), "vault", "walkthrough.py"), run_name="__main__")
