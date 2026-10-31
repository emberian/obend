#!/usr/bin/env python3
"""Execute lean/tests/ledger/WALKTHROUGH.md: the acceptance test of the ledger (`Obend.Ledger`).

The runner is the vault's (`tests/vault/walkthrough.py`): every ```sh block runs in order under bash
in one work directory with the built `obend` first on PATH, and its output is compared exactly with
the ```text block after it; a block marked `refused` must exit non-zero.

    python3 tests/ledger/walkthrough.py            # from lean/, after `lake build obend`
    python3 tests/ledger/walkthrough.py --record   # rewrite the expected outputs (then read them!)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "vault"))
import walkthrough  # noqa: E402

walkthrough.DOC = os.path.join(HERE, "WALKTHROUGH.md")
walkthrough.main()
