#!/usr/bin/env python3
"""Execute lean/tests/vault/CRASH.md: `obend` stopped in the middle of a write, and the vault opened
again (`Obend.Vault.Log`, `Obend.Vault.Replay`).

The runner is the vault's (`tests/vault/walkthrough.py`): every ```sh block runs in order under bash
in one work directory with the built `obend` first on PATH, and its output is compared exactly with
the ```text block after it; a block marked `refused` must exit non-zero.

    python3 tests/vault/crash.py            # from lean/, after `lake build obend`
    python3 tests/vault/crash.py --record   # rewrite the expected outputs (then read them!)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import walkthrough  # noqa: E402

walkthrough.DOC = os.path.join(HERE, "CRASH.md")
walkthrough.main()
