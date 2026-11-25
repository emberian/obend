"""Compare standalone obend open on two private copies of a seed-7 large.py fixture."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def run_open(binary, vault):
    start = time.perf_counter_ns()
    p = subprocess.run([binary, "open"], cwd=vault, env=dict(os.environ, OBEND_COST="1"),
                       capture_output=True, text=True, check=True)
    return {"wall_ms": (time.perf_counter_ns() - start) / 1e6,
            "output": p.stdout.strip(), "cost": p.stderr.strip()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("--samples", type=int, default=3)
    args = parser.parse_args()
    if args.samples < 1:
        parser.error("--samples must be positive")
    with tempfile.TemporaryDirectory() as tmp:
        vaults = {}
        for mode, binary in [("before", args.before), ("after", args.after)]:
            vault = Path(tmp) / mode
            shutil.copytree(args.snapshot, vault, symlinks=True)
            vaults[mode] = (binary.resolve(), vault)
            result = run_open(binary.resolve(), vault)
            print(json.dumps(dict(mode=mode, operation="initialize", **result)), flush=True)
        for sample in range(args.samples):
            for mode in list(vaults)[::1 if sample % 2 == 0 else -1]:
                binary, vault = vaults[mode]
                for op in ("unchanged", "edit"):
                    if op == "edit":
                        page = vault / "acct/P0017.md"
                        old = page.read_text()
                        replacement = f"Public sample {sample}."
                        new = (old.rstrip() + "\n\n" + replacement + "\n" if sample == 0
                               else old.replace(f"Public sample {sample - 1}.", replacement))
                        if new == old:
                            raise ValueError("fixture edit produced identical text")
                        page.write_text(new)
                    result = run_open(binary, vault)
                    print(json.dumps(dict(mode=mode, operation=op, sample=sample, **result)), flush=True)


if __name__ == "__main__":
    main()
