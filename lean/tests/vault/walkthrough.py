#!/usr/bin/env python3
"""Execute lean/tests/vault/WALKTHROUGH.md: the acceptance test of `obend open`.

Every ```sh block runs, in order, under bash in one work directory, with the built `obend`
(lean/.lake/build/bin/obend) first on PATH. The ```text block that follows a ```sh block is its
expected output (stdout and stderr together), compared exactly. A ```sh block marked `refused`
must exit non-zero; any other must exit 0.

    python3 tests/vault/walkthrough.py            # from lean/, after `lake build obend`
    python3 tests/vault/walkthrough.py --work DIR # run in DIR (must not exist) and keep it
    python3 tests/vault/walkthrough.py --record   # rewrite the expected outputs (then read them!)
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
DOC = os.path.join(HERE, "WALKTHROUGH.md")
BIN = os.path.join(LEAN, ".lake", "build", "bin")

FENCE = re.compile(r"^```(\w*)(.*)$")


def blocks(text):
    """The document as a list of (kind, info, body, start, end) for fenced blocks."""
    lines = text.split("\n")
    out = []
    i = 0
    while i < len(lines):
        m = FENCE.match(lines[i])
        if m and m.group(1):
            j = i + 1
            while j < len(lines) and lines[j] != "```":
                j += 1
            out.append((m.group(1), m.group(2).strip(), "\n".join(lines[i + 1:j]), i, j))
            i = j + 1
        else:
            i += 1
    return out


def main():
    args = sys.argv[1:]
    record = "--record" in args
    work = None
    if "--work" in args:
        work = os.path.abspath(args[args.index("--work") + 1])
        os.makedirs(work)
    else:
        work = tempfile.mkdtemp(prefix="obend-walkthrough-")
    if not os.path.exists(os.path.join(BIN, "obend")):
        sys.exit("build obend first: lake build obend")
    env = dict(os.environ, PATH=BIN + os.pathsep + os.environ["PATH"], LC_ALL="C.UTF-8")
    text = open(DOC, encoding="utf-8").read()
    bs = blocks(text)
    lines = text.split("\n")
    edits = []
    failures = 0
    steps = 0
    for k, (kind, info, body, start, end) in enumerate(bs):
        if kind != "sh":
            continue
        steps += 1
        r = subprocess.run(["bash", "-c", body], cwd=work, env=env, capture_output=True, text=True)
        got = (r.stdout + r.stderr).rstrip("\n")
        want_fail = info == "refused"
        if (r.returncode != 0) != want_fail:
            failures += 1
            print(f"FAIL step {steps} (line {start + 1}): exit {r.returncode}, expected "
                  f"{'non-zero' if want_fail else '0'}\n{got}")
        nxt = bs[k + 1] if k + 1 < len(bs) else None
        if nxt and nxt[0] == "text" and nxt[3] == end + 2:
            if record:
                edits.append((nxt[3], nxt[4], got))
            elif nxt[2] != got:
                failures += 1
                print(f"FAIL step {steps} (line {start + 1}): output differs\n--- expected\n{nxt[2]}\n--- got\n{got}")
            else:
                print(f"ok   step {steps} (line {start + 1})")
        else:
            print(f"ok   step {steps} (line {start + 1}) (no expected output)")
    if record:
        for s, e, got in reversed(edits):
            lines[s + 1:e] = got.split("\n") if got else []
        open(DOC, "w", encoding="utf-8").write("\n".join(lines))
        print(f"recorded {len(edits)} outputs into {DOC}")
    if failures:
        print(f"{failures} failure(s); work directory kept: {work}")
        sys.exit(1)
    print(f"walkthrough: {steps} steps ok")
    if "--work" not in args:
        shutil.rmtree(work)


if __name__ == "__main__":
    main()
