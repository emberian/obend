#!/usr/bin/env python3
"""Workspaces: cross-package extension run end to end through `obend` (Obend.Spec.Workspace).

Two workspaces under tests/obend-source/, each a `dregg.objective-bend.workspace.v1`:

  * three-package/: commons/counter (the base), ext/left (extends it by name, @^1), ext/right
    (extends it by content hash, @0x...), app/both (extends both). The base is reached by two
    routes and applied once; compose(E, E) across the boundary still applies E twice; a moved
    record makes the two routes disagree (refused by name); a re-pinned record makes a recorded
    turn stale by name; the four packages' laws judge a write as one effective law whose refusal
    names the ancestor package and clause.
  * stranger/: Astra's report extended by a stranger (ASTRA-SYNTHESIS-20261029 §G): papers/report
    (a report kind with a cited section and a publication law), lab/review (another owner adds a
    review section), kit/export (a third declares an Export protocol for the report's Page),
    notes/garden (the notebook that uses all three); kit/pdf and kit/html, two independent
    implementations of Export for Page: competing (refused), resolved by a package extending both,
    and the more specific one selected when only one is in the closure.

usage: python3 tests/run-workspace.py [OBEND_BINARY]      (from lean/, after `lake build obend`)
exit 0 when every check holds, 1 otherwise; a summary line last.
"""
import json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
SOURCE = os.path.join(HERE, "obend-source")
OBEND = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LEAN, ".lake", "build", "bin", "obend")

failures = []
count = 0


def obend(*args):
    r = subprocess.run([OBEND, *args], capture_output=True, text=True, cwd=LEAN)
    return r.returncode, r.stdout


def check(name, ok, detail=""):
    global count
    count += 1
    print(("ok   " if ok else "FAIL ") + name + ("" if ok else ": " + detail))
    if not ok:
        failures.append(name)


def run_lines(ws, *extra):
    code, out = obend("run", "--package", ws, *extra)
    return code, out.splitlines()


def expect_run(name, ws, lines, *extra):
    code, got = run_lines(ws, *extra)
    check(name, got[:len(lines)] == lines, "\n  want " + repr(lines) + "\n  got  " + repr(got))


def judge(ws, old, new):
    _, out = obend("judge", "--package", ws, json.dumps(old), json.dumps(new))
    return json.loads(out)


# ---------------------------------------------------------------- three packages

T = os.path.join(SOURCE, "three-package")
ws = os.path.join(T, "workspace.json")
expect_run("diamond: C4 over the spec diamond across four packages", ws,
           ["status: finished", "type: Nat", "result: 1324",
            "package: app/both > ext/left > ext/right > commons/counter",
            "pin: ext/left@^1 = 1.0.0 (record pin 1)",
            "pin: commons/counter@^1 = 1.0.0 (record pin 3)",
            "pin: ext/right@^1 = 1.0.0 (record pin 1)"])
expect_run("diamond: the base's weight is counted once", ws, ["status: finished", "type: Nat", "result: 1111"],
           "--entry", "weighed")
expect_run("compose(E, E) applies E twice across the boundary", ws, ["status: finished", "type: Nat", "result: 7"],
           '["5"]', "--entry", "twice")
code, got = run_lines(ws, "--entry", "interface")
check("reflection: precedence keys are (intention, declaration)",
      len(got) > 2 and '\\"precedence\\":[\\"app/both::Both.Both\\",\\"ext/left::Left.Left\\",\\"ext/right::Right.Right\\",\\"commons/counter::Counter.Base\\"]' in got[2],
      repr(got[2:3]))
code, got = run_lines(ws)
check("an extension parent is pinned by hash", any(l.startswith("pin: commons/counter@0x") and l.endswith("(fixed)") for l in got), repr(got))
expect_run("a moved record: two routes reach two releases, refused by name", os.path.join(T, "workspace-moved.json"),
           ["status: refused", "stage: objective-workspace",
            "message: refused (incompatible-revisions): commons/counter is resolved to 1.1.0 by one route and 1.0.0 by another"])

with tempfile.TemporaryDirectory() as work:
    _, out = obend("run", "--package", ws, "--json")
    turn = json.loads(out)["turn"]
    path = os.path.join(work, "turn.json")
    with open(path, "w") as f:
        json.dump(turn, f)
    code, out = obend("admit", "--package", ws, path)
    check("a turn re-derives at its own records: admitted", code == 0 and json.loads(out)["status"] == "admitted", out)
    code, out = obend("admit", "--package", os.path.join(T, "workspace-left-repinned.json"), path)
    a = json.loads(out)
    check("a re-pinned record: the turn is stale, by name", code == 3 and a["status"] == "stale" and a["name"] == "ext/left", out)
    code, out = obend("admit", "--package", os.path.join(T, "workspace-moved.json"), path)
    a = json.loads(out)
    check("a moved base: stale before anything is re-derived", code == 3 and a["status"] == "stale" and a["name"] == "commons/counter", out)

j = judge(ws, {"total": 3}, {"total": 5})
check("the effective law: every package's clauses, in precedence order",
      j["status"] == "admitted" and j["clauses"] == ["app/both law unlucky", "ext/left law monotone",
                                                     "ext/right law capped", "commons/counter law bounded"], repr(j))
for old, new, by in [(3, 13, "app/both law unlucky"), (5, 3, "ext/left law monotone"),
                     (5, 60, "ext/right law capped"), (60, 200, "ext/right law capped")]:
    j = judge(ws, {"total": old}, {"total": new})
    check(f"refusal {old} -> {new} names {by}", j.get("status") == "refused" and j.get("by") == by, repr(j))

print(f"WORKSPACES: {count - len(failures)}/{count} checks hold")
sys.exit(1 if failures else 0)
