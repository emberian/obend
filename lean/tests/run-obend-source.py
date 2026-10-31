#!/usr/bin/env python3
"""The source cohorts of the Objective Bend front end, run through `obend` (Obend.Spec).

Three conformance checks, all against outcomes minidregg pinned (commit 092027a2):

  * the LTUO probe cohort (tests/obend-source/ltuo/probe-cohort.json, 30 probes): each probe is
    captured as a package and previewed (`obend run --package ... --json`); the pinned `current`
    outcome must hold: status, the finished value, or a refusal message the pinned text prefixes
    (minidregg tests/objective-bend-source/ltuo/check-probes.ts);
  * the tutorial (tests/obend-source/tutorial/TUTORIAL.md, 16 chapters, 71 commands): every
    `$ bun docs/tutorial/run.ts ...` block is re-run as `obend run ...` and its printed lines
    must be equal, byte for byte, after one renaming: a machine diagnostic names
    `Obend.Core.Machine.` where Mini's named `Minidregg.Theory.ObjectiveBendDemandMachine.`
    (minidregg scripts/check-objective-tutorial.ts);
  * the preview cohort (tests/obend-source/preview-cohort.json, 161 items, multi-module packages
    included): each item is captured (`obend capture`) and previewed from a `preview-input.v2`
    request (`obend preview`), exactly as minidregg tests/objective-bend-source/check-preview.ts
    drives it; its expectations (`expected`, `expectedStatus`, `expectedRefusal`, `expectedTurns`,
    `expectedLastPlan`, `expectedType`, `expectedData`, `expectedDataStatus`, `expectedRecord`, the
    kernel Plan protocol) are checked as there, and the four request mutations after it (a wrong
    capture pin refuses, checkWork 1 is a named budget refusal, ticks 1 and heap 1 suspend).

Deviation from Mini: requests carry `checkWork` (the checker's work grant, Obend.Elab.Work.checkWork),
not Mini's nesting `typeFuel`; LIMITS pins 43237, the most any cohort program needs (MEASURED
2026-10-31, Market-book-*), where Mini pinned typeFuel 4096 (lean/docs/REPORT-SPEC-20261030.md).

A probe or a command whose outcome differs from Mini's is a port defect, not a new truth.

usage: python3 tests/run-obend-source.py [OBEND_BINARY]     (from lean/, after `lake build obend`)
exit 0 when every probe and every command holds, 1 otherwise; a summary line last.
"""
import hashlib, json, os, re, shlex, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
SOURCE = os.path.join(HERE, "obend-source")
OBEND = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LEAN, ".lake", "build", "bin", "obend")
RENAME = ("Minidregg.Theory.ObjectiveBendDemandMachine.", "Obend.Core.Machine.")


def run(args, cwd=LEAN):
    r = subprocess.run([OBEND, *args], cwd=cwd, capture_output=True, text=True)
    return r.returncode, r.stdout, r.stderr


# ---------------------------------------------------------------- probes

def probe_outcome(item, work):
    """check-probes.ts: capture the probe's modules as a package, preview with no responses."""
    cohort_dir = os.path.join(SOURCE, "ltuo")
    d = os.path.join(work, item["name"])
    os.mkdir(d)
    spec = {
        "schema": "dregg.objective-bend.package-input.v1", "edition": "objective-bend-1",
        "modules": [{"name": m["name"], "sourcePath": os.path.join(cohort_dir, m["source"]),
                     "imports": m.get("imports", [])} for m in item["modules"]],
        "entryModule": str(len(item["modules"]) - 1), "entryDefinition": item["entry"]}
    spec_path = os.path.join(d, "package-input.json")
    with open(spec_path, "w") as f:
        json.dump(spec, f, indent=2)
    code, out, err = run(["run", "--package", spec_path, json.dumps(item.get("arguments", [])), "[]", "--json"])
    try:
        result = json.loads(out)
    except json.JSONDecodeError:
        return {"status": "refused", "refusal": (err or out).strip()[:400]}, "no JSON: " + (err or out)[:200]
    if result.get("status") == "refused":
        message = str(result.get("diagnostic", {}).get("message", ""))
        return {"status": "refused", "refusal": message}, message
    status = result.get("status")
    if status == "finished":
        value = result.get("result", {}).get("value")
        # JavaScript String(): booleans print lowercase, naturals are already decimal strings.
        if isinstance(value, bool):
            value = "true" if value else "false"
        return {"status": "finished", "value": str(value)}, ""
    return {"status": status, "refusal": str(result.get("diagnostic", ""))}, str(result.get("diagnostic", ""))


def matches(actual, pinned):
    return (actual["status"] == pinned["status"]
            and (pinned.get("value") is None or actual.get("value") == pinned["value"])
            and (pinned.get("refusal") is None or actual.get("refusal", "").startswith(pinned["refusal"])))


def probes():
    with open(os.path.join(SOURCE, "ltuo", "probe-cohort.json")) as f:
        cohort = json.load(f)
    red = []
    rows = []
    with tempfile.TemporaryDirectory(prefix="obend-probes-") as work:
        for item in cohort:
            actual, message = probe_outcome(item, work)
            is_current = matches(actual, item["current"])
            target_met = matches(actual, item["target"])
            promoted = json.dumps(item["current"], sort_keys=True) == json.dumps(item["target"], sort_keys=True)
            if not is_current:
                verdict = ("RED: meets its target; promote current := target" if target_met
                           else "RED: outcome moved, matches neither current nor target")
                red.append(f"{item['name']}: {verdict} actual={json.dumps(actual)}")
            else:
                verdict = "met" if promoted else "pending " + item["owner"]
            rows.append((item["name"], verdict, actual, message))
    for name, verdict, actual, message in rows:
        shown = actual["status"] + ("=" + actual["value"] if "value" in actual else "")
        print(f"{name:<28} {verdict:<14} {shown}" + (f"  [{message[:120]}]" if message else ""))
    pending = [r for r in rows if r[1].startswith("pending")]
    print(f"LTUO PROBES: {len(rows)} rows pinned, {len(rows) - len(pending)} at target, "
          f"{len(pending)} pending ({' '.join(sorted({r[1].split(' ', 1)[1] for r in pending}))}); "
          f"{len(rows) - len(red)} of {len(rows)} at Mini's pinned current outcome")
    for line in red:
        print("  " + line)
    return len(red) == 0, len(rows), len(red)


# ---------------------------------------------------------------- tutorial

def tutorial_commands():
    """Every `$ bun docs/tutorial/run.ts ...` command of the tutorial with its printed lines."""
    with open(os.path.join(SOURCE, "tutorial", "TUTORIAL.md")) as f:
        text = f.read()
    commands = []
    for block in re.findall(r"```sh\n(.*?)```", text, re.S):
        lines = block.split("\n")
        i = 0
        while i < len(lines):
            if lines[i].startswith("$ bun docs/tutorial/run.ts "):
                command = lines[i][len("$ "):]
                i += 1
                expected = []
                while i < len(lines) and lines[i] != "" and not lines[i].startswith("$ "):
                    expected.append(lines[i])
                    i += 1
                commands.append((command, expected))
            else:
                i += 1
    return commands


def tutorial():
    commands = tutorial_commands()
    red = []
    for command, expected in commands:
        words = shlex.split(command)  # bun docs/tutorial/run.ts FILE ENTRY ...
        file = os.path.join(SOURCE, "tutorial", os.path.basename(words[2]))
        args = ["run", file, *words[3:]]
        code, out, err = run(args)
        got = out.rstrip("\n").split("\n") if out else []
        want = [e.replace(*RENAME) for e in expected]
        exit_line = [e for e in want if e.startswith("(exit status ")]
        want_lines = [e for e in want if not e.startswith("(exit status ")]
        want_code = int(exit_line[0][len("(exit status "):-1]) if exit_line else 0
        ok = got == want_lines and code == want_code
        print(("ok   " if ok else "RED  ") + command[len("bun docs/tutorial/run.ts "):])
        if not ok:
            red.append(command)
            print("   expected (exit %d):" % want_code)
            for e in want_lines:
                print("     " + e)
            print("   got (exit %d):" % code)
            for g in got:
                print("     " + g)
            if err.strip():
                print("   stderr: " + err.strip()[:300])
    print(f"TUTORIAL: {len(commands)} commands, {len(commands) - len(red)} equal to Mini's printed output "
          f"(after the one renaming), {len(red)} differ")
    return len(red) == 0, len(commands), len(red)


# ---------------------------------------------------------------- preview cohort (check-preview.ts)

LIMITS = {"ticks": "100000", "heap": "100000", "stack": "10000", "checkWork": "43237"}


def sha256_file(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def canonical(v):
    return json.dumps(v, sort_keys=True, separators=(",", ":"))


def norm(d):
    """Typed data with record fields ordered by name (materialization keeps source order)."""
    if isinstance(d, dict) and d.get("tag") == "record":
        return {**d, "fields": sorted(({"name": f["name"], "value": norm(f["value"])} for f in d["fields"]),
                                      key=lambda f: f["name"])}
    if isinstance(d, dict) and d.get("tag") == "variant":
        return {**d, "payload": norm(d.get("payload"))}
    return d


def field_of(d, name):
    if isinstance(d, dict) and d.get("tag") == "record":
        for f in d["fields"]:
            if f["name"] == name:
                return f["value"]
    return None


def natural(d):
    return isinstance(d, dict) and d.get("tag") == "natural" and re.fullmatch(r"[0-9]+", str(d.get("value"))) is not None


def plan_kind(p):
    if not (isinstance(p, dict) and p.get("tag") == "variant" and isinstance(p.get("payload"), dict)
            and p["payload"].get("tag") == "record"):
        return None
    f = lambda n: field_of(p["payload"], n)
    if p["label"] == "await":
        on = f("on")
        source = (isinstance(on, dict) and on.get("tag") == "variant" and (
            (on["label"] == "reply" and natural(field_of(on.get("payload"), "decider"))) or
            (on["label"] == "height" and natural(field_of(on.get("payload"), "at")))))
        write = f("write")
        return "await" if (isinstance(write, dict) and write.get("tag") == "record" and source
                           and natural(f("patience")) and int(f("patience")["value"]) > 0) else None
    if p["label"] == "transfer":
        write = f("write")
        return "transfer" if (isinstance(write, dict) and write.get("tag") == "record" and natural(f("to"))
                              and natural(f("amount")) and int(f("amount")["value"]) > 0) else None
    if p["label"] == "commit":
        write = f("write")
        return "commit" if isinstance(write, dict) and write.get("tag") == "record" else None
    return None


# A pin Mini's own later code contradicts: the cohort was pinned on 2026-10-07; minidregg 1653897b6
# (2026-10-08, "Bound objective-call extraction by the remaining turn allowance") split
# `Data.Failure.suspended` into `tickExhausted` (the forcing countdown ran out) and `suspended`
# (capacity or policy), and its validation list did not include check-preview. `neverFinishing`'s
# deep view exhausts its TICKS (heap 5000 would trip capacity; heap 100000 does not), so Mini's
# current code prints `tickExhausted` where the pin says `suspended`. Held here at the outcome of
# Mini's current code, by name, so that a change in it is still red; the port is unchanged.
STALE_PINS = {
    "Structured-neverFinishing-no-partial-value": ("expectedDataStatus", "suspended", "tickExhausted", "minidregg 1653897b6"),
}

AWAIT_OUTCOMES = ["reply", "refused", "unknown", "timedOut", "broken", "upgraded"]
TRANSFER_OUTCOMES = ["settled", "refused"]
COMMIT_OUTCOMES = ["settled"]


def source_path(cohort_dir, source):
    """A cohort source. Mini's Market rows import `../../world/market/*.obend` (its `world/` tree);
    those seven files are copied under tests/obend-source/world/market/."""
    if source.startswith("../../world/"):
        return os.path.join(cohort_dir, "world", source[len("../../world/"):])
    return os.path.join(cohort_dir, source)


def capture_and_preview(item, work, cohort_dir, request_change=None, name=None):
    """check-preview.ts's per-item drive: package-input, `obend capture`, a preview-input.v2 request,
    `obend preview`; returns (result, request) where result is preview.json, diagnostic.json or a
    refusal record, as front.ts's `preview` returns it."""
    name = name or item["name"]
    d = os.path.join(work, name)
    os.makedirs(d)
    spec = {
        "schema": "dregg.objective-bend.package-input.v1", "edition": "objective-bend-1",
        "modules": [{"name": m["name"], "sourcePath": source_path(cohort_dir, m["source"]),
                     "imports": m.get("imports", [])} for m in item["modules"]],
        "entryModule": str(len(item["modules"]) - 1), "entryDefinition": item["entry"]}
    spec_path = os.path.join(d, "package-input.json")
    with open(spec_path, "w") as f:
        json.dump(spec, f, indent=2)
    code, out, err = run(["capture", spec_path, os.path.join(d, "capture")])
    if code != 0:
        try:
            diagnostic = json.loads((err.strip().split("\n") or [""])[-1])
        except json.JSONDecodeError:
            diagnostic = {"stage": "objective-package-capture", "message": err.strip()[:400]}
        return {"status": "refused", "diagnostic": diagnostic}, None
    capture_path = os.path.join(d, "capture", "objective.json")
    request = {"schema": "dregg.objective-bend.preview-input.v2", "capturePath": capture_path,
               "captureSha256": sha256_file(capture_path),
               "argumentEncoding": item.get("argumentEncoding", "legacy-values-v1"),
               "arguments": item["arguments"], "projections": item.get("projections", []),
               "responses": item.get("responses", []), "limits": dict(LIMITS)}
    if request_change:
        request.update(request_change)
    request_path = os.path.join(d, "request.json")
    with open(request_path, "w") as f:
        json.dump(request, f, indent=2)
    code, out, err = run(["preview", request_path, os.path.join(d, "preview")])
    for file in ("preview.json", "diagnostic.json"):
        path = os.path.join(d, "preview", file)
        if os.path.exists(path):
            with open(path) as f:
                return json.load(f), request
    return {"status": "refused", "diagnostic": {"stage": "objective-front", "message": (err or out).strip()[:400]}}, request


def preview_cohort():
    cohort_path = os.path.join(SOURCE, "preview-cohort.json")
    cohort_dir = os.path.dirname(cohort_path)
    with open(cohort_path) as f:
        cohort = json.load(f)
    failures = []

    def require(ok, message):
        if not ok:
            failures.append(message)
        return ok

    summary = []
    stale = []
    with tempfile.TemporaryDirectory(prefix="obend-preview-") as work:
        first_finished_request = None
        for item in cohort:
            if item["name"] in STALE_PINS:
                key, pinned, current, why = STALE_PINS[item["name"]]
                if item.get(key) == pinned:
                    item = {**item, key: current}
                    stale.append(f"{item['name']}: {key} pinned {pinned!r}, held at {current!r} ({why})")
            out, request = capture_and_preview(item, work, cohort_dir)
            preview = out.get("preview") or {}
            turns = preview.get("turns") or []
            diagnostic = (out.get("diagnostic") or {}).get("message")
            result = preview.get("result")
            summary.append(item["name"] + ":" + str(out.get("status")) +
                           ("=" + str(result.get("value")) if isinstance(result, dict) and "value" in result else ""))
            if item.get("expectedStatus") != "refused" and first_finished_request is None and request is not None:
                first_finished_request = request
            if item.get("expectedStatus") == "refused":
                require(out.get("status") == "refused", f"source typing refusal differs: {item['name']} {out.get('status')}")
                if "expectedRefusal" in item:
                    require(str(diagnostic or "").startswith(item["expectedRefusal"]), f"refusal reason differs: {item['name']} {diagnostic}")
                continue
            for turn in turns:
                require(turn.get("quiescent") is True and turn.get("checkpointRoundTrips") is True,
                        f"yield not a quiescent round-tripping checkpoint: {item['name']}")
            if item.get("protocol") == "kernel":
                responses = item.get("responses", [])
                for i, turn in enumerate(turns):
                    kind = plan_kind(turn.get("plan"))
                    if not require(kind is not None, f"not a kernel Plan: {item['name']} turn {i} {json.dumps(turn.get('plan'))}"):
                        continue
                    if i >= len(responses):
                        continue
                    r = responses[i]
                    outcome = field_of(r.get("payload") if isinstance(r, dict) else None, "outcome")
                    view = field_of(r.get("payload") if isinstance(r, dict) else None, "view")
                    require(isinstance(r, dict) and r.get("tag") == "variant" and r.get("label") == "resumed"
                            and isinstance(outcome, dict) and outcome.get("tag") == "variant"
                            and natural(field_of(view, "version")) and field_of(view, "state") is not None,
                            f"not a kernel response resumed {{outcome, view}}: {item['name']} response {i}")
                    allowed = TRANSFER_OUTCOMES if kind == "transfer" else COMMIT_OUTCOMES if kind == "commit" else AWAIT_OUTCOMES
                    require(isinstance(outcome, dict) and outcome.get("label") in allowed,
                            f"outcome the kernel cannot deliver for a {kind}: {item['name']} response {i} {outcome and outcome.get('label')}")
            if "expectedTurns" in item:
                require(len(turns) == item["expectedTurns"], f"turn count differs: {item['name']} {len(turns)}")
            if "expectedLastPlan" in item:
                require(len(turns) > 0 and canonical(norm(turns[-1].get("plan"))) == canonical(norm(item["expectedLastPlan"])),
                        f"yielded plan differs: {item['name']} {json.dumps(turns[-1].get('plan') if turns else None)}")
            if item.get("expectedStatus") == "yielded":
                require(out.get("status") == "yielded" and preview.get("result") is None,
                        f"activity did not stop at a yield: {item['name']} {out.get('status')}")
                continue
            if item.get("expectedStatus") == "suspended":
                require(out.get("status") == "suspended" and preview.get("result") is None and preview.get("resultData") is None,
                        f"program did not suspend at its budget: {item['name']} {out.get('status')}")
                continue
            if not require(out.get("status") == "finished",
                           f"preview did not finish: {item['name']} {out.get('status')} {json.dumps(out.get('diagnostic') or preview.get('diagnostic'))}"):
                continue
            ty = preview["type"]
            result_type = ty["result"] if ty.get("tag") == "computation" else ty
            require(result_type.get("tag") == item.get("expectedType", "natural"),
                    f"actual typed source result type differs: {item['name']} {result_type.get('tag')}")
            if "expectedData" in item:
                require(preview.get("resultDataStatus") == "materialized" and canonical(norm(preview.get("resultData"))) == canonical(norm(item["expectedData"])),
                        f"deep result differs: {item['name']} {preview.get('resultDataStatus')} {json.dumps(preview.get('resultData'))}")
                require(result.get("tag") == (preview.get("resultData") or {}).get("tag"),
                        f"weak-head and deep result disagree on the constructor: {item['name']}")
            elif "expectedDataStatus" in item:
                require(preview.get("resultDataStatus") == item["expectedDataStatus"] and preview.get("resultData") is None and result.get("tag") == "record",
                        f"deep view status differs: {item['name']} {preview.get('resultDataStatus')} {json.dumps(preview.get('resultData'))}")
            else:
                require(result.get("tag") == "record" if item.get("expectedRecord") else result.get("value") == item.get("expected"),
                        f"actual typed source result differs: {item['name']} {json.dumps(result)}")
            if isinstance(result, dict) and "value" in result:
                require(canonical(preview.get("resultData")) == canonical(result),
                        f"deep view of a scalar differs from its weak-head view: {item['name']} {json.dumps(preview.get('resultData'))}")
            require(preview.get("sameDecodedTerm") is True and len(preview.get("uses", [1])) == 0,
                    f"checked/executed join differs: {item['name']}")
        # The four request mutations on the first finished item's request.
        first = next(c for c in cohort if c.get("expectedStatus") != "refused")
        for name, change, expect in [
                ("WrongCapture", {"captureSha256": "0" * 64}, "refused"),
                ("TypingBudget", {"limits": {**LIMITS, "checkWork": "1"}}, "refused"),
                ("Ticks", {"limits": {**LIMITS, "ticks": "1"}}, "suspended"),
                ("Capacity", {"limits": {**LIMITS, "heap": "1"}}, "suspended")]:
            out, _ = capture_and_preview(first, work, cohort_dir, request_change=change, name="mutation-" + name)
            require(out.get("status") == expect, f"preview refusal/exhaustion differs: {name} {out.get('status')}")
            if name == "TypingBudget":
                require(str((out.get("diagnostic") or {}).get("message", "")).startswith("checker budget refused"),
                        f"a budget refusal is not named as one: {(out.get('diagnostic') or {}).get('message')}")
            require(expect != "suspended" or (out.get("preview") or {}).get("result") is None,
                    "exhaustion falsely returned a source result")
    for line in summary:
        print("  " + line)
    print(f"PREVIEW COHORT: {len(cohort)} items and 4 request mutations, {len(failures)} failures, "
          f"{len(stale)} stale pin(s) held at Mini's current outcome")
    for line in stale:
        print("  STALE PIN " + line)
    for f_ in failures:
        print("  RED " + f_)
    return len(failures) == 0, len(cohort), len(failures)


if __name__ == "__main__":
    if not os.path.exists(OBEND):
        print("no obend binary at " + OBEND + "; run `lake build obend` first", file=sys.stderr)
        sys.exit(2)
    p_ok, p_n, p_red = probes()
    print()
    t_ok, t_n, t_red = tutorial()
    print()
    c_ok, c_n, c_red = preview_cohort()
    print()
    print(f"OBEND SOURCE COHORTS: probes {p_n - p_red}/{p_n}, tutorial {t_n - t_red}/{t_n}, "
          f"preview cohort {c_n} items with {c_red} failures"
          + ("" if p_ok and t_ok and c_ok else "  (RED)"))
    sys.exit(0 if p_ok and t_ok and c_ok else 1)
