#!/usr/bin/env python3
"""`obend analyze impact` against the actual re-judgment (Obend.Analysis).

Each check moves a pin in a scratch copy of a world, predicts with `obend analyze impact`, then makes
the move for real and re-judges with the world's own command; every predicted line must be what the
re-judgment says, and every dependent the re-judgment changes must be predicted.

  * a vault (Beta, and Alpha embedding it, Gamma linking it, Delta quoting its ^b block): the owner's
    write of a new Beta predicts Alpha's embed `behind` (and Beta's law row `rejudge`), nothing for
    Gamma or Delta; `obend status` after the write agrees cite by cite. Moving Beta back to v1 from the
    written world predicts the embed `restored`; writing the old text back agrees.
  * a workspace (tests/obend-source/three-package): re-pinning ext/left^1 and moving commons/counter^1
    each predict the recorded turn `stale` resting on that line, the intention pin blocked, the law
    row re-judged; `obend admit` of the turn at the moved records says `stale` naming the same line.
    A move to the pin the line already names predicts nothing; `obend admit` says `admitted`.
  * receipts: `obend verify` accepts each written receipt with no producer state; a receipt whose
    opening is flipped is refused `wrong-opening`, one with its line dropped `missing`.
  * the tooth: `--tooth drop-read` (the index drops each dependent's last read) predicts nothing for
    Alpha's embed, which the re-judgment shows behind; the checker refuses that list `missing`.
  * `CELL@?`: forgetting Beta lists every cite of it as open and every law row reading it.
  * replay: a journal kind's law amended from `new.words <= 20` to `<= 10` is replayed over the
    journal's history: Mon's second write (12 words) diverges, refused by the amended law, Tue's
    writes are judged alike; a vault with the amended kind in force from the start, given the same
    writes, refuses exactly Mon's second, with the same words.

usage: python3 tests/analysis/run-impact.py [OBEND_BINARY]      (from lean/, after `lake build obend`)
exit 0 when every check holds, 1 otherwise; a summary line last.
"""
import json, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
WS = os.path.join(LEAN, "tests", "obend-source", "three-package")
OBEND = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LEAN, ".lake", "build", "bin", "obend")

failures = []
count = 0


def obend(*args, cwd=LEAN):
    r = subprocess.run([OBEND, *args], capture_output=True, text=True, cwd=cwd)
    return r.returncode, r.stdout + r.stderr


def check(name, ok, detail=""):
    global count
    count += 1
    print(("ok   " if ok else "FAIL ") + name + ("" if ok else ": " + detail))
    if not ok:
        failures.append(name)


def predict(target, world, out, *extra):
    code, text = obend("analyze", "impact", target, "--world", world, "--out", out, *extra)
    if not os.path.exists(out):
        return code, text, {}, []
    r = json.load(open(out))
    kinds = {d["name"]: d["kind"] for d in r["object"]["deps"]}
    lines = r["certificate"]["lines"]
    return code, text, kinds, lines


def by(lines, kinds, goes, kind):
    return sorted(l["dep"] for l in lines if l["goes"] == goes and kinds.get(l["dep"]) == kind)


def failing_cites(vault):
    """`obend status`: the cites that do not hold, as `PAGE: TEXT`."""
    _, out = obend("-C", vault, "status")
    page, bad = None, set()
    for line in out.splitlines():
        if not line.startswith("  "):
            page = line.split(" v")[0]
        elif " ✗ " in line and page:
            txt = line[2:].split(" ✗ ")[0]
            txt = txt.rsplit(" (", 1)[0]
            bad.add(page + ": " + txt)
    return sorted(bad)


BETA = "# Beta\n\nThe beta line ^b\n\nmore text\n"
BETA2 = "# Beta\n\nThe beta line ^b\n\nmore text, revised\n"

with tempfile.TemporaryDirectory() as work:
    vault = os.path.join(work, "vault")
    os.makedirs(vault)
    for name, text in [("Beta", BETA), ("Alpha", "Alpha embeds ![[Beta]]\n"), ("Gamma", "Gamma links [[Beta]]\n"),
                       ("Delta", "Delta quotes ![[Beta#^b]]\n")]:
        open(os.path.join(vault, name + ".md"), "w").write(text)
    code, out = obend("open", vault)
    check("vault: opens, every cite current", code == 0 and failing_cites(vault) == [], out)

    new = os.path.join(work, "Beta-revised.md")
    open(new, "w").write(BETA2)
    r1 = os.path.join(work, "r1.json")
    code, text, kinds, lines = predict("Beta@" + new, vault, r1)
    behind = by(lines, kinds, "blocked", "cite")
    check("vault write: the prediction is accepted by the impact@1 judge", code == 0 and "checked (impact@1" in text, text)
    check("vault write: Alpha's embed predicted behind, nothing else", behind == ["Alpha: ![[Beta]]"], repr(lines))
    check("vault write: Beta's law row re-judged", by(lines, kinds, "rejudge", "law") == ["law of Beta"], repr(lines))
    code, out = obend("verify", r1)
    check("vault write: obend verify accepts the receipt", code == 0 and out.strip().endswith("verified (impact@1, decidable, compiled)"), out)

    # the tooth, before the move is made
    rt = os.path.join(work, "tooth.json")
    code, text, kinds_t, lines_t = predict("Beta@" + new, vault, rt, "--tooth", "drop-read")
    check("tooth: a dropped read predicts nothing for Alpha's embed", by(lines_t, kinds_t, "blocked", "cite") == [], repr(lines_t))
    check("tooth: the checker refuses the list as missing Alpha's embed",
          code == 3 and "refused: missing: Alpha: ![[Beta]]" in text, text)
    code, out = obend("verify", rt)
    check("tooth: obend verify refuses its receipt", code == 3 and "missing" in out, out)

    # tampered receipts
    r = json.load(open(r1))
    flipped = json.loads(json.dumps(r))
    for l in flipped["certificate"]["lines"]:
        if l["goes"] == "blocked":
            l["value"] = True
    bad = os.path.join(work, "flipped.json")
    json.dump(flipped, open(bad, "w"))
    code, out = obend("verify", bad)
    check("receipt with a flipped opening: refused wrong-opening", code == 3 and "wrong-opening" in out, out)
    dropped = json.loads(json.dumps(r))
    dropped["certificate"]["lines"] = [l for l in dropped["certificate"]["lines"] if l["goes"] != "blocked"]
    json.dump(dropped, open(bad, "w"))
    code, out = obend("verify", bad)
    check("receipt with its blocked line dropped: refused missing", code == 3 and "missing: Alpha: ![[Beta]]" in out, out)
    other = json.loads(json.dumps(r))
    other["certificate"]["lines"].append({"dep": "Gamma: [[Beta]]", "goes": "blocked",
                                          "support": {"cell": "Alpha", "name": "x", "pins": []}, "value": False})
    json.dump(other, open(bad, "w"))
    code, out = obend("verify", bad)
    check("receipt naming a dependent by a support it does not read: refused does-not-read",
          code == 3 and "does-not-read" in out, out)

    # forget
    code, out = obend("analyze", "impact", "Beta@?", "--world", vault)
    opened = sorted(l.split(None, 2)[2] for l in out.splitlines() if l.startswith("open "))
    check("forget Beta: every cite of Beta could change", opened == ["Alpha: ![[Beta]]", "Delta: [[Beta#^b]]", "Gamma: [[Beta]]"], out)

    # the actual move
    shutil.copy(new, os.path.join(vault, "Beta.md"))
    obend("open", vault)
    check("vault write, re-judged: obend status shows exactly the predicted cites behind",
          failing_cites(vault) == behind, repr(failing_cites(vault)) + " vs " + repr(behind))

    # move back to v1, predicted from the written world
    r2 = os.path.join(work, "r2.json")
    code, text, kinds, lines = predict("Beta@1", vault, r2)
    check("vault rollback: Alpha's embed predicted restored", code == 0 and by(lines, kinds, "restored", "cite") == ["Alpha: ![[Beta]]"]
          and by(lines, kinds, "blocked", "cite") == [], text)
    open(os.path.join(vault, "Beta.md"), "w").write(BETA)
    obend("open", vault)
    check("vault rollback, re-judged: the old bytes back, no cite fails", failing_cites(vault) == [], repr(failing_cites(vault)))

with tempfile.TemporaryDirectory() as work:
    ws = os.path.join(WS, "workspace.json")
    code, out = obend("run", "--package", ws, "--json")
    turn = os.path.join(work, "turn.json")
    json.dump(json.loads(out)["turn"], open(turn, "w"))
    for cell, other, name in [("ext/left^1", "workspace-left-repinned.json", "ext/left"),
                              ("commons/counter^1", "workspace-moved.json", "commons/counter")]:
        rr = os.path.join(work, name.replace("/", "-") + ".json")
        code, text, kinds, lines = predict(cell + "@" + os.path.join(WS, other), ws, rr, "--turn", turn)
        stale = [l for l in lines if l["goes"] == "blocked" and kinds[l["dep"]] == "turn"]
        check(f"workspace {name}: the turn predicted stale, resting on {cell}",
              code == 0 and len(stale) == 1 and stale[0]["support"]["cell"] == cell, text)
        check(f"workspace {name}: its intention pin predicted blocked",
              [l["dep"] for l in lines if l["goes"] == "blocked" and kinds[l["dep"]] == "candidate"] ==
              [d for d in kinds if kinds[d] == "candidate" and d.startswith(name + "@^")], text)
        check(f"workspace {name}: the closure's law re-judged", by(lines, kinds, "rejudge", "law") != [], text)
        code, out = obend("admit", "--package", os.path.join(WS, other), turn)
        a = json.loads(out)
        check(f"workspace {name}, re-judged: obend admit says stale, naming {name}",
              code == 3 and a["status"] == "stale" and a["name"] == name, out)
        code, out = obend("verify", rr)
        check(f"workspace {name}: obend verify accepts the receipt", code == 0, out)
    rr = os.path.join(work, "same.json")
    code, text, kinds, lines = predict("ext/right^1@1:1.0.0", ws, rr, "--turn", turn)
    check("workspace: a move to the pin already named predicts nothing", code == 0 and lines == [], text)
    code, out = obend("admit", "--package", ws, turn)
    check("workspace, re-judged: obend admit says admitted", code == 0 and json.loads(out)["status"] == "admitted", out)

KIND = "---\nlaw brief: new.words <= 20\n---\nA journal.\n"
KIND10 = "---\nlaw brief: new.words <= 10\n---\nA journal.\n"
MON = ["one two three\n", "one two three four five six seven eight nine ten eleven twelve\n", "short again\n"]


def journal(vault, kind, writes=len(MON)):
    os.makedirs(os.path.join(vault, "journal"))
    open(os.path.join(vault, "journal", "_kind.md"), "w").write(kind)
    open(os.path.join(vault, "journal", "Tue.md"), "w").write("a b c\n")
    for text in MON[:writes]:
        open(os.path.join(vault, "journal", "Mon.md"), "w").write(text)
        obend("open", vault)


with tempfile.TemporaryDirectory() as work:
    vault = os.path.join(work, "vault")
    journal(vault, KIND)
    _, out = obend("-C", vault, "status", "journal/Mon")
    check("replay: the journal's three writes are admitted under the law in force", out.startswith("journal/Mon v3"), out)
    amended = os.path.join(work, "kind10.md")
    open(amended, "w").write(KIND10)
    code, out = obend("analyze", "replay", "journal/_kind@" + amended, "--world", vault)
    lines = out.splitlines()
    mon = [i for i, l in enumerate(lines) if l.startswith("journal/Mon: v2 diverges after 1 write(s) judged alike")]
    check("replay: Mon's second write diverges", code == 0 and len(mon) == 1, out)
    would = lines[mon[0] + 2].split("amended:", 1)[1].strip() if mon else ""
    check("replay: the amended law refuses it, by name", would.startswith("refused by journal/_kind: brief"), out)
    check("replay: Tue's writes are judged alike", "journal/Tue: 1 write(s) judged alike" in out, out)
    fresh = os.path.join(work, "fresh")
    journal(fresh, KIND10, writes=2)
    _, out = obend("-C", fresh, "status", "journal/Mon")
    check("replay, re-judged: with the amended law in force, Mon's second write is refused with the same words",
          out.startswith("journal/Mon v1; its last write was " + would), out + "\nwanted: " + would)

print(f"{count - len(failures)}/{count} checks hold" + ("" if not failures else "; failing: " + ", ".join(failures)))
sys.exit(1 if failures else 0)
