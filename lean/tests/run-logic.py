#!/usr/bin/env python3
"""The claim logic end to end through `obend` (Obend.Logic), on tests/obend-source/ReviewMember.obend.

  * `obend check --obligations` lists `ReviewMember.Twice.repeated` unchecked at the object reached from
    `twiceOfThree`, fix(compose(Base, Twice, Augmented), seed);
  * `obend prove` runs the ground instances 0, 3, 41 (true) and the rewriter, and installs the
    two-step derivation (late binding at `twice` in the argument's context, then one beta step) as a
    rewrite@1 receipt with the one support twice -> ReviewMember.Twice; it is byte-identical to the
    recorded tests/logic/ReviewMember.Twice.repeated.json;
  * `obend verify` re-checks the recorded receipt with no producer state, and with the certificate
    read through the slot the status is `checked`.

Teeth (each red under its mutation):
  * ground: `twiceOfThree() == 7` holds; with Augmented mutated to `super.review(value) + 2n` the
    ground judge refutes it (exit 3), while `repeated` is still certified (it never unfolds review);
  * frame: with `Override` (def twice(value): value) composed last, the recorded certificate reads
    `blocked` naming `twice`, `obend prove` refutes `repeated` at 3, and `twiceOfThree() == 7` is
    refuted;
  * statement: the receipt with a wrong statement address is refused `malformed`; with the
    certificate's address changed, `statementMismatch`; with the late-binding step naming Augmented,
    `stepMismatch`; with a support relabelled, refused.

usage: python3 tests/run-logic.py [OBEND_BINARY]      (from lean/, after `lake build obend`)
exit 0 when every check holds, 1 otherwise; a summary line last.
"""
import json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
SOURCES = os.path.join(HERE, "obend-source")
RECORDED = os.path.join(HERE, "logic", "ReviewMember.Twice.repeated.json")
OBEND = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LEAN, ".lake", "build", "bin", "obend")
CLAIM = "ReviewMember.Twice.repeated"

failures = []
count = 0


def obend(*args):
    r = subprocess.run([OBEND, *args], capture_output=True, text=True, cwd=LEAN)
    return r.returncode, r.stdout + r.stderr


def check(name, ok, detail=""):
    global count
    count += 1
    if not ok:
        failures.append(name)
        print(f"FAIL {name}: {detail}")
    else:
        print(f"ok   {name}")


def package(d, member_source):
    """A package of ReviewBase and a (possibly mutated) ReviewMember."""
    base = os.path.join(SOURCES, "ReviewBase.obend")
    member = os.path.join(d, "ReviewMember.obend")
    with open(member, "w") as f:
        f.write(member_source)
    with open(os.path.join(d, "ReviewBase.obend"), "w") as f:
        f.write(open(base).read())
    spec = {"schema": "dregg.objective-bend.package-input.v1", "edition": "objective-bend-1",
            "modules": [{"name": "ReviewBase", "sourcePath": os.path.join(d, "ReviewBase.obend"), "imports": []},
                        {"name": "ReviewMember", "sourcePath": member,
                         "imports": [{"alias": "Prior", "path": "./ReviewBase.obend", "module": "0"}]}],
            "entryModule": "1", "entryDefinition": "twiceOfThree"}
    path = os.path.join(d, "package.json")
    with open(path, "w") as f:
        json.dump(spec, f)
    return path


ORIGINAL = open(os.path.join(SOURCES, "ReviewMember.obend")).read()
PLUS_TWO = ORIGINAL.replace("super.review(value) + 1", "super.review(value) + 2n")
OVERRIDE = ORIGINAL.replace(
    "def review(inherited: Prior.Review)",
    "spec Override for Prior.Review:\n  def twice(value: Nat) -> Nat:\n    value\ndef review(inherited: Prior.Review)").replace(
    "compose(Prior.Base, Twice, Augmented)", "compose(Prior.Base, Twice, Augmented, Override)")
assert PLUS_TWO != ORIGINAL and OVERRIDE != ORIGINAL

with tempfile.TemporaryDirectory() as root:
    def sub(name):
        d = os.path.join(root, name)
        os.mkdir(d)
        return d

    pkg = package(sub("original"), ORIGINAL)
    rc, out = obend("check", "--obligations", "--package", pkg, "--object", "twiceOfThree")
    line = json.loads(out.strip().splitlines()[0]) if rc == 0 and out.strip() else {}
    check("obligation listed unchecked", line.get("claim") == CLAIM and line.get("status") == "unchecked", out)
    check("object is compose(Base, Twice, Augmented)",
          line.get("object") == ["ReviewMember.Augmented", "ReviewMember.Twice", "ReviewBase.Base"], out)

    fresh = os.path.join(root, "fresh.json")
    rc, out = obend("prove", "--package", pkg, CLAIM, "--object", "twiceOfThree", "--out", fresh)
    check("prove: checked by rewrite@1", rc == 0 and "checked:" in out, out)
    receipt = json.load(open(fresh)) if os.path.exists(fresh) else {}
    check("prove: ground 0, 3, 41 true", [r["verdict"] for r in receipt.get("ground", {}).get("rows", [])] == ["ok"] * 3, out)
    check("supports: twice -> ReviewMember.Twice",
          [(s["member"], s["layer"]) for s in receipt.get("supports", [])] == [("twice", "ReviewMember.Twice")], out)
    check("regime and judgment named", receipt.get("regime") == "semidecidable" and receipt.get("judgment") == "HoldsEq"
          and receipt.get("ground", {}).get("judgment") == "Holds", out)
    check("fresh receipt equals the recorded one", os.path.exists(RECORDED) and receipt == json.load(open(RECORDED)),
          "regenerate tests/logic/ReviewMember.Twice.repeated.json if the elaborator moved")

    rc, out = obend("verify", RECORDED)
    check("verify: recorded receipt, no producer state", rc == 0 and "verified" in out, out)

    rdir = sub("receipts")
    with open(os.path.join(rdir, CLAIM + ".json"), "w") as f:
        json.dump(json.load(open(RECORDED)), f)
    rc, out = obend("check", "--obligations", "--package", pkg, "--object", "twiceOfThree", "--receipts", rdir)
    check("status through the slot: checked", '"status":"checked"' in out, out)

    rc, out = obend("ground", "--package", pkg, "twiceOfThree", "7")
    check("ground: twiceOfThree() == 7 holds", rc == 0 and out.startswith("ok"), out)

    # Tooth 1: ground.
    pkg2 = package(sub("plus-two"), PLUS_TWO)
    rc, out = obend("ground", "--package", pkg2, "twiceOfThree", "7")
    check("tooth ground: + 2n refutes twiceOfThree() == 7", rc == 3 and out.startswith("refuted"), out)
    rc, out = obend("prove", "--package", pkg2, CLAIM, "--object", "twiceOfThree", "--out", os.path.join(root, "p2.json"))
    check("tooth ground: + 2n keeps repeated (it never unfolds review)", rc == 0 and "checked:" in out, out)

    # Tooth 2: frame.
    pkg3 = package(sub("override"), OVERRIDE)
    rc, out = obend("check", "--obligations", "--package", pkg3, "--object", "twiceOfThree", "--receipts", rdir)
    line = json.loads(out.strip().splitlines()[0]) if rc == 0 and out.strip() else {}
    check("tooth frame: the certificate reads blocked naming twice",
          line.get("status") == "blocked" and line.get("blocked") == ["twice"], out)
    rc, out = obend("prove", "--package", pkg3, CLAIM, "--object", "twiceOfThree", "--out", os.path.join(root, "p3.json"),
                    "--ground", "3,0,41")
    check("tooth frame: repeated refuted at 3 of the new object", rc == 3 and "refuted" in out and "[3]" in out, out)
    if rc == 3:
        rc2, out2 = obend("verify", os.path.join(root, "p3.json"))
        check("tooth frame: the refutation receipt verifies", rc2 == 0 and "refuted at [3]" in out2, out2)
    rc, out = obend("ground", "--package", pkg3, "twiceOfThree", "7")
    check("tooth frame: twiceOfThree() == 7 refuted", rc == 3 and out.startswith("refuted"), out)

    # Tooth 3: statement.
    def tampered(name, change, expect):
        r = json.load(open(RECORDED))
        change(r)
        p = os.path.join(root, name + ".json")
        with open(p, "w") as f:
            json.dump(r, f)
        rc, out = obend("verify", p)
        check(f"tooth statement: {name}", rc == 3 and expect in out, out)

    def wrong_address(r):
        r["statement"]["address"] = str(int(r["statement"]["address"]) + 1)
    tampered("wrong statement address refused malformed", wrong_address, "malformed")

    def cert_address(r):
        r["certificate"]["address"] = str(int(r["certificate"]["address"]) + 1)
    tampered("certificate of another claim refused", cert_address, "statementMismatch")

    def wrong_layer(r):
        r["certificate"]["steps"][0]["congr"]["inner"][0]["lateBinding"]["layer"] = "ReviewMember.Augmented"
    tampered("late binding through the wrong layer refused", wrong_layer, "stepMismatch")

    def wrong_support(r):
        r["supports"][0]["layer"] = "ReviewMember.Augmented"
    tampered("relabelled support refused", wrong_support, "supports")

print(f"{count - len(failures)}/{count} checks hold")
sys.exit(1 if failures else 0)
