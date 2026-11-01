#!/usr/bin/env python3
"""The leaf emitter end to end through `obend` (Obend.Leaf), on tests/obend-source/ReviewMember.obend.

  * `obend emit` reaches fix(compose(Base, Twice, Augmented), seed) from `twiceOfThree`, flattens and
    emits it: two method slots, `review` and `twice`, `twice` reading slot 0 through `self`, the
    kind's brand `#kind` a static entry of the book (no slot), every
    definition closed; the book computes twice(3) = 7, as the demand machine does on the object and
    on `twiceOfThree()`;
  * `obend specialize` reads the specialization slot at the program's view with the emitted book
    stored: at the same program the book is usable and selected.

Teeth (each red under its mutation):
  * frame: with `Override` (def twice(value): value) composed last, the stored book reads blocked by
    exactly the object's pin, and the machine is selected, computing twice(3) = 3 where the stale
    book would say 7;
  * layer: with Augmented at `+ 2n`, the book is blocked by the object's pin and Augmented's, and the
    machine computes 9.

usage: python3 tests/run-leaf.py [OBEND_BINARY]      (from lean/, after `lake build obend`)
exit 0 when every check holds, 1 otherwise; a summary line last.
"""
import json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
SOURCES = os.path.join(HERE, "obend-source")
OBEND = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LEAN, ".lake", "build", "bin", "obend")

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
    book = os.path.join(root, "book.json")
    rc, out = obend("emit", "--package", pkg, "--object", "twiceOfThree", "--out", book, "--call", "twice", "3")
    check("emit: the object is compose(Base, Twice, Augmented)",
          rc == 0 and "object: fix(compose(ReviewBase.Base, ReviewMember.Twice, ReviewMember.Augmented), seed)" in out, out)
    check("emit: two slots, review and twice", 'slots: [review, twice]' in out, out)
    check("emit: twice is a method reading slot 0", "def 1 twice: method, reads [0]" in out, out)
    check("emit: review is a method reading nothing (super.review resolved)", "def 0 review: method, reads []" in out, out)
    check("emit: the kind's brand is static metadata, not a slot", "static #kind" in out, out)
    check("emit: every definition closed", "closed: true" in out, out)
    check("emit: the book computes twice(3) = 7", "book: twice(3) = 7" in out, out)
    check("emit: the machine computes 7 on the object and on twiceOfThree()",
          "machine: twice(3) = 7; twiceOfThree() = 7" in out, out)
    recorded = json.load(open(book)) if os.path.exists(book) else {}
    check("emit: the book file pins the composition", recorded.get("object") == "twiceOfThree"
          and "composition" in recorded and [d["member"] for d in recorded.get("defs", [])] == ["review", "twice"]
          and [s["member"] for s in recorded.get("statics", [])] == ["#kind"], book)

    rc, out = obend("specialize", "--package", pkg, "--object", "twiceOfThree", "--book", book, "--call", "twice", "3")
    check("specialize: same program, book usable and selected",
          rc == 0 and "book: usable" in out and "selected: book" in out and "book: twice(3) = 7" in out, out)

    # Tooth: frame.
    pkg3 = package(sub("override"), OVERRIDE)
    rc, out = obend("specialize", "--package", pkg3, "--object", "twiceOfThree", "--book", book, "--call", "twice", "3")
    check("tooth frame: Override blocks the book by the object's pin alone",
          "book: blocked by object twiceOfThree\n" in out, out)
    check("tooth frame: the machine is selected and computes 3",
          "selected: machine" in out and "machine: twice(3) = 3" in out, out)

    # Tooth: layer.
    pkg2 = package(sub("plus-two"), PLUS_TWO)
    rc, out = obend("specialize", "--package", pkg2, "--object", "twiceOfThree", "--book", book, "--call", "twice", "3")
    check("tooth layer: + 2n blocks the book by the object's pin and Augmented's",
          "book: blocked by object twiceOfThree, layer ReviewMember.Augmented" in out, out)
    check("tooth layer: the machine is selected and computes 9",
          "selected: machine" in out and "machine: twice(3) = 9" in out, out)

print(f"{count - len(failures)}/{count} checks hold")
sys.exit(1 if failures else 0)
