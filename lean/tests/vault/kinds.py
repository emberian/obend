#!/usr/bin/env python3
"""The vault's kinds are kind cells (C1, 2026-11-01), through `obend` on a fresh vault.

  * a kind page names several parents (`parents: a, b`): a page of it is judged by its own kind's
    laws and by both parents', each refusal naming the kind that refused;
  * `create --from c` births a page carrying the kind, with the kind's fields and not its parents;
  * revising a parent kind leaves the page's pin stale: a member's write is refused by name,
    naming the kind that moved; the owner's next write adopts the revised laws and renews the pin,
    after which the member's write is accepted.

usage: python3 tests/vault/kinds.py [OBEND_BINARY]     (from lean/, after `lake build obend`)
"""
import os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))
OBEND = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LEAN, ".lake", "build", "bin", "obend")
failures, count = [], 0


def check(name, ok, detail=""):
    global count
    count += 1
    print(("ok   " if ok else "FAIL ") + name + ("" if ok else ": " + detail))
    if not ok:
        failures.append(name)


with tempfile.TemporaryDirectory() as root:
    v = os.path.join(root, "v")
    for d in ("a", "b", "c"):
        os.makedirs(os.path.join(v, d))

    def write(path, text):
        with open(os.path.join(v, path), "w") as f:
            f.write(text)

    def obend(*args):
        r = subprocess.run([OBEND, *args], cwd=v, capture_output=True, text=True)
        return r.stdout + r.stderr

    write("a/_kind.md", "---\nlaw small: new.x <= 5\n---\nA.\n")
    write("b/_kind.md", "---\nlaw big: not (new.y <= 1)\ny: 2\n---\nB.\n")
    write("c/_kind.md", "---\nparents: a, b\nx: 1\ny: 3\n---\nC.\n")
    out = obend("open")
    check("three kind pages born", out.count("new page (v1)") == 3, out)
    out = obend("create", "--from", "c", "c/One")
    born = open(os.path.join(v, "c/One.md")).read()
    check("create --from c: the kind and its fields, not its parents",
          "created c/One (kind c/_kind)" in out and "kind: c/_kind" in born and "x: 1" in born
          and "parents" not in born, out + born)
    write("c/Two.md", "---\nkind: c\nx: 1\ny: 1\n---\nTwo.\n")
    write("Three.md", "---\nkind: c\nx: 9\ny: 3\n---\nThree.\n")
    out = obend("open")
    check("a page of c is judged by its parent b's law, by name",
          "c/Two: not born: refused by b/_kind: big" in out, out)
    check("and by its parent a's law, by name",
          "Three: not born: refused by a/_kind: small" in out, out)
    write("a/_kind.md", "---\nlaw small: new.x <= 4\n---\nA.\n")
    out = obend("open")
    check("the parent kind is revised", "a/_kind: v2 written" in out, out)
    obend("member", "add", "scout", "--grant", "post:c/One")
    with open(os.path.join(root, "p.md"), "w") as f:
        f.write("---\nkind: c/_kind\nx: 2\ny: 3\n---\nOne more.\n")
    out = obend("post", "c/One", os.path.join(root, "p.md"), "--as", "scout")
    check("a member's write to a page whose kind moved is refused, naming the kind",
          "refused (stale-kind)" in out and "a/_kind at v1" in out, out)
    write("c/One.md", "---\nkind: c/_kind\nx: 2\ny: 3\n---\nOwner.\n")
    out = obend("open")
    check("the owner's write adopts the revised kind", "c/One: v2 written" in out, out)
    out = obend("post", "c/One", os.path.join(root, "p.md"), "--as", "scout")
    check("then the member's write is accepted", "scout posted to c/One" in out, out)

print(f"vault kinds: {count - len(failures)}/{count} checks hold")
sys.exit(1 if failures else 0)
