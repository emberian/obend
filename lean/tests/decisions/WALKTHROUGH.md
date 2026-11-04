# The decisions ledger as a vault: a walkthrough

The dogfood test. `review/DECISIONS-20261031.md` is this project's own ledger of decisions: who
decided what, on what authority, and where it is recorded. This walkthrough keeps that ledger as an
`obend` vault and asks the vault to enforce what the ledger's preamble says we require: a decision is
appended, never rewritten; every decision carries a date and a decider (Ember, the integrator under
standing approval, or a lane); a decision that rests on a theorem names one the environment has.
What the vault's law fragment can say of that, it says and enforces below; what it cannot is listed
in `review/EXPERT-language-user-20261103.md` ("What landed", 2026-11-04, quest 2), and that list is
the point of the exercise.

Every block below is run, in order, by `python3 tests/decisions/walkthrough.py` (from `lean/`, after
`lake build obend`), and what it prints is checked against the block after it.

## 1. The ledger's kind

A decision is a page under `decisions/`, whose kind says what every decision keeps. Decider codes:
`1` Ember, `2` the integrator under standing approval, `3` a lane. The environment's theorem names
are a page of marked lines (a stub census, by hand, until the gate lane's identifier census writes
it), and a decision that cites a theorem quotes its line. `appendOnly` reads the write, not the
page: `deletions` counts the atoms of the settled text a write tombstoned (an author's change is
widened to whole lines), so `new.deletions == 0` admits inserted lines and nothing else, where
`monotone(bytes)` would admit any rewrite that keeps the count.

```sh
mkdir ledger && cd ledger && mkdir decisions environment
cat > decisions/_kind.md <<'MD'
---
law dated: not (new.date == 0)
law dateOnce: writeOnce(date)
law decider: new.decider in [1, 2, 3]
law deciderOnce: writeOnce(decider)
law appendOnly: new.deletions == 0
law cited: new.dangling == 0
date: 0
decider: 0
---
A decision: dated, decided by Ember (1), the integrator under standing approval (2) or a lane (3),
appended to line by line and never shortened or rewritten, and every theorem it names one the
environment has.
MD
cat > environment/Theorems.md <<'MD'
# Theorem names the environment has

A stub census, by hand. One line per name, each marked so a decision can quote it.

judge_admits ^judge_admits
judge_refuses ^judge_refuses
dated_sound ^dated_sound
no_toctou ^no_toctou
flatten_sound ^flatten_sound
solveLawWitness_sound ^solveLawWitness_sound
MD
cat > Ledger.md <<'MD'
---
law appendOnly: monotone(links)
law cited: new.dangling == 0
---
# Decisions ledger

Every decision a lane or reviewer addressed to Ember, with who took it and on what authority.
Standing approval is Ember's "let's raise our ambition and I approve. go forward as you like"
(10-31). Anything taken by a lane is reversible; the cost of reversing is stated in the decision.

- [[decisions/D-0001]]
- [[decisions/D-0002]]
- [[decisions/D-0003]]
MD
cat > decisions/D-0001.md <<'MD'
---
kind: decisions
date: 20261031
decider: 1
---
No per-theorem axiom lists; one crawling census. Where: `393eb2b`, memory `feedback-no-manual-axiom-lists`.
MD
cat > decisions/D-0002.md <<'MD'
---
kind: decisions
date: 20261101
decider: 2
---
Package law at adoption and relaw: adoption judged with old = new state; a relaw of a package law
is refused, the change is by upgrade. Cost to reverse: two compiler arms and two theorems.
MD
cat > decisions/D-0003.md <<'MD'
---
kind: decisions
date: 20261104
decider: 1
---
The project frame is research into the consequences of its design decisions; the user frame is a
lens taken sometimes, never the overriding one; the root documents say so.
MD
obend open && obend status Ledger
```

```text
Ledger: new page (v1)
decisions/D-0001: new page (v1)
decisions/D-0002: new page (v1)
decisions/D-0003: new page (v1)
decisions/_kind: new page (v1)
environment/Theorems: new page (v1)
Ledger v1
  [[decisions/D-0001]] (link) ✓ current: decisions/D-0001 exists
  [[decisions/D-0002]] (link) ✓ current: decisions/D-0002 exists
  [[decisions/D-0003]] (link) ✓ current: decisions/D-0003 exists
```

## 2. A decision appended

A lane records what it landed, dated, as a lane, resting on two theorems the census has. The
ledger gains a link (its `appendOnly` holds), the decision is born under the kind's six laws.

```sh
cd ledger
cat > decisions/D-0004.md <<'MD'
---
kind: decisions
date: 20261104
decider: 3
---
`monotone(F)` holds at a first write, so a page can be born under it. The vault's judge is what it
was: [[environment/Theorems#^judge_admits]] and [[environment/Theorems#^judge_refuses]] are
unchanged. Cost to reverse: one `denote` arm, one `cond` arm, two teeth.
MD
printf -- '- [[decisions/D-0004]]\n' >> Ledger.md
obend open && obend status decisions/D-0004
```

```text
Ledger: v2 written
decisions/D-0004: new page (v1)
decisions/D-0004 v1
  [[environment/Theorems#^judge_admits]] (block quote) ✓ current: the bytes it quotes are environment/Theorems's now
  [[environment/Theorems#^judge_refuses]] (block quote) ✓ current: the bytes it quotes are environment/Theorems's now
```

## 3. Refusals, each naming the ancestor and the clause

A decision resting on a theorem the environment does not have (the report's `suggestMultiField_admits`,
which was cited in THESIS.md and did not exist): its cite dangles, the kind's `cited` refuses, and
the decision is not born.

```sh
cd ledger
cat > decisions/D-0005.md <<'MD'
---
kind: decisions
date: 20261104
decider: 2
---
Constructive repair is proved: [[environment/Theorems#^suggestMultiField_admits]].
MD
obend open && obend status decisions/D-0005
```

```text
decisions/D-0005: not born: refused by decisions/_kind: cited (the kind of decisions/, an ancestor of decisions/D-0005): `new.dangling == 0` does not hold; dangling = 0 would pass (this write has dangling = 1)
decisions/D-0005 v0; its last write was refused by decisions/_kind: cited (the kind of decisions/, an ancestor of decisions/D-0005): `new.dangling == 0` does not hold; dangling = 0 would pass (this write has dangling = 1)
```

A decider that is none of the three, and a decision without a date: refused by the kind, the line
that would pass named.

```sh
cd ledger
rm decisions/D-0005.md
printf -- '---\nkind: decisions\ndate: 20261104\ndecider: 4\n---\nTaken by nobody in particular.\n' > decisions/D-0006.md
printf -- '---\nkind: decisions\ndecider: 1\n---\nUndated.\n' > decisions/D-0007.md
obend open
```

```text
decisions/D-0005: deleted (its file is gone; v0 kept; a file decisions/D-0005.md revives it)
decisions/D-0006: not born: refused by decisions/_kind: decider (the kind of decisions/, an ancestor of decisions/D-0006): `new.decider in [1, 2, 3]` does not hold; the line `decider: 3` would pass (the page has `decider: 4`)
decisions/D-0007: not born: refused by decisions/_kind: dated (the kind of decisions/, an ancestor of decisions/D-0007): `not (new.date == 0)` does not hold; date = 1 would pass (this write has date = 0)
```

A decision rewritten in place at the same length (one character of a commit hash): bytes, lines
and words are unchanged, so every count law would admit it; `appendOnly` refuses it, because the
line was deleted and written again.

```sh
cd ledger
sed -i.bak 's/393eb2b/393eb2c/' decisions/D-0001.md && rm decisions/D-0001.md.bak
obend open
```

```text
decisions/D-0001: refused by decisions/_kind: appendOnly (the kind of decisions/, an ancestor of decisions/D-0001): `new.deletions == 0` does not hold; deletions = 0 would pass (this write has deletions = 1)
decisions/D-0006: still not born: refused by decisions/_kind: decider (the kind of decisions/, an ancestor of decisions/D-0006): `new.decider in [1, 2, 3]` does not hold; the line `decider: 3` would pass (the page has `decider: 4`)
decisions/D-0007: still not born: refused by decisions/_kind: dated (the kind of decisions/, an ancestor of decisions/D-0007): `not (new.date == 0)` does not hold; date = 1 would pass (this write has date = 0)
```

A decision shortened, a decision re-dated, a decider changed after the fact: each refused by the
kind's clause, the file keeping what was typed and the world keeping the decision as it was.

```sh
cd ledger
rm decisions/D-0006.md decisions/D-0007.md
printf -- '---\nkind: decisions\ndate: 20261031\ndecider: 1\n---\nNo per-theorem axiom lists.\n' > decisions/D-0001.md
obend open && obend status decisions/D-0001 | head -1
```

```text
decisions/D-0006: deleted (its file is gone; v0 kept; a file decisions/D-0006.md revives it)
decisions/D-0007: deleted (its file is gone; v0 kept; a file decisions/D-0007.md revives it)
decisions/D-0001: refused by decisions/_kind: appendOnly (the kind of decisions/, an ancestor of decisions/D-0001): `new.deletions == 0` does not hold; deletions = 0 would pass (this write has deletions = 1)
decisions/D-0001 v1; its last write was refused by decisions/_kind: appendOnly (the kind of decisions/, an ancestor of decisions/D-0001): `new.deletions == 0` does not hold; deletions = 0 would pass (this write has deletions = 1)
```

```sh
cd ledger
printf -- '---\nkind: decisions\ndate: 20261031\ndecider: 1\n---\nNo per-theorem axiom lists; one crawling census. Where: `393eb2b`, memory `feedback-no-manual-axiom-lists`.\n' > decisions/D-0001.md
obend open
sed -i.bak 's/^date: 20261031$/date: 20261101/' decisions/D-0001.md && rm decisions/D-0001.md.bak && obend open
sed -i.bak 's/^date: 20261101$/date: 20261031/; s/^decider: 1$/decider: 3/' decisions/D-0001.md && rm decisions/D-0001.md.bak && obend open
```

```text
nothing changed
decisions/D-0001: refused by decisions/_kind: dateOnce (the kind of decisions/, an ancestor of decisions/D-0001): `writeOnce(date)` does not hold; the line `date: 20261031` would pass (the page has `date: 20261101`)
decisions/D-0001: refused by decisions/_kind: deciderOnce (the kind of decisions/, an ancestor of decisions/D-0001): `writeOnce(decider)` does not hold; the line `decider: 1` would pass (the page has `decider: 3`)
```

The ledger itself cannot lose a decision: removing a link is refused by its own `appendOnly`.

```sh
cd ledger
sed -i.bak 's/^decider: 3$/decider: 1/' decisions/D-0001.md && rm decisions/D-0001.md.bak
grep -v 'D-0002' Ledger.md > Ledger.tmp && mv Ledger.tmp Ledger.md
obend open && obend status Ledger | head -1
```

```text
Ledger: refused by its law appendOnly: `monotone(links)` does not hold; links = 4 would pass (this write has links = 3)
Ledger v2; its last write was refused by its law appendOnly: `monotone(links)` does not hold; links = 4 would pass (this write has links = 3)
```

## 4. A decision deleted is kept

A decision's file removed is not a decision forgotten: the kind's laws keep the page, and the open
writes it back and says which law.

```sh
cd ledger
printf -- '- [[decisions/D-0002]]\n' >> Ledger.md && obend open
rm decisions/D-0002.md && obend open && ls decisions
```

```text
Ledger: v3 written
decisions/D-0002: its file is gone, but it is under the law decisions/_kind: dated: not deleted, written back
rendered decisions/D-0002.md
D-0001.md
D-0002.md
D-0003.md
D-0004.md
_kind.md
```

## 5. A decision born from the kind

`obend create` writes the kind's fields; the template is not born until it is dated and decided,
and says so.

```sh refused
cd ledger && obend create --from decisions decisions/D-0008
```

```text
decisions/D-0008: not born: refused by decisions/_kind: dated (the kind of decisions/, an ancestor of decisions/D-0008): `not (new.date == 0)` does not hold; the line `date: 1` would pass (the page has `date: 0`)
```

```sh
cd ledger && cat decisions/D-0008.md
sed -i.bak 's/^date: 0$/date: 20261104/; s/^decider: 0$/decider: 3/' decisions/D-0008.md && rm decisions/D-0008.md.bak
printf 'A decision the lane took: this walkthrough is the dogfood test.\n' >> decisions/D-0008.md
obend open && obend status decisions/D-0008
```

```text
---
kind: decisions/_kind
date: 0
decider: 0
---
decisions/D-0008: v1 written
decisions/D-0008 v1
```

## 6. Two pages must agree

A fact about two pages: a decision the ledger lists is dated. No law of one page can say it; a law
over links can. `linked.date` is read at every page the ledger links to, when the ledger is written
and when a listed page is. Adding the law is a write of the ledger, judged at its links as they
stand.

```sh
cd ledger
awk '{print} /^law cited:/{print "law listedDated: not (linked.date == 0)"}' Ledger.md > Ledger.tmp && mv Ledger.tmp Ledger.md
obend open
```

```text
Ledger: v4 written
```

A note outside `decisions/` (no kind dates it), undated, listed: the ledger's write is refused at
the note, which is named with the clause and what would pass there.

```sh
cd ledger
mkdir -p notes && printf -- '---\ndate: 0\n---\nA note, not a decision.\n' > notes/Scratch.md
printf -- '- [[notes/Scratch]]\n' >> Ledger.md
obend open && obend status Ledger | head -1
```

```text
Ledger: refused by its law listedDated over its links, at notes/Scratch: `not (linked.date == 0)` does not hold there; the line `date: 1` would pass (the page has `date: 0`)
notes/Scratch: new page (v1)
Ledger v4; its last write was refused by its law listedDated over its links, at notes/Scratch: `not (linked.date == 0)` does not hold there; the line `date: 1` would pass (the page has `date: 0`)
```

Dating the note mends the ledger's write at the next open (a refused write is tried again at every
open that is not quiet). The note then cannot lose its date while the ledger lists it: the ledger's
law over its links refuses the note's write, naming whose law it is.

```sh
cd ledger
sed -i.bak 's/^date: 0$/date: 20261104/' notes/Scratch.md && rm notes/Scratch.md.bak && obend open
sed -i.bak 's/^date: 20261104$/date: 0/' notes/Scratch.md && rm notes/Scratch.md.bak && obend open
```

```text
Ledger: v5 written
notes/Scratch: v2 written
notes/Scratch: refused by Ledger: listedDated (a law over Ledger's links, of which notes/Scratch is one): `not (linked.date == 0)` does not hold; the line `date: 1` would pass (the page has `date: 0`)
```
