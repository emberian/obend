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

A decision is a page under `decisions/`, whose kind says what every decision keeps. The decider is a
label: `ember`, `integrator` (under standing approval) or `lane`; a decision that claims Ember must
have been posted by the owner (`new.poster`, the member whose text a write is, bound by the vault
at every write). The environment's names are the census's list, which the kind names as its
`environment:` (`lean/.lake/build/census/environment.txt`: the library's constants, written by
`tests/decisions/Environment.lean` from the tier-1 library, or by `lake build Obend.Census` over
the whole tree); a decision cites a theorem in backticks, and `cited` refuses a write whose added
lines name one the list lacks, naming it. `appendOnly` reads the write, not the
page: `deletions` counts the atoms of the settled text a write tombstoned (an author's change is
widened to whole lines), so `new.deletions == 0` admits inserted lines and nothing else, where
`monotone(bytes)` would admit any rewrite that keeps the count.

```sh
ln -s "$OBEND_ROOT/lean" lean && mkdir ledger && cd ledger && mkdir decisions
cat > decisions/_kind.md <<'MD'
---
environment: ../lean/.lake/build/census/environment.txt
law dated: not (new.date == 0)
law dateOnce: writeOnce(date)
law decider: new.decider in ["ember", "integrator", "lane"]
law claimed: (new.decider == "ember") implies (new.poster == "owner")
law deciderOnce: writeOnce(decider)
law appendOnly: new.deletions == 0
law cited: new.unresolvedInserted == 0
date: 0
decider: nobody
---
A decision: dated, decided by Ember, the integrator under standing approval or a lane, claiming Ember
only when the owner posted it,
appended to line by line and never shortened or rewritten, and every theorem it names one the
environment has.
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
decider: ember
---
No per-theorem axiom lists; one crawling census. Where: `393eb2b`, memory `feedback-no-manual-axiom-lists`.
MD
cat > decisions/D-0002.md <<'MD'
---
kind: decisions
date: 20261101
decider: integrator
---
Package law at adoption and relaw: adoption judged with old = new state; a relaw of a package law
is refused, the change is by upgrade. Cost to reverse: two compiler arms and two theorems.
MD
cat > decisions/D-0003.md <<'MD'
---
kind: decisions
date: 20261104
decider: ember
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
Ledger v1
  [[decisions/D-0001]] (link) ✓ current: decisions/D-0001 exists
  [[decisions/D-0002]] (link) ✓ current: decisions/D-0002 exists
  [[decisions/D-0003]] (link) ✓ current: decisions/D-0003 exists
```

## 2. A decision appended

A lane records what it landed, dated, as a lane, resting on two theorems the environment has. The
ledger gains a link (its `appendOnly` holds), the decision is born under the kind's laws.

```sh
cd ledger
cat > decisions/D-0004.md <<'MD'
---
kind: decisions
date: 20261104
decider: lane
---
`monotone(F)` holds at a first write, so a page can be born under it. The vault's judge is what it
was: `judge_admits` and `judge_refuses` are unchanged. Cost to reverse: one `denote` arm, one
`cond` arm, two teeth.
MD
printf -- '- [[decisions/D-0004]]\n' >> Ledger.md
obend open && obend status decisions/D-0004
```

```text
Ledger: v2 written
decisions/D-0004: new page (v1)
decisions/D-0004 v1
```

## 3. Refusals, each naming the ancestor and the clause

A decision resting on a theorem the environment does not have (the report's `suggestMultiField_admits`,
which was cited in THESIS.md and did not exist): the name is not in the census's list, the kind's
`cited` refuses naming it, and the decision is not born.

```sh
cd ledger
cat > decisions/D-0005.md <<'MD'
---
kind: decisions
date: 20261104
decider: integrator
---
Constructive repair is proved: `suggestMultiField_admits`.
MD
obend open && obend status decisions/D-0005
```

```text
decisions/D-0005: not born: refused by decisions/_kind: cited (the kind of decisions/, an ancestor of decisions/D-0005): `new.unresolvedInserted == 0` does not hold; unresolvedInserted = 0 would pass (this write has unresolvedInserted = 1); names the environment lacks: suggestMultiField_admits
decisions/D-0005 v0; its last write was refused by decisions/_kind: cited (the kind of decisions/, an ancestor of decisions/D-0005): `new.unresolvedInserted == 0` does not hold; unresolvedInserted = 0 would pass (this write has unresolvedInserted = 1); names the environment lacks: suggestMultiField_admits
```

A decider that is none of the three, and a decision without a date: refused by the kind, the line
that would pass named.

```sh
cd ledger
rm decisions/D-0005.md
printf -- '---\nkind: decisions\ndate: 20261104\ndecider: committee\n---\nTaken by nobody in particular.\n' > decisions/D-0006.md
printf -- '---\nkind: decisions\ndecider: ember\n---\nUndated.\n' > decisions/D-0007.md
obend open
```

```text
decisions/D-0005: deleted (its file is gone; v0 kept; a file decisions/D-0005.md revives it)
decisions/D-0006: not born: refused by decisions/_kind: decider (the kind of decisions/, an ancestor of decisions/D-0006): `new.decider in ["ember", "integrator", "lane"]` does not hold; the line `decider: ember` would pass (the page has `decider: committee`)
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
decisions/D-0006: still not born: refused by decisions/_kind: decider (the kind of decisions/, an ancestor of decisions/D-0006): `new.decider in ["ember", "integrator", "lane"]` does not hold; the line `decider: ember` would pass (the page has `decider: committee`)
decisions/D-0007: still not born: refused by decisions/_kind: dated (the kind of decisions/, an ancestor of decisions/D-0007): `not (new.date == 0)` does not hold; date = 1 would pass (this write has date = 0)
```

A decision shortened, a decision re-dated, a decider changed after the fact: each refused by the
kind's clause, the file keeping what was typed and the world keeping the decision as it was.

```sh
cd ledger
rm decisions/D-0006.md decisions/D-0007.md
printf -- '---\nkind: decisions\ndate: 20261031\ndecider: ember\n---\nNo per-theorem axiom lists.\n' > decisions/D-0001.md
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
printf -- '---\nkind: decisions\ndate: 20261031\ndecider: ember\n---\nNo per-theorem axiom lists; one crawling census. Where: `393eb2b`, memory `feedback-no-manual-axiom-lists`.\n' > decisions/D-0001.md
obend open
sed -i.bak 's/^date: 20261031$/date: 20261101/' decisions/D-0001.md && rm decisions/D-0001.md.bak && obend open
sed -i.bak 's/^date: 20261101$/date: 20261031/; s/^decider: ember$/decider: lane/' decisions/D-0001.md && rm decisions/D-0001.md.bak && obend open
```

```text
nothing changed
decisions/D-0001: refused by decisions/_kind: dateOnce (the kind of decisions/, an ancestor of decisions/D-0001): `writeOnce(date)` does not hold; the line `date: 20261031` would pass (the page has `date: 20261101`)
decisions/D-0001: refused by decisions/_kind: deciderOnce (the kind of decisions/, an ancestor of decisions/D-0001): `writeOnce(decider)` does not hold; the line `decider: ember` would pass (the page has `decider: lane`)
```

The ledger itself cannot lose a decision: removing a link is refused by its own `appendOnly`.

```sh
cd ledger
sed -i.bak 's/^decider: lane$/decider: ember/' decisions/D-0001.md && rm decisions/D-0001.md.bak
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
sed -i.bak 's/^date: 0$/date: 20261104/; s/^decider: nobody$/decider: lane/' decisions/D-0008.md && rm decisions/D-0008.md.bak
printf 'A decision the lane took: this walkthrough is the dogfood test.\n' >> decisions/D-0008.md
obend open && obend status decisions/D-0008
```

```text
---
kind: decisions/_kind
date: 0
decider: nobody
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

Dating the note mends the ledger's write at the next open (a refused write is judged again when a
page it read is written; the note is one the ledger's write read, so dating it wakes that write). The note then cannot lose its date while the ledger lists it: the ledger's
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

## 7. Who decided, and who says so

`decider` is a label and `poster` is one the vault binds at every write: the owner for the owner's
writes, the member for a member's post, and at a selection the author of the candidate kept. The
kind's `claimed` ties them: a decision that says Ember decided must be the owner's text. A member
`lane` may be granted a post to a decision Ember took, but the post is a write whose text is the
lane's, and the row claims Ember: refused at the post, naming the poster and the claimed decider,
and what would pass (`decider: lane`). (A member's post cannot change the frontmatter itself: that
is a relaw, the owner's.) The lane's proposal to a decision in its own name is admitted, and the
selection carries the lane as its poster.

```sh refused
cd ledger
obend create --from decisions decisions/D-0009 >/dev/null 2>&1
sed -i.bak 's/^date: 0$/date: 20261104/; s/^decider: nobody$/decider: ember/' decisions/D-0009.md && rm decisions/D-0009.md.bak
printf 'Ember: the decisions ledger is a vault from now on.\n' >> decisions/D-0009.md
obend open
obend member add lane --grant post:decisions/D-0009 --grant post:decisions/D-0008
{ cat decisions/D-0009.md; printf 'The lane adds: and the vault is where lanes record what they land.\n'; } > ../claim.md
obend post decisions/D-0009 ../claim.md --as lane
```

```text
decisions/D-0009: v1 written
member lane may post decisions/D-0009, post decisions/D-0008
refused: decisions/D-0009: refused by decisions/_kind: claimed (the kind of decisions/, an ancestor of decisions/D-0009): `(new.decider == "ember") implies (new.poster == "owner")` does not hold; the line `decider: lane` would pass (the page has `decider: ember`); posted by lane
```

```sh
cd ledger
{ cat decisions/D-0008.md; printf 'The lane adds: the dogfood test now has seven sections.\n'; } > ../more.md
obend post decisions/D-0008 ../more.md --as lane && obend select decisions/D-0008 1 2 && obend status decisions/D-0008 | head -1
```

```text
lane posted to decisions/D-0008
rendered decisions/D-0008.md
decisions/D-0008: section 1: 2 candidates (as it is, lane); keep one with: obend select decisions/D-0008 1 N
kept candidate 2 of section 1 of decisions/D-0008
rendered decisions/D-0008.md
decisions/D-0008 v3
```

## 8. A law per row

The ledger's natural unit is one decision, and `review/DECISIONS-20261031.md` keeps many on one
page. A kind law may name the rows a heading begins as its subject: `law appendOnly per ##:
new.deletions == 0` is judged at every `## ` row of the page, on that row's own measures (its
words, lines, bytes, links, embeds, quotes, dangling links and unresolved names) and its write's
(`deletions`, `insertions`: the lines of that row the write removed or rewrote, and added;
`unresolvedInserted`: the names the added lines cite that the environment lacks), and a refusal
names the row. The write is one turn: a row edited in place refuses it, naming the row, and the same rows
with one appended are admitted.

```sh
cd ledger && mkdir log
cat > log/_kind.md <<'MD'
---
environment: ../lean/.lake/build/census/environment.txt
law appendOnly per ##: new.deletions == 0
law cited per ##: new.unresolvedInserted == 0
---
A log of decisions, one `## ` row each: a row is appended to and never rewritten, and every
theorem a row names is one the environment has.
MD
cat > log/Decisions.md <<'MD'
# Decisions, as rows

## D-0001
No per-theorem axiom lists; one crawling census. Rests on `judge_admits`.

## D-0002
Package law at adoption and relaw: adoption judged with old = new state.

## D-0003
The project frame is research into the consequences of its design decisions.
MD
obend open
```

```text
log/Decisions: new page (v1)
log/_kind: new page (v1)
```

One row rewritten in place, and a row appended, in one write: refused at the row rewritten, with
the value that would pass; the file keeps both. The write has `deletions = 1` there, the line
rewritten: a change is widened to whole lines, and a whole line inserted or removed re-writes no
neighbour.

```sh
cd ledger
sed -i.bak 's/^Package law at adoption and relaw: adoption judged with old = new state.$/Package law at adoption only./' log/Decisions.md && rm log/Decisions.md.bak
printf -- '\n## D-0004\nA law per row, taken by the lane. Rests on `no_toctou`.\n' >> log/Decisions.md
obend open
```

```text
log/Decisions: refused by log/_kind: appendOnly per ## (the kind of log/, an ancestor of log/Decisions) at ## D-0002: `new.deletions == 0` does not hold there; deletions = 0 would pass (this write has deletions = 1)
```

The row put back as it was, the appended row stays: admitted. A row naming a theorem the
environment lacks is refused at that row, the name said.

```sh
cd ledger
sed -i.bak 's/^Package law at adoption only.$/Package law at adoption and relaw: adoption judged with old = new state./' log/Decisions.md && rm log/Decisions.md.bak
obend open
printf -- '\n## D-0005\nRests on `suggestMultiField_admits`.\n' >> log/Decisions.md
obend open
```

```text
log/Decisions: v2 written
log/Decisions: refused by log/_kind: cited per ## (the kind of log/, an ancestor of log/Decisions) at ## D-0005: `new.unresolvedInserted == 0` does not hold there; unresolvedInserted = 0 would pass (this write has unresolvedInserted = 1); names the environment lacks: suggestMultiField_admits
```

What a row cannot carry. `dated` and `deciderOnce` read fields, and a row has none: the reader
knows frontmatter fields (`key: value` lines between `---`, the page's), wikilinks, block ids
(`^id`) and heading lines, and nothing else a row could hold a value in. The real ledger's rows are
table rows whose columns are their fields (`| decision | choice | where |`), which the reader does
not read at all. To say `dated` per row the vault would need one of three things, each a decision
about what a row is: Obsidian's inline fields, `date:: 20261104` on a line of the row (Dataview's
syntax; `::` does not collide with prose colons, and the frontmatter's `key: value` reader applies
to it as is); a table whose header row names the columns and each row's cells are its fields
(markdown's own syntax, read by splitting on `|`, which is a new reader); or heading attributes,
`## D-0004 {date=20261104 decider=lane}` (Pandoc's). None is taken here.
