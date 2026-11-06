# `obend open`: a walkthrough

You keep notes as a folder of markdown, the way Obsidian does: one file per page, `[[wikilinks]]`
between them. `obend open` reads that folder as pages and keeps a world beside it, in a `.obend/`
directory; it never changes the shape of your notes. What it adds: a page can carry a law that
refuses an edit and says what would pass; someone you invite can propose changes without
overwriting yours; an edit made offline merges back; and a quote of another page knows when that
page has moved on.

Every block below is run, in order, by `python3 tests/vault/walkthrough.py` (from `lean/`, after
`lake build obend`), and what it prints is checked against the block after it.

## 1. A vault of three pages

Three pages that cite each other. `[[Beta]]` links to Beta; `![[Beta]]` embeds (quotes) Beta whole;
`[[Beta#^answer]]` quotes the one line of Beta marked `^answer`.

```sh
mkdir vault && cd vault
cat > Alpha.md <<'EOF'
# Alpha

Alpha is where I start. It links to [[Beta]] and to [[Gamma]].

It embeds Beta whole:

![[Beta]]

and quotes one of its lines: [[Beta#^answer]].
EOF
cat > Beta.md <<'EOF'
# Beta

Beta answers [[Alpha]].
The answer is forty-two. ^answer
EOF
cat > Gamma.md <<'EOF'
# Gamma

Gamma is a stub. See [[Alpha]], and [[Delta]], which I have not written yet.
EOF
obend open
```

```text
Alpha: new page (v1)
Beta: new page (v1)
Gamma: new page (v1)
Gamma: [[Delta]] (link) is dangling: no page of that name
```

`[[Delta]]` dangles: there is no Delta yet. Write it, and the next open makes the link a cite.

```sh
cd vault && printf '# Delta\n\nDelta, at last.\n' > Delta.md && obend open && obend status Gamma
```

```text
Gamma: v2 written
Delta: new page (v1)
Gamma v2
  [[Alpha]] (link) ✓ current: Alpha exists
  [[Delta]] (link) ✓ current: Delta exists
```

Opening again changes nothing, and the files are byte for byte what you wrote.

```sh
cd vault && obend open && ls -A
```

```text
nothing changed
.obend
Alpha.md
Beta.md
Delta.md
Gamma.md
```

`obend status` shows each page's version and each of its cites, with whether it holds.

```sh
cd vault && obend status
```

```text
Alpha v1
  [[Beta]] (link) ✓ current: Beta exists
  [[Gamma]] (link) ✓ current: Gamma exists
  ![[Beta]] (embed) ✓ current: the bytes it quotes are Beta's now
  [[Beta#^answer]] (block quote) ✓ current: the bytes it quotes are Beta's now
Beta v1
  [[Alpha]] (link) ✓ current: Alpha exists
Gamma v2
  [[Alpha]] (link) ✓ current: Alpha exists
  [[Delta]] (link) ✓ current: Delta exists
Delta v1
```

## 2. A law

A page's frontmatter may carry laws: `law NAME: EXPR`, in the `.obend` law fragment. A law reads the
page's measures (`words`, `lines`, `bytes`, `links`, `embeds`, `quotes`, `dangling`, `sections`, `version`), the
write's own (`deletions`, `insertions`: the atoms of the text it tombstoned and added), its
frontmatter's number, true/false and one-word (label) fields, who is writing (`request.caller`: 0 is
you) and whose text it is (`new.poster`: `owner`, or the member who posted it). Adding a
law is itself a write: the new law must hold of the page as it stands.

```sh
cd vault
cat > Beta.md <<'EOF'
---
law short: new.words <= 20
---
# Beta

Beta answers [[Alpha]].
The answer is forty-two. ^answer
EOF
obend open
```

```text
Beta: v2 written
rendered Alpha.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v2) and the bytes it quotes changed
```

The law line is part of Beta's text, so Alpha's embed of Beta (which quotes all of it) is now
behind, and Alpha's file says so where you read it. The mark is the view's, not your text: delete it
and the next open draws it again without counting an edit.

```sh
cd vault && grep 'Beta]]' Alpha.md
sed -i.bak 's/{behind}//' Alpha.md && rm Alpha.md.bak && obend open && grep 'Beta]]' Alpha.md && obend status Alpha | head -1
```

```text
Alpha is where I start. It links to [[Beta]] and to [[Gamma]].
![[Beta]]{behind}
nothing changed
rendered Alpha.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v2) and the bytes it quotes changed
Alpha is where I start. It links to [[Beta]] and to [[Gamma]].
![[Beta]]{behind}
Alpha v1
```

Step 5 comes back to the embed.

Now an edit that breaks the law. The file keeps what you typed; the world does not take it, and says
which law refused and what would pass.

```sh
cd vault
cat >> Beta.md <<'EOF'
And here is a long digression that goes on and on about nothing in particular at all.
EOF
obend open
```

```text
Beta: refused by its law short: `new.words <= 20` does not hold; words = 20 would pass (this write has words = 27)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v2) and the bytes it quotes changed
```

```sh
cd vault && obend status Beta
```

```text
Beta v2; its last write was refused by its law short: `new.words <= 20` does not hold; words = 20 would pass (this write has words = 27)
  [[Alpha]] (link) ✓ current: Alpha exists
```

Shorten it, and the write goes through.

```sh
cd vault
sed -i.bak 's/^And here is a long digression.*$/A short aside./' Beta.md && rm Beta.md.bak
obend open
```

```text
Beta: v3 written
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
```

A folder is a kind: the laws of its `_kind.md` are laws of every page in it.

```sh
cd vault && mkdir journal
printf -- '---\nlaw brief: new.words <= 8\n---\nA journal: one short line a day.\n' > journal/_kind.md
printf 'Rain all day.\n' > journal/Monday.md
printf 'Sun, then a long walk by the river, then dinner with friends, then bed.\n' > journal/Tuesday.md
obend open
```

```text
journal/Monday: new page (v1)
journal/Tuesday: not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
journal/_kind: new page (v1)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
```

A kind is a page of its own, with its own laws and the fields a page starts with, and a page born
under it carries its identity: `kind:` in its frontmatter names the kind, wherever the page lives,
and the kind's laws judge every write to it, the kind first among its ancestors.

```sh
cd vault && mkdir recipes
printf -- '---\nlaw serves: not (new.servings == 0)\nservings: 2\n---\nA recipe serves someone.\n' > recipes/_kind.md
obend open && obend create --from recipes recipes/Soup && cat recipes/Soup.md
```

```text
recipes/_kind: new page (v1)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
created recipes/Soup (kind recipes/_kind)
---
kind: recipes/_kind
servings: 2
---
```

A page outside the folder that names the kind is its instance too; one that serves nobody is refused
by the kind's law, by name:

```sh
cd vault
printf -- '---\nkind: recipes\nservings: 0\n---\nToast.\n' > Toast.md
obend open
```

```text
Toast: not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
```

## 3. A member

Invite someone (a person, or an agent) as a member who may post to Alpha. A member's post never
overwrites: each line it changes becomes a section with two candidates, the line as it is and the
line as proposed, until someone allowed to select keeps one.

```sh
cd vault && obend member add scout --grant post:Alpha && obend member list
```

```text
member scout may post Alpha
scout: post Alpha
```

The scout proposes a new first sentence for Alpha:

```sh
cd vault
sed 's/^Alpha is where I start./Alpha is where everything starts./' Alpha.md > ../proposal.md
obend post Alpha ../proposal.md --as scout && cat Alpha.md
```

```text
scout posted to Alpha
rendered Alpha.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
Alpha: section 1: 2 candidates (owner, scout); keep one with: obend select Alpha 1 N
# Alpha

<<<<<<< section 1 · candidate 1 (owner) · keep it: obend select Alpha 1 1
Alpha is where I start. It links to [[Beta]] and to [[Gamma]].
======= candidate 2 (scout) · keep it: obend select Alpha 1 2
Alpha is where everything starts. It links to [[Beta]] and to [[Gamma]].
>>>>>>> section 1

It embeds Beta whole:

![[Beta]]{behind}

and quotes one of its lines: [[Beta#^answer]].
```

The scout may post, but not select, and may not post to a page it was not granted.

```sh refused
cd vault && obend select Alpha 1 2 --as scout
```

```text
refused: scout may post to Alpha but not select on it (no select grant)
```

```sh refused
cd vault && obend post Beta Beta.md --as scout
```

```text
refused: scout may not post to Beta (no post grant)
```

You keep the scout's line, with the command the section shows:

```sh
cd vault && obend select Alpha 1 2 && cat Alpha.md
```

```text
kept candidate 2 of section 1 of Alpha
rendered Alpha.md
# Alpha

Alpha is where everything starts. It links to [[Beta]] and to [[Gamma]].

It embeds Beta whole:

![[Beta]]{behind}

and quotes one of its lines: [[Beta#^answer]].
```

## 4. An offline edit

Copy the vault to a laptop, edit Gamma there, and edit the same line here, differently.

```sh
cp -R vault laptop
cd laptop && sed -i.bak 's/^Gamma is a stub./Gamma, written on the train./' Gamma.md && rm Gamma.md.bak && obend open
```

```text
Gamma: v3 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
```

```sh
cd vault && sed -i.bak 's/^Gamma is a stub./Gamma, written at my desk./' Gamma.md && rm Gamma.md.bak && obend open
```

```text
Gamma: v3 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
```

Merge the laptop's world into this one. Each page merges by the pushout of the two versions: what
both sides did is kept, and where they wrote the same place differently, the page gets a section.

```sh
cd vault && obend merge ../laptop && cat Gamma.md
```

```text
Gamma: merged from laptop, 1 section(s) to select
rendered Gamma.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
Gamma: section 1: 2 candidates (owner, owner@laptop); keep one with: obend select Gamma 1 N
# Gamma

<<<<<<< section 1 · candidate 1 (owner) · keep it: obend select Gamma 1 1
Gamma, written at my desk. See [[Alpha]], and [[Delta]], which I have not written yet.
======= candidate 2 (owner@laptop) · keep it: obend select Gamma 1 2
Gamma, written on the train. See [[Alpha]], and [[Delta]], which I have not written yet.
>>>>>>> section 1
```

Keep the laptop's line:

```sh
cd vault && obend select Gamma 1 2 && cat Gamma.md && obend open
```

```text
kept candidate 2 of section 1 of Gamma
rendered Gamma.md
# Gamma

Gamma, written on the train. See [[Alpha]], and [[Delta]], which I have not written yet.
nothing changed
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
```

Or settle a section by hand. Both sides add a line at the end of Gamma; after the merge, delete the
three section lines and keep both lines in the order you want: `obend open` takes that as your edit.

```sh
cd laptop && echo 'A line from the train.' >> Gamma.md && obend open && cd ../vault && echo 'A line from the desk.' >> Gamma.md && obend open && obend merge ../laptop
grep -v -e '^<<<<<<<' -e '^=======' -e '^>>>>>>>' Gamma.md > Gamma.tmp && mv Gamma.tmp Gamma.md
obend open && obend open && cat Gamma.md
```

```text
Gamma: v4 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
Gamma: v6 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
Gamma: merged from laptop, 1 section(s) to select
rendered Gamma.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
Gamma: section 1: 2 candidates (owner, owner@laptop); keep one with: obend select Gamma 1 N
Gamma: v8 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
nothing changed
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
# Gamma

Gamma, written on the train. See [[Alpha]], and [[Delta]], which I have not written yet.
A line from the desk.
A line from the train.
```

## 5. A source moves

Alpha's embed has been behind since step 2: it quotes all of Beta, and adding the law changed Beta's
bytes. `obend recite` re-quotes a page's cites at their sources' current versions.

```sh
cd vault && obend recite Alpha && obend status Alpha
```

```text
re-cited 1 cite(s) of Alpha
rendered Alpha.md
Alpha v4
  [[Beta]] (link) ✓ current: Beta exists
  [[Gamma]] (link) ✓ current: Gamma exists
  ![[Beta]] (embed) ✓ current: the bytes it quotes are Beta's now
  [[Beta#^answer]] (block quote) ✓ current: the bytes it quotes are Beta's now
```

Now Beta gets a new line. Alpha's link `[[Beta]]` cites Beta's identity, so it stays current. Its
quote `[[Beta#^answer]]` cites the bytes of the marked line, which did not change, so it stays current
too. Its embed `![[Beta]]` quotes all of Beta, whose bytes did change: it goes behind. (It still
verifies against the version it quoted; behind is not broken.)

```sh
cd vault && echo 'Beta has grown a line.' >> Beta.md && obend open && obend status Alpha
```

```text
Beta: v4 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
rendered Alpha.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v4) and the bytes it quotes changed
Alpha v4
  [[Beta]] (link) ✓ current: Beta exists
  [[Gamma]] (link) ✓ current: Gamma exists
  ![[Beta]] (embed) ✗ behind: Beta moved on (v3 → v4) and the bytes it quotes changed
  [[Beta#^answer]] (block quote) ✓ current: the bytes it quotes are Beta's now
```

Change the marked line itself, and the line quote goes behind as well:

```sh
cd vault && sed -i.bak 's/forty-two/42/' Beta.md && rm Beta.md.bak && obend open && grep 'Beta' Alpha.md
```

```text
Beta: v5 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
rendered Alpha.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v5) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v5) and the bytes it quotes changed
Alpha is where everything starts. It links to [[Beta]] and to [[Gamma]].
It embeds Beta whole:
![[Beta]]{behind}
and quotes one of its lines: [[Beta#^answer]]{behind}.
```

## 6. Nothing else moved

Through all of this the vault stayed markdown, and opening it once more changes nothing.

```sh
cd vault && obend open && obend open
```

```text
nothing changed
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v5) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v5) and the bytes it quotes changed
nothing changed
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v5) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v5) and the bytes it quotes changed
```

## 7. Aliases, headings, renames and deletions

Obsidian's daily verbs. An alias, `[[Beta|the answer page]]`, is display text: the link cites Beta.
A heading embed, `![[Beta#Results]]`, quotes the heading line and goes behind when it changes; a
heading link, `[[Beta#Results]]`, cites Beta's identity only.

```sh
cd vault
printf '# Epsilon\n\nRead [[Beta|the answer page]] and ![[Beta#Results]]; see [[Beta#Results]].\n' > Epsilon.md
printf '# Beta\n\n## Results\nThe answer is 42. ^answer\n' > Beta.md
obend open && obend status Epsilon
```

```text
Beta: v6 written
Epsilon: new page (v1)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v6) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v6) and the bytes it quotes changed
Epsilon v1
  [[Beta|the answer page]] (link) ✓ current: Beta exists
  ![[Beta#Results]] (block quote) ✓ current: the bytes it quotes are Beta's now
  [[Beta#Results]] (link) ✓ current: Beta exists
```

Change the heading's line, and the heading embed goes behind while the heading link stays current:

```sh
cd vault && sed -i.bak 's/^## Results$/## Findings/' Beta.md && rm Beta.md.bak && obend open && obend status Epsilon
```

```text
Beta: v7 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
rendered Epsilon.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Epsilon v1
  [[Beta|the answer page]] (link) ✓ current: Beta exists
  ![[Beta#Results]] (block quote) ✗ behind: Beta moved on (v6 → v7) and the bytes it quotes changed
  [[Beta#Results]] (link) ✓ current: Beta exists
```

Rename a file, and the page is renamed: same page, same history, and links to the old name still
hold (they cite the page, not its name):

```sh
cd vault && mv Delta.md Theta.md && obend open && obend status Gamma
```

```text
Delta: renamed to Theta (same page, v1; links to Delta still hold)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Gamma v8
  [[Alpha]] (link) ✓ current: Alpha exists
  [[Delta]] (link) ✓ current: Theta exists
```

Delete a file, and the page is deleted: its cites go missing, its history is kept, and a file of
its name revives it. Opening again changes nothing.

```sh
cd vault && rm Theta.md && obend open && obend status Theta && obend open
```

```text
Theta: deleted (its file is gone; v1 kept; a file Theta.md revives it)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Gamma: [[Delta]] (link) is missing: Delta has no version
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Theta: deleted (was v1; a file Theta.md revives it, a new file with its text renames it)
nothing changed
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Gamma: [[Delta]] (link) is missing: Delta has no version
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
```

```sh
cd vault && printf '# Theta\n\nDelta, at last.\n' > Theta.md && obend open && obend status Theta
```

```text
Theta: revived (v1)
Theta: v2 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Theta v2
```

A page under a kind's laws is not deleted by removing its file: the register's postings, a journal's
days. The open says which law keeps it and writes it back.

```sh
cd vault && rm journal/Monday.md && obend open && ls journal
```

```text
journal/Monday: its file is gone, but it is under the law journal/_kind: brief: not deleted, written back
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
rendered journal/Monday.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Monday.md
Tuesday.md
_kind.md
```

A law may be `monotone(FIELD)` or `writeOnce(FIELD)`; both hold at a page's birth (there is nothing
for the first reading to fall below), and bite from the second write on:

```sh
cd vault && printf -- '---\nlaw growing: monotone(words)\n---\nOne two three.\n' > Kappa.md && obend open
printf -- '---\nlaw growing: monotone(words)\n---\nOne.\n' > Kappa.md && obend open
```

```text
Kappa: new page (v1)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Kappa: refused by its law growing: `monotone(words)` does not hold; words = 3 would pass (this write has words = 1)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
```

A page whose birth a law refused says so at every open, not only the first:

```sh
cd vault && printf -- '---\nlaw tiny: new.words <= 1\n---\nTwo words.\n' > Lambda.md && obend open && obend open
```

```text
Lambda: not born: refused by its law tiny: `new.words <= 1` does not hold; words = 1 would pass (this write has words = 2)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
nothing changed
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Lambda: still not born: refused by its law tiny: `new.words <= 1` does not hold; words = 1 would pass (this write has words = 2)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
```

## 8. A merge is judged by what its write read

A write of a page with a law over its links read the pages it links to; a replica's write carries
those readings as pins, and the merge admits it only where they hold. An index that requires every
listed page to be settled (no open section), edited on the laptop while Gamma changed here: the
laptop's write of the index read Gamma as it was there, and is refused here with what moved; the
change is made here instead.

```sh
cd vault
printf -- '---\nlaw settled: linked.sections == 0\n---\n# Index\n\n- [[Gamma]]\n' > Index.md && obend open
cd .. && rm -rf laptop2 && cp -R vault laptop2
cd laptop2 && printf -- '- [[Alpha]]\n' >> Index.md && obend open
cd ../vault && printf 'Gamma gains a line here while the laptop is away.\n' >> Gamma.md && obend open
obend merge ../laptop2
```

```text
Index: new page (v1)
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Lambda: still not born: refused by its law tiny: `new.words <= 1` does not hold; words = 1 would pass (this write has words = 2)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Index: v2 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Lambda: still not born: refused by its law tiny: `new.words <= 1` does not hold; words = 1 would pass (this write has words = 2)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Gamma: v9 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Lambda: still not born: refused by its law tiny: `new.words <= 1` does not hold; words = 1 would pass (this write has words = 2)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Index: not merged: its write at laptop2 read Gamma as it was there (bytes 143 → 193, lines 5 → 6, version 7 → 8, …); make the change here, against Gamma as it is
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
```

```sh
cd vault && printf -- '- [[Alpha]]\n' >> Index.md && obend open && obend status Index | head -1
```

```text
Index: v2 written
journal/Tuesday: still not born: refused by journal/_kind: brief (the kind of journal/, an ancestor of journal/Tuesday): `new.words <= 8` does not hold; words = 8 would pass (this write has words = 14)
Toast: still not born: refused by recipes/_kind: serves (the kind of recipes/, an ancestor of Toast): `not (new.servings == 0)` does not hold; the line `servings: 1` would pass (the page has `servings: 0`)
Lambda: still not born: refused by its law tiny: `new.words <= 1` does not hold; words = 1 would pass (this write has words = 2)
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
Index v2
```

## 9. A merge is settled at the tip

`obend merge` reads the two worlds as two branches of what they share (each page's common history)
and merges them at the TIP (`Obend.Vault.Merge`, `Obend.Vault.Branch.merge`). The tip keeps the
vault's store itself, and every write of either side is judged and landed there by the store's own
write, the same judgment an open makes: landed at the tip and landed in the store are one event
(`tip_lands_iff_store_lands`). The tip is a serial order, here's writes first. The laptop's Brief,
whose law over its links lists Note, read Note as it was there; Note moved here, so Brief is refused
by name. Made again here, Brief's own law refuses it, judged at Note as it is.

```sh
cd vault && printf -- '# Note\n\nShort.\n' > Note.md && obend open > /dev/null
cd .. && rm -rf laptop3 && cp -R vault laptop3
cd laptop3 && printf -- '---\nlaw brief: linked.words <= 6\n---\n# Brief\n\n- [[Note]]\n' > Brief.md && obend open > /dev/null
cd ../vault && printf 'Here it grows by a sentence of ten words or so.\n' >> Note.md && obend open > /dev/null
obend merge ../laptop3 | grep -e Note -e Brief
cp ../laptop3/Brief.md . && obend open | grep Brief
```

```text
Brief: not merged: its write at laptop3 read Note as it was there (bytes 15 → 63, lines 3 → 4, version 0 → 1, …); make the change here, against Note as it is
Brief: refused by its law brief over its links, at Note: `linked.words <= 6` does not hold there; words = 6 would pass (this write has words = 14)
Brief: still not born: refused by its law brief over its links, at Note: `linked.words <= 6` does not hold there; words = 6 would pass (this write has words = 14)
```

Two writes of one page that do not merge are a CONFLICT, and a conflict is a state of the store:
both candidates kept (`.obend/world.json`), neither landed, here's text waiting in the file as a
refused write, every open keeping it, `obend status` listing it. Both replicas wrote a new page
`Pair`, each its own text: two births that name one atom differently, so their texts do not merge.

```sh
rm -rf laptop4 && cp -R vault laptop4
cd laptop4 && printf -- '# Pair\n\nWritten on the train.\n' > Pair.md && obend open > /dev/null
cd ../vault && printf -- '# Pair\n\nWritten at the desk.\n' > Pair.md && obend open > /dev/null
obend merge ../laptop4 | grep Pair
obend open | grep Pair; obend status Pair
```

```text
Pair: here's write was not settled at the merge with laptop4: conflict at Pair: here's Pair and laptop4's Pair (both kept as candidates; neither landed)
conflict at Pair: here's Pair and laptop4's Pair (both kept as candidates; neither landed); keep one with: obend branch resolve 0 left|right
Pair: still not born: not settled at the merge with laptop4: conflict at Pair: here's Pair and laptop4's Pair (both kept as candidates; neither landed)
Pair v0; its last write was not settled at the merge with laptop4: conflict at Pair: here's Pair and laptop4's Pair (both kept as candidates; neither landed)
conflict 0 at Pair: here's Pair and laptop4's Pair (both kept as candidates; neither landed); keep one with: obend branch resolve 0 left|right
```

Resolve it by landing one candidate: the store's own write of it, judged as any write, and the
receipt names the candidate dropped.

```sh
cd vault && obend branch resolve 0 right && cat Pair.md && obend status Pair
```

```text
resolved conflict 0: landed Pair (resolving; dropped here's Pair)
rendered Pair.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v7) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v7) and the bytes it quotes changed
Epsilon: ![[Beta#Results]] (block quote) is behind: Beta moved on (v6 → v7) and the bytes it quotes changed
# Pair

Written on the train.
Pair v1
```

## Branches: two stores fork from one, post offline, and merge at the tip

`obend branch` works on a store file (`Obend.Vault.BranchCli`): pages with owners, law lines, links,
declared merges and states; sturdyrefs; a receipted history. alice and bob each fork it, post
offline (every act is judged on its own branch as it is posted), and the two branches merge at the
tip, where every act is judged again: authority read with both sides' revocations visible, every
write judged by every law of every page in its cone.

```sh
mkdir branch && cd branch && cat > base.json <<'JSON'
{"pages": [
  {"name": "notes/Alpha", "owner": "alice", "state": {"count": 1}},
  {"name": "notes/Beta", "owner": "bob", "state": {"count": 1}},
  {"name": "Shared", "owner": "alice", "state": {"v": 0}},
  {"name": "board/Bob", "owner": "bob", "state": {"posts": 0}},
  {"name": "notes/Gamma", "owner": "bob", "state": {"date": 3}},
  {"name": "Ledger", "owner": "alice", "state": {"date": 1}},
  {"name": "Counter", "owner": "alice", "laws": [["up", "monotone(count)"]], "merges": [["count", "add"]],
   "state": {"count": 1}}],
 "sturdyrefs": [{"uri": "sr:board", "cell": "board/Bob", "held": ["write"]},
                {"uri": "sr:shared", "cell": "Shared", "held": ["write"]},
                {"uri": "sr:counter", "cell": "Counter", "held": ["write"]}],
 "history": [{"seq": 0, "origin": "genesis", "label": "open", "cells": []}]}
JSON
obend branch fork base.json left.json left && obend branch fork base.json right.json right
```

```text
left: forked at receipt 0
right: forked at receipt 0
```

alice, offline: a write of her own page, a write of `Shared`, a post on bob's board through
`sr:board`, an increment of the counter, and a law over `Ledger`'s links listing `notes/Gamma`.

```sh
cd branch && obend branch write left.json alpha notes/Alpha count=2 --as alice &&
  obend branch write left.json shared-a Shared v=1 --as alice &&
  obend branch write left.json post-on-board board/Bob posts=1 --as alice --relies sr:board &&
  obend branch write left.json inc-a Counter count=3 --as alice &&
  obend branch relaw left.json list-gamma Ledger --as alice --links notes/Gamma --law 'dated=not (linked.date == 0)'
```

```text
left: alpha admitted on its branch
left: shared-a admitted on its branch
left: post-on-board admitted on its branch
left: inc-a admitted on its branch
left: list-gamma admitted on its branch
```

bob, offline: a write of his own page, a write of `Shared` through `sr:shared`, an increment of the
counter through `sr:counter`, the revocation of `sr:board`, and the undating of `notes/Gamma`.

```sh
cd branch && obend branch write right.json beta notes/Beta count=5 --as bob &&
  obend branch write right.json shared-b Shared v=2 --as bob --relies sr:shared &&
  obend branch write right.json inc-b Counter count=4 --as bob --relies sr:counter &&
  obend branch revoke right.json revoke-board sr:board --as bob &&
  obend branch write right.json undate-gamma notes/Gamma date=0 --as bob
```

```text
right: beta admitted on its branch
right: shared-b admitted on its branch
right: inc-b admitted on its branch
right: revoke-board admitted on its branch
right: undate-gamma admitted on its branch
```

The merge: the disjoint writes land as one receipted history after the base's; the two counter
increments merge by `Counter`'s declared `add` (its law `monotone(count)` is I-confluent for it) and
land once; alice's board post is refused for the sturdyref bob revoked; alice's law over `Ledger`'s
links refuses bob's undating of `notes/Gamma`; the two writes of `Shared` are a conflict, kept in
the tip with both candidates.

```sh
cd branch && obend branch merge base.json left.json right.json tip.json &&
  obend branch show tip.json Counter && obend branch show tip.json Shared
```

```text
landed 1: left's list-gamma
landed 2: right's revoke-board
landed 3: left's alpha
landed 4: right's beta
landed 5: left+right's inc-a + inc-b
refused: left's post-on-board: relied on the sturdyref sr:board, revoked at the tip by right's revoke-board
refused: right's undate-gamma: refused by Ledger: dated (alice's law `not (linked.date == 0)`), judged at notes/Gamma
conflict 0: conflict at Shared: left's shared-a and right's shared-b (both kept as candidates; neither landed)
Counter: count 6
Shared: v 0
```

The conflict is resolved by landing one candidate; the receipt names the one dropped.

```sh
cd branch && obend branch resolve tip.json 0 left && obend branch show tip.json Shared
```

```text
resolved conflict 0: landed shared-a (resolving; dropped right's shared-b)
Shared: v 1
```
