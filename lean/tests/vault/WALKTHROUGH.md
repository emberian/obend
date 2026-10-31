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
page's measures (`words`, `lines`, `bytes`, `links`, `embeds`, `quotes`, `sections`, `version`), its
frontmatter's number and true/false fields, and who is writing (`request.caller`: 0 is you). Adding a
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
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
```

```sh
cd vault && sed -i.bak 's/^Gamma is a stub./Gamma, written at my desk./' Gamma.md && rm Gamma.md.bak && obend open
```

```text
Gamma: v3 written
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
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
Gamma: v6 written
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
Gamma: merged from laptop, 1 section(s) to select
rendered Gamma.md
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
Gamma: section 1: 2 candidates (owner, owner@laptop); keep one with: obend select Gamma 1 N
Gamma: v8 written
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v1 → v3) and the bytes it quotes changed
nothing changed
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
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v5) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v5) and the bytes it quotes changed
nothing changed
Alpha: ![[Beta]] (embed) is behind: Beta moved on (v3 → v5) and the bytes it quotes changed
Alpha: [[Beta#^answer]] (block quote) is behind: Beta moved on (v1 → v5) and the bytes it quotes changed
```
