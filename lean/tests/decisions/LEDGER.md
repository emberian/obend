# The decisions ledger itself, under its kind: a walkthrough

`review/DECISIONS-20261031.md` is the project's ledger of decisions and `review/ledger/_kind.md`
is its kind: `appendOnly per ##` (no line of a section removed or rewritten) and `cited per ##`
(the lines a write adds cite no backticked name the environment lacks, the environment being the
census's list the kind names). This walkthrough copies `review/` into the work directory (the
real one is not touched), shows the adoption of the ledger as it stands, then a row added with
`obend post --into`, a row rewritten in place, and a row naming a theorem the library does not
have. `python3 tests/decisions/walkthrough.py` runs it (from `lean/`, after `lake build obend`)
after `WALKTHROUGH.md`, writing the environment first when it is missing.

## 1. The ledger before its kind

The ledger's first version is the file as it stood before the kind: `kind: ledger` lifted from it
here to replay that moment (the real file carries the line; `review/.obend/world.json` carries the
two versions below). A page without a kind line and outside any kind folder has no laws: its first
open is the birth of its history, not a judgment of it.

```sh
ln -s "$OBEND_ROOT/lean" lean && cp -R "$OBEND_ROOT/review" review && rm -rf review/.obend && cd review
tail -n +4 DECISIONS-20261031.md > D.tmp && mv D.tmp DECISIONS-20261031.md
obend open | grep -E 'DECISIONS-20261031|ledger/_kind|refused'
```

```text
DECISIONS-20261031: new page (v1)
ledger/_kind: new page (v1)
```

## 2. Adoption

Naming the kind is the owner's write that adopts its laws: judged with the old state the new
(`Occ.adopt`), so `appendOnly per ##` holds (the write removes nothing) and `cited per ##` holds
(the write adds no line but the kind's). The names the ledger already cites that the environment
lacks are not judged; `obend status` lists them (the list depends on the environment the machine
wrote and is not recorded here; the report records it on the day).

```sh
cd review
printf -- '---\nkind: ledger\n---\n' | cat - DECISIONS-20261031.md > D.tmp && mv D.tmp DECISIONS-20261031.md
obend open | grep DECISIONS-20261031
obend status DECISIONS-20261031 | sed -E 's/(lacks: ).*/\1(the names as of the recording are in the report)/' | head -2
```

```text
DECISIONS-20261031: v2 written
DECISIONS-20261031 v2
  names the environment lacks: (the names as of the recording are in the report)
```

## 3. A row added to a section

The owner's `obend post PAGE ROW --into HEADING` is the owner's write of the page with the row's
lines at the end of the section HEADING begins, judged like any write: the row removes nothing from
its section and the names it cites are the library's.

```sh
cd review
printf '| The ledger is a vault: a row is added with `obend post` into its section, judged by `review/ledger/_kind.md`; `judge_admits` is the theorem the judge rests on | frame lane, `lean/tests/decisions/LEDGER.md` | a kind page |\n' > ../row.md
obend post DECISIONS-20261031 ../row.md --into "Taken by lanes under standing approval, 2026-11-04"
grep -c 'The ledger is a vault' DECISIONS-20261031.md
```

```text
owner posted to DECISIONS-20261031 (v3)
rendered DECISIONS-20261031.md
1
```

## 4. A row rewritten in place

An edit of a line the ledger already has, in an editor: refused at the section, with the number of
lines the write removed; the file keeps the edit, and the next open with the line put back changes
nothing.

```sh
cd review
sed -i.bak 's/^| No per-theorem axiom lists; one crawling census | yes |/| No per-theorem axiom lists | yes |/' DECISIONS-20261031.md && rm DECISIONS-20261031.md.bak
obend open | grep DECISIONS-20261031
sed -i.bak 's/^| No per-theorem axiom lists | yes |/| No per-theorem axiom lists; one crawling census | yes |/' DECISIONS-20261031.md && rm DECISIONS-20261031.md.bak
obend open | grep -E 'DECISIONS-20261031|nothing changed'
```

```text
DECISIONS-20261031: refused by ledger/_kind: appendOnly per ## (the kind of ledger/, an ancestor of DECISIONS-20261031) at ## Decided by Ember: `new.deletions == 0` does not hold there; deletions = 0 would pass (this write has deletions = 1)
nothing changed
```

## 5. A row naming a theorem the library does not have

Refused at the post: the file is untouched, and the refusal names the section, the law and the name.

```sh refused
cd review
printf '| Constructive repair is proved: `suggestMultiField_admits` | frame lane | none |\n' > ../bad.md
obend post DECISIONS-20261031 ../bad.md --into "Open for Ember (2026-11-04)"
```

```text
DECISIONS-20261031: refused by ledger/_kind: cited per ## (the kind of ledger/, an ancestor of DECISIONS-20261031) at ## Open for Ember (2026-11-04): `new.unresolvedInserted == 0` does not hold there; unresolvedInserted = 0 would pass (this write has unresolvedInserted = 1); names the environment lacks: suggestMultiField_admits
```

```sh
cd review && grep -c suggestMultiField_admits DECISIONS-20261031.md || true
```

```text
0
```
