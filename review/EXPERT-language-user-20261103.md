# Expert read: the language user (PL designer who lives in Mathematica and Obsidian) — 2026-11-03

Slug `language-user`. I spent the session as a user of the built CLI (`lean/.lake/build/bin/obend`,
built 2026-11-01 16:31) and the built GUI (`target/debug/obend-gui`, 2026-11-02 23:58), not as a
reader of theorems. Every claim is tagged **READ** (file:line, or a command I ran and its output),
**INFERRED**, or **PROPOSED**. I edited nothing but this file. Scratch vaults and packages are under
`/private/tmp/claude-501/-Users-ember-dev-obend/a43ef565-cc2f-412d-8808-6f075bdeea89/scratchpad/`
(`garden/`, `g2/`, `obs/`, `big/`, `pkg/`, `pkg2/`, `pkg3/`, `claims/`).

## 0. Verdict

There is one stranger-usable product in this repository and it is very good: `obend open` on a
folder of Obsidian-style markdown, with laws in frontmatter, members who post without overwriting,
offline merge by pushout, cites that know when their source moved, a double-entry ledger whose
refusals name the clause and the value that would pass, and receipts a third party re-judges with
`obend verify`. Behind it the package spine (`check`, `run --package`, `prove`, `verify`, `ground`,
`emit`, `specialize`, `judge`, `admit`) works end to end and says honest things.

Nothing on the front door leads to it. `README.md` does not contain the words `obend open`,
markdown, Obsidian or vault-walkthrough (READ: `grep -c` = 0 for each); its quickstart leads with a
CNC file and two subcommands the binary does not have. The tutorial's 72 commands invoke a runner
from another repository. 24 of the 38 `.obend` programs under `apps/` and `stdlib/` do not
typecheck from the CLI, and 0 of their claims can be reached by `obend prove`. The GUI segfaults on
every subcommand. The notebook format has no instance in the tree and models a single bounded
counter. The digital-garden user is served by the best code here and addressed by none of the
documents a newcomer reads first.

## 1. What I did (so you can rerun it)

```
cd lean && ../lean/.lake/build/bin/obend                      # usage
obend check ../stdlib/physical/Cnc5AxisMill.obend             # README example: 11 JSON lines, 0.2 s
obend run   ../stdlib/physical/Cnc5AxisMill.obend compensatedErrorSample   # result: 26
obend verilate … / obend tapeout …                            # usage: not in this binary
python3 -I tests/vault/walkthrough.py     # 26/26 ok, 6.3 s
python3 -I tests/ledger/walkthrough.py    # 24/24 ok, 6.3 s
python3 -I tests/run-logic.py             # 20/20
python3 -I tests/run-leaf.py              # 14/14
python3 -I tests/run-receipts.py          # 32/32
python3 -I tests/run-workspace.py         # 33/33
python3 -I tests/run-obend-source.py      # probes 30/30, tutorial 71/71, preview cohort 161/161, 72 s
```

Then: every tutorial chapter by hand with `obend run`; the stranger workspace and its competing/
resolved/print variants; the three-package workspace with moved and re-pinned records and `obend
judge`; `check --obligations`, `prove`, `verify`, `ground`, `emit`, `specialize` on ReviewMember
and on packages I wrote; three scratch vaults (laws, members, renames, deletions, Obsidian syntax,
400 generated pages); `obend check` on all 38 app/stdlib files and `prove` on every claim of the
import-free ones; the GUI binary; and the sources named in the brief (`Spec/Law.lean`,
`Spec/LawCompile.lean`, `Spec/LawDial.lean`, `Vault/Law.lean`, `Vault/Cli.lean`, `Doc/Render.lean`,
`Elab/Workbook.lean`, `Doc/Structured.lean`, `Format/Reader.lean`, `crates/obend-gui/src/*`).

## 2. The afternoon: what a stranger can complete today

**READ (ran).** Each of these is a whole workflow with a refusal that names what would pass and a
repair that is then admitted:

- **Vault law.** `law short: new.words <= 20` in Beta's frontmatter; a 27-word edit is answered
  `Beta: refused by its law short: `new.words <= 20` does not hold; words = 20 would pass (this
  write has words = 27)`; the file keeps what I typed, the world does not; shortening it writes v3
  (`tests/vault/WALKTHROUGH.md` §2, reproduced in my `garden/`).
- **Kind law with a frontmatter repair.** `Toast: not born: refused by recipes/_kind: serves …;
  the line `servings: 1` would pass (the page has `servings: 0`)`.
- **Member who may post but not select.** Post → two-candidate section with the exact `obend
  select Alpha 1 2` to run; `obend select … --as scout` → `refused: scout may post to Alpha but
  not select on it (no select grant)`.
- **Offline merge.** Copy the vault, edit the same line both sides, `obend merge ../laptop` →
  one section, both candidates named `owner` and `owner@laptop`; or delete the markers by hand and
  the next `open` takes that as the edit.
- **Ledger.** An unbalanced bill: `refused by register/_kind: balanced …: `new.debits ==
  new.credits` does not hold; debits = 100 would pass (this write has debits = 120)`; fix the kind's
  template, post, `obend verify .obend/receipts/P-0003.json` re-judges the row without the books;
  posting twice is refused naming `P-0001` and the reversing command; a closed period never
  reopens.
- **Package world.** `obend run --package workspace-competing.json` → `refused
  (competing-protocol): kit/export::Export.Export.export for papers/report::Report.Page is
  implemented by kit/pdf::Pdf and by kit/html::Html, neither package extending the other; a
  package extending both decides by implementing it` — and `workspace-resolved.json` is exactly
  that repair (result 840). A moved base: `refused (incompatible-revisions): commons/counter is
  resolved to 1.1.0 by one route and 1.0.0 by another`.
- **Claim → receipt → offline verify.** `obend prove … ReviewMember.Twice.repeated` → `checked …
  by rewrite@1 (3 steps)`; `obend verify r.json` → statement address, the one support `twice ↦
  ReviewMember.Twice`, three ground rows, `verified`. `obend ground … twiceOfThree 8` → `refuted:
  twiceOfThree() == 8 runs to false`, exit 3.
- **Leaf.** `obend emit` prints the slots, each def's reads, `closed: true`, `book: twice(3) = 7`,
  `machine: twice(3) = 7`; `obend specialize` → `book: usable / selected: book`.
- **Impact on a vault page.** `obend analyze impact 'Notes/Rideau@1' --world .` → `0 affected of
  1 dependents … checked (impact@1, decidable, compiled)`.
- **Scale.** 400 generated pages with links and block quotes: `obend open` 0.24 s, re-open 0.19 s,
  one edit 0.22 s, `world.json` 342 KB (`big/`).

The refusal texts in the vault, ledger and workspace are the best I have seen in a "laws" system:
they name the law, its author (page or kind, with the ancestry), the failing value and a passing
one, and when a command would fix it they print the command. That is the thing to protect.

## 3. Suspicions, ranked by how much they would embarrass us in front of this user

### S1. The front door points away from the product (READ; confirmed)

What made me suspicious: `README.md` is a hardware brochure; the one thing a newcomer can run in an
afternoon is not on it.

- `grep -c 'obend open' README.md` = 0; `Obsidian`, `markdown`, `wikilink` = 0. The only root
  document that names the vault user is `AMBITION.md` §3 Realm I / §4.1 (working tree); THESIS,
  DESIGN, PLAN, README do not. `grep -rl Obsidian --include='*.md' .` → `AMBITION.md`,
  `lean/tests/vault/WALKTHROUGH.md`. "Digital garden" appears nowhere.
- README quickstart commands `obend verilate …` and `obend tapeout …` print the usage string
  (READ: ran both). The source has them (`lean/Obend/Main.lean:793`,
  `lean/Obend/Hardware/Cli.lean:479-484`) but `Main.lean` is dated Nov 2 23:54 and the binary Nov 1
  16:31. **INFERRED**: the committed README documents a binary that has not been built; a stranger
  who follows the rules of this brief (no builds) cannot reach §2 of the quickstart.
- `obend check` on the 38 app/stdlib programs: 14 accept, **24 do not** (READ, command in §1's
  loop): 16 fail `import count differs: X` at `objective-package-capture` (they import siblings and
  there is no manifest; the only `package.json` in `apps/` is the untracked
  `apps/quantum-photonic-matter/package.json`, with repo-root-relative paths that work only from
  the root), 8 (`apps/obend-risc/*`, `apps/zk-ntt/*`) fail `unexpected trailing expression token` at
  `0x13n` (`apps/obend-risc/BaseRiscCore.obend:25`; hex literals arrived in `Spec/Parse.lean` on Nov
  2, after the binary). The apps are reached only from Lean, by `#import_obend` in
  `lean/Obend/Apps/*.lean` (READ: `grep -rln '#import_obend' lean` lists the eight App files,
  `Stdlib.lean`, `Workbook.lean`), i.e. at `lake build` time by a Lean developer, never by the CLI.
- `target/debug/obend-gui viewport --kind prose --title Hello` → exit 139 (SIGSEGV), no output;
  `serve`, `run`, `inspect` likewise. `ObendSession::new()` runs before the subcommand match
  (`crates/obend-gui/src/main.rs:45-47`). **INFERRED** cause: the binary links
  `lean/.lake/build/lib/libobend_Obend.dylib` (`otool -L`), which was rebuilt Nov 3 01:12 by the
  parallel swarm, after the binary; I could not rebuild to confirm. What the user sees today is a
  crash.
- `find . -name '*.obnb'` → **zero files** in the tree. The notebook format of `NEXT-MATHEMATICA.md`
  §5 and the GUI's tab 2 has no example a user could open.

Evidence that would clear it: a README whose first command is `obend open`, a built binary that
matches `Main.lean`, one manifest per app, one `.obnb` file. None present.

### S2. The tutorial is for another project (READ; confirmed)

`lean/tests/obend-source/tutorial/TUTORIAL.md` says "You need `bun`, a `lean` binary, and the
compiled Lean modules … `Theory.ObjectiveBendTyping`, `Theory.ObjectiveBendDemandMachine` …", and
every one of its 72 command lines is `bun docs/tutorial/run.ts …` (`grep -c` = 72). Neither
`docs/tutorial` nor `run.ts` exists here. The chapter programs themselves are excellent and all run
under `obend run` (71/71 in `run-obend-source.py`; I ran chapters 1–4 and 9 by hand), and the
diagnostic has only been renamed (`Obend.Core.Machine.Suspension.ticks` for
`Minidregg.Theory…Suspension.ticks`). A stranger reading the prose has no working first command;
the chapter on how to run the chapters points at minidregg.

### S3. `claim` is a restatement checker, and no app claim is reachable (READ; confirmed)

What made me suspicious: every claim in `apps/` and `stdlib/` has the shape `claim
x_open_recursion(a): self.m(a) == <the body of m>`, which is a theorem only about `fix`.

- In my package `pkg2/Claims.obend` (`Base.bump = value + 1n`, `Twice.twice = self.bump(self.bump
  value)`): `claim arithmetic: self.twice(value) == value + 2n` → `unchecked: no producer found a
  certificate` (exit 3) after ground 0, 3, 41 all true; `claim commutes: self.twice(value) + 1n ==
  1n + self.twice(value)` → unchecked; `claim wrong: … == value + 3n` → `refuted: … runs to false
  at [0]` (good). The only producer is `rewrite@1`, late binding plus beta (`Main.lean:596`). There
  is no arithmetic normalisation, no induction, no commutativity. For a "laws plus proofs" language
  this is the first thing a PL person types and the answer is "unchecked".
- `claim box(x) given x <= 10n by judge("interval@1"): self.sq(x) <= 100n` (`pkg3/`) parses and is
  listed `unchecked`; `prove` prints `ground [41]: true` (vacuous: 41 violates the premise) and `no
  producer found`. The AutoCert judges the README advertises are not reachable from the CLI.
- **0 of 38** app/stdlib claims can be listed with an object, proved, or refuted from the CLI. The
  cause is one line: `Obend.Logic.Program.findObject` is applied to the entry's term and the object
  finder requires the seed of `fix(compose …, seed)` to be a record literal (`Main.lean:633`,
  message at `:580`). Every app writes `fix(Spec, seedX())` with a `def seedX()`; my minimal
  variants (`v_seeddef` → `no object of M.Twice is reached from go`; `v_inline`, `v_nocompose`,
  `v_requires` → checked) isolate it. Command: the loop in my transcript over
  `scratchpad/claims/*.json`; every result is `no object of <Spec> is reached from <entry>` for every
  entry I tried, including the defs that return the object (`compensated5AxisMill`,
  `institutionalZoeSeat`, `pureWord64`).

Verdict: the claim language is honest about what it cannot do, but it can do almost nothing a user
would call proving, and the eight flagships' claims are unreachable from the only user interface.

### S4. The vault law fragment versus what a note-taker types first (READ; mostly by design, one defect)

The grammar is `Spec/Law.lean:16-21`: `REF == INT | REF <= INT | REF in [..] | REF == REF | REF <=
REF | REF <= REF + INT | monotone(F) | writeOnce(F)` with `and/or/not/implies`; REF is `new.FIELD`,
`request.{subject,caller,turn}`, `ledger.height`. What I tried in `garden/` and what came back:

| law line | answer |
|---|---|
| `new.links >= old.links` | `law outside the enforced fragment: the character `>`` |
| `1 <= new.quotes` | `` `1` where a reference new.FIELD, request.FACT or ledger.height was expected `` |
| `new.words + new.lines <= 100` | `the operator `+` (an atom is REF == …, REF <= …, or REF in [INT, …])` |
| `new.status == draft` | `` `draft` where a reference … was expected `` (strings are not readable) |
| `new.words <= Beta.words` | `` `Beta` where a reference … was expected `` (no cross-page refs) |
| `old.links <= new.links` | `old.FIELD outside monotone(FIELD) and writeOnce(FIELD)` |
| `monotone(links)` on a new page | `not born: refused by its law growing: `monotone(links)` does not hold; no change of one field passes` |
| `monotone(words)` added to an existing page, then a shrinking edit | `refused … words = 11 would pass (this write has words = 1)` (correct) |

The first six are design (a difference-constraint fragment so that `LawDial.solveLawWitness` can
synthesise repairs, `Spec/LawDial.lean:21-30`); the messages are precise and I accept the trade.
Two things are not acceptable to a user: (a) `>=`, `<`, `>` are refused as *characters* with no hint
that `not (new.quotes == 0)` or swapping the sides is the spelling; (b) **a page with a
`monotone(F)` law can never be born**: `LawExpr.denote` makes `monotone` false when there is no old
state (`Spec/Law.lean:161-164`), `Occ.birth` passes `none` (`Vault/Law.lean:78-82`), and
`LawCompile.lean`'s header says so ("At a first write … `monotone` is false"). The repair text "no
change of one field passes" is then literally true and completely misleading. `writeOnce` at birth
is `true` (`Law.lean:165-168`); `monotone` should be too.

### S5. Obsidian's daily operations are not modelled (READ; confirmed)

The vault is advertised as Obsidian-shaped (`WALKTHROUGH.md:3`, `AMBITION.md` §3 Realm I). The
things an Obsidian user does every hour:

- **Alias links.** `[[Home|the index]]` → `dangling: no page of that name` (`obs/`). `takeLink`
  reads everything up to `]]` as the name (`Doc/Render.lean:46-50`); there is no `|` split. This is
  the most common link form in a real vault.
- **Heading transclusion.** `![[Beta#Method]]` is reported as `(link) ✓ current: Beta exists` and
  does not go behind when the section's text changes (`g2/`). `AMBITION.md` §3 names
  `![[Page#Heading]]` via `Obend.Doc.renderTranscludedAt`; `grep -rn renderTranscludedAt lean/Obend`
  finds no caller outside `Doc/Render.lean`. The claim is prose.
- **Rename.** `mv Notes/Faré.md Notes/Rideau.md; obend open` → `Notes/Rideau: new page (v1)` and
  `Notes/Faré` stays in the world forever, reporting its own cites (`garden/`). Obsidian rewrites
  links on rename; here the old identity is a ghost and the new one has no history.
- **Delete.** `rm Impl.md; obend open` → `nothing changed`; `obend status Impl` → `Impl v1`; and
  the next non-`open` command writes the file back: `rm Beta.md; obend recite Alpha` → `rendered
  Beta.md`, file reappears (`g2/`; `Vault/Cli.lean:111-119`, `finish` rewrites every page with
  history whose file is missing). A page cannot be deleted. The `{missing}` mark of
  `AMBITION.md` §3 never appears: after the delete Alpha's cites still say `✓ current: Beta exists`.
- **`.obend` files in the vault** are not pages (`Values.obend` absent from `world.json`), against
  `AMBITION.md` §3 "a folder of plain `.md` and `.obend` files is a live formal repository".
- **Silent unborn pages.** After a law refusal at birth, every later `obend open` prints `nothing
  changed` however the file changes (`garden/`, three times). The refusal is shown once; only
  `obend status` repeats it.
- Things that were fine: `.obsidian/` is ignored; unicode and spaces in names; nested folders;
  `tags:` lists; `%%comments%%` links are counted (debatable); `.canvas` ignored;
  `sketch.excalidraw.md` becomes a page (debatable).

### S6. Silent and inconsistent surfaces (READ)

- `obend check FILE` prints one compressed JSON object per declaration with the full row type
  inlined (the Cnc5AxisMill line is ~2 KB); there is no human form (`Main.lean:449-457`). The
  first command in the README is unreadable.
- A type error is one catch-all sentence with no location: `typing refused: types disagree, a
  custody value is shared or captured, or an activity rule (an Activity is refused as an argument,
  record/extend field, specification or prototype component, or sum payload; a Plan must be a sum
  of first-order data; a response must be first-order data)` (`SumsIllTyped.obend sum`). Compare the
  elaboration refusals, which are exemplary (`refused (requires-unprovided): this fix leaves
  missing of its final self unprovided: no layer of the composition and not the seed provides it
  (required by RequiresUnprovided.Needs)`).
- `obend status Nope` prints nothing, exit 0. `obend run FILE ENTRY` that suspends exits 0.
  `obend open --help` exits 1 with the usage. `obend judge` and `obend admit` are not in the usage
  string though the test suite depends on them (`run-workspace.py:62,98`).
- `obend judge --package ws '{"total":5}' '{"total":60}'` → `refused: ext/right law capped
  (capped)`, exit 0, and **no "would pass"**: the repair synthesis THESIS §1.4 promises
  (`suggestMultiField_admits`, which does not exist; the tree has
  `suggestMultiField_coupledMultiFieldLaw`, a `decide +kernel` example, `Vault/Law.lean:285`) is
  wired into the vault path only.

### S7. The eight apps are fixtures (READ + INFERRED; confirmed)

Census (`apps/*/*.obend`, `stdlib/*/*.obend`, 38 files, 47–98 lines each): every file is one
`record` of `Nat`-valued methods, two or three `spec`s, a `def seedX()` of zeros, and claims named
`*_open_recursion` whose right-hand side is the method body (`Seat.obend:27`, `Cnc5AxisMill.obend:27,
45`). The "5-axis volumetric error" is `arm * 4`; the Zoe seat's `offerSafetyMargin` is `cbdcEscrow
+ fillRatioPct * 250`. There are no manifests, no inputs, no outputs but one `Nat`, and (S3) no
claim reachable from the CLI. They are exercised as Lean test fixtures through `#import_obend`.
Nobody can *use* an app; a Lean developer can build one. The README calls them "8 end-to-end
flagship userspace qualification applications".

### S8. The notebook is a counter (READ; confirmed)

`ObnbWorkbook` is `title, lawName, boundField, maxBound, cells` with cells `prose | obend
name:field:delta | leanBridge theorem:spec` (`Format/Reader.lean:401-407, 412-416`);
`lowerObnbToObend` turns any workbook into one record with a single `step(delta)` method adding to
one field (`Reader.lean:640-660`). `obend-gui run NOTEBOOK` reads the bytes, calls `eval_cell`, and
prints `Evaluated N bytes successfully` (`crates/obend-gui/src/main.rs:50-54`); `inspect` prints the file size. The GUI's
tabs are `1. Literate .obend Workbook & PIDE Explorer / 2. .obnb CAD/Multiphysics & Lean 4 /
3. Rehydratable Membranes / 4. Live FPGA HAL, ILA & ICAP DPR / 5. 8 Flagship Apps & VCD Waveforms`
(`server.rs:4171-4175`); its only "vault" is a DeOS `vault_value` membrane demo (`server.rs:231`).
`NEXT-MATHEMATICA.md` §5 describes CAS cells and `Content.cell` AST merges. The GUI and the
markdown vault are two unconnected products; the notebook user and the garden user never meet.

### S9. Cleared: what is as good as it says (READ)

- `Vault/Law.lean:149-205`: `judge_admits` and `judge_refuses` are universally quantified over
  laws, state type, states and occasion; the vault's refusals rest on real theorems.
- `obend identity` prints the front-end's source hashes; `obend verify` works with no producer
  state; the receipt names supports, ground rows and regime.
- The pushout merge and the sections-as-candidates design are correct and pleasant.
- 400 pages in 0.24 s.
- All seven Python runners green against this binary (counts in §1).

## 4. What the language feels like to write, and what it cannot say

READ (tutorial chapters 1–9, `Spec/Parse.lean` keywords, the stranger and world programs).
`edition ObjectiveBend 1`; `record`, `sum`, `def`, `fn`, `spec … for …` with `self`/`super`,
`extension`, `fix`, `compose`, `extend`, `requires`, `claim … [given …] [by judge("…") | by
weave]`, `law NAME: EXPR` at package level, `package … extends …@^1`, `import … as …`; `Nat` with
the `n` suffix, `Bool`, `String` as labels, total `match` on `0n`/`1n+p` with no wildcard, lazy
fields, linear `once` custody, activities with yielded plans. The late-binding chapters are the
best teaching material in the repository: `raisedTotal` = 16 because `Defaults` read a `base` a
later layer changed, and nobody edited `Defaults`.

What it cannot say, from this chair: a negative number, a real, a string you compute with, a list
you did not define yourself, a polymorphic function, a claim that needs `x + 1 + 1 = x + 2`, a law
about two pages, a law with `>=`. Everything numeric is a `Nat` with the unit in the identifier
(`servoLagUm`, `cantileverArmDm`). That is a fine core for a laws-and-objects calculus; it is not
within sight of "what comes after Mathematica", and the documents should stop implying otherwise
until `Analysis/` is reachable from a `.obend` file through a judge a user can call.

## 5. The root documents' promises a user can touch today

| Promise (document) | Touchable | Where |
|---|---|---|
| Laws judged on every write, refusal names clause and passing value (AMBITION, THESIS §1.4) | **yes** (vault, ledger) | `obend open`, `obend ledger post` |
| Members propose without overwriting; offline merge through one door (AMBITION) | **yes** | `post`/`select`/`merge` |
| A quote knows when its source moved (AMBITION) | yes for whole-page embeds and `^block` quotes; **no** for headings | S5 |
| Stranger-checkable receipts (`obend verify`) | **yes** (ledger rows, claim receipts) | §2 |
| Stranger extends a stranger's package without copying (THESIS §3) | **yes** | `stranger/`, `three-package/` |
| Constructive multi-field repair (THESIS §1.4) | vault only; not `obend judge` | S6 |
| `claim` proofs (THESIS §1.4, README "Lean soundness proofs") | restatements only; app claims unreachable | S3 |
| AutoCert `interval@1`, `taylor-model@1` … from `.obend` (README) | **no** from the CLI | S3 |
| Eight usable flagship apps (README) | **no** (24/38 files do not check; no manifests) | S1, S7 |
| `obend verilate`, `obend tapeout` (README) | **no** in the built binary | S1 |
| `.obnb` notebooks, PIDE workbench (README, NEXT-MATHEMATICA) | **no** (0 files; GUI segfaults) | S1, S8 |
| `.obend` files as vault pages, `{missing}` marks, heading transclusion (AMBITION §3) | **no** | S5 |
| Tutorial (TUTORIAL.md) | programs yes; instructions no | S2 |

## 6. Where the digital-garden user stands

They are standing on the only finished floor of the building and the signs all point upstairs.
`AMBITION.md` (working tree) gives them Realm I of four and the first of four "universal measure"
scenarios; README gives them nothing; the GUI does not know they exist; the tutorial is for
programmers of another repository. Their daily verbs — rename, delete, alias, link to a heading —
are the ones that break. The things they would come for — a law on a note that refuses an edit and
says what would pass, a collaborator who can propose but not overwrite, a merge from the laptop, a
quote that knows its source moved, a ledger that is a folder of markdown — already work and are
faster than they need to be.

## 7. Three changes first

1. **Make `obend open` the front door and fix its five daily verbs.** README §Quickstart becomes
   the first eight lines of `tests/vault/WALKTHROUGH.md`; the tutorial's `bun docs/tutorial/run.ts`
   becomes `obend run lean/tests/obend-source/tutorial/` (one `sed`, then re-run
   `run-obend-source.py`). In `Doc/Render.lean:46` split the name at `|`; wire `renderTranscludedAt`
   for `![[P#Heading]]`; treat a missing file as a deletion (a tombstone version, cites go
   `{missing}`, no resurrection in `Vault/Cli.lean:111-119`); detect rename as delete+birth with the
   same identity when the bytes match; make `monotone` true at birth (`Spec/Law.lean:163`; the
   `compile_birth` proof at `Spec/Proofs/LawCompile.lean:509` moves with it) and print the refusal of an
   unborn page on every `open`. Cost: a few days of Lean in `Doc/Render`, `Vault/{Page,Cli,Law}`,
   `Spec/Law` plus their proofs and the two walkthroughs; zero new mechanism.
2. **Make the apps checkable and their claims reachable, or stop calling them apps.** One
   `package.json` per app directory (the QPM one is the template), paths relative to the manifest;
   `findObject` to follow a `def seedX()` (`Main.lean:633`; the finder is
   `Obend/Logic/Program.lean:84`); `check --obligations` and `prove` in each app's README; rebuild the
   binary so `0x13n`, `verilate` and `tapeout` exist or remove them from README. Cost: a day for the
   manifests and finder, one build. Until then README's "8 end-to-end flagship userspace
   applications" should read "8 Lean fixtures".
3. **One real notebook or none.** Either a single `.obnb` in the tree that a user can open
   (`obend-gui run`), with cells that are `.obend` definitions and at least one claim refuted by
   `tooth` as `NEXT-MATHEMATICA.md` §4.4 describes, and a GUI binary that starts; or delete the
   notebook claims from README and NEXT-MATHEMATICA until Phase 5 lands. Cost of the first: the
   FFI/dylib skew diagnosis, one example file, and `crates/obend-gui/src/main.rs:50-54` doing more than printing a byte
   count — probably a week; of the second: an hour.

## 8. The one question for Ember

Is the person you are building for the one in the Oct 29 brief — notes in Obsidian, a Mathematica
habit, who wants laws on their own pages — or the one on the current README? The vault code answers
"the first" and every document written since Oct 31 answers "the second". Until that is decided no
one can say which of the two unfinished halves (the garden's daily verbs, or the claim/judge/notebook
tower) is the one to finish, and the swarms will keep landing on the louder one.
