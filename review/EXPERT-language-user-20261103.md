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

## What landed (2026-11-04)

Ember's answer (`review/DECISIONS-20261031.md`, 2026-11-04): the frame is research into the
consequences of the design decisions; the user is a lens, never the overriding frame. The report
above became the plan, read through that answer. Built and checked on bb2 in `~/lane-frame` (a copy
of the verify tree overlaid with HEAD `85e6fd5` and these files; `swarm-build lake build obend`,
then `Obend.Vault Obend.Doc Obend.Spec Obend.Law Obend.Ledger Obend.Vault.Escrow Obend.FFI.Bridge
Obend.Teeth.Spec.LawCompileTeeth Obend.Teeth.Law.LawJudgeTeeth Obend.Teeth.Vault Obend.Analysis.Impact
Obend.Elab.Workbook Obend.Logic.Program`, 285 jobs, 0 errors; the whole-library target `Obend` does
not build at HEAD on bb2 for a reason outside this lane: `Obend/Apps.lean` is named and absent).
Commits, all unsigned:

- `fcad2f8` **law: `monotone(F)` holds at a first write.** `Spec/Law.lean`, `Spec/LawCompile.lean`,
  `Spec/Proofs/LawCompile.lean` (not in this lane's list; the proof moves with the definition),
  `Spec/LawDial.lean`. S4's birth defect. Teeth `first_write_teeth`/`adopt_teeth` assert the new
  verdict.
- `8efc555` **logic: the object finder reads a seed written as a `def` call.** `Logic/Program.lean`:
  `seedRecord`, `decodeProgram`, `object_bequiv_of_operands_seed`. S3's reachability gap: on bb2,
  `obend prove stdlib/physical/Cnc5AxisMill.obend Cnc5AxisMill.Uncompensated5AxisMill.volumetric_decomposition
  --object compensatedErrorAt6Dm` → `checked … by rewrite@1 (3 steps)`; `apps/sovereign-drex` and
  `apps/silicon-kernel-verilator` list their claims at their objects (`unchecked`, as restatements
  the rewriter does not reach through a 0-arity member). `FFI/Bridge.lean`'s private copy
  (`decodeProgramWithSeed`) is now redundant; its owner can call `Program.findObject`.
- `1f3d693` **vault: aliases, heading embeds, deletions and renames, refusals said at every open.**
  `Doc/Render.lean` (`target` drops `|alias`; S-2's heading embed kept), `Doc/Section.lean` and
  `Vault/Page.lean` (S-2, kept as a pair), `Vault/Store.lean` (`tombs`, `forgetMissing`, `tombLine`),
  `Vault/Json.lean`, `Vault/Cli.lean` (`forgottenLines`, `unbornLines`, `status` of a tomb or of no
  page, exit 2). S5 and S6. `tests/vault/WALKTHROUGH.md` §7 is the evidence, recorded on bb2 and
  read: alias link current; `![[Beta#Results]]` behind after the heading changes while
  `[[Beta#Results]]` stays current; `mv Delta.md Theta.md` → `Delta: renamed to Theta (same page,
  v1; links to Delta still hold)` and Gamma's `[[Delta]] ✓ current: Theta exists`; `rm Theta.md` →
  deleted, `Gamma: [[Delta]] (link) is missing`, second open `nothing changed`; the file returning
  revives it; `rm journal/Monday.md` → `its file is gone, but it is under the law journal/_kind:
  brief: not deleted, written back`; a page born under `monotone(words)` and refused when it shrinks;
  `Lambda: still not born: …` at the second open. 34 steps ok; the ledger walkthrough 24 ok.
- `cfd6bce` **cli: a directory is a package; manifests resolve from anywhere; a file with imports
  names the fix.** `Main.lean` (S-2's auto-detecting `packageOfSpec` kept; `packageOfObendDir`
  rewritten with dependency order and import locks; `resolveSourcePath`/`resolvedSpec`; the single-
  file refusal; usage), `tests/run-workspace.py` (every `apps/` directory), the two S-6 world
  programs kept. S1's 24 non-checking programs: 16 now check as directories or through their
  manifests; the 8 with hex literals parse with a current build; of the eight app directories four
  accept and four (`foc-hil`, `obend-risc`, `sdr-ft8`, `zk-ntt`) are refused by the front end with
  `a law belongs to the package's entry module; X is imported and declares N law(s)`, the programs'
  own defect, for their owners. `run-workspace.py` 42/42, `run-obend-source.py` 30/30, 71/71,
  161/161, `run-logic.py` 20/20, `run-leaf.py` 14/14, `run-receipts.py` 31/31 on bb2 (32 on the
  Mac: one check runs only where `cadical` is installed).
- `7bc9190` **obend-gui: the Lean session opens only where needed; subcommands say what they do.**
  `crates/obend-gui/src/main.rs`, `tests/challenger_gui_cli.rs`. S1's segfault: the crash was in
  `ObendSession::new()` run before the subcommand; `viewport` and `help` no longer touch Lean (ran on
  bb2); `run`→`eval-bytes` (an FFI smoke test, said so), `inspect` removed. The suspended lane's
  +3,972-line GUI diff is reverted (5 red tests under the stub FFI; HEAD green:
  `cargo test -p obend-gui` 7+6+1+10 ok). **Not fixed**: why the native session itself segfaults on
  the Mac. INFERRED from `crates/obend-ffi/src/pool.rs:9-18` and `lean/c/obend_bridge.c:28-50`: the
  Rust side calls `lean_initialize_thread()` before any `lean_initialize_runtime_module()`; the C
  bridge initialises the runtime only inside `obend_session_init`. For the FFI owner.
- `3ccc30d` **docs.** `AMBITION.md` rewritten in the research frame with "What this is not", the
  stranger's workflow as the measure of a subsystem, the user stories as lenses, no counts.
  `README.md` a draft in that frame, marked for ember to voice, naming only what the built binary
  does. `THESIS.md` without counts and without `suggestMultiField_admits`.
- `review/GEMINI-HANDOFF-20261103.md` §Adjudications: this lane's calls on its dirty files.

Not done, for the record: `obend judge` (package level) still names the refusing law without a
"would pass"; `obend check` output is still one JSON object per declaration; `prove` still certifies
restatements only (by design, now said in README); a deletion of a page under a kind's laws is
refused rather than judged (a deletion is not yet an occasion the law fragment can speak about); the
tutorial's `bun docs/tutorial/run.ts` lines are unchanged (the runner substitutes `obend run`; the
prose still points at minidregg); no `.obnb` example exists.

## What landed, second round (2026-11-04): module laws and the dogfood vault

### Quest 1 — a law in an imported module binds the importing package (`48727bb`)

Decision: **yes.** A package's laws are its root (entry) module's, bare, then those of every module
on the root's C4 precedence list over the module import graph, each named `Module.NAME`
(`lean/Obend/Spec/Syntax.lean`: `modulePrecedence`, `packageLaws`). Each import is its own C4 chain:
a module that imports `A` and then a `B` that imports `A` is not claiming `A` precedes `B` (the first
version, which took import order as a local chain, refused every such package with `no C3
candidate`, including the three-package and stranger workspaces). `FrontEnd.lowerDecoded` collects
them for a single package, `Workspace.close'` per package of a workspace (so the workspace rule
"a package's laws live in its root module" is generalised the same way), and `Workspace.judgeWith`
judges any `(package, laws)` list: `obend judge --package SPEC` takes a directory, a file or a
`package.json` as well as a workspace. The refusal names the module:

```
$ obend judge --package apps/foc-hil '{…, "modulationPermille": 500}' '{…, "modulationPermille": 1001}'
refused: foc-hil law ClarkePark.bounded_modulation_index (bounded_modulation_index)
clauses: foc-hil law monotone_hil_step, …, foc-hil law ClarkePark.monotone_electrical_angle, foc-hil law ClarkePark.bounded_modulation_index
```

READ (bb2): all eight `apps/` directories now `obend check` with every declaration accepted;
`run-workspace.py` 44/44 (two checks judge `apps/foc-hil` within and against ClarkePark's law);
`run-obend-source.py` 30/30, 71/71, 161/161; `run-logic` 20, `run-leaf` 14, `run-receipts` 31;
both walkthroughs. A judge over a state that lacks a field a law reads is refused by that law (an
absent reading is false, `Spec/Law.lean:136`): the state handed to `obend judge` must carry every
field the package's laws read, which is why the check builds the full `FOC` state. Files outside
this lane's list that the change needed: `Spec/Syntax.lean`, `Spec/FrontEnd.lean`,
`Spec/Workspace.lean` (recorded in the handoff).

### Quest 2 — the decisions ledger as a vault (`f3b832e`)

`lean/tests/decisions/WALKTHROUGH.md`, run by `tests/decisions/walkthrough.py` (the vault runner
with `--doc`), recorded on bb2 and read: 10 steps. The seed is `review/DECISIONS-20261031.md`: its
preamble as the index page `Ledger.md`, three of its rows as `decisions/D-000{1,2,3}`, and a kind:

```
law dated: not (new.date == 0)        law dateOnce: writeOnce(date)
law decider: new.decider in [1, 2, 3] law deciderOnce: writeOnce(decider)
law appendOnly: monotone(bytes)       law appendLines: monotone(lines)
law cited: new.dangling == 0          date: 0   decider: 0
```

Admitted: a lane's dated decision (`D-0004`, decider 3) quoting `[[environment/Theorems#^judge_admits]]`
and `…^judge_refuses]]`; the index gains its link. Refused, each naming the ancestor and clause:
`D-0005` citing `suggestMultiField_admits` (not in the census page) → `refused by decisions/_kind:
cited (the kind of decisions/, an ancestor of decisions/D-0005): new.dangling == 0 does not hold;
dangling = 0 would pass`; `decider: 4` → `decider … the line decider: 3 would pass`; no date →
`dated`; a shortened `D-0001` → `appendOnly: monotone(bytes) … bytes = 158 would pass (this write
has bytes = 78)`; re-dated → `dateOnce`; re-decided → `deciderOnce`; a link dropped from the index →
`Ledger: refused by its law appendOnly: monotone(links)`; `rm decisions/D-0002.md` → `its file is
gone, but it is under the law decisions/_kind: dated: not deleted, written back`; `obend create
--from decisions` writes the template and says it is not born until dated.

Two things the exercise needed and the vault gained: a `dangling` measure (`Vault/Page.lean`
`danglingCount`), so a law can say every cite of a page resolves; and a kind page is no longer judged
by its own law lines (`Store.ownLaws`): before, a kind whose instances must be dated could not be
born, because its own `date: 0` default violated its own law. (`Vault/Page.lean`, `Vault/Law.lean`
doc: outside the list, recorded.)

**What the vault could not express about our own process** (the deliverable):

1. **The unit of law is the page; the ledger's unit is the row.** The real ledger is one file of
   tables. No law can speak about a row: a date or decider per row, a row appended, a row cited.
   The vault only governs the ledger once each decision is its own page; the file in `review/`
   stays prose. A `rows` measure, or laws over a page's list items, would be the primitive.
2. **No strings.** `decider` is a code (1 Ember, 2 integrator, 3 lane), not a name; `date` is a
   number with no calendar (20261199 is dated); "where" (a commit hash, a file) is unreadable; a
   decision's text is counted, never read. The fragment reads naturals and booleans so that the
   difference-constraint solver can repair; every string in our process is outside it.
3. **Append-only is a count.** `monotone(bytes)` and `monotone(lines)` refuse a shortening and
   admit any rewrite that keeps or grows the counts: a decision's text can be replaced wholesale.
   The property we mean is "the old text is a prefix (or sub-sequence) of the new", which is about
   `old.` and `new.` bytes, and the fragment lets `old.` in only through `monotone`/`writeOnce`.
   The doc graph knows exactly which atoms a write deleted (`pieces`, `Step.del`); a law cannot
   ask it. `deleted == 0` as a measure of a write (not of a state) would be the primitive, and it
   is a different kind of measure: of the patch, not the page.
4. **"Names a theorem the environment has" is a cite into a page a person maintains.** The census
   page is a page like any other: anyone who can write it can add a name; nothing ties its lines to
   the Lean environment. Until the gate lane's identifier census writes that page from the build,
   the law proves that a name is on a list, not that a declaration exists. And `dangling == 0`
   forbids every unresolved link on the page, not only theorem cites: a decision cannot mention a
   page not yet written.
5. **Authority is not provenance.** `request.caller` is who commits the write; a lane's decision is
   posted by the lane and selected by the owner, and the selection is the owner's write, so
   `new.decider == request.caller` (expressible, `REF == REF`) would refuse the owner's selection of
   a lane's row and admit a lane claiming to be Ember on its own page. The poster of a candidate is
   in the authors list (`Page.authors`), not among the facts a law reads. "Taken under standing
   approval" and "reversible, cost to reverse" are prose.
6. **No cross-page facts.** "Dated no earlier than the previous decision", "the ledger lists every
   decision page", "`D-0004` cites a decision that exists" are relations between pages; a law reads
   one page's state and the request. The index page's `monotone(links)` is the nearest thing, and
   it cannot say which pages.
7. **A kind's own laws are not protected.** The owner can edit `decisions/_kind.md` and weaken
   `appendOnly` in one write; the kind page is judged by the kinds above it (none, at the vault's
   root). A ledger whose rules the keeper can relax silently is the thing the ledger exists to
   prevent. A root `_kind.md` with `writeOnce` on something could not reach law lines, which are
   not fields. A member grant `relaw` exists for pages; a kind's law lines need the same door and a
   law about who may pass it.
8. **The real file cannot be the vault's page.** `obend open review/` would make every review
   document a page, which is fine, but the decisions file would be one page with the limits above;
   the walkthrough therefore seeds pages from its rows by hand. If the ledger moves to pages under
   `review/decisions/`, the vault governs it and the single file becomes the index page.

What it could express is the shape of the ledger's preamble: dated, decided by one of three,
appended to, cited into a census, kept when its file is deleted, and a refusal that names the kind,
the clause, the failing value and a passing one. Items 1, 3 and 5 are the ones a research project
on laws should take as its next questions; 4 waits on the census; 7 is a design decision for Ember.

## What landed, third round (2026-11-04): the write as a measure, and laws over links

Commits `ffb8772` and the one after it, built and run on bb2 in `~/lane-frame` as before. Gap items
3 and 6 of the second round were the brief; 7 (a kind's own laws unprotected) and "may a law ask the
patch" are Ember's questions in `review/DECISIONS-20261031.md` and nothing here presumes an answer.

### Gap 3 — append-only is now a prefix law (`ffb8772`)

`deletions` and `insertions` are measures of the write: the atoms of the old version's settled text
the write tombstones, and the atoms of the new settled text the old lacked (`Vault/Page.lean`).
They are read through `Doc.apply`: `Patch.deletes`/`adds`, `isDead_apply_forward` and
`present_apply_forward` (an authored patch tombstones exactly what it deletes and makes present
exactly what it adds; a tooth that forgets the deletions bites), then `deletions_apply`,
`deletions_apply_eq_zero` (`new.deletions == 0` iff the patch deletes no atom of the settled text)
and `insertions_apply`. `commit` adds them to the new state only. The decisions kind now says
`law appendOnly: new.deletions == 0`, and the recorded walkthrough shows what the count could not:
one character of a commit hash rewritten in place, bytes, lines and words unchanged, refused with
`deletions = 1`. What "line" means here is `widenStretch`'s: an author's change is widened to whole
lines, so the law reads "no line removed or rewritten, lines only inserted"; a member's post deletes
nothing and a selection tombstones only candidates. Not exposed: an "edited-span count". A span is a
property of the alignment, not of the patch (two alignments of one edit differ in it; `Same` graphs
must measure alike), so it would not be tied to `apply`; the atom counts are. Interaction to know:
`fixDangling` replaces a text atom with a cite when its page appears (one deletion), so a page under
`deletions == 0` whose link dangled will not have that link resolved until the law's owner says so;
with `dangling == 0` on the same kind, as in the ledger, the case does not arise.

Two defects found by the walkthrough and fixed in the same commit: a refused edit put back kept the
page "refused" (now `ownerWrite`'s same-text branch clears the note), and a second refused edit with
the same message was not reported (`changes` compares the typed text, marks stripped).

### Gap 6 — cross-page facts: laws over links (next commit)

**What `Run/HyperLaw.lean` turned out to be.** READ (`lean/Obend/Run/HyperLaw.lean:1-363`, untracked,
imported by the dirty `Run.lean` only): two things, neither about pages. Part I is a `k=2`
non-interference checker over a list of paired world states with a `LowView` projection (Clarkson–
Schneider hyperproperties, with soundness and completeness on finite traces and a tooth); Part II is
a Gelfond–Lifschitz stable-model judge for modal programs registered as a `Judge.Format`. Both are
studies over an abstract `World`; nothing in them names a page, a footprint or a vault store. Not
used, not replaced: it should stay a study under `Run/` and say so.

**What `Vault/Hyperedge.lean` offered.** READ (`Hyperedge.lean:89-240,465`): a `VaultStore` is
`String → Option Data`; a `VaultTurn` has read pins (cell, observed state), write cells (pre, post),
an occasion, and proofs that its legs agree and balance; `applyTurn` writes the post states;
`no_toctou` says a turn whose pins hold at the authoring store and at the admission store is valid at
one iff at the other and writes the same cells. It is not connected to the markdown store (pages,
graphs, laws); the connection is what this round adds.

**The design, smallest honest version.** A law line that reads `linked.F` instead of `new.F` is a
law over the page's links: its subject is every page the page links to by identity cite (what the
`links` measure counts), and it is judged at each of them, on that page's state, on two occasions:
a write of the page (at its links as they stand) and a write of a linked page (at that page as
written, under the laws over links of every page that links to it). What it can read: the linked
page's measures and fields, and the request; not the page's own fields (`new.` in it is refused at
parse; a joined state is the next step). Inheritance: it is a law line, so a kind's `linked.` law
binds every page under the kind, over that page's links. Refusal: from the page's side, `refused by
its law listedDated over its links, at notes/Scratch: ... does not hold there; the line date: 1 would
pass (the page has date: 0)`; from the linked page's side, `refused by Ledger: listedDated (a law
over Ledger's links, of which notes/Scratch is one): ...`. The footprint is explicit: `writeTurn`
builds the write as a `VaultTurn` (its one write cell the page, pre and post state; a read pin per
page its laws over links read, at the state read) and the laws are judged on the store the turn
describes, `applyTurn turn.readPins.store turn`. `judgeLinksIn_of_turn` (via `Footprint.store_of_holds`
and `applyTurn_pin`) proves that equals the judgment on any store where the pins hold, which is the
premise `no_toctou` asks of a turn judged at one store and admitted at another. Hyperedge.lean is
imported, not edited; nothing is routed to the security lane. HEAD's Hyperedge lacks the dirty
copy's `ofWitnessLegs`, so `writeTurn` constructs the turn directly (one cert-less leg, empty id).

What the vault does not yet do with the turn: defer it. Every commit judges and applies in one
step, so the pins are checked against the store that produced them; `no_toctou`'s conclusion becomes
load-bearing when `merge` replays a replica's commits as turns, which is the natural next use. One
consequence is visible already: within one `obend open`, pages are committed in order against the
entries read at the start (a page being written is pinned at the version it is about to become), so
an index page judged against a draft decision whose own commit is then refused was judged against a
pin that did not hold. The retry of refused writes at every non-quiet open (`openPage`) is the
repair in practice; a turn admitted only when its pins hold would be the repair in principle.

**The decisions vault, section 6.** `Ledger.md` gains `law listedDated: not (linked.date == 0)`
(adopted, judged at D-0001..4); an undated note outside the kind, listed, refuses the ledger's write
at the note; dating the note mends the ledger at the next open (the retry); the note then cannot
lose its date while listed. Recorded on bb2 and read: 14 steps.

### The gap list, updated

1. Unit of law is the page, the ledger's is the row — open (a `rows` measure or laws over list
   items).
2. No strings — open.
3. Append-only is a count — **closed** by `deletions`. Remaining: a law still cannot say *which*
   lines may change (a "status" line that may flip while the body is append-only); that is a measure
   per section or per field, not per page.
4. Theorem names are a hand-kept census page — open until the gate lane's census writes it.
5. Authority is not provenance (`request.caller` is the selector, not the poster) — open.
6. No cross-page facts — **closed for one shape**: a law over the page's links, reading the linked
   page. Still not sayable: a comparison between the page and a linked page (`linked.date <=
   new.date`: needs a joined state), a law over the pages that link *to* a page (backlinks as
   subject), a law over a page's embeds or quotes rather than its identity links, and a relation
   between two linked pages (ordering of decisions by date).
7. A kind's own laws are unprotected — Ember's question, untouched.
8. The real `review/` file can only be the index page — open (follows from 1).

## What landed, fourth round (2026-11-04): labels, the poster, merges through pins

Gaps 2 and 5 of the second-round list, and the TOCTOU note of the third. Commits `47e6adc`
(fragment) and `bd160a6` (vault), built on bb2 module by module (never the umbrella: `Obend.Apps.*`
is an hour per build until the gate lane's change lands).

### Gap 2 — no strings in laws (`47e6adc`)

The fragment reads labels. A label constant `"ember"` is a reference (`LawRef.labelConst`), and
`==` between two references compares labels when both read as labels (`LawRef.readLabel`: a field
holding `Data.label`, or a constant) and naturals when both read as naturals, false otherwise; `REF
in ["a", "b"]` is an `or` of equalities; `writeOnce(F)` on a label field holds at a first write,
when the old label is unset, or when the new equals the old. `<=` stays numeric. Compiled by Core4's
`labelEqual` (`labelRead`, `labelField`); `fitsField` now says what a label field holds. The proof
chain carries (`cond_eval`'s `eqR`/`writeOnce` cases, `chk_cond`), `compile_checks`, `judge_admits`,
`judge_refuses` unchanged in statement. **`dial_free_confluent` stays true**: a label constant is
fact-only; a comparison with a label field is `.ordering` like every equality on a field
(`joinData` keeps the left state's label, so two admitted writes of different labels join to one of
them); no label clause is `.free`, and `dial`'s doc says so. The vault types a frontmatter word as
a label (`labelFields`, `stateTyWith`/`stateOfWith`) and suggests a label that would pass. The
decisions kind now says `new.decider in ["ember", "integrator", "lane"]`; D-0006 with `decider:
committee` is refused with `the line decider: ember would pass (the page has decider: committee)`,
and the re-decided D-0001 by `writeOnce(decider)` with `decider: ember` as the line that would pass.
A date is still a number: a calendar check is beyond the fragment (no `/`, no `%`); `20261199` is
dated. Blast radius outside my files: one line in `Elab/Workbook.lean` (`ToExpr LawRef`).

### Gap 5 — authority is not provenance (`bd160a6`)

The vault binds the POSTER at every write: the owner, the member who posted, or at a selection the
author of the candidate kept. It is the label `new.poster` (a measure; a frontmatter line of that
name cannot override it) and the request's `principal` (`requestBy who poster`; the kernel request
already had the field, so no change to `reqTy`). A refusal of a law reading it ends `; posted by
NAME`. The kind's `law claimed: (new.decider == "ember") implies (new.poster == "owner")`: a lane's
post to a decision of Ember's is refused at the post (`…does not hold; the line decider: lane would
pass (the page has decider: ember); posted by lane`); its post to a decision in its own name is
admitted and the selection carries the lane as poster. Found on the way: a member's post that
rewrites a frontmatter line is refused earlier as a relaw attempt (owner's), so the only way a lane's
text claims Ember is on a row the owner opened as Ember's, and that is what the law catches. Not
done: `request.poster` as a LawRef reading the request rather than the bound field (one more
hypothesis through the whole proof chain, `pr = facts.poster`; the bound field is the same value).

### The TOCTOU note — merges through pins (`bd160a6`)

`replicaPins`: the replica's write of a page with laws over links read the pages it links to at the
replica's states; `mergeFrom` admits the merged write only where those pins hold in the receiving
store (`admitFootprint` from Hyperedge, `no_toctou`'s premise), so by `judgeLinksIn_of_turn` the
laws over links say here what they said there. Where a linked page moved underneath, the merge
refuses by name with what moved and the change is made here (vault walkthrough §8: `Index: not
merged: its write at laptop2 read Gamma as it was there (bytes 143 → 193, lines 5 → 6, version 7 →
8, …); make the change here, against Gamma as it is`). A page without laws over links read nothing
and carries no pins. Hyperedge.lean is used, not changed; nothing to route. Open: within one
`obend open`, pins are still read at the start and refused writes retried (the practical repair);
the merge path is the first place the turn is admitted only when its pins hold.

Recorded on bb2: decisions 16, vault 36, ledger 24; tests/run-workspace.py WORKSPACES: 44/44 checks hold;tests/run-logic.py 20/20 checks hold;tests/run-leaf.py 14/14 checks hold;tests/run-receipts.py 31/31 receipt checks hold;tests/run-obend-source.py OBEND SOURCE COHORTS: probes 30/30, tutorial 71/71, preview cohort 161 items with 0 failures

### The gap list, updated

1. Unit of law is the page, the ledger's is the row — open.
2. No strings — **closed** for labels (one word): `==`, `in [...]`, `writeOnce`. Open: no order on
   labels, no string content (prefix, length), no calendar on dates.
3. Append-only is a count — closed (`deletions`); per-section measures open.
4. Theorem names are a hand-kept census page — open until the gate lane's census writes it.
5. Authority is not provenance — **closed**: `new.poster` and the request's principal; the owner's
   rows cannot carry a member's text claiming Ember. Open: the poster's *grant* is not a fact (a
   law cannot say "posted by someone with select"), and `request.poster` as a request fact.
6. No cross-page facts — closed for laws over links; joined states, backlinks as subject, relations
   between two linked pages open.
7. A kind's own laws are unprotected — Ember's question, untouched.
8. The real `review/` file can only be the index page — open (follows from 1).
9. (new) A merge replays a replica's write with its pins; an `obend open` does not yet admit a
   turn only when its pins hold.

## What landed, fifth round (2026-11-04): one admission path, and a law per row

Third generation of the lane (`cv distill` twice). Commits `9de897f` and `b8fa08b`, built on bb2
module by module (`Obend.Vault.Store`, `Obend.Analysis.{Worlds,Replay}`, `obend`); every runner as
before: vault 36, ledger 24, decisions 19 (three new steps), workspace 44, logic 20, leaf 14,
receipts 31, obend-source 30/71/161. No recorded line of the vault or ledger walkthrough changed.

### Gap 9 — one admission path (`9de897f`)

`obend open` judged every write of an open against entries read before any of them, the drafts of
all changed files among them (so a write could be admitted against the draft of a page whose own
write was then refused, and a kind page's draft laws bound pages before the kind was born), and
retried every refused write at every open that was not quiet. Now (`Vault/Store.lean`, "Admission")
the writes are turns, `admitWrites`: each is judged against the store at the moment of its
judgment, so the pins its judgment reads (`writeTurn`) hold at its admission; an admitted write
enters the store; a refused one is kept with the pins its judgment read (`pinsOf`: its kinds,
present or not yet; the pages its dangling links name; and where laws over links are judged, the
pages it links to and the pages that link to it under one), stays refused while they hold, and is
judged again exactly when a pin moves (an admission writes a page it read). The question "do the
pins hold here" is asked of `admitFootprint`, the door the merge admits a replica's write through
(`replicaPins`, third round): one rule for a write authored elsewhere and a write refused earlier.
The retry loop and the rule "a refused write is tried again at every non-quiet open" are gone
(`openPage` and the drafts-for-judgment `openEntries` use with it; `openEntries` remains for cite
resolution only).

What is proved. `admitWrites_ind`, an induction principle for the loop written by hand (nested
induction on the lexicographic measure, unfolding by the equation lemma): the generated
`fun_induction` principle depends on `admitWrites._unary.induct_unfolding`, which `#tooth` cannot
see across a module boundary, and its case binders come out `attach`ed. `admitWrites_admitted` and
**`open_admitted`**: every write an open refused was judged at pins the door admits at the store
the open leaves, so the files say what the store would say again. `open_idem` is now stated
through `openAdmission_{names,nodup,seen,cover}` and `quiet_after_settle`; honestly, its proof is
still the quietness argument (the second open reads every file as the first left it), and what turn
determinism bought is `open_admitted` and the deletion of the retry, not a new proof of `open_idem`.
The two teeth on `open_idem` (`writesFor`, `quiet` mutations) bite.

Two things the loop surfaced, both fixed before recording. A page born in the same open as its
`_kind` was judged before the kind existed: `journal/Tuesday` was admitted without `brief`, and
`decisions/D-000x` were refused as unknown-kind and, their kind chain empty, not pinned to the
absent kind. A kind now precedes its instances in the order (`pendingAt`: kind pages first, the
enclosing folder's before its folders'), and a write's pins name the kind it would be under whether
or not that page exists (`readsOf`: `kindLine`, `kindsOf`), so a kind born later is a pin that
moved. Order otherwise is page order and only matters where two writes in one open read each other
through laws over links; the backlink judgment at the second write catches what the first did not
see, as the decisions walkthrough's section 6 still shows.

Open, and said in the code: cite resolution still reads the files as they are about to become
(`openEntries`), so a cite of a block another changed file introduces is pinned at a version that
may be refused (it reads `behind` until `recite`); `fixDangling` in `settle` judges its re-cites
against the pre-settle store. Both are the pattern this round removed from the laws, left in the
cites, and named here rather than widened into this change.

### Gap 1 — the unit of a law is the page, not the row (`b8fa08b`)

The rows the Doc model already distinguishes are heading lines (`blockLine` resolves `[[P#H]]`),
and an atom is a line (`Obend.Doc.lex`), so a `## ` row is an atom range with ids stable across
versions: no new parser. `law NAME per ##: EXPR` (`lawKey`, `lawSubject`) is judged at every row the
marker begins (`rowsOf`: the heading line and the lines to the next heading of its level or above),
on the row's own measures (`rowMeasures`: bytes, lines, words, links, embeds, quotes, dangling) and
its write's (`deletions`, `insertions` within the row), against the row of the same title in the
old version (a new row is a birth; a vanished row is a write of it to nothing); laws over rows
inherit along kinds like any law line, and the refusal names the row. Decisions walkthrough
section 8: `log/_kind` with `appendOnly per ##` and `cited per ##`; one row rewritten in place and
a row appended in one write is refused `at ## D-0002: new.deletions == 0 does not hold there;
deletions = 0 would pass (this write has deletions = 2)` (the line and the blank line closing it:
`widen` re-writes a changed stretch up to the line end that closes it; the page's count is the
same two); the row put back, the appended row is admitted (v2); a row naming a theorem the census
lacks is refused `at ## D-0005` by `cited per ##`.

**Stopped at fields, as asked.** `dated` and `deciderOnce` read fields; a row has none. The reader
knows frontmatter `key: value` lines (the page's), wikilinks, block ids and heading lines, and the
real ledger (`review/DECISIONS-20261031.md`) keeps its rows in markdown tables whose columns are the
fields (`| decision | choice | where |`), which the reader does not read at all. To say `dated` per
row the vault needs one of three syntaxes, each a decision about what a row is, for Ember:
(a) Obsidian's inline fields, `date:: 20261104` on a line of the row — Dataview's, in wide use, `::`
does not collide with prose colons, and the frontmatter reader applies as is; (b) a table whose
header row names the columns and each row's cells are its fields — markdown's own syntax, the form
the real ledger already has, and a new reader (split on `|`); (c) Pandoc heading attributes,
`## D-0004 {date=20261104 decider=lane}`. My own order would be (b) then (a): (b) reads the ledger
as it is written today without touching a row, (a) is what an Obsidian user would type by habit.
Nothing of this is taken.

### The gap list, updated

1. Unit of law is the page — **closed for measures**: a law per `## ` row, named in the refusal.
   Open: fields per row (the three syntaxes above; Ember's call), rows of a table, rows inside a
   section with candidates (judged when one is kept).
2. No strings — closed for labels (fourth round); no order or content on labels, no calendar.
3. Append-only is a count — closed (`deletions`), now also per row.
4. Theorem names are a hand-kept census page — open until the gate lane's census writes it.
5. Authority is not provenance — closed (`poster`); the poster's grant as a fact, open.
6. No cross-page facts — closed for laws over links; joined states, backlinks as subject open.
7. A kind's own laws are unprotected — Ember's question, untouched.
8. The real `review/` file can only be the index page — open; follows from 1 (fields, tables).
9. One admission path — **closed**: open and merge admit a write through `admitFootprint`; no retry.
   Open and named: cite resolution against drafts (`openEntries`), `fixDangling`'s judgment in
   `settle`, and `open_idem`'s proof still being the quietness argument rather than determinism.
