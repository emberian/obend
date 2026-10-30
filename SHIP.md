# Shipping Objective Bend as one reusable library

Draft 1, 2026-10-29. How the thing gets built so that minidregg, nanodregg, delvetalk and a
stranger's notebook all depend on *one* `obend` package instead of each carrying a twin. The
rule is ATLAS's: nothing lands beside; everything replaces. A tree that adopts `obend` deletes
the modules it imported from it.

## 1. The shape: one Lake package, five libraries, one CLI

```
obend/                      Lean 4 (v4.30.0 now; the trees are at 4.30 and 4.34), no Mathlib
  Obend/Core/               Core4: Term, Step, Yields, Interaction; types and the checker;
                            the demand machine and its proofs; checkpoints; digest
  Obend/Spec/               the front end: parse, elaborate, templates, contract algebra, C4,
                            the specification closure, front-end adequacy, publication
  Obend/Law/                occasion-indexed laws (birth | write | relaw | invoke | adopt),
                            Verdict, the Pred fragment, the Std generators with meaning
                            theorems, `keeps` claims and their certifying-shape checker
  Obend/Slot/               the slot: candidates, supports, chooser, judge; open protocols;
                            `slot_repair`; an instance of its calculus laws at Core4
  Obend/Leaf/               the Bend book emitter (acyclic / dispatcher / represented machine),
                            the leaf interface, `leafProof` supports, the correspondence theorem
  Obend/Doc/                Page, Run, Patch (Add | Delete | Connect | SetField; compose, invert),
                            merge as pushout with conflicts as alternatives, cites, backlinks
  Obend/Main.lean           `obend`: check · run (landed 2026-10-31) · emit --bend · open <vault> · verdict
  tests/                    the ltuo probe cohort, the tutorial examples, the preview cohort,
                            the four programs of DESIGN §6 (CoAuthor, market, Tally, document)
```

Each library states its trust boundary at the top of its root module, in the trees' idiom:
what is proved, under which axioms, and what is trusted with no theorem.

## 2. Where each library comes from

| library | source today | extraction state (2026-10-31, `lean/docs/REPORT-20261030.md`, `lean/docs/REPORT-20261031.md`) |
|---|---|---|
| `Obend/Core` | minidregg `Theory/ObjectiveBend*.lean` (46 files, 25.8K lines) + `AxiomPin`, `AssertAxioms`, `AssertCompiled`, `HashBytes`, cSHAKE `Spec/Fast/Seam` | **landed** as `Obend.Core.*` / `Obend.Core.Proofs.*` / `Obend.Digest.*`, Lean v4.30.0 `module` files, no Mathlib, no Rust; every theorem statement and axiom pin kept (checked by name against the rename commit); seven evaluation teeth live in legacy leaves `Obend.Core.Teeth.*` because `Init` does not expose `Array.map`/`Array.zip`/`String.toUTF8` to module files. `Obend.Core.Backend` is the executor typeclass with the demand machine as its instance; `Obend.Digest.Class` the digest typeclass with the cSHAKE instance. 2026-10-31: `Obend.Core.Proofs.Substitution` proves the substitution lemma for `check` (`check_msubst`: closed fillings checking under the template's assumptions at their hypotheses' types keep a checked term checked at fuel `n + m`, with no more uses) and fuel monotonicity (`check_mono`); `Check.lean` is split into the checker, `Obend.Core.Packet` (the typed-core wire and receipt) and `Obend.Core.Proofs.CheckTeeth` (every `decide` tooth); `Obend.Main` is `lake exe obend check|run FILE.json`, exercised on minidregg's reference packets. |
| `Obend/Spec` | minidregg `Compiler/ObjectiveBend{Parse,Elaborate,C4,Contract,Templates,Law,TermWire,SpecificationClosure,FrontEndAdequacy,Publication,...}.lean` (24 files) + `Host/ObjectiveBend{FrontEnd,Preview}.lean` | not started; imports `Compiler.Sha256`, `Pred.Core` and Mini's codec modules; the parser and elaborator themselves import only `Lean`, `Std.Data.HashMap`, `Theory.*`. Extraction is a cut at the codec boundary. |
| `Obend/Law` | nanodregg `Lang/{Law,Claim,Std}.lean` + proofs; minidregg `Pred/Core.lean`, `Compiler/ObjectiveBendLaw.lean`, `Kernel/ObjectLaw*.lean` | not started; the port is to Core4 terms with the occasion sum as a Core4 `sum` type. |
| `Obend/Slot` | nanodregg `Lang/Contextual/{Protocol,Slot}.lean` + `Lang/Proofs/Contextual/{ProtocolTyping,Protocol,Negotiation}.lean` at origin/main 2dcc9ea | **landed** as `Obend.Slot`, `Obend.Slot.Protocol`, `Obend.Slot.Proofs.*`, statements unchanged (`slot_repair`, `resolve_ok`, the protocol families); `Obend.Slot.Calculus` is the calculus typeclass with `slotOf`/`resolve_checks`; `Obend.Slot.Core4` instantiates it at Core4 annotated terms on the closed-hole fragment (holes = free hypotheses, fillings closed), with its four equations proved and, since 2026-10-31, the law of the calculus discharged from `check_msubst` (`calculus_check_msubst` at `2 * checkFuel`; `calculus_check_msubst_within` at the judge's fuel within a budget; the fuel is the one conditional corner, REPORT-20261031 §7). `Obend.Slot.World` is the abstract history a slot's supports are judged against (pins per cell per view, retirement, audited steps; `receive_congr` and `stale_behind_forever` shapes as laws); `Obend.Slot.Integrity` states CONTEXTUAL INTEGRITY ∧ REPAIR of a filler over it, proves it for the slot's own filler over every World, and refutes the floor (`credulousHoles`, `firstCandidate`, `blindRefusal`) on a toy World where the repair happens. |
| `Obend/Leaf` | new; the emission rule in `DESIGN.md` §2 | not started; `Backend σ V` is the seam it instantiates. |
| `Obend/Doc` | breadstuffs `dregg-doc/src/lib.rs` + minidregg `Theory.Hyperdocument*` + nano LANG-83 | not started; the section-as-slot is `Obend.Slot` at `Run`. |

## 3. How the trees consume it

- **minidregg** `require obend` and deletes `Theory/ObjectiveBend*`, `Compiler/ObjectiveBend*`;
  its `Kernel/Objective*` (activities, calls, sends, seats, admission) stays, importing
  `Obend.Core`. Its `@[extern]` cSHAKE kernel is reattached by a one-line `@[csimp]` in Mini,
  the way `cshake256Bytes_eq_native` does today. Its `ObjectiveProofs` gate becomes `obend`'s
  own build.
- **nanodregg** `require obend` for `Obend.Slot` and `Obend.Law`, deletes
  `Lang/Contextual/*` and the Std law generators it ports, keeps its kernel, store, protocol,
  client. Its charter's scope (one writer, no proof system, no hiding) is untouched: `obend`
  is a language and a theory, not a kernel.
- **delvetalk** moves its `spec/bend` edition to `require obend` and keeps its object host,
  Spween and the town.
- **a stranger** installs `obend` and `bend`, runs `obend open ~/vault`, and has pages,
  sections, cites and laws over markdown, with Bend leaves callable from a page.

Toolchain: the package pins one Lean; the trees at 4.30 take it now; moving the package to
4.34 (BendTT's and delvetalk's) is a single bump the package owns, not a per-tree chore.

## 4. The order of construction

Each step is a coherent whole with its own tests and theorems; none is a stub for the next.

1. **`Obend/Core` as a package**, module names `Obend.Core.*`, the `ObjectiveProofs` statements
   and axiom pins carried over, the ltuo probe cohort and the preview cohort as tests, `obend
   check` and `obend run` as the CLI over the demand machine. This is the calculus paper's
   artefact and it exists today modulo renaming.
2. **`Obend/Spec`** cut from Mini at the codec boundary, with `package … extends …`, C4 identity
   `(intention, declaration)`, orthogonal `protocol … for …`, and the composition contract's
   theorems. The three-package test (`tests/objective-bend-source/three-package/`) grows into the
   report-extended-by-a-stranger of `ASTRA-SYNTHESIS` §G.
3. **`Obend/Slot` + `Obend/Law`** with the Core4 instance of the calculus laws, laws by occasion
   with `adopt`, laws with parents and the ancestor-naming refusal, `keeps` claims. The
   document section (LANG-83) is the first slot instance and the first page.
4. **`Obend/Doc`** and `obend open <vault>`: pages over markdown, sections as slots, cites as
   supports, patches and the pushout merge, the renderer. The stranger-usable kit is here: a
   report kind, a second author, an offline merge, an inherited-law refusal, no town required.
5. **`Obend/Leaf`**: the emitter with its three rules, the represented demand machine compiled
   by Bend, `leafProof` supports, the correspondence theorem, `obend emit --bend`. A Bend user's
   package becomes an ancestor of a kind here, and the second mature instantiation begins.
6. **Carry**: a Lean function with named drops between package versions of a page's state, so a
   vault is never re-genesised.

Steps 1 and 3 are extraction with new theorems at the joins; 2, 4 and 5 are new construction
over extracted parts; 6 is what makes the whole thing a garden rather than a demo.

## 5. What "high quality" means here, taken from the trees that earned it

- Every theorem ships with a tooth: a mutation or planted fault it refutes. A green that cannot
  red is not evidence. `P → P` and empty-premise statements are refused at review.
- One axiom census for the package, not a pin per theorem; `native_decide` only through
  `#assert_compiled`, which re-runs the claim.
- Refusals by name, with coordinates. A parse failure is never a verdict.
- The surface is checked by its own documentation: every code block in the guide is a file the
  gate compares byte for byte, and every command's output is re-run (Mini's tutorial gate).
- Delete the twin. When a tree adopts a library, the modules it replaced are removed in the
  same change, with the import boundary script saying so.
- No `partial def` on a deployed path; bounds on everything that crosses a boundary.
- The doc that explains a mechanism is written against the code at a named commit and says
  which words are *compiled*, *proved*, *executed*, *integrated*.
