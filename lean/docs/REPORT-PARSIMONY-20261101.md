# Lane Parsimony: delete what nothing consumes, fold what duplicates (Claude Opus, 2026-11-01)

Brief: `lean/docs/LANE-PARSIMONY-BRIEF-20261101.md`. Worktree `scratchpad/kinds`, branch
`lane-parsimony` from `origin/dev` `5892944`; Lean v4.35.0. Commits `f1e1406` (1), `0b6f44f` (2),
`8fb62e2` (3), `b84029e` (5), then this report.

**Start**: `LEAN_NUM_THREADS=2 lake build`, 290 jobs, 186 rebuilt from a partly warm tree, 250 s, at
load 70 to 97. **End**: 283 jobs, green; tier 2 (`Obend.Census Teeth`) green with 304 jobs. The census
counts 35,127 package constants: 27 rest on compiler trust, none on `sorryAx` or a declared axiom.
Controls were run at the end and match the Kinds lane's counts: cohorts (probes 30/30, tutorial 71/71,
preview 161 with 0 failures), receipts 22/22, workspaces 30/30, the vault walkthrough 26/26, and
`tests/doc/RoundTrip.lean` (edited, below). Net change under `lean/Obend` and `lean/tools`: +177 and
−2,065 lines; eight modules fewer (282 jobs after the sixth commit).

## What changed, and what each removal had consuming it

| step | deleted | lines | its consumers | the gate |
|---|---|---:|---|---|
| (1) | `Obend/Just.lean` (48 theorems, 2 teeth) | 485 | the census only | refused by its own gate (REPORT-JUST §3) |
| (1) | `Obend/Slot/PolySlot.lean` (40 theorems, 11 teeth) | 471 | the census only | same; its originals in `Slot`, `World` and `Integrity` stay |
| (1) | `tools/just-control.lean` | 426 | nothing (a control file) | REPORT-JUST §3 keeps the table and names `5892944` for a rerun |
| (2) | `Obend/Slot/Calculus.lean` (classes `Calculus`, `Decides`) | 78 | one instance each, Core4's | 55 → 15 non-blank lines for the typing judge's laws and bridge |
| (2) | `Obend/Core/Graded.lean` | 45 | one instance, `Nat`; every `Judge` was at `Nat` | `Judge Obj Cert R [Graded R]` → `Judge Obj Cert` |
| (2) | `Obend/Tactic/Fuel.lean` (`fuel_lift`) | 17 | none (its last use went with `calculus_check_msubst`) | — |
| (2) | `Judge.Instances.ofDecides`, Core4's `Covered`, `lowerFrom`, `liftFrom` | 23 + 8 | `ofDecides` none; the other three only `Calculus` fields | — |
| (3) | `firstCandidate`, `blindRefusal` and their floors and teeth | 35 | none outside `Integrity` | below |
| (5) | `Obend/Digest/Class.lean` (class `Digest`) | 30 | one instance, cSHAKE256; three callers | three proofs drop the `cshake_hash` rewrite |
| (5) | `Obend/Core/Backend.lean` (class `Backend`) | 79 | one instance, no consumer at all | — |

New classes: none. Classes remaining in the tree: `World` (five instances), `Judge` (eight).

### (1) Just and PolySlot
I deleted them as the brief asked. `Slot/Repair.lean` stays, as the brief said, but the brief's
reason does not hold. Nothing imports it except `Obend.lean` and the census; nothing names
`repair_sound`, `Compatible` or `pinWorld` outside it. It was the record of the repair-needs-compatibility
countermodel (REPORT-JUST §1), the same standing `PolySlot` had. On the coordinator's word it is
deleted in a sixth commit (191 lines; 9 theorems, 1 tooth). The record (`repair_sound`'s statement,
`Compatible`, `compatible_of_local`, the clash and `apart`) is written into `REPORT-JUST`, not into
`Integrity`: `repair_of_contextual`'s REPAIR is withdrawal plus fillability, not a plan of steps, and
does not want the compatibility condition. `THESIS.md` and `METATHEORY.md` no longer list
`repair_sound` as proved in the tree.
`REPORT-JUST` §3 already held the gate table. I added a paragraph there that names the commit
holding all three files and `tools/proofsize.py`, so the measurement can be rerun.

### (2) Decides folded into Judge
*Statement changes.*
- `Judge (Obj Cert : Type)`: `check : Nat → Obj → Cert → Verdict`, and `mono` is over `Nat`.
  `Format` loses its `R` and `graded` fields, and `badGrade : Nat`.
- The typing judge is the `Judge` instance `Judge.Instances.bidirectional`, which already existed.
  `Decides`'s fields map onto its fields:
  - `check_sound` → `sound`
  - `check_mono` → `mono`
  - `check_complete` and `prepare_sound` → `complete` (with `reannotates_typed`)
  - `check_covered` → `Fragment _ := True`
- New theorem `judge_iff_check`: `Core4.judge r Ψ t A = true ↔ bidirectional.check r (Ψ, t, A)
  t.annotations = .ok`. The slot's Boolean judge and the class's checker are one thing.
- `extend_filling_decided` is restated through the bridge as a `Judge` statement, in
  `Judge.Instances`.
- `Core4` now owns `Typed` (formerly `Calculus.Typed`), `judge_sound` (formerly the instance's
  `check_sound`), `Budget` (no longer parameterized by `R`), `BudgetRefusal`, `slotOf`, `admit`,
  `slotOf_usable` and `resolve_checks`. These were `Obend.Slot.Calculus.*` and are now
  `Obend.Slot.Core4.*`.
- `slotFiller_typed` and `slotFiller_uncovered` move from `Integrity` to `Slot/Budget.lean`, stated
  at `AnnotatedTerm`. `Integrity` no longer imports a calculus.
- Theorems that keep their names but change statement:
  - `uses_var` is now `freeIn x (var x).term = true`.
  - `annotation_presence_not_coverage` loses its trivial `Covered … ` conjunct (it was `True`).
- `calculus_typed_msubst` keeps its name and its statement over `Typed`.

*Gate.*
- The typing judge's laws plus their bridge: 55 non-blank lines (the class 11, the Core4 instance
  21, `ofDecides` 23) became 15 (`judge_sound` 4, `judge_iff_check` 7, `extend_filling_decided` 4).
- The eight theorems whose statements moved (`slotOf_usable`, `resolve_checks`, `slotFiller_typed`,
  `slotFiller_uncovered`, `typed_iff_preparable_within_work`, `budget_filling_typed`,
  `annotation_presence_not_coverage`, `uses_var`): proof text went from 35 lines and 1,593 characters
  to 33 lines and 1,401 (`tools/proofsize.py`, measured once against the files at `f1e1406`).
- `Graded`: its one instance gave it no second reading. `Judge.mono` and the improvement judge
  (`Judge/Cost.lean`) are both at `Nat`, so the brief's condition for keeping it failed.

### (3) Integrity's floor
There was one point to make: contextual integrity is not vacuous. I kept `credulousHoles`, the
strongest floor. It is the filler closest to the slot's own: it honours the judge and the order and
ignores only supports, which are B4's subject. I deleted the other two:
- `firstCandidate` was refuted by the same conjunct at the same witness, on a strictly weaker filler.
  REPORT-20261031 D16 had already noticed this.
- `blindRefusal` was refuted on the why-not clause. That clause is already load-bearing in a positive
  theorem: `repair_of_contextual`'s second half reads the refusal's naming, so weakening the clause
  breaks the build.

The transition floors `churn` and `sticky` are unchanged; `Selection` consumes them.

### (4) Folds and resolutions that `Fold` and `Intention` could subsume
I looked across `Run`, `Law`, `Doc`, `Vault` and `Spec/Ecosystem` and made no change. Each case:

- **Already instances.**
  - Folds: `Run.legalAdmission`, `Law.lawAdmission`, `Run.Shared.ledgerAdmission` and the shared
    family (`Fold.Family`, `projectMoves`), plus the receipt (`Receipt.issue` over any `Admission`).
  - Resolutions: package parents (`Ecosystem.packages`), cites (`Doc.cites`), kind references
    (`Kind.kindRefs`).
- **Projection still borrows each runner's reachability** (Runner-2). It does so for one clause that
  is not per row, the runner's `Kept`. A fold step reads one row and the accumulator, and `Kept` is a
  property of the whole history, so `Admission` cannot state it without a history-valued `Rest`. That
  would lengthen every member, so I did not do it.
- **The vault's `resolveIn`** looks a wikilink up by name, through `findEntry`, before any cite
  exists. The cite intention resolves a `CiteRef` by page id afterwards. These are two steps, not
  two copies; Kinds was right that it stays.
- **Two readers of the inherited-law verdict.** `Vault.Law.readVerdict` and the end of
  `Spec.Workspace.judge` both decode `ok | refused {by, reason}` from `Law.run`, and both hard-code
  fuel 200000. Sharing them would mean moving `Vault.Law.Verdict` down to `Obend.Law`, where the name
  `Law.Verdict` (the machine's) is taken. That needs a rename to save about four lines, so I did not
  adopt it.
- **Two kind-inheritance resolutions.** One is the vault's folder chain (`kindChain`, `kindLaws`,
  `lawsFor`, with `kindLaws_mem` at 25 proof lines). The other is the kind cell's C4 precedence
  (`Kind.effectiveOf`, `kind_law_inherited`). They compute the same kind of thing over different
  carriers: vault laws are `LawExpr` compiled per page state type, while kind laws are `Term`s.
  Subsuming one into the other means the vault building a `Kinds` registry from its `_kind.md` pages
  and compiling before resolving. That is a semantic change, not a parsimony edit. It is the decision
  below.

### (5) Classes over one instance
I removed `Digest` and `Backend` (table above).
- `Digest`'s callers now name `Cshake256.cshake256Bytes`. A native kernel still attaches by
  `@[csimp]` on that function, as the class's own docstring said it would.
- `Backend` had no consumer. The paper's limitations paragraph (`paper/objective-bend.md` §10) no
  longer names it. When the leaf starts, it brings the second instance and the class back together.

I found no definition over a concrete type that a second consumer wants in the same shape, so no
class was introduced.

## Other edits
- `tests/doc/RoundTrip.lean` imported `Obend.Digest.Class`. It now uses `Cshake256` and passes.
- Docs updated:
  - `lean/README.md` (Core, Digest and Slot lines)
  - `lean/Obend/Judge.lean`
  - `METATHEORY.md` §1 (a dated note under the `Calculus`/`Decides` split) and §4 (`fuel_lift`)
  - `Core/Proofs/Substitution.lean`'s header

## Not done
- `Run/Control`'s presets and descriptor. The census said they had one consumer, but
  `Run.Shared`, `Run.Negotiation`, `Run.Proofs.Shared` and the example all import them. They are not
  a deletion candidate.
- (4)'s two non-adoptions above.
- No end-to-end rebuild timing comparable to the start: the end build was warm (283 jobs, nothing to
  rebuild).

## The one decision for Ember
**Should the vault's kinds be kind cells?** (Queued with the nominal-typing lane.) Today two resolutions compute "the laws a write is judged
by, its kind's first". One is the vault's folder chain over `LawExpr`, which is a chain, so its C4
list is itself. The other is `Kind.effectiveOf` over registered `KindCell`s with C4 over multiple
parents.

If the vault built a `Kinds` registry from its `_kind.md` pages:
- `kindChain`, `kindLaws`, `lawsFor` and `kindLaws_mem` (about 75 lines) would go.
- A page could name two kinds, which a folder chain cannot express.
- Staleness of a page's kind would be `kind_stale_iff_blocked`, for free.

The cost is that vault laws are compiled per page state type before inheritance, so the registry
would hold compiled `Term`s, recompiled when a page's fields change. I recommend yes, together with
the nominal-typing lane Kinds proposed, since both put kinds on records.
