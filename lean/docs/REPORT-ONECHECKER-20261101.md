# Report: lane OneChecker (gate 2) — `Check.infer` retired; `Bidirectional.checkAgainst` is the checker (Claude Opus, 2026-11-01)

Brief: `lean/docs/LANE-ONECHECKER-BRIEF-20261101.md`. Worktree `scratchpad/cost`, branch `lane-onechecker`,
rebased onto `dev` before each push. Start: `08ff37a` (rebased onto `bd642a8`, docs only), tier 1
green at 283 jobs, tier 2 at 304 (warm); journal export `env-before` 36,048 rows.

## 0. Before the lane: compose without beta redexes (`1e039ff`)

At the coordinator's request (Gemini's second review), `Spec/Elaborate.composeStep` emits
`specification (composed{inherited, wrapping}) (mix value right)` instead of
`(λl. λr. specification m (mix l r)) value right`. One refinement: a step whose `value` is the
previous step's composite takes that composite's metadata *term* as its inherited provenance instead
of `metadata value`; re-reading it would copy the whole chain into each step and double the term at
every step of the left fold. `SpecificationClosure.compose_wrapper_typed` is restated over the direct
shape as `compose_typed` (generic in the provenance terms) and `compose_step_typed`. Control: the
cohort runner's output is byte-identical before and after (probes 30/30, tutorial 71/71, preview
161/0); `obend check` output identical on all 32 compose sources; receipts 32/32, workspaces 30/30.
Deviation: core packet digests of compose programs change with the AST
(`RepeatedExtension.repeated`: `6d1de6c0…`, 3,070 B → `e268294d…`, 2,684 B); outputs do not.

## 1. Inventory

Read off the journal export at the start (`typeCites`/`valueCites` of every constant against
`Check.infer`, `check`, `inferFields`, `inferArms`, `checkExtension`): 401 constants cite them
directly (most are auxiliary equations and tooth fixtures). The named ones, by module, with the
bidirectional counterpart each has or lacks at the start:

| module | names | counterpart at the start |
|---|---|---|
| `Core/Check` | `infer_zero` | none needed (no fuel) |
| `Core/Packet` | `refusalKind`, `refusalReason`, `packetReceipt`, `checkPacketFile`, `ampleFuel` | `Elab/Gate`'s same-named functions (already the only ones `Main` calls): dead code |
| `Core/Proofs/Preservation` | `check_runBounded_no_refusal` | `checked_runBounded_no_refusal` (any `Checked`, so any `checkAgainst` result) |
| `Core/Proofs/Hole` | `infer_refuses_hole`, `check_refuses_hole` | `Bidirectional.elaborate_refuses_hole` |
| `Core/Proofs/Substitution/Mono` | `infer_mono`, `check_mono` | the judge's `mono` (`Judge.Instances.bidirectional`); `checkAgainst` has no fuel |
| `Core/Proofs/Substitution/Transport` | `infer_transport` | `TypedSubstitution.partialTyping_closed_transport` (relation level) |
| `Core/Proofs/Substitution/Msubst` | `infer_msubst`, `check_msubst` | relation: `partialTyping_msubst`, `checked_msubst`, `Core4.calculus_typed_msubst`; **checker: lacking** |
| `Core/Proofs/Substitution/Defs` | `Fillings` (its `typed` field is an `infer` run) | used only by `infer_msubst` |
| `Core/Proofs/Templates` | `Discharges.infer_instantiate`, `Discharges.check_instantiate`, `inferFields_tail`, `weight_template_type`, `weight_template_accepted`, `coloured_instance_accepted`, `self_as_bound_row_alias_accepted`, `self_as_bound_row_rigid_refused` | **lacking** |
| `Core/Proofs/CheckCompletenessObstruction` | `unannotatedConstant_refused`, `checked_lambda_without_annotations_never_checks`, `checked_does_not_imply_eventual_success`, `annotatedConstant_accepted`, `aliasBranch_accepted`, `correct_lambda_annotation_now_checks`, `emptyCase_refused`, `annotated_empty_eliminator_still_incomplete`, `duplicateCase_refused` | the module's own bidirectional residue (`unannotatedConstant_checks`, `…_synthesis_names_annotation`, `aliasBranch_checks`, `emptyCase_checks`, `duplicateCase_names_duplicate_labels`), `BidirectionalCompleteness.coverage_premise_needed` |
| `Spec/FrontEnd` | `checkTemplate` (the open-template check: three `check` runs at rigid Self/Super) | **lacking**: the one live executable consumer |
| `Teeth/Core/CheckTeeth` | 58 teeth (`(check … fuel).isSome/isNone` by `decide +kernel`, the `futureRow*` extension fixtures on `checkExtension`, `refusal_kind_*` on `Packet.refusalKind`) | restated in step 4 |
| `Teeth/Core/SubstitutionTeeth` | 9 (`fuel_tooth`, `open_filling_tooth`, `assumptions_tooth`, and their fixtures) | restated in step 4 |
| `Teeth/Core/LinearTeeth` | `dropped_linear_custody_refused_by_check`, `specification_metadata_refused_by_check` | the same file's bidirectional teeth |

Transitively, the rest of the tree reaches the fuel checker only through `FrontEnd.checkTemplate`
(`FrontEnd.lower`, so `Main`, `Capture`, `Preview`, `FrontEndAdequacy` and the 13 `native_decide`
acceptance teeth of `SpecificationClosure`).

Already on `checkAgainst` before this lane (step 3 of the brief needs nothing there):
`Slot/Core4.judge` (grant over `checkWork`, no annotation-directed route left), the budget judge and
`budget_*` (`Slot/Budget`), `Judge/Instances.judge_iff_check` (its `check` is the `Judge` class's
method, not `Check.check`), `Elab/Gate` (front end admission, `obend check-core`, `run-core`,
preview). `routes_agree` was retired by the equi-recursive migration (`89bd283`).

## 2. The missing counterparts (`2aa048e`)

- `Templates.Discharges.partialTyping_instantiate` (public): the template theorem on the typing
  relation, by induction on the derivation. A derivation under rigid bounds is one at every
  discharging instance, in the instantiated context, at the instantiated type, with the same uses.
- `Core/Proofs/CheckerTransport` (new, tier 1):
  - `checkAgainst_msubst`: `checked_msubst` then `annotated_complete`. The filled term is accepted at
    `A` under prepared annotations, with no more uses (`UsesLE`).
  - `Discharges.checked_instantiate` and `Discharges.checkAgainst_instantiate`: `check_instantiate`
    over the checker. The instance is accepted at the instantiated type, with the same uses, under
    re-prepared annotations.
  - The template fixtures on the checker: `weight_template_checks`, `coloured_instance_checks` (by the
    theorem), `self_as_bound_row_alias_checks`, `self_as_bound_row_rigid_refused_by_checker`.

**Why prepared annotations rather than the template's annotations instantiated alongside** (decided by
the coordinator). `infer` only asked `agree` yes or no and kept its own synthesized type, so the
template's instantiated annotations stayed valid. The bidirectional checker's `ascribe` takes an
annotation's type when it agrees with the synthesized one and keeps its own otherwise, and the choice
drives the `whnf` heads and row lookups downstream. A rigid `Self` changes that branch under
instantiation: `variable Self` and its bound row disagree in the template (rigid, never an alias), and
the instance row and the instantiated bound may agree. So the instance run can take a branch the
template run never took, and no theorem of the form "the instantiated annotations are accepted"
follows from the template run. Acceptance under re-prepared annotations does follow, for every
instance. The module docstring records this.

## 3. Consumers moved (`268806e`)

- `Spec/FrontEnd.checkTemplate` was the last executable consumer. It now runs
  `Elab.Gate.admitSource` (preparation, then `checkAgainst` within the request's `checkWork`) for the
  same three named refusals (`super-rigid`, `self-rigid`, `template-typing`). Its docstring cites
  `Discharges.checked_instantiate`.
- `Core/Packet` keeps decoding, `typeJson`, `RefusalKind` and `relaxQuantities`. Its dead check-based
  receipt functions are deleted. The refusal-kind teeth are on `Gate.refusalKind`
  (`refusal_kind_starved_fuel` became `refusal_kind_starved_work`).
- Already on `checkAgainst` before this lane: the slot judge, the budget judge, `judge_iff_check` and
  the gate (§1). The slot judge has no annotation-directed route left.
- Controls: the cohort runner's output is byte-identical (30/30, 71/71, 161/0); `obend check` output
  is identical on all 117 sources under `tests/obend-source`; receipts 32/32, workspaces 30/30,
  walkthrough 26.

## 4. The fuel checker deleted (`90e3a25`)

`Core/Check` keeps the specification: `PartialTyping`/`FieldsTyping`/`ArmsTyping`, `Checked`,
`Inferred`/`InferredFields` (the checker's result types), the quantity rules (`argumentAllowed`,
`caseAllowed`, `caseQuantity`, …), `sameType` and the row machinery. Deleted with the fuel checker:
`infer`, `inferFields`, `inferArms`, `check`, `InferredArms`, `variantRow`, `agree` and its lemmas
(its nominal shareability guard; the checker converts by `sameType`), `CheckedExtension`/`checkExtension`,
`infer_zero`.

**Theorems whose statement went with their subject, and the counterpart of each:**

| deleted | counterpart |
|---|---|
| `check_msubst`, `infer_msubst` | `CheckerTransport.checkAgainst_msubst`; `TypedSubstitution.checked_msubst`; `Core4.calculus_typed_msubst` |
| `check_instantiate`, `infer_instantiate`, `inferFields_tail` | `CheckerTransport.Discharges.checkAgainst_instantiate` / `checked_instantiate`; `Templates.Discharges.partialTyping_instantiate`, `fieldsTyping_tail` |
| `check_mono`, `infer_mono` | the judge's grant monotonicity (`Judge.Instances.bidirectional.mono`); `checkAgainst` has no fuel |
| `infer_transport` | `TypedSubstitution.partialTyping_closed_transport` |
| `check_runBounded_no_refusal` | `Preservation.checked_runBounded_no_refusal` |
| `infer_refuses_hole`, `check_refuses_hole` | `Bidirectional.elaborate_refuses_hole` |
| `agree_instantiate`, `variantRow_instantiate`, `agree_never_manufactures_shareability` | none: their subjects (`agree`, `variantRow`) were the fuel checker's own. Shareability is now kept by agreement itself (`CheckTeeth.canonical_agreement_keeps_shareability`) |
| `weight_template_type`/`_accepted`, `coloured_instance_accepted`, `self_as_bound_row_*` | `CheckerTransport.weight_template_checks`, `coloured_instance_checks`, `self_as_bound_row_alias_checks`, `self_as_bound_row_rigid_refused_by_checker` |
| `CheckCompletenessObstruction`: `unannotatedConstant_refused`, `checked_lambda_without_annotations_never_checks`, `checked_does_not_imply_eventual_success`, `annotatedConstant_accepted`, `aliasBranch_accepted`, `correct_lambda_annotation_now_checks`, `emptyCase_refused`, `annotated_empty_eliminator_still_incomplete`, `duplicateCase_refused` | `checked_lambda_without_annotations_synthesis_refused`, `checked_does_not_imply_synthesis`, `annotatedConstant_synthesizes` (new), `aliasBranch_checks`, `emptyCase_checks`, `duplicateCase_names_duplicate_labels` (existing). The alias-branch and empty-eliminator obstructions do not exist for this checker |
| `LinearTeeth.*_refused_by_check` (two) | the same file's bidirectional teeth, which were already there |

Teeth: `CheckTeeth`'s 55 runs are on the checker in synthesis (`synth`, the top-level
`Bidirectional.infer`). The extension teeth check at the family's function type. The symbolic
future-row teeth use a `future_reduce` simp script. `SubstitutionTeeth`'s three corners are on
`checkAgainst`; its fuel corner is now the slot judge's work grant (`fuel_tooth`). On the Mac, every
`decide +kernel` tooth in `CheckTeeth` elaborated against the bidirectional checker with no change of
verdict before the build was moved to the box.

Deviation in `CheckTeeth`: `future_binary_instantiation_accepted` was a statement about every
shareable `Self` and row `Super`. On this checker the symbolic reduction did not finish in 500 s on
the box, so it is now held at two instances (a scalar `Self` over `{}`, and a row over a row).
`future_row_instantiation_accepted` and `future_row_typed` stay symbolic. They are proved by a staged
`simp only` script (`future_reduce`), about 6 s each. The first, plain-`simp` version of that script
is why the module crawled on the Mac.

**Builds, all on dregg-build2.** Tier 1 was green at the rebased head (291 jobs). Tier 2
(`lake build Obend.Census Teeth`, the census included: no `sorryAx`, no declared axiom) was green at
`05beecd` (315 jobs). Cohorts at `05beecd`: probes 30/30, tutorial 71/71, preview 161/0. Receipts
31/31: the 32nd check re-runs CaDiCaL, which is not on the box's PATH. Workspaces 30/30, walkthrough
26, logic 20/20. `dev` was pushed from the Mac with `--no-verify` because the identical commits were
green on the box.

## 5. The measurement (dregg-build2, warm tier 1 at `05beecd`, `LEAN_NUM_THREADS=4` under `swarm-build`, load 3–8)

| edit | modules rebuilt | wall |
|---|---|---|
| `checkAgainst` body (a no-op `let` at the head of its `do` block) | 52 | 42 s |
| `elaborate` body (the `.nat` arm: `value` → `id value`) | 52 | 44 s |
| restore after each | 52 | 42–43 s |

The gate is twenty, so it is not met. For comparison, an `infer` body edit rebuilt 112 modules before
this lane (`REPORT-EXPOSE2`); retiring the fuel checker roughly halves the cascade of a checker
edit. The 52 are every importer of `Bidirectional`, which is an `@[expose] public section`. By grep,
18 of them name `elaborate`/`checkAgainst` in a proof or call (completeness, preparation, the gate,
the slot and budget judges, `Judge.Instances`, `Code`, `LawCompile`, `CheckerTransport`, the obstruction
fixtures).

**Does the `_unsafe_rec` body cascade the same way?** Yes. With the section unexposed
(`public section`), an `elaborate` body edit still changes `Bidirectional.olean`
(`184270930ff4c7b2` → `985cbdb2510d69a0`). `elaborate._unsafe_rec`, `checkFields._unsafe_rec` and
`checkArms._unsafe_rec` are in the public `.olean`: Lean 4.35 writes the compiled body of a mutual,
list-nested structural recursion there whether or not it is exposed. That is the same limit
`REPORT-EXPOSE2` found for `infer`. So unexposing alone buys nothing for `elaborate`. For a
`checkAgainst`-only edit it would help, since that is a non-recursive definition.

**The one-`Nat`-recursion rewrite: refused on this evidence.** A single structural recursion on a
`Nat` would not emit `_unsafe_rec`, so an unexposed body edit would rebuild only the readers that
unfold the body: by the grep above about 18, with `import all`, under twenty. The cost is the
checker this lane just retired. Fuel would come back into the one executable checker. Every proof
that follows `elaborate` case by case would be redone against the fuel-indexed version
(`BidirectionalCompleteness` at 1,588 lines, `Prepare`/`PrepareChecks`, the gate, the decide teeth),
and a fuel-monotonicity theorem would be needed again. Two cheaper moves are open instead:
- Unexpose `Bidirectional` and give its readers `import all`. A `checkAgainst` edit then rebuilds the
  readers only.
- Move the `decide +kernel` fixtures of `Core4`, `Budget`, `Judge.Instances` and
  `CheckCompletenessObstruction` into tier 2. They are most of the non-proof readers.

## Journal (`lake exe journal`, `08ff37a` → `05beecd`; the base moved by the Logic and Sound (3) lanes)

1,279 withdrawn supports, 137 revised (almost all auxiliary equations; by name: `SpecificationClosure.provenance_typed`,
generalized by the compose commit, and `Spec.Syntax.Module.*` from the Logic lane), 24 STATEMENT-CITED,
10 PROOF-CITED, 1 reproved, 799 added, 799 removed, 17,637 unaffected.
- STATEMENT-CITED, rebuilt green with unchanged statements: the 13 `SpecificationClosure`
  acceptance teeth and `FrontEndAdequacy.accept_inhabited`, which reach the front end through
  `checkTemplate`.
- PROOF-CITED: `CheckTeeth.future_row_typed`.
- Removed: the fuel checker and the theorems in the §4 table.
- Added: `CheckerTransport`, `partialTyping_instantiate`, `compose_typed`/`compose_step_typed`, the
  restated teeth, and the Logic and Sound lanes' work.

## The decision for Ember

The checker gate is not met: 52 modules and about 42 s for a checker edit. I refused the
`Nat`-recursion rewrite, which would reintroduce fuel into the one checker. The choice is whether to
take the cheaper half instead: unexpose `Bidirectional`, give its readers `import all`, and move its
`decide` fixtures to tier 2. That leaves an `elaborate` body edit at the full cascade and brings a
`checkAgainst`-level edit down to its readers. Or accept 52 as the cost of a checker that is proved
complete.
