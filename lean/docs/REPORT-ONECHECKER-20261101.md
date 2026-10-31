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
