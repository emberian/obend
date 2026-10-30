# REPORT 2026-10-30: the checker aligned with declarative typing

Lane Checker (Claude Opus), on `LANE-CHECKER-BRIEF-20261030.md`, following the five-step order of
`review/ARGON-RESPONSE-20261030.md`. Tags: **MEASURED** (a command run here, output read), **READ** (a
file opened), **INFERRED** (my reasoning). Nothing under `~/dev/minidregg`, `nanodregg` or `bend` was
touched. Every commit was built in full with `LEAN_NUM_THREADS=2 lake build`: green at 121 jobs through
step 2 and 123 from step 3 on. There is no `sorry` and no new axiom. Every proof module still ends
with its pins, and the pins I added are listed below.

## 1. What landed (commits on `dev`)

| commit | step | what |
|---|---|---|
| `281bdac` | 1 | `sameType` becomes the equivalence closure of the old one-step agreement (`sameStep`), decided by bounded orbits. `Equivalence (sameType …)` is proved. Canonical form keeps a non-shareable shadowed member. The relation refuses repeated case labels. The visited-set walks `lookupV` and `isRowV` are proved equal to the relation's `∃ fuel`. |
| `d4fb86f` | 2 | `infer`'s `ifBool` and `ifZero` joins, and every later case arm, convert through `agree`. `correct_lambda_annotation_still_incomplete` becomes `correct_lambda_annotation_now_checks` (its negation). |
| `ad2ddfd` | 3 | `Obend/Core/Bidirectional.lean`: one structural `elaborate` over `Mode = synth \| check E`, with no fuel. It returns `Except CheckRefusal` and carries the derivation. `checkAgainst` and `infer` are the top level. `Ty.canonical_canonical` (idempotence). |
| `7f73cc1` | 4 | `Core/Proofs/BidirectionalCompleteness.lean`: `synthCovered` and `checkCovered`, and `complete` by induction on `PartialTyping`. Then `checkAgainst_complete`, `checked_covered_accepted`, the boundary theorems and a `#tooth`. |
| `b979802` | 5 | The Core4 `Decides` instance judges with `judge grant`, which is fragment, depth within the grant, and `checkAgainst`. `Covered` is `checkCovered`, and `Recognized` is deleted. |
| (this commit) | | this report |

**Step by step, what is proved.**

1. **Fully proved.**
   - `sameType_equivalence`. `sameType_chain` and `sameType_lift` decompose any agreement into steps, and the machine lemmas about one step lift through them: `sameType_activity_canonical`, `same_type_lookup_transport`, `same_type_preserves_head`, `Discharges.sameType_instantiate`, all with unchanged statements.
   - `Ty.shareableUnder_canonical`.
   - `case_labels_distinct` and `duplicate_arms_have_no_derivation`.
   - `lookupV_iff` and `isRowV_iff`.
   - Teeth: `sibling_aliases_agree`, `agreement_does_not_descend`, `rigid_variable_nominal`, `cyclic_aliases_close`, `visited_walk_cycle`, `canonical_agreement_keeps_shareability`.
2. **Fully proved.** `aliasBranch_accepted` and `correct_lambda_annotation_now_checks`.
3. **Fully proved.**
   - Soundness holds by construction, and `checkAgainst_sound` states it.
   - All three former counterexamples check by `decide`: `unannotatedConstant_checks`, `aliasBranch_checks` and `emptyCase_checks`.
   - The duplicate-arm program is refused, naming `duplicateLabels`.
   - The bare lambda in synthesis is refused, naming `missingLambdaAnnotation []`.
4. **Partly proved.** The direct theorem is fully proved: `complete` covers all 25 rules, fields and arms. The `#tooth` and `coverage_premise_needed` show the boundary bites. **`annotateFromDerivation` and the full corollary are not done** (§5).
5. **Fully proved.** `check_complete` is `checked_covered_accepted`. `budget_tooth` and the Integrity teeth rebuild unchanged.

The front end's conformance cohorts were run after steps 1 and 2 (**MEASURED**): probes 30/30, tutorial 71/71,
preview 161 items with 0 failures, and the same one stale pin as before.

## 2. The journal's repair sets (MEASURED, `lake exe journal export` and `diff`)

| | revised | STATEMENT-CITED | PROOF-CITED | unaffected | added / removed |
|---|---|---|---|---|---|
| step 1 (`281bdac` against `e256cab`) | 12 | 505 | 1 | 7870 | 147 / 65 |
| step 2 (`d4fb86f` against step 1) | 8 | 165 | 2 | 8358 | 2 / 2 |

Step 1's 505 statement-cited theorems fall by module as follows:

| module | theorems |
|---|---|
| `Core.Proofs.Preservation` | 163 |
| `Core.Check` | 95 |
| `Core.Proofs.CheckTeeth` | 62 |
| `Core.MachineTyping` | 32 |
| `Core.Collect` | 31 |
| `Core.Proofs.Substitution` | 17 |
| `Spec.Proofs.SpecificationClosure` | 16 |
| `Spec.FrontEnd` | 13 |
| `Core.Proofs.Templates` | 13 |
| `Core.Proofs.CheckCompletenessObstruction` | 11 |
| `Core.Ty` | 11 |
| `Slot.Core4` | 10 |
| all others | 21 |

Step 2's set is mostly the checker's own teeth and their consumers: `CheckTeeth` 61, `Check` 31, `Substitution` 16, `FrontEnd` 13, `SpecificationClosure` 13.

The exact sets are in the appendix. Of the statement-cited theorems, the ones whose proofs actually had to change are few:

- four lemmas in `Preservation/Base.lean`, rewritten as a lemma about one step plus `sameType_lift`;
- two canonical-row proofs, which needed a `shareable` split;
- `Templates`' `insertCanonical_same` (now with a shareability premise) and `canonical_instantiate_insert`;
- the `case` binders in the substitution, weakening and instantiation inductions, which gained a `distinct` premise;
- the join cases of three checker inductions (step 2).

The rest rebuilt as they were. The journal reads dependencies, not breakage: "statement-cited" means look again, not that the proof failed.

## 3. Decisions, each with a critique and a meta-critique

**D1. `sameType` is the equivalence closure of the one-step agreement. It does not descend structurally.**

Two types agree when their head-unfolding orbits meet within `bounds.length` steps. `Assumptions.chase_bounded` is the pigeonhole that makes that bound exact. Every old derivation is still a derivation, because the relation's `conversion` already chained steps. The relation's meaning is therefore unchanged, and the machine proofs needed only the step-wise lift.

*Alternative:* Argon's hereditary structural unfolding, which would make `α → Bool` agree with `Nat → Bool`.

*Critique:* without congruence, synthesis of an introduction form is not principal. A field converted inside a record literal gives a row that agrees with nothing the checker can synthesize. That is why the fragment puts every introduction form in checking position and leaves `extend` out.

*Meta-critique:* congruence over recursive aliases has to be either the inductive congruence closure or the equi-recursive one, and either needs `HeadNormalizes` and its consumers to compare components up to agreement instead of canonical equality. That is a redesign of the machine invariants, so I did not slip it in under step 1. It is the decision in §6.

**D2. Canonical form forgets a shadowed member only if that member is `shareable`.**

The checker's `agree` existed because canonical equality dropped a shadowed custody or once closure. The relation's `conversion` therefore accepted laundering that the checker refused. That was a fourth disagreement between the two judgments, which neither the report nor Argon lists. With the change, `Ty.shareableUnder_canonical` holds, the relation cannot launder, and `canonical_agreement_keeps_shareability` states it.

*Alternatives:*
- the checker drops `agree`, which loses a deliberate defence;
- the relation's `conversion` takes `agree`, which makes conversion directional and forces the machine typing (`ConversionPath`, `ValueTyping`) to follow.

*Critique:* overriding a non-shareable member, or a field typed by a variable (which is not `shareable`), no longer converts to the row without the shadowed entry. **MEASURED:** the cohorts did not notice.

*Meta-critique:* a type-variable field that is shareable under `shareableVariables` is kept too, which is conservative. Making `canonical` depend on the assumptions would have been more precise, but it would have broken `canonical_instantiate`.

**D3. The relation keeps `∃ fuel` for `lookup` and `isRow`.**

`lookupV` and `isRowV` walk with a visited set, budgeted by the bounds not yet visited. They are structural, so the kernel evaluates them, and they are proved equal to the relation's lookups (`lookupV_iff`, `isRowV_iff`).

*Alternative:* put the visited set in the relation itself, as the brief allowed.

*Critique:* the relation still has a fuel binder.

*Meta-critique:* the fuel is existential and proved immaterial. Moving it would have cost a cascade through `Records`, `Sums` and `Templates` and bought nothing.

**D4. Repeated case labels are refused by the relation (`labelsDistinct` premise on `case` and `effectCase`), not typed at their own row entry.**

The machine never reaches a later duplicate, and no scrutinee determines its payload, so a complete checker would have to guess it. A refusal is the one semantics both judgments can share.

*Critique:* this adds a premise to two constructors.

*Meta-critique:* the alternative (type the later duplicate at the first entry's payload) keeps dead code typable. That is no gain, and it would mean rebuilding `ArmsTyping`.

**D5. One structural function by mode.**

`elaborate` has an inline `finish` for eliminations and an `introduce` for introduction forms. The point is that synthesis falling back to checking on the *same* term stays structural, so `decide` evaluates it and the teeth are kernel proofs. The `case` clause is split by its arm list so that Lean generates its equation lemmas.

*Critique:* some code is duplicated between the two `case` equations.

*Meta-critique:* it is the price of structural recursion. Well-founded recursion would have made every tooth `native_decide`.

**D6. Annotations are read only in synthesis.**

The lambda and `inject`/`perform`/`done` meanings are unchanged. At other introduction forms an annotation is an ascription. At an elimination it is taken only when it agrees with what was synthesized. This is why the direct theorem holds *whatever the annotations*: the fragment never reads one that could be wrong.

*Critique:* a wrong ascription on an elimination is silently ignored.

*Meta-critique:* it is still sound (the certificate is what is trusted), and the full corollary needs ascriptions to make synthesized types exact.

**D7. Usage is proved equal, not `UsesLE`.**

Uses are syntactic occurrence counts, determined by the term. The derivation's vector and the checker's are equal, which is stronger than `UsesLE`.

**D8. The slot judge is the checker *restricted to the fragment*, with the grant bounding term depth.**

`Decides.check_covered` (acceptance implies `Covered`) makes a purely syntactic `Covered` possible only if the judge accepts nothing outside it. The grant now prices the invocation as recursion depth, which is honest for a fuel-free structural checker and keeps `budget_tooth` true.

*Critique:* annotated programs outside the fragment are refused by the slot judge, though `checkAgainst` certifies them. Objects built by `extend` are among them.

*Meta-critique:* the alternative, `Covered := checkCovered ∨ accepted`, re-creates `Recognized`. Widening the judge waits on D1's decision or on the full corollary.

**D9. The old checker's joins use `agree`, not plain `sameType`.**

This keeps its stated invariant ("every conversion the checker inserts goes through `agree`"). After D2 the two differ only on nominal alias shareability.

## 4. What Argon's design got wrong once I reached the code

- **"Prove `Equivalence (sameType …)` by hereditary structural unfolding."** Equivalence needs only the closure (D1). Structural descent is a *different relation*, with coinductive or congruence questions attached. What actually needs it is principality of synthesis, not equivalence.
- **The laundering gap was not on the list.** The relation's plain-`sameType` conversion and the checker's `agree` disagreed on shadowed non-shareable members. No complete checker could keep `agree`. D2 closes it in the relation.
- **`annotateFromDerivation : PartialTyping … → AnnotatedTerm` cannot be a function.** `PartialTyping` is a `Prop`, and it cannot be eliminated into data. The corollary has to be `∃ annotations`, proved by induction with a locality lemma, because the checker reads annotations only at positions under its own.
- **`Covered := checkCovered` with the class as it stands** forces the judge to be restricted to the fragment (D8). Argon's step 5 reads as if the judge could stay the whole checker.
- **"Usage synthesis stays inside the checker."** Correct, and more than that: the vectors are equal (D7).
- **"`lookup`/`isRow` fuel replaced by the visited-set bound."** Done as an equivalence rather than a replacement (D3).

## 5. Not done, and why

- **The full corollary** (`PartialTyping → ∃ annotations, checkAgainst accepts`). The checker is built for it:
  - lambda annotations;
  - ascriptions on introduction forms;
  - ascriptions on eliminations taken when they agree;
  - `extend`'s annotation, whose domain is the target's representative and whose codomain is the fields' row, checked positionally;
  - records with a repeated label now synthesize in checking mode rather than being refused.

  The proof needs a second induction of the size of `complete`, plus a locality lemma (results depend only on annotations at extensions of the path). I stopped at the direct theorem, which is complete and unconditional on annotations.
- **`extend`** is outside the direct fragment (D1).
- The front end still admits with `Check.check`. The brief did not ask to move it, and the cohorts were left as they were.

## 6. The one decision for Ember

**Should type agreement be a congruence?**

Today it is the equivalence closure of alias-head unfolding plus canonical row equality. It is decided, it is an equivalence, and it does not descend into arrows, rows, sums or activities. The cost is that synthesis of an introduction form is not principal. So:

- the fragment must put records, specifications, prototypes and every branching form in checking position;
- `extend` is outside the fragment;
- the slot judge, which is restricted to the fragment (D8), refuses object fillings built by `extend`.

The options:

- **(a) Keep it.** Widen admission instead by finishing the annotated corollary, so that annotated `extend` is admitted by a theorem rather than by fiat.
- **(b) Inductive congruence closure**, decided by congruence closure over the subterm graph of the types and the bounds.
- **(c) Equi-recursive agreement** (Amadio–Cardelli and Brandt–Henglein), decided by bisimulation with a visited set of pairs.

Options (b) and (c) both change `PartialTyping`'s meaning (more conversions). Both also require the machine invariants (`HeadNormalizes`, `canonical_lookup_transport` and their users in `Preservation.Cases.*`) to relate components up to agreement instead of canonical equality.

My recommendation is (a) now and (c) as its own lane:

- (a) is a proof of the size already done.
- (c) is the agreement a reader of recursive object types expects.
- (b) is weaker than (c) on recursive aliases, and no simpler to decide.

## Appendix: the journal's exact sets

Names are grouped by their namespace prefix; `_private.` prefixes are dropped. Auto-generated
declarations (`eq_def`, `_proof_n`, `brecOn`, structure projections) are part of the set as the
journal reports it.

### Step 1 (`281bdac` against `e256cab`)

**revised theorems (12)**

- `Obend.Core.Check.infer`: `_proof_17`, `_proof_18`, `eq_22`, `eq_def`
- `Obend.Core.Check.inferArms`: `eq_def`
- `Obend.Core.Check.sameType`: `eq_1`
- `Obend.Core.Proofs.CheckCompletenessObstruction.aliasBranchChecked`: `_proof_2`, `_proof_3`, `_proof_4`
- `Obend.Core.Ty.Ty.insertCanonical`: `eq_1`, `eq_def`
- `Obend.Core.Proofs.Templates`: `insertCanonical_same`

**STATEMENT-CITED (505)**

- `Obend.Core.Check.ArmsTyping`: `brecOn`
- `Obend.Core.Check.Checked`: `assumptionsValid`, `contextValid`, `derivation`, `safe`
- `Obend.Core.Check.Checked.mk`: `congr_simp`, `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.Check.CheckedExtension.mk`: `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.Check.CheckedExtension`: `required`, `shape`
- `Obend.Core.Check.FieldsTyping`: `brecOn`
- `Obend.Core.Check.Inferred`: `derivation`
- `Obend.Core.Check.Inferred.mk`: `congr_simp`, `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.Check.InferredArms`: `derivation`
- `Obend.Core.Check.InferredArms.mk`: `congr_simp`, `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.Check.InferredFields`: `derivation`
- `Obend.Core.Check.InferredFields.mk`: `congr_simp`, `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.Check.PartialTyping`: `brecOn`
- `Obend.Core.Check.agree`: `eq_1`
- `Obend.Core.Check`: `agree_never_manufactures_shareability`, `agree_sameType`, `agree_shareable`, `checked_erasure`, `reusable_lambda_capture_rule`, `sameType_isComputation`
- `Obend.Core.Check.check`: `_proof_1`, `eq_1`
- `Obend.Core.Check.infer`: `_proof_1`, `_proof_10`, `_proof_11`, `_proof_12`, `_proof_13`, `_proof_14`, `_proof_15`, `_proof_16`, `_proof_19`, `_proof_2`, `_proof_20`, `_proof_21`, `_proof_22`, `_proof_23`, `_proof_3`, `_proof_4`, `_proof_5`, `_proof_6`, `_proof_7`, `_proof_8`, `_proof_9`, `eq_1`, `eq_10`, `eq_11`, `eq_12`, `eq_13`, `eq_14`, `eq_15`, `eq_16`, `eq_17`, `eq_18`, `eq_19`, `eq_2`, `eq_20`, `eq_21`, `eq_23`, `eq_24`, `eq_25`, `eq_3`, `eq_4`, `eq_5`, `eq_6`, `eq_7`, `eq_8`, `eq_9`
- `Obend.Core.Check.inferArms`: `_proof_1`, `eq_1`, `eq_2`, `eq_3`, `eq_4`
- `Obend.Core.Check.inferFields`: `_proof_1`, `eq_1`, `eq_2`, `eq_3`, `eq_def`
- `Obend.Core.Collect.HeapGood`: `assumptionsValid`, `idle`, `size_le`, `typed`, `valid`
- `Obend.Core.Collect.closureTyping_rename`: `_proof_1`
- `Obend.Core.Collect.enteredTyping`: `_proof_1`, `_proof_2`, `_proof_5`, `_proof_6`, `_proof_7`, `_proof_8`, `_proof_9`
- `Obend.Core.Collect.garbageTyping`: `_proof_1`, `_proof_2`, `_proof_6`, `_proof_9`
- `Obend.Core.Collect`: `heapTyping_rename`, `heapTyping_settle`
- `Obend.Core.Collect.selfOriginTyping`: `_proof_2`
- `Obend.Core.Collect.typed_collect`: `_proof_1`, `_proof_2`
- `Obend.Core.Collect.typed_related`: `_proof_1`, `_proof_2`, `_proof_3`, `_proof_4`, `_proof_5`, `_proof_6`
- `Obend.Core.Collect.typed_settle`: `_proof_1`, `_proof_2`, `_proof_3`
- `Obend.Core.MachineTyping.ClosureTyping`: `contextValid`, `environment`, `safe`, `source`
- `Obend.Core.MachineTyping.ClosureTyping.mk`: `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.MachineTyping.ConversionPath`: `brecOn`
- `Obend.Core.MachineTyping.HeapTyping`: `cell`, `length`
- `Obend.Core.MachineTyping.StackTyping`: `brecOn`
- `Obend.Core.MachineTyping.StateTyping`: `assumptionsValid`, `busy`, `control`, `heap`, `lexical`, `stack`, `terminalStack`
- `Obend.Core.MachineTyping.StateTyping.mk`: `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.MachineTyping.ValueTyping`: `brecOn`
- `Obend.Core.MachineTyping.checked_initial_state`: `_proof_1`, `_proof_2`, `_proof_3`, `_proof_4`, `_proof_5`, `_proof_6`
- `Obend.Core.MachineTyping`: `source_fields_row`, `source_fields_scoped`, `source_scoped`, `source_uses_length`
- `Obend.Core.Proofs.CheckCompletenessObstruction`: `annotated_empty_eliminator_still_incomplete`, `checked_does_not_imply_eventual_success`, `checked_lambda_without_annotations_never_checks`, `correct_lambda_annotation_still_incomplete`, `aliasBranch_refused`, `annotatedConstant_accepted`, `duplicateCase_refused`, `emptyCase_refused`, `unannotatedConstant_refused`
- `Obend.Core.Proofs.CheckCompletenessObstruction.emptyCaseChecked`: `_proof_2`
- `Obend.Core.Proofs.CheckCompletenessObstruction.unannotatedConstantChecked`: `_proof_1`
- `Obend.Core.Proofs.CheckTeeth`: `absent_future_requirement_refused`, `affine_in_one_arm_accepted`, `affine_in_two_arms_refused`, `affine_mix_capture_refused`, `arbitrary_labels_are_not_booleans`, `arm_results_must_agree`, `boolean_label_equality_refused`, `closure_response_refused`, `custody_in_once_closure_accepted`, `custody_in_reusable_closure_refused`, `duplicate_affine_refused`, `effect_as_argument_refused`, `effect_case_accepted`, `effect_in_payload_refused`, `effect_in_record_field_refused`, `effect_in_specification_refused`, `equality_branch_accepted`, `exhaustive_case_accepted`, `explicit_boolean_conjunction_accepted`, `explicit_boolean_has_boolean_type`, `extra_arm_refused`, `future_binary_instantiation_accepted`, `future_row_instantiation_accepted`, `future_row_typed`, `heterogeneous_runtime_mix_accepted`, `independent_requirements_checked`, `independently_checked_future_rows`, `label_condition_refused`, `label_equality_accepted`, `missing_arm_refused`, `nat_primitive_label_operand_refused`, `nat_primitive_types`, `order_primitive_branch_accepted`, `pure_affine_argument_accepted`, `pure_arm_without_done_refused`, `record_wrapper_does_not_hide_custody`, `recursive_alias_does_not_hide_custody`, `recursive_global_knot_accepted`, `recursive_sum_ill_typed_tail_refused`, `recursive_sum_list_accepted`, `refusal_kind_custody_in_reusable_closure`, `refusal_kind_duplicate_affine`, `refusal_kind_label_conjunction`, `refusal_kind_starved_fuel`, `reordered_arms_accepted`, `reserved_string_has_string_type`, `reserved_strings_are_not_booleans`, `reusable_lexical_capture_accepted`, `reusable_mix_capture_accepted`, `scalar_plan_refused`, `scalar_record_extend_refused`, `shadowed_custody_laundering_refused`, `shadowed_once_closure_laundering_refused`, `shadowed_override_accepted`, `shadowed_shareable_member_accepted`, `unannotated_injection_refused`, `undeclared_injection_refused`, `_proof_1_1`, `_proof_1_1`, `_proof_1_1`, `_proof_1_1`
- `Obend.Core.Proofs.CheckTeeth.futureRowInstanceChecked`: `eq_1`
- `Obend.Core.Proofs.Hole`: `check_refuses_hole`, `infer_refuses_hole`
- `Obend.Core.Proofs.Preservation.CapturedFunction.arrow`: `eq_1`
- `Obend.Core.Proofs.Preservation.CapturedFunction`: `bodyTyped`, `captures`, `environmentTyped`, `safe`, `valid`
- `Obend.Core.Proofs.Preservation.CapturedFunction.mk`: `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.Proofs.Preservation.CellTyping`: `weaken`
- `Obend.Core.Proofs.Preservation.ClosureTyping.weaken`: `_proof_1`
- `Obend.Core.Proofs.Preservation.ControlTyping`: `weaken`
- `Obend.Core.Proofs.Preservation.FocusedSource`: `continuation`, `result`
- `Obend.Core.Proofs.Preservation.FocusedSource.mk`: `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.Proofs.Preservation.FrameTyping`: `weaken`
- `Obend.Core.Proofs.Preservation.HeadNormalizes`: `brecOn`
- `Obend.Core.Proofs.Preservation.ReusableTerm.abstraction`: `_proof_1`, `_proof_2`, `_proof_3`
- `Obend.Core.Proofs.Preservation.ReusableTerm.apply`: `_proof_1`, `_proof_2`, `_proof_3`
- `Obend.Core.Proofs.Preservation.ReusableTerm`: `captures`, `derivation`
- `Obend.Core.Proofs.Preservation.ReusableTerm.mk`: `inj`, `injEq`, `sizeOf_spec`
- `Obend.Core.Proofs.Preservation.ReusableTerm.shiftTwo`: `_proof_1`, `_proof_2`
- `Obend.Core.Proofs.Preservation.ReusableTerm.weaken`: `_proof_1`, `_proof_2`
- `Obend.Core.Proofs.Preservation.StackTyping`: `weaken`
- `Obend.Core.Proofs.Preservation.ValueTyping`: `weaken`
- `Obend.Core.Proofs.Preservation`: `arms_typing_find`, `boolean_value_form`, `callable_value_form`, `canonical_lookup`, `canonical_lookup_transport`, `canonical_same_type`, `check_runBounded_no_refusal`, `closure_callable_type`, `computation_canonical_inj`, `conversionPath_isComputation`, `head_normalizes_unique`, `heap_type_pure`, `heap_typed_push`, `heap_typed_set`, `label_value_form`, `natural_value_form`, `prototype_value_form`, `record_value_form`, `sameType_activity_canonical`, `same_type_lookup_transport`, `same_type_preserves_head`, `source_bound_assignment`, `source_convert_path`, `source_insert_binding`, `source_not_hole`, `source_weaken`, `source_weaken_twice`, `specification_callable_type`, `specification_value_form`, `stack_activity_head`, `stack_argument_value`, `stack_convert_path`, `stack_effect_case`, `stack_update_value`, `typed_application_focus_preserved`, `typed_argument_return_preserved`, `typed_binary_left_preserved`, `typed_binary_right_no_wrong_value`, `typed_binary_right_preserved`, `typed_bound_preserved`, `typed_case_preserved`, `typed_completion_preserved`, `typed_condition_no_wrong_value`, `typed_condition_preserved`, `typed_control_not_refused`, `typed_done_preserved`, `typed_enter_preserved`, `typed_extend_preserved`, `typed_field_preserved`, `typed_fix_preserved`, `typed_ifBool_preserved`, `typed_immediate_preserved`, `typed_inject_preserved`, `typed_metadata_preserved`, `typed_mix_preserved`, `typed_pair_preserved`, `typed_perform_preserved`, `typed_prototype_projection_preserved`, `typed_record_preserved`, `typed_resume_preserved`, `typed_source_focus_preserved`, `typed_stepRaw_preserved`, `typed_update_preserved`, `typed_yield_quiescent`, `value_closure_fields`, `value_head_correct`, `value_prototype_fields`, `value_specification_fields`, `value_typed_not_computation`, `value_variant_fields`, `variant_value_form`, `checked_reachable_no_internal_refusal`, `checked_reachable_no_refusal`, `checked_reachable_no_wrong_value_or_missing_field`, `checked_reachable_typed`, `typed_runBounded_no_refusal`
- `Obend.Core.Proofs.Preservation.reusable_mix_body`: `_proof_5`, `_proof_6`
- `Obend.Core.Proofs.Preservation.step_certificate`: `_proof_1`, `_proof_2`, `_proof_3`
- `Obend.Core.Proofs.Substitution.Fillings`: `closed`, `typed`
- `Obend.Core.Proofs.Substitution`: `check_mono`, `check_msubst`, `infer_mono`, `typed_scoped`, `alias_filling_checks`, `alias_template_checks`, `assumptions_tooth`, `fuel_filling_checks`, `fuel_template_checks`, `fuel_tooth`, `infer_msubst`, `infer_transport`, `linear_filling_checks`, `linear_template_checks`, `open_filling_tooth`
- `Obend.Core.Proofs.TypedSubstitution`: `checked_msubst`, `partialTyping_closed_transport`, `partialTyping_msubst`, `partialTyping_transport`
- `Obend.Core.Ty.Ty.canonical`: `eq_1`, `eq_2`, `eq_3`, `eq_4`, `eq_5`, `eq_6`, `eq_7`, `eq_def`
- `Obend.Core.Ty.Ty`: `canonical_isComputation`, `insertCanonical_not_computation`
- `Obend.Core.Ty.Ty.insertCanonical`: `eq_2`
- `Obend.Slot.Core4`: `calculus_check_iff`, `calculus_check_msubst`, `calculus_check_msubst_within`, `calculus_typed_msubst`, `gradedCheck_iff`, `uses_var`
- `Obend.Slot.Core4.instDecidesNatAnnotatedTerm`: `_proof_1`, `_proof_2`, `_proof_3`, `_proof_4`
- `Obend.Slot`: `budget_filling_typed`, `budget_tooth`, `budget_uncovered`
- `Obend.Spec.FrontEnd.Accepted`: `checkedExact`, `closed`, `decoded`, `erasure`, `packetTerm`, `proposed`, `shallow`, `sound`, `sourceExact`, `source_eq_packet`
- `Obend.Spec.FrontEnd.Accepted.mk`: `inj`, `injEq`, `sizeOf_spec`
- `Obend.Spec.Proofs.FrontEndAdequacy`: `accept_inhabited`, `accepted_execution_semantics`, `accepted_never_refused`, `accepted_typed`
- `Obend.Spec.Proofs.SpecificationClosure`: `binary_self_accepted`, `claim_spec_accepted`, `compose_wrapper_typed`, `empty_seed_accepted`, `f_bound_mismatch_refused`, `inherited_unprovided_refused`, `law_keyword_refused`, `meta_conversion`, `non_boolean_claim_refused`, `open_extension_reused_accepted`, `provenance_typed`, `requires_signature_refused`, `twice_accepted`, `unbound_self_member_refused`, `unprovided_requirement_refused`, `wrong_target_refused`
- `Obend.Core.Proofs.Collect`: `cellTyping_rename`, `controlTyping_rename`, `frameTyping_rename`, `garbageTyped_collect_typed`, `stackTyping_rename`, `typed_collect_exists`, `valueTyping_rename`
- `Obend.Core.Proofs.Force`: `good_foldlM`, `good_forceWith`, `good_materializeWith`, `good_of_finished`, `typed_checkpoint`, `typed_forceWith_any`, `typed_runBounded_any`, `typed_yieldedPlanWith`
- `Obend.Core.Proofs.LedgerPoles`: `conversionPath_head`, `conversionPath_natural`, `not_conversionPath_natural_boolean`
- `Obend.Core.Proofs.Preservation.Base`: `arms_uses_length`, `canonical_agreement_normalizes`, `canonical_is_variable`, `canonical_row_lookup_agreement`, `canonical_tail`, `canonical_type_head`, `canonical_variable_inverse`, `insert_canonical_lookup`, `insert_canonical_not_variable`, `insert_canonical_row_head`, `insert_canonical_tail`, `insert_usage_bound`, `row_head_normalizes`, `source_focus_typed`, `typed_step_no_invalidUpdate`
- `Obend.Core.Proofs.Preservation.Cases.Activities`: `source_done_decomposition`, `source_perform_decomposition`, `stack_activity_no_update`, `stack_activity_signature`, `written_response_typed`, `yielded_control_type`
- `Obend.Core.Proofs.Preservation.Cases.Arithmetic`: `primitive_result_typed`, `stack_binary_left_value`, `stack_binary_right_values`, `stack_condition_value`
- `Obend.Core.Proofs.Preservation.Cases.Functions`: `immediate_value_typed`, `source_application_decomposition`, `source_fix_expansion`, `source_mix_expansion`
- `Obend.Core.Proofs.Preservation.Cases.Pairs`: `source_pair_decomposition`, `source_pair_decomposition_pure`, `stack_metadata_value`, `stack_projection_value`
- `Obend.Core.Proofs.Preservation.Cases.Records`: `fields_overlay_lookup`, `fields_overlay_row`, `source_record_decomposition`, `stack_extend_value`, `stack_field_member`, `typed_fields_allocation`, `value_record_member`
- `Obend.Core.Proofs.Preservation.Cases.Sums`: `arms_row_closed`, `arms_typing_absent`, `source_inject_decomposition`, `source_inject_decomposition_pure`, `stack_case_value`, `stack_ifBool_value`
- `Obend.Core.Proofs.Templates`: `agree_instantiate`, `check_instantiate`, `infer_instantiate`, `sameType_instantiate`, `canonical_eq_instantiate`, `canonical_instantiate`, `canonical_instantiate_insert`, `coloured_instance_accepted`, `inferFields_tail`, `insertCanonical_comm`, `self_as_bound_row_alias_accepted`, `self_as_bound_row_rigid_refused`, `weight_template_accepted`

**PROOF-CITED (1)**

- `List.lookup`: `eq_def`

### Step 2 (`d4fb86f` against step 1)

**revised theorems (8)**

- `Obend.Core.Check.infer`: `_proof_14`, `_proof_19`, `eq_20`, `eq_23`, `eq_def`
- `Obend.Core.Check.inferArms`: `_proof_1`, `eq_4`, `eq_def`

**STATEMENT-CITED (165)**

- `Obend.Core.Check.check`: `eq_1`
- `Obend.Core.Check.infer`: `eq_1`, `eq_10`, `eq_11`, `eq_12`, `eq_13`, `eq_14`, `eq_15`, `eq_16`, `eq_17`, `eq_18`, `eq_19`, `eq_2`, `eq_21`, `eq_22`, `eq_24`, `eq_25`, `eq_3`, `eq_4`, `eq_5`, `eq_6`, `eq_7`, `eq_8`, `eq_9`
- `Obend.Core.Check.inferArms`: `eq_1`, `eq_2`, `eq_3`
- `Obend.Core.Check.inferFields`: `eq_1`, `eq_2`, `eq_3`, `eq_def`
- `Obend.Core.Proofs.CheckCompletenessObstruction`: `annotated_empty_eliminator_still_incomplete`, `checked_does_not_imply_eventual_success`, `checked_lambda_without_annotations_never_checks`, `annotatedConstant_accepted`, `duplicateCase_refused`, `emptyCase_refused`, `unannotatedConstant_refused`
- `Obend.Core.Proofs.CheckTeeth`: `absent_future_requirement_refused`, `affine_in_one_arm_accepted`, `affine_in_two_arms_refused`, `affine_mix_capture_refused`, `arbitrary_labels_are_not_booleans`, `arm_results_must_agree`, `boolean_label_equality_refused`, `closure_response_refused`, `custody_in_once_closure_accepted`, `custody_in_reusable_closure_refused`, `duplicate_affine_refused`, `effect_as_argument_refused`, `effect_case_accepted`, `effect_in_payload_refused`, `effect_in_record_field_refused`, `effect_in_specification_refused`, `equality_branch_accepted`, `exhaustive_case_accepted`, `explicit_boolean_conjunction_accepted`, `explicit_boolean_has_boolean_type`, `extra_arm_refused`, `future_binary_instantiation_accepted`, `future_row_instantiation_accepted`, `heterogeneous_runtime_mix_accepted`, `independent_requirements_checked`, `independently_checked_future_rows`, `label_condition_refused`, `label_equality_accepted`, `missing_arm_refused`, `nat_primitive_label_operand_refused`, `nat_primitive_types`, `order_primitive_branch_accepted`, `pure_affine_argument_accepted`, `pure_arm_without_done_refused`, `record_wrapper_does_not_hide_custody`, `recursive_alias_does_not_hide_custody`, `recursive_global_knot_accepted`, `recursive_sum_ill_typed_tail_refused`, `recursive_sum_list_accepted`, `refusal_kind_custody_in_reusable_closure`, `refusal_kind_duplicate_affine`, `refusal_kind_label_conjunction`, `refusal_kind_starved_fuel`, `reordered_arms_accepted`, `reserved_string_has_string_type`, `reserved_strings_are_not_booleans`, `reusable_lexical_capture_accepted`, `reusable_mix_capture_accepted`, `scalar_plan_refused`, `scalar_record_extend_refused`, `shadowed_custody_laundering_refused`, `shadowed_once_closure_laundering_refused`, `shadowed_override_accepted`, `shadowed_shareable_member_accepted`, `unannotated_injection_refused`, `undeclared_injection_refused`, `_proof_1_1`, `_proof_1_1`, `_proof_1_1`, `_proof_1_1`
- `Obend.Core.Proofs.CheckTeeth.futureRowInstanceChecked`: `eq_1`
- `Obend.Core.Proofs.Hole`: `check_refuses_hole`, `infer_refuses_hole`
- `Obend.Core.Proofs.Preservation`: `check_runBounded_no_refusal`
- `Obend.Core.Proofs.Substitution.Fillings`: `closed`, `typed`
- `Obend.Core.Proofs.Substitution`: `check_mono`, `check_msubst`, `infer_mono`, `alias_filling_checks`, `alias_template_checks`, `assumptions_tooth`, `fuel_filling_checks`, `fuel_template_checks`, `fuel_tooth`, `infer_msubst`, `infer_transport`, `linear_filling_checks`, `linear_template_checks`, `open_filling_tooth`
- `Obend.Slot.Core4`: `calculus_check_iff`, `calculus_check_msubst`, `calculus_check_msubst_within`, `gradedCheck_iff`
- `Obend.Slot.Core4.instDecidesNatAnnotatedTerm`: `_proof_1`, `_proof_2`, `_proof_3`, `_proof_4`
- `Obend.Slot`: `budget_tooth`, `budget_uncovered`
- `Obend.Spec.FrontEnd.Accepted`: `checkedExact`, `closed`, `decoded`, `erasure`, `packetTerm`, `proposed`, `shallow`, `sound`, `sourceExact`, `source_eq_packet`
- `Obend.Spec.FrontEnd.Accepted.mk`: `inj`, `injEq`, `sizeOf_spec`
- `Obend.Spec.Proofs.FrontEndAdequacy`: `accept_inhabited`, `accepted_execution_semantics`, `accepted_never_refused`, `accepted_typed`
- `Obend.Spec.Proofs.SpecificationClosure`: `binary_self_accepted`, `claim_spec_accepted`, `empty_seed_accepted`, `f_bound_mismatch_refused`, `inherited_unprovided_refused`, `law_keyword_refused`, `non_boolean_claim_refused`, `open_extension_reused_accepted`, `requires_signature_refused`, `twice_accepted`, `unbound_self_member_refused`, `unprovided_requirement_refused`, `wrong_target_refused`
- `Obend.Core.Proofs.Templates`: `check_instantiate`, `infer_instantiate`, `coloured_instance_accepted`, `inferFields_tail`, `self_as_bound_row_alias_accepted`, `self_as_bound_row_rigid_refused`, `weight_template_accepted`

**PROOF-CITED (2)**

- `Obend.Core.Proofs.CheckTeeth`: `future_row_typed`
- `Obend.Slot`: `budget_filling_typed`
