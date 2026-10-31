# Report: `linear` separates from `affine` in the checker (lane Linear, Claude Opus, 2026-11-01)

Brief: `lean/docs/LANE-LINEAR-BRIEF-20261101.md`. Rebased onto `ccbcd13` (the piece split `9c2e291` and
the build tiers `9450dc4` landed while the lane ran). Tier 1 (`lake build`) green at 275 jobs, tier 2
(`lake build Obend.Census Teeth`) green at 295 jobs; `#assert_axioms_tree`: 32950 package constants,
none on `sorryAx` or a declared axiom, 27 on the compiler trust as before (this lane adds no
`native_decide`). Start measurement: `lake build` at `66fad42`, 251 jobs, 164 s (most rebuilt from a
seeded `.lake`). End: 275 jobs, warm replay. Control: `tests/run-obend-source.py` probes 30/30, preview
161/161, tutorial 71/71 of which 3 at a decided deviation (below); `tests/run-receipts.py` 17/17, before
and after.

## The rule

Exact discharge is two premises, both in the kernel, both named by the bidirectional checker.

1. **At the binder.** `PartialTyping.lambda` gains a fifth premise, `annotation.parameter.fits
   (uses.headD 0) = true` (`Quantity.fits`, until now used only by `CheckTeeth`, is the rule). With
   `safeUses` already bounding a `linear` count by one, this says a `linear` parameter is used exactly
   once. `Check.infer` and `Bidirectional.elaborate` check it; the refusal is
   `CheckRefusal.linearBinderUnused path`, at the lambda. The uses vector is unchanged in shape.
2. **At the argument.** Counting at the binder alone is defeated by `λ(h : linear). (λ(z : affine). 0) h`
   (one syntactic use, then dropped). `argumentAllowed q Γ A u` gains `q == .linear || linearFree Γ u`
   (`Ty.linearFree`: no `linear` hypothesis has a nonzero count): a `linear` hypothesis is handed only to a
   `linear` parameter, never to one that may drop it (`erased`, `affine`) or share it (`unrestricted`,
   which already demanded reusable captures). The refusal is `linearArgumentDropped path index quantity`,
   naming the hypothesis and the callee's quantity (`Bidirectional.argumentRefusal`).

`safeQuantity`'s docstring no longer says exact discharge is checked elsewhere. `ValueTyping.closure`
(the machine) is unchanged: preservation needs fewer premises, not more.

## Metatheory re-established (all MEASURED green)

- **Substitution.** A closed filling never uses the binders above its position, so their counts are kept
  exactly, not only bounded. New `UsesLEOn k u v := UsesLE u v ∧ u.take k = v.take k`
  (`Substitution/Uses.lean`, with `.add`, `.tail`, `.headD`, `variableUses_take_zero`). `infer_msubst`
  now concludes `UsesLEOn Δ.length`; `partialTyping_msubst` likewise (strengthened; revised in the
  journal); `check_msubst`, `checked_msubst`, `calculus_typed_msubst` keep their statements (`.le`).
  `infer_transport` and `partialTyping_transport` carry `fits` (`headD_append`).
- **Preservation.** `argument_allowed_insert` (weakening) via `linear_free_insert` and
  `linearFree_of_reusableCaptures` (in `Ty.lean`); the lambda case via `headD_insert_succ`.
  `ReusableTerm.abstraction` takes `notLinear : quantity ≠ .linear := by decide` (a body with reusable
  captures uses its binder only when unrestricted, so a `linear` binder there would be unused;
  `reusable_binder_fits`). Its one caller (mix bodies) is `unrestricted`.
- **Completeness.** `completes_lambda` takes `fits` (revised); `complete`, `full_annotated` unchanged in
  statement. `prepare_checks` unchanged in statement; `LamInv` carries `fits`, `motive_lambda` and
  `lam_run` take it (revised).
- **Preparation changed (executable).** `Prepare.letQuantity` returned `unrestricted` or `affine`; a let
  whose argument uses a `linear` hypothesis now gets a `linear` parameter, and its body uses it once
  because the source derivation's parameter was forced `linear` by the same argument rule
  (`linear_of_used`, `fitsOf` in `PrepareChecks`). `linearFree_refines`: a refinement never makes a binder
  `linear` that was not.
- Templates (`linearFree_instantiate`), Law typing (`chk_app`), Spec closure, Slot fixtures: premise
  added or simp sets extended (`Quantity.fits`, `linearFree`).

## The coercion table, re-derived (`Elab/Coerce.lean`, `Elab/Proofs/CoerceProbes.lean`)

The η-wrapper matrix `wrapperMeasured q q'` (rows `q` = the callee's, columns `q'` = the wrapper's, order
erased, affine, linear, unrestricted), measured on the checker by `#guard`:

| q \ q' | before | after |
|---|---|---|
| erased | F T **T** T | F T **F** T |
| affine | F T **T** T | F T **F** T |
| linear | F T T T | F T T T |
| unrestricted | F F F T | F F F T |

Exactly the two cells ALGEBRAIC-SUBTYPING §5.1 and QUOTE-ORIENTATION §2.4 predict change: a `linear`
wrapper parameter relabelled as `affine` (or `erased`) and dropped. `linear → affine` stays (a
must-consume callee is safe for a droppable argument). Both changed cells are refused by the kernel as
`linearArgumentDropped [0,1] 0 q` (`#guard`). `wrapperAllowed` is that matrix; `coerce` refuses the two
cells first, by name, as `CoercionRefusal.launders q q'` (`#guard` for `affine → linear`, which was emitted
before, and `erased → linear`). When the wrapper's parameter is `linear`, its domain and codomain
components are emitted `linear` (`Emitted.once`): `linear → linear` with a codomain or a domain
coercion checks; a domain coercion that drops every field of the `linear` argument is refused
`.checker (.linearBinderUnused _)`; the same wrapper with the component left `affine` is refused
`linearArgumentDropped _ 0 .affine` (`#guard`). `emit_identity_checks`, `width_checks` carry `fits`.

## Teeth (`Obend/Teeth/Core/LinearTeeth.lean`, tier 2)

- `dropped_linear_custody_refused`: `λ(h : Custody). 0` at `linear` is `linearBinderUnused []`; the fuel
  checker refuses it too; at `affine` it is accepted. `#tooth … by mutation custodyQuantity := .affine`
  bites.
- `laundered_custody_refused`: `λ(h : linear Custody). (λ(z : affine). 0) h` is `linearArgumentDropped
  [0,1] 0 .affine`. `#tooth … by mutation calleeQuantity := .linear` bites; with a `linear` callee the drop
  is found at the callee's binder (`handed_to_linear_refused_at_callee`, `linearBinderUnused [0,0]`).
- `passed_linear_custody_accepted`: a `linear` custody into a `linear` slot that uses it checks.
- `open_filling_tooth` (`Teeth/Core/SubstitutionTeeth`) still bites (tier 2 log).
- A coercion that would launder a once-resource is refused by name: the `launders` probes in `CoerceProbes`.

## Deviations

- **Tutorial chapter 7** (Mini's `ch7-once.obend`): `droppedLinear` (a `linear` parameter never used) was
  pinned `finished 0`; the checker refuses it, and since it refuses the whole program, `once` and
  `dropped` in the same file are refused too. Before: `status: finished / type: Nat / result: 5|0|0`.
  After: `status: refused / stage: objective-typed-preview / message: ownership refused: a linear
  parameter is used exactly once, and only by a linear parameter; one is not used, or is passed where it
  may be dropped or shared (…)`, exit 2. Held by name in `DECIDED_DEVIATIONS` (`tests/run-obend-source.py`),
  printed per command with Mini's lines. The source file is Mini's and is unchanged.
- `Gate.refusalReason`'s ownership sentence names the linear case when the checker's refusal is one of the
  two new ones; the old sentence (Mini's, pinned by `ch7-twice`) is kept for overuse.
- Receipts: none.

## The journal (`lake exe journal`), `66fad42` → `3408ea3`

The base moved under the lane (split, tiers, Intention, Code, C4, Runner-2), so the diff mixes lanes:
2530 withdrawn supports, 192 revised, 1212 STATEMENT-CITED, 104 PROOF-CITED, 2643 added, 1622 removed
(module moves rename privates), 12680 unaffected. This lane's revised statements: `partialTyping_msubst`,
`completes_lambda`, `motive_lambda`, `lam_run` (and the private `infer_msubst`, `infer_transport`'s motive,
`ReusableTerm.abstraction`). `check_msubst`, `checked_msubst`, `calculus_typed_msubst`, `complete`,
`full_annotated`, `prepare_checks` are STATEMENT-CITED (they mention `PartialTyping`) and rebuilt green
with unchanged statements. The other revised names (`Data.*_remaining`, `Run.Shared.*`, `Spec.Ecosystem.*`,
`Law.c4_tooth`, …) are other lanes'.

## Round 2: joins and projections (Ember's decision, relayed 11-01)

The decision: at `ifBool`, `ifZero` and the arms of a `case`, a `linear` hypothesis's count is equal
across every branch and the join is that count; an `affine` one joins by maximum; and the projection
gap is closed the same way. Landed as follows.

**The combinator** (`Core/Ty.lean`). `joinUses first second := zipWith max` and `branchesAgree context
first second`, which is `Quantity.agrees` (equality for `linear`, true otherwise) pointwise over the
context. The three join rules share them: `ifBool` gives `addUses cu (joinUses tu fu)` under
`branchesAgree context tu fu`; `ifZero` gives `addUses vu (joinUses zu su.tail)` under
`branchesAgree context zu su.tail`; `ArmsTyping.cons` gives `joinUses bu.tail ru` under
`rest.isEmpty || branchesAgree context bu.tail ru` (the last arm agrees with no one, so a nil tail of
zeros does not demand zero). Refusal: `CheckRefusal.linearBranchesDisagree path index`.

**DEVIATION from the instruction: `unrestricted` joins by `max`, not by sum.** Two reasons, both
MEASURED as breakage when the join depends on the quantity. (i) `uses_determined`: a term's uses are a
function of the term alone (`occurrences`), which `Checked.eq_of_type` and `prepare_checks`
(`argumentUses : au = occurrences Γ.length argument`) rely on; a sum-or-max chosen by quantity makes
`occurrences` depend on the context. (ii) Preparation refines a binder's quantity
(`QuantityRefines`: `affine` or `linear` may become `unrestricted` at a let), and `prepare_checks`
asserts the prepared uses equal the derivation's exactly; a quantity-indexed join changes the vector
under that refinement. Nothing reads an `unrestricted` count except as zero or nonzero
(`reusableCaptures`), on which `max` and sum agree. So the combinator is one `max` everywhere and the
quantity enters only through `branchesAgree`; for `linear` and `affine` it is exactly what was asked.

**Projections.** `get`, `reflect`, `metadata` and `project` require `linearFree context targetUses`:
records, specifications and prototypes are multiplicative, so keeping one component drops the rest,
and a dropped sibling may hold a `linear` obligation. The binder count cannot see which sibling a
hypothesis went into, so the rule is that a projection's target uses no `linear` hypothesis at all.
Refusal: `CheckRefusal.linearProjected path index`. Consequence: a `linear` record cannot be projected;
it is consumed whole (passed to a `linear` parameter, put in a record or variant, matched).

**Metatheory re-established (MEASURED green, tier 1 and tier 2).**
- Substitution needed more than `UsesLEOn`: agreement must survive substitution, and `≤` lets one
  branch's count fall without the other's. Replaced by `UsesMasked σ depth u' u := u' = maskUses
  (keepAt σ depth) u` (`Substitution/Uses.lean`): substitution zeroes exactly the filled hypotheses, a
  function of the position, so both branches are masked alike (`UsesMasked.agree`); `.add`, `.join`,
  `.tail`, `.headD`, `.le`, `.zero`, `.variable`, `.filled`. `infer_msubst` and `partialTyping_msubst`
  conclude `UsesMasked` (strengthened; revised); `check_msubst`, `checked_msubst`,
  `calculus_typed_msubst` unchanged. `UsesLEOn` and its helpers are deleted.
- Transport (`branchesAgree_append_zero`, `split_join`), weakening (`join_uses_insert`,
  `branches_agree_insert`), the machine (`safe_join_uses_left/right`: a join is safe only if each branch
  is), templates (`branchesAgree_instantiate`), refinement (`branchesAgree_refines`).
- Completeness: `completes_ifBool`, `completes_ifZero`, `arms_cons_complete`, `completes_get`,
  `completes_reflect/metadata/project` take the new premise (revised); `complete`, `full_annotated`,
  `prepare_checks` unchanged in statement; `occurrences` joins by `max`; `motive_get`, `motive_ifBool`,
  `armsMotive_cons` take the premise.
- Laws (`Law/Proofs/Typing.lean`): `Syn` and `Chk` are now conditional on `NoLinear ctx` (no binder is
  `linear`), which every law context is (`Clean.noLinear`); only the primitive lemmas changed, the
  composite ones (`chk_andT`, `chk_anyOf`, …) are untouched.
- Other lanes' files touched only where the new premise broke a pattern: `Core/Code.lean` (one arms
  binder), `Spec/Proofs/SpecificationClosure.lean` (`linearFree_variableUses`).

**Coercions.** A record coercion projects its parameter, so a `linear` wrapper's record component is now
refused `.checker (.linearProjected _ 0)` (`#guard`, both the codomain and the domain case; they were
accepted in round 1); a sum component keeps the payload whole and still checks at `linear → linear`
(new `#guard`). `get_bound_checks` and `width_fields_check` take `q ≠ .linear`.

**Teeth** (`Teeth/Core/LinearTeeth.lean`). `dropped_on_branch_refused`: `λ(h : linear Nat). if true then
h else 0` is `linearBranchesDisagree [0] 0` (`#tooth` by mutating the false branch to `h` bites);
`used_on_every_branch_accepted` (it was refused by sum); `affine_branches_accepted`.
`sibling_projection_refused`: `λ(h : linear Nat). {kept = 1, held = h}.kept` is `linearProjected [0] 0`
(`#tooth` by mutating the quantity to `affine` bites); `sibling_projection_affine_accepted`.
`CheckTeeth.affine_in_two_arms_refused` (pinning "arms are additive") is now
`affine_in_two_arms_accepted`, with `affine_in_scrutinee_and_arm_refused` keeping the additive half.

**Cohorts and receipts unchanged**: probes 30/30, tutorial 71/71 (the three chapter-7 deviations of
round 1 and no new one), preview 161/161, receipts 22/22. Census: 33928 constants, none on `sorryAx`
or a declared axiom, 27 on the compiler trust.

**Journal** (`3408ea3` → round 2, base moved by `fdf6fc4`): this round's revised statements are
`infer_msubst`, `partialTyping_msubst`, `completes_get/reflect/metadata/project/ifBool/ifZero`,
`arms_cons_complete`, `motive_get`, `motive_ifBool`, `armsMotive_cons`, `get_bound_checks`,
`width_fields_check`; the `Receipt.*` revisions in the same diff are the base's.

## What remains (INFERRED)

The count is still syntactic and the machine does not track it: a divergent body never reaches its
use (`safeQuantity` docstring), and a `linear` hypothesis put in a record or variant is discharged by
being stored there, whatever later happens to the record (its type carries no quantity). The paper's
`paper/objective-bend.md:384` and `GROUNDING.md:60` still say "linear means at most once".
