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

## What exact discharge does not yet cover (INFERRED)

The count is syntactic. A `linear` hypothesis used in one branch of `ifBool`/`ifZero`/`case` counts one
(branches add), so it passes the binder and is dropped on the other path; used in both it counts two and
is refused, so a `linear` binder cannot be consumed on every path. A `linear` hypothesis put in a record
whose sibling is projected (`{a = h, b = 1}.b`) passes too. `GROUNDING.md:60` and
`paper/objective-bend.md:384` still say "linear means at most once"; not edited (outside `lean/`).

## The decision for Ember

Branches: should a `linear` binder's count combine across `ifBool`/`ifZero`/`case` arms by equality
(each arm uses it exactly as often as the others, the additive rule of linear logic) instead of by sum?
That changes `addUses` at three rules for `linear` positions only, closes the branch drop, and is what
T7's usage composition will otherwise inherit as an unsound case.
