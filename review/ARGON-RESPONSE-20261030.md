# Gemini Argon on the checker's incompleteness: what we checked, what we take

Argon's analysis (pasted by Ember, 2026-10-30) answered `CHECKER-COMPLETENESS-REPORT-20261030.md`.
Each claim below was checked against `lean/Obend/Core/Check.lean` at `c058ea6` before being accepted.

## Checked and accepted

1. **`uses` is already a synthesized output.** Every `PartialTyping` rule returns its uses vector
   bottom-up (`addUses functionUses argumentUses` at `application`, `uses.tail` at `lambda`, one-hot
   at `bound`). There is no top-down split to guess, so the report's §8 proposal to move usage
   accounting to a separate pass or to `omega` was wrong. Usage synthesis stays inside the
   bidirectional checker, and an unannotated lambda in checking mode gets its principal
   `(quantity, reuse)` from `(u_head, u_tail)`.
2. **`sameType` is not an equivalence.** `sameType a e := a.canonical == e.canonical || (a is an
   alias variable whose bound canonicalizes to e) || (symmetrically)`: one head unfolding, one side,
   no descent. `α₁ := Nat`, `α₂ := Nat` gives `sameType α₁ α₂ = false`; `α → Bool` versus
   `Nat → Bool` is never unfolded. Proving `Equivalence (sameType …)` as the report's §8 proposed
   would have failed on transitivity. The fix is Argon's: aliases unfold hereditarily and
   structurally on both sides, with a visited set bounding the walk if bounds are cyclic; rigid
   variables stay nominal with directional `lookup` through the lower bound.
3. **The branch join uses exact equality where the relation allows a conversion.** `infer`'s
   `.ifBool` case (Check.lean ~548) finishes with `hc ▸ c.derivation` and `hb ▸ f.derivation`;
   `inferArms` requires `later.result = first.type`. Replacing those with `sameType` plus
   `PartialTyping.conversion` retires counterexample 2 in the current checker before any redesign.
4. **`Covered` cannot be a syntactic predicate on the current checker**, because counterexample 2
   is fully annotated and whether it checks depends on how a context type is spelled. Once joins go
   through `sameType`, the fragment is syntactic: `synthCovered`/`checkCovered` as Argon wrote them,
   and because a slot filling is always checked against the slot's declared type, the top level is
   checking mode and `Covered := checkCovered`, under which a closed unannotated lambda needs no
   annotation at all.
5. **Two completeness theorems**, not one: direct completeness of the bidirectional checker on the
   `checkCovered` fragment, and full completeness via `annotateFromDerivation : PartialTyping … →
   AnnotatedTerm` whose output erases to the raw term and lies in the fragment. The second is what
   makes "complete for all of `PartialTyping`" true in the only sense the kernel needs.
6. **Refusals name the rule and the edit**: `check : … → Except CheckRefusal Checked` with
   constructors such as `missingLambdaAnnotation path`, `typeMismatch path expected actual`,
   `affineBinderOverused path idx n`, `emptyCaseInSynthMode path`.
7. **The two-tier architecture** (a local elaborator that unifies and grades, a kernel checker that
   verifies annotated terms with no search) is the project's own trust rule applied, and matches
   `Decides` with the budget as a support.

## Checked and corrected

- Rigid variables are already nominal in the data: `Assumptions.alias` returns `none` for an index
  in `rigid`, so `sameType` never equates a rigid variable with its bound. The conflation Argon
  describes is confined to the one-step bound on transparent aliases.
- `inject` already carries an annotation in the typed packet (one per `inject`, per
  `OBJECTIVE-BEND-FRONTEND.md`), and `infer`'s `.fix` case already inserts a conversion. Argon's
  "fourth and fifth counterexamples" are therefore pre-empted for annotated terms, and right for
  the bare-term fragment `synthCovered` describes.
- `PartialTyping` sums branch uses (`addUses tu fu` at `ifBool`, `ArmsTyping` likewise) rather
  than taking the pointwise maximum Argon recommends for additive control flow. The sum is sound and
  refuses `if c then x else x` for an affine `x`. Whether to relax to `max` is a design decision
  about the relation, not the checker, and is recorded here rather than taken.

## Precedents Argon names, to read before the lane writes code

Dunfield–Krishnaswami, *Bidirectional Typing* (CSUR 2021; POPL 2013) for annotatability;
Lennon-Bertrand, *Complete Bidirectional Typing for CIC* (2022, MetaCoq) for the same three
obstructions and their repair; Pierce–Turner, *Local Type Inference* (TOPLAS 2000); Wood–Atkey,
*A Linear Algebra Approach to Linear Metatheory* (ESOP 2022) for usage vectors as outputs;
Amadio–Cardelli and Brandt–Henglein for coinductive row equality with a visited set.

## The order the checker lane follows

1. `sameType` and rows: separate transparent aliases from rigid bounds; hereditary structural
   unfolding with a visited set; `Equivalence (sameType …)` proved; `lookup`/`isRow` fuel replaced
   by the visited-set bound; one canonical duplicate-label semantics shared by relation and checker.
2. The quick fix in the existing checker: `sameType` plus `conversion` at every join (`ifBool`,
   `inferArms`, application argument), so counterexample 2 falls now; the journal measures the cascade.
3. The bidirectional checker beside the old: `infer` and `checkAgainst`, `Except CheckRefusal
   Checked`, uses synthesized inline, native `checkAgainst` clauses for `lam`, `ifBool`, `case`,
   `inject`, `fix`, `extend`, conversion at the mode switch.
4. `Covered := checkCovered`, the direct completeness theorem for it by induction on
   `PartialTyping`, and `annotateFromDerivation` with the full completeness corollary.
5. Swap through `Decides`; the slot's `Covered` becomes the syntactic predicate; the old
   `Recognized` is deleted.
