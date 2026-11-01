module
/-
# Obend.Lower.Proofs.Complete — where the converse of `lower_sound` breaks

`lower_complete` would be the converse of `lower_sound_nat`: `Evaluates (lowerT e) (nat n) →
SSteps e (lit n)`. It is false on the simply typed fragment, and the term where it breaks is an
erasure: the recursor of a field-less proposition applied to a proof (`tests/lower/Programs.lean`
`kTooth`: `Witness.rec n Witness.mk`). The proof is erased to `{}`, which *is* the empty record the
lowered destructor wants, so Core4 runs `split {} [] n` to `n`; the source semantics has no rule for a
structure's recursor on a non-constructor major and is stuck. Lean's kernel reduces it (the recursor
is K-like, `toCtorWhenK`, and `kTooth_three` is `rfl`), so the gap is the source semantics', not
Core4's: with the K rule for field-less structures (`split [] F erased ↦ F`) this term is matched.
The remaining obstacle to `lower_complete` is not erasure but proof technique: the backward direction
needs a step-indexed form of `Ahead`, since the term behind may take more steps than the term ahead.
-/
public import Obend.Lower.Proofs.Sound
public import Obend.Lower.Typing
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
set_option autoImplicit false

/-- `Witness.rec 5 Witness.mk`, read: the destructor of a field-less structure on an erased proof. -/
def erasedRec : LExpr := .split [] (.lit 5) .erased

theorem erasedRec_typed : LTyped [] erasedRec .natural :=
  .split (Ts := []) rfl List.nodup_nil (by simp) (.erased _) (.lit _ _)

theorem erasedRec_lowered : Evaluates (lowerT erasedRec) (.nat 5) := by
  simp only [erasedRec, lowerT, box]
  exact ⟨.next (.splitRecord _ _ _ [] rfl) (.refl _), .natural 5⟩

theorem erasedRec_stuck : ∀ e', ¬ SStep erasedRec e' := by
  intro e' h
  cases h with
  | splitMajor _ _ s => cases s

/-- **The converse fails on the typed fragment, at an erasure.** -/
theorem lower_complete_fails :
    ¬ ∀ (e : LExpr) (n : Nat), LTyped [] e .natural → Evaluates (lowerT e) (.nat n) → SSteps e (.lit n) := by
  intro claim
  have run := claim erasedRec 5 erasedRec_typed erasedRec_lowered
  cases run with
  | next s _ => exact erasedRec_stuck _ s

end Obend.Lower
end
