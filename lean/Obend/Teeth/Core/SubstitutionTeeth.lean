module
/- The three corners of the substitution lemma (`Obend.Core.Proofs.Substitution`), each with a tooth:
fillings must be closed, fillings check under the template's assumptions, and the fuel adds. -/
public import Obend.Tactic.Tooth
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Substitution.Msubst
namespace Obend.Core.Proofs.Substitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant
set_option autoImplicit false

/-! ## Teeth: the three corners, each a refusal `decide` computes -/

theorem fuel_template_checks : (check fuelTemplate fuelContext 2).isSome = true := by
  simp [fuelTemplate, fuelContext, check, infer, agree, sameType_refl, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures, zeroUses, variableUses,
    addUses, Ty.shareableUnder, Ty.shareable, Ty.isComputation,
    Assumptions.valid, List.range_succ, List.zipWith, List.getElem?_cons_zero, List.getElem?_cons_succ]
theorem fuel_filling_checks : (check fuelFilling fuelContext 2).isSome = true := by
  simp [fuelFilling, fuelContext, check, infer, agree, sameType_refl, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures, zeroUses, variableUses,
    addUses, Ty.shareableUnder, Ty.shareable, Ty.isComputation,
    Assumptions.valid, List.range_succ, List.zipWith, List.getElem?_cons_zero, List.getElem?_cons_succ]
theorem msubst_fuel : msubst (fillZero fuelFilling) fuelTemplate =
    ⟨.lam (.lam (.bound 0)), annotationsAt (fillZero fuelFilling) fuelTemplate.annotations 0 [] fuelTemplate.term, {}⟩ := by
  have e : (msubst (fillZero fuelFilling) fuelTemplate).term = .lam (.lam (.bound 0)) := by
    simp [msubst, Term.substitute, liftSubstitution, fillTerm, fillingAt, fillZero, fuelTemplate, fuelFilling, Term.rename,
      liftRename]
  rw [← e]; rfl
/-- TOOTH (the fuel adds). Template and filling each check at fuel 2; the filled term is refused at
fuel 2 and accepted at 3. `check_msubst` promises fuel `2 + 2`; a fixed fuel limits procedural admission, not fuel-free semantic substitution
(`Obend.Slot.Core4.calculus_typed_msubst`). -/
theorem fuel_tooth :
    (check (msubst (fillZero fuelFilling) fuelTemplate) fuelContext 2).isNone = true ∧
    (check (msubst (fillZero fuelFilling) fuelTemplate) fuelContext 3).isSome = true := by
  rw [msubst_fuel]
  constructor
  · decide
  · -- Only these two annotation addresses are consumed. Kernel reduction at
    -- concrete paths avoids importing annotationsAt's generated splitters into
    -- the stored proof checked by the mutation tooth.
    have outer : annotationsAt (fillZero fuelFilling) fuelTemplate.annotations 0 []
        fuelTemplate.term [] =
        some ⟨.natural, .arrow .reusable .unrestricted .natural .natural,
          .unrestricted, .reusable⟩ := rfl
    have inner : annotationsAt (fillZero fuelFilling) fuelTemplate.annotations 0 []
        fuelTemplate.term [0] =
        some ⟨.natural, .natural, .unrestricted, .reusable⟩ := rfl
    simp [outer, inner, fuelContext, check, infer, agree, sameType_refl, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures, zeroUses, variableUses,
    addUses, Ty.shareableUnder, Ty.shareable, Ty.isComputation,
    Assumptions.valid, List.range_succ, List.zipWith, List.getElem?_cons_zero, List.getElem?_cons_succ]

#tooth fuel_tooth by mutation fuelFilling := ⟨.nat 0, fun _ => none, {}⟩

theorem linear_template_checks : (check linearTemplate linearContext 4).isSome = true := by decide
theorem linear_filling_checks : (check linearFilling linearContext 4).isSome = true := by decide
theorem linear_filling_open : ¬ Scoped 0 linearFilling.term := by
  intro h; have := (scoped_bound_iff _ _).1 h; omega
theorem msubst_linear : msubst (fillZero linearFilling) linearTemplate =
    ⟨.binary .add (.bound 1) (.bound 1), annotationsAt (fillZero linearFilling) linearTemplate.annotations 0 []
      linearTemplate.term, {}⟩ := by
  have e : (msubst (fillZero linearFilling) linearTemplate).term = .binary .add (.bound 1) (.bound 1) := by
    simp [msubst, Term.substitute, fillTerm, fillingAt, fillZero, linearTemplate, linearFilling]
  rw [← e]; rfl
/-- TOOTH (fillings are closed). An OPEN filling (`bound 1`, the linear hypothesis) checks at the type
of hypothesis `0`, and the template checks; the filled term uses the linear hypothesis twice and is
refused. `Scoped 0` on the fillings is load-bearing. -/
theorem open_filling_tooth : (check (msubst (fillZero linearFilling) linearTemplate) linearContext 4).isNone = true := by
  rw [msubst_linear]; decide

#tooth open_filling_tooth by mutation linearFilling := ⟨.nat 0, fun _ => none, {}⟩

theorem alias_filling_checks : (check aliasFilling aliasContext 4).isSome = true := by
  have aliased : sameType (⟨[(0, .variant sumRow)], [], []⟩ : Assumptions)
      (.variant sumRow) (.variable 0) = true := sameType_extends (by decide)
  dsimp only [sumRow] at aliased
  simp [aliasFilling, aliasContext, sumAssumptions, sumRow, Assumptions.alias,
    Ty.lookup, List.lookup, aliased, check, infer, agree, sameType_refl, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures, zeroUses, variableUses,
    addUses, Ty.shareableUnder, Ty.shareable, Ty.isComputation,
    Assumptions.valid, List.range_succ, List.zipWith, List.getElem?_cons_zero, List.getElem?_cons_succ]
theorem alias_template_checks : (check aliasTemplate aliasContext 4).isSome = true := by decide
theorem alias_filling_closed : Scoped 0 aliasFilling.term := .inject (.natural _)
theorem msubst_alias : msubst (fillZero aliasFilling) aliasTemplate =
    ⟨.inject "l" (.nat 1), annotationsAt (fillZero aliasFilling) aliasTemplate.annotations 0 [] aliasTemplate.term, {}⟩ := by
  have e : (msubst (fillZero aliasFilling) aliasTemplate).term = .inject "l" (.nat 1) := by
    simp [msubst, Term.substitute, fillTerm, fillingAt, fillZero, aliasTemplate, aliasFilling]
  rw [← e]; rfl
/-- TOOTH (fillings check under the template's assumptions). The filling checks under ITS assumptions
(a bound for type variable `0`, so its injection converts to the declared sum) at the hypothesis's
type; `msubst` keeps the template's assumptions, which have no bound, and the filled term is refused.
This is why `check_msubst` judges a filling as `{ f with assumptions := t.assumptions }`. -/
theorem assumptions_tooth : (check (msubst (fillZero aliasFilling) aliasTemplate) aliasContext 4).isNone = true := by
  rw [msubst_alias]; decide

#tooth assumptions_tooth by mutation aliasFilling := aliasTemplate

end Obend.Core.Proofs.Substitution
