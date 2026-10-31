module
public import Obend.Slot.Core4
public import Obend.Slot.Integrity

@[expose] public section
namespace Obend.Slot
open Obend.Core.Check Obend.Core.Ty
open Obend.Core.Proofs.Substitution

/-- The toy World declares the grant available at a view. Retirement and typing
remain their existing meanings; this grant prices one checker invocation in
`Obend.Elab.Work.checkWork` units: the filling's two nodes plus the two types of the
annotation the checker reads at its lambda cost four. -/
def toyBudget (view : Nat) : Budget Nat := ⟨if view = 0 then 1 else 1 + 3⟩

def budgetType : Ty := .arrow .reusable .unrestricted .natural .natural

def budgetSlot (view : Nat) : Slot Member AnnotatedTerm :=
  Calculus.slotOf (toyBudget view) fuelContext budgetType (fun _ => [.bob])

section BudgetFixtures
attribute [local irreducible] Obend.Core.Check.sameType
  Obend.Core.EquiRecursiveAgreement.agrees Obend.Core.TypeGraph.candidate
attribute [local congr] Obend.Tactic.MonadicReduction.except_bind_source_congr
  Obend.Tactic.MonadicReduction.except_map_source_congr
attribute [local simp ↓] Obend.Tactic.MonadicReduction.except_monad_bind
  Obend.Tactic.MonadicReduction.except_functor_map
attribute [local simp] Obend.Tactic.MonadicReduction.except_bind_ok
  Obend.Tactic.MonadicReduction.except_bind_error
  Obend.Tactic.MonadicReduction.except_map_ok
  Obend.Tactic.MonadicReduction.except_map_error

/-- The four-unit grant admits the filling through the single bidirectional judge. -/
theorem budget_filling_admitted : Core4.judge 4 fuelContext fuelFilling budgetType = true := by
  simp [Core4.judge, Core4.checkWork, Obend.Elab.Work.checkWork, Obend.Elab.Work.termWork,
    Obend.Elab.Work.annotationWork, Obend.Elab.Work.tyNodes, fuelContext, fuelFilling, budgetType,
    Obend.Core.Bidirectional.checkAgainst, Obend.Core.Bidirectional.checkAt,
    Obend.Core.Bidirectional.elaborate, Obend.Core.Bidirectional.finish,
    Obend.Core.Bidirectional.checkedSynth, Obend.Core.Bidirectional.need,
    sameType_refl, safeUses, safeQuantity, validContext, reusableAllowed,
    reusableCaptures, zeroUses, variableUses, addUses, Ty.shareableUnder,
    Ty.shareable, Ty.isComputation, Assumptions.valid,
    List.range_succ, List.zipWith, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Except.toBool, pure, Except.pure]

/-- The same filling has live supports at both views. The short grant refuses
by name; the combined grant makes it usable. This is a budget tooth, not a
counterexample to semantic substitution. -/
theorem budget_tooth :
    (budgetSlot 1).usable (World.holdsAt 1) fuelFilling = true ∧
    (match Calculus.admit (toyBudget 0) fuelContext budgetType fuelFilling with
      | .error (.uncovered r) => r == 1
      | .ok _ => false) = true := by
  constructor
  · apply (usable_iff _ _ _).2
    constructor
    · change Core4.judge 4 fuelContext fuelFilling budgetType = true
      exact budget_filling_admitted
    · intro member supported
      change member ∈ [Member.bob] at supported
      simp only [List.mem_singleton] at supported
      subst member
      rfl
  · rfl

theorem budget_uncovered :
    Calculus.admit (toyBudget 0) fuelContext budgetType fuelFilling = .error (.uncovered 1) := rfl

theorem budget_filling_typed : Calculus.Typed fuelContext fuelFilling budgetType :=
  (Calculus.slotOf_usable (Tm := AnnotatedTerm) (toyBudget 1) fuelContext budgetType (fun _ => [Member.bob])
    (World.holdsAt 1) fuelFilling budget_tooth.1).1

end BudgetFixtures

#assert_axioms budget_filling_admitted budget_tooth budget_uncovered budget_filling_typed
end Obend.Slot
