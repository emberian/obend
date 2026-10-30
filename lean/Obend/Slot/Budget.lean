module
public import Obend.Slot.Core4
public import Obend.Slot.Integrity

@[expose] public section
namespace Obend.Slot
open Obend.Core.Check Obend.Core.Ty
open Obend.Core.Proofs.Substitution

/-- The toy World declares the grant available at a view. Retirement and typing
remain their existing meanings; this grant prices one checker invocation. -/
def toyBudget (view : Nat) : Budget Nat := ⟨if view = 0 then 1 else 1 + 1⟩

def budgetType : Ty := .arrow .reusable .unrestricted .natural .natural

def budgetSlot (view : Nat) : Slot Member AnnotatedTerm :=
  Calculus.slotOf (toyBudget view) fuelContext budgetType (fun _ => [.bob])

/-- The same filling has live supports at both views. The short grant refuses
by name; the combined grant makes it usable. This is a budget tooth, not a
counterexample to semantic substitution. -/
theorem budget_tooth :
    (budgetSlot 1).usable (World.holdsAt 1) fuelFilling = true ∧
    (match Calculus.admit (toyBudget 0) fuelContext budgetType fuelFilling with
      | .error (.uncovered r) => r == 1
      | .ok _ => false) = true := by decide

theorem budget_uncovered :
    Calculus.admit (toyBudget 0) fuelContext budgetType fuelFilling = .error (.uncovered 1) := rfl

theorem budget_filling_typed : Calculus.Typed fuelContext fuelFilling budgetType :=
  (Calculus.slotOf_usable (Tm := AnnotatedTerm) (toyBudget 1) fuelContext budgetType (fun _ => [Member.bob])
    (World.holdsAt 1) fuelFilling budget_tooth.1).1

#assert_axioms budget_tooth budget_uncovered budget_filling_typed
end Obend.Slot
