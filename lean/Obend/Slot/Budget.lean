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
def toyBudget (view : Nat) : Core4.Budget := ⟨if view = 0 then 1 else 1 + 3⟩

def budgetType : Ty := .arrow .reusable .unrestricted .natural .natural

def budgetSlot (view : Nat) : Slot Member AnnotatedTerm :=
  Core4.slotOf (toyBudget view) fuelContext budgetType (fun _ => [.bob])

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
    sameType_refl, safeUses, safeQuantity, Quantity.fits, linearFree, validContext, reusableAllowed,
    reusableCaptures, zeroUses, variableUses, addUses, Ty.shareableUnder,
    Ty.shareable, Ty.isComputation, Assumptions.valid,
    List.range_succ, List.zipWith, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Except.toBool, pure, Except.pure]

/-- The same filling has live supports at both views. The short grant refuses
by name; the combined grant makes it usable. This is a budget tooth, not a
counterexample to semantic substitution. -/
theorem budget_tooth :
    (budgetSlot 1).usable (World.holdsAt 1) fuelFilling = true ∧
    (match Core4.admit (toyBudget 0) fuelContext budgetType fuelFilling with
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
    Core4.admit (toyBudget 0) fuelContext budgetType fuelFilling = .error (.uncovered 1) := rfl

theorem budget_filling_typed : Core4.Typed fuelContext fuelFilling budgetType :=
  (Core4.slotOf_usable (toyBudget 1) fuelContext budgetType (fun _ => [Member.bob])
    (World.holdsAt 1) fuelFilling budget_tooth.1).1

end BudgetFixtures

/-! ## The integrity-preserving filler on a checker's slot -/

section
variable {V Fact : Type} [World V Fact]
open World

/-- A Core4 filling selected by the integrity-preserving filler has semantic typing, independently
of the budget used to discover its certificate. -/
theorem slotFiller_typed (budget : Core4.Budget) (Ψ : Context) (A : Ty)
    (supports : AnnotatedTerm → List Fact) (v : V) (order : List AnnotatedTerm) (t : AnnotatedTerm)
    (h : (slotFiller : Filler V Fact AnnotatedTerm).fill
      (Core4.slotOf budget Ψ A supports) v order = .ok t) : Core4.Typed Ψ t A := by
  obtain ⟨_, hu, _⟩ := select_ok h
  exact (Core4.slotOf_usable budget Ψ A supports (holdsAt v) t hu).1

/-- When a budgeted slot refuses a candidate whose ordinary supports all hold, its named
explanation is precisely `uncovered` at the declared grade. This connects admission diagnostics to
the actual integrity-preserving filler. -/
theorem slotFiller_uncovered (budget : Core4.Budget) (Ψ : Context) (A : Ty)
    (supports : AnnotatedTerm → List Fact) (v : V) (order : List AnnotatedTerm) (t : AnnotatedTerm)
    (w : Refusal Fact AnnotatedTerm)
    (h : (slotFiller : Filler V Fact AnnotatedTerm).fill
      (Core4.slotOf budget Ψ A supports) v order = .error w)
    (member : t ∈ order) (live : ∀ f ∈ supports t, holdsAt v f = true) :
    Core4.admit budget Ψ A t = .error (.uncovered budget.grade) := by
  have refused := (select_error h).1 t member
  have dead : (Core4.slotOf budget Ψ A supports).dead (holdsAt v) t = [] :=
    (dead_eq_nil_iff _ _ _).2 live
  unfold Slot.usable at refused
  rw [dead] at refused
  have checkFalse : Core4.judge budget.grade Ψ t A = false := by
    simpa only [Core4.slotOf, List.isEmpty_nil, Bool.and_true] using refused
  simp [Core4.admit, checkFalse]

end

end Obend.Slot
