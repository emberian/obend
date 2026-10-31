module
public import Obend.Core.Proofs.Templates
public import Obend.Core.EquiRecursiveAgreement
@[expose] public section
namespace Obend.Core.EquiRecursiveSubstitution
open Obend.Core.Ty Obend.Core.Check Obend.Core.Proofs.Templates
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Without validated environments, a rigid shareability premise can be discharged by a syntactically
shareable variable whose transparent alias actually exposes custody. -/
def template : Assumptions :=
  ⟨[(1,.custody 7)],[0,1],[0]⟩

def instance_ : Assumptions :=
  ⟨[(1,.custody 7)],[1],[]⟩

def substitution (index : Nat) : Ty :=
  if index = 0 then .variable 1 else .variable index

theorem discharged : Discharges substitution template instance_ 0 where
  fixed := by
    intro j absent
    have different : j ≠ 0 := by simpa [template] using absent
    simp [substitution,different]
  bounds := by intro j _; rfl
  aliases := by
    intro j absent
    have different : j ≠ 0 := by simpa [template] using absent
    simp [Assumptions.alias,template,instance_,different,Bool.beq_eq_decide_eq]
  closed := by
    intro j bound _ found
    have same : bound = .custody 7 := by
      by_cases equal : j = 1
      · simpa [template,List.lookup,equal] using found.symm
      · simp [template,List.lookup,equal,Bool.beq_eq_decide_eq] at found
    subst bound
    rfl
  lookup := by
    intro k bound rigid found
    have same : k = 0 := by simpa [template] using rigid
    subst k
    simp [template,List.lookup] at found
  row := by
    intro k bound rigid found
    have same : k = 0 := by simpa [template] using rigid
    subst k
    simp [template,List.lookup] at found
  shareable := by
    intro j
    by_cases zero : j = 0
    · subst j
      decide
    · simp [substitution,zero,Ty.shareableUnder,template,instance_,
        Bool.beq_eq_decide_eq]
  pure := by
    intro j
    by_cases zero : j = 0 <;> simp [substitution,zero,Ty.isComputation]

def actual : Ty := .field "a" .natural (.field "a" (.variable 0) .emptyRow)
def expected : Ty := .field "a" .natural .emptyRow

open Obend.Core.TypeGraph Obend.Core.AliasExposure

private theorem rigid_zero_shareable (a : Assumptions)
    (rigid : a.rigid.contains 0 = true) (listed : a.shareableVariables.contains 0 = true) :
    RR.shareable a (.variable 0) = true := by
  apply Obend.Core.RecursiveRows.shareable_terminal
  have member : 0 ∈ a.shareableVariables := by simpa using listed
  simp [Obend.Core.ResourceSemantics.head,expose_rigid a 0 rigid,member]

theorem template_agreement :
    Obend.Core.EquiRecursiveAgreement.agrees template actual expected = true := by
  apply (Obend.Core.EquiRecursiveAgreement.agrees_iff _ _ _).mpr
  exact semantic_field_shadow template "a" .natural (.variable 0) .emptyRow
    (rigid_zero_shareable template (by decide) (by decide))

theorem invalid_image_resource : RR.shareable instance_ (.variable 1) = false := by
  apply Obend.Core.RecursiveRows.shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,instance_,expose,exposeWalk,
    Assumptions.alias,constructorHead,Ty.isComputation,List.lookup]

theorem instance_disagreement :
    Obend.Core.EquiRecursiveAgreement.agrees instance_
      (actual.instantiate substitution) (expected.instantiate substitution) = false := by
  cases outcome : Obend.Core.EquiRecursiveAgreement.agrees instance_
      (actual.instantiate substitution) (expected.instantiate substitution) with
  | false => rfl
  | true =>
    have resources := equivalent_shareable
      ((Obend.Core.EquiRecursiveAgreement.agrees_iff _ _ _).mp outcome)
    simp [actual,expected,Ty.instantiate,substitution,
      Obend.Core.RecursiveRows.shareable_field,invalid_image_resource] at resources

theorem counterexample_environments_invalid : template.valid = false ∧ instance_.valid = false := by decide

theorem discharges_not_substitution_stable :
    ∃ (σ : Nat → Ty) (a b : Assumptions) (x y : Ty),
      Discharges σ a b 0 ∧
      Obend.Core.EquiRecursiveAgreement.agrees a x y = true ∧
      Obend.Core.EquiRecursiveAgreement.agrees b (x.instantiate σ) (y.instantiate σ) = false :=
  ⟨substitution,template,instance_,actual,expected,discharged,template_agreement,instance_disagreement⟩

def validTemplate : Assumptions := ⟨[(0,.natural),(1,.variable 1)],[0,1],[0]⟩
def validInstance : Assumptions := ⟨[(1,.variable 1)],[1],[]⟩

theorem valid_discharged : Discharges substitution validTemplate validInstance 0 where
  fixed := by
    intro j absent
    have different : j ≠ 0 := by simpa [validTemplate] using absent
    simp [substitution,different]
  bounds := by
    intro j absent
    have different : j ≠ 0 := by simpa [validTemplate] using absent
    simp [validTemplate,validInstance,List.lookup,different,Bool.beq_eq_decide_eq]
  aliases := by
    intro j absent
    have different : j ≠ 0 := by simpa [validTemplate] using absent
    simp [Assumptions.alias,validTemplate,validInstance,List.lookup,different,Bool.beq_eq_decide_eq]
  closed := by
    intro j bound absent found
    have different : j ≠ 0 := by simpa [validTemplate] using absent
    have same : bound = .variable 1 := by
      by_cases equal : j = 1
      · simpa [validTemplate,List.lookup,equal] using found.symm
      · simp [validTemplate,List.lookup,different,equal,Bool.beq_eq_decide_eq] at found
    subst bound
    decide
  lookup := by
    intro k bound rigid found
    have same : k = 0 := by simpa [validTemplate] using rigid
    subst k
    have same : bound = .natural := by simpa [validTemplate,List.lookup] using found.symm
    subst bound
    intro fuel name member impossible
    cases fuel <;> simp [Ty.lookup] at impossible
  row := by
    intro k bound rigid found
    have same : k = 0 := by simpa [validTemplate] using rigid
    subst k
    have same : bound = .natural := by simpa [validTemplate,List.lookup] using found.symm
    subst bound
    intro fuel impossible
    cases fuel <;> simp [Ty.isRow] at impossible
  shareable := by
    intro j
    by_cases zero : j = 0
    · subst j; decide
    · simp [substitution,zero,Ty.shareableUnder,validTemplate,validInstance,
        Bool.beq_eq_decide_eq]
  pure := by
    intro j
    by_cases zero : j = 0 <;> simp [substitution,zero,Ty.isComputation]

theorem valid_environments : validTemplate.valid = true ∧ validInstance.valid = true := by decide


/-- With greatest resource safety, the alias-only cycle is safe. This former
counterexample now transports successfully without a new discharge premise. -/
theorem valid_image_resource : RR.shareable validInstance (.variable 1) = true := by
  apply Obend.Core.RecursiveRows.shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,validInstance,expose,exposeWalk,
    Assumptions.alias,constructorHead,cycleRepresentative,Ty.isComputation,List.lookup]

theorem valid_template_agreement :
    Obend.Core.EquiRecursiveAgreement.agrees validTemplate actual expected = true := by
  apply (Obend.Core.EquiRecursiveAgreement.agrees_iff _ _ _).mpr
  exact semantic_field_shadow validTemplate "a" .natural (.variable 0) .emptyRow
    (rigid_zero_shareable validTemplate (by decide) (by decide))

theorem valid_instance_agreement :
    Obend.Core.EquiRecursiveAgreement.agrees validInstance
      (actual.instantiate substitution) (expected.instantiate substitution) = true := by
  apply (Obend.Core.EquiRecursiveAgreement.agrees_iff _ _ _).mpr
  simpa only [actual,expected,Ty.instantiate,substitution,if_pos rfl,ite_true] using
    semantic_field_shadow validInstance "a" .natural (.variable 1) .emptyRow valid_image_resource

#assert_axioms discharged template_agreement invalid_image_resource instance_disagreement
  counterexample_environments_invalid discharges_not_substitution_stable valid_discharged
  valid_environments valid_image_resource valid_template_agreement valid_instance_agreement
end Obend.Core.EquiRecursiveSubstitution
