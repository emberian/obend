module
public import Obend.Core.SubstitutionExposure
public import Obend.Core.TypeGraphAlias
public import Obend.AxiomPin
@[expose] public section
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

public theorem residual_exposed_field {a : Assumptions} {row member tail : Ty} {name : String}
    (observed : expose a row = .constructor ⟨.field name, [member, tail]⟩) :
    residual a row = residual a tail := by
  have heads : expose a row = expose a (.field name member tail) :=
    observed.trans (raw_field_observation a name member tail).symm
  exact (residual_expose_eq a row (.field name member tail) _ observed heads rfl).trans
    (residual_field a name member tail)

public theorem scanStream_residual_emit
    (a : Assumptions) (remaining : List Ty) (row : Ty) (label : String) (first : Bool)
    (member tail : Ty) (emitted : scanStream a remaining label first row = .emit member tail) :
    residual a row = residual a tail := by
  rw [scanStream] at emitted
  split at emitted
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at emitted
    · contradiction
    · rename_i name current fieldTail tag children
      have shape : observation = ⟨.field name, [current, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have step := residual_exposed_field exposed
      split at emitted
      · rename_i present
        split at emitted
        · cases emitted
          exact step
        · exact step.trans (scanStream_residual_emit a (remaining.erase row)
            fieldTail label first member tail emitted)
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

public theorem residual_emit {a : Assumptions} {row : Ty} {label : String} {first : Bool}
    {member tail : Ty} (emitted : streamStep a row label first = .emit member tail) :
    residual a row = residual a tail :=
  scanStream_residual_emit a _ row label first member tail emitted

public theorem residual_skip {a : Assumptions} {row tail : Ty} {label : String} {first : Bool}
    (skipped : Obend.Core.TypeGraph.RowHit.step a label first row = .skip tail) :
    residual a row = residual a tail := by
  rw [Obend.Core.TypeGraph.RowHit.step] at skipped
  split at skipped
  · rename_i observation exposed
    split at skipped
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name, [member, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at skipped
      · contradiction
      · cases skipped
        exact residual_exposed_field exposed
    · contradiction
  · contradiction

/-- Residuals retain raw syntax only for non-row terminals. Those payloads
are compared by the type graph rather than by syntactic equality. -/
public inductive ResidualRelated (a : Assumptions) : Tail → Tail → Prop where
  | closed : ResidualRelated a .closed .closed
  | productiveCycle : ResidualRelated a .productiveCycle .productiveCycle
  | nominal (index : Nat) : ResidualRelated a (.nominal index) (.nominal index)
  | unproductive (index : Nat) : ResidualRelated a (.unproductive index) (.unproductive index)
  | nonRow {left right : Ty} : Obend.Core.TypeGraph.Equivalent a left right →
      ResidualRelated a (.nonRow left) (.nonRow right)

public theorem ResidualRelated.refl (a : Assumptions) (tail : Tail) :
    ResidualRelated a tail tail := by
  cases tail with
  | closed => exact .closed
  | productiveCycle => exact .productiveCycle
  | nominal index => exact .nominal index
  | unproductive index => exact .unproductive index
  | nonRow t => exact .nonRow (Obend.Core.TypeGraph.equivalent_of_expose_eq rfl)

public theorem residual_nonrow {a : Assumptions} {row : Ty} {c : Constructor}
    (observed : expose a row = .constructor c)
    (nonrow : Obend.Core.TypeGraph.rowTag c.tag = false) :
    residual a row = .nonRow row := by
  rw [residual, scanResidual, observed]
  cases c with
  | mk tag children => cases tag <;> simp_all [Obend.Core.TypeGraph.rowTag]

public theorem residual_related_of_expose_eq {a : Assumptions} {left right : Ty}
    (heads : expose a left = expose a right) :
    ResidualRelated a (residual a left) (residual a right) := by
  cases exposed : expose a left with
  | nominal index =>
    have other : expose a right = .nominal index := heads.symm.trans exposed
    simp only [residual, scanResidual, exposed, other]
    exact .nominal index
  | unproductive index =>
    have other : expose a right = .unproductive index := heads.symm.trans exposed
    simp only [residual, scanResidual, exposed, other]
    exact .unproductive index
  | constructor c =>
    have other : expose a right = .constructor c := heads.symm.trans exposed
    by_cases row : Obend.Core.TypeGraph.rowTag c.tag = true
    · rw [residual_expose_eq a left right c exposed heads row]
      exact .refl _ _
    · have nonrow : Obend.Core.TypeGraph.rowTag c.tag = false := by
        cases h : Obend.Core.TypeGraph.rowTag c.tag <;> simp_all
      rw [residual_nonrow exposed nonrow, residual_nonrow other nonrow]
      exact .nonRow (Obend.Core.TypeGraph.equivalent_of_expose_eq heads)

#assert_axioms residual_exposed_field scanStream_residual_emit residual_emit residual_skip
  ResidualRelated.refl residual_nonrow residual_related_of_expose_eq
end Obend.Core.RecursiveRows
