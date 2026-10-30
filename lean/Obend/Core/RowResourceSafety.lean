module
public import Obend.Core.WeightedResource
@[expose] public section
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

theorem exposed_field_shareable {a : Assumptions} {row member tail : Ty} {name : String}
    (observed : expose a row = .constructor ⟨.field name,[member,tail]⟩)
    (share : shareable a row = true) : shareable a member = true ∧ shareable a tail = true := by
  have closed := (shareable_unfold a row).mp share
  simpa [Obend.Core.ResourceSemantics.head,observed] using closed

theorem scanStream_emit_shareable (a : Assumptions) (remaining : List Ty)
    (label : String) (first : Bool) (row member tail : Ty)
    (share : shareable a row = true)
    (emitted : scanStream a remaining label first row = .emit member tail) :
    shareable a member = true ∧ shareable a tail = true := by
  rw [scanStream] at emitted
  split at emitted
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at emitted
    · contradiction
    · rename_i name fieldMember fieldTail tag children
      have shape : observation = ⟨.field name,[fieldMember,fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have safe := exposed_field_shareable exposed share
      split at emitted
      · split at emitted
        · cases emitted; exact safe
        · exact scanStream_emit_shareable a (remaining.erase row) label first
            fieldTail member tail safe.2 emitted
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

theorem streamStep_emit_shareable {a : Assumptions} {row member tail : Ty}
    {label : String} {first : Bool} (share : shareable a row = true)
    (emitted : streamStep a row label first = .emit member tail) :
    shareable a member = true ∧ shareable a tail = true :=
  scanStream_emit_shareable a _ label first row member tail share emitted

def TailShareable (a : Assumptions) : Tail → Prop
  | .nominal index => a.shareableVariables.contains index = true
  | .nonRow t => shareable a t = true
  | _ => True

theorem scanResidual_shareable (a : Assumptions) (remaining : List Ty) (row : Ty)
    (share : shareable a row = true) : TailShareable a (scanResidual a remaining row) := by
  rw [scanResidual]
  split
  · rename_i index exposed
    have good := (shareable_unfold a row).mp share
    simpa [TailShareable,Obend.Core.ResourceSemantics.head,exposed] using good
  · trivial
  · rename_i observation exposed
    split
    · trivial
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name,[member,tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have safe := exposed_field_shareable exposed share
      split
      · exact scanResidual_shareable a (remaining.erase row) tail safe.2
      · trivial
    · exact share
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

theorem residual_shareable {a : Assumptions} {row : Ty} (share : shareable a row = true) :
    TailShareable a (residual a row) := scanResidual_shareable a _ row share

#assert_axioms exposed_field_shareable scanStream_emit_shareable streamStep_emit_shareable
  scanResidual_shareable residual_shareable
end Obend.Core.RecursiveRows

namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Raising the interpretation of nominal resource leaves preserves safety.
This justifies omitting source-shareable entries after substitution. -/
theorem weighted_safe_of_shareable (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true)
    {t : Ty} (share : RR.shareable a t = true) :
    Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) (.type t) := by
  let P : Node → Prop := fun node => match node with
    | .type row | .stream row _ _ => RR.shareable a row = true
  refine ⟨P,?_,share⟩
  intro node safe
  cases node with
  | stream row label first =>
    cases emitted : RR.streamStep a row label first with
    | «end» ending => simp [weightedResourceGraph,graph,observe,emitted,
        weightedResourceLabel,weightedResourceDependencies]
    | emit member tail =>
      have children := Obend.Core.RecursiveRows.streamStep_emit_shareable safe emitted
      simpa [weightedResourceGraph,graph,observe,emitted,
        weightedResourceLabel,weightedResourceDependencies,P] using children
  | type row =>
    have safe : RR.shareable a row = true := safe
    have closed := (Obend.Core.RecursiveRows.shareable_unfold a row).mp safe
    cases exposed : expose a row with
    | nominal index =>
      have listed : a.shareableVariables.contains index = true := by
        simpa [Obend.Core.ResourceSemantics.head,exposed] using closed
      simp [weightedResourceGraph,graph,observe,exposed,
        weightedResourceLabel,weightedResourceDependencies,raised index listed]
    | unproductive representative =>
      simp [weightedResourceGraph,graph,observe,exposed,
        weightedResourceLabel,weightedResourceDependencies]
    | constructor observation =>
      by_cases isRow : rowTag observation.tag = true
      · have residualSafe := Obend.Core.RecursiveRows.residual_shareable safe
        have root : weightedResourceLabel nominal
            (.row (RR.labels a row) (tailKind (RR.residual a row)) (RR.shareable a row)) = true := by
          cases ending : RR.residual a row with
          | nominal index =>
            have listed : a.shareableVariables.contains index = true := by
              simpa [ending,Obend.Core.RecursiveRows.TailShareable] using residualSafe
            exact raised index listed
          | _ => rfl
        refine ⟨?_,?_⟩
        · simpa [weightedResourceGraph,graph,observe,exposed,isRow,rowObservation] using root
        · intro child inside
          change child ∈ (weightedResourceGraph a nominal).successors (.type row) at inside
          simp only [weightedResourceGraph,graph,observe,exposed,isRow,↓reduceIte,
            rowObservation,weightedResourceDependencies] at inside
          change child ∈ rowChildren a row at inside
          rcases List.mem_append.mp inside with stream | ending
          · obtain ⟨label,_,rfl⟩ := List.mem_map.mp stream
            exact safe
          · cases result : RR.residual a row <;> simp [tailChildren,result] at ending
            subst child
            simpa [result,Obend.Core.RecursiveRows.TailShareable] using residualSafe
      · cases tag : observation.tag <;>
          simp_all [weightedResourceGraph,graph,observe,weightedResourceLabel,
            weightedResourceDependencies,Obend.Core.ResourceSemantics.head,rowTag,P]

#assert_axioms weighted_safe_of_shareable
end Obend.Core.TypeGraph
