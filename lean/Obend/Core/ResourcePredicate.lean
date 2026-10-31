module
public import Obend.Core.WeightedResource
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Raw resource dependencies of a productive type constructor. -/
def resourceObservation (c : Constructor) : Bool × List Ty :=
  match c.tag with
  | .natural | .label | .boolean | .emptyRow => (true,[])
  | .arrow reuse _ => (reuse == .reusable,[])
  | .custody _ | .computation => (false,[])
  | .field _ | .specification | .prototype | .variant => (true,c.children)

/-- A local resource invariant, independent of the scanner's finite support.
This interface covers both source safety and safety after substitution. -/
structure ResourcePredicate (a : Assumptions) (nominal : Nat → Bool) (Q : Ty → Prop) : Prop where
  productive : ∀ {t c}, expose a t = .constructor c → Q t →
    (resourceObservation c).1 = true ∧ ∀ child ∈ (resourceObservation c).2, Q child
  nominal : ∀ {t j}, expose a t = .nominal j → Q t → nominal j = true

theorem ResourcePredicate.field {a : Assumptions} {nominal : Nat → Bool} {Q : Ty → Prop}
    (P : ResourcePredicate a nominal Q) {row member tail : Ty} {name : String}
    (observed : expose a row = .constructor ⟨.field name,[member,tail]⟩) (safe : Q row) :
    Q member ∧ Q tail := by
  simpa [resourceObservation] using P.productive observed safe

theorem ResourcePredicate.scanStream {a : Assumptions} {nominal : Nat → Bool} {Q : Ty → Prop}
    (P : ResourcePredicate a nominal Q) (remaining : List Ty)
    (label : String) (first : Bool) (row member tail : Ty) (safe : Q row)
    (emitted : Obend.Core.RecursiveRows.scanStream a remaining label first row = .emit member tail) :
    Q member ∧ Q tail := by
  rw [Obend.Core.RecursiveRows.scanStream] at emitted
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
      have childrenSafe := P.field exposed safe
      split at emitted
      · split at emitted
        · cases emitted; exact childrenSafe
        · exact P.scanStream (remaining.erase row) label first fieldTail member tail childrenSafe.2 emitted
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

def ResourceTailPredicate (nominal : Nat → Bool) (Q : Ty → Prop) : RR.Tail → Prop
  | .nominal index => nominal index = true
  | .nonRow t => Q t
  | _ => True

theorem ResourcePredicate.scanResidual {a : Assumptions} {nominal : Nat → Bool} {Q : Ty → Prop}
    (P : ResourcePredicate a nominal Q) (remaining : List Ty) (row : Ty) (safe : Q row) :
    ResourceTailPredicate nominal Q (Obend.Core.RecursiveRows.scanResidual a remaining row) := by
  rw [Obend.Core.RecursiveRows.scanResidual]
  split
  · rename_i index exposed
    exact P.nominal exposed safe
  · trivial
  · rename_i observation exposed
    split
    · trivial
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name,[member,tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      have childrenSafe := P.field exposed safe
      split
      · exact P.scanResidual (remaining.erase row) tail childrenSafe.2
      · trivial
    · exact safe
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

/-- A resource invariant closes over the quotient row graph. This is the shared
coinductive bridge used for ordinary safety and substitution-image safety. -/
theorem ResourcePredicate.weighted_safe {a : Assumptions} {nominal : Nat → Bool} {Q : Ty → Prop}
    (P : ResourcePredicate a nominal Q) {t : Ty} (safe : Q t) :
    Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) (.type t) := by
  let Nodes : Node → Prop := fun node => match node with
    | .type row | .stream row _ _ => Q row
  refine ⟨Nodes,?_,safe⟩
  intro node good
  cases node with
  | stream row label first =>
    cases emitted : RR.streamStep a row label first with
    | «end» ending => simp [weightedResourceGraph,graph,observe,emitted,
        weightedResourceLabel,weightedResourceDependencies]
    | emit member tail =>
      have children := P.scanStream _ label first row member tail good emitted
      simpa [weightedResourceGraph,graph,observe,emitted,
        weightedResourceLabel,weightedResourceDependencies,Nodes] using children
  | type row =>
    have good : Q row := good
    cases exposed : expose a row with
    | nominal index =>
      simp [weightedResourceGraph,graph,observe,exposed,
        weightedResourceLabel,weightedResourceDependencies,P.nominal exposed good]
    | unproductive representative =>
      simp [weightedResourceGraph,graph,observe,exposed,
        weightedResourceLabel,weightedResourceDependencies]
    | constructor observation =>
      have closed := P.productive exposed good
      by_cases isRow : rowTag observation.tag = true
      · have residualSafe : ResourceTailPredicate nominal Q (RR.residual a row) :=
          P.scanResidual (support a row row) row good
        have root : weightedResourceLabel nominal
            (.row (RR.labels a row) (tailKind (RR.residual a row)) (RR.shareable a row)) = true := by
          cases ending : RR.residual a row with
          | nominal index =>
            simpa [ending,ResourceTailPredicate,weightedResourceLabel,tailKind] using residualSafe
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
            exact good
          · cases result : RR.residual a row <;> simp [tailChildren,result] at ending
            subst child
            simpa [result,ResourceTailPredicate,Nodes] using residualSafe
      · cases tag : observation.tag <;>
          simp_all [weightedResourceGraph,graph,observe,weightedResourceLabel,
            weightedResourceDependencies,resourceObservation,rowTag,Nodes]

end Obend.Core.TypeGraph
