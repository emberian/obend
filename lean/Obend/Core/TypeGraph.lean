module
/- Candidate recursive type observations. This module does not replace the
checker equality: constructor congruence and compatibility remain obligations. -/
public import Obend.Core.AliasExposure
public import Obend.Core.RecursiveRows
public import Obend.Core.FinitePresentation
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
namespace RR
export Obend.Core.RecursiveRows (Tail StreamStep shareable labels residual streamStep fieldLabels
  labels_mem_fieldLabels streamStep_emit_support residual_nonRow_support)
end RR
namespace FP
export Obend.Core.FinitePresentation (Graph Bisimilar ClosedSupport bisimilar_equivalence)
end FP
set_option autoImplicit false

inductive Node where
  | type (type : Ty)
  | stream (row : Ty) (label : String) (first : Bool)
  deriving DecidableEq, Repr

inductive TailKind where
  | closed | productiveCycle
  | nominal (index : Nat)
  | unproductive (representative : Nat)
  | nonRow
  deriving DecidableEq, Repr

inductive Label where
  | nominal (index : Nat)
  | unproductive (representative : Nat)
  | ordinary (tag : Tag) (shareable : Bool)
  | row (labels : List String) (tail : TailKind) (shareable : Bool)
  | streamEnd | streamEmit
  deriving DecidableEq, Repr

def tailKind : RR.Tail → TailKind
  | .closed => .closed
  | .productiveCycle => .productiveCycle
  | .nominal index => .nominal index
  | .unproductive index => .unproductive index
  | .nonRow _ => .nonRow

def tailChildren : RR.Tail → List Node
  | .nonRow type => [.type type]
  | _ => []

def rowTag : Tag → Bool
  | .emptyRow | .field _ => true
  | _ => false

def rowChildren (assumptions : Assumptions) (t : Ty) : List Node :=
  (RR.labels assumptions t).map (fun label => .stream t label true) ++
    tailChildren (RR.residual assumptions t)

def rowObservation (assumptions : Assumptions) (t : Ty) : Label × List Node :=
  (.row (RR.labels assumptions t) (tailKind (RR.residual assumptions t))
    (RR.shareable assumptions t),rowChildren assumptions t)

/-- These observations are global: they do not depend on either comparison
root or on the particular finite support used to execute the decision. -/
def observe (assumptions : Assumptions) : Node → Label × List Node
  | .type t =>
    match expose assumptions t with
    | .nominal index => (.nominal index,[])
    | .unproductive index => (.unproductive index,[])
    | .constructor observation =>
      if rowTag observation.tag then rowObservation assumptions t
      else (.ordinary observation.tag (RR.shareable assumptions t),observation.children.map .type)
  | .stream row label first =>
    match RR.streamStep assumptions row label first with
    | .end _ => (.streamEnd,[])
    | .emit member tail => (.streamEmit,[.type member,.stream tail label false])

def graph (assumptions : Assumptions) : FP.Graph Node Label where
  label := fun node => (observe assumptions node).1
  successors := fun node => (observe assumptions node).2

def nodes (assumptions : Assumptions) (left right : Ty) : List Node :=
  let types := support assumptions left right
  types.map .type ++ types.flatMap (fun t =>
    (RR.fieldLabels types).flatMap (fun label => [.stream t label true,.stream t label false]))

theorem type_mem_nodes_iff (assumptions : Assumptions) (left right t : Ty) :
    Node.type t ∈ nodes assumptions left right ↔ t ∈ support assumptions left right := by
  simp [nodes,List.mem_flatMap,List.mem_map]

theorem stream_mem_nodes_iff (assumptions : Assumptions) (left right row : Ty)
    (label : String) (first : Bool) :
    Node.stream row label first ∈ nodes assumptions left right ↔
      row ∈ support assumptions left right ∧ label ∈ RR.fieldLabels (support assumptions left right) := by
  cases first <;> simp [nodes,List.mem_flatMap,List.mem_map]

theorem rowChildren_support {assumptions : Assumptions} {left right t : Ty}
    (present : t ∈ support assumptions left right) :
    ∀ child ∈ rowChildren assumptions t, child ∈ nodes assumptions left right := by
  intro child member
  rcases List.mem_append.mp member with stream | tail
  · obtain ⟨name,listed,rfl⟩ := List.mem_map.mp stream
    exact (stream_mem_nodes_iff _ _ _ _ _ _).mpr
      ⟨present,RR.labels_mem_fieldLabels present listed⟩
  · cases ending : RR.residual assumptions t with
    | closed => simp [tailChildren,ending] at tail
    | productiveCycle => simp [tailChildren,ending] at tail
    | nominal index => simp [tailChildren,ending] at tail
    | unproductive index => simp [tailChildren,ending] at tail
    | nonRow result =>
      have equal : child = .type result := by simpa [tailChildren,ending] using tail
      rw [equal]
      exact (type_mem_nodes_iff _ _ _ _).mpr (RR.residual_nonRow_support present ending)

theorem nodes_closed (assumptions : Assumptions) (left right : Ty) :
    ∀ node ∈ nodes assumptions left right,
      ∀ child ∈ (graph assumptions).successors node, child ∈ nodes assumptions left right := by
  intro node member child found
  change child ∈ (observe assumptions node).2 at found
  cases node with
  | type t =>
    have present := (type_mem_nodes_iff _ _ _ _).mp member
    cases exposed : expose assumptions t with
    | nominal index => simp [observe,exposed] at found
    | unproductive index => simp [observe,exposed] at found
    | constructor observation =>
      by_cases row : rowTag observation.tag = true
      · have rowMember : child ∈ rowChildren assumptions t := by
          simpa [observe,exposed,row,rowObservation] using found
        exact rowChildren_support present child rowMember
      · have ordinary : child ∈ observation.children.map Node.type := by
          simpa [observe,exposed,row] using found
        obtain ⟨type,inside,rfl⟩ := List.mem_map.mp ordinary
        exact (type_mem_nodes_iff _ _ _ _).mpr (expose_children_support present exposed type inside)
  | stream row label first =>
    obtain ⟨present,listed⟩ := (stream_mem_nodes_iff _ _ _ _ _ _).mp member
    cases emitted : RR.streamStep assumptions row label first with
    | «end» ending => simp [observe,emitted] at found
    | emit payload tail =>
      obtain ⟨payloadPresent,tailPresent⟩ := RR.streamStep_emit_support present emitted
      have either : child = .type payload ∨ child = .stream tail label false := by
        simpa [observe,emitted] using found
      rcases either with payloadChild | tailChild
      · rw [payloadChild]
        exact (type_mem_nodes_iff _ _ _ _).mpr payloadPresent
      · rw [tailChild]
        exact (stream_mem_nodes_iff _ _ _ _ _ _).mpr ⟨tailPresent,listed⟩

def presentation (assumptions : Assumptions) (left right : Ty) :
    FP.ClosedSupport (graph assumptions) :=
  ⟨nodes assumptions left right,nodes_closed assumptions left right⟩

theorem left_mem_nodes (assumptions : Assumptions) (left right : Ty) :
    Node.type left ∈ (presentation assumptions left right).nodes :=
  (type_mem_nodes_iff _ _ _ _).mpr (left_mem_support _ _ _)

theorem right_mem_nodes (assumptions : Assumptions) (left right : Ty) :
    Node.type right ∈ (presentation assumptions left right).nodes :=
  (type_mem_nodes_iff _ _ _ _).mpr (right_mem_support _ _ _)

def Equivalent (assumptions : Assumptions) (left right : Ty) : Prop :=
  FP.Bisimilar (graph assumptions) (.type left) (.type right)

def candidate (assumptions : Assumptions) (left right : Ty) : Bool :=
  (presentation assumptions left right).agreement (.type left) (.type right)
    (left_mem_nodes _ _ _) (right_mem_nodes _ _ _)

theorem candidate_iff (assumptions : Assumptions) (left right : Ty) :
    candidate assumptions left right = true ↔ Equivalent assumptions left right :=
  (presentation assumptions left right).global_iff _ _ _ _

theorem equivalent_equivalence (assumptions : Assumptions) : Equivalence (Equivalent assumptions) := by
  have equivalence := FP.bisimilar_equivalence (graph assumptions)
  exact ⟨fun t => equivalence.refl (.type t),fun h => equivalence.symm h,
    fun h k => equivalence.trans h k⟩

theorem candidate_equivalence (assumptions : Assumptions) :
    Equivalence (fun left right => candidate assumptions left right = true) := by
  have equivalence := equivalent_equivalence assumptions
  refine ⟨?_,?_,?_⟩
  · intro t; exact (candidate_iff _ _ _).mpr (equivalence.refl t)
  · intro x y h; exact (candidate_iff _ _ _).mpr (equivalence.symm ((candidate_iff _ _ _).mp h))
  · intro x y z h k
    exact (candidate_iff _ _ _).mpr (equivalence.trans ((candidate_iff _ _ _).mp h) ((candidate_iff _ _ _).mp k))

#assert_axioms nodes_closed candidate_iff equivalent_equivalence candidate_equivalence

open Obend.Core.FiniteBisimulation (Children)

/-- Arrow shareability observes reuse, independently of its component types. -/
theorem observe_arrow (assumptions : Assumptions) (reuse : Reuse) (quantity : Quantity)
    (domain codomain : Ty) :
    observe assumptions (.type (.arrow reuse quantity domain codomain)) =
      (.ordinary (.arrow reuse quantity) (reuse == .reusable),[.type domain,.type codomain]) := by
  simp [observe,expose,exposeWalk,constructorHead,rowTag,
    Obend.Core.RecursiveRows.shareable_arrow,Obend.Core.RecursiveRows.shareable_computation]

theorem observe_computation (assumptions : Assumptions) (plan response result : Ty) :
    observe assumptions (.type (.computation plan response result)) =
      (.ordinary .computation false,[.type plan,.type response,.type result]) := by
  simp [observe,expose,exposeWalk,constructorHead,rowTag,
    Obend.Core.RecursiveRows.shareable_arrow,Obend.Core.RecursiveRows.shareable_computation]

theorem arrow_congruence {assumptions : Assumptions} {reuse : Reuse} {quantity : Quantity}
    {domain codomain domain' codomain' : Ty}
    (domains : Equivalent assumptions domain domain')
    (codomains : Equivalent assumptions codomain codomain') :
    Equivalent assumptions (.arrow reuse quantity domain codomain)
      (.arrow reuse quantity domain' codomain') := by
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe assumptions (.type (.arrow reuse quantity domain codomain))).1 =
      (observe assumptions (.type (.arrow reuse quantity domain' codomain'))).1
    rw [observe_arrow,observe_arrow]
  · change Children _ (observe assumptions (.type (.arrow reuse quantity domain codomain))).2
      (observe assumptions (.type (.arrow reuse quantity domain' codomain'))).2
    rw [observe_arrow,observe_arrow]
    exact ⟨domains,codomains,True.intro⟩

theorem computation_congruence {assumptions : Assumptions}
    {plan response result plan' response' result' : Ty}
    (plans : Equivalent assumptions plan plan')
    (responses : Equivalent assumptions response response')
    (results : Equivalent assumptions result result') :
    Equivalent assumptions (.computation plan response result)
      (.computation plan' response' result') := by
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe assumptions (.type (.computation plan response result))).1 =
      (observe assumptions (.type (.computation plan' response' result'))).1
    rw [observe_computation,observe_computation]
  · change Children _ (observe assumptions (.type (.computation plan response result))).2
      (observe assumptions (.type (.computation plan' response' result'))).2
    rw [observe_computation,observe_computation]
    exact ⟨plans,responses,results,True.intro⟩

#assert_axioms observe_arrow observe_computation arrow_congruence computation_congruence

end Obend.Core.TypeGraph
