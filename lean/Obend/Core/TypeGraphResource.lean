module
public import Obend.Core.TypeGraph
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.FiniteBisimulation (Children)
set_option autoImplicit false

/-- Resource observations of type nodes can be recovered from their graph
label. Nominal variables use their explicit premise; alias-only cycles contain no resource constructors. -/
def labelShareable (assumptions : Assumptions) : Label → Bool
  | .nominal index => assumptions.shareableVariables.contains index
  | .unproductive _ => true
  | .ordinary _ resource | .row _ _ resource => resource
  | .streamEnd | .streamEmit => false

theorem observed_shareable (assumptions : Assumptions) (t : Ty) :
    labelShareable assumptions ((graph assumptions).label (.type t)) =
      Obend.Core.RecursiveRows.shareable assumptions t := by
  cases exposed : expose assumptions t with
  | nominal index =>
    have resource : Obend.Core.RecursiveRows.shareable assumptions t =
        assumptions.shareableVariables.contains index := by
      apply Obend.Core.RecursiveRows.shareable_terminal
      simp [Obend.Core.ResourceSemantics.head,exposed]
    simpa [graph,observe,exposed,labelShareable] using resource.symm
  | unproductive index =>
    have resource : Obend.Core.RecursiveRows.shareable assumptions t = true := by
      apply Obend.Core.RecursiveRows.shareable_terminal
      simp [Obend.Core.ResourceSemantics.head,exposed]
    simpa [graph,observe,exposed,labelShareable] using resource.symm
  | constructor observation =>
    by_cases row : rowTag observation.tag = true
    · simp [graph,observe,exposed,row,rowObservation,labelShareable]
    · simp [graph,observe,exposed,row,labelShareable]

/-- Candidate equality preserves the semantic resource predicate exactly. -/
theorem equivalent_shareable {assumptions : Assumptions} {left right : Ty}
    (related : Equivalent assumptions left right) :
    Obend.Core.RecursiveRows.shareable assumptions left =
      Obend.Core.RecursiveRows.shareable assumptions right := by
  have labels := (Obend.Core.FinitePresentation.bisimilar_closed (graph assumptions)
    (.type left) (.type right) related).1
  have resources := congrArg (labelShareable assumptions) labels
  simpa only [observed_shareable] using resources

theorem candidate_shareable {assumptions : Assumptions} {left right : Ty}
    (accepted : candidate assumptions left right = true) :
    Obend.Core.RecursiveRows.shareable assumptions left =
      Obend.Core.RecursiveRows.shareable assumptions right :=
  equivalent_shareable ((candidate_iff _ _ _).mp accepted)

theorem observe_specification (assumptions : Assumptions) (metadata extension : Ty) :
    observe assumptions (.type (.specification metadata extension)) =
      (.ordinary .specification
        (Obend.Core.RecursiveRows.shareable assumptions metadata &&
          Obend.Core.RecursiveRows.shareable assumptions extension),[.type metadata,.type extension]) := by
  simp [observe,expose,exposeWalk,constructorHead,rowTag,
    Obend.Core.RecursiveRows.shareable_specification]

theorem observe_prototype (assumptions : Assumptions) (spec target : Ty) :
    observe assumptions (.type (.prototype spec target)) =
      (.ordinary .prototype
        (Obend.Core.RecursiveRows.shareable assumptions spec &&
          Obend.Core.RecursiveRows.shareable assumptions target),[.type spec,.type target]) := by
  simp [observe,expose,exposeWalk,constructorHead,rowTag,
    Obend.Core.RecursiveRows.shareable_prototype]

theorem observe_variant (assumptions : Assumptions) (row : Ty) :
    observe assumptions (.type (.variant row)) =
      (.ordinary .variant (Obend.Core.RecursiveRows.shareable assumptions row),[.type row]) := by
  simp [observe,expose,exposeWalk,constructorHead,rowTag,
    Obend.Core.RecursiveRows.shareable_variant]

theorem specification_congruence {assumptions : Assumptions}
    {metadata extension metadata' extension' : Ty}
    (metadataRelated : Equivalent assumptions metadata metadata')
    (extensionRelated : Equivalent assumptions extension extension') :
    Equivalent assumptions (.specification metadata extension)
      (.specification metadata' extension') := by
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe assumptions (.type (.specification metadata extension))).1 =
      (observe assumptions (.type (.specification metadata' extension'))).1
    rw [observe_specification,observe_specification,
      equivalent_shareable metadataRelated,equivalent_shareable extensionRelated]
  · change Children _ (observe assumptions (.type (.specification metadata extension))).2
      (observe assumptions (.type (.specification metadata' extension'))).2
    rw [observe_specification,observe_specification]
    exact ⟨metadataRelated,extensionRelated,True.intro⟩

theorem prototype_congruence {assumptions : Assumptions}
    {spec target spec' target' : Ty}
    (specRelated : Equivalent assumptions spec spec')
    (targetRelated : Equivalent assumptions target target') :
    Equivalent assumptions (.prototype spec target) (.prototype spec' target') := by
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe assumptions (.type (.prototype spec target))).1 =
      (observe assumptions (.type (.prototype spec' target'))).1
    rw [observe_prototype,observe_prototype,
      equivalent_shareable specRelated,equivalent_shareable targetRelated]
  · change Children _ (observe assumptions (.type (.prototype spec target))).2
      (observe assumptions (.type (.prototype spec' target'))).2
    rw [observe_prototype,observe_prototype]
    exact ⟨specRelated,targetRelated,True.intro⟩

theorem variant_congruence {assumptions : Assumptions} {row row' : Ty}
    (related : Equivalent assumptions row row') :
    Equivalent assumptions (.variant row) (.variant row') := by
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · change (observe assumptions (.type (.variant row))).1 =
      (observe assumptions (.type (.variant row'))).1
    rw [observe_variant,observe_variant,equivalent_shareable related]
  · change Children _ (observe assumptions (.type (.variant row))).2
      (observe assumptions (.type (.variant row'))).2
    rw [observe_variant,observe_variant]
    exact ⟨related,True.intro⟩

#assert_axioms observed_shareable equivalent_shareable candidate_shareable
  observe_specification observe_prototype observe_variant
  specification_congruence prototype_congruence variant_congruence
end Obend.Core.TypeGraph
