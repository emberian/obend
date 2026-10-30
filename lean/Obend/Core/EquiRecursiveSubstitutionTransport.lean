module
public import Obend.Core.SubstitutionRows
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
open Obend.Core.FiniteBisimulation (Children children_mono)
set_option autoImplicit false

theorem existing_instantiation_closed {σ : Nat → Ty} {a b : Assumptions} {x y : Node}
    (related : FP.Bisimilar (graph b) x y) :
    (graph b).label x = (graph b).label y ∧
      Children (InstantiationRelated σ a b) ((graph b).successors x) ((graph b).successors y) := by
  obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph b) _ _ related
  exact ⟨labels,children_mono (fun _ _ h => InstantiationRelated.existing h) children⟩

theorem Discharges.type_seed_closed
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true) {left right : Ty}
    (related : Equivalent a left right) :
    (graph b).label (.type (left.instantiate σ)) = (graph b).label (.type (right.instantiate σ)) ∧
      Children (InstantiationRelated σ a b) ((graph b).successors (.type (left.instantiate σ)))
        ((graph b).successors (.type (right.instantiate σ))) := by
  obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ related
  cases sourceL : expose a left with
  | nominal index =>
    cases sourceR : expose a right with
    | nominal other =>
      have same : index = other := by simpa [graph,observe,sourceL,sourceR] using labels
      subst other
      exact existing_instantiation_closed (equivalent_of_expose_eq
        ((D.expose_instantiate_nominal sourceL).trans (D.expose_instantiate_nominal sourceR).symm))
    | unproductive other => simp [graph,observe,sourceL,sourceR] at labels
    | constructor c =>
      cases flag : rowTag c.tag <;> simp [graph,observe,sourceL,sourceR,flag,rowObservation] at labels
  | unproductive representative =>
    cases sourceR : expose a right with
    | unproductive other =>
      have same : representative = other := by simpa [graph,observe,sourceL,sourceR] using labels
      subst other
      exact existing_instantiation_closed (equivalent_of_expose_eq
        ((D.expose_instantiate_unproductive sourceL).trans (D.expose_instantiate_unproductive sourceR).symm))
    | nominal other => simp [graph,observe,sourceL,sourceR] at labels
    | constructor c =>
      cases flag : rowTag c.tag <;> simp [graph,observe,sourceL,sourceR,flag,rowObservation] at labels
  | constructor c =>
    cases sourceR : expose a right with
    | nominal other =>
      cases flag : rowTag c.tag <;> simp [graph,observe,sourceL,sourceR,flag,rowObservation] at labels
    | unproductive other =>
      cases flag : rowTag c.tag <;> simp [graph,observe,sourceL,sourceR,flag,rowObservation] at labels
    | constructor d =>
      have mappedL := D.expose_instantiate_constructor sourceL
      have mappedR := D.expose_instantiate_constructor sourceR
      have resources : RR.shareable b (left.instantiate σ) = RR.shareable b (right.instantiate σ) :=
        D.semantic_shareable_congr valid related
      by_cases lrow : rowTag c.tag = true
      · have rrow : rowTag d.tag = true := by
          by_cases isRow : rowTag d.tag = true
          · exact isRow
          · simp [graph,observe,sourceL,sourceR,lrow,isRow,rowObservation] at labels
        have view := equivalent_row_interface related
        have alphabet := D.row_alphabet_instantiate valid view
        have residual := D.row_residual_interface view
        constructor
        · simp [graph,observe,mappedL,mappedR,lrow,rrow,rowObservation,
            alphabet,residual.1,resources]
        · simp only [graph,observe,mappedL,mappedR,lrow,rrow,↓reduceIte,rowObservation]
          unfold rowChildren
          rw [← alphabet]
          apply children_append
          · apply children_mapped
            intro label _
            exact InstantiationRelated.streams (.source (view.streams label) view.residualKind)
          · exact residual.2
      · have rrow : rowTag d.tag ≠ true := by
          intro isRow
          simp [graph,observe,sourceL,sourceR,lrow,isRow,rowObservation] at labels
        have tags : c.tag = d.tag := by
          have ordinary : Label.ordinary c.tag (RR.shareable a left) =
              Label.ordinary d.tag (RR.shareable a right) := by
            simpa [graph,observe,sourceL,sourceR,lrow,rrow] using labels
          exact (Label.ordinary.inj ordinary).1
        have sourceChildren : Children (FP.Bisimilar (graph a))
            (c.children.map Node.type) (d.children.map Node.type) := by
          simpa [graph,observe,sourceL,sourceR,lrow,rrow] using children
        constructor
        · simp [graph,observe,mappedL,mappedR,lrow,rrow,tags,resources]
        · simpa [graph,observe,mappedL,mappedR,lrow,rrow,List.map_map,Function.comp_def] using
            instantiation_type_children σ a b c.children d.children sourceChildren

/-- Full hereditary recursive equality transport. The original discharge
contract is retained; the actual instance's premise validation is essential. -/
theorem Discharges.equivalent_instantiate
    {σ : Nat → Ty} {template instance_ : Assumptions} {extra : Nat}
    (D : Discharges σ template instance_ extra) (valid : instance_.valid = true)
    {actual expected : Ty} (agreement : Equivalent template actual expected) :
    Equivalent instance_ (actual.instantiate σ) (expected.instantiate σ) := by
  refine ⟨InstantiationRelated σ template instance_,?_,InstantiationRelated.types agreement⟩
  intro left right related
  induction related with
  | existing h => exact existing_instantiation_closed h
  | types h => exact D.type_seed_closed valid h
  | streams h => exact D.related_stream_closed valid h
  | trans h k ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1,instantiation_children_trans ih₁.2 ih₂.2⟩

#assert_axioms existing_instantiation_closed Discharges.type_seed_closed Discharges.equivalent_instantiate
end Obend.Core.Proofs.Templates
