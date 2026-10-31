module
public import Obend.Core.RowExposureInvariance
public import Obend.Core.TypeGraphResource
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.FiniteBisimulation (Children)
set_option autoImplicit false

private theorem self_related (assumptions : Assumptions) (nodes : List Node) :
    Children (Obend.Core.FinitePresentation.Bisimilar (graph assumptions)) nodes nodes := by
  induction nodes with
  | nil => trivial
  | cons node nodes ih =>
    exact ⟨Obend.Core.FinitePresentation.bisimilar_refl _ node,ih⟩

private theorem append_related {α : Type} {R : α → α → Prop}
    {xs ys us vs : List α} (first : Children R xs ys) (later : Children R us vs) :
    Children R (xs ++ us) (ys ++ vs) := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact later
    | cons y ys => exact False.elim first
  | cons x xs ih => cases ys with
    | nil => exact False.elim first
    | cons y ys => exact ⟨first.1,ih first.2⟩

private theorem mapped_related {α β : Type} {R : β → β → Prop}
    (f g : α → β) (xs : List α) (related : ∀ x ∈ xs, R (f x) (g x)) :
    Children R (xs.map f) (xs.map g) := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨related x (by simp),ih (fun y hy => related y (List.mem_cons_of_mem x hy))⟩

/-- Identical global observations are bisimilar even when their source states
have different finite-support indices. -/
theorem node_equivalent_of_observe_eq {assumptions : Assumptions} {left right : Node}
    (same : observe assumptions left = observe assumptions right) :
    Obend.Core.FinitePresentation.Bisimilar (graph assumptions) left right := by
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · exact congrArg Prod.fst same
  · have children : (graph assumptions).successors left = (graph assumptions).successors right :=
      congrArg Prod.snd same
    rw [children]
    exact self_related assumptions _

theorem stream_equivalent_of_expose_eq {assumptions : Assumptions}
    {left right : Ty} (heads : expose assumptions left = expose assumptions right)
    (name : String) (first : Bool) :
    Obend.Core.FinitePresentation.Bisimilar (graph assumptions)
      (.stream left name first) (.stream right name first) :=
  node_equivalent_of_observe_eq (RowHit.stream_observe_expose_eq assumptions name first left right heads)

/-- Equal productive exposures give equal type meanings. Row roots retain
their complete interface and residual while their stream states may differ. -/
theorem equivalent_of_expose_eq {assumptions : Assumptions} {left right : Ty}
    (heads : expose assumptions left = expose assumptions right) :
    Equivalent assumptions left right := by
  cases exposed : expose assumptions left with
  | nominal index =>
    have other : expose assumptions right = .nominal index := heads.symm.trans exposed
    apply node_equivalent_of_observe_eq
    simp [observe,exposed,other]
  | unproductive index =>
    have other : expose assumptions right = .unproductive index := heads.symm.trans exposed
    apply node_equivalent_of_observe_eq
    simp [observe,exposed,other]
  | constructor observation =>
    have other : expose assumptions right = .constructor observation := heads.symm.trans exposed
    have resources := Obend.Core.RecursiveRows.shareable_eq_of_expose_eq heads
    by_cases row : rowTag observation.tag = true
    · have names := Obend.Core.RecursiveRows.labels_expose_eq assumptions left right heads
      have endings := Obend.Core.RecursiveRows.residual_expose_eq assumptions left right observation
        exposed heads row
      apply Obend.Core.FinitePresentation.bisimilar_of_children
      · change (observe assumptions (.type left)).1 = (observe assumptions (.type right)).1
        simp [observe,exposed,other,row,rowObservation,names,endings,resources]
      · have one : (graph assumptions).successors (.type left) = rowChildren assumptions left := by
          simp [graph,observe,exposed,row,rowObservation]
        have two : (graph assumptions).successors (.type right) = rowChildren assumptions right := by
          simp [graph,observe,other,row,rowObservation]
        rw [one,two]
        unfold rowChildren
        simp only [← names,← endings]
        apply append_related
        · apply mapped_related
          intro name _
          exact stream_equivalent_of_expose_eq heads name true
        · exact self_related assumptions _
    · apply node_equivalent_of_observe_eq
      simp [observe,exposed,other,row,resources]

theorem alias_equivalent (assumptions : Assumptions) (index : Nat) (body : Ty)
    (found : assumptions.alias index = some body) (pure : body.isComputation = false) :
    Equivalent assumptions (.variable index) body :=
  equivalent_of_expose_eq (expose_alias assumptions index body found pure)

theorem alias_candidate (assumptions : Assumptions) (index : Nat) (body : Ty)
    (found : assumptions.alias index = some body) (pure : body.isComputation = false) :
    candidate assumptions (.variable index) body = true :=
  (candidate_iff _ _ _).mpr (alias_equivalent assumptions index body found pure)

end Obend.Core.TypeGraph
