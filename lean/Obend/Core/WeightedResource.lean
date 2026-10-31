module
public import Obend.Core.TypeGraph
public import Obend.Core.ResourceSemantics
@[expose] public section
namespace Obend.Core.FiniteSafety
open Obend.Core.FinitePresentation (Graph Bisimilar)
open Obend.Core.FiniteBisimulation (Children)
set_option autoImplicit false

theorem children_right_member {α : Type} {R : α → α → Prop} {xs ys : List α}
    (related : Children R xs ys) {y : α} (present : y ∈ ys) :
    ∃ x ∈ xs, R x y := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [Children]
  | cons x xs ih =>
    cases ys with
    | nil => simp at present
    | cons z zs =>
      rcases List.mem_cons.mp present with rfl | nested
      · exact ⟨x,by simp,related.1⟩
      · obtain ⟨original,inside,link⟩ := ih related.2 nested
        exact ⟨original,List.mem_cons_of_mem _ inside,link⟩

/-- Greatest resource safety is invariant under ordinary graph bisimulation. -/
theorem safe_of_bisimilar {α : Type} (g : Graph α Bool) {x y : α}
    (related : Bisimilar g x y) (safe : Safe g x) : Safe g y := by
  let P : α → Prop := fun target => ∃ source, Safe g source ∧ Bisimilar g source target
  refine ⟨P,?_,⟨x,safe,related⟩⟩
  intro target h
  obtain ⟨source,sourceSafe,link⟩ := h
  obtain ⟨good,children⟩ := safe_closed g source sourceSafe
  obtain ⟨labels,nested⟩ := Obend.Core.FinitePresentation.bisimilar_closed g _ _ link
  refine ⟨labels.symm.trans good,?_⟩
  intro child inside
  obtain ⟨original,present,related⟩ := children_right_member nested inside
  exact ⟨original,children original present,related⟩

theorem safe_bisimilar_iff {α : Type} (g : Graph α Bool) {x y : α}
    (related : Bisimilar g x y) : Safe g x ↔ Safe g y :=
  ⟨safe_of_bisimilar g related,
    safe_of_bisimilar g ((Obend.Core.FinitePresentation.bisimilar_equivalence g).symm related)⟩

end Obend.Core.FiniteSafety

namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check
set_option autoImplicit false

/-- Interpret nominal leaves with arbitrary resource values. Rows account for
their nominal residual in addition to their visible and retained member streams.
The source shareability annotation is deliberately not read by this interpretation. -/
def weightedResourceLabel (nominal : Nat → Bool) : Label → Bool
  | .nominal index => nominal index
  | .unproductive _ => true
  | .ordinary (.arrow reuse _) _ => reuse == .reusable
  | .ordinary (.custody _) _ | .ordinary .computation _ => false
  | .row _ (.nominal index) _ => nominal index
  | _ => true

def weightedResourceDependencies : Label → Bool
  | .ordinary .specification _ | .ordinary .prototype _ | .ordinary .variant _ => true
  | .ordinary _ _ => false
  | _ => true

def weightedResourceGraph (a : Assumptions) (nominal : Nat → Bool) :
    Obend.Core.FinitePresentation.Graph Node Bool where
  label := fun node => weightedResourceLabel nominal ((graph a).label node)
  successors := fun node => if weightedResourceDependencies ((graph a).label node)
    then (graph a).successors node else []

/-- Source equivalence transports to every weighted resource interpretation.
This separates the coinductive resource argument from scanner substitution. -/
theorem weightedResource_bisimilar (a : Assumptions) (nominal : Nat → Bool)
    {x y : Node} (related : FP.Bisimilar (graph a) x y) :
    FP.Bisimilar (weightedResourceGraph a nominal) x y := by
  refine ⟨FP.Bisimilar (graph a),?_,related⟩
  intro left right link
  obtain ⟨labels,children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ link
  refine ⟨congrArg (weightedResourceLabel nominal) labels,?_⟩
  change Obend.Core.FiniteBisimulation.Children _
    (if weightedResourceDependencies ((graph a).label left) then (graph a).successors left else [])
    (if weightedResourceDependencies ((graph a).label right) then (graph a).successors right else [])
  rw [← labels]
  cases weightedResourceDependencies ((graph a).label left) <;>
    simp only [Bool.false_eq_true,↓reduceIte]
  · trivial
  · exact children

theorem equivalent_weighted_resource {a : Assumptions} {left right : Ty}
    (nominal : Nat → Bool) (related : Equivalent a left right) :
    Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) (.type left) ↔
      Obend.Core.FiniteSafety.Safe (weightedResourceGraph a nominal) (.type right) :=
  Obend.Core.FiniteSafety.safe_bisimilar_iff _ (weightedResource_bisimilar a nominal related)

end Obend.Core.TypeGraph
