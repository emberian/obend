module
public import Obend.Core.ResourcePredicate
public import Obend.Core.WeightedRowSafety
public import Obend.Core.ResourceSubstitution
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Once omitted source-shareable entries are safe, the weighted quotient
interpretation satisfies precisely the raw resource equations. -/
theorem weighted_resource_predicate (a : Assumptions) (nominal : Nat → Bool)
    (raised : ∀ j, a.shareableVariables.contains j = true → nominal j = true) :
    ResourcePredicate a nominal (fun t => WeightedSafe a nominal (.type t)) where
  nominal := by
    intro t j exposed safe
    obtain ⟨good,_⟩ := Obend.Core.FiniteSafety.safe_closed (weightedResourceGraph a nominal) _ safe
    simpa [weightedResourceGraph,graph,observe,exposed,weightedResourceLabel] using good
  productive := by
    intro t c exposed safe
    obtain ⟨raw,_,head⟩ := expose_origin (left_mem_support a t t) exposed
    have nonvariable : ∀ index, raw ≠ .variable index := by
      intro index equal
      subst raw
      simp [constructorHead] at head
    have rawExposure : expose a raw = .constructor c :=
      (expose_nonvariable a raw nonvariable).trans head
    have rawSafe := (weighted_safe_of_related a nominal
      (equivalent_of_expose_eq (exposed.trans rawExposure.symm))).mp safe
    cases raw with
    | «variable» index => exact False.elim (nonvariable index rfl)
    | field name member tail =>
      have shape : c = ⟨.field name,[member,tail]⟩ := by simpa [constructorHead] using head.symm
      subst c
      simpa [resourceObservation] using (weighted_field_safe a nominal raised name member tail).mp rawSafe
    | _ =>
      simp only [constructorHead,Head.constructor.injEq] at head
      subst c
      simp only [WeightedSafe] at rawSafe ⊢
      rw [Obend.Core.FiniteSafety.safe_iff] at rawSafe
      simpa [resourceObservation,weightedResourceGraph,graph,observe,expose,exposeWalk,
        constructorHead,rowTag,weightedResourceLabel,weightedResourceDependencies] using rawSafe

#assert_axioms weighted_resource_predicate
end Obend.Core.TypeGraph

namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure Obend.Core.TypeGraph
set_option autoImplicit false

theorem Discharges.image_resource_predicate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat} (D : Discharges σ a b extra) :
    ResourcePredicate a (fun j => RS.shareable b (σ j))
      (fun t => RS.shareable b (t.instantiate σ) = true) where
  nominal := by
    intro t j observed safe
    have mapped := D.expose_instantiate_nominal observed
    exact (RS.shareable_eq_of_expose_eq mapped).symm.trans safe
  productive := by
    intro t c observed safe
    have mapped := D.expose_instantiate_constructor observed
    have closed := (Obend.Core.ResourceSemantics.shareable_unfold b (t.instantiate σ)).mp safe
    cases tag : c.tag <;>
      simp_all [RS.head,resourceObservation]

/-- Exact bridge between actual substitution-image safety and the weighted
source quotient. It uses local syntactic validity, not a new discharge field. -/
theorem Discharges.weighted_resource_iff_image
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true) (t : Ty) :
    WeightedSafe a (fun j => RS.shareable b (σ j)) (.type t) ↔
      RS.shareable b (t.instantiate σ) = true := by
  have raised : ∀ j, a.shareableVariables.contains j = true → RS.shareable b (σ j) = true := by
    intro j listed
    exact Obend.Core.ResourceValidity.valid_shareableUnder_shareable valid (σ j)
      ((D.shareable j).trans listed)
  have source := weighted_resource_predicate a (fun j => RS.shareable b (σ j)) raised
  constructor
  · intro safe
    let P : Ty → Prop := fun image => Obend.Core.FiniteSafety.Safe (RS.graph b) image ∨
      ∃ original, WeightedSafe a (fun j => RS.shareable b (σ j)) (.type original) ∧
        image = original.instantiate σ
    have prior (image : Ty) (safe : Obend.Core.FiniteSafety.Safe (RS.graph b) image) :
        (RS.graph b).label image = true ∧ ∀ child ∈ (RS.graph b).successors image, P child := by
      obtain ⟨good,children⟩ := Obend.Core.FiniteSafety.safe_closed (RS.graph b) _ safe
      exact ⟨good,fun child inside => Or.inl (children child inside)⟩
    apply (RS.shareable_iff _ _).mpr
    refine ⟨P,?_,Or.inr ⟨t,safe,rfl⟩⟩
    intro image related
    rcases related with existing | ⟨original,safe,rfl⟩
    · exact prior image existing
    · cases observed : expose a original with
      | nominal index =>
        have imageSafe := source.nominal observed safe
        have mapped := D.expose_instantiate_nominal observed
        have transferred : RS.shareable b (original.instantiate σ) = true :=
          (RS.shareable_eq_of_expose_eq mapped).trans imageSafe
        exact prior _ ((RS.shareable_iff _ _).mp transferred)
      | unproductive representative =>
        have mapped := D.expose_instantiate_unproductive observed
        simp [RS.graph,RS.head,mapped]
      | constructor c =>
        obtain ⟨good,children⟩ := source.productive observed safe
        have mapped := D.expose_instantiate_constructor observed
        have heads : RS.head b (original.instantiate σ) =
            ((resourceObservation c).1,(resourceObservation c).2.map (Ty.instantiate σ)) := by
          cases tag : c.tag <;> simp [RS.head,mapped,resourceObservation,tag]
        refine ⟨?_,?_⟩
        · change (RS.head b (original.instantiate σ)).1 = true
          simpa only [heads] using good
        · intro child inside
          change child ∈ (RS.head b (original.instantiate σ)).2 at inside
          rw [heads] at inside
          obtain ⟨originalChild,present,rfl⟩ := List.mem_map.mp inside
          exact Or.inr ⟨originalChild,children originalChild present,rfl⟩
  · intro safe
    exact D.image_resource_predicate.weighted_safe safe

/-- Source-equivalent types have exactly equal resource flags after
instantiation, even when an unconstrained nominal image becomes shareable. -/
theorem Discharges.semantic_shareable_congr
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true) {left right : Ty}
    (related : Equivalent a left right) :
    RS.shareable b (left.instantiate σ) = RS.shareable b (right.instantiate σ) := by
  apply Obend.Core.FiniteSafety.bool_ext
  exact (D.weighted_resource_iff_image valid left).symm.trans
    ((equivalent_weighted_resource _ related).trans (D.weighted_resource_iff_image valid right))

#assert_axioms Discharges.image_resource_predicate Discharges.weighted_resource_iff_image
  Discharges.semantic_shareable_congr
end Obend.Core.Proofs.Templates
