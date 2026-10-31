module
public import Obend.Core.SubstitutionExposure
public import Obend.Core.ResourceValidity
@[expose] public section
namespace Obend.Core.Proofs.Templates
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
namespace RS
export Obend.Core.ResourceSemantics (head graph shareable shareable_iff shareable_eq_of_expose_eq)
end RS
namespace FS
export Obend.Core.FiniteSafety (Safe Closed safe_closed)
end FS
set_option autoImplicit false

/-- Productive observations commute with substitution, including their resource
dependencies. Arrow children are type-equality dependencies, not resource ones. -/
theorem Discharges.resource_head_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) {t : Ty} {c : Constructor}
    (observed : expose a t = .constructor c) :
    RS.head b (t.instantiate σ) =
      ((RS.head a t).1,(RS.head a t).2.map (Ty.instantiate σ)) := by
  have mapped := D.expose_instantiate t
  rw [observed] at mapped
  cases tag : c.tag <;> simp [RS.head,observed,mapped,tag]

/-- Source safety is preserved, rather than reflected: substituting a safe
type for an unconstrained nominal variable can legitimately gain shareability.
The proof closes a greatest-safe predicate over mapped source states. -/
theorem Discharges.resource_safe_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {t : Ty} (sourceSafe : FS.Safe (RS.graph a) t) :
    FS.Safe (RS.graph b) (t.instantiate σ) := by
  let P : Ty → Prop := fun image => FS.Safe (RS.graph b) image ∨
    ∃ source, FS.Safe (RS.graph a) source ∧ image = source.instantiate σ
  have prior (image : Ty) (safe : FS.Safe (RS.graph b) image) :
      (RS.graph b).label image = true ∧
        ∀ child ∈ (RS.graph b).successors image, P child := by
    obtain ⟨good,children⟩ := FS.safe_closed (RS.graph b) image safe
    exact ⟨good,fun child inside => Or.inl (children child inside)⟩
  refine ⟨P,?_,Or.inr ⟨t,sourceSafe,rfl⟩⟩
  intro image related
  rcases related with safe | ⟨source,safe,rfl⟩
  · exact prior image safe
  · obtain ⟨good,children⟩ := FS.safe_closed (RS.graph a) source safe
    have mapped := D.expose_instantiate source
    cases observed : expose a source with
    | nominal index =>
      have listed : a.shareableVariables.contains index = true := by
        simpa [RS.graph,RS.head,observed] using good
      have imageShare : (σ index).shareableUnder b.shareableVariables = true :=
        (D.shareable index).trans listed
      have imageSafe := Obend.Core.ResourceValidity.valid_shareableUnder_shareable valid (σ index) imageShare
      have sameHead : expose b (source.instantiate σ) = expose b (σ index) := by
        simpa only [observed] using mapped
      have transported : RS.shareable b (source.instantiate σ) = true :=
        (RS.shareable_eq_of_expose_eq sameHead).trans imageSafe
      exact prior _ ((RS.shareable_iff _ _).mp transported)
    | unproductive representative =>
      have sameHead : expose b (source.instantiate σ) = .unproductive representative := by
        simpa only [observed] using mapped
      simp [RS.graph,RS.head,sameHead]
    | constructor c =>
      have heads := D.resource_head_instantiate observed
      refine ⟨?_,?_⟩
      · change (RS.head b (source.instantiate σ)).1 = true
        rw [heads]
        exact good
      · intro child inside
        change child ∈ (RS.head b (source.instantiate σ)).2 at inside
        rw [heads] at inside
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp inside
        exact Or.inr ⟨original,children original present,rfl⟩

theorem Discharges.semantic_shareable_instantiate
    {σ : Nat → Ty} {a b : Assumptions} {extra : Nat}
    (D : Discharges σ a b extra) (valid : b.valid = true)
    {t : Ty} (share : RS.shareable a t = true) :
    RS.shareable b (t.instantiate σ) = true :=
  (RS.shareable_iff _ _).mpr
    (D.resource_safe_instantiate valid ((RS.shareable_iff _ _).mp share))

end Obend.Core.Proofs.Templates
