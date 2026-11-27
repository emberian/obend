module
public import Obend.Category.FiberGrowth

/-! A predicate descends through an observation if a reader can state it entirely in the
observed coordinates. The resulting predicate lives in Prop. Obtaining an executable
decision or a uniform tracker requires further evidence. -/
public section
namespace Obend.Category.ObservationDescent
open Obend.Category.Projection Obend.Category.FiberGrowth
set_option autoImplicit false

universe u v z
variable {World : Type u} {View : Type v} {Coarse : Type z}

/-- Agreement with a predicate of the view on every represented world. -/
def Descends (observe : World → View) (P : World → Prop) : Prop :=
  ∃ Q : View → Prop, ∀ w, P w ↔ Q (observe w)

theorem descends_iff_invariant (observe : World → View) (P : World → Prop) :
    Descends observe P ↔ ∀ a b, observe a = observe b → (P a ↔ P b) := by
  constructor
  · rintro ⟨Q, hQ⟩ a b hab
    rw [hQ a, hQ b, hab]
  · intro h
    refine ⟨existsAlong observe P, fun w => ⟨fun hw => ⟨w, rfl, hw⟩, ?_⟩⟩
    rintro ⟨a, ha, hp⟩
    exact (h a w ha).mp hp

/-- On a represented observation, possible and certain agree exactly when all its
worlds agree. Empty fibers must be excluded: possibility is false and certainty true. -/
theorem descends_iff_modal_agreement (observe : World → View) (P : World → Prop) :
    Descends observe P ↔
      ∀ w, existsAlong observe P (observe w) ↔ forallAlong observe P (observe w) := by
  rw [descends_iff_invariant]
  constructor
  · intro h w
    constructor
    · rintro ⟨a, ha, hp⟩ b hb
      exact (h a b (ha.trans hb.symm)).mp hp
    · intro hAll
      exact ⟨w, rfl, hAll w rfl⟩
  · intro h a b hab
    exact ⟨fun hp => ((h a).mp ⟨a, rfl, hp⟩) b hab.symm,
      fun hp => ((h b).mp ⟨b, rfl, hp⟩) a hab⟩

/-- After a view forgets information, an old possibility remains possible and a new
certainty was already certain in the finer view. -/
theorem forget_view (observe : World → View) (forget : View → Coarse) (P : World → Prop)
    (v : View) :
    (forallAlong (forget ∘ observe) P (forget v) → forallAlong observe P v) ∧
      (existsAlong observe P v → existsAlong (forget ∘ observe) P (forget v)) := by
  constructor
  · intro h w hw
    exact h w (congrArg forget hw)
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, congrArg forget hw, hp⟩

/-- A fresh world with the same observation as a source can share a classifier with
the old worlds exactly when they had a classifier and the new answer agrees with the
source's. The retained predicate may be written differently after the extension. -/
theorem descends_insert_copy_iff (observe : World → View) (source : World)
    (pre : World → Prop) (post : Option World → Prop)
    (keep : ∀ w, post (some w) ↔ pre w) :
    Descends (insert observe (observe source)) post ↔
      Descends observe pre ∧ (post none ↔ pre source) := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨⟨Q, fun w => (keep w).symm.trans (hQ (some w))⟩, ?_⟩
    exact (hQ none).trans ((hQ (some source)).symm.trans (keep source))
  · rintro ⟨⟨Q, hQ⟩, fresh⟩
    refine ⟨Q, ?_⟩
    intro w
    cases w with
    | none => exact fresh.trans (hQ source)
    | some w => exact (keep w).trans (hQ w)

end Obend.Category.ObservationDescent
end
