module
/-
# Obend.Slot.Selection — selection soundness, factored out of `Integrity.incumbentTransition`

`astra/ASTRA-SELECTION-20261031.md` §7.1: the policy-independent clause of a stored-selection
policy is SOUNDNESS (whatever it selects is usable at the view), not incumbent retention.
`Integrity.incumbentTransition` implies it (`transition_sound`); so does first-usable re-selection (`churn`,
`churn_sound`), which is NOT incumbent-first (`Integrity.not_transition_churn`) and is still sound;
`sticky` is not (`not_sound_sticky`). Exclusion of retired supports needs only soundness
(`sound_retired`, the policy-independent form of `transition_retired`). The incumbent-first preset's
own choice law is `incumbent_choice`.
-/
public import Obend.Slot.Integrity
@[expose] public section

namespace Obend.Slot
open World

section
variable {V Fact Cand : Type} [World V Fact]

/-- A policy is SOUND when every selection it makes is usable at the view it is made at. -/
def SelectionSound (A : Advance V Fact Cand) : Prop :=
  ∀ (S : Slot Fact Cand) (v : V) (order : List Cand) (stored : Option Cand) (c : Cand),
    A.advance S v order stored = .ok c → S.usable (holdsAt v) c = true

theorem transition_sound {A : Advance V Fact Cand} (hA : Integrity.incumbentTransition A) :
    SelectionSound A :=
  fun S v order stored c h => ((hA S v order stored).2.1 c h).1

/-- First-usable re-selection is sound (though it is not incumbent-first). -/
theorem churn_sound : SelectionSound (churn : Advance V Fact Cand) :=
  fun _ _ _ _ _ h => (select_ok h).2.1

/-- The incumbent-first preset is sound. -/
theorem slotAdvance_sound : SelectionSound (slotAdvance : Advance V Fact Cand) :=
  transition_sound slotFiller_integrity.2

/-- **Retired supports are excluded by every sound policy**: a selection citing a cell retired at
`v` is never made at any later view, whatever the policy keeps or prefers. -/
theorem sound_retired {A : Advance V Fact Cand} (hA : SelectionSound A)
    (S : Slot Fact Cand) (order : List Cand) (stored : Option Cand) {v v' : V} {c : Cand} {f : Fact}
    (hf : f ∈ S.supports c) (hr : pin (Fact := Fact) v (cell f) = none)
    (hl : Later (Fact := Fact) v v') : A.advance S v' order stored ≠ .ok c := by
  intro h
  have live := ((usable_iff S _ c).1 (hA S v' order stored c h)).2 f hf
  rw [dead_behind_forever f hr hl] at live
  cases live

/-- **The incumbent-first choice law**: the stored selection is kept exactly while it is usable;
otherwise the choice is the first usable candidate of the order. -/
theorem incumbent_choice (S : Slot Fact Cand) (v : V) (order : List Cand) (stored : Option Cand)
    (c : Cand) :
    (slotAdvance : Advance V Fact Cand).advance S v order stored = .ok c ↔
      (stored = some c ∧ S.usable (holdsAt v) c = true) ∨
      ((∀ c', stored = some c' → S.usable (holdsAt v) c' = false) ∧
        S.select (holdsAt v) order = .ok c) := by
  show S.advance (holdsAt v) order stored = .ok c ↔ _
  cases stored with
  | none => simp [Slot.advance]
  | some s =>
    by_cases hu : S.usable (holdsAt v) s = true
    · simp only [Slot.advance, hu, ↓reduceIte, Except.ok.injEq, Option.some.injEq]
      constructor
      · intro e; exact .inl ⟨e, e ▸ hu⟩
      · rintro (⟨e, _⟩ | ⟨h, _⟩)
        · exact e
        · rw [h s rfl] at hu; cases hu
    · have hf : S.usable (holdsAt v) s = false := by simpa using hu
      simp only [Slot.advance, hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      constructor
      · intro h; exact .inr ⟨fun c' e => e ▸ hf, h⟩
      · rintro (⟨rfl, h⟩ | ⟨_, h⟩)
        · rw [hf] at h; cases h
        · exact h

/-- Keeping the stored selection whatever the view is not sound. -/
theorem not_sound_sticky : ¬ SelectionSound (sticky : Advance Nat Member Member) := by
  intro h
  have := h toySlot 1 toyOrder (some .alice) .alice rfl
  revert this
  decide

end

end Obend.Slot

end
