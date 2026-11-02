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
public section

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

/-! ## Cost-Ordered / Priority-Monotone Selection Policy (`prioritySelect`, `priorityAdvance`) -/

section
variable {Fact Cand : Type}

/-- Pick the candidate with minimum `cost` from a non-empty list, preserving first-seen on ties. -/
@[expose] def pickMinCost (cost : Cand → Nat) (best : Cand) : List Cand → Cand
  | [] => best
  | c :: cs =>
    if cost c < cost best then pickMinCost cost c cs
    else pickMinCost cost best cs

theorem pickMinCost_mem (cost : Cand → Nat) :
    ∀ (cs : List Cand) (best : Cand), pickMinCost cost best cs ∈ best :: cs
  | [], best => List.Mem.head []
  | c :: cs, best => by
    simp only [pickMinCost]
    split
    · exact List.Mem.tail best (pickMinCost_mem cost cs c)
    · rcases List.mem_cons.mp (pickMinCost_mem cost cs best) with heq | hmem
      · rw [heq]; exact List.Mem.head (c :: cs)
      · exact List.Mem.tail best (List.Mem.tail c hmem)

theorem pickMinCost_le (cost : Cand → Nat) :
    ∀ (cs : List Cand) (best : Cand) (x : Cand),
      x ∈ best :: cs → cost (pickMinCost cost best cs) ≤ cost x
  | [], best, x, hx => by
    rcases List.mem_singleton.mp hx with rfl
    exact Nat.le_refl _
  | c :: cs, best, x, hx => by
    simp only [pickMinCost]
    split
    · rename_i hlt
      rcases List.mem_cons.mp hx with heq | hx_tl
      · rw [heq]
        have hle_c := pickMinCost_le cost cs c c (List.Mem.head cs)
        omega
      · exact pickMinCost_le cost cs c x hx_tl
    · rename_i hge
      rcases List.mem_cons.mp hx with heq | hx_tl
      · rw [heq]
        exact pickMinCost_le cost cs best best (List.Mem.head cs)
      · rcases List.mem_cons.mp hx_tl with heq2 | hx_rest
        · rw [heq2]
          have hle_best := pickMinCost_le cost cs best best (List.Mem.head cs)
          omega
        · exact pickMinCost_le cost cs best x (List.Mem.tail best hx_rest)

/-- Cost-ordered selection at a view: selects the usable candidate from `order` that minimizes
    `cost`, or refuses naming every candidate's dead supports if none is usable. -/
@[expose] def prioritySelect (S : Slot Fact Cand) (holds : Fact → Bool) (order : List Cand)
    (cost : Cand → Nat := fun _ => 0) : Except (Refusal Fact Cand) Cand :=
  match S.alternatives holds order with
  | [] => .error (order.map fun c => (c, S.dead holds c))
  | c :: cs => .ok (pickMinCost cost c cs)

theorem prioritySelect_ok {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand}
    {cost : Cand → Nat} {c : Cand}
    (h : prioritySelect S holds order cost = .ok c) :
    c ∈ order ∧ S.usable holds c = true ∧ ∀ u ∈ S.alternatives holds order, cost c ≤ cost u := by
  unfold prioritySelect at h
  cases ha : S.alternatives holds order with
  | nil => rw [ha] at h; cases h
  | cons head tail =>
    rw [ha] at h
    injection h with hc_eq
    subst hc_eq
    have hmem_alt : pickMinCost cost head tail ∈ S.alternatives holds order := by
      rw [ha]
      exact pickMinCost_mem cost tail head
    have hfilt : pickMinCost cost head tail ∈ order.filter (S.usable holds) := hmem_alt
    rw [List.mem_filter] at hfilt
    refine ⟨hfilt.1, hfilt.2, ?_⟩
    intro u hu
    exact pickMinCost_le cost tail head u hu

end

section
variable {V Fact Cand : Type} [World V Fact]

/-- Priority-monotone stored-selection advance policy:
    - If a stored selection `s` is usable at `v`, keeps `s` unless a usable candidate in `order`
      has strictly lower `cost` (`cost best < cost s`), in which case it upgrades to `best`.
    - If `stored = none` or `s` is no longer usable at `v`, selects the minimum-cost usable
      candidate via `prioritySelect`. -/
@[expose] def priorityAdvance (cost : Cand → Nat := fun _ => 0) : Advance V Fact Cand where
  advance S v order stored :=
    match stored with
    | some s =>
      if S.usable (holdsAt v) s then
        match prioritySelect S (holdsAt v) order cost with
        | .ok best => if cost best < cost s then .ok best else .ok s
        | .error _ => .ok s
      else
        prioritySelect S (holdsAt v) order cost
    | none => prioritySelect S (holdsAt v) order cost

/-- Soundness of `priorityAdvance`: every candidate selected by `priorityAdvance` is usable at `v`. -/
theorem priorityAdvance_sound {cost : Cand → Nat} :
    SelectionSound (priorityAdvance cost : Advance V Fact Cand) := by
  intro S v order stored c h
  unfold priorityAdvance at h
  dsimp only at h
  cases stored with
  | none =>
    exact (prioritySelect_ok h).2.1
  | some s =>
    by_cases hs : S.usable (holdsAt v) s = true
    · simp only [hs, ↓reduceIte] at h
      cases hp : prioritySelect S (holdsAt v) order cost with
      | ok best =>
        rw [hp] at h
        dsimp only at h
        split at h
        · injection h with heq; subst heq; exact (prioritySelect_ok hp).2.1
        · injection h with heq; subst heq; exact hs
      | error _ =>
        rw [hp] at h
        injection h with heq; subst heq; exact hs
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      exact (prioritySelect_ok h).2.1

/-- Priority monotonicity: when `stored = some s` is usable at `v`, `priorityAdvance` never
    increases the cost (`cost c ≤ cost s`). -/
theorem priorityAdvance_monotone {cost : Cand → Nat} (S : Slot Fact Cand) (v : V)
    (order : List Cand) (s c : Cand)
    (hs : S.usable (holdsAt v) s = true)
    (h : (priorityAdvance cost).advance S v order (some s) = .ok c) :
    cost c ≤ cost s := by
  unfold priorityAdvance at h
  simp only [hs, ↓reduceIte] at h
  cases hp : prioritySelect S (holdsAt v) order cost with
  | ok best =>
    rw [hp] at h
    dsimp only at h
    split at h
    · rename_i hlt
      injection h with heq; subst heq; omega
    · injection h with heq; subst heq; exact Nat.le_refl _
  | error _ =>
    rw [hp] at h
    injection h with heq; subst heq; exact Nat.le_refl _

end

end Obend.Slot

end
