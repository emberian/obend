module
/-
# Obend.Slot.Repair — repairing a blocked candidate, and the condition under which it is sound

A REPAIR is an audited step that establishes one support from every view. Repairing every dead
support of a candidate one after another does not make the candidate usable in general: a repair can
retire a requirement that already held, or one an earlier repair established. Astra's countermodel
(`astra/ASTRA-EVAL-20261031.md` line 27): one cell, `f` = "pin is 0", `g` = "pin is 1", a candidate
needing both. Each repair establishes its fact from every view and is an allowed step, both facts
have repairs, and no view makes the candidate usable (`clash_unsat`, `clash_naive`).

COMPATIBILITY (`Repair.Compatible`): the repair preserves every requirement of the candidate that
already holds. Under it, a plan covering the candidate's dead supports makes it usable at a later
view (`repair_sound`). The countermodel's repairs are not compatible (`clash_refused`). A sufficient,
checkable form: the repair moves only the pin of its own fact's cell, and no other requirement of the
candidate is about that cell (`compatible_of_local`), as for `apart`, two requirements on two cells
(`apart_repaired`).

This is validation after repair, not the repair operation: which repair to take, and whether a moved
pin is re-cited rather than resurrected, is the planner's.
-/
public import Obend.Tactic.Tooth
public import Obend.Slot.World
public import Obend.AxiomPin
@[expose] public section

namespace Obend.Slot
open World

theorem Reaches.head {V : Type} {Step : V → V → Prop} {v w w' : V} (s : Step v w)
    (h : Reaches Step w w') : Reaches Step v w' := by
  induction h with
  | refl => exact .tail (.refl _) s
  | tail _ s' ih => exact .tail ih s'

section
variable {V Fact Cand : Type} [World V Fact]

/-- An audited step that establishes `fact` from every view. -/
structure Repair (V Fact : Type) [World V Fact] where
  fact : Fact
  act : V → V
  step : ∀ v, World.Step (Fact := Fact) v (act v)
  establishes : ∀ v, holdsAt (act v) fact = true

/-- The repair preserves every requirement of `c` that holds. -/
def Repair.Compatible (r : Repair V Fact) (S : Slot Fact Cand) (c : Cand) : Prop :=
  ∀ v, ∀ g ∈ S.supports c, holdsAt v g = true → holdsAt (r.act v) g = true

/-- The repair moves the pin of its fact's cell and no other. -/
def Repair.Local (r : Repair V Fact) : Prop :=
  ∀ v (c : World.Cell V), c ≠ cell r.fact → pin (Fact := Fact) (r.act v) c = pin (Fact := Fact) v c

/-- Apply a plan of repairs in order. -/
def applyPlan : List (Repair V Fact) → V → V
  | [], v => v
  | r :: rs, v => applyPlan rs (r.act v)

theorem plan_later (plan : List (Repair V Fact)) (v : V) : Later (Fact := Fact) v (applyPlan plan v) := by
  induction plan generalizing v with
  | nil => exact .refl v
  | cons r rs ih => exact Reaches.head (r.step v) (ih (r.act v))

theorem plan_keeps {S : Slot Fact Cand} {c : Cand} {plan : List (Repair V Fact)}
    (compat : ∀ r ∈ plan, r.Compatible S c) {g : Fact} (hg : g ∈ S.supports c) :
    ∀ v, holdsAt v g = true → holdsAt (applyPlan plan v) g = true := by
  induction plan with
  | nil => exact fun _ h => h
  | cons r rs ih =>
    exact fun v h => ih (fun r' hr' => compat r' (List.mem_cons_of_mem _ hr')) _
      (compat r List.mem_cons_self v g hg h)

theorem plan_establishes {S : Slot Fact Cand} {c : Cand} {plan : List (Repair V Fact)}
    (compat : ∀ r ∈ plan, r.Compatible S c) {r : Repair V Fact} (hr : r ∈ plan)
    (hf : r.fact ∈ S.supports c) : ∀ v, holdsAt (applyPlan plan v) r.fact = true := by
  induction plan with
  | nil => cases hr
  | cons r' rs ih =>
    intro v
    have compat' : ∀ r ∈ rs, r.Compatible S c := fun r h => compat r (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.1 hr with rfl | hr
    · exact plan_keeps compat' hf _ (r.establishes v)
    · exact ih compat' hr _

/-- REPAIR SOUNDNESS under compatibility: a plan of compatible repairs covering every dead support
of a candidate that passes the judge reaches a later view where the candidate is usable. -/
theorem repair_sound (S : Slot Fact Cand) (c : Cand) (plan : List (Repair V Fact)) (v : V)
    (hj : S.judge c = true) (compat : ∀ r ∈ plan, r.Compatible S c)
    (covers : ∀ f ∈ S.dead (holdsAt v) c, ∃ r ∈ plan, r.fact = f) :
    Later (Fact := Fact) v (applyPlan plan v) ∧ S.usable (holdsAt (applyPlan plan v)) c = true := by
  refine ⟨plan_later plan v, (usable_iff S _ c).2 ⟨hj, fun f hf => ?_⟩⟩
  cases hv : holdsAt v f with
  | true => exact plan_keeps compat hf v hv
  | false =>
    obtain ⟨r, hr, rfl⟩ := covers f ((mem_dead_iff S _ c f).2 ⟨hf, hv⟩)
    exact plan_establishes compat hr hf v

#tooth repair_sound by mutation Repair.Compatible := fun {_ _ _} [_] _ _ _ => True

/-- A local repair is compatible with a candidate none of whose other requirements is about the
repaired cell. -/
theorem compatible_of_local (r : Repair V Fact) (hl : r.Local) (S : Slot Fact Cand) (c : Cand)
    (hcell : ∀ g ∈ S.supports c, cell (V := V) g = cell (V := V) r.fact → g = r.fact) : r.Compatible S c := by
  intro v g hg hgv
  by_cases hc : cell (V := V) g = cell (V := V) r.fact
  · rw [hcell g hg hc]; exact r.establishes v
  · rw [holds_congr (r.act v) v g (hl v (cell g) hc)]; exact hgv

end

/-! ## The pin world: Astra's countermodel, refused, and a compatible repair -/

/-- Two cells (`false`, `true`), each holding a natural pin; the fact `(c, n)` says cell `c` holds
`n`. Every step is allowed and nothing retires. -/
instance pinWorld : World (Bool → Nat) (Bool × Nat) where
  Cell := Bool
  Pin := Nat
  cell := Prod.fst
  pin v c := some (v c)
  holdsAt v f := v f.1 == f.2
  Step _ _ := True
  holds_congr := fun v v' f h => by simp only [Option.some.injEq] at h; simp [h]
  retired_dead := fun _ _ h => by cases h
  retired_step := fun _ _ _ _ h => by cases h

/-- Set cell `c`'s pin to `n`. -/
def setPin (c : Bool) (n : Nat) (v : Bool → Nat) : Bool → Nat := fun b => if b = c then n else v b

def pinRepair (c : Bool) (n : Nat) : Repair (Bool → Nat) (Bool × Nat) :=
  ⟨(c, n), setPin c n, fun _ => trivial, fun v => by simp [holdsAt, setPin]⟩

theorem pinRepair_local (c : Bool) (n : Nat) : (pinRepair c n).Local := by
  intro v b hb
  simp only [pin, pinRepair, setPin, cell] at hb ⊢
  simp [hb]

/-- Astra's candidate: cell `false` at pin 0 and at pin 1. -/
def clash : Slot (Bool × Nat) Unit := ⟨fun _ => [(false, 0), (false, 1)], fun _ => true⟩

theorem clash_unsat (v : Bool → Nat) : clash.usable (holdsAt v) () = false := by
  cases h : clash.usable (holdsAt v) ()
  · rfl
  · have := ((usable_iff clash _ ()).1 h).2
    have h0 := this (false, 0) (by simp [clash])
    have h1 := this (false, 1) (by simp [clash])
    simp [holdsAt] at h0 h1
    omega

/-- The naive repair law (each repair an allowed step establishing its fact; every dead support
covered) holds of the clash, and the repaired candidate is not usable. -/
theorem clash_naive :
    (∀ f ∈ clash.dead (holdsAt (fun (_ : Bool) => 2)) (), ∃ r ∈ [pinRepair false 0, pinRepair false 1], r.fact = f) ∧
    clash.usable (holdsAt (applyPlan [pinRepair false 0, pinRepair false 1] fun (_ : Bool) => 2)) () = false :=
  ⟨by decide, clash_unsat _⟩

/-- Compatibility refuses the clash: repairing `pin = 0` retires `pin = 1` where it held. -/
theorem clash_refused : ¬ (pinRepair false 0).Compatible clash () := by
  intro h
  have := h (fun (_ : Bool) => 1) (false, 1) (by simp [clash]) rfl
  simp [holdsAt, pinRepair, setPin] at this

/-- Two requirements on two cells: the local repairs are compatible and repair the candidate. -/
def apart : Slot (Bool × Nat) Unit := ⟨fun _ => [(false, 0), (true, 1)], fun _ => true⟩

theorem apart_repaired :
    apart.usable (holdsAt (fun (_ : Bool) => 2)) () = false ∧
    apart.usable (holdsAt (applyPlan [pinRepair false 0, pinRepair true 1] fun (_ : Bool) => 2)) () = true := by
  refine ⟨rfl, (repair_sound apart () _ _ rfl (fun r hr => ?_) (by decide)).2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    exact compatible_of_local _ (pinRepair_local _ _) apart () (by
      simp only [apart, List.mem_cons, List.not_mem_nil, or_false]
      rintro g (rfl | rfl) h <;> simp_all [cell, pinRepair])

#assert_axioms Reaches.head plan_later plan_keeps plan_establishes repair_sound compatible_of_local
  pinRepair_local clash_unsat clash_naive clash_refused apart_repaired

end Obend.Slot
end
