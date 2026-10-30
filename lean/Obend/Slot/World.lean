module
/-
# Obend.Slot.World — the history a slot's supports are judged against

A slot (`Obend.Slot`) judges a candidate at a VIEW by asking whether each support it cites holds
there. This module says what a view is, abstractly: a `World` has views `V`, cells, and for each view
the PIN a cell holds there (a version; `none` once the cell is retired), a support `Fact` names a cell
and holds or not at a view, and views are joined by an audited `Step`. Three laws are fields, each
the abstract shape of a nano kernel theorem:

- `holds_congr` (`receive_congr`, `Kernel/Proofs/Receive.lean`): a support's truth at a view is a
  function of the pin its cell holds there, so a derivation depends only on the pinned view;
- `retired_dead`: a support of a retired cell does not hold;
- `retired_step` (`stale_behind_forever`, `Kernel/Proofs/Versions.lean`, the retirement case): a
  tombstone is terminal, so a cell retired at a view is retired at every view a step reaches.

From these: a support whose cell is retired is dead at every later view (`dead_behind_forever`), a
selection citing it stays blocked by that name (`blocked_forever`, `slot_repair`'s third clause with
retirement in place of `Permanent`), and two views that agree on the pins of a candidate's supports
read and resolve a slot the same (`read_congr`, `select_congr`). Not here: nano's forward-only
VERSION law (a pin that moved never returns, up to a hash collision on the pin inputs): a support
here is a fact about a cell, judged by the cell's current pin; which pins are "behind" is the
instance's business.
-/
public import Obend.Slot
public import Obend.AxiomPin
@[expose] public section

namespace Obend.Slot

/-- Views reachable by zero or more steps of `Step`. -/
inductive Reaches {V : Type} (Step : V → V → Prop) : V → V → Prop
  | refl (v : V) : Reaches Step v v
  | tail {v w w' : V} : Reaches Step v w → Step w w' → Reaches Step v w'

/-- A World: views, cells with the pin each view holds for them, supports about cells, and audited
steps, with the three laws the top clause needs. `Fact` is determined by `V`: a World's views come
with the supports they can be asked about. -/
class World (V : Type) (Fact : outParam Type) where
  /-- a cell (or a row slot: whatever a pin names) -/
  Cell : Type
  /-- a pin: the version a view holds for a cell -/
  Pin : Type
  /-- the cell a support is about -/
  cell : Fact → Cell
  /-- what a view holds for a cell: its pin, or `none` once the cell is retired -/
  pin : V → Cell → Option Pin
  /-- whether a support holds at a view -/
  holdsAt : V → Fact → Bool
  /-- one audited step between views -/
  Step : V → V → Prop
  /-- a support's truth at a view is a function of the pin its cell holds there -/
  holds_congr : ∀ (v v' : V) (f : Fact), pin v (cell f) = pin v' (cell f) → holdsAt v f = holdsAt v' f
  /-- a support of a retired cell does not hold -/
  retired_dead : ∀ (v : V) (f : Fact), pin v (cell f) = none → holdsAt v f = false
  /-- a tombstone is terminal: a cell retired at a view is retired after a step -/
  retired_step : ∀ (v v' : V) (c : Cell), Step v v' → pin v c = none → pin v' c = none

namespace World

variable {V Fact : Type} [World V Fact]

/-- Views reachable by zero or more audited steps. -/
abbrev Later (v v' : V) : Prop := Reaches (World.Step (V := V) (Fact := Fact)) v v'

/-- A retired cell stays retired at every later view. -/
theorem retired_later {v v' : V} (c : World.Cell V) (h : Later (Fact := Fact) v v')
    (hr : pin (Fact := Fact) v c = none) : pin (Fact := Fact) v' c = none := by
  induction h with
  | refl => exact hr
  | tail _ step ih => exact retired_step _ _ c step ih

/-- A support whose cell is retired at a view is dead at every later view. -/
theorem dead_behind_forever {v v' : V} (f : Fact) (hr : pin (Fact := Fact) v (cell f) = none)
    (h : Later (Fact := Fact) v v') : holdsAt v' f = false :=
  retired_dead v' f (retired_later (cell f) h hr)

section
variable {Cand : Type}

/-- Two views agreeing on the pins of a candidate's supports agree on which of them hold. -/
theorem holds_agree (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    ∀ f ∈ S.supports c, holdsAt v f = holdsAt v' f :=
  fun f hf => holds_congr v v' f (agree f hf)

/-- The dead supports of a candidate are the same at two views agreeing on its supports' pins. -/
theorem dead_congr (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    S.dead (holdsAt v) c = S.dead (holdsAt v') c := by
  unfold Slot.dead
  exact List.filter_congr fun f hf => by rw [holds_agree S c agree f hf]

/-- Whether a candidate is usable is the same at two views agreeing on its supports' pins. -/
theorem usable_congr (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    S.usable (holdsAt v) c = S.usable (holdsAt v') c := by
  unfold Slot.usable
  rw [dead_congr S c agree]

/-- A derivation depends only on the pinned view: two views agreeing on the pins of a selection's
supports read it the same. -/
theorem read_congr (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    S.read (holdsAt v) (some c) = S.read (holdsAt v') (some c) := by
  have ev : S.evidence (holdsAt v) c = S.evidence (holdsAt v') c := by
    unfold Slot.evidence
    exact List.map_congr_left fun f hf => by rw [holds_agree S c agree f hf]
  simp only [Slot.read]
  rw [dead_congr S c agree, ev]

/-- The usable candidates of an order are the same at two views agreeing on the pins of all their
supports. -/
theorem alternatives_congr (S : Slot Fact Cand) {v v' : V} (order : List Cand)
    (agree : ∀ c ∈ order, ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    S.alternatives (holdsAt v) order = S.alternatives (holdsAt v') order := by
  unfold Slot.alternatives
  exact List.filter_congr fun c hc => usable_congr S c (agree c hc)

/-- `slot_repair`'s third clause with retirement for `Permanent`: a selection citing a support whose
cell is retired at `v` reads blocked, by that support's name, at every later view. -/
theorem blocked_forever (S : Slot Fact Cand) {v v' : V} (c : Cand) (f : Fact) (hf : f ∈ S.supports c)
    (hr : pin (Fact := Fact) v (cell f) = none) (h : Later (Fact := Fact) v v') (hj : S.judge c = true) :
    ∃ d, S.read (holdsAt v') (some c) = .blocked c d ∧ f ∈ d := by
  have hdead : holdsAt v' f = false := dead_behind_forever f hr h
  have hmem : f ∈ S.dead (holdsAt v') c := (mem_dead_iff S _ c f).2 ⟨hf, hdead⟩
  unfold Slot.read
  simp only [hj, if_true]
  cases hd : S.dead (holdsAt v') c with
  | nil => rw [hd] at hmem; cases hmem
  | cons g t => exact ⟨g :: t, rfl, hd ▸ hmem⟩

end

#assert_axioms retired_later dead_behind_forever holds_agree dead_congr usable_congr read_congr alternatives_congr
  blocked_forever

end World
end Obend.Slot
end
