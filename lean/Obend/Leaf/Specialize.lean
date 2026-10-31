module
/-
# Obend.Leaf.Specialize — the emitted book as a candidate of a slot

DESIGN §7: an emitted leaf is a candidate whose supports are the pins it assumed, the machine is
the always-usable fallback, and deoptimization is the withdrawal of a support. This is the slot
(`Obend.Slot`) over two kinds of candidate, with no new slot theory:

* `Candidate.book name C`: the book `emit C` for the object `name`; its supports are the pins of the
  layers it flattened (`LeafCell.layer key ↦ L.code`) and of the object's composition, the layers in
  order and the seed (`LeafCell.object name ↦ C.code`); its judge admits compositions in the scope of
  `flatten_sound` (`Composition.closedB`);
* `Candidate.machine`: the unflattened term, no supports, always usable (`machine_usable`).

A view (`LeafView`) says what each cell holds now; `viewOf` is the view a program's object gives.
The read is the slot's: `book_usable_sound` says a usable book is the book of the composition the
view holds, so it computes what that object computes (`book_sound`); `specialize_choice` is the
incumbent-first law (`incumbent_choice`) at the order `[book, machine]`: the stored book is kept
exactly while its supports hold, else the machine is selected; `moved_pin_blocks` is
`read_blocked_exact`: a support that no longer holds blocks the book, and the read names it.
`specialize_integrity` is `slotFiller_integrity` at this world.
-/
public import Obend.Leaf.Emit
public import Obend.Slot.Selection
@[expose] public section
namespace Obend.Leaf
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
set_option autoImplicit false

/-- What a support pins: a layer under its key, or an object's composition under its name. -/
inductive LeafCell where
  | layer (key : String)
  | object (name : String)
  deriving DecidableEq, Repr

/-- A support: the cell, and the code it held when the book was emitted. -/
structure LeafPin where
  cell : LeafCell
  code : Term

/-- A view: a clock, and what each cell holds now (`none`: absent). -/
structure LeafView where
  clock : Nat
  decl : LeafCell → Option Term

/-- The world of the specialization slot: each cell pinned to its code at the view's clock; a step
moves the clock forward. A support holds when its cell holds the code it pinned (`termEq`, so the
pin is exact: no collision disjunct is owed). -/
instance : World LeafView LeafPin where
  Cell := LeafCell
  Pin := Nat × Option Term
  cell := LeafPin.cell
  pin v c := some (v.clock, v.decl c)
  holdsOfPin _ p f := match p with
    | some (_, some t) => Obend.Law.termEq t f.code
    | _ => false
  Step v v' := v.clock < v'.clock
  dead_none _ := rfl
  retired_step _ _ _ _ h := by cases h
  Ver := Nat × Option Term
  ver v c := (v.clock, v.decl c)
  Past a b := a.1 < b.1
  past_irrefl _ := Nat.lt_irrefl _
  past_trans _ _ _ := Nat.lt_trans
  pinOf _ := some
  pin_ver _ _ := rfl
  ver_step _ _ _ h := .inr h

/-- The view a program's object gives: each of its layers under its key, its composition under its
name. -/
def viewOf (clock : Nat) (name : String) (C : Composition) : LeafView where
  clock := clock
  decl
    | .layer k => (C.layers.find? (·.name == k)).map Layer.code
    | .object n => if n == name then some C.code else none

/-- The candidates of the specialization slot. -/
inductive Candidate where
  /-- the book `emit comp`, for the object `name` -/
  | book (name : String) (comp : Composition)
  /-- the machine: the unflattened term -/
  | machine

/-- The pins a book assumed: its object's composition and each layer it flattened. -/
def Candidate.supports : Candidate → List LeafPin
  | .book name C => ⟨.object name, C.code⟩ :: C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .machine => []

/-- A book is admitted for compositions in the scope of `flatten_sound`; the machine always. -/
def Candidate.judge : Candidate → Bool
  | .book _ C => C.closedB
  | .machine => true

/-- **The specialization slot.** -/
def specSlot : Slot LeafPin Candidate := ⟨Candidate.supports, Candidate.judge⟩

/-- The order a chooser gives: the book first, the machine as the fallback. -/
def specOrder (name : String) (C : Composition) : List Candidate := [.book name C, .machine]

theorem holdsAt_eq (v : LeafView) (p : LeafPin) :
    holdsAt v p = match v.decl p.cell with
      | some t => Obend.Law.termEq t p.code
      | none => false := by
  show (match some (v.clock, v.decl p.cell) with
    | some (_, some t) => Obend.Law.termEq t p.code
    | _ => false) = _
  cases v.decl p.cell <;> rfl

/-- **The machine is always usable.** -/
theorem machine_usable (v : LeafView) : specSlot.usable (holdsAt v) .machine = true := by
  simp [Slot.usable, Slot.dead, specSlot, Candidate.supports, Candidate.judge]

/-- **A usable book is the book of the view's composition**: the view's object has the code the book
pinned, so it emits the same book, and (when that object is closed, as an elaborated program's is)
every member the book computes is the member that object computes. -/
theorem book_usable_sound {k : Nat} {name : String} {C C' : Composition}
    (h : specSlot.usable (holdsAt (viewOf k name C')) (.book name C) = true) :
    emit C = emit C' ∧ (C'.closedB = true → ∀ m, .get (emit C).link m ≈b .get C'.object m) := by
  obtain ⟨_, hall⟩ := (usable_iff _ _ _).1 h
  have ho := hall ⟨.object name, C.code⟩ (by simp [specSlot, Candidate.supports])
  rw [holdsAt_eq] at ho
  simp only [viewOf, beq_self_eq_true, ite_true] at ho
  have e : emit C = emit C' := emit_congr (termEq_sound' ho).symm
  exact ⟨e, fun hc m => e ▸ book_sound C' hc m⟩

/-- **Incumbent-first, at the order `[book, machine]`**: a stored book is kept exactly while it is
usable; otherwise the machine is selected. `incumbent_choice`, applied. -/
theorem specialize_choice (v : LeafView) (name : String) (C : Composition) :
    (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot v (specOrder name C)
        (some (.book name C)) =
      if specSlot.usable (holdsAt v) (.book name C) then .ok (.book name C) else .ok .machine := by
  split
  · rename_i hu
    exact (incumbent_choice specSlot v _ _ _).2 (.inl ⟨rfl, hu⟩)
  · rename_i hu
    have hf : specSlot.usable (holdsAt v) (.book name C) = false := by simpa using hu
    refine (incumbent_choice specSlot v _ _ _).2 (.inr ⟨fun c e => by cases e; exact hf, ?_⟩)
    simp [Slot.select, Slot.alternatives, specOrder, hf, machine_usable]

/-- **A moved pin blocks the book by name**: when a support of an admitted book does not hold at a
view, the book's read there is blocked, and the blocked read names exactly the supports that do not
hold, this one among them. `read_blocked_exact`, applied. -/
theorem moved_pin_blocks {v : LeafView} {name : String} {C : Composition} (hj : C.closedB = true)
    {p : LeafPin} (hp : p ∈ (Candidate.book name C).supports) (hd : holdsAt v p = false) :
    ∃ d, specSlot.read (holdsAt v) (some (.book name C)) = .blocked (.book name C) d ∧ p ∈ d ∧
      ∀ q, q ∈ d ↔ q ∈ (Candidate.book name C).supports ∧ holdsAt v q = false := by
  have hmem : p ∈ specSlot.dead (holdsAt v) (.book name C) := (mem_dead_iff _ _ _ _).2 ⟨hp, hd⟩
  have hjudge : specSlot.judge (.book name C) = true := hj
  have hread : ∃ d, specSlot.read (holdsAt v) (some (.book name C)) = .blocked (.book name C) d ∧ p ∈ d := by
    unfold Slot.read
    simp only [hjudge, ite_true]
    cases hdd : specSlot.dead (holdsAt v) (.book name C) with
    | nil => rw [hdd] at hmem; cases hmem
    | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩
  obtain ⟨d, hr, hpd⟩ := hread
  exact ⟨d, hr, hpd, (read_blocked_exact specSlot _ _ _ _ hr).2⟩

/-- The specialization slot's filler and advance have CONTEXTUAL INTEGRITY ∧ TRANSITION. -/
theorem specialize_integrity :
    Integrity (slotFiller : Filler LeafView LeafPin Candidate) (slotAdvance : Advance LeafView LeafPin Candidate) :=
  slotFiller_integrity

end Obend.Leaf
end
