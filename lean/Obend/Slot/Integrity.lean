module
/-
# Obend.Slot.Integrity — CONTEXTUAL INTEGRITY ∧ REPAIR, over an abstract World

The top clause of the contextual layer (DESIGN-CTX §2.4, B4 and B4′), stated of a FILLER: the part of
a system that, at a view, fills a slot from the chooser's order or refuses. The slot's own filler
(`slotFiller`, `Slot.resolve` without the body) satisfies it over EVERY World, from `resolve_ok`,
`resolve_error`, `read_blocked_names` and the World's laws (`slotFiller_integrity`): nothing here is
stated with a premise beyond the `World` class.

B4, CONTEXTUAL INTEGRITY (`Integrity.contextual`): an admitted filling is a committed candidate (in
the order), typed at the interface (passes the judge), with every support it cites holding on the
view, and it is the one the chooser's order names (the first usable); a refusal names, for every
candidate of the order, the coordinate of a justification that did not hold: its dead supports, or
the judge when none is dead (why-not completeness). B4′, REPAIR (`Integrity.repair`): a justification
withdrawn stays withdrawn (a candidate citing a cell retired at a view is never filled at any later
view), and a slot with a usable candidate in the order is fillable now.

THE FLOOR, each refuted on the toy World (two members, one grant revoked at height 1):
`credulousHoles` (judges, ignores supports), `firstCandidate` (ignores both), `blindRefusal` (the
slot's selection, a refusal that names nothing). The toy also inhabits the non-trivial case: filled by
candidate 0 at height 0, the stored selection reads blocked by the revoked grant's name at height 1,
and the slot fills by candidate 1 there (`toy_repair`).
-/
public import Obend.Tactic.Tooth
public import Obend.Slot.World
public import Obend.Slot.Calculus
public import Obend.AxiomPin
@[expose] public section

namespace Obend.Slot
open World

/-- How a system fills a slot at a view from the chooser's order: a candidate, or a refusal naming,
per candidate, what failed. -/
structure Filler (V Fact Cand : Type) where
  fill : Slot Fact Cand → V → List Cand → Except (Refusal Fact Cand) Cand

section
variable {V Fact Cand : Type} [World V Fact]

/-- The slot's own selection at a view: the first usable candidate of the order, or the refusal
naming every candidate's dead supports. `Slot.resolve` is this with a body (`resolve_eq_select`). -/
def Slot.select (S : Slot Fact Cand) (holds : Fact → Bool) (order : List Cand) :
    Except (Refusal Fact Cand) Cand :=
  match S.alternatives holds order with
  | c :: _ => .ok c
  | [] => .error (order.map fun c => (c, S.dead holds c))

theorem resolve_eq_select {Ix : Type} {Sg : Protocol.Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    (S : Slot Fact Cand) (holds : Fact → Bool) {i : Ix} (body : Cand → Protocol.Prot Sg Hole A i)
    (order : List Cand) : S.resolve holds body order = (S.select holds order).map body := by
  unfold Slot.resolve Slot.select
  cases S.alternatives holds order <;> rfl

/-- The filler a slot gives. -/
def slotFiller : Filler V Fact Cand := ⟨fun S v order => S.select (holdsAt v) order⟩

/-- B4. CONTEXTUAL INTEGRITY. -/
def Integrity.contextual (F : Filler V Fact Cand) : Prop :=
  ∀ (S : Slot Fact Cand) (v : V) (order : List Cand),
    (∀ c, F.fill S v order = .ok c →
      c ∈ order ∧ S.judge c = true ∧ (∀ f ∈ S.supports c, holdsAt v f = true) ∧
      ∃ rest, S.alternatives (holdsAt v) order = c :: rest) ∧
    (∀ w, F.fill S v order = .error w → ∀ c ∈ order,
      ∃ d, (c, d) ∈ w ∧ (∀ f ∈ d, f ∈ S.supports c ∧ holdsAt v f = false) ∧ (d = [] → S.judge c = false))

/-- B4′. REPAIR. -/
def Integrity.repair (F : Filler V Fact Cand) : Prop :=
  ∀ (S : Slot Fact Cand) (order : List Cand),
    (∀ (v v' : V) (c : Cand) (f : Fact), f ∈ S.supports c → pin (Fact := Fact) v (cell f) = none →
      Later (Fact := Fact) v v' → F.fill S v' order ≠ .ok c) ∧
    (∀ (v : V) (c : Cand), c ∈ order → S.usable (holdsAt v) c = true → ∃ c', F.fill S v order = .ok c')

/-- CONTEXTUAL INTEGRITY ∧ REPAIR. -/
def Integrity (F : Filler V Fact Cand) : Prop := Integrity.contextual F ∧ Integrity.repair F

theorem select_ok {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand} {c : Cand}
    (h : S.select holds order = .ok c) :
    c ∈ order ∧ S.usable holds c = true ∧ ∃ rest, S.alternatives holds order = c :: rest := by
  unfold Slot.select at h
  cases ha : S.alternatives holds order with
  | nil => rw [ha] at h; cases h
  | cons c' rest =>
    rw [ha] at h
    have hc : c' ∈ order.filter (S.usable holds) := by
      show c' ∈ S.alternatives holds order; rw [ha]; exact List.mem_cons_self
    rw [List.mem_filter] at hc
    cases h
    exact ⟨hc.1, hc.2, rest, rfl⟩

theorem select_error {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand} {w : Refusal Fact Cand}
    (h : S.select holds order = .error w) :
    (∀ c ∈ order, S.usable holds c = false) ∧ w = order.map fun c => (c, S.dead holds c) := by
  unfold Slot.select at h
  cases ha : S.alternatives holds order with
  | cons c rest => rw [ha] at h; cases h
  | nil =>
    rw [ha] at h
    cases h
    refine ⟨fun c hc => ?_, rfl⟩
    have : c ∉ order.filter (S.usable holds) := by
      show c ∉ S.alternatives holds order; rw [ha]; simp
    simpa [List.mem_filter, hc] using this

/-- The slot's own filler has CONTEXTUAL INTEGRITY ∧ REPAIR over every World. -/
theorem slotFiller_integrity : Integrity (slotFiller : Filler V Fact Cand) := by
  refine ⟨fun S v order => ⟨fun c h => ?_, fun w h c hc => ?_⟩, fun S order => ⟨?_, ?_⟩⟩
  · obtain ⟨hmem, hu, rest, ha⟩ := select_ok h
    obtain ⟨hj, hholds⟩ := (usable_iff S _ c).1 hu
    exact ⟨hmem, hj, hholds, rest, ha⟩
  · obtain ⟨hnone, rfl⟩ := select_error h
    refine ⟨S.dead (holdsAt v) c, List.mem_map.2 ⟨c, hc, rfl⟩, fun f hf => (mem_dead_iff S _ c f).1 hf, fun hd => ?_⟩
    have := hnone c hc
    unfold Slot.usable at this
    rw [hd] at this
    simpa using this
  · intro v v' c f hf hr hl h
    obtain ⟨-, hu, -⟩ := select_ok h
    have hdead : holdsAt v' f = false := dead_behind_forever f hr hl
    have := ((usable_iff S _ c).1 hu).2 f hf
    rw [hdead] at this
    cases this
  · intro v c hc hu
    have hmem : c ∈ S.alternatives (holdsAt v) order := List.mem_filter.2 ⟨hc, hu⟩
    show ∃ c', S.select (holdsAt v) order = .ok c'
    unfold Slot.select
    cases ha : S.alternatives (holdsAt v) order with
    | nil => rw [ha] at hmem; cases hmem
    | cons c' rest => exact ⟨c', rfl⟩

/-- A calculus filling selected by the integrity-preserving filler has semantic
typing, independently of the budget used to discover its certificate. -/
theorem slotFiller_typed {Tm R : Type} [Calculus Tm] [Obend.Core.Graded R] [Decides R Tm]
    (budget : Budget R) (Ψ : Calculus.Ctx Tm) (A : Calculus.Ty Tm)
    (supports : Tm → List Fact) (v : V) (order : List Tm) (t : Tm)
    (h : (slotFiller : Filler V Fact Tm).fill
      (Calculus.slotOf budget Ψ A supports) v order = .ok t) : Calculus.Typed Ψ t A := by
  obtain ⟨_, hu, _⟩ := select_ok h
  exact (Calculus.slotOf_usable budget Ψ A supports (holdsAt v) t hu).1

/-- When a budgeted slot refuses a candidate whose ordinary supports all hold,
its named explanation is precisely `uncovered` at the declared grade. This
connects admission diagnostics to the actual integrity-preserving filler. -/
theorem slotFiller_uncovered {Tm R : Type} [Calculus Tm] [Obend.Core.Graded R] [Decides R Tm]
    (budget : Budget R) (Ψ : Calculus.Ctx Tm) (A : Calculus.Ty Tm)
    (supports : Tm → List Fact) (v : V) (order : List Tm) (t : Tm)
    (w : Refusal Fact Tm)
    (h : (slotFiller : Filler V Fact Tm).fill
      (Calculus.slotOf budget Ψ A supports) v order = .error w)
    (member : t ∈ order) (live : ∀ f ∈ supports t, holdsAt v f = true) :
    Calculus.admit budget Ψ A t = .error (.uncovered budget.grade) := by
  have refused := (select_error h).1 t member
  have dead : (Calculus.slotOf budget Ψ A supports).dead (holdsAt v) t = [] :=
    (dead_eq_nil_iff _ _ _).2 live
  unfold Slot.usable at refused
  rw [dead] at refused
  have checkFalse : Decides.check budget.grade Ψ t A = false := by
    simpa only [Calculus.slotOf, List.isEmpty_nil, Bool.and_true] using refused
  simp [Calculus.admit, checkFalse]

/-! ## The floor -/

/-- Judges, ignores supports: `supportLive := fun _ => true`. -/
def credulousHoles : Filler V Fact Cand :=
  ⟨fun S _ order => match order.filter S.judge with
    | c :: _ => .ok c
    | [] => .error (order.map fun c => (c, []))⟩

/-- Ignores the supports and the judge: fills with the first candidate. -/
def firstCandidate : Filler V Fact Cand :=
  ⟨fun _ _ order => match order with
    | c :: _ => .ok c
    | [] => .error []⟩

/-- The slot's selection, but a refusal that names nothing. -/
def blindRefusal : Filler V Fact Cand :=
  ⟨fun S v order => match S.alternatives (holdsAt v) order with
    | c :: _ => .ok c
    | [] => .error []⟩

end

/-! ## The toy World: two members, one grant revoked -/

inductive Member where
  | alice
  | bob
  deriving DecidableEq, Repr

/-- Alice's grant is live at height 0 and retired from height 1 on; Bob's is live throughout. -/
def toyPin : Nat → Member → Option Unit
  | height, .alice => if height < 1 then some () else none
  | _, .bob => some ()

/-- Views are heights; a support is "this member's grant is live"; one step is one height. -/
instance toyWorld : World Nat Member where
  Cell := Member
  Pin := Unit
  cell := id
  pin := toyPin
  holdsAt height member := (toyPin height member).isSome
  Step height height' := height' = height + 1
  holds_congr := fun _ _ _ h => by simp only [id] at h; rw [h]
  retired_dead := fun _ _ h => by simp only [id] at h; rw [h]; rfl
  retired_step := fun v v' c step h => by
    subst step
    cases c with
    | alice =>
      simp only [toyPin] at h ⊢
      split at h
      · cases h
      · rw [if_neg (by omega)]
    | bob => simp [toyPin] at h

/-- Each member's candidate cites that member's grant; the judge accepts both. -/
def toySlot : Slot Member Member := ⟨fun member => [member], fun _ => true⟩

/-- The order the chooser names: Alice's candidate first. -/
def toyOrder : List Member := [.alice, .bob]

/-- At height 0 the slot fills by candidate 0; at height 1, Alice's stored selection reads blocked by
the name of her grant, and the slot fills by candidate 1: an object repairs without its author. -/
theorem toy_repair :
    slotFiller.fill toySlot 0 toyOrder = .ok .alice ∧
    toySlot.read (holdsAt 1) (some .alice) = .blocked .alice [.alice] ∧
    slotFiller.fill toySlot 1 toyOrder = .ok .bob :=
  ⟨rfl, rfl, rfl⟩

#tooth toy_repair by mutation toyOrder := []

theorem toy_alice_dead : holdsAt (V := Nat) 1 Member.alice = false := rfl

/-- FLOOR. The credulous filler admits Alice's candidate at height 1, where her grant is retired. -/
theorem not_integrity_credulousHoles : ¬ Integrity (credulousHoles : Filler Nat Member Member) := by
  intro h
  have := ((h.1 toySlot 1 toyOrder).1 .alice rfl).2.2.1 .alice (by simp [toySlot])
  rw [toy_alice_dead] at this
  cases this

#tooth not_integrity_credulousHoles by mutation Integrity := fun {_ _ _} [_] _ => True

/-- FLOOR. The first-candidate filler admits Alice's candidate at height 1 too. -/
theorem not_integrity_firstCandidate : ¬ Integrity (firstCandidate : Filler Nat Member Member) := by
  intro h
  have := ((h.1 toySlot 1 toyOrder).1 .alice rfl).2.2.1 .alice (by simp [toySlot])
  rw [toy_alice_dead] at this
  cases this

#tooth not_integrity_firstCandidate by mutation Integrity := fun {_ _ _} [_] _ => True

/-- FLOOR. The blind refusal refuses Alice alone at height 1 with no coordinate: nothing names her
dead grant. -/
theorem not_integrity_blindRefusal : ¬ Integrity (blindRefusal : Filler Nat Member Member) := by
  intro h
  obtain ⟨d, hd, -⟩ := (h.1 toySlot 1 [.alice]).2 [] rfl .alice (List.mem_singleton.2 rfl)
  cases hd

#tooth not_integrity_blindRefusal by mutation blindRefusal := slotFiller

/-- The slot's filler has integrity on the toy, where the non-trivial case happens. -/
theorem toy_integrity : Integrity (slotFiller : Filler Nat Member Member) := slotFiller_integrity

#assert_axioms slotFiller_uncovered slotFiller_typed resolve_eq_select select_ok select_error slotFiller_integrity toy_repair toy_alice_dead
  not_integrity_credulousHoles not_integrity_firstCandidate not_integrity_blindRefusal toy_integrity

end Obend.Slot
end
