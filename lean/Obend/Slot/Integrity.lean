module
/-
# Obend.Slot.Integrity — CONTEXTUAL INTEGRITY ∧ TRANSITION, over an abstract World

The top clause of the contextual layer (DESIGN-CTX §2.4, B4 and B4′), stated of a FILLER (the part
of a system that, at a view, fills a slot from the chooser's order or refuses) and of an ADVANCE (the
transition a runner applies to a STORED selection when the view changes). The slot's own pair
(`slotFiller`, `slotAdvance`) satisfies it over EVERY World (`slotFiller_integrity`).

B4, CONTEXTUAL INTEGRITY (`Integrity.contextual`): an admitted filling is a committed candidate (in
the order), typed at the interface (passes the judge), with every support it cites holding on the
view, and it is the one the chooser's order names (the first usable); a refusal names, for every
candidate of the order, the coordinate of a justification that did not hold: its dead supports, or
the judge when none is dead (why-not completeness).

REPAIR (`Integrity.repair`: a justification withdrawn stays withdrawn, and a slot with a usable
candidate is fillable now) is not a second guarantee: it is a corollary of contextual integrity for
every filler (`repair_of_contextual`; Kimi `review/KIMI-REVIEW-20261030.md` §1, Astra's proof).

B4′, TRANSITION (`Integrity.transition`), the operational property over a stored selection: a stored
selection that is usable at the new view is kept; an advanced selection is usable at the new view,
and is either the kept one or the first usable of the order; a refusal happens only when the stored
selection and every candidate of the order are unusable, and names each candidate's dead supports.
A stored selection citing a retired cell is never kept at a later view (`transition_retired`). The
policy is INCUMBENT-FIRST: it differs from re-running `select` (`churn` is refuted), because the
first-usable choice of a later view is a different choice whenever an earlier candidate came back
(`reuse_needs_prefix`). Exact reuse of a first-usable choice needs the rejected prefix as evidence
(`select_prefix`, `select_reuse`).

THE FLOOR, each refuted on the toy World (two members, one grant revoked at height 1):
`credulousHoles` (judges, ignores supports), `firstCandidate` (ignores both), `blindRefusal` (the
slot's selection, a refusal that names nothing) fail contextual integrity; `churn` (re-select at
every view) and `sticky` (keep the stored selection whatever the view) fail the transition. The toy
also inhabits the non-trivial case: filled by candidate 0 at height 0, the stored selection reads
blocked by the revoked grant's name at height 1, and the stored selection advances to candidate 1
there (`toy_repair`, `toy_advance`).
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

/-- REPAIR: a justification withdrawn stays withdrawn, and a usable candidate makes the slot
fillable now. A corollary of `Integrity.contextual` (`repair_of_contextual`). -/
def Integrity.repair (F : Filler V Fact Cand) : Prop :=
  ∀ (S : Slot Fact Cand) (order : List Cand),
    (∀ (v v' : V) (c : Cand) (f : Fact), f ∈ S.supports c → pin (Fact := Fact) v (cell f) = none →
      Later (Fact := Fact) v v' → F.fill S v' order ≠ .ok c) ∧
    (∀ (v : V) (c : Cand), c ∈ order → S.usable (holdsAt v) c = true → ∃ c', F.fill S v order = .ok c')

/-- How a runner moves a STORED selection (`none`: nothing stored) when the view changes. -/
structure Advance (V Fact Cand : Type) where
  advance : Slot Fact Cand → V → List Cand → Option Cand → Except (Refusal Fact Cand) Cand

/-- B4′. TRANSITION, over a stored selection. -/
def Integrity.transition (A : Advance V Fact Cand) : Prop :=
  ∀ (S : Slot Fact Cand) (v : V) (order : List Cand) (stored : Option Cand),
    (∀ c, stored = some c → S.usable (holdsAt v) c = true → A.advance S v order stored = .ok c) ∧
    (∀ c, A.advance S v order stored = .ok c → S.usable (holdsAt v) c = true ∧
      (stored = some c ∨ ∃ rest, S.alternatives (holdsAt v) order = c :: rest)) ∧
    (∀ w, A.advance S v order stored = .error w →
      (∀ c, stored = some c → S.usable (holdsAt v) c = false) ∧
      (∀ c ∈ order, S.usable (holdsAt v) c = false) ∧
      ∀ c ∈ order, ∃ d, (c, d) ∈ w ∧ (∀ f ∈ d, f ∈ S.supports c ∧ holdsAt v f = false) ∧
        (d = [] → S.judge c = false))

/-- CONTEXTUAL INTEGRITY ∧ TRANSITION. -/
def Integrity (F : Filler V Fact Cand) (A : Advance V Fact Cand) : Prop :=
  Integrity.contextual F ∧ Integrity.transition A

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

/-- A refusal of `select` names, for every candidate, its dead supports, or the judge. -/
theorem select_names {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand}
    {w : Refusal Fact Cand} (h : S.select holds order = .error w) :
    ∀ c ∈ order, ∃ d, (c, d) ∈ w ∧ (∀ f ∈ d, f ∈ S.supports c ∧ holds f = false) ∧
      (d = [] → S.judge c = false) := by
  obtain ⟨hnone, rfl⟩ := select_error h
  intro c hc
  refine ⟨S.dead holds c, List.mem_map.2 ⟨c, hc, rfl⟩, fun f hf => (mem_dead_iff S _ c f).1 hf, fun hd => ?_⟩
  have := hnone c hc
  unfold Slot.usable at this
  rw [hd] at this
  simpa using this

/-- REPAIR is a corollary of CONTEXTUAL INTEGRITY, for every filler. -/
theorem repair_of_contextual {F : Filler V Fact Cand} (h : Integrity.contextual F) :
    Integrity.repair F := by
  intro S order
  refine ⟨fun v v' c f hf hr hl hfill => ?_, fun v c hc hu => ?_⟩
  · have live := ((h S v' order).1 c hfill).2.2.1 f hf
    rw [dead_behind_forever f hr hl] at live
    cases live
  · cases answer : F.fill S v order with
    | ok c' => exact ⟨c', rfl⟩
    | error w =>
      obtain ⟨d, -, sound, rejected⟩ := (h S v order).2 w answer c hc
      have ⟨hj, hall⟩ := (usable_iff S _ c).1 hu
      have empty : d = [] := List.eq_nil_iff_forall_not_mem.2 fun f hf => by
        have := hall f (sound f hf).1
        rw [(sound f hf).2] at this
        cases this
      rw [rejected empty] at hj
      cases hj

/-- The slot's transition of a stored selection: keep it while it is usable, else select. -/
def Slot.advance (S : Slot Fact Cand) (holds : Fact → Bool) (order : List Cand) :
    Option Cand → Except (Refusal Fact Cand) Cand
  | some c => if S.usable holds c then .ok c else S.select holds order
  | none => S.select holds order

/-- The advance a slot gives. -/
def slotAdvance : Advance V Fact Cand := ⟨fun S v order stored => S.advance (holdsAt v) order stored⟩

/-- `select` fills whenever some candidate of the order is usable. -/
theorem select_some {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand} {c : Cand}
    (hc : c ∈ order) (hu : S.usable holds c = true) : ∃ c', S.select holds order = .ok c' := by
  have hmem : c ∈ S.alternatives holds order := List.mem_filter.2 ⟨hc, hu⟩
  unfold Slot.select
  cases ha : S.alternatives holds order with
  | nil => rw [ha] at hmem; cases hmem
  | cons c' rest => exact ⟨c', rfl⟩

/-- The slot's own pair has CONTEXTUAL INTEGRITY ∧ TRANSITION over every World. -/
theorem slotFiller_integrity :
    Integrity (slotFiller : Filler V Fact Cand) (slotAdvance : Advance V Fact Cand) := by
  refine ⟨fun S v order => ⟨fun c h => ?_, fun w h => select_names h⟩,
    fun S v order stored => ⟨fun c hs hu => ?_, fun c h => ?_, fun w h => ?_⟩⟩
  · obtain ⟨hmem, hu, rest, ha⟩ := select_ok h
    obtain ⟨hj, hholds⟩ := (usable_iff S _ c).1 hu
    exact ⟨hmem, hj, hholds, rest, ha⟩
  · subst hs; simp [slotAdvance, Slot.advance, hu]
  · have fresh : S.select (holdsAt v) order = .ok c → S.usable (holdsAt v) c = true ∧
        (stored = some c ∨ ∃ rest, S.alternatives (holdsAt v) order = c :: rest) := fun h =>
      have ⟨_, hu, ha⟩ := select_ok h; ⟨hu, .inr ha⟩
    cases stored with
    | none => exact fresh h
    | some c₀ =>
      by_cases hu : S.usable (holdsAt v) c₀ = true
      · simp only [slotAdvance, Slot.advance, hu, ite_true, Except.ok.injEq] at h
        subst h; exact ⟨hu, .inl rfl⟩
      · simp only [slotAdvance, Slot.advance, hu] at h; exact fresh h
  · have hsel : S.select (holdsAt v) order = .error w ∧ ∀ c, stored = some c → S.usable (holdsAt v) c = false := by
      cases stored with
      | none => exact ⟨h, fun _ h => by cases h⟩
      | some c₀ =>
        by_cases hu : S.usable (holdsAt v) c₀ = true
        · simp [slotAdvance, Slot.advance, hu] at h
        · simp only [slotAdvance, Slot.advance, hu] at h
          exact ⟨h, fun c hc => by cases hc; simpa using hu⟩
    exact ⟨hsel.2, (select_error hsel.1).1, select_names hsel.1⟩

#tooth slotFiller_integrity by mutation Slot.advance := fun _ _ _ _ => .error []

/-- The slot's filler has REPAIR, as the corollary it is. -/
theorem slotFiller_repair : Integrity.repair (slotFiller : Filler V Fact Cand) :=
  repair_of_contextual slotFiller_integrity.1

/-- Under TRANSITION, a stored selection citing a cell retired at `v` is never the advanced
selection at any later view. -/
theorem transition_retired {A : Advance V Fact Cand} (hA : Integrity.transition A)
    (S : Slot Fact Cand) (order : List Cand) (stored : Option Cand) {v v' : V} {c : Cand} {f : Fact}
    (hf : f ∈ S.supports c) (hr : pin (Fact := Fact) v (cell f) = none) (hl : Later (Fact := Fact) v v') :
    A.advance S v' order stored ≠ .ok c := by
  intro h
  have live := ((usable_iff S _ c).1 ((hA S v' order stored).2.1 c h).1).2 f hf
  rw [dead_behind_forever f hr hl] at live
  cases live

/-! ## Exact reuse of a first-usable choice -/

/-- A first-usable choice is certified by its own eligibility and the ineligibility of the
candidates before it. -/
theorem select_prefix {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand} {c : Cand}
    (h : S.select holds order = .ok c) :
    ∃ pre post, order = pre ++ c :: post ∧ S.usable holds c = true ∧ ∀ c' ∈ pre, S.usable holds c' = false := by
  induction order with
  | nil => simp [Slot.select, Slot.alternatives] at h
  | cons x xs ih =>
    by_cases hx : S.usable holds x = true
    · simp [Slot.select, Slot.alternatives, hx] at h
      subst h; exact ⟨[], xs, rfl, hx, by simp⟩
    · have h' : S.select holds xs = .ok c := by
        simp only [Slot.select, Slot.alternatives, List.filter_cons, hx] at h ⊢
        split at h <;> simp_all
      obtain ⟨pre, post, rfl, hc, hpre⟩ := ih h'
      exact ⟨x :: pre, post, rfl, hc, fun c' hc' => by
        rcases List.mem_cons.1 hc' with rfl | hc'
        · simpa using hx
        · exact hpre c' hc'⟩

/-- Replaying a first-usable choice at another view: the same choice when it is still usable and
the rejected prefix is still rejected. -/
theorem select_reuse {S : Slot Fact Cand} {holds : Fact → Bool} {pre post : List Cand} {c : Cand}
    (hc : S.usable holds c = true) (hpre : ∀ c' ∈ pre, S.usable holds c' = false) :
    S.select holds (pre ++ c :: post) = .ok c := by
  unfold Slot.select Slot.alternatives
  rw [List.filter_append, List.filter_eq_nil_iff.2 fun c' h => by simp [hpre c' h],
    List.filter_cons_of_pos hc]
  rfl

#tooth select_reuse by mutation Slot.alternatives := fun _ _ _ => []

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

/-- Re-selects at every view: forgets the stored selection. -/
def churn : Advance V Fact Cand := ⟨fun S v order _ => S.select (holdsAt v) order⟩

/-- Keeps the stored selection whatever the view. -/
def sticky : Advance V Fact Cand :=
  ⟨fun S v order stored => match stored with
    | some c => .ok c
    | none => S.select (holdsAt v) order⟩

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

/-- The same, as transitions of the stored selection: Alice's selection is kept at height 0, moves to
Bob at height 1, and Bob's is kept at height 0 although Alice comes first in the order. -/
theorem toy_advance :
    slotAdvance.advance toySlot 0 toyOrder (some .alice) = .ok .alice ∧
    slotAdvance.advance toySlot 1 toyOrder (some .alice) = .ok .bob ∧
    slotAdvance.advance toySlot 0 toyOrder (some .bob) = .ok .bob :=
  ⟨rfl, rfl, rfl⟩

#tooth toy_advance by mutation toyOrder := []

theorem toy_alice_dead : holdsAt (V := Nat) 1 Member.alice = false := rfl

/-- FLOOR. The credulous filler admits Alice's candidate at height 1, where her grant is retired. -/
theorem not_integrity_credulousHoles :
    ¬ Integrity.contextual (credulousHoles : Filler Nat Member Member) := by
  intro h
  have := ((h toySlot 1 toyOrder).1 .alice rfl).2.2.1 .alice (by simp [toySlot])
  rw [toy_alice_dead] at this
  cases this

#tooth not_integrity_credulousHoles by mutation Integrity.contextual := fun {_ _ _} [_] _ => True

/-- FLOOR. The first-candidate filler admits Alice's candidate at height 1 too. -/
theorem not_integrity_firstCandidate :
    ¬ Integrity.contextual (firstCandidate : Filler Nat Member Member) := by
  intro h
  have := ((h toySlot 1 toyOrder).1 .alice rfl).2.2.1 .alice (by simp [toySlot])
  rw [toy_alice_dead] at this
  cases this

#tooth not_integrity_firstCandidate by mutation Integrity.contextual := fun {_ _ _} [_] _ => True

/-- FLOOR. The blind refusal refuses Alice alone at height 1 with no coordinate: nothing names her
dead grant. -/
theorem not_integrity_blindRefusal :
    ¬ Integrity.contextual (blindRefusal : Filler Nat Member Member) := by
  intro h
  obtain ⟨d, hd, -⟩ := (h toySlot 1 [.alice]).2 [] rfl .alice (List.mem_singleton.2 rfl)
  cases hd

#tooth not_integrity_blindRefusal by mutation blindRefusal := slotFiller

/-- FLOOR. Re-selecting at every view drops Bob's stored selection at height 0, where it is usable,
for Alice, who comes first. -/
theorem not_transition_churn : ¬ Integrity.transition (churn : Advance Nat Member Member) := by
  intro h
  have := (h toySlot 0 toyOrder (some .bob)).1 .bob rfl rfl
  cases this

#tooth not_transition_churn by mutation churn := slotAdvance

/-- FLOOR. Keeping the stored selection keeps Alice's at height 1, where her grant is retired. -/
theorem not_transition_sticky : ¬ Integrity.transition (sticky : Advance Nat Member Member) := by
  intro h
  have := ((h toySlot 1 toyOrder (some .alice)).2.1 .alice rfl).1
  cases this

#tooth not_transition_sticky by mutation sticky := slotAdvance

/-- Astra's countermodel to replay without the prefix: candidate 0 cites `early`, candidate 1 cites
`chosen`. With only `chosen` live the slot selects 1; once `early` is live too it selects 0, though
1 is still usable and its supports are unchanged. -/
def reuseSlot : Slot Bool Bool := ⟨fun c => [c], fun _ => true⟩

theorem reuse_needs_prefix :
    reuseSlot.select (fun f => f) [false, true] = .ok true ∧
    reuseSlot.usable (fun _ => true) true = true ∧
    reuseSlot.select (fun _ => true) [false, true] = .ok false :=
  ⟨rfl, rfl, rfl⟩

/-- The slot's pair has integrity on the toy, where the non-trivial case happens. -/
theorem toy_integrity : Integrity (slotFiller : Filler Nat Member Member) slotAdvance :=
  slotFiller_integrity

#assert_axioms slotFiller_uncovered slotFiller_typed resolve_eq_select select_ok select_error select_names
  repair_of_contextual select_some slotFiller_integrity slotFiller_repair transition_retired select_prefix
  select_reuse toy_repair toy_advance toy_alice_dead not_integrity_credulousHoles
  not_integrity_firstCandidate not_integrity_blindRefusal not_transition_churn not_transition_sticky
  reuse_needs_prefix toy_integrity

end Obend.Slot
end
