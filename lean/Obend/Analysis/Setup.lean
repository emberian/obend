module
/-
# Obend.Analysis.Setup — a world under a partial setup: per-cell domains of admissible pins

`review/WORLD-ANALYSIS-20261101.md` §0 and §5, corrected by `review/GEMINI-CHECKPOINT-20261101b.md`
§3. The kernel is never partial: `World.pin v c` is total. Partiality is the analyst's condition,
the question asked before a view exists or by someone not shown all of it. A SETUP says, for every
cell, which pins it may hold:

* `range c`: a finite list of pins (`some ps`), or `none`: any pin;
* `known`: supports the analyst knows to hold or to fail. They constrain their own cell: the cell's
  DOMAIN is its range less every pin that disagrees with a known support of it (`domain`).

A view COMPLETES the setup (`ext`) when every cell's pin there is admissible. The degenerate setup
is the three-valued map `Cell → Option (Option Pin)` (`ofMap`): a known pin is a one-pin range, an
unknown one is unbounded; a view itself is the setup that knows every pin (`ofView`).

What a support is under a setup (`holds3`), exactly per cell:

* on a finitely ranged cell, `.known b` iff the domain is non-empty and every admissible pin gives
  `b` (`holds3_exact`), `.open` iff two admissible pins disagree (`holds3_open_iff`), and
  `.contradiction` iff the domain is empty: the constraints contradict each other or the range;
* on an unbounded cell the answer is `.known b` only when the support itself is known, a
  contradiction when it is known both ways, and otherwise `.uncovered`: entailment over an
  unbounded pin domain is not decided here (a Core4 law's verdict over every pin is the machine's
  halting on every input), so the reading says so instead of guessing.

`holds3_sound`: a `.known b` fact is `b` at every completion; `holds3_contradiction`: a
contradictory cell has no completion. The read of a slot under a setup (`read3`) is `usable`,
`blocked` (supports known dead, named), `excluded` (no single support is known dead, but every
admissible pin of one finitely ranged cell kills one of the candidate's supports on it: Kleene's
per-fact reading misses this, Gemini §3), `undecided`, or the refusal `contradiction`.
`read3_sound` (T1): the three-valued read COVERS the two-valued read at every completion.
`move`/`forget` re-range one cell, and change no reading of a fact about another
(`holds3_move_ne`); a one-pin move reads every support of the moved cell off that pin
(`holds3_move_one`).
-/
public import Obend.Slot.World
public import Obend.Tactic.Tooth
@[expose] public section

namespace Obend.Analysis

open Obend.Slot

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- What an analyst can say of a support under a setup. -/
inductive Three where
  /-- every admissible pin gives `b` -/
  | known (b : Bool)
  /-- two admissible pins of a finitely ranged cell disagree -/
  | open
  /-- the cell is unbounded and nothing known settles the support -/
  | uncovered
  /-- the cell admits no pin -/
  | contradiction
  deriving DecidableEq, Repr

def Three.isKnown : Three → Bool
  | .known _ => true
  | _ => false

/-- **A setup**: per cell, the pins it ranges over (`none`: any), and the supports the analyst
knows to hold (`true`) or to fail (`false`). -/
structure Setup (V : Type) {Fact : Type} [World V Fact] where
  range : World.Cell V → Option (List (Option (World.Pin V)))
  known : List (Fact × Bool)

namespace Setup

variable {V Fact : Type} [World V Fact] [DecidableEq (World.Cell V)] [DecidableEq Fact]

/-- Every known support of cell `c` reads at pin `p` as it is known. -/
def agrees (σ : Setup V) (c : World.Cell V) (p : Option (World.Pin V)) : Bool :=
  σ.known.all fun k => !(decide (World.cell (V := V) k.1 = c)) || World.holdsOfPin c p k.1 == k.2

/-- The admissible pins of a finitely ranged cell; `none` for an unbounded one. -/
def domain (σ : Setup V) (c : World.Cell V) : Option (List (Option (World.Pin V))) :=
  (σ.range c).map (·.filter (σ.agrees c))

/-- A pin is admissible for a cell: in its range, and agreeing with every known support of it. -/
def Admissible (σ : Setup V) (c : World.Cell V) (p : Option (World.Pin V)) : Prop :=
  (∀ ps, σ.range c = some ps → p ∈ ps) ∧ σ.agrees c p = true

/-- The views that complete the setup: every cell's pin is admissible. -/
def ext (σ : Setup V) (v : V) : Prop :=
  ∀ c, σ.Admissible c (World.pin (Fact := Fact) v c)

/-- **A support under a setup.** -/
def holds3 (σ : Setup V) (f : Fact) : Three :=
  match σ.domain (World.cell f) with
  | some ps =>
    if ps.isEmpty then .contradiction
    else if ps.all (fun p => World.holdsOfPin (World.cell f) p f) then .known true
    else if ps.all (fun p => !World.holdsOfPin (World.cell f) p f) then .known false
    else .open
  | none =>
    if (f, true) ∈ σ.known ∧ (f, false) ∈ σ.known then .contradiction
    else if (f, true) ∈ σ.known then .known true
    else if (f, false) ∈ σ.known then .known false
    else .uncovered

theorem agrees_spec {σ : Setup V} {c : World.Cell V} {p : Option (World.Pin V)} (h : σ.agrees c p = true)
    {f : Fact} {b : Bool} (hk : (f, b) ∈ σ.known) (hc : World.cell (V := V) f = c) :
    World.holdsOfPin c p f = b := by
  have := List.all_eq_true.1 h _ hk
  simp only [hc, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

theorem mem_domain {σ : Setup V} {c : World.Cell V} {ps : List (Option (World.Pin V))}
    (hd : σ.domain c = some ps) {p : Option (World.Pin V)} (ha : σ.Admissible c p) : p ∈ ps := by
  unfold domain at hd
  cases hr : σ.range c with
  | none => rw [hr] at hd; cases hd
  | some qs =>
    rw [hr] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    exact List.mem_filter.2 ⟨ha.1 qs hr, ha.2⟩

/-- The pin a completion holds for a cell is admissible. -/
theorem ext_admissible {σ : Setup V} {v : V} (hv : σ.ext v) (c : World.Cell V) :
    σ.Admissible c (World.pin (Fact := Fact) v c) := hv c

/-- **A contradictory cell has no completion.** -/
theorem holds3_contradiction (σ : Setup V) {f : Fact} (h : σ.holds3 f = .contradiction) :
    ¬ ∃ v, σ.ext v := by
  rintro ⟨v, hv⟩
  have ha := hv (World.cell f)
  unfold holds3 at h
  cases hd : σ.domain (World.cell f) with
  | some ps =>
    rw [hd] at h
    have hm := mem_domain hd ha
    simp only at h
    split at h
    · rename_i he
      rw [List.isEmpty_iff] at he; subst he; cases hm
    · split at h
      · cases h
      · split at h <;> cases h
  | none =>
    rw [hd] at h
    simp only at h
    split at h
    · rename_i hb
      have h1 := agrees_spec ha.2 hb.1 rfl
      have h2 := agrees_spec ha.2 hb.2 rfl
      rw [h1] at h2; cases h2
    · split at h
      · cases h
      · split at h <;> cases h

/-- **Exact per cell** (finite range): a support is known `b` iff the cell's domain is non-empty
and every admissible pin gives `b`. -/
theorem holds3_exact (σ : Setup V) {f : Fact} {ps : List (Option (World.Pin V))}
    (hd : σ.domain (World.cell f) = some ps) (b : Bool) :
    σ.holds3 f = .known b ↔ ps ≠ [] ∧ ∀ p ∈ ps, World.holdsOfPin (World.cell f) p f = b := by
  unfold holds3
  rw [hd]
  simp only
  by_cases he : ps = []
  · subst he; simp
  · have hne : ps.isEmpty = false := by simpa [List.isEmpty_iff] using he
    rw [if_neg (by simp [hne])]
    obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil ps he
    by_cases ht : ps.all (fun p => World.holdsOfPin (World.cell f) p f) = true
    · rw [if_pos ht]
      have hall := List.all_eq_true.1 ht
      cases b
      · simp only [Three.known.injEq, Bool.true_eq_false, false_iff]
        intro ⟨_, h'⟩; have := h' p₀ hp₀; rw [hall p₀ hp₀] at this; cases this
      · simp only [true_iff]; exact ⟨he, hall⟩
    · rw [if_neg ht]
      obtain ⟨q, hq, hqf⟩ : ∃ q ∈ ps, World.holdsOfPin (World.cell f) q f = false := by
        simpa [List.all_eq_true] using ht
      by_cases hf : ps.all (fun p => !World.holdsOfPin (World.cell f) p f) = true
      · rw [if_pos hf]
        have hall := List.all_eq_true.1 hf
        cases b
        · simp only [true_iff]; exact ⟨he, fun p hp => by simpa using hall p hp⟩
        · simp only [Three.known.injEq, Bool.false_eq_true, false_iff]
          intro ⟨_, h'⟩; have := h' q hq; rw [hqf] at this; cases this
      · rw [if_neg hf]
        obtain ⟨r, hr, hrt⟩ : ∃ r ∈ ps, World.holdsOfPin (World.cell f) r f = true := by
          simpa [List.all_eq_true] using hf
        simp only [reduceCtorEq, false_iff]
        intro ⟨_, h'⟩
        cases b
        · have := h' r hr; rw [hrt] at this; cases this
        · have := h' q hq; rw [hqf] at this; cases this

/-- **Open, exactly** (finite range): two admissible pins disagree. -/
theorem holds3_open_iff (σ : Setup V) {f : Fact} {ps : List (Option (World.Pin V))}
    (hd : σ.domain (World.cell f) = some ps) :
    σ.holds3 f = .open ↔ (∃ p ∈ ps, World.holdsOfPin (World.cell f) p f = true) ∧
      ∃ p ∈ ps, World.holdsOfPin (World.cell f) p f = false := by
  unfold holds3
  rw [hd]
  simp only
  by_cases he : ps = []
  · subst he; simp
  · have hne : ps.isEmpty = false := by simpa [List.isEmpty_iff] using he
    rw [if_neg (by simp [hne])]
    by_cases ht : ps.all (fun p => World.holdsOfPin (World.cell f) p f) = true
    · rw [if_pos ht]
      have hall := List.all_eq_true.1 ht
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ ⟨q, hq, hqf⟩; rw [hall q hq] at hqf; cases hqf
    · rw [if_neg ht]
      obtain ⟨q, hq, hqf⟩ : ∃ q ∈ ps, World.holdsOfPin (World.cell f) q f = false := by
        simpa [List.all_eq_true] using ht
      by_cases hf : ps.all (fun p => !World.holdsOfPin (World.cell f) p f) = true
      · rw [if_pos hf]
        have hall := List.all_eq_true.1 hf
        simp only [reduceCtorEq, false_iff, not_and]
        intro ⟨r, hr, hrt⟩; have := hall r hr; rw [hrt] at this; cases this
      · rw [if_neg hf]
        obtain ⟨r, hr, hrt⟩ : ∃ r ∈ ps, World.holdsOfPin (World.cell f) r f = true := by
          simpa [List.all_eq_true] using hf
        simp only [true_iff]
        exact ⟨⟨r, hr, hrt⟩, ⟨q, hq, hqf⟩⟩

/-- **A known support is known at every completion.** -/
theorem holds3_sound (σ : Setup V) {f : Fact} {b : Bool} (h : σ.holds3 f = .known b) {v : V}
    (hv : σ.ext v) : World.holdsAt v f = b := by
  rw [World.holds_pin]
  have ha := hv (World.cell f)
  cases hd : σ.domain (World.cell f) with
  | some ps =>
    have hm := mem_domain hd ha
    exact ((σ.holds3_exact hd b).1 h).2 _ hm
  | none =>
    unfold holds3 at h
    rw [hd] at h
    simp only at h
    by_cases h1 : (f, true) ∈ σ.known ∧ (f, false) ∈ σ.known
    · rw [if_pos h1] at h; cases h
    · rw [if_neg h1] at h
      by_cases h2 : (f, true) ∈ σ.known
      · rw [if_pos h2] at h; cases h; exact agrees_spec ha.2 h2 rfl
      · rw [if_neg h2] at h
        by_cases h3 : (f, false) ∈ σ.known
        · rw [if_pos h3] at h; cases h; exact agrees_spec ha.2 h3 rfl
        · rw [if_neg h3] at h; cases h

/-! ## The degenerate setups: the three-valued map, and a view -/

/-- **The three-valued map** as a setup: a known pin is a one-pin range, an unknown one is
unbounded, nothing else is known. -/
def ofMap (m : World.Cell V → Option (Option (World.Pin V))) : Setup V :=
  ⟨fun c => (m c).map ([·]), []⟩

theorem holds3_ofMap_some (m : World.Cell V → Option (Option (World.Pin V))) {f : Fact}
    {p : Option (World.Pin V)} (h : m (World.cell f) = some p) :
    (ofMap m).holds3 f = .known (World.holdsOfPin (World.cell f) p f) := by
  have hd : (ofMap m).domain (World.cell f) = some [p] := by
    simp [domain, ofMap, h, agrees]
  rw [holds3_exact _ hd]
  simp

theorem holds3_ofMap_none (m : World.Cell V → Option (Option (World.Pin V))) {f : Fact}
    (h : m (World.cell f) = none) : (ofMap m).holds3 f = .uncovered := by
  simp [holds3, domain, ofMap, h]

/-- The completions of the three-valued map are the views agreeing with every known pin. -/
theorem ext_ofMap (m : World.Cell V → Option (Option (World.Pin V))) (v : V) :
    (ofMap m).ext v ↔ ∀ c p, m c = some p → World.pin (Fact := Fact) v c = p := by
  constructor
  · intro hv c p hm
    have := (hv c).1 [p] (by simp [ofMap, hm])
    simpa using this
  · intro h c
    refine ⟨fun ps hr => ?_, by simp [agrees, ofMap]⟩
    cases hm : m c with
    | none => simp [ofMap, hm] at hr
    | some p =>
      simp only [ofMap, hm, Option.map_some, Option.some.injEq] at hr
      subst hr; simp [h c p hm]

/-- A view as the setup that knows every pin. -/
def ofView (v : V) : Setup V := ofMap fun c => some (World.pin (Fact := Fact) v c)

theorem holds3_ofView (v : V) (f : Fact) : (ofView v).holds3 f = .known (World.holdsAt v f) :=
  holds3_ofMap_some _ rfl

theorem ext_ofView (v : V) : (ofView v).ext v :=
  (ext_ofMap _ v).2 fun _ _ h => by cases h; rfl

/-! ## Moving one cell -/

/-- Re-range cell `c`, and drop what was known of its supports. -/
def move (σ : Setup V) (c : World.Cell V) (r : Option (List (Option (World.Pin V)))) : Setup V :=
  ⟨fun d => if d = c then r else σ.range d, σ.known.filter fun k => !decide (World.cell (V := V) k.1 = c)⟩

/-- Forget cell `c`: any pin. -/
def forget (σ : Setup V) (c : World.Cell V) : Setup V := σ.move c none

theorem agrees_move_ne (σ : Setup V) {c d : World.Cell V} (r : Option (List (Option (World.Pin V))))
    (hne : d ≠ c) (p : Option (World.Pin V)) : (σ.move c r).agrees d p = σ.agrees d p := by
  unfold agrees move
  simp only [List.all_filter]
  congr 1
  funext k
  by_cases hk : World.cell (V := V) k.1 = c
  · have : c ≠ d := fun e => hne e.symm
    simp [hk, this]
  · simp [hk]

theorem domain_move_ne (σ : Setup V) {c d : World.Cell V} (r : Option (List (Option (World.Pin V))))
    (hne : d ≠ c) : (σ.move c r).domain d = σ.domain d := by
  unfold domain
  have hr : (σ.move c r).range d = σ.range d := by simp [move, hne]
  rw [hr]
  congr 1
  funext ps
  exact List.filter_congr fun p _ => agrees_move_ne σ r hne p

theorem mem_known_move_ne (σ : Setup V) {c : World.Cell V} (r : Option (List (Option (World.Pin V))))
    {f : Fact} (hne : World.cell f ≠ c) (b : Bool) : (f, b) ∈ (σ.move c r).known ↔ (f, b) ∈ σ.known := by
  simp [move, List.mem_filter, hne]

/-- **A move changes no reading of a support of another cell.** -/
theorem holds3_move_ne (σ : Setup V) {c : World.Cell V} (r : Option (List (Option (World.Pin V))))
    {f : Fact} (hne : World.cell f ≠ c) : (σ.move c r).holds3 f = σ.holds3 f := by
  unfold holds3
  rw [domain_move_ne σ r hne]
  simp only [mem_known_move_ne σ r hne]

theorem agrees_move_self (σ : Setup V) (c : World.Cell V) (r : Option (List (Option (World.Pin V))))
    (p : Option (World.Pin V)) : (σ.move c r).agrees c p = true := by
  unfold agrees move
  simp only [List.all_filter, List.all_eq_true]
  intro k _
  by_cases hk : World.cell (V := V) k.1 = c <;> simp [hk]

/-- **A one-pin move reads every support of the moved cell off that pin.** -/
theorem holds3_move_one (σ : Setup V) {c : World.Cell V} (p : Option (World.Pin V)) {f : Fact}
    (hc : World.cell f = c) : (σ.move c (some [p])).holds3 f = .known (World.holdsOfPin c p f) := by
  have hd : (σ.move c (some [p])).domain (World.cell f) = some [p] := by
    have := agrees_move_self σ (World.cell f) (some [p]) p
    subst hc; simp only [domain, move, if_pos]; simp only [move] at this; simp [this]
  rw [holds3_exact _ hd]
  subst hc; simp

/-- A forgotten cell's supports are uncovered. -/
theorem holds3_forget (σ : Setup V) {c : World.Cell V} {f : Fact} (hc : World.cell f = c) :
    (σ.forget c).holds3 f = .uncovered := by
  have hd : (σ.forget c).domain (World.cell f) = none := by subst hc; simp [domain, forget, move]
  have hk : ∀ b, (f, b) ∉ (σ.forget c).known := by
    intro b hm; simp [forget, move, List.mem_filter, hc] at hm
  unfold holds3
  rw [hd]
  simp [hk]

end Setup

/-! ## A slot read under a setup -/

/-- What a three-valued read of a stored selection says. -/
inductive Reading3 (Fact Cand : Type) where
  | empty
  | rejected (c : Cand)
  /-- every support known to hold -/
  | usable (c : Cand) (evidence : List (Fact × Bool))
  /-- these supports are known dead -/
  | blocked (c : Cand) (dead : List Fact)
  /-- no support is known dead, yet every admissible pin of these supports' one cell kills one -/
  | excluded (c : Cand) (supports : List Fact)
  /-- no support known dead; these are not decided -/
  | undecided (c : Cand) (unknown : List Fact)
  /-- the setup admits no pin for this support's cell: the question contradicts itself -/
  | contradiction (c : Cand) (f : Fact)

namespace Setup

variable {V Fact Cand : Type} [World V Fact] [DecidableEq (World.Cell V)] [DecidableEq Fact]

/-- A support of `c` whose cell admits no pin. -/
def contra3 (σ : Setup V) (S : Slot Fact Cand) (c : Cand) : Option Fact :=
  (S.supports c).find? fun f => σ.holds3 f == .contradiction

/-- The supports of `c` known dead. -/
def dead3 (σ : Setup V) (S : Slot Fact Cand) (c : Cand) : List Fact :=
  (S.supports c).filter fun f => σ.holds3 f == .known false

/-- The supports of `c` not decided. -/
def unknown3 (σ : Setup V) (S : Slot Fact Cand) (c : Cand) : List Fact :=
  (S.supports c).filter fun f => !(σ.holds3 f).isKnown

/-- The supports of `c` on cell `d`. -/
def onCell (S : Slot Fact Cand) (c : Cand) (d : World.Cell V) : List Fact :=
  (S.supports c).filter fun f => decide (World.cell (V := V) f = d)

/-- Every admissible pin of the finitely ranged cell `d` kills a support of `c` on it. -/
def excludes (σ : Setup V) (S : Slot Fact Cand) (c : Cand) (d : World.Cell V) : Bool :=
  match σ.domain d with
  | some ps => ps.all fun p => (onCell (V := V) S c d).any fun f => !World.holdsOfPin d p f
  | none => false

/-- A cell of `c`'s supports that excludes it, as the supports of `c` on it. -/
def excl3 (σ : Setup V) (S : Slot Fact Cand) (c : Cand) : Option (List Fact) :=
  (((S.supports c).map (World.cell (V := V))).find? (σ.excludes S c)).map (onCell (V := V) S c)

/-- **Read a stored selection under a setup.** -/
def read3 (σ : Setup V) (S : Slot Fact Cand) : Option Cand → Reading3 Fact Cand
  | none => .empty
  | some c =>
    if S.judge c then
      match σ.contra3 S c with
      | some f => .contradiction c f
      | none =>
        match σ.dead3 S c with
        | [] =>
          match σ.excl3 S c with
          | some fs => .excluded c fs
          | none =>
            match σ.unknown3 S c with
            | [] => .usable c ((S.supports c).map fun f => (f, true))
            | u => .undecided c u
        | d => .blocked c d
    else .rejected c

/-- What a three-valued read says of the two-valued read at one completion. -/
def _root_.Obend.Analysis.Reading3.Covers {Fact Cand : Type} : Reading3 Fact Cand → Reading Fact Cand → Prop
  | .empty, r => r = .empty
  | .rejected c, r => r = .rejected c
  | .usable c ev, r => r = .usable c ev
  | .blocked c d, r => ∃ d', r = .blocked c d' ∧ ∀ f ∈ d, f ∈ d'
  | .excluded c fs, r => ∃ d', r = .blocked c d' ∧ ∃ f ∈ fs, f ∈ d'
  | .undecided c _, r => (∃ ev, r = .usable c ev) ∨ ∃ d', r = .blocked c d'
  | .contradiction _ _, _ => False

theorem contra3_none {σ : Setup V} {S : Slot Fact Cand} {c : Cand} (h : σ.contra3 S c = none) :
    ∀ f ∈ S.supports c, σ.holds3 f ≠ .contradiction := by
  intro f hf he
  have := List.find?_eq_none.1 h f hf
  simp [he] at this

theorem mem_dead3 {σ : Setup V} {S : Slot Fact Cand} {c : Cand} {f : Fact} :
    f ∈ σ.dead3 S c ↔ f ∈ S.supports c ∧ σ.holds3 f = .known false := by
  simp [dead3, List.mem_filter]

theorem mem_unknown3 {σ : Setup V} {S : Slot Fact Cand} {c : Cand} {f : Fact} :
    f ∈ σ.unknown3 S c ↔ f ∈ S.supports c ∧ (σ.holds3 f).isKnown = false := by
  simp [unknown3, List.mem_filter]

/-- A judged candidate with a dead support reads blocked, naming it. -/
theorem read_of_dead_mem (S : Slot Fact Cand) (holds : Fact → Bool) {c : Cand} (hj : S.judge c = true)
    {f : Fact} (hf : f ∈ S.supports c) (hd : holds f = false) :
    ∃ d, S.read holds (some c) = .blocked c d ∧ f ∈ d := by
  have hmem : f ∈ S.dead holds c := (mem_dead_iff S _ c f).2 ⟨hf, hd⟩
  unfold Slot.read
  simp only [hj, ite_true]
  cases hdd : S.dead holds c with
  | nil => rw [hdd] at hmem; cases hmem
  | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩

/-- A judged candidate reads usable or blocked. -/
theorem read_judged (S : Slot Fact Cand) (holds : Fact → Bool) {c : Cand} (hj : S.judge c = true) :
    (∃ ev, S.read holds (some c) = .usable c ev) ∨ ∃ d, S.read holds (some c) = .blocked c d := by
  unfold Slot.read
  simp only [hj, ite_true]
  cases S.dead holds c with
  | nil => exact .inl ⟨_, rfl⟩
  | cons g t => exact .inr ⟨_, rfl⟩

/-- **T1, the bracket.** At every completion of the setup, the two-valued read is the one the
three-valued read covers: `usable` with the same evidence, `blocked` naming at least the supports
known dead (or one of an excluding cell's), `undecided` either way; a contradiction has no
completion at all. -/
theorem read3_sound (σ : Setup V) (S : Slot Fact Cand) (x : Option Cand) {v : V} (hv : σ.ext v) :
    (σ.read3 S x).Covers (S.read (World.holdsAt v) x) := by
  cases x with
  | none => simp [read3, Reading3.Covers, Slot.read]
  | some c =>
    unfold read3
    by_cases hj : S.judge c = true
    · simp only [hj, ite_true]
      cases hc : σ.contra3 S c with
      | some f =>
        simp only [Reading3.Covers]
        have hf : σ.holds3 f = .contradiction := by
          have := List.find?_some hc; simpa using this
        exact σ.holds3_contradiction hf ⟨v, hv⟩
      | none =>
        simp only
        cases hd : σ.dead3 S c with
        | cons g t =>
          simp only [Reading3.Covers]
          have hg : g ∈ σ.dead3 S c := by rw [hd]; exact List.mem_cons_self
          obtain ⟨hgs, hgk⟩ := mem_dead3.1 hg
          obtain ⟨d', hr, -⟩ := read_of_dead_mem S _ hj hgs (σ.holds3_sound hgk hv)
          refine ⟨d', hr, fun f hf => ?_⟩
          rw [← hd] at hf
          obtain ⟨hfs, hfk⟩ := mem_dead3.1 hf
          exact ((read_blocked_exact S _ c c d' hr).2 f).2 ⟨hfs, σ.holds3_sound hfk hv⟩
        | nil =>
          simp only
          cases he : σ.excl3 S c with
          | some fs =>
            simp only [Reading3.Covers]
            unfold excl3 at he
            cases hfd : ((S.supports c).map (World.cell (V := V))).find? (σ.excludes S c) with
            | none => rw [hfd] at he; cases he
            | some d =>
              rw [hfd] at he
              simp only [Option.map_some, Option.some.injEq] at he
              subst he
              have hx : σ.excludes S c d = true := by simpa using List.find?_some hfd
              unfold excludes at hx
              cases hdom : σ.domain d with
              | none => rw [hdom] at hx; cases hx
              | some ps =>
                rw [hdom] at hx
                have hm := mem_domain hdom (hv d)
                have := List.all_eq_true.1 hx _ hm
                obtain ⟨f, hf, hff⟩ := List.any_eq_true.1 this
                obtain ⟨hfs, hfc⟩ := List.mem_filter.1 hf
                have hfc : World.cell (V := V) f = d := by simpa using hfc
                have hdead : World.holdsAt v f = false := by
                  rw [World.holds_pin, hfc]; simpa using hff
                obtain ⟨d', hr, hfd'⟩ := read_of_dead_mem S _ hj hfs hdead
                exact ⟨d', hr, f, hf, hfd'⟩
          | none =>
            simp only
            cases hu : σ.unknown3 S c with
            | cons g t =>
              simp only [Reading3.Covers]
              rcases read_judged S (World.holdsAt v) hj with h | h
              · exact .inl h
              · exact .inr h
            | nil =>
              simp only [Reading3.Covers]
              have hall : ∀ f ∈ S.supports c, World.holdsAt v f = true := by
                intro f hf
                have hk : (σ.holds3 f).isKnown = true := by
                  cases e : (σ.holds3 f).isKnown
                  · have : f ∈ σ.unknown3 S c := mem_unknown3.2 ⟨hf, e⟩
                    rw [hu] at this; cases this
                  · rfl
                have hnd : σ.holds3 f ≠ .known false := fun e => by
                  have : f ∈ σ.dead3 S c := mem_dead3.2 ⟨hf, e⟩
                  rw [hd] at this; cases this
                cases e : σ.holds3 f with
                | known b =>
                  cases b
                  · exact absurd e hnd
                  · exact σ.holds3_sound e hv
                | _ => rw [e] at hk; cases hk
              have hu' : S.usable (World.holdsAt v) c = true := (usable_iff S _ c).2 ⟨hj, hall⟩
              rw [read_of_usable S _ c hu']
              congr 1
              exact List.map_congr_left fun f hf => by rw [hall f hf]
    · simp only [hj, Bool.false_eq_true, ite_false, Reading3.Covers]
      unfold Slot.read
      simp [hj]

/-- A usable three-valued read is the usable read, with the same evidence, at every completion. -/
theorem read3_usable (σ : Setup V) (S : Slot Fact Cand) {c : Cand} {ev : List (Fact × Bool)}
    (h : σ.read3 S (some c) = .usable c ev) {v : V} (hv : σ.ext v) :
    S.read (World.holdsAt v) (some c) = .usable c ev := by
  have := σ.read3_sound S (some c) hv
  rw [h] at this; exact this

/-- A blocked three-valued read is blocked, naming at least those supports, at every completion. -/
theorem read3_blocked (σ : Setup V) (S : Slot Fact Cand) {c : Cand} {d : List Fact}
    (h : σ.read3 S (some c) = .blocked c d) {v : V} (hv : σ.ext v) :
    ∃ d', S.read (World.holdsAt v) (some c) = .blocked c d' ∧ ∀ f ∈ d, f ∈ d' := by
  have := σ.read3_sound S (some c) hv
  rw [h] at this; exact this

/-- **The contradiction refusal**: a read refused as a contradiction has no completion. -/
theorem read3_contradiction (σ : Setup V) (S : Slot Fact Cand) {c : Cand} {f : Fact}
    (h : σ.read3 S (some c) = .contradiction c f) : ¬ ∃ v, σ.ext v := by
  rintro ⟨v, hv⟩
  have := σ.read3_sound S (some c) hv
  rw [h] at this; exact this

end Setup

end Obend.Analysis

end
