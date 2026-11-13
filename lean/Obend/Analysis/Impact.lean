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
/-
# Obend.Analysis.Impact — if this pin moves, what goes blocked, stale, behind, or must be re-judged

`review/WORLD-ANALYSIS-20261101.md` §2.1 and §5 (T2). The journal (`Journal.Journal`) is this
analysis for the Lean tree; over a world the dependents are the existing structures, each read off
the facts it reads:

| dependent | reads | goes |
|---|---|---|
| a slot's stored candidate | `S.supports c` | `blocked` (`read_blocked_exact`) |
| a package turn | its pins' record lines | `stale` (`Ecosystem.admit`, `stale_iff_blocked`) |
| a cite in a page | the cite's facts | `behind` (`cite_stale_iff_blocked`) |
| an issued receipt | its pins, as facts "this cell holds this pin" | no longer current |
| a row of an audited fold (a law's verdict) | `Admission.reads` at its accumulator | re-judge |

A `Dep` carries its kind, name, judge and READS; the reads index of a fold is `foldIndex`, every
row to the facts `Admission.reads` says it read, along the fold.

**T2 over setups.** `affected_reads`: a candidate whose three-valued read changes when one cell is
re-ranged reads that cell (the index is complete). `reads_affected`: a candidate that reads the
forgotten cell and has no other support short of known-true reads `undecided`, naming it (exact up
to known blocks). For a fold, `impact_row` and `impact_prefix`: rows that do not read the moved cell
keep their verdicts, and so does the fold before the first row that does (`step_of_reads`).

**A concrete move** (`Question`: a base view, the dependents, a cell and its new pin). The moved
view's reads are `movedHolds`: the new pin's for the moved cell's supports, the base's otherwise
(`moved_holds`, at every view with those pins; `holds3_moved`: the one-pin move of the base view as
a setup reads the same). `affected` lists, for each dependent that changes, one line carrying the
OPENING it rests on: the support naming the cell, and its value at the new pin. `Meaning`: every
line holds, read off `holdsOfPin` (`LineHolds`), and every dependent that changes has a line.
`affected_exact`: the producer's list means that. `line_blocked`: a `blocked` line's dependent reads
blocked at every view holding the new pin, naming that support, by `read_blocked_exact`'s read;
`line_restored`: a `restored` one reads usable at every moved view; `unlisted_unchanged`: no other
dependent's usability moves (exact up to known blocks). The analysis is the judge `impactJudge`,
registered as a format in `Obend.Analysis.Format`.

Tooth: `affected_exact` by mutation of the index (`indexReads` drops a dependent's last read): the
prediction then misses a blocked candidate.
-/
/-
# Obend.Analysis.Format — the impact analysis as a registered format, on an exported table

A registered format judges bytes, so its objects are a concrete type. The impact question of any
world is exported as a TABLE (`TView`, `TFact`): cells and pins are names, and each support lists
the pins, among those the question names, at which it holds. The table is itself a `World`
(`tableWorld`: a support holds at a pin iff it lists it; a retired cell holds nothing; views do not
step), so every theorem of `Obend.Analysis.Impact` is a theorem about the exported question:
`line_blocked` at a table view holding the new pin is the dependent's blocked read naming the
support, `read_blocked_exact`'s. An exporter (`Obend.Analysis.Worlds`) computes each listed pin by
the native world's own read, at the base and at the moved pin.

`impact@1` (`format`): object the question, certificate the affected list with its openings;
decidable, compiled trust. The planted bad certificate names a dependent that does not read the
moved cell (`bad_refused`). The tooth `drop_read_misses`: an index that drops a dependent's last
read lists nothing for a cite whose bytes moved, and the checker refuses that list as `missing`.
-/
public import Obend.Slot.World
public import Obend.Fold
public import Obend.Intention
public import Obend.Judge.Class
public import Obend.Tactic.Tooth
public import Lean.Data.Json
public section


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


namespace Obend.Analysis

open Obend.Slot Obend.Fold

set_option autoImplicit false
set_option linter.unusedSectionVars false

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?_cons, h x List.mem_cons_self]
    cases q x
    · exact find?_congr fun y hy => h y (List.mem_cons_of_mem _ hy)
    · rfl

/-! ## T2 over setups -/

section
variable {V Fact Cand : Type} [World V Fact] [DecidableEq (World.Cell V)] [DecidableEq Fact]

/-- A read under a setup depends only on its supports' readings and their cells' domains. -/
theorem read3_congr (σ τ : Setup V) (S : Slot Fact Cand) (x : Cand)
    (hh : ∀ f ∈ S.supports x, σ.holds3 f = τ.holds3 f)
    (hd : ∀ f ∈ S.supports x, σ.domain (World.cell f) = τ.domain (World.cell f)) :
    σ.read3 S (some x) = τ.read3 S (some x) := by
  have hc : σ.contra3 S x = τ.contra3 S x := find?_congr fun f hf => by rw [hh f hf]
  have hdd : σ.dead3 S x = τ.dead3 S x := List.filter_congr fun f hf => by rw [hh f hf]
  have hu : σ.unknown3 S x = τ.unknown3 S x := List.filter_congr fun f hf => by rw [hh f hf]
  have he : σ.excl3 S x = τ.excl3 S x := by
    unfold Setup.excl3
    congr 1
    apply find?_congr
    intro d hdm
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hdm
    unfold Setup.excludes
    rw [hd f hf]
  simp only [Setup.read3, hc, hdd, hu, he]

/-- **T2, the index is complete**: a candidate whose read changes when cell `c` is re-ranged has a
support naming `c`. -/
theorem affected_reads (σ : Setup V) (S : Slot Fact Cand) (c : World.Cell V)
    (r : Option (List (Option (World.Pin V)))) (x : Cand)
    (h : (σ.move c r).read3 S (some x) ≠ σ.read3 S (some x)) : ∃ f ∈ S.supports x, World.cell f = c :=
  Classical.byContradiction fun hn => h (read3_congr _ _ S x
    (fun f hf => σ.holds3_move_ne r fun e => hn ⟨f, hf, e⟩)
    (fun f hf => σ.domain_move_ne r fun e => hn ⟨f, hf, e⟩))

/-- **T2, exact up to known blocks**: a judged candidate that reads cell `c`, and whose other
supports are known to hold, reads `undecided` once `c` is forgotten, naming every support of `c`. -/
theorem reads_affected (σ : Setup V) (S : Slot Fact Cand) (c : World.Cell V) (x : Cand)
    (hj : S.judge x = true) {f : Fact} (hf : f ∈ S.supports x) (hfc : World.cell f = c)
    (hd : ∀ g ∈ S.supports x, World.cell g ≠ c → σ.holds3 g = .known true) :
    ∃ u, (σ.forget c).read3 S (some x) = .undecided x u ∧ f ∈ u := by
  have h3 : ∀ g ∈ S.supports x, (σ.forget c).holds3 g = .uncovered ∨ (σ.forget c).holds3 g = .known true := by
    intro g hg
    by_cases e : World.cell g = c
    · exact .inl (σ.holds3_forget e)
    · exact .inr ((σ.holds3_move_ne none e).trans (hd g hg e))
  have hc : (σ.forget c).contra3 S x = none := by
    apply List.find?_eq_none.2
    intro g hg
    rcases h3 g hg with e | e <;> simp [e]
  have hdd : (σ.forget c).dead3 S x = [] := by
    apply List.filter_eq_nil_iff.2
    intro g hg
    rcases h3 g hg with e | e <;> simp [e]
  have he : (σ.forget c).excl3 S x = none := by
    unfold Setup.excl3
    simp only [Option.map_eq_none_iff]
    apply List.find?_eq_none.2
    intro d hdm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hdm
    unfold Setup.excludes
    cases hdom : (σ.forget c).domain (World.cell g) with
    | none => simp
    | some ps =>
      have hgc : World.cell g ≠ c := by
        intro e
        have : (σ.forget c).domain (World.cell g) = none := by
          simp [Setup.forget, Setup.move, Setup.domain, e]
        rw [this] at hdom; cases hdom
      have hk : (σ.forget c).holds3 g = .known true := (σ.holds3_move_ne none hgc).trans (hd g hg hgc)
      obtain ⟨hne, hall⟩ := ((σ.forget c).holds3_exact hdom true).1 hk
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil ps hne
      simp only [Bool.not_eq_true, List.all_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true]
      refine ⟨p, hp, ?_⟩
      simp only [List.any_eq_false, Bool.not_eq_true']
      intro g' hg'
      obtain ⟨hg's, hg'c⟩ := List.mem_filter.1 hg'
      have hg'c : World.cell (V := V) g' = World.cell g := by simpa using hg'c
      have hg'c' : World.cell g' ≠ c := fun e' => hgc (hg'c ▸ e')
      have hk' : (σ.forget c).holds3 g' = .known true :=
        (σ.holds3_move_ne none hg'c').trans (hd g' hg's hg'c')
      have hdom' : (σ.forget c).domain (World.cell g') = some ps := by rw [hg'c]; exact hdom
      have := (((σ.forget c).holds3_exact hdom' true).1 hk').2 p hp
      rw [hg'c] at this
      simp [this]
  obtain ⟨u, hu⟩ : ∃ u, (σ.forget c).unknown3 S x = u := ⟨_, rfl⟩
  have hfu : f ∈ (σ.forget c).unknown3 S x :=
    Setup.mem_unknown3.2 ⟨hf, by rw [σ.holds3_forget hfc]; rfl⟩
  refine ⟨(σ.forget c).unknown3 S x, ?_, hfu⟩
  simp only [Setup.read3, hj, ite_true, hc, hdd, he]
  cases hu' : (σ.forget c).unknown3 S x with
  | nil => rw [hu'] at hfu; cases hfu
  | cons _ _ => rfl

end

/-! ## The reads index of an audited fold -/

section
variable {V Fact : Type} [World V Fact] {Rest Row Clause : Type}

/-- **The reads index of a fold**: every row the fold reaches, with the facts it read
(`Admission.reads`) at its accumulator; the fold stops at a refusal. -/
def foldIndex (A : Admission V Rest Row Fact Clause) : V × Rest → List Row → List (Row × List Fact)
  | _, [] => []
  | a, r :: rs => (r, A.reads a r) :: match A.step a r with
    | .ok b => foldIndex A b rs
    | .error _ => []

/-- **A row that does not read the moved cell keeps its verdict** (`step_of_reads`). -/
theorem impact_row (A : Admission V Rest Row Fact Clause) (hlook : A.look = World.holdsAt)
    (a : V × Rest) (r : Row) (hm : A.moves r = false) (c : World.Cell V) (v' : V)
    (hpin : ∀ d, d ≠ c → World.pin (Fact := Fact) v' d = World.pin (Fact := Fact) a.1 d)
    (hr : ∀ f ∈ A.reads a r, World.cell f ≠ c) :
    A.step (v', a.2) r = (A.step a r).map fun b => (v', b.2) :=
  A.step_of_reads a v' r hm fun f hf => by
    rw [hlook]; exact World.holds_congr _ _ f (hpin _ (hr f hf)).symm

/-- **The fold before the first row reading the moved cell is unaffected**: when no indexed row
reads cell `c` and none moves the world, the fold at a view differing from the accumulator's only
at `c` judges every row as it was. -/
theorem impact_prefix (A : Admission V Rest Row Fact Clause) (hlook : A.look = World.holdsAt)
    (c : World.Cell V) (v' : V) :
    ∀ (rows : List Row) (a : V × Rest), (∀ r ∈ rows, A.moves r = false) →
      (∀ e ∈ foldIndex A a rows, ∀ f ∈ e.2, World.cell f ≠ c) →
      (∀ d, d ≠ c → World.pin (Fact := Fact) v' d = World.pin (Fact := Fact) a.1 d) →
      A.run (v', a.2) rows = (A.run a rows).map fun b => (v', b.2)
  | [], _, _, _, _ => rfl
  | r :: rs, a, hm, hi, hpin => by
    have hr : ∀ f ∈ A.reads a r, World.cell f ≠ c := hi (r, A.reads a r) List.mem_cons_self
    have hs := impact_row A hlook a r (hm r List.mem_cons_self) c v' hpin hr
    simp only [Admission.run, List.foldlM_cons] at *
    rw [hs]
    cases hst : A.step a r with
    | error e => rfl
    | ok b =>
      have hw : b.1 = a.1 := A.keeps_world a r b (hm r List.mem_cons_self) hst
      simp only [Except.map, bind, Except.bind]
      have hi' : ∀ e ∈ foldIndex A b rs, ∀ f ∈ e.2, World.cell f ≠ c := by
        intro e he; apply hi e; simp only [foldIndex, hst]; exact List.mem_cons_of_mem _ he
      have ih := impact_prefix A hlook c v' rs b (fun r' h' => hm r' (List.mem_cons_of_mem _ h')) hi'
        (fun d hd => (hpin d hd).trans (by rw [hw]))
      exact ih

end

/-! ## Dependents, questions, and the affected list -/

/-- What kind of dependent: its verdict's word when a read dies. -/
inductive Kind where
  | candidate | turn | cite | receipt | law
  deriving DecidableEq, Repr

/-- A row of a fold (a law's verdict on a write): re-judged, not read as a slot. -/
def Kind.isRow : Kind → Bool
  | .law => true
  | _ => false

/-- The word for a dependent of this kind whose read goes blocked. -/
def Kind.word : Kind → String
  | .candidate => "blocked"
  | .turn => "stale"
  | .cite => "behind"
  | .receipt => "not-current"
  | .law => "rejudge"

def Kind.name : Kind → String
  | .candidate => "candidate"
  | .turn => "turn"
  | .cite => "cite"
  | .receipt => "receipt"
  | .law => "law"

/-- **A dependent**: something whose verdict is read off the facts it reads. -/
structure Dep (Fact : Type) where
  kind : Kind
  name : String
  judge : Bool
  reads : List Fact
  deriving DecidableEq, Repr

/-- The slot every dependent is a candidate of: its supports are its reads. -/
def depSlot {Fact : Type} : Slot Fact (Dep Fact) := ⟨Dep.reads, Dep.judge⟩

/-- The dependents a fold's index makes: one law row per indexed row. -/
def lawRows {Row Fact : Type} (name : Row → String) (ix : List (Row × List Fact)) : List (Dep Fact) :=
  ix.map fun e => ⟨.law, name e.1, true, e.2⟩

/-- The dependent of an intention's pin (a cite, a package pin): its supports are the pin's. -/
def pinDep {W Ref Pin Fact Err : Type} (I : Obend.Intention W Ref Pin Fact Err) (kind : Kind) (name : String)
    (p : Pin) : Dep Fact := ⟨kind, name, true, I.supports p⟩

/-- How a dependent goes. -/
inductive Goes where
  /-- usable at the base, blocked once moved: blocked, stale, behind, not current -/
  | blocked
  /-- blocked at the base, usable once moved -/
  | restored
  /-- a row reading the cell whose pin moved: its verdict must be re-judged -/
  | rejudge
  deriving DecidableEq, Repr

/-- **A line of the affected list**: the dependent, how it goes, and the OPENING it rests on: the
support naming the moved cell, with its value at the new pin. -/
structure Line (Fact : Type) where
  dep : String
  goes : Goes
  support : Fact
  value : Bool
  deriving DecidableEq, Repr

section
variable {V Fact : Type} [World V Fact] [DecidableEq (World.Cell V)] [DecidableEq Fact]
  [DecidableEq (World.Pin V)]

/-- **An impact question**: a base view, its dependents, and a cell moved to a new pin. -/
structure Question (V : Type) {Fact : Type} [World V Fact] where
  base : V
  deps : List (Dep Fact)
  cell : World.Cell V
  pin : Option (World.Pin V)

/-- The reads of the moved view: the new pin's for the moved cell's supports, the base's otherwise. -/
def movedHolds (q : Question V) (f : Fact) : Bool :=
  if World.cell f = q.cell then World.holdsOfPin q.cell q.pin f else World.holdsAt q.base f

/-- A view the move describes: the new pin at the cell, the base's pin everywhere else. -/
def Moved (q : Question V) (v : V) : Prop :=
  World.pin (Fact := Fact) v q.cell = q.pin ∧ ∀ d, d ≠ q.cell → World.pin (Fact := Fact) v d = World.pin (Fact := Fact) q.base d

/-- At every moved view, the reads are `movedHolds`. -/
theorem moved_holds (q : Question V) {v : V} (hv : Moved q v) (f : Fact) :
    World.holdsAt v f = movedHolds q f := by
  unfold movedHolds
  rw [World.holds_pin]
  by_cases e : World.cell f = q.cell
  · rw [if_pos e, e, hv.1]
  · rw [if_neg e, hv.2 _ e]; rfl

/-- The move as a setup: the base view with one cell moved to one pin. -/
def Question.setup (q : Question V) : Setup V := (Setup.ofView q.base).move q.cell (some [q.pin])

/-- The setup reads every support as `movedHolds`. -/
theorem holds3_moved (q : Question V) (f : Fact) : q.setup.holds3 f = .known (movedHolds q f) := by
  unfold Question.setup movedHolds
  by_cases e : World.cell f = q.cell
  · rw [Setup.holds3_move_one _ _ e, if_pos e]
  · rw [Setup.holds3_move_ne _ _ e, if_neg e, Setup.holds3_ofView]

/-- The moved views complete the move's setup. -/
theorem ext_moved (q : Question V) {v : V} (hv : Moved q v) : q.setup.ext v := by
  intro d
  refine ⟨fun ps hr => ?_, ?_⟩
  · by_cases e : d = q.cell
    · subst e; simp [Question.setup, Setup.move] at hr; subst hr; simp [hv.1]
    · simp [Question.setup, Setup.move, e, Setup.ofView, Setup.ofMap] at hr
      subst hr; simp [hv.2 d e]
  · unfold Question.setup Setup.agrees Setup.move
    simp [Setup.ofView, Setup.ofMap]

/-- Whether the dependent is usable at the base. -/
def before (q : Question V) (d : Dep Fact) : Bool := depSlot.usable (World.holdsAt q.base) d

/-- Whether the dependent is usable once moved. -/
def after (q : Question V) (d : Dep Fact) : Bool := depSlot.usable (movedHolds q) d

/-- **What one line claims**, read off `holdsOfPin` and the base view. -/
def LineHolds (q : Question V) (l : Line Fact) : Prop :=
  ∃ d ∈ q.deps, d.name = l.dep ∧ l.support ∈ d.reads ∧ World.cell l.support = q.cell ∧
    match l.goes with
    | .blocked => d.kind.isRow = false ∧ d.judge = true ∧ before q d = true ∧
        World.holdsOfPin q.cell q.pin l.support = false ∧ l.value = false
    | .restored => d.kind.isRow = false ∧ d.judge = true ∧ before q d = false ∧ after q d = true ∧
        World.holdsAt q.base l.support = false ∧ World.holdsOfPin q.cell q.pin l.support = true ∧ l.value = true
    | .rejudge => d.kind.isRow = true ∧ World.pin (Fact := Fact) q.base q.cell ≠ q.pin ∧
        l.value = World.holdsOfPin q.cell q.pin l.support

/-- **A dependent changes**: a row reading the cell whose pin moved, or a judged candidate whose
usability differs at the moved view. -/
def Changes (q : Question V) (d : Dep Fact) : Prop :=
  (d.kind.isRow = true ∧ (∃ f ∈ d.reads, World.cell f = q.cell) ∧ World.pin (Fact := Fact) q.base q.cell ≠ q.pin) ∨
    (d.kind.isRow = false ∧ d.judge = true ∧ before q d ≠ after q d)

/-- **The meaning of an affected list**: every line holds, and every dependent that changes has a
line. -/
def Meaning (q : Question V) (ls : List (Line Fact)) : Prop :=
  (∀ l ∈ ls, LineHolds q l) ∧ ∀ d ∈ q.deps, Changes q d → ∃ l ∈ ls, l.dep = d.name

@[no_expose] instance (q : Question V) (l : Line Fact) : Decidable (LineHolds q l) := by
  unfold LineHolds; cases l.goes <;> exact inferInstance

@[no_expose] instance (q : Question V) (d : Dep Fact) : Decidable (Changes q d) := by
  unfold Changes; exact inferInstance

/-- The index the producer consults: a dependent's reads. -/
def indexReads (d : Dep Fact) : List Fact := d.reads

/-- **The producer**, over an index `rd`. -/
def affectedWith (rd : Dep Fact → List Fact) (q : Question V) : List (Line Fact) :=
  q.deps.filterMap fun d =>
    if d.kind.isRow then
      if World.pin (Fact := Fact) q.base q.cell ≠ q.pin then
        ((rd d).find? fun f => decide (World.cell f = q.cell)).map fun f =>
          ⟨d.name, .rejudge, f, World.holdsOfPin q.cell q.pin f⟩
      else none
    else if d.judge then
      if before q d && !after q d then
        ((rd d).find? fun f => decide (World.cell f = q.cell) && !World.holdsOfPin q.cell q.pin f).map fun f =>
          ⟨d.name, .blocked, f, false⟩
      else if !before q d && after q d then
        ((rd d).find? fun f => decide (World.cell f = q.cell) && !World.holdsAt q.base f).map fun f =>
          ⟨d.name, .restored, f, true⟩
      else none
    else none

/-- **The affected list.** -/
def affected (q : Question V) : List (Line Fact) := affectedWith indexReads q

theorem usable_dep (h : Fact → Bool) (d : Dep Fact) :
    depSlot.usable h d = true ↔ d.judge = true ∧ ∀ f ∈ d.reads, h f = true :=
  usable_iff depSlot h d

/-- A dependent usable at the base and not once moved has a read of the moved cell dead at the new
pin; and conversely for one restored. -/
theorem moved_dead (q : Question V) {d : Dep Fact} (hb : before q d = true) (ha : after q d = false) :
    ∃ f ∈ d.reads, World.cell f = q.cell ∧ World.holdsOfPin q.cell q.pin f = false := by
  have hb' := (usable_dep _ d).1 hb
  have : ¬ ∀ f ∈ d.reads, movedHolds q f = true := fun h =>
    absurd ((usable_dep _ d).2 ⟨hb'.1, h⟩) (by simp [after] at ha; simp [ha])
  obtain ⟨f, hf, hff⟩ : ∃ f ∈ d.reads, movedHolds q f = false := by
    exact Classical.byContradiction fun hn => this fun f hf => by
      cases e : movedHolds q f
      · exact absurd ⟨f, hf, e⟩ hn
      · rfl
  have hbf := hb'.2 f hf
  unfold movedHolds at hff
  by_cases e : World.cell f = q.cell
  · rw [if_pos e] at hff; exact ⟨f, hf, e, hff⟩
  · rw [if_neg e, hbf] at hff; cases hff

theorem moved_live (q : Question V) {d : Dep Fact} (hj : d.judge = true) (hb : before q d = false)
    (ha : after q d = true) :
    ∃ f ∈ d.reads, World.cell f = q.cell ∧ World.holdsAt q.base f = false ∧
      World.holdsOfPin q.cell q.pin f = true := by
  have ha' := (usable_dep _ d).1 ha
  have : ¬ ∀ f ∈ d.reads, World.holdsAt q.base f = true := fun h =>
    absurd ((usable_dep _ d).2 ⟨hj, h⟩) (by simp [before] at hb; simp [hb])
  obtain ⟨f, hf, hff⟩ : ∃ f ∈ d.reads, World.holdsAt q.base f = false := by
    exact Classical.byContradiction fun hn => this fun f hf => by
      cases e : World.holdsAt q.base f
      · exact absurd ⟨f, hf, e⟩ hn
      · rfl
  have haf := ha'.2 f hf
  unfold movedHolds at haf
  by_cases e : World.cell f = q.cell
  · rw [if_pos e] at haf; exact ⟨f, hf, e, hff, haf⟩
  · rw [if_neg e, hff] at haf; cases haf

/-- **The producer's list means what it says**: every line holds and every dependent that changes
is listed. The impact analysis is exact up to known blocks. -/
theorem affected_exact (q : Question V) : Meaning q (affected q) := by
  constructor
  · intro l hl
    obtain ⟨d, hd, hdl⟩ := List.mem_filterMap.1 hl
    refine ⟨d, hd, ?_⟩
    simp only [affectedWith, indexReads] at hdl
    by_cases hr : d.kind.isRow = true
    · rw [if_pos hr] at hdl
      by_cases hp : World.pin (Fact := Fact) q.base q.cell ≠ q.pin
      · rw [if_pos hp] at hdl
        obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hdl
        have hfm := List.mem_of_find?_eq_some hf
        have hfc : World.cell f = q.cell := by simpa using List.find?_some hf
        exact ⟨rfl, hfm, hfc, hr, hp, rfl⟩
      · rw [if_neg hp] at hdl; cases hdl
    · rw [if_neg hr] at hdl
      have hr' : d.kind.isRow = false := by simpa using hr
      by_cases hj : d.judge = true
      · rw [if_pos hj] at hdl
        by_cases hba : (before q d && !after q d) = true
        · rw [if_pos hba] at hdl
          obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hdl
          have hfm := List.mem_of_find?_eq_some hf
          have hfp := List.find?_some hf
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hfp
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hba
          exact ⟨rfl, hfm, hfp.1, hr', hj, hba.1, hfp.2, rfl⟩
        · rw [if_neg hba] at hdl
          by_cases hab : (!before q d && after q d) = true
          · rw [if_pos hab] at hdl
            obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hdl
            have hfm := List.mem_of_find?_eq_some hf
            have hfp := List.find?_some hf
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hfp
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hab
            have hmv : movedHolds q f = true := by
              have := ((usable_dep _ d).1 hab.2).2 f hfm; exact this
            unfold movedHolds at hmv; rw [if_pos hfp.1] at hmv
            exact ⟨rfl, hfm, hfp.1, hr', hj, hab.1, hab.2, hfp.2, hmv, rfl⟩
          · rw [if_neg hab] at hdl; cases hdl
      · rw [if_neg hj] at hdl; cases hdl
  · intro d hd hc
    have mk : ∀ l, (if d.kind.isRow then
        (if World.pin (Fact := Fact) q.base q.cell ≠ q.pin then
          ((indexReads d).find? fun f => decide (World.cell f = q.cell)).map fun f =>
            (⟨d.name, .rejudge, f, World.holdsOfPin q.cell q.pin f⟩ : Line Fact)
        else none)
      else if d.judge then
        (if before q d && !after q d then
          ((indexReads d).find? fun f => decide (World.cell f = q.cell) && !World.holdsOfPin q.cell q.pin f).map fun f =>
            (⟨d.name, .blocked, f, false⟩ : Line Fact)
        else if !before q d && after q d then
          ((indexReads d).find? fun f => decide (World.cell f = q.cell) && !World.holdsAt q.base f).map fun f =>
            ⟨d.name, .restored, f, true⟩
        else none)
      else none) = some l → ∃ l ∈ affected q, l.dep = d.name := by
      intro l hl
      refine ⟨l, List.mem_filterMap.2 ⟨d, hd, hl⟩, ?_⟩
      revert hl
      split
      · split
        · intro h; obtain ⟨f, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl
        · intro h; cases h
      · split
        · split
          · intro h; obtain ⟨f, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl
          · split
            · intro h; obtain ⟨f, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl
            · intro h; cases h
        · intro h; cases h
    rcases hc with ⟨hr, ⟨f, hf, hfc⟩, hp⟩ | ⟨hr, hj, hba⟩
    · obtain ⟨g, hg⟩ : ∃ g, (indexReads d).find? (fun f => decide (World.cell f = q.cell)) = some g := by
        cases e : (indexReads d).find? (fun f => decide (World.cell f = q.cell)) with
        | some g => exact ⟨g, rfl⟩
        | none => have := List.find?_eq_none.1 e f hf; simp [hfc] at this
      exact mk _ (by rw [if_pos hr, if_pos hp, hg]; rfl)
    · cases hb : before q d <;> cases ha : after q d <;> rw [hb, ha] at hba
      · exact absurd rfl hba
      · obtain ⟨f, hf, hfc, hfb, hfa⟩ := moved_live q hj hb ha
        obtain ⟨g, hg⟩ : ∃ g, (indexReads d).find? (fun f => decide (World.cell f = q.cell) && !World.holdsAt q.base f) = some g := by
          cases e : (indexReads d).find? (fun f => decide (World.cell f = q.cell) && !World.holdsAt q.base f) with
          | some g => exact ⟨g, rfl⟩
          | none => have := List.find?_eq_none.1 e f hf; simp [hfc, hfb] at this
        exact mk _ (by rw [if_neg (by simp [hr]), if_pos hj, hb, ha]; simp only [Bool.not_false, Bool.and_true,
          Bool.false_and, Bool.false_eq_true, ite_false, Bool.not_true, ite_true]; rw [hg]; rfl)
      · obtain ⟨f, hf, hfc, hfa⟩ := moved_dead q hb ha
        obtain ⟨g, hg⟩ : ∃ g, (indexReads d).find? (fun f => decide (World.cell f = q.cell) && !World.holdsOfPin q.cell q.pin f) = some g := by
          cases e : (indexReads d).find? (fun f => decide (World.cell f = q.cell) && !World.holdsOfPin q.cell q.pin f) with
          | some g => exact ⟨g, rfl⟩
          | none => have := List.find?_eq_none.1 e f hf; simp [hfc, hfa] at this
        exact mk _ (by rw [if_neg (by simp [hr]), if_pos hj, hb, ha]; simp only [Bool.not_false, Bool.and_true,
          Bool.not_true, ite_true]; rw [hg]; rfl)
      · exact absurd rfl hba

/-- **A `blocked` line, checked by its opening**: at every view holding the new pin, the
dependent reads blocked, and its dead supports (exactly the ones that do not hold,
`read_blocked_exact`) name the line's support. -/
theorem line_blocked (q : Question V) {l : Line Fact} (hl : LineHolds q l) (hg : l.goes = .blocked)
    {v : V} (hv : World.pin (Fact := Fact) v q.cell = q.pin) :
    ∃ d ∈ q.deps, d.name = l.dep ∧ ∃ dead, depSlot.read (World.holdsAt v) (some d) = .blocked d dead ∧
      l.support ∈ dead ∧ ∀ f, f ∈ dead ↔ f ∈ d.reads ∧ World.holdsAt v f = false := by
  obtain ⟨d, hd, hn, hs, hc, h⟩ := hl
  rw [hg] at h
  obtain ⟨-, hj, -, hf, -⟩ := h
  have hdead : World.holdsAt v l.support = false := by rw [World.holds_pin, hc, hv]; exact hf
  obtain ⟨dead, hr, hm⟩ := Setup.read_of_dead_mem depSlot (World.holdsAt v) hj hs hdead
  exact ⟨d, hd, hn, dead, hr, hm, (read_blocked_exact depSlot _ d d dead hr).2⟩

/-- **A `restored` line**: at every moved view the dependent reads usable. -/
theorem line_restored (q : Question V) {l : Line Fact} (hl : LineHolds q l) (hg : l.goes = .restored)
    {v : V} (hv : Moved q v) :
    ∃ d ∈ q.deps, d.name = l.dep ∧ depSlot.read (World.holdsAt v) (some d) =
      .usable d (depSlot.evidence (World.holdsAt v) d) := by
  obtain ⟨d, hd, hn, -, -, h⟩ := hl
  rw [hg] at h
  obtain ⟨-, -, -, ha, -⟩ := h
  refine ⟨d, hd, hn, read_of_usable depSlot _ d ?_⟩
  have : depSlot.usable (World.holdsAt v) d = depSlot.usable (movedHolds q) d := by
    unfold Slot.usable Slot.dead
    congr 2
    exact List.filter_congr fun f _ => by rw [moved_holds q hv f]
  rw [this]; exact ha

/-- **Nothing else moves**: under an accepted list, a judged candidate no line names reads usable
at every moved view exactly when it did at the base. -/
theorem unlisted_unchanged (q : Question V) {ls : List (Line Fact)} (hm : Meaning q ls) {d : Dep Fact}
    (hd : d ∈ q.deps) (hr : d.kind.isRow = false) (hj : d.judge = true) (hn : ∀ l ∈ ls, l.dep ≠ d.name)
    {v : V} (hv : Moved q v) : depSlot.usable (World.holdsAt v) d = before q d := by
  have hc : ¬ Changes q d := fun hc => by
    obtain ⟨l, hl, he⟩ := hm.2 d hd hc; exact hn l hl he
  have hba : before q d = after q d := by
    cases e : (before q d == after q d)
    · exact absurd (.inr ⟨hr, hj, by simpa using e⟩) hc
    · simpa using e
  rw [hba]
  unfold after Slot.usable Slot.dead
  congr 2
  exact List.filter_congr fun f _ => by rw [moved_holds q hv f]

/-! ## The judge -/

/-- Why an affected list is refused. -/
inductive Clause where
  /-- the line names no dependent of the question -/
  | notIndexed (dep : String)
  /-- the line's support is not one the dependent reads, or does not name the moved cell -/
  | doesNotRead (dep : String)
  /-- the opening does not say what the new pin says, or the dependent does not go that way -/
  | wrongOpening (dep : String)
  /-- a dependent that changes is not listed -/
  | missing (dep : String)
  deriving DecidableEq, Repr

/-- The clause a failing line is refused by. -/
def clauseOf (q : Question V) (l : Line Fact) : Clause :=
  if (q.deps.any fun d => d.name == l.dep) then
    if (q.deps.any fun d => d.name == l.dep && decide (l.support ∈ d.reads) && decide (World.cell l.support = q.cell))
    then .wrongOpening l.dep else .doesNotRead l.dep
  else .notIndexed l.dep

/-- **The checker**: every line holds; then every dependent that changes is listed. -/
def check (_ : Nat) (q : Question V) (ls : List (Line Fact)) : Judge.Verdict Clause :=
  match ls.find? (fun l => !decide (LineHolds q l)) with
  | some l => .refused (clauseOf q l) [ls.findIdx (fun l => !decide (LineHolds q l))]
  | none =>
    match q.deps.find? (fun d => decide (Changes q d) && !ls.any (·.dep == d.name)) with
    | some d => .refused (.missing d.name) []
    | none => .ok

theorem check_sound {r : Nat} {q : Question V} {ls : List (Line Fact)} (h : check r q ls = .ok) :
    Meaning q ls := by
  unfold check at h
  cases h1 : ls.find? (fun l => !decide (LineHolds q l)) with
  | some e => rw [h1] at h; cases h
  | none =>
    rw [h1] at h
    simp only at h
    cases h2 : q.deps.find? (fun d => decide (Changes q d) && !ls.any (·.dep == d.name)) with
    | some d => rw [h2] at h; cases h
    | none =>
      constructor
      · intro l hl
        have := List.find?_eq_none.1 h1 l hl
        simpa using this
      · intro d hd hc
        have := List.find?_eq_none.1 h2 d hd
        simp only [hc, decide_true, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at this
        simpa [List.any_eq_true] using this

theorem check_complete {r : Nat} {q : Question V} {ls : List (Line Fact)} (h : Meaning q ls) :
    check r q ls = .ok := by
  unfold check
  have h1 : ls.find? (fun l => !decide (LineHolds q l)) = none := by
    apply List.find?_eq_none.2
    intro l hl
    simp [h.1 _ hl]
  have h2 : q.deps.find? (fun d => decide (Changes q d) && !ls.any (·.dep == d.name)) = none := by
    apply List.find?_eq_none.2
    intro d hd
    by_cases hc : Changes q d
    · obtain ⟨l, hl, he⟩ := h.2 d hd hc
      have hany : ls.any (·.dep == d.name) = true := List.any_eq_true.2 ⟨l, hl, by simp [he]⟩
      simp [hc, hany]
    · simp [hc]
  rw [h1, h2]

/-- **The impact analysis as a judge**: the certificate is the affected list with its openings;
decidable, complete everywhere (the producer's list is accepted, `affected_exact`); it never
refutes the question (a bad list says nothing of the move). -/
instance impactJudge : Judge (Question V) (List (Line Fact)) where
  Clause := Clause
  Meaning := Meaning
  check := check
  sound := check_sound
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ hk; cases hk
  Fragment _ := True
  complete := fun {q} _ _ => ⟨affected q, 0, check_complete (affected_exact q)⟩
  mono := by intro r r' o c _ _; rfl

end

end Obend.Analysis


namespace Obend.Analysis

open Obend.Slot Lean

set_option autoImplicit false

/-- A support in an exported table: the cell it names, its name, and the pins (among those the
question names) at which it holds. -/
structure TFact where
  cell : String
  name : String
  pins : List String
  deriving DecidableEq, Repr

/-- A view of an exported table: each cell's pin (a cell not listed is retired). -/
structure TView where
  pins : List (String × String)
  deriving DecidableEq, Repr

/-- **The table as a world.** -/
instance tableWorld : World TView TFact where
  Cell := String
  Pin := String
  cell f := f.cell
  pin v c := v.pins.lookup c
  holdsOfPin _ p f := match p with
    | some q => f.pins.contains q
    | none => false
  Step v v' := v = v'
  dead_none _ := rfl
  retired_step _ _ _ h hr := h ▸ hr
  Ver := Option String
  ver v c := v.pins.lookup c
  Past _ _ := False
  past_irrefl _ h := h
  past_trans _ _ _ h _ := h
  pinOf _ x := x
  pin_ver _ _ := rfl
  ver_step _ _ _ h := .inl (h ▸ rfl)

instance : DecidableEq (World.Cell TView) := inferInstanceAs (DecidableEq String)
instance : DecidableEq (World.Pin TView) := inferInstanceAs (DecidableEq String)

/-! ## The wire -/

def kindOf : String → Except String Kind
  | "candidate" => .ok .candidate
  | "turn" => .ok .turn
  | "cite" => .ok .cite
  | "receipt" => .ok .receipt
  | "law" => .ok .law
  | k => .error s!"unknown dependent kind {k}"

def goesName : Goes → String
  | .blocked => "blocked"
  | .restored => "restored"
  | .rejudge => "rejudge"

def goesOf : String → Except String Goes
  | "blocked" => .ok .blocked
  | "restored" => .ok .restored
  | "rejudge" => .ok .rejudge
  | g => .error s!"unknown line kind {g}"

def factJson (f : TFact) : Json :=
  Json.mkObj [("cell", toJson f.cell), ("name", toJson f.name), ("pins", toJson f.pins)]

def factOf (j : Json) : Except String TFact := do
  return ⟨← j.getObjValAs? String "cell", ← j.getObjValAs? String "name", ← j.getObjValAs? (List String) "pins"⟩

def depJson (d : Dep TFact) : Json :=
  Json.mkObj [("kind", toJson d.kind.name), ("name", toJson d.name), ("judge", toJson d.judge),
    ("reads", Json.arr (d.reads.map factJson).toArray)]

def depOf (j : Json) : Except String (Dep TFact) := do
  let reads ← (← j.getObjValAs? (Array Json) "reads").toList.mapM factOf
  return ⟨← kindOf (← j.getObjValAs? String "kind"), ← j.getObjValAs? String "name",
    ← j.getObjValAs? Bool "judge", reads⟩

def pinJson : Option String → Json
  | some p => toJson p
  | none => Json.null

def questionJson (q : Question TView) : Json :=
  Json.mkObj [("base", Json.arr (q.base.pins.map fun (c, p) => Json.arr #[toJson c, toJson p]).toArray),
    ("cell", toJson (show String from q.cell)), ("pin", pinJson q.pin),
    ("deps", Json.arr (q.deps.map depJson).toArray)]

def questionOfJson (j : Json) : Except String (Question TView) := do
  let base ← (← j.getObjValAs? (Array (Array String)) "base").toList.mapM fun a =>
    match a.toList with
    | [c, p] => .ok (c, p)
    | _ => .error "base: each entry is [cell, pin]"
  let deps ← (← j.getObjValAs? (Array Json) "deps").toList.mapM depOf
  let cell ← j.getObjValAs? String "cell"
  let pin : Option String := match j.getObjVal? "pin" with
    | .ok (.str p) => some p
    | _ => none
  return { base := ⟨base⟩, deps := deps, cell := cell, pin := pin }

def lineJson (l : Line TFact) : Json :=
  Json.mkObj [("dep", toJson l.dep), ("goes", toJson (goesName l.goes)), ("support", factJson l.support),
    ("value", toJson l.value)]

def lineOf (j : Json) : Except String (Line TFact) := do
  return ⟨← j.getObjValAs? String "dep", ← goesOf (← j.getObjValAs? String "goes"),
    ← factOf (← j.getObjVal? "support"), ← j.getObjValAs? Bool "value"⟩

def linesJson (ls : List (Line TFact)) : Json := Json.mkObj [("lines", Json.arr (ls.map lineJson).toArray)]

def linesOfJson (j : Json) : Except String (List (Line TFact)) := do
  (← j.getObjValAs? (Array Json) "lines").toList.mapM lineOf

def questionOf (s : String) : Except String (Question TView) := Json.parse s >>= questionOfJson
def linesOf (s : String) : Except String (List (Line TFact)) := Json.parse s >>= linesOfJson

/-! ## The planted bad certificate, and the tooth -/

/-- `a` reads cell `x`; the question moves `y`. -/
def badQuestion : Question TView :=
  { base := ⟨[("x", "1"), ("y", "1")]⟩, cell := "y", pin := some "2",
    deps := [⟨.candidate, "a", true, [⟨"x", "x is 1", ["1"]⟩]⟩] }

/-- A line naming `a` as blocked by a support that is not about the moved cell. -/
def badLines : List (Line TFact) := [⟨"a", .blocked, ⟨"x", "x is 1", ["1"]⟩, false⟩]

-- fixture kept (2026-11-04): consumed by Obend/Ledger/Report.lean, Obend/Hardware/Judge.lean, a proof in this file
theorem bad_refused : check 0 badQuestion badLines = .refused (.doesNotRead "a") [0] := by
  cbv

/-- A page `Beta` at version 1, a following embed of it in `Alpha` (its page present; its bytes the
same as at version 1), and Beta moved to version 2, whose bytes differ. -/
def embedQuestion : Question TView :=
  { base := ⟨[("Beta", "v1"), ("Alpha", "v1")]⟩, cell := "Beta", pin := some "v2",
    deps := [⟨.cite, "Alpha: ![[Beta]]", true,
      [⟨"Beta", "present Beta", ["v1", "v2"]⟩, ⟨"Beta", "current Beta@v1", ["v1"]⟩]⟩] }

/-- The honest prediction: the embed goes behind, resting on its `current` fact at v2. -/
-- fixture kept (2026-11-04): cheap closed check of `affected` on literal data
example :
    affected embedQuestion = [⟨"Alpha: ![[Beta]]", .blocked, ⟨"Beta", "current Beta@v1", ["v1"]⟩, false⟩] := by
  cbv

/-- **The registered format `impact@1`.** -/
@[expose] def format : Judge.Format where
  name := "impact"
  version := "1"
  Obj := Question TView
  Cert := List (Line TFact)
  judge := impactJudge
  decodeObj := questionOf
  decodeCert := linesOf
  trust := .compiled
  regime := .decidable
  bad := (badQuestion, badLines)
  badGrade := 0
  bad_refused := ⟨_, _, bad_refused⟩

/-- The formats the analyses register. -/
@[expose] def formats : List Judge.Format := [format]

end Obend.Analysis

end
