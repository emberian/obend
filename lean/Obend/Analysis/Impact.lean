module
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
public import Obend.Analysis.Setup
public import Obend.Fold
public import Obend.Intention
public import Obend.Judge.Class
public import Obend.Tactic.Tooth
@[expose] public section

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

instance (q : Question V) (l : Line Fact) : Decidable (LineHolds q l) := by
  unfold LineHolds; cases l.goes <;> exact inferInstance

instance (q : Question V) (d : Dep Fact) : Decidable (Changes q d) := by
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

end
