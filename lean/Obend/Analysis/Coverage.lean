module
/-
# Obend.Analysis.Coverage — a report is a judged fold, and its receipt says nothing was left out

`review/VISION-CLAUDE-20261031.md` §7.2 ("reports are judged folds with non-omission receipts":
completeness, every movement in the range is in the report, as a judge instance) and
`astra/ASTRA-VISION-20261031.md` §6.1 item 3 (a report is a query over a pinned view with its
completeness conditions).

A REPORT over rows (`Report`) says which rows it is about (`sel`), the key it names each by, and
how it adds one in. Its run is a left fold (`Report.run`) that takes every selected row, in order,
and nothing else. What a report says (`Said`) is the keys it took and what it added up.

A BOOK is the rows a report is run over, with the root a stranger holds for them (`rootOf`: a
digest of the whole list). The judge (`check`) recomputes the fold and the root and compares:

- `omitted k`: a selected row, keyed `k`, is not in the report;
- `extra k`: the report names a key no selected row has;
- `order`, `total`: the keys or the total differ from the fold's;
- `root` (checked last): the rows are not the ones the root commits (a REFUTATION: no report of
  these rows can be meant at that root, `Judge.refuted`).

Theorems, once for every report:

- `run_keys`, `run_total`: the fold takes exactly the selected rows, in order, and its total is
  theirs added up;
- `covers` (**non-omission**): every selected row of the book is in the report's keys;
  `only_selected`: every key it names is a selected row's;
- `check_covers`: a report the judge accepts names every selected row of the book, and its total is
  the selected rows' total; `check_binds`: of every list of rows whose root is the book's, when the
  root binds (two lists with one root are one list);
- `coverJudge`: the judge, sound, complete (the honest fold is accepted), monotone.

Teeth: `#tooth check_covers` by mutation of the fold (`Report.run` drops the last row: the proof
no longer checks), and `drop_last_refused` (a producer that drops a selected row is refused
`omitted`, naming the row).
-/
public import Obend.Judge.Class
public import Obend.Tactic.Tooth
@[expose] public section

namespace Obend.Analysis.Coverage

set_option autoImplicit false

/-- A report over rows: which rows it is about, the key it names each by, how it adds one in. -/
structure Report (Row Key Acc : Type) where
  sel : Row → Bool
  key : Row → Key
  add : Acc → Row → Acc
  init : Acc

/-- What a report says: the keys of the rows it took, in order, and what it added up. -/
structure Said (Key Acc : Type) where
  keys : List Key
  total : Acc
  deriving DecidableEq, Repr

variable {Row Key Acc : Type}

/-- One row of the report's fold: a selected row is taken, any other passed over. -/
def Report.step (R : Report Row Key Acc) (s : Said Key Acc) (r : Row) : Said Key Acc :=
  if R.sel r then ⟨s.keys ++ [R.key r], R.add s.total r⟩ else s

/-- **The report's fold** over the rows, from nothing. -/
def Report.run (R : Report Row Key Acc) (rows : List Row) : Said Key Acc :=
  rows.foldl R.step ⟨[], R.init⟩

theorem foldl_step (R : Report Row Key Acc) : ∀ (rows : List Row) (s : Said Key Acc),
    rows.foldl R.step s = ⟨s.keys ++ (rows.filter R.sel).map R.key, (rows.filter R.sel).foldl R.add s.total⟩
  | [], s => by simp
  | r :: rs, s => by
    simp only [List.foldl_cons, Report.step]
    cases h : R.sel r
    · simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons, h]
      exact foldl_step R rs s
    · simp only [↓reduceIte, List.filter_cons, h, List.map_cons, List.foldl_cons]
      rw [foldl_step R rs]
      simp

/-- The fold takes exactly the selected rows, in order. -/
theorem run_keys (R : Report Row Key Acc) (rows : List Row) :
    (R.run rows).keys = (rows.filter R.sel).map R.key := by
  simp [Report.run, foldl_step]

/-- Its total is the selected rows added up. -/
theorem run_total (R : Report Row Key Acc) (rows : List Row) :
    (R.run rows).total = (rows.filter R.sel).foldl R.add R.init := by
  simp [Report.run, foldl_step]

/-- **Non-omission**: every selected row is in the report. -/
theorem covers (R : Report Row Key Acc) {rows : List Row} {r : Row} (hr : r ∈ rows) (hs : R.sel r = true) :
    R.key r ∈ (R.run rows).keys := by
  rw [run_keys]
  exact List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, hs⟩, rfl⟩

/-- Every key the report names is a selected row's. -/
theorem only_selected (R : Report Row Key Acc) {rows : List Row} {k : Key} (hk : k ∈ (R.run rows).keys) :
    ∃ r ∈ rows, R.sel r = true ∧ R.key r = k := by
  rw [run_keys] at hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk
  obtain ⟨hr, hs⟩ := List.mem_filter.1 hr
  exact ⟨r, hr, hs, rfl⟩

/-! ## The judge -/

/-- The rows a report is run over, with the root a stranger holds for them. -/
structure Book (Row D : Type) where
  rows : List Row
  root : D

/-- Why a report was refused. -/
inductive Clause (Key : Type) where
  /-- a selected row is not in the report -/
  | omitted (k : Key)
  /-- the report names a key no selected row has -/
  | extra (k : Key)
  /-- the keys are the selected rows' but not in the fold's order, or repeated -/
  | order
  /-- the total is not the selected rows' -/
  | total
  /-- the rows are not the ones the root commits -/
  | root
  deriving DecidableEq, Repr

section
variable {D : Type} [DecidableEq D] [DecidableEq Key] [DecidableEq Acc]

/-- What an accepted report means: the root commits the rows, and the report is the fold. -/
def Meaning (R : Report Row Key Acc) (rootOf : List Row → D) (b : Book Row D) (s : Said Key Acc) : Prop :=
  rootOf b.rows = b.root ∧ s = R.run b.rows

/-- **The judge**: recompute the fold and the root, and say where the report departs from them. The
root is checked last, so a report's omissions are named before the digest is computed. -/
def check (R : Report Row Key Acc) (rootOf : List Row → D) (b : Book Row D) (s : Said Key Acc) :
    Judge.Verdict (Clause Key) :=
  match (R.run b.rows).keys.find? (fun k => !s.keys.contains k) with
  | some k => .refused (.omitted k) []
  | none =>
    match s.keys.find? (fun k => !(R.run b.rows).keys.contains k) with
    | some k => .refused (.extra k) []
    | none =>
      if s.keys ≠ (R.run b.rows).keys then .refused .order []
      else if s.total ≠ (R.run b.rows).total then .refused .total []
      else if rootOf b.rows ≠ b.root then .refused .root []
      else .ok

theorem check_sound {R : Report Row Key Acc} {rootOf : List Row → D} {b : Book Row D} {s : Said Key Acc}
    (h : check R rootOf b s = .ok) : Meaning R rootOf b s := by
  unfold check at h
  cases h1 : (R.run b.rows).keys.find? (fun k => !s.keys.contains k) with
  | some k => rw [h1] at h; cases h
  | none =>
    rw [h1] at h
    cases h2 : s.keys.find? (fun k => !(R.run b.rows).keys.contains k) with
    | some k => rw [h2] at h; cases h
    | none =>
      rw [h2] at h
      by_cases hk : s.keys = (R.run b.rows).keys
      · by_cases ht : s.total = (R.run b.rows).total
        · by_cases hr : rootOf b.rows = b.root
          · refine ⟨hr, ?_⟩
            cases s; cases hs : R.run b.rows
            simp_all
          · simp [hk, ht, hr] at h
        · simp [hk, ht] at h
      · simp [hk] at h

theorem check_complete {R : Report Row Key Acc} {rootOf : List Row → D} {b : Book Row D} {s : Said Key Acc}
    (h : Meaning R rootOf b s) : check R rootOf b s = .ok := by
  obtain ⟨hr, rfl⟩ := h
  unfold check
  have h1 : (R.run b.rows).keys.find? (fun k => !(R.run b.rows).keys.contains k) = none :=
    List.find?_eq_none.2 fun k hk => by simp [hk]
  simp only [h1, hr, ne_eq, not_true_eq_false, ↓reduceIte]

/-- A refusal of the root is a refutation: no report of these rows means anything at that root. -/
theorem check_root_refutes {R : Report Row Key Acc} {rootOf : List Row → D} {b : Book Row D} {s : Said Key Acc}
    {p : List Nat} (h : check R rootOf b s = .refused .root p) : ∀ s', ¬ Meaning R rootOf b s' := by
  intro s' hm
  unfold check at h
  cases h1 : (R.run b.rows).keys.find? (fun k => !s.keys.contains k) with
  | some k => rw [h1] at h; cases h
  | none =>
    rw [h1] at h
    cases h2 : s.keys.find? (fun k => !(R.run b.rows).keys.contains k) with
    | some k => rw [h2] at h; cases h
    | none =>
      rw [h2] at h
      simp only [hm.1, ne_eq, not_true_eq_false, ↓reduceIte] at h
      split at h
      · cases h
      · split at h <;> cases h

/-- **An accepted report covers the book**: every selected row is in it, it names no other, and its
total is the selected rows added up. -/
theorem check_covers {R : Report Row Key Acc} {rootOf : List Row → D} {b : Book Row D} {s : Said Key Acc}
    (h : check R rootOf b s = .ok) :
    (∀ r ∈ b.rows, R.sel r = true → R.key r ∈ s.keys) ∧
      (∀ k ∈ s.keys, ∃ r ∈ b.rows, R.sel r = true ∧ R.key r = k) ∧
      s.total = (b.rows.filter R.sel).foldl R.add R.init := by
  obtain ⟨_, rfl⟩ := check_sound h
  exact ⟨fun r hr hs => covers R hr hs, fun k hk => only_selected R hk, run_total R b.rows⟩

#tooth check_covers by mutation Report.run := fun R rows => rows.dropLast.foldl R.step ⟨[], R.init⟩

/-- **Non-omission against the register a stranger holds**: of every list of rows whose root is the
book's, an accepted report names every selected row, when the root binds. -/
theorem check_binds {R : Report Row Key Acc} {rootOf : List Row → D} {b : Book Row D} {s : Said Key Acc}
    (h : check R rootOf b s = .ok) (reg : List Row) (hroot : rootOf reg = b.root)
    (hbind : rootOf reg = rootOf b.rows → reg = b.rows) :
    ∀ r ∈ reg, R.sel r = true → R.key r ∈ s.keys := by
  have hm := check_sound h
  have : reg = b.rows := hbind (hroot.trans hm.1.symm)
  subst this
  exact (check_covers h).1

/-- **The coverage judge.** -/
@[reducible] def coverJudge (R : Report Row Key Acc) (rootOf : List Row → D) :
    Judge (Book Row D) (Said Key Acc) where
  Clause := Clause Key
  Meaning := Meaning R rootOf
  check _ := check R rootOf
  sound := check_sound
  refutes k := k == .root
  refuted := by
    intro _ o c k p h hk
    cases k <;> simp at hk
    exact check_root_refutes h
  Fragment _ := True
  complete := fun {o} _ ⟨c, hc⟩ => ⟨c, 0, check_complete hc⟩
  mono := by intro _ _ _ _ _ _; rfl

end

/-! ## The tooth on a concrete book -/

/-- Rows `(period, amount)`, keyed by their amount; the report is about period 11 and adds the
amounts. -/
def demo : Report (Nat × Nat) Nat Nat := ⟨fun r => r.1 == 11, fun r => r.2, fun t r => t + r.2, 0⟩

/-- A root that sees every row (a stand-in for the deployed digest in the example). -/
def demoRoot (l : List (Nat × Nat)) : Nat := l.foldl (fun h r => h * 1000003 + r.1 * 1009 + r.2) 7

def demoBook : Book (Nat × Nat) Nat :=
  ⟨[(10, 5), (11, 500), (11, 120), (12, 9)], demoRoot [(10, 5), (11, 500), (11, 120), (12, 9)]⟩

theorem demo_honest : check demo demoRoot demoBook (demo.run demoBook.rows) = .ok := by decide

/-- **A report that drops a selected row is refused, naming it.** -/
theorem drop_last_refused :
    check demo demoRoot demoBook ⟨[500], 500⟩ = .refused (.omitted 120) [] := by decide

/-- A report of other rows at the book's root is refuted by the root. -/
theorem other_rows_refuted :
    check demo demoRoot ⟨[(11, 500)], demoBook.root⟩ ⟨[500], 500⟩ = .refused .root [] := by decide

end Obend.Analysis.Coverage

end
