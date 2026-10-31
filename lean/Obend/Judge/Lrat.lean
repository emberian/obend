module
/-
# Obend.Judge.Lrat — LRAT refutations of CNF formulas, a registered foreign format

`review/VISION-CLAUDE-20261031.md` §6.3 (the SAT row) and §6.5 (the LRAT judge). A CNF is DIMACS
clauses over integer literals; an LRAT proof (Heule et al. 2013; Cruz-Filipe et al. 2017) is a list of
steps, each adding a clause with the ids of the clauses that make it a reverse-unit-propagation
(RUP) consequence of what is held, or deleting clauses. The checker keeps the held clauses as an
association list from ids, so the kernel and compiled code run the same function.

- `propagate_sound`: every clause RUP-checked against held clauses that a model satisfies is
  satisfied by that model; `run_sound`: a run that adds the empty clause refutes the formula.
- `lratJudge`: the judge. A certificate is a refutation or a MODEL; a model that satisfies the
  formula is a refusal by `satisfiable`, which REFUTES (the formula is not unsatisfiable,
  `refuted`), while a failed refutation (`noConflict`, `missingHint`, `notUnit`, `ratHint`,
  `noEmptyClause`) refuses without refuting. The grade is the number of steps checked.
- Completeness is claimed on the fragment of formulas holding two complementary unit clauses (the
  one-step refutation); completeness for every unsatisfiable formula is the completeness of
  resolution and is not claimed.
- `parseDimacs` / `parseLrat`: the decoders of CaDiCaL's text output (`--lrat --binary=false`);
  `format`: the registered format, trust `compiled` for byte-level runs and a planted certificate
  (a refutation whose one step names a hint that is not unit) refused at every grade.

RAT steps (negative hints) are refused as `ratHint`: CaDiCaL's LRAT is RUP-only.
-/
public import Obend.Judge.Class

public section
namespace Obend.Judge.Lrat
set_option autoImplicit false

/-! ## Formulas and their semantics -/

abbrev Clause := List Int

/-- A formula in DIMACS form: its declared variable count and its clauses, numbered from 1. -/
structure Cnf where
  vars : Nat
  clauses : List Clause
  deriving DecidableEq, Repr, Inhabited

/-- A literal's value under an assignment of the variables. -/
@[expose] def litTrue (σ : Nat → Bool) (l : Int) : Bool := if 0 < l then σ l.natAbs else !σ l.natAbs

@[expose] def Sat (σ : Nat → Bool) (c : Clause) : Prop := ∃ l ∈ c, litTrue σ l = true

@[expose] def Models (σ : Nat → Bool) (F : Cnf) : Prop := ∀ c ∈ F.clauses, Sat σ c

@[expose] def Unsat (F : Cnf) : Prop := ∀ σ, ¬ Models σ F

theorem litTrue_neg (σ : Nat → Bool) {l : Int} (h : l ≠ 0) : litTrue σ (-l) = !litTrue σ l := by
  unfold litTrue
  rw [Int.natAbs_neg]
  by_cases hp : 0 < l
  · rw [if_neg (show ¬ (0 < -l) by omega), if_pos hp]
  · rw [if_pos (show 0 < -l by omega), if_neg hp, Bool.not_not]

/-! ## Steps and the checker -/

inductive Step where
  | add (id : Nat) (clause : Clause) (hints : List Int)
  | del (ids : List Nat)
  deriving @[expose] DecidableEq, Repr

/-- A certificate: a refutation, or a model (a list of true literals) refuting unsatisfiability. -/
inductive Cert where
  | refutation (steps : List Step)
  | model (lits : List Int)
  deriving DecidableEq, Repr

inductive Refusal where
  /-- the hints ran out before a conflict -/
  | noConflict
  /-- a hint names no held clause -/
  | missingHint (id : Int)
  /-- a hint's clause is neither falsified nor unit under the propagated literals -/
  | notUnit (id : Int)
  /-- a negative hint (a RAT step), unsupported -/
  | ratHint (id : Int)
  /-- the proof ended without adding the empty clause -/
  | noEmptyClause
  /-- the model satisfies every clause: the formula is satisfiable -/
  | satisfiable
  /-- the model leaves this clause (by number) unsatisfied -/
  | notAModel (clause : Nat)
  deriving @[expose] DecidableEq, Repr

/-- The held clauses. -/
abbrev Db := List (Nat × Clause)

/-- `l` is falsified by the literals `α` taken true. -/
@[expose] def falsified (α : List Int) (l : Int) : Bool := l != 0 && α.contains (-l)

/-- Reverse unit propagation along `hints`, from the literals `α` taken true: `ok` on a conflict. -/
@[expose] def propagate (db : Db) : List Int → List Int → Except Refusal Unit
  | _, [] => .error .noConflict
  | α, h :: hs =>
    if h ≤ 0 then .error (.ratHint h) else
    match db.lookup h.toNat with
    | none => .error (.missingHint h)
    | some d =>
      match d.filter (fun l => !falsified α l) with
      | [] => .ok ()
      | [l] => propagate db (l :: α) hs
      | _ => .error (.notUnit h)

/-- The literals a clause's negation takes true. -/
@[expose] def negation (c : Clause) : List Int := (c.filter (· != 0)).map (- ·)

/-- Run the steps from the held clauses; `ok` when the empty clause is added. The refusal carries
the step's index. -/
@[expose] def run : Db → List Step → Nat → Except (Refusal × Nat) Unit
  | _, [], i => .error (.noEmptyClause, i)
  | db, .del ids :: rest, i => run (db.filter fun p => !ids.contains p.1) rest (i + 1)
  | db, .add id c hints :: rest, i =>
    match propagate db (negation c) hints with
    | .error e => .error (e, i)
    | .ok () => if c.isEmpty then .ok () else run ((id, c) :: db) rest (i + 1)

/-- The formula's clauses, numbered from 1. -/
@[expose] def initial (F : Cnf) : Db := (List.range F.clauses.length).zip F.clauses |>.map fun p => (p.1 + 1, p.2)

/-- The first clause (by number) a model leaves unsatisfied. -/
def firstUnsat (lits : List Int) (F : Cnf) : Option Nat :=
  ((List.range F.clauses.length).zip F.clauses).findSome? fun p =>
    if p.2.any lits.contains then none else some (p.1 + 1)

/-- A model as an assignment: a variable is true when its positive literal is listed. -/
def assignmentOf (lits : List Int) (v : Nat) : Bool := lits.contains (v : Int)

/-- The checker, at a grade bounding the number of steps. -/
@[expose] def check (r : Nat) (F : Cnf) : Cert → Verdict Refusal
  | .refutation steps =>
    if steps.length ≤ r then
      match run (initial F) steps 0 with
      | .ok () => .ok
      | .error (e, i) => .refused e [i]
    else .uncovered
  | .model lits =>
    if lits.all (fun l => l != 0 && !lits.contains (-l)) then
      match firstUnsat lits F with
      | none => .refused .satisfiable []
      | some i => .refused (.notAModel i) [i]
    else .refused (.notAModel 0) []

/-! ## Soundness -/

theorem lookup_mem {k : Nat} {d : Clause} : ∀ {db : Db}, db.lookup k = some d → (k, d) ∈ db
  | [], h => by simp at h
  | (k', d') :: rest, h => by
    cases e : k == k'
    · simp only [List.lookup, e] at h; exact List.mem_cons_of_mem _ (lookup_mem h)
    · simp only [List.lookup, e] at h; cases h
      have : k = k' := by simpa using e
      subst this; exact List.mem_cons_self

/-- **RUP is sound**: a model of every held clause, making every literal of `α` true, does not
reach a conflict. -/
theorem propagate_sound (σ : Nat → Bool) (db : Db) (hdb : ∀ p ∈ db, Sat σ p.2) :
    ∀ (hints : List Int) (α : List Int), (∀ a ∈ α, litTrue σ a = true) → propagate db α hints ≠ .ok ()
  | [], α, _ => by simp [propagate]
  | h :: hs, α, hα => by
    unfold propagate
    by_cases hneg : h ≤ 0
    · rw [if_pos hneg]; simp
    rw [if_neg hneg]
    cases hl : db.lookup h.toNat with
    | none => simp
    | some d =>
      obtain ⟨l, hl_mem, hl_true⟩ := hdb _ (lookup_mem hl)
      have hkeep : l ∈ d.filter (fun l => !falsified α l) := by
        refine List.mem_filter.2 ⟨hl_mem, ?_⟩
        cases hf : falsified α l
        · rfl
        · exfalso
          simp only [falsified, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at hf
          have := hα _ hf.2
          rw [litTrue_neg σ hf.1, hl_true] at this
          cases this
      simp only
      split
      · rename_i e; rw [e] at hkeep; cases hkeep
      · rename_i l' e
        rw [e] at hkeep
        have : l = l' := List.mem_singleton.1 hkeep
        subst this
        exact propagate_sound σ db hdb hs (l :: α) (by
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hl_true
          · exact hα a ha)
      · simp

/-- A clause RUP-checked against held clauses is satisfied by every model of them. -/
theorem negation_sound (σ : Nat → Bool) (db : Db) (hdb : ∀ p ∈ db, Sat σ p.2) (c : Clause) (hints : List Int)
    (h : propagate db (negation c) hints = .ok ()) : Sat σ c := by
  apply Classical.byContradiction
  intro hc
  apply propagate_sound σ db hdb hints (negation c) _ h
  intro a ha
  simp only [negation, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at ha
  obtain ⟨l, ⟨hl, hl0⟩, rfl⟩ := ha
  rw [litTrue_neg σ hl0]
  cases e : litTrue σ l
  · rfl
  · exact absurd ⟨l, hl, e⟩ hc

/-- **A run that adds the empty clause refutes every model of the held clauses.** -/
theorem run_sound (σ : Nat → Bool) : ∀ (db : Db) (steps : List Step) (i : Nat),
    (∀ p ∈ db, Sat σ p.2) → run db steps i = .ok () → False
  | db, [], i, _, h => by simp [run] at h
  | db, .del ids :: rest, i, hdb, h => by
    simp only [run] at h
    exact run_sound σ _ rest (i + 1) (fun p hp => hdb p (List.mem_filter.1 hp).1) h
  | db, .add id c hints :: rest, i, hdb, h => by
    simp only [run] at h
    cases hp : propagate db (negation c) hints with
    | error e => rw [hp] at h; cases h
    | ok u =>
      rw [hp] at h
      have hc := negation_sound σ db hdb c hints hp
      by_cases he : c.isEmpty
      · obtain ⟨l, hl, _⟩ := hc
        simp only [List.isEmpty_iff] at he; subst he; cases hl
      · rw [if_neg he] at h
        exact run_sound σ _ rest (i + 1) (by
          intro p hp'
          rcases List.mem_cons.1 hp' with rfl | hp'
          · exact hc
          · exact hdb p hp') h

theorem initial_sat (σ : Nat → Bool) (F : Cnf) (hσ : Models σ F) : ∀ p ∈ initial F, Sat σ p.2 := by
  intro p hp
  simp only [initial, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact hσ _ (List.of_mem_zip hq).2

/-- **Soundness**: an accepted refutation means the formula is unsatisfiable. -/
theorem check_sound {r : Nat} {F : Cnf} {c : Cert} (h : check r F c = .ok) : Unsat F := by
  intro σ hσ
  cases c with
  | refutation steps =>
    simp only [check] at h
    split at h
    · cases hr : run (initial F) steps 0 with
      | error e => rw [hr] at h; cases h
      | ok u => exact run_sound σ _ steps 0 (initial_sat σ F hσ) hr
    · cases h
  | model lits =>
    simp only [check] at h
    split at h
    · split at h <;> cases h
    · cases h

/-! ## The model side: a refusal by `satisfiable` refutes -/

theorem firstUnsat_none {lits : List Int} {F : Cnf} (h : firstUnsat lits F = none) :
    ∀ c ∈ F.clauses, c.any lits.contains = true := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hz : (i, F.clauses[i]) ∈ (List.range F.clauses.length).zip F.clauses := by
    rw [List.mem_iff_getElem]
    refine ⟨i, by simp [hi], ?_⟩
    simp
  have := List.findSome?_eq_none_iff.1 h _ hz
  simp only at this
  split at this
  · assumption
  · cases this

theorem model_sat {lits : List Int} (hcons : lits.all (fun l => l != 0 && !lits.contains (-l)) = true)
    {c : Clause} (hc : c.any lits.contains = true) : Sat (assignmentOf lits) c := by
  obtain ⟨l, hl, hin⟩ := List.any_eq_true.1 hc
  refine ⟨l, hl, ?_⟩
  have hin' : l ∈ lits := by simpa using hin
  have hok := List.all_eq_true.1 hcons l hin'
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hok
  obtain ⟨h0, hnot⟩ := hok
  have hnot' : -l ∉ lits := by simpa using hnot
  unfold litTrue assignmentOf
  by_cases gt : 0 < l
  · rw [if_pos gt]
    have : ((l.natAbs : Nat) : Int) = l := by omega
    rw [this]; simpa using hin'
  · rw [if_neg gt]
    have : ((l.natAbs : Nat) : Int) = -l := by omega
    rw [this]; simpa using hnot'

theorem propagate_ne_satisfiable (db : Db) : ∀ (α : List Int) (hints : List Int),
    propagate db α hints ≠ .error .satisfiable
  | _, [] => by simp [propagate]
  | α, h :: hs => by
    unfold propagate
    split
    · simp
    · split
      · simp
      · split
        · simp
        · exact propagate_ne_satisfiable db _ hs
        · simp

theorem run_ne_satisfiable : ∀ (db : Db) (steps : List Step) (i j : Nat), run db steps i ≠ .error (.satisfiable, j)
  | _, [], i, j => by simp [run]
  | db, .del ids :: rest, i, j => by simp only [run]; exact run_ne_satisfiable _ rest _ j
  | db, .add id c hints :: rest, i, j => by
    simp only [run]
    cases hp : propagate db (negation c) hints with
    | error e =>
      simp only [ne_eq, Except.error.injEq, Prod.mk.injEq, not_and]
      intro he; subst he; exact absurd hp (propagate_ne_satisfiable db _ hints)
    | ok u =>
      simp only
      split
      · simp
      · exact run_ne_satisfiable _ rest _ j

theorem check_refuted {r : Nat} {F : Cnf} {c : Cert} {k : Refusal} {p : List Nat}
    (h : check r F c = .refused k p) (hk : (k == .satisfiable) = true) : ¬ Unsat F := by
  have hk' : k = .satisfiable := by simpa using hk
  subst hk'
  cases c with
  | refutation steps =>
    simp only [check] at h
    split at h
    · split at h
      · cases h
      · rename_i e i he
        cases h
        exact absurd he (run_ne_satisfiable _ steps 0 i)
    · cases h
  | model lits =>
    simp only [check] at h
    split at h
    · rename_i hcons
      cases hf : firstUnsat lits F with
      | none =>
        intro hu
        exact hu (assignmentOf lits) fun c hc => model_sat hcons (firstUnsat_none hf c hc)
      | some i => rw [hf] at h; cases h
    · cases h

/-! ## Completeness on complementary units -/

/-- The fragment: two clauses `[l]` and `[-l]`, at numbers `i` and `j`. -/
def ComplementaryUnits (F : Cnf) : Prop :=
  ∃ i j : Nat, ∃ l : Int, l ≠ 0 ∧ (initial F).lookup i = some [l] ∧ (initial F).lookup j = some [-l]

theorem complementary_accepted {F : Cnf} {i j : Nat} {l : Int} (h0 : l ≠ 0)
    (hi : (initial F).lookup i = some [l]) (hj : (initial F).lookup j = some [-l]) (hi0 : 0 < i) (hj0 : 0 < j) :
    check 1 F (.refutation [.add 0 [] [(i : Int), (j : Int)]]) = .ok := by
  have hi' : ¬ ((i : Int) ≤ 0) := by omega
  have hj' : ¬ ((j : Int) ≤ 0) := by omega
  have hni : (i : Int).toNat = i := by omega
  have hnj : (j : Int).toNat = j := by omega
  have hf1 : falsified [] l = false := by simp [falsified]
  have hf2 : falsified [l] (-l) = true := by simp [falsified, h0]
  have i0 : i ≠ 0 := by omega
  have j0 : j ≠ 0 := by omega
  simp [check, run, negation, propagate, hni, hnj, hi, hj, hf1, hf2, i0, j0]

theorem initial_pos {F : Cnf} {i : Nat} {d : Clause} (h : (initial F).lookup i = some d) : 0 < i := by
  have := lookup_mem h
  simp only [initial, List.mem_map] at this
  obtain ⟨q, _, e⟩ := this
  cases e; omega

/-! ## The judge -/

instance lratJudge : Judge Cnf Cert where
  Clause := Refusal
  Meaning F _ := Unsat F
  check := check
  sound := check_sound
  refutes k := k == .satisfiable
  refuted h hk _ := check_refuted h hk
  Fragment := ComplementaryUnits
  complete := by
    rintro F ⟨i, j, l, h0, hi, hj⟩ _
    exact ⟨_, 1, complementary_accepted h0 hi hj (initial_pos hi) (initial_pos hj)⟩
  mono := by
    intro r r' F c le hne
    cases c with
    | refutation steps =>
      simp only [check] at hne ⊢
      by_cases hl : steps.length ≤ r
      · rw [if_pos hl, if_pos (Nat.le_trans hl le)]
      · rw [if_neg hl] at hne; exact absurd rfl hne
    | model lits => rfl

/-! ## Decoders (CaDiCaL's text output) -/

/-- The whitespace-separated tokens of a line. -/
def tokens (line : String) : List String :=
  (line.split fun c => c == ' ' || c == '\t' || c == '\r').toList.map (·.toString) |>.filter (· ≠ "")

def parseInt (s : String) : Except String Int :=
  match s.toInt? with
  | some n => .ok n
  | none => .error s!"not an integer: {s}"

/-- Split a list of integers at its first `0`. -/
def untilZero : List Int → Option (List Int × List Int)
  | [] => none
  | 0 :: rest => some ([], rest)
  | x :: rest => (untilZero rest).map fun (a, b) => (x :: a, b)

/-- DIMACS: a `p cnf V C` header, `c` comments, clauses terminated by `0` (possibly across lines). -/
def parseDimacs (text : String) : Except String Cnf := do
  let lines := (text.split (· == '\n')).toList.map (·.toString)
  let mut vars : Option Nat := none
  let mut count : Nat := 0
  let mut body : Array Int := #[]
  for line in lines do
    let ts := tokens line
    match ts with
    | [] => pure ()
    | "c" :: _ => pure ()
    | "p" :: "cnf" :: v :: c :: [] =>
      match v.toNat?, c.toNat? with
      | some v, some c => vars := some v; count := c
      | _, _ => throw s!"bad header: {line}"
    | _ =>
      if ts.head?.map (·.startsWith "c") == some true then pure () else
      for t in ts do body := body.push (← parseInt t)
  let some v := vars | throw "no `p cnf` header"
  let mut clauses : Array Clause := #[]
  let mut cur : Array Int := #[]
  for x in body do
    if x == 0 then clauses := clauses.push cur.toList; cur := #[] else cur := cur.push x
  if !cur.isEmpty then throw "last clause not terminated by 0"
  if clauses.size != count then throw s!"header says {count} clauses, found {clauses.size}"
  if clauses.any (·.any fun l => l.natAbs > v) then throw "a literal exceeds the declared variables"
  return ⟨v, clauses.toList⟩

/-- LRAT text: `id lits 0 hints 0` or `id d ids 0`, one step per line. -/
def parseLrat (text : String) : Except String Cert := do
  let lines := (text.split (· == '\n')).toList.map (·.toString)
  let mut steps : Array Step := #[]
  for line in lines do
    match tokens line with
    | [] => pure ()
    | "c" :: _ => pure ()
    | idTok :: "d" :: rest =>
      let _ ← parseInt idTok
      let ids ← rest.mapM parseInt
      let some (ids, []) := untilZero ids | throw s!"bad deletion: {line}"
      if ids.any (· < 0) then throw s!"negative id in deletion: {line}"
      steps := steps.push (.del (ids.map Int.toNat))
    | idTok :: rest =>
      let id ← parseInt idTok
      if id ≤ 0 then throw s!"bad step id: {line}"
      let xs ← rest.mapM parseInt
      let some (lits, more) := untilZero xs | throw s!"clause not terminated: {line}"
      let some (hints, []) := untilZero more | throw s!"hints not terminated: {line}"
      steps := steps.push (.add id.toNat lits hints)
  return .refutation steps.toList

/-- A model as text: DIMACS `v` lines (`v 1 -2 3 0`), as a SAT solver prints them. -/
def parseModel (text : String) : Except String Cert := do
  let lines := (text.split (· == '\n')).toList.map (·.toString)
  let mut lits : Array Int := #[]
  for line in lines do
    match tokens line with
    | "v" :: rest => for t in rest do
        let x ← parseInt t
        if x != 0 then lits := lits.push x
    | _ => pure ()
  return .model lits.toList

/-- A certificate as text: a model when it has `v` lines, else an LRAT refutation. -/
def parseCert (text : String) : Except String Cert :=
  if ((text.split (· == '\n')).toList.any fun l => (tokens l.toString).head? == some "v") then parseModel text
  else parseLrat text

/-- DIMACS text of a formula. -/
def Cnf.toDimacs (F : Cnf) : String :=
  let body := F.clauses.map fun c => String.intercalate " " ((c ++ [0]).map toString)
  String.intercalate "\n" (s!"p cnf {F.vars} {F.clauses.length}" :: body) ++ "\n"

/-! ## The registered format, with its planted certificate -/

/-- Two unit clauses `[1]` and `[-1]`. -/
def contradiction : Cnf := ⟨1, [[1], [-1]]⟩

/-- A planted bad certificate: the empty clause with clause 1 named twice as its hints and clause 2,
the one that conflicts, left out: propagation never reaches a conflict. -/
def planted : Cert := .refutation [.add 3 [] [1, 1]]

theorem planted_refused : check 1 contradiction planted = .refused .noConflict [0] := by
  decide

/-- **The registered format**: LRAT 1 over DIMACS, CaDiCaL's text output, the checker above run as
compiled code on bytes (its theorems are the kernel's). -/
@[expose] def format : Format where
  name := "lrat"
  version := "1"
  Obj := Cnf
  Cert := Cert
  decodeObj := parseDimacs
  decodeCert := parseCert
  trust := .compiled
  regime := .semidecidable
  bad := (contradiction, planted)
  badGrade := 1
  bad_refused := ⟨_, _, planted_refused⟩

/-- The format on text, at its concrete types. -/
def checkText (r : Nat) (cnf proof : String) : Verdict (FormatClause Refusal) := format.checkBytes r cnf proof

theorem checkText_sound {r : Nat} {cnf proof : String} (h : checkText r cnf proof = .ok) :
    ∃ F c, parseDimacs cnf = .ok F ∧ parseCert proof = .ok c ∧ Unsat F :=
  format.checkBytes_sound h

end Obend.Judge.Lrat
end
