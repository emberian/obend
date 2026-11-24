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
import all Obend.Judge.Class
import all Init.Data.String.Basic
import all Init.Data.String.Defs
import all Init.Data.String.Slice
import all Init.Data.String.Extra
import all Init.Data.String.Iterate
import all Init.Data.String.Legacy
import all Init.Data.String.Lemmas
import all Init.Data.String.Search
import all Init.Data.String.ToSlice
import all Init.Data.String.TakeDrop
import all Init.Data.List.SplitOn
import Init.Data.List.Sublist

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

/-! ## $O(1)$ `Array` Clause DB & Sparse-Trail `Array Bool` Literal Table (`@[csimp]`) -/

/-- Map a literal `l` injectively to a dense index `2 * |l| + (l ≤ 0)`. -/
@[inline] def litIdx (l : Int) : Nat :=
  if 0 < l then 2 * l.natAbs else 2 * l.natAbs + 1

private theorem litIdx_inj {a b : Int} (h : litIdx a = litIdx b) : a = b := by
  unfold litIdx at h
  by_cases pa : 0 < a <;> by_cases pb : 0 < b <;> simp only [pa, pb, ↓reduceIte] at h <;> omega

/-- Maximum clause ID referenced by `.add` steps. -/
def maxStepId : List Step → Nat
  | [] => 0
  | .add id _ _ :: rest => max id (maxStepId rest)
  | .del _ :: rest => maxStepId rest

/-- Maximum `|l|` across clauses and steps (sizing the literal mark table). -/
def maxClauseVar : Clause → Nat
  | [] => 0
  | l :: ls => max l.natAbs (maxClauseVar ls)

def maxClausesVar : List Clause → Nat
  | [] => 0
  | c :: cs => max (maxClauseVar c) (maxClausesVar cs)

def maxStepsVar : List Step → Nat
  | [] => 0
  | .add _ c _ :: rest => max (maxClauseVar c) (maxStepsVar rest)
  | .del _ :: rest => maxStepsVar rest

/-- Random-access clause lookup over `Array (Option Clause)`. -/
@[inline] def lookupDbArr (dbArr : @& Array (Option Clause)) (k : Nat) : Option Clause :=
  if h : k < dbArr.size then dbArr[k]'h else none

private theorem lookupDbArr_set (arr : Array (Option Clause)) (i : Nat) (hi : i < arr.size)
    (v : Option Clause) (k : Nat) :
    lookupDbArr (arr.set i v) k = if k = i then v else lookupDbArr arr k := by
  unfold lookupDbArr
  by_cases hki : k = i
  · subst hki
    have hk' : k < (arr.set k v).size := by rw [Array.size_set]; exact hi
    simp only [hk', ↓reduceDIte, Array.getElem_set_self, ↓reduceIte]
  · by_cases hk : k < arr.size
    · have hk' : k < (arr.set i v).size := by rw [Array.size_set]; exact hk
      simp only [hk, hk', ↓reduceDIte, Array.getElem_set, Ne.symm hki, hki, ↓reduceIte]
    · have hk' : ¬(k < (arr.set i v).size) := by rw [Array.size_set]; exact hk
      simp only [hk, hk', ↓reduceDIte, hki, ↓reduceIte]

def RepresentsDb (dbArr : Array (Option Clause)) (db : Db) : Prop :=
  ∀ k : Nat, lookupDbArr dbArr k = db.lookup k

private theorem representsDb_insert {dbArr : Array (Option Clause)} {db : Db}
    (hdb : RepresentsDb dbArr db) {id : Nat} (hid : id < dbArr.size) (c : Clause) :
    RepresentsDb (dbArr.set id (some c)) ((id, c) :: db) := by
  intro k
  rw [lookupDbArr_set dbArr id hid (some c) k]
  by_cases hki : k = id
  · subst hki
    simp only [↓reduceIte, List.lookup, beq_self_eq_true]
  · simp only [hki, ↓reduceIte, List.lookup, beq_eq_false_iff_ne.mpr hki, hdb k]

private theorem lookup_filter_not_contains (db : Db) (ids : List Nat) (k : Nat) :
    (db.filter fun p => !ids.contains p.1).lookup k =
      if ids.contains k then none else db.lookup k := by
  induction db with
  | nil => cases ids.contains k <;> rfl
  | cons p rest ih =>
    obtain ⟨id, c⟩ := p
    rw [List.filter_cons]
    cases hid : ids.contains id
    · simp only [Bool.not_false, ↓reduceIte, List.lookup]
      cases hkid : k == id
      · exact ih
      · have heq : k = id := beq_iff_eq.mp hkid
        subst heq
        simp only [hid, Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih]
      cases hkid : k == id
      · simp only [List.lookup, hkid]
      · have heq : k = id := beq_iff_eq.mp hkid
        subst heq
        simp only [hid, ↓reduceIte]

def deleteDbArr (dbArr : Array (Option Clause)) : List Nat → Array (Option Clause)
  | [] => dbArr
  | id :: ids =>
    let dbArr' := if h : id < dbArr.size then dbArr.set id none else dbArr
    deleteDbArr dbArr' ids

private theorem deleteDbArr_lookup (dbArr : Array (Option Clause)) :
    ∀ (ids : List Nat) (k : Nat),
      lookupDbArr (deleteDbArr dbArr ids) k =
        if ids.contains k then none else lookupDbArr dbArr k
  | [], _ => by simp only [deleteDbArr, List.contains_nil, Bool.false_eq_true, ↓reduceIte]
  | id :: ids, k => by
    unfold deleteDbArr
    have hone : lookupDbArr (if h : id < dbArr.size then dbArr.set id none else dbArr) k =
        if k = id then none else lookupDbArr dbArr k := by
      by_cases hid : id < dbArr.size
      · simp only [hid, ↓reduceDIte, lookupDbArr_set dbArr id hid none k]
      · simp only [hid, ↓reduceDIte]
        by_cases hk : k = id
        · subst hk; simp only [↓reduceIte, lookupDbArr, hid, ↓reduceDIte]
        · simp only [hk, ↓reduceIte]
    rw [deleteDbArr_lookup _ ids k, hone, List.contains_cons]
    by_cases hkid : k == id
    · have heq : k = id := beq_iff_eq.mp hkid
      subst heq
      cases ids.contains k <;> simp only [beq_self_eq_true, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
    · have hne : k ≠ id := fun he => hkid (beq_iff_eq.mpr he)
      simp only [hkid, Bool.false_or, hne, ↓reduceIte]

private theorem representsDb_delete {dbArr : Array (Option Clause)} {db : Db}
    (hdb : RepresentsDb dbArr db) (ids : List Nat) :
    RepresentsDb (deleteDbArr dbArr ids) (db.filter fun p => !ids.contains p.1) := by
  intro k
  rw [deleteDbArr_lookup, lookup_filter_not_contains, hdb k]

def buildInitialArr : List Clause → Nat → Array (Option Clause) → Array (Option Clause)
  | [], _, arr => arr
  | c :: cs, idx, arr =>
    let arr' := if h : idx < arr.size then arr.set idx (some c) else arr
    buildInitialArr cs (idx + 1) arr'

private theorem buildInitialArr_size :
    ∀ (cs : List Clause) (idx : Nat) (arr : Array (Option Clause)),
      (buildInitialArr cs idx arr).size = arr.size
  | [], _, _ => rfl
  | c :: cs, idx, arr => by
    unfold buildInitialArr
    split
    · exact (buildInitialArr_size cs (idx + 1) _).trans (Array.size_set ..)
    · exact buildInitialArr_size cs (idx + 1) arr

private theorem range'_zip_map (cs : List Clause) :
    ∀ (a start : Nat),
      ((List.range' a cs.length).zip cs |>.map fun p => (p.1 + start, p.2)) =
        ((List.range' 0 cs.length).zip cs |>.map fun p => (p.1 + (a + start), p.2)) := by
  induction cs with
  | nil => intro _ _; rfl
  | cons d ds ih =>
    intro a start
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, Nat.zero_add]
    rw [ih (a + 1) start, ih 1 (a + start), show a + 1 + start = 1 + (a + start) by omega]

private theorem range_zip_succ (cs : List Clause) (start : Nat) :
    ((List.range cs.length).zip cs |>.map fun p => (p.1 + start, p.2)) =
      match cs with
      | [] => []
      | c :: rest => (start, c) :: ((List.range rest.length).zip rest |>.map fun p => (p.1 + (start + 1), p.2)) := by
  cases cs with
  | nil => rfl
  | cons c rest =>
    simp only [List.length_cons, List.range_eq_range', List.range'_succ, List.zip_cons_cons,
      List.map_cons, Nat.zero_add]
    rw [range'_zip_map rest 1 start, show 1 + start = start + 1 by omega]

private theorem buildInitialArr_spec :
    ∀ (cs : List Clause) (start : Nat) (arr : Array (Option Clause)),
      start + cs.length ≤ arr.size →
      (∀ k, start ≤ k → lookupDbArr arr k = none) →
      ∀ k, lookupDbArr (buildInitialArr cs start arr) k =
        if k < start then lookupDbArr arr k
        else (((List.range cs.length).zip cs |>.map fun p => (p.1 + start, p.2)).lookup k)
  | [], start, arr, _, hnone, k => by
    simp only [buildInitialArr, List.length_nil, List.range_zero, List.zip_nil_left, List.map_nil,
      List.lookup_nil]
    by_cases hk : k < start
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte, hnone k (by omega)]
  | c :: cs, start, arr, hsz, hnone, k => by
    rw [range_zip_succ (c :: cs) start]
    dsimp only
    have hst : start < arr.size := by simp only [List.length_cons] at hsz; omega
    let arr' := arr.set start (some c)
    have harr' : buildInitialArr (c :: cs) start arr = buildInitialArr cs (start + 1) arr' := by
      simp only [buildInitialArr, hst, ↓reduceDIte, arr']
    have hsz' : (start + 1) + cs.length ≤ arr'.size := by
      dsimp only [arr']; rw [Array.size_set]; simp only [List.length_cons] at hsz; omega
    have hnone' : ∀ q, start + 1 ≤ q → lookupDbArr arr' q = none := by
      intro q hq
      dsimp only [arr']
      rw [lookupDbArr_set arr start hst (some c) q]
      have hne : q ≠ start := by omega
      simp only [hne, ↓reduceIte, hnone q (by omega)]
    rw [harr', buildInitialArr_spec cs (start + 1) arr' hsz' hnone' k]
    by_cases hk_lt : k < start
    · have hk_lt1 : k < start + 1 := by omega
      have hne : k ≠ start := by omega
      simp only [hk_lt, hk_lt1, ↓reduceIte, arr', lookupDbArr_set arr start hst (some c) k, hne]
    · by_cases hk_eq : k = start
      · subst hk_eq
        have hk_lt1 : k < k + 1 := by omega
        simp only [hk_lt, hk_lt1, ↓reduceIte, arr', lookupDbArr_set arr k hst (some c) k,
          List.lookup, beq_self_eq_true]
      · have hnlt1 : ¬(k < start + 1) := by omega
        have hb : (k == start) = false := beq_eq_false_iff_ne.mpr hk_eq
        simp only [hk_lt, hnlt1, ↓reduceIte, List.lookup, hb]

def initDbArr (idBound : Nat) (F : Cnf) : Array (Option Clause) :=
  buildInitialArr F.clauses 1 (Array.replicate idBound none)

private theorem lookup_zero_map_add :
    ∀ (xs : List (Nat × Clause)) (s : Nat), 1 ≤ s →
      (xs.map fun p => (p.1 + s, p.2)).lookup 0 = none
  | [], _, _ => rfl
  | (a, c) :: xs, s, hs => by
    have hne : (0 == a + s) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [List.map_cons, List.lookup, hne]
    exact lookup_zero_map_add xs s hs

private theorem initDbArr_represents (idBound : Nat) (F : Cnf)
    (hbnd : F.clauses.length + 1 ≤ idBound) :
    RepresentsDb (initDbArr idBound F) (initial F) := by
  intro k
  unfold initDbArr initial
  have hrep_sz : 1 + F.clauses.length ≤ (Array.replicate idBound (none : Option Clause)).size := by
    rw [Array.size_replicate]; omega
  have hrep_none : ∀ q, 1 ≤ q → lookupDbArr (Array.replicate idBound (none : Option Clause)) q = none := by
    intro q _; unfold lookupDbArr; split <;> simp
  rw [buildInitialArr_spec F.clauses 1 _ hrep_sz hrep_none k]
  by_cases hk : k < 1
  · have hk0 : k = 0 := by omega
    subst hk0
    simp only [Nat.zero_lt_one, ↓reduceIte]
    have h0_rep : lookupDbArr (Array.replicate idBound (none : Option Clause)) 0 = none := by
      unfold lookupDbArr; split <;> simp
    rw [h0_rep, lookup_zero_map_add _ 1 (Nat.le_refl 1)]
  · simp only [hk, ↓reduceIte]

/-- Check literal membership in `(marks, extra)` in $O(1)$ on in-range variables. -/
@[inline] def litMarked (marks : @& Array Bool) (extra : List Int) (x : Int) : Bool :=
  let idx := litIdx x
  if h : idx < marks.size then marks[idx]'h else extra.contains x

@[inline] def falsifiedExec (marks : @& Array Bool) (extra : List Int) (l : Int) : Bool :=
  l != 0 && litMarked marks extra (-l)

/-- Mark a nonzero literal in `marks` (recording `idx` on `trail` for $O(|trail|)$ sparse reset). -/
@[inline] def markLit (marks : Array Bool) (trail : List Nat) (extra : List Int) (x : Int) :
    Array Bool × List Nat × List Int :=
  let idx := litIdx x
  if h : idx < marks.size then
    if marks[idx]'h then (marks, trail, extra)
    else (marks.set idx true, idx :: trail, extra)
  else
    (marks, trail, x :: extra)

/-- Sparse reset of `marks` along `trail` ($O(|trail|)$ in-place writes, zero array reallocation). -/
def clearTrail : Array Bool → List Nat → Array Bool
  | marks, [] => marks
  | marks, idx :: rest =>
    let marks' := if h : idx < marks.size then marks.set idx false else marks
    clearTrail marks' rest

private theorem clearTrail_size : ∀ (marks : Array Bool) (trail : List Nat),
    (clearTrail marks trail).size = marks.size
  | _, [] => rfl
  | marks, idx :: rest => by
    unfold clearTrail
    split
    · exact (clearTrail_size _ rest).trans (Array.size_set ..)
    · exact clearTrail_size marks rest

def IsClean (marks : Array Bool) : Prop :=
  ∀ j (hj : j < marks.size), marks[j]'hj = false

private theorem clearTrail_clean :
    ∀ (trail : List Nat) (marks : Array Bool),
      (∀ j (hj : j < marks.size), marks[j]'hj = true → j ∈ trail) →
      IsClean (clearTrail marks trail)
  | [], marks, htr => fun j hj =>
    Bool.eq_false_iff.mpr (fun ht => List.not_mem_nil (htr j hj ht))
  | idx :: rest, marks, htr => by
    unfold clearTrail
    by_cases hidx : idx < marks.size
    · simp only [hidx, ↓reduceDIte]
      have hsz : (marks.set idx false).size = marks.size := Array.size_set ..
      refine clearTrail_clean rest (marks.set idx false) (fun q hq ht => ?_)
      have hq' : q < marks.size := hsz ▸ hq
      simp only [Array.getElem_set] at ht
      by_cases hqi : idx = q
      · simp only [hqi, ↓reduceIte, Bool.false_eq_true] at ht
      · simp only [hqi, ↓reduceIte] at ht
        rcases List.mem_cons.mp (htr q hq' ht) with rfl | hrest
        · exact absurd rfl hqi
        · exact hrest
    · simp only [hidx, ↓reduceDIte]
      refine clearTrail_clean rest marks (fun q hq ht => ?_)
      rcases List.mem_cons.mp (htr q hq ht) with rfl | hrest
      · exact absurd hq hidx
      · exact hrest

def MarksRepresent (marks : Array Bool) (trail : List Nat) (extra : List Int) (α : List Int) : Prop :=
  (∀ j (hj : j < marks.size), marks[j]'hj = true → j ∈ trail) ∧
  ∀ x : Int, x ≠ 0 → litMarked marks extra x = α.contains x

private theorem litMarked_set (marks : Array Bool) (extra : List Int) (idx : Nat)
    (hidx : idx < marks.size) (v : Bool) (y : Int) :
    litMarked (marks.set idx v) extra y =
      if idx = litIdx y then v else litMarked marks extra y := by
  unfold litMarked
  by_cases hy : litIdx y < marks.size
  · have hy' : litIdx y < (marks.set idx v).size := by rw [Array.size_set]; exact hy
    simp only [hy, hy', ↓reduceDIte, Array.getElem_set]
  · have hy' : ¬(litIdx y < (marks.set idx v).size) := by rw [Array.size_set]; exact hy
    have hne : idx ≠ litIdx y := by omega
    simp only [hy, hy', ↓reduceDIte, hne, ↓reduceIte]

private theorem markLit_size (marks : Array Bool) (trail : List Nat) (extra : List Int) (x : Int) :
    (markLit marks trail extra x).1.size = marks.size := by
  unfold markLit
  by_cases h : litIdx x < marks.size
  · simp only [h, ↓reduceDIte]
    split <;> simp only [Array.size_set]
  · simp only [h, ↓reduceDIte]

private theorem markLit_represents {marks : Array Bool} {trail : List Nat} {extra α : List Int}
    (hrep : MarksRepresent marks trail extra α) {x : Int} (hx0 : x ≠ 0) :
    MarksRepresent (markLit marks trail extra x).1 (markLit marks trail extra x).2.1
      (markLit marks trail extra x).2.2 (x :: α) := by
  unfold markLit
  by_cases h : litIdx x < marks.size
  · simp only [h, ↓reduceDIte]
    cases hm : marks[litIdx x]'h with
    | true =>
      simp only [↓reduceIte]
      refine ⟨hrep.1, fun y hy0 => ?_⟩
      have hx_in : α.contains x = true := by
        have := hrep.2 x hx0
        simpa [litMarked, h, hm] using this.symm
      rw [hrep.2 y hy0, List.contains_cons]
      by_cases hyx : y == x
      · have heq : y = x := beq_iff_eq.mp hyx
        subst heq; simp only [hyx, Bool.true_or, hx_in]
      · simp only [hyx, Bool.false_or]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hsz : (marks.set (litIdx x) true).size = marks.size := Array.size_set ..
      refine ⟨fun j hj ht => ?_, fun y hy0 => ?_⟩
      · have hj' : j < marks.size := hsz ▸ hj
        simp only [Array.getElem_set] at ht
        by_cases hjx : litIdx x = j
        · subst hjx; exact List.mem_cons_self
        · simp only [hjx, ↓reduceIte] at ht
          exact List.mem_cons_of_mem _ (hrep.1 j hj' ht)
      · rw [litMarked_set marks extra (litIdx x) h true y, List.contains_cons]
        by_cases hyx : y == x
        · have heq : y = x := beq_iff_eq.mp hyx
          subst heq
          simp only [↓reduceIte, beq_self_eq_true, Bool.true_or]
        · have hne : y ≠ x := fun he => hyx (beq_iff_eq.mpr he)
          have hidx_ne : litIdx x ≠ litIdx y := fun hi => hne (litIdx_inj hi).symm
          simp only [hidx_ne, ↓reduceIte, hyx, Bool.false_or, hrep.2 y hy0]
  · simp only [h, ↓reduceDIte]
    refine ⟨hrep.1, fun y hy0 => ?_⟩
    unfold litMarked
    rw [List.contains_cons, List.contains_cons]
    by_cases hyx : y == x
    · have heq : y = x := beq_iff_eq.mp hyx
      subst heq
      simp only [h, ↓reduceDIte, hyx, Bool.true_or]
    · simp only [hyx, Bool.false_or]
      exact hrep.2 y hy0

private theorem falsifiedExec_eq {marks : Array Bool} {trail : List Nat} {extra α : List Int}
    (hrep : MarksRepresent marks trail extra α) (l : Int) :
    falsifiedExec marks extra l = falsified α l := by
  unfold falsifiedExec falsified
  by_cases hl0 : l = 0
  · subst hl0; rfl
  · have hneg0 : -l ≠ 0 := by omega
    have hb : (l != 0) = true := bne_iff_ne.mpr hl0
    simp [hb, hrep.2 (-l) hneg0]

/-- Zero-allocation 2-literal early-exit scanner for `d.filter (fun l => !falsified α l)`. -/
inductive ClauseScan where
  | conflict
  | unit (u : Int)
  | many

def scanClause (marks : @& Array Bool) (extra : List Int) : List Int → ClauseScan → ClauseScan
  | [], st => st
  | l :: ls, st =>
    if falsifiedExec marks extra l then
      scanClause marks extra ls st
    else
      match st with
      | .conflict => scanClause marks extra ls (.unit l)
      | .unit _ => .many
      | .many => .many

private theorem scanClause_spec {marks : Array Bool} {trail : List Nat} {extra α : List Int}
    (hrep : MarksRepresent marks trail extra α) :
    ∀ (d : List Int),
      (scanClause marks extra d .conflict =
        match d.filter (fun l => !falsified α l) with
        | [] => .conflict
        | [u] => .unit u
        | _ => .many) ∧
      (∀ u : Int, scanClause marks extra d (.unit u) =
        match d.filter (fun l => !falsified α l) with
        | [] => .unit u
        | _ => .many)
  | [] => ⟨rfl, fun _ => rfl⟩
  | l :: ls => by
    obtain ⟨ih0, ih1⟩ := scanClause_spec hrep ls
    refine ⟨?_, fun u => ?_⟩
    · simp only [scanClause, falsifiedExec_eq hrep l, List.filter_cons]
      cases falsified α l
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, ih1 l]
        cases ls.filter (fun x => !falsified α x) with
        | nil => rfl
        | cons a as => rfl
      · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, ih0]
    · simp only [scanClause, falsifiedExec_eq hrep l, List.filter_cons]
      cases falsified α l
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, ih1 u]

/-- Mark all literals of `negation c` onto `(marks, trail, extra)`. -/
def markNegation (marks : Array Bool) (trail : List Nat) (extra : List Int) :
    Clause → Array Bool × List Nat × List Int
  | [] => (marks, trail, extra)
  | l :: ls =>
    if l != 0 then
      let m1 := markLit marks trail extra (-l)
      markNegation m1.1 m1.2.1 m1.2.2 ls
    else
      markNegation marks trail extra ls

private theorem markNegation_spec :
    ∀ (c : Clause) (marks : Array Bool) (trail : List Nat) (extra α : List Int),
      MarksRepresent marks trail extra α →
      (markNegation marks trail extra c).1.size = marks.size ∧
      MarksRepresent (markNegation marks trail extra c).1
        (markNegation marks trail extra c).2.1
        (markNegation marks trail extra c).2.2
        ((negation c).reverse ++ α)
  | [], marks, trail, extra, _, hrep => ⟨rfl, hrep⟩
  | l :: ls, marks, trail, extra, α, hrep => by
    unfold markNegation negation
    by_cases hl : (l != 0) = true
    · have hl0 : l ≠ 0 := bne_iff_ne.mp hl
      have hn0 : -l ≠ 0 := by omega
      simp only [hl, ↓reduceIte, List.filter_cons, List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      obtain ⟨hsz, hrep'⟩ := markNegation_spec ls _ _ _ (-l :: α) (markLit_represents hrep hn0)
      exact ⟨hsz.trans (markLit_size ..), hrep'⟩
    · simp only [hl, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      exact markNegation_spec ls marks trail extra α hrep

private theorem contains_reverse_iff {x : Int} {xs : List Int} :
    xs.reverse.contains x = xs.contains x := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_reverse]

/-- RUP propagation over `dbArr` + `(marks, trail, extra)`, always resetting `marks` via `clearTrail`. -/
def propagateExec (dbArr : @& Array (Option Clause)) :
    Array Bool → List Nat → List Int → List Int → Array Bool × Except Refusal Unit
  | marks, trail, _, [] => (clearTrail marks trail, .error .noConflict)
  | marks, trail, extra, h :: hs =>
    if h ≤ 0 then (clearTrail marks trail, .error (.ratHint h))
    else
      match lookupDbArr dbArr h.toNat with
      | none => (clearTrail marks trail, .error (.missingHint h))
      | some d =>
        match scanClause marks extra d .conflict with
        | .conflict => (clearTrail marks trail, .ok ())
        | .unit u =>
          if u != 0 then
            let m1 := markLit marks trail extra u
            propagateExec dbArr m1.1 m1.2.1 m1.2.2 hs
          else
            -- `u == 0` never fails `!falsified α 0` (`falsified α 0 = false`), so `0 :: α` has no effect on `falsified`:
            propagateExec dbArr marks trail extra hs
        | .many => (clearTrail marks trail, .error (.notUnit h))

private theorem propagate_congr (db : Db) :
    ∀ (hs α₁ α₂ : List Int),
      (∀ x : Int, x ≠ 0 → α₁.contains x = α₂.contains x) →
      propagate db α₁ hs = propagate db α₂ hs
  | [], _, _, _ => rfl
  | h :: hs, α₁, α₂, heq => by
    unfold propagate
    split
    · rfl
    · cases db.lookup h.toNat with
      | none => rfl
      | some d =>
        have hf : (fun l => !falsified α₁ l) = (fun l => !falsified α₂ l) := by
          funext l
          unfold falsified
          by_cases hl0 : l = 0
          · subst hl0; rfl
          · simp only [bne_iff_ne.mpr hl0, Bool.true_and, heq (-l) (by omega)]
        dsimp only; rw [hf]
        cases d.filter (fun l => !falsified α₂ l) with
        | nil => rfl
        | cons u rest =>
          cases rest with
          | nil =>
            exact propagate_congr db hs (u :: α₁) (u :: α₂) fun x hx0 => by
              simp only [List.contains_cons]
              cases (x == u) <;> simp only [Bool.true_or, Bool.false_or, heq x hx0]
          | cons _ _ => rfl

private theorem propagateExec_size (dbArr : Array (Option Clause)) :
    ∀ (hints : List Int) (marks : Array Bool) (trail : List Nat) (extra : List Int),
      (propagateExec dbArr marks trail extra hints).1.size = marks.size
  | [], marks, trail, _ => clearTrail_size marks trail
  | h :: hs, marks, trail, extra => by
    unfold propagateExec
    split
    · exact clearTrail_size marks trail
    · split
      · exact clearTrail_size marks trail
      · split
        · exact clearTrail_size marks trail
        · split
          · exact (propagateExec_size dbArr hs _ _ _).trans (markLit_size ..)
          · exact propagateExec_size dbArr hs marks trail extra
        · exact clearTrail_size marks trail

private theorem propagateExec_spec {dbArr : Array (Option Clause)} {db : Db}
    (hdb : RepresentsDb dbArr db) :
    ∀ (hints : List Int) (marks : Array Bool) (trail : List Nat) (extra α : List Int),
      MarksRepresent marks trail extra α →
      IsClean (propagateExec dbArr marks trail extra hints).1 ∧
      (propagateExec dbArr marks trail extra hints).2 = propagate db α hints
  | [], marks, trail, _, _, hrep =>
    ⟨clearTrail_clean trail marks hrep.1, rfl⟩
  | h :: hs, marks, trail, extra, α, hrep => by
    unfold propagateExec propagate
    by_cases hneg : h ≤ 0
    · rw [ite_eq_left hneg, ite_eq_left hneg]
      exact ⟨clearTrail_clean trail marks hrep.1, rfl⟩
    · rw [ite_eq_right hneg, ite_eq_right hneg, hdb h.toNat]
      cases db.lookup h.toNat with
      | none => exact ⟨clearTrail_clean trail marks hrep.1, rfl⟩
      | some d =>
        dsimp only
        rw [(scanClause_spec hrep d).1]
        cases d.filter (fun l => !falsified α l) with
        | nil => exact ⟨clearTrail_clean trail marks hrep.1, rfl⟩
        | cons u rest =>
          cases rest with
          | nil =>
            dsimp only
            by_cases hu : (u != 0) = true
            · have hu0 : u ≠ 0 := bne_iff_ne.mp hu
              simp only [hu, ↓reduceIte]
              exact propagateExec_spec hdb hs _ _ _ (u :: α) (markLit_represents hrep hu0)
            · have hu0 : u = 0 := Decidable.of_not_not (fun h => hu (bne_iff_ne.mpr h))
              subst hu0
              simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
              obtain ⟨hcl, hres⟩ := propagateExec_spec hdb hs marks trail extra α hrep
              refine ⟨hcl, hres.trans ?_⟩
              exact (propagate_congr db hs (0 :: α) α fun x hx0 => by
                simp only [List.contains_cons, beq_eq_false_iff_ne.mpr hx0, Bool.false_or]).symm
          | cons _ _ => exact ⟨clearTrail_clean trail marks hrep.1, rfl⟩

/-- Run LRAT steps over `Array (Option Clause)` + reusable `Array Bool` literal marks. -/
def runExec (dbArr : Array (Option Clause)) (marks : Array Bool) :
    List Step → Nat → Except (Refusal × Nat) Unit
  | [], i => .error (.noEmptyClause, i)
  | .del ids :: rest, i => runExec (deleteDbArr dbArr ids) marks rest (i + 1)
  | .add id c hints :: rest, i =>
    let m0 := markNegation marks [] [] c
    let step := propagateExec dbArr m0.1 m0.2.1 m0.2.2 hints
    match step.2 with
    | .error e => .error (e, i)
    | .ok () =>
      if c.isEmpty then .ok ()
      else
        let dbArr' := if h : id < dbArr.size then dbArr.set id (some c) else dbArr
        runExec dbArr' step.1 rest (i + 1)

private theorem steps_lt_succ_maxStepId :
    ∀ {steps : List Step} {id : Nat} {c : Clause} {hs : List Int} {bound : Nat},
      maxStepId steps < bound → Step.add id c hs ∈ steps → id < bound
  | [], _, _, _, _, _, hm => nomatch hm
  | .add id' c' hs' :: rest, id, c, hs, bound, hb, hm => by
    simp only [maxStepId] at hb
    rcases List.mem_cons.mp hm with heq | htl
    · injection heq with hid _ _; omega
    · exact steps_lt_succ_maxStepId (by omega) htl
  | .del _ :: rest, id, c, hs, bound, hb, hm => by
    simp only [maxStepId] at hb
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq
    · exact steps_lt_succ_maxStepId hb htl

private theorem runExec_eq :
    ∀ (steps : List Step) (dbArr : Array (Option Clause)) (db : Db) (marks : Array Bool) (i : Nat),
      RepresentsDb dbArr db →
      IsClean marks →
      (∀ id c hs, Step.add id c hs ∈ steps → id < dbArr.size) →
      runExec dbArr marks steps i = run db steps i
  | [], _, _, _, _, _, _, _ => rfl
  | .del ids :: rest, dbArr, db, marks, i, hdb, hclean, hbnd => by
    have hsz : (deleteDbArr dbArr ids).size = dbArr.size := by
      clear hdb hbnd
      induction ids generalizing dbArr with
      | nil => rfl
      | cons id tl ih =>
        unfold deleteDbArr
        split
        · exact (ih _).trans (Array.size_set ..)
        · exact ih dbArr
    exact runExec_eq rest (deleteDbArr dbArr ids) _ marks (i + 1)
      (representsDb_delete hdb ids) hclean
      (fun id c hs hm => hsz.symm ▸ hbnd id c hs (List.mem_cons_of_mem _ hm))
  | .add id c hints :: rest, dbArr, db, marks, i, hdb, hclean, hbnd => by
    have hrep0 : MarksRepresent marks [] [] [] := by
      refine ⟨(fun j hj ht => by rw [hclean j hj] at ht; cases ht), fun x _ => ?_⟩
      unfold litMarked
      by_cases hx : litIdx x < marks.size
      · simp only [hx, ↓reduceDIte, hclean _ hx, List.contains_nil]
      · simp only [hx, ↓reduceDIte, List.contains_nil]
    obtain ⟨_, hrep_neg⟩ := markNegation_spec c marks [] [] [] hrep0
    rw [List.append_nil] at hrep_neg
    obtain ⟨hclean', hres⟩ := propagateExec_spec hdb hints _ _ _ (negation c).reverse hrep_neg
    have hres' : (propagateExec dbArr (markNegation marks [] [] c).1
        (markNegation marks [] [] c).2.1 (markNegation marks [] [] c).2.2 hints).2 =
        propagate db (negation c) hints :=
      hres.trans (propagate_congr db hints (negation c).reverse (negation c) fun _ _ =>
        contains_reverse_iff)
    unfold runExec run
    dsimp only
    rw [hres']
    cases propagate db (negation c) hints with
    | error _ => rfl
    | ok u =>
      cases u
      by_cases he : c.isEmpty
      · simp only [he, ↓reduceIte]
      · have hid : id < dbArr.size := hbnd id c hints List.mem_cons_self
        simp only [he, Bool.false_eq_true, ↓reduceIte, hid, ↓reduceDIte]
        have hdb' := representsDb_insert hdb hid c
        have hbnd' : ∀ id' c' hs', Step.add id' c' hs' ∈ rest → id' < (dbArr.set id (some c)).size := by
          intro id' c' hs' hm
          rw [Array.size_set]
          exact hbnd id' c' hs' (List.mem_cons_of_mem _ hm)
        exact runExec_eq rest (dbArr.set id (some c)) ((id, c) :: db) _ (i + 1) hdb' hclean' hbnd'

/-- Single-pass $O(|lits|)$ model consistency builder (`none` iff `0 ∈ lits` or `l, -l ∈ lits`). -/
def buildModelMarks (marks : Array Bool) (extra : List Int) :
    List Int → Option (Array Bool × List Int)
  | [] => some (marks, extra)
  | l :: ls =>
    if l == 0 || litMarked marks extra (-l) then none
    else
      let m1 := markLit marks [] extra l
      buildModelMarks m1.1 m1.2.2 ls

private theorem markLit_lookup (marks : Array Bool) (extra : List Int)
    (l x : Int) :
    litMarked (markLit marks [] extra l).1 (markLit marks [] extra l).2.2 x =
      (x == l || litMarked marks extra x) := by
  unfold markLit
  by_cases hl : litIdx l < marks.size
  · simp only [hl, ↓reduceDIte]
    cases hm : marks[litIdx l]'hl with
    | true =>
      simp only [↓reduceIte]
      by_cases hxl : x == l
      · have heq : x = l := beq_iff_eq.mp hxl
        subst heq; simp only [hxl, Bool.true_or, litMarked, hl, ↓reduceDIte, hm]
      · simp only [hxl, Bool.false_or]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, litMarked_set marks extra (litIdx l) hl true x]
      by_cases hxl : x == l
      · have heq : x = l := beq_iff_eq.mp hxl
        subst heq; simp only [↓reduceIte, beq_self_eq_true, Bool.true_or]
      · have hne : x ≠ l := fun he => hxl (beq_iff_eq.mpr he)
        have hidx_ne : litIdx l ≠ litIdx x := fun hi => hne (litIdx_inj hi).symm
        simp only [hidx_ne, ↓reduceIte, hxl, Bool.false_or]
  · simp only [hl, ↓reduceDIte, litMarked, List.contains_cons]
    by_cases hxl : x == l
    · have heq : x = l := beq_iff_eq.mp hxl
      subst heq; simp only [hl, ↓reduceDIte, hxl, Bool.true_or]
    · simp only [hxl, Bool.false_or]

private theorem buildModelMarks_spec :
    ∀ (rem seen : List Int) (marks : Array Bool) (extra : List Int),
      (∀ s ∈ seen, s ≠ 0 ∧ -s ∉ seen) →
      (∀ x : Int, x ≠ 0 → litMarked marks extra x = seen.contains x) →
      match buildModelMarks marks extra rem with
      | some (marks', extra') =>
        (∀ l ∈ rem ++ seen, l ≠ 0 ∧ -l ∉ (rem ++ seen)) ∧
        (∀ x : Int, x ≠ 0 → litMarked marks' extra' x = (rem ++ seen).contains x)
      | none =>
        ¬(∀ l ∈ rem ++ seen, l ≠ 0 ∧ -l ∉ (rem ++ seen))
  | [], seen, marks, extra, hseen, hlook => by
    simp only [buildModelMarks, List.nil_append]
    exact ⟨hseen, hlook⟩
  | l :: ls, seen, marks, extra, hseen, hlook => by
    unfold buildModelMarks
    by_cases hbad : (l == 0 || litMarked marks extra (-l)) = true
    · simp only [hbad, ↓reduceIte]
      intro hall
      rw [Bool.or_eq_true] at hbad
      rcases hbad with hl0 | hneg
      · exact (hall l (List.mem_append_left _ List.mem_cons_self)).1 (beq_iff_eq.mp hl0)
      · have hl_ne : l ≠ 0 := (hall l (List.mem_append_left _ List.mem_cons_self)).1
        have hn_ne : -l ≠ 0 := by omega
        rw [hlook (-l) hn_ne, List.contains_iff_mem] at hneg
        exact (hall l (List.mem_append_left _ List.mem_cons_self)).2 (List.mem_append_right _ hneg)
    · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
      have hl_ne : l ≠ 0 := fun he => hbad (by simp only [he, beq_self_eq_true, Bool.true_or])
      have hn_ne : -l ≠ 0 := by omega
      have hn_not_seen : -l ∉ seen := fun hm => by
        have hc : litMarked marks extra (-l) = true := by
          rw [hlook (-l) hn_ne, List.contains_iff_mem]
          exact hm
        exact hbad (by simp only [hc, Bool.or_true])
      have hseen' : ∀ s ∈ l :: seen, s ≠ 0 ∧ -s ∉ l :: seen := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs'
        · refine ⟨hl_ne, ?_⟩
          rw [List.mem_cons, not_or]
          exact ⟨by omega, hn_not_seen⟩
        · refine ⟨(hseen s hs').1, ?_⟩
          rw [List.mem_cons, not_or]
          refine ⟨fun heq => ?_, (hseen s hs').2⟩
          have hsl : s = -l := by omega
          exact hn_not_seen (hsl ▸ hs')
      have hlook' : ∀ x : Int, x ≠ 0 →
          litMarked (markLit marks [] extra l).1 (markLit marks [] extra l).2.2 x =
            (l :: seen).contains x := by
        intro x hx0
        rw [markLit_lookup marks extra l x, hlook x hx0, List.contains_cons]
      have ih := buildModelMarks_spec ls (l :: seen) _ _ hseen' hlook'
      have hperm : ∀ x : Int, (x ∈ (l :: ls) ++ seen ↔ x ∈ ls ++ (l :: seen)) := by
        intro x; simp only [List.mem_append, List.mem_cons, or_assoc, or_left_comm]
      cases hbm : buildModelMarks (markLit marks [] extra l).1 (markLit marks [] extra l).2.2 ls with
      | none =>
        rw [hbm] at ih
        intro hall
        apply ih
        intro z hz
        have hz' := (hperm z).mpr hz
        exact ⟨(hall z hz').1, fun hnz => (hall z hz').2 ((hperm (-z)).mpr hnz)⟩
      | some me =>
        rw [hbm] at ih
        obtain ⟨ih_ok, ih_lk⟩ := ih
        refine ⟨fun z hz => ?_, fun x hx0 => ?_⟩
        · have hz' := (hperm z).mp hz
          exact ⟨(ih_ok z hz').1, fun hnz => (ih_ok z hz').2 ((hperm (-z)).mp hnz)⟩
        · rw [ih_lk x hx0]
          apply Bool.eq_iff_iff.mpr
          simp only [List.contains_iff_mem, hperm]

def firstUnsatExec (marks : @& Array Bool) (extra : List Int) : List Clause → Nat → Option Nat
  | [], _ => none
  | c :: cs, idx =>
    if c.any (fun l => l != 0 && litMarked marks extra l) then
      firstUnsatExec marks extra cs (idx + 1)
    else some idx

private theorem firstUnsatExec_eq {lits : List Int} (hlits0 : ∀ x ∈ lits, x ≠ 0)
    {marks : Array Bool} {extra : List Int}
    (hlook : ∀ x : Int, x ≠ 0 → litMarked marks extra x = lits.contains x) :
    ∀ (cs : List Clause) (start : Nat),
      firstUnsatExec marks extra cs (start + 1) =
        (((List.range cs.length).zip cs).findSome? fun p =>
          if p.2.any lits.contains then none else some (p.1 + start + 1))
  | [], _ => rfl
  | c :: cs, start => by
    unfold firstUnsatExec
    have hany : c.any (fun l => l != 0 && litMarked marks extra l) = c.any lits.contains := by
      apply List.any_congr rfl
      intro l
      by_cases hl0 : l = 0
      · subst hl0
        simp only [bne_self_eq_false, Bool.false_and]
        symm; apply Bool.eq_false_iff.mpr
        intro hc0; exact hlits0 0 (List.contains_iff_mem.mp hc0) rfl
      · simp only [bne_iff_ne.mpr hl0, Bool.true_and, hlook l hl0]
    rw [hany, List.length_cons, List.range_eq_range', List.range'_succ, List.zip_cons_cons,
      List.findSome?_cons]
    simp only [Nat.zero_add]
    cases c.any lits.contains with
    | false => rfl
    | true =>
      rw [firstUnsatExec_eq hlits0 hlook cs (start + 1)]
      have hshift :
          List.findSome? (fun p : Nat × Clause => if p.2.any lits.contains then none else some (p.1 + (start + 1) + 1))
            ((List.range cs.length).zip cs) =
          List.findSome? (fun p : Nat × Clause => if p.2.any lits.contains then none else some (p.1 + start + 1))
            ((List.range' 1 cs.length).zip cs) := by
        clear hany
        have : ∀ (k : Nat) (xs : List Clause),
            List.findSome? (fun p : Nat × Clause => if p.2.any lits.contains then none else some (p.1 + (start + 1) + 1))
              ((List.range' k xs.length).zip xs) =
            List.findSome? (fun p : Nat × Clause => if p.2.any lits.contains then none else some (p.1 + start + 1))
              ((List.range' (k + 1) xs.length).zip xs) := by
          intro k xs
          induction xs generalizing k with
          | nil => rfl
          | cons y ys ihy =>
            simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.findSome?_cons]
            cases y.any lits.contains
            · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; omega
            · simp only [↓reduceIte]; exact ihy (k + 1)
        rw [List.range_eq_range']
        exact this 0 cs
      exact hshift

/-- Linear-time LRAT + model verifier (`O(|F| + |proof|)` on dense DIMACS/LRAT formulas). -/
def checkExec (r : Nat) (F : Cnf) : Cert → Verdict Refusal
  | .refutation steps =>
    if steps.length ≤ r then
      let idBound := max F.clauses.length (maxStepId steps) + 1
      let vBound := max F.vars (max (maxClausesVar F.clauses) (maxStepsVar steps))
      let cap := 16 * (F.clauses.length + steps.length + 1) + 2048
      if idBound ≤ cap then
        let markCap := min (2 * vBound + 2) cap
        let dbArr := initDbArr idBound F
        let marks := Array.replicate markCap false
        match runExec dbArr marks steps 0 with
        | .ok () => .ok
        | .error (e, i) => .refused e [i]
      else
        match run (initial F) steps 0 with
        | .ok () => .ok
        | .error (e, i) => .refused e [i]
    else .uncovered
  | .model lits =>
    let vBound := max F.vars (maxClauseVar lits)
    let markCap := min (2 * vBound + 2) (16 * (F.clauses.length + lits.length + 1) + 2048)
    match buildModelMarks (Array.replicate markCap false) [] lits with
    | none => .refused (.notAModel 0) []
    | some (marks, extra) =>
      match firstUnsatExec marks extra F.clauses 1 with
      | none => .refused .satisfiable []
      | some i => .refused (.notAModel i) [i]

@[csimp] theorem check_eq_exec : @check = @checkExec := by
  funext r F cert
  cases cert with
  | refutation steps =>
    unfold check checkExec
    dsimp only
    by_cases hle : steps.length ≤ r
    · simp only [hle, ↓reduceIte]
      by_cases hd : max F.clauses.length (maxStepId steps) + 1 ≤
          16 * (F.clauses.length + steps.length + 1) + 2048
      · simp only [hd, ↓reduceIte]
        let idBound := max F.clauses.length (maxStepId steps) + 1
        let vBound := max F.vars (max (maxClausesVar F.clauses) (maxStepsVar steps))
        let cap := 16 * (F.clauses.length + steps.length + 1) + 2048
        have hinit : RepresentsDb (initDbArr idBound F) (initial F) :=
          initDbArr_represents idBound F (by dsimp only [idBound]; omega)
        have hclean : IsClean (Array.replicate (min (2 * vBound + 2) cap) false) :=
          fun _ _ => Array.getElem_replicate ..
        have hbnd : ∀ id c hs, Step.add id c hs ∈ steps → id < (initDbArr idBound F).size := by
          intro id c hs hm
          unfold initDbArr
          rw [buildInitialArr_size, Array.size_replicate]
          exact steps_lt_succ_maxStepId (by dsimp only [idBound]; omega) hm
        rw [runExec_eq steps _ (initial F) _ 0 hinit hclean hbnd]
      · simp only [hd, ↓reduceIte]
    · simp only [hle, ↓reduceIte]
  | model lits =>
    unfold check checkExec
    dsimp only
    let vBound := max F.vars (maxClauseVar lits)
    let markCap := min (2 * vBound + 2) (16 * (F.clauses.length + lits.length + 1) + 2048)
    have hlook0 : ∀ x : Int, x ≠ 0 →
        litMarked (Array.replicate markCap false) [] x = ([] : List Int).contains x := by
      intro x _
      unfold litMarked
      by_cases hx : litIdx x < (Array.replicate markCap false).size
      · simp only [hx, ↓reduceDIte, Array.getElem_replicate, List.contains_nil]
      · simp only [hx, ↓reduceDIte, List.contains_nil]
    have hspec := buildModelMarks_spec lits [] (Array.replicate markCap false) []
      (fun _ h => nomatch h) hlook0
    rw [List.append_nil] at hspec
    have hall_iff : lits.all (fun l => l != 0 && !lits.contains (-l)) = true ↔
        (∀ l ∈ lits, l ≠ 0 ∧ -l ∉ lits) := by
      simp only [List.all_eq_true, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true',
        Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
    cases hbm : buildModelMarks (Array.replicate markCap false) [] lits with
    | none =>
      rw [hbm] at hspec
      have hfalse : lits.all (fun l => l != 0 && !lits.contains (-l)) = false :=
        Bool.eq_false_iff.mpr (fun ht => hspec (hall_iff.mp ht))
      rw [hfalse]
      rfl
    | some me =>
      obtain ⟨marks, extra⟩ := me
      rw [hbm] at hspec
      obtain ⟨hok, hlk⟩ := hspec
      have htrue : lits.all (fun l => l != 0 && !lits.contains (-l)) = true :=
        hall_iff.mpr hok
      simp only [htrue, ↓reduceIte]
      have hfu := firstUnsatExec_eq (fun x hx => (hok x hx).1) hlk F.clauses 0
      simp only [Nat.zero_add] at hfu
      unfold firstUnsat
      rw [← hfu]

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
def format : Format where
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

private theorem propagate_and_run_inhabited :
    ∃ (db : Db) (c : Clause) (hints : List Int) (steps : List Step),
      0 < db.length ∧ 0 < steps.length ∧
      propagate db (negation c) hints = .ok () ∧
      run db steps 0 = .ok () ∧
      check 2 ⟨2, [[1], [-1, 2], [-2]]⟩ (.refutation steps) = .ok :=
  ⟨[(1, [1]), (2, [-1, 2]), (3, [-2])], [2], [1, 2],
    [.add 4 [2] [1, 2], .add 5 [] [4, 3]],
    by decide, by decide, rfl, rfl, rfl⟩

private theorem splitOnP_nil_cbv {α : Type} (p : α → Bool) :
    List.splitOnP p [] = [[]] := List.splitOnP_nil

private theorem splitOnP_cons_cbv {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    List.splitOnP p (x :: xs) =
      if p x then [] :: List.splitOnP p xs
      else match List.splitOnP p xs with
        | [] => [[x]]
        | h :: t => (x :: h) :: t := by
  rw [List.splitOnP_cons_eq_ite_modifyHead]
  split
  · rfl
  · cases h : List.splitOnP p xs with
    | nil => exact absurd h (List.splitOnP_ne_nil p xs)
    | cons a as => rfl

private theorem split_toString_eq (s : String) (p : Char → Bool) :
    (s.split p).toList.map (·.toString) = (s.toList.splitOnP p).map String.ofList := by
  have h := String.toList_split_bool (s := s) (p := p)
  simpa [String.Slice.toString_eq] using h

private theorem startsWith_cbv (s p : String) :
    s.startsWith p = decide (p.toList <+: s.toList) := by
  apply Bool.eq_iff_iff.mpr
  simp only [String.startsWith_string_iff, decide_eq_true_eq]

private theorem foldl_cbv {α : Type} (f : α → Char → α) (init : α) (s : String) :
    s.foldl f init = s.toList.foldl f init :=
  String.foldl_eq_foldl_toList

private theorem tokens_eq (line : String) :
    tokens line = ((line.toList.splitOnP fun c => c == ' ' || c == '\t' || c == '\r').map String.ofList).filter (· ≠ "") := by
  unfold tokens
  rw [split_toString_eq]

private theorem parseCert_eq (text : String) :
    parseCert text =
      if (((text.toList.splitOnP (· == '\n')).map String.ofList).any fun l => (tokens l).head? == some "v")
      then parseModel text else parseLrat text := by
  unfold parseCert
  have h : ((text.split (· == '\n')).toList.any fun l => (tokens l.toString).head? == some "v") =
      (((text.split (· == '\n')).toList.map (·.toString)).any fun l => (tokens l).head? == some "v") := by
    rw [List.any_map]; rfl
  rw [h, split_toString_eq]

attribute [local cbv_eval] splitOnP_nil_cbv splitOnP_cons_cbv split_toString_eq startsWith_cbv
  foldl_cbv tokens_eq parseCert_eq

set_option maxRecDepth 50000 in
private theorem checkText_inhabited :
    ∃ (r : Nat) (cnf proof : String),
      0 < r ∧ checkText r cnf proof = .ok := by
  refine ⟨2, "p cnf 2 3\n1 0\n-1 2 0\n-2 0\n", "4 2 0 1 2 0\n5 0 4 3 0\n", by decide, ?_⟩
  have hDimacs : parseDimacs "p cnf 2 3\n1 0\n-1 2 0\n-2 0\n" = .ok ⟨2, [[1], [-1, 2], [-2]]⟩ := by
    unfold parseDimacs
    rw [split_toString_eq]
    set_option cbv.maxSteps 500000 in
    cbv
  have hCert : parseCert "4 2 0 1 2 0\n5 0 4 3 0\n" =
      .ok (.refutation [.add 4 [2] [1, 2], .add 5 [] [4, 3]]) := by
    rw [parseCert_eq]
    have hLrat : parseLrat "4 2 0 1 2 0\n5 0 4 3 0\n" =
        .ok (.refutation [.add 4 [2] [1, 2], .add 5 [] [4, 3]]) := by
      unfold parseLrat
      rw [split_toString_eq]
      set_option cbv.maxSteps 500000 in
      cbv
    rw [hLrat]
    set_option cbv.maxSteps 500000 in
    cbv
  unfold checkText Judge.Format.checkBytes format
  simp only [hDimacs, hCert]
  rfl

end Obend.Judge.Lrat
end
