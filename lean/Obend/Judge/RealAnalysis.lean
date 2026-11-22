module
/-
# Obend.Judge.RealAnalysis — Certified Interval Arithmetic & Polynomial SOS Judges

Provides:
- `judge_mono_probe_dichotomy`: Proves that `Judge.mono` separates non-refuting certificate
  diagnostics from unbounded grade-indexed counterexample probes (`Judge.deepen`).
- `intervalJudge`: Verifies numerical interval bounds against `RealExpr` evaluations (`IntervalQuery.SemanticMeaning`),
  with fuel-driven rational grid/midpoint subdivision auto-refutation on `.counterexample []`.
- `sosJudge`: Verifies polynomial Sum-of-Squares (SOS) non-negativity certificates and Putinar/Gröbner
  identities under multiplicative Graded Lexicographic (`grlex`) order (`grlex_mul_compatible`), paired
  with multi-dimensional rational lattice + quadratic-vertex counterexample refutation on `sosSearchProbe`.
-/
public import Obend.Judge.Class
import all Obend.Judge.Class
public import Obend.Analysis.RealAnalysis
import all Obend.Analysis.RealAnalysis

public section
namespace Obend.Judge
open Obend.Analysis
open Obend.Analysis.CanonicalRat
set_option autoImplicit false

/-- **Monotonicity Dichotomy (`judge_mono_probe_dichotomy`)**:
If `(o, c)` settles at grade `0` to a non-refuting certificate diagnostic (`J.refutes k₀ = false`),
`Judge.mono` forces `J.check r o c` to return that identical diagnostic at every `r ≥ 0`; unbounded
grade-indexed counterexample search therefore uses probe certificates returning `.uncovered` until hit. -/
theorem judge_mono_probe_dichotomy {Obj Cert : Type} [J : Judge Obj Cert]
    (o : Obj) (c : Cert) (k₀ k₁ : J.Clause) (p₀ p₁ : List Nat) (r : Nat)
    (hDiag : J.check 0 o c = .refused k₀ p₀) (hNonRef : J.refutes k₀ = false) (hRef : J.refutes k₁ = true) :
    J.check r o c ≠ .refused k₁ p₁ := by
  have hEq := J.mono (Nat.zero_le r) (by rw [hDiag]; exact fun h => nomatch h)
  rw [hDiag] at hEq; intro hContr; rw [hEq] at hContr; injection hContr with hk _
  subst hk; rw [hNonRef] at hRef; cases hRef

/-! ## Certified Interval Judge (`interval@1`) -/

structure IntervalQuery where
  expr : RealExpr
  env : List (String × Interval)
  claimedBound : Interval
  deriving DecidableEq, Repr

inductive IntervalCert where
  | direct
  | counterexample (point : List (String × CanonicalRat))
  deriving DecidableEq, Repr

inductive IntervalClause where
  | boundViolated (computed claimed : Interval)
  | domainUndefined
  | refutationWitness (point : List (String × CanonicalRat))
  deriving DecidableEq, Repr

def pointAssignment (pt : List (String × CanonicalRat)) (v : String) : CanonicalRat :=
  match pt.find? (·.1 == v) with | some (_, x) => x | none => 0

def entryInDomain (pt : List (String × CanonicalRat)) (entry : String × Interval) : Bool :=
  match pt.find? (·.1 == entry.1) with | some (_, x) => entry.2.containsRat x | none => false

def dedupEnvAux (seen : List String) : List (String × Interval) → List (String × Interval)
  | [] => []
  | (v, iv) :: rest => if seen.any (· == v) then dedupEnvAux seen rest else (v, iv) :: dedupEnvAux (v :: seen) rest

def validIntervalWitness (q : IntervalQuery) (pt : List (String × CanonicalRat)) : Bool :=
  (dedupEnvAux [] q.env).all (entryInDomain pt) &&
  decide (evalExpr (pointAssignment pt) q.expr < q.claimedBound.lo ∨ q.claimedBound.hi < evalExpr (pointAssignment pt) q.expr)

def subdivideIntervalPoints (iv : Interval) (shell : Nat) : List CanonicalRat :=
  if decide (iv.lo ≤ iv.hi) then
    let n := shell + 1
    let step := (iv.hi - iv.lo) / ((n : Nat) : CanonicalRat)
    if shell == 0 then [iv.lo, iv.hi, (iv.lo + iv.hi) / 2]
    else (List.range (n + 1)).map fun k => iv.lo + ((k : Nat) : CanonicalRat) * step
  else []

def intervalEnvGridAtShell (shell : Nat) : List (String × Interval) → List (List (String × CanonicalRat))
  | [] => [[]]
  | (v, iv) :: rest =>
    (subdivideIntervalPoints iv shell).flatMap fun x => (intervalEnvGridAtShell shell rest).map ((v, x) :: ·)

def findIntervalCounterexampleAtShell (shell : Nat) (q : IntervalQuery) : Option (List (String × CanonicalRat)) :=
  (intervalEnvGridAtShell shell (dedupEnvAux [] q.env)).find? (validIntervalWitness q)

def findIntervalCounterexample (fuel : Nat) (q : IntervalQuery) : Option (List (String × CanonicalRat)) :=
  Judge.deepen (fun shell => findIntervalCounterexampleAtShell shell q) fuel

@[expose] def intervalCheck (fuel : Nat) (q : IntervalQuery) (c : IntervalCert) : Judge.Verdict IntervalClause :=
  match c with
  | .direct =>
    match evalInterval q.env q.expr with
    | some comp =>
      if decide (q.claimedBound.lo ≤ comp.lo ∧ comp.hi ≤ q.claimedBound.hi) then .ok
      else .refused (.boundViolated comp q.claimedBound) []
    | none => .refused .domainUndefined []
  | .counterexample [] =>
    if validIntervalWitness q [] then .refused (.refutationWitness []) []
    else match findIntervalCounterexample fuel q with
      | some w => .refused (.refutationWitness w) [] | none => .uncovered
  | .counterexample (hd :: tl) =>
    if validIntervalWitness q (hd :: tl) then .refused (.refutationWitness (hd :: tl)) [] else .uncovered

abbrev IntervalQuery.SemanticMeaning (q : IntervalQuery) : Prop :=
  ∀ (rho : String → CanonicalRat), (∀ v iv, q.env.lookup v = some iv → rho v ∈ iv) → evalExpr rho q.expr ∈ q.claimedBound

private theorem list_find?_some_prop_iv {α : Type} (p : α → Bool) : ∀ {xs : List α} {w : α}, xs.find? p = some w → p w = true
  | [], _, h => nomatch h
  | hd :: _, _, h => by
    simp only [List.find?] at h
    cases hhd : p hd with
    | true => rw [hhd] at h; injection h with hEq; subst hEq; exact hhd
    | false => rw [hhd] at h; exact list_find?_some_prop_iv p h

private theorem list_find?_exists_of_mem_iv {α : Type} (p : α → Bool) (xs : List α) {x : α} (hx : x ∈ xs) (hp : p x = true) :
    ∃ w, xs.find? p = some w ∧ p w = true := by
  induction xs with
  | nil => nomatch hx
  | cons hd _ ih =>
    simp only [List.find?]
    cases hhd : p hd with
    | true => exact ⟨hd, rfl, hhd⟩
    | false => rcases List.mem_cons.mp hx with rfl | htl; · rw [hp] at hhd; cases hhd
               · exact ih htl

theorem findIntervalCounterexampleAtShell_sound {shell : Nat} {q : IntervalQuery} {pt : List (String × CanonicalRat)}
    (h : findIntervalCounterexampleAtShell shell q = some pt) : validIntervalWitness q pt = true :=
  list_find?_some_prop_iv (validIntervalWitness q) h

theorem findIntervalCounterexample_sound {fuel : Nat} {q : IntervalQuery} {pt : List (String × CanonicalRat)}
    (h : findIntervalCounterexample fuel q = some pt) : validIntervalWitness q pt = true := by
  obtain ⟨_, _, hi⟩ := Judge.deepen_some _ h; exact findIntervalCounterexampleAtShell_sound hi

private theorem findIntervalCounterexample_inhabited :
    ∃ w1 w2, findIntervalCounterexampleAtShell 0 ⟨.sqr (.var "x"), [("x", ⟨0, 2⟩)], ⟨0, 1⟩⟩ = some w1 ∧
      findIntervalCounterexample 0 ⟨.sqr (.var "x"), [("x", ⟨0, 2⟩)], ⟨0, 1⟩⟩ = some w2 :=
  ⟨[("x", 2)], [("x", 2)], by decide +kernel, by decide +kernel⟩

theorem intervalCheck_sound (fuel : Nat) (q : IntervalQuery) (c : IntervalCert)
    (h : intervalCheck fuel q c = .ok) : IntervalQuery.SemanticMeaning q := by
  intro rho hEnv; unfold intervalCheck at h
  cases c with
  | direct =>
    dsimp only at h
    cases hEval : evalInterval q.env q.expr with
    | none => rw [hEval] at h; contradiction
    | some comp =>
      rw [hEval] at h; dsimp only at h; split at h
      · have hMem := evalInterval_sound q.env rho hEnv q.expr comp hEval
        rw [Interval.mem_iff] at hMem ⊢; grind
      · contradiction
  | counterexample pt =>
    cases pt with
    | nil => dsimp only at h; split at h; · contradiction
             · split at h <;> contradiction
    | cons _ _ => dsimp only at h; split at h <;> contradiction

inductive VarBoundInEnv (name : String) (iv : Interval) : List (String × Interval) → Prop where
  | head {rest} : VarBoundInEnv name iv ((name, iv) :: rest)
  | tail {k value rest} : k ≠ name → VarBoundInEnv name iv rest → VarBoundInEnv name iv ((k, value) :: rest)

private theorem varBound_iff_lookup {name iv env} : VarBoundInEnv name iv env ↔ env.lookup name = some iv := by
  constructor
  · intro h; induction h with
    | head => simp
    | tail hne _ ih => simpa [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm hne)] using ih
  · induction env with
    | nil => simp
    | cons hd tl ih =>
      obtain ⟨k, val⟩ := hd
      by_cases hk : k = name
      · subst k; simpa using fun h : val = iv => h ▸ VarBoundInEnv.head (rest := tl)
      · intro h; exact .tail hk (ih (by simpa [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm hk)] using h))

inductive ExprIntervalBounds (env : List (String × Interval)) : RealExpr → Interval → Prop where
  | const (x) : ExprIntervalBounds env (.const x) (.ofPoint x)
  | var {v I} : VarBoundInEnv v I env → ExprIntervalBounds env (.var v) I
  | add {l r A B} : ExprIntervalBounds env l A → ExprIntervalBounds env r B → ExprIntervalBounds env (.add l r) (.add A B)
  | sub {l r A B} : ExprIntervalBounds env l A → ExprIntervalBounds env r B → ExprIntervalBounds env (.sub l r) (.sub A B)
  | mul {l r A B} : ExprIntervalBounds env l A → ExprIntervalBounds env r B → ExprIntervalBounds env (.mul l r) (.mul A B)
  | sqr {e A} : ExprIntervalBounds env e A → ExprIntervalBounds env (.sqr e) (.sqr A)

theorem exprIntervalBounds_iff_evalInterval {env e I} : ExprIntervalBounds env e I ↔ evalInterval env e = some I := by
  constructor
  · intro h; induction h <;> simp_all [evalInterval, varBound_iff_lookup]
  · induction e generalizing I with
    | const x => rintro h; cases h; exact .const x
    | var v => intro h; exact .var (varBound_iff_lookup.mpr (by simpa [evalInterval] using h))
    | add _ _ il ir | sub _ _ il ir | mul _ _ il ir =>
      simp only [evalInterval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
      rintro ⟨A, ha, B, hb, rfl⟩; constructor <;> first | exact il ha | exact ir hb
    | sqr _ ih =>
      simp only [evalInterval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
      rintro ⟨A, ha, rfl⟩; exact .sqr (ih ha)

def DeclarativeIntervalEnclosed (q : IntervalQuery) : Prop :=
  ∃ B, ExprIntervalBounds q.env q.expr B ∧ q.claimedBound.lo ≤ B.lo ∧ B.hi ≤ q.claimedBound.hi

theorem declarativeIntervalEnclosed_iff_intervalCheck_ok (q : IntervalQuery) :
    DeclarativeIntervalEnclosed q ↔ ∃ c r, intervalCheck r q c = .ok := by
  constructor
  · rintro ⟨B, deriv, lo, hi⟩; exact ⟨.direct, 0, by simp [intervalCheck, exprIntervalBounds_iff_evalInterval.mp deriv, lo, hi]⟩
  · rintro ⟨c, _, ok⟩
    cases c with
    | direct =>
      cases he : evalInterval q.env q.expr with
      | none => simp [intervalCheck, he] at ok
      | some B => exact ⟨B, exprIntervalBounds_iff_evalInterval.mpr he, by simpa [intervalCheck, he, apply_ite] using ok⟩
    | counterexample pt =>
      cases pt with
      | nil => simp only [intervalCheck] at ok; split at ok; · contradiction
               · split at ok <;> contradiction
      | cons _ _ => simp only [intervalCheck] at ok; split at ok <;> contradiction

private theorem any_beq_iff_mem (seen : List String) (v : String) :
    seen.any (· == v) = true ↔ v ∈ seen := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨s, hs, hEq⟩ => (beq_iff_eq.mp hEq) ▸ hs, fun hv => ⟨v, hv, beq_self_eq_true v⟩⟩

private theorem lookup_mem_dedupEnvAux :
    ∀ (seen : List String) (env : List (String × Interval)) (v : String) (iv : Interval),
      v ∉ seen → env.lookup v = some iv → (v, iv) ∈ dedupEnvAux seen env
  | _, [], _, _, _, h => nomatch h
  | seen, (k, b) :: rest, v, iv, hNotSeen, hLook => by
    simp only [List.lookup] at hLook
    by_cases hvk : v == k
    · have hvEq : v = k := beq_iff_eq.mp hvk; subst hvEq
      simp only [beq_self_eq_true, Option.some.injEq] at hLook; subst hLook
      have hAny : seen.any (· == v) = false :=
        Bool.eq_false_iff.mpr (fun hT => hNotSeen ((any_beq_iff_mem seen v).mp hT))
      simp [dedupEnvAux, hAny]
    · simp only [hvk] at hLook; unfold dedupEnvAux
      split
      · exact lookup_mem_dedupEnvAux seen rest v iv hNotSeen hLook
      · apply List.Mem.tail
        refine lookup_mem_dedupEnvAux (k :: seen) rest v iv (fun hm => ?_) hLook
        rcases List.mem_cons.mp hm with rfl | hS
        · simp at hvk
        · exact hNotSeen hS

private theorem fst_not_mem_of_mem_dedupEnvAux :
    ∀ {seen : List String} {env : List (String × Interval)} {p : String × Interval},
      p ∈ dedupEnvAux seen env → p.1 ∉ seen
  | _, [], _, h => nomatch h
  | seen, (k, _) :: rest, p, h => by
    unfold dedupEnvAux at h; split at h
    · exact fst_not_mem_of_mem_dedupEnvAux h
    · rename_i hkNot; rcases List.mem_cons.mp h with rfl | hRest
      · exact fun hm => hkNot ((any_beq_iff_mem seen k).mpr hm)
      · exact fun hs => fst_not_mem_of_mem_dedupEnvAux hRest (List.Mem.tail k hs)

private theorem lookup_of_mem_dedupEnvAux :
    ∀ {seen : List String} {env : List (String × Interval)} {v : String} {iv : Interval},
      (v, iv) ∈ dedupEnvAux seen env → env.lookup v = some iv
  | _, [], _, _, h => nomatch h
  | seen, (k, _) :: rest, v, iv, h => by
    unfold dedupEnvAux at h; split at h
    · rename_i hkIn
      have hkMem := (any_beq_iff_mem seen k).mp hkIn
      have hvk : (v == k) = false := beq_false_of_ne (fun heq => fst_not_mem_of_mem_dedupEnvAux h (heq ▸ hkMem))
      simpa [List.lookup, hvk] using lookup_of_mem_dedupEnvAux h
    · rcases List.mem_cons.mp h with hEq | hRest
      · injection hEq with hv hb; subst hv hb; simp [List.lookup]
      · have hvk : (v == k) = false :=
          beq_false_of_ne (fun heq => fst_not_mem_of_mem_dedupEnvAux hRest (heq ▸ List.Mem.head seen))
        simpa [List.lookup, hvk] using lookup_of_mem_dedupEnvAux hRest

theorem validIntervalWitness_refutes {q : IntervalQuery} {pt : List (String × CanonicalRat)}
    (hValid : validIntervalWitness q pt = true) :
    ¬ IntervalQuery.SemanticMeaning q := by
  unfold validIntervalWitness at hValid
  rcases (Bool.and_eq_true _ _).mp hValid with ⟨domain, outsideB⟩
  have outside := of_decide_eq_true outsideB
  intro meaning
  have inside := meaning (pointAssignment pt) (by
    intro v iv hv
    have hm : (v, iv) ∈ dedupEnvAux [] q.env := lookup_mem_dedupEnvAux [] q.env v iv (fun h => nomatch h) hv
    have valid := List.all_eq_true.mp domain (v, iv) hm
    unfold entryInDomain at valid; unfold pointAssignment
    cases hp : pt.find? (·.1 == v) with
    | none => simp [hp] at valid
    | some pair => exact (Interval.containsRat_iff_mem _ _).mp (by simpa [hp] using valid))
  rw [Interval.mem_iff] at inside; grind

/-- Every `.refutationWitness pt` emitted by `intervalCheck` satisfies `validIntervalWitness q pt = true`. -/
theorem intervalCheck_refutation_witness {r q c pt path}
    (h : intervalCheck r q c = .refused (.refutationWitness pt) path) :
    path = [] ∧ (dedupEnvAux [] q.env).all (entryInDomain pt) = true ∧
      (evalExpr (pointAssignment pt) q.expr < q.claimedBound.lo ∨
       q.claimedBound.hi < evalExpr (pointAssignment pt) q.expr) := by
  have hVW : path = [] ∧ validIntervalWitness q pt = true := by
    cases c with
    | direct => simp only [intervalCheck] at h; split at h <;> (try split at h) <;> cases h
    | counterexample cand =>
      cases cand with
      | nil =>
        simp only [intervalCheck] at h
        by_cases hE : validIntervalWitness q [] = true
        · simp only [hE, ↓reduceIte] at h
          injection h with hCl hPath; injection hCl with hPt; subst hPt; exact ⟨hPath.symm, hE⟩
        · simp only [hE, Bool.false_eq_true, ↓reduceIte] at h
          cases hw : findIntervalCounterexample r q with
          | none => rw [hw] at h; cases h
          | some w =>
            rw [hw] at h; injection h with hCl hPath; injection hCl with hPt; subst hPt
            exact ⟨hPath.symm, findIntervalCounterexample_sound hw⟩
      | cons hd tl =>
        simp only [intervalCheck] at h
        by_cases hC : validIntervalWitness q (hd :: tl) = true
        · simp only [hC, ↓reduceIte] at h
          injection h with hCl hPath; injection hCl with hPt; subst hPt; exact ⟨hPath.symm, hC⟩
        · simp [hC] at h
  obtain ⟨hPath, hV⟩ := hVW; unfold validIntervalWitness at hV
  rcases (Bool.and_eq_true _ _).mp hV with ⟨hDom, hOut⟩
  exact ⟨hPath, hDom, of_decide_eq_true hOut⟩

theorem intervalCheck_refuted {r q c pt path}
    (h : intervalCheck r q c = .refused (.refutationWitness pt) path) :
    ¬ IntervalQuery.SemanticMeaning q := by
  obtain ⟨_, hDom, hOut⟩ := intervalCheck_refutation_witness h
  exact validIntervalWitness_refutes ((Bool.and_eq_true _ _).mpr ⟨hDom, decide_eq_true hOut⟩)

theorem intervalCheck_mono {r r' : Nat} {q : IntervalQuery} {c : IntervalCert}
    (le : r ≤ r') (hne : intervalCheck r q c ≠ .uncovered) :
    intervalCheck r' q c = intervalCheck r q c := by
  cases c with
  | direct => rfl
  | counterexample cand =>
    cases cand with
    | cons hd tl => rfl
    | nil =>
      unfold intervalCheck at hne ⊢
      dsimp only at hne ⊢
      split
      · rfl
      · rename_i hNotEmpty
        simp only [hNotEmpty, Bool.false_eq_true, ↓reduceIte] at hne
        cases hw : findIntervalCounterexample r q with
        | none => rw [hw] at hne; exact False.elim (hne rfl)
        | some w =>
          have hw' : findIntervalCounterexample r' q = some w := Judge.deepen_mono _ hw le
          simp only [hw']

theorem mem_subdivideIntervalPoints {iv : Interval} {shell k : Nat}
    (hLe : iv.lo ≤ iv.hi) (hShell : 1 ≤ shell) (hk : k ≤ shell + 1) :
    iv.lo + ((k : Nat) : CanonicalRat) * ((iv.hi - iv.lo) / ((shell + 1 : Nat) : CanonicalRat)) ∈
      subdivideIntervalPoints iv shell := by
  unfold subdivideIntervalPoints
  have hNe0 : (shell == 0) = false := beq_false_of_ne (by omega)
  simp only [decide_eq_true hLe, ↓reduceIte, hNe0, Bool.false_eq_true]
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩

private theorem map_rho_mem_grid (shell : Nat) (rho : String → CanonicalRat) :
    ∀ (xs : List (String × Interval)),
      (∀ p ∈ xs, rho p.1 ∈ subdivideIntervalPoints p.2 shell) →
      xs.map (fun p => (p.1, rho p.1)) ∈ intervalEnvGridAtShell shell xs
  | [], _ => List.Mem.head []
  | (v, iv) :: rest, hPts => by
    simp only [List.map_cons, intervalEnvGridAtShell, List.mem_flatMap, List.mem_map]
    exact ⟨rho v, hPts (v, iv) (List.Mem.head rest), rest.map (fun p => (p.1, rho p.1)),
      map_rho_mem_grid shell rho rest (fun p hp => hPts p (List.Mem.tail _ hp)), rfl⟩

private theorem find?_map_rho_some (rho : String → CanonicalRat) (w : String) :
    ∀ {xs : List (String × Interval)}, (∃ iv, (w, iv) ∈ xs) →
      (xs.map (fun p => (p.1, rho p.1))).find? (·.1 == w) = some (w, rho w)
  | [], ⟨_, h⟩ => nomatch h
  | (k, _) :: rest, ⟨iv, hMem⟩ => by
    simp only [List.map_cons, List.find?]
    by_cases hkw : k == w
    · have hk : k = w := beq_iff_eq.mp hkw; subst hk; simp
    · simp only [hkw]; rcases List.mem_cons.mp hMem with hEq | hRest
      · injection hEq with hk _; subst hk; simp at hkw
      · exact find?_map_rho_some rho w ⟨iv, hRest⟩

private theorem find?_map_rho_none (rho : String → CanonicalRat) (w : String) :
    ∀ {xs : List (String × Interval)}, (∀ iv, (w, iv) ∉ xs) →
      (xs.map (fun p => (p.1, rho p.1))).find? (·.1 == w) = none
  | [], _ => rfl
  | (k, b) :: rest, hNot => by
    have hkw : (k == w) = false := beq_false_of_ne (fun h => hNot b (h ▸ List.Mem.head rest))
    simpa [List.find?, hkw] using find?_map_rho_none rho w (fun iv hm => hNot iv (List.Mem.tail _ hm))

theorem intervalCheck_grid_complete (q : IntervalQuery) (shell : Nat)
    (pt : List (String × CanonicalRat))
    (hMem : pt ∈ intervalEnvGridAtShell shell (dedupEnvAux [] q.env))
    (hValid : validIntervalWitness q pt = true) :
    ∃ w, intervalCheck shell q (.counterexample []) = .refused (.refutationWitness w) [] ∧
         validIntervalWitness q w = true ∧
         ¬ IntervalQuery.SemanticMeaning q := by
  by_cases hE : validIntervalWitness q [] = true
  · refine ⟨[], ?_, hE, validIntervalWitness_refutes hE⟩; unfold intervalCheck; simp [hE]
  · obtain ⟨w0, hw0, _⟩ := list_find?_exists_of_mem_iv (validIntervalWitness q) _ hMem hValid
    obtain ⟨w, hwDeep⟩ := Judge.deepen_isSome (fun s => findIntervalCounterexampleAtShell s q) hw0
    change findIntervalCounterexample shell q = some w at hwDeep
    have hwValid := findIntervalCounterexample_sound hwDeep
    refine ⟨w, ?_, hwValid, validIntervalWitness_refutes hwValid⟩
    unfold intervalCheck; simp [hE, hwDeep]

/-- **Rational Subdivision Counterexample Completeness (`intervalCheck_subdivision_complete`)**:
For any `q : IntervalQuery`, resolution `1 ≤ shell`, and rational variable assignment `rho`
enclosed by `q.env` whose active coordinates lie on the `(shell + 1)`-subdivision grid and whose
evaluation violates `q.claimedBound`, `intervalCheck shell q (.counterexample [])` automatically
discovers a concrete counterexample witness `w` and refutes `IntervalQuery.SemanticMeaning q`. -/
theorem intervalCheck_subdivision_complete (q : IntervalQuery) (shell : Nat)
    (hShell : 1 ≤ shell) (rho : String → CanonicalRat)
    (hBox : ∀ v iv, q.env.lookup v = some iv → rho v ∈ iv)
    (hGrid : ∀ v iv, q.env.lookup v = some iv →
      ∃ k ≤ shell + 1,
        rho v = iv.lo + ((k : Nat) : CanonicalRat) * ((iv.hi - iv.lo) / ((shell + 1 : Nat) : CanonicalRat)))
    (hUnbound : ∀ v, q.env.lookup v = none → rho v = 0)
    (hViol : evalExpr rho q.expr < q.claimedBound.lo ∨ q.claimedBound.hi < evalExpr rho q.expr) :
    ∃ w, intervalCheck shell q (.counterexample []) = .refused (.refutationWitness w) [] ∧
         validIntervalWitness q w = true ∧
         ¬ IntervalQuery.SemanticMeaning q := by
  let env' := dedupEnvAux [] q.env
  let pt := env'.map (fun p => (p.1, rho p.1))
  have hMem : pt ∈ intervalEnvGridAtShell shell env' := by
    apply map_rho_mem_grid shell rho env'
    intro ⟨v, iv⟩ hp
    have hLook := lookup_of_mem_dedupEnvAux hp
    have hInIv := hBox v iv hLook; rw [Interval.mem_iff] at hInIv
    obtain ⟨k, hkLe, hkEq⟩ := hGrid v iv hLook
    rw [hkEq]; exact mem_subdivideIntervalPoints (by grind) hShell hkLe
  have hAssign : pointAssignment pt = rho := by
    funext w; unfold pointAssignment
    cases hLook : q.env.lookup w with
    | some iv =>
      have hm := lookup_mem_dedupEnvAux [] q.env w iv (fun h => nomatch h) hLook
      rw [find?_map_rho_some rho w ⟨iv, hm⟩]
    | none =>
      have hNone : ∀ iv, (w, iv) ∉ env' := fun iv hm => by
        rw [lookup_of_mem_dedupEnvAux hm] at hLook; cases hLook
      rw [find?_map_rho_none rho w hNone, hUnbound w hLook]
  have hDom : env'.all (entryInDomain pt) = true := by
    rw [List.all_eq_true]; intro ⟨v, iv⟩ hp
    unfold entryInDomain; rw [find?_map_rho_some rho v ⟨iv, hp⟩]
    exact (Interval.containsRat_iff_mem _ _).mpr (hBox v iv (lookup_of_mem_dedupEnvAux hp))
  have hValid : validIntervalWitness q pt = true := by
    unfold validIntervalWitness; rw [hAssign]; exact (Bool.and_eq_true _ _).mpr ⟨hDom, decide_eq_true hViol⟩
  exact intervalCheck_grid_complete q shell pt hMem hValid

instance intervalJudge : Judge IntervalQuery IntervalCert where
  Clause := IntervalClause
  Meaning q _c := IntervalQuery.SemanticMeaning q
  check := intervalCheck
  sound := by intro r q c h; exact intervalCheck_sound r q c h
  refutes
    | .refutationWitness _ => true
    | _ => false
  refuted := by
    intro r q c k path refused _ _
    cases k <;> first | contradiction | exact intervalCheck_refuted refused
  Fragment := DeclarativeIntervalEnclosed
  complete := fun h _ => (declarativeIntervalEnclosed_iff_intervalCheck_ok _).mp h
  mono := fun le hne => intervalCheck_mono le hne

theorem intervalJudge_refutes_iff (k : IntervalClause) :
    intervalJudge.refutes k = true ↔ ∃ pt, k = .refutationWitness pt := by
  cases k with
  | refutationWitness pt => exact ⟨fun _ => ⟨pt, rfl⟩, fun _ => rfl⟩
  | boundViolated _ _ | domainUndefined => exact ⟨(fun h => nomatch h), (fun ⟨_, h⟩ => nomatch h)⟩

example :
    let qSq : IntervalQuery := ⟨.sqr (.var "x"), [("x", ⟨0, 2⟩)], ⟨0, 1⟩⟩
    let qShadow : IntervalQuery := ⟨.var "x", [("x", ⟨0, 2⟩), ("x", ⟨5, 6⟩)], ⟨0, 1⟩⟩
    let qInt : IntervalQuery := ⟨.mul (.var "x") (.sub (.const 2) (.var "x")), [("x", ⟨0, 2⟩)], ⟨-1, CanonicalRat.mk 1 2⟩⟩
    let qSpike : IntervalQuery :=
      ⟨.sub (.const 1) (.mul (.const 36) (.sqr (.sub (.var "x") (.const (CanonicalRat.mk 1 3))))),
       [("x", ⟨0, 1⟩)], ⟨-100, 0⟩⟩
    intervalJudge.check 0 ⟨.var "x", [("x", ⟨0, 2⟩)], ⟨0, 2⟩⟩ .direct = .ok ∧
    intervalCheck 0 qSq (.counterexample []) = .refused (.refutationWitness [("x", 2)]) [] ∧
    intervalCheck 0 qShadow (.counterexample []) = .refused (.refutationWitness [("x", 2)]) [] ∧
    intervalCheck 0 qInt (.counterexample []) = .refused (.refutationWitness [("x", 1)]) [] ∧
    intervalCheck 0 qSpike (.counterexample []) = .uncovered ∧
    intervalCheck 1 qSpike (.counterexample []) = .uncovered ∧
    intervalCheck 2 qSpike (.counterexample []) = .refused (.refutationWitness [("x", CanonicalRat.mk 1 3)]) [] ∧
    intervalCheck 5 qSpike (.counterexample []) = .refused (.refutationWitness [("x", CanonicalRat.mk 1 3)]) [] :=
  ⟨rfl, by decide +kernel⟩

/-! ## Polynomial Sum-of-Squares (SOS) Judge (`sos@1`) & Multiplicative Graded-Lex (`grlex`) Order -/

namespace SOS

abbrev Monomial := List (Nat × Nat)

/-- Total degree $\sum_{(v, d) \in m} d$ of a monomial $m$. -/
abbrev monoTotalDeg (m : Monomial) : Nat := m.foldr (fun power degree => power.2 + degree) 0

@[simp] theorem monoTotalDeg_nil : monoTotalDeg [] = 0 := rfl
@[simp] theorem monoTotalDeg_cons (v d : Nat) (rest : Monomial) :
    monoTotalDeg ((v, d) :: rest) = d + monoTotalDeg rest := rfl

/-- Multiply a canonical monomial by $x_v^d$, dropping zero-exponent factors (`d == 0`). -/
@[expose] def mulVarPow (v d : Nat) : Monomial → Monomial
  | [] => if d == 0 then [] else [(v, d)]
  | (v2, d2) :: r2 =>
    if d == 0 then (v2, d2) :: r2
    else if v < v2 then (v, d) :: (v2, d2) :: r2
    else if v2 < v then (v2, d2) :: mulVarPow v d r2
    else (v, d + d2) :: r2

/-- Multiply two monomials `m1` and `m2`. -/
@[expose] def Monomial.mul : Monomial → Monomial → Monomial
  | [], m2 => m2
  | (v1, d1) :: r1, m2 => mulVarPow v1 d1 (Monomial.mul r1 m2)

/-- Normalize an arbitrary `Monomial` list into canonical strictly-increasing-variable, positive-exponent form. -/
abbrev monoNormalize (m : Monomial) : Monomial := Monomial.mul m []
abbrev Monomial.normalize : Monomial → Monomial := monoNormalize

def monoAllPos : Monomial → Bool
  | [] => true
  | (_, d) :: rest => decide (0 < d) && monoAllPos rest

/-- Reverse-lexicographic tie-breaker on normalized monomials of equal total degree. -/
@[expose] def monoRevLexLt : Monomial → Monomial → Bool
  | [], _ => false
  | _ :: _, [] => true
  | (v1, d1) :: r1, (v2, d2) :: r2 =>
    if v1 < v2 then true
    else if v2 < v1 then false
    else if d2 < d1 then true
    else if d1 < d2 then false
    else monoRevLexLt r1 r2

/-- **Graded Lexicographic (`grlex`) Monomial Order**. -/
@[expose] def Monomial.grlexLt (m1 m2 : Monomial) : Bool :=
  let deg1 := monoTotalDeg m1
  let deg2 := monoTotalDeg m2
  if deg1 < deg2 then true
  else if deg2 < deg1 then false
  else monoRevLexLt (monoNormalize m1) (monoNormalize m2)

abbrev Monomial.lt : Monomial → Monomial → Bool := Monomial.grlexLt

theorem monoTotalDeg_mulVarPow (v d : Nat) (m : Monomial) :
    monoTotalDeg (mulVarPow v d m) = d + monoTotalDeg m := by
  induction m with
  | nil => simp only [mulVarPow]; by_cases hd0 : d == 0; · have h0 := beq_iff_eq.mp hd0; subst h0; rfl
           · simp [hd0]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩; simp only [mulVarPow]
    by_cases hd0 : d == 0
    · have h0 := beq_iff_eq.mp hd0; subst h0; simp
    · simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1]
      · by_cases h2 : v2 < v <;> simp only [h1, h2, ↓reduceIte, monoTotalDeg_cons, ih] <;> omega

theorem monoTotalDeg_mul (m1 m2 : Monomial) :
    monoTotalDeg (Monomial.mul m1 m2) = monoTotalDeg m1 + monoTotalDeg m2 := by
  induction m1 with
  | nil => simp [Monomial.mul]
  | cons hd tl ih => rcases hd with ⟨v1, d1⟩; simp only [Monomial.mul, monoTotalDeg_mulVarPow, ih, monoTotalDeg_cons]; omega

theorem mulVarPow_zero (v : Nat) (m : Monomial) : mulVarPow v 0 m = m := by cases m <;> rfl

theorem mulVarPow_add (v d1 d2 : Nat) (m : Monomial) :
    mulVarPow v d1 (mulVarPow v d2 m) = mulVarPow v (d1 + d2) m := by
  induction m with
  | nil => grind [mulVarPow]
  | cons hd tl _ => rcases hd with ⟨v0, d0⟩; grind [mulVarPow]

theorem mulVarPow_comm (v1 d1 v2 d2 : Nat) (m : Monomial) :
    mulVarPow v1 d1 (mulVarPow v2 d2 m) = mulVarPow v2 d2 (mulVarPow v1 d1 m) := by
  induction m with
  | nil => grind [mulVarPow]
  | cons hd tl _ => rcases hd with ⟨v0, d0⟩; grind [mulVarPow]

theorem monoMul_mulVarPow (m1 : Monomial) (v d : Nat) (m2 : Monomial) :
    Monomial.mul m1 (mulVarPow v d m2) = mulVarPow v d (Monomial.mul m1 m2) := by
  induction m1 with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨v1, d1⟩; simp only [Monomial.mul, ih, mulVarPow_comm]

theorem monoNormalize_mulVarPow (v d : Nat) (m : Monomial) :
    monoNormalize (mulVarPow v d m) = mulVarPow v d (monoNormalize m) := by
  unfold monoNormalize
  induction m with
  | nil =>
    by_cases hd0 : d == 0
    · have h0 := beq_iff_eq.mp hd0; subst h0; rfl
    · simp [mulVarPow, hd0, Monomial.mul]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩
    by_cases hd0 : d == 0
    · have h0 := beq_iff_eq.mp hd0; subst h0; simp [mulVarPow_zero]
    · simp only [mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1, Monomial.mul]
      · by_cases h2 : v2 < v
        · simp only [h1, h2, ↓reduceIte, Monomial.mul]; rw [ih, mulVarPow_comm]
        · have hv : v = v2 := by omega
          subst hv; simp only [h1, ↓reduceIte, Monomial.mul]; rw [mulVarPow_add]

theorem monoNormalize_mul (m1 m2 : Monomial) :
    monoNormalize (Monomial.mul m1 m2) = Monomial.mul m1 (monoNormalize m2) := by
  induction m1 with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨v1, d1⟩; simp only [Monomial.mul, monoNormalize_mulVarPow, ih]

theorem monoMul_comm_nil (m1 m2 : Monomial) :
    Monomial.mul m1 (monoNormalize m2) = Monomial.mul m2 (monoNormalize m1) := by
  unfold monoNormalize
  induction m1 with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨v, d⟩; simp only [Monomial.mul, monoMul_mulVarPow, ih]

theorem monoNormalize_mul_comm (m1 m2 : Monomial) :
    monoNormalize (Monomial.mul m1 m2) = monoNormalize (Monomial.mul m2 m1) := by
  rw [monoNormalize_mul m1 m2, monoMul_comm_nil m1 m2, ← monoNormalize_mul m2 m1]

theorem monoAllPos_mulVarPow (v d : Nat) (m : Monomial) (hm : monoAllPos m = true) :
    monoAllPos (mulVarPow v d m) = true := by
  induction m with
  | nil =>
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · simp [hd0, monoAllPos]
    · have hd_pos : 0 < d := by cases d with | zero => contradiction | succ _ => omega
      simp [hd0, monoAllPos, hd_pos]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩
    simp only [monoAllPos, Bool.and_eq_true, decide_eq_true_eq] at hm
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · simp [hd0, monoAllPos, hm.1, hm.2]
    · have hd_pos : 0 < d := by cases d with | zero => contradiction | succ _ => omega
      simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1, monoAllPos, hd_pos, hm.1, hm.2]
      · by_cases h2 : v2 < v
        · simp [h1, h2, monoAllPos, hm.1, ih hm.2]
        · simp [h1, h2, monoAllPos, show 0 < d + d2 by omega, hm.2]

theorem monoAllPos_mul (m1 m2 : Monomial) (hm2 : monoAllPos m2 = true) :
    monoAllPos (Monomial.mul m1 m2) = true := by
  induction m1 with
  | nil => exact hm2
  | cons hd _ ih => exact monoAllPos_mulVarPow hd.1 hd.2 _ ih

theorem monoAllPos_monoNormalize (m : Monomial) : monoAllPos (monoNormalize m) = true :=
  monoAllPos_mul m [] rfl

@[simp] theorem monoRevLexLt_cons_same (v d : Nat) (r1 r2 : Monomial) :
    monoRevLexLt ((v, d) :: r1) ((v, d) :: r2) = monoRevLexLt r1 r2 := by simp [monoRevLexLt]

theorem monoRevLexLt_mulVarPow (v d : Nat) (m1 m2 : Monomial)
    (hm1 : monoAllPos m1 = true) (h : monoRevLexLt m1 m2 = true) :
    monoRevLexLt (mulVarPow v d m1) (mulVarPow v d m2) = true := by
  induction m1 generalizing m2 with
  | nil => cases m2 <;> simp [monoRevLexLt] at h
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨v1, d1⟩
    simp only [monoAllPos, Bool.and_eq_true, decide_eq_true_eq] at hm1
    cases m2 with
    | nil =>
      by_cases hd0 : d == 0
      · simp [mulVarPow, hd0, monoRevLexLt]
      · simp only [mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : v < v1
        · simp [h1, monoRevLexLt]
        · by_cases h2 : v1 < v
          · simp [h1, h2, monoRevLexLt]
          · have hvEq : v = v1 := (by omega); subst hvEq; simp [monoRevLexLt, show d < d + d1 by omega]
    | cons hd2 tl2 =>
      rcases hd2 with ⟨v2, d2⟩
      by_cases hd0 : d == 0
      · simp [mulVarPow, hd0, h]
      · simp only [mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
        by_cases hv12 : v1 < v2
        · by_cases hv_v1 : v < v1
          · simp [hv_v1, Nat.lt_trans hv_v1 hv12, h]
          · by_cases hv1_v : v1 < v
            · by_cases hv_v2 : v < v2
              · simp [hv_v1, hv1_v, hv_v2, monoRevLexLt]
              · by_cases hv2_v : v2 < v <;> simp [hv_v1, hv1_v, hv_v2, hv2_v, monoRevLexLt, hv12]
            · have hvEq : v = v1 := (by omega); subst hvEq; simp [hv12, monoRevLexLt, show d < d + d1 by omega]
        · have h' := h; simp only [monoRevLexLt] at h'
          by_cases hv21 : v2 < v1
          · simp [hv12, hv21] at h'
          · have hvEq : v1 = v2 := (by omega); subst hvEq
            simp only [Nat.lt_irrefl, ↓reduceIte] at h'
            by_cases hv_v1 : v < v1
            · simp [hv_v1, h]
            · by_cases hv1_v : v1 < v
              · simp only [hv_v1, hv1_v, ↓reduceIte, monoRevLexLt, Nat.lt_irrefl]
                by_cases hd21 : d2 < d1
                · simp [hd21]
                · by_cases hd12 : d1 < d2
                  · simp [hd21, hd12] at h'
                  · simp only [hd21, hd12, ↓reduceIte] at h' ⊢; exact ih tl2 hm1.2 h'
              · have hvEq : v = v1 := (by omega); subst hvEq
                simp only [Nat.lt_irrefl, ↓reduceIte, monoRevLexLt]
                by_cases hd21 : d2 < d1
                · simp [show d + d2 < d + d1 by omega]
                · by_cases hd12 : d1 < d2
                  · simp [hd21, hd12] at h'
                  · have hdEq : d1 = d2 := (by omega); subst hdEq; simpa only [Nat.lt_irrefl, ↓reduceIte] using h'

theorem monoRevLexLt_mul_left (m m1 m2 : Monomial)
    (hm1 : monoAllPos m1 = true) (h : monoRevLexLt m1 m2 = true) :
    monoRevLexLt (Monomial.mul m m1) (Monomial.mul m m2) = true := by
  induction m with
  | nil => exact h
  | cons hd tl ih => exact monoRevLexLt_mulVarPow hd.1 hd.2 _ _ (monoAllPos_mul tl m1 hm1) ih

/-- Left-multiplication compatibility for `Monomial.grlexLt`. -/
theorem grlex_mul_left_compatible (m m1 m2 : Monomial)
    (h : Monomial.grlexLt m1 m2 = true) :
    Monomial.grlexLt (Monomial.mul m m1) (Monomial.mul m m2) = true := by
  unfold Monomial.grlexLt at h ⊢
  rw [monoTotalDeg_mul, monoTotalDeg_mul]
  by_cases hdeg1 : monoTotalDeg m1 < monoTotalDeg m2
  · simp [show monoTotalDeg m + monoTotalDeg m1 < monoTotalDeg m + monoTotalDeg m2 by omega]
  · by_cases hdeg2 : monoTotalDeg m2 < monoTotalDeg m1
    · simp [hdeg1, hdeg2] at h
    · simp only [hdeg1, hdeg2, ↓reduceIte] at h
      simp only [show ¬(monoTotalDeg m + monoTotalDeg m1 < monoTotalDeg m + monoTotalDeg m2) by omega,
        show ¬(monoTotalDeg m + monoTotalDeg m2 < monoTotalDeg m + monoTotalDeg m1) by omega, ↓reduceIte]
      rw [monoNormalize_mul m m1, monoNormalize_mul m m2]
      exact monoRevLexLt_mul_left m (monoNormalize m1) (monoNormalize m2) (monoAllPos_monoNormalize m1) h

/-- **Theorem (`grlex_mul_compatible`)**: `Monomial.grlexLt` is strictly compatible with right multiplication. -/
theorem grlex_mul_compatible (m1 m2 m : Monomial)
    (h : Monomial.grlexLt m1 m2 = true) :
    Monomial.grlexLt (Monomial.mul m1 m) (Monomial.mul m2 m) = true := by
  unfold Monomial.grlexLt
  rw [monoTotalDeg_mul, monoTotalDeg_mul, monoNormalize_mul_comm m1 m, monoNormalize_mul_comm m2 m]
  have hL := grlex_mul_left_compatible m m1 m2 h
  unfold Monomial.grlexLt at hL
  rw [monoTotalDeg_mul, monoTotalDeg_mul] at hL
  simpa only [Nat.add_comm] using hL

@[expose] def insertNormalizedTerm (m : Monomial) (c : CanonicalRat) :
    List (Monomial × CanonicalRat) → List (Monomial × CanonicalRat)
  | [] => if c == 0 then [] else [(m, c)]
  | (m', c') :: rest =>
    let mNorm' := Monomial.normalize m'
    if m == mNorm' then
      let c_new := c + c'
      if c_new == 0 then rest else (m, c_new) :: rest
    else if Monomial.lt m mNorm' then
      if c == 0 then (mNorm', c') :: rest else (m, c) :: (mNorm', c') :: rest
    else (mNorm', c') :: insertNormalizedTerm m c rest

abbrev insertTerm (m : Monomial) (c : CanonicalRat)
    (ts : List (Monomial × CanonicalRat)) : List (Monomial × CanonicalRat) :=
  insertNormalizedTerm (Monomial.normalize m) c ts

structure Poly where
  terms : List (Monomial × CanonicalRat)
  deriving Repr

instance instDecidableEqPoly : DecidableEq Poly
  | ⟨xs⟩, ⟨ys⟩ => decidable_of_iff (xs = ys) ⟨congrArg Poly.mk, congrArg Poly.terms⟩

abbrev SparsePoly := Poly

/-! ### Independent Polynomial Ring Evaluation Semantics (`Monomial.eval`, `Poly.eval`, `SparsePoly.eval`) -/

@[expose] def ratPow (b : CanonicalRat) : Nat → CanonicalRat
  | 0 => 1
  | n + 1 => b * ratPow b n

theorem ratPow_add (b : CanonicalRat) (d1 d2 : Nat) :
    ratPow b (d1 + d2) = ratPow b d1 * ratPow b d2 := by
  induction d1 with
  | zero => simp [ratPow]
  | succ _ ih => simp only [Nat.succ_add, ratPow, ih]; grind

@[expose] def Monomial.eval (ρ : Nat → CanonicalRat) : Monomial → CanonicalRat
  | [] => 1
  | (v, d) :: rest => ratPow (ρ v) d * Monomial.eval ρ rest

theorem eval_mulVarPow (ρ : Nat → CanonicalRat) (v d : Nat) (m : Monomial) :
    Monomial.eval ρ (mulVarPow v d m) = ratPow (ρ v) d * Monomial.eval ρ m := by
  induction m with
  | nil =>
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · have h0 := beq_iff_eq.mp hd0; subst h0; simp [Monomial.eval, ratPow]
    · simp [hd0, Monomial.eval]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩; simp only [mulVarPow]
    by_cases hd0 : d == 0
    · have h0 := beq_iff_eq.mp hd0; subst h0; simp [Monomial.eval, ratPow]
    · simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1, Monomial.eval]
      · by_cases h2 : v2 < v
        · simp only [h1, h2, ↓reduceIte, Monomial.eval, ih]; grind
        · have hvEq : v = v2 := (by omega); subst hvEq; simp only [h1, ↓reduceIte, Monomial.eval]; rw [ratPow_add]; grind

theorem Monomial.eval_mul (ρ : Nat → CanonicalRat) (m1 m2 : Monomial) :
    Monomial.eval ρ (Monomial.mul m1 m2) = Monomial.eval ρ m1 * Monomial.eval ρ m2 := by
  induction m1 with
  | nil => simp [Monomial.mul, Monomial.eval]
  | cons hd _ ih => simp only [Monomial.mul, eval_mulVarPow, ih, Monomial.eval]; grind

@[simp] theorem Monomial.eval_normalize (ρ : Nat → CanonicalRat) (m : Monomial) :
    Monomial.eval ρ (monoNormalize m) = Monomial.eval ρ m := by
  unfold monoNormalize; rw [Monomial.eval_mul]; simp [Monomial.eval]

@[expose] def evalTerms (ρ : Nat → CanonicalRat) : List (Monomial × CanonicalRat) → CanonicalRat
  | [] => 0
  | (m, c) :: rest => c * Monomial.eval ρ m + evalTerms ρ rest

theorem evalTerms_insertNormalizedTerm (ρ : Nat → CanonicalRat) (m : Monomial) (c : CanonicalRat)
    (ts : List (Monomial × CanonicalRat)) :
    evalTerms ρ (insertNormalizedTerm m c ts) = c * Monomial.eval ρ m + evalTerms ρ ts := by
  induction ts with
  | nil =>
    simp only [insertNormalizedTerm]
    by_cases hc : c == 0
    · have h0 := beq_iff_eq.mp hc; subst h0; simp [evalTerms]; grind
    · simp [hc, evalTerms]
  | cons hd tl ih =>
    rcases hd with ⟨m', c'⟩; simp only [insertNormalizedTerm]
    have hmNorm' := Monomial.eval_normalize ρ m'
    by_cases hm : m == monoNormalize m'
    · have hEvalEq : Monomial.eval ρ m = Monomial.eval ρ m' := by rw [beq_iff_eq.mp hm, hmNorm']
      simp only [hm, ↓reduceIte]
      by_cases hsum : c + c' == 0
      · have hs0 : c + c' = 0 := beq_iff_eq.mp hsum
        simp only [hsum, ↓reduceIte, evalTerms]
        have : c * Monomial.eval ρ m + c' * Monomial.eval ρ m' = (c + c') * Monomial.eval ρ m' := by grind
        grind
      · simp only [hsum, Bool.false_eq_true, ↓reduceIte, evalTerms]; grind
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt : Monomial.lt m (monoNormalize m')
      · simp only [hlt, ↓reduceIte]
        by_cases hc : c == 0
        · have h0 := beq_iff_eq.mp hc; subst h0; simp [evalTerms, hmNorm']; grind
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, evalTerms, hmNorm']
      · simp only [hlt, Bool.false_eq_true, ↓reduceIte, evalTerms, hmNorm', ih]; grind

theorem evalTerms_insertTerm (ρ : Nat → CanonicalRat) (m : Monomial) (c : CanonicalRat)
    (ts : List (Monomial × CanonicalRat)) :
    evalTerms ρ (insertTerm m c ts) = c * Monomial.eval ρ m + evalTerms ρ ts := by
  unfold insertTerm Monomial.normalize; rw [evalTerms_insertNormalizedTerm, Monomial.eval_normalize]

namespace Poly

abbrev zero : Poly := ⟨[]⟩
abbrev one : Poly := ⟨[([], 1)]⟩
abbrev isZero (p : Poly) : Bool := p.terms.isEmpty
abbrev add (p1 p2 : Poly) : Poly := ⟨p2.terms.foldl (fun acc (m, c) => insertTerm m c acc) p1.terms⟩

@[expose] def mulTerm (t : Monomial × CanonicalRat) (p : Poly) : Poly :=
  if t.2 == 0 then zero else ⟨p.terms.map fun (m, c) => (Monomial.mul t.1 m, t.2 * c)⟩

@[expose] def scale (c : CanonicalRat) (p : Poly) : Poly :=
  if c == 0 then zero else ⟨p.terms.map fun (m, k) => (m, c * k)⟩

abbrev neg (p : Poly) : Poly := scale (-1) p
abbrev sub (p1 p2 : Poly) : Poly := add p1 (neg p2)
abbrev sumBy {α : Type} (terms : List α) (term : α → Poly) : Poly :=
  terms.foldl (fun acc t => add acc (term t)) zero
abbrev mul (p1 p2 : Poly) : Poly := sumBy p1.terms (fun t => mulTerm t p2)
abbrev sqr (p : Poly) : Poly := mul p p
abbrev eval (ρ : Nat → CanonicalRat) (p : Poly) : CanonicalRat := evalTerms ρ p.terms

@[simp] theorem eval_zero (ρ : Nat → CanonicalRat) : Poly.zero.eval ρ = 0 := rfl
@[simp] theorem eval_one (ρ : Nat → CanonicalRat) : Poly.one.eval ρ = 1 := by
  simp [Poly.eval, evalTerms, Monomial.eval]; grind

theorem eval_isZero (ρ : Nat → CanonicalRat) (p : Poly) (h : p.isZero = true) : p.eval ρ = 0 := by
  rcases p with ⟨ts⟩; cases ts with | nil => rfl | cons _ _ => simp [Poly.isZero] at h

theorem evalTerms_foldl_insert (ρ : Nat → CanonicalRat) (ts2 ts1 : List (Monomial × CanonicalRat)) :
    evalTerms ρ (ts2.foldl (fun acc (m, c) => insertTerm m c acc) ts1) = evalTerms ρ ts1 + evalTerms ρ ts2 := by
  induction ts2 generalizing ts1 with
  | nil => simp [evalTerms]; grind
  | cons hd _ ih => simp only [List.foldl_cons, ih, evalTerms_insertTerm, evalTerms]; grind

@[simp] theorem eval_add (ρ : Nat → CanonicalRat) (p1 p2 : Poly) :
    (Poly.add p1 p2).eval ρ = p1.eval ρ + p2.eval ρ :=
  evalTerms_foldl_insert ρ p2.terms p1.terms

theorem eval_mulTerm (ρ : Nat → CanonicalRat) (t : Monomial × CanonicalRat) (p : Poly) :
    (Poly.mulTerm t p).eval ρ = (t.2 * Monomial.eval ρ t.1) * p.eval ρ := by
  rcases p with ⟨ts⟩; rcases t with ⟨mt, ct⟩; unfold Poly.mulTerm Poly.eval; dsimp only
  by_cases hc : ct == 0
  · have h0 := beq_iff_eq.mp hc; subst h0; simp [Poly.zero, evalTerms]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    induction ts with
    | nil => simp [evalTerms]
    | cons hd _ ih => simp only [List.map_cons, evalTerms, Monomial.eval_mul, ih]; grind

@[simp] theorem eval_scale (ρ : Nat → CanonicalRat) (c : CanonicalRat) (p : Poly) :
    (Poly.scale c p).eval ρ = c * p.eval ρ := by
  change (mulTerm ([], c) p).eval ρ = c * p.eval ρ; rw [eval_mulTerm]; simp [Monomial.eval]

@[simp] theorem eval_neg (ρ : Nat → CanonicalRat) (p : Poly) : (Poly.neg p).eval ρ = -(p.eval ρ) := by
  rw [neg, eval_scale]; grind

@[simp] theorem eval_sub (ρ : Nat → CanonicalRat) (p1 p2 : Poly) :
    (Poly.sub p1 p2).eval ρ = p1.eval ρ - p2.eval ρ := by unfold Poly.sub; rw [eval_add, eval_neg]; grind

theorem eval_foldl_mulTerm (ρ : Nat → CanonicalRat) (ts1 : List (Monomial × CanonicalRat)) (p2 acc : Poly) :
    (ts1.foldl (fun a t => Poly.add a (Poly.mulTerm t p2)) acc).eval ρ = acc.eval ρ + evalTerms ρ ts1 * p2.eval ρ := by
  induction ts1 generalizing acc with
  | nil => simp [evalTerms]; grind
  | cons _ _ ih => simp only [List.foldl_cons, ih, eval_add, eval_mulTerm, evalTerms]; grind

@[simp] theorem eval_mul (ρ : Nat → CanonicalRat) (p1 p2 : Poly) :
    (Poly.mul p1 p2).eval ρ = p1.eval ρ * p2.eval ρ := by
  unfold Poly.mul sumBy; rw [eval_foldl_mulTerm, eval_zero]; unfold Poly.eval; grind

@[simp] theorem eval_sqr (ρ : Nat → CanonicalRat) (p : Poly) :
    (Poly.sqr p).eval ρ = p.eval ρ * p.eval ρ := eval_mul ρ p p

theorem eval_sq_nonneg (ρ : Nat → CanonicalRat) (p : Poly) : 0 ≤ (Poly.sqr p).eval ρ := by
  rw [eval_sqr]; exact Interval.rat_sq_nonneg (p.eval ρ)

end Poly

namespace SparsePoly
def eval (ρ : Nat → CanonicalRat) (p : SparsePoly) : CanonicalRat := Poly.eval ρ p
theorem eval_add (ρ : Nat → CanonicalRat) (p1 p2 : SparsePoly) :
    SparsePoly.eval ρ (Poly.add p1 p2) = SparsePoly.eval ρ p1 + SparsePoly.eval ρ p2 := Poly.eval_add ρ p1 p2
theorem eval_sub (ρ : Nat → CanonicalRat) (p1 p2 : SparsePoly) :
    SparsePoly.eval ρ (Poly.sub p1 p2) = SparsePoly.eval ρ p1 - SparsePoly.eval ρ p2 := Poly.eval_sub ρ p1 p2
theorem eval_mul (ρ : Nat → CanonicalRat) (p1 p2 : SparsePoly) :
    SparsePoly.eval ρ (Poly.mul p1 p2) = SparsePoly.eval ρ p1 * SparsePoly.eval ρ p2 := Poly.eval_mul ρ p1 p2
theorem eval_neg (ρ : Nat → CanonicalRat) (p : SparsePoly) :
    SparsePoly.eval ρ (Poly.neg p) = -(SparsePoly.eval ρ p) := Poly.eval_neg ρ p
theorem eval_sq_nonneg (ρ : Nat → CanonicalRat) (p : SparsePoly) :
    0 ≤ SparsePoly.eval ρ (Poly.sqr p) := Poly.eval_sq_nonneg ρ p
end SparsePoly

structure SOSPoly where
  terms : List (CanonicalRat × Poly)
  deriving DecidableEq, Repr

namespace SOSPoly
abbrev expand (sos : SOSPoly) : Poly := Poly.sumBy sos.terms (fun (c, p) => Poly.scale c (Poly.sqr p))
abbrev allCoeffsPos (sos : SOSPoly) : Bool := sos.terms.all fun (c, _) => decide (0 < c)

theorem eval_foldl_expand_nonneg (ρ : Nat → CanonicalRat)
    (ts : List (CanonicalRat × Poly)) (acc : Poly) (hAcc : 0 ≤ acc.eval ρ)
    (hPos : (ts.all fun (c, _) => decide (0 < c)) = true) :
    0 ≤ (ts.foldl (fun a (c, p) => Poly.add a (Poly.scale c (Poly.sqr p))) acc).eval ρ := by
  induction ts generalizing acc with
  | nil => exact hAcc
  | cons hd _ ih =>
    rcases hd with ⟨c, p⟩
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hPos
    simp only [List.foldl_cons]; apply ih _ ?_ hPos.2
    rw [Poly.eval_add, Poly.eval_scale]
    have hmul := Rat.mul_le_mul_of_nonneg_left (Poly.eval_sq_nonneg ρ p) (by grind : 0 ≤ c)
    grind

theorem eval_expand_nonneg (ρ : Nat → CanonicalRat) (sos : SOSPoly) (hPos : sos.allCoeffsPos = true) :
    0 ≤ sos.expand.eval ρ :=
  eval_foldl_expand_nonneg ρ sos.terms Poly.zero (by simp) hPos
end SOSPoly

structure SOSQuery where
  goal : Poly
  ineqs : List Poly
  eqs : List Poly
  deriving DecidableEq, Repr

structure SOSCert where
  sigma0 : SOSPoly
  sigmas : List (SOSPoly × Nat)
  lambdas : List (Poly × Nat)
  deriving DecidableEq, Repr

inductive SOSClause where
  | invalidSOSWeights
  | identityMismatch (residual : Poly)
  | violatedAt (point : List CanonicalRat)
  deriving DecidableEq, Repr

/-- Evaluate a finite rational coordinate vector `pt : List CanonicalRat` as a variable assignment `Nat → CanonicalRat`. -/
def ratPointEnv (pt : List CanonicalRat) (v : Nat) : CanonicalRat := (pt[v]?).getD 0

@[simp] theorem ratPointEnv_nil (v : Nat) : ratPointEnv [] v = 0 := by unfold ratPointEnv; rfl

theorem ratPointEnv_map_range (dim : Nat) (ρ : Nat → CanonicalRat) {v : Nat} (hv : v < dim) :
    ratPointEnv ((List.range dim).map ρ) v = ρ v := by
  unfold ratPointEnv; simp [List.getElem?_map, List.getElem?_range hv]

def monoVarBound : Monomial → Nat
  | [] => 0
  | (v, _) :: rest => max (v + 1) (monoVarBound rest)

def polyTermsVarBound : List (Monomial × CanonicalRat) → Nat
  | [] => 0
  | (m, _) :: rest => max (monoVarBound m) (polyTermsVarBound rest)

def polyVarBound (p : Poly) : Nat := polyTermsVarBound p.terms

def polyListVarBound : List Poly → Nat
  | [] => 0
  | p :: ps => max (polyVarBound p) (polyListVarBound ps)

theorem monoVarBound_eval_congr {bound : Nat} {ρ₁ ρ₂ : Nat → CanonicalRat}
    (hAgree : ∀ v, v < bound → ρ₁ v = ρ₂ v) :
    ∀ (m : Monomial), monoVarBound m ≤ bound → Monomial.eval ρ₁ m = Monomial.eval ρ₂ m
  | [], _ => rfl
  | (v, _) :: rest, hB => by
    unfold monoVarBound at hB
    simp only [Monomial.eval, hAgree v (by omega), monoVarBound_eval_congr hAgree rest (by omega)]

theorem polyTermsVarBound_eval_congr {bound : Nat} {ρ₁ ρ₂ : Nat → CanonicalRat}
    (hAgree : ∀ v, v < bound → ρ₁ v = ρ₂ v) :
    ∀ (ts : List (Monomial × CanonicalRat)), polyTermsVarBound ts ≤ bound → evalTerms ρ₁ ts = evalTerms ρ₂ ts
  | [], _ => rfl
  | (m, _) :: rest, hB => by
    unfold polyTermsVarBound at hB
    simp only [evalTerms, monoVarBound_eval_congr hAgree m (by omega), polyTermsVarBound_eval_congr hAgree rest (by omega)]

theorem polyVarBound_eval_congr {bound : Nat} {p : Poly} {ρ₁ ρ₂ : Nat → CanonicalRat}
    (hB : polyVarBound p ≤ bound) (hAgree : ∀ v, v < bound → ρ₁ v = ρ₂ v) :
    p.eval ρ₁ = p.eval ρ₂ := polyTermsVarBound_eval_congr hAgree p.terms hB

theorem polyVarBound_le_polyListVarBound {p : Poly} :
    ∀ {ps : List Poly}, p ∈ ps → polyVarBound p ≤ polyListVarBound ps
  | [], h => nomatch h
  | _ :: _, h => by
    unfold polyListVarBound
    rcases List.mem_cons.mp h with rfl | hRest
    · omega
    · have ih := polyVarBound_le_polyListVarBound hRest; omega

def signedIntsUpTo : Nat → List Int
  | 0 => [0]
  | k + 1 => signedIntsUpTo k ++ [Int.ofNat (k + 1), -Int.ofNat (k + 1)]

theorem mem_signedIntsUpTo (n : Int) : ∀ (B : Nat), n.natAbs ≤ B → n ∈ signedIntsUpTo B
  | 0, h => by have hn0 : n = 0 := (by omega); subst hn0; exact List.Mem.head []
  | k + 1, h => by
    unfold signedIntsUpTo
    by_cases hle : n.natAbs ≤ k
    · exact List.mem_append_left _ (mem_signedIntsUpTo n k hle)
    · have heq : n.natAbs = k + 1 := by omega
      apply List.mem_append_right
      cases n with
      | ofNat m => have hmEq : m = k + 1 := heq; subst hmEq; exact List.Mem.head _
      | negSucc m => have hmEq : m = k := (by omega); subst hmEq; exact List.Mem.tail _ (List.Mem.head [])

def posNatsUpTo (B : Nat) : List Nat := (List.range B).map (· + 1)

theorem mem_posNatsUpTo {d B : Nat} (hd0 : 0 < d) (hdB : d ≤ B) : d ∈ posNatsUpTo B :=
  List.mem_map.mpr ⟨d - 1, List.mem_range.mpr (by omega), by omega⟩

def ratsOfHeightLe (B : Nat) : List CanonicalRat :=
  (posNatsUpTo B).flatMap fun den => (signedIntsUpTo B).map fun num => CanonicalRat.mk num den

theorem mem_ratsOfHeightLe {q : CanonicalRat} {B : Nat}
    (hNum : q.num.natAbs ≤ B) (hDen : q.den ≤ B) : q ∈ ratsOfHeightLe B := by
  unfold ratsOfHeightLe; rw [List.mem_flatMap]
  refine ⟨q.den, mem_posNatsUpTo (Nat.pos_of_ne_zero q.den_nz) hDen, List.mem_map.mpr ?_⟩
  exact ⟨q.num, mem_signedIntsUpTo q.num B hNum, Rat.mkRat_self q⟩

def ratTuplesOfDim : Nat → Nat → List (List CanonicalRat)
  | 0, _ => [[]]
  | d + 1, B => (ratsOfHeightLe B).flatMap fun x => (ratTuplesOfDim d B).map fun xs => x :: xs

theorem mem_ratTuplesOfDim (B : Nat) :
    ∀ (xs : List CanonicalRat), (∀ x ∈ xs, x.num.natAbs ≤ B ∧ x.den ≤ B) → xs ∈ ratTuplesOfDim xs.length B
  | [], _ => List.Mem.head []
  | x :: xs, hCoords => by
    simp only [List.length_cons, ratTuplesOfDim, List.mem_flatMap, List.mem_map]
    have hx := hCoords x (List.Mem.head xs)
    exact ⟨x, mem_ratsOfHeightLe hx.1 hx.2, xs,
      mem_ratTuplesOfDim B xs (fun y hy => hCoords y (List.Mem.tail x hy)), rfl⟩

def ratTupleHeightBound (pt : List CanonicalRat) : Nat :=
  pt.foldr (fun x acc => max (max x.num.natAbs x.den) acc) 1

theorem one_le_ratTupleHeightBound (pt : List CanonicalRat) : 1 ≤ ratTupleHeightBound pt := by
  induction pt with
  | nil => exact Nat.le_refl 1
  | cons _ _ ih => unfold ratTupleHeightBound at ih ⊢; simp only [List.foldr_cons]; omega

theorem coord_le_ratTupleHeightBound {pt : List CanonicalRat} {x : CanonicalRat} (hx : x ∈ pt) :
    x.num.natAbs ≤ ratTupleHeightBound pt ∧ x.den ≤ ratTupleHeightBound pt := by
  induction pt with
  | nil => nomatch hx
  | cons _ _ ih =>
    unfold ratTupleHeightBound; simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hRest
    · exact ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := ih hRest; unfold ratTupleHeightBound at h1 h2; exact ⟨by omega, by omega⟩

theorem envPrefix_mem_ratTuplesOfDim (dim B : Nat) (pt : List CanonicalRat)
    (hB1 : 1 ≤ B) (hCoords : ∀ x ∈ pt, x.num.natAbs ≤ B ∧ x.den ≤ B) :
    (List.range dim).map (ratPointEnv pt) ∈ ratTuplesOfDim dim B := by
  have hMem : ((List.range dim).map (ratPointEnv pt)) ∈
      ratTuplesOfDim ((List.range dim).map (ratPointEnv pt)).length B := by
    apply mem_ratTuplesOfDim B
    intro x hx
    rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
    unfold ratPointEnv
    cases hget : pt[v]? with
    | none => exact ⟨Nat.zero_le B, hB1⟩
    | some y => exact hCoords y (List.mem_of_getElem? hget)
  simpa only [List.length_map, List.length_range] using hMem

theorem list_find?_some_prop {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {w : α}, xs.find? p = some w → p w = true := list_find?_some_prop_iv p

theorem list_find?_exists_of_mem {α : Type} (p : α → Bool)
    (xs : List α) {x : α} (hx : x ∈ xs) (hp : p x = true) :
    ∃ w, xs.find? p = some w ∧ p w = true := list_find?_exists_of_mem_iv p xs hx hp

def singleCoordPoint (v : Nat) (val : CanonicalRat) : List CanonicalRat := List.replicate v 0 ++ [val]

/-- Extract coordinate-axis univariate quadratic-vertex (`-b / (2a)`) and linear-root (`-c / b`)
rational seeds along axis `v` (holding other coordinates at `0`). -/
def polyAxisSeeds (v : Nat) (p : Poly) : List (List CanonicalRat) :=
  let p0 := p.eval (ratPointEnv [])
  let p1 := p.eval (ratPointEnv (singleCoordPoint v 1))
  let pm1 := p.eval (ratPointEnv (singleCoordPoint v (-1)))
  let twoA := p1 + pm1 - 2 * p0
  let twoB := p1 - pm1
  let half : CanonicalRat := CanonicalRat.mk 1 2
  if twoA != 0 then
    let vtx := (-twoB) / (2 * twoA)
    [vtx, vtx + half, vtx - half, vtx + 1, vtx - 1].map (singleCoordPoint v)
  else if twoB != 0 then
    let rt := (-2 * p0) / twoB
    [rt, rt + half, rt - half, rt + 1, rt - 1].map (singleCoordPoint v)
  else []

/-- Deterministic grade-0 rational seed candidates combining multi-axis probes and quadratic-vertex / root seeds. -/
def polyListSeedPoints (dim : Nat) (polys : List Poly) : List (List CanonicalRat) :=
  let half : CanonicalRat := CanonicalRat.mk 1 2
  let axisVals : List CanonicalRat := [1, -1, 2, -2, half, -half, 3, -3]
  let axisPts := (List.range dim).flatMap fun v => axisVals.map (singleCoordPoint v)
  let diagPts : List (List CanonicalRat) :=
    if 2 ≤ dim then [[1, 1], [1, -1], [-1, 1], [-1, -1], [2, 2], [2, -2]] else []
  let algPts := (List.range dim).flatMap fun v => polys.flatMap (polyAxisSeeds v)
  [] :: (algPts ++ axisPts ++ diagPts)

def sosQueryVarBound (q : SOSQuery) : Nat := polyListVarBound (q.goal :: (q.ineqs ++ q.eqs))

def evalSosViolation (q : SOSQuery) (pt : List CanonicalRat) : Bool :=
  let ρ := ratPointEnv pt
  (q.ineqs.all fun g => decide (0 ≤ g.eval ρ)) &&
  (q.eqs.all fun h => decide (h.eval ρ = 0)) &&
  decide (q.goal.eval ρ < 0)

def findNegativePolyWitnessAtShell (shell : Nat) (q : SOSQuery) : Option (List CanonicalRat) :=
  let dim := sosQueryVarBound q
  let cands :=
    if shell == 0 then polyListSeedPoints dim (q.goal :: (q.ineqs ++ q.eqs))
    else ratTuplesOfDim dim shell
  cands.find? (evalSosViolation q)

/-- Grade-indexed rational + quadratic-vertex counterexample search for `SOSQuery` via `Judge.deepen`. -/
def findNegativePolyWitness (grade : Nat) (q : SOSQuery) : Option (List CanonicalRat) :=
  Judge.deepen (fun g => findNegativePolyWitnessAtShell g q) grade

/-- Canonical empty refutation-probe certificate (`⟨⟨[]⟩, [], []⟩`) triggering unbounded grade-indexed
rational counterexample search across shells `0..grade` (`judge_mono_probe_dichotomy`). -/
def sosSearchProbe : SOSCert := ⟨⟨[]⟩, [], []⟩

def sosCertIsSearchProbe (c : SOSCert) : Bool :=
  c.sigma0.terms.isEmpty && c.sigmas.isEmpty && c.lambdas.isEmpty

@[expose] def indexedSum {α : Type} (factor : α → Poly) (gens : List Poly)
    (terms : List (α × Nat)) (acc : Poly) : Poly :=
  terms.foldl (fun sum (a, idx) =>
    match gens[idx]? with
    | some g => Poly.add sum (Poly.mul (factor a) g)
    | none => sum) acc

abbrev certificateResidual (q : SOSQuery) (c : SOSCert) : Poly :=
  let ineq := indexedSum SOSPoly.expand q.ineqs c.sigmas Poly.zero
  let eq := indexedSum id q.eqs c.lambdas Poly.zero
  Poly.sub q.goal (Poly.add c.sigma0.expand (Poly.add ineq eq))

/-- Verify an `SOSCert` `c` or (when `c` is the canonical search probe `sosSearchProbe`) search across
rational shells `0..grade` via `Judge.deepen` for a concrete counterexample witness `.violatedAt pt`. -/
def sosCheck (grade : Nat) (q : SOSQuery) (c : SOSCert) : Judge.Verdict SOSClause :=
  if c.sigma0.allCoeffsPos && c.sigmas.all (fun (s, _) => s.allCoeffsPos) &&
      c.sigmas.all (fun (_, idx) => decide (idx < q.ineqs.length)) &&
      c.lambdas.all (fun (_, idx) => decide (idx < q.eqs.length)) then
    let diff := certificateResidual q c
    if diff.isZero then .ok
    else if sosCertIsSearchProbe c then
      match findNegativePolyWitness grade q with
      | some pt => .refused (.violatedAt pt) []
      | none    => .uncovered
    else .refused (.identityMismatch diff) []
  else .refused .invalidSOSWeights []

abbrev SOSQuery.SemanticMeaning (q : SOSQuery) : Prop :=
  ∀ (ρ : Nat → CanonicalRat),
    (∀ g ∈ q.ineqs, 0 ≤ g.eval ρ) → (∀ h ∈ q.eqs, h.eval ρ = 0) → 0 ≤ q.goal.eval ρ

theorem eval_foldl_sigmas_nonneg (ρ : Nat → CanonicalRat) (ineqs : List Poly)
    (hIneqs : ∀ g ∈ ineqs, 0 ≤ g.eval ρ) (sigmas : List (SOSPoly × Nat)) (acc : Poly)
    (hAcc : 0 ≤ acc.eval ρ) (hPos : (sigmas.all fun (s, _) => s.allCoeffsPos) = true) :
    0 ≤ (sigmas.foldl (fun a (sig, idx) =>
      match ineqs[idx]? with
      | some gi => Poly.add a (Poly.mul sig.expand gi)
      | none => a) acc).eval ρ := by
  induction sigmas generalizing acc with
  | nil => exact hAcc
  | cons hd _ ih =>
    rcases hd with ⟨sig, idx⟩
    simp only [List.all_cons, Bool.and_eq_true] at hPos; simp only [List.foldl_cons]
    cases hgi : ineqs[idx]? with
    | none => exact ih acc hAcc hPos.2
    | some gi =>
      apply ih _ ?_ hPos.2; rw [Poly.eval_add, Poly.eval_mul]
      have hmul := Rat.mul_le_mul_of_nonneg_left (hIneqs gi (List.mem_of_getElem? hgi))
        (SOSPoly.eval_expand_nonneg ρ sig hPos.1)
      grind

theorem eval_foldl_lambdas_zero (ρ : Nat → CanonicalRat) (eqs : List Poly)
    (hEqs : ∀ h ∈ eqs, h.eval ρ = 0) (lambdas : List (Poly × Nat)) (acc : Poly) (hAcc : acc.eval ρ = 0) :
    (lambdas.foldl (fun a (lam, idx) =>
      match eqs[idx]? with
      | some hj => Poly.add a (Poly.mul lam hj)
      | none => a) acc).eval ρ = 0 := by
  induction lambdas generalizing acc with
  | nil => exact hAcc
  | cons hd _ ih =>
    rcases hd with ⟨lam, idx⟩; simp only [List.foldl_cons]
    cases hhj : eqs[idx]? with
    | none => exact ih acc hAcc
    | some hj =>
      apply ih; rw [Poly.eval_add, Poly.eval_mul, hAcc, hEqs hj (List.mem_of_getElem? hhj)]; grind

inductive NthPoly : List Poly → Nat → Poly → Prop where
  | head {p ps} : NthPoly (p :: ps) 0 p
  | tail {p ps i g} : NthPoly ps i g → NthPoly (p :: ps) (i + 1) g

private theorem nthPoly_iff_getElem? {gens i g} : NthPoly gens i g ↔ gens[i]? = some g := by
  constructor
  · intro h; induction h with | head => rfl | tail _ ih => exact ih
  · induction gens generalizing i with
    | nil => simp
    | cons _ _ ih => cases i with | zero => rintro h; cases h; exact .head | succ i => intro h; exact .tail (ih h)

inductive GeneratorSum {α : Type} (factor : α → Poly) (gens : List Poly) :
    List (α × Nat) → Poly → Poly → Prop where
  | nil {acc} : GeneratorSum factor gens [] acc acc
  | cons {a i rest acc g total} : NthPoly gens i g →
      GeneratorSum factor gens rest (Poly.add acc (Poly.mul (factor a) g)) total →
      GeneratorSum factor gens ((a, i) :: rest) acc total

private theorem generatorSum_iff {α : Type} {factor : α → Poly} {gens terms acc total} :
    GeneratorSum factor gens terms acc total ↔
      (∀ t ∈ terms, t.2 < gens.length) ∧ indexedSum factor gens terms acc = total := by
  constructor
  · intro deriv
    induction deriv with
    | nil => exact ⟨by simp, rfl⟩
    | cons nth _ ih =>
      have hx := nthPoly_iff_getElem?.mp nth
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hx
      exact ⟨by simpa using And.intro hi ih.1, by simpa [indexedSum, hx] using ih.2⟩
  · rintro ⟨bounds, rfl⟩
    induction terms generalizing acc with
    | nil => exact .nil
    | cons hd _ ih =>
      obtain ⟨a, i⟩ := hd
      have hi : i < gens.length := bounds (a, i) (by simp)
      have hx := List.getElem?_eq_getElem hi
      simp only [indexedSum, List.foldl_cons, hx]
      exact .cons (nthPoly_iff_getElem?.mpr hx) (ih (fun t ht => bounds t (by simp [ht])))

inductive SosExpansion : List (CanonicalRat × Poly) → Poly → Poly → Prop where
  | nil {acc} : SosExpansion [] acc acc
  | cons {w p rest acc total} :
      SosExpansion rest (Poly.add acc (Poly.scale w (Poly.sqr p))) total →
      SosExpansion ((w, p) :: rest) acc total

private theorem sosExpansion_iff {terms acc total} :
    SosExpansion terms acc total ↔
      terms.foldl (fun a (c, p) => Poly.add a (Poly.scale c (Poly.sqr p))) acc = total := by
  constructor
  · intro h; induction h with | nil => rfl | cons _ ih => simpa using ih
  · rintro rfl
    induction terms generalizing acc with
    | nil => exact .nil
    | cons hd _ ih => obtain ⟨_, _⟩ := hd; exact .cons ih

/-- A Putinar decomposition with positive square weights and a vanishing polynomial residual. -/
def SosDecomposition (q : SOSQuery) (c : SOSCert) : Prop :=
  (∀ cw ∈ c.sigma0.terms, 0 < cw.1) ∧
  (∀ t ∈ c.sigmas, ∀ cw ∈ t.1.terms, 0 < cw.1) ∧
  ∃ S₀ I E,
    SosExpansion c.sigma0.terms Poly.zero S₀ ∧
    GeneratorSum SOSPoly.expand q.ineqs c.sigmas Poly.zero I ∧
    GeneratorSum id q.eqs c.lambdas Poly.zero E ∧
    (Poly.sub q.goal (Poly.add S₀ (Poly.add I E))).terms = []

def DeclarativeSosDecomposable (q : SOSQuery) : Prop := ∃ c, SosDecomposition q c

theorem SosDecomposition.iff_validResidual (q : SOSQuery) (c : SOSCert) :
    SosDecomposition q c ↔
      (c.sigma0.allCoeffsPos && c.sigmas.all (fun (s, _) => s.allCoeffsPos) &&
        c.sigmas.all (fun (_, i) => decide (i < q.ineqs.length)) &&
        c.lambdas.all (fun (_, i) => decide (i < q.eqs.length))) = true ∧
      (certificateResidual q c).isZero = true := by
  simp only [SosDecomposition, sosExpansion_iff, generatorSum_iff,
    SOSPoly.expand, Poly.sumBy, Bool.and_eq_true, List.all_eq_true,
    SOSPoly.allCoeffsPos, decide_eq_true_eq, Poly.isZero, List.isEmpty_iff]
  exact ⟨fun ⟨pos, wts, _, _, _, rfl, ⟨ib, rfl⟩, ⟨eb, rfl⟩, idn⟩ => ⟨⟨⟨⟨pos, wts⟩, ib⟩, eb⟩, idn⟩,
         fun ⟨⟨⟨⟨pos, wts⟩, ib⟩, eb⟩, idn⟩ => ⟨pos, wts, _, _, _, rfl, ⟨ib, rfl⟩, ⟨eb, rfl⟩, idn⟩⟩

theorem SosDecomposition.meaning {q c} (h : SosDecomposition q c) : SOSQuery.SemanticMeaning q := by
  intro ρ hIneqs hEqs
  obtain ⟨weights, identity⟩ := (SosDecomposition.iff_validResidual q c).mp h
  simp only [Bool.and_eq_true] at weights
  have h0 := SOSPoly.eval_expand_nonneg ρ c.sigma0 weights.1.1.1
  have hI := eval_foldl_sigmas_nonneg ρ q.ineqs hIneqs c.sigmas Poly.zero (by simp) weights.1.1.2
  have hE := eval_foldl_lambdas_zero ρ q.eqs hEqs c.lambdas Poly.zero (by simp)
  have residual := Poly.eval_isZero ρ _ identity
  dsimp only [certificateResidual, indexedSum, id] at residual
  rw [Poly.eval_sub, Poly.eval_add, Poly.eval_add, hE] at residual; grind

theorem evalSosViolation_refutes {q : SOSQuery} {pt : List CanonicalRat}
    (h : evalSosViolation q pt = true) : ¬ SOSQuery.SemanticMeaning q := by
  simp only [evalSosViolation, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro meaning; have nonneg := meaning (ratPointEnv pt) h.1.1 h.1.2; grind

theorem findNegativePolyWitnessAtShell_sound {shell : Nat} {q : SOSQuery} {pt : List CanonicalRat}
    (h : findNegativePolyWitnessAtShell shell q = some pt) : evalSosViolation q pt = true :=
  list_find?_some_prop (evalSosViolation q) h

theorem findNegativePolyWitness_sound {grade : Nat} {q : SOSQuery} {pt : List CanonicalRat}
    (h : findNegativePolyWitness grade q = some pt) : evalSosViolation q pt = true := by
  obtain ⟨_, _, hi⟩ := Judge.deepen_some _ h; exact findNegativePolyWitnessAtShell_sound hi

private theorem findNegativePolyWitness_inhabited :
    ∃ pt1 pt2, findNegativePolyWitnessAtShell 0 ⟨Poly.neg Poly.one, [], []⟩ = some pt1 ∧
      findNegativePolyWitness 0 ⟨Poly.neg Poly.one, [], []⟩ = some pt2 := ⟨[], [], by decide +kernel, by decide +kernel⟩

theorem evalSosViolation_envPrefix {q : SOSQuery} {pt : List CanonicalRat} (h : evalSosViolation q pt = true) :
    evalSosViolation q ((List.range (sosQueryVarBound q)).map (ratPointEnv pt)) = true := by
  let dim := sosQueryVarBound q; let pref := (List.range dim).map (ratPointEnv pt)
  have hAgree : ∀ v, v < dim → ratPointEnv pref v = ratPointEnv pt v := fun v hv => ratPointEnv_map_range dim (ratPointEnv pt) hv
  simp only [evalSosViolation, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨⟨fun g hg => ?_, fun eqG heq => ?_⟩, ?_⟩
  · rw [polyVarBound_eval_congr (polyVarBound_le_polyListVarBound (List.Mem.tail _ (List.mem_append_left _ hg))) hAgree]; exact h.1.1 g hg
  · rw [polyVarBound_eval_congr (polyVarBound_le_polyListVarBound (List.Mem.tail _ (List.mem_append_right _ heq))) hAgree]; exact h.1.2 eqG heq
  · rw [polyVarBound_eval_congr (polyVarBound_le_polyListVarBound (List.Mem.head _)) hAgree]; exact h.2

/-- **Finite-Grade Rational Counterexample Completeness for `SOSQuery`**:
Every rational violation point `pt` (`evalSosViolation q pt = true`) with coordinate height `≤ B`
(`1 ≤ B`) is discovered at `grade = B` on `sosSearchProbe`. -/
theorem findNegativePolyWitness_complete (q : SOSQuery) (pt : List CanonicalRat) (B : Nat)
    (hB1 : 1 ≤ B) (hCoords : ∀ x ∈ pt, x.num.natAbs ≤ B ∧ x.den ≤ B) (hViol : evalSosViolation q pt = true) :
    ∃ w, findNegativePolyWitness B q = some w ∧ evalSosViolation q w = true ∧
         sosCheck B q sosSearchProbe = .refused (.violatedAt w) [] ∧ ¬ SOSQuery.SemanticMeaning q := by
  have hPrefViol := evalSosViolation_envPrefix hViol
  have hPrefMem := envPrefix_mem_ratTuplesOfDim (sosQueryVarBound q) B pt hB1 hCoords
  have hShell : ∃ w0, findNegativePolyWitnessAtShell B q = some w0 ∧ evalSosViolation q w0 = true := by
    unfold findNegativePolyWitnessAtShell; rw [beq_false_of_ne (by omega : B ≠ 0)]
    simp only [Bool.false_eq_true, ↓reduceIte]; exact list_find?_exists_of_mem (evalSosViolation q) _ hPrefMem hPrefViol
  obtain ⟨w0, hw0, _⟩ := hShell
  obtain ⟨w, hwDeep⟩ := Judge.deepen_isSome (fun g => findNegativePolyWitnessAtShell g q) hw0
  change findNegativePolyWitness B q = some w at hwDeep
  have hwViol := findNegativePolyWitness_sound hwDeep
  have hDiffNotZero : (certificateResidual q sosSearchProbe).isZero = false := by
    cases hZ : (certificateResidual q sosSearchProbe).isZero with
    | false => rfl
    | true =>
      have hEval0 := Poly.eval_isZero (ratPointEnv pt) _ hZ
      rw [certificateResidual, Poly.eval_sub, Poly.eval_add, Poly.eval_add] at hEval0
      have hZeroSum : (sosSearchProbe.sigma0.expand.eval (ratPointEnv pt) +
          ((indexedSum SOSPoly.expand q.ineqs sosSearchProbe.sigmas Poly.zero).eval (ratPointEnv pt) +
           (indexedSum id q.eqs sosSearchProbe.lambdas Poly.zero).eval (ratPointEnv pt))) = 0 := by
        simp [sosSearchProbe, SOSPoly.expand, Poly.sumBy, indexedSum]; grind
      rw [hZeroSum] at hEval0; simp only [evalSosViolation, Bool.and_eq_true, decide_eq_true_eq] at hViol
      have hGoalLt := hViol.2; grind
  have hCheck : sosCheck B q sosSearchProbe = .refused (.violatedAt w) [] := by
    unfold sosCheck
    have hWts : (sosSearchProbe.sigma0.allCoeffsPos && (sosSearchProbe.sigmas.all fun (s, _) => s.allCoeffsPos) &&
        (sosSearchProbe.sigmas.all fun (_, idx) => decide (idx < q.ineqs.length)) &&
        (sosSearchProbe.lambdas.all fun (_, idx) => decide (idx < q.eqs.length))) = true := by
      simp [sosSearchProbe, SOSPoly.allCoeffsPos]
    have hProbe : sosCertIsSearchProbe sosSearchProbe = true := rfl
    simp only [hWts, ↓reduceIte, hDiffNotZero, Bool.false_eq_true, hProbe, hwDeep]
  exact ⟨w, hwDeep, hwViol, hCheck, evalSosViolation_refutes hwViol⟩

theorem SosDecomposition.no_witness {q c} (h : SosDecomposition q c) (grade : Nat) :
    findNegativePolyWitness grade q = none := by
  cases hv : findNegativePolyWitness grade q with
  | none => rfl
  | some pt => exact False.elim (evalSosViolation_refutes (findNegativePolyWitness_sound hv) h.meaning)

theorem sosCheck_ok_iff (r : Nat) (q : SOSQuery) (c : SOSCert) :
    sosCheck r q c = .ok ↔ SosDecomposition q c := by
  constructor
  · intro h; apply (SosDecomposition.iff_validResidual q c).mpr
    unfold sosCheck at h; split at h
    · rename_i weights; dsimp only at h; split at h
      · exact ⟨weights, by assumption⟩
      · split at h; · split at h <;> contradiction
        · contradiction
    · contradiction
  · intro h; obtain ⟨weights, identity⟩ := (SosDecomposition.iff_validResidual q c).mp h
    simp [sosCheck, weights, identity]

instance (r : Nat) (q : SOSQuery) (c : SOSCert) : Decidable (sosCheck r q c = .ok) :=
  decidable_of_iff _ ((sosCheck_ok_iff r q c).trans (SosDecomposition.iff_validResidual q c)).symm

theorem sosCheck_sound (fuel : Nat) (q : SOSQuery) (c : SOSCert) (h : sosCheck fuel q c = .ok) :
    SOSQuery.SemanticMeaning q := ((sosCheck_ok_iff fuel q c).mp h).meaning

theorem sosCheck_refuted {r q c pt path} (h : sosCheck r q c = .refused (.violatedAt pt) path) :
    ¬ SOSQuery.SemanticMeaning q := by
  unfold sosCheck at h; split at h
  · dsimp only at h; split at h
    · cases h
    · split at h
      · cases hw : findNegativePolyWitness r q with
        | none => rw [hw] at h; cases h
        | some w =>
          rw [hw] at h; injection h with hClause _; injection hClause with hEq; subst hEq
          exact evalSosViolation_refutes (findNegativePolyWitness_sound hw)
      · cases h
  · cases h

theorem sosCheck_mono {r r' : Nat} {q : SOSQuery} {c : SOSCert}
    (le : r ≤ r') (hne : sosCheck r q c ≠ .uncovered) :
    sosCheck r' q c = sosCheck r q c := by
  unfold sosCheck at hne ⊢; split
  · dsimp only at hne ⊢; split
    · rfl
    · split
      · rename_i hWeights _ hProbe
        simp only [hWeights, ↓reduceIte, hProbe] at hne
        cases hw : findNegativePolyWitness r q with
        | none => exfalso; apply hne; split at hne <;> simp_all
        | some pt => have hw' : findNegativePolyWitness r' q = some pt := Judge.deepen_mono _ hw le; rw [hw']
      · rfl
  · rfl

theorem declarativeSosDecomposable_iff_sosCheck_ok (q : SOSQuery) :
    DeclarativeSosDecomposable q ↔ ∃ c r, sosCheck r q c = .ok :=
  ⟨fun ⟨c, h⟩ => ⟨c, 0, (sosCheck_ok_iff 0 q c).mpr h⟩,
   fun ⟨c, r, ok⟩ => ⟨c, (sosCheck_ok_iff r q c).mp ok⟩⟩

instance sosJudge : Judge SOSQuery SOSCert where
  Clause := SOSClause
  Meaning q _c := SOSQuery.SemanticMeaning q
  check := sosCheck
  sound := by intro r q c h; exact sosCheck_sound r q c h
  refutes | .violatedAt _ => true | _ => false
  refuted := by intro r q c k path refused _ _; cases k <;> first | contradiction | exact sosCheck_refuted refused
  Fragment := DeclarativeSosDecomposable
  complete := fun h _ => (declarativeSosDecomposable_iff_sosCheck_ok _).mp h
  mono := fun le hne => sosCheck_mono le hne

theorem sosJudge_refutes_iff (k : SOSClause) : sosJudge.refutes k = true ↔ ∃ pt, k = .violatedAt pt := by
  cases k with
  | violatedAt pt => exact ⟨fun _ => ⟨pt, rfl⟩, fun _ => rfl⟩
  | invalidSOSWeights | identityMismatch _ => exact ⟨(fun h => nomatch h), (fun ⟨_, h⟩ => nomatch h)⟩

/-- Shifted non-SOS quadratic `(x - 3)^2 - 1` (`p(0) = +8 > 0`, `p(3) = -1 < 0`) is refuted at
vertex `x = 3` by `sosJudge` on `sosSearchProbe` at grade `0`, alongside weight/index refusal checks. -/
example :
    let x0 : Poly := ⟨[([(0, 1)], 1)]⟩
    let shiftedQuad : Poly := Poly.sub (Poly.sqr (Poly.sub x0 ⟨[([], 3)]⟩)) Poly.one
    insertTerm [(0, 1), (1, 0)] 1 (insertTerm [(0, 1)] (-1) []) = [] ∧
    sosCheck 10 ⟨Poly.one, [], []⟩ ⟨⟨[(1, Poly.one)]⟩, [(⟨[(1, Poly.one)]⟩, 0)], []⟩ = .refused .invalidSOSWeights [] ∧
    sosCheck 10 ⟨Poly.one, [], []⟩ ⟨⟨[(1, Poly.one)]⟩, [], [(Poly.one, 0)]⟩ = .refused .invalidSOSWeights [] ∧
    sosCheck 0 ⟨Poly.neg Poly.one, [], [Poly.one]⟩ ⟨⟨[]⟩, [], [(Poly.neg Poly.one, 0)]⟩ = .ok ∧
    shiftedQuad.eval (fun _ => 0) = 8 ∧
    sosCheck 0 ⟨Poly.one, [], []⟩ ⟨⟨[(1, Poly.one)]⟩, [], []⟩ = .ok ∧
    sosCheck 0 ⟨Poly.neg Poly.one, [], []⟩ sosSearchProbe = .refused (.violatedAt []) [] ∧
    sosCheck 0 ⟨shiftedQuad, [], []⟩ sosSearchProbe = .refused (.violatedAt [3]) [] ∧
    sosJudge.refutes (.violatedAt [3]) = true := by decide +kernel

end SOS
end Obend.Judge
end
