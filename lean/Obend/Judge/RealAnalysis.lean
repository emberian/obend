module
/-
# Obend.Judge.RealAnalysis — certified interval arithmetic and polynomial SOS judges

Provides:
- `intervalJudge`: Verifies exact numerical interval bounds against `RealExpr` evaluations,
  backed by an independent evaluation semantics (`IntervalQuery.SemanticMeaning`) and `evalInterval_sound`.
- `sosJudge`: Verifies polynomial Sum-of-Squares (SOS) non-negativity certificates and Putinar/Gröbner constraints,
  equipped with a multiplicative Graded Lexicographic (`grlex`) monomial order (`grlex_mul_compatible`)
  and an independent ring evaluation semantics `Poly.eval` / `SparsePoly.eval` (`SOSQuery.SemanticMeaning`).
-/
public import Obend.Judge.Class
public import Obend.Analysis.RealAnalysis

public section
namespace Obend.Judge
open Obend.Analysis
open Obend.Analysis.CanonicalRat
set_option autoImplicit false

/-! ## Certified Interval Judge (`interval@1`) -/

/-- Query specifying an arithmetic expression, domain bounds for variables, and the claimed enclosure. -/
structure IntervalQuery where
  expr : RealExpr
  env : List (String × Interval)
  claimedBound : Interval
  deriving @[expose] DecidableEq, Repr

/-- Certificate for an interval query: direct evaluation or counterexample refutation point. -/
inductive IntervalCert where
  | direct
  | counterexample (point : List (String × CanonicalRat))
  deriving @[expose] DecidableEq, Repr

/-- Refusal clauses for interval verification. -/
inductive IntervalClause where
  | boundViolated (computed claimed : Interval)
  | domainUndefined
  | refutationWitness (point : List (String × CanonicalRat))
  deriving @[expose] DecidableEq, Repr

/-- Checker for IntervalJudge. -/
@[expose] def intervalCheck (_fuel : Nat) (q : IntervalQuery) (c : IntervalCert) : Judge.Verdict IntervalClause :=
  match c with
  | .direct =>
    match evalInterval q.env q.expr with
    | some comp =>
      if decide (q.claimedBound.lo ≤ comp.lo ∧ comp.hi ≤ q.claimedBound.hi) then .ok
      else .refused (.boundViolated comp q.claimedBound) []
    | none => .refused .domainUndefined []
  | .counterexample pt =>
    -- Domain Validation: verify every declared variable in q.env is assigned a value inside its interval
    let inDomain := q.env.all fun (s, iv) =>
      match pt.find? (·.1 == s) with
      | some (_, v) => iv.containsRat v
      | none => false
    if !inDomain then
      .uncovered
    else
      let rho (s : String) : CanonicalRat :=
        match pt.find? (·.1 == s) with
        | some (_, v) => v
        | none => 0
      match evalPoint rho q.expr with
      | some v =>
        if decide (v < q.claimedBound.lo ∨ q.claimedBound.hi < v) then
          .refused (.refutationWitness pt) []
        else .uncovered
      | none => .refused .domainUndefined []

/-- Independent semantic meaning of an `IntervalQuery`:
for every rational variable assignment `rho : String → CanonicalRat` enclosed by `q.env`,
evaluating `q.expr` at `rho` lies inside `q.claimedBound`. -/
@[expose] def IntervalQuery.SemanticMeaning (q : IntervalQuery) : Prop :=
  ∀ (rho : String → CanonicalRat),
    (∀ v iv, q.env.lookup v = some iv → rho v ∈ iv) →
    evalExpr rho q.expr ∈ q.claimedBound

/-- **Theorem (`intervalCheck_sound`)**:
Whenever `intervalCheck fuel q c = .ok`, the independent semantic interval enclosure
`IntervalQuery.SemanticMeaning q` holds for every point assignment `rho` in `q.env`. -/
theorem intervalCheck_sound (fuel : Nat) (q : IntervalQuery) (c : IntervalCert)
    (h : intervalCheck fuel q c = .ok) :
    IntervalQuery.SemanticMeaning q := by
  intro rho hEnv
  unfold intervalCheck at h
  cases c with
  | direct =>
    dsimp only at h
    cases hEval : evalInterval q.env q.expr with
    | none => rw [hEval] at h; contradiction
    | some comp =>
      rw [hEval] at h
      dsimp only at h
      split at h
      · rename_i hSub
        have hMem := evalInterval_sound q.env rho hEnv q.expr comp hEval
        rw [Interval.mem_iff] at hMem ⊢
        grind
      · contradiction
  | counterexample pt =>
    dsimp only at h
    split at h
    · contradiction
    · split at h
      · split at h <;> contradiction
      · contradiction

instance intervalJudge : Judge IntervalQuery IntervalCert where
  Clause := IntervalClause
  Meaning q _c := IntervalQuery.SemanticMeaning q
  check := intervalCheck
  sound := by intro r q c h; exact intervalCheck_sound r q c h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c r, intervalCheck r q c = .ok
  complete := by rintro q ⟨c, r, h⟩ _; exact ⟨c, r, h⟩
  mono := by intro r r' o c le hne; rfl

/-! ## Polynomial Sum-of-Squares (SOS) Judge (`sos@1`) & Multiplicative Graded-Lex (`grlex`) Order -/

namespace SOS

abbrev Monomial := List (Nat × Nat)

/-- Total degree $\sum_{(v, d) \in m} d$ of a monomial $m$. -/
@[expose] def monoTotalDeg : Monomial → Nat
  | [] => 0
  | (_, d) :: rest => d + monoTotalDeg rest

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

/-- Normalize an arbitrary `Monomial` list into canonical strictly-increasing-variable,
positive-exponent form by multiplying into `[]`. -/
@[expose] def monoNormalize (m : Monomial) : Monomial :=
  Monomial.mul m []

abbrev Monomial.normalize : Monomial → Monomial := monoNormalize

/-- Every entry in a normalized monomial has strictly positive exponent (`0 < d`). -/
@[expose] def monoAllPos : Monomial → Bool
  | [] => true
  | (_, d) :: rest => decide (0 < d) && monoAllPos rest

/-- Reverse-lexicographic tie-breaker on normalized monomials of equal total degree:
at the smallest variable index $v$ where the exponents of `m1` and `m2` differ,
`m1` is smaller than `m2` iff `m1` has the **larger** exponent on $x_v$ (so $x_0 < x_1 < x_2$,
preserving `LT(x_1 - x_0) = x_1` while being strictly invariant under monomial multiplication!). -/
@[expose] def monoRevLexLt : Monomial → Monomial → Bool
  | [], m2 =>
    match m2 with
    | [] => false
    | _ :: _ => false
  | (v1, d1) :: r1, m2 =>
    match m2 with
    | [] => true
    | (v2, d2) :: r2 =>
      if v1 < v2 then true
      else if v2 < v1 then false
      else if d2 < d1 then true
      else if d1 < d2 then false
      else monoRevLexLt r1 r2

/-- **Graded Lexicographic (`grlex`) Monomial Order**:
1. Compares total degrees `monoTotalDeg m1` vs `monoTotalDeg m2` first,
2. Breaks ties using `monoRevLexLt` on the normalized canonical monomials `monoNormalize m1` and `monoNormalize m2`. -/
@[expose] def Monomial.grlexLt (m1 m2 : Monomial) : Bool :=
  let deg1 := monoTotalDeg m1
  let deg2 := monoTotalDeg m2
  if deg1 < deg2 then true
  else if deg2 < deg1 then false
  else monoRevLexLt (monoNormalize m1) (monoNormalize m2)

/-- Canonical monomial order `Monomial.lt` is the multiplicative Graded-Lexicographic order `Monomial.grlexLt`. -/
abbrev Monomial.lt : Monomial → Monomial → Bool := Monomial.grlexLt

theorem monoTotalDeg_mulVarPow (v d : Nat) (m : Monomial) :
    monoTotalDeg (mulVarPow v d m) = d + monoTotalDeg m := by
  induction m with
  | nil =>
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · have h : d = 0 := beq_iff_eq.mp hd0
      subst h
      rfl
    · simp [hd0, monoTotalDeg]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · have h : d = 0 := beq_iff_eq.mp hd0
      subst h
      simp [monoTotalDeg]
    · simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1, monoTotalDeg]
      · by_cases h2 : v2 < v
        · simp only [h1, h2, ↓reduceIte, monoTotalDeg, ih]
          omega
        · simp only [h1, h2, ↓reduceIte, monoTotalDeg]
          omega

theorem monoTotalDeg_mul (m1 m2 : Monomial) :
    monoTotalDeg (Monomial.mul m1 m2) = monoTotalDeg m1 + monoTotalDeg m2 := by
  induction m1 with
  | nil => simp [Monomial.mul, monoTotalDeg]
  | cons hd tl ih =>
    rcases hd with ⟨v1, d1⟩
    simp only [Monomial.mul, monoTotalDeg_mulVarPow, ih, monoTotalDeg]
    omega

theorem mulVarPow_zero (v : Nat) (m : Monomial) :
    mulVarPow v 0 m = m := by
  cases m <;> rfl

theorem mulVarPow_add (v d1 d2 : Nat) (m : Monomial) :
    mulVarPow v d1 (mulVarPow v d2 m) = mulVarPow v (d1 + d2) m := by
  induction m with
  | nil => grind [mulVarPow]
  | cons hd tl ih =>
    rcases hd with ⟨v0, d0⟩
    grind [mulVarPow]

theorem mulVarPow_comm (v1 d1 v2 d2 : Nat) (m : Monomial) :
    mulVarPow v1 d1 (mulVarPow v2 d2 m) = mulVarPow v2 d2 (mulVarPow v1 d1 m) := by
  induction m with
  | nil => grind [mulVarPow]
  | cons hd tl ih =>
    rcases hd with ⟨v0, d0⟩
    grind [mulVarPow]

theorem monoMul_mulVarPow (m1 : Monomial) (v d : Nat) (m2 : Monomial) :
    Monomial.mul m1 (mulVarPow v d m2) = mulVarPow v d (Monomial.mul m1 m2) := by
  induction m1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v1, d1⟩
    simp only [Monomial.mul, ih, mulVarPow_comm]

theorem monoNormalize_mulVarPow (v d : Nat) (m : Monomial) :
    monoNormalize (mulVarPow v d m) = mulVarPow v d (monoNormalize m) := by
  unfold monoNormalize
  induction m with
  | nil =>
    by_cases hd0 : d == 0
    · have h : d = 0 := beq_iff_eq.mp hd0
      subst h
      rfl
    · simp [mulVarPow, hd0, Monomial.mul]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩
    by_cases hd0 : d == 0
    · have h : d = 0 := beq_iff_eq.mp hd0
      subst h
      simp [mulVarPow_zero]
    · simp only [mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1, Monomial.mul]
      · by_cases h2 : v2 < v
        · simp only [h1, h2, ↓reduceIte, Monomial.mul]
          rw [ih, mulVarPow_comm]
        · simp only [h1, h2, ↓reduceIte, Monomial.mul]
          have hv : v = v2 := by omega
          subst hv
          rw [mulVarPow_add]

theorem monoNormalize_mul (m1 m2 : Monomial) :
    monoNormalize (Monomial.mul m1 m2) = Monomial.mul m1 (monoNormalize m2) := by
  induction m1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v1, d1⟩
    simp only [Monomial.mul, monoNormalize_mulVarPow, ih]

theorem monoMul_comm_nil (m1 m2 : Monomial) :
    Monomial.mul m1 (monoNormalize m2) = Monomial.mul m2 (monoNormalize m1) := by
  unfold monoNormalize
  induction m1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v, d⟩
    simp only [Monomial.mul, monoMul_mulVarPow, ih]

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
    · have hd_pos : 0 < d := by
        cases d with
        | zero => contradiction
        | succ n => omega
      simp [hd0, monoAllPos, hd_pos]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩
    simp only [monoAllPos, Bool.and_eq_true, decide_eq_true_eq] at hm
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · simp [hd0, monoAllPos, hm.1, hm.2]
    · have hd_pos : 0 < d := by
        cases d with
        | zero => contradiction
        | succ n => omega
      simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1, monoAllPos, hd_pos, hm.1, hm.2]
      · by_cases h2 : v2 < v
        · simp [h1, h2, monoAllPos, hm.1, ih hm.2]
        · have hsum : 0 < d + d2 := by omega
          simp [h1, h2, monoAllPos, hsum, hm.2]

theorem monoAllPos_mul (m1 m2 : Monomial) (hm2 : monoAllPos m2 = true) :
    monoAllPos (Monomial.mul m1 m2) = true := by
  induction m1 with
  | nil => exact hm2
  | cons hd tl ih =>
    rcases hd with ⟨v, d⟩
    exact monoAllPos_mulVarPow v d _ ih

theorem monoAllPos_monoNormalize (m : Monomial) :
    monoAllPos (monoNormalize m) = true :=
  monoAllPos_mul m [] rfl

@[simp] theorem monoRevLexLt_cons_same (v d : Nat) (r1 r2 : Monomial) :
    monoRevLexLt ((v, d) :: r1) ((v, d) :: r2) = monoRevLexLt r1 r2 := by
  simp [monoRevLexLt]

theorem monoRevLexLt_mulVarPow (v d : Nat) (m1 m2 : Monomial)
    (hm1 : monoAllPos m1 = true)
    (h : monoRevLexLt m1 m2 = true) :
    monoRevLexLt (mulVarPow v d m1) (mulVarPow v d m2) = true := by
  induction m1 generalizing m2 with
  | nil =>
    cases m2 <;> simp [monoRevLexLt] at h
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨v1, d1⟩
    simp only [monoAllPos, Bool.and_eq_true, decide_eq_true_eq] at hm1
    have hd1_pos : 0 < d1 := hm1.1
    cases m2 with
    | nil =>
      by_cases hd0 : d == 0
      · simp [mulVarPow, hd0, monoRevLexLt]
      · simp only [mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : v < v1
        · simp [h1, monoRevLexLt]
        · by_cases h2 : v1 < v
          · simp [h1, h2, monoRevLexLt]
          · have hv : v = v1 := by omega
            subst hv
            have hlt : d < d + d1 := by omega
            simp [monoRevLexLt, hlt]
    | cons hd2 tl2 =>
      rcases hd2 with ⟨v2, d2⟩
      by_cases hd0 : d == 0
      · simp [mulVarPow, hd0, h]
      · simp only [mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
        by_cases hv12 : v1 < v2
        · by_cases hv_v1 : v < v1
          · have hv_v2 : v < v2 := Nat.lt_trans hv_v1 hv12
            simp [hv_v1, hv_v2, h]
          · by_cases hv1_v : v1 < v
            · by_cases hv_v2 : v < v2
              · simp [hv_v1, hv1_v, hv_v2, monoRevLexLt]
              · by_cases hv2_v : v2 < v
                · simp [hv_v1, hv1_v, hv_v2, hv2_v, monoRevLexLt, hv12]
                · simp [hv_v1, hv1_v, hv_v2, hv2_v, monoRevLexLt]
            · have hv : v = v1 := by omega
              subst hv
              have hv_v2 : v < v2 := hv12
              have hlt : d < d + d1 := by omega
              simp [hv_v2, monoRevLexLt, hlt]
        · have h' := h
          simp only [monoRevLexLt] at h'
          by_cases hv21 : v2 < v1
          · simp [hv12, hv21] at h'
          · have hv_eq : v1 = v2 := by omega
            subst hv_eq
            simp only [Nat.lt_irrefl, ↓reduceIte] at h'
            by_cases hv_v1 : v < v1
            · simp [hv_v1, h]
            · by_cases hv1_v : v1 < v
              · simp only [hv_v1, hv1_v, ↓reduceIte, monoRevLexLt, Nat.lt_irrefl]
                by_cases hd21 : d2 < d1
                · simp [hd21]
                · by_cases hd12 : d1 < d2
                  · simp [hd21, hd12] at h'
                  · simp only [hd21, hd12, ↓reduceIte] at h' ⊢
                    exact ih tl2 hm1.2 h'
              · have hv : v = v1 := by omega
                subst hv
                simp only [Nat.lt_irrefl, ↓reduceIte, monoRevLexLt]
                by_cases hd21 : d2 < d1
                · have hadd : d + d2 < d + d1 := by omega
                  simp [hadd]
                · by_cases hd12 : d1 < d2
                  · simp [hd21, hd12] at h'
                  · have hd_eq : d1 = d2 := by omega
                    subst hd_eq
                    simp only [Nat.lt_irrefl, ↓reduceIte] at h' ⊢
                    exact h'

theorem monoRevLexLt_mul_left (m m1 m2 : Monomial)
    (hm1 : monoAllPos m1 = true)
    (h : monoRevLexLt m1 m2 = true) :
    monoRevLexLt (Monomial.mul m m1) (Monomial.mul m m2) = true := by
  induction m with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨v, d⟩
    simp only [Monomial.mul]
    exact monoRevLexLt_mulVarPow v d _ _ (monoAllPos_mul tl m1 hm1) ih

/-- **Theorem (`grlex_mul_compatible`)**:
The Graded Lexicographic order `Monomial.grlexLt` (`Monomial.lt`) is strictly compatible with
monomial multiplication: for all monomials `m1`, `m2`, `m`,
`Monomial.grlexLt m1 m2 = true → Monomial.grlexLt (Monomial.mul m1 m) (Monomial.mul m2 m) = true`. -/
theorem grlex_mul_compatible (m1 m2 m : Monomial)
    (h : Monomial.grlexLt m1 m2 = true) :
    Monomial.grlexLt (Monomial.mul m1 m) (Monomial.mul m2 m) = true := by
  unfold Monomial.grlexLt at h ⊢
  rw [monoTotalDeg_mul, monoTotalDeg_mul]
  by_cases hdeg1 : monoTotalDeg m1 < monoTotalDeg m2
  · have hadd : monoTotalDeg m1 + monoTotalDeg m < monoTotalDeg m2 + monoTotalDeg m := by omega
    simp [hadd]
  · by_cases hdeg2 : monoTotalDeg m2 < monoTotalDeg m1
    · simp [hdeg1, hdeg2] at h
    · have h1 : ¬ (monoTotalDeg m1 + monoTotalDeg m < monoTotalDeg m2 + monoTotalDeg m) := by omega
      have h2 : ¬ (monoTotalDeg m2 + monoTotalDeg m < monoTotalDeg m1 + monoTotalDeg m) := by omega
      simp only [hdeg1, hdeg2, ↓reduceIte] at h
      simp only [h1, h2, ↓reduceIte]
      rw [monoNormalize_mul_comm m1 m, monoNormalize_mul_comm m2 m]
      rw [monoNormalize_mul m m1, monoNormalize_mul m m2]
      exact monoRevLexLt_mul_left m (monoNormalize m1) (monoNormalize m2) (monoAllPos_monoNormalize m1) h

/-- Left-multiplication compatibility for `Monomial.grlexLt`. -/
theorem grlex_mul_left_compatible (m m1 m2 : Monomial)
    (h : Monomial.grlexLt m1 m2 = true) :
    Monomial.grlexLt (Monomial.mul m m1) (Monomial.mul m m2) = true := by
  unfold Monomial.grlexLt at h ⊢
  rw [monoTotalDeg_mul, monoTotalDeg_mul]
  by_cases hdeg1 : monoTotalDeg m1 < monoTotalDeg m2
  · have hadd : monoTotalDeg m + monoTotalDeg m1 < monoTotalDeg m + monoTotalDeg m2 := by omega
    simp [hadd]
  · by_cases hdeg2 : monoTotalDeg m2 < monoTotalDeg m1
    · simp [hdeg1, hdeg2] at h
    · have h1 : ¬ (monoTotalDeg m + monoTotalDeg m1 < monoTotalDeg m + monoTotalDeg m2) := by omega
      have h2 : ¬ (monoTotalDeg m + monoTotalDeg m2 < monoTotalDeg m + monoTotalDeg m1) := by omega
      simp only [hdeg1, hdeg2, ↓reduceIte] at h
      simp only [h1, h2, ↓reduceIte]
      rw [monoNormalize_mul m m1, monoNormalize_mul m m2]
      exact monoRevLexLt_mul_left m (monoNormalize m1) (monoNormalize m2) (monoAllPos_monoNormalize m1) h

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
    else
      (mNorm', c') :: insertNormalizedTerm m c rest

@[expose] def insertTerm (m : Monomial) (c : CanonicalRat)
    (ts : List (Monomial × CanonicalRat)) : List (Monomial × CanonicalRat) :=
  let mNorm := Monomial.normalize m
  insertNormalizedTerm mNorm c ts

structure Poly where
  terms : List (Monomial × CanonicalRat)
  deriving @[expose] DecidableEq, Repr

/-- Alias `SparsePoly` for `Poly` (sparse multivariate polynomials over `CanonicalRat`). -/
abbrev SparsePoly := Poly

/-! ### Independent Polynomial Ring Evaluation Semantics (`Monomial.eval`, `Poly.eval`, `SparsePoly.eval`) -/

/-- Exact rational exponentiation $b^e$. -/
@[expose] def ratPow (b : CanonicalRat) : Nat → CanonicalRat
  | 0 => 1
  | n + 1 => b * ratPow b n

theorem ratPow_add (b : CanonicalRat) (d1 d2 : Nat) :
    ratPow b (d1 + d2) = ratPow b d1 * ratPow b d2 := by
  induction d1 with
  | zero => simp [ratPow]
  | succ n ih =>
    simp only [Nat.succ_add, ratPow, ih]
    grind

/-- Evaluate a monomial $\prod_{(v, d) \in m} \rho(v)^d$ at assignment $\rho : \mathbb{N} \to \mathbb{Q}$. -/
@[expose] def Monomial.eval (ρ : Nat → CanonicalRat) : Monomial → CanonicalRat
  | [] => 1
  | (v, d) :: rest => ratPow (ρ v) d * Monomial.eval ρ rest

theorem eval_mulVarPow (ρ : Nat → CanonicalRat) (v d : Nat) (m : Monomial) :
    Monomial.eval ρ (mulVarPow v d m) = ratPow (ρ v) d * Monomial.eval ρ m := by
  induction m with
  | nil =>
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · have h : d = 0 := beq_iff_eq.mp hd0
      subst h
      simp [Monomial.eval, ratPow]
    · simp [hd0, Monomial.eval]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · have h : d = 0 := beq_iff_eq.mp hd0
      subst h
      simp [Monomial.eval, ratPow]
    · simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1, Monomial.eval]
      · by_cases h2 : v2 < v
        · simp only [h1, h2, ↓reduceIte, Monomial.eval, ih]
          grind
        · simp only [h1, h2, ↓reduceIte, Monomial.eval]
          have hv : v = v2 := by omega
          subst hv
          rw [ratPow_add]
          grind

theorem Monomial.eval_mul (ρ : Nat → CanonicalRat) (m1 m2 : Monomial) :
    Monomial.eval ρ (Monomial.mul m1 m2) = Monomial.eval ρ m1 * Monomial.eval ρ m2 := by
  induction m1 with
  | nil => simp [Monomial.mul, Monomial.eval]
  | cons hd tl ih =>
    rcases hd with ⟨v1, d1⟩
    simp only [Monomial.mul, eval_mulVarPow, ih, Monomial.eval]
    grind

@[simp] theorem Monomial.eval_normalize (ρ : Nat → CanonicalRat) (m : Monomial) :
    Monomial.eval ρ (monoNormalize m) = Monomial.eval ρ m := by
  unfold monoNormalize
  rw [Monomial.eval_mul]
  simp [Monomial.eval]

/-- Evaluate a list of `(Monomial × CanonicalRat)` terms at variable assignment `ρ`. -/
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
    · have h0 : c = 0 := beq_iff_eq.mp hc
      subst h0
      simp [evalTerms]
      grind
    · simp [hc, evalTerms]
  | cons hd tl ih =>
    rcases hd with ⟨m', c'⟩
    simp only [insertNormalizedTerm, Monomial.normalize]
    have hmNorm' : Monomial.eval ρ (monoNormalize m') = Monomial.eval ρ m' :=
      Monomial.eval_normalize ρ m'
    by_cases hm : m == monoNormalize m'
    · have hmeq : m = monoNormalize m' := beq_iff_eq.mp hm
      simp only [hm, ↓reduceIte]
      by_cases hsum : c + c' == 0
      · have hs0 : c + c' = 0 := beq_iff_eq.mp hsum
        simp only [hsum, ↓reduceIte, evalTerms]
        have hEvalEq : Monomial.eval ρ m = Monomial.eval ρ m' := by rw [hmeq, hmNorm']
        have hlin : c * Monomial.eval ρ m + c' * Monomial.eval ρ m' = (c + c') * Monomial.eval ρ m' := by grind
        grind
      · simp only [hsum, Bool.false_eq_true, ↓reduceIte, evalTerms]
        have hEvalEq : Monomial.eval ρ m = Monomial.eval ρ m' := by rw [hmeq, hmNorm']
        grind
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt : Monomial.lt m (monoNormalize m')
      · simp only [hlt, ↓reduceIte]
        by_cases hc : c == 0
        · have h0 : c = 0 := beq_iff_eq.mp hc
          subst h0
          simp [evalTerms, hmNorm']
          grind
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, evalTerms, hmNorm']
      · simp only [hlt, Bool.false_eq_true, ↓reduceIte, evalTerms, hmNorm', ih]
        grind

theorem evalTerms_insertTerm (ρ : Nat → CanonicalRat) (m : Monomial) (c : CanonicalRat)
    (ts : List (Monomial × CanonicalRat)) :
    evalTerms ρ (insertTerm m c ts) = c * Monomial.eval ρ m + evalTerms ρ ts := by
  unfold insertTerm Monomial.normalize
  rw [evalTerms_insertNormalizedTerm, Monomial.eval_normalize]

namespace Poly

@[expose] def zero : Poly := ⟨[]⟩

@[expose] def one : Poly := ⟨[([], 1)]⟩

@[expose] def isZero (p : Poly) : Bool :=
  p.terms.isEmpty

@[expose] def add (p1 p2 : Poly) : Poly :=
  ⟨p2.terms.foldl (fun acc (m, c) => insertTerm m c acc) p1.terms⟩

@[expose] def neg (p : Poly) : Poly :=
  ⟨p.terms.map fun (m, c) => (m, -c)⟩

@[expose] def sub (p1 p2 : Poly) : Poly :=
  add p1 (neg p2)

@[expose] def scale (c : CanonicalRat) (p : Poly) : Poly :=
  if c == 0 then zero
  else ⟨p.terms.map fun (m, k) => (m, c * k)⟩

@[expose] def mulTerm (t : Monomial × CanonicalRat) (p : Poly) : Poly :=
  if t.2 == 0 then zero
  else ⟨p.terms.map fun (m, c) => (Monomial.mul t.1 m, t.2 * c)⟩

@[expose] def mul (p1 p2 : Poly) : Poly :=
  p1.terms.foldl (fun acc t => add acc (mulTerm t p2)) zero

@[expose] def sqr (p : Poly) : Poly :=
  mul p p

/-- Evaluate a sparse multivariate polynomial `p : Poly` at variable assignment `ρ : Nat → CanonicalRat`. -/
@[expose] def eval (ρ : Nat → CanonicalRat) (p : Poly) : CanonicalRat :=
  evalTerms ρ p.terms

@[simp] theorem eval_zero (ρ : Nat → CanonicalRat) : Poly.zero.eval ρ = 0 := rfl

@[simp] theorem eval_one (ρ : Nat → CanonicalRat) : Poly.one.eval ρ = 1 := by
  simp [Poly.one, Poly.eval, evalTerms, Monomial.eval]
  grind

theorem eval_isZero (ρ : Nat → CanonicalRat) (p : Poly) (h : p.isZero = true) :
    p.eval ρ = 0 := by
  rcases p with ⟨ts⟩
  cases ts with
  | nil => rfl
  | cons _ _ => simp [Poly.isZero] at h

theorem evalTerms_foldl_insert (ρ : Nat → CanonicalRat)
    (ts2 ts1 : List (Monomial × CanonicalRat)) :
    evalTerms ρ (ts2.foldl (fun acc (m, c) => insertTerm m c acc) ts1) =
      evalTerms ρ ts1 + evalTerms ρ ts2 := by
  induction ts2 generalizing ts1 with
  | nil =>
    simp [evalTerms]
    grind
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [List.foldl_cons, ih, evalTerms_insertTerm, evalTerms]
    grind

/-- **Theorem (`Poly.eval_add`)**: Polynomial addition commutes with evaluation. -/
@[simp] theorem eval_add (ρ : Nat → CanonicalRat) (p1 p2 : Poly) :
    (Poly.add p1 p2).eval ρ = p1.eval ρ + p2.eval ρ := by
  unfold Poly.add Poly.eval
  exact evalTerms_foldl_insert ρ p2.terms p1.terms

/-- **Theorem (`Poly.eval_neg`)**: Polynomial negation commutes with evaluation. -/
@[simp] theorem eval_neg (ρ : Nat → CanonicalRat) (p : Poly) :
    (Poly.neg p).eval ρ = -(p.eval ρ) := by
  rcases p with ⟨ts⟩
  unfold Poly.neg Poly.eval
  dsimp only
  induction ts with
  | nil => simp [evalTerms]
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [List.map_cons, evalTerms, ih]
    grind

/-- **Theorem (`Poly.eval_sub`)**: Polynomial subtraction commutes with evaluation. -/
@[simp] theorem eval_sub (ρ : Nat → CanonicalRat) (p1 p2 : Poly) :
    (Poly.sub p1 p2).eval ρ = p1.eval ρ - p2.eval ρ := by
  unfold Poly.sub
  rw [eval_add, eval_neg]
  grind

/-- **Theorem (`Poly.eval_scale`)**: Scalar multiplication commutes with evaluation. -/
@[simp] theorem eval_scale (ρ : Nat → CanonicalRat) (c : CanonicalRat) (p : Poly) :
    (Poly.scale c p).eval ρ = c * p.eval ρ := by
  rcases p with ⟨ts⟩
  unfold Poly.scale Poly.eval
  by_cases hc : c == 0
  · have h0 : c = 0 := beq_iff_eq.mp hc
    subst h0
    simp [Poly.zero, evalTerms]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    induction ts with
    | nil => simp [evalTerms]
    | cons hd tl ih =>
      rcases hd with ⟨m, k⟩
      simp only [List.map_cons, evalTerms, ih]
      grind

theorem eval_mulTerm (ρ : Nat → CanonicalRat) (t : Monomial × CanonicalRat) (p : Poly) :
    (Poly.mulTerm t p).eval ρ = (t.2 * Monomial.eval ρ t.1) * p.eval ρ := by
  rcases p with ⟨ts⟩
  rcases t with ⟨mt, ct⟩
  unfold Poly.mulTerm Poly.eval
  dsimp only
  by_cases hc : ct == 0
  · have h0 : ct = 0 := beq_iff_eq.mp hc
    subst h0
    simp [Poly.zero, evalTerms]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    induction ts with
    | nil => simp [evalTerms]
    | cons hd tl ih =>
      rcases hd with ⟨m, c⟩
      simp only [List.map_cons, evalTerms, Monomial.eval_mul, ih]
      grind

theorem eval_foldl_mulTerm (ρ : Nat → CanonicalRat)
    (ts1 : List (Monomial × CanonicalRat)) (p2 acc : Poly) :
    (ts1.foldl (fun a t => Poly.add a (Poly.mulTerm t p2)) acc).eval ρ =
      acc.eval ρ + evalTerms ρ ts1 * p2.eval ρ := by
  induction ts1 generalizing acc with
  | nil => simp [evalTerms]; grind
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [List.foldl_cons, ih, eval_add, eval_mulTerm, evalTerms]
    grind

/-- **Theorem (`Poly.eval_mul`)**: Polynomial multiplication commutes with evaluation. -/
@[simp] theorem eval_mul (ρ : Nat → CanonicalRat) (p1 p2 : Poly) :
    (Poly.mul p1 p2).eval ρ = p1.eval ρ * p2.eval ρ := by
  unfold Poly.mul
  rw [eval_foldl_mulTerm, eval_zero]
  unfold Poly.eval
  grind

/-- **Theorem (`Poly.eval_sqr`)**: Polynomial squaring evaluates to the square `(p.eval ρ) * (p.eval ρ)`. -/
@[simp] theorem eval_sqr (ρ : Nat → CanonicalRat) (p : Poly) :
    (Poly.sqr p).eval ρ = p.eval ρ * p.eval ρ := by
  unfold Poly.sqr
  exact eval_mul ρ p p

/-- **Theorem (`Poly.eval_sq_nonneg`)**: Every squared polynomial evaluates to a non-negative rational. -/
theorem eval_sq_nonneg (ρ : Nat → CanonicalRat) (p : Poly) :
    0 ≤ (Poly.sqr p).eval ρ := by
  rw [eval_sqr]
  exact Interval.rat_sq_nonneg (p.eval ρ)

end Poly

namespace SparsePoly

/-- Evaluate a sparse polynomial `p : SparsePoly` at variable assignment `ρ`. -/
@[expose] def eval (ρ : Nat → CanonicalRat) (p : SparsePoly) : CanonicalRat :=
  Poly.eval ρ p

theorem eval_add (ρ : Nat → CanonicalRat) (p1 p2 : SparsePoly) :
    SparsePoly.eval ρ (Poly.add p1 p2) = SparsePoly.eval ρ p1 + SparsePoly.eval ρ p2 :=
  Poly.eval_add ρ p1 p2

theorem eval_sub (ρ : Nat → CanonicalRat) (p1 p2 : SparsePoly) :
    SparsePoly.eval ρ (Poly.sub p1 p2) = SparsePoly.eval ρ p1 - SparsePoly.eval ρ p2 :=
  Poly.eval_sub ρ p1 p2

theorem eval_mul (ρ : Nat → CanonicalRat) (p1 p2 : SparsePoly) :
    SparsePoly.eval ρ (Poly.mul p1 p2) = SparsePoly.eval ρ p1 * SparsePoly.eval ρ p2 :=
  Poly.eval_mul ρ p1 p2

theorem eval_neg (ρ : Nat → CanonicalRat) (p : SparsePoly) :
    SparsePoly.eval ρ (Poly.neg p) = -(SparsePoly.eval ρ p) :=
  Poly.eval_neg ρ p

theorem eval_sq_nonneg (ρ : Nat → CanonicalRat) (p : SparsePoly) :
    0 ≤ SparsePoly.eval ρ (Poly.sqr p) :=
  Poly.eval_sq_nonneg ρ p

end SparsePoly

structure SOSPoly where
  terms : List (CanonicalRat × Poly)
  deriving @[expose] DecidableEq, Repr

namespace SOSPoly

@[expose] def expand (sos : SOSPoly) : Poly :=
  sos.terms.foldl (fun acc (c, p) => Poly.add acc (Poly.scale c (Poly.sqr p))) Poly.zero

@[expose] def allCoeffsPos (sos : SOSPoly) : Bool :=
  sos.terms.all fun (c, _) => decide (0 < c)

theorem eval_foldl_expand_nonneg (ρ : Nat → CanonicalRat)
    (ts : List (CanonicalRat × Poly)) (acc : Poly)
    (hAcc : 0 ≤ acc.eval ρ)
    (hPos : (ts.all fun (c, _) => decide (0 < c)) = true) :
    0 ≤ (ts.foldl (fun a (c, p) => Poly.add a (Poly.scale c (Poly.sqr p))) acc).eval ρ := by
  induction ts generalizing acc with
  | nil => exact hAcc
  | cons hd tl ih =>
    rcases hd with ⟨c, p⟩
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hPos
    simp only [List.foldl_cons]
    apply ih
    · rw [Poly.eval_add, Poly.eval_scale]
      have hsq := Poly.eval_sq_nonneg ρ p
      have hc : 0 ≤ c := by grind
      have hmul := Rat.mul_le_mul_of_nonneg_left hsq hc
      grind
    · exact hPos.2

/-- **Theorem (`SOSPoly.eval_expand_nonneg`)**:
Any `SOSPoly` whose weights satisfy `allCoeffsPos = true` evaluates to `≥ 0` at every assignment `ρ`. -/
theorem eval_expand_nonneg (ρ : Nat → CanonicalRat) (sos : SOSPoly)
    (hPos : sos.allCoeffsPos = true) :
    0 ≤ sos.expand.eval ρ := by
  unfold expand allCoeffsPos at *
  exact eval_foldl_expand_nonneg ρ sos.terms Poly.zero (by simp) hPos

end SOSPoly

structure SOSQuery where
  goal : Poly
  ineqs : List Poly
  eqs : List Poly
  deriving @[expose] DecidableEq, Repr

structure SOSCert where
  sigma0 : SOSPoly
  sigmas : List (SOSPoly × Nat)
  lambdas : List (Poly × Nat)
  deriving @[expose] DecidableEq, Repr

inductive SOSClause where
  | invalidSOSWeights
  | identityMismatch (residual : Poly)
  deriving @[expose] DecidableEq, Repr

@[expose] def sosCheck (_fuel : Nat) (q : SOSQuery) (c : SOSCert) : Judge.Verdict SOSClause :=
  if !c.sigma0.allCoeffsPos then
    .refused .invalidSOSWeights []
  else if !c.sigmas.all (fun (s, _) => s.allCoeffsPos) then
    .refused .invalidSOSWeights []
  else if !c.sigmas.all (fun (_, idx) => decide (idx < q.ineqs.length)) then
    .refused .invalidSOSWeights []
  else if !c.lambdas.all (fun (_, idx) => decide (idx < q.eqs.length)) then
    .refused .invalidSOSWeights []
  else
    let term0 := c.sigma0.expand
    let termIneq := c.sigmas.foldl (fun acc (sig, idx) =>
      match q.ineqs[idx]? with
      | some gi => Poly.add acc (Poly.mul sig.expand gi)
      | none => acc) Poly.zero
    let termEq := c.lambdas.foldl (fun acc (lam, idx) =>
      match q.eqs[idx]? with
      | some hj => Poly.add acc (Poly.mul lam hj)
      | none => acc) Poly.zero
    let certPoly := Poly.add term0 (Poly.add termIneq termEq)
    let diff := Poly.sub q.goal certPoly
    if diff.isZero then .ok
    else .refused (.identityMismatch diff) []

/-- Independent semantic meaning of an `SOSQuery`:
for every rational variable assignment `ρ : Nat → CanonicalRat`, whenever all inequality generators
`g ∈ q.ineqs` evaluate to `≥ 0` and all equality generators `h ∈ q.eqs` evaluate to `= 0`,
the target polynomial `q.goal` evaluates to `≥ 0`. -/
@[expose] def SOSQuery.SemanticMeaning (q : SOSQuery) : Prop :=
  ∀ (ρ : Nat → CanonicalRat),
    (∀ g ∈ q.ineqs, 0 ≤ g.eval ρ) →
    (∀ h ∈ q.eqs, h.eval ρ = 0) →
    0 ≤ q.goal.eval ρ

theorem eval_foldl_sigmas_nonneg (ρ : Nat → CanonicalRat) (ineqs : List Poly)
    (hIneqs : ∀ g ∈ ineqs, 0 ≤ g.eval ρ)
    (sigmas : List (SOSPoly × Nat)) (acc : Poly)
    (hAcc : 0 ≤ acc.eval ρ)
    (hPos : (sigmas.all fun (s, _) => s.allCoeffsPos) = true) :
    0 ≤ (sigmas.foldl (fun a (sig, idx) =>
      match ineqs[idx]? with
      | some gi => Poly.add a (Poly.mul sig.expand gi)
      | none => a) acc).eval ρ := by
  induction sigmas generalizing acc with
  | nil => exact hAcc
  | cons hd tl ih =>
    rcases hd with ⟨sig, idx⟩
    simp only [List.all_cons, Bool.and_eq_true] at hPos
    simp only [List.foldl_cons]
    cases hgi : ineqs[idx]? with
    | none =>
      exact ih acc hAcc hPos.2
    | some gi =>
      apply ih
      · rw [Poly.eval_add, Poly.eval_mul]
        have hsig := SOSPoly.eval_expand_nonneg ρ sig hPos.1
        have hmem : gi ∈ ineqs := List.mem_of_getElem? hgi
        have hgi_nonneg := hIneqs gi hmem
        have hmul := Rat.mul_le_mul_of_nonneg_left hgi_nonneg hsig
        grind
      · exact hPos.2

theorem eval_foldl_lambdas_zero (ρ : Nat → CanonicalRat) (eqs : List Poly)
    (hEqs : ∀ h ∈ eqs, h.eval ρ = 0)
    (lambdas : List (Poly × Nat)) (acc : Poly)
    (hAcc : acc.eval ρ = 0) :
    (lambdas.foldl (fun a (lam, idx) =>
      match eqs[idx]? with
      | some hj => Poly.add a (Poly.mul lam hj)
      | none => a) acc).eval ρ = 0 := by
  induction lambdas generalizing acc with
  | nil => exact hAcc
  | cons hd tl ih =>
    rcases hd with ⟨lam, idx⟩
    simp only [List.foldl_cons]
    cases hhj : eqs[idx]? with
    | none =>
      exact ih acc hAcc
    | some hj =>
      apply ih
      rw [Poly.eval_add, Poly.eval_mul, hAcc]
      have hmem : hj ∈ eqs := List.mem_of_getElem? hhj
      rw [hEqs hj hmem]
      grind

/-- **Theorem (`sosCheck_sound`)**:
Whenever `sosCheck fuel q c = .ok`, the independent polynomial non-negativity claim
`SOSQuery.SemanticMeaning q` holds for every assignment `ρ : Nat → CanonicalRat`. -/
theorem sosCheck_sound (fuel : Nat) (q : SOSQuery) (c : SOSCert)
    (h : sosCheck fuel q c = .ok) :
    SOSQuery.SemanticMeaning q := by
  intro ρ hIneqs hEqs
  unfold sosCheck at h
  by_cases hPos0 : c.sigma0.allCoeffsPos = true
  · simp only [hPos0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hPosS : (c.sigmas.all fun (s, _) => s.allCoeffsPos) = true
    · simp only [hPosS, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hBndS : (c.sigmas.all fun (_, idx) => decide (idx < q.ineqs.length)) = true
      · simp only [hBndS, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hBndL : (c.lambdas.all fun (_, idx) => decide (idx < q.eqs.length)) = true
        · simp only [hBndL, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · rename_i hDiffZero
            have hSub := Poly.eval_isZero ρ _ hDiffZero
            rw [Poly.eval_sub, Poly.eval_add, Poly.eval_add] at hSub
            have h0 := SOSPoly.eval_expand_nonneg ρ c.sigma0 hPos0
            have hIneq := eval_foldl_sigmas_nonneg ρ q.ineqs hIneqs c.sigmas Poly.zero (by simp) hPosS
            have hEq := eval_foldl_lambdas_zero ρ q.eqs hEqs c.lambdas Poly.zero (by simp)
            grind
          · contradiction
        · simp [hBndL] at h
      · simp [hBndS] at h
    · simp [hPosS] at h
  · simp [hPos0] at h

/-- **Theorem (`insertTerm_normalizes_and_sosCheck_rejects_oob`)**:
1. `insertTerm` normalizes unreduced monomials (such as `[(0, 1), (1, 0)]` vs `[(0, 1)]`) so they
   cancel identically instead of coexisting as duplicate monomials under `grlexLt`.
2. `sosCheck` strictly refuses certificates with out-of-bounds `sigmas` (`idx ≥ q.ineqs.length`)
   or `lambdas` (`idx ≥ q.eqs.length`) indices instead of silently substituting `Poly.zero`. -/
-- fixture kept in place (2026-11-04): a 13-line closed evaluation; worth a pre-push run; it moves to Obend/Teeth/ with the lane edit that owns this file
example :
    insertTerm [(0, 1), (1, 0)] 1 (insertTerm [(0, 1)] (-1) []) = [] ∧
    sosCheck 10
      { goal := Poly.one, ineqs := [], eqs := [] }
      { sigma0 := { terms := [(1, Poly.one)] }
      , sigmas := [({ terms := [(1, Poly.one)] }, 0)]
      , lambdas := [] } = .refused .invalidSOSWeights [] ∧
    sosCheck 10
      { goal := Poly.one, ineqs := [], eqs := [] }
      { sigma0 := { terms := [(1, Poly.one)] }
      , sigmas := []
      , lambdas := [(Poly.one, 0)] } = .refused .invalidSOSWeights [] := by
  decide +kernel

instance sosJudge : Judge SOSQuery SOSCert where
  Clause := SOSClause
  Meaning q _c := SOSQuery.SemanticMeaning q
  check := sosCheck
  sound := by intro r q c h; exact sosCheck_sound r q c h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c r, sosCheck r q c = .ok
  complete := by rintro q ⟨c, r, h⟩ _; exact ⟨c, r, h⟩
  mono := by intro r r' o c le hne; rfl

end SOS

end Obend.Judge
end
