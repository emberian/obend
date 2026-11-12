module
/-
# Obend.Hardware.CircuitDae — Index-1 MNA Circuit DAE Judge (`"mna-dae@1"`) & 5-Cell SiC FCML Hybrid Balance
1. **Rational MNA Linear Algebra & Gram Congruence (`§1`)**:
   - Nodal/branch inner products (`vecDotN`), matrix-vector products (`matVecMulN`), quadratic forms
     (`quadFormN`), stored electromagnetic/capacitive energy $\frac{1}{2} x^\top C x$ (`mnaStoredEnergy`),
     and rank-1 congruence factorizations $M = \sum_r w_r \ell_r \ell_r^\top$ (`gramCongruence_symm_and_psd`,
     `quadFormN_nonneg_of_symSum_gram`).
2. **Index-1 MNA Circuit DAE Enclosure & Unconditional Discrete Energy Passivity (`§2`)**:
   - Passive + monotone-nonlinear MNA systems $C \dot{x}(t) + G x(t) + i_{\text{nl}}(x(t)) = B u(t)$
     supporting non-symmetric MNA inductor/transformer stamps ($G + G^\top \succeq 0$) and 2-terminal
     sector-monotone diode/MOSFET channels (`MnaNonlinearBranch`, `stampNonlinearCurrents_passive`).
   - Backward-Euler & Trapezoidal step residual interval enclosure (`checkMnaStepEnclosure`,
     `checkMnaStepEnclosure_sound`) and unconditional discrete energy passivity
     (`mna_backward_euler_energy_dissipative`, `mna_trapezoidal_energy_dissipative`,
     `mna_backward_euler_trace_energy_monotone`).
3. **Inhabited `Obend.Judge` & `"mna-dae@1"` `Judge.Format` (`§3`)**:
   - `mnaCircuitDaeJudge : Judge MnaDaeProblem MnaDaeCert` (`Fragment := fun _ => True`, `refutes`
     rejecting negative diagonal capacitance/conductance, non-passive nonlinear steps, and DAE residual
     violations) + kernel-reducible wire format `mnaCircuitDaeFormat` (`"mna-dae@1"`).
4. **True 5-Cell (6-Level) SiC FCML Switched-Capacitor Hybrid Balance (`§4–§5`)**:
   - Exact switched-capacitor KCL recurrence $C_k \frac{dv_{C_k}}{dt} = (s_{k+1} - s_k) i_L$ across
     $s \in \{0,1\}^5$ (`FcmlSwitchState5`) with nominal ladder $v_{C_k}^* = \frac{k}{5} V_{\text{dc}}$,
     power conservation (`fcml_instantaneous_power_conservation`), FET blocking bounds
     (`fcml_cell_blocking_bounded_by_unbalance`), symmetric 5-phase PSP zero-net-charge-drift
     (`fcml_psp_nominal_zero_drift`), and saturated active duty-trim Lyapunov contraction
     (`fcml_active_trim_contracts_unbalance`).
-/
public import Obend.Judge.Class
public import Obend.Analysis.RealAnalysis
public import Obend.Analysis.SosLyapunov
public section
namespace Obend.Hardware.CircuitDae
open Obend
open Obend.Analysis
set_option autoImplicit false
/-! ## 1. Finite-Dimensional Rational MNA Linear Algebra & Gram Congruence -/
/-- Rational magnitude $|x|$ over `CanonicalRat`. -/
def ratAbs (x : CanonicalRat) : CanonicalRat := if 0 ≤ x then x else -x
theorem ratAbs_nonneg (x : CanonicalRat) : 0 ≤ ratAbs x := by unfold ratAbs; split <;> grind
theorem ratAbs_le_iff (x b : CanonicalRat) : ratAbs x ≤ b ↔ (-b ≤ x ∧ x ≤ b) := by unfold ratAbs; split <;> grind
/-- Entry `i` of a rational vector `v` and `(i, j)` of matrix `M` (`0` out of bounds). -/
def vecEntry (v : List CanonicalRat) (i : Nat) : CanonicalRat := v.getD i 0
def matEntry (M : List (List CanonicalRat)) (i j : Nat) : CanonicalRat := (M.getD i []).getD j 0
/-- Structural vector constructors `[f s, ..., f (s+c-1)]` and `[f 0, ..., f (n-1)]`. -/
def mkVecFrom (s : Nat) : Nat → (Nat → CanonicalRat) → List CanonicalRat
  | 0, _ => [] | c + 1, f => f s :: mkVecFrom (s + 1) c f
def mkVec (n : Nat) (f : Nat → CanonicalRat) : List CanonicalRat := mkVecFrom 0 n f
private theorem vecEntry_mkVecFrom (f : Nat → CanonicalRat) :
    ∀ (c s k : Nat), k < c → vecEntry (mkVecFrom s c f) k = f (s + k)
  | 0, _, _, hk => by omega
  | c + 1, s, 0, _ => by simp [mkVecFrom, vecEntry]
  | c + 1, s, k + 1, hk => by
    have ih := vecEntry_mkVecFrom f c (s + 1) k (by omega)
    simp only [mkVecFrom, vecEntry, List.getD_cons_succ] at ih ⊢
    rw [ih]; congr 1; omega
theorem vecEntry_mkVec (n : Nat) (f : Nat → CanonicalRat) (i : Nat) (hi : i < n) :
    vecEntry (mkVec n f) i = f i := by
  simpa [mkVec] using vecEntry_mkVecFrom f n 0 i hi
/-- Structural finite sum $\sum_{i=0}^{n-1} f(i)$. -/
def sumUpTo : Nat → (Nat → CanonicalRat) → CanonicalRat
  | 0, _ => 0
  | k + 1, f => sumUpTo k f + f k
theorem sumUpTo_congr (n : Nat) (f g : Nat → CanonicalRat)
    (h : ∀ i, i < n → f i = g i) : sumUpTo n f = sumUpTo n g := by
  induction n with
  | zero => rfl
  | succ k ih => dsimp [sumUpTo]; rw [ih (fun i hi => h i (by omega)), h k (by omega)]
theorem sumUpTo_add (n : Nat) (f g : Nat → CanonicalRat) :
    sumUpTo n (fun i => f i + g i) = sumUpTo n f + sumUpTo n g := by
  induction n with | zero => dsimp [sumUpTo]; grind | succ k ih => dsimp [sumUpTo]; rw [ih]; grind
theorem sumUpTo_sub (n : Nat) (f g : Nat → CanonicalRat) :
    sumUpTo n (fun i => f i - g i) = sumUpTo n f - sumUpTo n g := by
  induction n with | zero => dsimp [sumUpTo]; grind | succ k ih => dsimp [sumUpTo]; rw [ih]; grind
theorem sumUpTo_scale (n : Nat) (c : CanonicalRat) (f : Nat → CanonicalRat) :
    sumUpTo n (fun i => c * f i) = c * sumUpTo n f := by
  induction n with | zero => dsimp [sumUpTo]; grind | succ k ih => dsimp [sumUpTo]; rw [ih]; grind
theorem sumUpTo_nonneg (n : Nat) (f : Nat → CanonicalRat)
    (h : ∀ i, i < n → 0 ≤ f i) : 0 ≤ sumUpTo n f := by
  induction n with
  | zero => dsimp [sumUpTo]; grind
  | succ k ih =>
    dsimp [sumUpTo]; have := ih (fun i hi => h i (by omega)); have := h k (by omega); grind
theorem sumUpTo_zero (n : Nat) : sumUpTo n (fun _ => 0) = 0 := by
  induction n with | zero => rfl | succ k ih => dsimp [sumUpTo]; rw [ih]; grind
theorem sumUpTo_comm (n m : Nat) (h : Nat → Nat → CanonicalRat) :
    sumUpTo n (fun i => sumUpTo m (fun j => h i j)) =
      sumUpTo m (fun j => sumUpTo n (fun i => h i j)) := by
  induction n with
  | zero => dsimp [sumUpTo]; symm; exact sumUpTo_zero m
  | succ k ih => dsimp [sumUpTo]; rw [ih, ← sumUpTo_add]
theorem sumUpTo_delta (n k : Nat) (c : CanonicalRat) (hk : k < n) :
    sumUpTo n (fun i => if i = k then c else 0) = c := by
  induction n with
  | zero => omega
  | succ m ih =>
    dsimp [sumUpTo]
    by_cases hmk : m = k
    · subst hmk
      have hZero : sumUpTo m (fun i => if i = m then c else 0) = 0 := by
        rw [sumUpTo_congr m _ (fun _ => 0) (fun i hi => by simp [Nat.ne_of_lt hi])]
        exact sumUpTo_zero m
      rw [hZero]; simp; grind
    · rw [ih (by omega)]; simp [hmk]; grind
/-- Inner product $u^\top v = \sum_{i=0}^{n-1} u_i v_i$ and rational vector operations. -/
def vecDotN (n : Nat) (u v : List CanonicalRat) : CanonicalRat := sumUpTo n (fun i => vecEntry u i * vecEntry v i)
def vecAddN (n : Nat) (u v : List CanonicalRat) : List CanonicalRat := mkVec n (fun i => vecEntry u i + vecEntry v i)
def vecSubN (n : Nat) (u v : List CanonicalRat) : List CanonicalRat := mkVec n (fun i => vecEntry u i - vecEntry v i)
def vecScaleN (n : Nat) (c : CanonicalRat) (v : List CanonicalRat) : List CanonicalRat := mkVec n (fun i => c * vecEntry v i)
/-- Square & rectangular matrix-vector products and standard basis vector $e_k \in \mathbb{Q}^n$. -/
def matVecMulN (n : Nat) (M : List (List CanonicalRat)) (v : List CanonicalRat) : List CanonicalRat :=
  mkVec n (fun i => sumUpTo n (fun j => matEntry M i j * vecEntry v j))
def matRectVecMul (n m : Nat) (B : List (List CanonicalRat)) (u : List CanonicalRat) : List CanonicalRat :=
  mkVec n (fun i => sumUpTo m (fun j => matEntry B i j * vecEntry u j))
def basisVec (n k : Nat) : List CanonicalRat := mkVec n (fun i => if i = k then 1 else 0)
private theorem vecEntry_vecSubN (n : Nat) (u v : List CanonicalRat) (i : Nat) (hi : i < n) :
    vecEntry (vecSubN n u v) i = vecEntry u i - vecEntry v i := vecEntry_mkVec n _ i hi
private theorem vecEntry_basisVec (n k i : Nat) (hi : i < n) :
    vecEntry (basisVec n k) i = if i = k then 1 else 0 := vecEntry_mkVec n _ i hi
/-- Bilinear form $u^\top M v$. -/
def quadFormN (n : Nat) (M : List (List CanonicalRat)) (u v : List CanonicalRat) : CanonicalRat :=
  vecDotN n u (matVecMulN n M v)
/-- Stored electromagnetic & capacitive MNA energy $\mathcal{E}(x) = \frac{1}{2} x^\top C x$. -/
def mnaStoredEnergy (n : Nat) (C : List (List CanonicalRat)) (x : List CanonicalRat) : CanonicalRat :=
  (1 / 2) * quadFormN n C x x
theorem vecDotN_comm (n : Nat) (u v : List CanonicalRat) :
    vecDotN n u v = vecDotN n v u :=
  sumUpTo_congr n _ _ (fun _ _ => by grind)
theorem quadFormN_eq_sum (n : Nat) (M : List (List CanonicalRat)) (u v : List CanonicalRat) :
    quadFormN n M u v =
      sumUpTo n (fun i => vecEntry u i * sumUpTo n (fun j => matEntry M i j * vecEntry v j)) :=
  sumUpTo_congr n _ _ (fun i hi => by unfold matVecMulN; rw [vecEntry_mkVec n _ i hi])
theorem quadFormN_basis_diag (n k : Nat) (M : List (List CanonicalRat)) (hk : k < n) :
    quadFormN n M (basisVec n k) (basisVec n k) = matEntry M k k := by
  rw [quadFormN_eq_sum]
  have hInner : ∀ i, i < n →
      vecEntry (basisVec n k) i * sumUpTo n (fun j => matEntry M i j * vecEntry (basisVec n k) j) =
        if i = k then matEntry M k k else 0 := by
    intro i hi
    rw [vecEntry_basisVec n k i hi]
    by_cases hik : i = k
    · subst hik
      have hJ : sumUpTo n (fun j => matEntry M i j * vecEntry (basisVec n i) j) = matEntry M i i := by
        rw [sumUpTo_congr n _ (fun j => if j = i then matEntry M i i else 0)]
        · exact sumUpTo_delta n i (matEntry M i i) hi
        · intro j hj; rw [vecEntry_basisVec n i j hj]
          by_cases hji : j = i <;> simp [hji]
      rw [hJ]; simp
    · simp [hik]
  rw [sumUpTo_congr n _ _ hInner]
  exact sumUpTo_delta n k (matEntry M k k) hk
theorem quadFormN_symm_of_entries (n : Nat) (M : List (List CanonicalRat))
    (hSym : ∀ i j, i < n → j < n → matEntry M i j = matEntry M j i)
    (u v : List CanonicalRat) :
    quadFormN n M u v = quadFormN n M v u := by
  rw [quadFormN_eq_sum, quadFormN_eq_sum]
  have hL : sumUpTo n (fun i => vecEntry u i * sumUpTo n (fun j => matEntry M i j * vecEntry v j)) =
      sumUpTo n (fun i => sumUpTo n (fun j => vecEntry v j * (matEntry M j i * vecEntry u i))) := by
    refine sumUpTo_congr n _ _ (fun i hi => ?_)
    rw [← sumUpTo_scale]
    exact sumUpTo_congr n _ _ (fun j hj => by rw [hSym i j hi hj]; grind)
  rw [hL, sumUpTo_comm]
  exact sumUpTo_congr n _ _ (fun _ _ => by rw [← sumUpTo_scale])
private theorem quadFormN_sub_right (n : Nat) (M : List (List CanonicalRat))
    (u a b : List CanonicalRat) :
    quadFormN n M u (vecSubN n a b) = quadFormN n M u a - quadFormN n M u b := by
  rw [quadFormN_eq_sum, quadFormN_eq_sum, quadFormN_eq_sum, ← sumUpTo_sub]
  refine sumUpTo_congr n _ _ (fun i _ => ?_)
  have hIn : sumUpTo n (fun j => matEntry M i j * vecEntry (vecSubN n a b) j) =
      sumUpTo n (fun j => matEntry M i j * vecEntry a j) -
      sumUpTo n (fun j => matEntry M i j * vecEntry b j) := by
    rw [← sumUpTo_sub]
    exact sumUpTo_congr n _ _ (fun j hj => by rw [vecEntry_vecSubN n a b j hj]; grind)
  rw [hIn]; grind
/-- Weighted rank-1 Cholesky/LDLT Gram congruence factor $w_r \ell_r \ell_r^\top$ ($w_r \ge 0$). -/
structure MnaGramFactor where
  weight : CanonicalRat
  vec    : List CanonicalRat
  deriving DecidableEq, Repr
/-- Assembled `(i, j)` entry of $\sum_r w_r \ell_r \ell_r^\top$. -/
def gramEntry : List MnaGramFactor → Nat → Nat → CanonicalRat
  | [], _, _ => 0
  | f :: fs, i, j => f.weight * (vecEntry f.vec i * vecEntry f.vec j) + gramEntry fs i j
/-- Bilinear evaluation $\sum_r w_r (\ell_r^\top u)(\ell_r^\top v)$. -/
def evalGramBilinear (n : Nat) : List MnaGramFactor → List CanonicalRat → List CanonicalRat → CanonicalRat
  | [], _, _ => 0
  | f :: fs, u, v => f.weight * (vecDotN n f.vec u * vecDotN n f.vec v) + evalGramBilinear n fs u v
theorem gramEntry_diag_nonneg :
    ∀ (factors : List MnaGramFactor) (i : Nat),
      (∀ f, f ∈ factors → 0 ≤ f.weight) → 0 ≤ gramEntry factors i i
  | [], _, _ => by dsimp [gramEntry]; grind
  | f :: fs, i, hW => by
    dsimp [gramEntry]
    have hTerm := Rat.mul_nonneg (hW f (List.mem_cons_self ..)) (Interval.rat_sq_nonneg (vecEntry f.vec i))
    have hRest := gramEntry_diag_nonneg fs i (fun g hg => hW g (List.mem_cons_of_mem f hg))
    grind
private theorem evalGramBilinear_nonneg (n : Nat) :
    ∀ (factors : List MnaGramFactor) (x : List CanonicalRat),
      (∀ f, f ∈ factors → 0 ≤ f.weight) → 0 ≤ evalGramBilinear n factors x x
  | [], _, _ => by dsimp [evalGramBilinear]; grind
  | f :: fs, x, hW => by
    dsimp [evalGramBilinear]
    have hTerm := Rat.mul_nonneg (hW f (List.mem_cons_self ..)) (Interval.rat_sq_nonneg (vecDotN n f.vec x))
    have hRest := evalGramBilinear_nonneg n fs x (fun g hg => hW g (List.mem_cons_of_mem f hg))
    grind
private theorem sum_gramEntry_eq_bilinear (n : Nat) :
    ∀ (factors : List MnaGramFactor) (u v : List CanonicalRat),
      sumUpTo n (fun i => vecEntry u i * sumUpTo n (fun j => gramEntry factors i j * vecEntry v j)) =
        evalGramBilinear n factors u v
  | [], u, v => by
    dsimp [gramEntry, evalGramBilinear]
    rw [sumUpTo_congr n _ (fun _ => 0)]
    · exact sumUpTo_zero n
    · intro _ _; rw [sumUpTo_congr n _ (fun _ => 0) (fun _ _ => by grind), sumUpTo_zero]; grind
  | f :: fs, u, v => by
    dsimp [gramEntry, evalGramBilinear]
    have hSplit : sumUpTo n (fun i => vecEntry u i *
        sumUpTo n (fun j => (f.weight * (vecEntry f.vec i * vecEntry f.vec j) + gramEntry fs i j) * vecEntry v j)) =
      sumUpTo n (fun i => (f.weight * (vecEntry f.vec i * vecEntry u i)) *
        sumUpTo n (fun j => vecEntry f.vec j * vecEntry v j)) +
      sumUpTo n (fun i => vecEntry u i * sumUpTo n (fun j => gramEntry fs i j * vecEntry v j)) := by
      rw [← sumUpTo_add]
      refine sumUpTo_congr n _ _ (fun i _ => ?_)
      have hIn : sumUpTo n (fun j => (f.weight * (vecEntry f.vec i * vecEntry f.vec j) + gramEntry fs i j) * vecEntry v j) =
          (f.weight * vecEntry f.vec i) * sumUpTo n (fun j => vecEntry f.vec j * vecEntry v j) +
          sumUpTo n (fun j => gramEntry fs i j * vecEntry v j) := by
        rw [← sumUpTo_scale, ← sumUpTo_add]
        exact sumUpTo_congr n _ _ (fun _ _ => by grind)
      rw [hIn]; grind
    rw [hSplit, sum_gramEntry_eq_bilinear n fs u v]
    have hPull : sumUpTo n (fun i => (f.weight * (vecEntry f.vec i * vecEntry u i)) *
        sumUpTo n (fun j => vecEntry f.vec j * vecEntry v j)) =
        (f.weight * sumUpTo n (fun j => vecEntry f.vec j * vecEntry v j)) *
        sumUpTo n (fun i => vecEntry f.vec i * vecEntry u i) := by
      rw [← sumUpTo_scale]
      exact sumUpTo_congr n _ _ (fun _ _ => by grind)
    unfold vecDotN; rw [hPull]; grind
/-- **Gram Congruence Symmetry & Positive Semidefiniteness (`gramCongruence_symm_and_psd`)**. -/
theorem gramCongruence_symm_and_psd (n : Nat) (M : List (List CanonicalRat))
    (factors : List MnaGramFactor)
    (hEntries : ∀ i j, i < n → j < n → matEntry M i j = gramEntry factors i j)
    (hWeights : ∀ f, f ∈ factors → 0 ≤ f.weight) :
    (∀ i j, i < n → j < n → matEntry M i j = matEntry M j i) ∧
    (∀ u v, quadFormN n M u v = quadFormN n M v u) ∧
    (∀ x, 0 ≤ quadFormN n M x x) := by
  have hSymEntry : ∀ i j, i < n → j < n → matEntry M i j = matEntry M j i := by
    intro i j hi hj
    rw [hEntries i j hi hj, hEntries j i hj hi]
    clear hEntries hWeights
    induction factors with
    | nil => rfl
    | cons f fs ih => dsimp [gramEntry]; rw [ih]; grind
  refine ⟨hSymEntry, quadFormN_symm_of_entries n M hSymEntry, fun x => ?_⟩
  rw [quadFormN_eq_sum]
  have hRew : sumUpTo n (fun i => vecEntry x i * sumUpTo n (fun j => matEntry M i j * vecEntry x j)) =
      sumUpTo n (fun i => vecEntry x i * sumUpTo n (fun j => gramEntry factors i j * vecEntry x j)) :=
    sumUpTo_congr n _ _ (fun i hi => by rw [sumUpTo_congr n _ _ (fun j hj => by rw [hEntries i j hi hj])])
  rw [hRew, sum_gramEntry_eq_bilinear]
  exact evalGramBilinear_nonneg n factors x hWeights
/-- **Skew-Compatible Passive Conductance Lemma (`quadFormN_nonneg_of_symSum_gram`)**:
Since $2 \, x^\top G x = x^\top (G + G^\top) x$, a Gram factorization of $G + G^\top$ certifies
$0 \le x^\top G x$ even when $G$ contains skew-symmetric MNA inductor/transformer stamps. -/
theorem quadFormN_nonneg_of_symSum_gram (n : Nat) (G : List (List CanonicalRat))
    (factors : List MnaGramFactor)
    (hSymEntries : ∀ i j, i < n → j < n → matEntry G i j + matEntry G j i = gramEntry factors i j)
    (hWeights : ∀ f, f ∈ factors → 0 ≤ f.weight)
    (x : List CanonicalRat) :
    0 ≤ quadFormN n G x x := by
  have hDouble : 2 * quadFormN n G x x = evalGramBilinear n factors x x := by
    rw [← sum_gramEntry_eq_bilinear n factors x x, quadFormN_eq_sum]
    have hTranspose :
        sumUpTo n (fun i => vecEntry x i * sumUpTo n (fun j => matEntry G j i * vecEntry x j)) =
        sumUpTo n (fun i => vecEntry x i * sumUpTo n (fun j => matEntry G i j * vecEntry x j)) := by
      have h1 : sumUpTo n (fun i => vecEntry x i * sumUpTo n (fun j => matEntry G j i * vecEntry x j)) =
          sumUpTo n (fun i => sumUpTo n (fun j => vecEntry x j * (matEntry G j i * vecEntry x i))) :=
        sumUpTo_congr n _ _ (fun _ _ => by rw [← sumUpTo_scale]; exact sumUpTo_congr n _ _ (fun _ _ => by grind))
      rw [h1, sumUpTo_comm]
      exact sumUpTo_congr n _ _ (fun _ _ => by rw [← sumUpTo_scale])
    have hSum :
        sumUpTo n (fun i => vecEntry x i * sumUpTo n (fun j => gramEntry factors i j * vecEntry x j)) =
        sumUpTo n (fun i => vecEntry x i * sumUpTo n (fun j => matEntry G i j * vecEntry x j)) +
        sumUpTo n (fun i => vecEntry x i * sumUpTo n (fun j => matEntry G j i * vecEntry x j)) := by
      rw [← sumUpTo_add]
      refine sumUpTo_congr n _ _ (fun i hi => ?_)
      have hIn : sumUpTo n (fun j => gramEntry factors i j * vecEntry x j) =
          sumUpTo n (fun j => matEntry G i j * vecEntry x j) +
          sumUpTo n (fun j => matEntry G j i * vecEntry x j) := by
        rw [← sumUpTo_add]
        exact sumUpTo_congr n _ _ (fun j hj => by rw [← hSymEntries i j hi hj]; grind)
      rw [hIn]; grind
    rw [hSum, hTranspose]; grind
  have hGramNonneg := evalGramBilinear_nonneg n factors x hWeights
  have hTwo : (2 : CanonicalRat) * 0 ≤ 2 * quadFormN n G x x := by rw [hDouble]; grind
  exact Rat.le_of_mul_le_mul_left hTwo (by decide +kernel)
/-! ## 2. Index-1 MNA Circuit DAE Residual Enclosure & Unconditional Discrete Energy Passivity -/
/-- Implicit DAE time-stepping integration method. -/
inductive MnaMethod where
  | backwardEuler
  | trapezoidal
  deriving DecidableEq, Repr
/-- Passive 2-terminal sector-monotone nonlinear device (`none` = reference ground `0 V`). -/
structure MnaNonlinearBranch where
  nodeP? : Option Nat
  nodeN? : Option Nat
  gMin   : CanonicalRat
  gMax   : CanonicalRat
  deriving DecidableEq, Repr
/-- Branch port voltage $v_b(x) = x_p - x_q$ (`0` at ground `none`). -/
def branchVoltage (n : Nat) (b : MnaNonlinearBranch) (x : List CanonicalRat) : CanonicalRat :=
  (match b.nodeP? with | some p => if p < n then vecEntry x p else 0 | none => 0) -
  (match b.nodeN? with | some q => if q < n then vecEntry x q else 0 | none => 0)
/-- Stamp all 2-terminal nonlinear branch currents `iBranches` into the $n$-dimensional MNA KCL vector. -/
def stampNonlinearCurrents (n : Nat) : List MnaNonlinearBranch → List CanonicalRat → List CanonicalRat
  | [], _ => mkVec n (fun _ => 0)
  | b :: bs, ibs =>
    let ib := ibs.headD 0
    let rest := stampNonlinearCurrents n bs ibs.tail
    mkVec n (fun i =>
      (match b.nodeP? with | some p => if i = p ∧ p < n then ib else 0 | none => 0) -
      (match b.nodeN? with | some q => if i = q ∧ q < n then ib else 0 | none => 0) +
      vecEntry rest i)
private theorem sum_optNode_term (n : Nat) (opt : Option Nat) (ib : CanonicalRat) (x : List CanonicalRat) :
    sumUpTo n (fun i => vecEntry x i * (match opt with | some p => if i = p ∧ p < n then ib else 0 | none => 0)) =
      (match opt with | some p => if p < n then vecEntry x p else 0 | none => 0) * ib := by
  cases opt with
  | none => rw [sumUpTo_congr n _ (fun _ => 0) (fun _ _ => by grind), sumUpTo_zero]; grind
  | some p =>
    by_cases hp : p < n
    · rw [sumUpTo_congr n _ (fun i => if i = p then vecEntry x p * ib else 0)]
      · rw [sumUpTo_delta n p _ hp]; simp [hp]
      · intro i _; by_cases hip : i = p
        · subst hip; simp [hp]
        · simp [hip]
    · rw [sumUpTo_congr n _ (fun _ => 0) (fun _ _ => by simp [hp]), sumUpTo_zero]
      simp [hp]
/-- **Tellegen KCL Incidence Passivity (`stampNonlinearCurrents_passive`)**:
Sector-passive 2-terminal nonlinear branches ($v_b i_b \ge 0$) satisfy $x^\top i_{\text{nl}}(x) \ge 0$. -/
theorem stampNonlinearCurrents_passive (n : Nat) :
    ∀ (branches : List MnaNonlinearBranch) (iBranches x : List CanonicalRat),
      (∀ idx, idx < branches.length →
        let b := branches.getD idx ⟨none, none, 0, 0⟩
        0 ≤ branchVoltage n b x * vecEntry iBranches idx) →
      0 ≤ vecDotN n x (stampNonlinearCurrents n branches iBranches)
  | [], _, x, _ => by
    unfold stampNonlinearCurrents vecDotN
    rw [sumUpTo_congr n _ (fun _ => 0) (fun i hi => by rw [vecEntry_mkVec n _ i hi]; grind), sumUpTo_zero]
    grind
  | b :: bs, ibs, x, hPass => by
    dsimp only [stampNonlinearCurrents]
    unfold vecDotN
    have hSplit :
        sumUpTo n (fun i => vecEntry x i * vecEntry (mkVec n (fun i =>
          (match b.nodeP? with | some p => if i = p ∧ p < n then ibs.headD 0 else 0 | none => 0) -
          (match b.nodeN? with | some q => if i = q ∧ q < n then ibs.headD 0 else 0 | none => 0) +
          vecEntry (stampNonlinearCurrents n bs ibs.tail) i)) i) =
        branchVoltage n b x * ibs.headD 0 +
        vecDotN n x (stampNonlinearCurrents n bs ibs.tail) := by
      unfold vecDotN branchVoltage
      rw [sumUpTo_congr n _ (fun i =>
        (vecEntry x i * (match b.nodeP? with | some p => if i = p ∧ p < n then ibs.headD 0 else 0 | none => 0) -
         vecEntry x i * (match b.nodeN? with | some q => if i = q ∧ q < n then ibs.headD 0 else 0 | none => 0)) +
        vecEntry x i * vecEntry (stampNonlinearCurrents n bs ibs.tail) i)]
      · rw [sumUpTo_add, sumUpTo_sub, sum_optNode_term n b.nodeP?, sum_optNode_term n b.nodeN?]; grind
      · intro i hi; rw [vecEntry_mkVec n _ i hi]; grind
    rw [hSplit]
    have hHead : 0 ≤ branchVoltage n b x * ibs.headD 0 := by
      have h0 := hPass 0 (by simp)
      cases ibs <;> simp [vecEntry] at h0 ⊢ <;> exact h0
    have hTail : 0 ≤ vecDotN n x (stampNonlinearCurrents n bs ibs.tail) := by
      apply stampNonlinearCurrents_passive n bs ibs.tail x
      intro idx hIdx
      have hSucc := hPass (idx + 1) (by simp; omega)
      cases ibs <;> simp [vecEntry] at hSucc ⊢ <;> exact hSucc
    grind
/-- MNA Circuit DAE specification $C \dot{x}(t) + G x(t) + i_{\text{nl}}(x(t)) = B u(t)$. -/
structure MnaCircuitSpec where
  dim        : Nat
  inputDim   : Nat
  matC       : List (List CanonicalRat)
  matG       : List (List CanonicalRat)
  matB       : List (List CanonicalRat)
  nlBranches : List MnaNonlinearBranch
  deriving DecidableEq, Repr
/-- One implicit circuit DAE solver step with residual tolerance `residualTol`. -/
structure MnaTraceStep where
  dt            : CanonicalRat
  xPrev         : List CanonicalRat
  xNext         : List CanonicalRat
  uInput        : List CanonicalRat
  iBranchesPrev : List CanonicalRat
  iBranchesNext : List CanonicalRat
  residualTol   : CanonicalRat
  deriving DecidableEq, Repr
/-- Discretized MNA KCL/KVL step residual vector for Backward-Euler or Trapezoidal integration. -/
def mnaStepResidual (spec : MnaCircuitSpec) (method : MnaMethod) (step : MnaTraceStep) : List CanonicalRat :=
  let n := spec.dim
  let cDx := matVecMulN n spec.matC (vecSubN n step.xNext step.xPrev)
  let bu := matRectVecMul n spec.inputDim spec.matB step.uInput
  match method with
  | .backwardEuler =>
    let gx := matVecMulN n spec.matG step.xNext
    let inl := stampNonlinearCurrents n spec.nlBranches step.iBranchesNext
    mkVec n (fun i => vecEntry cDx i / step.dt + vecEntry gx i + vecEntry inl i - vecEntry bu i)
  | .trapezoidal =>
    let xMid := mkVec n (fun i => (vecEntry step.xNext i + vecEntry step.xPrev i) / 2)
    let gxMid := matVecMulN n spec.matG xMid
    let inlNext := stampNonlinearCurrents n spec.nlBranches step.iBranchesNext
    let inlPrev := stampNonlinearCurrents n spec.nlBranches step.iBranchesPrev
    mkVec n (fun i =>
      vecEntry cDx i / step.dt + vecEntry gxMid i +
      (vecEntry inlNext i + vecEntry inlPrev i) / 2 - vecEntry bu i)
/-- Check sector monotonicity (`0 ≤ gMin ≤ gMax`) and passivity (`0 ≤ v · i`) for every nonlinear branch. -/
def checkMnaStepNonlinear (spec : MnaCircuitSpec) (method : MnaMethod) (step : MnaTraceStep) : Bool :=
  (List.range spec.nlBranches.length).all fun idx =>
    let b := spec.nlBranches.getD idx ⟨none, none, 0, 0⟩
    let vNext := branchVoltage spec.dim b step.xNext
    let iNext := vecEntry step.iBranchesNext idx
    let okNext :=
      decide (0 ≤ b.gMin) && decide (b.gMin ≤ b.gMax) &&
      decide (0 ≤ vNext * iNext) &&
      decide (0 ≤ (iNext - b.gMin * vNext) * (b.gMax * vNext - iNext))
    match method with
    | .backwardEuler => okNext
    | .trapezoidal =>
      let vPrev := branchVoltage spec.dim b step.xPrev
      let iPrev := vecEntry step.iBranchesPrev idx
      okNext &&
      decide (0 ≤ vPrev * iPrev) &&
      decide (0 ≤ (iPrev - b.gMin * vPrev) * (b.gMax * vPrev - iPrev)) &&
      decide (0 ≤ ((vNext + vPrev) / 2) * ((iNext + iPrev) / 2))
/-- **Backward-Euler & Trapezoidal MNA Step Residual Enclosure Checker (`checkMnaStepEnclosure`)**. -/
def checkMnaStepEnclosure (spec : MnaCircuitSpec) (method : MnaMethod) (step : MnaTraceStep) : Bool :=
  decide (0 < step.dt) &&
  decide (0 ≤ step.residualTol) &&
  checkMnaStepNonlinear spec method step &&
  (List.range spec.dim).all fun i =>
    let r_i := vecEntry (mnaStepResidual spec method step) i
    decide (-step.residualTol ≤ r_i) && decide (r_i ≤ step.residualTol)
private theorem list_range_all_iff (n : Nat) (p : Nat → Bool) :
    (List.range n).all p = true ↔ ∀ i, i < n → p i = true := by
  simp [List.all_eq_true, List.mem_range]
/-- **Soundness of `checkMnaStepEnclosure` (`checkMnaStepEnclosure_sound`)**. -/
theorem checkMnaStepEnclosure_sound (spec : MnaCircuitSpec) (method : MnaMethod) (step : MnaTraceStep)
    (hOk : checkMnaStepEnclosure spec method step = true) :
    0 < step.dt ∧
    0 ≤ step.residualTol ∧
    0 ≤ vecDotN spec.dim step.xNext (stampNonlinearCurrents spec.dim spec.nlBranches step.iBranchesNext) ∧
    ∀ i, i < spec.dim →
      vecEntry (mnaStepResidual spec method step) i ∈ Interval.mk (-step.residualTol) step.residualTol := by
  unfold checkMnaStepEnclosure at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, list_range_all_iff] at hOk
  obtain ⟨⟨⟨hDt, hTol⟩, hNl⟩, hRes⟩ := hOk
  unfold checkMnaStepNonlinear at hNl
  rw [list_range_all_iff] at hNl
  have hPassNext : 0 ≤ vecDotN spec.dim step.xNext
      (stampNonlinearCurrents spec.dim spec.nlBranches step.iBranchesNext) := by
    apply stampNonlinearCurrents_passive
    intro idx hIdx
    have hB := hNl idx hIdx
    cases method <;> simp only [Bool.and_eq_true, decide_eq_true_eq] at hB <;> grind
  refine ⟨hDt, hTol, hPassNext, fun i hi => ?_⟩
  rw [Interval.mem_iff]
  exact hRes i hi
private theorem quadFormN_polarization_be (n : Nat) (C : List (List CanonicalRat))
    (hSym : ∀ i j, i < n → j < n → matEntry C i j = matEntry C j i)
    (xPrev xNext : List CanonicalRat) :
    mnaStoredEnergy n C xPrev - mnaStoredEnergy n C xNext =
      mnaStoredEnergy n C (vecSubN n xNext xPrev) -
      vecDotN n xNext (matVecMulN n C (vecSubN n xNext xPrev)) := by
  unfold mnaStoredEnergy
  have h3 : quadFormN n C (vecSubN n xNext xPrev) (vecSubN n xNext xPrev) =
      quadFormN n C xNext xNext - 2 * quadFormN n C xNext xPrev + quadFormN n C xPrev xPrev := by
    have hSubL : quadFormN n C (vecSubN n xNext xPrev) (vecSubN n xNext xPrev) =
        quadFormN n C xNext (vecSubN n xNext xPrev) - quadFormN n C xPrev (vecSubN n xNext xPrev) := by
      rw [quadFormN_eq_sum, quadFormN_eq_sum, quadFormN_eq_sum, ← sumUpTo_sub]
      exact sumUpTo_congr n _ _ (fun i hi => by rw [vecEntry_vecSubN n _ _ i hi]; grind)
    rw [hSubL, quadFormN_sub_right, quadFormN_sub_right, quadFormN_symm_of_entries n C hSym xPrev xNext]
    grind
  have h4 : vecDotN n xNext (matVecMulN n C (vecSubN n xNext xPrev)) =
      quadFormN n C xNext xNext - quadFormN n C xNext xPrev :=
    quadFormN_sub_right n C xNext xNext xPrev
  rw [h3, h4]; grind
/-- **Unconditional Backward-Euler MNA Energy Passivity (`mna_backward_euler_energy_dissipative`)**:
When $C \succeq 0$, $G + G^\top \succeq 0$, and $x_{k+1}^\top i_{\text{nl}}(x_{k+1}) \ge 0$ under zero
source $u = 0$, stored electromagnetic/capacitive energy $\frac{1}{2} x^\top C x$ is monotonically
non-increasing at every step regardless of $\Delta t > 0$! -/
theorem mna_backward_euler_energy_dissipative
    (n : Nat) (C G : List (List CanonicalRat))
    (capFactors condFactors : List MnaGramFactor)
    (hCapEntries : ∀ i j, i < n → j < n → matEntry C i j = gramEntry capFactors i j)
    (hCapWeights : ∀ f, f ∈ capFactors → 0 ≤ f.weight)
    (hCondEntries : ∀ i j, i < n → j < n → matEntry G i j + matEntry G j i = gramEntry condFactors i j)
    (hCondWeights : ∀ f, f ∈ condFactors → 0 ≤ f.weight)
    (dt : CanonicalRat) (hDt : 0 < dt)
    (xPrev xNext inl : List CanonicalRat)
    (hNlPassive : 0 ≤ vecDotN n xNext inl)
    (hBeStep : ∀ i, i < n →
      vecEntry (matVecMulN n C (vecSubN n xNext xPrev)) i +
      dt * (vecEntry (matVecMulN n G xNext) i + vecEntry inl i) = 0) :
    mnaStoredEnergy n C xPrev - mnaStoredEnergy n C xNext =
      mnaStoredEnergy n C (vecSubN n xNext xPrev) +
      dt * quadFormN n G xNext xNext +
      dt * vecDotN n xNext inl ∧
    mnaStoredEnergy n C xNext ≤ mnaStoredEnergy n C xPrev ∧
    0 ≤ mnaStoredEnergy n C xNext := by
  obtain ⟨hSymC, _, hPsdC⟩ := gramCongruence_symm_and_psd n C capFactors hCapEntries hCapWeights
  have hPsdG := quadFormN_nonneg_of_symSum_gram n G condFactors hCondEntries hCondWeights xNext
  have hPol := quadFormN_polarization_be n C hSymC xPrev xNext
  have hInnerEq : vecDotN n xNext (matVecMulN n C (vecSubN n xNext xPrev)) =
      -(dt * quadFormN n G xNext xNext + dt * vecDotN n xNext inl) := by
    unfold quadFormN vecDotN
    rw [sumUpTo_congr n _ (fun i =>
      -(dt * (vecEntry xNext i * vecEntry (matVecMulN n G xNext) i) +
        dt * (vecEntry xNext i * vecEntry inl i))) (fun i hi => by
      have hBe := hBeStep i hi
      have hC : vecEntry (matVecMulN n C (vecSubN n xNext xPrev)) i =
          -(dt * (vecEntry (matVecMulN n G xNext) i + vecEntry inl i)) := by grind
      rw [hC]; grind)]
    have hRhs : sumUpTo n (fun i =>
        -(dt * (vecEntry xNext i * vecEntry (matVecMulN n G xNext) i) + dt * (vecEntry xNext i * vecEntry inl i))) =
        (0 : CanonicalRat) - (dt * sumUpTo n (fun i => vecEntry xNext i * vecEntry (matVecMulN n G xNext) i) +
          dt * sumUpTo n (fun i => vecEntry xNext i * vecEntry inl i)) := by
      rw [← sumUpTo_scale, ← sumUpTo_scale, ← sumUpTo_add, ← sumUpTo_zero n, ← sumUpTo_sub]
      exact sumUpTo_congr n _ _ (fun _ _ => by grind)
    rw [hRhs]; grind
  rw [hInnerEq] at hPol
  have hNumDamp : 0 ≤ mnaStoredEnergy n C (vecSubN n xNext xPrev) :=
    Rat.mul_nonneg (by decide +kernel) (hPsdC _)
  have hEnNext : 0 ≤ mnaStoredEnergy n C xNext :=
    Rat.mul_nonneg (by decide +kernel) (hPsdC xNext)
  have hGTerm : 0 ≤ dt * quadFormN n G xNext xNext := Rat.mul_nonneg (by grind) hPsdG
  have hNlTerm : 0 ≤ dt * vecDotN n xNext inl := Rat.mul_nonneg (by grind) hNlPassive
  exact ⟨by grind, by grind, hEnNext⟩
/-- **Unconditional Trapezoidal MNA Energy Passivity (`mna_trapezoidal_energy_dissipative`)**. -/
theorem mna_trapezoidal_energy_dissipative
    (n : Nat) (C G : List (List CanonicalRat))
    (capFactors condFactors : List MnaGramFactor)
    (hCapEntries : ∀ i j, i < n → j < n → matEntry C i j = gramEntry capFactors i j)
    (hCapWeights : ∀ f, f ∈ capFactors → 0 ≤ f.weight)
    (hCondEntries : ∀ i j, i < n → j < n → matEntry G i j + matEntry G j i = gramEntry condFactors i j)
    (hCondWeights : ∀ f, f ∈ condFactors → 0 ≤ f.weight)
    (dt : CanonicalRat) (hDt : 0 < dt)
    (xPrev xNext iAvg : List CanonicalRat)
    (hNlMidPassive : 0 ≤ vecDotN n (mkVec n (fun i => (vecEntry xNext i + vecEntry xPrev i) / 2)) iAvg)
    (hTrapStep : ∀ i, i < n →
      let xMid := mkVec n (fun j => (vecEntry xNext j + vecEntry xPrev j) / 2)
      vecEntry (matVecMulN n C (vecSubN n xNext xPrev)) i +
      dt * (vecEntry (matVecMulN n G xMid) i + vecEntry iAvg i) = 0) :
    let xMid := mkVec n (fun i => (vecEntry xNext i + vecEntry xPrev i) / 2)
    mnaStoredEnergy n C xPrev - mnaStoredEnergy n C xNext =
      dt * quadFormN n G xMid xMid + dt * vecDotN n xMid iAvg ∧
    mnaStoredEnergy n C xNext ≤ mnaStoredEnergy n C xPrev := by
  intro xMid
  obtain ⟨hSymC, _, _⟩ := gramCongruence_symm_and_psd n C capFactors hCapEntries hCapWeights
  have hPsdG := quadFormN_nonneg_of_symSum_gram n G condFactors hCondEntries hCondWeights xMid
  have hMidDiff : vecDotN n xMid (matVecMulN n C (vecSubN n xNext xPrev)) =
      mnaStoredEnergy n C xNext - mnaStoredEnergy n C xPrev := by
    unfold mnaStoredEnergy
    have hAddL : vecDotN n xMid (matVecMulN n C (vecSubN n xNext xPrev)) =
        (1 / 2) * (quadFormN n C xNext (vecSubN n xNext xPrev) + quadFormN n C xPrev (vecSubN n xNext xPrev)) := by
      unfold quadFormN vecDotN
      rw [← sumUpTo_add, ← sumUpTo_scale]
      exact sumUpTo_congr n _ _ (fun i hi => by dsimp [xMid]; rw [vecEntry_mkVec n _ i hi]; grind)
    rw [hAddL, quadFormN_sub_right, quadFormN_sub_right, quadFormN_symm_of_entries n C hSymC xPrev xNext]; grind
  have hInnerEq : vecDotN n xMid (matVecMulN n C (vecSubN n xNext xPrev)) =
      -(dt * quadFormN n G xMid xMid + dt * vecDotN n xMid iAvg) := by
    unfold quadFormN vecDotN
    rw [sumUpTo_congr n _ (fun i =>
      -(dt * (vecEntry xMid i * vecEntry (matVecMulN n G xMid) i) +
        dt * (vecEntry xMid i * vecEntry iAvg i))) (fun i hi => by
      have hTr := hTrapStep i hi; dsimp only at hTr
      have hC : vecEntry (matVecMulN n C (vecSubN n xNext xPrev)) i =
          -(dt * (vecEntry (matVecMulN n G xMid) i + vecEntry iAvg i)) := by grind
      rw [hC]; grind)]
    have hRhs : sumUpTo n (fun i =>
        -(dt * (vecEntry xMid i * vecEntry (matVecMulN n G xMid) i) + dt * (vecEntry xMid i * vecEntry iAvg i))) =
        (0 : CanonicalRat) - (dt * sumUpTo n (fun i => vecEntry xMid i * vecEntry (matVecMulN n G xMid) i) +
          dt * sumUpTo n (fun i => vecEntry xMid i * vecEntry iAvg i)) := by
      rw [← sumUpTo_scale, ← sumUpTo_scale, ← sumUpTo_add, ← sumUpTo_zero n, ← sumUpTo_sub]
      exact sumUpTo_congr n _ _ (fun _ _ => by grind)
    rw [hRhs]; grind
  have hGTerm : 0 ≤ dt * quadFormN n G xMid xMid := Rat.mul_nonneg (by grind) hPsdG
  have hNlTerm : 0 ≤ dt * vecDotN n xMid iAvg := Rat.mul_nonneg (by grind) hNlMidPassive
  exact ⟨by grind, by grind⟩
/-- **Multi-Step Variable-Timestep Backward-Euler Trace Stability (`mna_backward_euler_trace_energy_monotone`)**. -/
theorem mna_backward_euler_trace_energy_monotone
    (n : Nat) (C G : List (List CanonicalRat))
    (capFactors condFactors : List MnaGramFactor)
    (hCapEntries : ∀ i j, i < n → j < n → matEntry C i j = gramEntry capFactors i j)
    (hCapWeights : ∀ f, f ∈ capFactors → 0 ≤ f.weight)
    (hCondEntries : ∀ i j, i < n → j < n → matEntry G i j + matEntry G j i = gramEntry condFactors i j)
    (hCondWeights : ∀ f, f ∈ condFactors → 0 ≤ f.weight) :
    ∀ (steps : List (CanonicalRat × List CanonicalRat × List CanonicalRat)) (x0 : List CanonicalRat),
      (∀ idx, idx < steps.length →
        let prev := if idx = 0 then x0 else (steps.getD (idx - 1) (1, [], [])).2.1
        let cur := steps.getD idx (1, [], [])
        0 < cur.1 ∧ 0 ≤ vecDotN n cur.2.1 cur.2.2 ∧
        ∀ i, i < n →
          vecEntry (matVecMulN n C (vecSubN n cur.2.1 prev)) i +
          cur.1 * (vecEntry (matVecMulN n G cur.2.1) i + vecEntry cur.2.2 i) = 0) →
      let xFinal := match steps.getLast? with | some s => s.2.1 | none => x0
      mnaStoredEnergy n C xFinal ≤ mnaStoredEnergy n C x0
  | [], x0, _ => by simp
  | (dt1, x1, inl1) :: rest, x0, hSteps => by
    have h0 := hSteps 0 (by simp)
    dsimp only [↓reduceIte, List.getD_cons_zero] at h0
    have hStep1 := (mna_backward_euler_energy_dissipative n C G capFactors condFactors
      hCapEntries hCapWeights hCondEntries hCondWeights dt1 h0.1 x0 x1 inl1 h0.2.1 h0.2.2).2.1
    cases rest with
    | nil => simpa using hStep1
    | cons s2 tail =>
      have hTail := mna_backward_euler_trace_energy_monotone n C G capFactors condFactors
        hCapEntries hCapWeights hCondEntries hCondWeights (s2 :: tail) x1 (by
          intro idx hIdx
          have hSucc := hSteps (idx + 1) (by simp at hIdx ⊢; omega)
          cases idx with
          | zero => simpa using hSucc
          | succ m => simpa using hSucc)
      have hLast : ((dt1, x1, inl1) :: s2 :: tail).getLast? = (s2 :: tail).getLast? := rfl
      rw [hLast] at *; grind
/-! ## 3. Inhabited `Obend.Judge` Instance (`mnaCircuitDaeJudge`) & `"mna-dae@1"` `Judge.Format` -/
/-- Problem object for `mnaCircuitDaeJudge` (`"mna-dae@1"`). -/
structure MnaDaeProblem where
  spec   : MnaCircuitSpec
  method : MnaMethod
  trace  : List MnaTraceStep
  deriving DecidableEq, Repr
/-- Gram congruence passivity certificate for `mnaCircuitDaeJudge` (`"mna-dae@1"`). -/
structure MnaDaeCert where
  capGramFactors     : List MnaGramFactor
  condSymGramFactors : List MnaGramFactor
  deriving DecidableEq, Repr
/-- Refusal vocabulary for `mnaCircuitDaeJudge`. -/
inductive MnaDaeClause where
  | badSystemDim
  | badMatrixDims
  | badTraceDimsOrContinuity
  | negativeCapacitanceDiag (node : Nat)
  | negativeConductanceDiag (node : Nat)
  | nonPassiveNonlinearStep (stepIdx : Nat)
  | stepResidualViolation   (stepIdx : Nat)
  | badCapGramCert
  | badCondGramCert
  deriving @[expose] DecidableEq, Repr
/-- Nonlinear branch admissibility proposition for a single step (pure mathematical `Prop`). -/
def MnaStepNonlinearProp (spec : MnaCircuitSpec) (method : MnaMethod) (step : MnaTraceStep) : Prop :=
  ∀ idx, idx < spec.nlBranches.length →
    let b := spec.nlBranches.getD idx ⟨none, none, 0, 0⟩
    let vNext := branchVoltage spec.dim b step.xNext
    let iNext := vecEntry step.iBranchesNext idx
    0 ≤ b.gMin ∧ b.gMin ≤ b.gMax ∧
    0 ≤ vNext * iNext ∧
    0 ≤ (iNext - b.gMin * vNext) * (b.gMax * vNext - iNext) ∧
    (method = .trapezoidal →
      let vPrev := branchVoltage spec.dim b step.xPrev
      let iPrev := vecEntry step.iBranchesPrev idx
      0 ≤ vPrev * iPrev ∧
      0 ≤ (iPrev - b.gMin * vPrev) * (b.gMax * vPrev - iPrev) ∧
      0 ≤ ((vNext + vPrev) / 2) * ((iNext + iPrev) / 2))
def dfltTraceStep : MnaTraceStep := ⟨1, [], [], [], [], [], 0⟩
/-- Exact dimensions and valid nonlinear branch terminal indices (`< s.dim`): out-of-range terminals never silently become ground. -/
@[expose] def MnaSpecDims (s : MnaCircuitSpec) : Prop :=
  s.matC.length = s.dim ∧ (∀ row ∈ s.matC, row.length = s.dim) ∧
  s.matG.length = s.dim ∧ (∀ row ∈ s.matG, row.length = s.dim) ∧
  s.matB.length = s.dim ∧ (∀ row ∈ s.matB, row.length = s.inputDim) ∧
  ∀ b ∈ s.nlBranches,
    b.nodeP?.all (fun p => decide (p < s.dim)) = true ∧
    b.nodeN?.all (fun q => decide (q < s.dim)) = true
instance (s : MnaCircuitSpec) : Decidable (MnaSpecDims s) := by unfold MnaSpecDims; infer_instance
def checkMnaSpecDims (s : MnaCircuitSpec) : Bool := decide (MnaSpecDims s)
theorem checkMnaSpecDims_iff (s : MnaCircuitSpec) : checkMnaSpecDims s = true ↔ MnaSpecDims s := by
  simp [checkMnaSpecDims]
/-- Exact vector dimensions plus inter-step continuity of both state `x` and nonlinear branch currents `iBranches`. -/
@[expose] def MnaTraceDims (s : MnaCircuitSpec) (steps : List MnaTraceStep) : Prop :=
  (∀ t ∈ steps, t.xPrev.length = s.dim ∧ t.xNext.length = s.dim ∧
    t.uInput.length = s.inputDim ∧ t.iBranchesPrev.length = s.nlBranches.length ∧
    t.iBranchesNext.length = s.nlBranches.length) ∧
  ∀ pair ∈ steps.zip (steps.drop 1),
    pair.1.xNext = pair.2.xPrev ∧ pair.1.iBranchesNext = pair.2.iBranchesPrev
instance (s : MnaCircuitSpec) (steps : List MnaTraceStep) : Decidable (MnaTraceDims s steps) := by
  unfold MnaTraceDims; infer_instance
/-- Independent semantic meaning of `mnaCircuitDaeJudge` (pure mathematical `Prop` without calling `check`). -/
@[expose] def MnaDaeMeaning (prob : MnaDaeProblem) (cert : MnaDaeCert) : Prop :=
  MnaSpecDims prob.spec ∧ MnaTraceDims prob.spec prob.trace ∧
  0 < prob.spec.dim ∧
  (∀ i j, i < prob.spec.dim → j < prob.spec.dim →
    matEntry prob.spec.matC i j = gramEntry cert.capGramFactors i j) ∧
  (∀ f, f ∈ cert.capGramFactors → 0 ≤ f.weight) ∧
  (∀ i j, i < prob.spec.dim → j < prob.spec.dim →
    matEntry prob.spec.matG i j + matEntry prob.spec.matG j i = gramEntry cert.condSymGramFactors i j) ∧
  (∀ f, f ∈ cert.condSymGramFactors → 0 ≤ f.weight) ∧
  ∀ k, k < prob.trace.length →
    let step := prob.trace.getD k dfltTraceStep
    0 < step.dt ∧ 0 ≤ step.residualTol ∧ MnaStepNonlinearProp prob.spec prob.method step ∧
    ∀ i, i < prob.spec.dim →
      vecEntry (mnaStepResidual prob.spec prob.method step) i ∈ Interval.mk (-step.residualTol) step.residualTol
private def findFirst (n : Nat) (pred : Nat → Bool) : Option Nat := (List.range n).find? pred
private theorem findFirst_some_iff (n : Nat) (pred : Nat → Bool) (k : Nat)
    (h : findFirst n pred = some k) : k < n ∧ pred k = true :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), List.find?_some h⟩
private theorem findFirst_none_iff (n : Nat) (pred : Nat → Bool)
    (h : findFirst n pred = none) : ∀ i, i < n → pred i = false := by
  simp only [findFirst, List.find?_eq_none, List.mem_range, Bool.not_eq_true] at h; exact h
private theorem findFirst_eq_none_of_all_false (n : Nat) (pred : Nat → Bool)
    (h : ∀ i, i < n → pred i = false) : findFirst n pred = none := by
  simp only [findFirst, List.find?_eq_none, List.mem_range, Bool.not_eq_true]; exact h
private def checkGramMatrix (n : Nat) (target : Nat → Nat → CanonicalRat) (factors : List MnaGramFactor) : Bool :=
  factors.all (fun f => decide (0 ≤ f.weight)) &&
  (List.range n).all (fun i => (List.range n).all (fun j => decide (target i j = gramEntry factors i j)))
private def stepResidualOk (spec : MnaCircuitSpec) (method : MnaMethod) (step : MnaTraceStep) : Bool :=
  decide (0 < step.dt) && decide (0 ≤ step.residualTol) &&
  (List.range spec.dim).all fun i =>
    let r_i := vecEntry (mnaStepResidual spec method step) i
    decide (-step.residualTol ≤ r_i) && decide (r_i ≤ step.residualTol)
/-- Continuity and dimensions are checked in addition to every KCL enclosure. -/
def checkMnaTrace (s : MnaCircuitSpec) (method : MnaMethod) (steps : List MnaTraceStep) : Bool :=
  decide (MnaTraceDims s steps) && steps.all (stepResidualOk s method)
theorem checkMnaTrace_dims {s : MnaCircuitSpec} {method : MnaMethod} {steps : List MnaTraceStep}
    (h : checkMnaTrace s method steps = true) : MnaTraceDims s steps := by
  simp only [checkMnaTrace, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1
/-- Graded certificate checker for `mnaCircuitDaeJudge`. -/
def checkMnaDaeProblem (grade : Nat) (prob : MnaDaeProblem) (cert : MnaDaeCert) :
    Judge.Verdict MnaDaeClause :=
  if grade < prob.trace.length then .uncovered
  else if !checkMnaSpecDims prob.spec then .refused .badMatrixDims []
  else if prob.spec.dim == 0 then .refused .badSystemDim []
  else match findFirst prob.spec.dim (fun i => decide (matEntry prob.spec.matC i i < 0)) with
  | some i => .refused (.negativeCapacitanceDiag i) [i]
  | none =>
    match findFirst prob.spec.dim (fun i => decide (matEntry prob.spec.matG i i < 0)) with
    | some i => .refused (.negativeConductanceDiag i) [i]
    | none =>
      match findFirst prob.trace.length (fun k =>
          !checkMnaStepNonlinear prob.spec prob.method (prob.trace.getD k dfltTraceStep)) with
      | some k => .refused (.nonPassiveNonlinearStep k) [k]
      | none =>
        match findFirst prob.trace.length (fun k =>
            !stepResidualOk prob.spec prob.method (prob.trace.getD k dfltTraceStep)) with
        | some k => .refused (.stepResidualViolation k) [k]
        | none =>
          if !checkMnaTrace prob.spec prob.method prob.trace then .refused .badTraceDimsOrContinuity []
          else if !checkGramMatrix prob.spec.dim (matEntry prob.spec.matC) cert.capGramFactors then
            .refused .badCapGramCert []
          else if !checkGramMatrix prob.spec.dim
              (fun i j => matEntry prob.spec.matG i j + matEntry prob.spec.matG j i) cert.condSymGramFactors then
            .refused .badCondGramCert []
          else .ok
/-- Refuting clauses of `mnaCircuitDaeJudge`. -/
def mnaClauseRefutes : MnaDaeClause → Bool
  | .badMatrixDims | .badTraceDimsOrContinuity | .badSystemDim | .negativeCapacitanceDiag _ | .negativeConductanceDiag _
  | .nonPassiveNonlinearStep _ | .stepResidualViolation _ => true
  | .badCapGramCert | .badCondGramCert => false
private theorem checkMnaStepNonlinear_iff (spec : MnaCircuitSpec) (method : MnaMethod) (step : MnaTraceStep) :
    checkMnaStepNonlinear spec method step = true ↔ MnaStepNonlinearProp spec method step := by
  unfold checkMnaStepNonlinear MnaStepNonlinearProp; rw [list_range_all_iff]
  constructor
  · intro h idx hIdx; have hB := h idx hIdx
    cases method <;> simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    · exact ⟨hB.1.1.1, hB.1.1.2, hB.1.2, hB.2, fun hEq => by cases hEq⟩
    · exact ⟨hB.1.1.1.1.1.1, hB.1.1.1.1.1.2, hB.1.1.1.1.2, hB.1.1.1.2, fun _ => ⟨hB.1.1.2, hB.1.2, hB.2⟩⟩
  · intro h idx hIdx; have hB := h idx hIdx
    cases method <;> simp only [Bool.and_eq_true, decide_eq_true_eq]
    · exact ⟨⟨⟨hB.1, hB.2.1⟩, hB.2.2.1⟩, hB.2.2.2.1⟩
    · have hTr := hB.2.2.2.2 rfl
      exact ⟨⟨⟨⟨⟨⟨hB.1, hB.2.1⟩, hB.2.2.1⟩, hB.2.2.2.1⟩, hTr.1⟩, hTr.2.1⟩, hTr.2.2⟩
private theorem stepResidualOk_iff (spec : MnaCircuitSpec) (method : MnaMethod) (step : MnaTraceStep) :
    stepResidualOk spec method step = true ↔
      (0 < step.dt ∧ 0 ≤ step.residualTol ∧
       ∀ i, i < spec.dim →
         vecEntry (mnaStepResidual spec method step) i ∈ Interval.mk (-step.residualTol) step.residualTol) := by
  unfold stepResidualOk; simp only [Bool.and_eq_true, decide_eq_true_eq, list_range_all_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, fun i hi => (Interval.mem_iff _ _).mpr (h3 i hi)⟩,
         fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, fun i hi => (Interval.mem_iff _ _).mp (h3 i hi)⟩⟩
private theorem checkGramMatrix_iff (n : Nat) (target : Nat → Nat → CanonicalRat) (factors : List MnaGramFactor) :
    checkGramMatrix n target factors = true ↔
      ((∀ i j, i < n → j < n → target i j = gramEntry factors i j) ∧ (∀ f, f ∈ factors → 0 ≤ f.weight)) := by
  unfold checkGramMatrix; simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨fun ⟨hw, he⟩ => ⟨fun i j hi hj => he i hi j hj, hw⟩,
         fun ⟨he, hw⟩ => ⟨hw, fun i hi j hj => he i j hi hj⟩⟩
/-- **Soundness of `checkMnaDaeProblem` (`checkMnaDaeProblem_sound`)**. -/
theorem checkMnaDaeProblem_sound {r : Nat} {prob : MnaDaeProblem} {cert : MnaDaeCert}
    (hOk : checkMnaDaeProblem r prob cert = .ok) : MnaDaeMeaning prob cert := by
  unfold checkMnaDaeProblem at hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  rename_i hDims
  have hDims : MnaSpecDims prob.spec := (checkMnaSpecDims_iff _).mp (by simpa using hDims)
  split at hOk; · cases hOk
  rename_i _ hDimNe
  have hNe0 : prob.spec.dim ≠ 0 := by intro hZ; simp [hZ] at hDimNe
  have hDimPos : 0 < prob.spec.dim := by omega
  cases hC : findFirst prob.spec.dim (fun i => decide (matEntry prob.spec.matC i i < 0)) with
  | some i => rw [hC] at hOk; cases hOk
  | none =>
    rw [hC] at hOk; dsimp only at hOk
    cases hG : findFirst prob.spec.dim (fun i => decide (matEntry prob.spec.matG i i < 0)) with
    | some i => rw [hG] at hOk; cases hOk
    | none =>
      rw [hG] at hOk; dsimp only at hOk
      cases hNl : findFirst prob.trace.length (fun k =>
          !checkMnaStepNonlinear prob.spec prob.method (prob.trace.getD k dfltTraceStep)) with
      | some k => rw [hNl] at hOk; cases hOk
      | none =>
        rw [hNl] at hOk; dsimp only at hOk
        cases hRes : findFirst prob.trace.length (fun k =>
            !stepResidualOk prob.spec prob.method (prob.trace.getD k dfltTraceStep)) with
        | some k => rw [hRes] at hOk; cases hOk
        | none =>
          rw [hRes] at hOk; dsimp only at hOk
          split at hOk; · cases hOk
          rename_i hTraceOk
          have hTraceOk : checkMnaTrace prob.spec prob.method prob.trace = true := by simpa using hTraceOk
          by_cases hCapOk : checkGramMatrix prob.spec.dim (matEntry prob.spec.matC) cert.capGramFactors = true
          · simp only [hCapOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
            by_cases hCondOk : checkGramMatrix prob.spec.dim
                (fun i j => matEntry prob.spec.matG i j + matEntry prob.spec.matG j i) cert.condSymGramFactors = true
            · obtain ⟨hCapE, hCapW⟩ := (checkGramMatrix_iff _ _ _).mp hCapOk
              obtain ⟨hCondE, hCondW⟩ := (checkGramMatrix_iff _ _ _).mp hCondOk
              refine ⟨hDims, checkMnaTrace_dims hTraceOk, hDimPos, hCapE, hCapW, hCondE, hCondW, fun k hk => ?_⟩
              have hNlK : checkMnaStepNonlinear prob.spec prob.method (prob.trace.getD k dfltTraceStep) = true := by
                have hF := findFirst_none_iff _ _ hNl k hk
                cases hB : checkMnaStepNonlinear prob.spec prob.method (prob.trace.getD k dfltTraceStep)
                · rw [hB] at hF; cases hF
                · rfl
              have hResK : stepResidualOk prob.spec prob.method (prob.trace.getD k dfltTraceStep) = true := by
                have hF := findFirst_none_iff _ _ hRes k hk
                cases hB : stepResidualOk prob.spec prob.method (prob.trace.getD k dfltTraceStep)
                · rw [hB] at hF; cases hF
                · rfl
              obtain ⟨hDt, hTol, hIv⟩ := (stepResidualOk_iff _ _ _).mp hResK
              exact ⟨hDt, hTol, (checkMnaStepNonlinear_iff _ _ _).mp hNlK, hIv⟩
            · simp [hCondOk] at hOk
          · simp [hCapOk] at hOk
/-- **Refutation Soundness (`checkMnaDaeProblem_refuted`)**. -/
theorem checkMnaDaeProblem_refuted {r : Nat} {prob : MnaDaeProblem} {cert : MnaDaeCert}
    {k : MnaDaeClause} {p : List Nat}
    (hRef : checkMnaDaeProblem r prob cert = .refused k p)
    (hRefutes : mnaClauseRefutes k = true) :
    ∀ c', ¬ MnaDaeMeaning prob c' := by
  intro c' ⟨hDims, hTraceDims, hDimPos, hCapE, hCapW, hCondE, hCondW, hTrace⟩
  unfold checkMnaDaeProblem at hRef
  split at hRef; · cases hRef
  have hDimsOk := (checkMnaSpecDims_iff _).mpr hDims
  simp only [hDimsOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
  split at hRef
  · rename_i hDimZero; have := beq_iff_eq.mp hDimZero; omega
  · cases hC : findFirst prob.spec.dim (fun i => decide (matEntry prob.spec.matC i i < 0)) with
    | some i =>
      obtain ⟨hi, hNegB⟩ := findFirst_some_iff _ _ i hC
      have := of_decide_eq_true hNegB; have := hCapE i i hi hi
      have := gramEntry_diag_nonneg c'.capGramFactors i hCapW; grind
    | none =>
      rw [hC] at hRef; dsimp only at hRef
      cases hG : findFirst prob.spec.dim (fun i => decide (matEntry prob.spec.matG i i < 0)) with
      | some i =>
        obtain ⟨hi, hNegB⟩ := findFirst_some_iff _ _ i hG
        have := of_decide_eq_true hNegB; have := hCondE i i hi hi
        have := gramEntry_diag_nonneg c'.condSymGramFactors i hCondW; grind
      | none =>
        rw [hG] at hRef; dsimp only at hRef
        cases hNl : findFirst prob.trace.length (fun j =>
            !checkMnaStepNonlinear prob.spec prob.method (prob.trace.getD j dfltTraceStep)) with
        | some j =>
          obtain ⟨hj, hFail⟩ := findFirst_some_iff _ _ j hNl
          have hTrue := (checkMnaStepNonlinear_iff _ _ _).mpr (hTrace j hj).2.2.1
          rw [hTrue] at hFail; cases hFail
        | none =>
          rw [hNl] at hRef; dsimp only at hRef
          cases hRes : findFirst prob.trace.length (fun j =>
              !stepResidualOk prob.spec prob.method (prob.trace.getD j dfltTraceStep)) with
          | some j =>
            obtain ⟨hj, hFail⟩ := findFirst_some_iff _ _ j hRes
            have hT := hTrace j hj
            have hTrue := (stepResidualOk_iff _ _ _).mpr ⟨hT.1, hT.2.1, hT.2.2.2⟩
            rw [hTrue] at hFail; cases hFail
          | none =>
            rw [hRes] at hRef; dsimp only at hRef
            have hTraceOk : checkMnaTrace prob.spec prob.method prob.trace = true := by
              simp only [checkMnaTrace, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
              refine ⟨hTraceDims, ?_⟩
              intro t ht
              obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
              have hT := hTrace j hj
              simpa [List.getD, hj] using (stepResidualOk_iff _ _ _).mpr ⟨hT.1, hT.2.1, hT.2.2.2⟩
            simp only [hTraceOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
            by_cases hCapOk : checkGramMatrix prob.spec.dim (matEntry prob.spec.matC) cert.capGramFactors = true
            · simp only [hCapOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
              by_cases hCondOk : checkGramMatrix prob.spec.dim
                  (fun i j => matEntry prob.spec.matG i j + matEntry prob.spec.matG j i) cert.condSymGramFactors = true
              · simp [hCondOk] at hRef
              · simp only [hCondOk, Bool.not_false, ↓reduceIte] at hRef
                injection hRef with hK _; subst hK; cases hRefutes
            · simp only [hCapOk, Bool.not_false, ↓reduceIte] at hRef
              injection hRef with hK _; subst hK; cases hRefutes
/-- **Completeness of `checkMnaDaeProblem` on the universal fragment (`checkMnaDaeProblem_complete`)**. -/
theorem checkMnaDaeProblem_complete {prob : MnaDaeProblem}
    (hEx : ∃ c, MnaDaeMeaning prob c) :
    ∃ c r, checkMnaDaeProblem r prob c = .ok := by
  obtain ⟨c, hDims, hTraceDims, hDimPos, hCapE, hCapW, hCondE, hCondW, hTrace⟩ := hEx
  refine ⟨c, prob.trace.length, ?_⟩
  unfold checkMnaDaeProblem
  have hDimsOk := (checkMnaSpecDims_iff _).mpr hDims
  have hTraceOk : checkMnaTrace prob.spec prob.method prob.trace = true := by
    simp only [checkMnaTrace, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨hTraceDims, ?_⟩
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    have hT := hTrace j hj
    simpa [List.getD, hj] using (stepResidualOk_iff _ _ _).mpr ⟨hT.1, hT.2.1, hT.2.2.2⟩
  have hNotLt : ¬ prob.trace.length < prob.trace.length := Nat.lt_irrefl _
  have hDimB : (prob.spec.dim == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hCNone : findFirst prob.spec.dim (fun i => decide (matEntry prob.spec.matC i i < 0)) = none :=
    findFirst_eq_none_of_all_false _ _ (fun i hi => by
      have := hCapE i i hi hi; have := gramEntry_diag_nonneg c.capGramFactors i hCapW
      exact decide_eq_false (by grind))
  have hGNone : findFirst prob.spec.dim (fun i => decide (matEntry prob.spec.matG i i < 0)) = none :=
    findFirst_eq_none_of_all_false _ _ (fun i hi => by
      have := hCondE i i hi hi; have := gramEntry_diag_nonneg c.condSymGramFactors i hCondW
      exact decide_eq_false (by grind))
  have hNlNone : findFirst prob.trace.length (fun k =>
      !checkMnaStepNonlinear prob.spec prob.method (prob.trace.getD k dfltTraceStep)) = none :=
    findFirst_eq_none_of_all_false _ _ (fun k hk => by
      have hOk := (checkMnaStepNonlinear_iff _ _ _).mpr (hTrace k hk).2.2.1; rw [hOk]; rfl)
  have hResNone : findFirst prob.trace.length (fun k =>
      !stepResidualOk prob.spec prob.method (prob.trace.getD k dfltTraceStep)) = none :=
    findFirst_eq_none_of_all_false _ _ (fun k hk => by
      have hT := hTrace k hk; have hOk := (stepResidualOk_iff _ _ _).mpr ⟨hT.1, hT.2.1, hT.2.2.2⟩; rw [hOk]; rfl)
  have hCapOk := (checkGramMatrix_iff _ _ _).mpr ⟨hCapE, hCapW⟩
  have hCondOk := (checkGramMatrix_iff _ _ _).mpr ⟨hCondE, hCondW⟩
  simp only [hNotLt, ↓reduceIte, hDimsOk, Bool.not_true, hDimB, Bool.false_eq_true]
  rw [hCNone]; dsimp only
  rw [hGNone]; dsimp only
  rw [hNlNone]; dsimp only
  rw [hResNone]; dsimp only
  simp [hTraceOk, hCapOk, hCondOk]
/-- **Inhabited MNA Circuit DAE Judge (`mnaCircuitDaeJudge`)**. -/
instance mnaCircuitDaeJudge : Judge MnaDaeProblem MnaDaeCert where
  Clause   := MnaDaeClause
  Meaning  := MnaDaeMeaning
  check    := checkMnaDaeProblem
  sound    := checkMnaDaeProblem_sound
  refutes  := mnaClauseRefutes
  refuted  := checkMnaDaeProblem_refuted
  Fragment := fun _ => True
  complete := fun _ hEx => checkMnaDaeProblem_complete hEx
  mono     := by
    intro r r' o c hLe hNe
    unfold checkMnaDaeProblem at hNe ⊢
    by_cases hr : r < o.trace.length
    · simp [hr] at hNe
    · have hr' : ¬ r' < o.trace.length := by omega
      simp [hr, hr']
/-- **Derived Physical Passivity & Step-Enclosure Theorem (`mnaDaeJudge_sound_passivity_and_enclosure`)**. -/
theorem mnaDaeJudge_sound_passivity_and_enclosure {r : Nat} {prob : MnaDaeProblem} {cert : MnaDaeCert}
    (hOk : checkMnaDaeProblem r prob cert = .ok) :
    (∀ x, 0 ≤ mnaStoredEnergy prob.spec.dim prob.spec.matC x) ∧
    (∀ x, 0 ≤ quadFormN prob.spec.dim prob.spec.matG x x) ∧
    (∀ k, k < prob.trace.length →
      let step := prob.trace.getD k dfltTraceStep
      0 < step.dt ∧
      0 ≤ vecDotN prob.spec.dim step.xNext
            (stampNonlinearCurrents prob.spec.dim prob.spec.nlBranches step.iBranchesNext) ∧
      ∀ i, i < prob.spec.dim →
        vecEntry (mnaStepResidual prob.spec prob.method step) i ∈ Interval.mk (-step.residualTol) step.residualTol) := by
  obtain ⟨_, _, _, hCapE, hCapW, hCondE, hCondW, hTrace⟩ := checkMnaDaeProblem_sound hOk
  obtain ⟨_, _, hPsdC⟩ := gramCongruence_symm_and_psd prob.spec.dim prob.spec.matC cert.capGramFactors hCapE hCapW
  refine ⟨fun x => Rat.mul_nonneg (by decide +kernel) (hPsdC x),
          quadFormN_nonneg_of_symSum_gram prob.spec.dim prob.spec.matG cert.condSymGramFactors hCondE hCondW,
          fun k hk => ?_⟩
  have hTk := hTrace k hk
  exact ⟨hTk.1, stampNonlinearCurrents_passive _ _ _ _ (fun idx hIdx => (hTk.2.2.1 idx hIdx).2.2.1), hTk.2.2.2⟩
/-! ### Kernel-Reducible JSON Wire Encoders/Decoders & `"mna-dae@1"` `Judge.Format` -/
private def encodeRatVecJson (v : List CanonicalRat) : SosJson := .arr (v.map sosJsonEncodeRat)
private def decodeRatVecJson (j : SosJson) : Except String (List CanonicalRat) := j.getArr? >>= List.mapM decodeRatJson
private def encodeRatMatJson (M : List (List CanonicalRat)) : SosJson := .arr (M.map encodeRatVecJson)
private def decodeRatMatJson (j : SosJson) : Except String (List (List CanonicalRat)) := j.getArr? >>= List.mapM decodeRatVecJson
private def encodeOptNatJson : Option Nat → SosJson | none => .ofInt (-1) | some k => .ofNat k
private def decodeOptNatJson (j : SosJson) : Except String (Option Nat) := do
  let m ← j.getInt?
  if m = -1 then .ok none else if 0 ≤ m then .ok (some m.toNat) else .error "non-canonical negative branch node"
private def encodeNlBranchJson (b : MnaNonlinearBranch) : SosJson :=
  SosJson.mkObj
    [ ("nodeP", encodeOptNatJson b.nodeP?), ("nodeN", encodeOptNatJson b.nodeN?)
    , ("gMin", sosJsonEncodeRat b.gMin), ("gMax", sosJsonEncodeRat b.gMax) ]
private def decodeNlBranchJson (j : SosJson) : Except String MnaNonlinearBranch := do
  pure ⟨← j.getObjVal? "nodeP" >>= decodeOptNatJson, ← j.getObjVal? "nodeN" >>= decodeOptNatJson,
        ← j.getObjVal? "gMin" >>= decodeRatJson, ← j.getObjVal? "gMax" >>= decodeRatJson⟩
private def encodeTraceStepJson (s : MnaTraceStep) : SosJson :=
  SosJson.mkObj
    [ ("dt", sosJsonEncodeRat s.dt), ("xPrev", encodeRatVecJson s.xPrev), ("xNext", encodeRatVecJson s.xNext)
    , ("uInput", encodeRatVecJson s.uInput), ("iBranchesPrev", encodeRatVecJson s.iBranchesPrev)
    , ("iBranchesNext", encodeRatVecJson s.iBranchesNext), ("residualTol", sosJsonEncodeRat s.residualTol) ]
private def decodeTraceStepJson (j : SosJson) : Except String MnaTraceStep := do
  pure ⟨← j.getObjVal? "dt" >>= decodeRatJson, ← j.getObjVal? "xPrev" >>= decodeRatVecJson,
        ← j.getObjVal? "xNext" >>= decodeRatVecJson, ← j.getObjVal? "uInput" >>= decodeRatVecJson,
        ← j.getObjVal? "iBranchesPrev" >>= decodeRatVecJson, ← j.getObjVal? "iBranchesNext" >>= decodeRatVecJson,
        ← j.getObjVal? "residualTol" >>= decodeRatJson⟩
def encodeMnaDaeProblem (prob : MnaDaeProblem) : String :=
  let methodStr := match prob.method with | .backwardEuler => "be" | .trapezoidal => "trap"
  sosJsonCompress <| SosJson.mkObj
    [ ("dim", .ofNat prob.spec.dim), ("inputDim", .ofNat prob.spec.inputDim)
    , ("matC", encodeRatMatJson prob.spec.matC), ("matG", encodeRatMatJson prob.spec.matG)
    , ("matB", encodeRatMatJson prob.spec.matB)
    , ("nlBranches", .arr (prob.spec.nlBranches.map encodeNlBranchJson))
    , ("method", .str methodStr.toList), ("trace", .arr (prob.trace.map encodeTraceStepJson)) ]
def decodeMnaDaeProblem (wire : String) : Except String MnaDaeProblem := do
  let root ← sosJsonParse wire
  let dim ← root.getObjNat? "dim"
  let inputDim ← root.getObjNat? "inputDim"
  let matC ← root.getObjVal? "matC" >>= decodeRatMatJson
  let matG ← root.getObjVal? "matG" >>= decodeRatMatJson
  let matB ← root.getObjVal? "matB" >>= decodeRatMatJson
  let nlBranches ← (root.getObjVal? "nlBranches" >>= SosJson.getArr?) >>= List.mapM decodeNlBranchJson
  let mStr ← root.getObjStr? "method"
  let method ← if mStr == "be" then .ok MnaMethod.backwardEuler
    else if mStr == "trap" then .ok MnaMethod.trapezoidal else .error s!"unknown MNA method: {mStr}"
  let trace ← (root.getObjVal? "trace" >>= SosJson.getArr?) >>= List.mapM decodeTraceStepJson
  pure ⟨⟨dim, inputDim, matC, matG, matB, nlBranches⟩, method, trace⟩
private def encodeGramFactorJson (f : MnaGramFactor) : SosJson :=
  SosJson.mkObj [("weight", sosJsonEncodeRat f.weight), ("vec", encodeRatVecJson f.vec)]
private def decodeGramFactorJson (j : SosJson) : Except String MnaGramFactor := do
  pure ⟨← j.getObjVal? "weight" >>= decodeRatJson, ← j.getObjVal? "vec" >>= decodeRatVecJson⟩
def encodeMnaDaeCert (cert : MnaDaeCert) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("capGram", .arr (cert.capGramFactors.map encodeGramFactorJson))
    , ("condSymGram", .arr (cert.condSymGramFactors.map encodeGramFactorJson)) ]
def decodeMnaDaeCert (wire : String) : Except String MnaDaeCert := do
  let root ← sosJsonParse wire
  pure ⟨← (root.getObjVal? "capGram" >>= SosJson.getArr?) >>= List.mapM decodeGramFactorJson,
        ← (root.getObjVal? "condSymGram" >>= SosJson.getArr?) >>= List.mapM decodeGramFactorJson⟩
/-- Concrete 2-node RC + passive half-wave diode rectifier MNA DAE benchmark. -/
def rcDiodeRectifierMnaSpec : MnaCircuitSpec :=
  ⟨2, 1, [[1, 0], [0, 2]], [[2, -1], [-1, 2]], [[1], [0]], [⟨some 0, some 1, 0, 1⟩]⟩
def rcDiodeRectifierBeStep : MnaTraceStep :=
  ⟨1, [6, CanonicalRat.mk 1 2], [2, 1], [0], [1], [1], 0⟩
def rcDiodeRectifierMnaProblem : MnaDaeProblem := ⟨rcDiodeRectifierMnaSpec, .backwardEuler, [rcDiodeRectifierBeStep]⟩
def rcDiodeRectifierMnaCert : MnaDaeCert :=
  ⟨[⟨1, [1, 0]⟩, ⟨2, [0, 1]⟩], [⟨2, [1, 0]⟩, ⟨2, [0, 1]⟩, ⟨2, [1, -1]⟩]⟩
/-- Planted non-passive negative-conductance MNA problem (`G_{00} = -3 < 0`). -/
def nonPassiveNegCondMnaProblem : MnaDaeProblem :=
  ⟨{ rcDiodeRectifierMnaSpec with matG := [[-3, 0], [0, 1]] }, .backwardEuler, []⟩
theorem nonPassiveNegCond_refused (grade : Nat) (cert : MnaDaeCert) :
    checkMnaDaeProblem grade nonPassiveNegCondMnaProblem cert =
      .refused (.negativeConductanceDiag 0) [0] := by
  unfold checkMnaDaeProblem nonPassiveNegCondMnaProblem rcDiodeRectifierMnaSpec
  have hNotLt : ¬ grade < ([] : List MnaTraceStep).length := by simp
  simp only [hNotLt, ↓reduceIte]; rfl
/-- Registered `"mna-dae@1"` `Judge.Format`. -/
def mnaCircuitDaeFormat : Judge.Format where
  name := "mna-dae"; version := "1"; Obj := MnaDaeProblem; Cert := MnaDaeCert
  judge := mnaCircuitDaeJudge; decodeObj := decodeMnaDaeProblem; decodeCert := decodeMnaDaeCert
  trust := .kernel; regime := .decidable
  bad := (nonPassiveNegCondMnaProblem, rcDiodeRectifierMnaCert)
  badGrade := 0; bad_refused := ⟨.negativeConductanceDiag 0, [0], nonPassiveNegCond_refused 0 rcDiodeRectifierMnaCert⟩
-- Inhabitedness witnesses required by `lean/uninhabited-premise-risk`
example : checkMnaStepEnclosure rcDiodeRectifierMnaSpec .backwardEuler rcDiodeRectifierBeStep = true := by decide +kernel
example : checkMnaDaeProblem 1 rcDiodeRectifierMnaProblem rcDiodeRectifierMnaCert = .ok := by decide +kernel
/-! ## 4. True 5-Cell (6-Level) SiC Flying-Capacitor Multilevel (`FCML`) Switched-Capacitor Hybrid Model -/
/-- Instantaneous 5-cell FCML switching vector $s = (s_1, s_2, s_3, s_4, s_5) \in \{0, 1\}^5$. -/
structure FcmlSwitchState5 where
  (s1 s2 s3 s4 s5 : Bool)
  deriving DecidableEq, Repr
/-- Map a complementary SiC half-bridge cell state `Bool` into $\{0, 1\} \subset \mathbb{Q}$. -/
def swBit (b : Bool) : CanonicalRat := if b then 1 else 0
/-- Physical parameters of a 5-cell (6-level) SiC FCML leg: 4 flying capacitances $C_{1..4} > 0$ and $V_{\text{dc}} > 0$. -/
structure FcmlCapSpec4 where
  (c1 c2 c3 c4 vdc : CanonicalRat)
  deriving DecidableEq, Repr
@[expose] def FcmlCapSpec4.Spec (p : FcmlCapSpec4) : Prop :=
  0 < p.c1 ∧ 0 < p.c2 ∧ 0 < p.c3 ∧ 0 < p.c4 ∧ 0 < p.vdc
/-- Flying-capacitor voltage state $v_C = (v_{C_1}, v_{C_2}, v_{C_3}, v_{C_4})$. -/
structure FcmlCapState4 where
  (vc1 vc2 vc3 vc4 : CanonicalRat)
  deriving DecidableEq, Repr
/-- Nominal balanced 5-cell FCML voltage ladder $v_{C_k}^* = \frac{k}{5} V_{\text{dc}}$ ($k = 1..4$). -/
def fcmlNominalLadder (vdc : CanonicalRat) : FcmlCapState4 :=
  ⟨vdc / 5, (2 * vdc) / 5, (3 * vdc) / 5, (4 * vdc) / 5⟩
/-- Capacitor voltage unbalance error $e_k = v_{C_k} - \frac{k}{5} V_{\text{dc}}$ ($k = 1..4$). -/
def fcmlCapError (vdc : CanonicalRat) (v : FcmlCapState4) : FcmlCapState4 :=
  let nom := fcmlNominalLadder vdc
  ⟨v.vc1 - nom.vc1, v.vc2 - nom.vc2, v.vc3 - nom.vc3, v.vc4 - nom.vc4⟩
/-- Exact KVL switch-node voltage $v_{\text{sw}}(s, v_C, V_{\text{dc}}) = \sum_{m=1}^5 s_m (v_{C_m} - v_{C_{m-1}})$. -/
def fcmlSwitchNodeVoltage (vdc : CanonicalRat) (s : FcmlSwitchState5) (v : FcmlCapState4) : CanonicalRat :=
  swBit s.s1 * v.vc1 + swBit s.s2 * (v.vc2 - v.vc1) + swBit s.s3 * (v.vc3 - v.vc2) +
  swBit s.s4 * (v.vc4 - v.vc3) + swBit s.s5 * (vdc - v.vc4)
/-- Per-cell SiC FET off-state voltage stress $(v_{C_1}, v_{C_2}-v_{C_1}, v_{C_3}-v_{C_2}, v_{C_4}-v_{C_3}, V_{\text{dc}}-v_{C_4})$. -/
structure FcmlCellBlocking5 where
  (vb1 vb2 vb3 vb4 vb5 : CanonicalRat)
  deriving DecidableEq, Repr
def fcmlCellBlockingVoltages (vdc : CanonicalRat) (v : FcmlCapState4) : FcmlCellBlocking5 :=
  ⟨v.vc1, v.vc2 - v.vc1, v.vc3 - v.vc2, v.vc4 - v.vc3, vdc - v.vc4⟩
/-- **Exact Switched-Capacitor KCL Subinterval Recurrence (`stepFcmlSwitchSubinterval`)**. -/
def stepFcmlSwitchSubinterval (p : FcmlCapSpec4) (dt iL : CanonicalRat)
    (s : FcmlSwitchState5) (v : FcmlCapState4) : FcmlCapState4 :=
  ⟨v.vc1 + (dt / p.c1) * ((swBit s.s2 - swBit s.s1) * iL),
   v.vc2 + (dt / p.c2) * ((swBit s.s3 - swBit s.s2) * iL),
   v.vc3 + (dt / p.c3) * ((swBit s.s4 - swBit s.s3) * iL),
   v.vc4 + (dt / p.c4) * ((swBit s.s5 - swBit s.s4) * iL)⟩
/-- Run a sequence of switched-capacitor subintervals at held inductor current `iL` and subinterval `dt`. -/
def runFcmlSubintervals (p : FcmlCapSpec4) (dt iL : CanonicalRat) :
    List FcmlSwitchState5 → FcmlCapState4 → FcmlCapState4
  | [], v => v
  | s :: ss, v => runFcmlSubintervals p dt iL ss (stepFcmlSwitchSubinterval p dt iL s v)
/-- **Balanced 6-Level Output & Instantaneous KCL/KVL Power Conservation (`fcml_instantaneous_power_conservation`)**. -/
theorem fcml_instantaneous_power_conservation
    (vdc iL : CanonicalRat) (s : FcmlSwitchState5) (v : FcmlCapState4) :
    fcmlSwitchNodeVoltage vdc s (fcmlNominalLadder vdc) =
      ((swBit s.s1 + swBit s.s2 + swBit s.s3 + swBit s.s4 + swBit s.s5) / 5) * vdc ∧
    swBit s.s5 * vdc * iL =
      fcmlSwitchNodeVoltage vdc s v * iL +
      (v.vc1 * ((swBit s.s2 - swBit s.s1) * iL) + v.vc2 * ((swBit s.s3 - swBit s.s2) * iL) +
       v.vc3 * ((swBit s.s4 - swBit s.s3) * iL) + v.vc4 * ((swBit s.s5 - swBit s.s4) * iL)) := by
  unfold fcmlSwitchNodeVoltage fcmlNominalLadder; exact ⟨by grind, by grind⟩
/-- **SiC FET Blocking Voltage Safety from Unbalance Ball (`fcml_cell_blocking_bounded_by_unbalance`)**. -/
theorem fcml_cell_blocking_bounded_by_unbalance
    (vdc dV vFetMax : CanonicalRat) (v : FcmlCapState4)
    (hdV0 : 0 ≤ dV) (hPosMargin : 2 * dV ≤ vdc / 5) (hFetMargin : vdc / 5 + 2 * dV ≤ vFetMax)
    (hE1 : -dV ≤ (fcmlCapError vdc v).vc1 ∧ (fcmlCapError vdc v).vc1 ≤ dV)
    (hE2 : -dV ≤ (fcmlCapError vdc v).vc2 ∧ (fcmlCapError vdc v).vc2 ≤ dV)
    (hE3 : -dV ≤ (fcmlCapError vdc v).vc3 ∧ (fcmlCapError vdc v).vc3 ≤ dV)
    (hE4 : -dV ≤ (fcmlCapError vdc v).vc4 ∧ (fcmlCapError vdc v).vc4 ≤ dV) :
    let b := fcmlCellBlockingVoltages vdc v
    (0 ≤ b.vb1 ∧ b.vb1 ≤ vFetMax) ∧ (0 ≤ b.vb2 ∧ b.vb2 ≤ vFetMax) ∧
    (0 ≤ b.vb3 ∧ b.vb3 ≤ vFetMax) ∧ (0 ≤ b.vb4 ∧ b.vb4 ≤ vFetMax) ∧
    (0 ≤ b.vb5 ∧ b.vb5 ≤ vFetMax) := by
  unfold fcmlCapError fcmlNominalLadder at hE1 hE2 hE3 hE4
  dsimp only [fcmlCellBlockingVoltages]
  exact ⟨⟨by grind, by grind⟩, ⟨by grind, by grind⟩, ⟨by grind, by grind⟩,
         ⟨by grind, by grind⟩, ⟨by grind, by grind⟩⟩
/-! ## 5. Symmetric 5-Phase PSP Zero-Net-Charge-Drift & Saturated Active Duty-Trim Contraction -/
/-- Cyclic cell permutation $\sigma(s_1, s_2, s_3, s_4, s_5) = (s_2, s_3, s_4, s_5, s_1)$ for 72°-shifted 5-phase PSP. -/
def fcmlCyclicShift (s : FcmlSwitchState5) : FcmlSwitchState5 := ⟨s.s2, s.s3, s.s4, s.s5, s.s1⟩
/-- The 5 symmetric PSP phase states $[s, \sigma(s), \sigma^2(s), \sigma^3(s), \sigma^4(s)]$. -/
def fcmlSymmetricPsp5Cycle (s0 : FcmlSwitchState5) : List FcmlSwitchState5 :=
  let s1 := fcmlCyclicShift s0; let s2 := fcmlCyclicShift s1
  let s3 := fcmlCyclicShift s2; let s4 := fcmlCyclicShift s3
  [s0, s1, s2, s3, s4]
/-- **Cyclic 5-Phase PSP Zero-Sum Incidence Theorem (`fcml_psp_cyclic_diff_sum_zero`)**. -/
theorem fcml_psp_cyclic_diff_sum_zero (s0 : FcmlSwitchState5) :
    let cyc := fcmlSymmetricPsp5Cycle s0
    let q0 := cyc.getD 0 s0; let q1 := cyc.getD 1 s0; let q2 := cyc.getD 2 s0
    let q3 := cyc.getD 3 s0; let q4 := cyc.getD 4 s0
    (swBit q0.s2 - swBit q0.s1) + (swBit q1.s2 - swBit q1.s1) + (swBit q2.s2 - swBit q2.s1) +
      (swBit q3.s2 - swBit q3.s1) + (swBit q4.s2 - swBit q4.s1) = 0 ∧
    (swBit q0.s3 - swBit q0.s2) + (swBit q1.s3 - swBit q1.s2) + (swBit q2.s3 - swBit q2.s2) +
      (swBit q3.s3 - swBit q3.s2) + (swBit q4.s3 - swBit q4.s2) = 0 ∧
    (swBit q0.s4 - swBit q0.s3) + (swBit q1.s4 - swBit q1.s3) + (swBit q2.s4 - swBit q2.s3) +
      (swBit q3.s4 - swBit q3.s3) + (swBit q4.s4 - swBit q4.s3) = 0 ∧
    (swBit q0.s5 - swBit q0.s4) + (swBit q1.s5 - swBit q1.s4) + (swBit q2.s5 - swBit q2.s4) +
      (swBit q3.s5 - swBit q3.s4) + (swBit q4.s5 - swBit q4.s4) = 0 := by
  dsimp [fcmlSymmetricPsp5Cycle, fcmlCyclicShift]; exact ⟨by grind, by grind, by grind, by grind⟩
/-- **Symmetric 5-Phase PSP Zero-Net-Charge-Drift (`fcml_psp_nominal_zero_drift`)**. -/
theorem fcml_psp_nominal_zero_drift
    (p : FcmlCapSpec4) (dt iL : CanonicalRat)
    (q0 q1 q2 q3 q4 : FcmlSwitchState5) (v0 : FcmlCapState4)
    (hBal1 : (swBit q0.s2 - swBit q0.s1) + (swBit q1.s2 - swBit q1.s1) + (swBit q2.s2 - swBit q2.s1) +
             (swBit q3.s2 - swBit q3.s1) + (swBit q4.s2 - swBit q4.s1) = 0)
    (hBal2 : (swBit q0.s3 - swBit q0.s2) + (swBit q1.s3 - swBit q1.s2) + (swBit q2.s3 - swBit q2.s2) +
             (swBit q3.s3 - swBit q3.s2) + (swBit q4.s3 - swBit q4.s2) = 0)
    (hBal3 : (swBit q0.s4 - swBit q0.s3) + (swBit q1.s4 - swBit q1.s3) + (swBit q2.s4 - swBit q2.s3) +
             (swBit q3.s4 - swBit q3.s3) + (swBit q4.s4 - swBit q4.s3) = 0)
    (hBal4 : (swBit q0.s5 - swBit q0.s4) + (swBit q1.s5 - swBit q1.s4) + (swBit q2.s5 - swBit q2.s4) +
             (swBit q3.s5 - swBit q3.s4) + (swBit q4.s5 - swBit q4.s4) = 0) :
    runFcmlSubintervals p dt iL [q0, q1, q2, q3, q4] v0 = v0 := by
  dsimp [runFcmlSubintervals, stepFcmlSwitchSubinterval]; cases v0; congr 1 <;> grind
/-- Per-cell active duty-cycle trims $(\Delta d_1, \Delta d_2, \Delta d_3, \Delta d_4, \Delta d_5)$. -/
structure FcmlDutyTrim5 where
  (dd1 dd2 dd3 dd4 dd5 : CanonicalRat)
  deriving DecidableEq, Repr
/-- Zero-sum 5-cell duty-trim synthesizer ($\Delta d_{k+1} - \Delta d_k = \delta_k$ and $\sum_{m=1}^5 \Delta d_m = 0$). -/
def fcmlSynthesizeZeroSumTrim (del1 del2 del3 del4 : CanonicalRat) : FcmlDutyTrim5 :=
  let dd1 := -(4 * del1 + 3 * del2 + 2 * del3 + del4) / 5
  let dd2 := dd1 + del1; let dd3 := dd2 + del2; let dd4 := dd3 + del3; let dd5 := dd4 + del4
  ⟨dd1, dd2, dd3, dd4, dd5⟩
theorem fcmlSynthesizeZeroSumTrim_exact (del1 del2 del3 del4 deltaMax : CanonicalRat)
    (h1 : -deltaMax ≤ del1 ∧ del1 ≤ deltaMax) (h2 : -deltaMax ≤ del2 ∧ del2 ≤ deltaMax)
    (h3 : -deltaMax ≤ del3 ∧ del3 ≤ deltaMax) (h4 : -deltaMax ≤ del4 ∧ del4 ≤ deltaMax) :
    let t := fcmlSynthesizeZeroSumTrim del1 del2 del3 del4
    t.dd2 - t.dd1 = del1 ∧ t.dd3 - t.dd2 = del2 ∧ t.dd4 - t.dd3 = del3 ∧ t.dd5 - t.dd4 = del4 ∧
    t.dd1 + t.dd2 + t.dd3 + t.dd4 + t.dd5 = 0 ∧
    (-2 * deltaMax ≤ t.dd1 ∧ t.dd1 ≤ 2 * deltaMax) ∧ (-2 * deltaMax ≤ t.dd2 ∧ t.dd2 ≤ 2 * deltaMax) ∧
    (-2 * deltaMax ≤ t.dd3 ∧ t.dd3 ≤ 2 * deltaMax) ∧ (-2 * deltaMax ≤ t.dd4 ∧ t.dd4 ≤ 2 * deltaMax) ∧
    (-2 * deltaMax ≤ t.dd5 ∧ t.dd5 ≤ 2 * deltaMax) := by
  dsimp [fcmlSynthesizeZeroSumTrim]
  exact ⟨by grind, by grind, by grind, by grind, by grind,
         ⟨by grind, by grind⟩, ⟨by grind, by grind⟩, ⟨by grind, by grind⟩,
         ⟨by grind, by grind⟩, ⟨by grind, by grind⟩⟩
/-- Symmetric rational saturation clamp into $[-\delta_{\max}, \delta_{\max}]$. -/
def ratClampSym (lim x : CanonicalRat) : CanonicalRat := max (-lim) (min lim x)
/-- Current-sign-aware saturated proportional differential duty trim
$\delta_k = \operatorname{clamp}_{[-\delta_{\max}, \delta_{\max}]}(-K_{\text{trim}} \operatorname{sgn}(i_L) e_k)$. -/
def fcmlClampedDiffTrim (kTrim deltaMax iL ek : CanonicalRat) : CanonicalRat :=
  let sgn : CanonicalRat := if 0 ≤ iL then 1 else -1
  ratClampSym deltaMax (-(kTrim * sgn * ek))
/-- One PWM-period averaged FCML active-balancing step with zero-sum saturated duty trims. -/
def stepFcmlActiveBalance
    (p : FcmlCapSpec4) (tPwm kTrim deltaMax iL : CanonicalRat)
    (eta : FcmlCapState4) (v : FcmlCapState4) : FcmlCapState4 :=
  let e := fcmlCapError p.vdc v
  let tr := fcmlSynthesizeZeroSumTrim
    (fcmlClampedDiffTrim kTrim deltaMax iL e.vc1) (fcmlClampedDiffTrim kTrim deltaMax iL e.vc2)
    (fcmlClampedDiffTrim kTrim deltaMax iL e.vc3) (fcmlClampedDiffTrim kTrim deltaMax iL e.vc4)
  { vc1 := v.vc1 + (tPwm / p.c1) * ((tr.dd2 - tr.dd1) * iL) + eta.vc1
  , vc2 := v.vc2 + (tPwm / p.c2) * ((tr.dd3 - tr.dd2) * iL) + eta.vc2
  , vc3 := v.vc3 + (tPwm / p.c3) * ((tr.dd4 - tr.dd3) * iL) + eta.vc3
  , vc4 := v.vc4 + (tPwm / p.c4) * ((tr.dd5 - tr.dd4) * iL) + eta.vc4 }
/-- Multi-cycle trajectory of `stepFcmlActiveBalance`. -/
def runFcmlActiveBalance
    (p : FcmlCapSpec4) (tPwm kTrim deltaMax : CanonicalRat)
    (iLSeq : Nat → CanonicalRat) (etaSeq : Nat → FcmlCapState4)
    (v0 : FcmlCapState4) : Nat → FcmlCapState4
  | 0 => v0
  | n + 1 => stepFcmlActiveBalance p tPwm kTrim deltaMax (iLSeq n) (etaSeq n)
      (runFcmlActiveBalance p tPwm kTrim deltaMax iLSeq etaSeq v0 n)
/-- Infinity-norm Lyapunov unbalance energy $V_\infty(v_C) = \max_{k=1..4} |v_{C_k} - \frac{k}{5} V_{\text{dc}}|$. -/
def fcmlMaxUnbalance (vdc : CanonicalRat) (v : FcmlCapState4) : CanonicalRat :=
  let e := fcmlCapError vdc v
  max (max (ratAbs e.vc1) (ratAbs e.vc2)) (max (ratAbs e.vc3) (ratAbs e.vc4))
/-- Structural rational power $r^n$. -/
def fcmlRatPow (r : CanonicalRat) : Nat → CanonicalRat
  | 0 => 1
  | n + 1 => r * fcmlRatPow r n
private theorem rat_div_nonneg (a b : CanonicalRat) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  have hEq : b * (a / b) = a := by grind
  exact Rat.le_of_mul_le_mul_left (by rw [hEq]; grind) hb
private theorem ratClampSym_neg (lim y : CanonicalRat) (hLim : 0 ≤ lim) :
    ratClampSym lim (-y) = -ratClampSym lim y := by unfold ratClampSym; grind
private theorem rat_max4_le {a1 a2 a3 a4 b : CanonicalRat}
    (h1 : a1 ≤ b) (h2 : a2 ≤ b) (h3 : a3 ≤ b) (h4 : a4 ≤ b) :
    max (max a1 a2) (max a3 a4) ≤ b := by grind
private theorem rat_max4_parts {a1 a2 a3 a4 b : CanonicalRat}
    (h : max (max a1 a2) (max a3 a4) ≤ b) : a1 ≤ b ∧ a2 ≤ b ∧ a3 ≤ b ∧ a4 ≤ b := by grind
private theorem rat_le_trans_add {x a b c : CanonicalRat} (h1 : x ≤ a + c) (h2 : a ≤ b) : x ≤ b + c := by grind
private theorem clamped_channel_contracts
    (cap tPwm kTrim deltaMax iL eMax gamma eta etaMax e : CanonicalRat)
    (hCap : 0 < cap) (hTpwm : 0 ≤ tPwm) (hK : 0 ≤ kTrim) (hDelta : 0 < deltaMax)
    (hEMax : 0 < eMax)
    (hNoOvershoot : (tPwm / cap) * ratAbs iL * kTrim ≤ 1)
    (hGammaLin : gamma ≤ (tPwm / cap) * ratAbs iL * kTrim)
    (hGammaSat : gamma * eMax ≤ (tPwm / cap) * ratAbs iL * deltaMax)
    (hE : ratAbs e ≤ eMax) (hEta : ratAbs eta ≤ etaMax) :
    ratAbs (e + (tPwm / cap) * (fcmlClampedDiffTrim kTrim deltaMax iL e * iL) + eta) ≤
      (1 - gamma) * ratAbs e + etaMax := by
  have hGain0 : 0 ≤ (tPwm / cap) * ratAbs iL := Rat.mul_nonneg (rat_div_nonneg tPwm cap hTpwm hCap) (ratAbs_nonneg iL)
  have hProdEq : fcmlClampedDiffTrim kTrim deltaMax iL e * iL = -(ratClampSym deltaMax (kTrim * e) * ratAbs iL) := by
    unfold fcmlClampedDiffTrim ratAbs
    by_cases hi : 0 ≤ iL
    · simp only [hi, ↓reduceIte]
      have hArg : -(kTrim * 1 * e) = -(kTrim * e) := by grind
      rw [hArg, ratClampSym_neg deltaMax _ (by grind)]; grind
    · simp only [hi, ↓reduceIte]
      have hArg : -(kTrim * -1 * e) = kTrim * e := by grind
      rw [hArg]; grind
  rw [hProdEq]
  let g := (tPwm / cap) * ratAbs iL
  have hRew : e + (tPwm / cap) * (-(ratClampSym deltaMax (kTrim * e) * ratAbs iL)) =
      e - g * ratClampSym deltaMax (kTrim * e) := by dsimp [g]; grind
  rw [hRew]
  have hEtaB := (ratAbs_le_iff eta etaMax).mp hEta
  have hEB := (ratAbs_le_iff e eMax).mp hE
  rw [ratAbs_le_iff]
  by_cases he0 : 0 ≤ e
  · have hAbsE : ratAbs e = e := by unfold ratAbs; simp [he0]
    rw [hAbsE]
    by_cases hSat : kTrim * e ≤ deltaMax
    · have hKe0 : 0 ≤ kTrim * e := Rat.mul_nonneg hK he0
      have hClamp : ratClampSym deltaMax (kTrim * e) = kTrim * e := by unfold ratClampSym; grind
      rw [hClamp]
      have hUp := Rat.mul_le_mul_of_nonneg_right hNoOvershoot he0
      have hLo := Rat.mul_le_mul_of_nonneg_right hGammaLin he0
      exact ⟨by grind, by grind⟩
    · have hClamp : ratClampSym deltaMax (kTrim * e) = deltaMax := by unfold ratClampSym; grind
      rw [hClamp]
      have hSub : g * deltaMax ≤ e := by
        have h1 := Rat.mul_le_mul_of_nonneg_left (by grind : deltaMax ≤ kTrim * e) hGain0
        have h2 := Rat.mul_le_mul_of_nonneg_right hNoOvershoot he0; grind
      have hDecay : gamma * e ≤ g * deltaMax := by
        have hA := Rat.mul_le_mul_of_nonneg_right hGammaSat he0
        have hB := Rat.mul_le_mul_of_nonneg_left hEB.2 (Rat.mul_nonneg hGain0 (by grind : 0 ≤ deltaMax))
        exact Rat.le_of_mul_le_mul_right (by grind : (gamma * e) * eMax ≤ (g * deltaMax) * eMax) hEMax
      exact ⟨by grind, by grind⟩
  · have hAbsE : ratAbs e = -e := by unfold ratAbs; simp [he0]
    rw [hAbsE]
    let u := -e; have hu0 : 0 ≤ u := by dsimp [u]; grind
    have huMax : u ≤ eMax := by dsimp [u]; grind
    by_cases hSat : kTrim * u ≤ deltaMax
    · have hKu0 : 0 ≤ kTrim * u := Rat.mul_nonneg hK hu0
      have hClamp : ratClampSym deltaMax (kTrim * e) = -(kTrim * u) := by unfold ratClampSym; dsimp [u]; grind
      rw [hClamp]
      have hUp := Rat.mul_le_mul_of_nonneg_right hNoOvershoot hu0
      have hLo := Rat.mul_le_mul_of_nonneg_right hGammaLin hu0
      dsimp [u] at *; exact ⟨by grind, by grind⟩
    · have hClamp : ratClampSym deltaMax (kTrim * e) = -deltaMax := by unfold ratClampSym; dsimp [u] at hSat; grind
      rw [hClamp]
      have hSub : g * deltaMax ≤ u := by
        have h1 := Rat.mul_le_mul_of_nonneg_left (by grind : deltaMax ≤ kTrim * u) hGain0
        have h2 := Rat.mul_le_mul_of_nonneg_right hNoOvershoot hu0; grind
      have hDecay : gamma * u ≤ g * deltaMax := by
        have hA := Rat.mul_le_mul_of_nonneg_right hGammaSat hu0
        have hB := Rat.mul_le_mul_of_nonneg_left huMax (Rat.mul_nonneg hGain0 (by grind : 0 ≤ deltaMax))
        exact Rat.le_of_mul_le_mul_right (by grind : (gamma * u) * eMax ≤ (g * deltaMax) * eMax) hEMax
      dsimp [u] at *; exact ⟨by grind, by grind⟩
/-- **Saturated Active Duty-Trim Lyapunov Contraction & Safe SiC FET Blocking (`fcml_active_trim_contracts_unbalance`)**:
Bounded zero-sum duty trims contract $V_\infty(v_C[n]) = \max_{k=1..4} |v_{C_k}[n] - \frac{k}{5} V_{\text{dc}}|$
exponentially into $R_{\text{bal}} = \eta_{\max} / \gamma$, preserve $V_\infty(v_C[n]) \le E_{\max}$, and
keep every SiC FET across all 5 cells within $[0, V_{\text{fet,max}}]$. -/
theorem fcml_active_trim_contracts_unbalance
    (p : FcmlCapSpec4) (hSpec : p.Spec)
    (tPwm kTrim deltaMax iLMin eMax gamma etaMax rBal vFetMax : CanonicalRat)
    (hTpwm : 0 ≤ tPwm) (hK : 0 ≤ kTrim) (hDelta : 0 < deltaMax)
    (hEMax : 0 < eMax) (hGammaPos : 0 < gamma) (hGammaLe1 : gamma ≤ 1)
    (hBall : gamma * rBal = etaMax) (hBallInEnv : rBal ≤ eMax)
    (hPosMargin : 2 * eMax ≤ p.vdc / 5) (hFetMargin : p.vdc / 5 + 2 * eMax ≤ vFetMax)
    (iLSeq : Nat → CanonicalRat)
    (hNoOvershoot : ∀ n,
      (tPwm / p.c1) * ratAbs (iLSeq n) * kTrim ≤ 1 ∧ (tPwm / p.c2) * ratAbs (iLSeq n) * kTrim ≤ 1 ∧
      (tPwm / p.c3) * ratAbs (iLSeq n) * kTrim ≤ 1 ∧ (tPwm / p.c4) * ratAbs (iLSeq n) * kTrim ≤ 1)
    (hILMin : ∀ n, iLMin ≤ ratAbs (iLSeq n))
    (hGamma1 : gamma ≤ (tPwm / p.c1) * iLMin * kTrim ∧ gamma * eMax ≤ (tPwm / p.c1) * iLMin * deltaMax)
    (hGamma2 : gamma ≤ (tPwm / p.c2) * iLMin * kTrim ∧ gamma * eMax ≤ (tPwm / p.c2) * iLMin * deltaMax)
    (hGamma3 : gamma ≤ (tPwm / p.c3) * iLMin * kTrim ∧ gamma * eMax ≤ (tPwm / p.c3) * iLMin * deltaMax)
    (hGamma4 : gamma ≤ (tPwm / p.c4) * iLMin * kTrim ∧ gamma * eMax ≤ (tPwm / p.c4) * iLMin * deltaMax)
    (etaSeq : Nat → FcmlCapState4)
    (hEtaSeq : ∀ n,
      ratAbs (etaSeq n).vc1 ≤ etaMax ∧ ratAbs (etaSeq n).vc2 ≤ etaMax ∧
      ratAbs (etaSeq n).vc3 ≤ etaMax ∧ ratAbs (etaSeq n).vc4 ≤ etaMax)
    (v0 : FcmlCapState4) (hInit : fcmlMaxUnbalance p.vdc v0 ≤ eMax) :
    let traj := runFcmlActiveBalance p tPwm kTrim deltaMax iLSeq etaSeq v0
    (∀ n, fcmlMaxUnbalance p.vdc (traj n) ≤ eMax) ∧
    (∀ n, fcmlMaxUnbalance p.vdc (traj n) - rBal ≤
      fcmlRatPow (1 - gamma) n * (fcmlMaxUnbalance p.vdc v0 - rBal)) ∧
    (∀ n,
      let b := fcmlCellBlockingVoltages p.vdc (traj n)
      (0 ≤ b.vb1 ∧ b.vb1 ≤ vFetMax) ∧ (0 ≤ b.vb2 ∧ b.vb2 ≤ vFetMax) ∧
      (0 ≤ b.vb3 ∧ b.vb3 ≤ vFetMax) ∧ (0 ≤ b.vb4 ∧ b.vb4 ≤ vFetMax) ∧
      (0 ≤ b.vb5 ∧ b.vb5 ≤ vFetMax)) := by
  intro traj; obtain ⟨hc1, hc2, hc3, hc4, _⟩ := hSpec
  have hStepBound : ∀ n,
      fcmlMaxUnbalance p.vdc (traj n) ≤ eMax →
      fcmlMaxUnbalance p.vdc (traj (n + 1)) ≤ (1 - gamma) * fcmlMaxUnbalance p.vdc (traj n) + etaMax := by
    intro n hEnvN
    let vn := traj n; let en := fcmlCapError p.vdc vn
    have hMaxDef := rat_max4_parts (@Rat.le_refl (fcmlMaxUnbalance p.vdc vn))
    have hEnvParts := rat_max4_parts hEnvN
    have hLiftLin : ∀ c, 0 < c → gamma ≤ (tPwm / c) * iLMin * kTrim →
        gamma ≤ (tPwm / c) * ratAbs (iLSeq n) * kTrim := fun c hc hG =>
      Rat.le_trans hG (Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left (hILMin n) (rat_div_nonneg tPwm c hTpwm hc)) hK)
    have hLiftSat : ∀ c, 0 < c → gamma * eMax ≤ (tPwm / c) * iLMin * deltaMax →
        gamma * eMax ≤ (tPwm / c) * ratAbs (iLSeq n) * deltaMax := fun c hc hG =>
      Rat.le_trans hG (Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left (hILMin n) (rat_div_nonneg tPwm c hTpwm hc)) (by grind : 0 ≤ deltaMax))
    have hC1 := clamped_channel_contracts p.c1 tPwm kTrim deltaMax (iLSeq n) eMax gamma (etaSeq n).vc1 etaMax en.vc1
      hc1 hTpwm hK hDelta hEMax (hNoOvershoot n).1 (hLiftLin _ hc1 hGamma1.1)
      (hLiftSat _ hc1 hGamma1.2) hEnvParts.1 (hEtaSeq n).1
    have hC2 := clamped_channel_contracts p.c2 tPwm kTrim deltaMax (iLSeq n) eMax gamma (etaSeq n).vc2 etaMax en.vc2
      hc2 hTpwm hK hDelta hEMax (hNoOvershoot n).2.1 (hLiftLin _ hc2 hGamma2.1)
      (hLiftSat _ hc2 hGamma2.2) hEnvParts.2.1 (hEtaSeq n).2.1
    have hC3 := clamped_channel_contracts p.c3 tPwm kTrim deltaMax (iLSeq n) eMax gamma (etaSeq n).vc3 etaMax en.vc3
      hc3 hTpwm hK hDelta hEMax (hNoOvershoot n).2.2.1 (hLiftLin _ hc3 hGamma3.1)
      (hLiftSat _ hc3 hGamma3.2) hEnvParts.2.2.1 (hEtaSeq n).2.2.1
    have hC4 := clamped_channel_contracts p.c4 tPwm kTrim deltaMax (iLSeq n) eMax gamma (etaSeq n).vc4 etaMax en.vc4
      hc4 hTpwm hK hDelta hEMax (hNoOvershoot n).2.2.2 (hLiftLin _ hc4 hGamma4.1)
      (hLiftSat _ hc4 hGamma4.2) hEnvParts.2.2.2 (hEtaSeq n).2.2.2
    have h1mg : 0 ≤ 1 - gamma := by grind
    have hM1 := Rat.mul_le_mul_of_nonneg_left hMaxDef.1 h1mg
    have hM2 := Rat.mul_le_mul_of_nonneg_left hMaxDef.2.1 h1mg
    have hM3 := Rat.mul_le_mul_of_nonneg_left hMaxDef.2.2.1 h1mg
    have hM4 := Rat.mul_le_mul_of_nonneg_left hMaxDef.2.2.2 h1mg
    have hNextErr : fcmlCapError p.vdc (traj (n + 1)) =
        ⟨en.vc1 + (tPwm / p.c1) * (fcmlClampedDiffTrim kTrim deltaMax (iLSeq n) en.vc1 * iLSeq n) + (etaSeq n).vc1,
         en.vc2 + (tPwm / p.c2) * (fcmlClampedDiffTrim kTrim deltaMax (iLSeq n) en.vc2 * iLSeq n) + (etaSeq n).vc2,
         en.vc3 + (tPwm / p.c3) * (fcmlClampedDiffTrim kTrim deltaMax (iLSeq n) en.vc3 * iLSeq n) + (etaSeq n).vc3,
         en.vc4 + (tPwm / p.c4) * (fcmlClampedDiffTrim kTrim deltaMax (iLSeq n) en.vc4 * iLSeq n) + (etaSeq n).vc4⟩ := by
      dsimp [traj, runFcmlActiveBalance, stepFcmlActiveBalance, fcmlSynthesizeZeroSumTrim,
             fcmlCapError, fcmlNominalLadder, en, vn]
      congr 1 <;> grind
    unfold fcmlMaxUnbalance; rw [hNextErr]; dsimp only
    exact rat_max4_le (rat_le_trans_add hC1 hM1) (rat_le_trans_add hC2 hM2)
      (rat_le_trans_add hC3 hM3) (rat_le_trans_add hC4 hM4)
  have hJoint : ∀ n,
      fcmlMaxUnbalance p.vdc (traj n) ≤ eMax ∧
      fcmlMaxUnbalance p.vdc (traj n) - rBal ≤
        fcmlRatPow (1 - gamma) n * (fcmlMaxUnbalance p.vdc v0 - rBal) := by
    intro n; induction n with
    | zero => dsimp [traj, runFcmlActiveBalance, fcmlRatPow]; exact ⟨hInit, by grind⟩
    | succ k ih =>
      have hOne := hStepBound k ih.1
      have h1mg : 0 ≤ 1 - gamma := by grind
      have hSub1 := Rat.mul_le_mul_of_nonneg_left ih.1 h1mg
      have hSub2 : etaMax ≤ gamma * eMax := by rw [← hBall]; exact Rat.mul_le_mul_of_nonneg_left hBallInEnv (by grind)
      have hChain := Rat.mul_le_mul_of_nonneg_left ih.2 h1mg
      dsimp [fcmlRatPow]; exact ⟨by grind, by grind⟩
  refine ⟨fun n => (hJoint n).1, fun n => (hJoint n).2, fun n => ?_⟩
  have hParts := rat_max4_parts (hJoint n).1
  exact fcml_cell_blocking_bounded_by_unbalance p.vdc eMax vFetMax (traj n)
    (by grind) hPosMargin hFetMargin
    ((ratAbs_le_iff _ eMax).mp hParts.1) ((ratAbs_le_iff _ eMax).mp hParts.2.1)
    ((ratAbs_le_iff _ eMax).mp hParts.2.2.1) ((ratAbs_le_iff _ eMax).mp hParts.2.2.2)
end Obend.Hardware.CircuitDae
end
