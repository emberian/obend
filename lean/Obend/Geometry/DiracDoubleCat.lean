module
/-
# Obend.Geometry.DiracDoubleCat — Acausal Dirac Structures ($D = D^\perp$) & `MultiscaleOpenDouble`

Formalizes acausal finite-dimensional Dirac port structures, resistive port-Hamiltonian closures,
and the symmetric monoidal double category `MultiscaleOpenDouble` coupling horizontal acausal
interconnection with vertical multiscale cochain coarse-graining and graded subgrid defects:

1. **Acausal Finite-Dimensional Dirac Structures (`KernelDirac`, $K f + L e = 0$, $D = D^\perp$)**:
   - Equips port bond spaces $\mathcal{F} \times \mathcal{E} = \mathbb{Q}^n \times \mathbb{Q}^n$ with
     the symmetric bilinear power pairing $\langle (f_1, e_1), (f_2, e_2) \rangle_+ = e_1 \cdot f_2 + e_2 \cdot f_1$.
   - Verifies skew-symmetry $K L^\top + L K^\top = 0$, full row rank $\operatorname{rank}[K \mid L] = n$,
     and dual image-kernel partition via `checkDiracIsotropicAndRank : Bool`.
   - Proves **`dirac_self_orthogonal_iff`** ($D = D^\perp$) and **`dirac_power_conservation`**
     ($\forall (f, e) \in D,\; e \cdot f = 0$: lossless Tellegen / Poynting / symplectic balance).
   - Proves **`resistiveDirac_dissipative_power`** ($\forall (f, e) \in D_R,\; e \cdot f \le 0$ under
     passive resistive port termination $e_R = R f_R$, $R + R^\top \succeq 0$) and bridges directly
     to `Obend.Category.OpenSystem.OpenDissipativeSys` (`DiracPortHamiltonianPlant.toOpenDissipativeSys`).
   - Instantiates four certified Dirac structures:
     (a) KCL/KVL 3-port junction extracted from `Obend.Hardware.OpenHypergraph.StrictOpenHypergraph`,
     (b) Electromechanical motor / gyrator coupler ($v_{\text{emf}} = k_t \omega, T_{\text{shaft}} = k_t i$ for all $k_t \in \mathbb{Q}$),
     (c) Ideal transformer ($v_2 = r v_1, i_1 + r i_2 = 0$ for all $r \in \mathbb{Q}$),
     (d) 1D DEC Maxwell transmission-line cell with boundary Poynting ports.
2. **Symmetric Monoidal Double Category `MultiscaleOpenDouble`**:
   - **Horizontal 1-Morphisms (`HorizOpenSys`):** Open acausal Dirac / dissipative systems composing
     via relational boundary pullback with shared-port flow reversal (`horizComp`), proving
     **`horizComp_preserves_power_balance`** ($e_A \cdot f_A + e_C \cdot f_C \le 0$) and parallel
     monoidal tensor (`horizTensor`).
   - **Vertical 1-Morphisms (`VertCoarseGrain`):** Cochain projections $\pi_\bullet : C_{\text{fine}}^\bullet \to C_{\text{coarse}}^\bullet$
     satisfying $d_{\text{coarse}} \circ \pi_k = \pi_{k+1} \circ d_{\text{fine}}$, proving
     **`coarseGrain_preserves_cohomology_and_conservation`** ($d_2 B_{\text{fine}} = 0 \implies d_2(\pi_2 B_{\text{fine}}) = 0$
     and gauge-coboundary preservation with zero topological drift).
   - **2-Cells (`MultiscaleSquare` with Quantitative Subgrid Defect $\varepsilon \in \mathbb{Q}_{\ge 0}$ & `CompositeGrade`):**
     Proves **`hPaste_sound`**, **`vPaste_sound`**, **`doubleCat_interchange_law`** (Eckmann–Hilton
     interchange compatibility `(α ⊞ₕ β) ⊞ᵥ (γ ⊞ₕ δ)` vs. `(α ⊞ᵥ γ) ⊞ₕ (β ⊞ᵥ δ)`), lifts squares into
     `Obend.Category.GradedTriple`, and constructs the **Worked Multiscale Telegrapher-to-MNA Square**
     coarse-graining an $N$-cell 1D DEC line into a lumped MNA section certified by
     `Obend.Hardware.CircuitDae.mnaCircuitDaeJudge`.
-/
public import Obend.Geometry.CochainAndGauge
public import Obend.Category.OpenSystem
public import Obend.Category.GradedLogic
public import Obend.Hardware.OpenHypergraph
public import Obend.Hardware.CircuitDae
import all Obend.Geometry.CochainAndGauge
import all Obend.Hardware.CircuitDae
public section

namespace Obend.Geometry.DiracDoubleCat
open Obend.Analysis
open Obend.Category
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.CircuitDae
open Obend.Geometry.CochainAndGauge
set_option autoImplicit false

/-! ## 1. Acausal Finite-Dimensional Dirac Structures ($K f + L e = 0$, $D = D^\perp$) -/

/-- Symmetric bilinear Dirac bond-space pairing $\langle (f_1, e_1), (f_2, e_2) \rangle_+ = e_1 \cdot f_2 + e_2 \cdot f_1$. -/
def diracPlusPairing (n : Nat) (f1 e1 f2 e2 : List CanonicalRat) : CanonicalRat :=
  vecDotN n e1 f2 + vecDotN n e2 f1

theorem diracPlusPairing_symm (n : Nat) (f1 e1 f2 e2 : List CanonicalRat) :
    diracPlusPairing n f1 e1 f2 e2 = diracPlusPairing n f2 e2 f1 e1 := by
  unfold diracPlusPairing; grind

theorem diracPlusPairing_diag (n : Nat) (f e : List CanonicalRat) :
    diracPlusPairing n f e f e = 2 * vecDotN n e f := by
  unfold diracPlusPairing; grind

/-- $n \times n$ matrix transpose, addition, and multiplication over `CanonicalRat`. -/
def matTransN (n : Nat) (M : List (List CanonicalRat)) : List (List CanonicalRat) :=
  (List.range n).map (fun i => mkVec n (fun j => matEntry M j i))

def matAddN (n : Nat) (A B : List (List CanonicalRat)) : List (List CanonicalRat) :=
  (List.range n).map (fun i => mkVec n (fun j => matEntry A i j + matEntry B i j))

def matMulN (n : Nat) (A B : List (List CanonicalRat)) : List (List CanonicalRat) :=
  (List.range n).map (fun i => mkVec n (fun j => sumUpTo n (fun k => matEntry A i k * matEntry B k j)))

private theorem getD_map_range (n : Nat) (g : Nat → List CanonicalRat) (i : Nat) (hi : i < n) :
    ((List.range n).map g).getD i [] = g i := by
  unfold List.getD
  simp [hi]

theorem matEntry_matTransN (n : Nat) (M : List (List CanonicalRat)) (i j : Nat)
    (hi : i < n) (hj : j < n) :
    matEntry (matTransN n M) i j = matEntry M j i := by
  unfold matEntry matTransN
  rw [getD_map_range n _ i hi]
  exact vecEntry_mkVec n _ j hj

theorem matEntry_matAddN (n : Nat) (A B : List (List CanonicalRat)) (i j : Nat)
    (hi : i < n) (hj : j < n) :
    matEntry (matAddN n A B) i j = matEntry A i j + matEntry B i j := by
  unfold matEntry matAddN
  rw [getD_map_range n _ i hi]
  exact vecEntry_mkVec n _ j hj

theorem matEntry_matMulN (n : Nat) (A B : List (List CanonicalRat)) (i j : Nat)
    (hi : i < n) (hj : j < n) :
    matEntry (matMulN n A B) i j = sumUpTo n (fun k => matEntry A i k * matEntry B k j) := by
  unfold matEntry matMulN
  rw [getD_map_range n _ i hi]
  exact vecEntry_mkVec n _ j hj

theorem matVecMulN_add_mat (n : Nat) (A B : List (List CanonicalRat)) (v : List CanonicalRat)
    (i : Nat) (hi : i < n) :
    vecEntry (matVecMulN n (matAddN n A B) v) i =
      vecEntry (matVecMulN n A v) i + vecEntry (matVecMulN n B v) i := by
  unfold matVecMulN
  rw [vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi, ← sumUpTo_add]
  refine sumUpTo_congr n _ _ (fun j hj => ?_)
  rw [matEntry_matAddN n A B i j hi hj]; grind

theorem matVecMulN_add_vec (n : Nat) (A : List (List CanonicalRat)) (u v : List CanonicalRat)
    (i : Nat) (hi : i < n) :
    vecEntry (matVecMulN n A (vecAddN n u v)) i =
      vecEntry (matVecMulN n A u) i + vecEntry (matVecMulN n A v) i := by
  unfold matVecMulN vecAddN
  rw [vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi, ← sumUpTo_add]
  refine sumUpTo_congr n _ _ (fun j hj => ?_)
  rw [vecEntry_mkVec n _ j hj]; grind

private theorem sumUpTo_scale_right (n : Nat) (c : CanonicalRat) (f : Nat → CanonicalRat) :
    sumUpTo n (fun i => f i * c) = sumUpTo n f * c := by
  induction n with
  | zero => dsimp [sumUpTo]; grind
  | succ k ih => dsimp [sumUpTo]; rw [ih]; grind

theorem matVecMulN_mul (n : Nat) (A B : List (List CanonicalRat)) (v : List CanonicalRat)
    (i : Nat) (hi : i < n) :
    vecEntry (matVecMulN n (matMulN n A B) v) i =
      vecEntry (matVecMulN n A (matVecMulN n B v)) i := by
  unfold matVecMulN
  rw [vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi]
  have hR : sumUpTo n (fun k => matEntry A i k * vecEntry (mkVec n (fun k' => sumUpTo n (fun j => matEntry B k' j * vecEntry v j))) k) =
      sumUpTo n (fun k => sumUpTo n (fun j => (matEntry A i k * matEntry B k j) * vecEntry v j)) := by
    refine sumUpTo_congr n _ _ (fun k hk => ?_)
    rw [vecEntry_mkVec n _ k hk, ← sumUpTo_scale]
    exact sumUpTo_congr n _ _ (fun _ _ => by grind)
  rw [hR, sumUpTo_comm]
  refine sumUpTo_congr n _ _ (fun j hj => ?_)
  rw [matEntry_matMulN n A B i j hi hj, ← sumUpTo_scale_right]

theorem vecDotN_matTransN_right (n : Nat) (A : List (List CanonicalRat)) (u v : List CanonicalRat) :
    vecDotN n u (matVecMulN n (matTransN n A) v) = vecDotN n (matVecMulN n A u) v := by
  unfold vecDotN matVecMulN
  have hL : sumUpTo n (fun i => vecEntry u i * vecEntry (mkVec n (fun i' => sumUpTo n (fun j => matEntry (matTransN n A) i' j * vecEntry v j))) i) =
      sumUpTo n (fun i => sumUpTo n (fun j => (matEntry A j i * vecEntry u i) * vecEntry v j)) := by
    refine sumUpTo_congr n _ _ (fun i hi => ?_)
    rw [vecEntry_mkVec n _ i hi, ← sumUpTo_scale]
    refine sumUpTo_congr n _ _ (fun j hj => ?_)
    rw [matEntry_matTransN n A i j hi hj]; grind
  rw [hL, sumUpTo_comm]
  refine sumUpTo_congr n _ _ (fun j hj => ?_)
  rw [vecEntry_mkVec n _ j hj, ← sumUpTo_scale_right]

private theorem vecDotN_congr_left (n : Nat) (u1 u2 v : List CanonicalRat)
    (h : ∀ i, i < n → vecEntry u1 i = vecEntry u2 i) :
    vecDotN n u1 v = vecDotN n u2 v :=
  sumUpTo_congr n _ _ (fun i hi => by rw [h i hi])

/-- Finite-dimensional kernel-representation Dirac structure $D = \{(f, e) \in \mathbb{Q}^n \times \mathbb{Q}^n \mid K f + L e = 0\}$,
    paired with full-rank Gram inverse witness `gramInv` $= (K K^\top + L L^\top)^{-1}$. -/
structure KernelDirac where
  dim     : Nat
  matK    : List (List CanonicalRat)
  matL    : List (List CanonicalRat)
  gramInv : List (List CanonicalRat)
  deriving DecidableEq, Repr

/-- Membership $(f, e) \in D$: $K f + L e = 0$ on $\{0, \dots, n-1\}$. -/
def KernelDirac.Mem (D : KernelDirac) (f e : List CanonicalRat) : Prop :=
  ∀ i, i < D.dim →
    vecEntry (matVecMulN D.dim D.matK f) i + vecEntry (matVecMulN D.dim D.matL e) i = 0

/-- Orthogonal complement $(f, e) \in D^\perp$ under the symmetric bond pairing $\langle \cdot, \cdot \rangle_+$. -/
def KernelDirac.Orthogonal (D : KernelDirac) (f e : List CanonicalRat) : Prop :=
  ∀ f' e', D.Mem f' e' → diracPlusPairing D.dim f e f' e' = 0

private def checkMatZeroN (n : Nat) (M : List (List CanonicalRat)) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j => decide (matEntry M i j = 0)))

private def checkMatIdN (n : Nat) (M : List (List CanonicalRat)) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j =>
    decide (matEntry M i j = if i = j then 1 else 0)))

/-- Verifies Dirac isotropy ($K L^\top + L K^\top = 0$), maximal rank $n$ ($(K K^\top + L L^\top) M = I_n$),
    and exact kernel-image projector partition ($K^\top M K + L^\top M L = I_n$, $K^\top M L + L^\top M K = 0$). -/
def checkDiracIsotropicAndRank (D : KernelDirac) : Bool :=
  let n := D.dim
  let Kt := matTransN n D.matK
  let Lt := matTransN n D.matL
  let iso := matAddN n (matMulN n D.matK Lt) (matMulN n D.matL Kt)
  let gram := matAddN n (matMulN n D.matK Kt) (matMulN n D.matL Lt)
  let rankOk := matMulN n gram D.gramInv
  let projDiag := matAddN n (matMulN n (matMulN n Kt D.gramInv) D.matK)
                            (matMulN n (matMulN n Lt D.gramInv) D.matL)
  let projCross := matAddN n (matMulN n (matMulN n Kt D.gramInv) D.matL)
                             (matMulN n (matMulN n Lt D.gramInv) D.matK)
  checkMatZeroN n iso &&
  checkMatIdN n rankOk &&
  checkMatIdN n projDiag &&
  checkMatZeroN n projCross

private theorem checkMatZeroN_iff (n : Nat) (M : List (List CanonicalRat)) :
    checkMatZeroN n M = true ↔ ∀ i j, i < n → j < n → matEntry M i j = 0 := by
  simp only [checkMatZeroN, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h i j hi hj => h i hi j hj, fun h i hi j hj => h i j hi hj⟩

private theorem checkMatIdN_iff (n : Nat) (M : List (List CanonicalRat)) :
    checkMatIdN n M = true ↔ ∀ i j, i < n → j < n → matEntry M i j = (if i = j then 1 else 0) := by
  simp only [checkMatIdN, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h i j hi hj => h i hi j hj, fun h i hi j hj => h i j hi hj⟩

private theorem matVecMulN_eq_id_of_entries (n : Nat) (M : List (List CanonicalRat))
    (hId : ∀ i j, i < n → j < n → matEntry M i j = (if i = j then 1 else 0))
    (v : List CanonicalRat) (i : Nat) (hi : i < n) :
    vecEntry (matVecMulN n M v) i = vecEntry v i := by
  unfold matVecMulN
  rw [vecEntry_mkVec n _ i hi]
  rw [sumUpTo_congr n _ (fun j => if j = i then vecEntry v i else 0)]
  · exact sumUpTo_delta n i (vecEntry v i) hi
  · intro j hj
    rw [hId i j hi hj]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]

private theorem matVecMulN_eq_zero_of_entries (n : Nat) (M : List (List CanonicalRat))
    (hZ : ∀ i j, i < n → j < n → matEntry M i j = 0)
    (v : List CanonicalRat) (i : Nat) (hi : i < n) :
    vecEntry (matVecMulN n M v) i = 0 := by
  unfold matVecMulN
  rw [vecEntry_mkVec n _ i hi]
  rw [sumUpTo_congr n _ (fun _ => 0) (fun j hj => by rw [hZ i j hi hj]; grind)]
  exact sumUpTo_zero n

/-- Image co-state parametrization: for every $\mu \in \mathbb{Q}^n$, $(L^\top \mu, K^\top \mu) \in D$,
    and conversely every $(f, e) \in D$ agrees on $\{0, \dots, n-1\}$ with $(L^\top \mu, K^\top \mu)$
    for $\mu = M (L f + K e)$. -/
theorem dirac_image_parametrization (D : KernelDirac)
    (hOk : checkDiracIsotropicAndRank D = true) :
    (∀ μ : List CanonicalRat,
      D.Mem (matVecMulN D.dim (matTransN D.dim D.matL) μ)
            (matVecMulN D.dim (matTransN D.dim D.matK) μ)) ∧
    (∀ f e : List CanonicalRat, D.Mem f e →
      let μ := matVecMulN D.dim D.gramInv
        (vecAddN D.dim (matVecMulN D.dim D.matL f) (matVecMulN D.dim D.matK e))
      (∀ i, i < D.dim → vecEntry (matVecMulN D.dim (matTransN D.dim D.matL) μ) i = vecEntry f i) ∧
      (∀ i, i < D.dim → vecEntry (matVecMulN D.dim (matTransN D.dim D.matK) μ) i = vecEntry e i)) := by
  unfold checkDiracIsotropicAndRank at hOk
  simp only [Bool.and_eq_true, checkMatZeroN_iff, checkMatIdN_iff] at hOk
  obtain ⟨⟨⟨hIso, _⟩, hDiag⟩, hCross⟩ := hOk
  let n := D.dim
  let Kt := matTransN n D.matK
  let Lt := matTransN n D.matL
  refine ⟨fun μ i hi => ?_, fun f e hMem => ?_⟩
  · rw [← matVecMulN_mul n D.matK Lt μ i hi,
        ← matVecMulN_mul n D.matL Kt μ i hi,
        ← matVecMulN_add_mat n _ _ μ i hi]
    exact matVecMulN_eq_zero_of_entries n _ hIso μ i hi
  · intro μ
    have hZeroVec : ∀ j, j < n →
        vecEntry (vecAddN n (matVecMulN n D.matK f) (matVecMulN n D.matL e)) j = 0 := by
      intro j hj; unfold vecAddN; rw [vecEntry_mkVec n _ j hj]; exact hMem j hj
    have matOnZero : ∀ (A : List (List CanonicalRat)) (w : List CanonicalRat),
        (∀ j, j < n → vecEntry w j = 0) → ∀ i, i < n → vecEntry (matVecMulN n A w) i = 0 := by
      intro A w hw i hi; unfold matVecMulN; rw [vecEntry_mkVec n _ i hi]
      rw [sumUpTo_congr n _ (fun _ => 0) (fun j hj => by rw [hw j hj]; grind)]
      exact sumUpTo_zero n
    have blockexpand : ∀ (P Q R : List (List CanonicalRat)),
        ∀ i, i < n →
          vecEntry (matVecMulN n P μ) i =
            vecEntry (matVecMulN n (matMulN n (matMulN n P D.gramInv) Q) f) i +
            vecEntry (matVecMulN n (matMulN n (matMulN n P D.gramInv) R) e) i → True := fun _ _ _ _ _ _ => trivial
    have _ := blockexpand
    have expandMu : ∀ (P : List (List CanonicalRat)) (i : Nat), i < n →
        vecEntry (matVecMulN n P μ) i =
          vecEntry (matVecMulN n (matMulN n (matMulN n P D.gramInv) D.matL) f) i +
          vecEntry (matVecMulN n (matMulN n (matMulN n P D.gramInv) D.matK) e) i := by
      intro P i hi; dsimp only [μ]
      rw [← matVecMulN_mul n P D.gramInv _ i hi, matVecMulN_add_vec n (matMulN n P D.gramInv) _ _ i hi,
          ← matVecMulN_mul n (matMulN n P D.gramInv) D.matL f i hi,
          ← matVecMulN_mul n (matMulN n P D.gramInv) D.matK e i hi]
    have expandZero : ∀ (P : List (List CanonicalRat)) (i : Nat), i < n →
        0 = vecEntry (matVecMulN n (matMulN n (matMulN n P D.gramInv) D.matK) f) i +
            vecEntry (matVecMulN n (matMulN n (matMulN n P D.gramInv) D.matL) e) i := by
      intro P i hi
      have h0 := matOnZero (matMulN n P D.gramInv) (vecAddN n (matVecMulN n D.matK f) (matVecMulN n D.matL e)) hZeroVec i hi
      rw [matVecMulN_add_vec n (matMulN n P D.gramInv) _ _ i hi,
          ← matVecMulN_mul n (matMulN n P D.gramInv) D.matK f i hi,
          ← matVecMulN_mul n (matMulN n P D.gramInv) D.matL e i hi] at h0
      exact h0.symm
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hLtMu := expandMu Lt i hi
      have hKtZero := expandZero Kt i hi
      have hDiagF : vecEntry (matVecMulN n (matMulN n (matMulN n Kt D.gramInv) D.matK) f) i +
          vecEntry (matVecMulN n (matMulN n (matMulN n Lt D.gramInv) D.matL) f) i = vecEntry f i := by
        rw [← matVecMulN_add_mat n _ _ f i hi]; exact matVecMulN_eq_id_of_entries n _ hDiag f i hi
      have hCrossE : vecEntry (matVecMulN n (matMulN n (matMulN n Kt D.gramInv) D.matL) e) i +
          vecEntry (matVecMulN n (matMulN n (matMulN n Lt D.gramInv) D.matK) e) i = 0 := by
        rw [← matVecMulN_add_mat n _ _ e i hi]; exact matVecMulN_eq_zero_of_entries n _ hCross e i hi
      grind
    · have hKtMu := expandMu Kt i hi
      have hLtZero := expandZero Lt i hi
      have hCrossF : vecEntry (matVecMulN n (matMulN n (matMulN n Kt D.gramInv) D.matL) f) i +
          vecEntry (matVecMulN n (matMulN n (matMulN n Lt D.gramInv) D.matK) f) i = 0 := by
        rw [← matVecMulN_add_mat n _ _ f i hi]; exact matVecMulN_eq_zero_of_entries n _ hCross f i hi
      have hDiagE : vecEntry (matVecMulN n (matMulN n (matMulN n Kt D.gramInv) D.matK) e) i +
          vecEntry (matVecMulN n (matMulN n (matMulN n Lt D.gramInv) D.matL) e) i = vecEntry e i := by
        rw [← matVecMulN_add_mat n _ _ e i hi]; exact matVecMulN_eq_id_of_entries n _ hDiag e i hi
      grind

/-- **Exact Self-Orthogonality (`dirac_self_orthogonal_iff`)**:
    Every certified `KernelDirac` satisfies $D = D^\perp$ under $\langle \cdot, \cdot \rangle_+$. -/
theorem dirac_self_orthogonal_iff (D : KernelDirac)
    (hOk : checkDiracIsotropicAndRank D = true)
    (f e : List CanonicalRat) :
    D.Mem f e ↔ D.Orthogonal f e := by
  obtain ⟨hImgIn, hImgRep⟩ := dirac_image_parametrization D hOk
  let n := D.dim
  constructor
  · intro hMem f' e' hMem'
    obtain ⟨hfRep, heRep⟩ := hImgRep f e hMem
    let μ := matVecMulN n D.gramInv
      (vecAddN n (matVecMulN n D.matL f) (matVecMulN n D.matK e))
    unfold diracPlusPairing
    rw [vecDotN_congr_left n e (matVecMulN n (matTransN n D.matK) μ) f' (fun i hi => (heRep i hi).symm),
        vecDotN_comm n e' f,
        vecDotN_congr_left n f (matVecMulN n (matTransN n D.matL) μ) e' (fun i hi => (hfRep i hi).symm),
        vecDotN_comm n (matVecMulN n (matTransN n D.matK) μ) f',
        vecDotN_comm n (matVecMulN n (matTransN n D.matL) μ) e',
        vecDotN_matTransN_right n D.matK f' μ,
        vecDotN_matTransN_right n D.matL e' μ]
    unfold vecDotN
    rw [← sumUpTo_add]
    rw [sumUpTo_congr n _ (fun _ => 0)]
    · exact sumUpTo_zero n
    · intro i hi
      have h0 := hMem' i hi
      have hFactor :
          vecEntry (matVecMulN n D.matK f') i * vecEntry μ i +
          vecEntry (matVecMulN n D.matL e') i * vecEntry μ i =
          (vecEntry (matVecMulN n D.matK f') i + vecEntry (matVecMulN n D.matL e') i) * vecEntry μ i := by grind
      rw [hFactor, h0]; grind
  · intro hOrth i hi
    let μ := basisVec n i
    have hPair0 := hOrth (matVecMulN n (matTransN n D.matL) μ)
                         (matVecMulN n (matTransN n D.matK) μ) (hImgIn μ)
    unfold diracPlusPairing at hPair0
    rw [vecDotN_matTransN_right n D.matL e μ,
        vecDotN_comm n (matVecMulN n (matTransN n D.matK) μ) f,
        vecDotN_matTransN_right n D.matK f μ] at hPair0
    have hBasisDot : ∀ w : List CanonicalRat, vecDotN n w μ = vecEntry w i := by
      intro w; unfold vecDotN
      rw [sumUpTo_congr n _ (fun j => if j = i then vecEntry w i else 0)]
      · exact sumUpTo_delta n i (vecEntry w i) hi
      · intro j hj; dsimp [μ]; rw [vecEntry_basisVec n i j hj]
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji]
    rw [hBasisDot, hBasisDot] at hPair0
    grind

/-- **Lossless Acausal Power Conservation (`dirac_power_conservation`)**:
    For every certified Dirac structure $D$ and port pair $(f, e) \in D$, $e \cdot f = 0$
    (Tellegen's theorem / Poynting balance / symplectic energy conservation). -/
theorem dirac_power_conservation (D : KernelDirac)
    (hOk : checkDiracIsotropicAndRank D = true)
    (f e : List CanonicalRat) (hMem : D.Mem f e) :
    vecDotN D.dim e f = 0 := by
  have hOrth := (dirac_self_orthogonal_iff D hOk f e).mp hMem
  have hSelf := hOrth f e hMem
  rw [diracPlusPairing_diag] at hSelf
  grind

/-! ### 1.1 Dissipative Port-Hamiltonian / Brayton–Moser Resistive Closure & `OpenDissipativeSys` Bridge -/

/-- Concatenate an external port vector ($n_{\text{ext}}$) and resistive port vector ($n_{\text{res}}$). -/
def splitConcatVec (nExt nRes : Nat) (vExt vRes : List CanonicalRat) : List CanonicalRat :=
  mkVec (nExt + nRes) (fun k => if k < nExt then vecEntry vExt k else vecEntry vRes (k - nExt))

private theorem vecDotN_splitConcat (nExt nRes : Nat) (uExt uRes vExt vRes : List CanonicalRat) :
    vecDotN (nExt + nRes) (splitConcatVec nExt nRes uExt uRes) (splitConcatVec nExt nRes vExt vRes) =
      vecDotN nExt uExt vExt + vecDotN nRes uRes vRes := by
  have sumAdd : ∀ (a b : Nat) (g : Nat → CanonicalRat),
      sumUpTo (a + b) g = sumUpTo a g + sumUpTo b (fun j => g (a + j)) := by
    intro a b g; induction b with
    | zero => simp [sumUpTo]; grind
    | succ m ih => dsimp [sumUpTo]; rw [ih]; grind
  unfold vecDotN
  rw [sumAdd nExt nRes]
  congr 1
  · refine sumUpTo_congr nExt _ _ (fun i hi => ?_)
    unfold splitConcatVec
    rw [vecEntry_mkVec (nExt + nRes) _ i (by omega), vecEntry_mkVec (nExt + nRes) _ i (by omega)]
    simp [hi]
  · refine sumUpTo_congr nRes _ _ (fun j hj => ?_)
    unfold splitConcatVec
    rw [vecEntry_mkVec (nExt + nRes) _ (nExt + j) (by omega),
        vecEntry_mkVec (nExt + nRes) _ (nExt + j) (by omega)]
    have hNotLt : ¬ (nExt + j < nExt) := by omega
    have hSub : nExt + j - nExt = j := by omega
    simp [hNotLt, hSub]

/-- Resistive Dirac / Port-Hamiltonian closure terminating $n_{\text{res}}$ ports of an
    $(n_{\text{ext}} + n_{\text{res}})$-port `KernelDirac` onto $e_R = R f_R$ with $R + R^\top \succeq 0$. -/
structure ResistiveDiracClosure where
  extDim  : Nat
  resDim  : Nat
  core    : KernelDirac
  matR    : List (List CanonicalRat)
  resGram : List MnaGramFactor
  deriving DecidableEq, Repr

/-- External port relation $D_R \subseteq \mathbb{Q}^{n_{\text{ext}}} \times \mathbb{Q}^{n_{\text{ext}}}$ induced by $e_R = R f_R$. -/
def ResistiveDiracClosure.ExtMem (C : ResistiveDiracClosure) (fExt eExt : List CanonicalRat) : Prop :=
  ∃ fRes eRes : List CanonicalRat,
    C.core.Mem (splitConcatVec C.extDim C.resDim fExt fRes)
               (splitConcatVec C.extDim C.resDim eExt eRes) ∧
    ∀ j, j < C.resDim → vecEntry eRes j = vecEntry (matVecMulN C.resDim C.matR fRes) j

/-- Verifies Dirac core exactness, port dimension split, and Gram PSD certificate for $R + R^\top \succeq 0$. -/
def checkResistiveDiracClosure (C : ResistiveDiracClosure) : Bool :=
  (C.core.dim == C.extDim + C.resDim) &&
  checkDiracIsotropicAndRank C.core &&
  C.resGram.all (fun f => decide (0 ≤ f.weight)) &&
  (List.range C.resDim).all (fun i => (List.range C.resDim).all (fun j =>
    decide (matEntry C.matR i j + matEntry C.matR j i = gramEntry C.resGram i j)))

/-- **Resistive Dirac / Brayton–Moser Passivity Theorem (`resistiveDirac_dissipative_power`)**:
    Terminating resistive ports with $e_R = R f_R$ ($R + R^\top \succeq 0$) guarantees dissipative
    external power balance $e_{\text{ext}} \cdot f_{\text{ext}} = - f_R^\top R f_R \le 0$ for all $(f_{\text{ext}}, e_{\text{ext}}) \in D_R$. -/
theorem resistiveDirac_dissipative_power (C : ResistiveDiracClosure)
    (hOk : checkResistiveDiracClosure C = true)
    (fExt eExt : List CanonicalRat) (hMem : C.ExtMem fExt eExt) :
    vecDotN C.extDim eExt fExt ≤ 0 := by
  unfold checkResistiveDiracClosure at hOk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hOk
  obtain ⟨⟨⟨hDim, hCore⟩, hWeights⟩, hSymR⟩ := hOk
  rcases hMem with ⟨fRes, eRes, hCoreMem, hOhm⟩
  have hZero := dirac_power_conservation C.core hCore
    (splitConcatVec C.extDim C.resDim fExt fRes)
    (splitConcatVec C.extDim C.resDim eExt eRes) hCoreMem
  rw [hDim, vecDotN_splitConcat] at hZero
  have hResQuad : vecDotN C.resDim eRes fRes = quadFormN C.resDim C.matR fRes fRes := by
    rw [vecDotN_congr_left C.resDim eRes (matVecMulN C.resDim C.matR fRes) fRes hOhm,
        vecDotN_comm]
    rfl
  have hPsdR : 0 ≤ quadFormN C.resDim C.matR fRes fRes :=
    quadFormN_nonneg_of_symSum_gram C.resDim C.matR C.resGram
      (fun i j hi hj => hSymR i hi j hj) hWeights fRes
  rw [hResQuad] at hZero
  grind

/-- Discrete-time Port-Hamiltonian plant coupled across a certified `ResistiveDiracClosure`,
    bridging acausal Dirac dissipation directly to `Obend.Category.OpenSystem.OpenDissipativeSys`. -/
structure DiracPortHamiltonianPlant (State PortIn PortOut : Type) where
  energy         : State → Int
  energy_nonneg  : ∀ s : State, 0 ≤ energy s
  closure        : ResistiveDiracClosure
  closure_ok     : checkResistiveDiracClosure closure = true
  step           : State → PortIn → State × PortOut
  portWitness    : State → PortIn → List CanonicalRat × List CanonicalRat
  witness_mem    : ∀ s u, closure.ExtMem (portWitness s u).1 (portWitness s u).2
  supply         : PortIn → PortOut → Int
  dissipative_balance : ∀ (s : State) (u : PortIn),
    ((energy (step s u).1 - energy s : Int) : CanonicalRat) ≤
      ((supply u (step s u).2 : Int) : CanonicalRat) +
      vecDotN closure.extDim (portWitness s u).2 (portWitness s u).1

/-- Convert any `DiracPortHamiltonianPlant` into a certified `Obend.Category.OpenDissipativeSys`. -/
@[expose] def DiracPortHamiltonianPlant.toOpenDissipativeSys {State PortIn PortOut : Type}
    (P : DiracPortHamiltonianPlant State PortIn PortOut) :
    OpenDissipativeSys State PortIn PortOut where
  energy := P.energy
  energy_nonneg := P.energy_nonneg
  supply := P.supply
  step := P.step
  dissipative s u := by
    have hDiss := resistiveDirac_dissipative_power P.closure P.closure_ok
      (P.portWitness s u).1 (P.portWitness s u).2 (P.witness_mem s u)
    have hBal := P.dissipative_balance s u
    have hRatLe : ((P.energy (P.step s u).1 - P.energy s : Int) : CanonicalRat) ≤
        ((P.supply u (P.step s u).2 : Int) : CanonicalRat) := by grind
    exact Rat.intCast_le_intCast.mp hRatLe

/-- **Global Multi-Step Trajectory Lyapunov Bound for Dirac-Coupled Plants (`diracPlant_trajectory_lyapunov`)**:
    Direct composition with `OpenDissipativeSys.energy_bounded_along_trajectory`. -/
theorem diracPlant_trajectory_lyapunov {State PortIn PortOut : Type}
    (P : DiracPortHamiltonianPlant State PortIn PortOut) (s₀ : State) (us : List PortIn) :
    0 ≤ P.energy (P.toOpenDissipativeSys.runTrajectory s₀ us) ∧
      P.energy (P.toOpenDissipativeSys.runTrajectory s₀ us) ≤
        P.energy s₀ + P.toOpenDissipativeSys.trajectorySupply s₀ us :=
  OpenDissipativeSys.energy_bounded_along_trajectory P.toOpenDissipativeSys s₀ us

/-- Quadratic storage energy $H(x) = \sum_{i < d} \frac{1}{2} q_i x_i^2$ and midpoint discrete gradient
    $e_{\text{stor}, i} = q_i \frac{x'_i + x_i}{2}$ over `CanonicalRat`. -/
def quadStorageEnergy (d : Nat) (q x : List CanonicalRat) : CanonicalRat :=
  sumUpTo d (fun i => (1 / 2) * vecEntry q i * (vecEntry x i * vecEntry x i))

def midpointStorageEffort (d : Nat) (q xPrev xNext : List CanonicalRat) : List CanonicalRat :=
  mkVec d (fun i => vecEntry q i * ((vecEntry xNext i + vecEntry xPrev i) / 2))

/-- **Exact Discrete-Gradient Midpoint Port-Hamiltonian Dissipation (`midpoint_resistive_ph_step_dissipative`)**:
    For any quadratic Hamiltonian $H(x) = \sum_{i < d} \frac{1}{2} q_i x_i^2$, midpoint effort
    $e_{\text{stor}} = Q \frac{x' + x}{2}$ satisfies the exact discrete chain rule
    $H(x') - H(x) = \langle e_{\text{stor}}, x' - x \rangle$ with **zero** numerical energy drift;
    when coupled to any certified `ResistiveDiracClosure` (`C.ExtMem fExt eExt`) via
    $\langle e_{\text{stor}}, x' - x \rangle = \Delta t (P_{\text{supply}} + \langle e_{\text{ext}}, f_{\text{ext}} \rangle)$
    with $\Delta t > 0$, dissipative passivity $H(x') - H(x) \le \Delta t \, P_{\text{supply}}$ follows identically. -/
theorem midpoint_resistive_ph_step_dissipative
    (C : ResistiveDiracClosure) (hOk : checkResistiveDiracClosure C = true)
    (d : Nat) (q xPrev xNext fExt eExt : List CanonicalRat)
    (dt supplyPower : CanonicalRat) (hDt : 0 < dt)
    (hMem : C.ExtMem fExt eExt)
    (hInterconn : vecDotN d (midpointStorageEffort d q xPrev xNext) (vecSubN d xNext xPrev) =
      dt * (supplyPower + vecDotN C.extDim eExt fExt)) :
    quadStorageEnergy d q xNext - quadStorageEnergy d q xPrev =
      vecDotN d (midpointStorageEffort d q xPrev xNext) (vecSubN d xNext xPrev) ∧
    quadStorageEnergy d q xNext - quadStorageEnergy d q xPrev ≤ dt * supplyPower := by
  have hChain : quadStorageEnergy d q xNext - quadStorageEnergy d q xPrev =
      vecDotN d (midpointStorageEffort d q xPrev xNext) (vecSubN d xNext xPrev) := by
    unfold quadStorageEnergy midpointStorageEffort vecDotN vecSubN
    rw [← sumUpTo_sub]
    refine sumUpTo_congr d _ _ (fun i hi => ?_)
    rw [vecEntry_mkVec d _ i hi, vecEntry_mkVec d _ i hi]; grind
  have hDiss := resistiveDirac_dissipative_power C hOk fExt eExt hMem
  have hMul : dt * (supplyPower + vecDotN C.extDim eExt fExt) ≤ dt * supplyPower :=
    Rat.mul_le_mul_of_nonneg_left (by grind) (Rat.le_of_lt hDt)
  exact ⟨hChain, by rw [hChain, hInterconn]; exact hMul⟩

/-! ### 1.2 Four Concrete Certified Dirac Structures (Hypergraph KCL/KVL, Gyrator, Transformer, DEC Poynting) -/

/-- Canonical 3-port common-bus `StrictOpenHypergraph` (`Obend.Hardware.OpenHypergraph`) with 2 input
    ports and 1 output port sharing wire `0`. -/
def junctionHypergraph3 : StrictOpenHypergraph where
  nodeTypes   := [64]
  ops         := []
  sources     := IndexedCoproduct.fromSegments 1 []
  targets     := IndexedCoproduct.fromSegments 1 []
  boundaryIn  := { source := 2, target := 1, table := [0, 0] }
  boundaryOut := { source := 1, target := 1, table := [0] }

/-- Extract the 3-port KCL/KVL Dirac structure induced by boundary ports incident to wire `w`
    of a `StrictOpenHypergraph`. -/
def hypergraphJunctionDirac (hg : StrictOpenHypergraph) (w : Nat) : KernelDirac :=
  let bVars := hg.boundaryIn.table ++ hg.boundaryOut.table
  let s0 : CanonicalRat := if bVars.getD 0 1 == w then 1 else 0
  let s1 : CanonicalRat := if bVars.getD 1 1 == w then 1 else 0
  let s2 : CanonicalRat := if bVars.getD 2 1 == w then 1 else 0
  { dim := 3
    matK := [[s0, s1, s2], [0, 0, 0], [0, 0, 0]]
    matL := [[0, 0, 0], [s0, 0, -s2], [0, s1, -s2]]
    gramInv :=
      [[1 / 3, 0, 0],
       [0, 2 / 3, -(1 / 3)],
       [0, -(1 / 3), 2 / 3]] }

private theorem vecEntry_cons_zero (x : CanonicalRat) (xs : List CanonicalRat) : vecEntry (x :: xs) 0 = x := rfl
private theorem vecEntry_cons_succ (x : CanonicalRat) (xs : List CanonicalRat) (k : Nat) : vecEntry (x :: xs) (k + 1) = vecEntry xs k := rfl
private theorem matEntry_cons_zero (r : List CanonicalRat) (rs : List (List CanonicalRat)) (j : Nat) : matEntry (r :: rs) 0 j = vecEntry r j := rfl
private theorem matEntry_cons_succ (r : List CanonicalRat) (rs : List (List CanonicalRat)) (i j : Nat) : matEntry (r :: rs) (i + 1) j = matEntry rs i j := rfl

/-- Certified KCL + KVL 3-port Dirac structure extracted from `junctionHypergraph3`. -/
theorem hypergraphJunctionDirac_certified_and_kcl_kvl (f e : List CanonicalRat) :
    junctionHypergraph3.wf = true ∧
    checkDiracIsotropicAndRank (hypergraphJunctionDirac junctionHypergraph3 0) = true ∧
    ((hypergraphJunctionDirac junctionHypergraph3 0).Mem f e ↔
      (vecEntry f 0 + vecEntry f 1 + vecEntry f 2 = 0 ∧
       vecEntry e 0 = vecEntry e 2 ∧ vecEntry e 1 = vecEntry e 2)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have hHg : hypergraphJunctionDirac junctionHypergraph3 0 =
      { dim := 3, matK := [[1, 1, 1], [0, 0, 0], [0, 0, 0]],
        matL := [[0, 0, 0], [1, 0, -1], [0, 1, -1]],
        gramInv := (hypergraphJunctionDirac junctionHypergraph3 0).gramInv } := rfl
  rw [hHg]; dsimp only [KernelDirac.Mem]
  constructor
  · intro h
    have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
    simp only [matVecMulN, mkVec, mkVecFrom, sumUpTo,
      vecEntry_cons_zero, vecEntry_cons_succ, matEntry_cons_zero, matEntry_cons_succ] at h0 h1 h2
    grind
  · rintro ⟨hkcl, he0, he1⟩ i hi
    match i with
    | 0 | 1 | 2 =>
      simp only [matVecMulN, mkVec, mkVecFrom, sumUpTo,
        vecEntry_cons_zero, vecEntry_cons_succ, matEntry_cons_zero, matEntry_cons_succ]; grind
    | n + 3 => omega

private theorem check2x2_entry_iff (P : Nat → Nat → Prop) :
    (∀ i j, i < 2 → j < 2 → P i j) ↔ (P 0 0 ∧ P 0 1 ∧ P 1 0 ∧ P 1 1) := by
  constructor
  · exact fun h => ⟨h 0 0 (by omega) (by omega), h 0 1 (by omega) (by omega),
                    h 1 0 (by omega) (by omega), h 1 1 (by omega) (by omega)⟩
  · rintro ⟨h00, h01, h10, h11⟩ i j hi hj
    match i, j with
    | 0, 0 => exact h00 | 0, 1 => exact h01 | 1, 0 => exact h10 | 1, 1 => exact h11
    | n + 2, _ => omega | _, m + 2 => omega

private theorem matEntry_add2 (A B : List (List CanonicalRat)) (i j : Nat) (hi : i < 2) (hj : j < 2) :
    matEntry (matAddN 2 A B) i j = matEntry A i j + matEntry B i j :=
  matEntry_matAddN 2 A B i j hi hj

private theorem matEntry_mul2 (A B : List (List CanonicalRat)) (i j : Nat) (hi : i < 2) (hj : j < 2) :
    matEntry (matMulN 2 A B) i j = matEntry A i 0 * matEntry B 0 j + matEntry A i 1 * matEntry B 1 j := by
  rw [matEntry_matMulN 2 A B i j hi hj]
  dsimp [sumUpTo]; grind

private theorem matEntry_trans2 (A : List (List CanonicalRat)) (i j : Nat) (hi : i < 2) (hj : j < 2) :
    matEntry (matTransN 2 A) i j = matEntry A j i :=
  matEntry_matTransN 2 A i j hi hj

/-- 2-port electromechanical motor / ideal gyrator Dirac structure (`kt : CanonicalRat`):
    electrical port $(f_0 = i, e_0 = -v_{\text{emf}})$ and shaft port $(f_1 = \omega, e_1 = T_{\text{shaft}})$
    satisfying $v_{\text{emf}} = k_t \omega$ ($e_0 + k_t f_1 = 0$) and $T_{\text{shaft}} = k_t i$ ($e_1 - k_t f_0 = 0$). -/
def gyratorMotorDirac (kt : CanonicalRat) : KernelDirac :=
  let invD := 1 / (1 + kt * kt)
  { dim := 2
    matK := [[0, kt], [-kt, 0]]
    matL := [[1, 0], [0, 1]]
    gramInv := [[invD, 0], [0, invD]] }

/-- Symbolic certification of `gyratorMotorDirac kt` for **every** torque constant $k_t \in \mathbb{Q}$. -/
theorem gyratorMotorDirac_certified (kt : CanonicalRat) :
    checkDiracIsotropicAndRank (gyratorMotorDirac kt) = true ∧
    ∀ f e : List CanonicalRat, (gyratorMotorDirac kt).Mem f e ↔
      (vecEntry e 0 + kt * vecEntry f 1 = 0 ∧ vecEntry e 1 - kt * vecEntry f 0 = 0) := by
  have hd : 1 + kt * kt ≠ 0 := by have := Interval.rat_sq_nonneg kt; grind
  refine ⟨?_, fun f e => ⟨fun h => ?_, ?_⟩⟩
  · unfold checkDiracIsotropicAndRank; dsimp only [gyratorMotorDirac]
    simp only [Bool.and_eq_true, checkMatZeroN_iff, checkMatIdN_iff, check2x2_entry_iff]
    have lt0 : 0 < 2 := by omega
    have lt1 : 1 < 2 := by omega
    simp only [matEntry_add2 _ _ _ _ lt0 lt0, matEntry_add2 _ _ _ _ lt0 lt1,
               matEntry_add2 _ _ _ _ lt1 lt0, matEntry_add2 _ _ _ _ lt1 lt1,
               matEntry_mul2 _ _ _ _ lt0 lt0, matEntry_mul2 _ _ _ _ lt0 lt1,
               matEntry_mul2 _ _ _ _ lt1 lt0, matEntry_mul2 _ _ _ _ lt1 lt1,
               matEntry_trans2 _ _ _ lt0 lt0, matEntry_trans2 _ _ _ lt0 lt1,
               matEntry_trans2 _ _ _ lt1 lt0, matEntry_trans2 _ _ _ lt1 lt1,
               matEntry_cons_zero, matEntry_cons_succ, vecEntry_cons_zero, vecEntry_cons_succ, ↓reduceIte]
    grind
  · dsimp only [KernelDirac.Mem, gyratorMotorDirac] at h
    have h0 := h 0 (by omega); have h1 := h 1 (by omega)
    simp only [matVecMulN, mkVec, mkVecFrom, sumUpTo, vecEntry_cons_zero, vecEntry_cons_succ,
      matEntry_cons_zero, matEntry_cons_succ] at h0 h1; grind
  · rintro ⟨h0, h1⟩ i hi; dsimp only [KernelDirac.Mem, gyratorMotorDirac] at hi ⊢
    match i with
    | 0 | 1 =>
      simp only [matVecMulN, mkVec, mkVecFrom, sumUpTo, vecEntry_cons_zero, vecEntry_cons_succ,
        matEntry_cons_zero, matEntry_cons_succ]; grind
    | n + 2 => omega

/-- 2-port ideal transformer Dirac structure with arbitrary rational turns ratio $r \in \mathbb{Q}$:
    $i_1 + r i_2 = 0$ ($f_0 + r f_1 = 0$) and $v_2 = r v_1$ ($e_1 - r e_0 = 0$). -/
def idealTransformerDirac (r : CanonicalRat) : KernelDirac :=
  let invD := 1 / (1 + r * r)
  { dim := 2, matK := [[1, r], [0, 0]], matL := [[0, 0], [-r, 1]], gramInv := [[invD, 0], [0, invD]] }

/-- Symbolic certification of `idealTransformerDirac r` for **every** rational turns ratio $r \in \mathbb{Q}$. -/
theorem idealTransformerDirac_certified (r : CanonicalRat) :
    checkDiracIsotropicAndRank (idealTransformerDirac r) = true ∧
    ∀ f e : List CanonicalRat, (idealTransformerDirac r).Mem f e ↔
      (vecEntry f 0 + r * vecEntry f 1 = 0 ∧ vecEntry e 1 - r * vecEntry e 0 = 0) := by
  have hd : 1 + r * r ≠ 0 := by have := Interval.rat_sq_nonneg r; grind
  refine ⟨?_, fun f e => ⟨fun h => ?_, ?_⟩⟩
  · unfold checkDiracIsotropicAndRank; dsimp only [idealTransformerDirac]
    simp only [Bool.and_eq_true, checkMatZeroN_iff, checkMatIdN_iff, check2x2_entry_iff]
    have lt0 : 0 < 2 := by omega
    have lt1 : 1 < 2 := by omega
    simp only [matEntry_add2 _ _ _ _ lt0 lt0, matEntry_add2 _ _ _ _ lt0 lt1,
               matEntry_add2 _ _ _ _ lt1 lt0, matEntry_add2 _ _ _ _ lt1 lt1,
               matEntry_mul2 _ _ _ _ lt0 lt0, matEntry_mul2 _ _ _ _ lt0 lt1,
               matEntry_mul2 _ _ _ _ lt1 lt0, matEntry_mul2 _ _ _ _ lt1 lt1,
               matEntry_trans2 _ _ _ lt0 lt0, matEntry_trans2 _ _ _ lt0 lt1,
               matEntry_trans2 _ _ _ lt1 lt0, matEntry_trans2 _ _ _ lt1 lt1,
               matEntry_cons_zero, matEntry_cons_succ, vecEntry_cons_zero, vecEntry_cons_succ, ↓reduceIte]
    grind
  · dsimp only [KernelDirac.Mem, idealTransformerDirac] at h
    have h0 := h 0 (by omega); have h1 := h 1 (by omega)
    simp only [matVecMulN, mkVec, mkVecFrom, sumUpTo, vecEntry_cons_zero, vecEntry_cons_succ,
      matEntry_cons_zero, matEntry_cons_succ] at h0 h1; grind
  · rintro ⟨h0, h1⟩ i hi; dsimp only [KernelDirac.Mem, idealTransformerDirac] at hi ⊢
    match i with
    | 0 | 1 =>
      simp only [matVecMulN, mkVec, mkVecFrom, sumUpTo, vecEntry_cons_zero, vecEntry_cons_succ,
        matEntry_cons_zero, matEntry_cons_succ]; grind
    | n + 2 => omega

/-- Single 1D DEC segment cell complex ($V = 2$, oriented edge $0 \to 1$). -/
def segment1DComplex : CellComplex3D where
  numV    := 2
  edges   := [(0, 1)]
  faces   := []
  volumes := []

/-- 5-port 1D DEC Maxwell / Stokes–Dirac transmission-line cell over `segment1DComplex`:
    - Ports $0, 1$: vertex 0-cochain electric storage ports $(-\dot{q}_0, V_0), (-\dot{q}_1, V_1)$,
    - Port $2$: edge 1-cochain magnetic flux storage port $(-\dot{\Phi}_{01}, H_{01})$ coupled via $d_0$,
    - Ports $3, 4$: left & right boundary Poynting ports $(I_L, V_L), (I_R, V_R)$. -/
def decMaxwellLineCellDirac : KernelDirac :=
  let d0_v0 := vecEntry (d0 segment1DComplex [1, 0]) 0  -- = -1
  let d0_v1 := vecEntry (d0 segment1DComplex [0, 1]) 0  -- = +1
  { dim := 5
    matK :=
      [[1, 0, 0, 1, 0],
       [0, 1, 0, 0, 1],
       [0, 0, 1, 0, 0],
       [0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0]]
    matL :=
      [[0, 0, -1, 0, 0],
       [0, 0,  1, 0, 0],
       [-d0_v0, -d0_v1, 0, 0, 0],
       [-1, 0, 0, 1, 0],
       [0, -1, 0, 0, 1]]
    gramInv :=
      [[3 / 8, 1 / 8, 0, 0, 0],
       [1 / 8, 3 / 8, 0, 0, 0],
       [0, 0,  4 / 8,  2 / 8, -(2 / 8)],
       [0, 0,  2 / 8,  5 / 8, -(1 / 8)],
       [0, 0, -(2 / 8), -(1 / 8), 5 / 8]] }

/-- **1D DEC Maxwell Boundary Poynting Balance (`decMaxwellLineCellDirac_certified`)**:
    `decMaxwellLineCellDirac` is a certified self-orthogonal Dirac structure ($D = D^\perp$), and
    for every field-boundary state $(f, e) \in D$, stored electromagnetic energy rate equals net
    boundary Poynting flux: $-(e_0 f_0 + e_1 f_1 + e_2 f_2) = e_3 f_3 + e_4 f_4$. -/
theorem decMaxwellLineCellDirac_certified (f e : List CanonicalRat) :
    checkComplexExact segment1DComplex = true ∧
    checkDiracIsotropicAndRank decMaxwellLineCellDirac = true ∧
    (decMaxwellLineCellDirac.Mem f e →
      -(vecEntry e 0 * vecEntry f 0 + vecEntry e 1 * vecEntry f 1 + vecEntry e 2 * vecEntry f 2) =
        vecEntry e 3 * vecEntry f 3 + vecEntry e 4 * vecEntry f 4) := by
  refine ⟨by decide +kernel, by decide +kernel, fun hMem => ?_⟩
  have hPow := dirac_power_conservation decMaxwellLineCellDirac (by decide +kernel) f e hMem
  change vecDotN 5 e f = 0 at hPow
  dsimp only [vecDotN, sumUpTo] at hPow
  grind

/-! ## 2. Symmetric Monoidal Double Category `MultiscaleOpenDouble` -/

/-- $\ell^\infty$ observable distance $\max_{0 \le i < n} |u_i - v_i|$ over `CanonicalRat` (`0` when $n = 0$). -/
def vecMaxDist : Nat → List CanonicalRat → List CanonicalRat → CanonicalRat
  | 0, _, _ => 0
  | k + 1, u, v =>
    let prev := vecMaxDist k u v
    let cur := ratAbs (vecEntry u k - vecEntry v k)
    if prev ≤ cur then cur else prev

theorem vecMaxDist_nonneg : ∀ (n : Nat) (u v : List CanonicalRat), 0 ≤ vecMaxDist n u v
  | 0, _, _ => by simp [vecMaxDist]
  | k + 1, u, v => by
    dsimp [vecMaxDist]
    have hPrev := vecMaxDist_nonneg k u v
    have hCur := ratAbs_nonneg (vecEntry u k - vecEntry v k)
    split <;> grind

theorem vecMaxDist_refl : ∀ (n : Nat) (u : List CanonicalRat), vecMaxDist n u u = 0
  | 0, _ => rfl
  | k + 1, u => by
    dsimp [vecMaxDist]
    rw [vecMaxDist_refl k u]
    have hZ : ratAbs (vecEntry u k - vecEntry u k) = 0 := by unfold ratAbs; split <;> grind
    rw [hZ]; simp

theorem entry_diff_le_vecMaxDist :
    ∀ (n : Nat) (u v : List CanonicalRat) (i : Nat),
      i < n → ratAbs (vecEntry u i - vecEntry v i) ≤ vecMaxDist n u v
  | 0, _, _, _, hi => by omega
  | k + 1, u, v, i, hi => by
    dsimp [vecMaxDist]
    by_cases hik : i = k
    · subst hik; split <;> grind
    · have ih := entry_diff_le_vecMaxDist k u v i (by omega)
      split <;> grind

theorem vecMaxDist_le_iff :
    ∀ (n : Nat) (u v : List CanonicalRat) (b : CanonicalRat),
      0 ≤ b → (vecMaxDist n u v ≤ b ↔ ∀ i, i < n → ratAbs (vecEntry u i - vecEntry v i) ≤ b)
  | 0, _, _, b, hb => by simp [vecMaxDist, hb]
  | k + 1, u, v, b, hb => by
    constructor
    · intro h i hi
      exact Rat.le_trans (entry_diff_le_vecMaxDist (k + 1) u v i hi) h
    · intro hAll
      dsimp [vecMaxDist]
      have hPrev : vecMaxDist k u v ≤ b :=
        (vecMaxDist_le_iff k u v b hb).mpr (fun i hi => hAll i (by omega))
      have hCur : ratAbs (vecEntry u k - vecEntry v k) ≤ b := hAll k (by omega)
      split <;> grind

theorem vecMaxDist_triangle (n : Nat) (u w v : List CanonicalRat) :
    vecMaxDist n u v ≤ vecMaxDist n u w + vecMaxDist n w v := by
  have hb : 0 ≤ vecMaxDist n u w + vecMaxDist n w v := by
    have := vecMaxDist_nonneg n u w; have := vecMaxDist_nonneg n w v; grind
  rw [vecMaxDist_le_iff n u v _ hb]
  intro i hi
  have h1 := (ratAbs_le_iff _ _).mp (entry_diff_le_vecMaxDist n u w i hi)
  have h2 := (ratAbs_le_iff _ _).mp (entry_diff_le_vecMaxDist n w v i hi)
  rw [ratAbs_le_iff]
  grind

/-- Objects of `MultiscaleOpenDouble`: typed boundary port space, observable readout space, and
    discrete 3-skeleton cell complex at a chosen spatial resolution. -/
structure ScaleObj where
  portDim : Nat
  obsDim  : Nat
  complex : CellComplex3D
  deriving DecidableEq, Repr

/-- Horizontal 1-morphisms `HorizOpenSys A B`: open acausal Dirac / dissipative systems between
    left boundary `A` and right boundary `B`, paired with a non-expansive observable response map. -/
structure HorizOpenSys (A B : ScaleObj) where
  portRel : List CanonicalRat → List CanonicalRat → List CanonicalRat → List CanonicalRat → Prop
  power_dissipative : ∀ fA eA fB eB,
    portRel fA eA fB eB → vecDotN A.portDim eA fA + vecDotN B.portDim eB fB ≤ 0
  stepObs : List CanonicalRat → List CanonicalRat
  stepObs_nonexpansive : ∀ x y,
    vecMaxDist B.obsDim (stepObs x) (stepObs y) ≤ vecMaxDist A.obsDim x y

/-- Horizontal identity 1-morphism on `A` (ideal lossless through-wire $f_R = -f_L$, $e_R = e_L$). -/
def HorizOpenSys.id (A : ScaleObj) : HorizOpenSys A A where
  portRel fL eL fR eR :=
    (∀ i, i < A.portDim → vecEntry fR i = -vecEntry fL i) ∧
    (∀ i, i < A.portDim → vecEntry eR i = vecEntry eL i)
  power_dissipative fL eL fR eR := by
    rintro ⟨hf, he⟩
    have hEq : vecDotN A.portDim eR fR = -vecDotN A.portDim eL fL := by
      unfold vecDotN
      have hNeg : sumUpTo A.portDim (fun i => vecEntry eR i * vecEntry fR i) =
          (-1) * sumUpTo A.portDim (fun i => vecEntry eL i * vecEntry fL i) := by
        rw [← sumUpTo_scale]
        exact sumUpTo_congr A.portDim _ _ (fun i hi => by rw [hf i hi, he i hi]; grind)
      rw [hNeg]; grind
    rw [hEq]; grind
  stepObs x := x
  stepObs_nonexpansive _ _ := by grind

/-- Horizontal composition `horizComp S1 S2` along shared boundary `B` via relational pullback with
    flow orientation reversal $(f_B, e_B) \leftrightarrow (-f_B, e_B)$:
    $D_{12} = \{(f_A, e_A, f_C, e_C) \mid \exists (f_B, e_B),\; (f_A, e_A, f_B, e_B) \in D_1 \wedge (-f_B, e_B, f_C, e_C) \in D_2\}$. -/
def horizComp {A B C : ScaleObj} (S1 : HorizOpenSys A B) (S2 : HorizOpenSys B C) :
    HorizOpenSys A C where
  portRel fA eA fC eC :=
    ∃ fB eB : List CanonicalRat,
      S1.portRel fA eA fB eB ∧
      S2.portRel (vecScaleN B.portDim (-1) fB) eB fC eC
  power_dissipative fA eA fC eC := by
    rintro ⟨fB, eB, h1, h2⟩
    have hp1 := S1.power_dissipative fA eA fB eB h1
    have hp2 := S2.power_dissipative (vecScaleN B.portDim (-1) fB) eB fC eC h2
    have hCancel : vecDotN B.portDim eB (vecScaleN B.portDim (-1) fB) = -vecDotN B.portDim eB fB := by
      unfold vecDotN vecScaleN
      have hScale : sumUpTo B.portDim (fun i => vecEntry eB i * vecEntry (mkVec B.portDim (fun k => -1 * vecEntry fB k)) i) =
          (-1) * sumUpTo B.portDim (fun i => vecEntry eB i * vecEntry fB i) := by
        rw [← sumUpTo_scale]
        exact sumUpTo_congr B.portDim _ _ (fun i hi => by rw [vecEntry_mkVec B.portDim _ i hi]; grind)
      rw [hScale]; grind
    rw [hCancel] at hp2
    grind
  stepObs x := S2.stepObs (S1.stepObs x)
  stepObs_nonexpansive x y :=
    Rat.le_trans (S2.stepObs_nonexpansive (S1.stepObs x) (S1.stepObs y))
                 (S1.stepObs_nonexpansive x y)

/-- **Horizontal Interconnection Preserves Power Balance (`horizComp_preserves_power_balance`)**:
    Arbitrary relational Dirac / port-Hamiltonian composition cancels internal boundary power
    $e_B \cdot f_B + e_B \cdot (-f_B) = 0$, preserving $e_A \cdot f_A + e_C \cdot f_C \le 0$. -/
theorem horizComp_preserves_power_balance {A B C : ScaleObj}
    (S1 : HorizOpenSys A B) (S2 : HorizOpenSys B C)
    (fA eA fC eC : List CanonicalRat)
    (hRel : (horizComp S1 S2).portRel fA eA fC eC) :
    vecDotN A.portDim eA fA + vecDotN C.portDim eC fC ≤ 0 :=
  (horizComp S1 S2).power_dissipative fA eA fC eC hRel

/-- Embed any certified lossless `KernelDirac` of dimension `A.portDim + B.portDim` directly as a
    horizontal 1-morphism `HorizOpenSys A B` (`e_A · f_A + e_B · f_B = 0 ≤ 0`). -/
def KernelDirac.toHorizOpenSys {A B : ScaleObj} (D : KernelDirac)
    (hDim : D.dim = A.portDim + B.portDim)
    (hOk : checkDiracIsotropicAndRank D = true)
    (obsMap : List CanonicalRat → List CanonicalRat)
    (hLip : ∀ x y, vecMaxDist B.obsDim (obsMap x) (obsMap y) ≤ vecMaxDist A.obsDim x y) :
    HorizOpenSys A B where
  portRel fA eA fB eB := D.Mem (splitConcatVec A.portDim B.portDim fA fB)
                               (splitConcatVec A.portDim B.portDim eA eB)
  power_dissipative fA eA fB eB hMem := by
    have h0 := dirac_power_conservation D hOk
      (splitConcatVec A.portDim B.portDim fA fB) (splitConcatVec A.portDim B.portDim eA eB) hMem
    rw [hDim, vecDotN_splitConcat] at h0
    grind
  stepObs := obsMap
  stepObs_nonexpansive := hLip

/-- Disjoint union (coproduct) of two oriented 3-skeleton cell complexes $K_1 \sqcup K_2$,
    offsetting $K_2$'s vertex, edge, and face indices by $(|V_1|, |E_1|, |F_1|)$. -/
def disjointUnionComplex (K1 K2 : CellComplex3D) : CellComplex3D where
  numV := K1.numV + K2.numV
  edges := K1.edges ++ K2.edges.map (fun (u, w) => (K1.numV + u, K1.numV + w))
  faces := K1.faces ++ K2.faces.map (fun ch => ch.map (fun (e, s) => (K1.numE + e, s)))
  volumes := K1.volumes ++ K2.volumes.map (fun ch => ch.map (fun (f, s) => (K1.numF + f, s)))

theorem disjointUnionComplex_counts (K1 K2 : CellComplex3D) :
    (disjointUnionComplex K1 K2).numV = K1.numV + K2.numV ∧
    (disjointUnionComplex K1 K2).numE = K1.numE + K2.numE ∧
    (disjointUnionComplex K1 K2).numF = K1.numF + K2.numF ∧
    (disjointUnionComplex K1 K2).numC = K1.numC + K2.numC := by
  simp [disjointUnionComplex, CellComplex3D.numE, CellComplex3D.numF, CellComplex3D.numC]

/-- Symmetric monoidal object tensor $A_1 \otimes A_2$ summing port/observable dimensions and taking $K_1 \sqcup K_2$. -/
def tensorScaleObj (A1 A2 : ScaleObj) : ScaleObj where
  portDim := A1.portDim + A2.portDim
  obsDim  := A1.obsDim + A2.obsDim
  complex := disjointUnionComplex A1.complex A2.complex

/-- Parallel monoidal product `horizTensor S1 S2` of two open acausal systems. -/
def horizTensor {A1 B1 A2 B2 : ScaleObj}
    (S1 : HorizOpenSys A1 B1) (S2 : HorizOpenSys A2 B2) :
    HorizOpenSys (tensorScaleObj A1 A2) (tensorScaleObj B1 B2) where
  portRel fA eA fB eB :=
    ∃ fA1 fA2 eA1 eA2 fB1 fB2 eB1 eB2,
      (∀ i, i < A1.portDim + A2.portDim →
        vecEntry fA i = vecEntry (splitConcatVec A1.portDim A2.portDim fA1 fA2) i ∧
        vecEntry eA i = vecEntry (splitConcatVec A1.portDim A2.portDim eA1 eA2) i) ∧
      (∀ j, j < B1.portDim + B2.portDim →
        vecEntry fB j = vecEntry (splitConcatVec B1.portDim B2.portDim fB1 fB2) j ∧
        vecEntry eB j = vecEntry (splitConcatVec B1.portDim B2.portDim eB1 eB2) j) ∧
      S1.portRel fA1 eA1 fB1 eB1 ∧
      S2.portRel fA2 eA2 fB2 eB2
  power_dissipative fA eA fB eB := by
    rintro ⟨fA1, fA2, eA1, eA2, fB1, fB2, eB1, eB2, hA, hB, hR1, hR2⟩
    have hDotA : vecDotN (A1.portDim + A2.portDim) eA fA =
        vecDotN A1.portDim eA1 fA1 + vecDotN A2.portDim eA2 fA2 := by
      rw [← vecDotN_splitConcat]
      exact sumUpTo_congr _ _ _ (fun i hi => by rw [(hA i hi).1, (hA i hi).2])
    have hDotB : vecDotN (B1.portDim + B2.portDim) eB fB =
        vecDotN B1.portDim eB1 fB1 + vecDotN B2.portDim eB2 fB2 := by
      rw [← vecDotN_splitConcat]
      exact sumUpTo_congr _ _ _ (fun j hj => by rw [(hB j hj).1, (hB j hj).2])
    change vecDotN (A1.portDim + A2.portDim) eA fA + vecDotN (B1.portDim + B2.portDim) eB fB ≤ 0
    rw [hDotA, hDotB]
    have hp1 := S1.power_dissipative fA1 eA1 fB1 eB1 hR1
    have hp2 := S2.power_dissipative fA2 eA2 fB2 eB2 hR2
    grind
  stepObs x :=
    let x1 := mkVec A1.obsDim (fun i => vecEntry x i)
    let x2 := mkVec A2.obsDim (fun j => vecEntry x (A1.obsDim + j))
    splitConcatVec B1.obsDim B2.obsDim (S1.stepObs x1) (S2.stepObs x2)
  stepObs_nonexpansive x y := by
    change vecMaxDist (B1.obsDim + B2.obsDim) _ _ ≤ vecMaxDist (A1.obsDim + A2.obsDim) x y
    rw [vecMaxDist_le_iff _ _ _ _ (vecMaxDist_nonneg _ x y)]
    intro k hk
    unfold splitConcatVec
    rw [vecEntry_mkVec (B1.obsDim + B2.obsDim) _ k hk,
        vecEntry_mkVec (B1.obsDim + B2.obsDim) _ k hk]
    let x1 := mkVec A1.obsDim (fun i => vecEntry x i)
    let y1 := mkVec A1.obsDim (fun i => vecEntry y i)
    let x2 := mkVec A2.obsDim (fun j => vecEntry x (A1.obsDim + j))
    let y2 := mkVec A2.obsDim (fun j => vecEntry y (A1.obsDim + j))
    have hBound1 : vecMaxDist A1.obsDim x1 y1 ≤ vecMaxDist (A1.obsDim + A2.obsDim) x y := by
      rw [vecMaxDist_le_iff _ _ _ _ (vecMaxDist_nonneg _ x y)]
      intro i hi
      dsimp [x1, y1]
      rw [vecEntry_mkVec A1.obsDim _ i hi, vecEntry_mkVec A1.obsDim _ i hi]
      exact entry_diff_le_vecMaxDist (A1.obsDim + A2.obsDim) x y i (by omega)
    have hBound2 : vecMaxDist A2.obsDim x2 y2 ≤ vecMaxDist (A1.obsDim + A2.obsDim) x y := by
      rw [vecMaxDist_le_iff _ _ _ _ (vecMaxDist_nonneg _ x y)]
      intro j hj
      dsimp [x2, y2]
      rw [vecEntry_mkVec A2.obsDim _ j hj, vecEntry_mkVec A2.obsDim _ j hj]
      exact entry_diff_le_vecMaxDist (A1.obsDim + A2.obsDim) x y (A1.obsDim + j) (by omega)
    by_cases hk1 : k < B1.obsDim
    · simp only [hk1, ↓reduceIte]
      exact Rat.le_trans (entry_diff_le_vecMaxDist B1.obsDim (S1.stepObs x1) (S1.stepObs y1) k hk1)
        (Rat.le_trans (S1.stepObs_nonexpansive x1 y1) hBound1)
    · simp only [hk1, ↓reduceIte]
      have hk2 : k - B1.obsDim < B2.obsDim := by omega
      exact Rat.le_trans (entry_diff_le_vecMaxDist B2.obsDim (S2.stepObs x2) (S2.stepObs y2) (k - B1.obsDim) hk2)
        (Rat.le_trans (S2.stepObs_nonexpansive x2 y2) hBound2)

/-! ### 2.1 Vertical 1-Morphisms: Cochain Coarse-Graining (`VertCoarseGrain`) -/

/-- Vertical 1-morphisms `VertCoarseGrain Fine Coarse`: cochain complex map
    $\pi_\bullet : (C_{\text{fine}}^\bullet, d_{\text{fine}}) \to (C_{\text{coarse}}^\bullet, d_{\text{coarse}})$
    commuting strictly with exterior coboundaries $d_0, d_1, d_2$, paired with a non-expansive
    observable projection `projObs`. -/
structure VertCoarseGrain (Fine Coarse : ScaleObj) where
  proj0 : List CanonicalRat → List CanonicalRat
  proj1 : List CanonicalRat → List CanonicalRat
  proj2 : List CanonicalRat → List CanonicalRat
  proj3 : List CanonicalRat → List CanonicalRat
  proj1_zero : proj1 (zeroCochain Fine.complex.numE) = zeroCochain Coarse.complex.numE
  proj2_zero : proj2 (zeroCochain Fine.complex.numF) = zeroCochain Coarse.complex.numF
  proj3_zero : proj3 (zeroCochain Fine.complex.numC) = zeroCochain Coarse.complex.numC
  proj1_add : ∀ α β,
    proj1 (vecAddN Fine.complex.numE α β) = vecAddN Coarse.complex.numE (proj1 α) (proj1 β)
  commutes01 : ∀ φ, d0 Coarse.complex (proj0 φ) = proj1 (d0 Fine.complex φ)
  commutes12 : ∀ α, d1 Coarse.complex (proj1 α) = proj2 (d1 Fine.complex α)
  commutes23 : ∀ B, d2 Coarse.complex (proj2 B) = proj3 (d2 Fine.complex B)
  projObs : List CanonicalRat → List CanonicalRat
  projObs_nonexpansive : ∀ x y,
    vecMaxDist Coarse.obsDim (projObs x) (projObs y) ≤ vecMaxDist Fine.obsDim x y

/-- Vertical identity coarse-graining on `A`. -/
def VertCoarseGrain.id (A : ScaleObj) : VertCoarseGrain A A where
  proj0 x := x; proj1 x := x; proj2 x := x; proj3 x := x
  proj1_zero := rfl; proj2_zero := rfl; proj3_zero := rfl; proj1_add _ _ := rfl
  commutes01 _ := rfl; commutes12 _ := rfl; commutes23 _ := rfl
  projObs x := x; projObs_nonexpansive _ _ := by grind

/-- Vertical composition of multiscale cochain projections `vertComp π1 π2`. -/
def vertComp {F M C : ScaleObj}
    (π1 : VertCoarseGrain F M) (π2 : VertCoarseGrain M C) : VertCoarseGrain F C where
  proj0 x := π2.proj0 (π1.proj0 x); proj1 x := π2.proj1 (π1.proj1 x)
  proj2 x := π2.proj2 (π1.proj2 x); proj3 x := π2.proj3 (π1.proj3 x)
  proj1_zero := by rw [π1.proj1_zero, π2.proj1_zero]
  proj2_zero := by rw [π1.proj2_zero, π2.proj2_zero]
  proj3_zero := by rw [π1.proj3_zero, π2.proj3_zero]
  proj1_add α β := by rw [π1.proj1_add, π2.proj1_add]
  commutes01 φ := by rw [π2.commutes01, π1.commutes01]
  commutes12 α := by rw [π2.commutes12, π1.commutes12]
  commutes23 B := by rw [π2.commutes23, π1.commutes23]
  projObs x := π2.projObs (π1.projObs x)
  projObs_nonexpansive x y :=
    Rat.le_trans (π2.projObs_nonexpansive (π1.projObs x) (π1.projObs y)) (π1.projObs_nonexpansive x y)

/-- **Coarse-Graining Preserves Cohomology & Topological Conservation (`coarseGrain_preserves_cohomology_and_conservation`)**:
    1. Closed 1-cocycles (irrotational fields $d_1 \alpha = 0$) project to closed coarse 1-cocycles $d_1(\pi_1 \alpha) = 0$.
    2. Divergence-free magnetic 2-cochains ($d_2 B_{\text{fine}} = 0$) project to divergence-free coarse 2-cochains
       $d_2(\pi_2 B_{\text{fine}}) = 0$ with zero topological monopole drift.
    3. Gauge-equivalent 1-cochains $\alpha' = \alpha + d_0 \chi$ map to coarse gauge-equivalent 1-cochains
       $\pi_1 \alpha' = \pi_1 \alpha + d_0(\pi_0 \chi)$ (well-defined map on $H^1$). -/
theorem coarseGrain_preserves_cohomology_and_conservation {Fine Coarse : ScaleObj}
    (π : VertCoarseGrain Fine Coarse) :
    (∀ α, d1 Fine.complex α = zeroCochain Fine.complex.numF →
      d1 Coarse.complex (π.proj1 α) = zeroCochain Coarse.complex.numF) ∧
    (∀ B, d2 Fine.complex B = zeroCochain Fine.complex.numC →
      d2 Coarse.complex (π.proj2 B) = zeroCochain Coarse.complex.numC) ∧
    (∀ α χ,
      π.proj1 (vecAddN Fine.complex.numE α (d0 Fine.complex χ)) =
        vecAddN Coarse.complex.numE (π.proj1 α) (d0 Coarse.complex (π.proj0 χ))) := by
  refine ⟨fun α hClosed => ?_, fun B hDiv0 => ?_, fun α χ => ?_⟩
  · rw [π.commutes12, hClosed, π.proj2_zero]
  · rw [π.commutes23, hDiv0, π.proj3_zero]
  · rw [π.proj1_add, π.commutes01]

/-! ### 2.2 Graded 2-Cells (`MultiscaleSquare`), Pasting Laws & Double-Categorical Interchange -/

/-- Quantitative 2-cells `MultiscaleSquare` of `MultiscaleOpenDouble`:
    witnesses that evolving the fine open system `S_fine` and coarse-graining via `π_out` agrees
    with coarse-graining via `π_in` and evolving `S_coarse` within rational Mori–Zwanzig subgrid
    closure bound `defectEps ≥ 0`, tracked alongside 5-axis `CompositeGrade` (`Obend.Category.GradedLogic`). -/
structure MultiscaleSquare {F1 F2 C1 C2 : ScaleObj}
    (S_fine : HorizOpenSys F1 F2) (S_coarse : HorizOpenSys C1 C2)
    (π_in : VertCoarseGrain F1 C1) (π_out : VertCoarseGrain F2 C2) where
  defectEps     : CanonicalRat
  defect_nonneg : 0 ≤ defectEps
  grade         : CompositeGrade
  closure_bound : ∀ x : List CanonicalRat,
    vecMaxDist C2.obsDim (π_out.projObs (S_fine.stepObs x))
                         (S_coarse.stepObs (π_in.projObs x)) ≤ defectEps

/-- Identity 2-cell on any vertical projection `π` (zero subgrid defect, zero `CompositeGrade`). -/
def MultiscaleSquare.hId {F C : ScaleObj} (π : VertCoarseGrain F C) :
    MultiscaleSquare (HorizOpenSys.id F) (HorizOpenSys.id C) π π where
  defectEps := 0
  defect_nonneg := by decide +kernel
  grade := 0
  closure_bound x := by
    dsimp [HorizOpenSys.id]
    rw [vecMaxDist_refl]
    decide +kernel

/-- Identity 2-cell on any horizontal open system `S` (zero subgrid defect, zero `CompositeGrade`). -/
def MultiscaleSquare.vId {A B : ScaleObj} (S : HorizOpenSys A B) :
    MultiscaleSquare S S (VertCoarseGrain.id A) (VertCoarseGrain.id B) where
  defectEps := 0
  defect_nonneg := by decide +kernel
  grade := 0
  closure_bound x := by
    dsimp [VertCoarseGrain.id]
    rw [vecMaxDist_refl]
    decide +kernel

/-- **Horizontal Pasting (`hPaste`, `α ⊞ₕ β`)** of adjacent multiscale squares along a shared vertical
    projection `π_mid : F2 → C2`. -/
def hPaste {F1 F2 F3 C1 C2 C3 : ScaleObj}
    {Sf1 : HorizOpenSys F1 F2} {Sf2 : HorizOpenSys F2 F3}
    {Sc1 : HorizOpenSys C1 C2} {Sc2 : HorizOpenSys C2 C3}
    {π1 : VertCoarseGrain F1 C1} {π2 : VertCoarseGrain F2 C2} {π3 : VertCoarseGrain F3 C3}
    (α : MultiscaleSquare Sf1 Sc1 π1 π2)
    (β : MultiscaleSquare Sf2 Sc2 π2 π3) :
    MultiscaleSquare (horizComp Sf1 Sf2) (horizComp Sc1 Sc2) π1 π3 where
  defectEps := α.defectEps + β.defectEps
  defect_nonneg := by have := α.defect_nonneg; have := β.defect_nonneg; grind
  grade := α.grade + β.grade
  closure_bound x := by
    dsimp [horizComp]
    have hTri := vecMaxDist_triangle C3.obsDim
      (π3.projObs (Sf2.stepObs (Sf1.stepObs x)))
      (Sc2.stepObs (π2.projObs (Sf1.stepObs x)))
      (Sc2.stepObs (Sc1.stepObs (π1.projObs x)))
    have hBeta := β.closure_bound (Sf1.stepObs x)
    have hLip := Sc2.stepObs_nonexpansive (π2.projObs (Sf1.stepObs x)) (Sc1.stepObs (π1.projObs x))
    have hAlpha := α.closure_bound x
    grind

/-- **Vertical Pasting (`vPaste`, `α ⊞ᵥ γ`)** of stacked multiscale squares across three resolution
    scales `Fine → Meso → Macro`. -/
def vPaste {F1 F2 M1 M2 C1 C2 : ScaleObj}
    {Sf : HorizOpenSys F1 F2} {Sm : HorizOpenSys M1 M2} {Sc : HorizOpenSys C1 C2}
    {π1L : VertCoarseGrain F1 M1} {π1R : VertCoarseGrain F2 M2}
    {π2L : VertCoarseGrain M1 C1} {π2R : VertCoarseGrain M2 C2}
    (α : MultiscaleSquare Sf Sm π1L π1R)
    (γ : MultiscaleSquare Sm Sc π2L π2R) :
    MultiscaleSquare Sf Sc (vertComp π1L π2L) (vertComp π1R π2R) where
  defectEps := α.defectEps + γ.defectEps
  defect_nonneg := by have := α.defect_nonneg; have := γ.defect_nonneg; grind
  grade := α.grade + γ.grade
  closure_bound x := by
    dsimp [vertComp]
    have hTri := vecMaxDist_triangle C2.obsDim
      (π2R.projObs (π1R.projObs (Sf.stepObs x)))
      (π2R.projObs (Sm.stepObs (π1L.projObs x)))
      (Sc.stepObs (π2L.projObs (π1L.projObs x)))
    have hProj := π2R.projObs_nonexpansive (π1R.projObs (Sf.stepObs x)) (Sm.stepObs (π1L.projObs x))
    have hAlpha := α.closure_bound x
    have hGamma := γ.closure_bound (π1L.projObs x)
    grind

/-- **Horizontal Pasting Soundness (`hPaste_sound`)**:
    Horizontally pasted squares satisfy the summed subgrid closure bound $\varepsilon_\alpha + \varepsilon_\beta$,
    summed `CompositeGrade`, and preserve dissipative boundary power balance. -/
theorem hPaste_sound {F1 F2 F3 C1 C2 C3 : ScaleObj}
    {Sf1 : HorizOpenSys F1 F2} {Sf2 : HorizOpenSys F2 F3}
    {Sc1 : HorizOpenSys C1 C2} {Sc2 : HorizOpenSys C2 C3}
    {π1 : VertCoarseGrain F1 C1} {π2 : VertCoarseGrain F2 C2} {π3 : VertCoarseGrain F3 C3}
    (α : MultiscaleSquare Sf1 Sc1 π1 π2)
    (β : MultiscaleSquare Sf2 Sc2 π2 π3) :
    (hPaste α β).defectEps = α.defectEps + β.defectEps ∧
    (hPaste α β).grade = α.grade + β.grade ∧
    (∀ x, vecMaxDist C3.obsDim
      (π3.projObs ((horizComp Sf1 Sf2).stepObs x))
      ((horizComp Sc1 Sc2).stepObs (π1.projObs x)) ≤ α.defectEps + β.defectEps) ∧
    (∀ fA eA fC eC, (horizComp Sc1 Sc2).portRel fA eA fC eC →
      vecDotN C1.portDim eA fA + vecDotN C3.portDim eC fC ≤ 0) :=
  ⟨rfl, rfl, (hPaste α β).closure_bound, horizComp_preserves_power_balance Sc1 Sc2⟩

/-- **Vertical Pasting Soundness (`vPaste_sound`)**:
    Vertically pasted squares across `Fine → Meso → Macro` accumulate subgrid closure defects
    $\varepsilon_\alpha + \varepsilon_\gamma$ and `CompositeGrade` $g_\alpha + g_\gamma$ while preserving
    exact cochain conservation laws across both projections. -/
theorem vPaste_sound {F1 F2 M1 M2 C1 C2 : ScaleObj}
    {Sf : HorizOpenSys F1 F2} {Sm : HorizOpenSys M1 M2} {Sc : HorizOpenSys C1 C2}
    {π1L : VertCoarseGrain F1 M1} {π1R : VertCoarseGrain F2 M2}
    {π2L : VertCoarseGrain M1 C1} {π2R : VertCoarseGrain M2 C2}
    (α : MultiscaleSquare Sf Sm π1L π1R)
    (γ : MultiscaleSquare Sm Sc π2L π2R) :
    (vPaste α γ).defectEps = α.defectEps + γ.defectEps ∧
    (vPaste α γ).grade = α.grade + γ.grade ∧
    (∀ x, vecMaxDist C2.obsDim
      ((vertComp π1R π2R).projObs (Sf.stepObs x))
      (Sc.stepObs ((vertComp π1L π2L).projObs x)) ≤ α.defectEps + γ.defectEps) ∧
    (∀ B, d2 F2.complex B = zeroCochain F2.complex.numC →
      d2 C2.complex ((vertComp π1R π2R).proj2 B) = zeroCochain C2.complex.numC) :=
  ⟨rfl, rfl, (vPaste α γ).closure_bound,
   (coarseGrain_preserves_cohomology_and_conservation (vertComp π1R π2R)).2.1⟩

/-- **Double-Categorical Interchange Law (`doubleCat_interchange_law` / Eckmann–Hilton Mediality)**:
    For any $2 \times 2$ grid of multiscale squares
    `α` (top-left), `β` (top-right), `γ` (bottom-left), `δ` (bottom-right),
    vertical-of-horizontal pasting `(α ⊞ₕ β) ⊞ᵥ (γ ⊞ₕ δ)` and horizontal-of-vertical pasting
    `(α ⊞ᵥ γ) ⊞ₕ (β ⊞ᵥ δ)` produce the **exact same** total rational subgrid closure bound,
    the **exact same** 5-axis `CompositeGrade`, and identical composite boundary closure guarantees. -/
theorem doubleCat_interchange_law
    {A00 A01 A02 A10 A11 A12 A20 A21 A22 : ScaleObj}
    {S0 : HorizOpenSys A00 A01} {T0 : HorizOpenSys A01 A02}
    {S1 : HorizOpenSys A10 A11} {T1 : HorizOpenSys A11 A12}
    {S2 : HorizOpenSys A20 A21} {T2 : HorizOpenSys A21 A22}
    {π00 : VertCoarseGrain A00 A10} {π01 : VertCoarseGrain A01 A11} {π02 : VertCoarseGrain A02 A12}
    {π10 : VertCoarseGrain A10 A20} {π11 : VertCoarseGrain A11 A21} {π12 : VertCoarseGrain A12 A22}
    (α : MultiscaleSquare S0 S1 π00 π01)
    (β : MultiscaleSquare T0 T1 π01 π02)
    (γ : MultiscaleSquare S1 S2 π10 π11)
    (δ : MultiscaleSquare T1 T2 π11 π12) :
    let vh := vPaste (hPaste α β) (hPaste γ δ)
    let hv := hPaste (vPaste α γ) (vPaste β δ)
    vh = hv ∧
    vh.defectEps = hv.defectEps ∧
    vh.grade = hv.grade ∧
    (∀ x, vecMaxDist A22.obsDim
      (π12.projObs (π02.projObs (T0.stepObs (S0.stepObs x))))
      (T2.stepObs (S2.stepObs (π10.projObs (π00.projObs x)))) ≤ vh.defectEps) ∧
    (∀ x, vecMaxDist A22.obsDim
      (π12.projObs (π02.projObs (T0.stepObs (S0.stepObs x))))
      (T2.stepObs (S2.stepObs (π10.projObs (π00.projObs x)))) ≤ hv.defectEps) := by
  intro vh hv
  have hEps : vh.defectEps = hv.defectEps := by
    change (α.defectEps + β.defectEps) + (γ.defectEps + δ.defectEps) =
           (α.defectEps + γ.defectEps) + (β.defectEps + δ.defectEps); grind
  have hGrade : vh.grade = hv.grade := by
    change (α.grade + β.grade) + (γ.grade + δ.grade) = (α.grade + γ.grade) + (β.grade + δ.grade)
    rw [GradeMonoid.add_assoc α.grade β.grade (γ.grade + δ.grade),
        ← GradeMonoid.add_assoc β.grade γ.grade δ.grade, GradeMonoid.add_comm β.grade γ.grade,
        GradeMonoid.add_assoc γ.grade β.grade δ.grade, ← GradeMonoid.add_assoc α.grade γ.grade (β.grade + δ.grade)]
  have hEq : vh = hv := by
    cases h1 : vh with | mk e1 nn1 g1 cb1 =>
    cases h2 : hv with | mk e2 nn2 g2 cb2 =>
    have he : e1 = e2 := by simpa [h1, h2] using hEps
    have hg : g1 = g2 := by simpa [h1, h2] using hGrade
    subst he; subst hg; rfl
  exact ⟨hEq, hEps, hGrade, vh.closure_bound, hv.closure_bound⟩

/-- Lift any `MultiscaleSquare` into a stateful graded computation in `GradedM CompositeGrade`
    (`Obend.Category.GradedLogic`), advancing the coarse observable while bounding subgrid error. -/
@[expose] def MultiscaleSquare.toGradedCmd {F1 F2 C1 C2 : ScaleObj}
    {Sf : HorizOpenSys F1 F2} {Sc : HorizOpenSys C1 C2}
    {πL : VertCoarseGrain F1 C1} {πR : VertCoarseGrain F2 C2}
    (sq : MultiscaleSquare Sf Sc πL πR) :
    GradedM CompositeGrade (List CanonicalRat) (List CanonicalRat) where
  run xFine :=
    (Sc.stepObs (πL.projObs xFine), Sf.stepObs xFine, sq.grade)

/-- Certified `GradedTriple` (`Obend.Category.GradedLogic`) for `MultiscaleSquare.toGradedCmd`. -/
theorem multiscaleSquare_gradedTriple {F1 F2 C1 C2 : ScaleObj}
    {Sf : HorizOpenSys F1 F2} {Sc : HorizOpenSys C1 C2}
    {πL : VertCoarseGrain F1 C1} {πR : VertCoarseGrain F2 C2}
    (sq : MultiscaleSquare Sf Sc πL πR) :
    GradedTriple (fun _ => True) sq.toGradedCmd sq.grade
      (fun coarseOut fineNext => vecMaxDist C2.obsDim (πR.projObs fineNext) coarseOut ≤ sq.defectEps) := by
  intro s _
  exact ⟨sq.closure_bound s, GradeMonoid.le_refl sq.grade⟩

/-! ## 3. Worked Multiscale Square: $N$-Cell Fine DEC Telegrapher/RC Line $\to$ Lumped MNA Section -/

/-- $N$-cell 1D DEC transmission line complex ($N + 1$ vertices $0 \dots N$, $N$ oriented edges $k \to k+1$). -/
def fineLineComplex (N : Nat) : CellComplex3D where
  numV    := N + 1
  edges   := (List.range N).map (fun k => (k, k + 1))
  faces   := []
  volumes := []

/-- Lumped 1-section macro complex ($2$ boundary vertices $0, 1$, $1$ macro-edge $0 \to 1$). -/
def lumpedSectionComplex : CellComplex3D := segment1DComplex

private theorem getElem?_map_range (N : Nat) (g : Nat → Nat × Nat) (k : Nat) (hk : k < N) :
    ((List.range N).map g)[k]? = some (g k) := by
  simp [hk]

/-- `fineLineComplex N` is a certified exact DEC cell complex for every $N \in \mathbb{N}$. -/
theorem fineLineComplex_exact (N : Nat) :
    checkComplexExact (fineLineComplex N) = true := by
  simp only [checkComplexExact, fineLineComplex, CellComplex3D.numF, CellComplex3D.numC,
    List.length_nil, List.range_zero, List.all_nil, Bool.and_true, List.all_eq_true,
    List.mem_map, List.mem_range, Bool.and_eq_true]
  rintro ⟨a, b⟩ ⟨k, hk, hEq⟩
  cases hEq
  exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩

/-- Discrete Fundamental Theorem of Calculus on `fineLineComplex N`: summing edge coboundaries
    $(d_0 \phi)_k = \phi_{k+1} - \phi_k$ telescopes identically to $\phi_N - \phi_0$. -/
theorem fineLine_d0_telescopes (N : Nat) (φ : List CanonicalRat) :
    sumUpTo N (fun k => vecEntry (d0 (fineLineComplex N) φ) k) =
      vecEntry φ N - vecEntry φ 0 := by
  have hExact := fineLineComplex_exact N
  have aux : ∀ m, m ≤ N →
      sumUpTo m (fun k => vecEntry (d0 (fineLineComplex N) φ) k) =
        vecEntry φ m - vecEntry φ 0 := by
    intro m hm
    induction m with
    | zero => dsimp [sumUpTo]; grind
    | succ j ih =>
      dsimp [sumUpTo]
      rw [ih (by omega)]
      have hEdge : (fineLineComplex N).edges[j]? = some (j, j + 1) :=
        getElem?_map_range N (fun k => (k, k + 1)) j (by omega)
      rw [d0_edge_diff (fineLineComplex N) hExact φ j j (j + 1) hEdge]
      grind
  exact aux N (Nat.le_refl N)

/-- Clamp a rational scalar onto the symmetric physical voltage envelope $[-V_{\max}, V_{\max}]$. -/
def clampRat (vMax x : CanonicalRat) : CanonicalRat :=
  if x < -vMax then -vMax else if vMax < x then vMax else x

private theorem clampRat_lipschitz (vMax : CanonicalRat) (hv : 0 ≤ vMax) (x y : CanonicalRat) :
    ratAbs (clampRat vMax x - clampRat vMax y) ≤ ratAbs (x - y) := by
  rw [ratAbs_le_iff]
  unfold ratAbs
  by_cases hx1 : x < -vMax <;> by_cases hx2 : vMax < x <;>
  by_cases hy1 : y < -vMax <;> by_cases hy2 : vMax < y <;>
  by_cases hxy : 0 ≤ x - y <;>
  simp only [clampRat, hx1, hx2, hy1, hy2, hxy, ↓reduceIte] <;> grind

private theorem clampRat_bounds (vMax : CanonicalRat) (hv : 0 ≤ vMax) (x : CanonicalRat) :
    -vMax ≤ clampRat vMax x ∧ clampRat vMax x ≤ vMax := by
  by_cases h1 : x < -vMax <;> by_cases h2 : vMax < x <;>
  simp only [clampRat, h1, h2, ↓reduceIte] <;> grind

/-- Scale object for an $N$-cell fine 1D DEC line (`obsDim` nodal voltages, 1-port terminals). -/
def fineLineScaleObj (N obsDim : Nat) : ScaleObj where
  portDim := 1
  obsDim  := obsDim
  complex := fineLineComplex N

/-- Scale object for the lumped 1-section MNA equivalent (`obsDim = 1` macro voltage). -/
def lumpedMnaScaleObj : ScaleObj where
  portDim := 1
  obsDim  := 1
  complex := lumpedSectionComplex

/-- Certified vertical coarse-graining `fineToLumpedCoarseGrain N` for **every** $N \ge 1$:
    - $\pi_0(\phi) = [\phi_0, \phi_N]$ (macro boundary terminal potentials),
    - $\pi_1(\alpha) = [\sum_{k=0}^{N-1} \alpha_k]$ (macro line-integral voltage),
    - $\pi_{\text{obs}}(v) = [(c_0 + c_1) / 2]$ (clamped spatial cell-average observable). -/
def fineToLumpedCoarseGrain (N : Nat) (_hN : 1 ≤ N) :
    VertCoarseGrain (fineLineScaleObj N 2) lumpedMnaScaleObj where
  proj0 φ := [vecEntry φ 0, vecEntry φ N]
  proj1 α := mkVec 1 (fun _ => sumUpTo N (fun k => vecEntry α k))
  proj2 _ := []
  proj3 _ := []
  proj1_zero := by
    dsimp only [fineLineScaleObj, lumpedMnaScaleObj]
    have hLenE : (fineLineComplex N).numE = N := by simp [fineLineComplex, CellComplex3D.numE]
    have hLenL : lumpedSectionComplex.numE = 1 := rfl
    rw [hLenE, hLenL]
    apply mkVec_ext 1 _ _ (fun i hi => ?_)
    have : i = 0 := by omega
    subst this
    rw [sumUpTo_congr N _ (fun _ => 0) (fun k _ => vecEntry_zeroCochain N k)]
    exact sumUpTo_zero N
  proj2_zero := rfl
  proj3_zero := rfl
  proj1_add α β := by
    dsimp only [fineLineScaleObj, lumpedMnaScaleObj]
    have hLenE : (fineLineComplex N).numE = N := by simp [fineLineComplex, CellComplex3D.numE]
    have hLenL : lumpedSectionComplex.numE = 1 := rfl
    rw [hLenE, hLenL]
    apply mkVec_ext 1 _ _ (fun i hi => ?_)
    have : i = 0 := by omega
    subst this
    unfold vecAddN
    rw [vecEntry_mkVec 1 _ 0 (by omega), vecEntry_mkVec 1 _ 0 (by omega), ← sumUpTo_add]
    exact sumUpTo_congr N _ _ (fun k hk => vecEntry_mkVec N _ k hk)
  commutes01 φ := by
    dsimp only [fineLineScaleObj, lumpedMnaScaleObj, lumpedSectionComplex]
    have hLHS := d0_edge_diff segment1DComplex (by decide +kernel) [vecEntry φ 0, vecEntry φ N] 0 0 1 rfl
    apply cochain_eq_of_entries 1 _ _ (d0_length _ _) (mkVec_length _ _)
    intro i hi
    have : i = 0 := by omega
    subst this
    rw [hLHS, vecEntry_mkVec 1 _ 0 (by omega), fineLine_d0_telescopes N φ]
    simp only [vecEntry_cons_zero, vecEntry_cons_succ]
  commutes12 _ := rfl
  commutes23 _ := rfl
  projObs v := [(clampRat 1 (vecEntry v 0) + clampRat 1 (vecEntry v 1)) / 2]
  projObs_nonexpansive x y := by
    dsimp only [fineLineScaleObj, lumpedMnaScaleObj]
    rw [vecMaxDist_le_iff 1 _ _ _ (vecMaxDist_nonneg 2 x y)]
    intro i hi
    have : i = 0 := by omega
    subst this
    have h0 := (ratAbs_le_iff _ _).mp (Rat.le_trans
      (clampRat_lipschitz 1 (by decide +kernel) (vecEntry x 0) (vecEntry y 0))
      (entry_diff_le_vecMaxDist 2 x y 0 (by omega)))
    have h1 := (ratAbs_le_iff _ _).mp (Rat.le_trans
      (clampRat_lipschitz 1 (by decide +kernel) (vecEntry x 1) (vecEntry y 1))
      (entry_diff_le_vecMaxDist 2 x y 1 (by omega)))
    simp only [vecEntry_cons_zero]
    rw [ratAbs_le_iff]
    grind

/-- Fine 2-cell Backward-Euler DEC telegrapher/RC section ($3 v_0' - v_1' = v_0$, $-v_0' + 2 v_1' = v_1$,
    inverse $\frac{1}{5}\begin{pmatrix} 2 & 1 \\ 1 & 3 \end{pmatrix}$) on physical envelope $[-1, 1]$. -/
def fine2CellHorizSys : HorizOpenSys (fineLineScaleObj 2 2) (fineLineScaleObj 2 2) where
  portRel fL eL fR eR :=
    vecEntry fR 0 = -vecEntry fL 0 ∧ vecEntry eR 0 = vecEntry eL 0
  power_dissipative fL eL fR eR := by
    rintro ⟨hf, he⟩
    dsimp only [fineLineScaleObj, vecDotN, sumUpTo]
    rw [hf, he]; grind
  stepObs v :=
    let v0 := clampRat 1 (vecEntry v 0)
    let v1 := clampRat 1 (vecEntry v 1)
    [(2 * v0 + v1) / 5, (v0 + 3 * v1) / 5]
  stepObs_nonexpansive x y := by
    dsimp only [fineLineScaleObj]
    rw [vecMaxDist_le_iff 2 _ _ _ (vecMaxDist_nonneg 2 x y)]
    intro i hi
    have h0 := (ratAbs_le_iff _ _).mp (Rat.le_trans
      (clampRat_lipschitz 1 (by decide +kernel) (vecEntry x 0) (vecEntry y 0))
      (entry_diff_le_vecMaxDist 2 x y 0 (by omega)))
    have h1 := (ratAbs_le_iff _ _).mp (Rat.le_trans
      (clampRat_lipschitz 1 (by decide +kernel) (vecEntry x 1) (vecEntry y 1))
      (entry_diff_le_vecMaxDist 2 x y 1 (by omega)))
    match i with
    | 0 | 1 =>
      simp only [vecEntry_cons_zero, vecEntry_cons_succ]
      rw [ratAbs_le_iff]; grind
    | n + 2 => omega

/-- Lumped 1-section MNA circuit specification ($C = [[2]]$, $G = [[6/7]]$, Backward-Euler $\Delta t = 1$
    giving $v' = \frac{7}{10} v$), paired with `Obend.Hardware.CircuitDae` passivity certificate. -/
def lumpedTelegrapherMnaSpec : MnaCircuitSpec where
  dim := 1; inputDim := 0; matC := [[2]]; matG := [[6 / 7]]; matB := [[]]; nlBranches := []

def lumpedTelegrapherMnaCert : MnaDaeCert where
  capGramFactors := [{ weight := 2, vec := [1] }]; condSymGramFactors := [{ weight := 12 / 7, vec := [1] }]

def lumpedTelegrapherMnaProb : MnaDaeProblem where
  spec := lumpedTelegrapherMnaSpec; method := .backwardEuler
  trace := [{ dt := 1, xPrev := [1], xNext := [7 / 10], uInput := [],
              iBranchesPrev := [], iBranchesNext := [], residualTol := 0 }]

/-- Coarse lumped MNA horizontal open system matching `lumpedTelegrapherMnaSpec` ($v' = \frac{7}{10} v$). -/
def lumpedMnaHorizSys : HorizOpenSys lumpedMnaScaleObj lumpedMnaScaleObj where
  portRel fL eL fR eR := vecEntry fR 0 = -vecEntry fL 0 ∧ vecEntry eR 0 = vecEntry eL 0
  power_dissipative fL eL fR eR := by rintro ⟨hf, he⟩; dsimp only [lumpedMnaScaleObj, vecDotN, sumUpTo]; rw [hf, he]; grind
  stepObs w := [(7 / 10) * clampRat 1 (vecEntry w 0)]
  stepObs_nonexpansive x y := by
    dsimp only [lumpedMnaScaleObj]; rw [vecMaxDist_le_iff 1 _ _ _ (vecMaxDist_nonneg 1 x y)]
    intro i hi; have : i = 0 := by omega
    subst this
    have h0 := (ratAbs_le_iff _ _).mp (Rat.le_trans
      (clampRat_lipschitz 1 (by decide +kernel) (vecEntry x 0) (vecEntry y 0))
      (entry_diff_le_vecMaxDist 1 x y 0 (by omega)))
    simp only [vecEntry_cons_zero]; rw [ratAbs_le_iff]; grind

private theorem clampRat_id_of_bounds (vMax x : CanonicalRat)
    (hLo : -vMax ≤ x) (hHi : x ≤ vMax) : clampRat vMax x = x := by
  by_cases h1 : x < -vMax <;> by_cases h2 : vMax < x <;>
  simp only [clampRat, h1, h2, ↓reduceIte] <;> grind

/-- **Worked Concrete Multiscale 2-Cell (`telegrapherToLumpedMnaSquare`)**:
    Coarse-grains `fine2CellHorizSys` into `lumpedMnaHorizSys` along `fineToLumpedCoarseGrain 2`
    with exact Mori–Zwanzig subgrid residual $\frac{1}{20}(c_1 - c_0)$ bounded uniformly by
    $\varepsilon = \frac{1}{10}$ across all nodal voltage profiles. -/
def telegrapherToLumpedMnaSquare :
    MultiscaleSquare fine2CellHorizSys lumpedMnaHorizSys
      (fineToLumpedCoarseGrain 2 (by omega))
      (fineToLumpedCoarseGrain 2 (by omega)) where
  defectEps := 1 / 10
  defect_nonneg := by decide +kernel
  grade := { uses := 2, errorNum := 1, noise := 0, cycles := 2, exergy := -1 }
  closure_bound v := by
    dsimp only [lumpedMnaScaleObj]
    rw [vecMaxDist_le_iff 1 _ _ _ (by decide +kernel)]
    intro i hi
    have : i = 0 := by omega
    subst this
    dsimp [fineToLumpedCoarseGrain, fine2CellHorizSys, lumpedMnaHorizSys]
    let c0 := clampRat 1 (vecEntry v 0)
    let c1 := clampRat 1 (vecEntry v 1)
    have hb0 := clampRat_bounds 1 (by decide +kernel) (vecEntry v 0)
    have hb1 := clampRat_bounds 1 (by decide +kernel) (vecEntry v 1)
    change ratAbs (vecEntry [(clampRat 1 (vecEntry [(2 * c0 + c1) / 5, (c0 + 3 * c1) / 5] 0) +
                              clampRat 1 (vecEntry [(2 * c0 + c1) / 5, (c0 + 3 * c1) / 5] 1)) / 2] 0 -
                   vecEntry [(7 / 10) * clampRat 1 (vecEntry [(c0 + c1) / 2] 0)] 0) ≤ 1 / 10
    simp only [vecEntry_cons_zero, vecEntry_cons_succ]
    rw [clampRat_id_of_bounds 1 ((2 * c0 + c1) / 5) (by grind) (by grind),
        clampRat_id_of_bounds 1 ((c0 + 3 * c1) / 5) (by grind) (by grind),
        clampRat_id_of_bounds 1 ((c0 + c1) / 2) (by grind) (by grind),
        ratAbs_le_iff]
    grind

/-- **Worked Multiscale Telegrapher-to-MNA Theorem (`telegrapherToLumpedMna_worked_sound`)**:
    1. `lumpedTelegrapherMnaProb` is certified `.ok` by `Obend.Hardware.CircuitDae.checkMnaDaeProblem`,
       establishing `MnaDaeMeaning` (`mnaCircuitDaeJudge` soundness).
    2. For every $N \ge 1$, `fineToLumpedCoarseGrain N` commutes exactly with $d_0$.
    3. On uniform states $[v, v]$, subgrid closure error vanishes identically (`= 0`), while on
       anti-symmetric subgrid mode $[-1, 1]$ it attains the sharp bound `1 / 10`. -/
theorem telegrapherToLumpedMna_worked_sound (N : Nat) (hN : 1 ≤ N) (φ : List CanonicalRat) :
    let π2 := fineToLumpedCoarseGrain 2 (Nat.le_succ_of_le (Nat.le_refl 1))
    checkMnaDaeProblem 1 lumpedTelegrapherMnaProb lumpedTelegrapherMnaCert = .ok ∧
    MnaDaeMeaning lumpedTelegrapherMnaProb lumpedTelegrapherMnaCert ∧
    d0 lumpedMnaScaleObj.complex ((fineToLumpedCoarseGrain N hN).proj0 φ) =
      (fineToLumpedCoarseGrain N hN).proj1 (d0 (fineLineScaleObj N 2).complex φ) ∧
    vecMaxDist 1 (π2.projObs (fine2CellHorizSys.stepObs [1 / 2, 1 / 2]))
                 (lumpedMnaHorizSys.stepObs (π2.projObs [1 / 2, 1 / 2])) = 0 ∧
    vecMaxDist 1 (π2.projObs (fine2CellHorizSys.stepObs [-1, 1]))
                 (lumpedMnaHorizSys.stepObs (π2.projObs [-1, 1])) = 1 / 10 := by
  have hCheckOk : checkMnaDaeProblem 1 lumpedTelegrapherMnaProb lumpedTelegrapherMnaCert = .ok := by
    decide +kernel
  exact ⟨hCheckOk, checkMnaDaeProblem_sound hCheckOk,
         (fineToLumpedCoarseGrain N hN).commutes01 φ,
         by decide +kernel, by decide +kernel⟩

end Obend.Geometry.DiracDoubleCat
end

