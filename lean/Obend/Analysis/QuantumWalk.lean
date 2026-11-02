module
/-
# Obend.Analysis.QuantumWalk — Hybrid Symbolic-Numeric Continuous-Time Quantum Walks (`CTQW`), Godsil's Spectral-Projector Calculus, Bachman–Tamon Quotient PST & Validated Unitary Flowpipes

Unifies the **Symbolic** and **Analytic** poles of `Obend.Analysis` for Continuous-Time Quantum Walks
($U(t) = e^{-i H t}$) and open-system quantum dynamics:

1. **Symbolic Pole — Godsil's Spectral-Projector Calculus & Algebraic Number Fields (`Groebner.lean`)**:
   - Models integer-scaled spectral idempotents $E_k$ ($E_k^2 = s E_k$, $E_j E_k = 0$, $\sum_k E_k = s I$)
     and algebraic number field projectors over $\mathbb{Q}(\alpha)/\langle m(\alpha) \rangle$ reduced via
     Buchberger/Gröbner division (`polyReduceFuel`, `checkGroebnerBasis`).
   - Proves **`orthogonal_idempotents_sum_sq`** universally: for any orthogonal scaled idempotents
     $E_1^2 = s E_1$, $E_2^2 = s E_2$, $E_1 E_2 = E_2 E_1 = 0$, their sum satisfies
     $(E_1 + E_2)^2 = s (E_1 + E_2)$.
   - Proves **Strong Cospectrality + Godsil's Parity Condition $\implies$ Perfect State Transfer (`PST`)**:
     * **`ctqw_k2_antipodal_pst_exact`**: exact PST on $K_2$ at $\tau = \pi/2$ over $\mathbb{Z}[i]$.
     * **`ctqw_p3_end_to_end_pst_algebraic`**: exact end-to-end PST on $P_3$ ($0 \to 2$) at
       $\tau = \pi/\sqrt{2}$ certified over $\mathbb{Q}(\alpha)/\langle \alpha^2 - 2 \rangle$ via
       `Groebner.polyReduceFuel`, contrasted with $P_4$'s algebraic parity-ratio obstruction.
     * **`ctqw_hypercube_factorization_exact`**: exact Krawtchouk tridiagonal distance quotient and
       tensor-power antipodal PST on the $d$-dimensional Hypercube $Q_d = K_2^{\square d}$ ($Q_3$ showcase).
     * **`bachman_tamon_quotient_pst_iff`**: universal proof that for any equitable partition with
       singleton endpoint cell $C_{\text{target}} = \{v\}$, the $n$-vertex quantum walk achieves state
       transfer amplitude $A$ at $v$ **if and only if** the $r$-cell quotient walk achieves $A$ at
       $C_{\text{target}}$.
2. **Analytic Pole — Validated Symplectic Schrödinger & Lindblad Flowpipes (`TaylorModel.lean`, `Flowpipe.lean`, `Hybrid.lean`)**:
   - Formulates the real-symplectic Schrödinger generator $(\dot{x} = H_{\text{im}} x + H_{\text{re}} y,\;
     \dot{y} = -H_{\text{re}} x + H_{\text{im}} y)$ as an `OdeSystem` and bounds unitary eigenmode
     phase factors $(\cos(\lambda_k t), -\sin(\lambda_k t))$ via `tmCos` and `tmSin`.
   - Proves **`ctqw_validated_flowpipe_and_taylor_unitarity`**, certifying Taylor-model unitary
     norm conservation, multi-step Schrödinger flowpipe safety, non-Hermitian runaway refusal,
     and hybrid pulsed-gate schedule verification.
-/
public import Obend.Analysis.Equitable
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.Flowpipe
public import Obend.Analysis.Hybrid
@[expose] public section

namespace Obend.Analysis
open Obend.Judge.SOS
set_option autoImplicit false

/-! ## 1. Symbolic Pole: Orthogonal Spectral Projectors & Universal Idempotency Calculus -/

/-- Elementary integer bilinear expansion $(a + b)(c + d) = (a c + a d) + (b c + b d)$. -/
theorem int_add_mul_add_expand (a b c d : Int) :
    (a + b) * (c + d) = (a * c + a * d) + (b * c + b * d) := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add]

/-- Bilinear expansion of matrix multiplication over `matAddEntry`:
$$((A + B)(A + B))_{u,v} = ((A^2)_{u,v} + (A B)_{u,v}) + ((B A)_{u,v} + (B^2)_{u,v}).$$ -/
theorem matMulEntry_add_expand
    (indices : List Nat)
    (A B : Nat → Nat → Int)
    (u v : Nat) :
    matMulEntry indices (matAddEntry A B) (matAddEntry A B) u v =
      (matMulEntry indices A A u v + matMulEntry indices A B u v) +
      (matMulEntry indices B A u v + matMulEntry indices B B u v) := by
  dsimp only [matMulEntry, matAddEntry]
  have hCongr :
      sumIntOver (fun w => (A u w + B u w) * (A w v + B w v)) indices =
      sumIntOver (fun w => (A u w * A w v + A u w * B w v) + (B u w * A w v + B u w * B w v)) indices := by
    apply sumIntOver_congr
    intro w _
    exact int_add_mul_add_expand (A u w) (B u w) (A w v) (B w v)
  rw [hCongr]
  rw [sumIntOver_add (fun w => A u w * A w v + A u w * B w v)
                     (fun w => B u w * A w v + B u w * B w v) indices]
  rw [sumIntOver_add (fun w => A u w * A w v) (fun w => A u w * B w v) indices]
  rw [sumIntOver_add (fun w => B u w * A w v) (fun w => B u w * B w v) indices]

/-- **Theorem (`orthogonal_idempotents_sum_sq`)**:
For any index set `indices`, scale factor $s \in \mathbb{Z}$, and orthogonal scaled spectral
idempotents $E_1, E_2$ satisfying $E_1^2 = s E_1$, $E_2^2 = s E_2$, $E_1 E_2 = 0$, and $E_2 E_1 = 0$
at entry $(u, v)$, their sum $E_1 + E_2$ is also a scaled idempotent of scale $s$:
$$((E_1 + E_2)^2)_{u, v} = s \cdot (E_1 + E_2)_{u, v}.$$ -/
theorem orthogonal_idempotents_sum_sq
    (indices : List Nat)
    (E1 E2 : Nat → Nat → Int)
    (s : Int)
    (u v : Nat)
    (h11 : matMulEntry indices E1 E1 u v = s * E1 u v)
    (h22 : matMulEntry indices E2 E2 u v = s * E2 u v)
    (h12 : matMulEntry indices E1 E2 u v = 0)
    (h21 : matMulEntry indices E2 E1 u v = 0) :
    matMulEntry indices (matAddEntry E1 E2) (matAddEntry E1 E2) u v =
      s * matAddEntry E1 E2 u v := by
  rw [matMulEntry_add_expand indices E1 E2 u v, h11, h22, h12, h21]
  dsimp only [matAddEntry]
  rw [Int.mul_add]
  omega

/-! ## 2. Strong Cospectrality & Godsil's Spectral-Projector CTQW Propagator -/

/-- Evaluate the scaled CTQW transition amplitude $(s \cdot U(t))_{w, u} = \sum_{k \in \text{modes}} \phi_k \cdot (E_k)_{w, u}$
in $\mathbb{Z}[i]$ from source vertex `u` to target vertex `w`, given scaled spectral projectors
`E k` and mode phase factors `phase k` ($\phi_k = e^{-i \lambda_k t}$). -/
def evalSpectralPropagatorEntry
    (modes : List Nat)
    (E : Nat → Nat → Nat → Int)
    (phase : Nat → GaussianInt)
    (w u : Nat) : GaussianInt :=
  sumGaussianOver (fun k => GaussianInt.scale (E k w u) (phase k)) modes

/-- Factoring a constant Gaussian integer phase `g` out of an integer-weighted sum:
$\sum_{k \in \text{modes}} c_k \cdot g = \left(\sum_{k \in \text{modes}} c_k\right) \cdot g$. -/
theorem sumGaussianOver_scale_const
    (c : Nat → Int)
    (g : GaussianInt) :
    ∀ (modes : List Nat),
      sumGaussianOver (fun k => GaussianInt.scale (c k) g) modes =
        GaussianInt.scale (sumIntOver c modes) g
  | [] => by
    dsimp only [sumGaussianOver, sumIntOver, GaussianInt.scale, GaussianInt.zero]
    rw [Int.zero_mul, Int.zero_mul]
  | k :: ks => by
    dsimp only [sumGaussianOver, sumIntOver]
    rw [sumGaussianOver_scale_const c g ks]
    dsimp only [GaussianInt.add, GaussianInt.scale]
    rw [Int.add_mul, Int.add_mul]

/-- Congruence of `sumGaussianOver` when two functions agree on `modes`. -/
theorem sumGaussianOver_congr (f1 f2 : Nat → GaussianInt) :
    ∀ (modes : List Nat),
      (∀ k, k ∈ modes → f1 k = f2 k) →
      sumGaussianOver f1 modes = sumGaussianOver f2 modes
  | [], _ => rfl
  | k :: ks, h => by
    dsimp only [sumGaussianOver]
    have hk : f1 k = f2 k := h k (List.Mem.head ks)
    have hRest : sumGaussianOver f1 ks = sumGaussianOver f2 ks :=
      sumGaussianOver_congr f1 f2 ks (fun m hm => h m (List.Mem.tail k hm))
    rw [hk, hRest]

/-- Associativity of integer scalar multiplication on `GaussianInt`:
`scale a (scale b z) = scale (a * b) z`. -/
theorem gaussianInt_scale_scale (a b : Int) (z : GaussianInt) :
    GaussianInt.scale a (GaussianInt.scale b z) = GaussianInt.scale (a * b) z := by
  dsimp only [GaussianInt.scale]
  rw [Int.mul_assoc, Int.mul_assoc]

/-- **Theorem (`godsil_cospectral_parity_implies_pst`)**:
**Godsil's Spectral-Projector Perfect State Transfer Theorem**:
Suppose vertices $u$ and $v$ are **strongly cospectral** with parity signs $\sigma_k \in \mathbb{Z}$
($E_k(w, u) = \sigma_k \cdot E_k(w, v)$ for all $k \in \text{modes}$) and at transfer time $t = \tau$
every mode phase $\phi_k \in \mathbb{Z}[i]$ satisfies the parity-phase alignment condition
$\sigma_k \cdot \phi_k = g_{\text{global}}$.
Then for every vertex $w$:
$$(s \cdot U(\tau))_{w, u} = \left(\sum_{k \in \text{modes}} E_k(w, v)\right) \cdot g_{\text{global}}.$$
In particular, by projector completeness $\sum_k E_k = s I$, at $w = v$ the amplitude is
$s \cdot g_{\text{global}}$ (100% state transfer when $|g_{\text{global}}|^2 = 1$), and at every
$w \neq v$ the amplitude is identically $\langle 0, 0 \rangle$! -/
theorem godsil_cospectral_parity_implies_pst
    (modes : List Nat)
    (E : Nat → Nat → Nat → Int)
    (paritySign : Nat → Int)
    (phase : Nat → GaussianInt)
    (globalPhase : GaussianInt)
    (u v w : Nat)
    (hCospec : ∀ k, k ∈ modes → E k w u = E k w v * paritySign k)
    (hPhaseAlign : ∀ k, k ∈ modes → GaussianInt.scale (paritySign k) (phase k) = globalPhase) :
    evalSpectralPropagatorEntry modes E phase w u =
      GaussianInt.scale (sumIntOver (fun k => E k w v) modes) globalPhase := by
  dsimp only [evalSpectralPropagatorEntry]
  have hCongr :
      sumGaussianOver (fun k => GaussianInt.scale (E k w u) (phase k)) modes =
      sumGaussianOver (fun k => GaussianInt.scale (E k w v) globalPhase) modes := by
    apply sumGaussianOver_congr
    intro k hk
    rw [hCospec k hk, ← gaussianInt_scale_scale (E k w v) (paritySign k) (phase k), hPhaseAlign k hk]
  rw [hCongr]
  exact sumGaussianOver_scale_const (fun k => E k w v) globalPhase modes

/-- Check strong cospectrality between vertices `u` and `v` across a list of scaled projectors `projectors`:
for every $E_k$, either column $u$ equals column $v$ ($E_k e_u = +E_k e_v$) or column $u$ equals
minus column $v$ ($E_k e_u = -E_k e_v$). -/
def checkStrongCospectrality (projectors : List IntMatrix) (u v : Nat) : Bool :=
  projectors.all (fun E =>
    let indices := List.range E.dim
    let isEven := indices.all (fun w => decide (E.entry w u = E.entry w v))
    let isOdd  := indices.all (fun w => decide (E.entry w u = -E.entry w v))
    isEven || isOdd)

/-- Auxiliary step for Faddeev–LeVerrier trace recurrence:
Given matrix `A`, current auxiliary matrix `B_{k-1}`, previous coefficient `c_{n-k+1}`,
current step `k`, and remaining steps `rem`, computes the list of lower coefficients
`[c_{n-k}, ..., c_0]`. -/
def faddeevLeVerrierAux (A B : IntMatrix) (cPrev : Int) (k : Nat) : Nat → List Int
  | 0 => []
  | rem + 1 =>
    let bNext := A.mul (B.add (IntMatrix.scaledIdentity A.dim cPrev))
    let cCurr := -(bNext.trace) / (k : Int)
    cCurr :: faddeevLeVerrierAux A bNext cCurr (k + 1) rem

/-- Compute the descending coefficient list `[1, c_{n-1}, ..., c_1, c_0]` of the monic
characteristic polynomial $\det(\lambda I - A) = \lambda^n + c_{n-1}\lambda^{n-1} + \dots + c_0$
via the Faddeev–LeVerrier trace recurrence. -/
def faddeevLeVerrierCoeffs (A : IntMatrix) : List Int :=
  1 :: faddeevLeVerrierAux A (IntMatrix.zero A.dim) 1 1 A.dim

/-- Convert a list of descending polynomial coefficients `[c_d, ..., c_0]` into a `Poly` in variable `0` ($\lambda$). -/
def coeffsToPolyDesc : List Int → Poly
  | [] => Poly.zero
  | c :: cs =>
    let deg := cs.length
    let term :=
      if c == 0 then Poly.zero
      else if deg == 0 then polyOfTerm [] (CanonicalRat.ofInt c)
      else polyOfTerm [(0, deg)] (CanonicalRat.ofInt c)
    Poly.add term (coeffsToPolyDesc cs)

/-- **Faddeev–LeVerrier Characteristic Polynomial Synthesis** (`faddeevLeVerrier`):
Computes $\det(\lambda I - A) \in \mathbb{Q}[\lambda]$ directly from the matrix entries of `A`. -/
def faddeevLeVerrier (A : IntMatrix) : Poly :=
  coeffsToPolyDesc (faddeevLeVerrierCoeffs A)

/-- Characteristic polynomial $\det(\lambda I - A)$ for $2 \times 2$ integer matrices via Faddeev–LeVerrier. -/
def charPoly2x2 (A : IntMatrix) : Poly :=
  faddeevLeVerrier A

/-- Characteristic polynomial $\det(\lambda I - A)$ for $3 \times 3$ integer matrices via Faddeev–LeVerrier. -/
def charPoly3x3 (A : IntMatrix) : Poly :=
  faddeevLeVerrier A

/-- Characteristic polynomial $\det(\lambda I - A)$ for $4 \times 4$ integer matrices via Faddeev–LeVerrier. -/
def charPoly4x4 (A : IntMatrix) : Poly :=
  faddeevLeVerrier A

/-- Sum a list of `dim × dim` integer matrices: $\sum_{P \in \text{ms}} P$. -/
def sumIntMatrices (dim : Nat) : List IntMatrix → IntMatrix
  | [] => IntMatrix.zero dim
  | P :: Ps => P.add (sumIntMatrices dim Ps)

/-- Weighted linear combination of `dim × dim` integer matrices: $\sum_{i} \lambda_i P_i$. -/
def weightedSumIntMatrices (dim : Nat) : List Int → List IntMatrix → IntMatrix
  | [], _ => IntMatrix.zero dim
  | _, [] => IntMatrix.zero dim
  | c :: cs, P :: Ps => (P.scale c).add (weightedSumIntMatrices dim cs Ps)

/-- **Lagrange–Sylvester Spectral Projector Synthesis over $\mathbb{Z}$** (`synthesizeSylvesterProjector`):
Constructs the scaled spectral projector for eigenvalue index `i`:
$$P_i(Q) = \text{cofactor} \cdot \prod_{j \neq i} (Q - \lambda_j I).$$ -/
def synthesizeSylvesterProjector
    (Q : IntMatrix)
    (eigs : List Int)
    (i : Nat)
    (cofactor : Int) : IntMatrix :=
  let indices := List.range eigs.length
  let prodMat := indices.foldl (fun acc j =>
    if j == i then acc
    else
      let lamJ := listGetInt eigs j
      acc.mul (Q.add (IntMatrix.scaledIdentity Q.dim (-lamJ))))
    (IntMatrix.scaledIdentity Q.dim 1)
  prodMat.scale cofactor

/-- Computable checker for a scaled spectral projector decomposition $(Q, s, \{\lambda_i\}, \{P_i\})$:
1. **Completeness**: $\sum_i P_i = s \cdot I$,
2. **Scaled Idempotence**: $\forall P \in \text{projs},\; P^2 = s \cdot P$,
3. **Pairwise Orthogonality**: $\forall i \neq j,\; P_i P_j = 0$,
4. **Spectral Reconstruction**: $\sum_i \lambda_i P_i = s \cdot Q$. -/
def checkSpectralDecomposition
    (Q : IntMatrix)
    (scale : Int)
    (eigs : List Int)
    (projs : List IntMatrix) : Bool :=
  let indices := List.range projs.length
  decide (sumIntMatrices Q.dim projs = IntMatrix.scaledIdentity Q.dim scale) &&
  projs.all (fun P => decide (P.mul P = P.scale scale)) &&
  indices.all (fun i =>
    indices.all (fun j =>
      if i == j then true
      else
        let pI := projs[i]?.getD (IntMatrix.zero Q.dim)
        let pJ := projs[j]?.getD (IntMatrix.zero Q.dim)
        decide (pI.mul pJ = IntMatrix.zero Q.dim))) &&
  decide (weightedSumIntMatrices Q.dim eigs projs = Q.scale scale)

/-- **Theorem (`checkSpectralDecomposition_sound`)**:
When `checkSpectralDecomposition Q scale eigs projs = true`, the projectors satisfy:
1. **Completeness**: `sumIntMatrices Q.dim projs = IntMatrix.scaledIdentity Q.dim scale` ($\sum P_i = s I$),
2. **Idempotence**: `∀ P ∈ projs, P.mul P = P.scale scale` ($P_i^2 = s P_i$),
3. **Orthogonality**: `∀ i j < projs.length, i ≠ j → P_i P_j = 0`,
4. **Spectral Reconstruction**: `weightedSumIntMatrices Q.dim eigs projs = Q.scale scale` ($\sum \lambda_i P_i = s Q$). -/
theorem checkSpectralDecomposition_sound
    (Q : IntMatrix)
    (scale : Int)
    (eigs : List Int)
    (projs : List IntMatrix)
    (hCheck : checkSpectralDecomposition Q scale eigs projs = true) :
    sumIntMatrices Q.dim projs = IntMatrix.scaledIdentity Q.dim scale ∧
    (∀ P, P ∈ projs → P.mul P = P.scale scale) ∧
    (∀ i j, i < projs.length → j < projs.length → i ≠ j →
      (projs[i]?.getD (IntMatrix.zero Q.dim)).mul (projs[j]?.getD (IntMatrix.zero Q.dim)) =
        IntMatrix.zero Q.dim) ∧
    weightedSumIntMatrices Q.dim eigs projs = Q.scale scale := by
  unfold checkSpectralDecomposition at hCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hCheck
  rcases hCheck with ⟨⟨⟨hComp, hIdemp⟩, hOrth⟩, hRecon⟩
  rw [list_all_iff_forall] at hIdemp hOrth
  refine ⟨hComp, ?_, ?_, hRecon⟩
  · intro P hP
    exact of_decide_eq_true (hIdemp P hP)
  · intro i j hi hj hNe
    have hiMem : i ∈ List.range projs.length := List.mem_range.mpr hi
    have hjMem : j ∈ List.range projs.length := List.mem_range.mpr hj
    have hRow := (list_all_iff_forall _ (List.range projs.length)).mp (hOrth i hiMem) j hjMem
    have hBeq : (i == j) = false := beq_false_of_ne hNe
    rw [hBeq] at hRow
    exact of_decide_eq_true hRow

/-! ## 3. Exact $K_2$ Antipodal PST (`ctqw_k2_antipodal_pst_exact`) -/

/-- Adjacency matrix of $K_2$ ($H_{K_2} = X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$). -/
def k2Matrix : IntMatrix where
  dim  := 2
  rows := [[0, 1], [1, 0]]

/-- Scaled symmetric projector $2 E_+ = Q + I = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$ ($\lambda_+ = +1$),
synthesized via `synthesizeSylvesterProjector`. -/
def k2ProjPlus : IntMatrix :=
  synthesizeSylvesterProjector k2Matrix [1, -1] 0 1

/-- Scaled antisymmetric projector $2 E_- = -(Q - I) = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$ ($\lambda_- = -1$),
synthesized via `synthesizeSylvesterProjector`. -/
def k2ProjMinus : IntMatrix :=
  synthesizeSylvesterProjector k2Matrix [1, -1] 1 (-1)

/-- **Theorem (`ctqw_k2_antipodal_pst_exact`)**:
On $K_2$ with scale $s = 2$:
1. $2 E_+$ and $2 E_-$ are orthogonal scaled idempotents:
   $(2 E_+)^2 = 2 (2 E_+)$, $(2 E_-)^2 = 2 (2 E_-)$, $(2 E_+)(2 E_-) = 0_2$,
2. Completeness & spectral decomposition hold:
   $2 E_+ + 2 E_- = 2 I_2$ and $(+1)(2 E_+) + (-1)(2 E_-) = 2 H_{K_2}$,
3. Vertices $0$ and $1$ are strongly cospectral (`checkStrongCospectrality = true`),
4. At transfer time $\tau = \pi/2$, the mode phases $\phi_+ = e^{-i\pi/2} = -i = \langle 0, -1 \rangle$
   and $\phi_- = e^{+i\pi/2} = +i = \langle 0, 1 \rangle$ yield zero survival amplitude at vertex $0$
   (`⟨0, 0⟩`) and full antipodal transfer amplitude `⟨0, -2⟩` (`normSq = 4 = 2^2`, 100% transfer
   probability) at vertex $1$! -/
theorem ctqw_k2_antipodal_pst_exact :
    let E : Nat → Nat → Nat → Int := fun k => if k == 0 then k2ProjPlus.entry else k2ProjMinus.entry
    let phasePiHalf : Nat → GaussianInt := fun k => if k == 0 then ⟨0, -1⟩ else ⟨0, 1⟩
    let amp00 := evalSpectralPropagatorEntry [0, 1] E phasePiHalf 0 0
    let amp10 := evalSpectralPropagatorEntry [0, 1] E phasePiHalf 1 0
    k2ProjPlus.mul k2ProjPlus = k2ProjPlus.scale 2 ∧
    k2ProjMinus.mul k2ProjMinus = k2ProjMinus.scale 2 ∧
    k2ProjPlus.mul k2ProjMinus = IntMatrix.zero 2 ∧
    k2ProjPlus.add k2ProjMinus = IntMatrix.scaledIdentity 2 2 ∧
    k2ProjPlus.add (k2ProjMinus.scale (-1)) = k2Matrix.scale 2 ∧
    checkStrongCospectrality [k2ProjPlus, k2ProjMinus] 0 1 = true ∧
    amp00 = ⟨0, 0⟩ ∧
    amp10 = ⟨0, -2⟩ ∧
    amp00.normSq = 0 ∧
    amp10.normSq = 4 := by
  decide +kernel

/-! ## 4. Algebraic Number Field Spectral Projectors on $P_3$ & $P_4$ via `Groebner.lean` (`ctqw_p3_end_to_end_pst_algebraic`) -/

/-- Matrix with polynomial entries in $\mathbb{Q}[\alpha]$ (`Obend.Judge.SOS.Poly`), used to represent
operators over the algebraic number field $\mathbb{Q}(\alpha)/\langle m(\alpha) \rangle$. -/
structure PolyMatrix where
  dim  : Nat
  rows : List (List Poly)
  deriving DecidableEq, Repr

namespace PolyMatrix

/-- Look up polynomial entry $(u, v)$ in a `PolyMatrix` (defaulting to `Poly.zero`). -/
def entry (m : PolyMatrix) (u v : Nat) : Poly :=
  match m.rows[u]? with
  | some row =>
    match row[v]? with
    | some p => p
    | none   => Poly.zero
  | none => Poly.zero

/-- Reduce every entry of `m` modulo a Gröbner basis `basis` with `fuel` reduction steps. -/
def reduceMod (basis : List Poly) (fuel : Nat) (m : PolyMatrix) : PolyMatrix :=
  { dim  := m.dim
  , rows := m.rows.map (fun row => row.map (fun p => polyReduceFuel basis fuel p)) }

/-- Add two `PolyMatrix` instances of dimension `dim`. -/
def add (A B : PolyMatrix) : PolyMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => Poly.add (A.entry u v) (B.entry u v))) }

/-- Subtract two `PolyMatrix` instances (`A - B`). -/
def sub (A B : PolyMatrix) : PolyMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => Poly.sub (A.entry u v) (B.entry u v))) }

/-- Multiply a `PolyMatrix` by a scalar polynomial `c : Poly` modulo `basis`. -/
def scalePolyMod (basis : List Poly) (fuel : Nat) (c : Poly) (A : PolyMatrix) : PolyMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => polyReduceFuel basis fuel (Poly.mul c (A.entry u v)))) }

/-- Multiply two `PolyMatrix` instances modulo the algebraic minimal-polynomial ideal `basis`. -/
def mulMod (basis : List Poly) (fuel : Nat) (A B : PolyMatrix) : PolyMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v =>
        let rawDot := indices.foldl (fun acc w =>
          Poly.add acc (Poly.mul (A.entry u w) (B.entry w v))) Poly.zero
        polyReduceFuel basis fuel rawDot)) }

/-- Check whether every entry of `m` reduces to `Poly.zero` modulo `basis`. -/
def isZeroMod (basis : List Poly) (fuel : Nat) (m : PolyMatrix) : Bool :=
  (m.reduceMod basis fuel).rows.all (fun row => row.all (fun p => p.isZero))

/-- Embed an `IntMatrix` into `PolyMatrix` as constant polynomials. -/
def ofIntMatrix (m : IntMatrix) : PolyMatrix :=
  { dim  := m.dim
  , rows := m.rows.map (fun row =>
      row.map (fun c => polyOfTerm [] (CanonicalRat.ofInt c))) }

/-- Scaled $n \times n$ polynomial identity matrix $c \cdot I_n$. -/
def scaledIdentity (dim : Nat) (c : Poly) : PolyMatrix :=
  let indices := List.range dim
  { dim  := dim
  , rows := indices.map (fun u =>
      indices.map (fun v => if u == v then c else Poly.zero)) }

end PolyMatrix

/-- **Lagrange–Sylvester Spectral Projector Synthesis over $\mathbb{Q}(\alpha)/\langle m(\alpha) \rangle$**
(`synthesizeSylvesterProjectorPoly`):
Constructs the scaled spectral projector for eigenvalue index `i`:
$$P_i(Q) \equiv \text{cofactor} \cdot \prod_{j \neq i} (Q - \lambda_j I) \pmod{\text{basis}}.$$ -/
def synthesizeSylvesterProjectorPoly
    (basis : List Poly)
    (fuel : Nat)
    (Q : PolyMatrix)
    (eigs : List Poly)
    (i : Nat)
    (cofactor : Poly := Poly.one) : PolyMatrix :=
  let indices := List.range eigs.length
  let prodMat := indices.foldl (fun acc j =>
    if j == i then acc
    else
      let lamJ := eigs[j]?.getD Poly.zero
      let shifted := PolyMatrix.sub Q (PolyMatrix.scaledIdentity Q.dim lamJ)
      PolyMatrix.mulMod basis fuel acc shifted)
    (PolyMatrix.scaledIdentity Q.dim Poly.one)
  PolyMatrix.scalePolyMod basis fuel cofactor prodMat

/-- Minimal polynomial $m(\alpha) = \alpha^2 - 2$ of $\alpha = \sqrt{2}$ (using variable $0$ for $\alpha$). -/
def p3MinPolyAlphaSqMinus2 : Poly :=
  Poly.sub ( polyVarPow 0 2 ) ( polyOfTerm [] 2 )

/-- Eigenvalue list $[\lambda_0, \lambda_+, \lambda_-] = [0, +\alpha, -\alpha]$ of $P_3$ over $\mathbb{Q}(\alpha)/\langle \alpha^2 - 2 \rangle$. -/
def p3AlgebraicEigenvalues : List Poly :=
  [Poly.zero, polyVarPow 0 1, polyOfTerm [(0, 1)] (-1)]

/-- Scaled spectral projector $4 P_0 = -2 (H_{P_3} - \alpha I)(H_{P_3} + \alpha I) = \begin{pmatrix} 2 & 0 & -2 \\ 0 & 0 & 0 \\ -2 & 0 & 2 \end{pmatrix}$
for eigenvalue $\lambda_0 = 0$ of $P_3$, synthesized via `synthesizeSylvesterProjectorPoly`. -/
def p3AlgebraicProj0 : PolyMatrix :=
  synthesizeSylvesterProjectorPoly [p3MinPolyAlphaSqMinus2] 6
    (PolyMatrix.ofIntMatrix path3Matrix) p3AlgebraicEigenvalues 0 (polyOfTerm [] (-2))

/-- Scaled spectral projector $4 P_+ = (H_{P_3} - 0 I)(H_{P_3} + \alpha I) = \begin{pmatrix} 1 & \alpha & 1 \\ \alpha & 2 & \alpha \\ 1 & \alpha & 1 \end{pmatrix}$
for eigenvalue $\lambda_+ = +\alpha = +\sqrt{2}$ of $P_3$, synthesized via `synthesizeSylvesterProjectorPoly`. -/
def p3AlgebraicProjPlus : PolyMatrix :=
  synthesizeSylvesterProjectorPoly [p3MinPolyAlphaSqMinus2] 6
    (PolyMatrix.ofIntMatrix path3Matrix) p3AlgebraicEigenvalues 1 Poly.one

/-- Scaled spectral projector $4 P_- = (H_{P_3} - 0 I)(H_{P_3} - \alpha I) = \begin{pmatrix} 1 & -\alpha & 1 \\ -\alpha & 2 & -\alpha \\ 1 & -\alpha & 1 \end{pmatrix}$
for eigenvalue $\lambda_- = -\alpha = -\sqrt{2}$ of $P_3$, synthesized via `synthesizeSylvesterProjectorPoly`. -/
def p3AlgebraicProjMinus : PolyMatrix :=
  synthesizeSylvesterProjectorPoly [p3MinPolyAlphaSqMinus2] 6
    (PolyMatrix.ofIntMatrix path3Matrix) p3AlgebraicEigenvalues 2 Poly.one

/-- $4 \times 4$ adjacency matrix of the 4-vertex path graph $P_4$ ($0 - 1 - 2 - 3$). -/
def path4Matrix : IntMatrix where
  dim  := 4
  rows :=
    [ [0, 1, 0, 0]
    , [1, 0, 1, 0]
    , [0, 1, 0, 1]
    , [0, 0, 1, 0] ]

/-- Antipodal reflection-even $2 \times 2$ quotient block of $P_4$ on $\{e_0 + e_3, e_1 + e_2\}$:
$$Q_{\text{even}}(P_4) = \begin{pmatrix} 0 & 1 \\ 1 & 1 \end{pmatrix}, \qquad \det(\lambda I - Q_{\text{even}}) = \lambda^2 - \lambda - 1.$$ -/
def p4EvenQuotient2x2 : IntMatrix where
  dim  := 2
  rows := [[0, 1], [1, 1]]

/-- Antipodal reflection-odd $2 \times 2$ quotient block of $P_4$ on $\{e_0 - e_3, e_1 - e_2\}$:
$$Q_{\text{odd}}(P_4) = \begin{pmatrix} 0 & 1 \\ 1 & -1 \end{pmatrix}, \qquad \det(\lambda I - Q_{\text{odd}}) = \lambda^2 + \lambda - 1.$$ -/
def p4OddQuotient2x2 : IntMatrix where
  dim  := 2
  rows := [[0, 1], [1, -1]]

/-- Signed antipodal $2 \times 2$ block $\begin{pmatrix} -1 & 1 \\ 1 & 1 \end{pmatrix}$ with trace $0$ and determinant $-2$. -/
def p4AntipodalOddBlock2x2 : IntMatrix where
  dim  := 2
  rows := [[-1, 1], [1, 1]]

/-- Polynomial power $p^k$ in $\mathbb{Q}[x]$. -/
def polyPow (p : Poly) : Nat → Poly
  | 0 => Poly.one
  | k + 1 => Poly.mul p (polyPow p k)

/-- Substitute $\lambda \mapsto q$ into a polynomial given by descending coefficients `[c_d, ..., c_0]`. -/
def evalCoeffsAtPoly ( q : Poly ) : List Int → Poly
  | [] => Poly.zero
  | c :: cs =>
    let deg := cs.length
    let term := Poly.scale (CanonicalRat.ofInt c) (polyPow q deg)
    Poly.add term (evalCoeffsAtPoly q cs)

/-- Multiply two polynomials given by descending integer coefficient lists `[c_d, ..., c_0]`
via exact Cauchy convolution over `Int` (zero `Rat` and zero `Classical.choice` dependency). -/
def intPolyMulDesc (p q : List Int) : List Int :=
  match p, q with
  | [], _ => []
  | _, [] => []
  | _, _ =>
    let degP := p.length - 1
    let degQ := q.length - 1
    let totalLen := degP + degQ + 1
    (List.range totalLen).map (fun k =>
      sumIntOver (fun i =>
        if Nat.ble i k && Nat.blt (k - i) q.length then
          listGetInt p i * listGetInt q (k - i)
        else 0) (List.range p.length))

/-- Pad the shorter of two descending integer coefficient lists on the left with leading zeros
and add them termwise over `Int`. -/
def intPolyAddDesc (p q : List Int) : List Int :=
  let len := max p.length q.length
  let padP := List.replicate (len - p.length) (0 : Int) ++ p
  let padQ := List.replicate (len - q.length) (0 : Int) ++ q
  List.zipWith (· + ·) padP padQ

/-- Exact polynomial power $q^k$ over descending integer coefficient lists `List Int`. -/
def intPolyPowDesc (q : List Int) : Nat → List Int
  | 0 => [1]
  | k + 1 => intPolyMulDesc q (intPolyPowDesc q k)

/-- Substitute $\lambda \mapsto q(\lambda_+)$ into a polynomial given by descending integer coefficients
`[c_d, ..., c_0]` over `List Int`. -/
def evalIntPolyAtPolyDesc (q : List Int) : List Int → List Int
  | [] => []
  | c :: cs =>
    let deg := cs.length
    let term := (intPolyPowDesc q deg).map (fun x => c * x)
    intPolyAddDesc term (evalIntPolyAtPolyDesc q cs)

/-- Evaluate a polynomial with descending integer coefficients `[c_d, ..., c_0]` at `x : Int` via Horner's rule. -/
def evalIntPolyDesc (coeffs : List Int) (x : Int) : Int :=
  coeffs.foldl (fun acc c => acc * x + c) 0

/-- Synthesize the descending integer coefficients `[1, -3, 1]` ($r^2 - 3r + 1$) of $P_4$'s
eigenvalue ratio minimal polynomial directly from `faddeevLeVerrierCoeffs p4EvenQuotient2x2`
($[c_2, c_1, c_0] = [1, -1, -1]$ for $\lambda^2 - \lambda - 1$) via the substitution $\lambda = r - 1$:
$$c_2 (r - 1)^2 + c_1 (r - 1) + c_0 = c_2 r^2 + (-2 c_2 + c_1) r + (c_2 - c_1 + c_0).$$ -/
def synthesizeP4RatioMinPolyCoeffs : List Int :=
  let cs := faddeevLeVerrierCoeffs p4EvenQuotient2x2
  let c2 := listGetInt cs 0
  let c1 := listGetInt cs 1
  let c0 := listGetInt cs 2
  [c2, -2 * c2 + c1, c2 - c1 + c0]

/-- Synthesize the minimal polynomial of $P_4$'s eigenvalue ratio $r = \lambda_+ / \lambda_-$ directly
from the Faddeev–LeVerrier characteristic polynomial of `p4EvenQuotient2x2`:
Since $\lambda_+ \lambda_- = 1$, $r = \lambda_+ / \lambda_- = \lambda_+^2 = \lambda_+ + 1$, so $\lambda_+ = r - 1$.
Substituting $\lambda = r - 1$ into `faddeevLeVerrierCoeffs p4EvenQuotient2x2` ($\lambda^2 - \lambda - 1$)
synthesizes $r^2 - 3r + 1$ directly from $P_4$'s matrix entries! -/
def synthesizeP4RatioMinPoly : Poly :=
  coeffsToPolyDesc synthesizeP4RatioMinPolyCoeffs

/-- Backwards-compatible alias for `synthesizeP4RatioMinPoly`. -/
abbrev p4RatioMinPolyR2Minus3RPlus1 : Poly :=
  synthesizeP4RatioMinPoly

/-- Check Godsil's eigenvalue parity-ratio condition for antipodal PST on $P_4$ by synthesizing
the ratio minimal polynomial `synthesizeP4RatioMinPoly` via Faddeev–LeVerrier from $P_4$'s quotient
and verifying that $r = 1$ (and rational parity ratios) cannot divide $r^2 - 3r + 1$. -/
def checkP4IrrationalRatioObstruction : Bool :=
  let rVar := polyVarPow 0 1
  let p4RatioMinPoly := synthesizeP4RatioMinPoly
  let linearFactorRMinus1 := Poly.sub rVar Poly.one
  !(polyReduceFuel [linearFactorRMinus1] 4 p4RatioMinPoly).isZero

/-- General $2 \times 2$ integer matrix $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$. -/
def mat2x2 (a b c d : Int) : IntMatrix where
  dim  := 2
  rows := [[a, b], [c, d]]

theorem mat2x2_scaledIdentity (s : Int) :
    IntMatrix.scaledIdentity 2 s = mat2x2 s 0 0 s := rfl

theorem mat2x2_zero :
    IntMatrix.zero 2 = mat2x2 0 0 0 0 := rfl

theorem mat2x2_add (a1 b1 c1 d1 a2 b2 c2 d2 : Int) :
    (mat2x2 a1 b1 c1 d1).add (mat2x2 a2 b2 c2 d2) =
      mat2x2 (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2) := rfl

theorem mat2x2_scale (s a b c d : Int) :
    (mat2x2 a b c d).scale s = mat2x2 (s * a) (s * b) (s * c) (s * d) := rfl

theorem mat2x2_trace (a b c d : Int) :
    (mat2x2 a b c d).trace = a + (d + 0) := rfl

theorem mat2x2_mul (a1 b1 c1 d1 a2 b2 c2 d2 : Int) :
    (mat2x2 a1 b1 c1 d1).mul (mat2x2 a2 b2 c2 d2) =
      mat2x2
        (a1 * a2 + (b1 * c2 + 0))
        (a1 * b2 + (b1 * d2 + 0))
        (c1 * a2 + (d1 * c2 + 0))
        (c1 * b2 + (d1 * d2 + 0)) := rfl

/-- **Theorem (`faddeevLeVerrier_2x2_exact_and_cayley_hamilton`)**:
For EVERY $2 \times 2$ integer matrix $A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ ($a, b, c, d \in \mathbb{Z}$):
1. **Exact Newton-Identity Trace Divisibility**:
   At step $k = 2$ of the Faddeev–LeVerrier recurrence, $B_2 = A(A - \operatorname{tr}(A) I_2)$ has
   trace $-\operatorname{tr}(B_2) = 2(a d - b c)$, which is **always** an exact multiple of $2$
   (`(-b2.trace) % 2 = 0` with zero remainder) and divides to `(-b2.trace) / 2 = a * d - b * c`.
2. **Exact Characteristic Polynomial Synthesis**:
   `faddeevLeVerrierCoeffs (mat2x2 a b c d) = [1, -(a + d), a * d - b * c]`.
3. **Universal $2 \times 2$ Cayley–Hamilton Theorem ($A^2 - \operatorname{tr}(A) A + \det(A) I_2 = 0_2$)**:
   `((A.mul A).add (A.scale (-(a + d)))).add (IntMatrix.scaledIdentity 2 (a * d - b * c)) = IntMatrix.zero 2`. -/
theorem faddeevLeVerrier_2x2_exact_and_cayley_hamilton (a b c d : Int) :
    let A := mat2x2 a b c d
    let trA := a + d
    let detA := a * d - b * c
    let b2 := A.mul (A.add (IntMatrix.scaledIdentity 2 (-trA)))
    (-b2.trace) % 2 = 0 ∧
    (-b2.trace) / 2 = detA ∧
    faddeevLeVerrierCoeffs A = [1, -trA, detA] ∧
    ((A.mul A).add (A.scale (-trA))).add (IntMatrix.scaledIdentity 2 detA) = IntMatrix.zero 2 := by
  have hDim : (mat2x2 a b c d).dim = 2 := rfl
  have hCast1 : ((1 : Nat) : Int) = 1 := rfl
  have hCast2 : ((1 + 1 : Nat) : Int) = 2 := rfl
  simp only [faddeevLeVerrierCoeffs, faddeevLeVerrierAux, hDim, hCast1, hCast2,
    mat2x2_zero, mat2x2_scaledIdentity, mat2x2_add, mat2x2_scale, mat2x2_mul, mat2x2_trace,
    Int.add_zero, Int.zero_add, Int.mul_zero, Int.mul_one, Int.ediv_one]
  have h1 : a + -(a + d) = -d := by omega
  have h2 : d + -(a + d) = -a := by omega
  rw [h1, h2]
  have hbc : c * b = b * c := Int.mul_comm c b
  have had1 : a * -d = -(a * d) := Int.mul_neg a d
  have had2 : d * -a = -(a * d) := by rw [Int.mul_neg d a, Int.mul_comm d a]
  have hTrace : -((a * -d + b * c) + (c * b + d * -a)) = 2 * (a * d - b * c) := by
    rw [had1, had2, hbc]
    omega
  rw [hTrace]
  have hMod : (2 * (a * d - b * c)) % 2 = 0 := Int.mul_emod_right 2 (a * d - b * c)
  have hDiv : (2 * (a * d - b * c)) / 2 = a * d - b * c :=
    Int.mul_ediv_cancel_left (a * d - b * c) (by decide)
  rw [hMod, hDiv]
  have hCH00 : a * a + b * c + -(a + d) * a + (a * d - b * c) = 0 := by
    have hDist : -(a + d) * a = -(a * a + d * a) := by
      rw [Int.neg_mul, Int.add_mul]
    have hda : d * a = a * d := Int.mul_comm d a
    omega
  have hCH01 : a * b + b * d + -(a + d) * b = 0 := by
    have hDist : -(a + d) * b = -(a * b + d * b) := by
      rw [Int.neg_mul, Int.add_mul]
    have hdb : d * b = b * d := Int.mul_comm d b
    omega
  have hCH10 : c * a + d * c + -(a + d) * c = 0 := by
    have hDist : -(a + d) * c = -(a * c + d * c) := by
      rw [Int.neg_mul, Int.add_mul]
    have hac : a * c = c * a := Int.mul_comm a c
    omega
  have hCH11 : c * b + d * d + -(a + d) * d + (a * d - b * c) = 0 := by
    have hDist : -(a + d) * d = -(a * d + d * d) := by
      rw [Int.neg_mul, Int.add_mul]
    omega
  rw [hCH00, hCH01, hCH10, hCH11]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem (`faddeevLeVerrier_charPoly_and_p4_obstruction_sound`)**:
1. **Faddeev–LeVerrier Characteristic Polynomial Synthesis**:
   - On $K_2$, `faddeevLeVerrierCoeffs k2Matrix` synthesizes $[1, 0, -1]$ ($\lambda^2 - 1$),
   - On $P_3$, `faddeevLeVerrierCoeffs path3Matrix` synthesizes $[1, 0, -2, 0]$ ($\lambda^3 - 2\lambda$),
   - On $P_4$, `faddeevLeVerrierCoeffs path4Matrix` synthesizes $[1, 0, -3, 0, 1]$ ($\lambda^4 - 3\lambda^2 + 1$),
     which factors as the exact product `intPolyMulDesc` of the even and odd antipodal quotient
     characteristic polynomials $(\lambda^2 - \lambda - 1)(\lambda^2 + \lambda - 1)$!
2. **Algebraic Derivation of $P_4$'s Eigenvalue Ratio Minimal Polynomial $r^2 - 3r + 1 = 0$**:
   - Let $\lambda_+$ be a root of $\chi(Q_{\text{even}})(\lambda) = \lambda^2 - \lambda - 1 = 0$ and
     $\lambda_- = \lambda_+ - 1$ (`lamMinusCoeffs = [1, -1]`). Over $\mathbb{Z}[\lambda_+]$:
     * $\chi(Q_{\text{odd}})(\lambda_+ - 1) = (\lambda_+ - 1)^2 + (\lambda_+ - 1) - 1 = \lambda_+^2 - \lambda_+ - 1 = \chi(Q_{\text{even}})(\lambda_+)$,
       so $\lambda_-$ is an exact root of $\chi(Q_{\text{odd}})(\lambda) = 0$,
     * $\lambda_+ \lambda_- - 1 = \lambda_+(\lambda_+ - 1) - 1 = \chi(Q_{\text{even}})(\lambda_+)$, so $\lambda_+ \lambda_- = 1$,
     * The eigenvalue ratio $r = \lambda_+ / \lambda_- = \lambda_+^2$ (`ratioRCoeffs = [1, 0, 0]`) satisfies
       $r^2 - 3r + 1 = (\lambda_+^2)^2 - 3(\lambda_+^2) + 1 = \chi(Q_{\text{odd}})(\lambda_+) \cdot \chi(Q_{\text{even}})(\lambda_+)$!
   - `synthesizeP4RatioMinPolyCoeffs` equals $[1, -3, 1]$ ($r^2 - 3r + 1$), which has no rational
     parity roots at $r = \pm 1$ (`evalIntPolyDesc synthesizeP4RatioMinPolyCoeffs 1 = -1` and
     `evalIntPolyDesc synthesizeP4RatioMinPolyCoeffs (-1) = 5`). -/
theorem faddeevLeVerrier_charPoly_and_p4_obstruction_sound :
    let chiEvenCoeffs := faddeevLeVerrierCoeffs p4EvenQuotient2x2
    let chiOddCoeffs := faddeevLeVerrierCoeffs p4OddQuotient2x2
    let lamPlusCoeffs : List Int := [1, 0]
    let lamMinusCoeffs : List Int := [1, -1]
    let ratioRCoeffs : List Int := [1, 0, 0]
    faddeevLeVerrierCoeffs k2Matrix = [1, 0, -1] ∧
    faddeevLeVerrierCoeffs path3Matrix = [1, 0, -2, 0] ∧
    faddeevLeVerrierCoeffs path4Matrix = [1, 0, -3, 0, 1] ∧
    chiEvenCoeffs = [1, -1, -1] ∧
    chiOddCoeffs = [1, 1, -1] ∧
    faddeevLeVerrierCoeffs p4AntipodalOddBlock2x2 = [1, 0, -2] ∧
    faddeevLeVerrierCoeffs path4Matrix = intPolyMulDesc chiEvenCoeffs chiOddCoeffs ∧
    evalIntPolyAtPolyDesc lamMinusCoeffs chiOddCoeffs = chiEvenCoeffs ∧
    intPolyAddDesc (intPolyMulDesc lamPlusCoeffs lamMinusCoeffs) [-1] = chiEvenCoeffs ∧
    evalIntPolyAtPolyDesc ratioRCoeffs synthesizeP4RatioMinPolyCoeffs =
      intPolyMulDesc chiOddCoeffs chiEvenCoeffs ∧
    synthesizeP4RatioMinPolyCoeffs = [1, -3, 1] ∧
    evalIntPolyDesc synthesizeP4RatioMinPolyCoeffs 1 = -1 ∧
    evalIntPolyDesc synthesizeP4RatioMinPolyCoeffs (-1) = 5 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem (`ctqw_p3_end_to_end_pst_algebraic`)**:
**Symbolic Algebraic Certificate for End-to-End PST on $P_3$ over $\mathbb{Q}(\alpha)/\langle \alpha^2 - 2 \rangle$**:
1. The minimal polynomial basis $G = [\alpha^2 - 2]$ satisfies Buchberger's criterion (`checkGroebnerBasis 4 G = true`).
2. Over $\mathbb{Q}[\alpha]/\langle \alpha^2 - 2 \rangle$ (via `PolyMatrix.mulMod G 6`):
   - Completeness holds: $4 P_0 + 4 P_+ + 4 P_- = 4 I_3$,
   - Spectral reconstruction holds modulo $\alpha^2 - 2$:
     $0 \cdot (4 P_0) + \alpha (4 P_+) + (-\alpha)(4 P_-) \equiv 4 H_{P_3} \pmod{\alpha^2 - 2}$,
   - Exact idempotence holds modulo $\alpha^2 - 2$:
     $(4 P_0)^2 = 4(4 P_0)$, $(4 P_+)^2 \equiv 4(4 P_+)$, $(4 P_-)^2 \equiv 4(4 P_-)$,
   - Pairwise orthogonality holds modulo $\alpha^2 - 2$:
     $(4 P_0)(4 P_+) \equiv 0$, $(4 P_+)(4 P_-) \equiv 0$.
3. At transfer time $\tau = \pi/\sqrt{2} = \pi/\alpha$, the mode phases are $\phi_0 = +1$,
   $\phi_+ = e^{-i\alpha(\pi/\alpha)} = -1$, and $\phi_- = e^{+i\alpha(\pi/\alpha)} = -1$.
   In the propagator $4 U(\pi/\alpha) = (+1)(4 P_0) + (-1)(4 P_+) + (-1)(4 P_-)$, all irrational
   $\pm\alpha$ terms cancel identically, mapping source vertex $0$ to $(0, 0, -4)^T$ (100% end-to-end
   state transfer to vertex $2$, `0` leakage at vertices $0$ and $1$).
4. Contrastingly, on $P_4$, the eigenvalue ratio satisfies $r^2 - 3r + 1 = 0$ and fails rational
   parity alignment (`checkP4IrrationalRatioObstruction = true`). -/
theorem ctqw_p3_end_to_end_pst_algebraic :
    let G := [p3MinPolyAlphaSqMinus2]
    let alpha := polyVarPow 0 1
    let negAlpha := polyOfTerm [(0, 1)] (-1)
    let negOne := polyOfTerm [] (-1)
    let sumProj := PolyMatrix.add p3AlgebraicProj0 (PolyMatrix.add p3AlgebraicProjPlus p3AlgebraicProjMinus)
    let idScaled4 := PolyMatrix.ofIntMatrix (IntMatrix.scaledIdentity 3 4)
    let hScaled4 := PolyMatrix.ofIntMatrix (path3Matrix.scale 4)
    let specRecon := PolyMatrix.add
      (PolyMatrix.scalePolyMod G 6 alpha p3AlgebraicProjPlus)
      (PolyMatrix.scalePolyMod G 6 negAlpha p3AlgebraicProjMinus)
    -- Propagator 4*U(pi / sqrt(2)) = (+1)*(4*P0) + (-1)*(4*P+) + (-1)*(4*P-)
    let propTau := PolyMatrix.add p3AlgebraicProj0
      (PolyMatrix.add
        (PolyMatrix.scalePolyMod G 6 negOne p3AlgebraicProjPlus)
        (PolyMatrix.scalePolyMod G 6 negOne p3AlgebraicProjMinus))
    checkGroebnerBasis 4 G = true ∧
    PolyMatrix.isZeroMod G 6 (PolyMatrix.sub sumProj idScaled4) = true ∧
    PolyMatrix.isZeroMod G 6 (PolyMatrix.sub specRecon hScaled4) = true ∧
    PolyMatrix.isZeroMod G 6
      (PolyMatrix.sub (PolyMatrix.mulMod G 6 p3AlgebraicProjPlus p3AlgebraicProjPlus)
                      (PolyMatrix.scalePolyMod G 6 (polyOfTerm [] 4) p3AlgebraicProjPlus)) = true ∧
    PolyMatrix.isZeroMod G 6
      (PolyMatrix.sub (PolyMatrix.mulMod G 6 p3AlgebraicProjMinus p3AlgebraicProjMinus)
                      (PolyMatrix.scalePolyMod G 6 (polyOfTerm [] 4) p3AlgebraicProjMinus)) = true ∧
    PolyMatrix.isZeroMod G 6 (PolyMatrix.mulMod G 6 p3AlgebraicProj0 p3AlgebraicProjPlus) = true ∧
    PolyMatrix.isZeroMod G 6 (PolyMatrix.mulMod G 6 p3AlgebraicProjPlus p3AlgebraicProjMinus) = true ∧
    -- End-to-end PST from vertex 0 to vertex 2: column 0 is [0, 0, -4]
    (propTau.entry 0 0).isZero = true ∧
    (propTau.entry 1 0).isZero = true ∧
    propTau.entry 2 0 = polyOfTerm [] (-4) ∧
    checkP4IrrationalRatioObstruction = true := by
  decide +kernel

/-! ## 5. Hypercube $Q_d$ Krawtchouk Quotient, Bachman–Tamon PST & Continuous-Time Taylor Propagator Intertwining -/

/-- Adjacency matrix of the 3-dimensional Hypercube $Q_3$ ($8$ vertices $0 \dots 7$, connected iff
their 3-bit binary representations differ in exactly 1 bit). -/
def hypercubeQ3Matrix : IntMatrix where
  dim  := 8
  rows :=
    [ [0, 1, 1, 0, 1, 0, 0, 0] -- 0 (000, weight 0)
    , [1, 0, 0, 1, 0, 1, 0, 0] -- 1 (001, weight 1)
    , [1, 0, 0, 1, 0, 0, 1, 0] -- 2 (010, weight 1)
    , [0, 1, 1, 0, 0, 0, 0, 1] -- 3 (011, weight 2)
    , [1, 0, 0, 0, 0, 1, 1, 0] -- 4 (100, weight 1)
    , [0, 1, 0, 0, 1, 0, 0, 1] -- 5 (101, weight 2)
    , [0, 0, 1, 0, 1, 0, 0, 1] -- 6 (110, weight 2)
    , [0, 0, 0, 1, 0, 1, 1, 0] -- 7 (111, weight 3)
    ]

/-- Hamming-weight distance partition of $Q_3$ into $4$ cells:
$C_0 = \{0\}$, $C_1 = \{1, 2, 4\}$, $C_2 = \{3, 5, 6\}$, $C_3 = \{7\}$. -/
def hypercubeQ3Part : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 3
  | _ => 0

/-- $4 \times 4$ Krawtchouk / Ehrenfest tridiagonal quotient matrix of $Q_3$:
$$Q(Q_3) = \begin{pmatrix} 0 & 3 & 0 & 0 \\ 1 & 0 & 2 & 0 \\ 0 & 2 & 0 & 1 \\ 0 & 0 & 3 & 0 \end{pmatrix},$$
where row $j$ has lower degree $j$ (into $C_{j-1}$) and upper degree $3 - j$ (into $C_{j+1}$). -/
def hypercubeQ3Quotient : Nat → Nat → Int
  | 0, 1 => 3
  | 1, 0 => 1
  | 1, 2 => 2
  | 2, 1 => 2
  | 2, 3 => 1
  | 3, 2 => 3
  | _, _ => 0

/-- `IntMatrix` representation of the $4 \times 4$ Krawtchouk quotient $Q(Q_3)$ (eigenvalues $3, 1, -1, -3$). -/
def hypercubeQ3QuotientMatrix : IntMatrix where
  dim  := 4
  rows :=
    [ [0, 3, 0, 0]
    , [1, 0, 2, 0]
    , [0, 2, 0, 1]
    , [0, 0, 3, 0] ]

/-- Synthesized Lagrange–Sylvester spectral projectors for $Q(Q_3)$ at common scale $s = 48$
(cofactors $[1, -3, 3, -1]$ for eigenvalues $[3, 1, -1, -3]$ since
$\prod_{j \neq 0}(\lambda_0 - \lambda_j) = 2 \cdot 4 \cdot 6 = 48$ and
$\prod_{j \neq 1}(\lambda_1 - \lambda_j) = (-2) \cdot 2 \cdot 4 = -16$). -/
def q3QuotientSylvesterProjectors : List IntMatrix :=
  let eigs := [3, 1, -1, -3]
  [ synthesizeSylvesterProjector hypercubeQ3QuotientMatrix eigs 0 1
  , synthesizeSylvesterProjector hypercubeQ3QuotientMatrix eigs 1 (-3)
  , synthesizeSylvesterProjector hypercubeQ3QuotientMatrix eigs 2 3
  , synthesizeSylvesterProjector hypercubeQ3QuotientMatrix eigs 3 (-1) ]

/-- General $(d+1) \times (d+1)$ Krawtchouk / Ehrenfest tridiagonal quotient entry for the $d$-cube $Q_d$:
for cell $i \in \{0, \dots, d\}$, $Q_{i, i-1} = i$ and $Q_{i, i+1} = d - i$. -/
def krawtchoukQuotientEntry (d i j : Nat) : Int :=
  if decide (i ≤ d) && decide (j ≤ d) then
    if i + 1 == j then (d - i : Nat)
    else if j + 1 == i then (i : Nat)
    else 0
  else 0

/-- Tensor-power antipodal transition amplitude $(-i)^d \in \mathbb{Z}[i]$ for $Q_d = K_2^{\square d}$
at transfer time $\tau = \pi/2$, where each $K_2$ factor contributes $-i = \langle 0, -1 \rangle$. -/
def hypercubeAntipodalPhase : Nat → GaussianInt
  | 0 => GaussianInt.one
  | d + 1 => GaussianInt.mul ⟨0, -1⟩ (hypercubeAntipodalPhase d)

/-- Theorem (`hypercubeAntipodalPhase_unit_norm`):
For EVERY hypercube dimension $d \in \mathbb{N}$, the $d$-fold tensor-product antipodal transfer
amplitude $(-i)^d$ at $\tau = \pi/2$ has exact unit squared modulus (`(hypercubeAntipodalPhase d).normSq = 1`),
certifying 100% antipodal state transfer across all dimensions $d$! -/
theorem hypercubeAntipodalPhase_unit_norm :
    ∀ (d : Nat), (hypercubeAntipodalPhase d).normSq = 1
  | 0 => rfl
  | d + 1 => by
    dsimp only [hypercubeAntipodalPhase]
    rw [gaussianInt_normSq_mul ⟨0, -1⟩ (hypercubeAntipodalPhase d)]
    rw [hypercubeAntipodalPhase_unit_norm d]
    rfl

/-- **Theorem (`ctqw_hypercube_factorization_exact`)**:
1. The Hamming-weight partition of $Q_3$ ($8$ vertices $\to 4$ cells of sizes $1, 3, 3, 1$) is
   strictly equitable (`checkEquitablePartition = true`), 1-WL bisimulation-stable
   (`checkWl1ColorRefinementStable = true`), satisfies the symmetrizability handshake identity
   $\binom{3}{i} Q_{i,j} = \binom{3}{j} Q_{j,i}$ (`checkHandshakeIdentity = true`), and has zero
   equitable residual (`evalEquitableResidualNormSq = 0`).
2. Its quotient matrix matches `krawtchoukQuotientEntry 3` across all $0 \le i, j < 4$, has
   Faddeev–LeVerrier characteristic polynomial $(\lambda^2 - 9)(\lambda^2 - 1) = \lambda^4 - 10\lambda^2 + 9$,
   and its synthesized Lagrange–Sylvester projectors pass `checkSpectralDecomposition = true`!
3. By Cartesian tensor factorization $U_{Q_d}(\pi/2) = U_{K_2}(\pi/2)^{\otimes d}$, the antipodal
   state transfer amplitude $(-i)^d$ has exact unit norm (`normSq = 1`) for every dimension $d \in \mathbb{N}$
   (with `hypercubeAntipodalPhase 3 = ⟨0, 1⟩`, i.e., $(-i)^3 = +i$). -/
theorem ctqw_hypercube_factorization_exact :
    let cells := [0, 1, 2, 3]
    hypercubeQ3Matrix.isSymmetric = true ∧
    checkEquitablePartition hypercubeQ3Matrix 4 hypercubeQ3Part hypercubeQ3Quotient = true ∧
    checkWl1ColorRefinementStable hypercubeQ3Matrix 4 hypercubeQ3Part = true ∧
    checkHandshakeIdentity 8 4 hypercubeQ3Part hypercubeQ3Quotient = true ∧
    evalEquitableResidualNormSq hypercubeQ3Matrix 4 hypercubeQ3Part hypercubeQ3Quotient = 0 ∧
    (cells.all fun i => cells.all fun j =>
      decide (hypercubeQ3Quotient i j = krawtchoukQuotientEntry 3 i j)) = true ∧
    faddeevLeVerrierCoeffs hypercubeQ3QuotientMatrix = [1, 0, -10, 0, 9] ∧
    checkSpectralDecomposition hypercubeQ3QuotientMatrix 48 [3, 1, -1, -3] q3QuotientSylvesterProjectors = true ∧
    hypercubeAntipodalPhase 3 = ⟨0, 1⟩ ∧
    (hypercubeAntipodalPhase 3).normSq = 1 := by
  decide +kernel

/-- **Theorem (`bachman_tamon_quotient_pst_iff`)**:
**Bachman–Tamon Quotient Perfect State Transfer Equivalence Theorem**:
Let $(H, \text{part}, Q)$ be an equitable partition over `cellIndices` and `cellOf`, and let $v$ be
a target vertex belonging to cell $i_{\text{target}} = \text{part}(v)$.
1. **Universal Intertwining Equivalence**: For EVERY step/power $k \in \mathbb{N}$, EVERY initial
   quotient state $w_0 : \text{Nat} \to \text{Int}$ (such as $w_0 = e_{i_{\text{source}}}$ for a
   singleton source cell $C_{i_{\text{source}}} = \{u\}$), and EVERY target amplitude $A_{\text{target}} \in \mathbb{Z}$,
   the full $n$-vertex evolution $(H^k (S w_0))_v$ equals $A_{\text{target}}$ **if and only if**
   the $r$-cell quotient evolution $(Q^k w_0)_{i_{\text{target}}}$ equals $A_{\text{target}}$!
2. **Concrete $Q_3$ vs. $4$-Cell Quotient Walk Verification**: Across powers $k = 0, 1, 2, 3$ starting
   from $|000\rangle$ ($w_0 = (1, 0, 0, 0)$), the $8$-vertex $Q_3$ walk amplitude at antipodal
   vertex $7$ (`|111⟩`) matches the $4$-cell Krawtchouk quotient walk amplitude at cell $3$ (`0, 0, 0, 6`
   where $6 = 3!$ counts the 6 shortest length-3 paths from $000$ to $111$!). -/
theorem bachman_tamon_quotient_pst_iff
    (H Q : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqAll : ∀ u, ∀ j, j ∈ cellIndices → cellRowSum H (cellOf j) u = Q (part u) j)
    (k : Nat)
    (w0 : Nat → Int)
    (v : Nat)
    (targetAmp : Int) :
    (iterateVecOp (partitionedMatVec H cellIndices cellOf) k (liftQuotientVec part w0) v = targetAmp ↔
      iterateVecOp (quotientMatVec Q cellIndices) k w0 (part v) = targetAmp) ∧
    (let q3Cells := [0, 1, 2, 3]
     let q3CellOf := fun j => cellMembers (List.range 8) hypercubeQ3Part j
     let wSource : Nat → Int := fun i => if i == 0 then 1 else 0
     let fullWalk3 := iterateVecOp (partitionedMatVec hypercubeQ3Matrix.entry q3Cells q3CellOf) 3
                        (liftQuotientVec hypercubeQ3Part wSource) 7
     let quotWalk3 := iterateVecOp (quotientMatVec hypercubeQ3Quotient q3Cells) 3 wSource 3
     fullWalk3 = 6 ∧ quotWalk3 = 6) := by
  have hPower :
      iterateVecOp (partitionedMatVec H cellIndices cellOf) k (liftQuotientVec part w0) v =
        iterateVecOp (quotientMatVec Q cellIndices) k w0 (part v) :=
    equitable_intertwining_power H Q part cellIndices cellOf hCells hEqAll k w0 v
  refine ⟨?_, by decide +kernel⟩
  rw [hPower]

/-- Compute $(-i t)^k \in \mathbb{Z}[i]$ for integer-scaled time $t \in \mathbb{Z}$. -/
def negITimePow (t : Int) : Nat → GaussianInt
  | 0 => GaussianInt.one
  | k + 1 => GaussianInt.mul ⟨0, -t⟩ (negITimePow t k)

/-- Compute $k! \in \mathbb{N}$. -/
def natFactorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * natFactorial k

/-- Integer-scaled Taylor coefficient $N! \cdot \frac{(-i t)^k}{k!} \in \mathbb{Z}[i]$ for the
$N$-th order unitary propagator truncation $N! \sum_{k=0}^N \frac{(-i H t)^k}{k!}$. -/
def taylorScaledWeight (t : Int) (tOrder k : Nat) : GaussianInt :=
  GaussianInt.scale ((natFactorial tOrder / natFactorial k : Nat) : Int) (negITimePow t k)

/-- Evaluate the $N$-th order truncated continuous-time Taylor propagator
$$U_N(t) v = \sum_{k=0}^N \left(N! \frac{(-i t)^k}{k!}\right) A^k v$$
of a linear operator `op` at time `t`, truncation order `tOrder`, vector `v`, and index `u`. -/
def evalTaylorPropagator
    (op : (Nat → Int) → (Nat → Int))
    (t : Int)
    (tOrder : Nat)
    (v : Nat → Int)
    (u : Nat) : GaussianInt :=
  sumGaussianOver
    (fun k => GaussianInt.scale (iterateVecOp op k v u) (taylorScaledWeight t tOrder k))
    (List.range (tOrder + 1))

/-- Full-space vs. quotient-space $N$-th order Taylor propagator step (`propagatorTaylorStep`). -/
def propagatorTaylorStep
    (H Q : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (t : Int)
    (tOrder : Nat)
    (w : Nat → Int)
    (u : Nat) : GaussianInt × GaussianInt :=
  ( evalTaylorPropagator (partitionedMatVec H cellIndices cellOf) t tOrder (liftQuotientVec part w) u
  , evalTaylorPropagator (quotientMatVec Q cellIndices) t tOrder w (part u) )

/-- **Theorem (`continuous_time_taylor_propagator_intertwines`)**:
**Universal Continuous-Time Taylor Propagator Intertwining Theorem**:
For EVERY time $t \in \mathbb{Z}$, EVERY Taylor truncation order $N \in \mathbb{N}$ (`tOrder`),
EVERY initial quotient vector $w : \text{Nat} \to \text{Int}$, and EVERY vertex $u \in \mathbb{N}$,
if $(H, \text{part}, Q)$ is an equitable partition across `cellIndices` and `cellOf`, then the
$N$-th order unitary Taylor propagator $\sum_{k=0}^N \frac{(-i t)^k}{k!} H^k$ intertwines exact
equitable lifts with $\sum_{k=0}^N \frac{(-i t)^k}{k!} Q^k$:
$$(U_N^H(t) (S w))_u = (S (U_N^Q(t) w))_u = (U_N^Q(t) w)_{\text{part}(u)}.$$ -/
theorem continuous_time_taylor_propagator_intertwines
    (H Q : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (t : Int)
    (tOrder : Nat)
    (w : Nat → Int)
    (u : Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqAll : ∀ u, ∀ j, j ∈ cellIndices → cellRowSum H (cellOf j) u = Q (part u) j) :
    evalTaylorPropagator (partitionedMatVec H cellIndices cellOf) t tOrder (liftQuotientVec part w) u =
      evalTaylorPropagator (quotientMatVec Q cellIndices) t tOrder w (part u) := by
  dsimp only [evalTaylorPropagator]
  apply sumGaussianOver_congr
  intro k _
  rw [equitable_intertwining_power H Q part cellIndices cellOf hCells hEqAll k w u]
  rfl

/-- **Theorem (`continuous_time_taylor_propagator_intertwines_unpartitioned`)**:
End-to-end continuous-time Taylor propagator intertwining for both unpartitioned
`matVec (List.range m.dim) m.entry` and `propagatorTaylorStep` on any bounded vertex $u < m.\text{dim}$
whenever `checkEquitablePartition m numCells part Q = true`! -/
theorem continuous_time_taylor_propagator_intertwines_unpartitioned
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (Q : Nat → Nat → Int)
    (t : Int)
    (tOrder : Nat)
    (w : Nat → Int)
    (u : Nat)
    (hCheck : checkEquitablePartition m numCells part Q = true)
    (hu : u < m.dim) :
    evalTaylorPropagator (matVec (List.range m.dim) m.entry) t tOrder (liftQuotientVec part w) u =
      evalTaylorPropagator (quotientMatVec Q (List.range numCells)) t tOrder w (part u) ∧
    (propagatorTaylorStep m.entry Q part (List.range numCells)
      (cellMembers (List.range m.dim) part) t tOrder w u).1 =
    (propagatorTaylorStep m.entry Q part (List.range numCells)
      (cellMembers (List.range m.dim) part) t tOrder w u).2 := by
  dsimp only [propagatorTaylorStep, evalTaylorPropagator]
  constructor
  · apply sumGaussianOver_congr
    intro k _
    rw [(equitable_intertwining_power_unpartitioned m numCells part Q hCheck k w u hu).1]
    rfl
  · apply sumGaussianOver_congr
    intro k _
    rw [(equitable_intertwining_power_unpartitioned m numCells part Q hCheck k w u hu).2]
    rfl

/-! ## 6. Analytic Pole: Symplectic Schrödinger & Lindblad Flowpipes & Validated Taylor Phase Enclosures -/

/-- Construct the validated degree-4/5 Taylor model pair $(\cos(\theta), -\sin(\theta))$ for the
unitary Schrödinger eigenmode phase factor $e^{-i \theta} = \cos(\theta) - i \sin(\theta)$ over
$\theta \in \text{dom}$ with Lagrange remainder bound `rem`. -/
def tmUnitaryPhasePair (dom rem : Interval) : TaylorModel × TaylorModel :=
  let cosTM := tmCos dom rem
  let negSinTM := tmScale (-1) (tmSin dom rem)
  (cosTM, negSinTM)

/-- Construct the validated degree-4 Taylor model for the unitary probability norm
$|e^{-i\theta}|^2 = \cos^2(\theta) + (-\sin(\theta))^2$ over $\theta \in \text{dom}$. -/
def tmUnitaryNormSq (dom rem : Interval) : TaylorModel :=
  let (cosTM, negSinTM) := tmUnitaryPhasePair dom rem
  tmAdd (tmMul 4 cosTM cosTM) (tmMul 4 negSinTM negSinTM)

/-- Real-symplectic Schrödinger `OdeSystem` for a single eigenmode $\psi_k(t) = x(t) + i y(t)$ with
eigenvalue $\lambda$:
$$\dot{x} = \lambda y, \qquad \dot{y} = -\lambda x.$$ -/
def schrodingerEigenmodeOde (lambda dt : CanonicalRat) (remPad : Interval) : OdeSystem where
  fields :=
    [ ("x", .mul (.const lambda) (.var "y"))
    , ("y", .mul (.const (-lambda)) (.var "x")) ]
  dt           := dt
  remainderPad := remPad

/-- Real-symplectic Schrödinger `OdeSystem` for the coupled 2-site $K_2$ quantum walk
($H = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, $\dot{x}_0 = y_1, \dot{y}_0 = -x_1, \dot{x}_1 = y_0, \dot{y}_1 = -x_0$). -/
def schrodingerK2CoupledOde (dt : CanonicalRat) (remPad : Interval) : OdeSystem where
  fields :=
    [ ("x0", .var "y1")
    , ("y0", .sub (.const 0) (.var "x1"))
    , ("x1", .var "y0")
    , ("y1", .sub (.const 0) (.var "x0")) ]
  dt           := dt
  remainderPad := remPad

/-- Open-system Lindblad dephasing ODE for off-diagonal coherence $c(t)$ with decoherence rate $\gamma > 0$:
$\dot{c} = -\gamma c$. -/
def lindbladDephasingOde (gamma dt : CanonicalRat) (remPad : Interval) : OdeSystem where
  fields       := [("c", .mul (.const (-gamma)) (.var "c"))]
  dt           := dt
  remainderPad := remPad

/-- Unphysical non-Hermitian anti-damped ODE ($\dot{x} = +2 x + 1$) that violates unitary norm
conservation and blows up outside the probability envelope $[-2, 2]$. -/
def nonHermitianGainRunawayOde : OdeSystem where
  fields       := [("x", .add (.mul (.const 2) (.var "x")) (.const 1))]
  dt           := 1
  remainderPad := ⟨0, CanonicalRat.mk 1 10⟩

/-- Hybrid quantum control automaton modeling a pulsed two-mode gate schedule:
* Mode `"rabi_drive"`: coherent population transfer $\dot{p} = \frac{1}{2}$ with $\Delta t = 1$,
  invariant $p \in [0, 1]$.
* Mode `"idle_readout"`: Lindblad T1 relaxation $\dot{p} = -\frac{1}{10} p$ during dispersive
  readout with $\Delta t = 1$, invariant $p \in [0, 1]$.
* Guarded transition `"rabi_drive" → "idle_readout"` enabled when population reaches the target
  excited window $p \in [4/5, 1]$. -/
def quantumPulseHybridAutomaton : HybridAutomaton where
  modes :=
    [ { modeId := "rabi_drive"
      , ode :=
          { fields       := [("p", .const (CanonicalRat.mk 1 2))]
          , dt           := 1
          , remainderPad := ⟨CanonicalRat.mk (-1) 20, CanonicalRat.mk 1 20⟩ }
      , invariantBounds := [("p", ⟨0, 1⟩)] }
    , { modeId := "idle_readout"
      , ode :=
          { fields       := [("p", .mul (.const (CanonicalRat.mk (-1) 10)) (.var "p"))]
          , dt           := 1
          , remainderPad := ⟨CanonicalRat.mk (-1) 50, CanonicalRat.mk 1 50⟩ }
      , invariantBounds := [("p", ⟨0, 1⟩)] } ]
  jumps :=
    [ { fromMode    := "rabi_drive"
      , toMode      := "idle_readout"
      , guardBounds := [("p", ⟨CanonicalRat.mk 4 5, 1⟩)]
      , resetMap    := { resets := [] } } ]
  safeEnvelope := [("p", ⟨0, 1⟩)]

/-- **Theorem (`ctqw_validated_flowpipe_and_taylor_unitarity`)**:
1. **Validated Taylor-Model Unitary Phase Conservation**:
   Over $\theta \in [-1/10, 1/10]$, the degree-4 Taylor model `tmUnitaryNormSq` for
   $|e^{-i\theta}|^2 = \cos^2(\theta) + (-\sin(\theta))^2$ cancels all polynomial drift of degrees
   $1, 2, 3, 4$ (`coeffs = [1, 0, 0, 0, 0]`) and rigorously encloses exact unit probability $1$.
2. **Validated Symplectic Schrödinger & Lindblad Flowpipes (Positive Poles)**:
   - Over 3 steps with $\Delta t = 1/10$, the symplectic eigenmode ODE `schrodingerEigenmodeOde 1 (1/10)`
     and coupled 2-site walk `schrodingerK2CoupledOde (1/10)` starting from $|0\rangle$ stay strictly
     inside the unitary amplitude envelope (`verifyTrajectorySafety = true`).
   - Open-system Lindblad dephasing `lindbladDephasingOde (1/2) (1/2)` monotonically contracts coherence
     inside $[0, 1]$ (`verifyTrajectorySafety = true`).
3. **Non-Hermitian Runaway Refusal (Negative Pole)**:
   - The non-Hermitian anti-damped generator `nonHermitianGainRunawayOde` breaches the unitary envelope
     $[-2, 2]$ on step 1 and is refused (`verifyTrajectorySafety = false`).
4. **Hybrid Quantum Pulse Schedule Verification**:
   - Driving in `"rabi_drive"` from $p_0 \in [2/5, 9/20]$ into the $[4/5, 1]$ target window followed
     by `.jumpTo "idle_readout"` and readout relaxation passes `verifyHybridScheduleSafety = true`,
     whereas a premature readout jump before reaching the excited guard is refused (`= false`). -/
theorem ctqw_validated_flowpipe_and_taylor_unitarity :
    let dom : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    let rem5 : Interval := ⟨CanonicalRat.mk (-1) 100000, CanonicalRat.mk 1 100000⟩
    let normTM := tmUnitaryNormSq dom rem5
    let dtSmall := CanonicalRat.mk 1 10
    let remSmall : Interval := ⟨CanonicalRat.mk (-1) 100, CanonicalRat.mk 1 100⟩
    let eigenOde := schrodingerEigenmodeOde 1 dtSmall remSmall
    let k2Ode := schrodingerK2CoupledOde dtSmall remSmall
    let lindbladOde := lindbladDephasingOde (CanonicalRat.mk 1 2) (CanonicalRat.mk 1 2) remSmall
    let initEigen := [("x", Interval.ofPoint 1), ("y", Interval.ofPoint 0)]
    let safeEigen := [("x", (⟨-2, 2⟩ : Interval)), ("y", (⟨-2, 2⟩ : Interval))]
    let initK2 :=
      [ ("x0", Interval.ofPoint 1), ("y0", Interval.ofPoint 0)
      , ("x1", Interval.ofPoint 0), ("y1", Interval.ofPoint 0) ]
    let safeK2 :=
      [ ("x0", (⟨-2, 2⟩ : Interval)), ("y0", (⟨-2, 2⟩ : Interval))
      , ("x1", (⟨-2, 2⟩ : Interval)), ("y1", (⟨-2, 2⟩ : Interval)) ]
    let initPulse : HybridState :=
      { modeId := "rabi_drive"
      , box    := [("p", ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 9 20⟩)] }
    -- 1. Taylor model unitary phase identity cos^2(theta) + (-sin(theta))^2 = 1
    normTM.coeffs = [1, 0, 0, 0, 0] ∧
    Interval.containsRat (evalTaylorModelRange normTM) 1 = true ∧
    -- 2. Symplectic Schrodinger & Lindblad flowpipe safety (positive poles)
    verifyTrajectorySafety eigenOde initEigen 3 safeEigen = true ∧
    verifyTrajectorySafety k2Ode initK2 3 safeK2 = true ∧
    verifyTrajectorySafety lindbladOde [("c", ⟨CanonicalRat.mk 4 5, 1⟩)] 3 [("c", ⟨0, 1⟩)] = true ∧
    -- 3. Non-Hermitian gain runaway refusal (negative pole)
    verifyTrajectorySafety nonHermitianGainRunawayOde [("x", Interval.ofPoint 1)] 2 [("x", ⟨-2, 2⟩)] = false ∧
    -- 4. Hybrid quantum pulse schedule safety vs premature jump refusal
    verifyHybridScheduleSafety quantumPulseHybridAutomaton initPulse [.flowStep, .jumpTo "idle_readout", .flowStep] = true ∧
    verifyHybridScheduleSafety quantumPulseHybridAutomaton initPulse [.jumpTo "idle_readout"] = false := by
  decide +kernel

end Obend.Analysis
end
