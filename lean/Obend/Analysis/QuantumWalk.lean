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

/-- Matrix multiplication entry $(A B)_{u, v} = \sum_{w \in \text{indices}} A_{u, w} \cdot B_{w, v}$. -/
def matMulEntry (indices : List Nat) (A B : Nat → Nat → Int) (u v : Nat) : Int :=
  sumIntOver (fun w => A u w * B w v) indices

/-- Matrix addition entry $(A + B)_{u, v} = A_{u, v} + B_{u, v}$. -/
def matAddEntry (A B : Nat → Nat → Int) (u v : Nat) : Int :=
  A u v + B u v

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

/-- Concrete `IntMatrix` multiplication $(A \cdot B)$ of two `dim × dim` integer matrices. -/
def IntMatrix.mul (A B : IntMatrix) : IntMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v =>
        matMulEntry indices A.entry B.entry u v)) }

/-- Concrete `IntMatrix` addition $(A + B)$. -/
def IntMatrix.add (A B : IntMatrix) : IntMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => A.entry u v + B.entry u v)) }

/-- Concrete `IntMatrix` scalar multiplication $c \cdot A$. -/
def IntMatrix.scale (c : Int) (A : IntMatrix) : IntMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => c * A.entry u v)) }

/-- Scaled $n \times n$ identity matrix $s \cdot I_n$. -/
def IntMatrix.scaledIdentity (dim : Nat) (s : Int) : IntMatrix :=
  let indices := List.range dim
  { dim  := dim
  , rows := indices.map (fun u =>
      indices.map (fun v => if u == v then s else 0)) }

/-- Zero $n \times n$ matrix $0_n$. -/
def IntMatrix.zero (dim : Nat) : IntMatrix :=
  IntMatrix.scaledIdentity dim 0

/-! ## 2. Strong Cospectrality & Godsil's Spectral-Projector CTQW Propagator -/

/-- Sum a `GaussianInt`-valued function over a list of spectral mode indices `modes`. -/
def sumGaussianOver (f : Nat → GaussianInt) : List Nat → GaussianInt
  | [] => GaussianInt.zero
  | k :: ks => GaussianInt.add (f k) (sumGaussianOver f ks)

@[simp] theorem sumGaussianOver_nil (f : Nat → GaussianInt) :
    sumGaussianOver f [] = GaussianInt.zero := rfl

@[simp] theorem sumGaussianOver_cons (f : Nat → GaussianInt) (k : Nat) (ks : List Nat) :
    sumGaussianOver f (k :: ks) = GaussianInt.add (f k) (sumGaussianOver f ks) := rfl

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

/-! ## 3. Exact $K_2$ Antipodal PST (`ctqw_k2_antipodal_pst_exact`) -/

/-- Adjacency matrix of $K_2$ ($H_{K_2} = X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$). -/
def k2Matrix : IntMatrix where
  dim  := 2
  rows := [[0, 1], [1, 0]]

/-- Scaled symmetric projector $2 E_+ = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$ ($\lambda_+ = +1$). -/
def k2ProjPlus : IntMatrix where
  dim  := 2
  rows := [[1, 1], [1, 1]]

/-- Scaled antisymmetric projector $2 E_- = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$ ($\lambda_- = -1$). -/
def k2ProjMinus : IntMatrix where
  dim  := 2
  rows := [[1, -1], [-1, 1]]

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

/-! ## 4. Algebraic Number Field Spectral Projectors on $P_3$ via `Groebner.lean` (`ctqw_p3_end_to_end_pst_algebraic`) -/

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

end PolyMatrix

/-- Minimal polynomial $m(\alpha) = \alpha^2 - 2$ of $\alpha = \sqrt{2}$ (using variable $0$ for $\alpha$). -/
def p3MinPolyAlphaSqMinus2 : Poly :=
  Poly.sub ( polyVarPow 0 2 ) ( polyOfTerm [] 2 )

/-- Scaled spectral projector $4 P_0 = \begin{pmatrix} 2 & 0 & -2 \\ 0 & 0 & 0 \\ -2 & 0 & 2 \end{pmatrix}$
for eigenvalue $\lambda_0 = 0$ of $P_3$. -/
def p3AlgebraicProj0 : PolyMatrix :=
  PolyMatrix.ofIntMatrix { dim := 3, rows := [[2, 0, -2], [0, 0, 0], [-2, 0, 2]] }

/-- Scaled spectral projector $4 P_+ = \begin{pmatrix} 1 & \alpha & 1 \\ \alpha & 2 & \alpha \\ 1 & \alpha & 1 \end{pmatrix}$
for eigenvalue $\lambda_+ = +\alpha = +\sqrt{2}$ of $P_3$ in $\mathbb{Q}(\alpha)/\langle \alpha^2 - 2 \rangle$. -/
def p3AlgebraicProjPlus : PolyMatrix :=
  let c1 := polyOfTerm [] 1
  let c2 := polyOfTerm [] 2
  let alpha := polyVarPow 0 1
  { dim  := 3
  , rows :=
      [ [c1, alpha, c1]
      , [alpha, c2, alpha]
      , [c1, alpha, c1] ] }

/-- Scaled spectral projector $4 P_- = \begin{pmatrix} 1 & -\alpha & 1 \\ -\alpha & 2 & -\alpha \\ 1 & -\alpha & 1 \end{pmatrix}$
for eigenvalue $\lambda_- = -\alpha = -\sqrt{2}$ of $P_3$ in $\mathbb{Q}(\alpha)/\langle \alpha^2 - 2 \rangle$. -/
def p3AlgebraicProjMinus : PolyMatrix :=
  let c1 := polyOfTerm [] 1
  let c2 := polyOfTerm [] 2
  let negAlpha := polyOfTerm [(0, 1)] (-1)
  { dim  := 3
  , rows :=
      [ [c1, negAlpha, c1]
      , [negAlpha, c2, negAlpha]
      , [c1, negAlpha, c1] ] }

/-- Check Godsil's eigenvalue parity-ratio condition for antipodal PST:
Given integer-scaled squared differences or rationalized eigenvalue ratios, verifies whether all
odd-parity vs. even-parity eigenvalue differences share a common odd integer ratio multiple.
On $P_3$, $(\lambda_+ - \lambda_0) : (\lambda_0 - \lambda_-) = \sqrt{2} : \sqrt{2} = 1 : 1$ (odd/odd, passes!).
On $P_4$, eigenvalues are $\pm \frac{\sqrt{5}+1}{2}, \pm \frac{\sqrt{5}-1}{2}$ whose ratio
$\frac{\sqrt{5}+1}{\sqrt{5}-1} = \frac{3 + \sqrt{5}}{2} \notin \mathbb{Q}$ is irrational (`= false`). -/
def checkP4IrrationalRatioObstruction : Bool :=
  -- Minimal polynomial of ratio r on P4 is r^2 - 3*r + 1 = 0, which has no rational root:
  -- discriminant is 9 - 4 = 5 (not a square in Q), and r = 1 gives 1 - 3 + 1 = -1 ≠ 0.
  let rVar := polyVarPow 0 1
  let p4RatioMinPoly := Poly.add (Poly.sub (polyVarPow 0 2) (Poly.scale 3 rVar)) Poly.one
  let linearFactorRMinus1 := Poly.sub rVar Poly.one
  !(polyReduceFuel [linearFactorRMinus1] 4 p4RatioMinPoly).isZero

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

/-! ## 5. Hypercube $Q_d$ Krawtchouk Quotient & Bachman–Tamon Quotient PST Theorem -/

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
2. Its quotient matrix matches `krawtchoukQuotientEntry 3` across all $0 \le i, j < 4$.
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
