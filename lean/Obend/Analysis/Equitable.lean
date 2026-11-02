module
/-
# Obend.Analysis.Equitable — Computable Equitable Partitions, 1-WL Color Refinement, Symmetrizable Handshake Identity & Intertwining Calculus

Mechanizes computable **Equitable Graph / Hamiltonian Partitions**, **1-WL Color Refinement (Bisimulation)**,
the **Equitable Handshake / Symmetrizability Identity** ($D Q = Q^T D$), the **Fundamental Intertwining
Theorem** ($H S = S Q \implies H^k S = S Q^k$), and **Irreducibility / Residual Floor Certification**:

1. **Gaussian Integers & Rationals ($\mathbb{Z}[i]$ / $\mathbb{Q}[i]$) & Integer-Scaled Operators (`GaussianInt`, `GaussianRat`, `IntMatrix`)**:
   - Exact arithmetic over $\mathbb{Z}[i]$ and $\mathbb{Q}[i]$ with universal Brahmagupta–Fibonacci
     norm multiplicativity (`gaussianInt_normSq_mul`).
2. **Row-Profile Equitability & 1-WL Bisimulation Checker (`cellRowSum`, `checkEquitablePartition`, `checkWl1ColorRefinementStable`)**:
   - Verifies that for every vertex $u \in C_i$ and target cell $C_j$, the row sum $\sum_{v \in C_j} H_{u,v}$
     equals the quotient entry $Q_{i,j}$ independently of the representative $u \in C_i$.
3. **Equitable Handshake / Symmetrizability Theorem (`equitable_handshake_identity`)**:
   - Proves universally over arbitrary symmetric operators $H$ and finite cells $C_i, C_j$ that
     $|C_i| \cdot Q_{i,j} = |C_j| \cdot Q_{j,i}$ ($D Q = Q^T D$) via bipartite double counting,
     requiring zero `Real.sqrt` or noncomputable reals.
4. **Fundamental Intertwining Theorem (`equitable_intertwining_step`, `equitable_intertwining_power`)**:
   - Proves universally that for any cell-constant vector $v = S w$ ($v_u = w_{\text{part}(u)}$),
     $(H (S w))_u = (Q w)_{\text{part}(u)}$, and inductively $(H^k (S w))_u = (Q^k w)_{\text{part}(u)}$
     for all $k \in \mathbb{N}$.
5. **Irreducibility & Residual Floor Certification (`evalEquitableResidualNormSq`)**:
   - Quantifies the exact squared $\ell_2$/Frobenius residual norm of an operator outside the
     equitable subspace, certifying when lossless quotient compression is exact (`residual = 0`)
     versus when symmetry breaking forces a strictly positive error floor (`residual > 0`).
-/
public import Obend.Analysis.RealAnalysis
public import Obend.Analysis.Groebner
@[expose] public section

namespace Obend.Analysis
set_option autoImplicit false

/-! ## 1. Elementary Integer Ring Lemmas & Gaussian Integers / Rationals ($\mathbb{Z}[i]$, $\mathbb{Q}[i]$) -/

/-- The square of any integer is non-negative (`0 ≤ a * a`). -/
theorem equitable_int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases a with
  | ofNat n =>
    exact Int.natCast_nonneg (n * n)
  | negSucc n =>
    exact Int.natCast_nonneg (Nat.succ n * Nat.succ n)

/-- Four-factor integer multiplication swap $(p q)(r s) = (p r)(q s)$. -/
theorem equitable_int_mul_four_swap (p q r s : Int) :
    (p * q) * (r * s) = (p * r) * (q * s) := by
  rw [Int.mul_assoc p q (r * s)]
  rw [← Int.mul_assoc q r s]
  rw [Int.mul_comm q r]
  rw [Int.mul_assoc r q s]
  rw [← Int.mul_assoc p r (q * s)]

/-- Exact Gaussian integer $z = \text{re} + i \cdot \text{im} \in \mathbb{Z}[i]$. -/
structure GaussianInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace GaussianInt

/-- Additive identity $0 + 0i \in \mathbb{Z}[i]$. -/
def zero : GaussianInt := ⟨0, 0⟩

/-- Multiplicative identity $1 + 0i \in \mathbb{Z}[i]$. -/
def one : GaussianInt := ⟨1, 0⟩

/-- Imaginary unit $i = 0 + 1i \in \mathbb{Z}[i]$. -/
def iUnit : GaussianInt := ⟨0, 1⟩

/-- Embed an integer $n \in \mathbb{Z}$ as $n + 0i \in \mathbb{Z}[i]$. -/
def ofInt (n : Int) : GaussianInt := ⟨n, 0⟩

/-- Gaussian integer addition. -/
def add (z w : GaussianInt) : GaussianInt :=
  ⟨z.re + w.re, z.im + w.im⟩

/-- Gaussian integer subtraction. -/
def sub (z w : GaussianInt) : GaussianInt :=
  ⟨z.re - w.re, z.im - w.im⟩

/-- Gaussian integer negation. -/
def neg (z : GaussianInt) : GaussianInt :=
  ⟨-z.re, -z.im⟩

/-- Scalar multiplication by $c \in \mathbb{Z}$. -/
def scale (c : Int) (z : GaussianInt) : GaussianInt :=
  ⟨c * z.re, c * z.im⟩

/-- Complex conjugation $\overline{a + bi} = a - bi$. -/
def conj (z : GaussianInt) : GaussianInt :=
  ⟨z.re, -z.im⟩

/-- Gaussian integer multiplication $(a + bi)(c + di) = (ac - bd) + (ad + bc)i$. -/
def mul (z w : GaussianInt) : GaussianInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- Squared modulus (norm) $|a + bi|^2 = a^2 + b^2 \in \mathbb{Z}$. -/
def normSq (z : GaussianInt) : Int :=
  z.re * z.re + z.im * z.im

end GaussianInt

/-- Theorem (`gaussianInt_normSq_nonneg`):
For every Gaussian integer $z \in \mathbb{Z}[i]$, its squared modulus `z.normSq` is non-negative. -/
theorem gaussianInt_normSq_nonneg (z : GaussianInt) :
    0 ≤ z.normSq := by
  dsimp only [GaussianInt.normSq]
  have hRe : 0 ≤ z.re * z.re := equitable_int_sq_nonneg z.re
  have hIm : 0 ≤ z.im * z.im := equitable_int_sq_nonneg z.im
  omega

/-- Theorem (`gaussianInt_normSq_mul`):
**Brahmagupta–Fibonacci Multiplicative Norm Identity on $\mathbb{Z}[i]$**:
For all $z, w \in \mathbb{Z}[i]$, $|z \cdot w|^2 = |z|^2 \cdot |w|^2$. -/
theorem gaussianInt_normSq_mul (z w : GaussianInt) :
    (z.mul w).normSq = z.normSq * w.normSq := by
  dsimp only [GaussianInt.mul, GaussianInt.normSq]
  have hSubSq :
      (z.re * w.re - z.im * w.im) * (z.re * w.re - z.im * w.im) =
      (z.re * w.re) * (z.re * w.re) - (z.re * w.re) * (z.im * w.im) -
        (z.im * w.im) * (z.re * w.re) + (z.im * w.im) * (z.im * w.im) := by
    rw [Int.mul_sub, Int.sub_mul, Int.sub_mul]
    omega
  have hAddSq :
      (z.re * w.im + z.im * w.re) * (z.re * w.im + z.im * w.re) =
      (z.re * w.im) * (z.re * w.im) + (z.re * w.im) * (z.im * w.re) +
        (z.im * w.re) * (z.re * w.im) + (z.im * w.re) * (z.im * w.re) := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    omega
  have hRhs :
      (z.re * z.re + z.im * z.im) * (w.re * w.re + w.im * w.im) =
      (z.re * z.re) * (w.re * w.re) + (z.im * z.im) * (w.re * w.re) +
        (z.re * z.re) * (w.im * w.im) + (z.im * z.im) * (w.im * w.im) := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]
    omega
  have h1 : (z.re * w.re) * (z.re * w.re) = (z.re * z.re) * (w.re * w.re) :=
    equitable_int_mul_four_swap z.re w.re z.re w.re
  have h2 : (z.im * w.im) * (z.im * w.im) = (z.im * z.im) * (w.im * w.im) :=
    equitable_int_mul_four_swap z.im w.im z.im w.im
  have h3 : (z.re * w.im) * (z.re * w.im) = (z.re * z.re) * (w.im * w.im) :=
    equitable_int_mul_four_swap z.re w.im z.re w.im
  have h4 : (z.im * w.re) * (z.im * w.re) = (z.im * z.im) * (w.re * w.re) :=
    equitable_int_mul_four_swap z.im w.re z.im w.re
  have hCross1 : (z.re * w.re) * (z.im * w.im) = (z.re * w.im) * (z.im * w.re) := by
    rw [equitable_int_mul_four_swap z.re w.re z.im w.im, equitable_int_mul_four_swap z.re w.im z.im w.re, Int.mul_comm w.re w.im]
  have hCross2 : (z.im * w.im) * (z.re * w.re) = (z.im * w.re) * (z.re * w.im) := by
    rw [Int.mul_comm (z.im * w.im) (z.re * w.re), Int.mul_comm (z.im * w.re) (z.re * w.im), hCross1]
  omega

/-- Exact Gaussian rational $z = \text{re} + i \cdot \text{im} \in \mathbb{Q}[i]$ over `CanonicalRat`. -/
structure GaussianRat where
  re : CanonicalRat
  im : CanonicalRat
  deriving DecidableEq, Repr

namespace GaussianRat

def zero : GaussianRat := ⟨0, 0⟩
def one : GaussianRat := ⟨1, 0⟩
def iUnit : GaussianRat := ⟨0, 1⟩

def ofRat (q : CanonicalRat) : GaussianRat := ⟨q, 0⟩

def ofGaussianInt (z : GaussianInt) : GaussianRat :=
  ⟨CanonicalRat.ofInt z.re, CanonicalRat.ofInt z.im⟩

def add (z w : GaussianRat) : GaussianRat := ⟨z.re + w.re, z.im + w.im⟩
def sub (z w : GaussianRat) : GaussianRat := ⟨z.re - w.re, z.im - w.im⟩
def neg (z : GaussianRat) : GaussianRat := ⟨-z.re, -z.im⟩
def conj (z : GaussianRat) : GaussianRat := ⟨z.re, -z.im⟩
def scale (c : CanonicalRat) (z : GaussianRat) : GaussianRat := ⟨c * z.re, c * z.im⟩

def mul (z w : GaussianRat) : GaussianRat :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def normSq (z : GaussianRat) : CanonicalRat :=
  z.re * z.re + z.im * z.im

end GaussianRat

/-! ## 2. Finite Vertex Summation Algebra & Integer-Scaled Matrices (`sumIntOver`, `IntMatrix`) -/

/-- Sum an integer-valued function `f : Nat → Int` over a list of indices `xs` via structural recursion. -/
def sumIntOver (f : Nat → Int) : List Nat → Int
  | [] => 0
  | x :: xs => f x + sumIntOver f xs

@[simp] theorem sumIntOver_nil (f : Nat → Int) :
    sumIntOver f [] = 0 := rfl

@[simp] theorem sumIntOver_cons (f : Nat → Int) (x : Nat) (xs : List Nat) :
    sumIntOver f (x :: xs) = f x + sumIntOver f xs := rfl

/-- Summing the identically zero function over any list yields `0`. -/
theorem sumIntOver_zero : ∀ (xs : List Nat), sumIntOver (fun _ => 0) xs = 0
  | [] => rfl
  | _ :: xs => by
    dsimp only [sumIntOver]
    rw [sumIntOver_zero xs]
    omega

/-- Congruence of `sumIntOver` when two functions agree on all members of `xs`. -/
theorem sumIntOver_congr (f g : Nat → Int) :
    ∀ (xs : List Nat), (∀ x, x ∈ xs → f x = g x) → sumIntOver f xs = sumIntOver g xs
  | [], _ => rfl
  | x :: xs, h => by
    dsimp only [sumIntOver]
    have hx : f x = g x := h x (List.Mem.head xs)
    have hRest : sumIntOver f xs = sumIntOver g xs :=
      sumIntOver_congr f g xs (fun y hy => h y (List.Mem.tail x hy))
    rw [hx, hRest]

/-- If `f x = q` for every `x ∈ xs`, then $\sum_{x \in xs} f(x) = |xs| \cdot q$. -/
theorem sumIntOver_const_of_eq (f : Nat → Int) (q : Int) :
    ∀ (xs : List Nat), (∀ x, x ∈ xs → f x = q) → sumIntOver f xs = (xs.length : Int) * q
  | [], _ => by
    change 0 = (0 : Int) * q
    rw [Int.zero_mul]
  | x :: xs, h => by
    dsimp only [sumIntOver]
    have hx : f x = q := h x (List.Mem.head xs)
    have hRest : sumIntOver f xs = (xs.length : Int) * q :=
      sumIntOver_const_of_eq f q xs (fun y hy => h y (List.Mem.tail x hy))
    have hLen : ((x :: xs).length : Int) = (xs.length : Int) + 1 := by
      change ((xs.length + 1 : Nat) : Int) = (xs.length : Int) + 1
      omega
    rw [hx, hRest, hLen, Int.add_mul, Int.one_mul]
    omega

/-- Linearity of `sumIntOver` over pointwise addition. -/
theorem sumIntOver_add (f g : Nat → Int) :
    ∀ (xs : List Nat),
      sumIntOver (fun x => f x + g x) xs = sumIntOver f xs + sumIntOver g xs
  | [] => by dsimp only [sumIntOver]; omega
  | x :: xs => by
    dsimp only [sumIntOver]
    rw [sumIntOver_add f g xs]
    omega

/-- Factoring a constant right multiplier out of `sumIntOver`:
$\sum_{x \in xs} f(x) \cdot c = \left(\sum_{x \in xs} f(x)\right) \cdot c$. -/
theorem sumIntOver_mul_right (f : Nat → Int) (c : Int) :
    ∀ (xs : List Nat),
      sumIntOver (fun x => f x * c) xs = sumIntOver f xs * c
  | [] => by dsimp only [sumIntOver]; rw [Int.zero_mul]
  | x :: xs => by
    dsimp only [sumIntOver]
    rw [sumIntOver_mul_right f c xs, Int.add_mul]

/-- Factoring a constant left multiplier out of `sumIntOver`:
$\sum_{x \in xs} c \cdot f(x) = c \cdot \left(\sum_{x \in xs} f(x)\right)$. -/
theorem sumIntOver_mul_left (c : Int) (f : Nat → Int) :
    ∀ (xs : List Nat),
      sumIntOver (fun x => c * f x) xs = c * sumIntOver f xs
  | [] => by dsimp only [sumIntOver]; rw [Int.mul_zero]
  | x :: xs => by
    dsimp only [sumIntOver]
    rw [sumIntOver_mul_left c f xs, Int.mul_add]

/-- If every term `f x` is non-negative (`0 ≤ f x`), then `0 ≤ sumIntOver f xs`. -/
theorem sumIntOver_nonneg (f : Nat → Int) :
    ∀ (xs : List Nat), (∀ x, x ∈ xs → 0 ≤ f x) → 0 ≤ sumIntOver f xs
  | [], _ => by dsimp only [sumIntOver]; omega
  | x :: xs, h => by
    dsimp only [sumIntOver]
    have hx : 0 ≤ f x := h x (List.Mem.head xs)
    have hRest : 0 ≤ sumIntOver f xs :=
      sumIntOver_nonneg f xs (fun y hy => h y (List.Mem.tail x hy))
    omega

/-- **Fubini / Double-Sum Interchange Lemma (`doubleSum_swap`)**:
For any binary weight function `H : Nat → Nat → Int` and any finite vertex lists `xs, ys : List Nat`:
$$\sum_{u \in xs} \sum_{v \in ys} H(u, v) = \sum_{v \in ys} \sum_{u \in xs} H(u, v).$$ -/
theorem doubleSum_swap (H : Nat → Nat → Int) :
    ∀ (xs ys : List Nat),
      sumIntOver (fun u => sumIntOver (fun v => H u v) ys) xs =
      sumIntOver (fun v => sumIntOver (fun u => H u v) xs) ys
  | [], ys => by
    dsimp only [sumIntOver]
    exact (sumIntOver_zero ys).symm
  | u :: xs, ys => by
    dsimp only [sumIntOver]
    rw [doubleSum_swap H xs ys]
    exact (sumIntOver_add (fun v => H u v) (fun v => sumIntOver (fun u' => H u' v) xs) ys).symm

/-- Look up an integer at index `idx` in a list, defaulting to `0` out of bounds. -/
def listGetInt (xs : List Int) (idx : Nat) : Int :=
  match xs[idx]? with
  | some v => v
  | none   => 0

/-- Look up a natural number at index `idx` in a list, defaulting to `0` out of bounds. -/
def listGetNat (xs : List Nat) (idx : Nat) : Nat :=
  match xs[idx]? with
  | some v => v
  | none   => 0

/-- Explicit integer-scaled adjacency / Hamiltonian matrix of dimension `dim × dim`. -/
structure IntMatrix where
  dim  : Nat
  rows : List (List Int)
  deriving DecidableEq, Repr

namespace IntMatrix

/-- Entry lookup $H_{u,v}$ (returns `0` out of bounds). -/
def entry (m : IntMatrix) (u v : Nat) : Int :=
  match m.rows[u]? with
  | some row => listGetInt row v
  | none     => 0

/-- Check whether `m` is a well-shaped `dim × dim` symmetric matrix ($H_{u,v} = H_{v,u}$). -/
def isSymmetric (m : IntMatrix) : Bool :=
  let indices := List.range m.dim
  decide (m.rows.length == m.dim) &&
  m.rows.all (fun r => decide (r.length == m.dim)) &&
  indices.all (fun u =>
    indices.all (fun v =>
      decide (m.entry u v = m.entry v u)))

end IntMatrix

/-! ## 3. Equitable Partitions, Row-Sum Profiles & 1-WL Color Refinement -/

/-- Return the ordered list of vertices in `vertices` assigned to cell `j` under `part`. -/
def cellMembers (vertices : List Nat) (part : Nat → Nat) (j : Nat) : List Nat :=
  vertices.filter (fun v => part v == j)

/-- Cardinality $|C_j|$ of cell `j` within `vertices`. -/
def cellSize (vertices : List Nat) (part : Nat → Nat) (j : Nat) : Nat :=
  (cellMembers vertices part j).length

/-- Row sum $\sum_{v \in C_j} H_{u,v}$ of vertex `u` into target cell `cellJ`. -/
def cellRowSum (H : Nat → Nat → Int) (cellJ : List Nat) (u : Nat) : Int :=
  sumIntOver (fun v => H u v) cellJ

/-- Computable **Row-Profile Equitability Checker** (`checkEquitablePartition`):
Verifies that:
1. Every vertex $u \in \{0, \dots, \text{dim}-1\}$ is assigned to a valid cell $\text{part}(u) < \text{numCells}$,
2. Every cell $C_j$ ($j < \text{numCells}$) is non-empty (`1 ≤ |C_j|`),
3. For every vertex $u$ and every target cell $C_j$, the row sum $\sum_{v \in C_j} H_{u,v}$ equals the
   quotient matrix entry `quotientEntry (part u) j`. -/
def checkEquitablePartition
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (quotientEntry : Nat → Nat → Int) : Bool :=
  let vertices := List.range m.dim
  let cells := List.range numCells
  vertices.all (fun u => decide (part u < numCells)) &&
  cells.all (fun j => decide (1 ≤ cellSize vertices part j)) &&
  vertices.all (fun u =>
    cells.all (fun j =>
      let cJ := cellMembers vertices part j
      decide (cellRowSum m.entry cJ u = quotientEntry (part u) j)))

/-- Compute the 1-Weisfeiler-Leman (1-WL) color refinement signature of vertex `u`:
`(part u, [sum_{v in C_0} H_{u,v}, ..., sum_{v in C_{r-1}} H_{u,v}])`. -/
def wl1VertexProfile
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (u : Nat) : Nat × List Int :=
  let vertices := List.range m.dim
  let cells := List.range numCells
  (part u, cells.map (fun j => cellRowSum m.entry (cellMembers vertices part j) u))

/-- Check whether the partition `part` is a stable 1-WL color refinement fixed point (bisimulation):
any two vertices $u, v$ sharing the same color `part u = part v` have identical cell-degree row profiles. -/
def checkWl1ColorRefinementStable
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat) : Bool :=
  let vertices := List.range m.dim
  vertices.all (fun u =>
    vertices.all (fun v =>
      if part u == part v then
        decide (wl1VertexProfile m numCells part u = wl1VertexProfile m numCells part v)
      else
        true))

/-! ## 4. Equitable Handshake / Symmetrizability Theorem ($|C_i| \cdot Q_{i,j} = |C_j| \cdot Q_{j,i}$) -/

/-- **Theorem (`equitable_handshake_identity`)**:
For any symmetric Hamiltonian / adjacency operator $H$ ($\forall u \in C_i, \forall v \in C_j, H_{u,v} = H_{v,u}$)
and any pair of cells $C_i, C_j$ where every vertex $u \in C_i$ has row sum $Q_{i,j}$ into $C_j$
and every vertex $v \in C_j$ has row sum $Q_{j,i}$ into $C_i$, the bipartite interaction weight
double-counts to the exact integer identity:
$$|C_i| \cdot Q_{i,j} = |C_j| \cdot Q_{j,i} \qquad (D Q = Q^T D).$$
Requires zero `Real.sqrt` and zero noncomputable reals. -/
theorem equitable_handshake_identity
    (H : Nat → Nat → Int)
    (cellI cellJ : List Nat)
    (qIJ qJI : Int)
    (hSym : ∀ u, u ∈ cellI → ∀ v, v ∈ cellJ → H u v = H v u)
    (hRowI : ∀ u, u ∈ cellI → cellRowSum H cellJ u = qIJ)
    (hRowJ : ∀ v, v ∈ cellJ → cellRowSum H cellI v = qJI) :
    (cellI.length : Int) * qIJ = (cellJ.length : Int) * qJI := by
  have hLhs :
      sumIntOver (fun u => cellRowSum H cellJ u) cellI = (cellI.length : Int) * qIJ :=
    sumIntOver_const_of_eq (fun u => cellRowSum H cellJ u) qIJ cellI hRowI
  have hRhs :
      sumIntOver (fun v => cellRowSum H cellI v) cellJ = (cellJ.length : Int) * qJI :=
    sumIntOver_const_of_eq (fun v => cellRowSum H cellI v) qJI cellJ hRowJ
  have hSwap :
      sumIntOver (fun u => cellRowSum H cellJ u) cellI =
      sumIntOver (fun v => sumIntOver (fun u => H u v) cellI) cellJ := by
    dsimp only [cellRowSum]
    exact doubleSum_swap H cellI cellJ
  have hSymCongr :
      sumIntOver (fun v => sumIntOver (fun u => H u v) cellI) cellJ =
      sumIntOver (fun v => cellRowSum H cellI v) cellJ := by
    apply sumIntOver_congr
    intro v hv
    dsimp only [cellRowSum]
    apply sumIntOver_congr
    intro u hu
    exact hSym u hu v hv
  exact hLhs.symm.trans (hSwap.trans (hSymCongr.trans hRhs))

/-- Computable checker for the symmetrizability identity $|C_i| \cdot Q_{i,j} = |C_j| \cdot Q_{j,i}$
across all cell pairs $0 \le i, j < \text{numCells}$. -/
def checkHandshakeIdentity
    (dim numCells : Nat)
    (part : Nat → Nat)
    (quotientEntry : Nat → Nat → Int) : Bool :=
  let vertices := List.range dim
  let cells := List.range numCells
  cells.all (fun i =>
    cells.all (fun j =>
      let sizeI : Int := cellSize vertices part i
      let sizeJ : Int := cellSize vertices part j
      decide (sizeI * quotientEntry i j = sizeJ * quotientEntry j i)))

/-- Helper lemma: `xs.all p = true` iff `p x = true` for every `x ∈ xs`. -/
theorem list_all_iff_forall {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.all p = true ↔ ∀ x, x ∈ xs → p x = true
  | [] => by
    simp only [List.all_nil, List.not_mem_nil, false_implies, implies_true]
  | x :: xs => by
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons]
    rw [list_all_iff_forall p xs]
    constructor
    · intro ⟨hx, hxs⟩ y hy
      cases hy with
      | inl hEq => rw [hEq]; exact hx
      | inr hIn => exact hxs y hIn
    · intro h
      exact ⟨h x (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩

/-- Every member of `cellMembers vertices part j` belongs to `vertices` and has `part x = j`. -/
theorem cellMembers_part_eq (vertices : List Nat) (part : Nat → Nat) (j : Nat) :
    ∀ x, x ∈ cellMembers vertices part j → part x = j := by
  intro x hx
  dsimp only [cellMembers] at hx
  rw [List.mem_filter] at hx
  exact of_decide_eq_true hx.2

/-- **Theorem (`checkEquitablePartition_sound`)**:
**Checker Soundness Bridge for `checkEquitablePartition`**:
If `checkEquitablePartition m numCells part Q = true`, then:
1. Every vertex $u < m.\text{dim}$ is assigned to a valid cell $\text{part}(u) < \text{numCells}$,
2. Every cell $j < \text{numCells}$ is non-empty (`1 ≤ cellSize (List.range m.dim) part j`), and
3. Every vertex $u < m.\text{dim}$ and target cell $j < \text{numCells}$ satisfies the exact
   equitable row-sum identity:
   $$\text{cellRowSum}\; m.\text{entry}\; (\text{cellMembers}\; (\text{List.range}\; m.\text{dim})\; \text{part}\; j)\; u = Q(\text{part}(u), j).$$ -/
theorem checkEquitablePartition_sound
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (Q : Nat → Nat → Int)
    (hCheck : checkEquitablePartition m numCells part Q = true) :
    (∀ u, u < m.dim → part u < numCells) ∧
    (∀ j, j < numCells → 1 ≤ cellSize (List.range m.dim) part j) ∧
    (∀ u j, u < m.dim → j < numCells →
      cellRowSum m.entry (cellMembers (List.range m.dim) part j) u = Q (part u) j) := by
  unfold checkEquitablePartition at hCheck
  simp only [Bool.and_eq_true] at hCheck
  rcases hCheck with ⟨⟨hPartAll, hSizeAll⟩, hRowAll⟩
  rw [list_all_iff_forall] at hPartAll hSizeAll hRowAll
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have huMem : u ∈ List.range m.dim := List.mem_range.mpr hu
    exact of_decide_eq_true (hPartAll u huMem)
  · intro j hj
    have hjMem : j ∈ List.range numCells := List.mem_range.mpr hj
    exact of_decide_eq_true (hSizeAll j hjMem)
  · intro u j hu hj
    have huMem : u ∈ List.range m.dim := List.mem_range.mpr hu
    have hjMem : j ∈ List.range numCells := List.mem_range.mpr hj
    have hRowU := (list_all_iff_forall _ (List.range numCells)).mp (hRowAll u huMem) j hjMem
    exact of_decide_eq_true hRowU

/-! ## 5. Fundamental Intertwining Theorem ($H S = S Q$, $H^k S = S Q^k$, and $p(H) S = S p(Q)$) -/

/-- Lift a quotient cell vector `w : Nat → Int` to a cell-constant vertex vector $(S w)_u = w_{\text{part}(u)}$. -/
def liftQuotientVec (part : Nat → Nat) (w : Nat → Int) (u : Nat) : Int :=
  w (part u)

/-- Alias for `liftQuotientVec`. -/
abbrev liftVec := liftQuotientVec

/-- Standard unpartitioned matrix-vector multiplication $(H v)_u = \sum_{x \in \text{indices}} H_{u,x} \cdot v_x$. -/
def matVec (indices : List Nat) (H : Nat → Nat → Int) (v : Nat → Int) (u : Nat) : Int :=
  sumIntOver (fun x => H u x * v x) indices

/-- Apply the $r \times r$ quotient matrix $Q$ to a quotient vector $w$ at cell $i$:
$$(Q w)_i = \sum_{j \in \text{cellIndices}} Q_{i, j} \cdot w_j.$$ -/
def quotientMatVec
    (Q : Nat → Nat → Int)
    (cellIndices : List Nat)
    (w : Nat → Int)
    (i : Nat) : Int :=
  sumIntOver (fun j => Q i j * w j) cellIndices

/-- Apply the $n \times n$ operator $H$ decomposed across the partition cells `cellOf j` ($j \in \text{cellIndices}$):
$$(H v)_u = \sum_{j \in \text{cellIndices}} \sum_{x \in C_j} H_{u, x} \cdot v_x.$$ -/
def partitionedMatVec
    (H : Nat → Nat → Int)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (v : Nat → Int)
    (u : Nat) : Int :=
  sumIntOver (fun j => sumIntOver (fun x => H u x * v x) (cellOf j)) cellIndices

/-- Additivity of `sumIntOver` across list concatenation `xs ++ ys`. -/
theorem sumIntOver_append (f : Nat → Int) :
    ∀ (xs ys : List Nat),
      sumIntOver f (xs ++ ys) = sumIntOver f xs + sumIntOver f ys
  | [], ys => by
    dsimp only [List.nil_append, sumIntOver]
    omega
  | x :: xs, ys => by
    dsimp only [List.cons_append, sumIntOver]
    rw [sumIntOver_append f xs ys]
    omega

/-- Decomposition of `sumIntOver` over `cellIndices.flatMap cellOf` into a nested cell sum. -/
theorem sumIntOver_flatMap (f : Nat → Int) (cellOf : Nat → List Nat) :
    ∀ (cellIndices : List Nat),
      sumIntOver f (cellIndices.flatMap cellOf) =
        sumIntOver (fun j => sumIntOver f (cellOf j)) cellIndices
  | [] => rfl
  | j :: js => by
    simp only [List.flatMap_cons, sumIntOver]
    rw [sumIntOver_append f (cellOf j) (js.flatMap cellOf)]
    rw [sumIntOver_flatMap f cellOf js]

/-- Step expansion of `sumIntOver f (cellMembers (x :: xs) part j)`. -/
theorem sumIntOver_cellMembers_cons
    (f : Nat → Int) (x : Nat) (xs : List Nat) (part : Nat → Nat) (j : Nat) :
    sumIntOver f (cellMembers (x :: xs) part j) =
      (if part x == j then f x else 0) + sumIntOver f (cellMembers xs part j) := by
  dsimp only [cellMembers, List.filter]
  cases h : (part x == j)
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_add]
  · simp only [↓reduceIte, sumIntOver]

/-- Summing a Kronecker delta `if target == j then c else 0` over a list not containing `target` yields `0`. -/
theorem sumIntOver_ite_eq_zero_of_not_mem (c : Int) (target : Nat) :
    ∀ (js : List Nat), (∀ j, j ∈ js → target ≠ j) →
      sumIntOver (fun j => if target == j then c else 0) js = 0
  | [], _ => rfl
  | j :: js, hNotMem => by
    dsimp only [sumIntOver]
    have hNe : target ≠ j := hNotMem j (List.Mem.head js)
    have hBeq : (target == j) = false := beq_false_of_ne hNe
    rw [hBeq]
    simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_add]
    exact sumIntOver_ite_eq_zero_of_not_mem c target js
      (fun k hk => hNotMem k (List.Mem.tail j hk))

/-- Summing a Kronecker delta `if target == j then c else 0` over `List.range n` yields `c` whenever `target < n`. -/
theorem sumIntOver_ite_range_eq (c : Int) (target : Nat) :
    ∀ (n : Nat), target < n →
      sumIntOver (fun j => if target == j then c else 0) (List.range n) = c
  | 0, hLt => absurd hLt (Nat.not_lt_zero target)
  | n + 1, hLt => by
    rw [List.range_succ, sumIntOver_append]
    dsimp only [sumIntOver]
    by_cases hEq : target = n
    · subst hEq
      have hBeq : (target == target) = true := beq_self_eq_true target
      rw [hBeq]
      simp only [↓reduceIte, Int.add_zero]
      have hZero : sumIntOver (fun j => if target == j then c else 0) (List.range target) = 0 := by
        apply sumIntOver_ite_eq_zero_of_not_mem
        intro j hj
        have hjLt : j < target := List.mem_range.mp hj
        omega
      rw [hZero, Int.zero_add]
    · have hLtN : target < n := by omega
      have hBeq : (target == n) = false := beq_false_of_ne hEq
      rw [hBeq, sumIntOver_ite_range_eq c target n hLtN]
      simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero]

/-- **Partition Bijection Sum Decomposition Lemma (`sumIntOver_cellMembers_partition`)**:
For any vertex list `vertices`, partition `part : Nat → Nat`, and `numCells : Nat`, if every
vertex $x \in \text{vertices}$ has $\text{part}(x) < \text{numCells}$, then summing any function
$f : \text{Nat} \to \text{Int}$ over the disjoint cells `cellMembers vertices part j` ($0 \le j < \text{numCells}$)
equals summing $f$ directly over `vertices`:
$$\sum_{j=0}^{\text{numCells}-1} \sum_{x \in C_j} f(x) = \sum_{x \in \text{vertices}} f(x).$$ -/
theorem sumIntOver_cellMembers_partition
    (f : Nat → Int)
    (part : Nat → Nat)
    (numCells : Nat) :
    ∀ (vertices : List Nat),
      (∀ x, x ∈ vertices → part x < numCells) →
      sumIntOver (fun j => sumIntOver f (cellMembers vertices part j)) (List.range numCells) =
        sumIntOver f vertices
  | [], _ => by
    dsimp only [cellMembers, List.filter, sumIntOver]
    exact sumIntOver_zero (List.range numCells)
  | x :: xs, hPart => by
    dsimp only [sumIntOver]
    have hCongr :
        sumIntOver (fun j => sumIntOver f (cellMembers (x :: xs) part j)) (List.range numCells) =
        sumIntOver (fun j => (if part x == j then f x else 0) + sumIntOver f (cellMembers xs part j))
          (List.range numCells) := by
      apply sumIntOver_congr
      intro j _
      exact sumIntOver_cellMembers_cons f x xs part j
    rw [hCongr, sumIntOver_add]
    have hxLt : part x < numCells := hPart x (List.Mem.head xs)
    rw [sumIntOver_ite_range_eq (f x) (part x) numCells hxLt]
    rw [sumIntOver_cellMembers_partition f part numCells xs (fun y hy => hPart y (List.Mem.tail x hy))]

/-- **Theorem (`partitionedMatVec_eq_matVec`)**:
When every vertex $x \in \text{vertices}$ is assigned to a valid cell $\text{part}(x) < \text{numCells}$,
the cell-partitioned matrix-vector product `partitionedMatVec` equals the standard unpartitioned
matrix-vector product `matVec`:
$$\sum_{j=0}^{\text{numCells}-1} \sum_{x \in C_j} H_{u,x} v_x = \sum_{x \in \text{vertices}} H_{u,x} v_x.$$ -/
theorem partitionedMatVec_eq_matVec
    (H : Nat → Nat → Int)
    (vertices : List Nat)
    (numCells : Nat)
    (part : Nat → Nat)
    (v : Nat → Int)
    (u : Nat)
    (hPart : ∀ x, x ∈ vertices → part x < numCells) :
    partitionedMatVec H (List.range numCells) (cellMembers vertices part) v u =
      matVec vertices H v u := by
  dsimp only [partitionedMatVec, matVec]
  exact sumIntOver_cellMembers_partition (fun x => H u x * v x) part numCells vertices hPart

/-- **Theorem (`matMulEntry_eq_partitionedMatVec`)**:
For any vertex list `indices` partitioned by `part` into `numCells` cells (`∀ x ∈ indices, part x < numCells`),
the unpartitioned matrix-vector sum $\sum_{x \in \text{indices}} H_{u,x} v_x$ equals
`partitionedMatVec H (List.range numCells) (cellMembers indices part) v u`. -/
theorem matMulEntry_eq_partitionedMatVec
    (H : Nat → Nat → Int)
    (indices : List Nat)
    (numCells : Nat)
    (part : Nat → Nat)
    (v : Nat → Int)
    (u : Nat)
    (hPart : ∀ x, x ∈ indices → part x < numCells) :
    matVec indices H v u =
      partitionedMatVec H (List.range numCells) (cellMembers indices part) v u :=
  (partitionedMatVec_eq_matVec H indices numCells part v u hPart).symm

/-- Helper lemma: within a single cell `cellJ` where every vertex $x \in \text{cellJ}$ has $\text{part}(x) = j$,
summing $H_{u,x} \cdot w_{\text{part}(x)}$ factors out the constant cell weight $w_j$:
$$\sum_{x \in C_j} H_{u,x} \cdot w_{\text{part}(x)} = \left(\sum_{x \in C_j} H_{u,x}\right) \cdot w_j.$$ -/
theorem cellSum_liftQuotientVec
    (H : Nat → Nat → Int)
    (part : Nat → Nat)
    (w : Nat → Int)
    (u j : Nat)
    (cellJ : List Nat)
    (hCell : ∀ x, x ∈ cellJ → part x = j) :
    sumIntOver (fun x => H u x * liftQuotientVec part w x) cellJ =
      cellRowSum H cellJ u * w j := by
  have hCongr :
      sumIntOver (fun x => H u x * liftQuotientVec part w x) cellJ =
      sumIntOver (fun x => H u x * w j) cellJ := by
    apply sumIntOver_congr
    intro x hx
    dsimp only [liftQuotientVec]
    rw [hCell x hx]
  rw [hCongr, sumIntOver_mul_right (fun x => H u x) (w j) cellJ]
  rfl

/-- **Theorem (`equitable_intertwining_step`)**:
**Fundamental One-Step Intertwining Identity ($H S = S Q$)**:
For any operator $H$, partition `part`, cell family `cellOf`, and quotient matrix $Q$, if:
1. every vertex $x \in \text{cellOf}(j)$ has $\text{part}(x) = j$, and
2. vertex $u$ satisfies the equitable row-sum condition $\sum_{x \in \text{cellOf}(j)} H_{u,x} = Q_{\text{part}(u), j}$
   for all $j \in \text{cellIndices}$,
then for EVERY quotient vector $w : \text{Nat} \to \text{Int}$:
$$(H (S w))_u = (S (Q w))_u.$$ -/
theorem equitable_intertwining_step
    (H Q : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (w : Nat → Int)
    (u : Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqRow : ∀ j, j ∈ cellIndices → cellRowSum H (cellOf j) u = Q (part u) j) :
    partitionedMatVec H cellIndices cellOf (liftQuotientVec part w) u =
      liftQuotientVec part (quotientMatVec Q cellIndices w) u := by
  dsimp only [partitionedMatVec, quotientMatVec]
  change sumIntOver (fun j => sumIntOver (fun x => H u x * liftQuotientVec part w x) (cellOf j)) cellIndices =
    sumIntOver (fun j => Q (part u) j * w j) cellIndices
  apply sumIntOver_congr
  intro j hj
  have hStep := cellSum_liftQuotientVec H part w u j (cellOf j) (hCells j hj)
  rw [hStep, hEqRow j hj]

/-- **Theorem (`equitable_intertwining_step_unpartitioned`)**:
End-to-end one-step intertwining for the standard unpartitioned `matVec (List.range m.dim) m.entry`
whenever `checkEquitablePartition m numCells part Q = true`! -/
theorem equitable_intertwining_step_unpartitioned
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (Q : Nat → Nat → Int)
    (w : Nat → Int)
    (u : Nat)
    (hCheck : checkEquitablePartition m numCells part Q = true)
    (hu : u < m.dim) :
    matVec (List.range m.dim) m.entry (liftQuotientVec part w) u =
      liftQuotientVec part (quotientMatVec Q (List.range numCells) w) u := by
  rcases checkEquitablePartition_sound m numCells part Q hCheck with ⟨hPart, _, hRow⟩
  rw [matMulEntry_eq_partitionedMatVec m.entry (List.range m.dim) numCells part
        (liftQuotientVec part w) u (fun x hx => hPart x (List.mem_range.mp hx))]
  apply equitable_intertwining_step
  · intro j _ x hx
    exact cellMembers_part_eq (List.range m.dim) part j x hx
  · intro j hj
    exact hRow u j hu (List.mem_range.mp hj)

/-- Congruence of `partitionedMatVec` when two vertex vectors agree on all vertices of all cells. -/
theorem partitionedMatVec_congr
    (H : Nat → Nat → Int)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (v1 v2 : Nat → Int)
    (u : Nat)
    (hEq : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → v1 x = v2 x) :
    partitionedMatVec H cellIndices cellOf v1 u =
      partitionedMatVec H cellIndices cellOf v2 u := by
  dsimp only [partitionedMatVec]
  apply sumIntOver_congr
  intro j hj
  apply sumIntOver_congr
  intro x hx
  rw [hEq j hj x hx]

/-- Congruence of `matVec` when two vertex vectors agree on all `x ∈ indices`. -/
theorem matVec_congr
    (indices : List Nat)
    (H : Nat → Nat → Int)
    (v1 v2 : Nat → Int)
    (u : Nat)
    (hEq : ∀ x, x ∈ indices → v1 x = v2 x) :
    matVec indices H v1 u = matVec indices H v2 u := by
  dsimp only [matVec]
  apply sumIntOver_congr
  intro x hx
  rw [hEq x hx]

/-- Iterate a linear operator on vectors `k` times: $A^0 v = v$, $A^{k+1} v = A (A^k v)$. -/
def iterateVecOp (op : (Nat → Int) → (Nat → Int)) : Nat → (Nat → Int) → (Nat → Int)
  | 0, v => v
  | k + 1, v => op (iterateVecOp op k v)

/-- **Theorem (`equitable_intertwining_power`)**:
**Fundamental Multi-Step / Power-Series Intertwining Theorem ($H^k S = S Q^k$)**:
If $(H, \text{part}, Q)$ forms an equitable partition across `cellIndices` and `cellOf`, then
for EVERY power $k \in \mathbb{N}$, EVERY quotient vector $w : \text{Nat} \to \text{Int}$, and
EVERY vertex $u$:
$$(H^k (S w))_u = (S (Q^k w))_u.$$
Thus $n$-dimensional Krylov / Taylor / matrix-exponential Hamiltonian evolution on any cell-constant
initial state factors **identically** through the $r$-dimensional quotient matrix $Q$! -/
theorem equitable_intertwining_power
    (H Q : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqAll : ∀ u, ∀ j, j ∈ cellIndices → cellRowSum H (cellOf j) u = Q (part u) j) :
    ∀ (k : Nat) (w : Nat → Int) (u : Nat),
      iterateVecOp (partitionedMatVec H cellIndices cellOf) k (liftQuotientVec part w) u =
        liftQuotientVec part (iterateVecOp (quotientMatVec Q cellIndices) k w) u
  | 0, _, _ => rfl
  | k + 1, w, u => by
    dsimp only [iterateVecOp]
    have hCongr :
        partitionedMatVec H cellIndices cellOf
          (iterateVecOp (partitionedMatVec H cellIndices cellOf) k (liftQuotientVec part w)) u =
        partitionedMatVec H cellIndices cellOf
          (liftQuotientVec part (iterateVecOp (quotientMatVec Q cellIndices) k w)) u := by
      apply partitionedMatVec_congr
      intro j _ x _
      exact equitable_intertwining_power H Q part cellIndices cellOf hCells hEqAll k w x
    rw [hCongr]
    exact equitable_intertwining_step H Q part cellIndices cellOf
      (iterateVecOp (quotientMatVec Q cellIndices) k w) u hCells (hEqAll u)

/-- **Theorem (`equitable_intertwining_power_unpartitioned`)**:
End-to-end multi-step power intertwining for the standard unpartitioned `matVec (List.range m.dim) m.entry`
(and `partitionedMatVec`) on any bounded vertex $u < m.\text{dim}$ whenever
`checkEquitablePartition m numCells part Q = true`! -/
theorem equitable_intertwining_power_unpartitioned
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (Q : Nat → Nat → Int)
    (hCheck : checkEquitablePartition m numCells part Q = true) :
    ∀ (k : Nat) (w : Nat → Int) (u : Nat),
      u < m.dim →
      iterateVecOp (matVec (List.range m.dim) m.entry) k (liftQuotientVec part w) u =
        liftQuotientVec part (iterateVecOp (quotientMatVec Q (List.range numCells)) k w) u ∧
      iterateVecOp
          (partitionedMatVec m.entry (List.range numCells) (cellMembers (List.range m.dim) part))
          k (liftQuotientVec part w) u =
        liftQuotientVec part (iterateVecOp (quotientMatVec Q (List.range numCells)) k w) u
  | 0, _, _, _ => ⟨rfl, rfl⟩
  | k + 1, w, u, hu => by
    dsimp only [iterateVecOp]
    rcases checkEquitablePartition_sound m numCells part Q hCheck with ⟨hPart, _, hRow⟩
    have hCongrMat :
        matVec (List.range m.dim) m.entry
          (iterateVecOp (matVec (List.range m.dim) m.entry) k (liftQuotientVec part w)) u =
        matVec (List.range m.dim) m.entry
          (liftQuotientVec part (iterateVecOp (quotientMatVec Q (List.range numCells)) k w)) u := by
      apply matVec_congr
      intro x hx
      exact (equitable_intertwining_power_unpartitioned m numCells part Q hCheck k w x
        (List.mem_range.mp hx)).1
    have hCongrPart :
        partitionedMatVec m.entry (List.range numCells) (cellMembers (List.range m.dim) part)
          (iterateVecOp
            (partitionedMatVec m.entry (List.range numCells) (cellMembers (List.range m.dim) part))
            k (liftQuotientVec part w)) u =
        partitionedMatVec m.entry (List.range numCells) (cellMembers (List.range m.dim) part)
          (liftQuotientVec part (iterateVecOp (quotientMatVec Q (List.range numCells)) k w)) u := by
      apply partitionedMatVec_congr
      intro j _ x hx
      dsimp only [cellMembers] at hx
      rw [List.mem_filter] at hx
      exact (equitable_intertwining_power_unpartitioned m numCells part Q hCheck k w x
        (List.mem_range.mp hx.1)).2
    constructor
    · rw [hCongrMat]
      exact equitable_intertwining_step_unpartitioned m numCells part Q
        (iterateVecOp (quotientMatVec Q (List.range numCells)) k w) u hCheck hu
    · rw [hCongrPart]
      apply equitable_intertwining_step
      · intro j _ x hx
        exact cellMembers_part_eq (List.range m.dim) part j x hx
      · intro j hj
        exact hRow u j hu (List.mem_range.mp hj)

/-- Auxiliary evaluator for matrix polynomial $\sum_{m} c_m (A^{k+m} v)_u$ starting at degree `k`. -/
def evalMatrixPolyAux (op : (Nat → Int) → (Nat → Int)) (k : Nat) : List Int → (Nat → Int) → (Nat → Int)
  | [], _ => fun _ => 0
  | c :: cs, v => fun u => c * iterateVecOp op k v u + evalMatrixPolyAux op (k + 1) cs v u

/-- Evaluate the matrix polynomial $\sum_{k} c_k A^k v$ of a linear operator `op` on vector `v` at index `u`. -/
def evalMatrixPoly (op : (Nat → Int) → (Nat → Int)) (coeffs : List Int) (v : Nat → Int) (u : Nat) : Int :=
  evalMatrixPolyAux op 0 coeffs v u

/-- Helper lemma: `evalMatrixPolyAux` intertwines equitable lifts starting from any power offset `k`. -/
theorem equitable_intertwining_poly_aux
    (H Q : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqAll : ∀ u, ∀ j, j ∈ cellIndices → cellRowSum H (cellOf j) u = Q (part u) j) :
    ∀ (coeffs : List Int) (k : Nat) (w : Nat → Int) (u : Nat),
      evalMatrixPolyAux (partitionedMatVec H cellIndices cellOf) k coeffs (liftQuotientVec part w) u =
        liftQuotientVec part (evalMatrixPolyAux (quotientMatVec Q cellIndices) k coeffs w) u
  | [], _, _, _ => rfl
  | c :: cs, k, w, u => by
    dsimp only [evalMatrixPolyAux, liftQuotientVec]
    rw [equitable_intertwining_power H Q part cellIndices cellOf hCells hEqAll k w u]
    rw [equitable_intertwining_poly_aux H Q part cellIndices cellOf hCells hEqAll cs (k + 1) w u]
    rfl

/-- **Theorem (`equitable_intertwining_poly`)**:
**Universal Polynomial Intertwining Theorem ($p(H) S = S p(Q)$)**:
For any polynomial $p(x) = \sum_{k} c_k x^k$ (`coeffs : List Int`), any equitable partition
$(H, \text{part}, Q)$ across `cellIndices` and `cellOf`, any quotient vector `w : Nat → Int`,
and any vertex `u : Nat`:
$$\left(\sum_{k} c_k H^k (S w)\right)_u = \left(S \left(\sum_{k} c_k Q^k w\right)\right)_u = \left(\sum_{k} c_k Q^k w\right)_{\text{part}(u)}.$$
This immediately implies exact intertwining of any truncated Taylor propagator or Chebyshev / Krylov
spectral filter polynomial! -/
theorem equitable_intertwining_poly
    (H Q : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (coeffs : List Int)
    (w : Nat → Int)
    (u : Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqAll : ∀ u, ∀ j, j ∈ cellIndices → cellRowSum H (cellOf j) u = Q (part u) j) :
    evalMatrixPoly (partitionedMatVec H cellIndices cellOf) coeffs (liftQuotientVec part w) u =
      liftQuotientVec part (evalMatrixPoly (quotientMatVec Q cellIndices) coeffs w) u :=
  equitable_intertwining_poly_aux H Q part cellIndices cellOf hCells hEqAll coeffs 0 w u

/-- Helper lemma: `evalMatrixPolyAux` intertwines unpartitioned `matVec` and `partitionedMatVec`
on all bounded vertices $u < m.\text{dim}$ whenever `checkEquitablePartition m numCells part Q = true`. -/
theorem equitable_intertwining_poly_unpartitioned_aux
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (Q : Nat → Nat → Int)
    (hCheck : checkEquitablePartition m numCells part Q = true) :
    ∀ (coeffs : List Int) (k : Nat) (w : Nat → Int) (u : Nat),
      u < m.dim →
      evalMatrixPolyAux (matVec (List.range m.dim) m.entry) k coeffs (liftQuotientVec part w) u =
        liftQuotientVec part (evalMatrixPolyAux (quotientMatVec Q (List.range numCells)) k coeffs w) u ∧
      evalMatrixPolyAux
          (partitionedMatVec m.entry (List.range numCells) (cellMembers (List.range m.dim) part))
          k coeffs (liftQuotientVec part w) u =
        liftQuotientVec part (evalMatrixPolyAux (quotientMatVec Q (List.range numCells)) k coeffs w) u
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | c :: cs, k, w, u, hu => by
    dsimp only [evalMatrixPolyAux, liftQuotientVec]
    rcases equitable_intertwining_power_unpartitioned m numCells part Q hCheck k w u hu with ⟨hPowMat, hPowPart⟩
    rcases equitable_intertwining_poly_unpartitioned_aux m numCells part Q hCheck cs (k + 1) w u hu with ⟨hRestMat, hRestPart⟩
    rw [hPowMat, hPowPart]
    exact ⟨congrArg (c * liftQuotientVec part (iterateVecOp (quotientMatVec Q (List.range numCells)) k w) u + ·) hRestMat,
           congrArg (c * liftQuotientVec part (iterateVecOp (quotientMatVec Q (List.range numCells)) k w) u + ·) hRestPart⟩

/-- **Theorem (`equitable_intertwining_poly_unpartitioned`)**:
End-to-end universal polynomial intertwining for both unpartitioned `matVec (List.range m.dim) m.entry`
and `partitionedMatVec` on any vertex $u < m.\text{dim}$ whenever
`checkEquitablePartition m numCells part Q = true`! -/
theorem equitable_intertwining_poly_unpartitioned
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (Q : Nat → Nat → Int)
    (coeffs : List Int)
    (w : Nat → Int)
    (u : Nat)
    (hCheck : checkEquitablePartition m numCells part Q = true)
    (hu : u < m.dim) :
    evalMatrixPoly (matVec (List.range m.dim) m.entry) coeffs (liftQuotientVec part w) u =
      liftQuotientVec part (evalMatrixPoly (quotientMatVec Q (List.range numCells)) coeffs w) u ∧
    evalMatrixPoly
        (partitionedMatVec m.entry (List.range numCells) (cellMembers (List.range m.dim) part))
        coeffs (liftQuotientVec part w) u =
      liftQuotientVec part (evalMatrixPoly (quotientMatVec Q (List.range numCells)) coeffs w) u :=
  equitable_intertwining_poly_unpartitioned_aux m numCells part Q hCheck coeffs 0 w u hu

/-! ## 6. Irreducibility & Residual Floor Certification (`evalEquitableResidualNormSq`) -/

/-- Row-sum residual $R(u, j) = \left(\sum_{v \in C_j} H_{u,v}\right) - Q_{\text{part}(u), j}$ measuring
the deviation of vertex $u$ from the equitable quotient entry $Q_{\text{part}(u), j}$. -/
def evalVertexCellResidual
    (m : IntMatrix)
    (part : Nat → Nat)
    (quotientEntry : Nat → Nat → Int)
    (u j : Nat) : Int :=
  let vertices := List.range m.dim
  let cJ := cellMembers vertices part j
  cellRowSum m.entry cJ u - quotientEntry (part u) j

/-- Total squared Frobenius / $\ell_2$ equitable residual norm:
$$\|R_{\text{eq}}(H, Q)\|_2^2 = \sum_{u=0}^{n-1} \sum_{j=0}^{r-1} \left(\sum_{v \in C_j} H_{u,v} - Q_{\text{part}(u), j}\right)^2.$$
Equals `0` if and only if $H$ satisfies the exact row-sum equitability condition with quotient $Q$;
when $> 0$, it certifies an irreducible symmetry-breaking residual floor. -/
def evalEquitableResidualNormSq
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (quotientEntry : Nat → Nat → Int) : Int :=
  let vertices := List.range m.dim
  let cells := List.range numCells
  sumIntOver (fun u =>
    sumIntOver (fun j =>
      let d := evalVertexCellResidual m part quotientEntry u j
      d * d) cells) vertices

/-- Theorem (`equitableResidualNormSq_nonneg`):
The equitable residual norm squared is universally non-negative (`0 ≤ evalEquitableResidualNormSq`)
for all matrices, partitions, and target quotients. -/
theorem equitableResidualNormSq_nonneg
    (m : IntMatrix)
    (numCells : Nat)
    (part : Nat → Nat)
    (quotientEntry : Nat → Nat → Int) :
    0 ≤ evalEquitableResidualNormSq m numCells part quotientEntry := by
  dsimp only [evalEquitableResidualNormSq]
  apply sumIntOver_nonneg
  intro u _
  apply sumIntOver_nonneg
  intro j _
  exact equitable_int_sq_nonneg (evalVertexCellResidual m part quotientEntry u j)

/-! ## 7. Canonical Showcase Models: Path $P_3$, Tied GQA Attention vs. Untied Residual Floor -/

/-- Adjacency matrix of the 3-vertex path graph $P_3$ ($0 - 1 - 2$):
$$H_{P_3} = \begin{pmatrix} 0 & 1 & 0 \\ 1 & 0 & 1 \\ 0 & 1 & 0 \end{pmatrix}.$$ -/
def path3Matrix : IntMatrix where
  dim  := 3
  rows := [[0, 1, 0], [1, 0, 1], [0, 1, 0]]

/-- Orbit partition of $P_3$ into outer endpoints $C_0 = \{0, 2\}$ and center hub $C_1 = \{1\}$. -/
def path3Part : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => 0

/-- $2 \times 2$ quotient matrix of $P_3$:
$$Q_{P_3} = \begin{pmatrix} 0 & 1 \\ 2 & 0 \end{pmatrix}, \qquad |C_0| \cdot Q_{0,1} = 2 \cdot 1 = 1 \cdot 2 = |C_1| \cdot Q_{1,0}.$$ -/
def path3Quotient : Nat → Nat → Int
  | 0, 1 => 1
  | 1, 0 => 2
  | _, _ => 0

/-- Grouped-Query Attention (GQA) tied 4-head / 4-token coupling operator with exact 2-group symmetry
($C_0 = \{0, 1\}$, $C_1 = \{2, 3\}$):
$$H_{\text{GQA}} = \begin{pmatrix} 2 & 1 & 3 & 3 \\ 1 & 2 & 3 & 3 \\ 3 & 3 & 4 & 2 \\ 3 & 3 & 2 & 4 \end{pmatrix}.$$ -/
def gqaTiedOperator : IntMatrix where
  dim  := 4
  rows :=
    [ [2, 1, 3, 3]
    , [1, 2, 3, 3]
    , [3, 3, 4, 2]
    , [3, 3, 2, 4] ]

/-- Untied / symmetry-broken operator where head $0$ has Perturbed cross-group couplings $[4, 4]$
while head $1$ has $[2, 2]$ into group $C_1$, breaking 1-WL equitability and inducing a non-zero
residual floor $\|R_{\text{eq}}\|_2^2 = 8 > 0$:
$$H_{\text{untied}} = \begin{pmatrix} 2 & 1 & 4 & 4 \\ 1 & 2 & 2 & 2 \\ 3 & 3 & 4 & 2 \\ 3 & 3 & 2 & 4 \end{pmatrix}.$$ -/
def gqaUntiedOperator : IntMatrix where
  dim  := 4
  rows :=
    [ [2, 1, 4, 4]
    , [1, 2, 2, 2]
    , [3, 3, 4, 2]
    , [3, 3, 2, 4] ]

/-- 2-group GQA partition: tokens $\{0, 1\} \in C_0$, tokens $\{2, 3\} \in C_1$. -/
def gqa2GroupPart : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 0

/-- Target $2 \times 2$ GQA quotient matrix $Q = \begin{pmatrix} 3 & 6 \\ 6 & 6 \end{pmatrix}$. -/
def gqa2GroupQuotient : Nat → Nat → Int
  | 0, 0 => 3
  | 0, 1 => 6
  | 1, 0 => 6
  | 1, 1 => 6
  | _, _ => 0

/-- **Theorem (`equitable_partition_and_residual_floor_sound`)**:
1. **Path $P_3$ Equitable Quotient & Handshake Identity**:
   `path3Matrix` is symmetric, passes `checkEquitablePartition`, is a stable 1-WL color refinement
   fixed point (`checkWl1ColorRefinementStable = true`), satisfies the asymmetric-degree handshake
   identity $|C_0| Q_{0,1} = 2 \cdot 1 = 1 \cdot 2 = |C_1| Q_{1,0}$ (`checkHandshakeIdentity = true`),
   and has zero equitable residual (`evalEquitableResidualNormSq = 0`).
2. **GQA Tied Operator (Exact Quotient Factorization)**:
   `gqaTiedOperator` passes `checkEquitablePartition` and `checkWl1ColorRefinementStable` with
   `evalEquitableResidualNormSq = 0`.
3. **Symmetry-Broken Untied Operator (Irreducible Residual Floor)**:
   `gqaUntiedOperator` is rejected by `checkEquitablePartition` (`= false`) and
   `checkWl1ColorRefinementStable` (`= false`), and exhibits a strictly positive irreducible
   residual floor `evalEquitableResidualNormSq = 8 > 0`. -/
theorem equitable_partition_and_residual_floor_sound :
    path3Matrix.isSymmetric = true ∧
    checkEquitablePartition path3Matrix 2 path3Part path3Quotient = true ∧
    checkWl1ColorRefinementStable path3Matrix 2 path3Part = true ∧
    checkHandshakeIdentity 3 2 path3Part path3Quotient = true ∧
    evalEquitableResidualNormSq path3Matrix 2 path3Part path3Quotient = 0 ∧
    checkEquitablePartition gqaTiedOperator 2 gqa2GroupPart gqa2GroupQuotient = true ∧
    checkWl1ColorRefinementStable gqaTiedOperator 2 gqa2GroupPart = true ∧
    evalEquitableResidualNormSq gqaTiedOperator 2 gqa2GroupPart gqa2GroupQuotient = 0 ∧
    checkEquitablePartition gqaUntiedOperator 2 gqa2GroupPart gqa2GroupQuotient = false ∧
    checkWl1ColorRefinementStable gqaUntiedOperator 2 gqa2GroupPart = false ∧
    evalEquitableResidualNormSq gqaUntiedOperator 2 gqa2GroupPart gqa2GroupQuotient = 8 := by
  decide +kernel

end Obend.Analysis
end
