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

/-- Matrix multiplication entry $(A B)_{u, v} = \sum_{w \in \text{indices}} A_{u, w} \cdot B_{w, v}$. -/
def matMulEntry (indices : List Nat) (A B : Nat → Nat → Int) (u v : Nat) : Int :=
  sumIntOver (fun w => A u w * B w v) indices

/-- Matrix addition entry $(A + B)_{u, v} = A_{u, v} + B_{u, v}$. -/
def matAddEntry (A B : Nat → Nat → Int) (u v : Nat) : Int :=
  A u v + B u v

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

/-- Concrete `IntMatrix` subtraction $(A - B)$. -/
def IntMatrix.sub (A B : IntMatrix) : IntMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => A.entry u v - B.entry u v)) }

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

/-- Multiply an `IntMatrix` $A$ by a column vector `v : List Int`. -/
def IntMatrix.mulVec (A : IntMatrix) (v : List Int) : List Int :=
  let indices := List.range A.dim
  indices.map (fun i =>
    sumIntOver (fun j => A.entry i j * listGetInt v j) indices)

/-- Matrix trace $\operatorname{tr}(A) = \sum_{i=0}^{n-1} A_{i, i}$. -/
def IntMatrix.trace (A : IntMatrix) : Int :=
  sumIntOver (fun i => A.entry i i) (List.range A.dim)

/-- Sum a `GaussianInt`-valued function over a list of indices `modes`. -/
def sumGaussianOver (f : Nat → GaussianInt) : List Nat → GaussianInt
  | [] => GaussianInt.zero
  | k :: ks => GaussianInt.add (f k) (sumGaussianOver f ks)

@[simp] theorem sumGaussianOver_nil (f : Nat → GaussianInt) :
    sumGaussianOver f [] = GaussianInt.zero := rfl

@[simp] theorem sumGaussianOver_cons (f : Nat → GaussianInt) (k : Nat) (ks : List Nat) :
    sumGaussianOver f (k :: ks) = GaussianInt.add (f k) (sumGaussianOver f ks) := rfl

/-- Exact $n \times n$ matrix over Gaussian integers $\mathbb{Z}[i]$ (`GaussianInt`), used for
unitary photonic transfer matrices and the faithful $4 \times 4$ Jordan–Wigner / Pauli spinor
representation of $Cl_4$. -/
structure GaussianMatrix where
  dim  : Nat
  rows : List (List GaussianInt)
  deriving DecidableEq, Repr

namespace GaussianMatrix

/-- Look up a `GaussianInt` at index `v` in a row by structural recursion (`0 Classical.choice`). -/
def listGetGaussian : List GaussianInt → Nat → GaussianInt
  | [], _ => GaussianInt.zero
  | x :: _, 0 => x
  | _ :: xs, v + 1 => listGetGaussian xs v

/-- Look up row `u` in a list of `GaussianInt` rows by structural recursion (`0 Classical.choice`). -/
def listGetGaussianRow : List (List GaussianInt) → Nat → List GaussianInt
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, u + 1 => listGetGaussianRow rs u

/-- Entry lookup $(u, v)$ in a `GaussianMatrix` (defaulting to `GaussianInt.zero`). -/
def entry (m : GaussianMatrix) (u v : Nat) : GaussianInt :=
  listGetGaussian (listGetGaussianRow m.rows u) v

/-- Pure boolean equality on `GaussianInt` (`0 Classical.choice`). -/
def gaussianIntBeq (z w : GaussianInt) : Bool :=
  decide (z.re = w.re) && decide (z.im = w.im)

theorem gaussianInt_eq_of_beq {z w : GaussianInt} (h : gaussianIntBeq z w = true) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      unfold gaussianIntBeq at h
      have hAnd := (Bool.and_eq_true _ _).mp h
      have hRe : zr = wr := of_decide_eq_true hAnd.1
      have hIm : zi = wi := of_decide_eq_true hAnd.2
      rw [hRe, hIm]

/-- Pure boolean equality on `List GaussianInt` (`0 Classical.choice`). -/
def listBeqGaussian : List GaussianInt → List GaussianInt → Bool
  | [], [] => true
  | x :: xs, y :: ys => gaussianIntBeq x y && listBeqGaussian xs ys
  | _, _ => false

theorem listBeqGaussian_eq : ∀ {xs ys : List GaussianInt}, listBeqGaussian xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | _ :: _, _ :: _, h => by
    have hAnd := (Bool.and_eq_true _ _).mp h
    rw [gaussianInt_eq_of_beq hAnd.1, listBeqGaussian_eq hAnd.2]

/-- Pure boolean equality on `List (List GaussianInt)` (`0 Classical.choice`). -/
def listBeqGaussianRows : List (List GaussianInt) → List (List GaussianInt) → Bool
  | [], [] => true
  | r1 :: rs1, r2 :: rs2 => listBeqGaussian r1 r2 && listBeqGaussianRows rs1 rs2
  | _, _ => false

theorem listBeqGaussianRows_eq :
    ∀ {rs1 rs2 : List (List GaussianInt)}, listBeqGaussianRows rs1 rs2 = true → rs1 = rs2
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | _ :: _, _ :: _, h => by
    have hAnd := (Bool.and_eq_true _ _).mp h
    rw [listBeqGaussian_eq hAnd.1, listBeqGaussianRows_eq hAnd.2]

/-- Pure boolean equality on `GaussianMatrix` (`0 Classical.choice`). -/
def beq (A B : GaussianMatrix) : Bool :=
  decide (A.dim = B.dim) && listBeqGaussianRows A.rows B.rows

theorem eq_of_beq {A B : GaussianMatrix} (h : GaussianMatrix.beq A B = true) : A = B := by
  cases A with
  | mk d1 r1 =>
    cases B with
    | mk d2 r2 =>
      unfold GaussianMatrix.beq at h
      have hAnd := (Bool.and_eq_true _ _).mp h
      have hDim : d1 = d2 := of_decide_eq_true hAnd.1
      have hRows : r1 = r2 := listBeqGaussianRows_eq hAnd.2
      rw [hDim, hRows]

/-- Identity matrix $I_n$ over $\mathbb{Z}[i]$. -/
def identity (dim : Nat) : GaussianMatrix :=
  let indices := List.range dim
  { dim  := dim
  , rows := indices.map (fun u =>
      indices.map (fun v => cond (u == v) GaussianInt.one GaussianInt.zero)) }

/-- Zero matrix $0_n$ over $\mathbb{Z}[i]$. -/
def zero (dim : Nat) : GaussianMatrix :=
  let indices := List.range dim
  { dim  := dim
  , rows := indices.map (fun _ => indices.map (fun _ => GaussianInt.zero)) }

/-- Matrix addition $A + B$ over $\mathbb{Z}[i]$. -/
def add (A B : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => GaussianInt.add (A.entry u v) (B.entry u v))) }

/-- Matrix subtraction $A - B$ over $\mathbb{Z}[i]$. -/
def sub (A B : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => GaussianInt.sub (A.entry u v) (B.entry u v))) }

/-- Scalar multiplication $c \cdot A$ ($c \in \mathbb{Z}$) over $\mathbb{Z}[i]$. -/
def scale (c : Int) (A : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => GaussianInt.scale c (A.entry u v))) }

/-- Matrix multiplication $A \cdot B$ over $\mathbb{Z}[i]$. -/
def mul (A B : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v =>
        sumGaussianOver (fun w => GaussianInt.mul (A.entry u w) (B.entry w v)) indices)) }

/-- Conjugate transpose (Hermitian adjoint) $A^\dagger$ over $\mathbb{Z}[i]$. -/
def conjTranspose (A : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => GaussianInt.conj (A.entry v u))) }

/-- Matrix trace $\operatorname{Tr}(A) = \sum_{u=0}^{\text{dim}-1} A_{u, u} \in \mathbb{Z}[i]$. -/
def trace (A : GaussianMatrix) : GaussianInt :=
  sumGaussianOver (fun u => A.entry u u) (List.range A.dim)

end GaussianMatrix

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

/-! ## 8. Block-Equitable Partitions & $d \times d$ Spinor Block Intertwining (`checkBlockEquitablePartition`, `block_equitable_intertwining_poly`) -/

/-- Extract the $d \times d$ spinor block at block row `p` and block column `q` from `A : IntMatrix`:
$$\operatorname{extractCellBlock}(A, d, p, q)_{\alpha, \beta} = A_{p \cdot d + \alpha,\; q \cdot d + \beta}.$$ -/
def extractCellBlock (A : IntMatrix) (d p q : Nat) : IntMatrix :=
  let subIdx := List.range d
  { dim  := d
  , rows := subIdx.map (fun alpha =>
      subIdx.map (fun beta => A.entry (p * d + alpha) (q * d + beta))) }

/-- Cell index assigned to $d \times d$ spinor block `p` by vertex partition `part`. -/
def blockCellOf (part : Nat → Nat) (d p : Nat) : Nat :=
  part (p * d)

/-- List of block indices in `blocks` belonging to cell `j`. -/
def blockCellMembers (blocks : List Nat) (part : Nat → Nat) (d j : Nat) : List Nat :=
  blocks.filter (fun q => blockCellOf part d q == j)

/-- Entry $(\alpha, \beta)$ of the $d \times d$ block row sum of block `p` into target block cell `blockCellJ`:
$$\left(\sum_{q \in \text{blockCellJ}} A_{[p, q]}\right)_{\alpha, \beta} = \sum_{q \in \text{blockCellJ}} A_{p \cdot d + \alpha,\; q \cdot d + \beta}.$$ -/
def blockCellRowSumEntry
    (A : IntMatrix) (d : Nat) (blockCellJ : List Nat) (p alpha beta : Nat) : Int :=
  sumIntOver (fun q => A.entry (p * d + alpha) (q * d + beta)) blockCellJ

/-- $d \times d$ matrix block row sum $\sum_{q \in \text{blockCellJ}} \operatorname{extractCellBlock}(A, d, p, q)$
of block `p` into target block cell `blockCellJ`. -/
def blockCellRowSum (A : IntMatrix) (d : Nat) (blockCellJ : List Nat) (p : Nat) : IntMatrix :=
  let subIdx := List.range d
  { dim  := d
  , rows := subIdx.map (fun alpha =>
      subIdx.map (fun beta => blockCellRowSumEntry A d blockCellJ p alpha beta)) }

/-- Computable **Block-Equitable Partition Checker** (`checkBlockEquitablePartition`):
Verifies that `A` (partitioned into `numBlocks = A.dim / d` spinor blocks of size $d \times d$ across `r` cells)
satisfies:
1. $d > 0$ and $A.\text{dim} = \text{numBlocks} \cdot d$,
2. Every vertex $p \cdot d + \alpha$ within block $p$ shares the block's cell assignment $\text{part}(p \cdot d) < r$,
3. Every cell $j < r$ contains at least one $d \times d$ block, and
4. For every block $p < \text{numBlocks}$ and target cell $j < r$, the $d \times d$ block row sum
   `blockCellRowSum A d (blockCellMembers blocks part d j) p` equals the $d \times d$ quotient block
   `Q (blockCellOf part d p) j`. -/
def checkBlockEquitablePartition
    (A : IntMatrix)
    (r d : Nat)
    (part : Nat → Nat)
    (Q : Nat → Nat → IntMatrix) : Bool :=
  let numBlocks := A.dim / d
  let blocks := List.range numBlocks
  let cells := List.range r
  let subIdx := List.range d
  decide (0 < d) &&
  decide (A.dim = numBlocks * d) &&
  blocks.all (fun p =>
    decide (blockCellOf part d p < r) &&
    subIdx.all (fun alpha => decide (part (p * d + alpha) = blockCellOf part d p))) &&
  cells.all (fun j => decide (1 ≤ (blockCellMembers blocks part d j).length)) &&
  blocks.all (fun p =>
    cells.all (fun j =>
      let cJ := blockCellMembers blocks part d j
      let qBlock := Q (blockCellOf part d p) j
      decide (qBlock.dim = d) &&
      subIdx.all (fun alpha =>
        subIdx.all (fun beta =>
          decide (blockCellRowSumEntry A d cJ p alpha beta = qBlock.entry alpha beta)))))

/-- Entry $(u, k)$ of the block characteristic matrix $P_{\text{block}}$ (`blockCharMatrix`):
for $u = p \cdot d + \alpha$ and $k = j \cdot d + \beta$, equals `1` when block $p$ belongs to cell $j$
and spinor component $\alpha = \beta$, and `0` otherwise ($I_d$ on matching cell blocks, $0_d$ elsewhere). -/
def blockCharEntry (part : Nat → Nat) (d u k : Nat) : Int :=
  if d == 0 then 0
  else
    let p := u / d
    let alpha := u % d
    let j := k / d
    let beta := k % d
    if blockCellOf part d p == j && alpha == beta then 1 else 0

/-- Block characteristic matrix $P_{\text{block}}$ of dimension $(\text{numBlocks} \cdot d) \times (r \cdot d)$
whose $(p, j)$ block is $I_d$ if $\text{part}(p \cdot d) = j$ and $0_d$ otherwise. -/
def blockCharMatrix (numBlocks r d : Nat) (part : Nat → Nat) : IntMatrix :=
  let rowsIdx := List.range (numBlocks * d)
  let colsIdx := List.range (r * d)
  { dim  := numBlocks * d
  , rows := rowsIdx.map (fun u =>
      colsIdx.map (fun k => blockCharEntry part d u k)) }

/-- Lift a block-quotient spinor vector $W : \text{Nat} \to \text{Nat} \to \text{Int}$ ($r$ cells of $d$-spinors)
to the full block-spinor space via $P_{\text{block}}$:
$$(P_{\text{block}} W)_{p, \alpha} = W(\text{blockCellOf}(\text{part}, d, p), \alpha).$$ -/
def liftBlockQuotientVec
    (part : Nat → Nat) (d : Nat) (W : Nat → Nat → Int) (p alpha : Nat) : Int :=
  W (blockCellOf part d p) alpha

/-- Full block-partitioned operator action on a block-spinor vector $V : \text{Nat} \to \text{Nat} \to \text{Int}$:
$$(A V)_{p, \alpha} = \sum_{j \in \text{cellIndices}} \sum_{q \in \text{blockCellOfJ}(j)} \sum_{\beta=0}^{d-1} A_{p \cdot d + \alpha,\; q \cdot d + \beta} \cdot V(q, \beta).$$ -/
def blockPartitionedMatVec
    (A : IntMatrix)
    (d : Nat)
    (cellIndices : List Nat)
    (blockCellOfJ : Nat → List Nat)
    (V : Nat → Nat → Int)
    (p alpha : Nat) : Int :=
  let subIdx := List.range d
  sumIntOver (fun j =>
    sumIntOver (fun q =>
      sumIntOver (fun beta =>
        A.entry (p * d + alpha) (q * d + beta) * V q beta) subIdx)
      (blockCellOfJ j))
    cellIndices

/-- Block-quotient operator action $B_{\text{block}} W$ on a quotient spinor vector $W : \text{Nat} \to \text{Nat} \to \text{Int}$:
$$(B_{\text{block}} W)_{i, \alpha} = \sum_{j \in \text{cellIndices}} \sum_{\beta=0}^{d-1} (Q_{i, j})_{\alpha, \beta} \cdot W(j, \beta).$$ -/
def blockQuotientMatVec
    (Q : Nat → Nat → IntMatrix)
    (d : Nat)
    (cellIndices : List Nat)
    (W : Nat → Nat → Int)
    (i alpha : Nat) : Int :=
  let subIdx := List.range d
  sumIntOver (fun j =>
    sumIntOver (fun beta =>
      (Q i j).entry alpha beta * W j beta) subIdx)
    cellIndices

/-- Congruence of `blockPartitionedMatVec` under pointwise equality of block-spinor vectors. -/
theorem blockPartitionedMatVec_congr
    (A : IntMatrix)
    (d : Nat)
    (cellIndices : List Nat)
    (blockCellOfJ : Nat → List Nat)
    (V1 V2 : Nat → Nat → Int)
    (p alpha : Nat)
    (hEq : ∀ j, j ∈ cellIndices → ∀ q, q ∈ blockCellOfJ j → ∀ beta, beta ∈ List.range d → V1 q beta = V2 q beta) :
    blockPartitionedMatVec A d cellIndices blockCellOfJ V1 p alpha =
      blockPartitionedMatVec A d cellIndices blockCellOfJ V2 p alpha := by
  dsimp only [blockPartitionedMatVec]
  apply sumIntOver_congr
  intro j hj
  apply sumIntOver_congr
  intro q hq
  apply sumIntOver_congr
  intro beta hbeta
  rw [hEq j hj q hq beta hbeta]

/-- Single-cell spinor block factorization lemma:
for any block cell `blockCellJ` where every block $q \in \text{blockCellJ}$ has `blockCellOf part d q = j`,
summing $\sum_{q \in \text{blockCellJ}} \sum_{\beta=0}^{d-1} A_{p d + \alpha, q d + \beta} (P_{\text{block}} W)_{q, \beta}$
interchanges via `doubleSum_swap` to $\sum_{\beta=0}^{d-1} (\text{blockCellRowSumEntry } A\, d\, \text{blockCellJ}\, p\, \alpha\, \beta) \cdot W(j, \beta)$. -/
theorem blockCellSum_liftBlockQuotientVec
    (A : IntMatrix)
    (part : Nat → Nat)
    (d : Nat)
    (W : Nat → Nat → Int)
    (p alpha j : Nat)
    (blockCellJ : List Nat)
    (hCell : ∀ q, q ∈ blockCellJ → blockCellOf part d q = j) :
    sumIntOver (fun q =>
      sumIntOver (fun beta =>
        A.entry (p * d + alpha) (q * d + beta) * liftBlockQuotientVec part d W q beta)
        (List.range d))
      blockCellJ =
    sumIntOver (fun beta =>
      blockCellRowSumEntry A d blockCellJ p alpha beta * W j beta)
      (List.range d) := by
  have hCongr :
      sumIntOver (fun q =>
        sumIntOver (fun beta =>
          A.entry (p * d + alpha) (q * d + beta) * liftBlockQuotientVec part d W q beta)
          (List.range d))
        blockCellJ =
      sumIntOver (fun q =>
        sumIntOver (fun beta =>
          A.entry (p * d + alpha) (q * d + beta) * W j beta)
          (List.range d))
        blockCellJ := by
    apply sumIntOver_congr
    intro q hq
    apply sumIntOver_congr
    intro beta _
    dsimp only [liftBlockQuotientVec]
    rw [hCell q hq]
  rw [hCongr]
  rw [doubleSum_swap (fun q beta => A.entry (p * d + alpha) (q * d + beta) * W j beta) blockCellJ (List.range d)]
  apply sumIntOver_congr
  intro beta _
  rw [sumIntOver_mul_right (fun q => A.entry (p * d + alpha) (q * d + beta)) (W j beta) blockCellJ]
  rfl

/-- **Theorem (`block_equitable_intertwining_step`)**:
**Fundamental One-Step Block-Equitable Intertwining Identity ($A P_{\text{block}} = P_{\text{block}} B_{\text{block}}$)**:
For any $d \times d$ block-equitable partition $(A, \text{part}, Q)$ across `cellIndices` and `blockCellOfJ`,
and any block-quotient spinor vector $W : \text{Nat} \to \text{Nat} \to \text{Int}$:
$$(A (P_{\text{block}} W))_{p, \alpha} = (P_{\text{block}} (B_{\text{block}} W))_{p, \alpha}.$$ -/
theorem block_equitable_intertwining_step
    (A : IntMatrix)
    (Q : Nat → Nat → IntMatrix)
    (part : Nat → Nat)
    (d : Nat)
    (cellIndices : List Nat)
    (blockCellOfJ : Nat → List Nat)
    (W : Nat → Nat → Int)
    (p alpha : Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ q, q ∈ blockCellOfJ j → blockCellOf part d q = j)
    (hEqRow : ∀ j, j ∈ cellIndices → ∀ beta, beta ∈ List.range d →
      blockCellRowSumEntry A d (blockCellOfJ j) p alpha beta = (Q (blockCellOf part d p) j).entry alpha beta) :
    blockPartitionedMatVec A d cellIndices blockCellOfJ (liftBlockQuotientVec part d W) p alpha =
      liftBlockQuotientVec part d (blockQuotientMatVec Q d cellIndices W) p alpha := by
  dsimp only [blockPartitionedMatVec, blockQuotientMatVec]
  apply sumIntOver_congr
  intro j hj
  rw [blockCellSum_liftBlockQuotientVec A part d W p alpha j (blockCellOfJ j) (hCells j hj)]
  apply sumIntOver_congr
  intro beta hbeta
  rw [hEqRow j hj beta hbeta]

/-- Iterate a block-spinor linear operator `op : (Nat → Nat → Int) → (Nat → Nat → Int)` $k$ times. -/
def iterateBlockVecOp
    (op : (Nat → Nat → Int) → (Nat → Nat → Int)) :
    Nat → (Nat → Nat → Int) → (Nat → Nat → Int)
  | 0, V => V
  | k + 1, V => op (iterateBlockVecOp op k V)

/-- **Theorem (`block_equitable_intertwining_power`)**:
**Multi-Step Power Block Intertwining Identity ($A^k P_{\text{block}} = P_{\text{block}} B_{\text{block}}^k$)**:
If $(A, \text{part}, Q)$ is $d \times d$ block-equitable across `cellIndices` and `blockCellOfJ`,
then for every power $k \in \mathbb{N}$ and every quotient spinor vector $W$:
$$(A^k (P_{\text{block}} W))_{p, \alpha} = (P_{\text{block}} (B_{\text{block}}^k W))_{p, \alpha}.$$ -/
theorem block_equitable_intertwining_power
    (A : IntMatrix)
    (Q : Nat → Nat → IntMatrix)
    (part : Nat → Nat)
    (d : Nat)
    (cellIndices : List Nat)
    (blockCellOfJ : Nat → List Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ q, q ∈ blockCellOfJ j → blockCellOf part d q = j)
    (hEqAll : ∀ p alpha, ∀ j, j ∈ cellIndices → ∀ beta, beta ∈ List.range d →
      blockCellRowSumEntry A d (blockCellOfJ j) p alpha beta = (Q (blockCellOf part d p) j).entry alpha beta) :
    ∀ (k : Nat) (W : Nat → Nat → Int) (p alpha : Nat),
      iterateBlockVecOp (blockPartitionedMatVec A d cellIndices blockCellOfJ) k (liftBlockQuotientVec part d W) p alpha =
        liftBlockQuotientVec part d (iterateBlockVecOp (blockQuotientMatVec Q d cellIndices) k W) p alpha
  | 0, _, _, _ => rfl
  | k + 1, W, p, alpha => by
    dsimp only [iterateBlockVecOp]
    have hCongr :
        blockPartitionedMatVec A d cellIndices blockCellOfJ
          (iterateBlockVecOp (blockPartitionedMatVec A d cellIndices blockCellOfJ) k (liftBlockQuotientVec part d W)) p alpha =
        blockPartitionedMatVec A d cellIndices blockCellOfJ
          (liftBlockQuotientVec part d (iterateBlockVecOp (blockQuotientMatVec Q d cellIndices) k W)) p alpha := by
      apply blockPartitionedMatVec_congr
      intro j _ q _ beta _
      exact block_equitable_intertwining_power A Q part d cellIndices blockCellOfJ hCells hEqAll k W q beta
    rw [hCongr]
    exact block_equitable_intertwining_step A Q part d cellIndices blockCellOfJ
      (iterateBlockVecOp (blockQuotientMatVec Q d cellIndices) k W) p alpha hCells (hEqAll p alpha)

/-- Auxiliary evaluator for block-spinor matrix polynomial $\sum_{m} c_m (A^{k+m} V)_{p, \alpha}$. -/
def evalBlockMatrixPolyAux
    (op : (Nat → Nat → Int) → (Nat → Nat → Int))
    (k : Nat) : List Int → (Nat → Nat → Int) → (Nat → Nat → Int)
  | [], _ => fun _ _ => 0
  | c :: cs, V => fun p alpha =>
      c * iterateBlockVecOp op k V p alpha + evalBlockMatrixPolyAux op (k + 1) cs V p alpha

/-- Evaluate the matrix polynomial $p(A) V = \sum_{k} c_k A^k V$ on a block-spinor vector $V$ at $(p, \alpha)$. -/
def evalBlockMatrixPoly
    (op : (Nat → Nat → Int) → (Nat → Nat → Int))
    (coeffs : List Int)
    (V : Nat → Nat → Int)
    (p alpha : Nat) : Int :=
  evalBlockMatrixPolyAux op 0 coeffs V p alpha

/-- Helper lemma: `evalBlockMatrixPolyAux` intertwines block-equitable lifts from any power offset `k`. -/
theorem block_equitable_intertwining_poly_aux
    (A : IntMatrix)
    (Q : Nat → Nat → IntMatrix)
    (part : Nat → Nat)
    (d : Nat)
    (cellIndices : List Nat)
    (blockCellOfJ : Nat → List Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ q, q ∈ blockCellOfJ j → blockCellOf part d q = j)
    (hEqAll : ∀ p alpha, ∀ j, j ∈ cellIndices → ∀ beta, beta ∈ List.range d →
      blockCellRowSumEntry A d (blockCellOfJ j) p alpha beta = (Q (blockCellOf part d p) j).entry alpha beta) :
    ∀ (coeffs : List Int) (k : Nat) (W : Nat → Nat → Int) (p alpha : Nat),
      evalBlockMatrixPolyAux (blockPartitionedMatVec A d cellIndices blockCellOfJ) k coeffs
        (liftBlockQuotientVec part d W) p alpha =
      liftBlockQuotientVec part d
        (evalBlockMatrixPolyAux (blockQuotientMatVec Q d cellIndices) k coeffs W) p alpha
  | [], _, _, _, _ => rfl
  | c :: cs, k, W, p, alpha => by
    dsimp only [evalBlockMatrixPolyAux, liftBlockQuotientVec]
    rw [block_equitable_intertwining_power A Q part d cellIndices blockCellOfJ hCells hEqAll k W p alpha]
    rw [block_equitable_intertwining_poly_aux A Q part d cellIndices blockCellOfJ hCells hEqAll cs (k + 1) W p alpha]
    rfl

/-- **Theorem (`block_equitable_intertwining_poly`)**:
**Universal Block-Equitable Polynomial Intertwining Theorem ($p(A) P_{\text{block}} = P_{\text{block}} p(B_{\text{block}})$)**:
For any polynomial $p(x) = \sum_{k} c_k x^k$ (`coeffs : List Int`), any block-equitable partition
$(A, \text{part}, Q)$ of $r$ cells of $d \times d$ spinor blocks across `cellIndices` and `blockCellOfJ`,
any block-quotient spinor vector $W : \text{Nat} \to \text{Nat} \to \text{Int}$, and any block $p$ and
spinor index $\alpha \in \{0, \dots, d-1\}$:
$$\left(p(A) (P_{\text{block}} W)\right)_{p, \alpha} = \left(P_{\text{block}} \left(p(B_{\text{block}}) W\right)\right)_{p, \alpha} = \left(p(B_{\text{block}}) W\right)_{\text{blockCellOf}(\text{part}, d, p), \alpha}.$$ -/
theorem block_equitable_intertwining_poly
    (A : IntMatrix)
    (Q : Nat → Nat → IntMatrix)
    (part : Nat → Nat)
    (d : Nat)
    (cellIndices : List Nat)
    (blockCellOfJ : Nat → List Nat)
    (coeffs : List Int)
    (W : Nat → Nat → Int)
    (p alpha : Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ q, q ∈ blockCellOfJ j → blockCellOf part d q = j)
    (hEqAll : ∀ p alpha, ∀ j, j ∈ cellIndices → ∀ beta, beta ∈ List.range d →
      blockCellRowSumEntry A d (blockCellOfJ j) p alpha beta = (Q (blockCellOf part d p) j).entry alpha beta) :
    evalBlockMatrixPoly (blockPartitionedMatVec A d cellIndices blockCellOfJ) coeffs
      (liftBlockQuotientVec part d W) p alpha =
    liftBlockQuotientVec part d
      (evalBlockMatrixPoly (blockQuotientMatVec Q d cellIndices) coeffs W) p alpha :=
  block_equitable_intertwining_poly_aux A Q part d cellIndices blockCellOfJ hCells hEqAll coeffs 0 W p alpha

/-! ## 9. Faddeev–LeVerrier Adjugate Crosstalk Compensation & 2-Boson Hong–Ou–Mandel Permanents -/

/-- Auxiliary Faddeev–LeVerrier recurrence returning the penultimate matrix $M_n = B_{n-1} + c_1 I_n$
and the constant term $c_0 = \det(-A)$ of $\det(\lambda I - A)$. -/
def faddeevAdjugateAux (A B : IntMatrix) (cPrev : Int) (k : Nat) : Nat → IntMatrix × Int
  | 0 => (B, cPrev)
  | rem + 1 =>
    let mCurr := B.add (IntMatrix.scaledIdentity A.dim cPrev)
    let bNext := A.mul mCurr
    let cCurr := -(bNext.trace) / (k : Int)
    match rem with
    | 0 => (mCurr, cCurr)
    | _ => faddeevAdjugateAux A bNext cCurr (k + 1) rem

/-- **Faddeev–LeVerrier Exact Classical Adjugate & Determinant** (`faddeevAdjugateAndDet`):
For any $n \times n$ integer matrix $A$, computes `(adj(A), det(A))` via the division-free
Faddeev–LeVerrier trace recurrence such that:
$$A \cdot \operatorname{adj}(A) = \operatorname{adj}(A) \cdot A = \det(A) \cdot I_n.$$ -/
def faddeevAdjugateAndDet (A : IntMatrix) : IntMatrix × Int :=
  if A.dim == 0 then (IntMatrix.zero 0, 1)
  else
    let (mN, c0) := faddeevAdjugateAux A (IntMatrix.zero A.dim) 1 1 A.dim
    let sign : Int := if A.dim % 2 == 0 then -1 else 1
    (mN.scale sign, (-c0) * sign)

/-- Multi-channel thermo-optic phase-shifter array specification (`ThermoOpticPhaseShifter`):
* `numChannels`: number of coupled waveguide TiN/doped-Si micro-heaters $r$,
* `crosstalkMatrix`: $r \times r$ integer-scaled thermal conductance / crosstalk matrix $G_{\text{th}}$,
* `maxPowerMw`: per-channel maximum heater power budget in milliwatts. -/
structure ThermoOpticPhaseShifter where
  numChannels     : Nat
  crosstalkMatrix : IntMatrix
  maxPowerMw      : Nat
  deriving DecidableEq, Repr

/-- **Exact Adjugate Pre-Distortion for Thermo-Optic Crosstalk** (`compensateThermalCrosstalk`):
Given an $r \times r$ thermal crosstalk matrix $G_{\text{th}}$ and target phase vector $\phi_{\text{target}}$,
computes `(u_comp, det(G_th))` where $u_{\text{comp}} = \operatorname{adj}(G_{\text{th}}) \cdot \phi_{\text{target}}$,
so that the physical thermally-coupled phase response is strictly crosstalk-free:
$$G_{\text{th}} \cdot u_{\text{comp}} = \det(G_{\text{th}}) \cdot \phi_{\text{target}}.$$ -/
def compensateThermalCrosstalk (G_th : IntMatrix) (phiTarget : List Int) : List Int × Int :=
  let res := faddeevAdjugateAndDet G_th
  (res.1.mulVec phiTarget, res.2)

/-- Canonical $4 \times 4$ tridiagonal nearest-neighbor silicon thermo-optic crosstalk matrix $G_{\text{th}}$
(diagonal self-heating gain $10$, nearest-neighbor diffusive thermal coupling $2$, next-nearest $1$):
$$G_{\text{th}} = \begin{pmatrix} 10 & 2 & 1 & 0 \\ 2 & 10 & 2 & 1 \\ 1 & 2 & 10 & 2 \\ 0 & 1 & 2 & 10 \end{pmatrix}.$$ -/
def goldenThermalCrosstalk4x4 : IntMatrix where
  dim  := 4
  rows :=
    [ [10, 2, 1, 0]
    , [2, 10, 2, 1]
    , [1, 2, 10, 2]
    , [0, 1, 2, 10] ]

/-- Explicit Faddeev–LeVerrier adjugate and determinant of `goldenThermalCrosstalk4x4`. -/
theorem goldenThermalCrosstalk4x4_adj_eq :
    faddeevAdjugateAndDet goldenThermalCrosstalk4x4 =
      ({ dim := 4
       , rows :=
           [ [918, -174, -63, 30]
           , [-174, 950, -160, -63]
           , [-63, -160, 950, -174]
           , [30, -63, -174, 918] ] }, 8769) := by
  decide +kernel

/-- **Theorem (`faddeevAdjugate_cancels_crosstalk_4x4`)**:
For the $4 \times 4$ thermo-optic crosstalk matrix `goldenThermalCrosstalk4x4`, `faddeevAdjugateAndDet`
synthesizes `(adjG, detG)` with $\det(G_{\text{th}}) = 8769 > 0$ such that both left and right
matrix products cancel all off-diagonal thermal crosstalk identically:
$$G_{\text{th}} \cdot \operatorname{adj}(G_{\text{th}}) = \operatorname{adj}(G_{\text{th}}) \cdot G_{\text{th}} = \det(G_{\text{th}}) \cdot I_4.$$ -/
theorem faddeevAdjugate_cancels_crosstalk_4x4 :
    let res := faddeevAdjugateAndDet goldenThermalCrosstalk4x4
    res.2 = 8769 ∧
    goldenThermalCrosstalk4x4.mul res.1 = IntMatrix.scaledIdentity 4 res.2 ∧
    res.1.mul goldenThermalCrosstalk4x4 = IntMatrix.scaledIdentity 4 res.2 := by
  decide +kernel

/-- **Theorem (`compensateThermalCrosstalk_exact_4x4`)**:
For ANY 4-channel target phase vector $\phi_{\text{target}} = [\phi_0, \phi_1, \phi_2, \phi_3] \in \mathbb{Z}^4$,
applying `goldenThermalCrosstalk4x4` to the pre-distorted heater drive
`u_comp = (compensateThermalCrosstalk goldenThermalCrosstalk4x4 [phi0, phi1, phi2, phi3]).1`
recovers the exact crosstalk-free scaled target phase vector
`[detG * phi0, detG * phi1, detG * phi2, detG * phi3]`! -/
theorem compensateThermalCrosstalk_exact_4x4 (phi0 phi1 phi2 phi3 : Int) :
    let target := [phi0, phi1, phi2, phi3]
    let res := compensateThermalCrosstalk goldenThermalCrosstalk4x4 target
    goldenThermalCrosstalk4x4.mulVec res.1 =
      [res.2 * phi0, res.2 * phi1, res.2 * phi2, res.2 * phi3] := by
  dsimp only [compensateThermalCrosstalk]
  rw [goldenThermalCrosstalk4x4_adj_eq]
  dsimp only [IntMatrix.mulVec, goldenThermalCrosstalk4x4, IntMatrix.entry, listGetInt,
    sumIntOver, List.range, List.range.loop, List.map,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  congr 1
  · omega
  · congr 1
    · omega
    · congr 1
      · omega
      · congr 1
        · omega

/-- **2-Boson Matrix Permanent** (`twoBosonPermanent`):
Evaluates the exact $2 \times 2$ permanent governing 2-photon bosonic transition amplitude from
input waveguide modes $(c, d)$ to output waveguide modes $(a, b)$ under single-photon unitary $U$:
$$\operatorname{perm}(U_{[a, b;\, c, d]}) = U_{a, c} U_{b, d} + U_{a, d} U_{b, c} \in \mathbb{Z}[i].$$ -/
def twoBosonPermanent (U : GaussianMatrix) (a b c d : Fin 4) : GaussianInt :=
  GaussianInt.add
    (GaussianInt.mul (U.entry a.val c.val) (U.entry b.val d.val))
    (GaussianInt.mul (U.entry a.val d.val) (U.entry b.val c.val))

/-- Scaled $4 \times 4$ 50:50 lossless symmetric directional coupler (beam-splitter) unitary over $\mathbb{Z}[i]$
acting on waveguide modes `a` and `b` ($U_{a,a} = U_{b,b} = 1$, $U_{a,b} = U_{b,a} = i$, and identity
on spectator modes; returns `GaussianMatrix.zero 4` in the degenerate case `a = b`). -/
def beamSplitter5050 (a b : Fin 4) : GaussianMatrix :=
  if a.val == b.val then
    GaussianMatrix.zero 4
  else
    let indices := List.range 4
    { dim  := 4
    , rows := indices.map (fun u =>
        indices.map (fun v =>
          if (u == a.val && v == a.val) || (u == b.val && v == b.val) then
            GaussianInt.one
          else if (u == a.val && v == b.val) || (u == b.val && v == a.val) then
            GaussianInt.iUnit
          else if u == v then
            GaussianInt.one
          else
            GaussianInt.zero)) }

/-- **Theorem (`hong_ou_mandel_bunching_exact`)**:
**Exact Hong–Ou–Mandel (HOM) Two-Boson Coincidence Extinction Theorem**:
For any pair of waveguide modes $a, b \in \text{Fin } 4$, injecting one photon into mode $a$ and
one photon into mode $b$ of a symmetric 50:50 beam-splitter `beamSplitter5050 a b` yields identically
zero $(1, 1)$ anti-bunched coincidence amplitude (`twoBosonPermanent (beamSplitter5050 a b) a b a b = GaussianInt.zero`),
because the transmitted-transmitted amplitude ($1 \cdot 1 = +1$) and reflected-reflected amplitude
($i \cdot i = -1$) interfere destructively ($+1 + (-1) = 0$)! -/
theorem hong_ou_mandel_bunching_exact (a b : Fin 4) :
    twoBosonPermanent (beamSplitter5050 a b) a b a b = GaussianInt.zero := by
  revert a b
  decide +kernel

/-- Commutativity of Gaussian integer addition (`z + w = w + z`). -/
theorem gaussianInt_add_comm (z w : GaussianInt) :
    GaussianInt.add z w = GaussianInt.add w z := by
  cases z
  cases w
  dsimp only [GaussianInt.add]
  congr 1 <;> omega

/-- Commutativity of Gaussian integer multiplication (`z * w = w * z`). -/
theorem gaussianInt_mul_comm (z w : GaussianInt) :
    GaussianInt.mul z w = GaussianInt.mul w z := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      dsimp only [GaussianInt.mul]
      rw [Int.mul_comm zr wr, Int.mul_comm zi wi, Int.mul_comm zr wi, Int.mul_comm zi wr, Int.add_comm]

/-- **Theorem (`twoBosonPermanent_bose_symmetry`)**:
**Universal Bosonic Exchange Symmetry of the 2-Boson Permanent**:
For EVERY $4 \times 4$ unitary/transfer matrix `U : GaussianMatrix` and ALL mode indices $a, b, c, d \in \text{Fin } 4$,
the 2-boson permanent is invariant under exchanging the output bosons ($a \leftrightarrow b$) and
under exchanging the input bosons ($c \leftrightarrow d$):
$$\operatorname{perm}(U_{[b,a;\, c,d]}) = \operatorname{perm}(U_{[a,b;\, c,d]}) \;\wedge\;
  \operatorname{perm}(U_{[a,b;\, d,c]}) = \operatorname{perm}(U_{[a,b;\, c,d]}).$$ -/
theorem twoBosonPermanent_bose_symmetry (U : GaussianMatrix) (a b c d : Fin 4) :
    twoBosonPermanent U b a c d = twoBosonPermanent U a b c d ∧
    twoBosonPermanent U a b d c = twoBosonPermanent U a b c d := by
  dsimp only [twoBosonPermanent]
  constructor
  · rw [gaussianInt_mul_comm (U.entry b.val c.val) (U.entry a.val d.val)]
    rw [gaussianInt_mul_comm (U.entry b.val d.val) (U.entry a.val c.val)]
    exact gaussianInt_add_comm
      (GaussianInt.mul (U.entry a.val d.val) (U.entry b.val c.val))
      (GaussianInt.mul (U.entry a.val c.val) (U.entry b.val d.val))
  · exact gaussianInt_add_comm
      (GaussianInt.mul (U.entry a.val d.val) (U.entry b.val c.val))
      (GaussianInt.mul (U.entry a.val c.val) (U.entry b.val d.val))

/-- 2-Boson two-particle Hamiltonian $H^{(2)} = H_{K_2} \otimes I_2 + I_2 \otimes H_{K_2}$ on the
4-state 2-photon basis $\{|0,0\rangle, |0,1\rangle, |1,0\rangle, |1,1\rangle\}$:
$$H^{(2)} = \begin{pmatrix} 0 & 1 & 1 & 0 \\ 1 & 0 & 0 & 1 \\ 1 & 0 & 0 & 1 \\ 0 & 1 & 1 & 0 \end{pmatrix}.$$ -/
def twoBosonHamiltonian : IntMatrix where
  dim  := 4
  rows :=
    [ [0, 1, 1, 0]
    , [1, 0, 0, 1]
    , [1, 0, 0, 1]
    , [0, 1, 1, 0] ]

/-- Symmetrized Fock-space partition of the 4-state 2-boson space into the 3 bosonic occupation
sectors $C_0 = \{|2, 0\rangle\} = \{0\}$, $C_1 = \{|0,1\rangle, |1,0\rangle\} = \{1, 2\}$, and
$C_2 = \{|0, 2\rangle\} = \{3\}$. -/
def twoBosonPart : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 0

/-- $3 \times 3$ bosonic Fock-space quotient matrix of `twoBosonHamiltonian`:
$$Q_{\text{2-boson}} = \begin{pmatrix} 0 & 2 & 0 \\ 1 & 0 & 1 \\ 0 & 2 & 0 \end{pmatrix}.$$ -/
def twoBosonQuotient : Nat → Nat → Int
  | 0, 1 => 2
  | 1, 0 => 1
  | 1, 2 => 1
  | 2, 1 => 2
  | _, _ => 0

/-- **Theorem (`twoBoson_equitable_intertwining_poly`)**:
The 4-state 2-boson Hamiltonian $H^{(2)} = H_{K_2} \otimes I + I \otimes H_{K_2}$ is an exact
equitable partition over the 3-sector bosonic Fock partition `twoBosonPart` (`checkEquitablePartition = true`),
and for EVERY polynomial $p(x) = \sum_k c_k x^k$ (`coeffs : List Int`), EVERY Fock-sector wavevector
`w : Nat → Int`, and EVERY 2-photon basis state `u < 4`, the 2-boson polynomial evolution intertwines
with the 3-mode Fock quotient `twoBosonQuotient`! -/
theorem twoBoson_equitable_intertwining_poly
    (coeffs : List Int) (w : Nat → Int) (u : Nat) (hu : u < 4) :
    checkEquitablePartition twoBosonHamiltonian 3 twoBosonPart twoBosonQuotient = true ∧
    evalMatrixPoly (matVec (List.range 4) twoBosonHamiltonian.entry) coeffs (liftQuotientVec twoBosonPart w) u =
      liftQuotientVec twoBosonPart (evalMatrixPoly (quotientMatVec twoBosonQuotient (List.range 3)) coeffs w) u := by
  have hCheck : checkEquitablePartition twoBosonHamiltonian 3 twoBosonPart twoBosonQuotient = true := by
    decide +kernel
  exact ⟨hCheck, (equitable_intertwining_poly_unpartitioned twoBosonHamiltonian 3 twoBosonPart twoBosonQuotient coeffs w u hCheck hu).1⟩

end Obend.Analysis
end
