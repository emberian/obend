module
/-
# Obend.Hardware.QuantumMatter — IBM Heavy-Hex $C_{12}$ Lattice, Majorana-1 Clifford $Cl_4$ Parity Sector & `StrictOpenHypergraph` Equitable Quotient Intertwining

Mechanizes:
1. **IBM Heavy-Hex $C_{12}$ Lattice & Microsoft Majorana-1 Tetron Parity-Sector Noise Immunity**:
   - 12-qubit Heavy-Hex ring unit cell $C_{12}$ under its 7-cell antipodal distance partition and
     2-cell corner-vs-bridge partition, plus the 4-Majorana $Cl_4$ fermion parity projector system
     ($C_{\text{even}} = \{0, 1\}$, $C_{\text{odd}} = \{2, 3\}$).
   - `symmetry_preserving_noise_zero_leakage`, `breakingScore_zero_iff_equitable`, and
     `perturbative_disorder_leakage_bound`: any perturbation commuting with an equitable / parity
     partition produces identically zero leakage out of the quotient subspace, whereas parity-breaking
     quasiparticle poisoning induces a strictly positive leakage bound.
2. **Symmetric `StrictOpenHypergraph` Equitable Quotient Compression (`quotientOpenHypergraph_intertwines_eval_and_adjoint`)**:
   - Forward evaluation and reverse-mode `compileGraphAdjoint` differentiation of
     `buildSymmetric4LaneHypergraph` factor through `quotientOpenHypergraph`.
-/
public import Obend.Hardware.OpenHypergraph
public import Obend.Leaf.Specialize
public import Obend.Analysis.Equitable
public import Obend.Analysis.QuantumWalk
public section

namespace Obend.Hardware.QuantumMatter
open Obend.Hardware.OpenHypergraph
open Obend.Leaf
open Obend.Slot
open Obend.Slot.World
open Obend.Core.Term
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. IBM Heavy-Hex $C_{12}$ Unit-Cell Lattice & Microsoft Majorana-1 Tetron Parity Sector -/

/-- Adjacency matrix of the 12-qubit **IBM Heavy-Hex** ring unit cell $C_{12}$ ($0 - 1 - \dots - 11 - 0$). -/
def heavyHexC12RingMatrix : IntMatrix where
  dim  := 12
  rows :=
    [ [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] -- 0 (corner)
    , [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] -- 1 (bridge)
    , [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] -- 2 (bridge)
    , [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0] -- 3 (corner)
    , [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0] -- 4 (bridge)
    , [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0] -- 5 (bridge)
    , [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0] -- 6 (antipodal corner)
    , [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] -- 7 (bridge)
    , [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0] -- 8 (bridge)
    , [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0] -- 9 (corner)
    , [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1] -- 10 (bridge)
    , [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] -- 11 (bridge)
    ]

/-- 7-cell antipodal reflection/distance partition of the Heavy-Hex $C_{12}$ unit cell:
$C_0 = \{0\}$, $C_1 = \{1, 11\}$, $C_2 = \{2, 10\}$, $C_3 = \{3, 9\}$, $C_4 = \{4, 8\}$,
$C_5 = \{5, 7\}$, $C_6 = \{6\}$. -/
def heavyHexC12DistancePart : Nat → Nat
  | 0  => 0
  | 1  => 1
  | 2  => 2
  | 3  => 3
  | 4  => 4
  | 5  => 5
  | 6  => 6
  | 7  => 5
  | 8  => 4
  | 9  => 3
  | 10 => 2
  | 11 => 1
  | _  => 0

/-- $7 \times 7$ tridiagonal quotient matrix of the Heavy-Hex $C_{12}$ distance partition:
endpoints $C_0, C_6$ have out-degree $2$ into $C_1, C_5$, while interior cells have degree $1$
left and $1$ right. -/
def heavyHexC12DistanceQuotient : Nat → Nat → Int
  | 0, 1 => 2
  | 1, 0 => 1
  | 1, 2 => 1
  | 2, 1 => 1
  | 2, 3 => 1
  | 3, 2 => 1
  | 3, 4 => 1
  | 4, 3 => 1
  | 4, 5 => 1
  | 5, 4 => 1
  | 5, 6 => 1
  | 6, 5 => 2
  | _, _ => 0

/-- Heavy-Hex $C_{12}$ effective Hamiltonian incorporating the degree-3 corner Z-shift ($+3$ on corners
$\{0, 3, 6, 9\}$) vs. degree-2 bridge qubits ($+2$ on $\{1, 2, 4, 5, 7, 8, 10, 11\}$) plus
nearest-neighbor bridge couplings. -/
def heavyHexC12CornerBridgeMatrix : IntMatrix where
  dim  := 12
  rows :=
    [ [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] -- 0 (corner: self 3, 2 bridges)
    , [1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] -- 1 (bridge: self 2, 1 corner, 1 bridge)
    , [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0] -- 2 (bridge: self 2, 1 corner, 1 bridge)
    , [0, 0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0] -- 3 (corner)
    , [0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0] -- 4 (bridge)
    , [0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0] -- 5 (bridge)
    , [0, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 0] -- 6 (corner)
    , [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0] -- 7 (bridge)
    , [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0] -- 8 (bridge)
    , [0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0] -- 9 (corner)
    , [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1] -- 10 (bridge)
    , [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2] -- 11 (bridge)
    ]

/-- 2-cell corner-vs-bridge partition of Heavy-Hex $C_{12}$:
$C_0 = \{0, 3, 6, 9\}$ ($4$ degree-3 corner qubits) and $C_1 = \{1, 2, 4, 5, 7, 8, 10, 11\}$ ($8$ degree-2 bridge qubits). -/
def heavyHexC12CornerBridgePart : Nat → Nat
  | 0 => 0
  | 3 => 0
  | 6 => 0
  | 9 => 0
  | _ => 1

/-- $2 \times 2$ quotient matrix of the Heavy-Hex corner-vs-bridge partition:
$Q = \begin{pmatrix} 3 & 2 \\ 1 & 3 \end{pmatrix}$ with handshake identity $|C_0| Q_{0,1} = 4 \cdot 2 = 8 \cdot 1 = |C_1| Q_{1,0}$. -/
def heavyHexC12CornerBridgeQuotient : Nat → Nat → Int
  | 0, 0 => 3
  | 0, 1 => 2
  | 1, 0 => 1
  | 1, 1 => 3
  | _, _ => 0

/-- **Microsoft Majorana-1 Tetron** 4-state Hamiltonian partitioned into the even fermion-parity
computational sector $C_{\text{even}} = \{0, 1\}$ and odd fermion-parity sector $C_{\text{odd}} = \{2, 3\}$:
$$H_{\text{tetron}} = \begin{pmatrix} 2 & 1 & 0 & 0 \\ 1 & 2 & 0 & 0 \\ 0 & 0 & -2 & 1 \\ 0 & 0 & 1 & -2 \end{pmatrix}.$$ -/
def majoranaTetronHamiltonian : IntMatrix where
  dim  := 4
  rows :=
    [ [2, 1, 0, 0]
    , [1, 2, 0, 0]
    , [0, 0, -2, 1]
    , [0, 0, 1, -2] ]

/-- Symmetry-preserving (parity-conserving) Majorana-1 braiding / dephasing perturbation $\Delta H_{\text{sym}}$
that commutes with total fermion parity $P_{\text{tot}} = -\gamma_1 \gamma_2 \gamma_3 \gamma_4$:
$$\Delta H_{\text{sym}} = \begin{pmatrix} 1 & 2 & 0 & 0 \\ 2 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \end{pmatrix}.$$ -/
def majoranaParityPreserveNoise : IntMatrix where
  dim  := 4
  rows :=
    [ [1, 2, 0, 0]
    , [2, 1, 0, 0]
    , [0, 0, 1, 0]
    , [0, 0, 0, 1] ]

/-- Parity-breaking quasiparticle-poisoning perturbation $\Delta H_{\text{poison}}$ that couples
state $0 \in C_{\text{even}}$ to $C_{\text{odd}}$ asymmetrically, breaking parity conservation and
inducing leakage into the odd-parity sector:
$$\Delta H_{\text{poison}} = \begin{pmatrix} 0 & 0 & 1 & 1 \\ 0 & 0 & -1 & -1 \\ 1 & -1 & 0 & 0 \\ 1 & -1 & 0 & 0 \end{pmatrix}.$$ -/
def majoranaQuasiparticlePoisonNoise : IntMatrix where
  dim  := 4
  rows :=
    [ [0, 0, 1, 1]
    , [0, 0, -1, -1]
    , [1, -1, 0, 0]
    , [1, -1, 0, 0] ]

/-- Fermion-parity partition of the Majorana-1 tetron:
$C_{\text{even}} = \{0, 1\} \mapsto 0$, $C_{\text{odd}} = \{2, 3\} \mapsto 1$. -/
def majoranaParityPart : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 0

/-- Nominal $2 \times 2$ block-diagonal parity quotient of `majoranaTetronHamiltonian`:
$Q_{\text{tetron}} = \begin{pmatrix} 3 & 0 \\ 0 & -1 \end{pmatrix}$. -/
def majoranaTetronQuotient : Nat → Nat → Int
  | 0, 0 => 3
  | 1, 1 => -1
  | _, _ => 0

/-- $2 \times 2$ block-diagonal parity quotient of `majoranaParityPreserveNoise`:
$\Delta Q_{\text{sym}} = \begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def majoranaNoiseSymQuotient : Nat → Nat → Int
  | 0, 0 => 3
  | 1, 1 => 1
  | _, _ => 0

/-! ## 4. True 16-Dimensional Clifford Algebra $Cl_4$ & Majorana Parity Selection Theorem

`Obend.Teeth.Hardware.CliffordKernel` decides three universal theorems about this algebra in the
kernel (the spinor homomorphism on all 256 blade pairs, parity of the braid gates, the Artin
relation) without `import all`, so the kernel there has to unfold the product, the spinor
representation and the braid gates down to integers. The definitions on that path that compute
(pattern matches, the product, the coefficient sums, the generator lookup, the parity check) carry the expose
attribute; the one-line shorthands on it (`bladeBit`, `cliffordGamma`, `cliffordCommutator`,
`spinorBraidGate`, ...) are `abbrev`s, whose bodies are always visible. Everything off that path
(the tetron matrix, the Lindblad dissipator, the hypergraph quotient, ...) is sealed. -/

/-- Basis blade index $m \in \{0, \dots, 15\}$ of the 16-dimensional Clifford algebra $Cl_4$
generated by 4 Majorana fermion operators $\gamma_0, \gamma_1, \gamma_2, \gamma_3$ with
$\{\gamma_a, \gamma_b\} = 2 \delta_{a,b}$. -/
abbrev CliffordBlade := Fin 16

/-- Extract bit `idx` ($0 \le \text{idx} < 4$) of a 4-bit Majorana blade mask. -/
abbrev bladeBit (mask idx : Nat) : Nat :=
  (mask >>> idx) % 2

/-- Hamming weight (`popcount`) of a 4-bit Majorana blade mask $m \in \{0, \dots, 15\}$. -/
def bladePopcount (mask : Nat) : Nat :=
  bladeBit mask 0 + bladeBit mask 1 + bladeBit mask 2 + bladeBit mask 3

/-- Number of anticommuting Majorana transpositions required to normal-order $e_a \cdot e_b$:
$$\text{koszulSwaps}(a, b) = \sum_{0 \le j < i < 4} a_i \cdot b_j.$$ -/
abbrev koszulSwaps (a b : Nat) : Nat :=
  bladeBit b 0 * (bladeBit a 1 + bladeBit a 2 + bladeBit a 3) +
  bladeBit b 1 * (bladeBit a 2 + bladeBit a 3) +
  bladeBit b 2 * bladeBit a 3

/-- Map a parity bit `0` or `1` to its Koszul sign `+1` or `-1`. -/
abbrev signOfBit : Nat → Int
  | 0 => 1
  | _ => -1

/-- Exact Koszul sign rule $\text{cliffordSign}(a, b) = (-1)^{\text{koszulSwaps}(a, b)} \in \{1, -1\}$
for multiplying basis blades $e_a \cdot e_b = \text{cliffordSign}(a, b)\, e_{a \oplus b}$ in $Cl_4$. -/
@[expose] def cliffordSign (a b : Nat) : Int :=
  signOfBit (koszulSwaps a b % 2)

/-- General element $H = \sum_{m=0}^{15} b_m e_m$ of the 16-dimensional Clifford algebra $Cl_4$ over $\mathbb{Z}$. -/
structure CliffordElem where
  b0  : Int
  b1  : Int
  b2  : Int
  b3  : Int
  b4  : Int
  b5  : Int
  b6  : Int
  b7  : Int
  b8  : Int
  b9  : Int
  b10 : Int
  b11 : Int
  b12 : Int
  b13 : Int
  b14 : Int
  b15 : Int
  deriving Repr

deriving instance @[expose] DecidableEq for CliffordElem

namespace CliffordElem

/-- Look up the coefficient of basis blade $e_m$ ($0 \le m < 16$). -/
@[expose] def coeff (H : CliffordElem) : Nat → Int
  | 0  => H.b0
  | 1  => H.b1
  | 2  => H.b2
  | 3  => H.b3
  | 4  => H.b4
  | 5  => H.b5
  | 6  => H.b6
  | 7  => H.b7
  | 8  => H.b8
  | 9  => H.b9
  | 10 => H.b10
  | 11 => H.b11
  | 12 => H.b12
  | 13 => H.b13
  | 14 => H.b14
  | 15 => H.b15
  | _  => 0

/-- Construct a `CliffordElem` from a coefficient function `f : Nat → Int`. -/
abbrev ofFn (f : Nat → Int) : CliffordElem :=
  { b0  := f 0,  b1  := f 1,  b2  := f 2,  b3  := f 3
  , b4  := f 4,  b5  := f 5,  b6  := f 6,  b7  := f 7
  , b8  := f 8,  b9  := f 9,  b10 := f 10, b11 := f 11
  , b12 := f 12, b13 := f 13, b14 := f 14, b15 := f 15 }

/-- Extensionality characterization of `CliffordElem` across its 16 basis blade coordinates. -/
theorem ext_iff (A B : CliffordElem) :
    A = B ↔
      A.b0 = B.b0 ∧ A.b1 = B.b1 ∧ A.b2 = B.b2 ∧ A.b3 = B.b3 ∧
      A.b4 = B.b4 ∧ A.b5 = B.b5 ∧ A.b6 = B.b6 ∧ A.b7 = B.b7 ∧
      A.b8 = B.b8 ∧ A.b9 = B.b9 ∧ A.b10 = B.b10 ∧ A.b11 = B.b11 ∧
      A.b12 = B.b12 ∧ A.b13 = B.b13 ∧ A.b14 = B.b14 ∧ A.b15 = B.b15 := by
  cases A
  cases B
  constructor
  · intro h
    injection h
    refine ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

end CliffordElem

/-- Sum an integer-valued function over the 16 Clifford basis blades $0 \dots 15$. -/
abbrev sum16Blades (f : Nat → Int) : Int :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 +
  f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15

/-- Zero element $0 \in Cl_4$. -/
abbrev cliffordZero : CliffordElem :=
  CliffordElem.ofFn (fun _ => 0)

/-- Scalar multiplicative identity $1 = e_0 \in Cl_4$. -/
abbrev cliffordOne : CliffordElem :=
  CliffordElem.ofFn (fun m => cond (m == 0) 1 0)

/-- Basis blade $e_m \in Cl_4$ ($0 \le m < 16$). -/
abbrev cliffordBasisBlade (m : Nat) : CliffordElem :=
  CliffordElem.ofFn (fun k => cond (k == m % 16) 1 0)

/-- Majorana fermion generator $\gamma_a = e_{2^a} \in Cl_4$ for $a \in \{0, 1, 2, 3\}$. -/
abbrev cliffordGamma (a : Fin 4) : CliffordElem :=
  cliffordBasisBlade (1 <<< a.val)

/-- Total 4-Majorana fermion parity operator $P = -\gamma_0 \gamma_1 \gamma_2 \gamma_3 = -e_{15} \in Cl_4$
(blade `0b1111 = 15` with coefficient `-1`). -/
abbrev cliffordParity : CliffordElem :=
  { cliffordZero with b15 := -1 }

/-- Addition in $Cl_4$. -/
abbrev cliffordAdd (A B : CliffordElem) : CliffordElem :=
  CliffordElem.ofFn (fun k => A.coeff k + B.coeff k)

/-- Subtraction in $Cl_4$. -/
abbrev cliffordSub (A B : CliffordElem) : CliffordElem :=
  CliffordElem.ofFn (fun k => A.coeff k - B.coeff k)

/-- Scalar multiplication $c \cdot A$ in $Cl_4$. -/
def cliffordScale (c : Int) (A : CliffordElem) : CliffordElem :=
  CliffordElem.ofFn (fun k => c * A.coeff k)

/-- Bilinear Clifford product $A \cdot B \in Cl_4$ governed by the Koszul sign rule `cliffordSign`:
$$(A \cdot B)_k = \sum_{a=0}^{15} \text{cliffordSign}(a, a \oplus k) \cdot A_a \cdot B_{a \oplus k}.$$ -/
@[expose] def cliffordMul (A B : CliffordElem) : CliffordElem :=
  CliffordElem.ofFn (fun k =>
    sum16Blades (fun a => cliffordSign a (a ^^^ k) * A.coeff a * B.coeff (a ^^^ k)))

/-- Clifford commutator $[A, B] = A \cdot B - B \cdot A \in Cl_4$. -/
abbrev cliffordCommutator (A B : CliffordElem) : CliffordElem :=
  cliffordSub (cliffordMul A B) (cliffordMul B A)

/-- Check whether an operator $H \in Cl_4$ commutes with fermion parity $P = -\gamma_0\gamma_1\gamma_2\gamma_3$
($[H, P] = 0$). -/
@[expose] def commutesWithParity (H : CliffordElem) : Bool :=
  decide (cliffordCommutator H cliffordParity = cliffordZero)

/-- Check whether $H \in Cl_4$ is supported purely on even-weight Majorana blades
(`bladePopcount m % 2 == 0`, so all odd-weight blades $m \in \{1, 2, 4, 7, 8, 11, 13, 14\}$ have
zero coefficient `H.coeff m = 0`). -/
def isEvenBladeSupported (H : CliffordElem) : Bool :=
  decide (H.b1 = 0) &&
  decide (H.b2 = 0) &&
  decide (H.b4 = 0) &&
  decide (H.b7 = 0) &&
  decide (H.b8 = 0) &&
  decide (H.b11 = 0) &&
  decide (H.b13 = 0) &&
  decide (H.b14 = 0)

/-- Majorana generator square, canonical anticommutation, and fermion parity involution ($P^2 = 1$). -/
theorem clifford_majorana_algebra_laws (a : Fin 4) :
    cliffordMul (cliffordGamma a) (cliffordGamma a) = cliffordOne ∧
    (∀ b : Fin 4, a ≠ b →
      cliffordAdd (cliffordMul (cliffordGamma a) (cliffordGamma b))
                  (cliffordMul (cliffordGamma b) (cliffordGamma a)) = cliffordZero) ∧
    cliffordMul cliffordParity cliffordParity = cliffordOne := by
  revert a
  decide +kernel

/-- $H \in Cl_4$ commutes with fermion parity $P$ iff $H$ is supported purely on even-weight blades. -/
theorem clifford_commutesWithParity_iff_even_blades (H : CliffordElem) :
    commutesWithParity H = true ↔ isEvenBladeSupported H = true := by
  rcases H with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩
  unfold commutesWithParity isEvenBladeSupported
  rw [decide_eq_true_iff]
  simp only [Bool.and_eq_true]
  rw [decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff,
      decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
  rw [CliffordElem.ext_iff]
  simp only [cliffordMul,
    CliffordElem.ofFn, CliffordElem.coeff, sum16Blades, cliffordSign, signOfBit, koszulSwaps,
    bladeBit, Nat.reduceXor, Nat.reduceShiftRight, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    Int.reduceNeg, Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.mul_neg, Int.neg_mul,
    Int.add_zero, Int.zero_add]
  constructor
  · rintro ⟨_, h1, h2, _, h4, _, _, h7, h8, _, _, h11, _, h13, h14, _⟩
    refine ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb4⟩, hb7⟩, hb8⟩, hb11⟩, hb13⟩, hb14⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Rank-16 bijective $4 \times 4$ Pauli-block matrix representation of $H \in Cl_4$ in the parity-ordered basis. -/
def cliffordToTetronMatrix (H : CliffordElem) : IntMatrix where
  dim := 4
  rows :=
    let e00 := (H.b0 - H.b15) + (H.b6 - H.b9)
    let e01 := (H.b3 + H.b12) + (H.b5 + H.b10)
    let e10 := (H.b3 + H.b12) - (H.b5 + H.b10)
    let e11 := (H.b0 - H.b15) - (H.b6 - H.b9)
    let o00 := (H.b0 + H.b15) + (H.b6 + H.b9)
    let o01 := (H.b3 - H.b12) + (H.b5 - H.b10)
    let o10 := (H.b3 - H.b12) - (H.b5 - H.b10)
    let o11 := (H.b0 + H.b15) - (H.b6 + H.b9)
    let c02 := H.b1 + H.b13
    let c03 := H.b1 + H.b2 + H.b7
    let c12 := -H.b1 + H.b4 + H.b11
    let c13 := -H.b1 + H.b8 + H.b14
    let c20 := H.b1 - H.b13
    let c21 := -H.b1 + H.b4 - H.b11
    let c30 := H.b1 + H.b2 - H.b7
    let c31 := -H.b1 + H.b8 - H.b14
    [ [e00, e01, c02, c03]
    , [e10, e11, c12, c13]
    , [c20, c21, o00, o01]
    , [c30, c31, o10, o11] ]

/-- Clifford element realizing `majoranaTetronHamiltonian` ($2 P + \gamma_0\gamma_1 = -2 e_{15} + e_3$). -/
def majoranaTetronClifford : CliffordElem :=
  { cliffordZero with b3 := 1, b15 := -2 }

/-- Clifford element realizing `majoranaParityPreserveNoise` ($e_0 + e_3 + e_{12}$). -/
def majoranaParityPreserveClifford : CliffordElem :=
  { cliffordZero with b0 := 1, b3 := 1, b12 := 1 }

/-- Clifford element realizing `majoranaQuasiparticlePoisonNoise` ($\gamma_0 = e_1$, odd-weight blade!). -/
def majoranaQuasiparticlePoisonClifford : CliffordElem :=
  cliffordGamma ⟨0, by decide⟩

/-- $2 \times 2$ Pauli spinor block quotient induced on `C_even = {0, 1}`, `C_odd = {2, 3}` by $H \in Cl_4$. -/
def cliffordParityQuotient (H : CliffordElem) : Nat → Nat → IntMatrix
  | 0, 0 => extractCellBlock (cliffordToTetronMatrix H) 2 0 0
  | 1, 1 => extractCellBlock (cliffordToTetronMatrix H) 2 1 1
  | _, _ => IntMatrix.zero 2

/-- Whenever $\Delta H \in Cl_4$ commutes with fermion parity $P$, all odd blades and off-sector entries vanish. -/
theorem clifford_commutesWithParity_zero_offblock_and_leakage
    (dH : CliffordElem)
    (hComm : commutesWithParity dH = true) :
    isEvenBladeSupported dH = true ∧
    (cliffordToTetronMatrix dH).entry 0 2 = 0 ∧
    (cliffordToTetronMatrix dH).entry 0 3 = 0 ∧
    (cliffordToTetronMatrix dH).entry 1 2 = 0 ∧
    (cliffordToTetronMatrix dH).entry 1 3 = 0 ∧
    (cliffordToTetronMatrix dH).entry 2 0 = 0 ∧
    (cliffordToTetronMatrix dH).entry 2 1 = 0 ∧
    (cliffordToTetronMatrix dH).entry 3 0 = 0 ∧
    (cliffordToTetronMatrix dH).entry 3 1 = 0 ∧
    cellRowSum (cliffordToTetronMatrix dH).entry [0, 1] 2 = 0 ∧
    cellRowSum (cliffordToTetronMatrix dH).entry [0, 1] 3 = 0 ∧
    cellRowSum (cliffordToTetronMatrix dH).entry [2, 3] 0 = 0 ∧
    cellRowSum (cliffordToTetronMatrix dH).entry [2, 3] 1 = 0 ∧
    cliffordParityQuotient dH 1 0 = IntMatrix.zero 2 ∧
    cliffordParityQuotient dH 0 1 = IntMatrix.zero 2 := by
  have hEven : isEvenBladeSupported dH = true :=
    (clifford_commutesWithParity_iff_even_blades dH).mp hComm
  rcases dH with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩
  have hEven' := hEven
  unfold isEvenBladeSupported at hEven'
  simp only [Bool.and_eq_true] at hEven'
  rcases hEven' with ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb4⟩, hb7⟩, hb8⟩, hb11⟩, hb13⟩, hb14⟩
  have h1  : b1 = 0  := of_decide_eq_true hb1
  have h2  : b2 = 0  := of_decide_eq_true hb2
  have h4  : b4 = 0  := of_decide_eq_true hb4
  have h7  : b7 = 0  := of_decide_eq_true hb7
  have h8  : b8 = 0  := of_decide_eq_true hb8
  have h11 : b11 = 0 := of_decide_eq_true hb11
  have h13 : b13 = 0 := of_decide_eq_true hb13
  have h14 : b14 = 0 := of_decide_eq_true hb14
  refine ⟨hEven, ?_⟩
  change (b1 + b13 = 0) ∧
    (b1 + b2 + b7 = 0) ∧
    (-b1 + b4 + b11 = 0) ∧
    (-b1 + b8 + b14 = 0) ∧
    (b1 - b13 = 0) ∧
    (-b1 + b4 - b11 = 0) ∧
    (b1 + b2 - b7 = 0) ∧
    (-b1 + b8 - b14 = 0) ∧
    ((b1 - b13) + ((-b1 + b4 - b11) + 0) = 0) ∧
    ((b1 + b2 - b7) + ((-b1 + b8 - b14) + 0) = 0) ∧
    ((b1 + b13) + ((b1 + b2 + b7) + 0) = 0) ∧
    ((-b1 + b4 + b11) + ((-b1 + b8 + b14) + 0) = 0) ∧
    (IntMatrix.zero 2 = IntMatrix.zero 2) ∧ (IntMatrix.zero 2 = IntMatrix.zero 2)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega, by omega, rfl, rfl⟩

/-- Bidirectional off-sector vanishing, block-equitable partition equivalence, and 16D injectivity for $Cl_4$. -/
theorem clifford_commutesWithParity_iff_offblock_and_equitable (H : CliffordElem) :
    ((extractCellBlock (cliffordToTetronMatrix H) 2 0 1 = IntMatrix.zero 2 ∧
      extractCellBlock (cliffordToTetronMatrix H) 2 1 0 = IntMatrix.zero 2) ↔
     commutesWithParity H = true) ∧
    (commutesWithParity H = true ↔
     checkBlockEquitablePartition (cliffordToTetronMatrix H) 2 2 majoranaParityPart (cliffordParityQuotient H) = true) ∧
    (cliffordToTetronMatrix H = IntMatrix.zero 4 ↔ H = cliffordZero) := by
  rw [clifford_commutesWithParity_iff_even_blades H]
  rcases H with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold isEvenBladeSupported
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    change (({ dim := 2, rows := [[b1 + b13, b1 + b2 + b7], [-b1 + b4 + b11, -b1 + b8 + b14]] } : IntMatrix) =
              { dim := 2, rows := [[0, 0], [0, 0]] } ∧
            ({ dim := 2, rows := [[b1 - b13, -b1 + b4 - b11], [b1 + b2 - b7, -b1 + b8 - b14]] } : IntMatrix) =
              { dim := 2, rows := [[0, 0], [0, 0]] }) ↔
      (((((((b1 = 0 ∧ b2 = 0) ∧ b4 = 0) ∧ b7 = 0) ∧ b8 = 0) ∧ b11 = 0) ∧ b13 = 0) ∧ b14 = 0)
    simp only [IntMatrix.mk.injEq, List.cons.injEq, and_true, true_and]
    constructor
    · rintro ⟨⟨⟨h02, h03⟩, ⟨h12, h13⟩⟩, ⟨⟨h20, h21⟩, ⟨h30, h31⟩⟩⟩
      refine ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩
    · rintro ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb4⟩, hb7⟩, hb8⟩, hb11⟩, hb13⟩, hb14⟩
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩
  · unfold isEvenBladeSupported checkBlockEquitablePartition
    have hRange : List.range 2 = [0, 1] := rfl
    have hDiv42 : (4 : Nat) / 2 = 2 := by decide
    simp [cliffordToTetronMatrix, hDiv42, hRange,
      blockCellOf, blockCellMembers, blockCellRowSumEntry,
      cliffordParityQuotient, extractCellBlock, majoranaParityPart,
      IntMatrix.zero, IntMatrix.scaledIdentity, IntMatrix.entry, listGetInt, sumIntOver]
    constructor
    · intro h
      repeat' constructor <;> omega
    · intro h
      repeat' constructor <;> omega
  · rw [CliffordElem.ext_iff]
    change ({ dim := 4
            , rows :=
                [ [(b0 - b15) + (b6 - b9), (b3 + b12) + (b5 + b10), b1 + b13, b1 + b2 + b7]
                , [(b3 + b12) - (b5 + b10), (b0 - b15) - (b6 - b9), -b1 + b4 + b11, -b1 + b8 + b14]
                , [b1 - b13, -b1 + b4 - b11, (b0 + b15) + (b6 + b9), (b3 - b12) + (b5 - b10)]
                , [b1 + b2 - b7, -b1 + b8 - b14, (b3 - b12) - (b5 - b10), (b0 + b15) - (b6 + b9)] ] } : IntMatrix) =
           { dim := 4, rows := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]] } ↔
      (b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0 ∧ b6 = 0 ∧ b7 = 0 ∧
       b8 = 0 ∧ b9 = 0 ∧ b10 = 0 ∧ b11 = 0 ∧ b12 = 0 ∧ b13 = 0 ∧ b14 = 0 ∧ b15 = 0)
    simp only [IntMatrix.mk.injEq, List.cons.injEq, and_true, true_and]
    constructor
    · rintro ⟨⟨e00, e01, c02, c03⟩, ⟨e10, e11, c12, c13⟩, ⟨c20, c21, o00, o01⟩, ⟨c30, c31, o10, o11⟩⟩
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
              by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Faithful $4 \times 4$ Pauli spinor matrices over $\mathbb{Z}[i]$ for the 4 Majorana generators ($\gamma_0 = X \otimes I, \gamma_1 = Y \otimes X, \gamma_2 = Y \otimes Y, \gamma_3 = Y \otimes Z$). -/
@[expose] def spinorGammaNat (a : Nat) : GaussianMatrix where
  dim := 4
  rows := match a with
    | 0 =>
        [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]
        , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]
        , [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
        , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]
    | 1 =>
        [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]
        , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]
        , [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]
        , [⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]
    | 2 =>
        [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]
        , [⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]
        , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
        , [⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]
    | _ =>
        [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]
        , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]
        , [⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
        , [⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]

def gamma0Spinor : GaussianMatrix := spinorGammaNat 0
def gamma1Spinor : GaussianMatrix := spinorGammaNat 1
def gamma2Spinor : GaussianMatrix := spinorGammaNat 2
def gamma3Spinor : GaussianMatrix := spinorGammaNat 3

/-- Right-multiply `acc` by `G` if `bit == 1`, otherwise return `acc`. -/
abbrev mulSpinorIfBit (acc : GaussianMatrix) (bit : Nat) (G : GaussianMatrix) : GaussianMatrix :=
  cond (bit == 1) (acc.mul G) acc

/-- $4 \times 4$ spinor matrix $\rho_{\mathbb{Z}[i]}(e_m) = \gamma_0^{m_0} \gamma_1^{m_1} \gamma_2^{m_2} \gamma_3^{m_3}$
for basis blade $e_m \in Cl_4$. -/
@[expose] def cliffordBladeSpinorMatrix (m : Nat) : GaussianMatrix :=
  let r0 := cond (bladeBit m 0 == 1) (spinorGammaNat 0) (GaussianMatrix.identity 4)
  let r1 := mulSpinorIfBit r0 (bladeBit m 1) (spinorGammaNat 1)
  let r2 := mulSpinorIfBit r1 (bladeBit m 2) (spinorGammaNat 2)
  mulSpinorIfBit r2 (bladeBit m 3) (spinorGammaNat 3)

/-- Faithful $4 \times 4$ Jordan–Wigner spinor matrix representation $\rho_{\mathbb{Z}[i]} : Cl_4 \to M_4(\mathbb{Z}[i])$
(`cliffordToSpinorMatrix`). -/
@[expose] def cliffordToSpinorMatrix (H : CliffordElem) : GaussianMatrix :=
  (List.range 16).foldl (fun acc m =>
    let c := H.coeff m
    cond (decide (c = 0)) acc (acc.add ((cliffordBladeSpinorMatrix m).scale c)))
    (GaussianMatrix.zero 4)

/-! ## 5. Universal Theorem: Symmetry-Preserving Noise Produces Identically Zero Leakage -/

/-- Perturbed Hamiltonian entry $(H + \epsilon \Delta H)_{u, v} = H_{u,v} + \epsilon \cdot \Delta H_{u,v}$. -/
def perturbedHamiltonian (H dH : Nat → Nat → Int) (eps : Int) (u v : Nat) : Int :=
  H u v + eps * dH u v

/-- Perturbed quotient entry $(Q + \epsilon \Delta Q)_{i, j} = Q_{i,j} + \epsilon \cdot \Delta Q_{i,j}$. -/
def perturbedQuotient (Q dQ : Nat → Nat → Int) (eps : Int) (i j : Nat) : Int :=
  Q i j + eps * dQ i j

/-- Perturbed $2 \times 2$ block quotient $(Q + \epsilon \Delta Q)_{i, j} = Q_{i,j} + \epsilon \cdot \Delta Q_{i,j}$. -/
def perturbedBlockQuotient (Q dQ : Nat → Nat → IntMatrix) (eps : Int) (i j : Nat) : IntMatrix :=
  (Q i j).add ((dQ i j).scale eps)

/-- **Theorem (`clifford_parity_protected_zero_sector_leakage`)**:
For ANY nominal Clifford Hamiltonian `cH : CliffordElem` and noise operator `cDH : CliffordElem`,
if both commute with fermion parity $P = -\gamma_0\gamma_1\gamma_2\gamma_3$
(`commutesWithParity cH = true` and `commutesWithParity cDH = true`), then for EVERY noise
amplitude `eps : Int` and EVERY initial state `w : Nat → Int` prepared in the $+1$ parity
eigenspace (`w 1 = 0`), **without assuming `Q 1 0 = 0` or `dQ 1 0 = 0`**:
1. The odd-parity $2 \times 2$ inter-sector block quotient after $Q_{cH} + \epsilon Q_{cDH}$ is identically `IntMatrix.zero 2`, and
2. The full 4-state tetron amplitudes at odd-parity basis states $u = 2$ and $u = 3$ after
   $\rho(cH) + \epsilon \rho(cDH)$ are **identically `0`**! -/
theorem clifford_parity_protected_zero_sector_leakage
    (cH cDH : CliffordElem)
    (eps : Int)
    (w : Nat → Int)
    (hCommH  : commutesWithParity cH = true)
    (hCommDH : commutesWithParity cDH = true)
    (hEvenInit : w 1 = 0) :
    perturbedBlockQuotient (cliffordParityQuotient cH) (cliffordParityQuotient cDH) eps 1 0 = IntMatrix.zero 2 ∧
    matVec [0, 1, 2, 3]
      (perturbedHamiltonian (cliffordToTetronMatrix cH).entry (cliffordToTetronMatrix cDH).entry eps)
      (liftQuotientVec majoranaParityPart w) 2 = 0 ∧
    matVec [0, 1, 2, 3]
      (perturbedHamiltonian (cliffordToTetronMatrix cH).entry (cliffordToTetronMatrix cDH).entry eps)
      (liftQuotientVec majoranaParityPart w) 3 = 0 := by
  have hZ_H  := clifford_commutesWithParity_zero_offblock_and_leakage cH hCommH
  have hZ_DH := clifford_commutesWithParity_zero_offblock_and_leakage cDH hCommDH
  rcases hZ_H with ⟨_, _, _, _, _, hH20, hH21, hH30, hH31, _, _, _, _, hQH10, _⟩
  rcases hZ_DH with ⟨_, _, _, _, _, hDH20, hDH21, hDH30, hDH31, _, _, _, _, hQDH10, _⟩
  refine ⟨?_, ?_⟩
  · dsimp only [perturbedBlockQuotient]
    rw [hQH10, hQDH10]
    change ({ dim := 2, rows := [[0 + eps * 0, 0 + eps * 0], [0 + eps * 0, 0 + eps * 0]] } : IntMatrix) =
           { dim := 2, rows := [[0, 0], [0, 0]] }
    simp only [Int.mul_zero, Int.add_zero]
  · change (((cliffordToTetronMatrix cH).entry 2 0 + eps * (cliffordToTetronMatrix cDH).entry 2 0) * w 0 +
      (((cliffordToTetronMatrix cH).entry 2 1 + eps * (cliffordToTetronMatrix cDH).entry 2 1) * w 0 +
       (((cliffordToTetronMatrix cH).entry 2 2 + eps * (cliffordToTetronMatrix cDH).entry 2 2) * w 1 +
        (((cliffordToTetronMatrix cH).entry 2 3 + eps * (cliffordToTetronMatrix cDH).entry 2 3) * w 1 + 0))) = 0) ∧
      (((cliffordToTetronMatrix cH).entry 3 0 + eps * (cliffordToTetronMatrix cDH).entry 3 0) * w 0 +
       (((cliffordToTetronMatrix cH).entry 3 1 + eps * (cliffordToTetronMatrix cDH).entry 3 1) * w 0 +
        (((cliffordToTetronMatrix cH).entry 3 2 + eps * (cliffordToTetronMatrix cDH).entry 3 2) * w 1 +
         (((cliffordToTetronMatrix cH).entry 3 3 + eps * (cliffordToTetronMatrix cDH).entry 3 3) * w 1 + 0))) = 0)
    rw [hH20, hH21, hH30, hH31, hDH20, hDH21, hDH30, hDH31, hEvenInit]
    exact ⟨by omega, by omega⟩

/-- Lemma (`perturbed_cellRowSum_equitable`):
If both $H$ and a noise perturbation $\Delta H$ are equitable with respect to cell `cellJ` (with
quotient entries $Q_{\text{part}(u), j}$ and $\Delta Q_{\text{part}(u), j}$), then for EVERY noise
amplitude $\epsilon \in \mathbb{Z}$, the perturbed Hamiltonian $H + \epsilon \Delta H$ has exact
cell row sum $Q_{\text{part}(u), j} + \epsilon \Delta Q_{\text{part}(u), j}$! -/
theorem perturbed_cellRowSum_equitable
    (H dH Q dQ : Nat → Nat → Int)
    (part : Nat → Nat)
    (eps : Int)
    (cellJ : List Nat)
    (u j : Nat)
    (hRowH  : cellRowSum H cellJ u = Q (part u) j)
    (hRowDH : cellRowSum dH cellJ u = dQ (part u) j) :
    cellRowSum (perturbedHamiltonian H dH eps) cellJ u =
      perturbedQuotient Q dQ eps (part u) j := by
  dsimp only [cellRowSum, perturbedHamiltonian, perturbedQuotient] at *
  rw [sumIntOver_add (fun v => H u v) (fun v => eps * dH u v) cellJ]
  rw [sumIntOver_mul_left eps (fun v => dH u v) cellJ]
  rw [hRowH, hRowDH]

/-- **Theorem (`symmetry_preserving_noise_zero_leakage`)**:
**Universal & Concrete Symmetry-Preserving Noise Immunity Theorem**:
1. **Universal Noisy Intertwining (Zero Orthogonal Subspace Leakage)**:
   For ANY nominal Hamiltonian $H$, symmetry-preserving perturbation $\Delta H$, partition `part`,
   and quotients $Q, \Delta Q$, if $H$ and $\Delta H$ are equitable across `cellIndices` and `cellOf`,
   then for EVERY noise amplitude $\epsilon \in \mathbb{Z}$ and EVERY quotient vector $w$:
   $$((H + \epsilon \Delta H)(S w))_u = (S ((Q + \epsilon \Delta Q) w))_u.$$
   Thus the noisy evolution remains 100% inside the equitable computational subspace $\text{im}(S)$
   with identically zero leakage into the orthogonal complement $\text{im}(S)^\perp$!
2. **Universal Parity-Sector Block Isolation (Zero Odd-Parity Quasiparticle Leakage)**:
   When the two-sector parity quotient `[0, 1]` has zero inter-sector coupling in both the nominal
   Hamiltonian and noise ($Q(1, 0) = 0$ and $\Delta Q(1, 0) = 0$, which is derived from
   `commutesWithParity` by `clifford_commutesWithParity_zero_offblock_and_leakage`) and the system
   starts in the even-parity computational sector ($w_1 = 0$), the odd-parity sector amplitude after
   applying $Q + \epsilon \Delta Q$ is **identically `0`** for all $\epsilon \in \mathbb{Z}$ and all $w_0 \in \mathbb{Z}$!
3. **Concrete IBM Heavy-Hex $C_{12}$ & Microsoft Majorana-1 Tetron Clifford Verification**:
   - Both the 7-cell distance partition and the 2-cell corner-vs-bridge partition of Heavy-Hex $C_{12}$
     pass `checkEquitablePartition = true`, `checkHandshakeIdentity = true`, and have
     `evalEquitableResidualNormSq = 0`.
   - On the Majorana-1 Tetron, `cliffordToTetronMatrix majoranaTetronClifford = majoranaTetronHamiltonian`
     (`commutesWithParity = true`), `cliffordToTetronMatrix majoranaParityPreserveClifford = majoranaParityPreserveNoise`
     (`commutesWithParity = true`, `evalEquitableResidualNormSq = 0`), whereas
     `majoranaQuasiparticlePoisonClifford` ($\gamma_0$) fails `commutesWithParity` (`= false`), breaks
     parity equitability (`checkEquitablePartition = false`), and induces a non-zero leakage residual floor
     `evalEquitableResidualNormSq = 8 > 0`! -/
theorem symmetry_preserving_noise_zero_leakage
    (H dH Q dQ : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (eps : Int)
    (w : Nat → Int)
    (u : Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqH   : ∀ j, j ∈ cellIndices → cellRowSum H (cellOf j) u = Q (part u) j)
    (hEqDH  : ∀ j, j ∈ cellIndices → cellRowSum dH (cellOf j) u = dQ (part u) j)
    (hBlockH  : Q 1 0 = 0)
    (hBlockDH : dQ 1 0 = 0)
    (hEvenInit : w 1 = 0) :
    -- 1. Universal intertwining of H + eps * dH with Q + eps * dQ
    partitionedMatVec (perturbedHamiltonian H dH eps) cellIndices cellOf (liftQuotientVec part w) u =
      liftQuotientVec part (quotientMatVec (perturbedQuotient Q dQ eps) cellIndices w) u ∧
    -- 2. Universal zero leakage into the odd parity sector (sector 1)
    quotientMatVec (perturbedQuotient Q dQ eps) [0, 1] w 1 = 0 ∧
    -- 3. Concrete IBM Heavy-Hex C12 & Majorana-1 Tetron Clifford certificates
    checkEquitablePartition heavyHexC12RingMatrix 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = true ∧
    checkHandshakeIdentity 12 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = true ∧
    evalEquitableResidualNormSq heavyHexC12RingMatrix 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = 0 ∧
    checkEquitablePartition heavyHexC12CornerBridgeMatrix 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = true ∧
    checkHandshakeIdentity 12 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = true ∧
    evalEquitableResidualNormSq heavyHexC12CornerBridgeMatrix 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = 0 ∧
    cliffordToTetronMatrix majoranaTetronClifford = majoranaTetronHamiltonian ∧
    cliffordToTetronMatrix majoranaParityPreserveClifford = majoranaParityPreserveNoise ∧
    cliffordToTetronMatrix majoranaQuasiparticlePoisonClifford = majoranaQuasiparticlePoisonNoise ∧
    commutesWithParity majoranaTetronClifford = true ∧
    commutesWithParity majoranaParityPreserveClifford = true ∧
    commutesWithParity majoranaQuasiparticlePoisonClifford = false ∧
    checkEquitablePartition majoranaTetronHamiltonian 2 majoranaParityPart majoranaTetronQuotient = true ∧
    checkEquitablePartition majoranaParityPreserveNoise 2 majoranaParityPart majoranaNoiseSymQuotient = true ∧
    evalEquitableResidualNormSq majoranaParityPreserveNoise 2 majoranaParityPart majoranaNoiseSymQuotient = 0 ∧
    checkEquitablePartition majoranaQuasiparticlePoisonNoise 2 majoranaParityPart (fun _ _ => 0) = false ∧
    evalEquitableResidualNormSq majoranaQuasiparticlePoisonNoise 2 majoranaParityPart (fun _ _ => 0) = 8 := by
  have hPerturbRow : ∀ j, j ∈ cellIndices →
      cellRowSum (perturbedHamiltonian H dH eps) (cellOf j) u =
        perturbedQuotient Q dQ eps (part u) j := by
    intro j hj
    exact perturbed_cellRowSum_equitable H dH Q dQ part eps (cellOf j) u j (hEqH j hj) (hEqDH j hj)
  have hIntertwine :=
    equitable_intertwining_step
      (perturbedHamiltonian H dH eps)
      (perturbedQuotient Q dQ eps)
      part cellIndices cellOf w u hCells hPerturbRow
  have hZeroOdd : quotientMatVec (perturbedQuotient Q dQ eps) [0, 1] w 1 = 0 := by
    dsimp only [quotientMatVec, perturbedQuotient, sumIntOver]
    rw [hBlockH, hBlockDH, hEvenInit]
    simp only [Int.mul_zero, Int.zero_mul, Int.add_zero]
  refine ⟨hIntertwine, hZeroOdd, ?_⟩
  decide +kernel

/-! ## 6. Ivanov Majorana Braiding Gates, Artin Braid Group & Open-System Lindblad Parity Cooling -/

/-- Scaled Ivanov / measurement-based Majorana exchange braid generator $T_{a, b} = 1 + \gamma_a \gamma_b \in Cl_4$
($U_{a,b} = \frac{1}{\sqrt{2}}(1 + \gamma_a \gamma_b) = \exp(\frac{\pi}{4}\gamma_a\gamma_b)$). -/
abbrev majoranaBraidElem (a b : Fin 4) : CliffordElem :=
  cliffordAdd cliffordOne (cliffordMul (cliffordGamma a) (cliffordGamma b))

/-- Hermitian adjoint Majorana braid generator $T_{a, b}^\dagger = 1 + \gamma_b \gamma_a = 1 - \gamma_a \gamma_b \in Cl_4$
(for $a \neq b$). -/
abbrev majoranaBraidAdjElem (a b : Fin 4) : CliffordElem :=
  cliffordAdd cliffordOne (cliffordMul (cliffordGamma b) (cliffordGamma a))

/-- Direct lookup of the $4 \times 4$ spinor matrix $\rho_{\mathbb{Z}[i]}(\gamma_a)$ for Majorana generator $a \in \text{Fin } 4$. -/
abbrev spinorGamma (a : Fin 4) : GaussianMatrix :=
  spinorGammaNat a.val

/-- $4 \times 4$ spinor matrix $\rho_{\mathbb{Z}[i]}(T_{a,b}) = I_4 + \rho_{\mathbb{Z}[i]}(\gamma_a)\rho_{\mathbb{Z}[i]}(\gamma_b)$
of the Majorana braiding gate over $\mathbb{Z}[i]$. -/
abbrev spinorBraidGate (a b : Fin 4) : GaussianMatrix :=
  (GaussianMatrix.identity 4).add ((spinorGamma a).mul (spinorGamma b))

/-- Exact equivalence between `spinorBraidGate a b` and `cliffordToSpinorMatrix (majoranaBraidElem a b)`
for all Majorana modes $a, b \in \text{Fin } 4$. -/
theorem spinorBraidGate_eq_cliffordToSpinorMatrix (a b : Fin 4) :
    spinorBraidGate a b = cliffordToSpinorMatrix (majoranaBraidElem a b) := by
  have hCheck : (List.range 4).all (fun i =>
      (List.range 4).all (fun j =>
        GaussianMatrix.beq
          (spinorBraidGate ⟨i % 4, Nat.mod_lt i (by decide)⟩ ⟨j % 4, Nat.mod_lt j (by decide)⟩)
          (cliffordToSpinorMatrix
            (majoranaBraidElem ⟨i % 4, Nat.mod_lt i (by decide)⟩ ⟨j % 4, Nat.mod_lt j (by decide)⟩)))) = true := by
    decide +kernel
  rw [list_all_iff_forall] at hCheck
  have hRow := (list_all_iff_forall _ (List.range 4)).mp (hCheck a.val (List.mem_range.mpr a.isLt))
  have hEq := GaussianMatrix.eq_of_beq (hRow b.val (List.mem_range.mpr b.isLt))
  have ha : (⟨a.val % 4, Nat.mod_lt a.val (by decide)⟩ : Fin 4) = a := by
    ext; exact Nat.mod_eq_of_lt a.isLt
  have hb : (⟨b.val % 4, Nat.mod_lt b.val (by decide)⟩ : Fin 4) = b := by
    ext; exact Nat.mod_eq_of_lt b.isLt
  rw [ha, hb] at hEq
  exact hEq

/-- Chiral fermion parity spinor matrix $\rho_{\mathbb{Z}[i]}(P) = \operatorname{diag}(1, 1, -1, -1)$. -/
@[expose] def spinorChiralParity : GaussianMatrix where
  dim  := 4
  rows :=
    [ [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] ]

/-- Even-parity computational subspace projector $\Pi_{\text{even}} = \frac{1}{2}(I_4 + P) = \operatorname{diag}(1, 1, 0, 0)$
over $\mathbb{Z}[i]$. -/
def spinorEvenParityProjector : GaussianMatrix where
  dim  := 4
  rows :=
    [ [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]

/-- Odd-parity poisoned subspace projector $\Pi_{\text{odd}} = \frac{1}{2}(I_4 - P) = \operatorname{diag}(0, 0, 1, 1)$
over $\mathbb{Z}[i]$. -/
def spinorOddParityProjector : GaussianMatrix where
  dim  := 4
  rows :=
    [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] ]

/-- **Theorem (`majoranaBraidElem_unitary`)**:
For every pair of distinct Majorana modes $a, b \in \text{Fin } 4$ ($a \neq b$), the Ivanov braid
generator $T_{a,b} = 1 + \gamma_a\gamma_b$ is scaled unitary of norm $2$:
$$T_{a,b} T_{a,b}^\dagger = T_{a,b}^\dagger T_{a,b} = 2 \cdot 1_{Cl_4} \;\wedge\;
  \rho(T_{a,b}) \rho(T_{a,b})^\dagger = \rho(T_{a,b})^\dagger \rho(T_{a,b}) = 2 I_4.$$ -/
theorem majoranaBraidElem_unitary (a b : Fin 4) (hNe : a ≠ b) :
    cliffordMul (majoranaBraidElem a b) (majoranaBraidAdjElem a b) = cliffordScale 2 cliffordOne ∧
    cliffordMul (majoranaBraidAdjElem a b) (majoranaBraidElem a b) = cliffordScale 2 cliffordOne ∧
    (spinorBraidGate a b).mul (spinorBraidGate a b).conjTranspose = (GaussianMatrix.identity 4).scale 2 ∧
    (spinorBraidGate a b).conjTranspose.mul (spinorBraidGate a b) = (GaussianMatrix.identity 4).scale 2 := by
  revert a b hNe
  decide +kernel

/-- **Theorem (`spinorParityProjectors_orthogonal_idempotent`)**:
The even and odd fermion-parity projectors $\Pi_{\text{even}}, \Pi_{\text{odd}}$ form a complete
orthogonal idempotent resolution of the identity and spectral decomposition of chiral parity $P$:
$$\Pi_{\text{even}}^2 = \Pi_{\text{even}},\quad \Pi_{\text{odd}}^2 = \Pi_{\text{odd}},\quad
  \Pi_{\text{even}}\Pi_{\text{odd}} = \Pi_{\text{odd}}\Pi_{\text{even}} = 0_4,\quad
  \Pi_{\text{even}} + \Pi_{\text{odd}} = I_4,\quad \Pi_{\text{even}} - \Pi_{\text{odd}} = P.$$ -/
-- fixture kept (2026-11-04): algebraic identities of the two defined 4x4 projectors; there is no universal version to state
example :
    spinorEvenParityProjector.mul spinorEvenParityProjector = spinorEvenParityProjector ∧
    spinorOddParityProjector.mul spinorOddParityProjector = spinorOddParityProjector ∧
    spinorEvenParityProjector.mul spinorOddParityProjector = GaussianMatrix.zero 4 ∧
    spinorOddParityProjector.mul spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    spinorEvenParityProjector.add spinorOddParityProjector = GaussianMatrix.identity 4 ∧
    spinorEvenParityProjector.sub spinorOddParityProjector = spinorChiralParity := by
  decide +kernel

/-- **Theorem (`majoranaBraid_exchanges_modes`)**:
**Ivanov Non-Abelian Majorana Exchange Law**:
For all distinct Majorana modes $a, b \in \text{Fin } 4$ ($a \neq b$), conjugating $\gamma_a$ and $\gamma_b$
by $T_{a,b} = 1 + \gamma_a\gamma_b$ exchanges the two Majorana modes with a topological relative minus sign:
$$T_{a,b} \gamma_a T_{a,b}^\dagger = -2 \gamma_b \;\wedge\; T_{a,b} \gamma_b T_{a,b}^\dagger = +2 \gamma_a.$$ -/
theorem majoranaBraid_exchanges_modes (a b : Fin 4) (hNe : a ≠ b) :
    cliffordMul (cliffordMul (majoranaBraidElem a b) (cliffordGamma a)) (majoranaBraidAdjElem a b) =
      cliffordScale (-2) (cliffordGamma b) ∧
    cliffordMul (cliffordMul (majoranaBraidElem a b) (cliffordGamma b)) (majoranaBraidAdjElem a b) =
      cliffordScale 2 (cliffordGamma a) := by
  revert a b hNe
  decide +kernel

/-- Scaled open-system Lindblad dissipator $2 \mathcal{D}[L](\rho) = 2 L \rho L^\dagger - (L^\dagger L \rho + \rho L^\dagger L)$
over $M_4(\mathbb{Z}[i])$. -/
def lindbladDissipator2 (L rho : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range L.dim
  let rhoNorm : GaussianMatrix :=
    { dim  := L.dim
    , rows := indices.map (fun u => indices.map (fun v => rho.entry u v)) }
  let lDag := L.conjTranspose
  let lDagL := lDag.mul L
  let jumpTerm := ((L.mul rhoNorm).mul lDag).scale 2
  let antiComm := (lDagL.mul rhoNorm).add (rhoNorm.mul lDagL)
  jumpTerm.sub antiComm

/-- Engineered dissipative parity-cooling jump operator $L_{\text{cool}}(a) = \rho(\gamma_a) \Pi_{\text{odd}}$
that detects and resets odd-parity quasiparticle-poisoned states back into the even-parity logical
qubit sector without disturbing even-parity states. -/
def parityCoolingJumpOp (a : Fin 4) : GaussianMatrix :=
  (spinorGamma a).mul spinorOddParityProjector

/-- **Theorem (`lindbladDissipator2_trace_zero`)**:
For every Majorana parity-cooling jump operator $L_{\text{cool}}(a)$ ($a \in \text{Fin } 4$) and
EVERY $4 \times 4$ density matrix $\rho \in M_4(\mathbb{Z}[i])$ (universally quantified over all
matrix entries of $\rho$), the Lindblad dissipator is strictly trace-preserving:
$$\operatorname{Tr}(2 \mathcal{D}[L_{\text{cool}}(a)](\rho)) = 0 + 0i.$$ -/
theorem lindbladDissipator2_trace_zero (a : Fin 4) (rho : GaussianMatrix) :
    (lindbladDissipator2 (parityCoolingJumpOp a) rho).trace = GaussianInt.zero := by
  obtain ⟨n, hn⟩ := a
  have modes : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  have hRange : List.range 4 = [0, 1, 2, 3] := rfl
  rcases modes with rfl | rfl | rfl | rfl
  all_goals
    -- Evaluate the fixed jump matrix before expanding the dissipator on symbolic entries of rho.
    conv => lhs; arg 1; arg 1; cbv
    dsimp only [lindbladDissipator2, GaussianMatrix.mul, GaussianMatrix.conjTranspose,
      GaussianMatrix.scale, GaussianMatrix.add, GaussianMatrix.sub, GaussianMatrix.trace]
    simp only [hRange, GaussianMatrix.entry, GaussianMatrix.listGetGaussianRow,
      GaussianMatrix.listGetGaussian, sumGaussianOver, GaussianInt.mul, GaussianInt.add,
      GaussianInt.sub, GaussianInt.scale, GaussianInt.conj, GaussianInt.zero, List.map,
      GaussianInt.mk.injEq]
    constructor <;> omega

/-- **Theorem (`lindblad_bilocal_preserves_even_sector`)**:
For all Majorana mode pairs $a, b \in \text{Fin } 4$, any bilocal parity-conserving Lindblad jump
operator $L_{a,b} = \rho(\gamma_a \gamma_b)$ preserves the even-parity computational sector with
identically zero dissipative leakage into the odd-parity sector ($\Pi_{\text{odd}} \mathcal{D}[L_{a,b}](\Pi_{\text{even}}) = 0_4$). -/
theorem lindblad_bilocal_preserves_even_sector (a b : Fin 4) :
    let L := (spinorGamma a).mul (spinorGamma b)
    let D := lindbladDissipator2 L spinorEvenParityProjector
    spinorOddParityProjector.mul D = GaussianMatrix.zero 4 ∧
    D.mul spinorOddParityProjector = GaussianMatrix.zero 4 ∧
    D = GaussianMatrix.zero 4 := by
  revert a b
  decide +kernel

/-- **Theorem (`parityCoolingJumpOp_dark_on_even_and_corrects_odd`)**:
For every Majorana mode $a \in \text{Fin } 4$, the engineered parity-cooling jump operator
$L_{\text{cool}}(a) = \rho(\gamma_a) \Pi_{\text{odd}}$ satisfies:
1. **Even-Sector Dark State**: $L_{\text{cool}}(a) \Pi_{\text{even}} = 0_4$ and
   $\mathcal{D}[L_{\text{cool}}(a)](\Pi_{\text{even}}) = 0_4$ (the logical even-parity subspace is
   completely dark to the cooling channel),
2. **Autonomous Odd-to-Even Quasiparticle Reset**:
   $L_{\text{cool}}(a) \Pi_{\text{odd}} L_{\text{cool}}(a)^\dagger = \Pi_{\text{even}}$ and
   $\Pi_{\text{even}} L_{\text{cool}}(a) = L_{\text{cool}}(a)$ (every odd-parity poisoned state is
   autonomously transferred back into the even-parity computational sector!). -/
theorem parityCoolingJumpOp_dark_on_even_and_corrects_odd (a : Fin 4) :
    (parityCoolingJumpOp a).mul spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    lindbladDissipator2 (parityCoolingJumpOp a) spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    ((parityCoolingJumpOp a).mul spinorOddParityProjector).mul (parityCoolingJumpOp a).conjTranspose =
      spinorEvenParityProjector ∧
    spinorEvenParityProjector.mul (parityCoolingJumpOp a) = parityCoolingJumpOp a ∧
    (lindbladDissipator2 (parityCoolingJumpOp a) spinorOddParityProjector).trace = GaussianInt.zero := by
  revert a
  decide +kernel

/-! ## 7. Perturbative Equitable Breaking Score & Grönwall/Duhamel Disorder Leakage Bound (`breakingScore_zero_iff_equitable`, `perturbative_disorder_leakage_bound`) -/

/-- Auxiliary lookup finding the index $i$ of the cell in `part : List (List Nat)` that contains vertex `u`. -/
def cellIndexOfListPartAux (u : Nat) (idx : Nat) : List (List Nat) → Nat
  | [] => 0
  | cell :: rest =>
    if cell.contains u then idx
    else cellIndexOfListPartAux u (idx + 1) rest

/-- Map vertex `u` to its cell index in `part : List (List Nat)`. -/
def cellIndexOfListPart (part : List (List Nat)) (u : Nat) : Nat :=
  cellIndexOfListPartAux u 0 part

/-- Members of cell `j` in `part : List (List Nat)`. -/
def cellMembersAt (part : List (List Nat)) (j : Nat) : List Nat :=
  part[j]?.getD []

/-- **Equitable Breaking Residual Matrix (`equitableBreakingResidual`)**:
Given an $n \times n$ perturbation/disorder matrix $\Delta H$, partition `part : List (List Nat)`
of $n$ vertices into $r$ cells, and candidate $r \times r$ quotient perturbation $Q_\Delta$,
computes the $n \times r$ intertwining defect matrix
$$R(\Delta H, P, Q_\Delta) = \Delta H \cdot P - P \cdot Q_\Delta,$$
whose entry $(u, j)$ is $\sum_{v \in C_j} \Delta H_{u, v} - Q_\Delta(\text{cell}(u), j)$. -/
def equitableBreakingResidual
    (dH : IntMatrix)
    (n r : Nat)
    (part : List (List Nat))
    (Q_d : Nat → Nat → Int) : IntMatrix where
  dim  := n
  rows := (List.range n).map (fun u =>
    (List.range r).map (fun j =>
      cellRowSum dH.entry (cellMembersAt part j) u - Q_d (cellIndexOfListPart part u) j))

/-- Sum a list of natural numbers using right-associative addition (convenient for structural induction). -/
def sumNatListRight : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNatListRight xs

/-- **Perturbative Equitable Breaking Score (`equitableBreakingScore`)**:
Computes the entrywise $\ell_1$ norm $\| \Delta H \cdot P - P \cdot Q_\Delta \|_1 = \sum_{u < n} \sum_{j < r} |R_{u, j}|$
of `equitableBreakingResidual dH n r part Q_d`. -/
def equitableBreakingScore
    (dH : IntMatrix)
    (n r : Nat)
    (part : List (List Nat))
    (Q_d : Nat → Nat → Int) : Nat :=
  let res := equitableBreakingResidual dH n r part Q_d
  sumNatListRight (res.rows.map (fun row => sumNatListRight (row.map Int.natAbs)))

theorem sumNatListRight_eq_zero_iff (xs : List Nat) :
    sumNatListRight xs = 0 ↔ ∀ x, x ∈ xs → x = 0 := by
  induction xs with
  | nil =>
    simp [sumNatListRight]
  | cons x rest ih =>
    simp only [sumNatListRight, Nat.add_eq_zero_iff, List.mem_cons]
    constructor
    · rintro ⟨hx, hrest⟩ y (rfl | hy)
      · exact hx
      · exact (ih.mp hrest) y hy
    · intro hAll
      exact ⟨hAll x (Or.inl rfl), ih.mpr (fun y hy => hAll y (Or.inr hy))⟩

/-- **Theorem (`breakingScore_zero_iff_equitable`)**:
**Equitable Breaking Score Zero Equivalence Theorem**:
1. **Universal Zero-Score $\iff$ Exact Equitability**:
   For ANY $n \times n$ perturbation matrix $\Delta H$, dimensions $n, r \in \mathbb{N}$, partition
   `part : List (List Nat)`, and quotient $Q_\Delta$,
   `equitableBreakingScore dH n r part Q_d = 0` **if and only if** every cell-transition residual vanishes:
   $$\forall u < n,\; \forall j < r,\quad \sum_{v \in C_j} \Delta H_{u,v} = Q_\Delta(\text{cell}(u), j).$$
2. **Exact Intertwining Recovery (`symmetry_preserving_noise_zero_leakage` Special Case)**:
   Whenever `equitableBreakingScore dH n r part Q_d = 0` and `part` assigns every $x \in C_j$ to cell $j$,
   $\Delta H$ intertwines identically with $Q_\Delta$ across all $u < n$ and all quotient states $w$:
   $$(\Delta H (P w))_u = (P (Q_\Delta w))_u.$$
3. **Concrete Majorana-1 Parity Noise Verification**:
   - Parity-preserving bilocal noise `majoranaParityPreserveNoise` on cells `[[0, 1], [2, 3]]` has
     `equitableBreakingScore = 0`,
   - Quasiparticle poisoning noise `majoranaQuasiparticlePoisonNoise` ($\gamma_0$) breaks parity
     equitability with strictly positive breaking score `equitableBreakingScore = 4 > 0`! -/
theorem breakingScore_zero_iff_equitable
    (dH : IntMatrix)
    (n r : Nat)
    (part : List (List Nat))
    (Q_d : Nat → Nat → Int) :
    (equitableBreakingScore dH n r part Q_d = 0 ↔
      ∀ u, u < n → ∀ j, j < r →
        cellRowSum dH.entry (cellMembersAt part j) u = Q_d (cellIndexOfListPart part u) j) ∧
    (equitableBreakingScore dH n r part Q_d = 0 →
      (∀ j, j ∈ List.range r → ∀ x, x ∈ cellMembersAt part j → cellIndexOfListPart part x = j) →
      ∀ (w : Nat → Int) (u : Nat), u < n →
        partitionedMatVec dH.entry (List.range r) (cellMembersAt part)
          (liftQuotientVec (cellIndexOfListPart part) w) u =
        liftQuotientVec (cellIndexOfListPart part) (quotientMatVec Q_d (List.range r) w) u) ∧
    equitableBreakingScore majoranaParityPreserveNoise 4 2 [[0, 1], [2, 3]] majoranaNoiseSymQuotient = 0 ∧
    equitableBreakingScore majoranaQuasiparticlePoisonNoise 4 2 [[0, 1], [2, 3]] (fun _ _ => 0) = 4 := by
  have hIff :
      equitableBreakingScore dH n r part Q_d = 0 ↔
        ∀ u, u < n → ∀ j, j < r →
          cellRowSum dH.entry (cellMembersAt part j) u = Q_d (cellIndexOfListPart part u) j := by
    unfold equitableBreakingScore equitableBreakingResidual
    dsimp only
    rw [sumNatListRight_eq_zero_iff]
    simp only [List.mem_map, List.mem_range]
    constructor
    · intro hRows u hu j hj
      have hRowZero := hRows
        (sumNatListRight ((List.range r).map (fun j =>
          Int.natAbs (cellRowSum dH.entry (cellMembersAt part j) u - Q_d (cellIndexOfListPart part u) j))))
        ⟨(List.range r).map (fun j =>
          cellRowSum dH.entry (cellMembersAt part j) u - Q_d (cellIndexOfListPart part u) j),
          ⟨u, hu, rfl⟩, by rw [List.map_map]; rfl⟩
      rw [sumNatListRight_eq_zero_iff] at hRowZero
      simp only [List.mem_map, List.mem_range] at hRowZero
      have hEntryZero := hRowZero
        (Int.natAbs (cellRowSum dH.entry (cellMembersAt part j) u - Q_d (cellIndexOfListPart part u) j))
        ⟨j, hj, rfl⟩
      omega
    · rintro hAll _ ⟨row, ⟨u, hu, rfl⟩, rfl⟩
      rw [List.map_map, sumNatListRight_eq_zero_iff]
      simp only [List.mem_map, List.mem_range, Function.comp_apply]
      rintro _ ⟨j, hj, rfl⟩
      have hEq := hAll u hu j hj
      omega
  refine ⟨hIff, ?_, by decide +kernel, by decide +kernel⟩
  intro hZero hCells w u hu
  have hRows := hIff.mp hZero u hu
  exact equitable_intertwining_step dH.entry Q_d (cellIndexOfListPart part) (List.range r)
    (cellMembersAt part) w u hCells (fun j hj => hRows j (List.mem_range.mp hj))

/-- Discrete-time Duhamel / Grönwall error propagation recurrence for $K$ propagator steps under
nominal operator norm bound `opNorm` ($\|H\|$) and per-step symmetry-breaking score bound `epsBreak` ($\varepsilon_{\text{break}}$):
$$E_0 = 0, \qquad E_{k+1} = \|H\| \cdot E_k + \varepsilon_{\text{break}} \cdot \|H\|^k.$$ -/
def evalDuhamelLeakageRecurrence (opNorm epsBreak : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => opNorm * evalDuhamelLeakageRecurrence opNorm epsBreak k + epsBreak * (opNorm ^ k)

/-- Exact closed-form identity for `evalDuhamelLeakageRecurrence`:
for EVERY $K \in \mathbb{N}$, $E_K = K \cdot \varepsilon_{\text{break}} \cdot \|H\|^{K-1}$. -/
theorem evalDuhamelLeakageRecurrence_closed_form (opNorm epsBreak K : Nat) :
    evalDuhamelLeakageRecurrence opNorm epsBreak K = K * epsBreak * (opNorm ^ (K - 1)) := by
  induction K with
  | zero => simp [evalDuhamelLeakageRecurrence]
  | succ k ih =>
    cases k with
    | zero =>
      simp [evalDuhamelLeakageRecurrence]
    | succ m =>
      change opNorm * evalDuhamelLeakageRecurrence opNorm epsBreak (m + 1) + epsBreak * (opNorm ^ (m + 1)) =
        (m + 1 + 1) * epsBreak * (opNorm ^ (m + 1))
      rw [ih]
      have hSub : m + 1 - 1 = m := rfl
      rw [hSub, Nat.pow_succ]
      calc opNorm * ((m + 1) * epsBreak * opNorm ^ m) + epsBreak * (opNorm ^ m * opNorm)
        _ = (m + 1) * (epsBreak * (opNorm ^ m * opNorm)) + 1 * (epsBreak * (opNorm ^ m * opNorm)) := by
          ac_rfl
        _ = (m + 1 + 1) * (epsBreak * (opNorm ^ m * opNorm)) := by
          rw [← Nat.add_mul]
        _ = (m + 1 + 1) * epsBreak * (opNorm ^ m * opNorm) := by
          ac_rfl

/-- **Theorem (`perturbative_disorder_leakage_bound`)**:
**Quantitative Perturbative Fabrication-Disorder Leakage Bound (Discrete Duhamel / Grönwall Certificate)**:
Suppose fabrication or thermal disorder $\Delta H$ has equitable breaking score bounded by
`equitableBreakingScore dH n r part Q_d ≤ epsBreak` ($\varepsilon_{\text{break}}$) and the nominal
propagator step has operator norm bound `opNorm` ($\|H\|$). Then for ANY non-negative leaked amplitude
trajectory `leak : Nat → Nat` starting in the equitable/Majorana code space (`leak 0 = 0`) and
satisfying the per-step Duhamel inequality
$$\forall k,\quad \text{leak}(k + 1) \le \|H\| \cdot \text{leak}(k) + \text{equitableBreakingScore}(\Delta H) \cdot \|H\|^k:$$
1. **Closed-Form Duhamel Envelope**: `evalDuhamelLeakageRecurrence opNorm epsBreak K = K * epsBreak * (opNorm ^ (K - 1))` for all $K \in \mathbb{N}$.
2. **Universal Polynomial Leakage Bound**: After $K$ discrete propagator steps, the leaked amplitude
   outside the equitable code space satisfies
   $$\text{leak}(K) \le K \cdot \varepsilon_{\text{break}} \cdot \|H\|^{K - 1}.$$
3. **Zero-Leakage Corollary ($\varepsilon_{\text{break}} = 0$)**: When `epsBreak = 0` (exact symmetry-preserving
   disorder), `leak K = 0` for all $K \in \mathbb{N}$! -/
theorem perturbative_disorder_leakage_bound
    (dH : IntMatrix)
    (n r : Nat)
    (part : List (List Nat))
    (Q_d : Nat → Nat → Int)
    (opNorm epsBreak : Nat)
    (leak : Nat → Nat)
    (hScore : equitableBreakingScore dH n r part Q_d ≤ epsBreak)
    (hInit : leak 0 = 0)
    (hStep : ∀ k, leak (k + 1) ≤ opNorm * leak k + equitableBreakingScore dH n r part Q_d * (opNorm ^ k)) :
    ∀ (K : Nat),
      evalDuhamelLeakageRecurrence opNorm epsBreak K = K * epsBreak * (opNorm ^ (K - 1)) ∧
      leak K ≤ K * epsBreak * (opNorm ^ (K - 1)) ∧
      (epsBreak = 0 → leak K = 0) := by
  have hLeRec : ∀ K, leak K ≤ evalDuhamelLeakageRecurrence opNorm epsBreak K := by
    intro K
    induction K with
    | zero =>
      simp [evalDuhamelLeakageRecurrence, hInit]
    | succ k ih =>
      dsimp only [evalDuhamelLeakageRecurrence]
      have hk := hStep k
      have h1 : opNorm * leak k ≤ opNorm * evalDuhamelLeakageRecurrence opNorm epsBreak k :=
        Nat.mul_le_mul_left opNorm ih
      have h2 : equitableBreakingScore dH n r part Q_d * (opNorm ^ k) ≤ epsBreak * (opNorm ^ k) :=
        Nat.mul_le_mul_right (opNorm ^ k) hScore
      omega
  intro K
  have hClosed := evalDuhamelLeakageRecurrence_closed_form opNorm epsBreak K
  have hBound : leak K ≤ K * epsBreak * (opNorm ^ (K - 1)) := by
    rw [← hClosed]
    exact hLeRec K
  refine ⟨hClosed, hBound, ?_⟩
  intro hZero
  rw [hZero] at hBound
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.le_zero] at hBound
  exact hBound

/-! ## 2. Symmetric `StrictOpenHypergraph` Equitable Quotient Compression & `quotientHypergraphSlot` (`quotientOpenHypergraph_intertwines_eval_and_adjoint`, `quotientHypergraph_moved_pin_blocks`) -/

/-- Partition of a 4-channel parallel hardware/photonic/attention hypergraph into $r = 2$ equitable
symmetry cells $C_0 = \{0, 1\}$ and $C_1 = \{2, 3\}$. -/
def sym4LaneCellOf : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 0

/-- Construct an $N = 4$-channel `StrictOpenHypergraph` where each channel lane $u \in \{0, 1, 2, 3\}$
processes its input pair $(x_u, y_u)$ through a channel-weighted stage-1 scale `.scale w_u` followed
by a shared stage-2 operation `op2 : OpticOp`:
- Lane $u \in \{0, 1, 2, 3\}$ occupies a 6-wire slice `[6*u .. 6*u + 5]`:
  * `6*u + 0`: boundary input $x_u$,
  * `6*u + 1`: boundary input $y_u$ (fans out to both stage 1 and stage 2),
  * `6*u + 2`: stage-1 output $m_u = w_u \cdot x_u$,
  * `6*u + 3`: boundary output $z_u = \text{op}_2(m_u, y_u)$,
  * `6*u + 4`, `6*u + 5`: internal scratch wires. -/
def buildSymmetric4LaneHypergraph
    (w0 w1 w2 w3 : Int)
    (op2 : OpticOp) : StrictOpenHypergraph :=
  let lane0 := opticFwdHyperEdges (.scale w0) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5
  let lane1 := opticFwdHyperEdges (.scale w1) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11
  let lane2 := opticFwdHyperEdges (.scale w2) 12 13 14 16 ++ opticFwdHyperEdges op2 14 13 15 17
  let lane3 := opticFwdHyperEdges (.scale w3) 18 19 20 22 ++ opticFwdHyperEdges op2 20 19 21 23
  mkStrictOpenHypergraph 24
    [0, 1, 6, 7, 12, 13, 18, 19]
    [3, 9, 15, 21]
    (reindexHyperEdges (lane0 ++ lane1 ++ lane2 ++ lane3))

/-- **Equitable Quotient Open Hypergraph Compression (`quotientOpenHypergraph`)**:
Compresses the $N = 4$-channel symmetric `StrictOpenHypergraph` (with equitable cell weights
$w_0 = w_1 = W_0$ on cell $C_0 = \{0, 1\}$ and $w_2 = w_3 = W_1$ on cell $C_1 = \{2, 3\}$)
down to an $r = 2$-cell quotient `StrictOpenHypergraph` ($12$ wires instead of $24$, and half the
hyperedges in both the forward pass and `compileGraphAdjoint`!). -/
def quotientOpenHypergraph
    (W0 W1 : Int)
    (op2 : OpticOp) : StrictOpenHypergraph :=
  let cell0 := opticFwdHyperEdges (.scale W0) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5
  let cell1 := opticFwdHyperEdges (.scale W1) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11
  mkStrictOpenHypergraph 12
    [0, 1, 6, 7]
    [3, 9]
    (reindexHyperEdges (cell0 ++ cell1))

/-- Initial wire environment for the compressed $r = 2$-cell quotient hypergraph (and its adjoint
`compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2)`, whose output cotangent seed wires are
`12` and `13`). -/
def quotientHypergraphInitEnv
    (x0 y0 x1 y1 dOut0 dOut1 : Int) (w : Nat) : Int :=
  match w with
  | 0  => x0
  | 1  => y0
  | 6  => x1
  | 7  => y1
  | 12 => dOut0
  | 13 => dOut1
  | _  => 0

/-- Cell-constant lifted wire environment for the $N = 4$-lane symmetric hypergraph (and its adjoint
`compileGraphAdjoint (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2)`, whose output cotangent seed
wires are `24, 25, 26, 27`), lifting cell $C_0$'s inputs $(x_0, y_0, dOut_0)$ to lanes $0, 1$ and
cell $C_1$'s inputs $(x_1, y_1, dOut_1)$ to lanes $2, 3$. -/
def liftSymmetric4LaneInitEnv
    (x0 y0 x1 y1 dOut0 dOut1 : Int) (w : Nat) : Int :=
  match w with
  | 0  => x0
  | 1  => y0
  | 6  => x0
  | 7  => y0
  | 12 => x1
  | 13 => y1
  | 18 => x1
  | 19 => y1
  | 24 => dOut0
  | 25 => dOut0
  | 26 => dOut1
  | 27 => dOut1
  | _  => 0

/-- Lift the 2-cell forward output vector `[z0, z1]` of `quotientOpenHypergraph` to the 4-lane
output vector `[z0, z0, z1, z1]` across $C_0 = \{0, 1\}$ and $C_1 = \{2, 3\}$. -/
def liftQuotientFwdOutputs (qOut : List Int) : List Int :=
  [qOut.getD 0 0, qOut.getD 0 0, qOut.getD 1 0, qOut.getD 1 0]

/-- Lift the 6-element adjoint output vector `[z0, z1, dx0, dy0, dx1, dy1]` of
`compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2)` to the 12-element 4-lane adjoint output
vector `[z0, z0, z1, z1, dx0, dy0, dx0, dy0, dx1, dy1, dx1, dy1]`. -/
def liftQuotientAdjointOutputs (qAdjOut : List Int) : List Int :=
  let z0  := qAdjOut.getD 0 0
  let z1  := qAdjOut.getD 1 0
  let dx0 := qAdjOut.getD 2 0
  let dy0 := qAdjOut.getD 3 0
  let dx1 := qAdjOut.getD 4 0
  let dy1 := qAdjOut.getD 5 0
  [z0, z0, z1, z1, dx0, dy0, dx0, dy0, dx1, dy1, dx1, dy1]

private theorem quotientOpenHypergraph_fwd_comb (W0 W1 : Int) (op2 : OpticOp)
    (x0 y0 x1 y1 dOut0 dOut1 : Int) :
    evalHypergraphComb (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2)
      (liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1) =
    liftQuotientFwdOutputs (evalHypergraphComb (quotientOpenHypergraph W0 W1 op2)
      (quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1)) := by
  unfold buildSymmetric4LaneHypergraph quotientOpenHypergraph
  rw [evalHypergraphComb_mkStrictOpenHypergraph_reindex, evalHypergraphComb_mkStrictOpenHypergraph_reindex]
  cases op2 <;>
    dsimp [opticFwdHyperEdges, evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp,
      liftSymmetric4LaneInitEnv, quotientHypergraphInitEnv, liftQuotientFwdOutputs,
      List.foldl, List.map, list_getD_zero_cons, list_getD_one_cons] <;> rfl

private theorem quotient_adj_eq_full (W0 W1 : Int) (op2 : OpticOp) :
    compileGraphAdjoint (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2) =
      compileGraphAdjointAux 24 [0, 1, 6, 7, 12, 13, 18, 19] [3, 9, 15, 21]
        (reindexHyperEdges
          ((opticFwdHyperEdges (.scale W0) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5) ++
           (opticFwdHyperEdges (.scale W0) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11) ++
           (opticFwdHyperEdges (.scale W1) 12 13 14 16 ++ opticFwdHyperEdges op2 14 13 15 17) ++
           (opticFwdHyperEdges (.scale W1) 18 19 20 22 ++ opticFwdHyperEdges op2 20 19 21 23))) := by
  unfold compileGraphAdjoint buildSymmetric4LaneHypergraph
  change compileGraphAdjointAux (List.replicate 24 64).length [0, 1, 6, 7, 12, 13, 18, 19] [3, 9, 15, 21]
    (extractHyperEdges (mkStrictOpenHypergraph 24 [0, 1, 6, 7, 12, 13, 18, 19] [3, 9, 15, 21] _)) = _
  rw [List.length_replicate, extractHyperEdges_mkStrictOpenHypergraph]

private theorem quotient_adj_eq_quot (W0 W1 : Int) (op2 : OpticOp) :
    compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2) =
      compileGraphAdjointAux 12 [0, 1, 6, 7] [3, 9]
        (reindexHyperEdges
          ((opticFwdHyperEdges (.scale W0) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5) ++
           (opticFwdHyperEdges (.scale W1) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11))) := by
  unfold compileGraphAdjoint quotientOpenHypergraph
  change compileGraphAdjointAux (List.replicate 12 64).length [0, 1, 6, 7] [3, 9]
    (extractHyperEdges (mkStrictOpenHypergraph 12 [0, 1, 6, 7] [3, 9] _)) = _
  rw [List.length_replicate, extractHyperEdges_mkStrictOpenHypergraph]

private abbrev QuotientAdjGoal (W0 W1 : Int) (op2 : OpticOp) (x0 y0 x1 y1 dOut0 dOut1 : Int) : Prop :=
  evalHypergraphComb (compileGraphAdjoint (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2))
    (liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1) =
  liftQuotientAdjointOutputs (evalHypergraphComb (compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2))
    (quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1))

local macro "quotient_adj_step" : tactic =>
  `(tactic| (
    dsimp only [QuotientAdjGoal]
    rw [quotient_adj_eq_full, quotient_adj_eq_quot,
        evalHypergraphComb_compileGraphAdjointAux, evalHypergraphComb_compileGraphAdjointAux]
    dsimp [evalBuildGraphAdjointComb, buildGraphAdjointState,
      opticFwdHyperEdges, reindexHyperEdges, reindexHyperEdgesAux,
      seedCotangentStateAux, accumWireCotangent, emitAndAccum, upsertCotWire,
      pullbackHyperEdge, wireAt, emitRevEdge, resolveInputCotWires, setCotWire,
      evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp,
      liftSymmetric4LaneInitEnv, quotientHypergraphInitEnv, liftQuotientAdjointOutputs,
      List.reverse, List.reverseAux, List.foldl, List.map, List.lookup,
      list_getD_zero_cons, list_getD_one_cons, list_getD_two_cons, list_getD_nil]
    rfl))

private theorem quotient_adj_add (W0 W1 x0 y0 x1 y1 d0 d1 : Int) :
    QuotientAdjGoal W0 W1 .add x0 y0 x1 y1 d0 d1 := by
  quotient_adj_step

private theorem quotient_adj_sub (W0 W1 x0 y0 x1 y1 d0 d1 : Int) :
    QuotientAdjGoal W0 W1 .sub x0 y0 x1 y1 d0 d1 := by
  quotient_adj_step

private theorem quotient_adj_mul (W0 W1 x0 y0 x1 y1 d0 d1 : Int) :
    QuotientAdjGoal W0 W1 .mul x0 y0 x1 y1 d0 d1 := by
  quotient_adj_step

private theorem quotient_adj_scale (W0 W1 k x0 y0 x1 y1 d0 d1 : Int) :
    QuotientAdjGoal W0 W1 (.scale k) x0 y0 x1 y1 d0 d1 := by
  quotient_adj_step

private theorem quotient_adj_square (W0 W1 x0 y0 x1 y1 d0 d1 : Int) :
    QuotientAdjGoal W0 W1 .square x0 y0 x1 y1 d0 d1 := by
  quotient_adj_step

private theorem quotient_adj_linearMac (W0 W1 w x0 y0 x1 y1 d0 d1 : Int) :
    QuotientAdjGoal W0 W1 (.linearMac w) x0 y0 x1 y1 d0 d1 := by
  quotient_adj_step

private theorem quotient_adj_bilinear (W0 W1 c x0 y0 x1 y1 d0 d1 : Int) :
    QuotientAdjGoal W0 W1 (.bilinear c) x0 y0 x1 y1 d0 d1 := by
  quotient_adj_step

private theorem quotientOpenHypergraph_adj_comb (W0 W1 : Int) (op2 : OpticOp)
    (x0 y0 x1 y1 dOut0 dOut1 : Int) : QuotientAdjGoal W0 W1 op2 x0 y0 x1 y1 dOut0 dOut1 := by
  cases op2 with
  | add => exact quotient_adj_add W0 W1 x0 y0 x1 y1 dOut0 dOut1
  | sub => exact quotient_adj_sub W0 W1 x0 y0 x1 y1 dOut0 dOut1
  | mul => exact quotient_adj_mul W0 W1 x0 y0 x1 y1 dOut0 dOut1
  | scale k => exact quotient_adj_scale W0 W1 k x0 y0 x1 y1 dOut0 dOut1
  | square => exact quotient_adj_square W0 W1 x0 y0 x1 y1 dOut0 dOut1
  | linearMac w => exact quotient_adj_linearMac W0 W1 w x0 y0 x1 y1 dOut0 dOut1
  | bilinear c => exact quotient_adj_bilinear W0 W1 c x0 y0 x1 y1 dOut0 dOut1

/-- **Theorem (`quotientOpenHypergraph_intertwines_eval_and_adjoint`)**:
**Universal Symmetric `StrictOpenHypergraph` Forward & Reverse-Mode AD Quotient Intertwining Theorem**:
For EVERY stage-2 operation `op2 : OpticOp`, EVERY symmetry-cell weight pair `W0, W1 : Int`,
EVERY cell-constant primal input state `x0, y0, x1, y1 : Int`, and EVERY cell-constant upstream
cotangent seed `dOut0, dOut1 : Int`:
1. **Structural Well-Formedness & $2\times$ Compression**:
   Both `buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2` ($24$ wires) and its compressed quotient
   `quotientOpenHypergraph W0 W1 op2` ($12$ wires) are well-formed (`wf = true`).
2. **Combinational & Wavefront-Layered Forward Intertwining (`evalHypergraphComb` & `evalHypergraphLayered`)**:
   Evaluating the 4-lane symmetric hypergraph via `evalHypergraphComb` or `evalHypergraphLayered`
   on the lifted cell-constant environment produces the exact lifted output of the compressed 2-cell
   quotient hypergraph:
   $$\text{evalHypergraphLayered}(G_{\text{full}}, P w) = P_{\text{out}}\!\left(\text{evalHypergraphLayered}(G_{\text{quot}}, w)\right).$$
3. **Whole-DAG Reverse-Mode AD Intertwining (`compileGraphAdjoint`)**:
   Running whole-DAG reverse-mode AD `compileGraphAdjoint` on the 4-lane symmetric hypergraph
   (via `evalHypergraphComb` or `evalHypergraphLayered`) produces the **exact lifted primal outputs
   AND lifted input cotangent gradients $(\partial L / \partial x_u, \partial L / \partial y_u)$**
   of `compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2)`! -/
theorem quotientOpenHypergraph_intertwines_eval_and_adjoint
    (W0 W1 : Int)
    (op2 : OpticOp)
    (x0 y0 x1 y1 dOut0 dOut1 : Int) :
    let gFull := buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2
    let gQuot := quotientOpenHypergraph W0 W1 op2
    let envFull := liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1
    let envQuot := quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1
    let adjFull := compileGraphAdjoint gFull
    let adjQuot := compileGraphAdjoint gQuot
    -- 1. Well-formedness & compression ratio
    gFull.wf = true ∧
    gQuot.wf = true ∧
    gFull.nodeTypes.length = 24 ∧
    gQuot.nodeTypes.length = 12 ∧
    -- 2. Forward combinational & wavefront-layered intertwining
    evalHypergraphComb gFull envFull = liftQuotientFwdOutputs (evalHypergraphComb gQuot envQuot) ∧
    evalHypergraphLayered gFull envFull = liftQuotientFwdOutputs (evalHypergraphLayered gQuot envQuot) ∧
    -- 3. Whole-DAG reverse-mode AD (compileGraphAdjoint) combinational & layered intertwining
    evalHypergraphComb adjFull envFull = liftQuotientAdjointOutputs (evalHypergraphComb adjQuot envQuot) ∧
    evalHypergraphLayered adjFull envFull = liftQuotientAdjointOutputs (evalHypergraphLayered adjQuot envQuot) := by
  have hWfFull : (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2).wf = true := by cases op2 <;> rfl
  have hWfQuot : (quotientOpenHypergraph W0 W1 op2).wf = true := by cases op2 <;> rfl
  have hFwd := quotientOpenHypergraph_fwd_comb W0 W1 op2 x0 y0 x1 y1 dOut0 dOut1
  have hAdj := quotientOpenHypergraph_adj_comb W0 W1 op2 x0 y0 x1 y1 dOut0 dOut1
  dsimp only
  refine ⟨hWfFull, hWfQuot, rfl, rfl, hFwd, ?_, hAdj, ?_⟩
  · rw [(evalHypergraph_pipelined_eq_comb _ _).1, (evalHypergraph_pipelined_eq_comb _ _).1, hFwd]
  · rw [(evalHypergraph_pipelined_eq_comb _ _).1, (evalHypergraph_pipelined_eq_comb _ _).1, hAdj]

/-- Specialization candidates for `quotientHypergraphSlot`:
- `.quotientCompressed gFull gQuot weightPins eqOk`: the compressed $r$-lane quotient hypergraph
  `gQuot`, supported by the `LeafPin` list `weightPins` pinning every channel weight parameter
  $w_i = W_{\text{cell}(i)}$ across symmetry cells,
- `.unreducedFull gFull`: the unreduced $N$-lane hypergraph fallback (no symmetry pins required). -/
inductive QuotientHypergraphCandidate where
  | quotientCompressed
      (gFull : StrictOpenHypergraph)
      (gQuot : StrictOpenHypergraph)
      (weightPins : List LeafPin)
      (equitableOk : Bool)
  | unreducedFull (gFull : StrictOpenHypergraph)

/-- Support pins for a `QuotientHypergraphCandidate`. -/
def QuotientHypergraphCandidate.supports : QuotientHypergraphCandidate → List LeafPin
  | .quotientCompressed _ _ pins _ => pins
  | .unreducedFull _ => []

/-- Admission judge for a `QuotientHypergraphCandidate`. -/
def QuotientHypergraphCandidate.judge : QuotientHypergraphCandidate → Bool
  | .quotientCompressed gFull gQuot _ eqOk => gFull.wf && gQuot.wf && eqOk
  | .unreducedFull gFull => gFull.wf

/-- **The Quotient Hypergraph Specialization Slot (`quotientHypergraphSlot`)**:
Pins the symmetry-preserving channel weight parameters (`w_i = w_j` within each equitable cell)
and automatically invalidates the compressed $r$-lane quotient candidate whenever an outer `.obend`
layer overrides a channel weight and breaks equitability. -/
def quotientHypergraphSlot : Slot LeafPin QuotientHypergraphCandidate :=
  ⟨QuotientHypergraphCandidate.supports, QuotientHypergraphCandidate.judge⟩

/-- Construct a `LeafPin` pinning channel weight key `key` (e.g. `"weights.w1"`) to integer literal `w`. -/
def mkChannelWeightPin (key : String) (w : Nat) : LeafPin :=
  ⟨.layer key, .nat w⟩

/-- The 4 symmetry-preserving channel weight pins for a 4-lane hypergraph with cell weights $W_0, W_1 \in \mathbb{N}$
($w_0 = W_0, w_1 = W_0$ in cell $C_0$, and $w_2 = W_1, w_3 = W_1$ in cell $C_1$). -/
def sym4LaneWeightPins (W0 W1 : Nat) : List LeafPin :=
  [ mkChannelWeightPin "weights.w0" W0
  , mkChannelWeightPin "weights.w1" W0
  , mkChannelWeightPin "weights.w2" W1
  , mkChannelWeightPin "weights.w3" W1 ]

/-- Build a `LeafView` at `clock` assigning channel weights `(w0, w1, w2, w3)` to `"weights.w0" .. "weights.w3"`. -/
def mkChannelWeightView (clock w0 w1 w2 w3 : Nat) : LeafView where
  clock := clock
  decl
    | .layer "weights.w0" => some (.nat w0)
    | .layer "weights.w1" => some (.nat w1)
    | .layer "weights.w2" => some (.nat w2)
    | .layer "weights.w3" => some (.nat w3)
    | _ => none

/-- **Theorem (`quotientHypergraph_moved_pin_blocks`)**:
1. **Universal Moved-Pin Blocking (`read_blocked_exact`)**:
   Whenever a compressed quotient candidate `cand = .quotientCompressed gFull gQuot pins true` is
   admitted (`quotientHypergraphSlot.judge cand = true`), if ANY symmetry-preserving channel weight
   pin `p ∈ pins` ceases to hold at `v : LeafView` (`holdsAt v p = false`), then reading
   `quotientHypergraphSlot` at `v` immediately returns `.blocked cand d` with `p ∈ d` and
   `∀ q, q ∈ d ↔ q ∈ pins ∧ holdsAt v q = false`, AND `slotAdvance.advance` falls back to
   `.ok (.unreducedFull gFull)` in 1 cycle!
2. **Concrete `.obend` Single-Channel Weight Override Verification**:
   - At clock $0$ (`vSym := mkChannelWeightView 0 5 5 7 7`, where $w_0 = w_1 = 5$ and $w_2 = w_3 = 7$
     preserve equitability), the compressed 2-lane quotient candidate is `.usable`.
   - At clock $1$ (`vBroken := mkChannelWeightView 1 5 99 7 7`, where an outer `.obend` layer overrides
     a single channel weight $w_1 := 99 \neq 5$ and breaks equitability), `quotientHypergraphSlot.read`
     blocks the compressed quotient candidate in 1 cycle, naming the exact broken pin cell
     `[.layer "weights.w1"]`! -/
theorem quotientHypergraph_moved_pin_blocks
    (v : LeafView)
    (gFull gQuot : StrictOpenHypergraph)
    (pins : List LeafPin)
    (hWfFull : gFull.wf = true)
    (hWfQuot : gQuot.wf = true)
    (p : LeafPin)
    (hp : p ∈ pins)
    (hd : holdsAt v p = false) :
    let cand := QuotientHypergraphCandidate.quotientCompressed gFull gQuot pins true
    let fallback := QuotientHypergraphCandidate.unreducedFull gFull
    (∃ d,
      quotientHypergraphSlot.read (holdsAt v) (some cand) = .blocked cand d ∧
      p ∈ d ∧
      (∀ q, q ∈ d ↔ q ∈ pins ∧ holdsAt v q = false)) ∧
    (slotAdvance : Advance LeafView LeafPin QuotientHypergraphCandidate).advance
      quotientHypergraphSlot v [cand, fallback] (some cand) = .ok fallback ∧
    (let gFullConcrete := buildSymmetric4LaneHypergraph 5 5 7 7 .add
     let gQuotConcrete := quotientOpenHypergraph 5 7 .add
     let pinsConcrete := sym4LaneWeightPins 5 7
     let candConcrete := QuotientHypergraphCandidate.quotientCompressed
                           gFullConcrete gQuotConcrete pinsConcrete true
     let vSym := mkChannelWeightView 0 5 5 7 7
     let vBroken := mkChannelWeightView 1 5 99 7 7
     quotientHypergraphSlot.usable (holdsAt vSym) candConcrete = true ∧
     quotientHypergraphSlot.usable (holdsAt vBroken) candConcrete = false ∧
     (quotientHypergraphSlot.dead (holdsAt vBroken) candConcrete).map LeafPin.cell =
       [.layer "weights.w1"]) := by
  dsimp only
  let cand := QuotientHypergraphCandidate.quotientCompressed gFull gQuot pins true
  let fallback := QuotientHypergraphCandidate.unreducedFull gFull
  have hJudge : quotientHypergraphSlot.judge cand = true := by
    simp [quotientHypergraphSlot, QuotientHypergraphCandidate.judge, cand, hWfFull, hWfQuot]
  have hMemDead : p ∈ quotientHypergraphSlot.dead (holdsAt v) cand :=
    (mem_dead_iff quotientHypergraphSlot (holdsAt v) cand p).2 ⟨hp, hd⟩
  have hread : ∃ d,
      quotientHypergraphSlot.read (holdsAt v) (some cand) = .blocked cand d ∧ p ∈ d := by
    unfold Slot.read
    simp only [hJudge, ite_true]
    cases hdd : quotientHypergraphSlot.dead (holdsAt v) cand with
    | nil =>
      rw [hdd] at hMemDead
      cases hMemDead
    | cons g t =>
      exact ⟨g :: t, rfl, hdd ▸ hMemDead⟩
  obtain ⟨d, hr, hpd⟩ := hread
  have hRead : ∃ d,
      quotientHypergraphSlot.read (holdsAt v) (some cand) = .blocked cand d ∧
      p ∈ d ∧
      (∀ q, q ∈ d ↔ q ∈ pins ∧ holdsAt v q = false) :=
    ⟨d, hr, hpd, (read_blocked_exact quotientHypergraphSlot _ _ _ _ hr).2⟩
  have hNotUsable : quotientHypergraphSlot.usable (holdsAt v) cand = false := by
    unfold Slot.usable
    cases hdd : quotientHypergraphSlot.dead (holdsAt v) cand with
    | nil =>
      rw [hdd] at hMemDead
      cases hMemDead
    | cons _ _ =>
      simp [List.isEmpty]
  have hFallbackUsable : quotientHypergraphSlot.usable (holdsAt v) fallback = true := by
    simp [Slot.usable, Slot.dead, quotientHypergraphSlot,
      QuotientHypergraphCandidate.supports, QuotientHypergraphCandidate.judge, fallback, hWfFull]
  have hAdv :
      (slotAdvance : Advance LeafView LeafPin QuotientHypergraphCandidate).advance
        quotientHypergraphSlot v [cand, fallback] (some cand) = .ok fallback := by
    refine (incumbent_choice quotientHypergraphSlot v [cand, fallback] (some cand) fallback).2
      (.inr ⟨fun c hc => by cases hc; exact hNotUsable, ?_⟩)
    simp [Slot.select, Slot.alternatives, hNotUsable, hFallbackUsable]
  refine ⟨hRead, hAdv, ?_⟩
  decide +kernel

end Obend.Hardware.QuantumMatter
end
