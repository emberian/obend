module
/-
# Obend.Crypto.DualSpine — Lattice Ajtai / `PikkuFold` Norm Guard & Cross-Assumption `DualPCS`

Unifies the **Lattice Module-SIS spine** (`PikkuFold 2026/1809`, `Akita 2026/1983`, `LaBinius 2026/2260`)
with the **Hash-UDR spine** (`Canopy` / `Magnetar` / `Sable`) under one polymorphic `Sumcheck` PIOP:
1. **Short-Integer Ajtai Module-SIS Commitment (`ajtaiCommit`)**:
   Additive homomorphism `ajtaiCommitRaw_add` / `ajtaiCommit_add`, $\ell_\infty$ norm bound
   `ShortNormBound β w`, and `ModuleSISHard` collision-to-short-kernel reduction.
2. **`PikkuFold` (`ePrint 2026/1809`) Ternary $\{-1, 0, 1\}$ Projection Guard**:
   `applyTernaryProj` and `normInf_ternaryProj_le`, proving that a ternary projection matrix of
   row weight $\le k$ strictly bounds output $\ell_\infty$ norm by $k \cdot \beta$.
3. **Gadget-Decomposed `ajtaiLatticePCS` & `Akita` `SparseOneHotCommit` over `Goldilocks`**:
   Decomposes each 64-bit `Goldilocks` element into four 16-bit limbs ($\|\mathbf{w}\|_\infty \le 65535$),
   proving `ajtai_double_open_yields_sis_kernel`, `ajtaiLatticePCS_bindingSound_of_sisHard`, and
   $O(\text{rows})$ single-column `SparseOneHotCommit`.
4. **Cross-Assumption `DualPCS P₁ P₂` Product Combinator**:
   Pairs any two `MultilinearPCS R` schemes under one shared Fenzi-bound `Sumcheck` claim,
   proving `dualPCS_completeness` and **`dualPCS_sound_of_either`**:
   `BindingSound P₁ ∨ BindingSound P₂ → BindingSound (DualPCS P₁ P₂)`.
-/
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Crypto.PCS

@[expose] public section
namespace Obend.Crypto

open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Apps.ZkNtt

set_option autoImplicit false

/-! ## 1. Integer Lattice Vectors, $\ell_\infty$ Norm & `ShortNormBound` -/

/-- $\ell_\infty$ norm $\max_i |w_i|$ of an integer lattice vector. -/
def normInf : List Int → Nat
  | [] => 0
  | x :: xs => Nat.max x.natAbs (normInf xs)

/-- Short $\ell_\infty$ witness norm guard $\|\mathbf{w}\|_\infty \le \beta$. -/
def ShortNormBound (β : Nat) (w : List Int) : Prop :=
  normInf w ≤ β

/-- Executable short-norm check. -/
def checkShortNorm (β : Nat) (w : List Int) : Bool :=
  decide (normInf w ≤ β)

theorem checkShortNorm_iff (β : Nat) (w : List Int) :
    checkShortNorm β w = true ↔ ShortNormBound β w := by
  simp [checkShortNorm, ShortNormBound]

theorem normInf_cons_le_iff {x : Int} {xs : List Int} {B : Nat} :
    normInf (x :: xs) ≤ B ↔ x.natAbs ≤ B ∧ normInf xs ≤ B := by
  simp only [normInf, Nat.max_le]

theorem mem_natAbs_le_normInf {x : Int} {w : List Int} (hx : x ∈ w) :
    x.natAbs ≤ normInf w := by
  induction w with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [normInf]
    rcases hx with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem normInf_le_of_forall {w : List Int} {B : Nat}
    (h : ∀ x ∈ w, x.natAbs ≤ B) : normInf w ≤ B := by
  induction w with
  | nil => exact Nat.zero_le B
  | cons x xs ih =>
    rw [normInf_cons_le_iff]
    exact ⟨h x (.head xs), ih (fun y hy => h y (.tail x hy))⟩

/-- Coordinate-wise integer vector addition. -/
def vecAdd : List Int → List Int → List Int
  | x :: xs, y :: ys => (x + y) :: vecAdd xs ys
  | _, _ => []

/-- Coordinate-wise integer vector subtraction. -/
def vecSub : List Int → List Int → List Int
  | x :: xs, y :: ys => (x - y) :: vecSub xs ys
  | _, _ => []

theorem vecAdd_length : ∀ (u v : List Int), u.length = v.length → (vecAdd u v).length = u.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    simp [vecAdd, vecAdd_length xs ys h]

theorem vecSub_length : ∀ (u v : List Int), u.length = v.length → (vecSub u v).length = u.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    simp [vecSub, vecSub_length xs ys h]

theorem normInf_vecAdd_le : ∀ (u v : List Int), normInf (vecAdd u v) ≤ normInf u + normInf v
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | x :: xs, y :: ys => by
    simp only [vecAdd, normInf]
    rw [Nat.max_le]
    refine ⟨?_, ?_⟩
    · have htri : (x + y).natAbs ≤ x.natAbs + y.natAbs := Int.natAbs_add_le x y
      have hx : x.natAbs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_left _ _
      have hy : y.natAbs ≤ Nat.max y.natAbs (normInf ys) := Nat.le_max_left _ _
      omega
    · have ih := normInf_vecAdd_le xs ys
      have hx : normInf xs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_right _ _
      have hy : normInf ys ≤ Nat.max y.natAbs (normInf ys) := Nat.le_max_right _ _
      omega

theorem normInf_vecSub_le : ∀ (u v : List Int), normInf (vecSub u v) ≤ normInf u + normInf v
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | x :: xs, y :: ys => by
    simp only [vecSub, normInf]
    rw [Nat.max_le]
    refine ⟨?_, ?_⟩
    · have htri : (x - y).natAbs ≤ x.natAbs + y.natAbs := by
        have h := Int.natAbs_add_le x (-y)
        simpa [Int.sub_eq_add_neg, Int.natAbs_neg] using h
      have hx : x.natAbs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_left _ _
      have hy : y.natAbs ≤ Nat.max y.natAbs (normInf ys) := Nat.le_max_left _ _
      omega
    · have ih := normInf_vecSub_le xs ys
      have hx : normInf xs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_right _ _
      have hy : normInf ys ≤ Nat.max y.natAbs (normInf ys) := Nat.le_max_right _ _
      omega

theorem vecSub_nonzero_of_ne :
    ∀ {u v : List Int}, u.length = v.length → u ≠ v → ∃ z ∈ vecSub u v, z ≠ 0
  | [], [], _, hne => absurd rfl hne
  | x :: xs, y :: ys, hlen, hne => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    by_cases hxy : x = y
    · subst hxy
      have hTail : xs ≠ ys := fun h => hne (congrArg (x :: ·) h)
      obtain ⟨z, hzMem, hzNe⟩ := vecSub_nonzero_of_ne hlen hTail
      exact ⟨z, List.mem_cons_of_mem _ hzMem, hzNe⟩
    · exact ⟨x - y, .head _, by omega⟩

/-! ## 2. `PikkuFold` (`ePrint 2026/1809`) Ternary $\{-1, 0, 1\}$ Projection & Norm Guard -/

/-- Ternary projection coefficient in $\{-1, 0, +1\}$. -/
inductive TernaryCoeff where
  | negOne
  | zero
  | one
  deriving DecidableEq, Repr

/-- Number of non-zero ($\pm 1$) entries in a ternary projection row. -/
def ternaryRowWeight : List TernaryCoeff → Nat
  | [] => 0
  | .zero :: cs => ternaryRowWeight cs
  | .negOne :: cs => 1 + ternaryRowWeight cs
  | .one :: cs => 1 + ternaryRowWeight cs

/-- Apply one ternary row in $\{-1, 0, +1\}^m$ to an integer witness `w` using pure add/sub. -/
def applyTernaryRow : List TernaryCoeff → List Int → Int
  | .negOne :: cs, x :: xs => -x + applyTernaryRow cs xs
  | .zero :: cs, _ :: xs => applyTernaryRow cs xs
  | .one :: cs, x :: xs => x + applyTernaryRow cs xs
  | _, _ => 0

/-- **`PikkuFold` (`2026/1809`) Ternary Projection Step**:
    Projects witness `w` by a ternary matrix `proj : List (List TernaryCoeff)` without field/ring
    multiplications, preserving strict linear $\ell_\infty$ norm control. -/
def applyTernaryProj (proj : List (List TernaryCoeff)) (w : List Int) : List Int :=
  proj.map fun row => applyTernaryRow row w

theorem natAbs_applyTernaryRow_le :
    ∀ (row : List TernaryCoeff) (w : List Int),
      (applyTernaryRow row w).natAbs ≤ ternaryRowWeight row * normInf w
  | [], _ => Nat.zero_le _
  | .negOne :: _, [] => Nat.zero_le _
  | .zero :: _, [] => Nat.zero_le _
  | .one :: _, [] => Nat.zero_le _
  | .zero :: cs, x :: xs => by
    simp only [applyTernaryRow, ternaryRowWeight, normInf]
    have ih := natAbs_applyTernaryRow_le cs xs
    have hle : normInf xs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_right _ _
    exact Nat.le_trans ih (Nat.mul_le_mul_left (ternaryRowWeight cs) hle)
  | .one :: cs, x :: xs => by
    simp only [applyTernaryRow, ternaryRowWeight, normInf]
    have htri : (x + applyTernaryRow cs xs).natAbs ≤
        x.natAbs + (applyTernaryRow cs xs).natAbs := Int.natAbs_add_le _ _
    have ih := natAbs_applyTernaryRow_le cs xs
    have hx : x.natAbs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_left _ _
    have hxs : normInf xs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_right _ _
    have hmul : ternaryRowWeight cs * normInf xs ≤
        ternaryRowWeight cs * Nat.max x.natAbs (normInf xs) :=
      Nat.mul_le_mul_left _ hxs
    rw [Nat.add_mul, Nat.one_mul]
    omega
  | .negOne :: cs, x :: xs => by
    simp only [applyTernaryRow, ternaryRowWeight, normInf]
    have htri : (-x + applyTernaryRow cs xs).natAbs ≤
        x.natAbs + (applyTernaryRow cs xs).natAbs := by
      have h := Int.natAbs_add_le (-x) (applyTernaryRow cs xs)
      simpa [Int.natAbs_neg] using h
    have ih := natAbs_applyTernaryRow_le cs xs
    have hx : x.natAbs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_left _ _
    have hxs : normInf xs ≤ Nat.max x.natAbs (normInf xs) := Nat.le_max_right _ _
    have hmul : ternaryRowWeight cs * normInf xs ≤
        ternaryRowWeight cs * Nat.max x.natAbs (normInf xs) :=
      Nat.mul_le_mul_left _ hxs
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **`PikkuFold` Ternary Norm Triangle Bound (`normInf_ternaryProj_le`)**:
    For every ternary projection `proj` whose rows have $\ell_1$ weight $\le k$, and every
    witness `w` satisfying `ShortNormBound β w`, the projected witness satisfies
    `ShortNormBound (k * β) (applyTernaryProj proj w)`. -/
theorem normInf_ternaryProj_le (proj : List (List TernaryCoeff)) (w : List Int)
    (k β : Nat)
    (hRows : ∀ row ∈ proj, ternaryRowWeight row ≤ k)
    (hShort : ShortNormBound β w) :
    ShortNormBound (k * β) (applyTernaryProj proj w) := by
  unfold ShortNormBound applyTernaryProj
  apply normInf_le_of_forall
  intro y hy
  obtain ⟨row, hRowMem, rfl⟩ := List.mem_map.1 hy
  have h1 := natAbs_applyTernaryRow_le row w
  have h2 : ternaryRowWeight row * normInf w ≤ k * β :=
    Nat.mul_le_mul (hRows row hRowMem) hShort
  exact Nat.le_trans h1 h2

/-! ## 3. Ajtai Module-SIS Commitment, Linear Homomorphism & SIS Kernel Reduction -/

/-- Public parameters for an Ajtai $\mathbb{Z}_q^{m \times n}$ lattice commitment. -/
structure AjtaiParams where
  modulus : Nat
  modulus_pos : 0 < modulus
  matrix : List (List Int)

/-- Integer inner product $\langle \mathbf{r}, \mathbf{w} \rangle$. -/
def dotInt : List Int → List Int → Int
  | r :: rs, w :: ws => r * w + dotInt rs ws
  | _, _ => 0

theorem dotInt_vecAdd :
    ∀ (row u v : List Int), u.length = v.length →
      dotInt row (vecAdd u v) = dotInt row u + dotInt row v
  | [], _, _, _ => by simp [dotInt]
  | _ :: _, [], [], _ => by simp [vecAdd, dotInt]
  | r :: rs, x :: xs, y :: ys, hlen => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [vecAdd, dotInt, dotInt_vecAdd rs xs ys hlen, Int.mul_add]
    omega

theorem dotInt_vecSub :
    ∀ (row u v : List Int), u.length = v.length →
      dotInt row (vecSub u v) = dotInt row u - dotInt row v
  | [], _, _, _ => by simp [dotInt]
  | _ :: _, [], [], _ => by simp [vecSub, dotInt]
  | r :: rs, x :: xs, y :: ys, hlen => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [vecSub, dotInt, dotInt_vecSub rs xs ys hlen, Int.mul_sub]
    omega

/-- Unreduced integer matrix-vector product $\mathbf{A} \cdot \mathbf{w} \in \mathbb{Z}^m$. -/
def ajtaiCommitRaw (matrix : List (List Int)) (w : List Int) : List Int :=
  matrix.map fun row => dotInt row w

/-- Modular Ajtai commitment $\mathbf{A} \cdot \mathbf{w} \bmod q \in \mathbb{Z}_q^m$. -/
def ajtaiCommit (pp : AjtaiParams) (w : List Int) : List Int :=
  (ajtaiCommitRaw pp.matrix w).map fun s => s % (pp.modulus : Int)

/-- Coordinate-wise modular vector addition $(\mathbf{u} + \mathbf{v}) \bmod q$. -/
def vecAddMod (q : Int) : List Int → List Int → List Int
  | x :: xs, y :: ys => ((x + y) % q) :: vecAddMod q xs ys
  | _, _ => []

/-- Unreduced Ajtai linear homomorphism: $\mathbf{A}(\mathbf{w}_1 + \mathbf{w}_2) = \mathbf{A}\mathbf{w}_1 + \mathbf{A}\mathbf{w}_2$. -/
theorem ajtaiCommitRaw_add (matrix : List (List Int)) {w₁ w₂ : List Int}
    (hlen : w₁.length = w₂.length) :
    ajtaiCommitRaw matrix (vecAdd w₁ w₂) =
      vecAdd (ajtaiCommitRaw matrix w₁) (ajtaiCommitRaw matrix w₂) := by
  unfold ajtaiCommitRaw
  induction matrix with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, vecAdd, dotInt_vecAdd row w₁ w₂ hlen, ih]

/-- **Modular Ajtai Linear Homomorphism (`ajtaiCommit_add`)**:
    $\text{ajtaiCommit}(\mathbf{w}_1 + \mathbf{w}_2) = (\text{ajtaiCommit}(\mathbf{w}_1) + \text{ajtaiCommit}(\mathbf{w}_2)) \bmod q$. -/
theorem ajtaiCommit_add (pp : AjtaiParams) {w₁ w₂ : List Int}
    (hlen : w₁.length = w₂.length) :
    ajtaiCommit pp (vecAdd w₁ w₂) =
      vecAddMod (pp.modulus : Int) (ajtaiCommit pp w₁) (ajtaiCommit pp w₂) := by
  unfold ajtaiCommit ajtaiCommitRaw
  induction pp.matrix with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, vecAddMod, dotInt_vecAdd row w₁ w₂ hlen]
    rw [← Int.add_emod]
    exact congrArg _ ih

theorem ajtaiCommitMatrix_vecSub_eq_zeros (q : Int) :
    ∀ (matrix : List (List Int)) {w₁ w₂ : List Int},
      w₁.length = w₂.length →
      (matrix.map fun row => (dotInt row w₁) % q) = (matrix.map fun row => (dotInt row w₂) % q) →
      (matrix.map fun row => (dotInt row (vecSub w₁ w₂)) % q) = List.replicate matrix.length 0
  | [], _, _, _, _ => rfl
  | row :: rows, w₁, w₂, hlen, heq => by
    simp only [List.map_cons, List.cons.injEq] at heq
    simp only [List.map_cons, List.length_cons, List.replicate_succ, dotInt_vecSub row w₁ w₂ hlen]
    rw [Int.sub_emod, heq.1, Int.sub_self, Int.zero_emod]
    exact congrArg (0 :: ·) (ajtaiCommitMatrix_vecSub_eq_zeros q rows hlen heq.2)

theorem ajtaiCommit_vecSub_eq_zeros (pp : AjtaiParams) {w₁ w₂ : List Int}
    (hlen : w₁.length = w₂.length)
    (heq : ajtaiCommit pp w₁ = ajtaiCommit pp w₂) :
    ajtaiCommit pp (vecSub w₁ w₂) = List.replicate pp.matrix.length 0 := by
  unfold ajtaiCommit ajtaiCommitRaw at heq ⊢
  rw [List.map_map, List.map_map] at heq
  rw [List.map_map]
  exact ajtaiCommitMatrix_vecSub_eq_zeros (pp.modulus : Int) pp.matrix hlen heq

/-- A concrete non-zero short-integer kernel vector $\boldsymbol{\delta}$ solving
    $\mathbf{A} \cdot \boldsymbol{\delta} \equiv \mathbf{0} \pmod q$ with $\|\boldsymbol{\delta}\|_\infty \le B$. -/
structure SISKernelSolution (pp : AjtaiParams) (B : Nat) where
  delta : List Int
  nonzero : ∃ z ∈ delta, z ≠ 0
  short : ShortNormBound B delta
  inKernel : ajtaiCommit pp delta = List.replicate pp.matrix.length 0

/-- **Module-SIS Hardness Predicate (`ModuleSISHard pp B`)**:
    No non-zero integer vector of $\ell_\infty$ norm $\le B$ lies in $\ker(\mathbf{A} \bmod q)$. -/
def ModuleSISHard (pp : AjtaiParams) (B : Nat) : Prop :=
  ¬ Nonempty (SISKernelSolution pp B)

/-! ## 4. Base-$2^{16}$ Gadget-Decomposed `ajtaiLatticePCS` & `Akita` `SparseOneHotCommit` -/

/-- Decompose a canonical 64-bit `Goldilocks` element into four short 16-bit integer limbs
    in $[0, 65535]$. -/
def gadgetDecomposeGoldilocks (x : Goldilocks) : List Int :=
  let n := x.val
  [(((n % 65536) : Nat) : Int),
   ((((n / 65536) % 65536) : Nat) : Int),
   ((((n / 4294967296) % 65536) : Nat) : Int),
   (((n / 281474976710656) : Nat) : Int)]

/-- Flatten a `Goldilocks` table into its $4 \cdot |\text{tbl}|$ short base-$2^{16}$ limbs. -/
def gadgetDecomposeTable (tbl : List Goldilocks) : List Int :=
  tbl.flatMap gadgetDecomposeGoldilocks

theorem gadgetDecomposeTable_length (tbl : List Goldilocks) :
    (gadgetDecomposeTable tbl).length = 4 * tbl.length := by
  unfold gadgetDecomposeTable
  induction tbl with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, gadgetDecomposeGoldilocks,
      List.cons_append, List.nil_append, List.length_cons, ih]
    omega

theorem gadgetDecomposeGoldilocks_short (x : Goldilocks) :
    ∀ z ∈ gadgetDecomposeGoldilocks x, z.natAbs ≤ 65535 := by
  intro z hz
  have h64 : x.val < 2 ^ 64 := Goldilocks.val_lt_two_pow_64 x
  simp only [gadgetDecomposeGoldilocks, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> omega

theorem gadgetDecomposeTable_short (tbl : List Goldilocks) :
    ShortNormBound 65535 (gadgetDecomposeTable tbl) := by
  apply normInf_le_of_forall
  intro z hz
  unfold gadgetDecomposeTable at hz
  obtain ⟨x, _, hzx⟩ := List.mem_flatMap.1 hz
  exact gadgetDecomposeGoldilocks_short x z hzx

/-- Recompose four checked 16-bit limbs $[l_0, l_1, l_2, l_3] \in [0, 65535]^4$ back into a
    canonical `Goldilocks` field element. -/
def gadgetRecomposeOne (l₀ l₁ l₂ l₃ : Int) : Option Goldilocks :=
  if 0 ≤ l₀ && l₀ < 65536 && 0 ≤ l₁ && l₁ < 65536 &&
     0 ≤ l₂ && l₂ < 65536 && 0 ≤ l₃ && l₃ < 65536 then
    let v : Nat := l₀.toNat + 65536 * l₁.toNat +
                   4294967296 * l₂.toNat + 281474976710656 * l₃.toNat
    if hv : v < goldilocksPrime then
      some ⟨v, hv⟩
    else
      none
  else
    none

theorem gadgetRecomposeOne_decompose (x : Goldilocks) :
    gadgetRecomposeOne
      (((x.val % 65536 : Nat) : Int))
      ((((x.val / 65536) % 65536 : Nat) : Int))
      ((((x.val / 4294967296) % 65536 : Nat) : Int))
      (((x.val / 281474976710656 : Nat) : Int)) = some x := by
  unfold gadgetRecomposeOne
  have h64 : x.val < 2 ^ 64 := Goldilocks.val_lt_two_pow_64 x
  have hCond : (decide (0 ≤ (((x.val % 65536 : Nat) : Int))) &&
      decide ((((x.val % 65536 : Nat) : Int)) < 65536) &&
      decide (0 ≤ ((((x.val / 65536) % 65536 : Nat) : Int))) &&
      decide (((((x.val / 65536) % 65536 : Nat) : Int)) < 65536) &&
      decide (0 ≤ ((((x.val / 4294967296) % 65536 : Nat) : Int))) &&
      decide (((((x.val / 4294967296) % 65536 : Nat) : Int)) < 65536) &&
      decide (0 ≤ (((x.val / 281474976710656 : Nat) : Int))) &&
      decide ((((x.val / 281474976710656 : Nat) : Int)) < 65536)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [hCond]
  simp only [↓reduceIte]
  have hVal : (((x.val % 65536 : Nat) : Int)).toNat +
      65536 * ((((x.val / 65536) % 65536 : Nat) : Int)).toNat +
      4294967296 * ((((x.val / 4294967296) % 65536 : Nat) : Int)).toNat +
      281474976710656 * (((x.val / 281474976710656 : Nat) : Int)).toNat = x.val := by
    omega
  simp only [hVal, x.isLt, ↓reduceDIte]

/-- Recompose a $4 N$-limb short integer vector into `Option (List Goldilocks)`. -/
def gadgetRecomposeTable : List Int → Option (List Goldilocks)
  | [] => some []
  | l₀ :: l₁ :: l₂ :: l₃ :: rest =>
    match gadgetRecomposeOne l₀ l₁ l₂ l₃, gadgetRecomposeTable rest with
    | some x, some xs => some (x :: xs)
    | _, _ => none
  | _ => none

theorem gadgetRecomposeTable_decompose :
    ∀ (tbl : List Goldilocks), gadgetRecomposeTable (gadgetDecomposeTable tbl) = some tbl
  | [] => rfl
  | x :: xs => by
    have ih := gadgetRecomposeTable_decompose xs
    unfold gadgetDecomposeTable at ih ⊢
    simp only [List.flatMap_cons, gadgetDecomposeGoldilocks,
      List.cons_append, List.nil_append, gadgetRecomposeTable,
      gadgetRecomposeOne_decompose x, ih]

/-- Ajtai lattice commitment carrying arity and modular $\mathbb{Z}_q^m$ syndrome. -/
structure AjtaiCommitment where
  numVars : Nat
  syndrome : List Int
  deriving DecidableEq, Repr

/-- Ajtai lattice opening proof: short base-$2^{16}$ integer witness limbs. -/
structure AjtaiOpeningProof where
  shortLimbs : List Int
  deriving DecidableEq, Repr

/-- `"AJTAI.PCS.OPEN"` transcript label. -/
def ajtaiOpenLabel : ByteArray :=
  Native.bytesOfList [0x41, 0x4a, 0x54, 0x41, 0x49, 0x2e,
                      0x50, 0x43, 0x53, 0x2e, 0x4f, 0x50, 0x45, 0x4e]

def encodeSyndromeBytes (syn : List Int) : ByteArray :=
  Native.bytesOfList (syn.flatMap fun s => leb128 s.natAbs)

def ajtaiLatticeCommit (pp : AjtaiParams) (numVars : Nat) (tbl : List Goldilocks) :
    AjtaiCommitment :=
  { numVars := numVars
    syndrome := ajtaiCommit pp (gadgetDecomposeTable tbl) }

def ajtaiLatticeOpenEval (pp : AjtaiParams) (numVars : Nat) (tbl : List Goldilocks)
    (claim : EvalClaim Goldilocks numVars) (tr : Transcript .relationBound) :
    AjtaiOpeningProof × Transcript .relationBound :=
  let limbs := gadgetDecomposeTable tbl
  let syn := ajtaiCommit pp limbs
  let tr' := absorbMsg ajtaiOpenLabel
    (encodeFrame (encodeSyndromeBytes syn) (encodeGoldilocksBytes claim.expectedVal) ByteArray.empty) tr
  (⟨limbs⟩, tr')

def ajtaiLatticeVerifyEval (pp : AjtaiParams) (numVars : Nat) (comm : AjtaiCommitment)
    (claim : EvalClaim Goldilocks numVars) (prf : AjtaiOpeningProof)
    (tr : Transcript .relationBound) : Bool × Transcript .relationBound :=
  let tr' := absorbMsg ajtaiOpenLabel
    (encodeFrame (encodeSyndromeBytes comm.syndrome) (encodeGoldilocksBytes claim.expectedVal) ByteArray.empty) tr
  let ok :=
    (comm.numVars == numVars) &&
    (prf.shortLimbs.length == 4 * (2 ^ numVars)) &&
    checkShortNorm 65535 prf.shortLimbs &&
    (ajtaiCommit pp prf.shortLimbs == comm.syndrome) &&
    match gadgetRecomposeTable prf.shortLimbs with
    | some tbl => mleEval tbl claim.point == claim.expectedVal
    | none => false
  (ok, tr')

/-- **Ajtai Double-Opening to Module-SIS Kernel Reduction (`ajtai_double_open_yields_sis_kernel`)**:
    Two accepted openings of the same `AjtaiCommitment` at the same evaluation point claiming
    distinct values explicitly yield a non-zero short vector in $\ker(\mathbf{A} \bmod q)$
    with $\|\boldsymbol{\delta}\|_\infty \le 2 \cdot 65535 = 131070$. -/
theorem ajtai_double_open_yields_sis_kernel (pp : AjtaiParams)
    {v : Nat} {comm : AjtaiCommitment}
    {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : AjtaiOpeningProof}
    {tr₁ tr₂ : Transcript .relationBound}
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : (ajtaiLatticeVerifyEval pp v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (ajtaiLatticeVerifyEval pp v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    Nonempty (SISKernelSolution pp 131070) := by
  simp only [ajtaiLatticeVerifyEval, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hAcc₁ hAcc₂
  rcases hAcc₁ with ⟨⟨⟨⟨_, hLen₁⟩, hShort₁⟩, hSyn₁⟩, hRec₁⟩
  rcases hAcc₂ with ⟨⟨⟨⟨_, hLen₂⟩, hShort₂⟩, hSyn₂⟩, hRec₂⟩
  have hSameLen : π₁.shortLimbs.length = π₂.shortLimbs.length := by rw [hLen₁, hLen₂]
  have hLimbsNe : π₁.shortLimbs ≠ π₂.shortLimbs := by
    intro hEq
    rw [hEq] at hRec₁
    cases hRec : gadgetRecomposeTable π₂.shortLimbs with
    | none => rw [hRec] at hRec₁; cases hRec₁
    | some tbl =>
      rw [hRec, beq_iff_eq] at hRec₁ hRec₂
      apply hDisagree
      rw [← hRec₁, ← hRec₂, hPt]
  refine ⟨
    { delta := vecSub π₁.shortLimbs π₂.shortLimbs
      nonzero := vecSub_nonzero_of_ne hSameLen hLimbsNe
      short := ?_
      inKernel := ajtaiCommit_vecSub_eq_zeros pp hSameLen (hSyn₁.trans hSyn₂.symm) }⟩
  unfold ShortNormBound at hShort₁ hShort₂ ⊢
  have hSub := normInf_vecSub_le π₁.shortLimbs π₂.shortLimbs
  omega

/-- Executable `ajtaiLatticePCS` over `Goldilocks` parameterized by `pp : AjtaiParams`. -/
def ajtaiLatticePCS (pp : AjtaiParams) : MultilinearPCS Goldilocks where
  domainKind := .primeField
  regime := .uniqueDecodingRadius
  validRegime := .primeUDR
  Params := Unit
  Commitment := AjtaiCommitment
  OpeningProof := AjtaiOpeningProof
  commit _ v tbl := ajtaiLatticeCommit pp v tbl
  openEval _ v tbl claim tr := ajtaiLatticeOpenEval pp v tbl claim tr
  verifyEval _ v comm claim prf tr := ajtaiLatticeVerifyEval pp v comm claim prf tr
  completeness := by
    intro _ v tbl _ _ _ hTblLen
    dsimp only [ajtaiLatticeCommit, ajtaiLatticeOpenEval, ajtaiLatticeVerifyEval]
    simp only [Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff]
    refine ⟨⟨⟨⟨trivial, ?_⟩, gadgetDecomposeTable_short tbl⟩, trivial⟩, ?_⟩
    · rw [gadgetDecomposeTable_length, hTblLen]
    · rw [gadgetRecomposeTable_decompose tbl, beq_iff_eq]

/-- **Module-SIS Hardness Implies `BindingSound` (`ajtaiLatticePCS_bindingSound_of_sisHard`)**:
    Under `ModuleSISHard pp 131070`, `ajtaiLatticePCS pp` is unconditionally evaluation-binding. -/
theorem ajtaiLatticePCS_bindingSound_of_sisHard (pp : AjtaiParams)
    (hSIS : ModuleSISHard pp 131070) :
    BindingSound (ajtaiLatticePCS pp) := by
  intro _ v comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  exact Classical.byContradiction fun hNe =>
    hSIS (ajtai_double_open_yields_sis_kernel pp hPt hAcc₁ hAcc₂ hNe)

/-! ### `Akita` (`2026/1983`) / `Twist & Shout` $O(\text{rows})$ Sparse One-Hot Ajtai Specialization -/

/-- Standard basis integer vector of length `len` with `1` at `col` and `0` elsewhere. -/
def unitVecInt : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, 0 => 1 :: List.replicate n 0
  | n + 1, k + 1 => 0 :: unitVecInt n k

theorem dotInt_replicate_zero : ∀ (row : List Int) (n : Nat), dotInt row (List.replicate n 0) = 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | r :: rs, n + 1 => by
    simp [List.replicate_succ, dotInt, dotInt_replicate_zero rs n]

theorem dotInt_unitVecInt :
    ∀ (len col : Nat) (row : List Int), col < len →
      dotInt row (unitVecInt len col) = row.getD col 0
  | 0, _, _, hlt => by omega
  | n + 1, 0, [], _ => rfl
  | n + 1, 0, r :: rs, _ => by
    simp [unitVecInt, dotInt, dotInt_replicate_zero]
  | n + 1, k + 1, [], _ => rfl
  | n + 1, k + 1, r :: rs, hlt => by
    have hk : k < n := by omega
    simp [unitVecInt, dotInt, dotInt_unitVecInt n k rs hk]

example : gadgetDecomposeGoldilocks Goldilocks.zero = [0, 0, 0, 0] := rfl

example : gadgetDecomposeGoldilocks Goldilocks.one = [1, 0, 0, 0] := rfl

theorem replicate_append_zero :
    ∀ (a b : Nat), List.replicate a (0 : Int) ++ List.replicate b 0 = List.replicate (a + b) 0
  | 0, b => by simp
  | a + 1, b => by
    rw [Nat.succ_add]
    simp [List.replicate_succ, replicate_append_zero a b]

theorem unitVecInt_prepend_four_zeros (len k : Nat) :
    ([0, 0, 0, 0] : List Int) ++ unitVecInt len k = unitVecInt (len + 4) (k + 4) := by
  rfl

theorem gadgetDecompose_oneHot_aux :
    ∀ (m start idx : Nat),
      ((List.range m).map (fun j =>
        if start + j = idx then Goldilocks.one else Goldilocks.zero)).flatMap gadgetDecomposeGoldilocks =
      if idx < start then
        List.replicate (4 * m) 0
      else if idx < start + m then
        unitVecInt (4 * m) (4 * (idx - start))
      else
        List.replicate (4 * m) 0
  | 0, _, _ => by simp [unitVecInt]
  | m + 1, start, idx => by
    have hRange : List.range (m + 1) = 0 :: (List.range m).map (· + 1) := @List.range_succ_eq_map m
    rw [hRange, List.map_cons, List.map_map, List.flatMap_cons]
    have hShift :
        ((List.range m).map ((fun j => if start + j = idx then Goldilocks.one else Goldilocks.zero) ∘ (· + 1))) =
        ((List.range m).map (fun j => if (start + 1) + j = idx then Goldilocks.one else Goldilocks.zero)) := by
      apply List.map_congr_left
      intro j _
      dsimp only [Function.comp]
      have hAdd : start + (j + 1) = (start + 1) + j := by omega
      rw [hAdd]
    rw [hShift, gadgetDecompose_oneHot_aux m (start + 1) idx]
    by_cases hEq : start = idx
    · subst hEq
      have hPos : start < start + (m + 1) := by omega
      have hOne : gadgetDecomposeGoldilocks Goldilocks.one = [1, 0, 0, 0] := rfl
      simp only [Nat.add_zero, ↓reduceIte, hOne,
        show start < start + 1 by omega, show ¬ start < start by omega, hPos]
      have hMul : 4 * (m + 1) = 4 * m + 4 := by omega
      rw [Nat.sub_self, Nat.mul_zero, hMul]
      simp [unitVecInt, List.replicate_succ]
    · have hHead : (if start + 0 = idx then Goldilocks.one else Goldilocks.zero) = Goldilocks.zero := by
        rw [Nat.add_zero]; simp [hEq]
      have hZero : gadgetDecomposeGoldilocks Goldilocks.zero = [0, 0, 0, 0] := rfl
      rw [hHead, hZero]
      by_cases hLt : idx < start
      · have hLt1 : idx < start + 1 := by omega
        simp only [hLt, hLt1, ↓reduceIte]
        have h4 : ([0, 0, 0, 0] : List Int) = List.replicate 4 0 := rfl
        rw [h4, replicate_append_zero]
        congr 1; omega
      · have hNotLt1 : ¬ idx < start + 1 := by omega
        simp only [hLt, hNotLt1, ↓reduceIte]
        by_cases hIn : idx < start + (m + 1)
        · have hIn' : idx < start + 1 + m := by omega
          simp only [hIn, hIn', ↓reduceIte]
          rw [unitVecInt_prepend_four_zeros]
          have hL : 4 * m + 4 = 4 * (m + 1) := by omega
          have hC : 4 * (idx - (start + 1)) + 4 = 4 * (idx - start) := by omega
          rw [hL, hC]
        · have hIn' : ¬ idx < start + 1 + m := by omega
          simp only [hIn, hIn', ↓reduceIte]
          have h4 : ([0, 0, 0, 0] : List Int) = List.replicate 4 0 := rfl
          rw [h4, replicate_append_zero]
          congr 1; omega

theorem gadgetDecomposeTable_oneHot (v idx : Nat) (hIdx : idx < 2 ^ v) :
    gadgetDecomposeTable (oneHotTable Goldilocks v idx) =
      unitVecInt (4 * 2 ^ v) (4 * idx) := by
  unfold gadgetDecomposeTable oneHotTable
  have h := gadgetDecompose_oneHot_aux (2 ^ v) 0 idx
  simp only [Nat.zero_add, show ¬ idx < 0 by omega, hIdx, ↓reduceIte, Nat.sub_zero] at h
  exact h

/-- Commit to a 1-hot lookup table in $O(\text{rows})$ operations by reading column `4 * idx`
    directly out of `pp.matrix`. -/
def ajtaiCommitOneHotColumn (pp : AjtaiParams) (numVars idx : Nat) : AjtaiCommitment :=
  { numVars := numVars
    syndrome := pp.matrix.map fun row => (row.getD (4 * idx) 0) % (pp.modulus : Int) }

/-- **`Akita` / `Twist & Shout` Sparse One-Hot Commitment Instance (`ajtaiSparseOneHot`)**:
    Proves that $O(\text{rows})$ single-column lookup agrees identically with dense
    $O(2^v)$ `ajtaiLatticePCS` commitment on `oneHotTable Goldilocks v idx`. -/
instance ajtaiSparseOneHot (pp : AjtaiParams) :
    SparseOneHotCommit Goldilocks (ajtaiLatticePCS pp) where
  commitOneHot _ v idx := ajtaiCommitOneHotColumn pp v idx
  commitOneHot_eq_commit := by
    intro _ v idx hIdx
    dsimp only [ajtaiLatticePCS, ajtaiLatticeCommit, ajtaiCommitOneHotColumn]
    congr 1
    rw [gadgetDecomposeTable_oneHot v idx hIdx]
    unfold ajtaiCommit ajtaiCommitRaw
    rw [List.map_map]
    apply List.map_congr_left
    intro row _
    dsimp only [Function.comp]
    have hCol : 4 * idx < 4 * 2 ^ v := by omega
    rw [dotInt_unitVecInt (4 * 2 ^ v) (4 * idx) row hCol]

/-! ## 5. Cross-Assumption `DualPCS P₁ P₂` Product Combinator & `dualPCS_sound_of_either` -/

/-- Conservative domain kind of a dual-track PCS pair: `.primeField` iff both tracks are
    `.primeField`, otherwise `.binaryAdditive` (enforcing `2026/2424` UDR!). -/
def dualDomainKind : DomainKind → DomainKind → DomainKind
  | .primeField, .primeField => .primeField
  | _, _ => .binaryAdditive

/-- Conservative proximity regime of a dual-track PCS pair. -/
def dualProximityRegime (d₁ d₂ : DomainKind) (r₁ r₂ : ProximityRegime) : ProximityRegime :=
  match dualDomainKind d₁ d₂ with
  | .binaryAdditive => .uniqueDecodingRadius
  | .primeField =>
    match r₁, r₂ with
    | .uniqueDecodingRadius, _ => .uniqueDecodingRadius
    | _, .uniqueDecodingRadius => .uniqueDecodingRadius
    | .johnsonBound, _ => .johnsonBound
    | _, .johnsonBound => .johnsonBound
    | .capacityBound, .capacityBound => .capacityBound

theorem dualValidProximityConfig (d₁ d₂ : DomainKind) (r₁ r₂ : ProximityRegime) :
    ValidProximityConfig (dualDomainKind d₁ d₂) (dualProximityRegime d₁ d₂ r₁ r₂) := by
  cases d₁ <;> cases d₂ <;> simp only [dualDomainKind, dualProximityRegime]
  · cases r₁ <;> cases r₂ <;> simp only
    all_goals first | exact .primeUDR | exact .primeJohnson | exact .primeCapacity
  · exact .binaryUDR
  · exact .binaryUDR
  · exact .binaryUDR

/-- Domain-separated Fiat–Shamir fork labels for `DualPCS` track 1, track 2, and join. -/
def dualTrack1Label : ByteArray :=
  Native.bytesOfList [0x44, 0x55, 0x41, 0x4c, 0x2e, 0x54, 0x52, 0x41, 0x43, 0x4b, 0x31]

def dualTrack2Label : ByteArray :=
  Native.bytesOfList [0x44, 0x55, 0x41, 0x4c, 0x2e, 0x54, 0x52, 0x41, 0x43, 0x4b, 0x32]

def dualJoinLabel : ByteArray :=
  Native.bytesOfList [0x44, 0x55, 0x41, 0x4c, 0x2e, 0x4a, 0x4f, 0x49, 0x4e]

/-- Conjunction gate joining the two independent PCS verification verdicts in `DualPCS`. -/
def dualVerdictJoin (ok₁ ok₂ : Bool) : Bool :=
  ok₁ && ok₂

/-- **Cross-Assumption `DualPCS P₁ P₂` Product Combinator**:
    Pairs any two `MultilinearPCS R` backends (e.g. Hash-UDR `canopyMerklePCS` and Lattice-SIS
    `ajtaiLatticePCS`) under one shared `EvalClaim R v` and Fenzi-bound `Transcript .relationBound`. -/
def DualPCS {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R) : MultilinearPCS R where
  domainKind := dualDomainKind P₁.domainKind P₂.domainKind
  regime := dualProximityRegime P₁.domainKind P₂.domainKind P₁.regime P₂.regime
  validRegime := dualValidProximityConfig P₁.domainKind P₂.domainKind P₁.regime P₂.regime
  Params := P₁.Params × P₂.Params
  Commitment := P₁.Commitment × P₂.Commitment
  OpeningProof := P₁.OpeningProof × P₂.OpeningProof
  commit pp v tbl := (P₁.commit pp.1 v tbl, P₂.commit pp.2 v tbl)
  openEval pp v tbl claim tr :=
    let tr₁ := absorbMsg dualTrack1Label ByteArray.empty tr
    let tr₂ := absorbMsg dualTrack2Label ByteArray.empty tr
    let (π₁, tr₁') := P₁.openEval pp.1 v tbl claim tr₁
    let (π₂, tr₂') := P₂.openEval pp.2 v tbl claim tr₂
    let trJoin := absorbMsg dualJoinLabel (encodeFrame tr₁'.state tr₂'.state ByteArray.empty) tr
    ((π₁, π₂), trJoin)
  verifyEval pp v comm claim prf tr :=
    let tr₁ := absorbMsg dualTrack1Label ByteArray.empty tr
    let tr₂ := absorbMsg dualTrack2Label ByteArray.empty tr
    let (ok₁, tr₁') := P₁.verifyEval pp.1 v comm.1 claim prf.1 tr₁
    let (ok₂, tr₂') := P₂.verifyEval pp.2 v comm.2 claim prf.2 tr₂
    let trJoin := absorbMsg dualJoinLabel (encodeFrame tr₁'.state tr₂'.state ByteArray.empty) tr
    (dualVerdictJoin ok₁ ok₂, trJoin)
  completeness := by
    intro pp v tbl pt hPt tr hTblLen
    dsimp only [dualVerdictJoin]
    rw [Bool.and_eq_true]
    exact ⟨P₁.completeness pp.1 v tbl pt hPt (absorbMsg dualTrack1Label ByteArray.empty tr) hTblLen,
           P₂.completeness pp.2 v tbl pt hPt (absorbMsg dualTrack2Label ByteArray.empty tr) hTblLen⟩

/-- Explicit standalone completeness theorem for `DualPCS P₁ P₂`. -/
theorem dualPCS_completeness {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R)
    (pp : P₁.Params × P₂.Params) (v : Nat) (tbl : List R)
    (pt : List R) (hPt : pt.length = v) (tr : Transcript .relationBound)
    (hTblLen : tbl.length = 2 ^ v) :
    let claim : EvalClaim R v := ⟨pt, hPt, mleEval tbl pt⟩
    let (prf, _) := (DualPCS P₁ P₂).openEval pp v tbl claim tr
    ((DualPCS P₁ P₂).verifyEval pp v ((DualPCS P₁ P₂).commit pp v tbl) claim prf tr).1 = true :=
  (DualPCS P₁ P₂).completeness pp v tbl pt hPt tr hTblLen

/-- **Cryptographic Redundancy Theorem (`dualPCS_sound_of_either`)**:
    If *either* `P₁` is evaluation-binding *or* `P₂` is evaluation-binding, then their
    cross-assumption product `DualPCS P₁ P₂` is evaluation-binding. An attacker must break
    *both* underlying hardness assumptions simultaneously to forge an opening. -/
theorem dualPCS_sound_of_either {R : Type} [CommRingOps R]
    (P₁ P₂ : MultilinearPCS R)
    (hEither : BindingSound P₁ ∨ BindingSound P₂) :
    BindingSound (DualPCS P₁ P₂) := by
  intro pp v comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  simp only [DualPCS, dualVerdictJoin, Bool.and_eq_true] at hAcc₁ hAcc₂
  rcases hEither with hSound₁ | hSound₂
  · exact hSound₁ pp.1 v comm.1 c₁ c₂ π₁.1 π₂.1
      (absorbMsg dualTrack1Label ByteArray.empty tr₁)
      (absorbMsg dualTrack1Label ByteArray.empty tr₂)
      hPt hAcc₁.1 hAcc₂.1
  · exact hSound₂ pp.2 v comm.2 c₁ c₂ π₁.2 π₂.2
      (absorbMsg dualTrack2Label ByteArray.empty tr₁)
      (absorbMsg dualTrack2Label ByteArray.empty tr₂)
      hPt hAcc₁.2 hAcc₂.2

/-- Concrete deployed dual-track PCS over `Goldilocks`: pairs 256-bit cSHAKE256 `canopyMerklePCS`
    (`HashUDR`) with base-$2^{16}$ `ajtaiLatticePCS` (`ModuleSIS`). -/
def canopyAjtaiDualPCS (H : Hash32) (pp : AjtaiParams) : MultilinearPCS Goldilocks :=
  DualPCS (canopyMerklePCS H) (ajtaiLatticePCS pp)

/-- **Concrete Hash-or-Lattice Survival Theorem (`canopyAjtaiDualPCS_sound_of_hash_or_sis`)**:
    If *either* `H.eval` has no 256-bit hash collision *or* `ModuleSISHard pp 131070` holds,
    `canopyAjtaiDualPCS H pp` is unconditionally evaluation-binding. -/
theorem canopyAjtaiDualPCS_sound_of_hash_or_sis (H : Hash32) (pp : AjtaiParams)
    (hOr : ¬ Collision H.eval ∨ ModuleSISHard pp 131070) :
    BindingSound (canopyAjtaiDualPCS H pp) := by
  apply dualPCS_sound_of_either
  rcases hOr with hNoCol | hSIS
  · exact .inl (canopyMerklePCS_bindingSound_of_collisionFree H hNoCol)
  · exact .inr (ajtaiLatticePCS_bindingSound_of_sisHard pp hSIS)

/-- End-to-end Dual-Spine Sumcheck + PCS Verifier over a Fenzi-bound transcript:
    reduces $\sum_{\mathbf{x} \in \{0,1\}^v} \tilde{f}(\mathbf{x}) = S$ via `verifySumcheck`
    and checks the resulting `EvalClaim` against `DualPCS P₁ P₂`. -/
def verifyDualSumcheckPIOP {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R]
    (P₁ P₂ : MultilinearPCS R) (pp : P₁.Params × P₂.Params)
    (maxDeg numVars : Nat) (comm : P₁.Commitment × P₂.Commitment)
    (claimedSum : R) (rounds : List (RoundPoly R))
    (openingPrf : P₁.OpeningProof × P₂.OpeningProof)
    (tr : Transcript .relationBound) : Bool :=
  match verifySumcheck (R := R) maxDeg numVars claimedSum rounds tr with
  | none => false
  | some (claim, trAfterSumcheck) =>
    ((DualPCS (R := R) P₁ P₂).verifyEval pp numVars comm claim openingPrf trAfterSumcheck).1

theorem verifyDualSumcheckPIOP_completeness
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    (P₁ P₂ : MultilinearPCS R) (pp : P₁.Params × P₂.Params)
    {maxDeg : Nat} (hDeg : 1 ≤ maxDeg) (v : Nat) (tbl : List R)
    (tr : Transcript .relationBound) (hTblLen : tbl.length = 2 ^ v) :
    let (rounds, claim, trAfter) := honestSumcheckProver (R := R) v tbl tr
    let (prf, _) := (DualPCS (R := R) P₁ P₂).openEval pp v tbl claim trAfter
    verifyDualSumcheckPIOP (R := R) P₁ P₂ pp maxDeg v
      ((DualPCS (R := R) P₁ P₂).commit pp v tbl) (hypercubeSum v tbl) rounds prf tr = true := by
  dsimp only [verifyDualSumcheckPIOP]
  obtain ⟨hVer, hVal⟩ := honestSumcheckProver_completeness hDeg v tbl tr
  rw [hVer]
  dsimp only
  let sc := honestSumcheckProver v tbl tr
  have hClaimEq : sc.2.1 = ⟨sc.2.1.point, sc.2.1.point_len, mleEval tbl sc.2.1.point⟩ := by
    cases hCl : sc.2.1 with
    | mk pt hPt expVal =>
      have hVal' : expVal = mleEval tbl pt := by simpa [sc, hCl] using hVal
      subst hVal'
      rfl
  change ((DualPCS P₁ P₂).verifyEval pp v ((DualPCS P₁ P₂).commit pp v tbl)
    sc.2.1 ((DualPCS P₁ P₂).openEval pp v tbl sc.2.1 sc.2.2).1 sc.2.2).1 = true
  rw [hClaimEq]
  exact (DualPCS P₁ P₂).completeness pp v tbl sc.2.1.point sc.2.1.point_len sc.2.2 hTblLen

end Obend.Crypto
end
