module
/-
# Obend.Crypto.DualSpine — Exact-Dimension Ajtai SIS, Non-Vacuity Witness, `dualExtract` & Instance-Bound `DualPCS`
Unifies the **Lattice Module-SIS spine** (`PikkuFold 2026/1809`, `Akita 2026/1983`) with the
**Hash-UDR spine** (`Canopy`) under one instance-bound `Sumcheck` PIOP (`BoundTranscript`),
exact-dimension `dotInt` (`NonPigeonholeSISParams`, `inhabitedAjtaiParams_sisHard`), and
constructive `0 Classical` `Type`-valued witness extraction (`dualExtract`).
-/
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Crypto.PCS
public import Obend.Judge.Computational
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.PCS
import all Obend.Judge.Computational

public section
namespace Obend.Crypto

open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Apps.ZkNtt
open Obend.Judge.Computational (HashCollisionWitness SISShortVecWitness Unbroken)

set_option autoImplicit false

/-! ## 1. Integer Lattice Vectors, $\ell_\infty$ Norm & Graded `Short cols β` -/

/-- $\ell_\infty$ norm $\max_i |w_i|$ of an integer lattice vector. -/
def normInf : List Int → Nat
  | [] => 0
  | x :: xs => max x.natAbs (normInf xs)

theorem normInf_eq_vecInfNorm : ∀ (w : List Int), normInf w = Obend.Judge.Computational.vecInfNorm w
  | [] => by unfold normInf Obend.Judge.Computational.vecInfNorm; rfl
  | x :: xs => by
    simp only [normInf, Obend.Judge.Computational.vecInfNorm, normInf_eq_vecInfNorm xs]

/-- Short $\ell_\infty$ witness norm guard $\|\mathbf{w}\|_\infty \le \beta$. -/
@[expose] def ShortNormBound (β : Nat) (w : List Int) : Prop :=
  normInf w ≤ β

/-- Graded short witness predicate enforcing both exact column width `w.length = cols` and `‖w‖_∞ ≤ β`. -/
@[expose] def Short (cols β : Nat) (w : List Int) : Prop :=
  w.length = cols ∧ normInf w ≤ β

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

theorem vecSub_eq_compVecSub : ∀ (u v : List Int), vecSub u v = Obend.Judge.Computational.vecSub u v
  | [], [] => by unfold vecSub Obend.Judge.Computational.vecSub; rfl
  | [], _ :: _ => by unfold vecSub Obend.Judge.Computational.vecSub; rfl
  | _ :: _, [] => by unfold vecSub Obend.Judge.Computational.vecSub; rfl
  | x :: xs, y :: ys => by
    simp only [vecSub, Obend.Judge.Computational.vecSub, vecSub_eq_compVecSub xs ys]

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
    simp only [vecAdd, normInf]; rw [Nat.max_le]
    have htri := Int.natAbs_add_le x y
    have ih := normInf_vecAdd_le xs ys
    have hx1 := Nat.le_max_left x.natAbs (normInf xs)
    have hy1 := Nat.le_max_left y.natAbs (normInf ys)
    have hx2 := Nat.le_max_right x.natAbs (normInf xs)
    have hy2 := Nat.le_max_right y.natAbs (normInf ys)
    exact ⟨by omega, by omega⟩

theorem normInf_vecSub_le : ∀ (u v : List Int), normInf (vecSub u v) ≤ normInf u + normInf v
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | x :: xs, y :: ys => by
    simp only [vecSub, normInf]; rw [Nat.max_le]
    have htri : (x - y).natAbs ≤ x.natAbs + y.natAbs := by
      simpa [Int.sub_eq_add_neg, Int.natAbs_neg] using Int.natAbs_add_le x (-y)
    have ih := normInf_vecSub_le xs ys
    have hx1 := Nat.le_max_left x.natAbs (normInf xs)
    have hy1 := Nat.le_max_left y.natAbs (normInf ys)
    have hx2 := Nat.le_max_right x.natAbs (normInf xs)
    have hy2 := Nat.le_max_right y.natAbs (normInf ys)
    exact ⟨by omega, by omega⟩

theorem normInf_pos_of_ne :
    ∀ {u v : List Int}, u.length = v.length → u ≠ v → 0 < normInf (vecSub u v) := by
  intro u v hlen hne
  rw [normInf_eq_vecInfNorm, vecSub_eq_compVecSub]
  exact Obend.Judge.Computational.vecInfNorm_pos_of_ne hlen hne

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
    exact Nat.le_trans (natAbs_applyTernaryRow_le cs xs)
      (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
  | .one :: cs, x :: xs => by
    simp only [applyTernaryRow, ternaryRowWeight, normInf]
    have htri := Int.natAbs_add_le x (applyTernaryRow cs xs)
    have ih := natAbs_applyTernaryRow_le cs xs
    have hx := Nat.le_max_left x.natAbs (normInf xs)
    have hmul := Nat.mul_le_mul_left (ternaryRowWeight cs) (Nat.le_max_right x.natAbs (normInf xs))
    rw [Nat.add_mul, Nat.one_mul]; omega
  | .negOne :: cs, x :: xs => by
    simp only [applyTernaryRow, ternaryRowWeight, normInf]
    have htri : (-x + applyTernaryRow cs xs).natAbs ≤ x.natAbs + (applyTernaryRow cs xs).natAbs := by
      simpa [Int.natAbs_neg] using Int.natAbs_add_le (-x) (applyTernaryRow cs xs)
    have ih := natAbs_applyTernaryRow_le cs xs
    have hx := Nat.le_max_left x.natAbs (normInf xs)
    have hmul := Nat.mul_le_mul_left (ternaryRowWeight cs) (Nat.le_max_right x.natAbs (normInf xs))
    rw [Nat.add_mul, Nat.one_mul]; omega

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

/-! ## 3. Exact-Dimension Ajtai Module-SIS Commitment, Homomorphism & Non-Vacuity Witness -/

/-- Public parameters for an exact-dimension $\mathbb{Z}_q^{\text{rows} \times \text{cols}}$ Ajtai commitment. -/
structure AjtaiParams where
  rows : Nat
  cols : Nat
  rows_pos : 0 < rows
  modulus : Nat
  modulus_pos : 0 < modulus
  matrix : List (List Int)
  matrix_rows : matrix.length = rows
  matrix_cols : ∀ row ∈ matrix, row.length = cols

/-- Non-pigeonhole SIS dimension regime guard (`cols ≤ 4 * rows`). -/
@[expose] def NonPigeonholeSISParams (pp : AjtaiParams) : Prop :=
  pp.cols ≤ 4 * pp.rows

theorem ajtai_nonPigeonhole_of_validArity (pp : AjtaiParams) {v : Nat}
    (hCols : pp.cols = 4 * (2 ^ v)) (hRows : 2 ^ v ≤ pp.rows) :
    NonPigeonholeSISParams pp := by
  unfold NonPigeonholeSISParams
  rw [hCols]
  exact Nat.mul_le_mul_left 4 hRows

/-- **Exact-Dimension Integer Inner Product (`dotInt`)**:
    Requires `u.length = v.length` at compile time — mismatched vector lengths CANNOT silently truncate! -/
def dotInt : (u v : List Int) → u.length = v.length → Int
  | [], [], _ => 0
  | r :: rs, w :: ws, h => r * w + dotInt rs ws (Nat.succ.inj h)

theorem dotInt_eq_dotProd :
    ∀ (u v : List Int) (h : u.length = v.length),
      dotInt u v h = Obend.Judge.Computational.dotProd u v
  | [], [], _ => by unfold dotInt Obend.Judge.Computational.dotProd; rfl
  | r :: rs, w :: ws, h => by
    simp only [dotInt, Obend.Judge.Computational.dotProd,
      dotInt_eq_dotProd rs ws (Nat.succ.inj h)]

theorem dotInt_vecAdd :
    ∀ (row u v : List Int) (hru : row.length = u.length) (huv : u.length = v.length),
      dotInt row (vecAdd u v) (hru.trans (vecAdd_length u v huv).symm) =
        dotInt row u hru + dotInt row v (hru.trans huv)
  | [], [], [], _, _ => rfl
  | r :: rs, x :: xs, y :: ys, hru, huv => by
    have hru' : rs.length = xs.length := Nat.succ.inj hru
    have huv' : xs.length = ys.length := Nat.succ.inj huv
    simp only [vecAdd, dotInt, dotInt_vecAdd rs xs ys hru' huv', Int.mul_add]
    omega

theorem dotInt_vecSub :
    ∀ (row u v : List Int) (hru : row.length = u.length) (huv : u.length = v.length),
      dotInt row (vecSub u v) (hru.trans (vecSub_length u v huv).symm) =
        dotInt row u hru - dotInt row v (hru.trans huv)
  | [], [], [], _, _ => rfl
  | r :: rs, x :: xs, y :: ys, hru, huv => by
    have hru' : rs.length = xs.length := Nat.succ.inj hru
    have huv' : xs.length = ys.length := Nat.succ.inj huv
    simp only [vecSub, dotInt, dotInt_vecSub rs xs ys hru' huv', Int.mul_sub]
    omega

private def mapRowsDot :
    (rows : List (List Int)) → (cols : Nat) → (∀ r ∈ rows, r.length = cols) →
    (w : List Int) → w.length = cols → List Int
  | [], _, _, _, _ => []
  | row :: rest, cols, hCols, w, hw =>
    dotInt row w ((hCols row (.head _)).trans hw.symm) ::
      mapRowsDot rest cols (fun r hr => hCols r (.tail _ hr)) w hw

private theorem mapRowsDot_eq_matVecMul :
    ∀ (rows : List (List Int)) (cols : Nat) (hCols : ∀ r ∈ rows, r.length = cols)
      (w : List Int) (hw : w.length = cols),
      mapRowsDot rows cols hCols w hw = Obend.Judge.Computational.matVecMul rows w
  | [], _, _, _, _ => by unfold mapRowsDot Obend.Judge.Computational.matVecMul; rfl
  | row :: rest, cols, hCols, w, hw => by
    simp only [mapRowsDot, Obend.Judge.Computational.matVecMul, List.map_cons,
      dotInt_eq_dotProd, mapRowsDot_eq_matVecMul rest cols _ w hw]

/-- Unreduced integer matrix-vector product $\mathbf{A} \cdot \mathbf{w} \in \mathbb{Z}^{\text{rows}}$
    requiring exact witness length `w.length = pp.cols`. -/
def ajtaiCommitRaw (pp : AjtaiParams) (w : List Int) (hw : w.length = pp.cols) : List Int :=
  mapRowsDot pp.matrix pp.cols pp.matrix_cols w hw

/-- Modular Ajtai commitment $\mathbf{A} \cdot \mathbf{w} \bmod q \in \mathbb{Z}_q^{\text{rows}}$
    requiring exact witness length `w.length = pp.cols`. -/
def ajtaiCommit (pp : AjtaiParams) (w : List Int) (hw : w.length = pp.cols) : List Int :=
  (ajtaiCommitRaw pp w hw).map fun s => s % (pp.modulus : Int)

/-- Coordinate-wise modular vector addition $(\mathbf{u} + \mathbf{v}) \bmod q$. -/
def vecAddMod (q : Int) : List Int → List Int → List Int
  | x :: xs, y :: ys => ((x + y) % q) :: vecAddMod q xs ys
  | _, _ => []

/-- Unreduced Ajtai linear homomorphism: $\mathbf{A}(\mathbf{w}_1 + \mathbf{w}_2) = \mathbf{A}\mathbf{w}_1 + \mathbf{A}\mathbf{w}_2$. -/
theorem ajtaiCommitRaw_add (pp : AjtaiParams) {w₁ w₂ : List Int}
    (hw₁ : w₁.length = pp.cols) (hw₂ : w₂.length = pp.cols) :
    ajtaiCommitRaw pp (vecAdd w₁ w₂) ((vecAdd_length w₁ w₂ (hw₁.trans hw₂.symm)).trans hw₁) =
      vecAdd (ajtaiCommitRaw pp w₁ hw₁) (ajtaiCommitRaw pp w₂ hw₂) := by
  unfold ajtaiCommitRaw
  have aux : ∀ (rows : List (List Int)) (hCols : ∀ r ∈ rows, r.length = pp.cols),
      mapRowsDot rows pp.cols hCols (vecAdd w₁ w₂)
        ((vecAdd_length w₁ w₂ (hw₁.trans hw₂.symm)).trans hw₁) =
      vecAdd (mapRowsDot rows pp.cols hCols w₁ hw₁) (mapRowsDot rows pp.cols hCols w₂ hw₂) := by
    intro rows hCols
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      simp only [mapRowsDot, vecAdd,
        dotInt_vecAdd row w₁ w₂ ((hCols row (.head _)).trans hw₁.symm) (hw₁.trans hw₂.symm),
        ih (fun r hr => hCols r (.tail _ hr))]
  exact aux pp.matrix pp.matrix_cols

/-- **Modular Ajtai Linear Homomorphism (`ajtaiCommit_add`)**:
    $\text{ajtaiCommit}(\mathbf{w}_1 + \mathbf{w}_2) = (\text{ajtaiCommit}(\mathbf{w}_1) + \text{ajtaiCommit}(\mathbf{w}_2)) \bmod q$. -/
theorem ajtaiCommit_add (pp : AjtaiParams) {w₁ w₂ : List Int}
    (hw₁ : w₁.length = pp.cols) (hw₂ : w₂.length = pp.cols) :
    ajtaiCommit pp (vecAdd w₁ w₂) ((vecAdd_length w₁ w₂ (hw₁.trans hw₂.symm)).trans hw₁) =
      vecAddMod (pp.modulus : Int) (ajtaiCommit pp w₁ hw₁) (ajtaiCommit pp w₂ hw₂) := by
  unfold ajtaiCommit
  rw [ajtaiCommitRaw_add pp hw₁ hw₂]
  have aux : ∀ (u v : List Int),
      u.length = v.length →
      (vecAdd u v).map (fun s => s % (pp.modulus : Int)) =
        vecAddMod (pp.modulus : Int)
          (u.map fun s => s % (pp.modulus : Int))
          (v.map fun s => s % (pp.modulus : Int)) := by
    intro u v hlen
    induction u generalizing v with
    | nil =>
      cases v with
      | nil => rfl
      | cons _ _ => simp at hlen
    | cons x xs ih =>
      cases v with
      | nil => simp at hlen
      | cons y ys =>
        simp only [List.length_cons, Nat.succ.injEq] at hlen
        simp only [vecAdd, List.map_cons, vecAddMod, ← Int.add_emod, ih ys hlen]
  apply aux
  unfold ajtaiCommitRaw
  rw [mapRowsDot_eq_matVecMul, mapRowsDot_eq_matVecMul]
  simp [Obend.Judge.Computational.matVecMul]

private theorem matVecModZero_of_ajtaiCommit_eq (pp : AjtaiParams) {w₁ w₂ : List Int}
    (hw₁ : w₁.length = pp.cols) (hw₂ : w₂.length = pp.cols)
    (heq : ajtaiCommit pp w₁ hw₁ = ajtaiCommit pp w₂ hw₂) :
    Obend.Judge.Computational.matVecModZero pp.modulus pp.matrix (vecSub w₁ w₂) = true := by
  unfold ajtaiCommit ajtaiCommitRaw at heq
  rw [mapRowsDot_eq_matVecMul, mapRowsDot_eq_matVecMul] at heq
  have hSubLen : (vecSub w₁ w₂).length = pp.cols :=
    (vecSub_length w₁ w₂ (hw₁.trans hw₂.symm)).trans hw₁
  unfold Obend.Judge.Computational.matVecModZero
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨pp.modulus_pos, ?_⟩
  have hRows : ∀ (rows : List (List Int)),
      (∀ r ∈ rows, r.length = pp.cols) →
      (Obend.Judge.Computational.matVecMul rows w₁).map (fun s => s % (pp.modulus : Int)) =
      (Obend.Judge.Computational.matVecMul rows w₂).map (fun s => s % (pp.modulus : Int)) →
      ∀ row ∈ rows,
        row.length = (vecSub w₁ w₂).length ∧
        (Obend.Judge.Computational.dotProd row (vecSub w₁ w₂)) % (pp.modulus : Int) = 0 := by
    intro rows hCols hMapEq
    induction rows with
    | nil => intro _ hmem; cases hmem
    | cons r rs ih =>
      simp only [Obend.Judge.Computational.matVecMul, List.map_cons, List.cons.injEq] at hMapEq
      intro row hmem
      cases hmem with
      | head =>
        refine ⟨(hCols r (.head _)).trans hSubLen.symm, ?_⟩
        rw [vecSub_eq_compVecSub,
            Obend.Judge.Computational.dotProd_sub r w₁ w₂ (hw₁.trans hw₂.symm),
            Int.sub_emod, hMapEq.1, Int.sub_self, Int.zero_emod]
      | tail _ ht =>
        exact ih (fun r' hr' => hCols r' (.tail _ hr')) hMapEq.2 row ht
  exact hRows pp.matrix pp.matrix_cols heq

/-- **Module-SIS Hardness Predicate (`ModuleSISHard pp B`)**:
    Wired directly to `Obend.Judge.Computational.Unbroken (.moduleSISShortVec pp.modulus B pp.matrix)`:
    no non-zero integer vector `z` of length `pp.cols` and `‖z‖_∞ ≤ B` satisfies `A · z ≡ 0 (mod q)`. -/
@[expose] def ModuleSISHard (pp : AjtaiParams) (B : Nat) : Prop :=
  Unbroken (.moduleSISShortVec pp.modulus B pp.matrix)

/-! ### Constructive Non-Vacuity Proof: `ModuleSISHard` & `NonPigeonholeSISParams` Are Inhabited for Every Arity `v` -/

/-- Radix `262141 = 2 * 131070 + 1` strictly exceeding `2 * B` at `B = 131070`. -/
def sisWitnessRadix : Nat := 262141

private def blockBasisMatrix : Nat → List (List Int)
  | 0 => []
  | m + 1 =>
    let b : Int := (sisWitnessRadix : Int)
    ([1, b, b * b, b * b * b] ++ List.replicate (4 * m) 0) ::
      (blockBasisMatrix m).map (fun r => [0, 0, 0, 0] ++ r)

private theorem blockBasisMatrix_length : ∀ (m : Nat), (blockBasisMatrix m).length = m
  | 0 => rfl
  | m + 1 => by simp [blockBasisMatrix, blockBasisMatrix_length m]

private theorem blockBasisMatrix_cols :
    ∀ (m : Nat) (row : List Int), row ∈ blockBasisMatrix m → row.length = 4 * m
  | 0, _, h => by cases h
  | m + 1, row, h => by
    simp only [blockBasisMatrix, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨r, hr, rfl⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
      omega
    · have ih := blockBasisMatrix_cols m r hr
      simp only [List.length_append, List.length_cons, List.length_nil, ih]
      omega

/-- Concrete `AjtaiParams` for arity `v` (`rows = 2^v`, `cols = 4 * 2^v`, `cols ≤ 4 * rows`,
    `modulus = 262141^4`) whose homogeneous kernel contains **zero** non-zero vectors of norm `≤ 131070`. -/
def inhabitedAjtaiParams (v : Nat) : AjtaiParams where
  rows := 2 ^ v
  cols := 4 * (2 ^ v)
  rows_pos := Nat.two_pow_pos v
  modulus := sisWitnessRadix ^ 4
  modulus_pos := by decide
  matrix := blockBasisMatrix (2 ^ v)
  matrix_rows := blockBasisMatrix_length (2 ^ v)
  matrix_cols := blockBasisMatrix_cols (2 ^ v)

private theorem dotProd_replicate_zero :
    ∀ (n : Nat) (zs : List Int),
      Obend.Judge.Computational.dotProd (List.replicate n 0) zs = 0
  | 0, _ => by unfold Obend.Judge.Computational.dotProd; rfl
  | _ + 1, [] => by unfold List.replicate Obend.Judge.Computational.dotProd; rfl
  | n + 1, _ :: zs => by
    simp [List.replicate_succ, Obend.Judge.Computational.dotProd, dotProd_replicate_zero n zs]

private theorem four_limb_radix_zero {z₀ z₁ z₂ z₃ : Int}
    (h0 : z₀.natAbs ≤ 131070) (h1 : z₁.natAbs ≤ 131070)
    (h2 : z₂.natAbs ≤ 131070) (h3 : z₃.natAbs ≤ 131070)
    (hmod : (1 * z₀ + (sisWitnessRadix : Int) * z₁ +
      (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₂ +
      (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₃) %
      ((sisWitnessRadix ^ 4 : Nat) : Int) = 0) :
    z₀ = 0 ∧ z₁ = 0 ∧ z₂ = 0 ∧ z₃ = 0 := by
  dsimp only [sisWitnessRadix] at hmod
  have hQ : ((262141 ^ 4 : Nat) : Int) = 262141 * 262141 * 262141 * 262141 := by decide
  rw [hQ] at hmod
  omega

private theorem blockBasis_kernel_trivial :
    ∀ (m : Nat) (z : List Int),
      z.length = 4 * m →
      Obend.Judge.Computational.vecInfNorm z ≤ 131070 →
      (∀ row ∈ blockBasisMatrix m,
        (Obend.Judge.Computational.dotProd row z) % ((sisWitnessRadix ^ 4 : Nat) : Int) = 0) →
      Obend.Judge.Computational.vecInfNorm z = 0
  | 0, z, hlen, _, _ => by
    cases z with
    | nil => unfold Obend.Judge.Computational.vecInfNorm; rfl
    | cons _ _ => simp at hlen
  | m + 1, z, hlen, hnorm, hker => by
    match z, hlen with
    | z₀ :: z₁ :: z₂ :: z₃ :: zs, hlen =>
      have hzsLen : zs.length = 4 * m := by
        simp only [List.length_cons] at hlen
        omega
      simp only [Obend.Judge.Computational.vecInfNorm, Nat.max_le] at hnorm
      rcases hnorm with ⟨hz0, hz1, hz2, hz3, hzsNorm⟩
      have hRow0 := hker _ (.head _)
      simp only [List.cons_append, List.nil_append, Obend.Judge.Computational.dotProd,
        dotProd_replicate_zero] at hRow0
      have hSumEq : 1 * z₀ + ((sisWitnessRadix : Int) * z₁ +
          ((sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₂ +
           ((sisWitnessRadix : Int) * (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₃ + 0))) =
          1 * z₀ + (sisWitnessRadix : Int) * z₁ +
          (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₂ +
          (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₃ := by
        omega
      rw [hSumEq] at hRow0
      obtain ⟨rfl, rfl, rfl, rfl⟩ := four_limb_radix_zero hz0 hz1 hz2 hz3 hRow0
      have hTailKer : ∀ r ∈ blockBasisMatrix m,
          (Obend.Judge.Computational.dotProd r zs) % ((sisWitnessRadix ^ 4 : Nat) : Int) = 0 := by
        intro r hr
        have hMem : ([0, 0, 0, 0] ++ r) ∈ blockBasisMatrix (m + 1) :=
          .tail _ (List.mem_map.2 ⟨r, hr, rfl⟩)
        have hDot := hker _ hMem
        simpa [Obend.Judge.Computational.dotProd] using hDot
      have ih := blockBasis_kernel_trivial m zs hzsLen hzsNorm hTailKer
      simp [Obend.Judge.Computational.vecInfNorm, ih]

/-- **Inhabitedness / Non-Vacuity Theorem (`inhabitedAjtaiParams_sisHard`)**:
    For **every** arity `v : Nat`, `inhabitedAjtaiParams v` satisfies exact column width
    `4 * 2 ^ v`, `NonPigeonholeSISParams` (`cols ≤ 4 * rows`), and `ModuleSISHard ... 131070`. -/
theorem inhabitedAjtaiParams_sisHard (v : Nat) :
    (inhabitedAjtaiParams v).cols = 4 * (2 ^ v) ∧
    NonPigeonholeSISParams (inhabitedAjtaiParams v) ∧
    ModuleSISHard (inhabitedAjtaiParams v) 131070 := by
  refine ⟨rfl, Nat.le_refl _, ?_⟩
  rintro ⟨w⟩
  have hInKer := w.inKernel
  unfold Obend.Judge.Computational.matVecModZero at hInKer
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hInKer
  have hMemAny : ∃ r₀, r₀ ∈ (inhabitedAjtaiParams v).matrix := by
    have hpos : 0 < (inhabitedAjtaiParams v).matrix.length := by
      rw [(inhabitedAjtaiParams v).matrix_rows]; exact (inhabitedAjtaiParams v).rows_pos
    cases hm : (inhabitedAjtaiParams v).matrix with
    | nil => rw [hm] at hpos; simp at hpos
    | cons r _ => exact ⟨r, .head _⟩
  obtain ⟨r₀, hr₀⟩ := hMemAny
  have hwLen : w.shortVec.length = 4 * (2 ^ v) :=
    ((hInKer.2 r₀ hr₀).1).symm.trans ((inhabitedAjtaiParams v).matrix_cols r₀ hr₀)
  have hZero := blockBasis_kernel_trivial (2 ^ v) w.shortVec hwLen w.shortNorm
    (fun r hr => (hInKer.2 r hr).2)
  have hPos := w.nonZero
  omega

/-! ## 4. Base-$2^{16}$ Gadget-Decomposed `ajtaiLatticePCS`, Point Binding & `Akita` `SparseOneHotCommit` -/

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

theorem gadgetDecomposeTable_injective {t₁ t₂ : List Goldilocks}
    (h : gadgetDecomposeTable t₁ = gadgetDecomposeTable t₂) : t₁ = t₂ := by
  have hr := congrArg gadgetRecomposeTable h
  rw [gadgetRecomposeTable_decompose, gadgetRecomposeTable_decompose, Option.some.injEq] at hr
  exact hr

/-- Ajtai lattice commitment carrying arity and modular $\mathbb{Z}_q^{\text{rows}}$ syndrome. -/
structure AjtaiCommitment where
  numVars : Nat
  syndrome : List Int
  deriving DecidableEq, Repr

instance : LawfulTranscriptEncode AjtaiCommitment where
  encodeTranscriptBytes c := TranscriptEncode.encodeTranscriptBytes (c.numVars, c.syndrome)
  encodeTranscriptBytes_injective {c₁ c₂} h := by
    have hp := LawfulTranscriptEncode.encodeTranscriptBytes_injective (ι := Nat × List Int) h
    cases c₁; cases c₂
    simp only [Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    rfl

/-- Ajtai lattice opening proof: short base-$2^{16}$ integer witness limbs. -/
structure AjtaiOpeningProof where
  shortLimbs : List Int
  deriving DecidableEq, Repr

/-- `"AJTAI.PCS.OPEN"` transcript label. -/
def ajtaiOpenLabel : ByteArray :=
  Native.bytesOfList [0x41, 0x4a, 0x54, 0x41, 0x49, 0x2e,
                      0x50, 0x43, 0x53, 0x2e, 0x4f, 0x50, 0x45, 0x4e]

/-- Sign-injective canonical byte encoding of an Ajtai syndrome `syn : List Int`. -/
def encodeSyndromeBytes (syn : List Int) : ByteArray :=
  encodeSignedIntBytes syn

theorem encodeSyndromeBytes_injective {s₁ s₂ : List Int}
    (h : encodeSyndromeBytes s₁ = encodeSyndromeBytes s₂) : s₁ = s₂ :=
  encodeSignedIntBytes_injective h

/-- Canonical 3-field frame absorbed by `ajtaiLatticePCS` during opening & verification:
    binds `(encodeSyndromeBytes syn, encodePointBytes claim.point, encodeGoldilocksBytes claim.expectedVal)`. -/
def ajtaiOpenFrame {numVars : Nat} (syn : List Int) (claim : EvalClaim Goldilocks numVars) :
    ByteArray :=
  encodeFrame (encodeSyndromeBytes syn) (encodePointBytes claim.point)
    (encodeGoldilocksBytes claim.expectedVal)

theorem ajtaiOpenFrame_injective {v₁ v₂ : Nat} {s₁ s₂ : List Int}
    {c₁ : EvalClaim Goldilocks v₁} {c₂ : EvalClaim Goldilocks v₂}
    (h : ajtaiOpenFrame s₁ c₁ = ajtaiOpenFrame s₂ c₂) :
    s₁ = s₂ ∧ c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal := by
  obtain ⟨hs, hpt, hval⟩ := encodeFrame_injective h
  exact ⟨encodeSyndromeBytes_injective hs,
         encodePointBytes_injective hpt,
         encodeGoldilocksBytes_injective hval⟩

def ajtaiLatticeCommit (pp : AjtaiParams) (numVars : Nat) (tbl : List Goldilocks) :
    AjtaiCommitment :=
  let limbs := gadgetDecomposeTable tbl
  if hLen : limbs.length = pp.cols then
    { numVars := numVars
      syndrome := ajtaiCommit pp limbs hLen }
  else
    { numVars := numVars
      syndrome := [] }

def ajtaiLatticeOpenEval (pp : AjtaiParams) {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (numVars : Nat) (tbl : List Goldilocks)
    (claim : EvalClaim Goldilocks numVars) (tr : Transcript phase) :
    AjtaiOpeningProof × Transcript phase :=
  let limbs := gadgetDecomposeTable tbl
  let syn := if hLen : limbs.length = pp.cols then ajtaiCommit pp limbs hLen else []
  let tr' := absorbMsg ajtaiOpenLabel (ajtaiOpenFrame syn claim) tr
  (⟨limbs⟩, tr')

def ajtaiLatticeVerifyEval (pp : AjtaiParams) {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (numVars : Nat) (comm : AjtaiCommitment)
    (claim : EvalClaim Goldilocks numVars) (prf : AjtaiOpeningProof)
    (tr : Transcript phase) : Bool × Transcript phase :=
  let tr' := absorbMsg ajtaiOpenLabel (ajtaiOpenFrame comm.syndrome claim) tr
  let ok :=
    (pp.cols == 4 * (2 ^ numVars)) &&
    if hLen : prf.shortLimbs.length = pp.cols then
      (comm.numVars == numVars) &&
      checkShortNorm 65535 prf.shortLimbs &&
      (ajtaiCommit pp prf.shortLimbs hLen == comm.syndrome) &&
      match gadgetRecomposeTable prf.shortLimbs with
      | some tbl => mleEval tbl claim.point == claim.expectedVal
      | none => false
    else false
  (ok, tr')

/-- **Point-Binding Theorem for `ajtaiLatticeVerifyEval` (`ajtaiLatticeVerifyEval_binds_point`)**:
    Two `ajtaiLatticeVerifyEval` calls yielding identical sponge states either bound the exact
    same `(tr, comm.syndrome, claim.point, claim.expectedVal)` tuple or witness a bounded cSHAKE256 collision. -/
theorem ajtaiLatticeVerifyEval_binds_point (pp : AjtaiParams)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {v₁ v₂ : Nat} {comm₁ comm₂ : AjtaiCommitment}
    {c₁ : EvalClaim Goldilocks v₁} {c₂ : EvalClaim Goldilocks v₂}
    {π₁ π₂ : AjtaiOpeningProof} {tr₁ tr₂ : Transcript phase}
    (hState : (ajtaiLatticeVerifyEval pp v₁ comm₁ c₁ π₁ tr₁).2.state =
              (ajtaiLatticeVerifyEval pp v₂ comm₂ c₂ π₂ tr₂).2.state) :
    (tr₁ = tr₂ ∧ comm₁.syndrome = comm₂.syndrome ∧
     c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal) ∨
    BoundedCollision (cshake256Bytes fsAbsorbCustomization)
      (Nat.max
        (encodeFrameList tr₁.state.data.toList ajtaiOpenLabel.data.toList
          (leb128 tr₁.stepCount ++ (ajtaiOpenFrame comm₁.syndrome c₁).data.toList)).length
        (encodeFrameList tr₂.state.data.toList ajtaiOpenLabel.data.toList
          (leb128 tr₂.stepCount ++ (ajtaiOpenFrame comm₂.syndrome c₂).data.toList)).length) := by
  cases extractAbsorbMsgOrEq ajtaiOpenLabel (ajtaiOpenFrame comm₁.syndrome c₁)
      ajtaiOpenLabel (ajtaiOpenFrame comm₂.syndrome c₂) tr₁ tr₂ hState with
  | inl heq =>
    obtain ⟨hs, hpt, hval⟩ := ajtaiOpenFrame_injective heq.2.2
    exact .inl ⟨heq.1, hs, hpt, hval⟩
  | inr w => exact .inr ⟨w⟩

/-- **Constructive Short-Kernel Witness Builder (`extractShortDiffSISWitness`, `0 Classical`)**:
    Given two distinct `pp.cols`-dimensional vectors `u ≠ v` with `‖u‖_∞ ≤ 65535`, `‖v‖_∞ ≤ 65535`,
    and equal `ajtaiCommit`, deterministically constructs `SISShortVecWitness pp.modulus 131070 pp.matrix`. -/
def extractShortDiffSISWitness (pp : AjtaiParams)
    (u v : List Int) (huLen : u.length = pp.cols) (hvLen : v.length = pp.cols)
    (huShort : ShortNormBound 65535 u) (hvShort : ShortNormBound 65535 v)
    (hNe : u ≠ v) (hSyn : ajtaiCommit pp u huLen = ajtaiCommit pp v hvLen) :
    SISShortVecWitness pp.modulus 131070 pp.matrix where
  shortVec := vecSub u v
  nonZero := by
    rw [← normInf_eq_vecInfNorm]
    exact normInf_pos_of_ne (huLen.trans hvLen.symm) hNe
  shortNorm := by
    rw [← normInf_eq_vecInfNorm]
    unfold ShortNormBound at huShort hvShort
    have hSub := normInf_vecSub_le u v
    omega
  inKernel := matVecModZero_of_ajtaiCommit_eq pp huLen hvLen hSyn

/-- **Constructive Ajtai Double-Opening Extractor (`extractAjtaiDoubleOpenSIS`, `0 Classical`)**:
    Two accepted openings of the same `AjtaiCommitment` at `c₁.point = c₂.point` claiming
    `c₁.expectedVal ≠ c₂.expectedVal` deterministically produce `SISShortVecWitness pp.modulus 131070 pp.matrix`
    AND prove `pp.cols = 4 * (2 ^ v)`. -/
def extractAjtaiDoubleOpenSIS (pp : AjtaiParams)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    {v : Nat} {comm : AjtaiCommitment}
    {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : AjtaiOpeningProof}
    {tr₁ : Transcript phase₁} {tr₂ : Transcript phase₂}
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : (ajtaiLatticeVerifyEval pp v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (ajtaiLatticeVerifyEval pp v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    { _w : SISShortVecWitness pp.modulus 131070 pp.matrix // pp.cols = 4 * (2 ^ v) } :=
  have hFacts :
      pp.cols = 4 * (2 ^ v) ∧
      π₁.shortLimbs.length = pp.cols ∧
      π₂.shortLimbs.length = pp.cols ∧
      ShortNormBound 65535 π₁.shortLimbs ∧
      ShortNormBound 65535 π₂.shortLimbs ∧
      π₁.shortLimbs ≠ π₂.shortLimbs ∧
      (∀ (l₁ : π₁.shortLimbs.length = pp.cols) (l₂ : π₂.shortLimbs.length = pp.cols),
        ajtaiCommit pp π₁.shortLimbs l₁ = ajtaiCommit pp π₂.shortLimbs l₂) := by
    unfold ajtaiLatticeVerifyEval at hAcc₁ hAcc₂
    dsimp only at hAcc₁ hAcc₂
    simp only [Bool.and_eq_true, beq_iff_eq] at hAcc₁ hAcc₂
    obtain ⟨hCols, hAcc₁⟩ := hAcc₁
    obtain ⟨_, hAcc₂⟩ := hAcc₂
    if hL₁ : π₁.shortLimbs.length = pp.cols then
      if hL₂ : π₂.shortLimbs.length = pp.cols then
        simp only [hL₁, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hAcc₁
        simp only [hL₂, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hAcc₂
        rcases hAcc₁ with ⟨⟨⟨_, hSh₁⟩, hSyn₁⟩, hRec₁⟩
        rcases hAcc₂ with ⟨⟨⟨_, hSh₂⟩, hSyn₂⟩, hRec₂⟩
        refine ⟨hCols, hL₁, hL₂, hSh₁, hSh₂, ?_, fun _ _ => hSyn₁.trans hSyn₂.symm⟩
        intro hEq
        rw [hEq] at hRec₁
        cases hRec : gadgetRecomposeTable π₂.shortLimbs with
        | none => rw [hRec] at hRec₁; cases hRec₁
        | some tbl =>
          rw [hRec, beq_iff_eq] at hRec₁ hRec₂
          exact hDisagree (by rw [← hRec₁, ← hRec₂, hPt])
      else simp only [hL₂, ↓reduceDIte] at hAcc₂; cases hAcc₂
    else simp only [hL₁, ↓reduceDIte] at hAcc₁; cases hAcc₁
  ⟨extractShortDiffSISWitness pp π₁.shortLimbs π₂.shortLimbs
    hFacts.2.1 hFacts.2.2.1 hFacts.2.2.2.1 hFacts.2.2.2.2.1 hFacts.2.2.2.2.2.1
    (hFacts.2.2.2.2.2.2 hFacts.2.1 hFacts.2.2.1),
   hFacts.1⟩

/-- Proposition-level corollary of `extractAjtaiDoubleOpenSIS`. -/
theorem ajtai_double_open_yields_sis_kernel (pp : AjtaiParams)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    {v : Nat} {comm : AjtaiCommitment}
    {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : AjtaiOpeningProof}
    {tr₁ : Transcript phase₁} {tr₂ : Transcript phase₂}
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : (ajtaiLatticeVerifyEval pp v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (ajtaiLatticeVerifyEval pp v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    Nonempty (SISShortVecWitness pp.modulus 131070 pp.matrix) :=
  ⟨(extractAjtaiDoubleOpenSIS pp hPt hAcc₁ hAcc₂ hDisagree).1⟩

theorem ajtaiLatticePCS_complete_aux (pp : AjtaiParams) :
    ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase]
      (_ : Unit) (v : Nat) (tbl : List Goldilocks)
      (pt : List Goldilocks) (hPt : pt.length = v) (tr : Transcript phase),
      pp.cols = 4 * (2 ^ v) → tbl.length = 2 ^ v →
      let claim : EvalClaim Goldilocks v := ⟨pt, hPt, mleEval tbl pt⟩
      let (prf, _) := ajtaiLatticeOpenEval pp v tbl claim tr
      (ajtaiLatticeVerifyEval pp v (ajtaiLatticeCommit pp v tbl) claim prf tr).1 = true := by
  intro _ _ _ v tbl _ _ _ hCols hTblLen
  have hLimbsLen : (gadgetDecomposeTable tbl).length = pp.cols := by
    rw [gadgetDecomposeTable_length, hTblLen, hCols]
  dsimp only [ajtaiLatticeCommit, ajtaiLatticeOpenEval, ajtaiLatticeVerifyEval]
  simp only [hLimbsLen, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff]
  exact ⟨hCols, ⟨⟨⟨trivial, gadgetDecomposeTable_short tbl⟩, trivial⟩,
         by rw [gadgetRecomposeTable_decompose tbl, beq_iff_eq]⟩⟩

/-- Executable `ajtaiLatticePCS` over `Goldilocks` parameterized by `pp : AjtaiParams`. -/
@[expose, instance_reducible] def ajtaiLatticePCS (pp : AjtaiParams) : MultilinearPCS Goldilocks where
  domainKind := .primeField
  regime := .uniqueDecodingRadius
  validRegime := .primeUDR
  Params := Unit
  Commitment := AjtaiCommitment
  OpeningProof := AjtaiOpeningProof
  ValidArity _ v := pp.cols = 4 * (2 ^ v)
  commit _ v tbl := ajtaiLatticeCommit pp v tbl
  openEval _ v tbl claim tr := ajtaiLatticeOpenEval pp v tbl claim tr
  verifyEval _ v comm claim prf tr := ajtaiLatticeVerifyEval pp v comm claim prf tr
  completeness := ajtaiLatticePCS_complete_aux pp

instance (pp : AjtaiParams) : LawfulTranscriptEncode (ajtaiLatticePCS pp).Commitment :=
  inferInstanceAs (LawfulTranscriptEncode AjtaiCommitment)

/-- **Module-SIS Hardness Implies `BindingSound` (`ajtaiLatticePCS_bindingSound_of_sisHard`, `0 Classical`)**:
    Under `ModuleSISHard pp 131070` (provably inhabited via `inhabitedAjtaiParams_sisHard`),
    `ajtaiLatticePCS pp` is unconditionally evaluation-binding with zero classical axioms. -/
theorem ajtaiLatticePCS_bindingSound_of_sisHard (pp : AjtaiParams)
    (hSIS : ModuleSISHard pp 131070) :
    BindingSound (ajtaiLatticePCS pp) := by
  intro v _ _ _ _ _ comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  if hEq : c₁.expectedVal = c₂.expectedVal then
    exact hEq
  else
    exact False.elim (hSIS ⟨(extractAjtaiDoubleOpenSIS pp hPt hAcc₁ hAcc₂ hEq).1⟩)

/-! ### `Akita` (`2026/1983`) / `Twist & Shout` $O(\text{rows})$ Sparse One-Hot Ajtai Specialization -/

/-- Standard basis integer vector of length `len` with `1` at `col` and `0` elsewhere. -/
def unitVecInt : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, 0 => 1 :: List.replicate n 0
  | n + 1, k + 1 => 0 :: unitVecInt n k

theorem unitVecInt_length : ∀ (len col : Nat), (unitVecInt len col).length = len
  | 0, _ => rfl
  | n + 1, 0 => by simp [unitVecInt]
  | n + 1, k + 1 => by simp [unitVecInt, unitVecInt_length n k]

theorem dotInt_replicate_zero :
    ∀ (row : List Int) (n : Nat) (h : row.length = (List.replicate n (0 : Int)).length),
      dotInt row (List.replicate n 0) h = 0
  | [], 0, _ => rfl
  | r :: rs, n + 1, h => by
    simp [List.replicate_succ, dotInt, dotInt_replicate_zero rs n (Nat.succ.inj h)]

theorem dotInt_unitVecInt :
    ∀ (len col : Nat) (row : List Int) (hLen : row.length = (unitVecInt len col).length),
      col < len →
      dotInt row (unitVecInt len col) hLen = row.getD col 0
  | 0, _, _, _, hlt => by omega
  | n + 1, 0, r :: rs, hLen, _ => by
    have hRep : rs.length = (List.replicate n (0 : Int)).length := by
      simp only [unitVecInt, List.length_cons, Nat.succ.injEq] at hLen
      exact hLen
    simp [unitVecInt, dotInt, dotInt_replicate_zero rs n hRep]
  | n + 1, k + 1, r :: rs, hLen, hlt => by
    have hk : k < n := by omega
    have hSub : rs.length = (unitVecInt n k).length := by
      simp only [unitVecInt, List.length_cons, Nat.succ.injEq] at hLen
      exact hLen
    simp [unitVecInt, dotInt, dotInt_unitVecInt n k rs hSub hk]

example : gadgetDecomposeGoldilocks Goldilocks.zero = [0, 0, 0, 0] := by
  unfold gadgetDecomposeGoldilocks; rfl
example : gadgetDecomposeGoldilocks Goldilocks.one = [1, 0, 0, 0] := by
  unfold gadgetDecomposeGoldilocks; rfl

theorem replicate_append_zero :
    ∀ (a b : Nat), List.replicate a (0 : Int) ++ List.replicate b 0 = List.replicate (a + b) 0
  | 0, _ => by simp
  | a + 1, b => by
    rw [Nat.succ_add]
    simp [List.replicate_succ, replicate_append_zero a b]

theorem unitVecInt_prepend_four_zeros (len k : Nat) :
    ([0, 0, 0, 0] : List Int) ++ unitVecInt len k = unitVecInt (len + 4) (k + 4) := by
  simp [unitVecInt]

theorem gadgetDecompose_oneHot_aux :
    ∀ (m start idx : Nat),
      ((List.range m).map (fun j =>
        if start + j = idx then Goldilocks.one else Goldilocks.zero)).flatMap gadgetDecomposeGoldilocks =
      if idx < start then List.replicate (4 * m) 0
      else if idx < start + m then unitVecInt (4 * m) (4 * (idx - start))
      else List.replicate (4 * m) 0
  | 0, _, _ => by simp [unitVecInt]
  | m + 1, start, idx => by
    have hRange : List.range (m + 1) = 0 :: (List.range m).map (· + 1) := @List.range_succ_eq_map m
    rw [hRange, List.map_cons, List.map_map, List.flatMap_cons]
    have hShift :
        ((List.range m).map ((fun j => if start + j = idx then Goldilocks.one else Goldilocks.zero) ∘ (· + 1))) =
        ((List.range m).map (fun j => if (start + 1) + j = idx then Goldilocks.one else Goldilocks.zero)) :=
      List.map_congr_left fun j _ => by dsimp only [Function.comp]; rw [show start + (j + 1) = (start + 1) + j by omega]
    rw [hShift, gadgetDecompose_oneHot_aux m (start + 1) idx]
    if hEq : start = idx then
      subst hEq
      have hOne : gadgetDecomposeGoldilocks Goldilocks.one = [1, 0, 0, 0] := rfl
      simp only [Nat.add_zero, ↓reduceIte, hOne,
        show start < start + 1 by omega, show ¬ start < start by omega, show start < start + (m + 1) by omega]
      rw [Nat.sub_self, Nat.mul_zero, show 4 * (m + 1) = 4 * m + 4 by omega]
      simp [unitVecInt, List.replicate_succ]
    else
      have hHead : (if start + 0 = idx then Goldilocks.one else Goldilocks.zero) = Goldilocks.zero := by
        rw [Nat.add_zero]; simp [hEq]
      have hZero : gadgetDecomposeGoldilocks Goldilocks.zero = [0, 0, 0, 0] := rfl
      have h4 : ([0, 0, 0, 0] : List Int) = List.replicate 4 0 := rfl
      rw [hHead, hZero]
      if hLt : idx < start then
        simp only [hLt, show idx < start + 1 by omega, ↓reduceIte]
        rw [h4, replicate_append_zero]; congr 1; omega
      else
        simp only [hLt, show ¬ idx < start + 1 by omega, ↓reduceIte]
        if hIn : idx < start + (m + 1) then
          simp only [hIn, show idx < start + 1 + m by omega, ↓reduceIte]
          rw [unitVecInt_prepend_four_zeros, show 4 * m + 4 = 4 * (m + 1) by omega,
              show 4 * (idx - (start + 1)) + 4 = 4 * (idx - start) by omega]
        else
          simp only [hIn, show ¬ idx < start + 1 + m by omega, ↓reduceIte]
          rw [h4, replicate_append_zero]; congr 1; omega

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
    $O(2^v)$ `ajtaiLatticePCS` commitment on `oneHotTable Goldilocks v idx` when `pp.cols = 4 * 2 ^ v`. -/
instance ajtaiSparseOneHot (pp : AjtaiParams) :
    SparseOneHotCommit Goldilocks (ajtaiLatticePCS pp) where
  commitOneHot _ v idx := ajtaiCommitOneHotColumn pp v idx
  commitOneHot_eq_commit := by
    intro _ v idx hCols hIdx
    change ajtaiCommitOneHotColumn pp v idx = ajtaiLatticeCommit pp v (oneHotTable Goldilocks v idx)
    dsimp only [ajtaiLatticeCommit, ajtaiCommitOneHotColumn]
    have hDecomp := gadgetDecomposeTable_oneHot v idx hIdx
    have hUnitLen : (gadgetDecomposeTable (oneHotTable Goldilocks v idx)).length = pp.cols := by
      rw [hDecomp, unitVecInt_length, hCols]
    simp only [hUnitLen, ↓reduceDIte]
    congr 1
    unfold ajtaiCommit ajtaiCommitRaw
    have aux : ∀ (rows : List (List Int)) (hR : ∀ r ∈ rows, r.length = pp.cols),
        (rows.map fun row => (row.getD (4 * idx) 0) % (pp.modulus : Int)) =
        (mapRowsDot rows pp.cols hR (gadgetDecomposeTable (oneHotTable Goldilocks v idx)) hUnitLen).map
          (fun s => s % (pp.modulus : Int)) := by
      intro rows hR
      induction rows with
      | nil => rfl
      | cons row rest ih =>
        simp only [List.map_cons, mapRowsDot, List.cons.injEq]
        refine ⟨?_, ih (fun r hr => hR r (.tail _ hr))⟩
        congr 1
        have hColLt : 4 * idx < 4 * 2 ^ v := by omega
        have hRowLen : row.length = (unitVecInt (4 * 2 ^ v) (4 * idx)).length := by
          rw [unitVecInt_length, hR row (.head _), hCols]
        have hDotEq :
            dotInt row (gadgetDecomposeTable (oneHotTable Goldilocks v idx))
              ((hR row (.head _)).trans hUnitLen.symm) =
            dotInt row (unitVecInt (4 * 2 ^ v) (4 * idx)) hRowLen := by
          rw [dotInt_eq_dotProd, dotInt_eq_dotProd, hDecomp]
        rw [hDotEq, dotInt_unitVecInt (4 * 2 ^ v) (4 * idx) row hRowLen hColLt]
    exact aux pp.matrix pp.matrix_cols

/-! ## 5. Cross-Assumption `DualPCS P₁ P₂`, Constructive `dualExtract` (`0 Classical`) & Survival Theorem -/

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

def dualOpenEval {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (pp : P₁.Params × P₂.Params) (v : Nat) (tbl : List R)
    (claim : EvalClaim R v) (tr : Transcript phase) :
    (P₁.OpeningProof × P₂.OpeningProof) × Transcript phase :=
  let tr₁ := absorbMsg dualTrack1Label ByteArray.empty tr
  let tr₂ := absorbMsg dualTrack2Label ByteArray.empty tr
  let (π₁, tr₁') := P₁.openEval pp.1 v tbl claim tr₁
  let (π₂, tr₂') := P₂.openEval pp.2 v tbl claim tr₂
  ((π₁, π₂), absorbMsg dualJoinLabel (encodeFrame tr₁'.state tr₂'.state ByteArray.empty) tr)

def dualVerifyEval {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (pp : P₁.Params × P₂.Params) (v : Nat) (comm : P₁.Commitment × P₂.Commitment)
    (claim : EvalClaim R v) (prf : P₁.OpeningProof × P₂.OpeningProof)
    (tr : Transcript phase) : Bool × Transcript phase :=
  let tr₁ := absorbMsg dualTrack1Label ByteArray.empty tr
  let tr₂ := absorbMsg dualTrack2Label ByteArray.empty tr
  let (ok₁, tr₁') := P₁.verifyEval pp.1 v comm.1 claim prf.1 tr₁
  let (ok₂, tr₂') := P₂.verifyEval pp.2 v comm.2 claim prf.2 tr₂
  (dualVerdictJoin ok₁ ok₂,
   absorbMsg dualJoinLabel (encodeFrame tr₁'.state tr₂'.state ByteArray.empty) tr)

theorem dualPCS_complete_aux {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R) :
    ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase]
      (pp : P₁.Params × P₂.Params) (v : Nat) (tbl : List R)
      (pt : List R) (hPt : pt.length = v) (tr : Transcript phase),
      (P₁.ValidArity pp.1 v ∧ P₂.ValidArity pp.2 v) → tbl.length = 2 ^ v →
      let claim : EvalClaim R v := ⟨pt, hPt, mleEval tbl pt⟩
      let (prf, _) := dualOpenEval P₁ P₂ pp v tbl claim tr
      (dualVerifyEval P₁ P₂ pp v (P₁.commit pp.1 v tbl, P₂.commit pp.2 v tbl) claim prf tr).1 = true := by
  intro _ _ pp v tbl pt hPt tr hValid hTblLen
  dsimp only [dualOpenEval, dualVerifyEval, dualVerdictJoin]
  rw [Bool.and_eq_true]
  exact ⟨P₁.completeness pp.1 v tbl pt hPt (absorbMsg dualTrack1Label ByteArray.empty tr) hValid.1 hTblLen,
         P₂.completeness pp.2 v tbl pt hPt (absorbMsg dualTrack2Label ByteArray.empty tr) hValid.2 hTblLen⟩

/-- **Cross-Assumption `DualPCS P₁ P₂` Product Combinator**:
    Pairs any two `MultilinearPCS R` backends under one shared `EvalClaim R v` and `Transcript phase`. -/
@[expose, instance_reducible] def DualPCS {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R) : MultilinearPCS R where
  domainKind := dualDomainKind P₁.domainKind P₂.domainKind
  regime := dualProximityRegime P₁.domainKind P₂.domainKind P₁.regime P₂.regime
  validRegime := dualValidProximityConfig P₁.domainKind P₂.domainKind P₁.regime P₂.regime
  Params := P₁.Params × P₂.Params
  Commitment := P₁.Commitment × P₂.Commitment
  OpeningProof := P₁.OpeningProof × P₂.OpeningProof
  ValidArity pp v := P₁.ValidArity pp.1 v ∧ P₂.ValidArity pp.2 v
  commit pp v tbl := (P₁.commit pp.1 v tbl, P₂.commit pp.2 v tbl)
  openEval := dualOpenEval P₁ P₂
  verifyEval := dualVerifyEval P₁ P₂
  completeness := dualPCS_complete_aux P₁ P₂

instance {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R)
    [LawfulTranscriptEncode P₁.Commitment] [LawfulTranscriptEncode P₂.Commitment] :
    LawfulTranscriptEncode (DualPCS P₁ P₂).Commitment :=
  inferInstanceAs (LawfulTranscriptEncode (P₁.Commitment × P₂.Commitment))

/-- Explicit standalone completeness theorem for `DualPCS P₁ P₂`. -/
theorem dualPCS_completeness {R : Type} [CommRingOps R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (P₁ P₂ : MultilinearPCS R)
    (pp : P₁.Params × P₂.Params) (v : Nat) (tbl : List R)
    (pt : List R) (hPt : pt.length = v) (tr : Transcript phase)
    (hValid : (DualPCS P₁ P₂).ValidArity pp v)
    (hTblLen : tbl.length = 2 ^ v) :
    let claim : EvalClaim R v := ⟨pt, hPt, mleEval tbl pt⟩
    let (prf, _) := (DualPCS P₁ P₂).openEval pp v tbl claim tr
    ((DualPCS P₁ P₂).verifyEval pp v ((DualPCS P₁ P₂).commit pp v tbl) claim prf tr).1 = true :=
  (DualPCS P₁ P₂).completeness pp v tbl pt hPt tr hValid hTblLen

/-- Arity-scoped cryptographic redundancy theorem (`dualPCS_bindingSoundAt_of_either`). -/
theorem dualPCS_bindingSoundAt_of_either {R : Type} [CommRingOps R]
    (v : Nat) (P₁ P₂ : MultilinearPCS R)
    (hEither : BindingSoundAt v P₁ ∨ BindingSoundAt v P₂) :
    BindingSoundAt v (DualPCS P₁ P₂) := by
  intro _ _ _ _ pp comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  simp only [DualPCS, dualVerifyEval, dualVerdictJoin, Bool.and_eq_true] at hAcc₁ hAcc₂
  rcases hEither with hSound₁ | hSound₂
  · exact hSound₁ pp.1 comm.1 c₁ c₂ π₁.1 π₂.1
      (absorbMsg dualTrack1Label ByteArray.empty tr₁)
      (absorbMsg dualTrack1Label ByteArray.empty tr₂)
      hPt hAcc₁.1 hAcc₂.1
  · exact hSound₂ pp.2 comm.2 c₁ c₂ π₁.2 π₂.2
      (absorbMsg dualTrack2Label ByteArray.empty tr₁)
      (absorbMsg dualTrack2Label ByteArray.empty tr₂)
      hPt hAcc₁.2 hAcc₂.2

/-- **Cryptographic Redundancy Theorem (`dualPCS_sound_of_either`)**:
    If *either* `P₁` or `P₂` is evaluation-binding, `DualPCS P₁ P₂` is evaluation-binding. -/
theorem dualPCS_sound_of_either {R : Type} [CommRingOps R]
    (P₁ P₂ : MultilinearPCS R)
    (hEither : BindingSound P₁ ∨ BindingSound P₂) :
    BindingSound (DualPCS P₁ P₂) := by
  intro v
  exact dualPCS_bindingSoundAt_of_either v P₁ P₂
    (hEither.elim (fun h₁ => .inl (h₁ v)) (fun h₂ => .inr (h₂ v)))

/-- Concrete deployed dual-track PCS over `Goldilocks`: pairs 256-bit cSHAKE256 `canopyMerklePCS`
    (`HashUDR`) with exact-dimension base-$2^{16}$ `ajtaiLatticePCS` (`ModuleSIS`). -/
@[expose, instance_reducible] def canopyAjtaiDualPCS (H : Hash32) (pp : AjtaiParams) : MultilinearPCS Goldilocks :=
  DualPCS (canopyMerklePCS H) (ajtaiLatticePCS pp)

/-! ### Constructive `Type`-Valued Witness Extraction (`DualForgery`, `dualExtract`, `dualExtractBoth`, `0 Classical`) -/

/-- Double-opening forgery bundle on `canopyAjtaiDualPCS H pp` at arity `v`. -/
structure DualDoubleOpenForgery (H : Hash32) (pp : AjtaiParams) (v : Nat) where
  comm : CanopyCommitment × AjtaiCommitment
  c₁ : EvalClaim Goldilocks v
  c₂ : EvalClaim Goldilocks v
  π₁ : CanopyOpeningProof × AjtaiOpeningProof
  π₂ : CanopyOpeningProof × AjtaiOpeningProof
  tr₁ : Transcript .relationBound
  tr₂ : Transcript .relationBound
  samePoint : c₁.point = c₂.point
  disagree : c₁.expectedVal ≠ c₂.expectedVal
  acc₁ : ((canopyAjtaiDualPCS H pp).verifyEval ((), ()) v comm c₁ π₁ tr₁).1 = true
  acc₂ : ((canopyAjtaiDualPCS H pp).verifyEval ((), ()) v comm c₂ π₂ tr₂).1 = true

/-- **Simultaneous Product Witness Extractor (`dualExtractBoth`, `0 Classical`)**:
    Any accepted double-opening of `canopyAjtaiDualPCS H pp` deterministically produces **both**
    a `HashCollisionWitness H.eval (merkleMaxPreimageBytes v)` **and** a
    `SISShortVecWitness pp.modulus 131070 pp.matrix`! -/
def dualExtractBoth {H : Hash32} {pp : AjtaiParams} {v : Nat}
    (f : DualDoubleOpenForgery H pp v) :
    HashCollisionWitness H.eval (merkleMaxPreimageBytes v) ×
    SISShortVecWitness pp.modulus 131070 pp.matrix :=
  have hBoth₁ :
      (canopyVerifyEval H v f.comm.1 f.c₁ f.π₁.1
        (absorbMsg dualTrack1Label ByteArray.empty f.tr₁)).1 = true ∧
      (ajtaiLatticeVerifyEval pp v f.comm.2 f.c₁ f.π₁.2
        (absorbMsg dualTrack2Label ByteArray.empty f.tr₁)).1 = true := by
    simpa [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS,
           dualVerdictJoin, Bool.and_eq_true] using f.acc₁
  have hBoth₂ :
      (canopyVerifyEval H v f.comm.1 f.c₂ f.π₂.1
        (absorbMsg dualTrack1Label ByteArray.empty f.tr₂)).1 = true ∧
      (ajtaiLatticeVerifyEval pp v f.comm.2 f.c₂ f.π₂.2
        (absorbMsg dualTrack2Label ByteArray.empty f.tr₂)).1 = true := by
    simpa [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS,
           dualVerdictJoin, Bool.and_eq_true] using f.acc₂
  (extractCanopyDoubleOpenCollision H f.samePoint hBoth₁.1 hBoth₂.1 f.disagree,
   (extractAjtaiDoubleOpenSIS pp f.samePoint hBoth₁.2 hBoth₂.2 f.disagree).1)

/-- Unified `Type`-valued forgery sum (`DualForgery H pp v`) covering:
    1. `sameTableMerkleMismatch`: conflicting value `val ≠ tbl[idx]` authenticated at index `idx`
       of a committed table `tbl` (conflicting directly with `openMerkle H tbl idx`);
    2. `crossTableMismatch`: an accepted `canopyAjtaiDualPCS` opening `(claim, π)` against a
       pair of committed tables `(tblMerkle, tblAjtai)` (including both honest `tblMerkle = tblAjtai`
       and split/cross-table `tblMerkle ≠ tblAjtai`) where `claim.expectedVal` disagrees with
       `mleEval tblMerkle claim.point` or `mleEval tblAjtai claim.point`;
    3. `doubleOpening`: two conflicting `canopyAjtaiDualPCS` openings at the same evaluation point. -/
inductive DualForgery (H : Hash32) (pp : AjtaiParams) (v : Nat) : Type where
  | sameTableMerkleMismatch
      (tbl : List Goldilocks) (hTbl : tbl.length = 2 ^ v)
      (idx : Nat) (hIdx : idx < 2 ^ v)
      (val : Goldilocks) (path : List Digest32)
      (hNe : val ≠ tbl[idx]'(by omega))
      (hVer : verifyMerklePath H (2 ^ v) idx val path (canopyCommit H v tbl).root = true)
  | crossTableMismatch
      (tblMerkle tblAjtai : List Goldilocks)
      (hLenM : tblMerkle.length = 2 ^ v)
      (hLenA : tblAjtai.length = 2 ^ v)
      (hCols : pp.cols = 4 * (2 ^ v))
      (claim : EvalClaim Goldilocks v)
      (π : CanopyOpeningProof × AjtaiOpeningProof)
      (tr : Transcript .relationBound)
      (hAcc : ((canopyAjtaiDualPCS H pp).verifyEval ((), ()) v
                (canopyCommit H v tblMerkle, ajtaiLatticeCommit pp v tblAjtai) claim π tr).1 = true)
      (hDisagree : claim.expectedVal ≠ mleEval tblMerkle claim.point ∨
                   claim.expectedVal ≠ mleEval tblAjtai claim.point)
  | doubleOpening (f : DualDoubleOpenForgery H pp v)

/-- **Constructive `Type`-Valued Dual Witness Extractor (`dualExtract`, `0 Classical`)**:
    Deterministically extracts a bounded hash collision or SIS short vector from `DualForgery H pp v`. -/
def dualExtract {H : Hash32} {pp : AjtaiParams} {v : Nat}
    (forgery : DualForgery H pp v) :
    PSum (HashCollisionWitness H.eval (merkleMaxPreimageBytes v))
         (SISShortVecWitness pp.modulus 131070 pp.matrix) :=
  match forgery with
  | .sameTableMerkleMismatch tbl hTbl idx hIdx val path hNe hVer =>
    .inl (extractMerklePathCollision H hIdx path (openMerkle H tbl idx)
            (canopyCommit H v tbl).root hNe hVer (verifyMerklePath_openMerkle H v tbl hTbl idx hIdx))
  | .crossTableMismatch tblM tblA hLenM hLenA hCols claim π tr hAcc hDisagree =>
    have hBoth :
        (canopyVerifyEval H v (canopyCommit H v tblM) claim π.1
          (absorbMsg dualTrack1Label ByteArray.empty tr)).1 = true ∧
        (ajtaiLatticeVerifyEval pp v (ajtaiLatticeCommit pp v tblA) claim π.2
          (absorbMsg dualTrack2Label ByteArray.empty tr)).1 = true := by
      simpa [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS,
             dualVerdictJoin, Bool.and_eq_true] using hAcc
    if hEqM : claim.expectedVal = mleEval tblM claim.point then
      have hNeA : claim.expectedVal ≠ mleEval tblA claim.point :=
        hDisagree.elim (fun hbad => False.elim (hbad hEqM)) id
      let honestLimbs := gadgetDecomposeTable tblA
      have hHonestLen : honestLimbs.length = pp.cols := by
        dsimp [honestLimbs]; rw [gadgetDecomposeTable_length, hLenA, hCols]
      have hAjtaiFacts :
          π.2.shortLimbs.length = pp.cols ∧
          ShortNormBound 65535 π.2.shortLimbs ∧
          π.2.shortLimbs ≠ honestLimbs ∧
          (∀ l₁ : π.2.shortLimbs.length = pp.cols,
            ajtaiCommit pp π.2.shortLimbs l₁ = ajtaiCommit pp honestLimbs hHonestLen) := by
        have hHonestLen' : (gadgetDecomposeTable tblA).length = pp.cols := hHonestLen
        have hAccA := hBoth.2
        unfold ajtaiLatticeVerifyEval ajtaiLatticeCommit at hAccA
        dsimp only at hAccA
        simp only [Bool.and_eq_true, beq_iff_eq] at hAccA
        obtain ⟨_, hAccA⟩ := hAccA
        if hPrfLen : π.2.shortLimbs.length = pp.cols then
          simp only [hPrfLen, hHonestLen', ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hAccA
          rcases hAccA with ⟨⟨⟨_, hSh⟩, hSyn⟩, hRec⟩
          refine ⟨hPrfLen, hSh, ?_, fun _ => hSyn⟩
          intro hEqLimbs
          rw [hEqLimbs, gadgetRecomposeTable_decompose tblA, beq_iff_eq] at hRec
          exact hNeA hRec.symm
        else
          simp only [hPrfLen, ↓reduceDIte] at hAccA; cases hAccA
      .inr (extractShortDiffSISWitness pp π.2.shortLimbs honestLimbs
              hAjtaiFacts.1 hHonestLen hAjtaiFacts.2.1 (gadgetDecomposeTable_short tblA)
              hAjtaiFacts.2.2.1 (hAjtaiFacts.2.2.2 hAjtaiFacts.1))
    else
      have hTblMNe : π.1.entries.map Prod.fst ≠ tblM := by
        have hAccM := hBoth.1
        simp only [canopyVerifyEval, Bool.and_eq_true, beq_iff_eq] at hAccM
        intro hEqEntries
        rw [hEqEntries] at hAccM
        exact hEqM hAccM.2.symm
      .inl (extractCanopyOpenMerkleCollision H tblM hLenM π.1
              (absorbMsg dualTrack1Label ByteArray.empty tr) hBoth.1 hTblMNe)
  | .doubleOpening f =>
    .inl (dualExtractBoth f).1

/-- **Constructive Commitment-Collision Extractor (`extractDualCommitCollisionBoth`, `0 Classical`)**:
    If two distinct `2 ^ v`-element `Goldilocks` tables `t₁ ≠ t₂` (`pp.cols = 4 * 2 ^ v`) produce
    equal `canopyAjtaiDualPCS H pp` commitments, deterministically extracts **both** a
    `HashCollisionWitness` (via `openMerkle`) AND a `SISShortVecWitness`! -/
def extractDualCommitCollisionBoth (H : Hash32) (pp : AjtaiParams) {v : Nat}
    (t₁ t₂ : List Goldilocks) (ht₁ : t₁.length = 2 ^ v) (ht₂ : t₂.length = 2 ^ v)
    (hCols : pp.cols = 4 * (2 ^ v)) (hNe : t₁ ≠ t₂)
    (hCommEq : (canopyAjtaiDualPCS H pp).commit ((), ()) v t₁ =
               (canopyAjtaiDualPCS H pp).commit ((), ()) v t₂) :
    HashCollisionWitness H.eval (merkleMaxPreimageBytes v) ×
    SISShortVecWitness pp.modulus 131070 pp.matrix :=
  let diff := findDiffIndex t₁ t₂ (ht₁.trans ht₂.symm) hNe
  let idx := diff.1
  have hIdxPow : idx < 2 ^ v := by
    obtain ⟨hx, _, _⟩ := diff.2
    simpa [ht₁] using hx
  have hIn₁ : idx < t₁.length := by rw [ht₁]; exact hIdxPow
  have hIn₂ : idx < t₂.length := by rw [ht₂]; exact hIdxPow
  have hNeAt : t₁[idx]'hIn₁ ≠ t₂[idx]'hIn₂ := by
    obtain ⟨_, _, hne⟩ := diff.2
    exact hne
  have hPairEq : canopyCommit H v t₁ = canopyCommit H v t₂ ∧
      ajtaiLatticeCommit pp v t₁ = ajtaiLatticeCommit pp v t₂ :=
    Prod.mk.inj hCommEq
  have hRootEq : (canopyCommit H v t₁).root = (canopyCommit H v t₂).root :=
    congrArg CanopyCommitment.root hPairEq.1
  have hVer₁ := verifyMerklePath_openMerkle H v t₁ ht₁ idx hIdxPow
  have hVer₂ : verifyMerklePath H (2 ^ v) idx (t₂[idx]'hIn₂)
      (openMerkle H t₂ idx) (canopyCommit H v t₁).root = true := by
    rw [hRootEq]
    exact verifyMerklePath_openMerkle H v t₂ ht₂ idx hIdxPow
  let hashWit := extractMerklePathCollision H hIdxPow
    (openMerkle H t₁ idx) (openMerkle H t₂ idx) (canopyCommit H v t₁).root hNeAt hVer₁ hVer₂
  let limbs₁ := gadgetDecomposeTable t₁
  let limbs₂ := gadgetDecomposeTable t₂
  have hL₁ : limbs₁.length = pp.cols := by
    dsimp [limbs₁]; rw [gadgetDecomposeTable_length, ht₁, hCols]
  have hL₂ : limbs₂.length = pp.cols := by
    dsimp [limbs₂]; rw [gadgetDecomposeTable_length, ht₂, hCols]
  have hLimbsNe : limbs₁ ≠ limbs₂ := fun h => hNe (gadgetDecomposeTable_injective h)
  have hSynEq : ajtaiCommit pp limbs₁ hL₁ = ajtaiCommit pp limbs₂ hL₂ := by
    have hAj := congrArg AjtaiCommitment.syndrome hPairEq.2
    simpa [ajtaiLatticeCommit, limbs₁, limbs₂, hL₁, hL₂] using hAj
  let sisWit := extractShortDiffSISWitness pp limbs₁ limbs₂ hL₁ hL₂
    (gadgetDecomposeTable_short t₁) (gadgetDecomposeTable_short t₂) hLimbsNe hSynEq
  (hashWit, sisWit)

/-- **Non-Vacuous Arity-Scoped Hash-or-Lattice Survival Theorem (`canopyAjtaiDualPCS_bindingSoundAt_of_hash_or_sis`)**:
    At any arity `v`, if **either** `¬ BoundedCollision H.eval (merkleMaxPreimageBytes v)` **or**
    `ModuleSISHard pp 131070` holds, `canopyAjtaiDualPCS H pp` is evaluation-binding (`0 Classical`).
    Both disjuncts are provably satisfiable (`toyInjectiveHash32_no_boundedCollision`, `inhabitedAjtaiParams_sisHard`). -/
theorem canopyAjtaiDualPCS_bindingSoundAt_of_hash_or_sis
    (H : Hash32) (pp : AjtaiParams) (v : Nat)
    (hOr : ¬ BoundedCollision H.eval (merkleMaxPreimageBytes v) ∨ ModuleSISHard pp 131070) :
    BindingSoundAt v (canopyAjtaiDualPCS H pp) := by
  apply dualPCS_bindingSoundAt_of_either
  rcases hOr with hNoCol | hSIS
  · exact .inl (canopyMerklePCS_bindingSoundAt_of_boundedCollisionFree H v hNoCol)
  · exact .inr (ajtaiLatticePCS_bindingSound_of_sisHard pp hSIS v)

/-- **Concrete Hash-or-Lattice Survival Theorem (`canopyAjtaiDualPCS_sound_of_hash_or_sis`, `0 Classical`)**:
    Because `ajtaiLatticeVerifyEval` enforces `pp.cols = 4 * 2 ^ v`, only the arity matching `pp.cols`
    can accept! Thus if **either** `H.eval` has no bounded collision at the `pp.cols`-compatible arity
    **or** `ModuleSISHard pp 131070` holds, `canopyAjtaiDualPCS H pp` is globally `BindingSound`.
    Both disjuncts are unconditionally satisfiable (`toyInjectiveHash32`, `inhabitedAjtaiParams`)! -/
theorem canopyAjtaiDualPCS_sound_of_hash_or_sis (H : Hash32) (pp : AjtaiParams)
    (hOr : (∀ v : Nat, pp.cols = 4 * (2 ^ v) → ¬ BoundedCollision H.eval (merkleMaxPreimageBytes v)) ∨
           ModuleSISHard pp 131070) :
    BindingSound (canopyAjtaiDualPCS H pp) := by
  intro v _ _ _ _ _ comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  if hEq : c₁.expectedVal = c₂.expectedVal then
    exact hEq
  else
    simp only [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS,
               dualVerdictJoin, Bool.and_eq_true] at hAcc₁ hAcc₂
    let sisOut := extractAjtaiDoubleOpenSIS pp hPt hAcc₁.2 hAcc₂.2 hEq
    rcases hOr with hNoCol | hSIS
    · have hCol := extractCanopyDoubleOpenCollision H hPt hAcc₁.1 hAcc₂.1 hEq
      exact False.elim (hNoCol v sisOut.2 ⟨hCol⟩)
    · exact False.elim (hSIS ⟨sisOut.1⟩)

/-- Explicit non-vacuity witness 1 (Hash disjunct): `BindingSound` via `¬ BoundedCollision` alone! -/
example : BindingSound (canopyAjtaiDualPCS toyInjectiveHash32 (inhabitedAjtaiParams 0)) :=
  canopyAjtaiDualPCS_sound_of_hash_or_sis toyInjectiveHash32 (inhabitedAjtaiParams 0)
    (.inl fun v hv => by
      have hv0 : v = 0 := by
        change 4 = 4 * (2 ^ v) at hv
        cases v with
        | zero => rfl
        | succ k =>
          have hge : 2 ≤ 2 ^ (k + 1) := by
            rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega
          omega
      subst hv0
      exact toyInjectiveHash32_no_boundedCollision (by decide))

/-- Explicit non-vacuity witness 2 (Lattice disjunct): `BindingSound` via `ModuleSISHard` alone! -/
theorem canopyAjtaiDualPCS_inhabited_sis_branch (H : Hash32) (v : Nat) :
    BindingSound (canopyAjtaiDualPCS H (inhabitedAjtaiParams v)) :=
  canopyAjtaiDualPCS_sound_of_hash_or_sis H (inhabitedAjtaiParams v)
    (.inr (inhabitedAjtaiParams_sisHard v).2.2)

/-! ## 6. Instance-Bound `verifyDualSumcheckPIOP` (Closing Statement/Commitment Grinding `F3`) -/

/-- Bind `(comm, numVars, claimedSum)` into `BoundTranscript` (`.instanceBound`) BEFORE squeezing challenges. -/
def bindDualSumcheckInstance
    {Commit₁ Commit₂ R : Type} [TranscriptEncode Commit₁] [TranscriptEncode Commit₂]
    [TranscriptEncode R]
    (comm : Commit₁ × Commit₂) (numVars : Nat) (claimedSum : R)
    (tr : Transcript .relationBound) :
    BoundTranscript (comm, (numVars, claimedSum)) :=
  bindInstance (comm, (numVars, claimedSum)) tr

/-- **Instance-Binding Theorem (`bindDualSumcheckInstance_binds`)**:
    Equal `.instanceBound` sponge states imply identical `(tr, comm, numVars, claimedSum)` or a
    bounded cSHAKE256 collision on `fsInstanceCustomization` (defeating `0`-grinding across commitments/sums). -/
theorem bindDualSumcheckInstance_binds
    {Commit₁ Commit₂ R : Type}
    [LawfulTranscriptEncode Commit₁] [LawfulTranscriptEncode Commit₂] [LawfulTranscriptEncode R]
    {c₁ c₂ : Commit₁ × Commit₂} {v₁ v₂ : Nat} {s₁ s₂ : R}
    {tr₁ tr₂ : Transcript .relationBound}
    (hState : (bindDualSumcheckInstance c₁ v₁ s₁ tr₁).transcript.state =
              (bindDualSumcheckInstance c₂ v₂ s₂ tr₂).transcript.state) :
    (tr₁ = tr₂ ∧ c₁ = c₂ ∧ v₁ = v₂ ∧ s₁ = s₂) ∨
    BoundedCollision (cshake256Bytes fsInstanceCustomization)
      (Nat.max
        (instancePreimageList tr₁.state tr₁.stepCount
          (TranscriptEncode.encodeTranscriptBytes (c₁, (v₁, s₁)))).length
        (instancePreimageList tr₂.state tr₂.stepCount
          (TranscriptEncode.encodeTranscriptBytes (c₂, (v₂, s₂)))).length) := by
  rcases bindInstance_binds_or_collides hState with ⟨htr, hinst⟩ | hcol
  · simp only [Prod.mk.injEq] at hinst
    exact .inl ⟨htr, hinst.1, hinst.2.1, hinst.2.2⟩
  · exact .inr hcol

/-- **End-to-End Instance-Bound Dual-Spine Sumcheck + PCS Verifier (`verifyDualSumcheckPIOP`)**:
    Absorbs `(comm, numVars, claimedSum)` into `.instanceBound` via `bindDualSumcheckInstance`
    BEFORE squeezing any Fiat–Shamir challenge, then verifies `DualPCS P₁ P₂` on the bound tuple. -/
def verifyDualSumcheckPIOP
    {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] [TranscriptEncode R]
    (P₁ P₂ : MultilinearPCS R)
    [TranscriptEncode P₁.Commitment] [TranscriptEncode P₂.Commitment]
    (pp : P₁.Params × P₂.Params)
    (maxDeg numVars : Nat) (comm : P₁.Commitment × P₂.Commitment)
    (claimedSum : R) (rounds : List (RoundPoly R))
    (openingPrf : P₁.OpeningProof × P₂.OpeningProof)
    (tr : Transcript .relationBound) : Bool :=
  let btr := bindDualSumcheckInstance comm numVars claimedSum tr
  match verifyBoundSumcheck (Commit := P₁.Commitment × P₂.Commitment) (R := R) maxDeg btr rounds with
  | none => false
  | some (boundComm, claim, trAfterSumcheck) =>
    ((DualPCS (R := R) P₁ P₂).verifyEval pp btr.inst.2.1 boundComm claim openingPrf trAfterSumcheck).1

theorem verifyDualSumcheckPIOP_completeness
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R] [TranscriptEncode R]
    (P₁ P₂ : MultilinearPCS R)
    [TranscriptEncode P₁.Commitment] [TranscriptEncode P₂.Commitment]
    (pp : P₁.Params × P₂.Params)
    {maxDeg : Nat} (hDeg : 1 ≤ maxDeg) (v : Nat) (tbl : List R)
    (tr : Transcript .relationBound)
    (hValid : (DualPCS P₁ P₂).ValidArity pp v)
    (hTblLen : tbl.length = 2 ^ v) :
    let comm : P₁.Commitment × P₂.Commitment := (DualPCS (R := R) P₁ P₂).commit pp v tbl
    let (rounds, claim, trAfter) := honestBoundSumcheckProver (R := R) comm v tbl tr
    let (prf, _) := (DualPCS (R := R) P₁ P₂).openEval pp v tbl claim trAfter
    verifyDualSumcheckPIOP (R := R) P₁ P₂ pp maxDeg v
      comm (hypercubeSum v tbl) rounds prf tr = true := by
  let comm : P₁.Commitment × P₂.Commitment := (P₁.commit pp.1 v tbl, P₂.commit pp.2 v tbl)
  obtain ⟨hVerBound, hVal⟩ :=
    verifyBoundSumcheck_completeness (Commit := P₁.Commitment × P₂.Commitment) (R := R)
      hDeg comm v tbl tr
  let sc := honestSumcheckProver v tbl (bindInstance (comm, (v, hypercubeSum v tbl)) tr).transcript
  have hCompl := (DualPCS P₁ P₂).completeness pp v tbl sc.2.1.point sc.2.1.point_len sc.2.2 hValid hTblLen
  dsimp only [verifyDualSumcheckPIOP, bindDualSumcheckInstance, BoundTranscript.inst,
              honestBoundSumcheckProver, DualPCS] at hVerBound hVal hCompl ⊢
  dsimp only [comm, sc] at hVerBound hVal hCompl
  rw [hVerBound]
  dsimp only
  have hClaimMle : sc.2.1 = ⟨sc.2.1.point, sc.2.1.point_len, mleEval tbl sc.2.1.point⟩ := by
    cases hcl : sc.2.1 with
    | mk pt hPt expVal =>
      have hVal' : expVal = mleEval tbl pt := by simpa [sc, comm, hcl] using hVal
      subst hVal'; rfl
  dsimp only [sc, comm] at hClaimMle
  rw [hClaimMle]
  exact hCompl

end Obend.Crypto
end
