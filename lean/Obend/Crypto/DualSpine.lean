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
public import Obend.Crypto.GameSoundness
public import Obend.Judge.Computational
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.PCS
import all Obend.Crypto.GameSoundness
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
def normInf : List Int → Nat | [] => 0 | x :: xs => max x.natAbs (normInf xs)
theorem normInf_eq_vecInfNorm : ∀ (w : List Int), normInf w = Obend.Judge.Computational.vecInfNorm w
  | [] => by unfold normInf Obend.Judge.Computational.vecInfNorm; rfl
  | x :: xs => by simp only [normInf, Obend.Judge.Computational.vecInfNorm, normInf_eq_vecInfNorm xs]
@[expose] def ShortNormBound (β : Nat) (w : List Int) : Prop := normInf w ≤ β
@[expose] def Short (cols β : Nat) (w : List Int) : Prop := w.length = cols ∧ normInf w ≤ β
def checkShortNorm (β : Nat) (w : List Int) : Bool := decide (normInf w ≤ β)
theorem checkShortNorm_iff (β : Nat) (w : List Int) : checkShortNorm β w = true ↔ ShortNormBound β w := by simp [checkShortNorm, ShortNormBound]
theorem normInf_cons_le_iff {x : Int} {xs : List Int} {B : Nat} : normInf (x :: xs) ≤ B ↔ x.natAbs ≤ B ∧ normInf xs ≤ B := by simp only [normInf, Nat.max_le]
theorem mem_natAbs_le_normInf {x : Int} {w : List Int} (hx : x ∈ w) : x.natAbs ≤ normInf w := by
  induction w with
  | nil => cases hx
  | cons y ys ih => simp only [List.mem_cons] at hx; simp only [normInf]; exact hx.elim (fun h => h ▸ Nat.le_max_left _ _) (fun hm => Nat.le_trans (ih hm) (Nat.le_max_right _ _))
theorem normInf_le_of_forall {w : List Int} {B : Nat} (h : ∀ x ∈ w, x.natAbs ≤ B) : normInf w ≤ B := by
  induction w with | nil => exact Nat.zero_le B | cons x xs ih => exact (normInf_cons_le_iff).2 ⟨h x (.head xs), ih (fun y hy => h y (.tail x hy))⟩
def vecAdd : List Int → List Int → List Int | x :: xs, y :: ys => (x + y) :: vecAdd xs ys | _, _ => []
def vecSub : List Int → List Int → List Int | x :: xs, y :: ys => (x - y) :: vecSub xs ys | _, _ => []
theorem vecSub_eq_compVecSub : ∀ (u v : List Int), vecSub u v = Obend.Judge.Computational.vecSub u v
  | [], [] | [], _ :: _ | _ :: _, [] => by unfold vecSub Obend.Judge.Computational.vecSub; rfl
  | x :: xs, y :: ys => by simp only [vecSub, Obend.Judge.Computational.vecSub, vecSub_eq_compVecSub xs ys]
theorem vecAdd_length : ∀ (u v : List Int), u.length = v.length → (vecAdd u v).length = u.length
  | [], [], _ => rfl | _ :: xs, _ :: ys, h => by simp [vecAdd, vecAdd_length xs ys (Nat.succ.inj h)]
theorem vecSub_length : ∀ (u v : List Int), u.length = v.length → (vecSub u v).length = u.length
  | [], [], _ => rfl | _ :: xs, _ :: ys, h => by simp [vecSub, vecSub_length xs ys (Nat.succ.inj h)]

theorem normInf_vecAdd_le : ∀ (u v : List Int), normInf (vecAdd u v) ≤ normInf u + normInf v
  | [], _ | _ :: _, [] => Nat.zero_le _
  | x :: xs, y :: ys => by
    simp only [vecAdd, normInf]; rw [Nat.max_le]
    have htri := Int.natAbs_add_le x y; have ih := normInf_vecAdd_le xs ys
    have hx1 := Nat.le_max_left x.natAbs (normInf xs); have hy1 := Nat.le_max_left y.natAbs (normInf ys)
    have hx2 := Nat.le_max_right x.natAbs (normInf xs); have hy2 := Nat.le_max_right y.natAbs (normInf ys)
    exact ⟨by omega, by omega⟩

theorem normInf_vecSub_le : ∀ (u v : List Int), normInf (vecSub u v) ≤ normInf u + normInf v
  | [], _ | _ :: _, [] => Nat.zero_le _
  | x :: xs, y :: ys => by
    simp only [vecSub, normInf]; rw [Nat.max_le]
    have htri : (x - y).natAbs ≤ x.natAbs + y.natAbs := by
      simpa [Int.sub_eq_add_neg, Int.natAbs_neg] using Int.natAbs_add_le x (-y)
    have ih := normInf_vecSub_le xs ys
    have hx1 := Nat.le_max_left x.natAbs (normInf xs); have hy1 := Nat.le_max_left y.natAbs (normInf ys)
    have hx2 := Nat.le_max_right x.natAbs (normInf xs); have hy2 := Nat.le_max_right y.natAbs (normInf ys)
    exact ⟨by omega, by omega⟩

theorem normInf_pos_of_ne {u v : List Int} (hlen : u.length = v.length) (hne : u ≠ v) :
    0 < normInf (vecSub u v) := by
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
  | [], _ | .negOne :: _, [] | .zero :: _, [] | .one :: _, [] => Nat.zero_le _
  | .zero :: cs, _ :: xs => by
    simp only [applyTernaryRow, ternaryRowWeight, normInf]
    exact Nat.le_trans (natAbs_applyTernaryRow_le cs xs) (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
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
theorem normInf_ternaryProj_le (proj : List (List TernaryCoeff)) (w : List Int) (k β : Nat)
    (hRows : ∀ row ∈ proj, ternaryRowWeight row ≤ k) (hShort : ShortNormBound β w) :
    ShortNormBound (k * β) (applyTernaryProj proj w) :=
  normInf_le_of_forall fun _ hy => by
    obtain ⟨row, hRowMem, rfl⟩ := List.mem_map.1 hy
    exact Nat.le_trans (natAbs_applyTernaryRow_le row w) (Nat.mul_le_mul (hRows row hRowMem) hShort)

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
theorem ajtaiCommit_add (pp : AjtaiParams) {w₁ w₂ : List Int} (hw₁ : w₁.length = pp.cols) (hw₂ : w₂.length = pp.cols) :
    ajtaiCommit pp (vecAdd w₁ w₂) ((vecAdd_length w₁ w₂ (hw₁.trans hw₂.symm)).trans hw₁) =
      vecAddMod (pp.modulus : Int) (ajtaiCommit pp w₁ hw₁) (ajtaiCommit pp w₂ hw₂) := by
  unfold ajtaiCommit; rw [ajtaiCommitRaw_add pp hw₁ hw₂]
  have aux : ∀ (u v : List Int), u.length = v.length →
      (vecAdd u v).map (fun s => s % (pp.modulus : Int)) =
        vecAddMod (pp.modulus : Int) (u.map fun s => s % (pp.modulus : Int)) (v.map fun s => s % (pp.modulus : Int)) := by
    intro u v hlen; induction u generalizing v with
    | nil => cases v with | nil => rfl | cons _ _ => simp at hlen
    | cons x xs ih =>
      cases v with
      | nil => simp at hlen
      | cons y ys => simp only [List.length_cons, Nat.succ.injEq] at hlen; simp only [vecAdd, List.map_cons, vecAddMod, ← Int.add_emod, ih ys hlen]
  apply aux; unfold ajtaiCommitRaw; rw [mapRowsDot_eq_matVecMul, mapRowsDot_eq_matVecMul]; simp [Obend.Judge.Computational.matVecMul]

private theorem matVecModZero_of_ajtaiCommit_eq (pp : AjtaiParams) {w₁ w₂ : List Int}
    (hw₁ : w₁.length = pp.cols) (hw₂ : w₂.length = pp.cols) (heq : ajtaiCommit pp w₁ hw₁ = ajtaiCommit pp w₂ hw₂) :
    Obend.Judge.Computational.matVecModZero pp.modulus pp.matrix (vecSub w₁ w₂) = true := by
  unfold ajtaiCommit ajtaiCommitRaw at heq; rw [mapRowsDot_eq_matVecMul, mapRowsDot_eq_matVecMul] at heq
  have hSubLen : (vecSub w₁ w₂).length = pp.cols := (vecSub_length w₁ w₂ (hw₁.trans hw₂.symm)).trans hw₁
  unfold Obend.Judge.Computational.matVecModZero
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]; refine ⟨pp.modulus_pos, ?_⟩
  have hRows : ∀ (rows : List (List Int)), (∀ r ∈ rows, r.length = pp.cols) →
      (Obend.Judge.Computational.matVecMul rows w₁).map (fun s => s % (pp.modulus : Int)) =
      (Obend.Judge.Computational.matVecMul rows w₂).map (fun s => s % (pp.modulus : Int)) →
      ∀ row ∈ rows, row.length = (vecSub w₁ w₂).length ∧ (Obend.Judge.Computational.dotProd row (vecSub w₁ w₂)) % (pp.modulus : Int) = 0 := by
    intro rows hCols hMapEq; induction rows with
    | nil => intro _ hmem; cases hmem
    | cons r rs ih =>
      simp only [Obend.Judge.Computational.matVecMul, List.map_cons, List.cons.injEq] at hMapEq
      intro row hmem; cases hmem with
      | head =>
        refine ⟨(hCols r (.head _)).trans hSubLen.symm, ?_⟩
        rw [vecSub_eq_compVecSub, Obend.Judge.Computational.dotProd_sub r w₁ w₂ (hw₁.trans hw₂.symm), Int.sub_emod, hMapEq.1, Int.sub_self, Int.zero_emod]
      | tail _ ht => exact ih (fun r' hr' => hCols r' (.tail _ hr')) hMapEq.2 row ht
  exact hRows pp.matrix pp.matrix_cols heq

/-- **Module-SIS Short-Kernel Hardness (`ModuleSISHard pp B`)**:
    Asserts no non-zero `B`-short kernel vector exists for `pp.matrix` mod `pp.modulus`
    (paired with `NonPigeonholeSISParams pp` in non-compressing theorems, or replaced by
    CRS-sampled `GameSoundness.msisAdvantage` in compressing `4 * rows < cols` regimes). -/
@[expose] def ModuleSISHard (pp : AjtaiParams) (B : Nat) : Prop :=
  NonPigeonholeSISParams pp ∧ (Nonempty (SISShortVecWitness pp.modulus B pp.matrix) → False)

instance {pp : AjtaiParams} {B : Nat} :
    CoeFun (ModuleSISHard pp B) (fun _ => Nonempty (SISShortVecWitness pp.modulus B pp.matrix) → False) :=
  ⟨And.right⟩

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
    · simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]; omega
    · have ih := blockBasisMatrix_cols m r hr
      simp only [List.length_append, List.length_cons, List.length_nil, ih]; omega

/-- Concrete non-pigeonhole `AjtaiParams` (`rows = 2^v`, `cols = 4 * 2^v`, `cols ≤ 4 * rows`,
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
    ∀ (n : Nat) (zs : List Int), Obend.Judge.Computational.dotProd (List.replicate n 0) zs = 0
  | 0, _ => by unfold Obend.Judge.Computational.dotProd; rfl
  | _ + 1, [] => by unfold List.replicate Obend.Judge.Computational.dotProd; rfl
  | n + 1, _ :: zs => by simp [List.replicate_succ, Obend.Judge.Computational.dotProd, dotProd_replicate_zero n zs]

private theorem four_limb_radix_zero {z₀ z₁ z₂ z₃ : Int}
    (h0 : z₀.natAbs ≤ 131070) (h1 : z₁.natAbs ≤ 131070) (h2 : z₂.natAbs ≤ 131070) (h3 : z₃.natAbs ≤ 131070)
    (hmod : (1 * z₀ + (sisWitnessRadix : Int) * z₁ +
      (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₂ +
      (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₃) %
      ((sisWitnessRadix ^ 4 : Nat) : Int) = 0) :
    z₀ = 0 ∧ z₁ = 0 ∧ z₂ = 0 ∧ z₃ = 0 := by
  dsimp only [sisWitnessRadix] at hmod
  rw [show ((262141 ^ 4 : Nat) : Int) = 262141 * 262141 * 262141 * 262141 by decide] at hmod
  omega

private theorem blockBasis_kernel_trivial :
    ∀ (m : Nat) (z : List Int), z.length = 4 * m → Obend.Judge.Computational.vecInfNorm z ≤ 131070 →
      (∀ row ∈ blockBasisMatrix m, (Obend.Judge.Computational.dotProd row z) % ((sisWitnessRadix ^ 4 : Nat) : Int) = 0) →
      Obend.Judge.Computational.vecInfNorm z = 0
  | 0, [], _, _, _ => by unfold Obend.Judge.Computational.vecInfNorm; rfl
  | 0, _ :: _, hlen, _, _ => by simp at hlen
  | _ + 1, [], hlen, _, _ => by simp at hlen
  | _ + 1, [_], hlen, _, _ => by simp at hlen; omega
  | _ + 1, [_, _], hlen, _, _ => by simp at hlen; omega
  | _ + 1, [_, _, _], hlen, _, _ => by simp at hlen; omega
  | m + 1, z₀ :: z₁ :: z₂ :: z₃ :: zs, hlen, hnorm, hker => by
    have hzsLen : zs.length = 4 * m := by simp only [List.length_cons] at hlen; omega
    simp only [Obend.Judge.Computational.vecInfNorm, Nat.max_le] at hnorm
    rcases hnorm with ⟨hz0, hz1, hz2, hz3, hzsNorm⟩
    have hRow0 := hker _ (.head _)
    simp only [List.cons_append, List.nil_append, Obend.Judge.Computational.dotProd, dotProd_replicate_zero] at hRow0
    have hSumEq : 1 * z₀ + ((sisWitnessRadix : Int) * z₁ + ((sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₂ +
        ((sisWitnessRadix : Int) * (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₃ + 0))) =
        1 * z₀ + (sisWitnessRadix : Int) * z₁ + (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₂ +
        (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * (sisWitnessRadix : Int) * z₃ := by omega
    rw [hSumEq] at hRow0; obtain ⟨rfl, rfl, rfl, rfl⟩ := four_limb_radix_zero hz0 hz1 hz2 hz3 hRow0
    have ih := blockBasis_kernel_trivial m zs hzsLen hzsNorm fun r hr => by
      simpa [Obend.Judge.Computational.dotProd] using hker _ (.tail _ (List.mem_map.2 ⟨r, hr, rfl⟩))
    simp [Obend.Judge.Computational.vecInfNorm, ih]

/-- **Inhabitedness / Non-Vacuity Theorem (`inhabitedAjtaiParams_sisHard`)**:
    For **every** arity `v : Nat`, `inhabitedAjtaiParams v` satisfies exact column width
    `4 * 2 ^ v`, `NonPigeonholeSISParams` (`cols ≤ 4 * rows`), and `ModuleSISHard ... 131070`. -/
theorem inhabitedAjtaiParams_sisHard (v : Nat) :
    (inhabitedAjtaiParams v).cols = 4 * (2 ^ v) ∧
    NonPigeonholeSISParams (inhabitedAjtaiParams v) ∧
    ModuleSISHard (inhabitedAjtaiParams v) 131070 := by
  refine ⟨rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  rintro ⟨w⟩
  have hInKer := w.inKernel
  unfold Obend.Judge.Computational.matVecModZero at hInKer
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hInKer
  have hpos : 0 < (inhabitedAjtaiParams v).matrix.length := by
    rw [(inhabitedAjtaiParams v).matrix_rows]; exact (inhabitedAjtaiParams v).rows_pos
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ ∈ (inhabitedAjtaiParams v).matrix := by
    cases hm : (inhabitedAjtaiParams v).matrix with
    | nil => rw [hm] at hpos; simp at hpos
    | cons r _ => exact ⟨r, .head _⟩
  have hwLen : w.shortVec.length = 4 * (2 ^ v) :=
    ((hInKer.2 r₀ hr₀).1).symm.trans ((inhabitedAjtaiParams v).matrix_cols r₀ hr₀)
  have hZero := blockBasis_kernel_trivial (2 ^ v) w.shortVec hwLen w.shortNorm (fun r hr => (hInKer.2 r hr).2)
  have hPos := w.nonZero
  omega

/-! ## 4. Base-$2^{16}$ Gadget-Decomposed `ajtaiLatticePCS`, Point Binding & `Akita` `SparseOneHotCommit` -/

def gadgetDecomposeGoldilocks (x : Goldilocks) : List Int :=
  let n := x.val
  [(((n % 65536) : Nat) : Int), ((((n / 65536) % 65536) : Nat) : Int),
   ((((n / 4294967296) % 65536) : Nat) : Int), (((n / 281474976710656) : Nat) : Int)]

def gadgetDecomposeTable (tbl : List Goldilocks) : List Int := tbl.flatMap gadgetDecomposeGoldilocks

theorem gadgetDecomposeTable_length (tbl : List Goldilocks) : (gadgetDecomposeTable tbl).length = 4 * tbl.length := by
  unfold gadgetDecomposeTable; induction tbl with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, gadgetDecomposeGoldilocks, List.cons_append, List.nil_append, List.length_cons, ih]; omega

theorem gadgetDecomposeGoldilocks_short (x : Goldilocks) : ∀ z ∈ gadgetDecomposeGoldilocks x, z.natAbs ≤ 65535 := by
  intro z hz; have h64 : x.val < 2 ^ 64 := Goldilocks.val_lt_two_pow_64 x
  simp only [gadgetDecomposeGoldilocks, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> omega

theorem gadgetDecomposeTable_short (tbl : List Goldilocks) : ShortNormBound 65535 (gadgetDecomposeTable tbl) :=
  normInf_le_of_forall fun z hz => by
    unfold gadgetDecomposeTable at hz; obtain ⟨x, _, hzx⟩ := List.mem_flatMap.1 hz
    exact gadgetDecomposeGoldilocks_short x z hzx

def gadgetRecomposeOne (l₀ l₁ l₂ l₃ : Int) : Option Goldilocks :=
  if 0 ≤ l₀ && l₀ < 65536 && 0 ≤ l₁ && l₁ < 65536 && 0 ≤ l₂ && l₂ < 65536 && 0 ≤ l₃ && l₃ < 65536 then
    let v : Nat := l₀.toNat + 65536 * l₁.toNat + 4294967296 * l₂.toNat + 281474976710656 * l₃.toNat
    if hv : v < goldilocksPrime then some ⟨v, hv⟩ else none
  else none

theorem gadgetRecomposeOne_decompose (x : Goldilocks) :
    gadgetRecomposeOne (((x.val % 65536 : Nat) : Int)) ((((x.val / 65536) % 65536 : Nat) : Int))
      ((((x.val / 4294967296) % 65536 : Nat) : Int)) (((x.val / 281474976710656 : Nat) : Int)) = some x := by
  unfold gadgetRecomposeOne; have h64 : x.val < 2 ^ 64 := Goldilocks.val_lt_two_pow_64 x
  have hCond : (decide (0 ≤ (((x.val % 65536 : Nat) : Int))) && decide ((((x.val % 65536 : Nat) : Int)) < 65536) &&
      decide (0 ≤ ((((x.val / 65536) % 65536 : Nat) : Int))) && decide (((((x.val / 65536) % 65536 : Nat) : Int)) < 65536) &&
      decide (0 ≤ ((((x.val / 4294967296) % 65536 : Nat) : Int))) && decide (((((x.val / 4294967296) % 65536 : Nat) : Int)) < 65536) &&
      decide (0 ≤ (((x.val / 281474976710656 : Nat) : Int))) && decide ((((x.val / 281474976710656 : Nat) : Int)) < 65536)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  rw [hCond]; simp only [↓reduceIte]
  have hVal : (((x.val % 65536 : Nat) : Int)).toNat + 65536 * ((((x.val / 65536) % 65536 : Nat) : Int)).toNat +
      4294967296 * ((((x.val / 4294967296) % 65536 : Nat) : Int)).toNat +
      281474976710656 * (((x.val / 281474976710656 : Nat) : Int)).toNat = x.val := by omega
  simp only [hVal, x.isLt, ↓reduceDIte]

def gadgetRecomposeTable : List Int → Option (List Goldilocks)
  | [] => some []
  | l₀ :: l₁ :: l₂ :: l₃ :: rest =>
    match gadgetRecomposeOne l₀ l₁ l₂ l₃, gadgetRecomposeTable rest with
    | some x, some xs => some (x :: xs)
    | _, _ => none
  | _ => none

theorem gadgetRecomposeTable_decompose : ∀ (tbl : List Goldilocks), gadgetRecomposeTable (gadgetDecomposeTable tbl) = some tbl
  | [] => rfl
  | x :: xs => by
    have ih := gadgetRecomposeTable_decompose xs; unfold gadgetDecomposeTable at ih ⊢
    simp only [List.flatMap_cons, gadgetDecomposeGoldilocks, List.cons_append, List.nil_append, gadgetRecomposeTable, gadgetRecomposeOne_decompose x, ih]

theorem gadgetDecomposeTable_injective {t₁ t₂ : List Goldilocks} (h : gadgetDecomposeTable t₁ = gadgetDecomposeTable t₂) : t₁ = t₂ := by
  have hr := congrArg gadgetRecomposeTable h
  rw [gadgetRecomposeTable_decompose, gadgetRecomposeTable_decompose, Option.some.injEq] at hr; exact hr

structure AjtaiCommitment where
  numVars : Nat
  syndrome : List Int
  deriving DecidableEq, Repr

instance : LawfulTranscriptEncode AjtaiCommitment where
  encodeTranscriptBytes c := TranscriptEncode.encodeTranscriptBytes (c.numVars, c.syndrome)
  encodeTranscriptBytes_injective {c₁ c₂} h := by
    have hp := LawfulTranscriptEncode.encodeTranscriptBytes_injective (ι := Nat × List Int) h
    cases c₁; cases c₂; simp only [Prod.mk.injEq] at hp; rcases hp with ⟨rfl, rfl⟩; rfl

structure AjtaiOpeningProof where
  shortLimbs : List Int
  deriving DecidableEq, Repr

def ajtaiOpenLabel : ByteArray :=
  Native.bytesOfList [0x41, 0x4a, 0x54, 0x41, 0x49, 0x2e, 0x50, 0x43, 0x53, 0x2e, 0x4f, 0x50, 0x45, 0x4e]

def encodeSyndromeBytes (syn : List Int) : ByteArray := encodeSignedIntBytes syn

theorem encodeSyndromeBytes_injective {s₁ s₂ : List Int} (h : encodeSyndromeBytes s₁ = encodeSyndromeBytes s₂) : s₁ = s₂ :=
  encodeSignedIntBytes_injective h

def ajtaiOpenFrame {numVars : Nat} (syn : List Int) (claim : EvalClaim Goldilocks numVars) : ByteArray :=
  encodeFrame (encodeSyndromeBytes syn) (encodePointBytes claim.point) (encodeGoldilocksBytes claim.expectedVal)

theorem ajtaiOpenFrame_injective {v₁ v₂ : Nat} {s₁ s₂ : List Int} {c₁ : EvalClaim Goldilocks v₁} {c₂ : EvalClaim Goldilocks v₂}
    (h : ajtaiOpenFrame s₁ c₁ = ajtaiOpenFrame s₂ c₂) : s₁ = s₂ ∧ c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal := by
  obtain ⟨hs, hpt, hval⟩ := encodeFrame_injective h
  exact ⟨encodeSyndromeBytes_injective hs, encodePointBytes_injective hpt, encodeGoldilocksBytes_injective hval⟩

def ajtaiLatticeCommit (pp : AjtaiParams) (numVars : Nat) (tbl : List Goldilocks) : AjtaiCommitment :=
  let limbs := gadgetDecomposeTable tbl
  if hLen : limbs.length = pp.cols then { numVars := numVars, syndrome := ajtaiCommit pp limbs hLen }
  else { numVars := numVars, syndrome := [] }

def ajtaiLatticeOpenEval (pp : AjtaiParams) {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (numVars : Nat) (tbl : List Goldilocks) (claim : EvalClaim Goldilocks numVars) (tr : Transcript phase) :
    AjtaiOpeningProof × Transcript phase :=
  let limbs := gadgetDecomposeTable tbl
  let syn := if hLen : limbs.length = pp.cols then ajtaiCommit pp limbs hLen else []
  (⟨limbs⟩, absorbMsg ajtaiOpenLabel (ajtaiOpenFrame syn claim) tr)

def ajtaiLatticeVerifyEval (pp : AjtaiParams) {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (numVars : Nat) (comm : AjtaiCommitment) (claim : EvalClaim Goldilocks numVars) (prf : AjtaiOpeningProof)
    (tr : Transcript phase) : Bool × Transcript phase :=
  let tr' := absorbMsg ajtaiOpenLabel (ajtaiOpenFrame comm.syndrome claim) tr
  let ok := (pp.cols == 4 * (2 ^ numVars)) &&
    if hLen : prf.shortLimbs.length = pp.cols then
      (comm.numVars == numVars) && checkShortNorm 65535 prf.shortLimbs &&
      (ajtaiCommit pp prf.shortLimbs hLen == comm.syndrome) &&
      match gadgetRecomposeTable prf.shortLimbs with
      | some tbl => mleEval tbl claim.point == claim.expectedVal
      | none => false
    else false
  (ok, tr')

def ajtaiAbsorbFrameList {phase : TranscriptPhase} {v : Nat}
    (comm : AjtaiCommitment) (claim : EvalClaim Goldilocks v) (tr : Transcript phase) : List UInt8 :=
  encodeFrameList tr.state.data.toList ajtaiOpenLabel.data.toList
    (leb128 tr.stepCount ++ (ajtaiOpenFrame comm.syndrome claim).data.toList)

def extractAjtaiVerifyEvalPointOrCollision (pp : AjtaiParams)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase] {v₁ v₂ : Nat} (comm₁ comm₂ : AjtaiCommitment)
    (c₁ : EvalClaim Goldilocks v₁) (c₂ : EvalClaim Goldilocks v₂) (π₁ π₂ : AjtaiOpeningProof) (tr₁ tr₂ : Transcript phase)
    (hState : (ajtaiLatticeVerifyEval pp v₁ comm₁ c₁ π₁ tr₁).2.state = (ajtaiLatticeVerifyEval pp v₂ comm₂ c₂ π₂ tr₂).2.state) :
    PSum (tr₁ = tr₂ ∧ comm₁.syndrome = comm₂.syndrome ∧ c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal)
      { p : List UInt8 × List UInt8 // p.1 = ajtaiAbsorbFrameList comm₁ c₁ tr₁ ∧ p.2 = ajtaiAbsorbFrameList comm₂ c₂ tr₂ ∧
        p.1 ≠ p.2 ∧ cshake256Bytes fsAbsorbCustomization p.1 = cshake256Bytes fsAbsorbCustomization p.2 } :=
  let f₁ := ajtaiAbsorbFrameList comm₁ c₁ tr₁; let f₂ := ajtaiAbsorbFrameList comm₂ c₂ tr₂
  if hf : f₁ = f₂ then
    .inl (by
      dsimp only [f₁, f₂, ajtaiAbsorbFrameList] at hf
      obtain ⟨hs, _, hcm⟩ := encodeFrameList_injective hf; obtain ⟨hc, hm⟩ := leb128_prefix_inj hcm
      have hsBA := byteArray_eq_of_toList_eq hs
      have htr : tr₁ = tr₂ := by cases tr₁; cases tr₂; simp only at hsBA hc; subst hsBA hc; rfl
      obtain ⟨hsyn, hpt, hval⟩ := ajtaiOpenFrame_injective (byteArray_eq_of_toList_eq hm)
      exact ⟨htr, hsyn, hpt, hval⟩)
  else
    .inr ⟨(f₁, f₂), rfl, rfl, hf, by
      dsimp only [ajtaiLatticeVerifyEval] at hState; rw [absorbMsg_state_eq, absorbMsg_state_eq] at hState
      simpa only [cshake32ByteArray, Native.bytesOfList_toList, f₁, f₂, ajtaiAbsorbFrameList] using congrArg (fun b => b.data.toList) hState⟩

theorem ajtaiLatticeVerifyEval_binds_point (pp : AjtaiParams)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase] {v₁ v₂ : Nat} {comm₁ comm₂ : AjtaiCommitment}
    {c₁ : EvalClaim Goldilocks v₁} {c₂ : EvalClaim Goldilocks v₂} {π₁ π₂ : AjtaiOpeningProof} {tr₁ tr₂ : Transcript phase}
    (hState : (ajtaiLatticeVerifyEval pp v₁ comm₁ c₁ π₁ tr₁).2.state = (ajtaiLatticeVerifyEval pp v₂ comm₂ c₂ π₂ tr₂).2.state) :
    (tr₁ = tr₂ ∧ comm₁.syndrome = comm₂.syndrome ∧ c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal) ∨
    (ajtaiAbsorbFrameList comm₁ c₁ tr₁ ≠ ajtaiAbsorbFrameList comm₂ c₂ tr₂ ∧
     cshake256Bytes fsAbsorbCustomization (ajtaiAbsorbFrameList comm₁ c₁ tr₁) =
       cshake256Bytes fsAbsorbCustomization (ajtaiAbsorbFrameList comm₂ c₂ tr₂)) := by
  cases extractAjtaiVerifyEvalPointOrCollision pp comm₁ comm₂ c₁ c₂ π₁ π₂ tr₁ tr₂ hState with
  | inl heq => exact .inl heq
  | inr w => rcases w with ⟨⟨_, _⟩, hp₁, hp₂, hNe, hHash⟩; dsimp only at hp₁ hp₂ hNe hHash; rw [hp₁, hp₂] at hNe hHash; exact .inr ⟨hNe, hHash⟩

def extractShortDiffSISWitness (pp : AjtaiParams)
    (u v : List Int) (huLen : u.length = pp.cols) (hvLen : v.length = pp.cols)
    (huShort : ShortNormBound 65535 u) (hvShort : ShortNormBound 65535 v)
    (hNe : u ≠ v) (hSyn : ajtaiCommit pp u huLen = ajtaiCommit pp v hvLen) :
    SISShortVecWitness pp.modulus 131070 pp.matrix where
  shortVec := vecSub u v
  nonZero := by rw [← normInf_eq_vecInfNorm]; exact normInf_pos_of_ne (huLen.trans hvLen.symm) hNe
  shortNorm := by rw [← normInf_eq_vecInfNorm]; unfold ShortNormBound at huShort hvShort; have := normInf_vecSub_le u v; omega
  inKernel := matVecModZero_of_ajtaiCommit_eq pp huLen hvLen hSyn

def extractAjtaiDoubleOpenSIS (pp : AjtaiParams)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    {v : Nat} {comm : AjtaiCommitment} {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : AjtaiOpeningProof}
    {tr₁ : Transcript phase₁} {tr₂ : Transcript phase₂} (hPt : c₁.point = c₂.point)
    (hAcc₁ : (ajtaiLatticeVerifyEval pp v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (ajtaiLatticeVerifyEval pp v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    { _w : SISShortVecWitness pp.modulus 131070 pp.matrix // pp.cols = 4 * (2 ^ v) } :=
  have hFacts : pp.cols = 4 * (2 ^ v) ∧ π₁.shortLimbs.length = pp.cols ∧ π₂.shortLimbs.length = pp.cols ∧
      ShortNormBound 65535 π₁.shortLimbs ∧ ShortNormBound 65535 π₂.shortLimbs ∧ π₁.shortLimbs ≠ π₂.shortLimbs ∧
      (∀ (l₁ : π₁.shortLimbs.length = pp.cols) (l₂ : π₂.shortLimbs.length = pp.cols),
        ajtaiCommit pp π₁.shortLimbs l₁ = ajtaiCommit pp π₂.shortLimbs l₂) := by
    unfold ajtaiLatticeVerifyEval at hAcc₁ hAcc₂; dsimp only at hAcc₁ hAcc₂
    simp only [Bool.and_eq_true, beq_iff_eq] at hAcc₁ hAcc₂
    obtain ⟨hCols, hAcc₁⟩ := hAcc₁; obtain ⟨_, hAcc₂⟩ := hAcc₂
    if hL₁ : π₁.shortLimbs.length = pp.cols then
      if hL₂ : π₂.shortLimbs.length = pp.cols then
        simp only [hL₁, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hAcc₁
        simp only [hL₂, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hAcc₂
        rcases hAcc₁ with ⟨⟨⟨_, hSh₁⟩, hSyn₁⟩, hRec₁⟩; rcases hAcc₂ with ⟨⟨⟨_, hSh₂⟩, hSyn₂⟩, hRec₂⟩
        refine ⟨hCols, hL₁, hL₂, hSh₁, hSh₂, ?_, fun _ _ => hSyn₁.trans hSyn₂.symm⟩
        intro hEq; rw [hEq] at hRec₁
        cases hRec : gadgetRecomposeTable π₂.shortLimbs with
        | none => rw [hRec] at hRec₁; cases hRec₁
        | some tbl => rw [hRec, beq_iff_eq] at hRec₁ hRec₂; exact hDisagree (by rw [← hRec₁, ← hRec₂, hPt])
      else simp only [hL₂, ↓reduceDIte] at hAcc₂; cases hAcc₂
    else simp only [hL₁, ↓reduceDIte] at hAcc₁; cases hAcc₁
  ⟨extractShortDiffSISWitness pp π₁.shortLimbs π₂.shortLimbs hFacts.2.1 hFacts.2.2.1 hFacts.2.2.2.1
    hFacts.2.2.2.2.1 hFacts.2.2.2.2.2.1 (hFacts.2.2.2.2.2.2 hFacts.2.1 hFacts.2.2.1), hFacts.1⟩

theorem ajtai_double_open_yields_sis_kernel (pp : AjtaiParams)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    {v : Nat} {comm : AjtaiCommitment} {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : AjtaiOpeningProof}
    {tr₁ : Transcript phase₁} {tr₂ : Transcript phase₂} (hPt : c₁.point = c₂.point)
    (hAcc₁ : (ajtaiLatticeVerifyEval pp v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (ajtaiLatticeVerifyEval pp v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    Nonempty (SISShortVecWitness pp.modulus 131070 pp.matrix) :=
  ⟨(extractAjtaiDoubleOpenSIS pp hPt hAcc₁ hAcc₂ hDisagree).1⟩

theorem ajtaiLatticePCS_complete_aux (pp : AjtaiParams) :
    ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase] (_ : Unit) (v : Nat) (tbl : List Goldilocks)
      (pt : List Goldilocks) (hPt : pt.length = v) (tr : Transcript phase),
      pp.cols = 4 * (2 ^ v) → tbl.length = 2 ^ v →
      let claim : EvalClaim Goldilocks v := ⟨pt, hPt, mleEval tbl pt⟩
      let (prf, _) := ajtaiLatticeOpenEval pp v tbl claim tr
      (ajtaiLatticeVerifyEval pp v (ajtaiLatticeCommit pp v tbl) claim prf tr).1 = true := by
  intro _ _ _ v tbl _ _ _ hCols hTblLen
  have hLimbsLen : (gadgetDecomposeTable tbl).length = pp.cols := by rw [gadgetDecomposeTable_length, hTblLen, hCols]
  dsimp only [ajtaiLatticeCommit, ajtaiLatticeOpenEval, ajtaiLatticeVerifyEval]
  simp only [hLimbsLen, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff]
  exact ⟨hCols, ⟨⟨⟨trivial, gadgetDecomposeTable_short tbl⟩, trivial⟩, by rw [gadgetRecomposeTable_decompose tbl, beq_iff_eq]⟩⟩

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

theorem ajtaiLatticePCS_bindingSound_of_sisHard (pp : AjtaiParams)
    (hNonPig : NonPigeonholeSISParams pp) (hSIS : ModuleSISHard pp 131070) :
    NonPigeonholeSISParams pp ∧ BindingSound (ajtaiLatticePCS pp) := by
  refine ⟨hNonPig, fun v _ _ _ _ _ comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂ => ?_⟩
  if hEq : c₁.expectedVal = c₂.expectedVal then exact hEq
  else exact False.elim (hSIS ⟨(extractAjtaiDoubleOpenSIS pp hPt hAcc₁ hAcc₂ hEq).1⟩)

/-! ### `Akita` (`2026/1983`) / `Twist & Shout` $O(\text{rows})$ Sparse One-Hot Ajtai Specialization -/

def unitVecInt : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, 0 => 1 :: List.replicate n 0
  | n + 1, k + 1 => 0 :: unitVecInt n k

theorem unitVecInt_length : ∀ (len col : Nat), (unitVecInt len col).length = len
  | 0, _ => rfl
  | n + 1, 0 => by simp [unitVecInt]
  | n + 1, k + 1 => by simp [unitVecInt, unitVecInt_length n k]

theorem dotInt_replicate_zero :
    ∀ (row : List Int) (n : Nat) (h : row.length = (List.replicate n (0 : Int)).length), dotInt row (List.replicate n 0) h = 0
  | [], 0, _ => rfl
  | r :: rs, n + 1, h => by simp [List.replicate_succ, dotInt, dotInt_replicate_zero rs n (Nat.succ.inj h)]

theorem dotInt_unitVecInt :
    ∀ (len col : Nat) (row : List Int) (hLen : row.length = (unitVecInt len col).length),
      col < len → dotInt row (unitVecInt len col) hLen = row.getD col 0
  | 0, _, _, _, hlt => by omega
  | n + 1, 0, r :: rs, hLen, _ => by
    have hRep : rs.length = (List.replicate n (0 : Int)).length := by simpa [unitVecInt] using hLen
    simp [unitVecInt, dotInt, dotInt_replicate_zero rs n hRep]
  | n + 1, k + 1, r :: rs, hLen, hlt => by
    have hSub : rs.length = (unitVecInt n k).length := by simpa [unitVecInt] using hLen
    simp [unitVecInt, dotInt, dotInt_unitVecInt n k rs hSub (by omega)]

theorem replicate_append_zero : ∀ (a b : Nat), List.replicate a (0 : Int) ++ List.replicate b 0 = List.replicate (a + b) 0
  | 0, _ => by simp
  | a + 1, b => by rw [Nat.succ_add]; simp [List.replicate_succ, replicate_append_zero a b]

theorem unitVecInt_prepend_four_zeros (len k : Nat) :
    ([0, 0, 0, 0] : List Int) ++ unitVecInt len k = unitVecInt (len + 4) (k + 4) := by simp [unitVecInt]

theorem gadgetDecompose_oneHot_aux :
    ∀ (m start idx : Nat),
      ((List.range m).map (fun j => if start + j = idx then Goldilocks.one else Goldilocks.zero)).flatMap gadgetDecomposeGoldilocks =
      if idx < start then List.replicate (4 * m) 0
      else if idx < start + m then unitVecInt (4 * m) (4 * (idx - start)) else List.replicate (4 * m) 0
  | 0, _, _ => by simp [unitVecInt]
  | m + 1, start, idx => by
    have hRange : List.range (m + 1) = 0 :: (List.range m).map (· + 1) := @List.range_succ_eq_map m
    rw [hRange, List.map_cons, List.map_map, List.flatMap_cons]
    have hShift : ((List.range m).map ((fun j => if start + j = idx then Goldilocks.one else Goldilocks.zero) ∘ (· + 1))) =
        ((List.range m).map (fun j => if (start + 1) + j = idx then Goldilocks.one else Goldilocks.zero)) :=
      List.map_congr_left fun j _ => by dsimp only [Function.comp]; rw [show start + (j + 1) = (start + 1) + j by omega]
    rw [hShift, gadgetDecompose_oneHot_aux m (start + 1) idx]
    if hEq : start = idx then
      subst hEq; have hOne : gadgetDecomposeGoldilocks Goldilocks.one = [1, 0, 0, 0] := rfl
      simp only [Nat.add_zero, ↓reduceIte, hOne, show start < start + 1 by omega, show ¬ start < start by omega, show start < start + (m + 1) by omega]
      rw [Nat.sub_self, Nat.mul_zero, show 4 * (m + 1) = 4 * m + 4 by omega]; simp [unitVecInt, List.replicate_succ]
    else
      have hHead : (if start + 0 = idx then Goldilocks.one else Goldilocks.zero) = Goldilocks.zero := by rw [Nat.add_zero]; simp [hEq]
      have hZero : gadgetDecomposeGoldilocks Goldilocks.zero = [0, 0, 0, 0] := rfl
      have h4 : ([0, 0, 0, 0] : List Int) = List.replicate 4 0 := rfl
      rw [hHead, hZero]
      if hLt : idx < start then
        simp only [hLt, show idx < start + 1 by omega, ↓reduceIte]; rw [h4, replicate_append_zero]; congr 1; omega
      else
        simp only [hLt, show ¬ idx < start + 1 by omega, ↓reduceIte]
        if hIn : idx < start + (m + 1) then
          simp only [hIn, show idx < start + 1 + m by omega, ↓reduceIte]
          rw [unitVecInt_prepend_four_zeros, show 4 * m + 4 = 4 * (m + 1) by omega, show 4 * (idx - (start + 1)) + 4 = 4 * (idx - start) by omega]
        else simp only [hIn, show ¬ idx < start + 1 + m by omega, ↓reduceIte]; rw [h4, replicate_append_zero]; congr 1; omega

theorem gadgetDecomposeTable_oneHot (v idx : Nat) (hIdx : idx < 2 ^ v) :
    gadgetDecomposeTable (oneHotTable Goldilocks v idx) = unitVecInt (4 * 2 ^ v) (4 * idx) := by
  unfold gadgetDecomposeTable oneHotTable; have h := gadgetDecompose_oneHot_aux (2 ^ v) 0 idx
  simp only [Nat.zero_add, show ¬ idx < 0 by omega, hIdx, ↓reduceIte, Nat.sub_zero] at h; exact h

def ajtaiCommitOneHotColumn (pp : AjtaiParams) (numVars idx : Nat) : AjtaiCommitment :=
  { numVars := numVars, syndrome := pp.matrix.map fun row => (row.getD (4 * idx) 0) % (pp.modulus : Int) }

instance ajtaiSparseOneHot (pp : AjtaiParams) : SparseOneHotCommit Goldilocks (ajtaiLatticePCS pp) where
  commitOneHot _ v idx := ajtaiCommitOneHotColumn pp v idx
  commitOneHot_eq_commit := by
    intro _ v idx hCols hIdx
    change ajtaiCommitOneHotColumn pp v idx = ajtaiLatticeCommit pp v (oneHotTable Goldilocks v idx)
    dsimp only [ajtaiLatticeCommit, ajtaiCommitOneHotColumn]
    have hDecomp := gadgetDecomposeTable_oneHot v idx hIdx
    have hUnitLen : (gadgetDecomposeTable (oneHotTable Goldilocks v idx)).length = pp.cols := by rw [hDecomp, unitVecInt_length, hCols]
    simp only [hUnitLen, ↓reduceDIte]; congr 1; unfold ajtaiCommit ajtaiCommitRaw
    have aux : ∀ (rows : List (List Int)) (hR : ∀ r ∈ rows, r.length = pp.cols),
        (rows.map fun row => (row.getD (4 * idx) 0) % (pp.modulus : Int)) =
        (mapRowsDot rows pp.cols hR (gadgetDecomposeTable (oneHotTable Goldilocks v idx)) hUnitLen).map (fun s => s % (pp.modulus : Int)) := by
      intro rows hR; induction rows with
      | nil => rfl
      | cons row rest ih =>
        simp only [List.map_cons, mapRowsDot, List.cons.injEq]; refine ⟨?_, ih (fun r hr => hR r (.tail _ hr))⟩; congr 1
        have hRowLen : row.length = (unitVecInt (4 * 2 ^ v) (4 * idx)).length := by rw [unitVecInt_length, hR row (.head _), hCols]
        have hDotEq : dotInt row (gadgetDecomposeTable (oneHotTable Goldilocks v idx)) ((hR row (.head _)).trans hUnitLen.symm) =
            dotInt row (unitVecInt (4 * 2 ^ v) (4 * idx)) hRowLen := by rw [dotInt_eq_dotProd, dotInt_eq_dotProd, hDecomp]
        rw [hDotEq, dotInt_unitVecInt (4 * 2 ^ v) (4 * idx) row hRowLen (by omega)]
    exact aux pp.matrix pp.matrix_cols

/-! ## 5. Cross-Assumption `DualPCS P₁ P₂`, Constructive `dualExtract` (`0 Classical`) & Survival Theorem -/

def dualDomainKind : DomainKind → DomainKind → DomainKind
  | .primeField, .primeField => .primeField
  | _, _ => .binaryAdditive

def dualProximityRegime (d₁ d₂ : DomainKind) (r₁ r₂ : ProximityRegime) : ProximityRegime :=
  match dualDomainKind d₁ d₂ with
  | .binaryAdditive => .uniqueDecodingRadius
  | .primeField =>
    match r₁, r₂ with
    | .uniqueDecodingRadius, _ | _, .uniqueDecodingRadius => .uniqueDecodingRadius
    | .johnsonBound, _ | _, .johnsonBound => .johnsonBound
    | .capacityBound, .capacityBound => .capacityBound

theorem dualValidProximityConfig (d₁ d₂ : DomainKind) (r₁ r₂ : ProximityRegime) :
    ValidProximityConfig (dualDomainKind d₁ d₂) (dualProximityRegime d₁ d₂ r₁ r₂) := by
  cases d₁ <;> cases d₂ <;> simp only [dualDomainKind, dualProximityRegime]
  · cases r₁ <;> cases r₂ <;> simp only; all_goals first | exact .primeUDR | exact .primeJohnson | exact .primeCapacity
  · exact .binaryUDR
  · exact .binaryUDR
  · exact .binaryUDR

def dualTrack1Label : ByteArray := Native.bytesOfList [0x44, 0x55, 0x41, 0x4c, 0x2e, 0x54, 0x52, 0x41, 0x43, 0x4b, 0x31]
def dualTrack2Label : ByteArray := Native.bytesOfList [0x44, 0x55, 0x41, 0x4c, 0x2e, 0x54, 0x52, 0x41, 0x43, 0x4b, 0x32]
def dualJoinLabel : ByteArray := Native.bytesOfList [0x44, 0x55, 0x41, 0x4c, 0x2e, 0x4a, 0x4f, 0x49, 0x4e]
def dualVerdictJoin (ok₁ ok₂ : Bool) : Bool := ok₁ && ok₂

def dualOpenEval {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (pp : P₁.Params × P₂.Params) (v : Nat) (tbl : List R) (claim : EvalClaim R v) (tr : Transcript phase) :
    (P₁.OpeningProof × P₂.OpeningProof) × Transcript phase :=
  let (π₁, tr₁') := P₁.openEval pp.1 v tbl claim (absorbMsg dualTrack1Label ByteArray.empty tr)
  let (π₂, tr₂') := P₂.openEval pp.2 v tbl claim (absorbMsg dualTrack2Label ByteArray.empty tr)
  ((π₁, π₂), absorbMsg dualJoinLabel (encodeFrame tr₁'.state tr₂'.state ByteArray.empty) tr)

def dualVerifyEval {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (pp : P₁.Params × P₂.Params) (v : Nat) (comm : P₁.Commitment × P₂.Commitment)
    (claim : EvalClaim R v) (prf : P₁.OpeningProof × P₂.OpeningProof) (tr : Transcript phase) : Bool × Transcript phase :=
  let (ok₁, tr₁') := P₁.verifyEval pp.1 v comm.1 claim prf.1 (absorbMsg dualTrack1Label ByteArray.empty tr)
  let (ok₂, tr₂') := P₂.verifyEval pp.2 v comm.2 claim prf.2 (absorbMsg dualTrack2Label ByteArray.empty tr)
  (dualVerdictJoin ok₁ ok₂, absorbMsg dualJoinLabel (encodeFrame tr₁'.state tr₂'.state ByteArray.empty) tr)

theorem dualPCS_complete_aux {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R) :
    ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase]
      (pp : P₁.Params × P₂.Params) (v : Nat) (tbl : List R) (pt : List R) (hPt : pt.length = v) (tr : Transcript phase),
      (P₁.ValidArity pp.1 v ∧ P₂.ValidArity pp.2 v) → tbl.length = 2 ^ v →
      let claim : EvalClaim R v := ⟨pt, hPt, mleEval tbl pt⟩
      let (prf, _) := dualOpenEval P₁ P₂ pp v tbl claim tr
      (dualVerifyEval P₁ P₂ pp v (P₁.commit pp.1 v tbl, P₂.commit pp.2 v tbl) claim prf tr).1 = true := by
  intro _ _ pp v tbl pt hPt tr hValid hTblLen
  dsimp only [dualOpenEval, dualVerifyEval, dualVerdictJoin]; rw [Bool.and_eq_true]
  exact ⟨P₁.completeness pp.1 v tbl pt hPt (absorbMsg dualTrack1Label ByteArray.empty tr) hValid.1 hTblLen,
         P₂.completeness pp.2 v tbl pt hPt (absorbMsg dualTrack2Label ByteArray.empty tr) hValid.2 hTblLen⟩

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

theorem dualPCS_completeness {R : Type} [CommRingOps R] {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (P₁ P₂ : MultilinearPCS R) (pp : P₁.Params × P₂.Params) (v : Nat) (tbl : List R)
    (pt : List R) (hPt : pt.length = v) (tr : Transcript phase)
    (hValid : (DualPCS P₁ P₂).ValidArity pp v) (hTblLen : tbl.length = 2 ^ v) :
    let claim : EvalClaim R v := ⟨pt, hPt, mleEval tbl pt⟩
    let (prf, _) := (DualPCS P₁ P₂).openEval pp v tbl claim tr
    ((DualPCS P₁ P₂).verifyEval pp v ((DualPCS P₁ P₂).commit pp v tbl) claim prf tr).1 = true :=
  (DualPCS P₁ P₂).completeness pp v tbl pt hPt tr hValid hTblLen

theorem dualPCS_bindingSoundAt_of_either {R : Type} [CommRingOps R]
    (v : Nat) (P₁ P₂ : MultilinearPCS R) (hEither : BindingSoundAt v P₁ ∨ BindingSoundAt v P₂) :
    BindingSoundAt v (DualPCS P₁ P₂) := by
  intro _ _ _ _ pp comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  simp only [DualPCS, dualVerifyEval, dualVerdictJoin, Bool.and_eq_true] at hAcc₁ hAcc₂
  rcases hEither with hSound₁ | hSound₂
  · exact hSound₁ pp.1 comm.1 c₁ c₂ π₁.1 π₂.1 (absorbMsg dualTrack1Label ByteArray.empty tr₁)
      (absorbMsg dualTrack1Label ByteArray.empty tr₂) hPt hAcc₁.1 hAcc₂.1
  · exact hSound₂ pp.2 comm.2 c₁ c₂ π₁.2 π₂.2 (absorbMsg dualTrack2Label ByteArray.empty tr₁)
      (absorbMsg dualTrack2Label ByteArray.empty tr₂) hPt hAcc₁.2 hAcc₂.2

theorem dualPCS_sound_of_either {R : Type} [CommRingOps R] (P₁ P₂ : MultilinearPCS R)
    (hEither : BindingSound P₁ ∨ BindingSound P₂) : BindingSound (DualPCS P₁ P₂) :=
  fun v => dualPCS_bindingSoundAt_of_either v P₁ P₂ (hEither.elim (fun h₁ => .inl (h₁ v)) (fun h₂ => .inr (h₂ v)))

@[expose, instance_reducible] def canopyAjtaiDualPCS (H : Hash32) (pp : AjtaiParams) : MultilinearPCS Goldilocks :=
  DualPCS (canopyMerklePCS H) (ajtaiLatticePCS pp)

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

def dualExtractBoth {H : Hash32} {pp : AjtaiParams} {v : Nat} (f : DualDoubleOpenForgery H pp v) :
    HashCollisionWitness H.eval (merkleMaxPreimageBytes v) × SISShortVecWitness pp.modulus 131070 pp.matrix :=
  have hBoth₁ : (canopyVerifyEval H v f.comm.1 f.c₁ f.π₁.1 (absorbMsg dualTrack1Label ByteArray.empty f.tr₁)).1 = true ∧
      (ajtaiLatticeVerifyEval pp v f.comm.2 f.c₁ f.π₁.2 (absorbMsg dualTrack2Label ByteArray.empty f.tr₁)).1 = true := by
    simpa [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS, dualVerdictJoin, Bool.and_eq_true] using f.acc₁
  have hBoth₂ : (canopyVerifyEval H v f.comm.1 f.c₂ f.π₂.1 (absorbMsg dualTrack1Label ByteArray.empty f.tr₂)).1 = true ∧
      (ajtaiLatticeVerifyEval pp v f.comm.2 f.c₂ f.π₂.2 (absorbMsg dualTrack2Label ByteArray.empty f.tr₂)).1 = true := by
    simpa [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS, dualVerdictJoin, Bool.and_eq_true] using f.acc₂
  (extractCanopyDoubleOpenCollision H f.samePoint hBoth₁.1 hBoth₂.1 f.disagree,
   (extractAjtaiDoubleOpenSIS pp f.samePoint hBoth₁.2 hBoth₂.2 f.disagree).1)

inductive DualForgery (H : Hash32) (pp : AjtaiParams) (v : Nat) : Type where
  | sameTableMerkleMismatch (tbl : List Goldilocks) (hTbl : tbl.length = 2 ^ v) (idx : Nat) (hIdx : idx < 2 ^ v)
      (val : Goldilocks) (path : List Digest32) (hNe : val ≠ tbl[idx]'(by omega))
      (hVer : verifyMerklePath H (2 ^ v) idx val path (canopyCommit H v tbl).root = true)
  | crossTableMismatch (tblMerkle tblAjtai : List Goldilocks) (hLenM : tblMerkle.length = 2 ^ v)
      (hLenA : tblAjtai.length = 2 ^ v) (hCols : pp.cols = 4 * (2 ^ v)) (claim : EvalClaim Goldilocks v)
      (π : CanopyOpeningProof × AjtaiOpeningProof) (tr : Transcript .relationBound)
      (hAcc : ((canopyAjtaiDualPCS H pp).verifyEval ((), ()) v (canopyCommit H v tblMerkle, ajtaiLatticeCommit pp v tblAjtai) claim π tr).1 = true)
      (hDisagree : claim.expectedVal ≠ mleEval tblMerkle claim.point ∨ claim.expectedVal ≠ mleEval tblAjtai claim.point)
  | doubleOpening (f : DualDoubleOpenForgery H pp v)

def dualExtract {H : Hash32} {pp : AjtaiParams} {v : Nat} (forgery : DualForgery H pp v) :
    PSum (HashCollisionWitness H.eval (merkleMaxPreimageBytes v)) (SISShortVecWitness pp.modulus 131070 pp.matrix) :=
  match forgery with
  | .sameTableMerkleMismatch tbl hTbl idx hIdx val path hNe hVer =>
    .inl (extractMerklePathCollision H hIdx path (openMerkle H tbl idx)
            (canopyCommit H v tbl).root hNe hVer (verifyMerklePath_openMerkle H v tbl hTbl idx hIdx))
  | .crossTableMismatch tblM tblA hLenM hLenA hCols claim π tr hAcc hDisagree =>
    have hBoth : (canopyVerifyEval H v (canopyCommit H v tblM) claim π.1 (absorbMsg dualTrack1Label ByteArray.empty tr)).1 = true ∧
        (ajtaiLatticeVerifyEval pp v (ajtaiLatticeCommit pp v tblA) claim π.2 (absorbMsg dualTrack2Label ByteArray.empty tr)).1 = true := by
      simpa [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS, dualVerdictJoin, Bool.and_eq_true] using hAcc
    if hEqM : claim.expectedVal = mleEval tblM claim.point then
      have hNeA : claim.expectedVal ≠ mleEval tblA claim.point := hDisagree.elim (fun hbad => False.elim (hbad hEqM)) id
      let honestLimbs := gadgetDecomposeTable tblA
      have hHonestLen : honestLimbs.length = pp.cols := by dsimp [honestLimbs]; rw [gadgetDecomposeTable_length, hLenA, hCols]
      have hAjtaiFacts : π.2.shortLimbs.length = pp.cols ∧ ShortNormBound 65535 π.2.shortLimbs ∧ π.2.shortLimbs ≠ honestLimbs ∧
          (∀ l₁ : π.2.shortLimbs.length = pp.cols, ajtaiCommit pp π.2.shortLimbs l₁ = ajtaiCommit pp honestLimbs hHonestLen) := by
        have hHonestLen' : (gadgetDecomposeTable tblA).length = pp.cols := hHonestLen
        have hAccA := hBoth.2; unfold ajtaiLatticeVerifyEval ajtaiLatticeCommit at hAccA; dsimp only at hAccA
        simp only [Bool.and_eq_true, beq_iff_eq] at hAccA; obtain ⟨_, hAccA⟩ := hAccA
        if hPrfLen : π.2.shortLimbs.length = pp.cols then
          simp only [hPrfLen, hHonestLen', ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hAccA
          rcases hAccA with ⟨⟨⟨_, hSh⟩, hSyn⟩, hRec⟩; refine ⟨hPrfLen, hSh, ?_, fun _ => hSyn⟩
          intro hEqLimbs; rw [hEqLimbs, gadgetRecomposeTable_decompose tblA, beq_iff_eq] at hRec; exact hNeA hRec.symm
        else simp only [hPrfLen, ↓reduceDIte] at hAccA; cases hAccA
      .inr (extractShortDiffSISWitness pp π.2.shortLimbs honestLimbs hAjtaiFacts.1 hHonestLen
              hAjtaiFacts.2.1 (gadgetDecomposeTable_short tblA) hAjtaiFacts.2.2.1 (hAjtaiFacts.2.2.2 hAjtaiFacts.1))
    else
      have hTblMNe : π.1.entries.map Prod.fst ≠ tblM := by
        have hAccM := hBoth.1; simp only [canopyVerifyEval, Bool.and_eq_true, beq_iff_eq] at hAccM
        intro hEqEntries; rw [hEqEntries] at hAccM; exact hEqM hAccM.2.symm
      .inl (extractCanopyOpenMerkleCollision H tblM hLenM π.1 (absorbMsg dualTrack1Label ByteArray.empty tr) hBoth.1 hTblMNe)
  | .doubleOpening f => .inl (dualExtractBoth f).1

def extractDualCommitCollisionBoth (H : Hash32) (pp : AjtaiParams) {v : Nat}
    (t₁ t₂ : List Goldilocks) (ht₁ : t₁.length = 2 ^ v) (ht₂ : t₂.length = 2 ^ v)
    (hCols : pp.cols = 4 * (2 ^ v)) (hNe : t₁ ≠ t₂)
    (hCommEq : (canopyAjtaiDualPCS H pp).commit ((), ()) v t₁ = (canopyAjtaiDualPCS H pp).commit ((), ()) v t₂) :
    HashCollisionWitness H.eval (merkleMaxPreimageBytes v) × SISShortVecWitness pp.modulus 131070 pp.matrix :=
  let diff := findDiffIndex t₁ t₂ (ht₁.trans ht₂.symm) hNe; let idx := diff.1
  have hIdxPow : idx < 2 ^ v := by obtain ⟨hx, _, _⟩ := diff.2; simpa [ht₁] using hx
  have hIn₁ : idx < t₁.length := by rw [ht₁]; exact hIdxPow
  have hIn₂ : idx < t₂.length := by rw [ht₂]; exact hIdxPow
  have hNeAt : t₁[idx]'hIn₁ ≠ t₂[idx]'hIn₂ := diff.2.2.2
  have hPairEq : canopyCommit H v t₁ = canopyCommit H v t₂ ∧ ajtaiLatticeCommit pp v t₁ = ajtaiLatticeCommit pp v t₂ :=
    Prod.mk.inj hCommEq
  have hVer₁ := verifyMerklePath_openMerkle H v t₁ ht₁ idx hIdxPow
  have hVer₂ : verifyMerklePath H (2 ^ v) idx (t₂[idx]'hIn₂) (openMerkle H t₂ idx) (canopyCommit H v t₁).root = true := by
    rw [congrArg CanopyCommitment.root hPairEq.1]; exact verifyMerklePath_openMerkle H v t₂ ht₂ idx hIdxPow
  let hashWit := extractMerklePathCollision H hIdxPow (openMerkle H t₁ idx) (openMerkle H t₂ idx) (canopyCommit H v t₁).root hNeAt hVer₁ hVer₂
  let limbs₁ := gadgetDecomposeTable t₁; let limbs₂ := gadgetDecomposeTable t₂
  have hL₁ : limbs₁.length = pp.cols := by dsimp [limbs₁]; rw [gadgetDecomposeTable_length, ht₁, hCols]
  have hL₂ : limbs₂.length = pp.cols := by dsimp [limbs₂]; rw [gadgetDecomposeTable_length, ht₂, hCols]
  have hSynEq : ajtaiCommit pp limbs₁ hL₁ = ajtaiCommit pp limbs₂ hL₂ := by
    simpa [ajtaiLatticeCommit, limbs₁, limbs₂, hL₁, hL₂] using congrArg AjtaiCommitment.syndrome hPairEq.2
  (hashWit, extractShortDiffSISWitness pp limbs₁ limbs₂ hL₁ hL₂ (gadgetDecomposeTable_short t₁)
    (gadgetDecomposeTable_short t₂) (fun h => hNe (gadgetDecomposeTable_injective h)) hSynEq)

class CanopyNonPigeonholeOrLazyRORefuter (H : Hash32) (R : Nat → Prop) : Prop where
  refute_double_open : ∀ (v : Nat), R v → HashCollisionWitness H.eval (merkleMaxPreimageBytes v) → False

instance (H : Hash32) : CanopyNonPigeonholeOrLazyRORefuter H (fun v => v = 0 ∧ ¬ BoundedCollision H.eval 10) where
  refute_double_open
    | 0, ⟨_, hNoCol⟩, w => hNoCol ⟨w⟩
    | _ + 1, ⟨hv, _⟩, _ => Nat.noConfusion hv

class HashBoundAtLeastMerkle (B : Nat → Nat) : Type where
  le_bound : ∀ v, merkleMaxPreimageBytes v ≤ B v

instance : HashBoundAtLeastMerkle merkleMaxPreimageBytes := ⟨fun _ => Nat.le_refl _⟩

instance (H : Hash32) (B : Nat → Nat) [hB : HashBoundAtLeastMerkle B] :
    CanopyNonPigeonholeOrLazyRORefuter H (fun v => ¬ BoundedCollision H.eval (B v)) where
  refute_double_open v h w :=
    h ⟨⟨w.msgA, w.msgB, Nat.le_trans w.lenA (hB.le_bound v), Nat.le_trans w.lenB (hB.le_bound v), w.distinct, w.sameDigest⟩⟩

theorem canopyAjtaiDualPCS_bindingSoundAt_of_hash_or_sis (H : Hash32) (pp : AjtaiParams)
    (hNonPig : NonPigeonholeSISParams pp)
    (hOr : ¬ BoundedCollision H.eval 10 ∨ ModuleSISHard pp 131070) :
    NonPigeonholeSISParams pp ∧ BindingSoundAt 0 (canopyAjtaiDualPCS H pp) := by
  refine ⟨hNonPig, dualPCS_bindingSoundAt_of_either 0 _ _ ?_⟩
  exact hOr.elim (fun h => .inl (canopyMerklePCS_bindingSoundAt_of_boundedCollisionFree H h))
    (fun h => .inr ((ajtaiLatticePCS_bindingSound_of_sisHard pp hNonPig h).2 0))

theorem canopyAjtaiDualPCS_bind_of_roLog_or_sis (H : Hash32) (pp : AjtaiParams) (v : Nat)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    (log : GameSoundness.ROLog (List UInt8) Digest32) (comm : CanopyCommitment × AjtaiCommitment)
    (c₁ c₂ : EvalClaim Goldilocks v) (π₁ π₂ : CanopyOpeningProof × AjtaiOpeningProof)
    (tr₁ : Transcript phase₁) (tr₂ : Transcript phase₂) (hPt : c₁.point = c₂.point)
    (hAcc₁ : ((canopyAjtaiDualPCS H pp).verifyEval ((), ()) v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : ((canopyAjtaiDualPCS H pp).verifyEval ((), ()) v comm c₂ π₂ tr₂).1 = true)
    (hOr : (GameSoundness.hasLogCollision log = false ∧
            (∀ m ∈ canopyOpeningFrames H v π₁.1, (m, evalDigest32 H m) ∈ log) ∧
            (∀ m ∈ canopyOpeningFrames H v π₂.1, (m, evalDigest32 H m) ∈ log)) ∨ ModuleSISHard pp 131070) :
    c₁.expectedVal = c₂.expectedVal := by
  simp only [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS, dualVerdictJoin, Bool.and_eq_true] at hAcc₁ hAcc₂
  rcases hOr with ⟨hNoCol, hLog₁, hLog₂⟩ | hSIS
  · exact canopyMerklePCS_bind_of_roLog H v log hNoCol comm.1 c₁ c₂ π₁.1 π₂.1
      (absorbMsg dualTrack1Label ByteArray.empty tr₁) (absorbMsg dualTrack1Label ByteArray.empty tr₂) hPt hAcc₁.1 hAcc₂.1 hLog₁ hLog₂
  · if hEq : c₁.expectedVal = c₂.expectedVal then exact hEq
    else exact False.elim (hSIS ⟨(extractAjtaiDoubleOpenSIS pp hPt hAcc₁.2 hAcc₂.2 hEq).1⟩)

theorem canopyAjtaiDualPCS_sound_of_hash_or_sis (H : Hash32) (pp : AjtaiParams)
    {R : Nat → Prop} [CanopyNonPigeonholeOrLazyRORefuter H R]
    (hOr : (∀ v : Nat, pp.cols = 4 * (2 ^ v) → R v) ∨ ModuleSISHard pp 131070) :
    BindingSound (canopyAjtaiDualPCS H pp) := by
  intro v _ _ _ _ _ comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  if hEq : c₁.expectedVal = c₂.expectedVal then exact hEq
  else
    simp only [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS, ajtaiLatticePCS, dualVerdictJoin, Bool.and_eq_true] at hAcc₁ hAcc₂
    let sisOut := extractAjtaiDoubleOpenSIS pp hPt hAcc₁.2 hAcc₂.2 hEq
    rcases hOr with hRef | hSIS
    · exact False.elim (CanopyNonPigeonholeOrLazyRORefuter.refute_double_open v (hRef v sisOut.2) (extractCanopyDoubleOpenCollision H hPt hAcc₁.1 hAcc₂.1 hEq))
    · exact False.elim (hSIS ⟨sisOut.1⟩)

example : BindingSound (canopyAjtaiDualPCS toyInjectiveHash32 (inhabitedAjtaiParams 0)) :=
  canopyAjtaiDualPCS_sound_of_hash_or_sis toyInjectiveHash32 (inhabitedAjtaiParams 0)
    (R := fun v => v = 0 ∧ ¬ BoundedCollision toyInjectiveHash32.eval 10)
    (.inl fun v hv => by
      have hv0 : v = 0 := by
        change 4 = 4 * (2 ^ v) at hv; cases v with | zero => rfl | succ k => rw [Nat.pow_succ] at hv; have := Nat.two_pow_pos k; omega
      exact ⟨hv0, toyInjectiveHash32_no_boundedCollision (by decide)⟩)

theorem canopyAjtaiDualPCS_inhabited_sis_branch (H : Hash32) (v : Nat) :
    BindingSound (canopyAjtaiDualPCS H (inhabitedAjtaiParams v)) :=
  canopyAjtaiDualPCS_sound_of_hash_or_sis H (inhabitedAjtaiParams v)
    (R := fun u => u = 0 ∧ ¬ BoundedCollision H.eval 10) (.inr (inhabitedAjtaiParams_sisHard v).2.2)

/-! ## 6. Instance-Bound `verifyDualSumcheckPIOP` (Closing Statement/Commitment Grinding `F3`) -/

def bindDualSumcheckInstance
    {Commit₁ Commit₂ R : Type} [TranscriptEncode Commit₁] [TranscriptEncode Commit₂] [TranscriptEncode R]
    (comm : Commit₁ × Commit₂) (numVars : Nat) (claimedSum : R) (tr : Transcript .relationBound) :
    BoundTranscript (comm, (numVars, claimedSum)) :=
  bindInstance (comm, (numVars, claimedSum)) tr

def dualSumcheckInstanceFrame
    {Commit₁ Commit₂ R : Type} [TranscriptEncode Commit₁] [TranscriptEncode Commit₂] [TranscriptEncode R]
    (comm : Commit₁ × Commit₂) (numVars : Nat) (claimedSum : R) (tr : Transcript .relationBound) : List UInt8 :=
  instancePreimageList tr.state tr.stepCount (TranscriptEncode.encodeTranscriptBytes (comm, (numVars, claimedSum)))

theorem bindDualSumcheckInstance_binds
    {Commit₁ Commit₂ R : Type} [LawfulTranscriptEncode Commit₁] [LawfulTranscriptEncode Commit₂] [LawfulTranscriptEncode R]
    {c₁ c₂ : Commit₁ × Commit₂} {v₁ v₂ : Nat} {s₁ s₂ : R} {tr₁ tr₂ : Transcript .relationBound}
    (hState : (bindDualSumcheckInstance c₁ v₁ s₁ tr₁).transcript.state =
              (bindDualSumcheckInstance c₂ v₂ s₂ tr₂).transcript.state) :
    (tr₁ = tr₂ ∧ c₁ = c₂ ∧ v₁ = v₂ ∧ s₁ = s₂) ∨
    (dualSumcheckInstanceFrame c₁ v₁ s₁ tr₁ ≠ dualSumcheckInstanceFrame c₂ v₂ s₂ tr₂ ∧
     cshake256Bytes fsInstanceCustomization (dualSumcheckInstanceFrame c₁ v₁ s₁ tr₁) =
       cshake256Bytes fsInstanceCustomization (dualSumcheckInstanceFrame c₂ v₂ s₂ tr₂)) := by
  if hf : dualSumcheckInstanceFrame c₁ v₁ s₁ tr₁ = dualSumcheckInstanceFrame c₂ v₂ s₂ tr₂ then
    obtain ⟨hs, hc, hi⟩ := instancePreimageList_injective hf
    have htr : tr₁ = tr₂ := by cases tr₁; cases tr₂; simp only at hs hc; subst hs hc; rfl
    have hinst := LawfulTranscriptEncode.encodeTranscriptBytes_injective hi
    simp only [Prod.mk.injEq] at hinst; exact .inl ⟨htr, hinst.1, hinst.2.1, hinst.2.2⟩
  else
    refine .inr ⟨hf, ?_⟩; dsimp only [bindDualSumcheckInstance] at hState
    rw [bindInstance_state_eq, bindInstance_state_eq] at hState
    simpa only [cshake32ByteArray, Native.bytesOfList_toList, dualSumcheckInstanceFrame] using congrArg (fun b => b.data.toList) hState

def verifyDualSumcheckPIOP
    {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] [TranscriptEncode R]
    (P₁ P₂ : MultilinearPCS R) [TranscriptEncode P₁.Commitment] [TranscriptEncode P₂.Commitment]
    (pp : P₁.Params × P₂.Params) (maxDeg numVars : Nat) (comm : P₁.Commitment × P₂.Commitment)
    (claimedSum : R) (rounds : List (RoundPoly R)) (openingPrf : P₁.OpeningProof × P₂.OpeningProof)
    (tr : Transcript .relationBound) : Bool :=
  let btr := bindDualSumcheckInstance comm numVars claimedSum tr
  match verifyBoundSumcheck (Commit := P₁.Commitment × P₂.Commitment) (R := R) maxDeg btr rounds with
  | none => false
  | some (boundComm, claim, trAfterSumcheck) =>
    ((DualPCS (R := R) P₁ P₂).verifyEval pp btr.inst.2.1 boundComm claim openingPrf trAfterSumcheck).1

theorem verifyDualSumcheckPIOP_completeness
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R] [TranscriptEncode R]
    (P₁ P₂ : MultilinearPCS R) [TranscriptEncode P₁.Commitment] [TranscriptEncode P₂.Commitment]
    (pp : P₁.Params × P₂.Params) {maxDeg : Nat} (hDeg : 1 ≤ maxDeg) (v : Nat) (tbl : List R)
    (tr : Transcript .relationBound) (hValid : (DualPCS P₁ P₂).ValidArity pp v) (hTblLen : tbl.length = 2 ^ v) :
    let comm : P₁.Commitment × P₂.Commitment := (DualPCS (R := R) P₁ P₂).commit pp v tbl
    let (rounds, claim, trAfter) := honestBoundSumcheckProver (R := R) comm v tbl tr
    let (prf, _) := (DualPCS (R := R) P₁ P₂).openEval pp v tbl claim trAfter
    verifyDualSumcheckPIOP (R := R) P₁ P₂ pp maxDeg v comm (hypercubeSum v tbl) rounds prf tr = true := by
  let comm : P₁.Commitment × P₂.Commitment := (P₁.commit pp.1 v tbl, P₂.commit pp.2 v tbl)
  obtain ⟨hVerBound, hVal⟩ := verifyBoundSumcheck_completeness (Commit := P₁.Commitment × P₂.Commitment) (R := R) hDeg comm v tbl tr
  let sc := honestSumcheckProver v tbl (bindInstance (comm, (v, hypercubeSum v tbl)) tr).transcript
  have hCompl := (DualPCS P₁ P₂).completeness pp v tbl sc.2.1.point sc.2.1.point_len sc.2.2 hValid hTblLen
  dsimp only [verifyDualSumcheckPIOP, bindDualSumcheckInstance, BoundTranscript.inst, honestBoundSumcheckProver, DualPCS] at hVerBound hVal hCompl ⊢
  dsimp only [comm, sc] at hVerBound hVal hCompl; rw [hVerBound]; dsimp only
  have hClaimMle : sc.2.1 = ⟨sc.2.1.point, sc.2.1.point_len, mleEval tbl sc.2.1.point⟩ := by
    cases hcl : sc.2.1 with
    | mk pt hPt expVal =>
      have hVal' : expVal = mleEval tbl pt := by simpa [sc, comm, hcl] using hVal
      subst hVal'; rfl
  dsimp only [sc, comm] at hClaimMle; rw [hClaimMle]; exact hCompl

/-! ## 7. Compressing Masked Ajtai Opening (`4 * rows < cols`), `MSISGame` Binding & Joint-Transcript Statistical ZK -/

/-- **Compressing Ajtai Regime (`CompressingSISParams`)**: `4 * rows < cols` (`inhabitedAjtaiParams` used `cols = 4 * rows`). -/
def CompressingSISParams (P : GameSoundness.MSISParams) : Prop := 4 * P.rows < P.cols

/-- Concrete genuinely compressing (`rows = 2, cols = 12, beta = 131070 < q = 262147`) uniform-CRS `MSISParams`. -/
def compressingMSISParams : GameSoundness.MSISParams := ⟨2, 12, 262147, 131070, by decide, by decide, by decide, by decide⟩

theorem compressingMSISParams_is_compressing (extraCols : Nat) :
    CompressingSISParams { compressingMSISParams with cols := 12 + extraCols, cols_pos := by omega } := by
  unfold CompressingSISParams compressingMSISParams; dsimp; omega

/-- Unkeyed `Unbroken` fails on compressing `compressingMSISParams` (`262147^2 < 17^12`), whereas CRS `msisAdvantage` is non-vacuous. -/
theorem compressingMSISParams_unbroken_false (A : List (List Int))
    (hRows : A.length = 2) (hCols : ∀ row ∈ A, row.length = 12) :
    GameSoundness.UnbrokenMSIS 12 262147 16 A → False :=
  GameSoundness.unbroken_sis_false_when_compressing 2 12 262147 16 (by decide) A hRows hCols (by decide)

/-- Cleartext `ajtaiLatticeOpenEval` exposes `gadgetDecomposeTable tbl`, so `gadgetRecomposeTable` recovers `tbl`. -/
theorem cleartextAjtaiOpen_recovers_table (pp : AjtaiParams)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (v : Nat) (tbl : List Goldilocks) (claim : EvalClaim Goldilocks v) (tr : Transcript phase) :
    gadgetRecomposeTable (ajtaiLatticeOpenEval pp v tbl claim tr).1.shortLimbs = some tbl :=
  gadgetRecomposeTable_decompose tbl

/-- Pairing a hiding commitment with unmasked `AjtaiOpeningProof` forces statistical ZK error `≥ 1/2`. -/
theorem cleartextAjtaiOpen_breaks_dual_zk {Stmt V₁ : Type} [DecidableEq V₁]
    (Rel : Stmt → List Goldilocks → Prop) (real₁ : Stmt → List Goldilocks → GameSoundness.FinDist V₁)
    (Sim : GameSoundness.ZKSimulator Stmt Unit (V₁ × List Int)) (ε : GameSoundness.RatProb)
    (hDual : GameSoundness.StatisticalZK
      ⟨Rel, fun _ _ => (), fun x tbl => GameSoundness.FinDist.prod (real₁ x tbl)
        (GameSoundness.FinDist.pure (gadgetDecomposeTable tbl))⟩ Sim ε)
    {x : Stmt} {t₀ t₁ : List Goldilocks} (hR₀ : Rel x t₀) (hR₁ : Rel x t₁) (hDiff : t₀ ≠ t₁) :
    GameSoundness.RatProb.le ⟨1, 2, by decide⟩ ε :=
  GameSoundness.cleartext_opening_destroys_dual_zk Rel real₁ gadgetDecomposeTable Sim ε hDual
    hR₀ hR₁ (fun hEq => hDiff (gadgetDecomposeTable_injective hEq))

/-- Lyubashevsky / Schnorr masked response `z = c · w + y` over integer lattice vectors. -/
def maskedResponse (c : Int) (w y : List Int) : List Int := GameSoundness.vecLinComb c 1 w y

/-- Executable verifier for a masked Ajtai opening `(t, z)` against `(A, cm, c)` with smudging bound `bZ`. -/
def verifyMaskedAjtaiOpening (q cols bZ : Nat) (A : List (List Int)) (cm t : List Int) (c : Int) (z : List Int) : Bool :=
  (z.length == cols) && (cm.length == A.length) && (t.length == A.length) &&
  z.all (fun x => decide (x.natAbs ≤ bZ)) &&
  (GameSoundness.ajtaiSyndrome q A z == List.zipWith (fun ti cmi => (ti + c * cmi) % (q : Int)) t cm)

theorem verifyMaskedAjtaiOpening_inhabited (bZ : Nat) (hb : 4 ≤ bZ) :
    verifyMaskedAjtaiOpening 65537 4 bZ [[1, 2, 3, 4]] [10] [20] 1 [4, 2, 2, 4] = true := by
  unfold verifyMaskedAjtaiOpening GameSoundness.ajtaiSyndrome; simp [hb, show 2 ≤ bZ by omega]; decide

private theorem masked_syndrome_row_eq (c a b q : Int) : (c * a + 1 * b) % q = (b % q + c * (a % q)) % q := by
  rw [Int.one_mul, Int.add_comm (c * a) b, Int.add_emod b (c * a) q,
      Int.add_emod (b % q) (c * (a % q)) q, Int.emod_emod, Int.mul_emod c a q, Int.mul_emod c (a % q) q, Int.emod_emod]

/-- Honest completeness of `verifyMaskedAjtaiOpening` whenever `‖w‖_∞ ≤ bW`, `‖y‖_∞ ≤ bMask`, and `|c| · bW + bMask ≤ bZ`. -/
theorem verifyMaskedAjtaiOpening_complete (q cols bW bMask bZ : Nat)
    (A : List (List Int)) (c : Int) (w y : List Int) (hwLen : w.length = cols) (hyLen : y.length = cols)
    (hwNorm : ∀ x ∈ w, x.natAbs ≤ bW) (hyNorm : ∀ u ∈ y, u.natAbs ≤ bMask) (hSlack : c.natAbs * bW + bMask ≤ bZ) :
    c.natAbs * bW + bMask ≤ bZ ∧
    verifyMaskedAjtaiOpening q cols bZ A (GameSoundness.ajtaiSyndrome q A w)
      (GameSoundness.ajtaiSyndrome q A y) c (maskedResponse c w y) = true := by
  refine ⟨hSlack, ?_⟩; unfold verifyMaskedAjtaiOpening maskedResponse
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  have hzLen : (GameSoundness.vecLinComb c 1 w y).length = cols := by
    unfold GameSoundness.vecLinComb; rw [List.length_zipWith, hwLen, hyLen, Nat.min_self]
  refine ⟨⟨⟨⟨hzLen, by simp [GameSoundness.ajtaiSyndrome]⟩, by simp [GameSoundness.ajtaiSyndrome]⟩, ?_⟩, ?_⟩
  · have aux : ∀ (ws ys : List Int), (∀ x ∈ ws, x.natAbs ≤ bW) → (∀ u ∈ ys, u.natAbs ≤ bMask) →
        ∀ z ∈ GameSoundness.vecLinComb c 1 ws ys, z.natAbs ≤ bZ := by
      intro ws; induction ws with
      | nil => intro _ _ _ _ hz; simp [GameSoundness.vecLinComb] at hz
      | cons x ws ih =>
        intro ys hx hu z hz; cases ys with
        | nil => simp [GameSoundness.vecLinComb] at hz
        | cons u ys =>
          dsimp only [GameSoundness.vecLinComb, List.zipWith] at hz
          rcases List.mem_cons.1 hz with rfl | hTl
          · have h1 := Int.natAbs_add_le (c * x) (1 * u); rw [Int.natAbs_mul, Int.one_mul] at h1
            have h2 := Nat.mul_le_mul_left c.natAbs (hx x List.mem_cons_self)
            have h3 := hu u List.mem_cons_self; omega
          · exact ih ys (fun x' hm => hx x' (List.mem_cons_of_mem _ hm)) (fun u' hm => hu u' (List.mem_cons_of_mem _ hm)) z hTl
    exact aux w y hwNorm hyNorm
  · unfold GameSoundness.ajtaiSyndrome; induction A with
    | nil => rfl
    | cons row rs ih =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.cons.injEq]; refine ⟨?_, ih⟩
      rw [GameSoundness.dotInt_vecLinComb c 1 row w y (hwLen.trans hyLen.symm)]; exact masked_syndrome_row_eq c _ _ (q : Int)

/-- 2-special-soundness rewinding extractor for `verifyMaskedAjtaiOpening` (`0 Classical`). -/
theorem verifyMaskedAjtaiOpening_forking_sound (q cols bZ : Nat)
    (A : List (List Int)) (cm t : List Int) (c₁ c₂ : Int) (z₁ z₂ : List Int) (hNeC : c₁ ≠ c₂)
    (hAcc₁ : verifyMaskedAjtaiOpening q cols bZ A cm t c₁ z₁ = true)
    (hAcc₂ : verifyMaskedAjtaiOpening q cols bZ A cm t c₂ z₂ = true) :
    let dz := GameSoundness.vecLinComb 1 (-1) z₁ z₂
    c₁ ≠ c₂ ∧ dz.length = cols ∧ (c₁ - c₂) ≠ 0 ∧ (∀ x ∈ dz, x.natAbs ≤ 2 * bZ) ∧
    GameSoundness.ajtaiSyndrome q A dz = cm.map (fun cmi => ((c₁ - c₂) * cmi) % (q : Int)) := by
  simp only [verifyMaskedAjtaiOpening, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hAcc₁ hAcc₂
  rcases hAcc₁ with ⟨⟨⟨⟨hL₁, hCmLen⟩, hTLen⟩, hB₁⟩, hSyn₁⟩
  rcases hAcc₂ with ⟨⟨⟨⟨hL₂, _⟩, _⟩, hB₂⟩, hSyn₂⟩
  have hDzLen : (GameSoundness.vecLinComb 1 (-1) z₁ z₂).length = cols := by
    unfold GameSoundness.vecLinComb; rw [List.length_zipWith, hL₁, hL₂, Nat.min_self]
  refine ⟨hNeC, hDzLen, fun h => hNeC (by omega), ?_, ?_⟩
  · have aux : ∀ (u₁ u₂ : List Int), (∀ a ∈ u₁, a.natAbs ≤ bZ) → (∀ b ∈ u₂, b.natAbs ≤ bZ) →
        ∀ x ∈ GameSoundness.vecLinComb 1 (-1) u₁ u₂, x.natAbs ≤ 2 * bZ := by
      intro u₁; induction u₁ with
      | nil => intro _ _ _ _ hx; simp [GameSoundness.vecLinComb] at hx
      | cons a u₁ ih =>
        intro u₂ ha hb x hx; cases u₂ with
        | nil => simp [GameSoundness.vecLinComb] at hx
        | cons b u₂ =>
          dsimp only [GameSoundness.vecLinComb, List.zipWith] at hx
          rcases List.mem_cons.1 hx with rfl | hTl
          · have := ha a List.mem_cons_self; have := hb b List.mem_cons_self; omega
          · exact ih u₂ (fun a' hm => ha a' (List.mem_cons_of_mem _ hm)) (fun b' hm => hb b' (List.mem_cons_of_mem _ hm)) x hTl
    exact aux z₁ z₂ hB₁ hB₂
  · have auxSyn : ∀ (rs : List (List Int)) (cms ts : List Int), cms.length = rs.length → ts.length = rs.length →
        GameSoundness.ajtaiSyndrome q rs z₁ = List.zipWith (fun ti cmi => (ti + c₁ * cmi) % (q : Int)) ts cms →
        GameSoundness.ajtaiSyndrome q rs z₂ = List.zipWith (fun ti cmi => (ti + c₂ * cmi) % (q : Int)) ts cms →
        GameSoundness.ajtaiSyndrome q rs (GameSoundness.vecLinComb 1 (-1) z₁ z₂) =
          cms.map (fun cmi => ((c₁ - c₂) * cmi) % (q : Int)) := by
      intro rs; induction rs with
      | nil => intro cms _ hcl _ _ _; cases cms with | nil => rfl | cons _ _ => simp at hcl
      | cons row rs ih =>
        intro cms ts hcl htl hs₁ hs₂; cases cms with
        | nil => simp at hcl
        | cons cmi cms => cases ts with
          | nil => simp at htl
          | cons ti ts =>
            simp only [GameSoundness.ajtaiSyndrome, List.map_cons, List.zipWith_cons_cons, List.cons.injEq] at hs₁ hs₂ ⊢
            refine ⟨?_, ih cms ts (Nat.succ.inj hcl) (Nat.succ.inj htl) hs₁.2 hs₂.2⟩
            rw [GameSoundness.dotInt_vecLinComb 1 (-1) row z₁ z₂ (hL₁.trans hL₂.symm)]
            rw [show 1 * GameSoundness.dotInt row z₁ + (-1) * GameSoundness.dotInt row z₂ =
                    GameSoundness.dotInt row z₁ - GameSoundness.dotInt row z₂ by omega,
                Int.sub_emod, hs₁.1, hs₂.1, ← Int.sub_emod,
                show (ti + c₁ * cmi) - (ti + c₂ * cmi) = (c₁ - c₂) * cmi by rw [Int.sub_mul]; omega]
    exact auxSyn A cm t hCmLen hTLen hSyn₁ hSyn₂

/-- Distributional `MSISGame` binding reduction in the compressing regime (`4 * rows < cols`). -/
theorem maskedAjtai_binding_advantage_le_msis (P : GameSoundness.MSISParams) (bOpen : Nat)
    (hComp : CompressingSISParams P) (hBeta : 2 * bOpen ≤ P.beta)
    (adv : List (List Int) → GameSoundness.FinDist (List Int × List Int)) :
    CompressingSISParams P ∧
    GameSoundness.RatProb.le (GameSoundness.bindBreakProb P bOpen adv)
      (GameSoundness.msisAdvantage P (GameSoundness.reduceBindToMSIS adv)) :=
  ⟨hComp, GameSoundness.binding_advantage_le_msis_advantage P bOpen hBeta adv⟩

/-- Accepted masked transcript fork `(wRef, t, c₁, z₁, c₂, z₂)` against commitment `cm = A · wRef mod q`. -/
structure MaskedTranscriptFork where
  wRef : List Int
  t : List Int
  c₁ : Int
  z₁ : List Int
  c₂ : Int
  z₂ : List Int

def isValidMaskedTranscriptFork (P : GameSoundness.MSISParams) (bZ bW bChal : Nat)
    (A : List (List Int)) (f : MaskedTranscriptFork) : Bool :=
  let cm := GameSoundness.ajtaiSyndrome P.q A f.wRef
  (f.wRef.length == P.cols) && f.wRef.all (fun x => decide (x.natAbs ≤ bW)) &&
  (f.c₁ != f.c₂) && decide (f.c₁.natAbs ≤ bChal) && decide (f.c₂.natAbs ≤ bChal) &&
  verifyMaskedAjtaiOpening P.q P.cols bZ A cm f.t f.c₁ f.z₁ &&
  verifyMaskedAjtaiOpening P.q P.cols bZ A cm f.t f.c₂ f.z₂ &&
  (GameSoundness.vecLinComb 1 (-1) f.z₁ f.z₂ != GameSoundness.vecLinComb (f.c₁ - f.c₂) 0 f.wRef f.wRef)

def reduceMaskedForkStep (f : MaskedTranscriptFork) : List Int × List Int :=
  (GameSoundness.vecLinComb 1 (-1) f.z₁ f.z₂, GameSoundness.vecLinComb (f.c₁ - f.c₂) 0 f.wRef f.wRef)

/-- End-to-end accepted `verifyMaskedAjtaiOpening` transcript-fork reduction to `msisAdvantage P`. -/
theorem maskedTranscriptFork_advantage_le_msis (P : GameSoundness.MSISParams) (bZ bW bChal : Nat)
    (hComp : CompressingSISParams P) (hBeta : 2 * Nat.max (2 * bZ) (2 * bChal * bW) ≤ P.beta)
    (adv : List (List Int) → GameSoundness.FinDist MaskedTranscriptFork) :
    CompressingSISParams P ∧
    GameSoundness.RatProb.le
      (((GameSoundness.uniformMatDist P).bind (fun A => (adv A).map (isValidMaskedTranscriptFork P bZ bW bChal A))).probEvent id)
      (GameSoundness.msisAdvantage P (GameSoundness.reduceBindToMSIS (fun A => (adv A).map reduceMaskedForkStep))) := by
  refine ⟨hComp, GameSoundness.RatProb.le_trans ?_
    (GameSoundness.binding_advantage_le_msis_advantage P (Nat.max (2 * bZ) (2 * bChal * bW)) hBeta
      (fun A => (adv A).map reduceMaskedForkStep))⟩
  unfold GameSoundness.bindBreakProb
  refine GameSoundness.probEvent_bind_mono (GameSoundness.uniformMatDist P) _ _ id id (fun A _ _ => ?_)
  rw [GameSoundness.FinDist.probEvent_map, GameSoundness.FinDist.probEvent_map, GameSoundness.FinDist.probEvent_map]
  unfold GameSoundness.RatProb.le GameSoundness.FinDist.probEvent; apply Nat.mul_le_mul_right
  let bOpen := Nat.max (2 * bZ) (2 * bChal * bW)
  have ptImp : ∀ f : MaskedTranscriptFork, isValidMaskedTranscriptFork P bZ bW bChal A f = true →
      GameSoundness.isValidDoubleOpening P bOpen A (reduceMaskedForkStep f) = true := by
    intro f hF
    simp only [isValidMaskedTranscriptFork, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, List.all_eq_true, decide_eq_true_eq] at hF
    rcases hF with ⟨⟨⟨⟨⟨⟨⟨hWL, hWB⟩, hcNe⟩, hc1⟩, hc2⟩, hAcc₁⟩, hAcc₂⟩, hDiscrep⟩
    have hFork := verifyMaskedAjtaiOpening_forking_sound P.q P.cols bZ A
      (GameSoundness.ajtaiSyndrome P.q A f.wRef) f.t f.c₁ f.c₂ f.z₁ f.z₂ hcNe hAcc₁ hAcc₂
    have hScLen : (GameSoundness.vecLinComb (f.c₁ - f.c₂) 0 f.wRef f.wRef).length = P.cols := by
      unfold GameSoundness.vecLinComb; rw [List.length_zipWith, hWL, Nat.min_self]
    have hScBnd : ∀ x ∈ GameSoundness.vecLinComb (f.c₁ - f.c₂) 0 f.wRef f.wRef, x.natAbs ≤ bOpen := by
      have hcDiff : (f.c₁ - f.c₂).natAbs ≤ 2 * bChal := by omega
      have auxS : ∀ ws : List Int, (∀ u ∈ ws, u.natAbs ≤ bW) →
          ∀ x ∈ GameSoundness.vecLinComb (f.c₁ - f.c₂) 0 ws ws, x.natAbs ≤ 2 * bChal * bW := by
        intro ws; induction ws with
        | nil => intro _ _ hx; simp [GameSoundness.vecLinComb] at hx
        | cons u ws ih =>
          intro hU x hx; dsimp only [GameSoundness.vecLinComb, List.zipWith] at hx
          rcases List.mem_cons.1 hx with rfl | hTl
          · rw [Int.zero_mul, Int.add_zero, Int.natAbs_mul]; exact Nat.mul_le_mul hcDiff (hU u List.mem_cons_self)
          · exact ih (fun u' hm => hU u' (List.mem_cons_of_mem _ hm)) x hTl
      exact fun x hx => Nat.le_trans (auxS f.wRef hWB x hx) (Nat.le_max_right _ _)
    have hScSyn : GameSoundness.ajtaiSyndrome P.q A (GameSoundness.vecLinComb (f.c₁ - f.c₂) 0 f.wRef f.wRef) =
        (GameSoundness.ajtaiSyndrome P.q A f.wRef).map (fun cmi => ((f.c₁ - f.c₂) * cmi) % (P.q : Int)) := by
      have auxSyn : ∀ (mat : List (List Int)),
          GameSoundness.ajtaiSyndrome P.q mat (GameSoundness.vecLinComb (f.c₁ - f.c₂) 0 f.wRef f.wRef) =
            (GameSoundness.ajtaiSyndrome P.q mat f.wRef).map (fun cmi => ((f.c₁ - f.c₂) * cmi) % (P.q : Int)) := by
        intro mat; unfold GameSoundness.ajtaiSyndrome; induction mat with
        | nil => rfl
        | cons row rs ih =>
          simp only [List.map_cons, List.cons.injEq]; refine ⟨?_, ih⟩
          rw [GameSoundness.dotInt_vecLinComb (f.c₁ - f.c₂) 0 row f.wRef f.wRef rfl, Int.zero_mul, Int.add_zero,
              Int.mul_emod (f.c₁ - f.c₂) _ (P.q : Int), Int.mul_emod (f.c₁ - f.c₂) (_ % _) (P.q : Int), Int.emod_emod]
      exact auxSyn A
    simp only [GameSoundness.isValidDoubleOpening, reduceMaskedForkStep, Bool.and_eq_true, beq_iff_eq,
      bne_iff_ne, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨hFork.2.1, hScLen⟩, hDiscrep⟩, fun x hx => Nat.le_trans (hFork.2.2.2.1 x hx) (Nat.le_max_left _ _)⟩,
      hScBnd⟩, hFork.2.2.2.2.trans hScSyn.symm⟩
  have monoMass : ∀ (p₁ p₂ : MaskedTranscriptFork → Bool) (hImp : ∀ x, p₁ x = true → p₂ x = true)
      (xs : List (MaskedTranscriptFork × Nat)),
      GameSoundness.eventMass p₁ xs ≤ GameSoundness.eventMass p₂ xs := by
    intro p₁ p₂ hImp xs; induction xs with
    | nil => exact Nat.le_refl 0
    | cons hd _ ih =>
      rcases hd with ⟨f, wt⟩; dsimp only [GameSoundness.eventMass]
      cases hp₁ : p₁ f
      · cases p₂ f <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      · rw [hImp f hp₁]; simp only [↓reduceIte]; omega
  exact monoMass (isValidMaskedTranscriptFork P bZ bW bChal A)
    (GameSoundness.isValidDoubleOpening P bOpen A ∘ reduceMaskedForkStep) ptImp (adv A).support

/-- Public statement `(q, cols, A, cm, c)` for the joint-transcript `(t, z)` masked Ajtai HVZK game. -/
structure MaskedAjtaiStmt where
  q : Nat
  cols : Nat
  matrix : List (List Int)
  cm : List Int
  chal : Int

def MaskedAjtaiRel (bW cMax : Nat) (x : MaskedAjtaiStmt) (w : List Int) : Prop :=
  w.length = x.cols ∧ (∀ wi ∈ w, wi.natAbs ≤ bW) ∧ x.chal.natAbs ≤ cMax ∧
  x.cm = GameSoundness.ajtaiSyndrome x.q x.matrix w

def maskedAjtaiZKProtocol (B bW cMax : Nat) :
    GameSoundness.ZKProtocol MaskedAjtaiStmt (List Int) (List Int × List Int) Unit where
  Rel := MaskedAjtaiRel bW cMax
  leakage _ _ := ()
  realView x w := (GameSoundness.uniformVecDist B x.cols).map fun y =>
    (GameSoundness.ajtaiSyndrome x.q x.matrix y, maskedResponse x.chal w y)

/-- Witness-independent joint-transcript `(t, z)` simulator programming `t := (A z - c · cm) mod q`. -/
def maskedAjtaiSimulator (B : Nat) :
    GameSoundness.ZKSimulator MaskedAjtaiStmt Unit (List Int × List Int) where
  simView x _ := (GameSoundness.uniformVecDist B x.cols).map fun z =>
    (List.zipWith (fun az cmi => (az - x.chal * cmi) % (x.q : Int)) (GameSoundness.ajtaiSyndrome x.q x.matrix z) x.cm, z)

private theorem schnorr_sim_mod_eq (c a b q : Int) : ((c * a + 1 * b) % q - c * (a % q)) % q = b % q := by
  rw [masked_syndrome_row_eq c a b q, Int.sub_emod, Int.emod_emod, ← Int.sub_emod,
      show (b % q + c * (a % q)) - c * (a % q) = b % q by omega, Int.emod_emod]

private theorem scaleSupport_mem_fst {α : Type} {c : Nat} {xs : List (α × Nat)} {p : α × Nat}
    (hp : p ∈ GameSoundness.scaleSupport c xs) : ∃ wt, (p.1, wt) ∈ xs := by
  induction xs with
  | nil => cases hp
  | cons hd tl ih =>
    rcases hd with ⟨a, w⟩; simp only [GameSoundness.scaleSupport, List.mem_cons] at hp
    rcases hp with rfl | htl
    · exact ⟨w, .head _⟩
    · obtain ⟨wt, hwt⟩ := ih htl; exact ⟨wt, .tail _ hwt⟩

private theorem bindRaw_mem_fst {α β : Type} :
    ∀ (xs : List (α × Nat)) (k : α → GameSoundness.FinDist β) {p : β × Nat},
      p ∈ (GameSoundness.bindRaw xs k).1 → ∃ a wt wt', (a, wt) ∈ xs ∧ (p.1, wt') ∈ (k a).support
  | [], _, _, hp => by simp [GameSoundness.bindRaw] at hp
  | (a, w) :: rest, k, p, hp => by
    simp only [GameSoundness.bindRaw, List.mem_append] at hp; rcases hp with hL | hR
    · obtain ⟨wt', hwt'⟩ := scaleSupport_mem_fst hL; exact ⟨a, w, wt', .head _, hwt'⟩
    · obtain ⟨wt0, hwt0⟩ := scaleSupport_mem_fst hR
      obtain ⟨a', wt, wt', ha', hb'⟩ := bindRaw_mem_fst rest k hwt0; exact ⟨a', wt, wt', .tail _ ha', hb'⟩

private theorem uniformVecDist_mem_length (B : Nat) :
    ∀ (m : Nat) {p : List Int × Nat}, p ∈ (GameSoundness.uniformVecDist B m).support → p.1.length = m
  | 0, p, hp => by simp only [GameSoundness.uniformVecDist, GameSoundness.FinDist.pure, List.mem_singleton] at hp; rw [hp]; rfl
  | m + 1, p, hp => by
    simp only [GameSoundness.uniformVecDist, GameSoundness.FinDist.map, List.mem_map] at hp
    rcases hp with ⟨⟨⟨u, us⟩, wt⟩, hProd, hEq⟩
    obtain ⟨_, _, _, _, hMap⟩ := bindRaw_mem_fst _ _ hProd
    simp only [GameSoundness.FinDist.map, List.mem_map] at hMap; rcases hMap with ⟨⟨us', wt'⟩, hus', hPairEq⟩
    rw [congrArg Prod.fst hEq.symm, List.length_cons, congrArg (fun q => q.1.2) hPairEq.symm, uniformVecDist_mem_length B m hus']

/-- Joint-transcript `(t, z)` statistical ZK with TV error `≤ (cols · cMax · bW) / (2 · B + 1)`. -/
theorem maskedAjtai_statistical_zk (B bW cMax : Nat) (x : MaskedAjtaiStmt) (w : List Int)
    (hRel : (maskedAjtaiZKProtocol B bW cMax).Rel x w) :
    GameSoundness.RatProb.le
      (GameSoundness.tvDist ((maskedAjtaiZKProtocol B bW cMax).realView x w) ((maskedAjtaiSimulator B).simView x ()))
      ⟨x.cols * (cMax * bW), 2 * B + 1, by omega⟩ := by
  rcases hRel with ⟨hwLen, hwBnd, hcBnd, hCmEq⟩
  let cw : List Int := w.map (x.chal * ·)
  have hcwLen : cw.length = x.cols := by simp [cw, hwLen]
  have hcwBnd : ∀ u ∈ cw, u.natAbs ≤ cMax * bW := by
    intro u hu; obtain ⟨wi, hwi, rfl⟩ := List.mem_map.1 hu; rw [Int.natAbs_mul]; exact Nat.mul_le_mul hcBnd (hwBnd wi hwi)
  let liftView : List Int → List Int × List Int := fun z =>
    (List.zipWith (fun az cmi => (az - x.chal * cmi) % (x.q : Int)) (GameSoundness.ajtaiSyndrome x.q x.matrix z) x.cm, z)
  have hRealEq : (maskedAjtaiZKProtocol B bW cMax).realView x w =
      (((GameSoundness.uniformVecDist B cw.length).map (fun y => List.zipWith (· + ·) cw y)).map liftView) := by
    apply GameSoundness.FinDist.ext_support; dsimp only [maskedAjtaiZKProtocol, liftView, GameSoundness.FinDist.map]
    rw [hcwLen, List.map_map]; refine List.map_congr_left fun p hp => ?_
    have hy : p.1.length = x.cols := uniformVecDist_mem_length B x.cols hp
    dsimp only [Function.comp]; refine Prod.ext ?_ rfl
    have hzEq : List.zipWith (· + ·) cw p.1 = maskedResponse x.chal w p.1 := by
      dsimp only [cw, maskedResponse, GameSoundness.vecLinComb]
      have auxZ : ∀ (ws ys : List Int), List.zipWith (· + ·) (ws.map (x.chal * ·)) ys =
          List.zipWith (fun wi yi => x.chal * wi + 1 * yi) ws ys := by
        intro ws; induction ws with | nil => intros; rfl | cons wi ws ih => intro ys; cases ys with | nil => rfl | cons yi ys => simp [ih ys]
      exact auxZ w p.1
    dsimp only [liftView]; rw [hzEq, hCmEq]; refine Prod.ext ?_ rfl
    unfold GameSoundness.ajtaiSyndrome; induction x.matrix with
    | nil => rfl
    | cons row rs ih =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.cons.injEq]; refine ⟨?_, ih⟩; dsimp only [maskedResponse]
      rw [GameSoundness.dotInt_vecLinComb x.chal 1 row w p.1 (hwLen.trans hy.symm)]
      exact (schnorr_sim_mod_eq x.chal _ _ (x.q : Int)).symm
  have hSimEq : (maskedAjtaiSimulator B).simView x () = (GameSoundness.uniformVecDist B cw.length).map liftView := by
    dsimp only [maskedAjtaiSimulator, liftView]; rw [hcwLen]
  rw [hRealEq, hSimEq]; refine GameSoundness.RatProb.le_trans (GameSoundness.tvDist_map_le liftView _ _) ?_
  simpa [hcwLen] using GameSoundness.uniformVecShift_tvDist_le B (cMax * bW) cw hcwBnd

theorem maskedAjtai_protocol_statistical_zk (B bW cMax cols : Nat) :
    GameSoundness.StatisticalZK
      { Rel := fun x w => x.cols = cols ∧ MaskedAjtaiRel bW cMax x w, leakage := fun _ _ => (),
        realView := (maskedAjtaiZKProtocol B bW cMax).realView }
      (maskedAjtaiSimulator B) ⟨cols * (cMax * bW), 2 * B + 1, by omega⟩ :=
  fun x w ⟨hCols, hRel⟩ => by simpa [hCols] using maskedAjtai_statistical_zk B bW cMax x w hRel

/-- Dual masked spine achieves BOTH $\lor$-binding (`msisAdvantage`) AND $\land$-statistical-ZK. -/
theorem dualSpine_masked_both_bind_and_zk {V₁ : Type} [DecidableEq V₁]
    (P : GameSoundness.MSISParams) (bOpen B bW cMax : Nat) (hComp : CompressingSISParams P) (hBeta : 2 * bOpen ≤ P.beta)
    (adv : List (List Int) → GameSoundness.FinDist (List Int × List Int))
    (prot₁ : GameSoundness.ZKProtocol MaskedAjtaiStmt (List Int) V₁ Unit)
    (Sim₁ : GameSoundness.ZKSimulator MaskedAjtaiStmt Unit V₁) (ε₁ : GameSoundness.RatProb)
    (hRelImp : ∀ x w, prot₁.Rel x w → x.cols = P.cols ∧ MaskedAjtaiRel bW cMax x w)
    (hZK₁ : GameSoundness.StatisticalZK prot₁ Sim₁ ε₁) :
    GameSoundness.RatProb.le (GameSoundness.bindBreakProb P bOpen adv)
      (GameSoundness.msisAdvantage P (GameSoundness.reduceBindToMSIS adv)) ∧
    GameSoundness.StatisticalZK
      ⟨prot₁.Rel, fun _ _ => (), fun x w =>
        GameSoundness.FinDist.prod (prot₁.realView x w) ((maskedAjtaiZKProtocol B bW cMax).realView x w)⟩
      ⟨fun x u => GameSoundness.FinDist.prod (Sim₁.simView x u) ((maskedAjtaiSimulator B).simView x u)⟩
      (GameSoundness.RatProb.add ε₁ ⟨P.cols * (cMax * bW), 2 * B + 1, by omega⟩) :=
  ⟨(maskedAjtai_binding_advantage_le_msis P bOpen hComp hBeta adv).2,
   GameSoundness.dual_zk_of_both_zk prot₁
     ⟨fun x w => x.cols = P.cols ∧ MaskedAjtaiRel bW cMax x w, fun _ _ => (), (maskedAjtaiZKProtocol B bW cMax).realView⟩
     Sim₁ (maskedAjtaiSimulator B) ε₁ ⟨P.cols * (cMax * bW), 2 * B + 1, by omega⟩
     hRelImp hZK₁ (maskedAjtai_protocol_statistical_zk B bW cMax P.cols)⟩

end Obend.Crypto
end
