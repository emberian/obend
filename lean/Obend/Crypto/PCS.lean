module
/-
# Obend.Crypto.PCS — Proximity-Gap Guard (`2026/2424`), `MultilinearPCS` & `CanopyMerklePCS`

Polymorphic multilinear polynomial commitment interface and concrete 256-bit hash-tree backend:
1. **Oct 2026 Binary RS Proximity-Gap Guard (`Dao–Kominers–Thaler–Zheng, ePrint 2026/2424`)**:
   `DomainKind` (`.primeField | .binaryAdditive`), `ProximityRegime`
   (`.uniqueDecodingRadius | .johnsonBound | .capacityBound`), and `ValidProximityConfig`
   make it a **type-level impossibility** to instantiate a `.binaryAdditive` PCS outside
   `.uniqueDecodingRadius` (`binaryAdditive_forces_udr`, `binaryAdditive_refuses_johnson`,
   `binaryAdditive_refuses_capacity`).
2. **`MultilinearPCS R` & `BindingSound`**:
   Polymorphic commitment, Fenzi-bound transcript opening, evaluation verification, completeness
   contract, and evaluation-binding soundness predicate.
3. **`SparseOneHotCommit` (`Twist & Shout` / `Akita` Specialization)**:
   Nonzero-proportional commitment interface agreeing with `commit` on `oneHotTable R v idx`.
4. **`CanopyMerklePCS` over `Goldilocks`**:
   Executable 32-byte `Digest32` cSHAKE256 Merkle-tensor commitment and opening scheme with
   proved path completeness (`verifyMerklePath_completeness`), collision reduction
   (`merkle_double_open_yields_hash_collision`), and unconditional `BindingSound` under
   collision resistance (`canopyMerklePCS_bindingSound_of_collisionFree`).
-/
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck

@[expose] public section
namespace Obend.Crypto

open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Binary vs. Prime-Field Proximity-Gap Guard (`ePrint 2026/2424`) -/

/-- Underlying linear-code evaluation domain algebra. -/
inductive DomainKind where
  | primeField
  | binaryAdditive
  deriving DecidableEq, Repr

/-- Proximity-gap / list-decoding soundness regime of a code-based PCS. -/
inductive ProximityRegime where
  | uniqueDecodingRadius
  | johnsonBound
  | capacityBound
  deriving DecidableEq, Repr

/-- **Sound Proximity Configuration (`ValidProximityConfig`)**:
    Encodes `ePrint 2026/2424` (binary additive RS codes suffer superpolynomial exceptional
    challenges below the Johnson bound) vs. `arXiv:2609.05870` / `2026/2056` (prime-field RS
    codes enjoy capacity MCA): `.binaryAdditive` ONLY inhabits `.uniqueDecodingRadius`. -/
inductive ValidProximityConfig : DomainKind → ProximityRegime → Prop where
  | primeUDR : ValidProximityConfig .primeField .uniqueDecodingRadius
  | primeJohnson : ValidProximityConfig .primeField .johnsonBound
  | primeCapacity : ValidProximityConfig .primeField .capacityBound
  | binaryUDR : ValidProximityConfig .binaryAdditive .uniqueDecodingRadius

/-- Executable checker for `ValidProximityConfig`. -/
def checkProximityConfig (dom : DomainKind) (reg : ProximityRegime) : Bool :=
  match dom, reg with
  | .primeField, _ => true
  | .binaryAdditive, .uniqueDecodingRadius => true
  | .binaryAdditive, .johnsonBound => false
  | .binaryAdditive, .capacityBound => false

theorem checkProximityConfig_iff (dom : DomainKind) (reg : ProximityRegime) :
    checkProximityConfig dom reg = true ↔ ValidProximityConfig dom reg := by
  cases dom <;> cases reg <;> constructor <;> intro h
  · exact .primeUDR
  · rfl
  · exact .primeJohnson
  · rfl
  · exact .primeCapacity
  · rfl
  · exact .binaryUDR
  · rfl
  · cases h
  · cases h
  · cases h
  · cases h

/-- **`ePrint 2026/2424` Guard Theorem**: Any valid proximity configuration over a
    `.binaryAdditive` domain is forced to `.uniqueDecodingRadius`. -/
theorem binaryAdditive_forces_udr (reg : ProximityRegime)
    (h : ValidProximityConfig .binaryAdditive reg) :
    reg = .uniqueDecodingRadius := by
  cases h
  rfl

/-- **`ePrint 2026/2424` Non-UDR Refusal Theorem**:
    Every proximity regime `reg ≠ .uniqueDecodingRadius` (both `.johnsonBound` and `.capacityBound`)
    is uninhabited on `.binaryAdditive` domains. -/
theorem binaryAdditive_refuses_non_udr (reg : ProximityRegime)
    (hNe : reg ≠ .uniqueDecodingRadius) :
    ¬ ValidProximityConfig .binaryAdditive reg := by
  intro hValid
  exact hNe (binaryAdditive_forces_udr reg hValid)

example : ¬ ValidProximityConfig .binaryAdditive .johnsonBound :=
  binaryAdditive_refuses_non_udr .johnsonBound (by decide)

example : ¬ ValidProximityConfig .binaryAdditive .capacityBound :=
  binaryAdditive_refuses_non_udr .capacityBound (by decide)

/-! ## 2. Polymorphic `MultilinearPCS R`, `BindingSound` & `SparseOneHotCommit` -/

/-- Polymorphic Multilinear Polynomial Commitment Scheme over `[CommRingOps R]`,
    carrying a mandatory type-level `ValidProximityConfig` witness and operating over
    Fenzi-safe `Transcript .relationBound` challenges. -/
structure MultilinearPCS (R : Type) [CommRingOps R] where
  domainKind : DomainKind
  regime : ProximityRegime
  validRegime : ValidProximityConfig domainKind regime
  Params : Type
  Commitment : Type
  OpeningProof : Type
  commit : Params → (numVars : Nat) → List R → Commitment
  openEval : Params → (numVars : Nat) → List R → EvalClaim R numVars →
    Transcript .relationBound → OpeningProof × Transcript .relationBound
  verifyEval : Params → (numVars : Nat) → Commitment → EvalClaim R numVars →
    OpeningProof → Transcript .relationBound → Bool × Transcript .relationBound
  completeness :
    ∀ (pp : Params) (v : Nat) (tbl : List R) (pt : List R) (hPt : pt.length = v)
      (tr : Transcript .relationBound),
      tbl.length = 2 ^ v →
      let claim : EvalClaim R v := ⟨pt, hPt, mleEval tbl pt⟩
      let (prf, _) := openEval pp v tbl claim tr
      (verifyEval pp v (commit pp v tbl) claim prf tr).1 = true

/-- **Evaluation Binding Soundness (`BindingSound`)**:
    No commitment `comm` can be opened to two distinct values `c₁.expectedVal ≠ c₂.expectedVal`
    at the same evaluation point `c₁.point = c₂.point`. -/
def BindingSound {R : Type} [CommRingOps R] (P : MultilinearPCS R) : Prop :=
  ∀ (pp : P.Params) (v : Nat) (comm : P.Commitment)
    (c₁ c₂ : EvalClaim R v) (π₁ π₂ : P.OpeningProof)
    (tr₁ tr₂ : Transcript .relationBound),
    c₁.point = c₂.point →
    (P.verifyEval pp v comm c₁ π₁ tr₁).1 = true →
    (P.verifyEval pp v comm c₂ π₂ tr₂).1 = true →
    c₁.expectedVal = c₂.expectedVal

/-- Dense one-hot multilinear table of length $2^{\text{numVars}}$ with `1` at `idx` and `0` elsewhere. -/
def oneHotTable (R : Type) [CommRingOps R] (numVars idx : Nat) : List R :=
  (List.range (2 ^ numVars)).map fun i =>
    if i = idx then CommRingOps.one else CommRingOps.zero

theorem oneHotTable_length (R : Type) [CommRingOps R] (numVars idx : Nat) :
    (oneHotTable R numVars idx).length = 2 ^ numVars := by
  simp [oneHotTable]

/-- **`Twist & Shout` / `Akita` (`2026/1983`) Sparse One-Hot Commitment Specialization**:
    Allows committing to a 1-hot lookup indicator in $O(1)$ column operations rather than
    $O(2^v)$ dense operations, with proved equality to `P.commit pp v (oneHotTable R v idx)`. -/
class SparseOneHotCommit (R : Type) [CommRingOps R] (P : MultilinearPCS R) where
  commitOneHot : P.Params → (numVars : Nat) → (idx : Nat) → P.Commitment
  commitOneHot_eq_commit :
    ∀ (pp : P.Params) (v idx : Nat),
      idx < 2 ^ v →
      commitOneHot pp v idx = P.commit pp v (oneHotTable R v idx)

/-! ## 3. Exact 32-Byte Digest Carrier (`Digest32`) & Domain-Separated Merkle Tree -/

/-- Exact 32-byte (256-bit) digest node (`bytes.size = 32`). -/
structure Digest32 where
  bytes : ByteArray
  size_eq : bytes.size = 32
  deriving DecidableEq

namespace Digest32

theorem ext {a b : Digest32} (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem toList_length (d : Digest32) : d.bytes.data.toList.length = 32 := by
  rw [← Fast.size_eq_length]
  exact d.size_eq

end Digest32

/-- A 256-bit byte hash function guaranteed to emit 32-byte digests. -/
structure Hash32 where
  eval : Hash
  len_eq : ∀ input : List UInt8, (eval input).length = 32

/-- `"OBEND.CRYPTO.CANOPY.MERKLE/v1"` in ASCII. -/
def canopyMerkleCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x43, 0x52, 0x59, 0x50, 0x54, 0x4f,
   0x2e, 0x43, 0x41, 0x4e, 0x4f, 0x50, 0x59, 0x2e, 0x4d, 0x45, 0x52, 0x4b,
   0x4c, 0x45, 0x2f, 0x76, 0x31]

/-- Deployed 256-bit cSHAKE256 `Hash32` instance for `CanopyMerklePCS`. -/
def deployedCanopyHash32 : Hash32 where
  eval := cshake256Bytes canopyMerkleCustomization
  len_eq input := cshake256Bytes_length canopyMerkleCustomization input

/-- Apply `H : Hash32` to produce a `Digest32`. -/
def evalDigest32 (H : Hash32) (preimage : List UInt8) : Digest32 :=
  ⟨Native.bytesOfList (H.eval preimage), by
    rw [Fast.size_eq_length, Native.bytesOfList_toList, H.len_eq]⟩

theorem evalDigest32_eq_imp_collision (H : Hash32) {p₁ p₂ : List UInt8}
    (hne : p₁ ≠ p₂) (heq : evalDigest32 H p₁ = evalDigest32 H p₂) :
    Collision H.eval := by
  have hl : (evalDigest32 H p₁).bytes.data.toList = (evalDigest32 H p₂).bytes.data.toList :=
    congrArg (fun d => d.bytes.data.toList) heq
  simp only [evalDigest32, Native.bytesOfList_toList] at hl
  exact ⟨p₁, p₂, hne, congrArg ofBE hl⟩

/-- RFC-6962 / Canopy domain-separated leaf preimage: `0x00 ‖ leb128(idx) ‖ be8(val)`. -/
def merkleLeafPreimage (idx : Nat) (x : Goldilocks) : List UInt8 :=
  (0x00 : UInt8) :: (leb128 idx ++ be 8 x.val)

theorem merkleLeafPreimage_injective {i₁ i₂ : Nat} {x₁ x₂ : Goldilocks}
    (h : merkleLeafPreimage i₁ x₁ = merkleLeafPreimage i₂ x₂) :
    i₁ = i₂ ∧ x₁ = x₂ := by
  simp only [merkleLeafPreimage, List.cons.injEq] at h
  obtain ⟨hi, hbe⟩ := leb128_prefix_inj h.2
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hx := be_injective (h8 ▸ Goldilocks.val_lt_two_pow_64 x₁)
                          (h8 ▸ Goldilocks.val_lt_two_pow_64 x₂) hbe
  exact ⟨hi, Goldilocks.ext hx⟩

/-- Domain-separated internal node preimage: `0x01 ‖ leftBytes(32) ‖ rightBytes(32)`. -/
def merkleNodePreimage (l r : Digest32) : List UInt8 :=
  (0x01 : UInt8) :: (l.bytes.data.toList ++ r.bytes.data.toList)

theorem merkleNodePreimage_injective {l₁ r₁ l₂ r₂ : Digest32}
    (h : merkleNodePreimage l₁ r₁ = merkleNodePreimage l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  simp only [merkleNodePreimage, List.cons.injEq] at h
  have hlen : l₁.bytes.data.toList.length = l₂.bytes.data.toList.length := by
    rw [l₁.toList_length, l₂.toList_length]
  obtain ⟨hl, hr⟩ := List.append_inj h.2 hlen
  exact ⟨Digest32.ext (byteArray_eq_of_toList_eq hl),
         Digest32.ext (byteArray_eq_of_toList_eq hr)⟩

def hashLeaf32 (H : Hash32) (idx : Nat) (x : Goldilocks) : Digest32 :=
  evalDigest32 H (merkleLeafPreimage idx x)

def hashNode32 (H : Hash32) (l r : Digest32) : Digest32 :=
  evalDigest32 H (merkleNodePreimage l r)

def emptyTreeDigest32 (H : Hash32) : Digest32 :=
  evalDigest32 H [0x02]

theorem hashLeaf32_binds (H : Hash32) {i : Nat} {x₁ x₂ : Goldilocks}
    (h : hashLeaf32 H i x₁ = hashLeaf32 H i x₂) :
    x₁ = x₂ ∨ Collision H.eval := by
  by_cases hpre : merkleLeafPreimage i x₁ = merkleLeafPreimage i x₂
  · exact .inl (merkleLeafPreimage_injective hpre).2
  · exact .inr (evalDigest32_eq_imp_collision H hpre h)

theorem hashNode32_binds (H : Hash32) {l₁ r₁ l₂ r₂ : Digest32}
    (h : hashNode32 H l₁ r₁ = hashNode32 H l₂ r₂) :
    (l₁ = l₂ ∧ r₁ = r₂) ∨ Collision H.eval := by
  by_cases hpre : merkleNodePreimage l₁ r₁ = merkleNodePreimage l₂ r₂
  · exact .inl (merkleNodePreimage_injective hpre)
  · exact .inr (evalDigest32_eq_imp_collision H hpre h)

/-- Balanced binary 32-byte Merkle root over `leaves : List Digest32`. -/
def merkleRoot32 (H : Hash32) (leaves : List Digest32) : Digest32 :=
  if h0 : leaves.isEmpty then emptyTreeDigest32 H
  else if h1 : leaves.length < 2 then
    match leaves, h0 with
    | d :: _, _ => d
  else
    hashNode32 H (merkleRoot32 H (leaves.take (leaves.length / 2)))
                 (merkleRoot32 H (leaves.drop (leaves.length / 2)))
termination_by leaves.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- Sibling authentication path from leaf `idx` to the root (top-down order). -/
def merklePath32 (H : Hash32) (leaves : List Digest32) (idx : Nat) : List Digest32 :=
  if leaves.length < 2 then []
  else if idx < leaves.length / 2 then
    merkleRoot32 H (leaves.drop (leaves.length / 2)) ::
      merklePath32 H (leaves.take (leaves.length / 2)) idx
  else
    merkleRoot32 H (leaves.take (leaves.length / 2)) ::
      merklePath32 H (leaves.drop (leaves.length / 2)) (idx - leaves.length / 2)
termination_by leaves.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- Climb a 32-byte Merkle path from leaf digest `leaf` at position `idx` of a tree of `n` leaves. -/
def climbMerkle32 (H : Hash32) : (n idx : Nat) → Digest32 → List Digest32 → Option Digest32
  | n, idx, leaf, [] => if n = 1 && idx == 0 then some leaf else none
  | n, idx, leaf, sib :: rest =>
    if n < 2 || idx ≥ n then none
    else if idx < n / 2 then
      (climbMerkle32 H (n / 2) idx leaf rest).map fun l => hashNode32 H l sib
    else
      (climbMerkle32 H (n - n / 2) (idx - n / 2) leaf rest).map fun r => hashNode32 H sib r

theorem getElem_take_digest (l : List Digest32) {k i : Nat} (hi : i < k) (hlt : i < (l.take k).length) :
    (l.take k)[i] = l[i]'(by rw [List.length_take] at hlt; omega) := by
  simp [List.getElem_take]

theorem getElem_drop_digest (l : List Digest32) (k i : Nat) (hlt : i < (l.drop k).length) :
    (l.drop k)[i] = l[k + i]'(by rw [List.length_drop] at hlt; omega) := by
  simp [List.getElem_drop]

/-- Honest `merklePath32` climbs cleanly to `merkleRoot32`. -/
theorem climbMerkle32_merklePath32 (H : Hash32) (leaves : List Digest32)
    (idx : Nat) (hIdx : idx < leaves.length) :
    climbMerkle32 H leaves.length idx leaves[idx] (merklePath32 H leaves idx) =
      some (merkleRoot32 H leaves) := by
  by_cases h2 : leaves.length < 2
  · have h1 : leaves.length = 1 := by omega
    have hIdx0 : idx = 0 := by omega
    subst hIdx0
    match leaves, h1 with
    | [d], _ =>
      rw [merklePath32]
      conv => rhs; rw [merkleRoot32]
      simp [climbMerkle32]
  · have hNotEmpty : leaves.isEmpty = false := by
      cases leaves with
      | nil => simp at h2
      | cons _ _ => rfl
    have hlt : (leaves.take (leaves.length / 2)).length = leaves.length / 2 := by
      rw [List.length_take]; omega
    have hld : (leaves.drop (leaves.length / 2)).length = leaves.length - leaves.length / 2 :=
      List.length_drop
    rw [merklePath32]
    simp only [h2, ↓reduceIte]
    conv => rhs; rw [merkleRoot32]; simp only [hNotEmpty, Bool.false_eq_true, h2, ↓reduceDIte]
    by_cases hi : idx < leaves.length / 2
    · simp only [hi, ↓reduceIte]
      have hiTake : idx < (leaves.take (leaves.length / 2)).length := by rw [hlt]; exact hi
      have ihL := climbMerkle32_merklePath32 H (leaves.take (leaves.length / 2)) idx hiTake
      rw [hlt, getElem_take_digest leaves hi hiTake] at ihL
      have hBad : (decide (leaves.length < 2) || decide (idx ≥ leaves.length)) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
      simp only [climbMerkle32, hBad, Bool.false_eq_true, ↓reduceIte, hi, ihL, Option.map_some]
    · simp only [hi, ↓reduceIte]
      have hiDrop : idx - leaves.length / 2 < (leaves.drop (leaves.length / 2)).length := by
        rw [hld]; omega
      have ihR := climbMerkle32_merklePath32 H (leaves.drop (leaves.length / 2))
        (idx - leaves.length / 2) hiDrop
      rw [hld, getElem_drop_digest leaves _ _ hiDrop] at ihR
      have hElemEq : leaves[leaves.length / 2 + (idx - leaves.length / 2)]'(by omega) =
          leaves[idx] := by congr 1; omega
      rw [hElemEq] at ihR
      have hBad : (decide (leaves.length < 2) || decide (idx ≥ leaves.length)) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
      simp only [climbMerkle32, hBad, Bool.false_eq_true, ↓reduceIte, hi, ihR, Option.map_some]
termination_by leaves.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- **Merkle Climb Binding (`climbMerkle32_binds`)**:
    Two valid climbs from position `idx` of a size-`n` tree to the same `root` either start
    from the exact same leaf `Digest32` or witness a `Collision H.eval`. -/
theorem climbMerkle32_binds (H : Hash32) :
    ∀ (p₁ p₂ : List Digest32) (n idx : Nat) (leaf₁ leaf₂ root : Digest32),
      climbMerkle32 H n idx leaf₁ p₁ = some root →
      climbMerkle32 H n idx leaf₂ p₂ = some root →
      leaf₁ = leaf₂ ∨ Collision H.eval
  | [], [], n, idx, leaf₁, leaf₂, root, h₁, h₂ => by
    simp only [climbMerkle32] at h₁ h₂
    split at h₁
    · rename_i hc
      simp only [hc, ↓reduceIte, Option.some.injEq] at h₁ h₂
      exact .inl (h₁.trans h₂.symm)
    · cases h₁
  | [], _ :: _, n, idx, _, _, _, h₁, h₂ => by
    simp only [climbMerkle32] at h₁ h₂
    split at h₁
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨rfl, _⟩
      simp at h₂
    · cases h₁
  | _ :: _, [], n, idx, _, _, _, h₁, h₂ => by
    simp only [climbMerkle32] at h₁ h₂
    split at h₂
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨rfl, _⟩
      simp at h₁
    · cases h₂
  | s₁ :: ss₁, s₂ :: ss₂, n, idx, leaf₁, leaf₂, root, h₁, h₂ => by
    simp only [climbMerkle32] at h₁ h₂
    split at h₁
    · cases h₁
    split at h₂
    · cases h₂
    split at h₁
    · rename_i hi
      simp only [hi, ↓reduceIte] at h₂
      obtain ⟨l₁, hl₁, rfl⟩ := Option.map_eq_some_iff.1 h₁
      obtain ⟨l₂, hl₂, hNode⟩ := Option.map_eq_some_iff.1 h₂
      rcases hashNode32_binds H hNode.symm with ⟨hll, _⟩ | hCol
      · exact climbMerkle32_binds H ss₁ ss₂ (n / 2) idx leaf₁ leaf₂ l₁ hl₁ (hll ▸ hl₂)
      · exact .inr hCol
    · rename_i hi
      simp only [hi, ↓reduceIte] at h₂
      obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.1 h₁
      obtain ⟨r₂, hr₂, hNode⟩ := Option.map_eq_some_iff.1 h₂
      rcases hashNode32_binds H hNode.symm with ⟨_, hrr⟩ | hCol
      · exact climbMerkle32_binds H ss₁ ss₂ (n - n / 2) (idx - n / 2) leaf₁ leaf₂ r₁ hr₁ (hrr ▸ hr₂)
      · exact .inr hCol

/-- Hash a Goldilocks table into indexed 32-byte Merkle leaves. -/
def hashTableLeaves (H : Hash32) (tbl : List Goldilocks) : List Digest32 :=
  tbl.mapIdx fun idx x => hashLeaf32 H idx x

theorem hashTableLeaves_length (H : Hash32) (tbl : List Goldilocks) :
    (hashTableLeaves H tbl).length = tbl.length := by
  simp [hashTableLeaves]

/-- Verify a single 32-byte Merkle authentication path for `(idx, val)` against `root`. -/
def verifyMerklePath (H : Hash32) (treeSize idx : Nat) (val : Goldilocks)
    (path : List Digest32) (root : Digest32) : Bool :=
  climbMerkle32 H treeSize idx (hashLeaf32 H idx val) path == some root

/-- **Merkle Path Completeness (`verifyMerklePath_completeness`)**:
    For every 32-byte hash `H`, Goldilocks table `tbl`, and in-bounds index `idx < tbl.length`,
    `verifyMerklePath` accepts the honest authentication path against `merkleRoot32`. -/
theorem verifyMerklePath_completeness (H : Hash32) (tbl : List Goldilocks)
    (idx : Nat) (hIdx : idx < tbl.length) :
    verifyMerklePath H tbl.length idx tbl[idx]
      (merklePath32 H (hashTableLeaves H tbl) idx)
      (merkleRoot32 H (hashTableLeaves H tbl)) = true := by
  unfold verifyMerklePath
  rw [beq_iff_eq]
  have hLen : idx < (hashTableLeaves H tbl).length := by
    rw [hashTableLeaves_length]; exact hIdx
  have hClimb := climbMerkle32_merklePath32 H (hashTableLeaves H tbl) idx hLen
  rw [hashTableLeaves_length] at hClimb
  have hLeaf : (hashTableLeaves H tbl)[idx]'hLen = hashLeaf32 H idx tbl[idx] := by
    simp [hashTableLeaves]
  rw [← hLeaf]
  exact hClimb

/-- Single-position Merkle double-opening reduces directly to `Collision H.eval`. -/
theorem verifyMerklePath_double_open_binds (H : Hash32)
    {n idx : Nat} {v₁ v₂ : Goldilocks} {p₁ p₂ : List Digest32} {root : Digest32}
    (hv₁ : verifyMerklePath H n idx v₁ p₁ root = true)
    (hv₂ : verifyMerklePath H n idx v₂ p₂ root = true) :
    v₁ = v₂ ∨ Collision H.eval := by
  simp only [verifyMerklePath, beq_iff_eq] at hv₁ hv₂
  rcases climbMerkle32_binds H p₁ p₂ n idx _ _ root hv₁ hv₂ with hLeaf | hCol
  · exact hashLeaf32_binds H hLeaf
  · exact .inr hCol

/-! ## 4. Concrete `CanopyMerklePCS` over `Goldilocks` -/

/-- Canopy / Merkle multilinear commitment: variable arity + 32-byte Merkle root. -/
structure CanopyCommitment where
  numVars : Nat
  root : Digest32
  deriving DecidableEq

/-- Canopy opening proof: authenticated multilinear table entries `(val, path)` of size $2^v$. -/
structure CanopyOpeningProof where
  entries : List (Goldilocks × List Digest32)
  deriving DecidableEq

/-- `"CANOPY.PCS.OPEN"` transcript absorption label. -/
def canopyOpenLabel : ByteArray :=
  Native.bytesOfList [0x43, 0x41, 0x4e, 0x4f, 0x50, 0x59, 0x2e,
                      0x50, 0x43, 0x53, 0x2e, 0x4f, 0x50, 0x45, 0x4e]

def canopyCommit (H : Hash32) (numVars : Nat) (tbl : List Goldilocks) : CanopyCommitment :=
  { numVars := numVars
    root := merkleRoot32 H (hashTableLeaves H tbl) }

def canopyOpenEval (H : Hash32) (_numVars : Nat) (tbl : List Goldilocks)
    (claim : EvalClaim Goldilocks _numVars) (tr : Transcript .relationBound) :
    CanopyOpeningProof × Transcript .relationBound :=
  let leaves := hashTableLeaves H tbl
  let entries := tbl.mapIdx fun idx x => (x, merklePath32 H leaves idx)
  let root := merkleRoot32 H leaves
  let tr' := absorbMsg canopyOpenLabel
    (encodeFrame root.bytes (encodeGoldilocksBytes claim.expectedVal) ByteArray.empty) tr
  (⟨entries⟩, tr')

def verifyAllIndexedPaths (H : Hash32) (treeSize : Nat) (root : Digest32)
    (entries : List (Goldilocks × List Digest32)) : Bool :=
  (List.finRange entries.length).all fun i =>
    let item := entries[i]
    verifyMerklePath H treeSize i.val item.1 item.2 root

def canopyVerifyEval (H : Hash32) (numVars : Nat) (comm : CanopyCommitment)
    (claim : EvalClaim Goldilocks numVars) (prf : CanopyOpeningProof)
    (tr : Transcript .relationBound) : Bool × Transcript .relationBound :=
  let tr' := absorbMsg canopyOpenLabel
    (encodeFrame comm.root.bytes (encodeGoldilocksBytes claim.expectedVal) ByteArray.empty) tr
  let ok :=
    (comm.numVars == numVars) &&
    (prf.entries.length == 2 ^ numVars) &&
    verifyAllIndexedPaths H (2 ^ numVars) comm.root prf.entries &&
    (mleEval (prf.entries.map Prod.fst) claim.point == claim.expectedVal)
  (ok, tr')

theorem map_fst_honest_entries (H : Hash32) (tbl : List Goldilocks) :
    (tbl.mapIdx fun idx x => (x, merklePath32 H (hashTableLeaves H tbl) idx)).map Prod.fst = tbl := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp

theorem list_diff_at_index {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.length = ys.length → xs ≠ ys →
      ∃ (idx : Nat) (hx : idx < xs.length) (hy : idx < ys.length), xs[idx]'hx ≠ ys[idx]'hy
  | [], [], _, hne => absurd rfl hne
  | x :: xs, y :: ys, hlen, hne => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    by_cases hxy : x = y
    · subst hxy
      have hneTail : xs ≠ ys := fun h => hne (congrArg (x :: ·) h)
      obtain ⟨idx, hx, hy, hdiff⟩ := list_diff_at_index hlen hneTail
      exact ⟨idx + 1, Nat.succ_lt_succ hx, Nat.succ_lt_succ hy, hdiff⟩
    · exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, hxy⟩

/-- **Canopy / Merkle Double-Opening Collision Reduction (`merkle_double_open_yields_hash_collision`)**:
    Any two accepted `CanopyMerklePCS` openings against the same 32-byte commitment `comm` at
    the same evaluation point `c₁.point = c₂.point` claiming `c₁.expectedVal ≠ c₂.expectedVal`
    explicitly yield a 256-bit hash collision `Collision H.eval`. -/
theorem merkle_double_open_yields_hash_collision (H : Hash32)
    {v : Nat} {comm : CanopyCommitment}
    {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : CanopyOpeningProof}
    {tr₁ tr₂ : Transcript .relationBound}
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : (canopyVerifyEval H v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (canopyVerifyEval H v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    Collision H.eval := by
  simp only [canopyVerifyEval, Bool.and_eq_true, beq_iff_eq] at hAcc₁ hAcc₂
  rcases hAcc₁ with ⟨⟨⟨_, hLen₁⟩, hPaths₁⟩, hEval₁⟩
  rcases hAcc₂ with ⟨⟨⟨_, hLen₂⟩, hPaths₂⟩, hEval₂⟩
  let vals₁ := π₁.entries.map Prod.fst
  let vals₂ := π₂.entries.map Prod.fst
  have hValsNe : vals₁ ≠ vals₂ := by
    intro hEq
    dsimp only [vals₁, vals₂] at hEq
    apply hDisagree
    rw [← hEval₁, ← hEval₂, ← hPt, hEq]
  have hValsLen : vals₁.length = vals₂.length := by
    simp [vals₁, vals₂, hLen₁, hLen₂]
  obtain ⟨idx, hIdx₁, hIdx₂, hDiff⟩ := list_diff_at_index hValsLen hValsNe
  have hIn₁ : idx < π₁.entries.length := by simpa [vals₁] using hIdx₁
  have hIn₂ : idx < π₂.entries.length := by simpa [vals₂] using hIdx₂
  simp only [verifyAllIndexedPaths, List.all_eq_true] at hPaths₁ hPaths₂
  have hVer₁ := hPaths₁ ⟨idx, hIn₁⟩ (List.mem_finRange _)
  have hVer₂ := hPaths₂ ⟨idx, hIn₂⟩ (List.mem_finRange _)
  dsimp only at hVer₁ hVer₂
  rcases verifyMerklePath_double_open_binds H hVer₁ hVer₂ with hSame | hCol
  · exfalso
    apply hDiff
    simpa [vals₁, vals₂] using hSame
  · exact hCol

/-- Executable `CanopyMerklePCS` instance over `Goldilocks` in the `.primeField` +
    `.uniqueDecodingRadius` regime, parameterized by `H : Hash32` (default `deployedCanopyHash32`). -/
def canopyMerklePCS (H : Hash32 := deployedCanopyHash32) : MultilinearPCS Goldilocks where
  domainKind := .primeField
  regime := .uniqueDecodingRadius
  validRegime := .primeUDR
  Params := Unit
  Commitment := CanopyCommitment
  OpeningProof := CanopyOpeningProof
  commit _ v tbl := canopyCommit H v tbl
  openEval _ v tbl claim tr := canopyOpenEval H v tbl claim tr
  verifyEval _ v comm claim prf tr := canopyVerifyEval H v comm claim prf tr
  completeness := by
    intro _ v tbl _ _ tr hTblLen
    dsimp only [canopyCommit, canopyOpenEval, canopyVerifyEval]
    simp only [Bool.and_eq_true, beq_iff_eq]
    have hMapFst := map_fst_honest_entries H tbl
    refine ⟨⟨⟨trivial, ?_⟩, ?_⟩, ?_⟩
    · simp [hTblLen]
    · simp only [verifyAllIndexedPaths, List.all_eq_true]
      intro i _
      have hiLen : i.val < tbl.length := by
        have hi := i.isLt
        simp at hi
        exact hi
      rw [← hTblLen]
      simpa [List.getElem_mapIdx] using verifyMerklePath_completeness H tbl i.val hiLen
    · rw [hMapFst]

/-- **Collision-Resistance Implies `BindingSound` (`canopyMerklePCS_bindingSound_of_collisionFree`)**:
    Under `¬ Collision H.eval`, `canopyMerklePCS H` is unconditionally evaluation-binding. -/
theorem canopyMerklePCS_bindingSound_of_collisionFree (H : Hash32)
    (hNoCol : ¬ Collision H.eval) :
    BindingSound (canopyMerklePCS H) := by
  intro _ v comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  exact Classical.byContradiction fun hNe =>
    hNoCol (merkle_double_open_yields_hash_collision H hPt hAcc₁ hAcc₂ hNe)

end Obend.Crypto
end
