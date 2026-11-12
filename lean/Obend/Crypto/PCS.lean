module
/-
# Obend.Crypto.PCS — Proximity-Gap Guard (`2026/2424`), `MultilinearPCS`, `openMerkle` & `CanopyMerklePCS`

Polymorphic multilinear polynomial commitment interface and concrete 256-bit hash-tree backend:
1. **Oct 2026 Binary RS Proximity-Gap Guard (`Dao–Kominers–Thaler–Zheng, ePrint 2026/2424`)**:
   `DomainKind`, `ProximityRegime`, and `ValidProximityConfig` make it a type-level impossibility
   to instantiate a `.binaryAdditive` PCS outside `.uniqueDecodingRadius`.
2. **`MultilinearPCS R`, `BindingSoundAt` & `BindingSound`**:
   Polymorphic commitment, seeded/instance-bound transcript opening (absorbing `(comm, point, expectedVal)`),
   arity-checked completeness, and evaluation-binding soundness.
3. **`CanopyMerklePCS` with `BoundedCollision` & `0 Classical` Witness Extraction**:
   Executable 32-byte `Digest32` cSHAKE256 Merkle commitment and `openMerkle` opening scheme with:
   - `extractCanopyDoubleOpenCollision` (`0 Classical`, `Type`-valued `HashCollisionWitness`),
   - `canopyVerifyEval_binds_point` (proving `claim.point` is cryptographically bound into `Transcript`),
   - non-vacuous `canopyMerklePCS_bindingSoundAt_of_boundedCollisionFree` under `¬ BoundedCollision`,
   - concrete inhabitedness witness `toyInjectiveHash32_no_boundedCollision` proving `¬ BoundedCollision`
     is genuinely satisfiable on bounded preimage domains (eliminating pigeonhole vacuity).
-/
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Judge.Computational

public section
namespace Obend.Crypto

open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Judge.Computational

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

/-! ## 2. Polymorphic `MultilinearPCS R`, `BindingSoundAt`, `BindingSound` & `SparseOneHotCommit` -/

/-- Polymorphic Multilinear Polynomial Commitment Scheme over `[CommRingOps R]`,
    carrying a mandatory type-level `ValidProximityConfig` witness, an explicit arity compatibility
    predicate `ValidArity`, and operating over any seeded `Transcript phase`. -/
structure MultilinearPCS (R : Type) [CommRingOps R] where
  domainKind : DomainKind
  regime : ProximityRegime
  validRegime : ValidProximityConfig domainKind regime
  Params : Type
  Commitment : Type
  OpeningProof : Type
  ValidArity : Params → Nat → Prop
  commit : Params → (numVars : Nat) → List R → Commitment
  openEval : ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase],
    Params → (numVars : Nat) → List R → EvalClaim R numVars →
    Transcript phase → OpeningProof × Transcript phase
  verifyEval : ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase],
    Params → (numVars : Nat) → Commitment → EvalClaim R numVars →
    OpeningProof → Transcript phase → Bool × Transcript phase
  completeness :
    ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase]
      (pp : Params) (v : Nat) (tbl : List R) (pt : List R) (hPt : pt.length = v)
      (tr : Transcript phase),
      ValidArity pp v →
      tbl.length = 2 ^ v →
      let claim : EvalClaim R v := ⟨pt, hPt, mleEval tbl pt⟩
      let (prf, _) := openEval pp v tbl claim tr
      (verifyEval pp v (commit pp v tbl) claim prf tr).1 = true

/-- **Arity-Scoped Evaluation Binding Soundness (`BindingSoundAt`)**:
    At fixed variable count `v`, no commitment `comm` can be opened to two distinct values
    `c₁.expectedVal ≠ c₂.expectedVal` at the same evaluation point `c₁.point = c₂.point`. -/
@[expose] def BindingSoundAt {R : Type} [CommRingOps R] (v : Nat) (P : MultilinearPCS R) : Prop :=
  ∀ {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    (pp : P.Params) (comm : P.Commitment)
    (c₁ c₂ : EvalClaim R v) (π₁ π₂ : P.OpeningProof)
    (tr₁ : Transcript phase₁) (tr₂ : Transcript phase₂),
    c₁.point = c₂.point →
    (P.verifyEval pp v comm c₁ π₁ tr₁).1 = true →
    (P.verifyEval pp v comm c₂ π₂ tr₂).1 = true →
    c₁.expectedVal = c₂.expectedVal

/-- **Global Evaluation Binding Soundness (`BindingSound`)**:
    Evaluation binding across all variable arities `v` accepted by `P.verifyEval`. -/
@[expose] def BindingSound {R : Type} [CommRingOps R] (P : MultilinearPCS R) : Prop :=
  ∀ (v : Nat), BindingSoundAt v P

/-- Dense one-hot multilinear table of length $2^{\text{numVars}}$ with `1` at `idx` and `0` elsewhere. -/
def oneHotTable (R : Type) [CommRingOps R] (numVars idx : Nat) : List R :=
  (List.range (2 ^ numVars)).map fun i =>
    if i = idx then CommRingOps.one else CommRingOps.zero

theorem oneHotTable_length (R : Type) [CommRingOps R] (numVars idx : Nat) :
    (oneHotTable R numVars idx).length = 2 ^ numVars := by
  simp [oneHotTable]

/-- **`Twist & Shout` / `Akita` (`2026/1983`) Sparse One-Hot Commitment Specialization**:
    Allows committing to a 1-hot lookup indicator in $O(1)$ column operations rather than
    $O(2^v)$ dense operations whenever `P.ValidArity pp v` holds. -/
class SparseOneHotCommit (R : Type) [CommRingOps R] (P : MultilinearPCS R) where
  commitOneHot : P.Params → (numVars : Nat) → (idx : Nat) → P.Commitment
  commitOneHot_eq_commit :
    ∀ (pp : P.Params) (v idx : Nat),
      P.ValidArity pp v →
      idx < 2 ^ v →
      commitOneHot pp v idx = P.commit pp v (oneHotTable R v idx)

/-! ## 3. Exact 32-Byte Digest Carrier (`Digest32`), `openMerkle` & Bounded Preimage Extraction -/

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

instance : LawfulTranscriptEncode Digest32 where
  encodeTranscriptBytes d := d.bytes
  encodeTranscriptBytes_injective h := Digest32.ext h

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
@[expose] def deployedCanopyHash32 : Hash32 where
  eval := cshake256Bytes canopyMerkleCustomization
  len_eq input := cshake256Bytes_length canopyMerkleCustomization input

/-- Apply `H : Hash32` to produce a `Digest32`. -/
@[expose] def evalDigest32 (H : Hash32) (preimage : List UInt8) : Digest32 :=
  ⟨Native.bytesOfList (H.eval preimage), by
    rw [Fast.size_eq_length, Native.bytesOfList_toList, H.len_eq]⟩

/-- Constructive `Type`-valued bounded collision extractor for `evalDigest32` (`0 Classical`). -/
def extractEvalDigest32Collision (H : Hash32) {maxBytes : Nat} {p₁ p₂ : List UInt8}
    (hLen₁ : p₁.length ≤ maxBytes) (hLen₂ : p₂.length ≤ maxBytes)
    (hne : p₁ ≠ p₂) (heq : evalDigest32 H p₁ = evalDigest32 H p₂) :
    HashCollisionWitness H.eval maxBytes where
  msgA := p₁
  msgB := p₂
  lenA := hLen₁
  lenB := hLen₂
  distinct := hne
  sameDigest := by
    have hl : (evalDigest32 H p₁).bytes.data.toList = (evalDigest32 H p₂).bytes.data.toList :=
      congrArg (fun d => d.bytes.data.toList) heq
    simp only [evalDigest32, Native.bytesOfList_toList] at hl
    exact congrArg ofBE hl

theorem evalDigest32_eq_imp_collision (H : Hash32) {p₁ p₂ : List UInt8}
    (hne : p₁ ≠ p₂) (heq : evalDigest32 H p₁ = evalDigest32 H p₂) :
    Collision H.eval :=
  (extractEvalDigest32Collision H (Nat.le_max_left p₁.length p₂.length)
    (Nat.le_max_right p₁.length p₂.length) hne heq).toCollision

/-- Tight upper bound on Merkle leaf & internal-node preimage byte lengths for a $2^v$-leaf tree:
    - at $v = 0$ ($2^0 = 1$ leaf, zero internal nodes), only leaf index `0` is hashed (`10` bytes);
    - at $v \ge 1$, internal nodes have `65` bytes and leaves at `idx < 2^v` have `≤ 10 + v` bytes. -/
@[expose] def merkleMaxPreimageBytes : Nat → Nat
  | 0 => 10
  | v + 1 => Nat.max 65 (11 + v)

/-- RFC-6962 / Canopy domain-separated leaf preimage: `0x00 ‖ leb128(idx) ‖ be8(val)`. -/
def merkleLeafPreimage (idx : Nat) (x : Goldilocks) : List UInt8 :=
  (0x00 : UInt8) :: (leb128 idx ++ be 8 x.val)

theorem merkleLeafPreimage_length_le {v idx : Nat} (hIdx : idx < 2 ^ v) (x : Goldilocks) :
    (merkleLeafPreimage idx x).length ≤ merkleMaxPreimageBytes v := by
  have hleb : (leb128 idx).length ≤ v + 1 := leb128_length_le_of_lt_two_pow hIdx
  simp only [merkleLeafPreimage, List.length_cons, List.length_append, length_be]
  cases v with
  | zero =>
    simp only [merkleMaxPreimageBytes]
    omega
  | succ k =>
    simp only [merkleMaxPreimageBytes]
    have hle : (leb128 idx).length + 8 + 1 ≤ 11 + k := by omega
    exact Nat.le_trans hle (Nat.le_max_right _ _)

theorem merkleLeafPreimage_injective {i₁ i₂ : Nat} {x₁ x₂ : Goldilocks}
    (h : merkleLeafPreimage i₁ x₁ = merkleLeafPreimage i₂ x₂) :
    i₁ = i₂ ∧ x₁ = x₂ := by
  simp only [merkleLeafPreimage, List.cons.injEq] at h
  obtain ⟨hi, hbe⟩ := leb128_prefix_inj h.2
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hx := be_injective (h8 ▸ Goldilocks.val_lt_two_pow_64 x₁)
                          (h8 ▸ Goldilocks.val_lt_two_pow_64 x₂) hbe
  exact ⟨hi, Goldilocks.ext hx⟩

/-- Domain-separated internal node preimage: `0x01 ‖ leftBytes(32) ‖ rightBytes(32)` (`65` bytes). -/
def merkleNodePreimage (l r : Digest32) : List UInt8 :=
  (0x01 : UInt8) :: (l.bytes.data.toList ++ r.bytes.data.toList)

theorem merkleNodePreimage_length (l r : Digest32) :
    (merkleNodePreimage l r).length = 65 := by
  simp [merkleNodePreimage, l.toList_length, r.toList_length]

theorem merkleNodePreimage_injective {l₁ r₁ l₂ r₂ : Digest32}
    (h : merkleNodePreimage l₁ r₁ = merkleNodePreimage l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  simp only [merkleNodePreimage, List.cons.injEq] at h
  have hlen : l₁.bytes.data.toList.length = l₂.bytes.data.toList.length := by
    rw [l₁.toList_length, l₂.toList_length]
  obtain ⟨hl, hr⟩ := List.append_inj h.2 hlen
  exact ⟨Digest32.ext (byteArray_eq_of_toList_eq hl),
         Digest32.ext (byteArray_eq_of_toList_eq hr)⟩

@[expose] def hashLeaf32 (H : Hash32) (idx : Nat) (x : Goldilocks) : Digest32 :=
  evalDigest32 H (merkleLeafPreimage idx x)

@[expose] def hashNode32 (H : Hash32) (l r : Digest32) : Digest32 :=
  evalDigest32 H (merkleNodePreimage l r)

def emptyTreeDigest32 (H : Hash32) : Digest32 :=
  evalDigest32 H [0x02]

/-- Balanced binary 32-byte Merkle root over `leaves : List Digest32`. -/
def merkleRoot32 (H : Hash32) (leaves : List Digest32) : Digest32 :=
  if h0 : leaves.isEmpty then emptyTreeDigest32 H
  else if _ : leaves.length < 2 then
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
  if h2 : leaves.length < 2 then
    have h1 : leaves.length = 1 := by omega
    have hIdx0 : idx = 0 := by omega
    subst hIdx0
    match leaves, h1 with
    | [d], _ =>
      rw [merklePath32]
      conv => rhs; rw [merkleRoot32]
      simp [climbMerkle32]
  else
    have hNotEmpty : leaves.isEmpty = false := by
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
    if hi : idx < leaves.length / 2 then
      simp only [hi, ↓reduceIte]
      have hiTake : idx < (leaves.take (leaves.length / 2)).length := by rw [hlt]; exact hi
      have ihL := climbMerkle32_merklePath32 H (leaves.take (leaves.length / 2)) idx hiTake
      rw [hlt, getElem_take_digest leaves hi hiTake] at ihL
      have hBad : (decide (leaves.length < 2) || decide (idx ≥ leaves.length)) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
      simp only [climbMerkle32, hBad, Bool.false_eq_true, ↓reduceIte, hi, ihL, Option.map_some]
    else
      simp only [hi, ↓reduceIte]
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

/-- **Constructive `Type`-Valued Merkle Climb Collision Extractor (`extractClimbMerkleCollision`, `0 Classical`)**:
    Given two valid climbs from distinct leaf digests `leaf₁ ≠ leaf₂` at position `idx` of a
    size-`n` tree to the same `root`, deterministically extracts a `HashCollisionWitness` of length `≤ maxBytes`. -/
def extractClimbMerkleCollision (H : Hash32) {maxBytes : Nat} :
    ∀ (p₁ p₂ : List Digest32) (n idx : Nat) (leaf₁ leaf₂ root : Digest32),
      (2 ≤ n → 65 ≤ maxBytes) →
      leaf₁ ≠ leaf₂ →
      climbMerkle32 H n idx leaf₁ p₁ = some root →
      climbMerkle32 H n idx leaf₂ p₂ = some root →
      HashCollisionWitness H.eval maxBytes
  | [], [], n, idx, leaf₁, leaf₂, _, _, hNe, h₁, h₂ => by
    exfalso
    simp only [climbMerkle32] at h₁ h₂
    split at h₁
    · rename_i hc
      simp only [hc, ↓reduceIte, Option.some.injEq] at h₁ h₂
      exact hNe (h₁.trans h₂.symm)
    · cases h₁
  | [], _ :: _, n, idx, _, _, _, _, _, h₁, h₂ => by
    exfalso
    simp only [climbMerkle32] at h₁ h₂
    split at h₁
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨rfl, _⟩
      simp at h₂
    · cases h₁
  | _ :: _, [], n, idx, _, _, _, _, _, h₁, h₂ => by
    exfalso
    simp only [climbMerkle32] at h₁ h₂
    split at h₂
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨rfl, _⟩
      simp at h₁
    · cases h₂
  | s₁ :: ss₁, s₂ :: ss₂, n, idx, leaf₁, leaf₂, root, hNodeBound, hNe, h₁, h₂ =>
    if hBad : n < 2 || idx ≥ n then
      False.elim (by simp [climbMerkle32, hBad] at h₁)
    else
      have h65 : 65 ≤ maxBytes := hNodeBound (by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hBad
        omega)
      if hi : idx < n / 2 then
        match hc₁ : climbMerkle32 H (n / 2) idx leaf₁ ss₁,
              hc₂ : climbMerkle32 H (n / 2) idx leaf₂ ss₂ with
        | none, _ => False.elim (by simp [climbMerkle32, hBad, hi, hc₁] at h₁)
        | _, none => False.elim (by simp [climbMerkle32, hBad, hi, hc₂] at h₂)
        | some l₁, some l₂ =>
          have hNodeEq : hashNode32 H l₁ s₁ = hashNode32 H l₂ s₂ := by
            simp only [climbMerkle32, hBad, Bool.false_eq_true, ↓reduceIte, hi, hc₁, hc₂,
              Option.map_some, Option.some.injEq] at h₁ h₂
            exact h₁.trans h₂.symm
          if hEqL : l₁ = l₂ then
            extractClimbMerkleCollision H ss₁ ss₂ (n / 2) idx leaf₁ leaf₂ l₁
              (fun _ => h65) hNe hc₁ (hEqL ▸ hc₂)
          else
            extractEvalDigest32Collision H
              (by rw [merkleNodePreimage_length]; exact h65)
              (by rw [merkleNodePreimage_length]; exact h65)
              (fun hpre => hEqL (merkleNodePreimage_injective hpre).1)
              hNodeEq
      else
        match hc₁ : climbMerkle32 H (n - n / 2) (idx - n / 2) leaf₁ ss₁,
              hc₂ : climbMerkle32 H (n - n / 2) (idx - n / 2) leaf₂ ss₂ with
        | none, _ => False.elim (by simp [climbMerkle32, hBad, hi, hc₁] at h₁)
        | _, none => False.elim (by simp [climbMerkle32, hBad, hi, hc₂] at h₂)
        | some r₁, some r₂ =>
          have hNodeEq : hashNode32 H s₁ r₁ = hashNode32 H s₂ r₂ := by
            simp only [climbMerkle32, hBad, Bool.false_eq_true, ↓reduceIte, hi, hc₁, hc₂,
              Option.map_some, Option.some.injEq] at h₁ h₂
            exact h₁.trans h₂.symm
          if hEqR : r₁ = r₂ then
            extractClimbMerkleCollision H ss₁ ss₂ (n - n / 2) (idx - n / 2) leaf₁ leaf₂ r₁
              (fun _ => h65) hNe hc₁ (hEqR ▸ hc₂)
          else
            extractEvalDigest32Collision H
              (by rw [merkleNodePreimage_length]; exact h65)
              (by rw [merkleNodePreimage_length]; exact h65)
              (fun hpre => hEqR (merkleNodePreimage_injective hpre).2)
              hNodeEq

/-- **Merkle Climb Binding (`climbMerkle32_binds`, `0 Classical`)**:
    Two valid climbs from position `idx` of a size-`n` tree to the same `root` either start
    from the exact same leaf `Digest32` or witness a `Collision H.eval`. -/
theorem climbMerkle32_binds (H : Hash32)
    (p₁ p₂ : List Digest32) (n idx : Nat) (leaf₁ leaf₂ root : Digest32)
    (h₁ : climbMerkle32 H n idx leaf₁ p₁ = some root)
    (h₂ : climbMerkle32 H n idx leaf₂ p₂ = some root) :
    leaf₁ = leaf₂ ∨ Collision H.eval := by
  if hEq : leaf₁ = leaf₂ then
    exact .inl hEq
  else
    exact .inr (extractClimbMerkleCollision H (maxBytes := 65) p₁ p₂ n idx leaf₁ leaf₂ root
      (fun _ => Nat.le_refl 65) hEq h₁ h₂).toCollision

/-- Hash a Goldilocks table into indexed 32-byte Merkle leaves. -/
def hashTableLeaves (H : Hash32) (tbl : List Goldilocks) : List Digest32 :=
  tbl.mapIdx fun idx x => hashLeaf32 H idx x

theorem hashTableLeaves_length (H : Hash32) (tbl : List Goldilocks) :
    (hashTableLeaves H tbl).length = tbl.length := by
  simp [hashTableLeaves]

/-- Canonical single-leaf Merkle opening path (`openMerkle`) for `tbl[idx]`. -/
def openMerkle (H : Hash32) (tbl : List Goldilocks) (idx : Nat) : List Digest32 :=
  merklePath32 H (hashTableLeaves H tbl) idx

/-- Verify a single 32-byte Merkle authentication path for `(idx, val)` against `root`. -/
def verifyMerklePath (H : Hash32) (treeSize idx : Nat) (val : Goldilocks)
    (path : List Digest32) (root : Digest32) : Bool :=
  climbMerkle32 H treeSize idx (hashLeaf32 H idx val) path == some root

/-- **Merkle Path Completeness (`verifyMerklePath_completeness`)**:
    For every 32-byte hash `H`, Goldilocks table `tbl`, and in-bounds index `idx < tbl.length`,
    `verifyMerklePath` accepts `openMerkle H tbl idx` against `merkleRoot32`. -/
theorem verifyMerklePath_completeness (H : Hash32) (tbl : List Goldilocks)
    (idx : Nat) (hIdx : idx < tbl.length) :
    verifyMerklePath H tbl.length idx tbl[idx]
      (openMerkle H tbl idx)
      (merkleRoot32 H (hashTableLeaves H tbl)) = true := by
  unfold verifyMerklePath openMerkle
  rw [beq_iff_eq]
  have hLen : idx < (hashTableLeaves H tbl).length := by
    rw [hashTableLeaves_length]; exact hIdx
  have hClimb := climbMerkle32_merklePath32 H (hashTableLeaves H tbl) idx hLen
  rw [hashTableLeaves_length] at hClimb
  have hLeaf : (hashTableLeaves H tbl)[idx]'hLen = hashLeaf32 H idx tbl[idx] := by
    simp [hashTableLeaves]
  rw [← hLeaf]
  exact hClimb

/-- **Constructive Single-Leaf Merkle Collision Extractor (`extractMerklePathCollision`, `0 Classical`)**:
    Two valid Merkle authentication paths for distinct values `v₁ ≠ v₂` at index `idx < 2 ^ v`
    against the same `root` deterministically produce a `HashCollisionWitness H.eval (merkleMaxPreimageBytes v)`. -/
def extractMerklePathCollision (H : Hash32) {v idx : Nat} (hIdx : idx < 2 ^ v)
    {v₁ v₂ : Goldilocks} (p₁ p₂ : List Digest32) (root : Digest32)
    (hNe : v₁ ≠ v₂)
    (hv₁ : verifyMerklePath H (2 ^ v) idx v₁ p₁ root = true)
    (hv₂ : verifyMerklePath H (2 ^ v) idx v₂ p₂ root = true) :
    HashCollisionWitness H.eval (merkleMaxPreimageBytes v) :=
  if hLeafEq : hashLeaf32 H idx v₁ = hashLeaf32 H idx v₂ then
    extractEvalDigest32Collision H
      (merkleLeafPreimage_length_le hIdx v₁)
      (merkleLeafPreimage_length_le hIdx v₂)
      (fun hpre => hNe (merkleLeafPreimage_injective hpre).2)
      hLeafEq
  else
    have hNodeBound : 2 ≤ 2 ^ v → 65 ≤ merkleMaxPreimageBytes v := by
      cases v with
      | zero => intro h; omega
      | succ k => intro _; exact Nat.le_max_left 65 (11 + k)
    extractClimbMerkleCollision H p₁ p₂ (2 ^ v) idx
      (hashLeaf32 H idx v₁) (hashLeaf32 H idx v₂) root
      hNodeBound hLeafEq
      (by simpa [verifyMerklePath, beq_iff_eq] using hv₁)
      (by simpa [verifyMerklePath, beq_iff_eq] using hv₂)

/-! ## 4. Concrete `CanopyMerklePCS` over `Goldilocks` with Point Binding & Non-Vacuity Witness -/

/-- Canopy / Merkle multilinear commitment: variable arity + 32-byte Merkle root. -/
structure CanopyCommitment where
  numVars : Nat
  root : Digest32
  deriving DecidableEq

instance : LawfulTranscriptEncode CanopyCommitment where
  encodeTranscriptBytes c := TranscriptEncode.encodeTranscriptBytes (c.numVars, c.root)
  encodeTranscriptBytes_injective {c₁ c₂} h := by
    have hp := LawfulTranscriptEncode.encodeTranscriptBytes_injective (ι := Nat × Digest32) h
    cases c₁; cases c₂
    simp only [Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    rfl

/-- Canopy opening proof: authenticated multilinear table entries `(val, path)` of size $2^v$. -/
structure CanopyOpeningProof where
  entries : List (Goldilocks × List Digest32)
  deriving DecidableEq

/-- `"CANOPY.PCS.OPEN"` transcript absorption label. -/
def canopyOpenLabel : ByteArray :=
  Native.bytesOfList [0x43, 0x41, 0x4e, 0x4f, 0x50, 0x59, 0x2e,
                      0x50, 0x43, 0x53, 0x2e, 0x4f, 0x50, 0x45, 0x4e]

/-- Canonical 3-field frame absorbed by `CanopyMerklePCS` during opening & verification:
    binds `(root.bytes, encodePointBytes claim.point, encodeGoldilocksBytes claim.expectedVal)`. -/
def canopyOpenFrame {numVars : Nat} (root : Digest32) (claim : EvalClaim Goldilocks numVars) :
    ByteArray :=
  encodeFrame root.bytes (encodePointBytes claim.point) (encodeGoldilocksBytes claim.expectedVal)

theorem canopyOpenFrame_injective {v₁ v₂ : Nat} {r₁ r₂ : Digest32}
    {c₁ : EvalClaim Goldilocks v₁} {c₂ : EvalClaim Goldilocks v₂}
    (h : canopyOpenFrame r₁ c₁ = canopyOpenFrame r₂ c₂) :
    r₁ = r₂ ∧ c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal := by
  obtain ⟨hr, hpt, hval⟩ := encodeFrame_injective h
  exact ⟨Digest32.ext hr, encodePointBytes_injective hpt, encodeGoldilocksBytes_injective hval⟩

def canopyCommit (H : Hash32) (numVars : Nat) (tbl : List Goldilocks) : CanopyCommitment :=
  { numVars := numVars
    root := merkleRoot32 H (hashTableLeaves H tbl) }

theorem verifyMerklePath_openMerkle (H : Hash32) (v : Nat) (tbl : List Goldilocks)
    (hTbl : tbl.length = 2 ^ v) (idx : Nat) (hIdx : idx < 2 ^ v) :
    verifyMerklePath H (2 ^ v) idx (tbl[idx]'(by rw [hTbl]; exact hIdx))
      (openMerkle H tbl idx) (canopyCommit H v tbl).root = true := by
  have h := verifyMerklePath_completeness H tbl idx (by rw [hTbl]; exact hIdx)
  simpa [canopyCommit, hTbl] using h

def canopyOpenEval (H : Hash32) {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (numVars : Nat) (tbl : List Goldilocks)
    (claim : EvalClaim Goldilocks numVars) (tr : Transcript phase) :
    CanopyOpeningProof × Transcript phase :=
  let leaves := hashTableLeaves H tbl
  let entries := tbl.mapIdx fun idx x => (x, merklePath32 H leaves idx)
  let root := merkleRoot32 H leaves
  let tr' := absorbMsg canopyOpenLabel (canopyOpenFrame root claim) tr
  (⟨entries⟩, tr')

def verifyAllIndexedPaths (H : Hash32) (treeSize : Nat) (root : Digest32)
    (entries : List (Goldilocks × List Digest32)) : Bool :=
  (List.finRange entries.length).all fun i =>
    let item := entries[i]
    verifyMerklePath H treeSize i.val item.1 item.2 root

def canopyVerifyEval (H : Hash32) {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (numVars : Nat) (comm : CanopyCommitment)
    (claim : EvalClaim Goldilocks numVars) (prf : CanopyOpeningProof)
    (tr : Transcript phase) : Bool × Transcript phase :=
  let tr' := absorbMsg canopyOpenLabel (canopyOpenFrame comm.root claim) tr
  let ok :=
    (comm.numVars == numVars) &&
    (prf.entries.length == 2 ^ numVars) &&
    verifyAllIndexedPaths H (2 ^ numVars) comm.root prf.entries &&
    (mleEval (prf.entries.map Prod.fst) claim.point == claim.expectedVal)
  (ok, tr')

/-- **Point-Binding Theorem for `canopyVerifyEval` (`canopyVerifyEval_binds_point`)**:
    Two `canopyVerifyEval` runs yielding identical output sponge states either bound the exact
    same `(tr, comm.root, claim.point, claim.expectedVal)` tuple or witness a bounded cSHAKE256 collision. -/
theorem canopyVerifyEval_binds_point (H : Hash32)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {v₁ v₂ : Nat} {comm₁ comm₂ : CanopyCommitment}
    {c₁ : EvalClaim Goldilocks v₁} {c₂ : EvalClaim Goldilocks v₂}
    {π₁ π₂ : CanopyOpeningProof} {tr₁ tr₂ : Transcript phase}
    (hState : (canopyVerifyEval H v₁ comm₁ c₁ π₁ tr₁).2.state =
              (canopyVerifyEval H v₂ comm₂ c₂ π₂ tr₂).2.state) :
    (tr₁ = tr₂ ∧ comm₁.root = comm₂.root ∧ c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal) ∨
    BoundedCollision (cshake256Bytes fsAbsorbCustomization)
      (Nat.max
        (encodeFrameList tr₁.state.data.toList canopyOpenLabel.data.toList
          (leb128 tr₁.stepCount ++ (canopyOpenFrame comm₁.root c₁).data.toList)).length
        (encodeFrameList tr₂.state.data.toList canopyOpenLabel.data.toList
          (leb128 tr₂.stepCount ++ (canopyOpenFrame comm₂.root c₂).data.toList)).length) := by
  cases extractAbsorbMsgOrEq canopyOpenLabel (canopyOpenFrame comm₁.root c₁)
      canopyOpenLabel (canopyOpenFrame comm₂.root c₂) tr₁ tr₂ hState with
  | inl heq =>
    obtain ⟨hr, hpt, hval⟩ := canopyOpenFrame_injective heq.2.2
    exact .inl ⟨heq.1, hr, hpt, hval⟩
  | inr w => exact .inr ⟨w⟩

theorem map_fst_honest_entries (H : Hash32) (tbl : List Goldilocks) :
    (tbl.mapIdx fun idx x => (x, merklePath32 H (hashTableLeaves H tbl) idx)).map Prod.fst = tbl := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp

/-- Constructive `Type`-valued finder returning the first index where two equal-length lists differ (`0 Classical`). -/
def findDiffIndex {α : Type} [DecidableEq α] :
    ∀ (xs ys : List α), xs.length = ys.length → xs ≠ ys →
      { idx : Nat // ∃ (hx : idx < xs.length) (hy : idx < ys.length), xs[idx]'hx ≠ ys[idx]'hy }
  | [], [], _, hne => False.elim (hne rfl)
  | x :: xs, y :: ys, hlen, hne =>
    if hxy : x = y then
      let sub := findDiffIndex xs ys (Nat.succ.inj hlen) (fun h => hne (by rw [hxy, h]))
      ⟨sub.1 + 1, by
        obtain ⟨hx, hy, hdiff⟩ := sub.2
        exact ⟨Nat.succ_lt_succ hx, Nat.succ_lt_succ hy, hdiff⟩⟩
    else
      ⟨0, ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _, hxy⟩⟩

/-- **Constructive Canopy Double-Opening Collision Extractor (`extractCanopyDoubleOpenCollision`, `0 Classical`)**:
    Deterministically computes a `HashCollisionWitness H.eval (merkleMaxPreimageBytes v)` from any
    two accepted `canopyVerifyEval` openings at `c₁.point = c₂.point` claiming `c₁.expectedVal ≠ c₂.expectedVal`. -/
def extractCanopyDoubleOpenCollision (H : Hash32)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    {v : Nat} {comm : CanopyCommitment}
    {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : CanopyOpeningProof}
    {tr₁ : Transcript phase₁} {tr₂ : Transcript phase₂}
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : (canopyVerifyEval H v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (canopyVerifyEval H v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    HashCollisionWitness H.eval (merkleMaxPreimageBytes v) :=
  let vals₁ := π₁.entries.map Prod.fst
  let vals₂ := π₂.entries.map Prod.fst
  have hFacts :
      π₁.entries.length = 2 ^ v ∧
      π₂.entries.length = 2 ^ v ∧
      verifyAllIndexedPaths H (2 ^ v) comm.root π₁.entries = true ∧
      verifyAllIndexedPaths H (2 ^ v) comm.root π₂.entries = true ∧
      vals₁ ≠ vals₂ := by
    simp only [canopyVerifyEval, Bool.and_eq_true, beq_iff_eq] at hAcc₁ hAcc₂
    rcases hAcc₁ with ⟨⟨⟨_, hLen₁⟩, hPaths₁⟩, hEval₁⟩
    rcases hAcc₂ with ⟨⟨⟨_, hLen₂⟩, hPaths₂⟩, hEval₂⟩
    refine ⟨hLen₁, hLen₂, hPaths₁, hPaths₂, fun hEq => hDisagree ?_⟩
    dsimp only [vals₁, vals₂] at hEq
    rw [← hEval₁, ← hEval₂, ← hPt, hEq]
  have hValsLen : vals₁.length = vals₂.length := by
    simp [vals₁, vals₂, hFacts.1, hFacts.2.1]
  let diff := findDiffIndex vals₁ vals₂ hValsLen hFacts.2.2.2.2
  let idx := diff.1
  have hIdxPow : idx < 2 ^ v := by
    obtain ⟨hx, _, _⟩ := diff.2
    simpa [vals₁, hFacts.1] using hx
  have hIn₁ : idx < π₁.entries.length := by rw [hFacts.1]; exact hIdxPow
  have hIn₂ : idx < π₂.entries.length := by rw [hFacts.2.1]; exact hIdxPow
  have hNeAt : (π₁.entries[idx]'hIn₁).1 ≠ (π₂.entries[idx]'hIn₂).1 := by
    obtain ⟨_, _, hne⟩ := diff.2
    simpa [vals₁, vals₂, idx] using hne
  have hVer₁ : verifyMerklePath H (2 ^ v) idx (π₁.entries[idx]'hIn₁).1
      (π₁.entries[idx]'hIn₁).2 comm.root = true := by
    have hAll := hFacts.2.2.1
    simp only [verifyAllIndexedPaths, List.all_eq_true] at hAll
    exact hAll ⟨idx, hIn₁⟩ (List.mem_finRange _)
  have hVer₂ : verifyMerklePath H (2 ^ v) idx (π₂.entries[idx]'hIn₂).1
      (π₂.entries[idx]'hIn₂).2 comm.root = true := by
    have hAll := hFacts.2.2.2.1
    simp only [verifyAllIndexedPaths, List.all_eq_true] at hAll
    exact hAll ⟨idx, hIn₂⟩ (List.mem_finRange _)
  extractMerklePathCollision H hIdxPow
    (π₁.entries[idx]'hIn₁).2 (π₂.entries[idx]'hIn₂).2 comm.root hNeAt hVer₁ hVer₂

/-- **Constructive Cross-Table `openMerkle` Collision Extractor (`extractCanopyOpenMerkleCollision`, `0 Classical`)**:
    Given an honest table `tbl` (`tbl.length = 2 ^ v`) and ANY accepted `canopyVerifyEval` proof `π`
    against `comm = canopyCommit H v tbl` whose opened entries disagree with `tbl`, deterministically
    computes a `HashCollisionWitness H.eval (merkleMaxPreimageBytes v)` against `openMerkle H tbl`. -/
def extractCanopyOpenMerkleCollision (H : Hash32)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {v : Nat} (tbl : List Goldilocks) (hTbl : tbl.length = 2 ^ v)
    {c : EvalClaim Goldilocks v} (π : CanopyOpeningProof) (tr : Transcript phase)
    (hAcc : (canopyVerifyEval H v (canopyCommit H v tbl) c π tr).1 = true)
    (hTblNe : π.entries.map Prod.fst ≠ tbl) :
    HashCollisionWitness H.eval (merkleMaxPreimageBytes v) :=
  let vals := π.entries.map Prod.fst
  have hFacts :
      π.entries.length = 2 ^ v ∧
      verifyAllIndexedPaths H (2 ^ v) (canopyCommit H v tbl).root π.entries = true := by
    simp only [canopyVerifyEval, Bool.and_eq_true, beq_iff_eq] at hAcc
    exact ⟨hAcc.1.1.2, hAcc.1.2⟩
  have hValsLen : vals.length = tbl.length := by
    simp [vals, hFacts.1, hTbl]
  let diff := findDiffIndex vals tbl hValsLen hTblNe
  let idx := diff.1
  have hIdxPow : idx < 2 ^ v := by
    obtain ⟨_, hy, _⟩ := diff.2
    simpa [hTbl] using hy
  have hIn : idx < π.entries.length := by rw [hFacts.1]; exact hIdxPow
  have hInTbl : idx < tbl.length := by rw [hTbl]; exact hIdxPow
  have hNeAt : (π.entries[idx]'hIn).1 ≠ tbl[idx]'hInTbl := by
    obtain ⟨_, _, hne⟩ := diff.2
    simpa [vals, idx] using hne
  have hVerPrf : verifyMerklePath H (2 ^ v) idx (π.entries[idx]'hIn).1
      (π.entries[idx]'hIn).2 (canopyCommit H v tbl).root = true := by
    have hAll := hFacts.2
    simp only [verifyAllIndexedPaths, List.all_eq_true] at hAll
    exact hAll ⟨idx, hIn⟩ (List.mem_finRange _)
  have hVerHonest := verifyMerklePath_openMerkle H v tbl hTbl idx hIdxPow
  extractMerklePathCollision H hIdxPow
    (π.entries[idx]'hIn).2 (openMerkle H tbl idx) (canopyCommit H v tbl).root
    hNeAt hVerPrf hVerHonest

/-- **Canopy / Merkle Double-Opening Bounded Collision Reduction (`merkle_double_open_yields_bounded_collision`)**:
    Any two accepted `CanopyMerklePCS` openings at `c₁.point = c₂.point` claiming distinct values
    yield `BoundedCollision H.eval (merkleMaxPreimageBytes v)`. -/
theorem merkle_double_open_yields_bounded_collision (H : Hash32)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    {v : Nat} {comm : CanopyCommitment}
    {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : CanopyOpeningProof}
    {tr₁ : Transcript phase₁} {tr₂ : Transcript phase₂}
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : (canopyVerifyEval H v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (canopyVerifyEval H v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    BoundedCollision H.eval (merkleMaxPreimageBytes v) :=
  ⟨extractCanopyDoubleOpenCollision H hPt hAcc₁ hAcc₂ hDisagree⟩

/-- Backwards-compatible global collision corollary (`BoundedCollision → Collision`). -/
theorem merkle_double_open_yields_hash_collision (H : Hash32)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    {v : Nat} {comm : CanopyCommitment}
    {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : CanopyOpeningProof}
    {tr₁ : Transcript phase₁} {tr₂ : Transcript phase₂}
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : (canopyVerifyEval H v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (canopyVerifyEval H v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    Collision H.eval :=
  (extractCanopyDoubleOpenCollision H hPt hAcc₁ hAcc₂ hDisagree).toCollision

theorem canopyMerklePCS_complete_aux (H : Hash32) :
    ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase]
      (_ : Unit) (v : Nat) (tbl : List Goldilocks)
      (pt : List Goldilocks) (hPt : pt.length = v) (tr : Transcript phase),
      True → tbl.length = 2 ^ v →
      let claim : EvalClaim Goldilocks v := ⟨pt, hPt, mleEval tbl pt⟩
      let (prf, _) := canopyOpenEval H v tbl claim tr
      (canopyVerifyEval H v (canopyCommit H v tbl) claim prf tr).1 = true := by
  intro _ _ _ v tbl _ _ tr _ hTblLen
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
    simpa [List.getElem_mapIdx, openMerkle] using verifyMerklePath_completeness H tbl i.val hiLen
  · rw [hMapFst]

/-- Executable `CanopyMerklePCS` instance over `Goldilocks` in the `.primeField` +
    `.uniqueDecodingRadius` regime, parameterized by `H : Hash32` (default `deployedCanopyHash32`). -/
@[expose, instance_reducible] def canopyMerklePCS (H : Hash32 := deployedCanopyHash32) : MultilinearPCS Goldilocks where
  domainKind := .primeField
  regime := .uniqueDecodingRadius
  validRegime := .primeUDR
  Params := Unit
  Commitment := CanopyCommitment
  OpeningProof := CanopyOpeningProof
  ValidArity _ _ := True
  commit _ v tbl := canopyCommit H v tbl
  openEval _ v tbl claim tr := canopyOpenEval H v tbl claim tr
  verifyEval _ v comm claim prf tr := canopyVerifyEval H v comm claim prf tr
  completeness := canopyMerklePCS_complete_aux H

instance (H : Hash32) : LawfulTranscriptEncode (canopyMerklePCS H).Commitment :=
  inferInstanceAs (LawfulTranscriptEncode CanopyCommitment)

/-- **Non-Vacuous Bounded Collision-Resistance Implies `BindingSoundAt` (`0 Classical`)**:
    Under `¬ BoundedCollision H.eval (merkleMaxPreimageBytes v)`, `canopyMerklePCS H` is
    evaluation-binding at arity `v` with zero classical axioms. -/
theorem canopyMerklePCS_bindingSoundAt_of_boundedCollisionFree (H : Hash32) (v : Nat)
    (hNoCol : ¬ BoundedCollision H.eval (merkleMaxPreimageBytes v)) :
    BindingSoundAt v (canopyMerklePCS H) := by
  intro _ _ _ _ _ comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  if hEq : c₁.expectedVal = c₂.expectedVal then
    exact hEq
  else
    exact False.elim (hNoCol ⟨extractCanopyDoubleOpenCollision H hPt hAcc₁ hAcc₂ hEq⟩)

/-- Predicate-indexed `BindingSound` corollary for `canopyMerklePCS H` (`0 Classical`). -/
theorem canopyMerklePCS_bindingSound_of_collisionFree (H : Hash32)
    (hNoCol : ∀ v : Nat, ¬ BoundedCollision H.eval (merkleMaxPreimageBytes v)) :
    BindingSound (canopyMerklePCS H) := fun v =>
  canopyMerklePCS_bindingSoundAt_of_boundedCollisionFree H v (hNoCol v)

/-! ## 5. Concrete Inhabitedness Witness Proving `¬ BoundedCollision` Is Non-Vacuous -/

/-- Explicit injective 32-byte length-padded identity map on inputs of length `≤ 31` bytes:
    proves `¬ BoundedCollision H.eval maxBytes` (`maxBytes ≤ 31`, including `merkleMaxPreimageBytes 0 = 10`)
    is genuinely satisfiable without pigeonhole contradiction. -/
def toyInjectiveHash32 : Hash32 where
  eval input :=
    if input.length ≤ 31 then
      UInt8.ofNat input.length :: (input ++ List.replicate (31 - input.length) (0 : UInt8))
    else
      List.replicate 32 (0xff : UInt8)
  len_eq input := by
    split
    · rename_i hle
      simp only [List.length_cons, List.length_append, List.length_replicate]
      omega
    · simp

private theorem be_ofBE_reverse_aux :
    ∀ (ys : List UInt8), be ys.reverse.length (ofBE ys.reverse) = ys.reverse
  | [] => rfl
  | last :: revInit => by
    simp only [List.reverse_cons, List.length_append, List.length_singleton, ofBE_append_single, be]
    have hlt : last.toNat < 256 := last.toNat_lt
    have hdiv : (ofBE revInit.reverse * 256 + last.toNat) / 256 = ofBE revInit.reverse := by omega
    have hmod : (ofBE revInit.reverse * 256 + last.toNat) % 256 = last.toNat := by omega
    have hu8 : UInt8.ofNat last.toNat = last := UInt8.ofNat_toNat
    rw [hdiv, hmod, be_ofBE_reverse_aux revInit, hu8]

private theorem be_ofBE_roundtrip (xs : List UInt8) : be xs.length (ofBE xs) = xs := by
  have h := be_ofBE_reverse_aux xs.reverse
  rwa [List.reverse_reverse] at h

private theorem ofBE_injective_of_length_eq {xs ys : List UInt8}
    (hlen : xs.length = ys.length) (heq : ofBE xs = ofBE ys) : xs = ys := by
  rw [← be_ofBE_roundtrip xs, ← be_ofBE_roundtrip ys, hlen, heq]

/-- **Inhabitedness / Non-Vacuity Theorem (`toyInjectiveHash32_no_boundedCollision`)**:
    For every `maxBytes ≤ 31`, `¬ BoundedCollision toyInjectiveHash32.eval maxBytes` holds unconditionally,
    and hence `BindingSoundAt 0 (canopyMerklePCS toyInjectiveHash32)` is constructively inhabited! -/
theorem toyInjectiveHash32_no_boundedCollision {maxBytes : Nat} (hMax : maxBytes ≤ 31) :
    ¬ BoundedCollision toyInjectiveHash32.eval maxBytes := by
  rintro ⟨w⟩
  have ha31 : w.msgA.length ≤ 31 := Nat.le_trans w.lenA hMax
  have hb31 : w.msgB.length ≤ 31 := Nat.le_trans w.lenB hMax
  have hOutEq : toyInjectiveHash32.eval w.msgA = toyInjectiveHash32.eval w.msgB :=
    ofBE_injective_of_length_eq
      ((toyInjectiveHash32.len_eq w.msgA).trans (toyInjectiveHash32.len_eq w.msgB).symm)
      w.sameDigest
  simp only [toyInjectiveHash32, ha31, hb31, ↓reduceIte, List.cons.injEq] at hOutEq
  have hLenEq : w.msgA.length = w.msgB.length := by
    have hb := congrArg UInt8.toNat hOutEq.1
    rw [uint8_toNat_lt_256_of_lt (by omega), uint8_toNat_lt_256_of_lt (by omega)] at hb
    exact hb
  have hMsgEq : w.msgA = w.msgB := (List.append_inj hOutEq.2 hLenEq).1
  exact w.distinct hMsgEq

example : BindingSoundAt 0 (canopyMerklePCS toyInjectiveHash32) :=
  canopyMerklePCS_bindingSoundAt_of_boundedCollisionFree toyInjectiveHash32 0
    (toyInjectiveHash32_no_boundedCollision (by decide))

end Obend.Crypto
end
