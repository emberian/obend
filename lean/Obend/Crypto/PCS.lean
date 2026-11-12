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
public import Obend.Crypto.GameSoundness
import all Obend.Crypto.GameSoundness

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

/-- **Constructive `Type`-Valued Merkle Climb Extractor (`climbMerkle32_bindsOrCollides`, `0 Classical`)**:
    Two valid climbs from position `idx` of a size-`n` tree to the same `root` constructively return
    either `leaf₁ = leaf₂` or a `HashCollisionWitness H.eval 65` without unkeyed `Prop` vacuity. -/
def climbMerkle32_bindsOrCollides (H : Hash32)
    (p₁ p₂ : List Digest32) (n idx : Nat) (leaf₁ leaf₂ root : Digest32)
    (h₁ : climbMerkle32 H n idx leaf₁ p₁ = some root)
    (h₂ : climbMerkle32 H n idx leaf₂ p₂ = some root) :
    PSum (leaf₁ = leaf₂) (HashCollisionWitness H.eval 65) :=
  if hEq : leaf₁ = leaf₂ then
    .inl hEq
  else
    .inr (extractClimbMerkleCollision H (maxBytes := 65) p₁ p₂ n idx leaf₁ leaf₂ root
      (fun _ => Nat.le_refl 65) hEq h₁ h₂)

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

/-- Exact transcript frame hashed by `canopyVerifyEval` during `absorbMsg`. -/
def canopyAbsorbFrameList {phase : TranscriptPhase} {v : Nat}
    (comm : CanopyCommitment) (claim : EvalClaim Goldilocks v) (tr : Transcript phase) : List UInt8 :=
  encodeFrameList tr.state.data.toList canopyOpenLabel.data.toList
    (leb128 tr.stepCount ++ (canopyOpenFrame comm.root claim).data.toList)

/-- **Constructive `0 Classical` Point-Binding Extractor (`extractCanopyVerifyEvalPointOrCollision`)**: -/
def extractCanopyVerifyEvalPointOrCollision (H : Hash32)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {v₁ v₂ : Nat} (comm₁ comm₂ : CanopyCommitment)
    (c₁ : EvalClaim Goldilocks v₁) (c₂ : EvalClaim Goldilocks v₂)
    (π₁ π₂ : CanopyOpeningProof) (tr₁ tr₂ : Transcript phase)
    (hState : (canopyVerifyEval H v₁ comm₁ c₁ π₁ tr₁).2.state =
              (canopyVerifyEval H v₂ comm₂ c₂ π₂ tr₂).2.state) :
    PSum
      (tr₁ = tr₂ ∧ comm₁.root = comm₂.root ∧ c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal)
      { p : List UInt8 × List UInt8 //
        p.1 = canopyAbsorbFrameList comm₁ c₁ tr₁ ∧
        p.2 = canopyAbsorbFrameList comm₂ c₂ tr₂ ∧
        p.1 ≠ p.2 ∧
        cshake256Bytes fsAbsorbCustomization p.1 = cshake256Bytes fsAbsorbCustomization p.2 } :=
  let f₁ := canopyAbsorbFrameList comm₁ c₁ tr₁
  let f₂ := canopyAbsorbFrameList comm₂ c₂ tr₂
  if hf : f₁ = f₂ then
    .inl (by
      obtain ⟨hSt, _, hTail⟩ := encodeFrameList_injective hf
      obtain ⟨hCnt, hOpen⟩ := leb128_prefix_inj hTail
      have hTr : tr₁ = tr₂ := by
        cases tr₁; cases tr₂
        have hs := byteArray_eq_of_toList_eq hSt
        simp only at hs hCnt; subst hs hCnt; rfl
      obtain ⟨hr, hpt, hval⟩ := canopyOpenFrame_injective (byteArray_eq_of_toList_eq hOpen)
      exact ⟨hTr, hr, hpt, hval⟩)
  else
    .inr ⟨(f₁, f₂), rfl, rfl, hf, by
      dsimp only [canopyVerifyEval] at hState
      rw [absorbMsg_state_eq, absorbMsg_state_eq] at hState
      have hl := congrArg (fun b => b.data.toList) hState
      dsimp only [f₁, f₂, canopyAbsorbFrameList]
      simpa only [cshake32ByteArray, Native.bytesOfList_toList] using hl⟩

/-- **Point-Binding Theorem for `canopyVerifyEval` (`canopyVerifyEval_binds_point`)**:
    Two `canopyVerifyEval` runs yielding identical output sponge states either bound the exact
    same `(tr, comm.root, claim.point, claim.expectedVal)` tuple or those two specific transcript
    frames collide under `cshake256Bytes fsAbsorbCustomization` (zero pigeonhole vacuity). -/
theorem canopyVerifyEval_binds_point (H : Hash32)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {v₁ v₂ : Nat} {comm₁ comm₂ : CanopyCommitment}
    {c₁ : EvalClaim Goldilocks v₁} {c₂ : EvalClaim Goldilocks v₂}
    {π₁ π₂ : CanopyOpeningProof} {tr₁ tr₂ : Transcript phase}
    (hState : (canopyVerifyEval H v₁ comm₁ c₁ π₁ tr₁).2.state =
              (canopyVerifyEval H v₂ comm₂ c₂ π₂ tr₂).2.state) :
    (tr₁ = tr₂ ∧ comm₁.root = comm₂.root ∧ c₁.point = c₂.point ∧ c₁.expectedVal = c₂.expectedVal) ∨
    (canopyAbsorbFrameList comm₁ c₁ tr₁ ≠ canopyAbsorbFrameList comm₂ c₂ tr₂ ∧
      cshake256Bytes fsAbsorbCustomization (canopyAbsorbFrameList comm₁ c₁ tr₁) =
        cshake256Bytes fsAbsorbCustomization (canopyAbsorbFrameList comm₂ c₂ tr₂)) := by
  cases extractCanopyVerifyEvalPointOrCollision H comm₁ comm₂ c₁ c₂ π₁ π₂ tr₁ tr₂ hState with
  | inl hEq => exact .inl hEq
  | inr w =>
    rcases w with ⟨⟨_, _⟩, hp₁, hp₂, hNe, hHash⟩
    dsimp only at hp₁ hp₂ hNe hHash
    rw [hp₁, hp₂] at hNe hHash
    exact .inr ⟨hNe, hHash⟩

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

/-- Exact list of 65-byte internal-node preimages hashed along a `climbMerkle32` path. -/
def climbMerkleFrames (H : Hash32) :
    List Digest32 → Nat → Nat → Digest32 → List (List UInt8)
  | [], _, _, _ => []
  | s :: ss, n, idx, leaf =>
    if n < 2 || idx ≥ n then []
    else if idx < n / 2 then
      match climbMerkle32 H (n / 2) idx leaf ss with
      | none => []
      | some l => merkleNodePreimage l s :: climbMerkleFrames H ss (n / 2) idx leaf
    else
      match climbMerkle32 H (n - n / 2) (idx - n / 2) leaf ss with
      | none => []
      | some r => merkleNodePreimage s r :: climbMerkleFrames H ss (n - n / 2) (idx - n / 2) leaf

/-- Exact leaf + internal-node preimage frames hashed by `verifyMerklePath H n idx val path`. -/
def merkleEntryFrames (H : Hash32) (n idx : Nat) (val : Goldilocks) (path : List Digest32) :
    List (List UInt8) :=
  merkleLeafPreimage idx val :: climbMerkleFrames H path n idx (hashLeaf32 H idx val)

/-- Exact finite set of hash preimage frames queried by `canopyVerifyEval H v comm c π tr`. -/
def canopyOpeningFrames (H : Hash32) (v : Nat) (π : CanopyOpeningProof) : List (List UInt8) :=
  (List.finRange π.entries.length).flatMap fun i =>
    merkleEntryFrames H (2 ^ v) i.val (π.entries[i]).1 (π.entries[i]).2

private theorem extractClimbMerkleCollision_mem_frames (H : Hash32) {maxBytes : Nat} :
    ∀ (p₁ p₂ : List Digest32) (n idx : Nat) (leaf₁ leaf₂ root : Digest32)
      (hNodeBound : 2 ≤ n → 65 ≤ maxBytes) (hNe : leaf₁ ≠ leaf₂)
      (h₁ : climbMerkle32 H n idx leaf₁ p₁ = some root)
      (h₂ : climbMerkle32 H n idx leaf₂ p₂ = some root),
      let w := extractClimbMerkleCollision H p₁ p₂ n idx leaf₁ leaf₂ root hNodeBound hNe h₁ h₂
      w.msgA ∈ climbMerkleFrames H p₁ n idx leaf₁ ∧
      w.msgB ∈ climbMerkleFrames H p₂ n idx leaf₂
  | [], [], n, idx, leaf₁, leaf₂, _, _, hNe, h₁, h₂ => by
    exfalso
    simp only [climbMerkle32] at h₁ h₂
    split at h₁
    · rename_i hc; simp only [hc, ↓reduceIte, Option.some.injEq] at h₁ h₂; exact hNe (h₁.trans h₂.symm)
    · cases h₁
  | [], _ :: _, _, _, _, _, _, _, _, h₁, h₂ => by
    exfalso
    simp only [climbMerkle32] at h₁ h₂
    split at h₁
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; rcases hc with ⟨rfl, _⟩; simp at h₂
    · cases h₁
  | _ :: _, [], _, _, _, _, _, _, _, h₁, h₂ => by
    exfalso
    simp only [climbMerkle32] at h₁ h₂
    split at h₂
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; rcases hc with ⟨rfl, _⟩; simp at h₁
    · cases h₂
  | s₁ :: ss₁, s₂ :: ss₂, n, idx, leaf₁, leaf₂, root, hNodeBound, hNe, h₁, h₂ => by
    dsimp only [extractClimbMerkleCollision, climbMerkleFrames]
    if hBad : n < 2 || idx ≥ n then
      exfalso; simp [climbMerkle32, hBad] at h₁
    else
      have h65 : 65 ≤ maxBytes := hNodeBound (by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hBad; omega)
      simp only [hBad, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
      if hi : idx < n / 2 then
        simp only [hi, ↓reduceIte, ↓reduceDIte]
        refine ⟨?_, ?_⟩
        · split
          · rename_i hc₁; exfalso; simp [climbMerkle32, hBad, hi, hc₁] at h₁
          · rename_i l₁ hc₁
            split
            · rename_i _ hc₁'; exfalso; simp [climbMerkle32, hBad, hi, hc₁'] at h₁
            · rename_i _ hc₂' _; exfalso; simp [climbMerkle32, hBad, hi, hc₂'] at h₂
            · rename_i l₁' l₂' hc₁' hc₂'
              have hl : l₁' = l₁ := Option.some.inj (hc₁'.symm.trans hc₁)
              subst hl
              if hEqL : l₁' = l₂' then
                subst hEqL
                simp only [↓reduceDIte]
                exact List.mem_cons_of_mem _ (extractClimbMerkleCollision_mem_frames H
                  (maxBytes := maxBytes) ss₁ ss₂ (n / 2) idx leaf₁ leaf₂ l₁' (fun _ => h65) hNe hc₁' hc₂').1
              else
                simp only [hEqL, ↓reduceDIte, extractEvalDigest32Collision]
                exact List.Mem.head _
        · split
          · rename_i hc₂; exfalso; simp [climbMerkle32, hBad, hi, hc₂] at h₂
          · rename_i l₂ hc₂
            split
            · rename_i _ hc₁'; exfalso; simp [climbMerkle32, hBad, hi, hc₁'] at h₁
            · rename_i _ hc₂' _; exfalso; simp [climbMerkle32, hBad, hi, hc₂'] at h₂
            · rename_i l₁' l₂' hc₁' hc₂'
              have hl : l₂' = l₂ := Option.some.inj (hc₂'.symm.trans hc₂)
              subst hl
              if hEqL : l₁' = l₂' then
                subst hEqL
                simp only [↓reduceDIte]
                exact List.mem_cons_of_mem _ (extractClimbMerkleCollision_mem_frames H
                  (maxBytes := maxBytes) ss₁ ss₂ (n / 2) idx leaf₁ leaf₂ l₁' (fun _ => h65) hNe hc₁' hc₂').2
              else
                simp only [hEqL, ↓reduceDIte, extractEvalDigest32Collision]
                exact List.Mem.head _
      else
        simp only [hi, ↓reduceIte, ↓reduceDIte]
        refine ⟨?_, ?_⟩
        · split
          · rename_i hc₁; exfalso; simp [climbMerkle32, hBad, hi, hc₁] at h₁
          · rename_i r₁ hc₁
            split
            · rename_i _ hc₁'; exfalso; simp [climbMerkle32, hBad, hi, hc₁'] at h₁
            · rename_i _ hc₂' _; exfalso; simp [climbMerkle32, hBad, hi, hc₂'] at h₂
            · rename_i r₁' r₂' hc₁' hc₂'
              have hr : r₁' = r₁ := Option.some.inj (hc₁'.symm.trans hc₁)
              subst hr
              if hEqR : r₁' = r₂' then
                subst hEqR
                simp only [↓reduceDIte]
                exact List.mem_cons_of_mem _ (extractClimbMerkleCollision_mem_frames H
                  (maxBytes := maxBytes) ss₁ ss₂ (n - n / 2) (idx - n / 2) leaf₁ leaf₂ r₁' (fun _ => h65) hNe hc₁' hc₂').1
              else
                simp only [hEqR, ↓reduceDIte, extractEvalDigest32Collision]
                exact List.Mem.head _
        · split
          · rename_i hc₂; exfalso; simp [climbMerkle32, hBad, hi, hc₂] at h₂
          · rename_i r₂ hc₂
            split
            · rename_i _ hc₁'; exfalso; simp [climbMerkle32, hBad, hi, hc₁'] at h₁
            · rename_i _ hc₂' _; exfalso; simp [climbMerkle32, hBad, hi, hc₂'] at h₂
            · rename_i r₁' r₂' hc₁' hc₂'
              have hr : r₂' = r₂ := Option.some.inj (hc₂'.symm.trans hc₂)
              subst hr
              if hEqR : r₁' = r₂' then
                subst hEqR
                simp only [↓reduceDIte]
                exact List.mem_cons_of_mem _ (extractClimbMerkleCollision_mem_frames H
                  (maxBytes := maxBytes) ss₁ ss₂ (n - n / 2) (idx - n / 2) leaf₁ leaf₂ r₁' (fun _ => h65) hNe hc₁' hc₂').2
              else
                simp only [hEqR, ↓reduceDIte, extractEvalDigest32Collision]
                exact List.Mem.head _

theorem extractMerklePathCollision_mem_frames (H : Hash32) {v idx : Nat} (hIdx : idx < 2 ^ v)
    {v₁ v₂ : Goldilocks} (p₁ p₂ : List Digest32) (root : Digest32)
    (hNe : v₁ ≠ v₂)
    (hv₁ : verifyMerklePath H (2 ^ v) idx v₁ p₁ root = true)
    (hv₂ : verifyMerklePath H (2 ^ v) idx v₂ p₂ root = true) :
    let w := extractMerklePathCollision H hIdx p₁ p₂ root hNe hv₁ hv₂
    w.msgA ∈ merkleEntryFrames H (2 ^ v) idx v₁ p₁ ∧
    w.msgB ∈ merkleEntryFrames H (2 ^ v) idx v₂ p₂ := by
  dsimp only [extractMerklePathCollision, merkleEntryFrames]
  if hLeafEq : hashLeaf32 H idx v₁ = hashLeaf32 H idx v₂ then
    simp only [hLeafEq, ↓reduceDIte, extractEvalDigest32Collision]
    exact ⟨List.Mem.head _, List.Mem.head _⟩
  else
    simp only [hLeafEq, ↓reduceDIte]
    have hSub := extractClimbMerkleCollision_mem_frames H (maxBytes := merkleMaxPreimageBytes v)
      p₁ p₂ (2 ^ v) idx (hashLeaf32 H idx v₁) (hashLeaf32 H idx v₂) root
      (by cases v with | zero => intro h; omega | succ k => intro _; exact Nat.le_max_left 65 (11 + k))
      hLeafEq
      (by simpa [verifyMerklePath, beq_iff_eq] using hv₁)
      (by simpa [verifyMerklePath, beq_iff_eq] using hv₂)
    exact ⟨List.mem_cons_of_mem _ hSub.1, List.mem_cons_of_mem _ hSub.2⟩

private theorem mem_canopyOpeningFrames_of_entry (H : Hash32) {v idx : Nat}
    {π : CanopyOpeningProof} (hIn : idx < π.entries.length) {m : List UInt8}
    (hMem : m ∈ merkleEntryFrames H (2 ^ v) idx (π.entries[idx]'hIn).1 (π.entries[idx]'hIn).2) :
    m ∈ canopyOpeningFrames H v π :=
  List.mem_flatMap.2 ⟨⟨idx, hIn⟩, List.mem_finRange _, hMem⟩

private theorem extractMerklePathCollision_mem_openingFrames (H : Hash32) {v idx : Nat}
    {π₁ π₂ : CanopyOpeningProof} (hIdx : idx < 2 ^ v)
    (hIn₁ : idx < π₁.entries.length) (hIn₂ : idx < π₂.entries.length)
    (root : Digest32)
    (hNe : (π₁.entries[idx]'hIn₁).1 ≠ (π₂.entries[idx]'hIn₂).1)
    (hv₁ : verifyMerklePath H (2 ^ v) idx (π₁.entries[idx]'hIn₁).1 (π₁.entries[idx]'hIn₁).2 root = true)
    (hv₂ : verifyMerklePath H (2 ^ v) idx (π₂.entries[idx]'hIn₂).1 (π₂.entries[idx]'hIn₂).2 root = true) :
    (extractMerklePathCollision H hIdx (π₁.entries[idx]'hIn₁).2 (π₂.entries[idx]'hIn₂).2 root hNe hv₁ hv₂).msgA ∈
      canopyOpeningFrames H v π₁ ∧
    (extractMerklePathCollision H hIdx (π₁.entries[idx]'hIn₁).2 (π₂.entries[idx]'hIn₂).2 root hNe hv₁ hv₂).msgB ∈
      canopyOpeningFrames H v π₂ := by
  have hMem := extractMerklePathCollision_mem_frames H hIdx
    (π₁.entries[idx]'hIn₁).2 (π₂.entries[idx]'hIn₂).2 root hNe hv₁ hv₂
  exact ⟨mem_canopyOpeningFrames_of_entry H hIn₁ hMem.1,
         mem_canopyOpeningFrames_of_entry H hIn₂ hMem.2⟩

/-- Every witness extracted by `extractCanopyDoubleOpenCollision` has `msgA ∈ canopyOpeningFrames H v π₁`
    and `msgB ∈ canopyOpeningFrames H v π₂` (so only the openings' own finite Merkle frames need be logged!). -/
theorem extractCanopyDoubleOpenCollision_mem_frames (H : Hash32)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    {v : Nat} {comm : CanopyCommitment}
    {c₁ c₂ : EvalClaim Goldilocks v} {π₁ π₂ : CanopyOpeningProof}
    {tr₁ : Transcript phase₁} {tr₂ : Transcript phase₂}
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : (canopyVerifyEval H v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : (canopyVerifyEval H v comm c₂ π₂ tr₂).1 = true)
    (hDisagree : c₁.expectedVal ≠ c₂.expectedVal) :
    let w := extractCanopyDoubleOpenCollision H hPt hAcc₁ hAcc₂ hDisagree
    w.msgA ∈ canopyOpeningFrames H v π₁ ∧ w.msgB ∈ canopyOpeningFrames H v π₂ := by
  dsimp only [extractCanopyDoubleOpenCollision]
  apply extractMerklePathCollision_mem_openingFrames

/-- **Constructive `0 Classical` Double-Open-Or-Equal Extractor for All Arities `v : Nat`**:
    For EVERY variable count `v` (including compressing trees `v ≥ 1` where `merkleMaxPreimageBytes v = 65`),
    any two accepted openings at `c₁.point = c₂.point` either agree on `expectedVal` or constructively
    return an explicit `HashCollisionWitness H.eval (merkleMaxPreimageBytes v)`. -/
def canopyMerklePCS_extractDoubleOpenOrEq (H : Hash32) (v : Nat)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    (comm : CanopyCommitment) (c₁ c₂ : EvalClaim Goldilocks v)
    (π₁ π₂ : CanopyOpeningProof) (tr₁ : Transcript phase₁) (tr₂ : Transcript phase₂)
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : ((canopyMerklePCS H).verifyEval () v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : ((canopyMerklePCS H).verifyEval () v comm c₂ π₂ tr₂).1 = true) :
    PSum (c₁.expectedVal = c₂.expectedVal) (HashCollisionWitness H.eval (merkleMaxPreimageBytes v)) :=
  if hEq : c₁.expectedVal = c₂.expectedVal then
    .inl hEq
  else
    .inr (extractCanopyDoubleOpenCollision H hPt hAcc₁ hAcc₂ hEq)

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

theorem evalDigest32_eq_of_sameDigest (H : Hash32) {m₁ m₂ : List UInt8}
    (hSame : ofBE (H.eval m₁) = ofBE (H.eval m₂)) :
    evalDigest32 H m₁ = evalDigest32 H m₂ :=
  Digest32.ext (congrArg Native.bytesOfList
    (ofBE_injective_of_length_eq ((H.len_eq m₁).trans (H.len_eq m₂).symm) hSame))

/-- **LazyRO Collision-Free Log Binding (`canopyMerklePCS_bind_of_roLog`, `0 Classical`)**:
    In the Random Oracle Model (`GameSoundness.ROLog`), for ANY arity `v` (including `v ≥ 1`),
    whenever the finite Merkle frames of `π₁` and `π₂` (`canopyOpeningFrames H v πᵢ`) appear in a
    collision-free 32-byte `Digest32` query log (`GameSoundness.hasLogCollision log = false`, bounded
    by Birthday `q(q-1)/(2·2^256)`), their claimed evaluations MUST agree! -/
theorem canopyMerklePCS_bind_of_roLog (H : Hash32) (v : Nat)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    (log : GameSoundness.ROLog (List UInt8) Digest32)
    (hNoLogCol : GameSoundness.hasLogCollision log = false)
    (comm : CanopyCommitment) (c₁ c₂ : EvalClaim Goldilocks v)
    (π₁ π₂ : CanopyOpeningProof) (tr₁ : Transcript phase₁) (tr₂ : Transcript phase₂)
    (hPt : c₁.point = c₂.point)
    (hAcc₁ : ((canopyMerklePCS H).verifyEval () v comm c₁ π₁ tr₁).1 = true)
    (hAcc₂ : ((canopyMerklePCS H).verifyEval () v comm c₂ π₂ tr₂).1 = true)
    (hLogged₁ : ∀ m ∈ canopyOpeningFrames H v π₁, (m, evalDigest32 H m) ∈ log)
    (hLogged₂ : ∀ m ∈ canopyOpeningFrames H v π₂, (m, evalDigest32 H m) ∈ log) :
    c₁.expectedVal = c₂.expectedVal := by
  if hEq : c₁.expectedVal = c₂.expectedVal then
    exact hEq
  else
    exfalso
    let w := extractCanopyDoubleOpenCollision H hPt hAcc₁ hAcc₂ hEq
    have hMem := extractCanopyDoubleOpenCollision_mem_frames H hPt hAcc₁ hAcc₂ hEq
    have hCol : GameSoundness.hasLogCollision log = true :=
      (GameSoundness.hasLogCollision_iff log).2
        ⟨(w.msgA, evalDigest32 H w.msgA), hLogged₁ w.msgA hMem.1,
         (w.msgB, evalDigest32 H w.msgB), hLogged₂ w.msgB hMem.2,
         w.distinct, evalDigest32_eq_of_sameDigest H w.sameDigest⟩
    rw [hNoLogCol] at hCol
    cases hCol

/-- **Game-Level `LazyRO` Birthday Bound for 32-Byte Canopy Frame Logs (`canopyMerkle_lazyRO_birthday_bound`)**:
    Over any nodup 32-byte `Digest32` domain `dom` (`|dom| = 2^256` at full 32-byte width), any
    $q$-query adaptive adversary `adv : QueryProg (List UInt8) Digest32 α q` against `lazyROPackage`
    violates `hasLogCollision log = false` with probability at most $\frac{q(q-1)}{2 \cdot |dom|}$. -/
theorem canopyMerkle_lazyRO_birthday_bound {α : Type}
    (dom : List Digest32) (hne : dom ≠ []) (hNodup : dom.Nodup)
    {q : Nat} (adv : GameSoundness.QueryProg (List UInt8) Digest32 α q) :
    GameSoundness.RatProb.le
      ((GameSoundness.runProg (GameSoundness.lazyROPackage dom hne) adv []).probEvent
        (fun (_, lf) => GameSoundness.hasLogCollision lf))
      ⟨q * (q - 1), 2 * dom.length, Nat.mul_pos (by decide) (GameSoundness.length_pos_of_ne_nil hne)⟩ :=
  GameSoundness.lazyRO_collision_prob_le_birthday_dom dom hne hNodup adv

/-- Logged double-opening forgery event connecting verifier execution to the `LazyRO` query transcript `lf`. -/
def isLoggedDoubleOpenForgery (H : Hash32) (v : Nat)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    (comm : CanopyCommitment) (tr₁ : Transcript phase₁) (tr₂ : Transcript phase₂)
    (outLog : (EvalClaim Goldilocks v × EvalClaim Goldilocks v × CanopyOpeningProof × CanopyOpeningProof) ×
              GameSoundness.ROLog (List UInt8) Digest32) : Bool :=
  let ((c₁, c₂, π₁, π₂), lf) := outLog
  decide (c₁.point = c₂.point) && decide (c₁.expectedVal ≠ c₂.expectedVal) &&
    ((canopyMerklePCS H).verifyEval () v comm c₁ π₁ tr₁).1 &&
    ((canopyMerklePCS H).verifyEval () v comm c₂ π₂ tr₂).1 &&
    (canopyOpeningFrames H v π₁).all (fun m => decide ((m, evalDigest32 H m) ∈ lf)) &&
    (canopyOpeningFrames H v π₂).all (fun m => decide ((m, evalDigest32 H m) ∈ lf))

/-- **End-to-End `LazyRO` PCS Forgery Probability Bound (`canopyDoubleOpen_forger_prob_le_birthday`)**:
    Bridges `canopyMerklePCS_bind_of_roLog` directly to `lazyROPackage`: any $q$-query adaptive adversary
    whose accepted verification frames appear in the RO log `lf` produces a discrepant double opening
    (`c₁.point = c₂.point ∧ c₁.expectedVal ≠ c₂.expectedVal`) with probability at most $\frac{q(q-1)}{2 \cdot |dom|}$. -/
theorem canopyDoubleOpen_forger_prob_le_birthday (H : Hash32) (v : Nat)
    {phase₁ phase₂ : TranscriptPhase} [CanSqueezeTranscript phase₁] [CanSqueezeTranscript phase₂]
    (dom : List Digest32) (hne : dom ≠ []) (hNodup : dom.Nodup)
    (comm : CanopyCommitment) (tr₁ : Transcript phase₁) (tr₂ : Transcript phase₂)
    {q : Nat}
    (adv : GameSoundness.QueryProg (List UInt8) Digest32
             (EvalClaim Goldilocks v × EvalClaim Goldilocks v × CanopyOpeningProof × CanopyOpeningProof) q) :
    GameSoundness.RatProb.le
      ((GameSoundness.runProg (GameSoundness.lazyROPackage dom hne) adv []).probEvent
        (isLoggedDoubleOpenForgery H v comm tr₁ tr₂))
      ⟨q * (q - 1), 2 * dom.length, Nat.mul_pos (by decide) (GameSoundness.length_pos_of_ne_nil hne)⟩ := by
  refine GameSoundness.RatProb.le_trans ?_ (canopyMerkle_lazyRO_birthday_bound dom hne hNodup adv)
  unfold GameSoundness.RatProb.le GameSoundness.FinDist.probEvent
  apply Nat.mul_le_mul_right
  have ptImp : ∀ outLog, isLoggedDoubleOpenForgery H v comm tr₁ tr₂ outLog = true →
      GameSoundness.hasLogCollision outLog.2 = true := by
    rintro ⟨⟨c₁, c₂, π₁, π₂⟩, lf⟩ hF
    simp only [isLoggedDoubleOpenForgery, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hF
    rcases hF with ⟨⟨⟨⟨⟨hPt, hNe⟩, hAcc₁⟩, hAcc₂⟩, hLog₁⟩, hLog₂⟩
    cases hCol : GameSoundness.hasLogCollision lf
    · exact False.elim (hNe (canopyMerklePCS_bind_of_roLog H v lf hCol comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂ hLog₁ hLog₂))
    · rfl
  have monoMass : ∀ {α : Type} (p₁ p₂ : α → Bool) (hImp : ∀ x, p₁ x = true → p₂ x = true) (xs : List (α × Nat)),
      GameSoundness.eventMass p₁ xs ≤ GameSoundness.eventMass p₂ xs := by
    intro α p₁ p₂ hImp xs; induction xs with
    | nil => exact Nat.le_refl 0
    | cons hd tail ih =>
      rcases hd with ⟨x, wt⟩; dsimp only [GameSoundness.eventMass]
      cases hp₁ : p₁ x
      · cases p₂ x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      · rw [hImp x hp₁]; simp only [↓reduceIte]; omega
  exact monoMass (isLoggedDoubleOpenForgery H v comm tr₁ tr₂) (fun (_, lf) => GameSoundness.hasLogCollision lf)
    (fun ⟨out, lf⟩ hF => ptImp (out, lf) hF)
    (GameSoundness.runProg (GameSoundness.lazyROPackage dom hne) adv []).support

/-- **Non-Compressing (`10 ≤ 32`-Byte) Arity-0 Bounded Collision-Resistance Implies `BindingSoundAt 0` (`0 Classical`)**:
    At `v = 0`, `merkleMaxPreimageBytes 0 = 10 ≤ 32`, so `¬ BoundedCollision H.eval 10` is genuinely
    non-vacuous (`toyInjectiveHash32_no_boundedCollision`); for `v ≥ 1`, use `canopyMerklePCS_bind_of_roLog`
    and `canopyMerklePCS_extractDoubleOpenOrEq`. -/
theorem canopyMerklePCS_bindingSoundAt_of_boundedCollisionFree (H : Hash32)
    (hNoCol : ¬ BoundedCollision H.eval 10) :
    BindingSoundAt 0 (canopyMerklePCS H) := by
  intro _ _ _ _ _ comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂
  cases canopyMerklePCS_extractDoubleOpenOrEq H 0 comm c₁ c₂ π₁ π₂ tr₁ tr₂ hPt hAcc₁ hAcc₂ with
  | inl hEq => exact hEq
  | inr w => exact False.elim (hNoCol ⟨w⟩)

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
  canopyMerklePCS_bindingSoundAt_of_boundedCollisionFree toyInjectiveHash32
    (toyInjectiveHash32_no_boundedCollision (by decide))

end Obend.Crypto
end
