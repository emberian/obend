module
/-
# Obend.SymbolicZk.EinSumcheckMxfp4 — `EinSumcheck` (`(F₁, F_{≥2}, S)`) & Native `MXFP4` (`E2M1`) Core

Grounded verifiable-inference primitives over base-field `Goldilocks` ($p = 2^{64} - 2^{32} + 1$):
1. **Authenticated Suite Profiles (`OBEND.SHE.ZKML_SUITE/v1`), `E2M1` Domain & `OBEND.SHE.ZKML_WEIGHTS/v1`**:
   - Authenticates all 8 `ZkmlSuiteProfile` fields (`extractZkmlSuiteProfileBinding`, `0 Classical.choice`),
     signed `E2M1` integer mantissas $Q[b,k,j] \in \{0, \pm 1, \pm 2, \pm 3, \pm 4, \pm 6, \pm 8, \pm 12\}$,
     and power-of-two block scales $S[k,j] = 2^{\mathrm{sh}[k,j]}$ ($\mathrm{sh} \le 30$) without offline
     weight dequantization (`extractMxfp4ModelBinding`, `maxZkmlHypercubeVars = 20`).
2. **Binary `OBEND.SHE.ZKML_MERKLE/v1` Butterfly Fold Walks & `windowed_find_map_first` PoW Grinder**:
   - Proves `extractZkmlMerkleAt` (`0 Classical.choice`), `verifyFoldWalk_iff_spec`, `verifyFoldWalk_complete`,
     `verifyFoldWalk_deviates_pair` + `openFoldWalk_no_discrepancy` (sound & non-vacuous fold-pair discrepancy),
     and `windowedFindMapFirst_minimal_and_pred_invalid` (`w - 1` provably invalid).
3. **Characteristic-Free `(2^logB, 3^logK, 3^logJ)` `EinSumcheck` & Native 3-Operand `MXFP4` Contraction**:
   - Proves `einsum2Op_mle_identity`, `naive_batched_matmul_incomplete` (refuting `zkGPT` Eq. (8)'s `eq`-free
     batched-matmul check), `gqa_rounds_and_kv_savings`, `proveMxfp4Sumcheck_complete`, witness-pinned
     `Mxfp4SumcheckRootHit` (`proveMxfp4Sumcheck_no_rootHit`), and `verifyMxfp4Sumcheck_sound`.
   - **Honest Scoping**: This PIOP executes over base-field `Goldilocks` and rate-1 uncoded binary Merkle
     trees (not Reed–Solomon codewords or extension-field challenges); Lean proves the exact constructive
     failure-event disjunction (`0` probability axioms; uniform challenges give per-chunk Schwartz–Zippel
     error $(\mathrm{logI} + \mathrm{logJ} + 2\mathrm{logB} + 3\mathrm{logK} + 3\mathrm{logJ}) / p$, while
     128-bit modular squeezing shifts per-point mass to $\le \lceil 2^{128}/p \rceil / 2^{128}$).
-/
public import Obend.Digest.Cshake256
public import Obend.Crypto.PCS
public section
namespace Obend.SymbolicZk.ProvenZkmlGate
open Obend.Apps.ZkNtt Obend.Crypto Obend.Digest.Cshake256 Obend.Digest.HashBytes Obend.Judge.Computational
set_option autoImplicit false
/-! ## 1. Authenticated `ZkmlSuiteProfile`, Framing, `E2M1` Domain & `OBEND.SHE.ZKML_WEIGHTS/v1` -/
structure ZkmlSuiteProfile where
  fieldModulusBits : Nat
  extDegree : Nat
  logBlowup : Nat
  numQueries : Nat
  grindBits : Nat
  logTraceHeight : Nat
  digestBits : Nat
  logArity : Nat := 1
  deriving DecidableEq, Repr, Inhabited
instance : Inhabited Goldilocks := ⟨Goldilocks.zero⟩
instance : Inhabited (RoundPoly Goldilocks) := ⟨⟨[]⟩⟩
instance : Inhabited Digest32 := ⟨⟨⟨(List.replicate 32 0).toArray⟩, by decide⟩⟩
def u64ToBe8 (w : UInt64) : List UInt8 := be 8 w.toNat
theorem u64ToBe8_length (w : UInt64) : (u64ToBe8 w).length = 8 := length_be ..
theorem u64ToBe8_injective {w₁ w₂ : UInt64} (h : u64ToBe8 w₁ = u64ToBe8 w₂) : w₁ = w₂ := UInt64.toNat_inj.mp (be_injective (w := 8) w₁.toNat_lt w₂.toNat_lt h)
theorem leb128_inj {a b : Nat} (h : leb128 a = leb128 b) : a = b := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa [List.append_nil] using h)).1
def glToBe8 (x : Goldilocks) : List UInt8 := be 8 x.val
theorem glToBe8_injective {x y : Goldilocks} (h : glToBe8 x = glToBe8 y) : x = y := by
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  exact Goldilocks.ext (be_injective (h8 ▸ Goldilocks.val_lt_two_pow_64 x) (h8 ▸ Goldilocks.val_lt_two_pow_64 y) h)
def encodeSignedInt : Int → List UInt8
  | .ofNat n => 0x00 :: leb128 n | .negSucc n => 0x01 :: leb128 n
theorem encodeSignedInt_injective {z₁ z₂ : Int} (h : encodeSignedInt z₁ = encodeSignedInt z₂) : z₁ = z₂ := by
  cases z₁ <;> cases z₂ <;> simp only [encodeSignedInt, List.cons.injEq] at h
  · exact congrArg Int.ofNat (leb128_inj h.2)
  · nomatch h.1
  · nomatch h.1
  · exact congrArg Int.negSucc (leb128_inj h.2)
def encodeZkmlFields : List (List UInt8) → List UInt8
  | [] => [] | f :: fs => encodeListField f ++ encodeZkmlFields fs
private theorem encodeListField_ne_nil (f : List UInt8) : encodeListField f ≠ [] := by
  unfold encodeListField leb128; cases f.length with | zero => simp [leb128Aux] | succ _ => simp only [leb128Aux]; split <;> simp
theorem encodeZkmlFields_injective : ∀ {fs₁ fs₂ : List (List UInt8)}, encodeZkmlFields fs₁ = encodeZkmlFields fs₂ → fs₁ = fs₂
  | [], [], _ => rfl | [], b :: _, h => absurd h.symm (fun e => encodeListField_ne_nil b (List.append_eq_nil_iff.mp e).1)
  | a :: _, [], h => absurd h (fun e => encodeListField_ne_nil a (List.append_eq_nil_iff.mp e).1)
  | _ :: _, _ :: _, h => by simp only [encodeZkmlFields] at h; obtain ⟨hab, hrest⟩ := encodeListField_prefix_inj h; rw [hab, encodeZkmlFields_injective hrest]
def extractZkmlCshake32 (customization p₁ p₂ : List UInt8) (h : cshake32ByteArray customization p₁ = cshake32ByteArray customization p₂) : PSum (PLift (p₁ = p₂))
      (PLift (CollisionAmong (cshake256Bytes customization) (fun x => x = p₁ ∨ x = p₂))) :=
  if hp : p₁ = p₂ then .inl ⟨hp⟩
  else .inr ⟨by
    have hl := congrArg (fun b => b.data.toList) h
    simp only [cshake32ByteArray, Native.bytesOfList_toList] at hl; exact ⟨p₁, p₂, .inl rfl, .inr rfl, hp, congrArg ofBE hl⟩⟩
def ZkmlSuiteProfile.encode (p : ZkmlSuiteProfile) : List UInt8 :=
  encodeZkmlFields [leb128 p.fieldModulusBits, leb128 p.extDegree, leb128 p.logBlowup,
    leb128 p.numQueries, leb128 p.grindBits, leb128 p.logTraceHeight, leb128 p.digestBits, leb128 p.logArity]
theorem ZkmlSuiteProfile.encode_injective {p₁ p₂ : ZkmlSuiteProfile} (h : p₁.encode = p₂.encode) : p₁ = p₂ := by
  have hf := encodeZkmlFields_injective h; simp only [List.cons.injEq, and_true] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf; cases p₁; cases p₂; simp only [ZkmlSuiteProfile.mk.injEq]
  exact ⟨leb128_inj h1, leb128_inj h2, leb128_inj h3, leb128_inj h4, leb128_inj h5, leb128_inj h6, leb128_inj h7, leb128_inj h8⟩
def ZkmlSuiteProfile.digest (p : ZkmlSuiteProfile) : ByteArray := cshake32ByteArray "OBEND.SHE.ZKML_SUITE/v1".toUTF8.data.toList p.encode
theorem ZkmlSuiteProfile.digest_size (p : ZkmlSuiteProfile) : p.digest.size = 32 := cshake32ByteArray_size _ _
def extractZkmlSuiteProfileBinding (p₁ p₂ : ZkmlSuiteProfile) (h : p₁.digest = p₂.digest) : PSum (PLift (p₁ = p₂))
      (PLift (CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_SUITE/v1".toUTF8.data.toList) (fun x => x = p₁.encode ∨ x = p₂.encode))) :=
  match extractZkmlCshake32 "OBEND.SHE.ZKML_SUITE/v1".toUTF8.data.toList p₁.encode p₂.encode h with
  | .inl hp => .inl ⟨ZkmlSuiteProfile.encode_injective hp.down⟩ | .inr hc => .inr hc
theorem zkmlSuiteProfile_digest_binds {p₁ p₂ : ZkmlSuiteProfile} (h : p₁.digest = p₂.digest) :
    p₁ = p₂ ∨ CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_SUITE/v1".toUTF8.data.toList) (fun x => x = p₁.encode ∨ x = p₂.encode) := by
  cases extractZkmlSuiteProfileBinding p₁ p₂ h with | inl e => exact .inl e.down | inr c => exact .inr c.down
private theorem flatMap_gl_inj : ∀ {xs ys : List Goldilocks}, xs.length = ys.length → xs.flatMap glToBe8 = ys.flatMap glToBe8 → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen; simp only [List.flatMap_cons] at h; obtain ⟨hh, ht⟩ := List.append_inj h (by simp [glToBe8, length_be])
    rw [glToBe8_injective hh, flatMap_gl_inj hlen ht]
def encodeGoldilocksVec (xs : List Goldilocks) : List UInt8 := leb128 xs.length ++ xs.flatMap glToBe8
theorem encodeGoldilocksVec_injective {xs ys : List Goldilocks} (h : encodeGoldilocksVec xs = encodeGoldilocksVec ys) : xs = ys := by
  unfold encodeGoldilocksVec at h; obtain ⟨hlen, hbody⟩ := leb128_prefix_inj h; exact flatMap_gl_inj hlen hbody
def encodeDigest32List (ds : List Digest32) : List UInt8 := encodeZkmlFields (ds.map fun d => d.bytes.data.toList)
theorem encodeDigest32List_injective {d₁ d₂ : List Digest32} (h : encodeDigest32List d₁ = encodeDigest32List d₂) : d₁ = d₂ :=
  (List.map_inj_right fun _ _ heq => Digest32.ext (byteArray_eq_of_toList_eq heq)).mp (encodeZkmlFields_injective h)
@[expose] def e2m1Domain : List Int := [-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12]
@[expose] def isValidE2m1Mantissa (q : Int) : Bool := decide (q ∈ e2m1Domain)
@[expose] def maxMxfp4ScaleShift : Nat := 30
@[expose] def isValidMxfp4Shift (sh : Nat) : Bool := decide (sh ≤ maxMxfp4ScaleShift)
@[expose] def maxZkmlHypercubeVars : Nat := 20
def intToGoldilocks : Int → Goldilocks
  | .ofNat n => Goldilocks.ofNat n | .negSucc n => CommRingOps.neg (Goldilocks.ofNat (n + 1))
def shiftToGoldilocks (sh : Nat) : Goldilocks := Goldilocks.ofNat (2 ^ sh)
private theorem e2m1Domain_inj_check : (e2m1Domain.all fun q₁ => e2m1Domain.all fun q₂ => decide (intToGoldilocks q₁ = intToGoldilocks q₂ → q₁ = q₂)) = true := by decide
theorem e2m1_intToGoldilocks_injective {q₁ q₂ : Int} (h₁ : isValidE2m1Mantissa q₁ = true) (h₂ : isValidE2m1Mantissa q₂ = true)
    (heq : intToGoldilocks q₁ = intToGoldilocks q₂) : q₁ = q₂ :=
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp e2m1Domain_inj_check q₁ (of_decide_eq_true h₁)) q₂ (of_decide_eq_true h₂)) heq
theorem mxfp4_shiftToGoldilocks_injective {sh₁ sh₂ : Nat} (h₁ : isValidMxfp4Shift sh₁ = true) (h₂ : isValidMxfp4Shift sh₂ = true)
    (heq : shiftToGoldilocks sh₁ = shiftToGoldilocks sh₂) : sh₁ = sh₂ := by
  have hp30 : 2 ^ 30 < goldilocksPrime := by unfold goldilocksPrime; decide
  have hlt1 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (of_decide_eq_true h₁)) hp30
  have hlt2 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (of_decide_eq_true h₂)) hp30
  have hv := congrArg Goldilocks.val heq; simp only [shiftToGoldilocks, Goldilocks.ofNat, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
  if hcmp : sh₁ < sh₂ then exact absurd hv (Nat.ne_of_lt (Nat.pow_lt_pow_right (by decide) hcmp))
  else if hcmp2 : sh₂ < sh₁ then exact absurd hv.symm (Nat.ne_of_lt (Nat.pow_lt_pow_right (by decide) hcmp2))
  else omega
structure Mxfp4LayerKey where
  logI : Nat
  logJ : Nat
  logK : Nat
  logB : Nat
  qMerkleRoot : ByteArray
  sMerkleRoot : ByteArray
  deriving DecidableEq, Inhabited
@[expose] def Mxfp4LayerKey.validDims (lk : Mxfp4LayerKey) : Bool :=
  decide (1 ≤ lk.logI ∧ 1 ≤ lk.logJ ∧ 1 ≤ lk.logK ∧ 1 ≤ lk.logB ∧ lk.logI + lk.logJ < maxZkmlHypercubeVars ∧ lk.logI + lk.logB + lk.logK < maxZkmlHypercubeVars ∧
    lk.logB + lk.logK + lk.logJ < maxZkmlHypercubeVars ∧ lk.qMerkleRoot.size = 32 ∧ lk.sMerkleRoot.size = 32)
def Mxfp4LayerKey.encode (lk : Mxfp4LayerKey) : List UInt8 :=
  encodeZkmlFields [leb128 lk.logI, leb128 lk.logJ, leb128 lk.logK, leb128 lk.logB, lk.qMerkleRoot.data.toList, lk.sMerkleRoot.data.toList]
theorem Mxfp4LayerKey.encode_injective {a b : Mxfp4LayerKey} (h : a.encode = b.encode) : a = b := by
  have hf := encodeZkmlFields_injective h; simp only [List.cons.injEq, and_true] at hf; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf; cases a; cases b; simp only [Mxfp4LayerKey.mk.injEq]
  exact ⟨leb128_inj h1, leb128_inj h2, leb128_inj h3, leb128_inj h4, byteArray_eq_of_toList_eq h5, byteArray_eq_of_toList_eq h6⟩
structure Mxfp4ModelManifest where
  layers : List Mxfp4LayerKey
  deriving DecidableEq, Inhabited
@[expose] def Mxfp4ModelManifest.valid (M : Mxfp4ModelManifest) : Bool := decide (M.layers ≠ [] ∧ M.layers.length ≤ 1024) && M.layers.all Mxfp4LayerKey.validDims
def Mxfp4ModelManifest.preimage (M : Mxfp4ModelManifest) : List UInt8 := encodeZkmlFields (M.layers.map Mxfp4LayerKey.encode)
def Mxfp4ModelManifest.root (M : Mxfp4ModelManifest) : ByteArray := cshake32ByteArray "OBEND.SHE.ZKML_WEIGHTS/v1".toUTF8.data.toList M.preimage
theorem Mxfp4ModelManifest.root_size (M : Mxfp4ModelManifest) : M.root.size = 32 := cshake32ByteArray_size _ _
def extractMxfp4ModelBinding (M₁ M₂ : Mxfp4ModelManifest) (h : M₁.root = M₂.root) : PSum (PLift (M₁ = M₂))
      (PLift (CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_WEIGHTS/v1".toUTF8.data.toList) (fun x => x = M₁.preimage ∨ x = M₂.preimage))) :=
  match extractZkmlCshake32 "OBEND.SHE.ZKML_WEIGHTS/v1".toUTF8.data.toList M₁.preimage M₂.preimage h with
  | .inr hc => .inr hc | .inl hp => .inl ⟨by
      cases M₁; cases M₂; simp only [Mxfp4ModelManifest.mk.injEq]
      exact (List.map_inj_right fun _ _ => Mxfp4LayerKey.encode_injective).mp (encodeZkmlFields_injective hp.down)⟩
/-! ## 2. `OBEND.SHE.ZKML_MERKLE/v1` Trees, Fold Walks & `windowed_find_map_first` PoW Grinder -/
def zkmlMerkleCust : List UInt8 := "OBEND.SHE.ZKML_MERKLE/v1".toUTF8.data.toList
def zkmlMerkleHash32 : Hash32 := ⟨cshake256Bytes zkmlMerkleCust, cshake256Bytes_length zkmlMerkleCust⟩
def zkmlLeafPre (tag : UInt8) (idx : Nat) (pay : List UInt8) : List UInt8 := tag :: (leb128 idx ++ pay)
private theorem zkmlLeafPre_pay_inj {tag : UInt8} {idx : Nat} {p₁ p₂ : List UInt8} (h : zkmlLeafPre tag idx p₁ = zkmlLeafPre tag idx p₂) : p₁ = p₂ := by
  simp only [zkmlLeafPre, List.cons.injEq] at h; exact (leb128_prefix_inj h.2).2
def zkmlLeaf32 (tag : UInt8) (idx : Nat) (pay : List UInt8) : Digest32 := evalDigest32 zkmlMerkleHash32 (zkmlLeafPre tag idx pay)
def hashTensorLeaf (idx : Nat) (x : Goldilocks) : Digest32 := zkmlLeaf32 0x03 idx (glToBe8 x)
def hashMantissaLeaf (idx : Nat) (q : Int) : Digest32 := zkmlLeaf32 0x06 idx (encodeSignedInt q)
def hashShiftLeaf (idx : Nat) (sh : Nat) : Digest32 := zkmlLeaf32 0x07 idx (leb128 sh)
theorem glToBe8_length (x : Goldilocks) : (glToBe8 x).length = 8 := by simp [glToBe8, length_be]
theorem hashTensorLeaf_eq (idx : Nat) (x : Goldilocks) : hashTensorLeaf idx x = zkmlLeaf32 0x03 idx (glToBe8 x) := by rfl
theorem hashMantissaLeaf_eq (idx : Nat) (q : Int) : hashMantissaLeaf idx q = zkmlLeaf32 0x06 idx (encodeSignedInt q) := by rfl
theorem hashShiftLeaf_eq (idx : Nat) (sh : Nat) : hashShiftLeaf idx sh = zkmlLeaf32 0x07 idx (leb128 sh) := by rfl
def hashFoldPairLeaf (layerIdx pairIdx : Nat) (lo hi : Goldilocks) : Digest32 :=
  evalDigest32 zkmlMerkleHash32 (0x05 :: (leb128 layerIdx ++ leb128 pairIdx ++ encodeGoldilocksVec [lo, hi]))
def climbZkml32 (treeSize idx : Nat) (leaf : Digest32) (path : List Digest32) (rootBytes : ByteArray) : Bool :=
  match climbMerkle32 zkmlMerkleHash32 treeSize idx leaf path with
  | some r => decide (r.bytes = rootBytes) | none => false
theorem climbZkml32_iff (treeSize idx : Nat) (leaf : Digest32) (path : List Digest32) (rootBytes : ByteArray) : climbZkml32 treeSize idx leaf path rootBytes = true ↔
      ∃ r : Digest32, climbMerkle32 zkmlMerkleHash32 treeSize idx leaf path = some r ∧ r.bytes = rootBytes := by
  unfold climbZkml32; cases climbMerkle32 zkmlMerkleHash32 treeSize idx leaf path with
  | none => simp | some r => simp [decide_eq_true_eq]
theorem climbZkml32_path_len {n : Nat} (leaves : List Digest32) (hlen : leaves.length = n) (idx : Nat) (hIdx : idx < n) :
    climbZkml32 n idx (leaves[idx]'(by omega)) (merklePath32 zkmlMerkleHash32 leaves idx) (merkleRoot32 zkmlMerkleHash32 leaves).bytes = true := by
  subst hlen; unfold climbZkml32; rw [climbMerkle32_merklePath32 _ _ _ hIdx]; simp
def maxByteLen (xs : List (List UInt8)) : Nat := xs.foldr (fun x m => Nat.max x.length m) 0
theorem len_le_maxByteLen {x : List UInt8} {xs : List (List UInt8)} (h : x ∈ xs) : x.length ≤ maxByteLen xs := by
  induction xs with
  | nil => cases h | cons _ _ ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)
private theorem zkmlLeafPre_len_le {v idx cap : Nat} {tag : UInt8} {pay : List UInt8} (hIdx : idx < 2 ^ v) (hPay : pay.length ≤ cap) :
    (zkmlLeafPre tag idx pay).length ≤ 65 + v + 2 + cap := by
  have hleb : (leb128 idx).length ≤ v + 1 := leb128_length_le_of_lt_two_pow hIdx; simp only [zkmlLeafPre, List.length_cons, List.length_append]
  calc (leb128 idx).length + pay.length + 1
    _ ≤ (v + 1) + cap + 1 := Nat.add_le_add_right (Nat.add_le_add hleb hPay) 1
    _ ≤ (65 + v) + 2 + cap := by rw [Nat.add_right_comm (v + 1) cap 1, Nat.add_assoc v 1 1]; exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left v 65) 2) cap
theorem zkmlMerkleHonest_climb {α : Type} (tag : UInt8) (enc : α → List UInt8) (v idx : Nat) (items : List α) (hlen : items.length = 2 ^ v) (hIdx : idx < 2 ^ v) :
    let leaves := items.mapIdx fun i a => zkmlLeaf32 tag i (enc a)
    climbMerkle32 zkmlMerkleHash32 (2 ^ v) idx (zkmlLeaf32 tag idx (enc (items[idx]'(hlen.symm ▸ hIdx))))
      (merklePath32 zkmlMerkleHash32 leaves idx) = some (merkleRoot32 zkmlMerkleHash32 leaves) := by
  intro leaves; have hc := climbMerkle32_merklePath32 zkmlMerkleHash32 leaves idx (by simp [leaves, hlen]; exact hIdx)
  simpa [leaves, hlen] using hc
def extractZkmlMerkleAt {α : Type} [DecidableEq α] (tag : UInt8) (enc : α → List UInt8) (enc_inj : ∀ {a b : α}, enc a = enc b → a = b)
    (v idx cap : Nat) (items : List α) (hlen : items.length = 2 ^ v) (hIdx : idx < 2 ^ v) (opened : α) (path : List Digest32) (rootBytes : ByteArray)
    (hOpenLen : (enc opened).length ≤ cap) (hItemLen : (enc (items[idx]'(hlen.symm ▸ hIdx))).length ≤ cap)
    (hRoot : (merkleRoot32 zkmlMerkleHash32 (items.mapIdx fun i a => zkmlLeaf32 tag i (enc a))).bytes = rootBytes)
    (hClimb : climbZkml32 (2 ^ v) idx (zkmlLeaf32 tag idx (enc opened)) path rootBytes = true) (hHonest : let leaves := items.mapIdx fun i a => zkmlLeaf32 tag i (enc a)
      climbMerkle32 zkmlMerkleHash32 (2 ^ v) idx (zkmlLeaf32 tag idx (enc (items[idx]'(hlen.symm ▸ hIdx))))
        (merklePath32 zkmlMerkleHash32 leaves idx) = some (merkleRoot32 zkmlMerkleHash32 leaves)) :
    PSum (PLift (opened = items[idx]'(hlen.symm ▸ hIdx))) (HashCollisionWitness (cshake256Bytes zkmlMerkleCust) (65 + v + 2 + cap)) :=
  let leaves := items.mapIdx fun i a => zkmlLeaf32 tag i (enc a)
  have hClOpen : climbMerkle32 zkmlMerkleHash32 (2 ^ v) idx (zkmlLeaf32 tag idx (enc opened)) path = some (merkleRoot32 zkmlMerkleHash32 leaves) := by
    obtain ⟨r, hr, hrBytes⟩ := (climbZkml32_iff ..).mp hClimb; exact hr.trans (congrArg some (Digest32.ext (hrBytes.trans hRoot.symm)))
  have h65 : 65 ≤ 65 + v + 2 + cap := Nat.le_trans (Nat.le_add_right 65 v) (Nat.le_trans (Nat.le_add_right _ 2) (Nat.le_add_right _ cap))
  match climbMerkle32_bindsOrCollides zkmlMerkleHash32 path (merklePath32 zkmlMerkleHash32 leaves idx)
      (2 ^ v) idx (zkmlLeaf32 tag idx (enc opened)) (zkmlLeaf32 tag idx (enc (items[idx]'(hlen.symm ▸ hIdx)))) (merkleRoot32 zkmlMerkleHash32 leaves) hClOpen hHonest with
  | .inr w65 => .inr ⟨w65.msgA, w65.msgB, Nat.le_trans w65.lenA h65, Nat.le_trans w65.lenB h65, w65.distinct, w65.sameDigest⟩ | .inl hLeafEq =>
    if hEq : opened = items[idx]'(hlen.symm ▸ hIdx) then .inl ⟨hEq⟩
    else .inr (extractEvalDigest32Collision zkmlMerkleHash32 (zkmlLeafPre_len_le hIdx hOpenLen)
      (zkmlLeafPre_len_le hIdx hItemLen) (fun hpre => hEq (enc_inj (zkmlLeafPre_pay_inj hpre))) hLeafEq)
private theorem foldFirstVar_even_spec (k : Nat) : ∀ (tbl : List Goldilocks) (r : Goldilocks) (hlen : tbl.length = 2 * k),
      (foldFirstVar tbl r).length = k ∧ ∀ (p : Nat) (hp : p < k), (foldFirstVar tbl r)[p]'(by rw [foldFirstVar_length]; omega) = CommRingOps.add (tbl[2 * p]'(by omega))
            (CommRingOps.mul r (CommRingOps.sub (tbl[2 * p + 1]'(by omega)) (tbl[2 * p]'(by omega)))) := by
  induction k with
  | zero => intro tbl _ hlen; cases tbl with | nil => exact ⟨rfl, fun _ hp => nomatch hp⟩ | cons _ _ => simp at hlen
  | succ k ih =>
    intro tbl r hlen; cases tbl with
    | nil => simp at hlen
    | cons lo tl => cases tl with
      | nil => simp only [List.length_cons, List.length_nil] at hlen; omega | cons hi rest =>
        obtain ⟨hLenF, hElemF⟩ := ih rest r (by simp only [List.length_cons] at hlen; omega)
        refine ⟨by simp [foldFirstVar, hLenF], fun p hp => ?_⟩
        cases p with
        | zero => simp [foldFirstVar] | succ j =>
          have h2j : 2 * (j + 1) = 2 * j + 2 := by omega
          simp only [foldFirstVar, List.getElem_cons_succ, hElemF j (Nat.lt_of_succ_lt_succ hp), h2j]
structure FoldLayerStep where
  lo : Goldilocks
  hi : Goldilocks
  merklePath : List Digest32
  deriving DecidableEq, Inhabited
def FoldLayerStep.encode (s : FoldLayerStep) : List UInt8 := encodeZkmlFields [encodeGoldilocksVec [s.lo, s.hi], encodeDigest32List s.merklePath]
theorem FoldLayerStep.encode_injective {s₁ s₂ : FoldLayerStep} (h : s₁.encode = s₂.encode) : s₁ = s₂ := by
  have hf := encodeZkmlFields_injective h; simp only [List.cons.injEq, and_true] at hf; have hp := encodeGoldilocksVec_injective hf.1; simp only [List.cons.injEq, and_true] at hp
  cases s₁; cases s₂; simp only [FoldLayerStep.mk.injEq]
  exact ⟨hp.1, hp.2, encodeDigest32List_injective hf.2⟩
def buildFoldLayerLeaves (layerIdx rem : Nat) (tbl : List Goldilocks) : List Digest32 :=
  (List.range (2 ^ rem)).map fun p =>
    hashFoldPairLeaf layerIdx p (tbl.getD (2 * p) Goldilocks.zero) (tbl.getD (2 * p + 1) Goldilocks.zero)
def buildFoldRoots : Nat → Nat → List Goldilocks → List Goldilocks → List Digest32
  | _, 0, _, _ => [] | _, _ + 1, _, [] => [] | layerIdx, rem + 1, tbl, r :: rs =>
    merkleRoot32 zkmlMerkleHash32 (buildFoldLayerLeaves layerIdx rem tbl) :: buildFoldRoots (layerIdx + 1) rem (foldFirstVar tbl r) rs
def openFoldWalk : Nat → Nat → Nat → List Goldilocks → List Goldilocks → List FoldLayerStep
  | _, 0, _, _, _ => [] | _, _ + 1, _, _, [] => [] | layerIdx, rem + 1, idx, tbl, r :: rs =>
    let pairIdx := idx / 2; let leaves := buildFoldLayerLeaves layerIdx rem tbl
    ⟨tbl.getD (2 * pairIdx) Goldilocks.zero, tbl.getD (2 * pairIdx + 1) Goldilocks.zero, merklePath32 zkmlMerkleHash32 leaves pairIdx⟩ ::
      openFoldWalk (layerIdx + 1) rem pairIdx (foldFirstVar tbl r) rs
def verifyFoldWalk : Nat → Nat → Nat → Goldilocks → Goldilocks → List Goldilocks → List Digest32 → List FoldLayerStep → Bool
  | _, 0, idx, curVal, expectedFinal, rs, roots, steps => decide (idx = 0) && decide (rs = []) && decide (roots = []) && decide (steps = []) && decide (curVal = expectedFinal)
  | layerIdx, rem + 1, idx, curVal, expectedFinal, r :: rs, root :: roots, st :: steps =>
    let pairIdx := idx / 2
    decide (curVal = if decide (idx % 2 = 0) then st.lo else st.hi) &&
    climbZkml32 (2 ^ rem) pairIdx (hashFoldPairLeaf layerIdx pairIdx st.lo st.hi) st.merklePath root.bytes &&
    verifyFoldWalk (layerIdx + 1) rem pairIdx (CommRingOps.add st.lo (CommRingOps.mul r (CommRingOps.sub st.hi st.lo))) expectedFinal rs roots steps
  | _, _ + 1, _, _, _, [], _, _ => false | _, _ + 1, _, _, _, _ :: _, [], _ => false | _, _ + 1, _, _, _, _ :: _, _ :: _, [] => false
inductive FoldWalkSpec :
    Nat → Nat → Nat → Goldilocks → Goldilocks →
    List Goldilocks → List Digest32 → List FoldLayerStep → Prop where
  | zero (layerIdx : Nat) (val : Goldilocks) :
      FoldWalkSpec layerIdx 0 0 val val [] [] []
  | succ {layerIdx rem idx : Nat} {curVal expectedFinal r : Goldilocks}
      {rs : List Goldilocks} {root : Digest32} {roots : List Digest32}
      {st : FoldLayerStep} {steps : List FoldLayerStep} :
      curVal = (if idx % 2 = 0 then st.lo else st.hi) →
      climbMerkle32 zkmlMerkleHash32 (2 ^ rem) (idx / 2)
        (hashFoldPairLeaf layerIdx (idx / 2) st.lo st.hi) st.merklePath = some root →
      FoldWalkSpec (layerIdx + 1) rem (idx / 2)
        (CommRingOps.add st.lo (CommRingOps.mul r (CommRingOps.sub st.hi st.lo))) expectedFinal rs roots steps →
      FoldWalkSpec layerIdx (rem + 1) idx curVal expectedFinal (r :: rs) (root :: roots) (st :: steps)
theorem verifyFoldWalk_iff_spec (rem : Nat) : ∀ (layerIdx idx : Nat) (curVal expectedFinal : Goldilocks)
      (rs : List Goldilocks) (roots : List Digest32) (steps : List FoldLayerStep), verifyFoldWalk layerIdx rem idx curVal expectedFinal rs roots steps = true ↔
        FoldWalkSpec layerIdx rem idx curVal expectedFinal rs roots steps := by
  induction rem with
  | zero =>
    intro layerIdx idx curVal expectedFinal rs roots steps; constructor
    · intro h; simp only [verifyFoldWalk, Bool.and_eq_true, decide_eq_true_eq] at h; rcases h with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩; exact .zero _ _
    · intro h; cases h; simp [verifyFoldWalk]
  | succ rem ih =>
    intro layerIdx idx curVal expectedFinal rs roots steps; cases rs with
    | nil => simp [verifyFoldWalk]; intro h; cases h
    | cons r rs => cases roots with
      | nil => simp [verifyFoldWalk]; intro h; cases h
      | cons root roots => cases steps with
        | nil => simp [verifyFoldWalk]; intro h; cases h | cons st steps =>
          simp only [verifyFoldWalk, Bool.and_eq_true, decide_eq_true_eq, climbZkml32_iff, ih]; constructor
          · rintro ⟨⟨hSide, ⟨rOut, hCl, hBytes⟩⟩, hRec⟩
            exact .succ hSide (hCl.trans (congrArg some (Digest32.ext hBytes))) hRec
          · intro h; cases h with
            | succ hSide hCl hRec => exact ⟨⟨hSide, ⟨root, hCl, rfl⟩⟩, hRec⟩
theorem buildFoldRoots_length (rem : Nat) : ∀ (layerIdx : Nat) (tbl rs : List Goldilocks), rs.length = rem → (buildFoldRoots layerIdx rem tbl rs).length = rem := by
  induction rem with
  | zero => intro _ _ rs hlen; cases rs <;> simp_all [buildFoldRoots] | succ rem ih =>
    intro layerIdx tbl rs hlen; cases rs with
    | nil => simp at hlen | cons r rs => simp only [List.length_cons, Nat.succ.injEq] at hlen; simp [buildFoldRoots, ih _ _ _ hlen]
theorem verifyFoldWalk_complete (rem : Nat) : ∀ (layerIdx idx : Nat) (tbl rs : List Goldilocks) (hTbl : tbl.length = 2 ^ rem) (hIdx : idx < 2 ^ rem) (_hRs : rs.length = rem),
      verifyFoldWalk layerIdx rem idx (tbl[idx]'(by omega)) (mleEval tbl rs) rs (buildFoldRoots layerIdx rem tbl rs) (openFoldWalk layerIdx rem idx tbl rs) = true := by
  induction rem with
  | zero =>
    intro _ idx tbl rs hTbl hIdx hRs; have hi0 : idx = 0 := by simp at hIdx; exact hIdx
    subst hi0; cases rs with
    | cons _ _ => simp at hRs
    | nil => cases tbl with
      | nil => simp at hTbl | cons v₀ tl =>
        have htl : tl = [] := by simp at hTbl; exact hTbl
        subst htl; simp only [buildFoldRoots, openFoldWalk, verifyFoldWalk, mleEval, List.length_nil,
          hypercube, List.map_cons, List.map_nil, eqPoly, innerProd, Bool.true_and, decide_true, decide_eq_true_eq]
        change v₀ = CommRingOps.add (CommRingOps.mul v₀ CommRingOps.one) CommRingOps.zero; rw [LawfulCommRing.mul_one, LawfulCommRing.add_zero]
  | succ rem ih =>
    intro layerIdx idx tbl rs hTbl hIdx hRs; cases rs with
    | nil => simp at hRs | cons r rs =>
      simp only [List.length_cons, Nat.succ.injEq] at hRs; have hEven : tbl.length = 2 * 2 ^ rem := by rw [hTbl, Nat.pow_succ, Nat.mul_comm]
      obtain ⟨hFoldLen, hFoldElem⟩ := foldFirstVar_even_spec (2 ^ rem) tbl r hEven; have hPairLt : idx / 2 < 2 ^ rem := by rw [Nat.pow_succ] at hIdx; omega
      have hLo : tbl.getD (2 * (idx / 2)) Goldilocks.zero = tbl[2 * (idx / 2)]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hHi : tbl.getD (2 * (idx / 2) + 1) Goldilocks.zero = tbl[2 * (idx / 2) + 1]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hSide : tbl[idx]'(by omega) = (if decide (idx % 2 = 0) then tbl[2 * (idx / 2)]'(by omega) else tbl[2 * (idx / 2) + 1]'(by omega)) := by
        if heven : idx % 2 = 0 then have hEqIdx : idx = 2 * (idx / 2) := (by omega); simp [heven, ← hEqIdx]
        else simp only [decide_eq_false heven, Bool.false_eq_true, ↓reduceIte]; congr 1; omega
      let leaves := buildFoldLayerLeaves layerIdx rem tbl; have hClimb := climbZkml32_path_len leaves (by simp [leaves, buildFoldLayerLeaves]) (idx / 2) hPairLt
      have hLeafAt : leaves[idx / 2]'(by simp [leaves, buildFoldLayerLeaves]; exact hPairLt) = hashFoldPairLeaf layerIdx (idx / 2) (tbl.getD (2 * (idx / 2)) Goldilocks.zero)
            (tbl.getD (2 * (idx / 2) + 1) Goldilocks.zero) := by simp [leaves, buildFoldLayerLeaves]
      rw [hLeafAt] at hClimb; have ihStep := ih (layerIdx + 1) (idx / 2) (foldFirstVar tbl r) rs hFoldLen hPairLt hRs
      rw [hFoldElem (idx / 2) hPairLt, mleEval_foldFirstVar] at ihStep; simp only [buildFoldRoots, openFoldWalk, verifyFoldWalk]
      rw [hClimb, hLo, hHi, decide_eq_true hSide]; simpa using ihStep
/-- Witness-pinned fold-pair discrepancy: at some butterfly layer along `idx`'s trajectory,
    a Merkle-authenticated pair `(st.lo, st.hi)` in `roots` disagrees with the honest folded table. -/
def FoldPairDiscrepancy : Nat → Nat → Nat → List Goldilocks → List Goldilocks → List Digest32 → List FoldLayerStep → Prop
  | _, 0, _, _, _, _, _ => False | layerIdx, rem + 1, idx, tbl, r :: rs, root :: roots, st :: steps =>
    let pairIdx := idx / 2
    (climbMerkle32 zkmlMerkleHash32 (2 ^ rem) pairIdx (hashFoldPairLeaf layerIdx pairIdx st.lo st.hi) st.merklePath = some root ∧ (st.lo ≠ tbl.getD (2 * pairIdx) Goldilocks.zero ∨
       st.hi ≠ tbl.getD (2 * pairIdx + 1) Goldilocks.zero)) ∨
    FoldPairDiscrepancy (layerIdx + 1) rem pairIdx (foldFirstVar tbl r) rs roots steps
  | _, _ + 1, _, _, _, _, _ => False
theorem openFoldWalk_no_discrepancy (rem : Nat) : ∀ (layerIdx idx : Nat) (tbl rs : List Goldilocks), ¬ FoldPairDiscrepancy layerIdx rem idx tbl rs
          (buildFoldRoots layerIdx rem tbl rs) (openFoldWalk layerIdx rem idx tbl rs) := by
  induction rem with
  | zero => intros; simp [FoldPairDiscrepancy] | succ rem ih =>
    intro layerIdx idx tbl rs; cases rs with
    | nil => simp [FoldPairDiscrepancy] | cons r rs =>
      simp only [buildFoldRoots, openFoldWalk, FoldPairDiscrepancy, ne_eq, not_true_eq_false, or_self, and_false, false_or]
      exact ih (layerIdx + 1) (idx / 2) (foldFirstVar tbl r) rs
theorem verifyFoldWalk_deviates_pair (rem : Nat) : ∀ (layerIdx idx : Nat) (curVal expectedFinal : Goldilocks)
      (tbl rs : List Goldilocks) (roots : List Digest32) (steps : List FoldLayerStep) (hTbl : tbl.length = 2 ^ rem) (hIdx : idx < 2 ^ rem) (_hRs : rs.length = rem),
      curVal = (tbl[idx]'(by omega)) → expectedFinal ≠ mleEval tbl rs → verifyFoldWalk layerIdx rem idx curVal expectedFinal rs roots steps = true →
      FoldPairDiscrepancy layerIdx rem idx tbl rs roots steps := by
  induction rem with
  | zero =>
    intro _ idx curVal expectedFinal tbl rs roots steps hTbl hIdx hRs hCur hNe hVer; have hi0 : idx = 0 := by simp at hIdx; exact hIdx
    subst hi0; cases rs with
    | cons _ _ => simp at hRs
    | nil => cases tbl with
      | nil => simp at hTbl | cons v₀ tl =>
        have htl : tl = [] := by simp at hTbl; exact hTbl
        subst htl; simp only [verifyFoldWalk, Bool.and_eq_true, decide_eq_true_eq] at hVer; have hMle : mleEval [v₀] [] = v₀ := by
          simp only [mleEval, List.length_nil, hypercube, List.map_cons, List.map_nil, eqPoly, innerProd]
          change CommRingOps.add (CommRingOps.mul v₀ CommRingOps.one) CommRingOps.zero = v₀; rw [LawfulCommRing.mul_one, LawfulCommRing.add_zero]
        exact absurd (hVer.2.symm.trans (hCur.trans hMle.symm)) hNe
  | succ rem ih =>
    intro layerIdx idx curVal expectedFinal tbl rs roots steps hTbl hIdx hRs _hCur hNe hVer; cases rs with
    | nil => simp at hRs
    | cons r rs => cases roots with
      | nil => simp [verifyFoldWalk] at hVer
      | cons root roots => cases steps with
        | nil => simp [verifyFoldWalk] at hVer | cons st steps =>
          simp only [List.length_cons, Nat.succ.injEq] at hRs; simp only [verifyFoldWalk, Bool.and_eq_true, decide_eq_true_eq, climbZkml32_iff] at hVer
          obtain ⟨⟨_, ⟨rOut, hCl, hBytes⟩⟩, hRec⟩ := hVer
          have hClRoot : climbMerkle32 zkmlMerkleHash32 (2 ^ rem) (idx / 2) (hashFoldPairLeaf layerIdx (idx / 2) st.lo st.hi) st.merklePath = some root :=
            hCl.trans (congrArg some (Digest32.ext hBytes))
          if hLo : st.lo = tbl.getD (2 * (idx / 2)) Goldilocks.zero then
            if hHi : st.hi = tbl.getD (2 * (idx / 2) + 1) Goldilocks.zero then
              have hEven : tbl.length = 2 * 2 ^ rem := by rw [hTbl, Nat.pow_succ, Nat.mul_comm]
              obtain ⟨hFoldLen, hFoldElem⟩ := foldFirstVar_even_spec (2 ^ rem) tbl r hEven; have hPairLt : idx / 2 < 2 ^ rem := by rw [Nat.pow_succ] at hIdx; omega
              have hLoG : tbl.getD (2 * (idx / 2)) Goldilocks.zero = tbl[2 * (idx / 2)]'(by omega) := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hHiG : tbl.getD (2 * (idx / 2) + 1) Goldilocks.zero = tbl[2 * (idx / 2) + 1]'(by omega) := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hNextCur : CommRingOps.add st.lo (CommRingOps.mul r (CommRingOps.sub st.hi st.lo)) = (foldFirstVar tbl r)[idx / 2]'(by omega) := by
                rw [hLo, hHi, hLoG, hHiG, hFoldElem (idx / 2) hPairLt]
              have hNextNe : expectedFinal ≠ mleEval (foldFirstVar tbl r) rs := by rwa [mleEval_foldFirstVar]
              exact .inr (ih (layerIdx + 1) (idx / 2) _ expectedFinal (foldFirstVar tbl r) rs roots steps hFoldLen hPairLt hRs hNextCur hNextNe hRec)
            else exact .inl ⟨hClRoot, .inr hHi⟩
          else exact .inl ⟨hClRoot, .inl hLo⟩
def seqFindMapRange {α : Type} (scan : Nat → Option α) : Nat → Nat → Option (Nat × α)
  | _, 0 => none | base, len + 1 =>
    match scan base with | some v => some (base, v) | none => seqFindMapRange scan (base + 1) len
def windowedFindMapLoop {α : Type} (scan : Nat → Option α) (win : Nat) : Nat → Nat → Option (Nat × α)
  | _, 0 => none | base, rem + 1 =>
    let wLen := Nat.min (Nat.max win 1) (rem + 1)
    match seqFindMapRange scan base wLen with
    | some hit => some hit | none => windowedFindMapLoop scan win (base + wLen) (rem + 1 - wLen)
termination_by _ rem => rem
decreasing_by
  have : 1 ≤ Nat.min (Nat.max win 1) (rem + 1) := Nat.le_min.mpr ⟨Nat.le_max_right win 1, by omega⟩
  omega
def windowedFindMapFirst {α : Type} (span window : Nat) (scan : Nat → Option α) : Option (Nat × α) := windowedFindMapLoop scan window 0 span
private theorem seqFindMapRange_split {α : Type} (scan : Nat → Option α) (k : Nat) : ∀ (base m : Nat), seqFindMapRange scan base (k + m) =
        match seqFindMapRange scan base k with | some hit => some hit | none => seqFindMapRange scan (base + k) m := by
  induction k with
  | zero => intro base m; simp [seqFindMapRange] | succ k ih =>
    intro base m; have hAdd : k + 1 + m = k + m + 1 := by omega
    have hBase : base + 1 + k = base + (k + 1) := by omega
    rw [hAdd]; simp only [seqFindMapRange]; cases scan base with | some _ => rfl | none => rw [ih (base + 1) m, hBase]
theorem windowedFindMapLoop_eq_seq {α : Type} (scan : Nat → Option α) (win : Nat) : ∀ (base rem : Nat), windowedFindMapLoop scan win base rem = seqFindMapRange scan base rem := by
  intro base rem
  induction rem using Nat.strongRecOn generalizing base with
  | ind rem ih =>
    cases rem with
    | zero => simp [windowedFindMapLoop, seqFindMapRange] | succ r =>
      unfold windowedFindMapLoop; let wLen := Nat.min (Nat.max win 1) (r + 1); have hwPos : 1 ≤ wLen := Nat.le_min.mpr ⟨Nat.le_max_right win 1, by omega⟩
      have hwLe : wLen ≤ r + 1 := Nat.min_le_right _ _; have hSplit : r + 1 = wLen + (r + 1 - wLen) := by omega
      conv => rhs; rw [hSplit, seqFindMapRange_split scan wLen base (r + 1 - wLen)]
      dsimp only [wLen]; cases seqFindMapRange scan base wLen with
      | some _ => rfl | none => exact ih (r + 1 - wLen) (by omega) (base + wLen)
theorem seqFindMapRange_minimal {α : Type} (scan : Nat → Option α) (len : Nat) : ∀ {base w : Nat} {val : α}, seqFindMapRange scan base len = some (w, val) →
      base ≤ w ∧ w < base + len ∧ scan w = some val ∧ ∀ u, base ≤ u → u < w → scan u = none := by
  induction len with
  | zero => intro _ _ _ h; cases h | succ len ih =>
    intro base w val h; simp only [seqFindMapRange] at h; cases hs : scan base with
    | some v0 =>
      rw [hs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
      exact ⟨Nat.le_refl _, by omega, hs, fun _ hge hlt => absurd hlt (Nat.not_lt_of_ge hge)⟩
    | none =>
      rw [hs] at h; obtain ⟨hge, hlt, hsw, hnone⟩ := ih h; refine ⟨by omega, by omega, hsw, fun u huGe huLt => ?_⟩
      if heq : u = base then subst heq; exact hs else exact hnone u (by omega) huLt
theorem windowedFindMapFirst_minimal_and_pred_invalid {α : Type} (span window : Nat) (scan : Nat → Option α) {w : Nat} {val : α}
    (h : windowedFindMapFirst span window scan = some (w, val)) : windowedFindMapFirst span 1 scan = some (w, val) ∧
    w < span ∧ scan w = some val ∧ (∀ u < w, scan u = none) ∧ (0 < w → scan (w - 1) = none) := by
  unfold windowedFindMapFirst at h ⊢; rw [windowedFindMapLoop_eq_seq] at h ⊢; obtain ⟨_, hlt, hsw, hnone⟩ := seqFindMapRange_minimal scan span h
  exact ⟨h, by omega, hsw, fun u hu => hnone u (Nat.zero_le u) hu, fun hwPos => hnone (w - 1) (Nat.zero_le _) (by omega)⟩
def digestLow64LE (d : ByteArray) : Nat :=
  (d.data.getD 0 0).toNat + (d.data.getD 1 0).toNat * 256 + (d.data.getD 2 0).toNat * 65536 +
  (d.data.getD 3 0).toNat * 16777216 + (d.data.getD 4 0).toNat * 4294967296 +
  (d.data.getD 5 0).toNat * 1099511627776 + (d.data.getD 6 0).toNat * 281474976710656 +
  (d.data.getD 7 0).toNat * 72057594037927936
@[expose] def checkChunkPow (powBits : Nat) (digest : ByteArray) : Bool := decide (powBits ≤ 64) && decide (digestLow64LE digest % (2 ^ powBits) = 0)
theorem checkChunkPow_zero (d : ByteArray) : checkChunkPow 0 d = true := by simp [checkChunkPow, Nat.mod_one]
def zkmlDClaimLabel : ByteArray := "ZKML.D.CLAIM".toUTF8
def zkmlFoldRootsLabel : ByteArray := "ZKML.FOLD.ROOTS".toUTF8
def zkmlPowNonceLabel : ByteArray := "ZKML.POW.NONCE".toUTF8
def powCandidateState {phase : TranscriptPhase} [CanSqueezeTranscript phase] (trPostFold : Transcript phase) (nonce : UInt64) : ByteArray :=
  (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 nonce)) trPostFold).state
def grindChunkPowWindowed {phase : TranscriptPhase} [CanSqueezeTranscript phase] (powBits span window : Nat) (trPostFold : Transcript phase) : Option UInt64 :=
  (windowedFindMapFirst span window (fun u =>
    if decide (u < 2 ^ 64) && checkChunkPow powBits (powCandidateState trPostFold (UInt64.ofNat u)) then
      some (UInt64.ofNat u)
    else none)).map Prod.snd
theorem grindChunkPowWindowed_sound_and_pred_invalid {phase : TranscriptPhase} [CanSqueezeTranscript phase] {powBits span window : Nat} {trPostFold : Transcript phase} {w : UInt64}
    (h : grindChunkPowWindowed powBits span window trPostFold = some w) : checkChunkPow powBits (powCandidateState trPostFold w) = true ∧
    (0 < w.toNat → checkChunkPow powBits (powCandidateState trPostFold (w - 1)) = false) := by
  unfold grindChunkPowWindowed at h; cases hWin : windowedFindMapFirst span window _ with
  | none => rw [hWin] at h; cases h | some hit =>
    rcases hit with ⟨u, cand⟩; rw [hWin] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    obtain ⟨_, _, hsu, _, hpred⟩ := windowedFindMapFirst_minimal_and_pred_invalid span window _ hWin
    cases hCond : (decide (u < 2 ^ 64) && checkChunkPow powBits (powCandidateState trPostFold (UInt64.ofNat u)))
    · rw [hCond] at hsu; cases hsu
    · rw [hCond] at hsu; simp only [↓reduceIte, Option.some.injEq] at hsu; simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
      have huVal : (UInt64.ofNat u).toNat = u := Nat.mod_eq_of_lt hCond.1; refine ⟨hsu ▸ hCond.2, fun hwPos => ?_⟩
      have huPos : 0 < u := by rw [← hsu, huVal] at hwPos; exact hwPos
      have hPredNone := hpred huPos; have hSubLt : u - 1 < 2 ^ 64 := by omega
      have hSubEq : UInt64.ofNat (u - 1) = cand - 1 := by
        apply UInt64.toNat_inj.mp
        rw [← hsu, UInt64.toNat_sub_of_le]
        · simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hSubLt, huVal]
        · show (1 : UInt64).toNat ≤ (UInt64.ofNat u).toNat; simp [huVal]; omega
      rw [decide_eq_true hSubLt, Bool.true_and, hSubEq] at hPredNone; cases hChk : checkChunkPow powBits (powCandidateState trPostFold (cand - 1))
      · rfl
      · rw [hChk] at hPredNone; simp at hPredNone
private theorem windowedFindMapFirst_one_some {α : Type} (scan : Nat → Option α) (v : α) (h : scan 0 = some v) : windowedFindMapFirst 1 1 scan = some (0, v) := by
  unfold windowedFindMapFirst; rw [windowedFindMapLoop_eq_seq]; simp only [seqFindMapRange, h]
private theorem grindScan_zero_eq (b : ByteArray) : (if decide (0 < 2 ^ 64) && checkChunkPow 0 b then some (UInt64.ofNat 0) else none) = some 0 := by
  have h0 : decide (0 < 2 ^ 64) = true := decide_eq_true (Nat.two_pow_pos 64); rw [h0, checkChunkPow_zero]; rfl
private theorem grindChunkPowWindowed_zero_span1 (tr : Transcript .instanceBound) : grindChunkPowWindowed 0 1 1 tr = some 0 :=
  let scan : Nat → Option UInt64 := fun u =>
    if decide (u < 2 ^ 64) && checkChunkPow 0 (powCandidateState tr (UInt64.ofNat u)) then
      some (UInt64.ofNat u)
    else none
  congrArg (Option.map Prod.snd) (windowedFindMapFirst_one_some scan 0 (grindScan_zero_eq (powCandidateState tr (UInt64.ofNat 0))))
theorem windowedFindMapFirst_inhabited : ∃ (tr : Transcript .instanceBound) (w : UInt64),
      grindChunkPowWindowed 0 1 1 tr = some w ∧ checkChunkPow 0 (powCandidateState tr w) = true :=
  let tr₀ := (bindInstance ByteArray.empty (bindRelation "ZKML" ByteArray.empty ByteArray.empty (Transcript.newUnseeded ByteArray.empty))).transcript
  ⟨tr₀, 0, grindChunkPowWindowed_zero_span1 tr₀, checkChunkPow_zero _⟩
def squeezeGoldilocksVec {phase : TranscriptPhase} [CanSqueezeTranscript phase] : Nat → Transcript phase → List Goldilocks × Transcript phase
  | 0, tr => ([], tr)
  | n + 1, tr => let (r, tr') := squeezeGoldilocks tr; let (rs, trEnd) := squeezeGoldilocksVec n tr'; (r :: rs, trEnd)
theorem squeezeGoldilocksVec_length {phase : TranscriptPhase} [CanSqueezeTranscript phase] : ∀ (n : Nat) (tr : Transcript phase), (squeezeGoldilocksVec n tr).1.length = n
  | 0, _ => rfl | n + 1, _ => by simp [squeezeGoldilocksVec, squeezeGoldilocksVec_length n]
def squeezeRawQueries {phase : TranscriptPhase} [CanSqueezeTranscript phase] : Nat → Transcript phase → List Nat × Transcript phase
  | 0, tr => ([], tr) | q + 1, tr =>
    let (⟨bytes, _⟩, tr') := squeezeChallenge256 tr; let (rest, trEnd) := squeezeRawQueries q tr'
    (digestLow64LE bytes :: rest, trEnd)
theorem squeezeRawQueries_length {phase : TranscriptPhase} [CanSqueezeTranscript phase] : ∀ (q : Nat) (tr : Transcript phase), (squeezeRawQueries q tr).1.length = q
  | 0, _ => rfl | q + 1, _ => by simp [squeezeRawQueries, squeezeRawQueries_length q]
/-! ## 3. Characteristic-Free Quadratic/Cubic Sumcheck & `(F₁, F_{≥2}, S)` `EinSumcheck` -/
private theorem mul_two_pow_succ (m rem : Nat) : m * 2 ^ (rem + 1) = 2 * (m * 2 ^ rem) := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (m * 2 ^ rem) 2]
private theorem half_two_mul (n : Nat) : (2 * n + 1) / 2 = n := by omega
def foldVars {R : Type} [CommRingOps R] : List R → List R → List R
  | tbl, [] => tbl | tbl, r :: rs => foldVars (foldFirstVar tbl r) rs
@[simp] private theorem foldVars_nil {R : Type} [CommRingOps R] (tbl : List R) : foldVars tbl [] = tbl := rfl
theorem mleEval_foldVars {R : Type} [LawfulCommRing R] : ∀ (rs₁ : List R) (tbl rs₂ : List R), mleEval (foldVars tbl rs₁) rs₂ = mleEval tbl (rs₁ ++ rs₂)
  | [], _, _ => rfl
  | r :: rs₁, tbl, rs₂ => by simp only [foldVars, List.cons_append, mleEval_foldVars rs₁, mleEval_foldFirstVar]
theorem foldVars_full_eq_singleton {R : Type} [LawfulCommRing R] : ∀ (rs : List R) (tbl : List R), tbl.length = 2 ^ rs.length → foldVars tbl rs = [mleEval tbl rs]
  | [], tbl, hlen => by
    cases tbl with
    | nil => simp at hlen | cons v₀ tl =>
      have htl : tl = [] := by simp at hlen; exact hlen
      subst htl; simp only [foldVars, mleEval, List.length_nil, hypercube, List.map_cons, List.map_nil, eqPoly, innerProd, List.cons.injEq, and_true]
      change v₀ = CommRingOps.add (CommRingOps.mul v₀ CommRingOps.one) CommRingOps.zero; rw [LawfulCommRing.mul_one, LawfulCommRing.add_zero]
  | r :: rs, tbl, hlen => by
    have hNext : (foldFirstVar tbl r).length = 2 ^ rs.length := by
      have h2 : tbl.length = 2 * 2 ^ rs.length := by rw [hlen, List.length_cons, Nat.pow_succ, Nat.mul_comm]
      rw [foldFirstVar_length, h2, half_two_mul]
    simp only [foldVars, foldVars_full_eq_singleton rs (foldFirstVar tbl r) hNext, mleEval_foldFirstVar]
private theorem foldVars_length_mul {R : Type} [CommRingOps R] : ∀ (rs : List R) (m : Nat) (xs : List R), xs.length = m * 2 ^ rs.length → (foldVars xs rs).length = m
  | [], _, _, hx => by simpa [foldVars_nil] using hx
  | r :: rs, m, xs, hx => by
    have h2 : xs.length = 2 * (m * 2 ^ rs.length) := by rw [hx, List.length_cons, mul_two_pow_succ]
    exact foldVars_length_mul rs m (foldFirstVar xs r) (by rw [foldFirstVar_length, h2, half_two_mul])
theorem foldFirstVar_append_even {R : Type} [CommRingOps R] (k : Nat) :
    ∀ (a b : List R) (r : R), a.length = 2 * k → foldFirstVar (a ++ b) r = foldFirstVar a r ++ foldFirstVar b r := by
  induction k with
  | zero => intro a _ _ ha; cases a with | nil => rfl | cons _ _ => simp at ha
  | succ k ih =>
    intro a b r ha; cases a with
    | nil => simp at ha
    | cons x₀ tl => cases tl with
      | nil => simp only [List.length_cons, List.length_nil] at ha; omega | cons x₁ rest =>
        simp only [List.cons_append, foldFirstVar]; rw [ih rest b r (by simp only [List.length_cons] at ha; omega)]
def tileBlocks {R : Type} (m : Nat) (base : List R) : List R :=
  match m with | 0 => [] | m' + 1 => base ++ tileBlocks m' base
private theorem tileBlocks_succ {R : Type} (m : Nat) (base : List R) : tileBlocks (m + 1) base = base ++ tileBlocks m base := rfl
theorem tileBlocks_length {R : Type} : ∀ (m : Nat) (base : List R), (tileBlocks m base).length = m * base.length
  | 0, _ => by simp [tileBlocks]
  | m + 1, base => by rw [tileBlocks_succ, List.length_append, tileBlocks_length m, Nat.succ_mul, Nat.add_comm]
theorem foldFirstVar_tileBlocks {R : Type} [CommRingOps R] (k : Nat) : ∀ (m : Nat) (base : List R) (r : R), base.length = 2 * k →
      foldFirstVar (tileBlocks m base) r = tileBlocks m (foldFirstVar base r)
  | 0, _, _, _ => rfl
  | m + 1, base, r, hlen => by rw [tileBlocks_succ, foldFirstVar_append_even k base _ r hlen, foldFirstVar_tileBlocks k m base r hlen, tileBlocks_succ]
private theorem foldVars_tileBlocks {R : Type} [CommRingOps R] (m : Nat) : ∀ (rs : List R) (k : Nat) (base : List R), base.length = k * 2 ^ rs.length →
      foldVars (tileBlocks m base) rs = tileBlocks m (foldVars base rs)
  | [], _, _, _ => rfl
  | r :: rs, k, base, hb => by
    have h2 : base.length = 2 * (k * 2 ^ rs.length) := by rw [hb, List.length_cons, mul_two_pow_succ]
    simp only [foldVars, foldFirstVar_tileBlocks (k * 2 ^ rs.length) m base r h2]
    exact foldVars_tileBlocks m rs k (foldFirstVar base r) (by rw [foldFirstVar_length, h2, half_two_mul])
def scaleList {R : Type} [CommRingOps R] (c : R) (xs : List R) : List R := xs.map (CommRingOps.mul c)
def vecAddList {R : Type} [CommRingOps R] : List R → List R → List R := List.zipWith CommRingOps.add
private theorem scaleList_cons {R : Type} [CommRingOps R] (c x : R) (xs : List R) : scaleList c (x :: xs) = CommRingOps.mul c x :: scaleList c xs := rfl
private theorem vecAddList_cons {R : Type} [CommRingOps R] (a b : R) (as bs : List R) : vecAddList (a :: as) (b :: bs) = CommRingOps.add a b :: vecAddList as bs := rfl
theorem foldFirstVar_scaleList {R : Type} [LawfulCommRing R] (k : Nat) (c r : R) :
    ∀ (xs : List R), xs.length = 2 * k → foldFirstVar (scaleList c xs) r = scaleList c (foldFirstVar xs r) := by
  induction k with
  | zero => intro xs h; cases xs with | nil => rfl | cons _ _ => simp at h
  | succ k ih =>
    intro xs h; cases xs with
    | nil => simp at h
    | cons x₀ tl => cases tl with
      | nil => simp only [List.length_cons, List.length_nil] at h; omega | cons x₁ rest =>
        rw [scaleList_cons, scaleList_cons, foldFirstVar, foldFirstVar, scaleList_cons, ih rest (by simp only [List.length_cons] at h; omega)]
        congr 1; rw [← LawfulCommRing.mul_sub, ← LawfulCommRing.mul_assoc r c, LawfulCommRing.mul_comm r c, LawfulCommRing.mul_assoc c r, ← LawfulCommRing.left_distrib]
private theorem foldVars_scaleList {R : Type} [LawfulCommRing R] (c : R) : ∀ (rs : List R) (xs : List R), xs.length = 2 ^ rs.length →
      foldVars (scaleList c xs) rs = scaleList c (foldVars xs rs)
  | [], _, _ => rfl
  | r :: rs, xs, hx => by
    have h2 : xs.length = 2 * 2 ^ rs.length := by rw [hx, List.length_cons, Nat.pow_succ, Nat.mul_comm]
    simp only [foldVars, foldFirstVar_scaleList (2 ^ rs.length) c r xs h2]; exact foldVars_scaleList c rs (foldFirstVar xs r) (by rw [foldFirstVar_length, h2, half_two_mul])
theorem innerProd_scaleList_left {R : Type} [LawfulCommRing R] (c : R) : ∀ (xs ys : List R), innerProd (scaleList c xs) ys = CommRingOps.mul c (innerProd xs ys)
  | [], _ => by simp [scaleList, innerProd, LawfulCommRing.mul_zero]
  | _ :: _, [] => by simp [scaleList, innerProd, LawfulCommRing.mul_zero]
  | x :: xs, y :: ys => by rw [scaleList_cons, innerProd, innerProd, innerProd_scaleList_left c xs ys, LawfulCommRing.mul_assoc, LawfulCommRing.left_distrib]
private theorem innerProd_scaleList_right {R : Type} [LawfulCommRing R] (c : R) : ∀ (xs ys : List R), innerProd xs (scaleList c ys) = CommRingOps.mul (innerProd xs ys) c
  | [], _ => by simp [innerProd, LawfulCommRing.zero_mul]
  | _ :: _, [] => by simp [scaleList, innerProd, LawfulCommRing.zero_mul]
  | x :: xs, y :: ys => by
    rw [scaleList_cons, innerProd, innerProd, innerProd_scaleList_right c xs ys, LawfulCommRing.right_distrib]
    congr 1; rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x c, LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm c]
private theorem innerProd_append {R : Type} [LawfulCommRing R] : ∀ (u₁ u₂ v₁ v₂ : List R), u₁.length = v₁.length →
      innerProd (u₁ ++ u₂) (v₁ ++ v₂) = CommRingOps.add (innerProd u₁ v₁) (innerProd u₂ v₂)
  | [], _, [], _, _ => by simp [innerProd, LawfulCommRing.zero_add]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | x :: xs, u₂, y :: ys, v₂, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h; simp only [List.cons_append, innerProd, innerProd_append xs u₂ ys v₂ h, LawfulCommRing.add_assoc]
theorem innerProd_vecAdd_left {R : Type} [LawfulCommRing R] : ∀ (xs₁ xs₂ ys : List R), xs₁.length = xs₂.length →
      innerProd (vecAddList xs₁ xs₂) ys = CommRingOps.add (innerProd xs₁ ys) (innerProd xs₂ ys)
  | [], [], _, _ => by simp [vecAddList, innerProd, LawfulCommRing.add_zero]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | _ :: _, _ :: _, [], _ => by simp [vecAddList, innerProd, LawfulCommRing.add_zero]
  | x₁ :: xs₁, x₂ :: xs₂, y :: ys, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    rw [vecAddList_cons, innerProd, innerProd, innerProd, innerProd_vecAdd_left xs₁ xs₂ ys h, LawfulCommRing.right_distrib, LawfulCommRing.add_add_add_comm]
theorem mleEval_scaleList {R : Type} [LawfulCommRing R] (c : R) (xs rs : List R) :
    mleEval (scaleList c xs) rs = CommRingOps.mul c (mleEval xs rs) := innerProd_scaleList_left c xs _
theorem mleEval_vecAddList {R : Type} [LawfulCommRing R] {xs₁ xs₂ : List R} (rs : List R) (h : xs₁.length = xs₂.length) :
    mleEval (vecAddList xs₁ xs₂) rs = CommRingOps.add (mleEval xs₁ rs) (mleEval xs₂ rs) := innerProd_vecAdd_left xs₁ xs₂ _ h
def eqTable {R : Type} [CommRingOps R] (xs : List R) : List R := (hypercube xs.length).map (eqPoly xs)
theorem eqTable_length {R : Type} [CommRingOps R] (xs : List R) : (eqTable xs).length = 2 ^ xs.length := by simp [eqTable, hypercube_length]
def eqPolyVec {R : Type} [CommRingOps R] : List R → List R → R
  | [], [] => CommRingOps.one | x :: xs, y :: ys =>
    CommRingOps.mul (CommRingOps.add (CommRingOps.mul (CommRingOps.sub CommRingOps.one x) (CommRingOps.sub CommRingOps.one y)) (CommRingOps.mul x y)) (eqPolyVec xs ys)
  | _, _ => CommRingOps.zero
private theorem foldFirstVar_flatMap_pair {R : Type} [LawfulCommRing R] (x y : R) : ∀ (ws : List R),
      foldFirstVar (ws.flatMap fun w => [CommRingOps.mul (CommRingOps.sub CommRingOps.one x) w, CommRingOps.mul x w]) y =
        scaleList (CommRingOps.add (CommRingOps.mul (CommRingOps.sub CommRingOps.one x) (CommRingOps.sub CommRingOps.one y)) (CommRingOps.mul x y)) ws
  | [] => rfl
  | w :: ws => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, foldFirstVar]; rw [foldFirstVar_flatMap_pair x y ws, scaleList_cons]; congr 1
    rw [LawfulCommRing.foldStep_eq_barycentric, LawfulCommRing.right_distrib, ← LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc,
        LawfulCommRing.mul_comm (CommRingOps.sub CommRingOps.one y) (CommRingOps.sub CommRingOps.one x), LawfulCommRing.mul_comm y x]
theorem foldVars_eqTable {R : Type} [LawfulCommRing R] : ∀ (xs ys : List R), xs.length = ys.length → foldVars (eqTable xs) ys = [eqPolyVec xs ys]
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | x :: xs, y :: ys, hlen => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    have hStep : foldFirstVar (eqTable (x :: xs)) y = scaleList (CommRingOps.add (CommRingOps.mul (CommRingOps.sub CommRingOps.one x)
          (CommRingOps.sub CommRingOps.one y)) (CommRingOps.mul x y)) (eqTable xs) := by
      unfold eqTable; simp only [List.length_cons, hypercube]; rw [flatMap_eqPoly_cons, foldFirstVar_flatMap_pair]
    rw [foldVars, hStep, foldVars_scaleList _ ys (eqTable xs) (hlen ▸ eqTable_length xs), foldVars_eqTable xs ys hlen]; rfl
def evalHorner {R : Type} [CommRingOps R] : List R → R → R
  | [], _ => CommRingOps.zero | c :: cs, x => CommRingOps.add c (CommRingOps.mul x (evalHorner cs x))
def evalPoly {R : Type} [CommRingOps R] (p : RoundPoly R) (x : R) : R := evalHorner p.coeffs x
@[expose] def degLePoly {R : Type} (maxDeg : Nat) (p : RoundPoly R) : Bool := decide (p.coeffs.length ≤ maxDeg + 1)
private theorem evalHorner_vecAdd {R : Type} [LawfulCommRing R] (r : R) : ∀ (cs ds : List R), cs.length = ds.length →
      evalHorner (vecAddList cs ds) r = CommRingOps.add (evalHorner cs r) (evalHorner ds r)
  | [], [], _ => by simp [vecAddList, evalHorner, LawfulCommRing.add_zero]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, d :: ds, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    rw [vecAddList_cons, evalHorner, evalHorner, evalHorner, evalHorner_vecAdd r cs ds h, LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]
def quadPairCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | a₀ :: a₁ :: as, b₀ :: b₁ :: bs =>
    let da := CommRingOps.sub a₁ a₀; let db := CommRingOps.sub b₁ b₀
    vecAddList [CommRingOps.mul a₀ b₀, CommRingOps.add (CommRingOps.mul a₀ db) (CommRingOps.mul da b₀), CommRingOps.mul da db] (quadPairCoeffs as bs)
  | _, _ => [CommRingOps.zero, CommRingOps.zero, CommRingOps.zero]
private theorem quadPairCoeffs_length {R : Type} [CommRingOps R] : ∀ (A B : List R), (quadPairCoeffs A B).length = 3
  | _ :: _ :: as, _ :: _ :: bs => by simp [quadPairCoeffs, vecAddList, quadPairCoeffs_length as bs]
  | [], _ => rfl | [_], _ => rfl | _ :: _ :: _, [] => rfl | _ :: _ :: _, [_] => rfl
def quadPairRoundPoly {R : Type} [CommRingOps R] (A B : List R) : RoundPoly R := ⟨quadPairCoeffs A B⟩
theorem quadPairRoundPoly_degLe {R : Type} [CommRingOps R] (A B : List R) :
    degLePoly 2 (quadPairRoundPoly A B) = true := by simp [degLePoly, quadPairRoundPoly, quadPairCoeffs_length]
private theorem linear_pair_horner {R : Type} [LawfulCommRing R] (a₀ da b₀ db r : R) :
    CommRingOps.mul (CommRingOps.add a₀ (CommRingOps.mul r da)) (CommRingOps.add b₀ (CommRingOps.mul r db)) =
      CommRingOps.add (CommRingOps.mul a₀ b₀) (CommRingOps.mul r (CommRingOps.add (CommRingOps.add (CommRingOps.mul a₀ db) (CommRingOps.mul da b₀))
        (CommRingOps.mul r (CommRingOps.mul da db)))) := by
  have h1 : CommRingOps.mul a₀ (CommRingOps.mul r db) = CommRingOps.mul r (CommRingOps.mul a₀ db) := by
    rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm a₀ r, LawfulCommRing.mul_assoc]
  have h2 : CommRingOps.mul (CommRingOps.mul r da) b₀ = CommRingOps.mul r (CommRingOps.mul da b₀) := LawfulCommRing.mul_assoc r da b₀
  have h3 : CommRingOps.mul (CommRingOps.mul r da) (CommRingOps.mul r db) = CommRingOps.mul r (CommRingOps.mul r (CommRingOps.mul da db)) := by
    rw [LawfulCommRing.mul_assoc r da, ← LawfulCommRing.mul_assoc da r db, LawfulCommRing.mul_comm da r, LawfulCommRing.mul_assoc r da db]
  calc CommRingOps.mul (CommRingOps.add a₀ (CommRingOps.mul r da)) (CommRingOps.add b₀ (CommRingOps.mul r db))
    _ = CommRingOps.add (CommRingOps.add (CommRingOps.mul a₀ b₀) (CommRingOps.mul a₀ (CommRingOps.mul r db))) (CommRingOps.add (CommRingOps.mul (CommRingOps.mul r da) b₀)
                           (CommRingOps.mul (CommRingOps.mul r da) (CommRingOps.mul r db))) := by
          rw [LawfulCommRing.right_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
    _ = CommRingOps.add (CommRingOps.mul a₀ b₀) (CommRingOps.add (CommRingOps.mul r (CommRingOps.mul a₀ db)) (CommRingOps.add (CommRingOps.mul r (CommRingOps.mul da b₀))
            (CommRingOps.mul r (CommRingOps.mul r (CommRingOps.mul da db))))) := by
          rw [h1, h2, h3, LawfulCommRing.add_assoc]
    _ = CommRingOps.add (CommRingOps.mul a₀ b₀) (CommRingOps.mul r (CommRingOps.add (CommRingOps.add (CommRingOps.mul a₀ db) (CommRingOps.mul da b₀))
          (CommRingOps.mul r (CommRingOps.mul da db)))) := by
          rw [← LawfulCommRing.left_distrib, ← LawfulCommRing.left_distrib, LawfulCommRing.add_assoc]
theorem quadPairRoundPoly_eval {R : Type} [LawfulCommRing R] (k : Nat) : ∀ (A B : List R) (r : R), A.length = 2 * k → B.length = 2 * k →
      evalPoly (quadPairRoundPoly A B) r = innerProd (foldFirstVar A r) (foldFirstVar B r) := by
  induction k with
  | zero =>
    intro A B r hA hB; cases A with | cons _ _ => simp at hA | nil =>
    cases B with | cons _ _ => simp at hB | nil =>
    simp [evalPoly, quadPairRoundPoly, quadPairCoeffs, evalHorner, foldFirstVar, innerProd, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | succ k ih =>
    intro A B r hA hB; cases A with | nil => simp at hA | cons a₀ tlA => cases tlA with
      | nil => simp only [List.length_cons, List.length_nil] at hA; omega
      | cons a₁ as => cases B with | nil => simp at hB | cons b₀ tlB => cases tlB with
        | nil => simp only [List.length_cons, List.length_nil] at hB; omega | cons b₁ bs =>
          have ihE := ih as bs r (by simp only [List.length_cons] at hA; omega) (by simp only [List.length_cons] at hB; omega)
          simp only [evalPoly, quadPairRoundPoly] at ihE ⊢; rw [quadPairCoeffs, evalHorner_vecAdd r _ _ (by simp [quadPairCoeffs_length]), ihE]
          simp only [evalHorner, LawfulCommRing.mul_zero, LawfulCommRing.add_zero, foldFirstVar, innerProd]; rw [linear_pair_horner]
theorem quadPairRoundPoly_sum {R : Type} [LawfulCommRing R] (k : Nat) (A B : List R) (hA : A.length = 2 * k) (hB : B.length = 2 * k) :
    CommRingOps.add (evalPoly (quadPairRoundPoly A B) CommRingOps.zero) (evalPoly (quadPairRoundPoly A B) CommRingOps.one) = innerProd A B := by
  rw [quadPairRoundPoly_eval k A B CommRingOps.zero hA hB, quadPairRoundPoly_eval k A B CommRingOps.one hA hB]
  induction k generalizing A B with
  | zero =>
    cases A with | cons _ _ => simp at hA | nil =>
    cases B with | cons _ _ => simp at hB | nil => simp [foldFirstVar, innerProd, LawfulCommRing.add_zero]
  | succ k ih =>
    cases A with | nil => simp at hA | cons a₀ tlA => cases tlA with
      | nil => simp only [List.length_cons, List.length_nil] at hA; omega
      | cons a₁ as => cases B with | nil => simp at hB | cons b₀ tlB => cases tlB with
        | nil => simp only [List.length_cons, List.length_nil] at hB; omega | cons b₁ bs =>
          simp only [foldFirstVar, innerProd, LawfulCommRing.zero_mul, LawfulCommRing.add_zero, LawfulCommRing.one_mul, LawfulCommRing.add_sub_cancel_left]
          rw [LawfulCommRing.add_add_add_comm, ih as bs (by simp only [List.length_cons] at hA; omega) (by simp only [List.length_cons] at hB; omega), LawfulCommRing.add_assoc]
def tripleInnerProd {R : Type} [CommRingOps R] : List R → List R → List R → R
  | a :: as, b :: bs, c :: cs => CommRingOps.add (CommRingOps.mul a (CommRingOps.mul b c)) (tripleInnerProd as bs cs) | _, _, _ => CommRingOps.zero
def cubicTripleCoeffs {R : Type} [CommRingOps R] : List R → List R → List R → List R
  | a₀ :: a₁ :: as, b₀ :: b₁ :: bs, c₀ :: c₁ :: cs =>
    let da := CommRingOps.sub a₁ a₀; let db := CommRingOps.sub b₁ b₀; let dc := CommRingOps.sub c₁ c₀
    let u₀ := CommRingOps.mul a₀ b₀; let u₁ := CommRingOps.add (CommRingOps.mul a₀ db) (CommRingOps.mul da b₀); let u₂ := CommRingOps.mul da db
    vecAddList [CommRingOps.mul u₀ c₀, CommRingOps.add (CommRingOps.mul u₀ dc) (CommRingOps.mul u₁ c₀),
      CommRingOps.add (CommRingOps.mul u₁ dc) (CommRingOps.mul u₂ c₀), CommRingOps.mul u₂ dc] (cubicTripleCoeffs as bs cs)
  | _, _, _ => [CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero]
private theorem cubicTripleCoeffs_length {R : Type} [CommRingOps R] : ∀ (A B C : List R), (cubicTripleCoeffs A B C).length = 4
  | _ :: _ :: as, _ :: _ :: bs, _ :: _ :: cs => by simp [cubicTripleCoeffs, vecAddList, cubicTripleCoeffs_length as bs cs]
  | [], _, _ => rfl | [_], _, _ => rfl | _ :: _ :: _, [], _ => rfl | _ :: _ :: _, [_], _ => rfl | _ :: _ :: _, _ :: _ :: _, [] => rfl | _ :: _ :: _, _ :: _ :: _, [_] => rfl
def cubicTripleRoundPoly {R : Type} [CommRingOps R] (A B C : List R) : RoundPoly R := ⟨cubicTripleCoeffs A B C⟩
theorem cubicTripleRoundPoly_degLe {R : Type} [CommRingOps R] (A B C : List R) :
    degLePoly 3 (cubicTripleRoundPoly A B C) = true := by simp [degLePoly, cubicTripleRoundPoly, cubicTripleCoeffs_length]
private theorem quad_linear_horner {R : Type} [LawfulCommRing R] (u₀ u₁ u₂ c₀ dc r : R) :
    CommRingOps.mul (CommRingOps.add u₀ (CommRingOps.mul r (CommRingOps.add u₁ (CommRingOps.mul r u₂)))) (CommRingOps.add c₀ (CommRingOps.mul r dc)) =
      evalHorner [CommRingOps.mul u₀ c₀, CommRingOps.add (CommRingOps.mul u₀ dc) (CommRingOps.mul u₁ c₀),
        CommRingOps.add (CommRingOps.mul u₁ dc) (CommRingOps.mul u₂ c₀), CommRingOps.mul u₂ dc] r := by
  rw [linear_pair_horner u₀ (CommRingOps.add u₁ (CommRingOps.mul r u₂)) c₀ dc r]; simp only [evalHorner, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]; congr 2
  have hc : CommRingOps.mul (CommRingOps.add u₁ (CommRingOps.mul r u₂)) c₀ = CommRingOps.add (CommRingOps.mul u₁ c₀) (CommRingOps.mul r (CommRingOps.mul u₂ c₀)) := by
    rw [LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc]
  have hd : CommRingOps.mul (CommRingOps.add u₁ (CommRingOps.mul r u₂)) dc = CommRingOps.add (CommRingOps.mul u₁ dc) (CommRingOps.mul r (CommRingOps.mul u₂ dc)) := by
    rw [LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc]
  calc CommRingOps.add (CommRingOps.add (CommRingOps.mul u₀ dc) (CommRingOps.mul (CommRingOps.add u₁ (CommRingOps.mul r u₂)) c₀))
         (CommRingOps.mul r (CommRingOps.mul (CommRingOps.add u₁ (CommRingOps.mul r u₂)) dc))
    _ = CommRingOps.add (CommRingOps.add (CommRingOps.mul u₀ dc) (CommRingOps.mul u₁ c₀)) (CommRingOps.add (CommRingOps.mul r (CommRingOps.mul u₂ c₀))
            (CommRingOps.add (CommRingOps.mul r (CommRingOps.mul u₁ dc)) (CommRingOps.mul r (CommRingOps.mul r (CommRingOps.mul u₂ dc))))) := by
          rw [hc, hd, ← LawfulCommRing.add_assoc (CommRingOps.mul u₀ dc), LawfulCommRing.left_distrib, LawfulCommRing.add_assoc]
    _ = CommRingOps.add (CommRingOps.add (CommRingOps.mul u₀ dc) (CommRingOps.mul u₁ c₀))
          (CommRingOps.mul r (CommRingOps.add (CommRingOps.add (CommRingOps.mul u₁ dc) (CommRingOps.mul u₂ c₀)) (CommRingOps.mul r (CommRingOps.mul u₂ dc)))) := by
          rw [← LawfulCommRing.left_distrib, ← LawfulCommRing.left_distrib, ← LawfulCommRing.add_assoc (CommRingOps.mul u₂ c₀),
              LawfulCommRing.add_comm (CommRingOps.mul u₂ c₀) (CommRingOps.mul u₁ dc)]
theorem cubicTripleRoundPoly_eval {R : Type} [LawfulCommRing R] (k : Nat) : ∀ (A B C : List R) (r : R), A.length = 2 * k → B.length = 2 * k → C.length = 2 * k →
      evalPoly (cubicTripleRoundPoly A B C) r = tripleInnerProd (foldFirstVar A r) (foldFirstVar B r) (foldFirstVar C r) := by
  induction k with
  | zero =>
    intro A B C r hA hB hC; cases A with | cons _ _ => simp at hA | nil =>
    cases B with | cons _ _ => simp at hB | nil =>
    cases C with | cons _ _ => simp at hC | nil =>
    simp [evalPoly, cubicTripleRoundPoly, cubicTripleCoeffs, evalHorner, foldFirstVar, tripleInnerProd, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | succ k ih =>
    intro A B C r hA hB hC; cases A with | nil => simp at hA | cons a₀ tlA => cases tlA with
      | nil => simp only [List.length_cons, List.length_nil] at hA; omega
      | cons a₁ as => cases B with | nil => simp at hB | cons b₀ tlB => cases tlB with
        | nil => simp only [List.length_cons, List.length_nil] at hB; omega
        | cons b₁ bs => cases C with | nil => simp at hC | cons c₀ tlC => cases tlC with
          | nil => simp only [List.length_cons, List.length_nil] at hC; omega | cons c₁ cs =>
            have ihE := ih as bs cs r (by simp only [List.length_cons] at hA; omega) (by simp only [List.length_cons] at hB; omega) (by simp only [List.length_cons] at hC; omega)
            simp only [evalPoly, cubicTripleRoundPoly] at ihE ⊢; rw [cubicTripleCoeffs, evalHorner_vecAdd r _ _ (by simp [cubicTripleCoeffs_length]), ihE]
            simp only [foldFirstVar, tripleInnerProd]; rw [← LawfulCommRing.mul_assoc (CommRingOps.add a₀ _), linear_pair_horner, quad_linear_horner]
theorem cubicTripleRoundPoly_sum {R : Type} [LawfulCommRing R] (k : Nat) (A B C : List R) (hA : A.length = 2 * k) (hB : B.length = 2 * k) (hC : C.length = 2 * k) :
    CommRingOps.add (evalPoly (cubicTripleRoundPoly A B C) CommRingOps.zero) (evalPoly (cubicTripleRoundPoly A B C) CommRingOps.one) = tripleInnerProd A B C := by
  rw [cubicTripleRoundPoly_eval k A B C CommRingOps.zero hA hB hC, cubicTripleRoundPoly_eval k A B C CommRingOps.one hA hB hC]
  induction k generalizing A B C with
  | zero =>
    cases A with | cons _ _ => simp at hA | nil =>
    cases B with | cons _ _ => simp at hB | nil =>
    cases C with | cons _ _ => simp at hC | nil => simp [foldFirstVar, tripleInnerProd, LawfulCommRing.add_zero]
  | succ k ih =>
    cases A with | nil => simp at hA | cons a₀ tlA => cases tlA with
      | nil => simp only [List.length_cons, List.length_nil] at hA; omega
      | cons a₁ as => cases B with | nil => simp at hB | cons b₀ tlB => cases tlB with
        | nil => simp only [List.length_cons, List.length_nil] at hB; omega
        | cons b₁ bs => cases C with | nil => simp at hC | cons c₀ tlC => cases tlC with
          | nil => simp only [List.length_cons, List.length_nil] at hC; omega | cons c₁ cs =>
            simp only [foldFirstVar, tripleInnerProd, LawfulCommRing.zero_mul, LawfulCommRing.add_zero, LawfulCommRing.one_mul, LawfulCommRing.add_sub_cancel_left]
            rw [LawfulCommRing.add_add_add_comm, ih as bs cs (by simp only [List.length_cons] at hA; omega)
                (by simp only [List.length_cons] at hB; omega) (by simp only [List.length_cons] at hC; omega), LawfulCommRing.add_assoc]
def einsum2OpSlice {R : Type} [CommRingOps R] (aSlices bSlices : List (List R)) (xL xR : List R) : R :=
  innerProd (aSlices.map fun aCol => mleEval aCol xL) (bSlices.map fun bCol => mleEval bCol xR)
theorem einsum2Op_mle_identity {R : Type} [LawfulCommRing R] (A_blocks B_blocks : List (List (List R))) (xL xR xS : List R) (hLenA : A_blocks.length = B_blocks.length) :
    mleEval (List.zipWith (fun aS bS => einsum2OpSlice aS bS xL xR) A_blocks B_blocks) xS = tripleInnerProd (eqTable xS) (List.replicate A_blocks.length (CommRingOps.one : R))
        (List.zipWith (fun aS bS => einsum2OpSlice aS bS xL xR) A_blocks B_blocks) := by
  unfold mleEval; have hAux : ∀ (zs eqs : List R) (n : Nat), zs.length ≤ n → innerProd zs eqs = tripleInnerProd eqs (List.replicate n (CommRingOps.one : R)) zs := by
    intro zs; induction zs with
    | nil => intros eqs n _; cases eqs <;> cases n <;> rfl | cons z zs ih =>
      intro eqs n hle; cases eqs with
      | nil => rfl
      | cons e eqs => cases n with
        | zero => simp at hle | succ n =>
          simp only [List.replicate_succ, innerProd, tripleInnerProd, LawfulCommRing.one_mul, LawfulCommRing.mul_comm z e]
          exact congrArg (CommRingOps.add (CommRingOps.mul e z)) (ih eqs n (Nat.le_of_succ_le_succ hle))
  exact hAux _ _ _ (by simp [hLenA])
theorem naive_batched_matmul_incomplete : let zTbl : List Goldilocks := [Goldilocks.ofNat 1, Goldilocks.ofNat 6]
    let aTbl : List Goldilocks := [Goldilocks.ofNat 1, Goldilocks.ofNat 2]; let bTbl : List Goldilocks := [Goldilocks.ofNat 1, Goldilocks.ofNat 3]
    let xS : List Goldilocks := [Goldilocks.ofNat 2]
    mleEval zTbl xS ≠ CommRingOps.mul (mleEval aTbl xS) (mleEval bTbl xS) ∧
    mleEval zTbl xS = tripleInnerProd (eqTable xS) aTbl bTbl := by decide
theorem gqa_rounds_and_kv_savings (logKV logG logHD logSeq : Nat) (hG : 1 ≤ logG) : logKV + logHD < (logKV + logG) + logHD ∧
    2 ^ (logSeq + logKV + logHD) < 2 ^ (logSeq + (logKV + logG) + logHD) ∧ (3 + 6 = 9 ∧ (3 + 3) + 6 = 12 ∧ 2 ^ (10 + 3 + 6) * 8 = 2 ^ (10 + 6 + 6)) :=
  ⟨by omega, Nat.pow_lt_pow_right (by decide) (by omega), ⟨rfl, rfl, rfl⟩⟩
def PolyDiscrepancyRootHit {R : Type} [CommRingOps R] (p pStar : RoundPoly R) (r : R) : Prop :=
  evalPoly p r = evalPoly pStar r ∧
  (evalPoly p CommRingOps.zero ≠ evalPoly pStar CommRingOps.zero ∨ evalPoly p CommRingOps.one ≠ evalPoly pStar CommRingOps.one)
def stepScheduledRound {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (maxDeg : Nat) (claimedSum : R) (p : RoundPoly R) (tr : Transcript phase) : Option (R × R × Transcript phase) :=
  if (p.coeffs.drop (maxDeg + 1)).isEmpty && degLePoly maxDeg p &&
      decide (CommRingOps.add (evalPoly p CommRingOps.zero) (evalPoly p CommRingOps.one) = claimedSum) then
    let (r, tr') := absorbAndSqueezeRound p tr; some (r, evalPoly p r, tr')
  else none
def verifyScheduledSumcheck {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    List Nat → R → List (RoundPoly R) → Transcript phase → Option ((List R × R) × Transcript phase)
  | [], claimedSum, [], tr => some (([], claimedSum), tr) | d :: ds, claimedSum, p :: ps, tr =>
    match stepScheduledRound d claimedSum p tr with
    | none => none | some (r, nextClaim, tr') =>
      match verifyScheduledSumcheck ds nextClaim ps tr' with
      | none => none | some ((rs, finalVal), trFinal) => some ((r :: rs, finalVal), trFinal)
  | [], _, _ :: _, _ => none | _ :: _, _, [], _ => none
inductive ScheduledSumcheckSpec {R : Type} [CommRingOps R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    List Nat → R → List (RoundPoly R) → Transcript phase → List R → R → Transcript phase → Prop where
  | nil (s : R) (tr : Transcript phase) : ScheduledSumcheckSpec [] s [] tr [] s tr
  | cons {d : Nat} {ds : List Nat} {s fv : R} {p : RoundPoly R} {ps : List (RoundPoly R)}
      {tr trOut : Transcript phase} {rs : List R} :
      p.coeffs.length ≤ d + 1 →
      CommRingOps.add (evalPoly p CommRingOps.zero) (evalPoly p CommRingOps.one) = s →
      ScheduledSumcheckSpec ds (evalPoly p (absorbAndSqueezeRound p tr).1) ps
        (absorbAndSqueezeRound p tr).2 rs fv trOut →
      ScheduledSumcheckSpec (d :: ds) s (p :: ps) tr ((absorbAndSqueezeRound p tr).1 :: rs) fv trOut
theorem verifyScheduledSumcheck_iff_spec {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    ∀ (ds : List Nat) (s fv : R) (ps : List (RoundPoly R)) (rs : List R) (tr trOut : Transcript phase), verifyScheduledSumcheck ds s ps tr = some ((rs, fv), trOut) ↔
        ScheduledSumcheckSpec ds s ps tr rs fv trOut
  | [], s, fv, [], rs, tr, trOut => by
    simp only [verifyScheduledSumcheck, Option.some.injEq, Prod.mk.injEq]; constructor
    · rintro ⟨⟨rfl, rfl⟩, rfl⟩; exact .nil _ _
    · intro h; cases h; exact ⟨⟨rfl, rfl⟩, rfl⟩
  | [], _, _, _ :: _, _, _, _ => by constructor <;> intro h <;> cases h
  | _ :: _, _, _, [], _, _, _ => by constructor <;> intro h <;> cases h
  | d :: ds, s, fv, p :: ps, rs, tr, trOut => by
    constructor
    · intro h; simp only [verifyScheduledSumcheck] at h; cases hStep : stepScheduledRound d s p tr with
      | none => rw [hStep] at h; cases h | some st =>
        rcases st with ⟨r, nextC, tr'⟩; rw [hStep] at h; dsimp only at h; cases hRec : verifyScheduledSumcheck ds nextC ps tr' with
        | none => rw [hRec] at h; cases h | some sub =>
          rcases sub with ⟨⟨rs', fv'⟩, trF⟩; rw [hRec] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
          unfold stepScheduledRound at hStep; split at hStep
          · rename_i hc; simp only [Bool.and_eq_true, List.isEmpty_iff, List.drop_eq_nil_iff, degLePoly, decide_eq_true_eq] at hc
            simp only [Option.some.injEq, Prod.mk.injEq] at hStep; rcases hStep with ⟨hr, hn, ht⟩; subst hr hn ht
            exact .cons hc.1.1 hc.2 ((verifyScheduledSumcheck_iff_spec ds _ _ ps rs' _ _).mp hRec)
          · cases hStep
    · intro h; cases h with
      | cons hLen hSum hSub =>
        have hRec := (verifyScheduledSumcheck_iff_spec ds _ _ ps _ _ _).mpr hSub
        have hDrop : (p.coeffs.drop (d + 1)).isEmpty = true := by simp [List.isEmpty_iff, List.drop_eq_nil_iff, hLen]
        have hStep : stepScheduledRound d s p tr = some ((absorbAndSqueezeRound p tr).1, evalPoly p (absorbAndSqueezeRound p tr).1, (absorbAndSqueezeRound p tr).2) := by
          unfold stepScheduledRound degLePoly; simp [hDrop, decide_eq_true hLen, decide_eq_true hSum]
        simp [verifyScheduledSumcheck, hStep, hRec]
def advanceSumcheckTranscript {R : Type} [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] : List (RoundPoly R) → Transcript phase → Transcript phase
  | [], tr => tr | p :: ps, tr => advanceSumcheckTranscript ps (absorbAndSqueezeRound p tr).2
private theorem verifyScheduledSumcheck_transcript_eq {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    ∀ (ds : List Nat) (s₀ s₁ : R) (ps : List (RoundPoly R)) (rs : List R) (tr₀ tr₁ : Transcript phase), verifyScheduledSumcheck ds s₀ ps tr₀ = some ((rs, s₁), tr₁) →
      tr₁ = advanceSumcheckTranscript ps tr₀
  | [], _, _, [], _, _, _, h => by simp only [verifyScheduledSumcheck, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | [], _, _, _ :: _, _, _, _, h => nomatch h | _ :: _, _, _, [], _, _, _, h => nomatch h
  | d :: ds, s₀, s₁, p :: ps, rs, tr₀, tr₁, h => by
    have hSpec := (verifyScheduledSumcheck_iff_spec (d :: ds) s₀ s₁ (p :: ps) rs tr₀ tr₁).mp h; cases hSpec with
    | cons _ _ hSub => exact verifyScheduledSumcheck_transcript_eq ds _ s₁ ps _ _ tr₁ ((verifyScheduledSumcheck_iff_spec ds _ s₁ ps _ _ tr₁).mpr hSub)
theorem verifyScheduledSumcheck_point_len {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    ∀ (ds : List Nat) (claimedSum : R) (ps : List (RoundPoly R)) (tr : Transcript phase) (rs : List R) (finalVal : R) (trOut : Transcript phase),
      verifyScheduledSumcheck ds claimedSum ps tr = some ((rs, finalVal), trOut) → rs.length = ds.length ∧ ps.length = ds.length := by
  intro ds s ps tr rs fv trOut h; have hs := (verifyScheduledSumcheck_iff_spec ds s fv ps rs tr trOut).mp h
  clear h
  induction hs with
  | nil => exact ⟨rfl, rfl⟩ | cons _ _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩
theorem verifyScheduledRound_sound {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {maxDeg : Nat} {claimedSum trueSum : R} {p pStar : RoundPoly R} {tr : Transcript phase} {r nextClaim : R} {tr' : Transcript phase}
    (hAcc : stepScheduledRound maxDeg claimedSum p tr = some (r, nextClaim, tr'))
    (hPStarSum : CommRingOps.add (evalPoly pStar CommRingOps.zero) (evalPoly pStar CommRingOps.one) = trueSum) (hFalse : claimedSum ≠ trueSum) :
    p.coeffs.length ≤ maxDeg + 1 ∧ (r, tr') = absorbAndSqueezeRound p tr ∧ (nextClaim ≠ evalPoly pStar r ∨ PolyDiscrepancyRootHit p pStar r) := by
  unfold stepScheduledRound at hAcc; split at hAcc
  · rename_i hCond; simp only [Bool.and_eq_true, List.isEmpty_iff, List.drop_eq_nil_iff, degLePoly, decide_eq_true_eq] at hCond
    simp only [Option.some.injEq, Prod.mk.injEq] at hAcc; rcases hAcc with ⟨hr, hNext, hTr⟩; subst hr hNext hTr; refine ⟨hCond.1.1, rfl, ?_⟩
    let ch := (absorbAndSqueezeRound p tr).1; if hAgree : evalPoly p ch = evalPoly pStar ch then
      right; refine ⟨hAgree, ?_⟩
      if h0 : evalPoly p CommRingOps.zero = evalPoly pStar CommRingOps.zero then
        exact .inr (fun h1 => hFalse (by rw [← hCond.2, h0, h1, hPStarSum]))
      else exact .inl h0
    else exact .inl hAgree
  · cases hAcc
/-! ## 4. Native 3-Operand `MXFP4` `EinSumcheck` (`(2^logB, 3^logK, 3^logJ)`) Completeness & Soundness -/
@[expose] def mxfp4DegSchedule (logB logK logJ : Nat) : List Nat := List.replicate logB 2 ++ List.replicate logK 3 ++ List.replicate logJ 3
theorem mxfp4DegSchedule_never_deg_four (logB logK logJ : Nat) : (mxfp4DegSchedule logB logK logJ).length = logB + logK + logJ ∧
    ∀ d ∈ mxfp4DegSchedule logB logK logJ, (d = 2 ∨ d = 3) ∧ d ≤ 3 := by
  refine ⟨by simp [mxfp4DegSchedule, Nat.add_assoc], fun d hd => ?_⟩
  simp only [mxfp4DegSchedule, List.mem_append, List.mem_replicate] at hd; rcases hd with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
  · exact ⟨.inl rfl, by decide⟩
  · exact ⟨.inr rfl, by decide⟩
  · exact ⟨.inr rfl, by decide⟩
def chunkBlocks {α : Type} : Nat → Nat → List α → List (List α)
  | 0, _, _ => [] | m + 1, blkLen, xs => xs.take blkLen :: chunkBlocks m blkLen (xs.drop blkLen)
theorem chunkBlocks_spec {α : Type} (m blkLen : Nat) : ∀ (xs : List α), xs.length = m * blkLen → (chunkBlocks m blkLen xs).length = m ∧ (chunkBlocks m blkLen xs).flatten = xs ∧
      (∀ blk ∈ chunkBlocks m blkLen xs, blk.length = blkLen) := by
  induction m with
  | zero => intro xs h; cases xs with | nil => exact ⟨rfl, rfl, fun _ hm => nomatch hm⟩ | cons _ _ => simp at h
  | succ m ih =>
    intro xs h; have hLe : blkLen ≤ xs.length := by rw [h, Nat.succ_mul]; omega
    obtain ⟨hL, hF, hAll⟩ := ih (xs.drop blkLen) (by rw [List.length_drop, h, Nat.succ_mul]; omega)
    refine ⟨by simp [chunkBlocks, hL], by simp [chunkBlocks, hF, List.take_append_drop], fun blk hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | htail
    · exact List.length_take_of_le hLe
    · exact hAll blk htail
theorem foldVars_flatten_blocks {R : Type} [LawfulCommRing R] : ∀ (rs : List R) (blocks : List (List R)), (∀ blk ∈ blocks, blk.length = 2 ^ rs.length) →
      foldVars blocks.flatten rs = blocks.map (fun blk => mleEval blk rs)
  | [], blocks, hall => by
    simp only [foldVars_nil]; induction blocks with
    | nil => rfl | cons blk bs ih =>
      have h1 : blk.length = 1 := hall blk (.head _); cases blk with
      | nil => simp at h1 | cons v₀ tl =>
        have htl : tl = [] := by simp at h1; exact h1
        subst htl; simp only [List.flatten_cons, List.cons_append, List.nil_append, List.map_cons,
          mleEval, List.length_nil, hypercube, List.map_nil, eqPoly, innerProd, List.cons.injEq]
        refine ⟨?_, ih fun b hb => hall b (.tail _ hb)⟩
        change v₀ = CommRingOps.add (CommRingOps.mul v₀ CommRingOps.one) CommRingOps.zero; rw [LawfulCommRing.mul_one, LawfulCommRing.add_zero]
  | r :: rs, blocks, hall => by
    have hStep : ∀ (bs : List (List R)), (∀ blk ∈ bs, blk.length = 2 * 2 ^ rs.length) → foldFirstVar bs.flatten r = (bs.map fun blk => foldFirstVar blk r).flatten := by
      intro bs; induction bs with
      | nil => intros; rfl | cons blk rest ihB =>
        intro hB; simp only [List.flatten_cons, List.map_cons]
        rw [foldFirstVar_append_even (2 ^ rs.length) blk rest.flatten r (hB blk (.head _)), ihB fun b hb => hB b (.tail _ hb)]
    have h2 : ∀ blk ∈ blocks, blk.length = 2 * 2 ^ rs.length := fun blk hb => by rw [hall blk hb, List.length_cons, Nat.pow_succ, Nat.mul_comm]
    simp only [foldVars, hStep blocks h2]; rw [foldVars_flatten_blocks rs (blocks.map fun blk => foldFirstVar blk r)]
    · simp only [List.map_map]; exact List.map_congr_left fun blk _ => mleEval_foldFirstVar blk r rs
    · intro fblk hf; obtain ⟨blk, hb, rfl⟩ := List.mem_map.mp hf; rw [foldFirstVar_length, h2 blk hb, half_two_mul]
def scaleEachBlock {R : Type} [CommRingOps R] (ws : List R) (blocks : List (List R)) : List R := (List.zipWith scaleList ws blocks).flatten
private theorem scaleEachBlock_cons {R : Type} [CommRingOps R] (w : R) (ws : List R) (b : List R) (bs : List (List R)) :
    scaleEachBlock (w :: ws) (b :: bs) = scaleList w b ++ scaleEachBlock ws bs := rfl
theorem scaleEachBlock_length {R : Type} [CommRingOps R] (blkLen : Nat) : ∀ (ws : List R) (blocks : List (List R)), ws.length = blocks.length → (∀ b ∈ blocks, b.length = blkLen) →
      (scaleEachBlock ws blocks).length = ws.length * blkLen
  | [], [], _, _ => by simp [scaleEachBlock]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | w :: ws, b :: bs, hlen, hall => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    rw [scaleEachBlock_cons, List.length_append, scaleList, List.length_map, hall b (.head _), scaleEachBlock_length blkLen ws bs hlen (fun x hx => hall x (.tail _ hx)),
        List.length_cons, Nat.succ_mul, Nat.add_comm]
theorem foldFirstVar_scaleEachBlock {R : Type} [LawfulCommRing R] (k : Nat) (r : R) : ∀ (ws : List R) (blocks : List (List R)),
      ws.length = blocks.length → (∀ b ∈ blocks, b.length = 2 * k) → foldFirstVar (scaleEachBlock ws blocks) r = scaleEachBlock ws (blocks.map fun b => foldFirstVar b r)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | w :: ws, b :: bs, hlen, hall => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen; have hb := hall b (.head _)
    rw [scaleEachBlock_cons, List.map_cons, scaleEachBlock_cons, foldFirstVar_append_even k (scaleList w b) _ r (by simp [scaleList, hb]), foldFirstVar_scaleList k w r b hb,
        foldFirstVar_scaleEachBlock k r ws bs hlen (fun x hx => hall x (.tail _ hx))]
private theorem foldVars_scaleEachBlock {R : Type} [LawfulCommRing R] : ∀ (rs : List R) (ws : List R) (bs : List (List R)),
      ws.length = bs.length → (∀ b ∈ bs, b.length = 2 ^ rs.length) → foldVars (scaleEachBlock ws bs) rs = scaleEachBlock ws (bs.map fun b => foldVars b rs)
  | [], _, bs, _, _ => by simp only [foldVars_nil, List.map_id']
  | r :: rs, ws, bs, hwl, hall => by
    have h2 : ∀ b ∈ bs, b.length = 2 * 2 ^ rs.length := fun b hb => by rw [hall b hb, List.length_cons, Nat.pow_succ, Nat.mul_comm]
    simp only [foldVars, foldFirstVar_scaleEachBlock (2 ^ rs.length) r ws bs hwl h2]; rw [foldVars_scaleEachBlock rs ws (bs.map fun b => foldFirstVar b r) (by simp [hwl])
      (fun fb hf => by obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf; rw [foldFirstVar_length, h2 b hb, half_two_mul])]
    simp only [List.map_map]; rfl
theorem scaleEachBlock_singletons {R : Type} [CommRingOps R] : ∀ (ws : List R) (blocks : List (List R)) (vals : List R),
      ws.length = vals.length → blocks = vals.map (fun v => [v]) → scaleEachBlock ws blocks = List.zipWith CommRingOps.mul ws vals
  | [], _, [], _, rfl => rfl
  | [], _, _ :: _, h, _ => by simp at h
  | _ :: _, _, [], h, _ => by simp at h
  | w :: ws, _, v :: vs, hlen, rfl => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen; rw [List.map_cons, scaleEachBlock_cons]
    exact congrArg (CommRingOps.mul w v :: ·) (scaleEachBlock_singletons ws _ vs hlen rfl)
def weightedVecSum {R : Type} [CommRingOps R] (vecLen : Nat) : List R → List (List R) → List R
  | c :: cs, v :: vs => vecAddList (scaleList c v) (weightedVecSum vecLen cs vs) | _, _ => List.replicate vecLen CommRingOps.zero
theorem weightedVecSum_length {R : Type} [CommRingOps R] (vecLen : Nat) :
    ∀ (cs : List R) (vs : List (List R)), (∀ v ∈ vs, v.length = vecLen) → (weightedVecSum vecLen cs vs).length = vecLen
  | [], _, _ => List.length_replicate .. | _ :: _, [], _ => List.length_replicate ..
  | _ :: cs, v :: vs, hall => by
    simp only [weightedVecSum, vecAddList, List.length_zipWith, scaleList, List.length_map,
      hall v (.head _), weightedVecSum_length vecLen cs vs fun u hu => hall u (.tail _ hu), Nat.min_self]
theorem mleEval_zero_replicate {R : Type} [LawfulCommRing R] : ∀ (n : Nat) (eqs : List R), innerProd (List.replicate n (CommRingOps.zero : R)) eqs = CommRingOps.zero
  | 0, _ => rfl | _ + 1, [] => rfl
  | n + 1, _ :: eqs => by simp only [List.replicate_succ, innerProd, LawfulCommRing.zero_mul, mleEval_zero_replicate n eqs, LawfulCommRing.add_zero]
theorem mleEval_weightedVecSum {R : Type} [LawfulCommRing R] (rs : List R) : ∀ (cs : List R) (vs : List (List R)), cs.length = vs.length → (∀ v ∈ vs, v.length = 2 ^ rs.length) →
      mleEval (weightedVecSum (2 ^ rs.length) cs vs) rs = innerProd (vs.map fun v => mleEval v rs) cs
  | [], [], _, _ => by simp [weightedVecSum, mleEval, mleEval_zero_replicate, innerProd]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, v :: vs, hlen, hall => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen; have hv := hall v (.head _); have hRestLen := weightedVecSum_length (2 ^ rs.length) cs vs fun u hu => hall u (.tail _ hu)
    rw [weightedVecSum, mleEval_vecAddList rs (by simp [scaleList, hv, hRestLen]), mleEval_scaleList, mleEval_weightedVecSum rs cs vs hlen fun u hu => hall u (.tail _ hu)]
    simp only [List.map_cons, innerProd]; rw [LawfulCommRing.mul_comm c]
def mxfp4ContractTable (logI logJ logK logB : Nat) (xTbl : List Goldilocks) (qInts : List Int) (sShifts : List Nat) : List Goldilocks :=
  let I := 2 ^ logI; let J := 2 ^ logJ; let K := 2 ^ logK; let B := 2 ^ logB; let xBlocks := chunkBlocks (B * K) I xTbl
  let qPerJ := chunkBlocks J (B * K) (qInts.map intToGoldilocks); let sPerJ := chunkBlocks J K (sShifts.map shiftToGoldilocks)
  (List.zipWith (fun qJ sJ => weightedVecSum I (scaleEachBlock sJ (chunkBlocks K B qJ)) xBlocks) qPerJ sPerJ).flatten
theorem mxfp4ContractTable_length (logI logJ logK logB : Nat) (xTbl : List Goldilocks) (qInts : List Int) (sShifts : List Nat) (hQ : qInts.length = 2 ^ (logB + logK + logJ))
    (hS : sShifts.length = 2 ^ (logK + logJ)) (hX : xTbl.length = 2 ^ (logI + logB + logK)) :
    (mxfp4ContractTable logI logJ logK logB xTbl qInts sShifts).length = 2 ^ (logI + logJ) := by
  unfold mxfp4ContractTable; have hPowX : xTbl.length = (2 ^ logB * 2 ^ logK) * 2 ^ logI := by rw [hX, Nat.pow_add, Nat.pow_add]; ac_rfl
  have hPowQ : (qInts.map intToGoldilocks).length = 2 ^ logJ * (2 ^ logB * 2 ^ logK) := by rw [List.length_map, hQ, Nat.pow_add, Nat.pow_add]; ac_rfl
  have hPowS : (sShifts.map shiftToGoldilocks).length = 2 ^ logJ * 2 ^ logK := by rw [List.length_map, hS, Nat.pow_add]; ac_rfl
  obtain ⟨_, _, hXAll⟩ := chunkBlocks_spec (2 ^ logB * 2 ^ logK) (2 ^ logI) xTbl hPowX; obtain ⟨hQLen, _, _⟩ := chunkBlocks_spec (2 ^ logJ) (2 ^ logB * 2 ^ logK) _ hPowQ
  obtain ⟨hSLen, _, _⟩ := chunkBlocks_spec (2 ^ logJ) (2 ^ logK) _ hPowS
  have hZipLen : ∀ (qs ss : List (List Goldilocks)), qs.length = ss.length → ((List.zipWith (fun qJ sJ => weightedVecSum (2 ^ logI)
        (scaleEachBlock sJ (chunkBlocks (2 ^ logK) (2 ^ logB) qJ)) (chunkBlocks (2 ^ logB * 2 ^ logK) (2 ^ logI) xTbl)) qs ss).flatten).length = qs.length * 2 ^ logI := by
    intro qs; induction qs with
    | nil => intros; simp | cons _ qs ih =>
      intro ss hls; cases ss with
      | nil => simp at hls | cons _ ss =>
        simp only [List.length_cons, Nat.succ.injEq] at hls; simp only [List.zipWith_cons_cons, List.flatten_cons, List.length_append,
          weightedVecSum_length (2 ^ logI) _ _ hXAll, ih ss hls, List.length_cons, Nat.succ_mul, Nat.add_comm]
  rw [hZipLen _ _ (hQLen.trans hSLen.symm), hQLen, Nat.pow_add]; ac_rfl
def proveQuadRounds {R : Type} [CommRingOps R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    Nat → List R → List R → Transcript phase → List (RoundPoly R) × List R × List R × List R × Transcript phase
  | 0, A, B, tr => ([], [], A, B, tr) | rem + 1, A, B, tr =>
    let p := quadPairRoundPoly A B; let (r, tr') := absorbAndSqueezeRound p tr; let (ps, rs, af, bf, trEnd) := proveQuadRounds rem (foldFirstVar A r) (foldFirstVar B r) tr'
    (p :: ps, r :: rs, af, bf, trEnd)
def proveCubicRounds {R : Type} [CommRingOps R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] : Nat → List R → List R → List R → Transcript phase →
    List (RoundPoly R) × List R × List R × List R × List R × Transcript phase
  | 0, A, B, C, tr => ([], [], A, B, C, tr) | rem + 1, A, B, C, tr =>
    let p := cubicTripleRoundPoly A B C; let (r, tr') := absorbAndSqueezeRound p tr
    let (ps, rs, af, bf, cf, trEnd) := proveCubicRounds rem (foldFirstVar A r) (foldFirstVar B r) (foldFirstVar C r) tr'
    (p :: ps, r :: rs, af, bf, cf, trEnd)
theorem proveQuadRounds_complete {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] (rem : Nat) :
    ∀ (m : Nat) (A B : List R) (tr : Transcript phase), A.length = m * 2 ^ rem → B.length = m * 2 ^ rem → let (ps, rs, af, bf, trOut) := proveQuadRounds rem A B tr
      verifyScheduledSumcheck (List.replicate rem 2) (innerProd A B) ps tr = some ((rs, innerProd af bf), trOut) ∧
      rs.length = rem ∧ af = foldVars A rs ∧ bf = foldVars B rs := by
  induction rem with
  | zero => intro _ A B tr _ _; simp [proveQuadRounds, verifyScheduledSumcheck] | succ rem ih =>
    intro m A B tr hA hB; have hEA : A.length = 2 * (m * 2 ^ rem) := hA.trans (mul_two_pow_succ m rem); have hEB : B.length = 2 * (m * 2 ^ rem) := hB.trans (mul_two_pow_succ m rem)
    let p := quadPairRoundPoly A B; let step := absorbAndSqueezeRound p tr
    have hRound : stepScheduledRound 2 (innerProd A B) p tr = some (step.1, innerProd (foldFirstVar A step.1) (foldFirstVar B step.1), step.2) := by
      have hDr : (p.coeffs.drop 3).isEmpty = true := by
        have hl := quadPairRoundPoly_degLe A B; simp only [degLePoly, decide_eq_true_eq] at hl; simp [p, List.isEmpty_iff, List.drop_eq_nil_iff, hl]
      unfold stepScheduledRound; rw [hDr, quadPairRoundPoly_degLe A B, decide_eq_true (quadPairRoundPoly_sum (m * 2 ^ rem) A B hEA hEB)]
      simp [p, step, quadPairRoundPoly_eval (m * 2 ^ rem) A B step.1 hEA hEB]
    obtain ⟨ihVer, ihLen, ihA, ihB⟩ := ih m (foldFirstVar A step.1) (foldFirstVar B step.1) step.2
      (by rw [foldFirstVar_length, hEA, half_two_mul]) (by rw [foldFirstVar_length, hEB, half_two_mul])
    dsimp only [proveQuadRounds]; refine ⟨?_, congrArg Nat.succ ihLen, ihA, ihB⟩
    change (match stepScheduledRound 2 (innerProd A B) p tr with
      | none => none | some (r, nextC, tr') =>
        match verifyScheduledSumcheck (List.replicate rem 2) nextC (proveQuadRounds rem (foldFirstVar A step.1) (foldFirstVar B step.1) step.2).1 tr' with
        | none => none | some ((rs, fv), trF) => some ((r :: rs, fv), trF)) = _
    rw [hRound]; dsimp only; rw [ihVer]
theorem proveCubicRounds_complete {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] (rem : Nat) :
    ∀ (m : Nat) (A B C : List R) (tr : Transcript phase), A.length = m * 2 ^ rem → B.length = m * 2 ^ rem → C.length = m * 2 ^ rem →
      let (ps, rs, af, bf, cf, trOut) := proveCubicRounds rem A B C tr
      verifyScheduledSumcheck (List.replicate rem 3) (tripleInnerProd A B C) ps tr = some ((rs, tripleInnerProd af bf cf), trOut) ∧
      rs.length = rem ∧ af = foldVars A rs ∧ bf = foldVars B rs ∧ cf = foldVars C rs := by
  induction rem with
  | zero => intro _ A B C tr _ _ _; simp [proveCubicRounds, verifyScheduledSumcheck] | succ rem ih =>
    intro m A B C tr hA hB hC; have hEA : A.length = 2 * (m * 2 ^ rem) := hA.trans (mul_two_pow_succ m rem)
    have hEB : B.length = 2 * (m * 2 ^ rem) := hB.trans (mul_two_pow_succ m rem); have hEC : C.length = 2 * (m * 2 ^ rem) := hC.trans (mul_two_pow_succ m rem)
    let p := cubicTripleRoundPoly A B C; let step := absorbAndSqueezeRound p tr; have hRound : stepScheduledRound 3 (tripleInnerProd A B C) p tr =
        some (step.1, tripleInnerProd (foldFirstVar A step.1) (foldFirstVar B step.1) (foldFirstVar C step.1), step.2) := by
      have hDr : (p.coeffs.drop 4).isEmpty = true := by
        have hl := cubicTripleRoundPoly_degLe A B C; simp only [degLePoly, decide_eq_true_eq] at hl; simp [p, List.isEmpty_iff, List.drop_eq_nil_iff, hl]
      unfold stepScheduledRound; rw [hDr, cubicTripleRoundPoly_degLe A B C, decide_eq_true (cubicTripleRoundPoly_sum (m * 2 ^ rem) A B C hEA hEB hEC)]
      simp [p, step, cubicTripleRoundPoly_eval (m * 2 ^ rem) A B C step.1 hEA hEB hEC]
    obtain ⟨ihVer, ihLen, ihA, ihB, ihC⟩ := ih m (foldFirstVar A step.1) (foldFirstVar B step.1) (foldFirstVar C step.1) step.2 (by rw [foldFirstVar_length, hEA, half_two_mul])
      (by rw [foldFirstVar_length, hEB, half_two_mul]) (by rw [foldFirstVar_length, hEC, half_two_mul])
    dsimp only [proveCubicRounds]; refine ⟨?_, congrArg Nat.succ ihLen, ihA, ihB, ihC⟩
    change (match stepScheduledRound 3 (tripleInnerProd A B C) p tr with
      | none => none | some (r, nextC, tr') =>
        match verifyScheduledSumcheck (List.replicate rem 3) nextC (proveCubicRounds rem (foldFirstVar A step.1) (foldFirstVar B step.1) (foldFirstVar C step.1) step.2).1 tr' with
        | none => none | some ((rs, fv), trF) => some ((r :: rs, fv), trF)) = _
    rw [hRound]; dsimp only; rw [ihVer]
theorem verifyScheduledSumcheck_append {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    ∀ (ds₁ ds₂ : List Nat) (s₀ s₁ s₂ : R) (ps₁ ps₂ : List (RoundPoly R)) (rs₁ rs₂ : List R) (tr₀ tr₁ tr₂ : Transcript phase),
      verifyScheduledSumcheck ds₁ s₀ ps₁ tr₀ = some ((rs₁, s₁), tr₁) → verifyScheduledSumcheck ds₂ s₁ ps₂ tr₁ = some ((rs₂, s₂), tr₂) →
      verifyScheduledSumcheck (ds₁ ++ ds₂) s₀ (ps₁ ++ ps₂) tr₀ = some ((rs₁ ++ rs₂, s₂), tr₂)
  | [], _, _, _, _, [], _, _, _, _, _, _, h1, h2 => by
    simp only [verifyScheduledSumcheck, Option.some.injEq, Prod.mk.injEq] at h1; rcases h1 with ⟨⟨rfl, rfl⟩, rfl⟩; simpa using h2
  | [], _, _, _, _, _ :: _, _, _, _, _, _, _, h1, _ => nomatch h1 | _ :: _, _, _, _, _, [], _, _, _, _, _, _, h1, _ => nomatch h1
  | d :: ds₁, ds₂, s₀, s₁, s₂, p :: ps₁, ps₂, rs₁, rs₂, tr₀, tr₁, tr₂, h1, h2 => by
    simp only [verifyScheduledSumcheck] at h1; cases hR : stepScheduledRound d s₀ p tr₀ with
    | none => rw [hR] at h1; cases h1 | some step =>
      rcases step with ⟨r, nextC, tr'⟩; rw [hR] at h1; dsimp only at h1; cases hRec : verifyScheduledSumcheck ds₁ nextC ps₁ tr' with
      | none => rw [hRec] at h1; cases h1 | some sub =>
        rcases sub with ⟨⟨rs₁', fv⟩, trM⟩; rw [hRec] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; rcases h1 with ⟨⟨rfl, rfl⟩, rfl⟩
        simp only [List.cons_append, verifyScheduledSumcheck, hR, verifyScheduledSumcheck_append ds₁ ds₂ nextC fv s₂ ps₁ ps₂ rs₁' rs₂ tr' trM tr₂ hRec h2]
private theorem scheduledSumcheck_split {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R] {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    ∀ (ds₁ ds₂ : List Nat) (s₀ s₂ : R) (ps : List (RoundPoly R)) (rs : List R) (tr₀ tr₂ : Transcript phase), verifyScheduledSumcheck (ds₁ ++ ds₂) s₀ ps tr₀ = some ((rs, s₂), tr₂) →
      ∃ s₁ tr₁, verifyScheduledSumcheck ds₁ s₀ (ps.take ds₁.length) tr₀ = some ((rs.take ds₁.length, s₁), tr₁) ∧
        verifyScheduledSumcheck ds₂ s₁ (ps.drop ds₁.length) tr₁ = some ((rs.drop ds₁.length, s₂), tr₂)
  | [], _, s₀, _, ps, rs, tr₀, _, h => ⟨s₀, tr₀, by simp [verifyScheduledSumcheck], by simpa using h⟩
  | _ :: _, _, _, _, [], _, _, _, h => nomatch h
  | d :: ds₁, ds₂, s₀, s₂, p :: ps, rs, tr₀, tr₂, h => by
    simp only [List.cons_append, verifyScheduledSumcheck] at h; cases hR : stepScheduledRound d s₀ p tr₀ with
    | none => rw [hR] at h; cases h | some step =>
      rcases step with ⟨r, nextC, tr'⟩; rw [hR] at h; dsimp only at h; cases hRec : verifyScheduledSumcheck (ds₁ ++ ds₂) nextC ps tr' with
      | none => rw [hRec] at h; cases h | some sub =>
        rcases sub with ⟨⟨rs', fv⟩, trF⟩; rw [hRec] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
        obtain ⟨s₁, tr₁, h1, h2⟩ := scheduledSumcheck_split ds₁ ds₂ nextC fv ps rs' tr' trF hRec; exact ⟨s₁, tr₁, by simp [verifyScheduledSumcheck, hR, h1], by simpa using h2⟩
/-- Witness-pinned quadratic round root-hit (`pStar := quadPairRoundPoly A B`, never a free polynomial!). -/
inductive QuadRoundsRootHit {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    Nat → List Goldilocks → List Goldilocks → List (RoundPoly Goldilocks) → Transcript phase → Prop where
  | hitHere {rem : Nat} {A B : List Goldilocks} {p : RoundPoly Goldilocks}
      {ps : List (RoundPoly Goldilocks)} {tr : Transcript phase} :
      p.coeffs.length ≤ 3 → PolyDiscrepancyRootHit p (quadPairRoundPoly A B) (absorbAndSqueezeRound p tr).1 →
      QuadRoundsRootHit (rem + 1) A B (p :: ps) tr
  | hitLater {rem : Nat} {A B : List Goldilocks} {p : RoundPoly Goldilocks}
      {ps : List (RoundPoly Goldilocks)} {tr : Transcript phase} :
      QuadRoundsRootHit rem (foldFirstVar A (absorbAndSqueezeRound p tr).1)
        (foldFirstVar B (absorbAndSqueezeRound p tr).1) ps (absorbAndSqueezeRound p tr).2 →
      QuadRoundsRootHit (rem + 1) A B (p :: ps) tr
/-- Witness-pinned cubic round root-hit (`pStar := cubicTripleRoundPoly A B C`, never a free polynomial!). -/
inductive CubicRoundsRootHit {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    Nat → List Goldilocks → List Goldilocks → List Goldilocks → List (RoundPoly Goldilocks) → Transcript phase → Prop where
  | hitHere {rem : Nat} {A B C : List Goldilocks} {p : RoundPoly Goldilocks}
      {ps : List (RoundPoly Goldilocks)} {tr : Transcript phase} :
      p.coeffs.length ≤ 4 → PolyDiscrepancyRootHit p (cubicTripleRoundPoly A B C) (absorbAndSqueezeRound p tr).1 →
      CubicRoundsRootHit (rem + 1) A B C (p :: ps) tr
  | hitLater {rem : Nat} {A B C : List Goldilocks} {p : RoundPoly Goldilocks}
      {ps : List (RoundPoly Goldilocks)} {tr : Transcript phase} :
      CubicRoundsRootHit rem (foldFirstVar A (absorbAndSqueezeRound p tr).1)
        (foldFirstVar B (absorbAndSqueezeRound p tr).1) (foldFirstVar C (absorbAndSqueezeRound p tr).1)
        ps (absorbAndSqueezeRound p tr).2 →
      CubicRoundsRootHit (rem + 1) A B C (p :: ps) tr
theorem proveQuadRounds_no_rootHit {phase : TranscriptPhase} [CanSqueezeTranscript phase] (rem : Nat) : ∀ (A B : List Goldilocks) (tr : Transcript phase),
      ¬ QuadRoundsRootHit rem A B (proveQuadRounds rem A B tr).1 tr := by
  induction rem with
  | zero => intros _ _ _ h; cases h | succ rem ih =>
    intro A B tr h; dsimp only [proveQuadRounds] at h; cases h with
    | hitHere _ hHit => rcases hHit.2 with h0 | h1 <;> exact absurd rfl (by assumption)
    | hitLater hSub => exact ih _ _ _ hSub
theorem proveCubicRounds_no_rootHit {phase : TranscriptPhase} [CanSqueezeTranscript phase] (rem : Nat) : ∀ (A B C : List Goldilocks) (tr : Transcript phase),
      ¬ CubicRoundsRootHit rem A B C (proveCubicRounds rem A B C tr).1 tr := by
  induction rem with
  | zero => intros _ _ _ _ h; cases h | succ rem ih =>
    intro A B C tr h; dsimp only [proveCubicRounds] at h; cases h with
    | hitHere _ hHit => rcases hHit.2 with h0 | h1 <;> exact absurd rfl (by assumption)
    | hitLater hSub => exact ih _ _ _ _ hSub
private theorem verifyQuadRounds_sound {phase : TranscriptPhase} [CanSqueezeTranscript phase] (rem : Nat) :
    ∀ (m : Nat) (A B : List Goldilocks) (claimedSum : Goldilocks) (ps : List (RoundPoly Goldilocks)) (rs : List Goldilocks) (midVal : Goldilocks) (tr trOut : Transcript phase),
      A.length = m * 2 ^ rem → B.length = m * 2 ^ rem → verifyScheduledSumcheck (List.replicate rem 2) claimedSum ps tr = some ((rs, midVal), trOut) → claimedSum ≠ innerProd A B →
      midVal ≠ innerProd (foldVars A rs) (foldVars B rs) ∨ QuadRoundsRootHit rem A B ps tr := by
  induction rem with
  | zero =>
    intro _ A B claimedSum ps rs midVal tr _ _ _ hVer hFalse; cases ps with
    | cons _ _ => cases hVer | nil =>
      simp only [List.replicate_zero, verifyScheduledSumcheck, Option.some.injEq, Prod.mk.injEq] at hVer; rcases hVer with ⟨⟨rfl, rfl⟩, rfl⟩; exact .inl hFalse
  | succ rem ih =>
    intro m A B claimedSum ps rs midVal tr trOut hA hB hVer hFalse; cases ps with
    | nil => cases hVer | cons p ps =>
      simp only [List.replicate_succ, verifyScheduledSumcheck] at hVer; cases hR : stepScheduledRound 2 claimedSum p tr with
      | none => rw [hR] at hVer; cases hVer | some step =>
        rcases step with ⟨r, nextC, tr'⟩; rw [hR] at hVer; dsimp only at hVer; cases hRec : verifyScheduledSumcheck (List.replicate rem 2) nextC ps tr' with
        | none => rw [hRec] at hVer; cases hVer | some sub =>
          rcases sub with ⟨⟨rs', fv⟩, trF⟩; rw [hRec] at hVer; simp only [Option.some.injEq, Prod.mk.injEq] at hVer; rcases hVer with ⟨⟨rfl, rfl⟩, rfl⟩
          have hEA := hA.trans (mul_two_pow_succ m rem); have hEB := hB.trans (mul_two_pow_succ m rem)
          obtain ⟨hPLen, hStepEq, hDich⟩ := verifyScheduledRound_sound hR (quadPairRoundPoly_sum (m * 2 ^ rem) A B hEA hEB) hFalse
          have hR1 : r = (absorbAndSqueezeRound p tr).1 := congrArg Prod.fst hStepEq; have hT2 : tr' = (absorbAndSqueezeRound p tr).2 := congrArg Prod.snd hStepEq; subst hR1 hT2
          rw [quadPairRoundPoly_eval (m * 2 ^ rem) A B _ hEA hEB] at hDich; rcases hDich with hNextFalse | hHit
          · rcases ih m _ _ nextC ps rs' fv _ trF (by rw [foldFirstVar_length, hEA, half_two_mul])
                (by rw [foldFirstVar_length, hEB, half_two_mul]) hRec hNextFalse with hEndF | hLater
            · exact .inl hEndF
            · exact .inr (.hitLater hLater)
          · exact .inr (.hitHere hPLen hHit)
private theorem verifyCubicRounds_sound {phase : TranscriptPhase} [CanSqueezeTranscript phase] (rem : Nat) :
    ∀ (m : Nat) (A B C : List Goldilocks) (claimedSum : Goldilocks) (ps : List (RoundPoly Goldilocks)) (rs : List Goldilocks) (midVal : Goldilocks) (tr trOut : Transcript phase),
      A.length = m * 2 ^ rem → B.length = m * 2 ^ rem → C.length = m * 2 ^ rem → verifyScheduledSumcheck (List.replicate rem 3) claimedSum ps tr = some ((rs, midVal), trOut) →
      claimedSum ≠ tripleInnerProd A B C → midVal ≠ tripleInnerProd (foldVars A rs) (foldVars B rs) (foldVars C rs) ∨ CubicRoundsRootHit rem A B C ps tr := by
  induction rem with
  | zero =>
    intro _ A B C claimedSum ps rs midVal tr _ _ _ _ hVer hFalse; cases ps with
    | cons _ _ => cases hVer | nil =>
      simp only [List.replicate_zero, verifyScheduledSumcheck, Option.some.injEq, Prod.mk.injEq] at hVer; rcases hVer with ⟨⟨rfl, rfl⟩, rfl⟩; exact .inl hFalse
  | succ rem ih =>
    intro m A B C claimedSum ps rs midVal tr trOut hA hB hC hVer hFalse; cases ps with
    | nil => cases hVer | cons p ps =>
      simp only [List.replicate_succ, verifyScheduledSumcheck] at hVer; cases hR : stepScheduledRound 3 claimedSum p tr with
      | none => rw [hR] at hVer; cases hVer | some step =>
        rcases step with ⟨r, nextC, tr'⟩; rw [hR] at hVer; dsimp only at hVer; cases hRec : verifyScheduledSumcheck (List.replicate rem 3) nextC ps tr' with
        | none => rw [hRec] at hVer; cases hVer | some sub =>
          rcases sub with ⟨⟨rs', fv⟩, trF⟩; rw [hRec] at hVer; simp only [Option.some.injEq, Prod.mk.injEq] at hVer; rcases hVer with ⟨⟨rfl, rfl⟩, rfl⟩
          have hEA := hA.trans (mul_two_pow_succ m rem); have hEB := hB.trans (mul_two_pow_succ m rem); have hEC := hC.trans (mul_two_pow_succ m rem)
          obtain ⟨hPLen, hStepEq, hDich⟩ := verifyScheduledRound_sound hR (cubicTripleRoundPoly_sum (m * 2 ^ rem) A B C hEA hEB hEC) hFalse
          have hR1 : r = (absorbAndSqueezeRound p tr).1 := congrArg Prod.fst hStepEq; have hT2 : tr' = (absorbAndSqueezeRound p tr).2 := congrArg Prod.snd hStepEq; subst hR1 hT2
          rw [cubicTripleRoundPoly_eval (m * 2 ^ rem) A B C _ hEA hEB hEC] at hDich; rcases hDich with hNextFalse | hHit
          · rcases ih m _ _ _ nextC ps rs' fv _ trF (by rw [foldFirstVar_length, hEA, half_two_mul])
                (by rw [foldFirstVar_length, hEB, half_two_mul]) (by rw [foldFirstVar_length, hEC, half_two_mul]) hRec hNextFalse with hEndF | hLater
            · exact .inl hEndF
            · exact .inr (.hitLater hLater)
          · exact .inr (.hitHere hPLen hHit)
def mxfp4Phase1Vectors (logJ logK logB : Nat) (xTbl qTbl sTbl rI rJ : List Goldilocks) : List Goldilocks × List Goldilocks :=
  let J := 2 ^ logJ; let K := 2 ^ logK; let B := 2 ^ logB
  (tileBlocks J (foldVars xTbl rI), scaleEachBlock (scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)) (chunkBlocks (K * J) B qTbl))
def proveMxfp4Sumcheck {phase : TranscriptPhase} [CanSqueezeTranscript phase] (logJ logK logB : Nat) (xTbl qTbl sTbl rI rJ : List Goldilocks) (tr₀ : Transcript phase) :
    List (RoundPoly Goldilocks) × List Goldilocks × List Goldilocks × List Goldilocks × Transcript phase :=
  let J := 2 ^ logJ; let K := 2 ^ logK; let (aB, bB) := mxfp4Phase1Vectors logJ logK logB xTbl qTbl sTbl rI rJ; let (psB, rB, _, _, tr₁) := proveQuadRounds logB aB bB tr₀
  let xK := foldVars (foldVars xTbl rI) rB; let qKj := foldVars qTbl rB; let sEqKj := scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)
  let (psK, rK, _, _, _, tr₂) := proveCubicRounds logK (tileBlocks J xK) qKj sEqKj tr₁; let xStar := mleEval xTbl (rI ++ rB ++ rK)
  let (psJ, rJp, _, _, _, tr₃) := proveCubicRounds logJ (scaleList xStar (eqTable rJ)) (foldVars qKj rK) (foldVars sTbl rK) tr₂
  (psB ++ psK ++ psJ, rB, rK, rJp, tr₃)
/-- Witness-pinned 3-phase `MXFP4` sumcheck discrepancy root-hit (zero existential `pStar`!). -/
def Mxfp4SumcheckRootHit {phase : TranscriptPhase} [CanSqueezeTranscript phase] (logJ logK logB : Nat) (xTbl qTbl sTbl rI rJ rB rK : List Goldilocks)
    (rounds : List (RoundPoly Goldilocks)) (tr₀ : Transcript phase) : Prop :=
  let J := 2 ^ logJ; let K := 2 ^ logK; let v1 := mxfp4Phase1Vectors logJ logK logB xTbl qTbl sTbl rI rJ; let psB := rounds.take logB; let psK := (rounds.drop logB).take logK
  let psJ := rounds.drop (logB + logK); let tr₁ := advanceSumcheckTranscript psB tr₀; let tr₂ := advanceSumcheckTranscript psK tr₁; let xK := foldVars (foldVars xTbl rI) rB
  let qKj := foldVars qTbl rB; let sEqKj := scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl); let xStar := mleEval xTbl (rI ++ rB ++ rK)
  QuadRoundsRootHit logB v1.1 v1.2 psB tr₀ ∨
  CubicRoundsRootHit logK (tileBlocks J xK) qKj sEqKj psK tr₁ ∨
  CubicRoundsRootHit logJ (scaleList xStar (eqTable rJ)) (foldVars qKj rK) (foldVars sTbl rK) psJ tr₂
private theorem scaleEachBlock_append {R : Type} [CommRingOps R] : ∀ (w₁ w₂ : List R) (b₁ b₂ : List (List R)), w₁.length = b₁.length →
      scaleEachBlock (w₁ ++ w₂) (b₁ ++ b₂) = scaleEachBlock w₁ b₁ ++ scaleEachBlock w₂ b₂
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | w :: ws, w₂, b :: bs, b₂, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    rw [List.cons_append, List.cons_append, scaleEachBlock_cons, scaleEachBlock_cons, scaleEachBlock_append ws w₂ bs b₂ h, List.append_assoc]
private theorem scaleEachBlock_scaleList {R : Type} [LawfulCommRing R] (c : R) :
    ∀ (ws : List R) (bs : List (List R)), scaleEachBlock (scaleList c ws) bs = scaleList c (scaleEachBlock ws bs)
  | [], _ => rfl | _ :: _, [] => rfl
  | w :: ws, b :: bs => by
    have hComp : scaleList (CommRingOps.mul c w) b = scaleList c (scaleList w b) := by
      unfold scaleList; rw [List.map_map]; exact List.map_congr_left fun z _ => LawfulCommRing.mul_assoc c w z
    rw [scaleList_cons, scaleEachBlock_cons, scaleEachBlock_cons, hComp, scaleEachBlock_scaleList c ws bs]; unfold scaleList; rw [List.map_append]
private theorem mxfp4_phase1_eq_mle (logI logJ logK logB : Nat) (xTbl : List Goldilocks) (qInts : List Int) (sShifts : List Nat) (rI rJ : List Goldilocks)
    (hRI : rI.length = logI) (hRJ : rJ.length = logJ) (hX : xTbl.length = 2 ^ (logI + logB + logK))
    (hQ : qInts.length = 2 ^ (logB + logK + logJ)) (hS : sShifts.length = 2 ^ (logK + logJ)) :
    let v1 := mxfp4Phase1Vectors logJ logK logB xTbl (qInts.map intToGoldilocks) (sShifts.map shiftToGoldilocks) rI rJ
    mleEval (mxfp4ContractTable logI logJ logK logB xTbl qInts sShifts) (rI ++ rJ) = innerProd v1.1 v1.2 := by
  let I := 2 ^ logI; let J := 2 ^ logJ; let K := 2 ^ logK; let B := 2 ^ logB; let qTbl := qInts.map intToGoldilocks; let sTbl := sShifts.map shiftToGoldilocks
  have hPowX : xTbl.length = (B * K) * I := by rw [hX, Nat.pow_add, Nat.pow_add]; dsimp [I, K, B]; ac_rfl
  have hPowQ : qTbl.length = J * (B * K) := by rw [List.length_map, hQ, Nat.pow_add, Nat.pow_add]; dsimp [J, K, B]; ac_rfl
  have hPowS : sTbl.length = J * K := by rw [List.length_map, hS, Nat.pow_add]; dsimp [J, K]; ac_rfl
  obtain ⟨hXBLen, hXBFlat, hXBAll⟩ := chunkBlocks_spec (B * K) I xTbl hPowX; obtain ⟨hQJLen, hQJFlat, hQJAll⟩ := chunkBlocks_spec J (B * K) qTbl hPowQ
  obtain ⟨hSJLen, _, hSJAll⟩ := chunkBlocks_spec J K sTbl hPowS; have hXBkEq : foldVars xTbl rI = (chunkBlocks (B * K) I xTbl).map (fun blk => mleEval blk rI) := by
    conv => lhs; rw [← hXBFlat]
    exact foldVars_flatten_blocks rI _ (fun blk hb => hRI ▸ hXBAll blk hb)
  have hXBkLen : (foldVars xTbl rI).length = B * K := by rw [hXBkEq, List.length_map, hXBLen]
  let rowsJ := List.zipWith (fun qJ sJ =>
    weightedVecSum I (scaleEachBlock sJ (chunkBlocks K B qJ)) (chunkBlocks (B * K) I xTbl))
    (chunkBlocks J (B * K) qTbl) (chunkBlocks J K sTbl)
  have hRowsAll : ∀ r ∈ rowsJ, r.length = 2 ^ rI.length := by
    intro r hr; rw [hRI]; have hMem : ∀ (qs ss : List (List Goldilocks)), r ∈ List.zipWith (fun qJ sJ =>
          weightedVecSum I (scaleEachBlock sJ (chunkBlocks K B qJ)) (chunkBlocks (B * K) I xTbl)) qs ss → r.length = I := by
      intro qs; induction qs with
      | nil => intros _ hm; cases hm | cons _ qs ih =>
        intro ss hm; cases ss with
        | nil => cases hm | cons _ ss =>
          rcases List.mem_cons.mp hm with rfl | htl
          · exact weightedVecSum_length I _ _ hXBAll
          · exact ih ss htl
    exact hMem _ _ hr
  have hChunkFlat : chunkBlocks (K * J) B qTbl = ((chunkBlocks J (B * K) qTbl).map (chunkBlocks K B)).flatten := by
    conv => lhs; rw [← hQJFlat]
    have hAux : ∀ (qs : List (List Goldilocks)), (∀ qJ ∈ qs, qJ.length = B * K) → chunkBlocks (K * qs.length) B qs.flatten = (qs.map (chunkBlocks K B)).flatten := by
      intro qs; induction qs with
      | nil => intros; simp [chunkBlocks] | cons qJ qs ih =>
        intro hallQ; have hq0 : qJ.length = K * B := (hallQ qJ (.head _)).trans (Nat.mul_comm B K); have hSplit : ∀ (k : Nat) (u v : List Goldilocks), u.length = k * B →
            chunkBlocks (k + K * qs.length) B (u ++ v) = chunkBlocks k B u ++ chunkBlocks (K * qs.length) B v := by
          intro k; induction k with
          | zero => intro u _ hu; cases u with | nil => simp [chunkBlocks] | cons _ _ => simp at hu
          | succ k ihK =>
            intro u v hu; have hLe : B ≤ u.length := by rw [hu, Nat.succ_mul]; omega
            simp only [Nat.succ_add, chunkBlocks, List.take_append_of_le_length hLe, List.drop_append_of_le_length hLe, List.cons_append]
            exact congrArg (_ :: ·) (ihK (u.drop B) v (by rw [List.length_drop, hu, Nat.succ_mul]; omega))
        have hMul : K * (qs.length + 1) = K + K * qs.length := by rw [Nat.mul_succ, Nat.add_comm]
        simp only [List.length_cons, hMul, List.flatten_cons, List.map_cons]; rw [hSplit K qJ qs.flatten hq0, ih fun x hx => hallQ x (.tail _ hx)]
    simpa [hQJLen] using hAux (chunkBlocks J (B * K) qTbl) hQJAll
  have hRhs : ∀ (eqs : List Goldilocks) (qs ss : List (List Goldilocks)), eqs.length = qs.length → qs.length = ss.length →
      (∀ qJ ∈ qs, qJ.length = B * K) → (∀ sJ ∈ ss, sJ.length = K) → innerProd (tileBlocks eqs.length (foldVars xTbl rI))
        (scaleEachBlock (scaleEachBlock eqs ss) ((qs.map (chunkBlocks K B)).flatten)) = innerProd (List.zipWith (fun qJ sJ =>
        mleEval (weightedVecSum I (scaleEachBlock sJ (chunkBlocks K B qJ)) (chunkBlocks (B * K) I xTbl)) rI) qs ss) eqs := by
    intro eqs; induction eqs with
    | nil => intro qs _ h1 _ _ _; cases qs with | nil => simp [tileBlocks, scaleEachBlock, innerProd] | cons _ _ => simp at h1
    | cons e eqs ih =>
      intro qs ss h1 h2 hqAll hsAll; cases qs with | nil => simp at h1 | cons qJ qs =>
      cases ss with | nil => simp at h2 | cons sJ ss =>
      simp only [List.length_cons, Nat.succ.injEq] at h1 h2; have hq0 : qJ.length = K * B := (hqAll qJ (.head _)).trans (Nat.mul_comm B K); have hs0 := hsAll sJ (.head _)
      obtain ⟨hKBLen, _, hKBAll⟩ := chunkBlocks_spec K B qJ hq0; rw [List.length_cons, tileBlocks_succ, scaleEachBlock_cons, List.map_cons, List.flatten_cons,
          scaleEachBlock_append (scaleList e sJ) _ (chunkBlocks K B qJ) _ (by simp [scaleList, hs0, hKBLen])]
      have hSegLen : (scaleEachBlock (scaleList e sJ) (chunkBlocks K B qJ)).length = B * K := by
        rw [scaleEachBlock_length B _ _ (by simp [scaleList, hs0, hKBLen]) hKBAll, scaleList, List.length_map, hs0, Nat.mul_comm]
      rw [innerProd_append (foldVars xTbl rI) _ _ _ (hXBkLen.trans hSegLen.symm), ih qs ss h1 h2 (fun x hx => hqAll x (.tail _ hx)) (fun x hx => hsAll x (.tail _ hx)),
          scaleEachBlock_scaleList, innerProd_scaleList_right]
      have hWLen : (scaleEachBlock sJ (chunkBlocks K B qJ)).length = B * K := by rw [scaleEachBlock_length B _ _ (hs0.trans hKBLen.symm) hKBAll, hs0, Nat.mul_comm]
      have hRowMle := mleEval_weightedVecSum rI (scaleEachBlock sJ (chunkBlocks K B qJ)) (chunkBlocks (B * K) I xTbl) (by rw [hWLen, hXBLen]) (fun v hv => hRI ▸ hXBAll v hv)
      rw [hRI] at hRowMle; simp only [List.zipWith_cons_cons, innerProd]; rw [hRowMle, ← hXBkEq]
  have hZMap : ∀ (qs ss : List (List Goldilocks)), List.map (fun blk => mleEval blk rI)
        (List.zipWith (fun qJ sJ => weightedVecSum I (scaleEachBlock sJ (chunkBlocks K B qJ)) (chunkBlocks (B * K) I xTbl)) qs ss) = List.zipWith (fun qJ sJ =>
        mleEval (weightedVecSum I (scaleEachBlock sJ (chunkBlocks K B qJ)) (chunkBlocks (B * K) I xTbl)) rI) qs ss := by
    intro qs; induction qs with | nil => intros; rfl | cons _ qs ihZ => intro ss; cases ss <;> simp [ihZ]
  change mleEval rowsJ.flatten (rI ++ rJ) = innerProd (tileBlocks J (foldVars xTbl rI))
      (scaleEachBlock (scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)) (chunkBlocks (K * J) B qTbl))
  rw [← mleEval_foldVars, foldVars_flatten_blocks rI rowsJ hRowsAll, hZMap, hChunkFlat]; have hEqLen : (eqTable rJ).length = J := by rw [eqTable_length, hRJ]
  have hGoal := (hRhs (eqTable rJ) (chunkBlocks J (B * K) qTbl) (chunkBlocks J K sTbl) (hEqLen.trans hQJLen.symm) (hQJLen.trans hSJLen.symm) hQJAll hSJAll).symm
  rw [hEqLen] at hGoal; exact hGoal
private theorem phase1_to_phase2_sum (K J : Nat) (xK qKj wKj : List Goldilocks) (hX : xK.length = K) (hQ : qKj.length = K * J) (hW : wKj.length = K * J) :
    innerProd (tileBlocks J xK) (List.zipWith CommRingOps.mul wKj qKj) = tripleInnerProd (tileBlocks J xK) qKj wKj := by
  have hTileLen : (tileBlocks J xK).length = K * J := by rw [tileBlocks_length, hX, Nat.mul_comm]
  have hAux : ∀ (as qs ws : List Goldilocks), as.length = qs.length → qs.length = ws.length → innerProd as (List.zipWith CommRingOps.mul ws qs) = tripleInnerProd as qs ws := by
    intro as; induction as with
    | nil => intro qs _ h1 _; cases qs with | nil => rfl | cons _ _ => simp at h1
    | cons a as ih =>
      intro qs ws h1 h2; cases qs with | nil => simp at h1 | cons q qs =>
      cases ws with | nil => simp at h2 | cons w ws =>
      simp only [List.length_cons, Nat.succ.injEq] at h1 h2; simp only [List.zipWith_cons_cons, innerProd, tripleInnerProd, ih qs ws h1 h2, LawfulCommRing.mul_comm w q]
  exact hAux _ _ _ (hTileLen.trans hQ.symm) (hQ.trans hW.symm)
private theorem phase2_to_phase3_sum (xStar : Goldilocks) : ∀ (eqs qs ss : List Goldilocks), eqs.length = qs.length → qs.length = ss.length →
      tripleInnerProd (tileBlocks eqs.length [xStar]) qs (List.zipWith CommRingOps.mul eqs ss) = tripleInnerProd (scaleList xStar eqs) qs ss
  | [], [], [], _, _ => rfl
  | [], _ :: _, _, h1, _ => by simp at h1
  | _ :: _, [], _, h1, _ => by simp at h1
  | _ :: _, _ :: _, [], _, h2 => by simp at h2
  | e :: eqs, q :: qs, s :: ss, h1, h2 => by
    simp only [List.length_cons, Nat.succ.injEq] at h1 h2; rw [List.length_cons, tileBlocks_succ, List.singleton_append, List.zipWith_cons_cons,
        scaleList_cons, tripleInnerProd, tripleInnerProd, phase2_to_phase3_sum xStar eqs qs ss h1 h2]
    congr 1
    calc CommRingOps.mul xStar (CommRingOps.mul q (CommRingOps.mul e s))
      _ = CommRingOps.mul xStar (CommRingOps.mul (CommRingOps.mul q e) s) := by rw [← LawfulCommRing.mul_assoc q e s]
      _ = CommRingOps.mul xStar (CommRingOps.mul (CommRingOps.mul e q) s) := by rw [LawfulCommRing.mul_comm q e]
      _ = CommRingOps.mul xStar (CommRingOps.mul e (CommRingOps.mul q s)) := by rw [LawfulCommRing.mul_assoc e q s]
      _ = CommRingOps.mul (CommRingOps.mul xStar e) (CommRingOps.mul q s) := by rw [← LawfulCommRing.mul_assoc xStar e]
private theorem mxfp4_phase_transitions (logI logJ logK logB : Nat) (xTbl qTbl sTbl rI rJ rB rK rJp : List Goldilocks) (hX : xTbl.length = 2 ^ (logI + logB + logK))
    (hQ : qTbl.length = 2 ^ (logB + logK + logJ)) (hS : sTbl.length = 2 ^ (logK + logJ)) (hRI : rI.length = logI) (hRJ : rJ.length = logJ)
    (hRB : rB.length = logB) (hRK : rK.length = logK) (hRJp : rJp.length = logJ) : let J := 2 ^ logJ; let K := 2 ^ logK; let B := 2 ^ logB
    let v1 := mxfp4Phase1Vectors logJ logK logB xTbl qTbl sTbl rI rJ; let xK := foldVars (foldVars xTbl rI) rB; let qKj := foldVars qTbl rB
    let sEqKj := scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl); let xStar := mleEval xTbl (rI ++ rB ++ rK); let qJ := foldVars qKj rK; let sJ := foldVars sTbl rK
    v1.1.length = (K * J) * B ∧ v1.2.length = (K * J) * B ∧
    innerProd (foldVars v1.1 rB) (foldVars v1.2 rB) = tripleInnerProd (tileBlocks J xK) qKj sEqKj ∧
    (tileBlocks J xK).length = J * K ∧ qKj.length = J * K ∧ sEqKj.length = J * K ∧
    tripleInnerProd (foldVars (tileBlocks J xK) rK) (foldVars qKj rK) (foldVars sEqKj rK) = tripleInnerProd (scaleList xStar (eqTable rJ)) qJ sJ ∧
    (scaleList xStar (eqTable rJ)).length = 1 * J ∧ qJ.length = 1 * J ∧ sJ.length = 1 * J ∧
    tripleInnerProd (foldVars (scaleList xStar (eqTable rJ)) rJp) (foldVars qJ rJp) (foldVars sJ rJp) = CommRingOps.mul (eqPolyVec rJ rJp)
        (CommRingOps.mul xStar (CommRingOps.mul (mleEval qTbl (rB ++ rK ++ rJp)) (mleEval sTbl (rK ++ rJp)))) := by
  let J := 2 ^ logJ; let K := 2 ^ logK; let B := 2 ^ logB; have hPowX : xTbl.length = (K * B) * 2 ^ logI := by rw [hX, Nat.pow_add, Nat.pow_add]; dsimp [K, B]; ac_rfl
  have hPowQ : qTbl.length = (K * J) * B := by rw [hQ, Nat.pow_add, Nat.pow_add]; dsimp [J, K, B]; ac_rfl
  have hPowS : sTbl.length = J * K := by rw [hS, Nat.pow_add]; dsimp [J, K]; ac_rfl
  obtain ⟨hXBLen, hXBFlat, hXBAll⟩ := chunkBlocks_spec (K * B) (2 ^ logI) xTbl hPowX; obtain ⟨hQKJLen, hQKJFlat, hQKJAll⟩ := chunkBlocks_spec (K * J) B qTbl hPowQ
  obtain ⟨hSJLen, hSJFlat, hSJAll⟩ := chunkBlocks_spec J K sTbl hPowS; have hXBkLen : (foldVars xTbl rI).length = K * B := by
    conv => lhs; rw [← hXBFlat, foldVars_flatten_blocks rI _ (fun b hb => hRI ▸ hXBAll b hb)]
    simp [hXBLen]
  have hEqJLen : (eqTable rJ).length = J := by rw [eqTable_length, hRJ]
  have hWKjLen : (scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)).length = K * J := by
    rw [scaleEachBlock_length K _ _ (hEqJLen.trans hSJLen.symm) hSJAll, hEqJLen, Nat.mul_comm]
  have hABLen : (tileBlocks J (foldVars xTbl rI)).length = (K * J) * B := by rw [tileBlocks_length, hXBkLen]; ac_rfl
  have hBBLen : (scaleEachBlock (scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)) (chunkBlocks (K * J) B qTbl)).length =
      (K * J) * B := by rw [scaleEachBlock_length B _ _ (hWKjLen.trans hQKJLen.symm) hQKJAll, hWKjLen]
  have hQKjEq : foldVars qTbl rB = (chunkBlocks (K * J) B qTbl).map (fun b => mleEval b rB) := by
    conv => lhs; rw [← hQKJFlat]
    exact foldVars_flatten_blocks rB _ (fun b hb => hRB ▸ hQKJAll b hb)
  have hQKjLen : (foldVars qTbl rB).length = K * J := by rw [hQKjEq, List.length_map, hQKJLen]
  have hXKLen : (foldVars (foldVars xTbl rI) rB).length = K := foldVars_length_mul rB K _ (hRB ▸ hXBkLen); have hMid12 : innerProd (foldVars (tileBlocks J (foldVars xTbl rI)) rB)
      (foldVars (scaleEachBlock (scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)) (chunkBlocks (K * J) B qTbl)) rB) =
      tripleInnerProd (tileBlocks J (foldVars (foldVars xTbl rI) rB)) (foldVars qTbl rB) (scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)) := by
    rw [foldVars_tileBlocks J rB K _ (hRB ▸ hXBkLen), foldVars_scaleEachBlock rB _ _ (hWKjLen.trans hQKJLen.symm) (fun b hb => hRB ▸ hQKJAll b hb),
        scaleEachBlock_singletons _ _ (foldVars qTbl rB) (hWKjLen.trans hQKjLen.symm)
          (by rw [hQKjEq, List.map_map]; exact List.map_congr_left fun b hb => foldVars_full_eq_singleton rB b (hRB ▸ hQKJAll b hb))]
    exact phase1_to_phase2_sum K J _ _ _ hXKLen hQKjLen hWKjLen
  have hSJFoldEq : foldVars sTbl rK = (chunkBlocks J K sTbl).map (fun b => mleEval b rK) := by
    conv => lhs; rw [← hSJFlat]
    exact foldVars_flatten_blocks rK _ (fun b hb => hRK ▸ hSJAll b hb)
  have hSJFoldLen : (foldVars sTbl rK).length = J := by rw [hSJFoldEq, List.length_map, hSJLen]
  have hQJFoldLen : (foldVars (foldVars qTbl rB) rK).length = J := foldVars_length_mul rK J _ (by rw [hRK, hQKjLen, Nat.mul_comm])
  let xStar := mleEval xTbl (rI ++ rB ++ rK); have hXStar : foldVars (foldVars (foldVars xTbl rI) rB) rK = [xStar] := by
    rw [foldVars_full_eq_singleton rK _ (hRK ▸ hXKLen), mleEval_foldVars, mleEval_foldVars, ← List.append_assoc]
  have hMid23 : tripleInnerProd (foldVars (tileBlocks J (foldVars (foldVars xTbl rI) rB)) rK) (foldVars (foldVars qTbl rB) rK)
      (foldVars (scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)) rK) = tripleInnerProd (scaleList xStar (eqTable rJ)) (foldVars (foldVars qTbl rB) rK) (foldVars sTbl rK) := by
    rw [foldVars_tileBlocks J rK 1 _ (by rw [hRK, Nat.one_mul]; exact hXKLen), hXStar, foldVars_scaleEachBlock rK _ _ (hEqJLen.trans hSJLen.symm) (fun b hb => hRK ▸ hSJAll b hb),
        scaleEachBlock_singletons _ _ (foldVars sTbl rK) (hEqJLen.trans hSJFoldLen.symm)
          (by rw [hSJFoldEq, List.map_map]; exact List.map_congr_left fun b hb => foldVars_full_eq_singleton rK b (hRK ▸ hSJAll b hb)), ← hEqJLen]
    exact phase2_to_phase3_sum xStar (eqTable rJ) _ _ (hEqJLen.trans hQJFoldLen.symm) (hQJFoldLen.trans hSJFoldLen.symm)
  have hFin : tripleInnerProd (foldVars (scaleList xStar (eqTable rJ)) rJp) (foldVars (foldVars (foldVars qTbl rB) rK) rJp) (foldVars (foldVars sTbl rK) rJp) =
      CommRingOps.mul (eqPolyVec rJ rJp) (CommRingOps.mul xStar (CommRingOps.mul (mleEval qTbl (rB ++ rK ++ rJp)) (mleEval sTbl (rK ++ rJp)))) := by
    rw [foldVars_scaleList xStar rJp (eqTable rJ) (hRJp ▸ hEqJLen), foldVars_eqTable rJ rJp (hRJ.trans hRJp.symm), foldVars_full_eq_singleton rJp _ (hRJp ▸ hQJFoldLen),
        foldVars_full_eq_singleton rJp _ (hRJp ▸ hSJFoldLen), mleEval_foldVars, mleEval_foldVars, mleEval_foldVars, ← List.append_assoc, scaleList_cons]
    simp only [scaleList, List.map_nil, tripleInnerProd, LawfulCommRing.add_zero]; rw [LawfulCommRing.mul_comm xStar (eqPolyVec rJ rJp), LawfulCommRing.mul_assoc]
  exact ⟨hABLen, hBBLen, hMid12,
    by rw [tileBlocks_length, hXKLen], by rw [hQKjLen, Nat.mul_comm], by rw [hWKjLen, Nat.mul_comm],
    hMid23, by dsimp [scaleList]; rw [List.length_map, hEqJLen, Nat.one_mul],
    by rw [Nat.one_mul]; exact hQJFoldLen, by rw [Nat.one_mul]; exact hSJFoldLen, hFin⟩
theorem proveMxfp4Sumcheck_complete {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (logI logJ logK logB : Nat) (xTbl : List Goldilocks) (qInts : List Int) (sShifts : List Nat) (rI rJ : List Goldilocks) (tr₀ : Transcript phase)
    (hX : xTbl.length = 2 ^ (logI + logB + logK)) (hQ : qInts.length = 2 ^ (logB + logK + logJ)) (hS : sShifts.length = 2 ^ (logK + logJ))
    (hRI : rI.length = logI) (hRJ : rJ.length = logJ) : let qTbl := qInts.map intToGoldilocks; let sTbl := sShifts.map shiftToGoldilocks
    let dTrue := mxfp4ContractTable logI logJ logK logB xTbl qInts sShifts; let (ps, rB, rK, rJp, tr₃) := proveMxfp4Sumcheck logJ logK logB xTbl qTbl sTbl rI rJ tr₀
    let expectedFinal := CommRingOps.mul (eqPolyVec rJ rJp) (CommRingOps.mul (mleEval xTbl (rI ++ rB ++ rK))
        (CommRingOps.mul (mleEval qTbl (rB ++ rK ++ rJp)) (mleEval sTbl (rK ++ rJp))))
    verifyScheduledSumcheck (mxfp4DegSchedule logB logK logJ) (mleEval dTrue (rI ++ rJ)) ps tr₀ = some ((rB ++ rK ++ rJp, expectedFinal), tr₃) ∧
    rB.length = logB ∧ rK.length = logK ∧ rJp.length = logJ ∧
    ¬ Mxfp4SumcheckRootHit logJ logK logB xTbl qTbl sTbl rI rJ rB rK ps tr₀ := by
  let J := 2 ^ logJ; let K := 2 ^ logK; let qTbl := qInts.map intToGoldilocks; let sTbl := sShifts.map shiftToGoldilocks
  let v1 := mxfp4Phase1Vectors logJ logK logB xTbl qTbl sTbl rI rJ; have hInit := mxfp4_phase1_eq_mle logI logJ logK logB xTbl qInts sShifts rI rJ hRI hRJ hX hQ hS
  have hTr0 := mxfp4_phase_transitions logI logJ logK logB xTbl qTbl sTbl rI rJ
    (List.replicate logB Goldilocks.zero) (List.replicate logK Goldilocks.zero) (List.replicate logJ Goldilocks.zero) hX (by simp [qTbl, hQ]) (by simp [sTbl, hS]) hRI hRJ
    (List.length_replicate ..) (List.length_replicate ..) (List.length_replicate ..)
  let p1 := proveQuadRounds logB v1.1 v1.2 tr₀; obtain ⟨hVer1, hRBL, hAf1, hBf1⟩ := proveQuadRounds_complete logB (K * J) v1.1 v1.2 tr₀ hTr0.1 hTr0.2.1
  let rB := p1.2.1; let tr₁ := p1.2.2.2.2
  have hTr1 := mxfp4_phase_transitions logI logJ logK logB xTbl qTbl sTbl rI rJ rB (List.replicate logK Goldilocks.zero) (List.replicate logJ Goldilocks.zero)
    hX (by simp [qTbl, hQ]) (by simp [sTbl, hS]) hRI hRJ hRBL (List.length_replicate ..) (List.length_replicate ..)
  let a2 := tileBlocks J (foldVars (foldVars xTbl rI) rB); let b2 := foldVars qTbl rB; let c2 := scaleEachBlock (eqTable rJ) (chunkBlocks J K sTbl)
  let p2 := proveCubicRounds logK a2 b2 c2 tr₁; obtain ⟨hVer2, hRKL, hAf2, hBf2, hCf2⟩ := proveCubicRounds_complete logK J a2 b2 c2 tr₁ hTr1.2.2.2.1 hTr1.2.2.2.2.1 hTr1.2.2.2.2.2.1
  let rK := p2.2.1; let tr₂ := p2.2.2.2.2.2; have hTr2 := mxfp4_phase_transitions logI logJ logK logB xTbl qTbl sTbl rI rJ rB rK
    (List.replicate logJ Goldilocks.zero) hX (by simp [qTbl, hQ]) (by simp [sTbl, hS]) hRI hRJ hRBL hRKL (List.length_replicate ..)
  let xStar := mleEval xTbl (rI ++ rB ++ rK); let a3 := scaleList xStar (eqTable rJ); let b3 := foldVars (foldVars qTbl rB) rK; let c3 := foldVars sTbl rK
  let p3 := proveCubicRounds logJ a3 b3 c3 tr₂
  obtain ⟨hVer3, hRJpL, hAf3, hBf3, hCf3⟩ := proveCubicRounds_complete logJ 1 a3 b3 c3 tr₂ hTr2.2.2.2.2.2.2.2.1 hTr2.2.2.2.2.2.2.2.2.1 hTr2.2.2.2.2.2.2.2.2.2.1
  let rJp := p3.2.1; let tr₃ := p3.2.2.2.2.2
  have hTr3 := mxfp4_phase_transitions logI logJ logK logB xTbl qTbl sTbl rI rJ rB rK rJp hX (by simp [qTbl, hQ]) (by simp [sTbl, hS]) hRI hRJ hRBL hRKL hRJpL
  obtain ⟨_, hP1Len⟩ := verifyScheduledSumcheck_point_len _ _ _ _ _ _ _ hVer1; obtain ⟨_, hP2Len⟩ := verifyScheduledSumcheck_point_len _ _ _ _ _ _ _ hVer2
  simp only [List.length_replicate] at hP1Len hP2Len; have hTr1Adv := verifyScheduledSumcheck_transcript_eq _ _ _ _ _ _ _ hVer1
  have hTr2Adv := verifyScheduledSumcheck_transcript_eq _ _ _ _ _ _ _ hVer2; rw [← hInit, hAf1, hBf1, hTr3.2.2.1] at hVer1; rw [hAf2, hBf2, hCf2, hTr3.2.2.2.2.2.2.1] at hVer2
  rw [hAf3, hBf3, hCf3, hTr3.2.2.2.2.2.2.2.2.2.2] at hVer3
  have hVerAll := verifyScheduledSumcheck_append _ _ _ _ _ _ _ _ _ _ _ _ (verifyScheduledSumcheck_append _ _ _ _ _ _ _ _ _ _ _ _ hVer1 hVer2) hVer3
  have hTakeB : (p1.1 ++ p2.1 ++ p3.1).take logB = p1.1 := by rw [List.append_assoc, List.take_left' hP1Len]
  have hTakeK : ((p1.1 ++ p2.1 ++ p3.1).drop logB).take logK = p2.1 := by rw [List.append_assoc, List.drop_left' hP1Len, List.take_left' hP2Len]
  have hDropBK : (p1.1 ++ p2.1 ++ p3.1).drop (logB + logK) = p3.1 := List.drop_left' (by rw [List.length_append, hP1Len, hP2Len])
  dsimp only [proveMxfp4Sumcheck]; refine ⟨hVerAll, hRBL, hRKL, hRJpL, ?_⟩
  unfold Mxfp4SumcheckRootHit; dsimp only; rw [hTakeB, hTakeK, hDropBK, ← hTr1Adv, ← hTr2Adv]
  rintro (h1 | h2 | h3)
  · exact proveQuadRounds_no_rootHit logB v1.1 v1.2 tr₀ h1
  · exact proveCubicRounds_no_rootHit logK a2 b2 c2 tr₁ h2
  · exact proveCubicRounds_no_rootHit logJ a3 b3 c3 tr₂ h3
theorem verifyMxfp4Sumcheck_sound {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (logI logJ logK logB : Nat) (xTbl : List Goldilocks) (qInts : List Int) (sShifts : List Nat) (dClaim fv : Goldilocks) (ps : List (RoundPoly Goldilocks))
    (rI rJ allChals : List Goldilocks) (tr₀ tr₃ : Transcript phase) (hX : xTbl.length = 2 ^ (logI + logB + logK))
    (hQ : qInts.length = 2 ^ (logB + logK + logJ)) (hS : sShifts.length = 2 ^ (logK + logJ)) (hRI : rI.length = logI) (hRJ : rJ.length = logJ)
    (hVer : verifyScheduledSumcheck (mxfp4DegSchedule logB logK logJ) dClaim ps tr₀ = some ((allChals, fv), tr₃)) (hFinEq :
      let rB := allChals.take logB; let rK := (allChals.drop logB).take logK; let rJp := allChals.drop (logB + logK)
      let qTbl := qInts.map intToGoldilocks; let sTbl := sShifts.map shiftToGoldilocks
      fv = CommRingOps.mul (eqPolyVec rJ rJp) (CommRingOps.mul (mleEval xTbl (rI ++ rB ++ rK)) (CommRingOps.mul (mleEval qTbl (rB ++ rK ++ rJp)) (mleEval sTbl (rK ++ rJp)))))
    (hSumFalse : dClaim ≠ mleEval (mxfp4ContractTable logI logJ logK logB xTbl qInts sShifts) (rI ++ rJ)) :
    Mxfp4SumcheckRootHit logJ logK logB xTbl (qInts.map intToGoldilocks) (sShifts.map shiftToGoldilocks) rI rJ (allChals.take logB) ((allChals.drop logB).take logK) ps tr₀ := by
  obtain ⟨hAllLen, _⟩ := verifyScheduledSumcheck_point_len _ _ _ _ _ _ _ hVer; rw [(mxfp4DegSchedule_never_deg_four _ _ _).1] at hAllLen
  rw [mxfp4_phase1_eq_mle logI logJ logK logB xTbl qInts sShifts rI rJ hRI hRJ hX hQ hS] at hSumFalse; unfold mxfp4DegSchedule at hVer; rw [List.append_assoc] at hVer
  obtain ⟨s₁, tr₁, hVerB, hVerKJ⟩ := scheduledSumcheck_split (List.replicate logB 2) (List.replicate logK 3 ++ List.replicate logJ 3) _ _ _ _ _ _ hVer
  simp only [List.length_replicate] at hVerB hVerKJ; obtain ⟨s₂, tr₂, hVerK, hVerJ⟩ := scheduledSumcheck_split (List.replicate logK 3) (List.replicate logJ 3) _ _ _ _ _ _ hVerKJ
  simp only [List.length_replicate, List.drop_drop] at hVerK hVerJ; have hTr1Eq := verifyScheduledSumcheck_transcript_eq _ _ _ _ _ _ _ hVerB
  have hTr2Eq := verifyScheduledSumcheck_transcript_eq _ _ _ _ _ _ _ hVerK
  let rB := allChals.take logB; let rK := (allChals.drop logB).take logK; let rJp := allChals.drop (logB + logK)
  have hRBL : rB.length = logB := by dsimp [rB]; rw [List.length_take, hAllLen]; omega
  have hRKL : rK.length = logK := by dsimp [rK]; rw [List.length_take, List.length_drop, hAllLen]; omega
  have hRJpL : rJp.length = logJ := by dsimp [rJp]; rw [List.length_drop, hAllLen]; omega
  let qTbl := qInts.map intToGoldilocks; let sTbl := sShifts.map shiftToGoldilocks
  have hTr := mxfp4_phase_transitions logI logJ logK logB xTbl qTbl sTbl rI rJ rB rK rJp hX (by simp [qTbl, hQ]) (by simp [sTbl, hS]) hRI hRJ hRBL hRKL hRJpL
  let v1 := mxfp4Phase1Vectors logJ logK logB xTbl qTbl sTbl rI rJ; let a2 := tileBlocks (2 ^ logJ) (foldVars (foldVars xTbl rI) rB); let b2 := foldVars qTbl rB
  let c2 := scaleEachBlock (eqTable rJ) (chunkBlocks (2 ^ logJ) (2 ^ logK) sTbl); let a3 := scaleList (mleEval xTbl (rI ++ rB ++ rK)) (eqTable rJ)
  let b3 := foldVars (foldVars qTbl rB) rK; let c3 := foldVars sTbl rK; unfold Mxfp4SumcheckRootHit; dsimp only; rw [← hTr1Eq, ← hTr2Eq]
  rcases verifyQuadRounds_sound logB (2 ^ logK * 2 ^ logJ) v1.1 v1.2 dClaim (ps.take logB) rB s₁ tr₀ tr₁ hTr.1 hTr.2.1 hVerB hSumFalse with hMid1F | hHitB
  · rw [hTr.2.2.1] at hMid1F
    rcases verifyCubicRounds_sound logK (2 ^ logJ) a2 b2 c2 s₁ ((ps.drop logB).take logK) rK s₂ tr₁ tr₂ hTr.2.2.2.1 hTr.2.2.2.2.1 hTr.2.2.2.2.2.1 hVerK hMid1F with hMid2F | hHitK
    · rw [hTr.2.2.2.2.2.2.1] at hMid2F; rcases verifyCubicRounds_sound logJ 1 a3 b3 c3 s₂ (ps.drop (logB + logK)) rJp fv tr₂ tr₃
          hTr.2.2.2.2.2.2.2.1 hTr.2.2.2.2.2.2.2.2.1 hTr.2.2.2.2.2.2.2.2.2.1 hVerJ hMid2F with hFinF | hHitJ
      · exfalso; exact hFinF (hFinEq.trans hTr.2.2.2.2.2.2.2.2.2.2.symm)
      · exact .inr (.inr hHitJ)
    · exact .inr (.inl hHitK)
  · exact .inl hHitB
end Obend.SymbolicZk.ProvenZkmlGate
end
