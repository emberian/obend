module
/-
# Obend.SymbolicZk.ProvenZkmlGate — Unconditional-Regime (`UDR`/`JBR`) Soundness Gate & Streaming Chunk IVC

Closes *Rainbows End* SHE Gap #4:
1. Unconditional `UDR`/`JBR` vs. withdrawn `CBR` milli-bit soundness accounting (`ZkmlSuiteProfile`,
   `udr_strictly_below_withdrawn_cbr`, `grind_bits_additive_and_regime_free`, `checkZkmlSuiteProvenFloor_sound`).
2. Streaming recurrent chunk-carry IVC (`OBEND.SHE.ZKML_CHUNK/v1`, `verifyZkmlChunkChainExec_iff_spec`,
   `zkmlChunkChain_binds_endToEnd` with scoped `CollisionAmong`, `tampered_weights_or_hidden_carry_refused`).
3. `provenZkmlJudge : Judge ZkmlTurnQuery ZkmlTurnCert` & multi-turn `verifyZkmlSessionTrace_sound`.
-/
public import Obend.Judge.Class
public import Obend.Crypto.Transcript

public section
namespace Obend.SymbolicZk.ProvenZkmlGate

open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Unconditional `UDR` & `JBR` vs. Withdrawn `CBR` Soundness Accounting -/

/-- Decoding regime under which a FRI / BaseFold proximity-gap query phase is analyzed. -/
inductive ZkmlSecurityRegime where
  | provenUdr | provenJbr | withdrawnCbr
  deriving DecidableEq, Repr, Inhabited

/-- Epistemic status of a `ZkmlSecurityRegime`. -/
inductive ZkmlRegimeStatus where
  | unconditionalProven | johnsonIdealised | withdrawnRefuted
  deriving DecidableEq, Repr, Inhabited

/-- `provenUdr` is unconditional; `provenJbr` is Johnson-bound; `withdrawnCbr` is refuted/withdrawn. -/
def ZkmlSecurityRegime.status : ZkmlSecurityRegime → ZkmlRegimeStatus
  | .provenUdr => .unconditionalProven
  | .provenJbr => .johnsonIdealised
  | .withdrawnCbr => .withdrawnRefuted

/-- Only non-withdrawn regimes may be cited by the SHE soundness gate. -/
@[expose] def ZkmlSecurityRegime.Reportable (r : ZkmlSecurityRegime) : Prop :=
  r.status ≠ .withdrawnRefuted

theorem provenUdr_reportable : ZkmlSecurityRegime.provenUdr.Reportable := by
  unfold ZkmlSecurityRegime.Reportable ZkmlSecurityRegime.status; decide
theorem provenJbr_reportable : ZkmlSecurityRegime.provenJbr.Reportable := by
  unfold ZkmlSecurityRegime.Reportable ZkmlSecurityRegime.status; decide
theorem withdrawnCbr_not_reportable : ¬ ZkmlSecurityRegime.withdrawnCbr.Reportable := by
  unfold ZkmlSecurityRegime.Reportable ZkmlSecurityRegime.status; decide

/-- Proof-suite soundness parameters exported by `ZkmlSuiteArtifact` (`CROSS_REPO_CONTRACTS.md` §2). -/
structure ZkmlSuiteProfile where
  fieldModulusBits : Nat
  extDegree : Nat
  logBlowup : Nat
  numQueries : Nat
  grindBits : Nat
  logTraceHeight : Nat
  digestBits : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Mandatory SHE proven soundness floor: `100,000` milli-bits (`100.000` bits). -/
def provenFloorMilliBits : Nat := 100000

/-- Exact integer milli-bits per query in `UDR`: `⌊1000 · (1 - log₂(1 + 2^(-lb)))⌋`. -/
def udrQueryMilliBits : Nat → Nat
  | 0 => 0 | 1 => 415 | 2 => 678 | 3 => 830 | 4 => 912 | 5 => 955
  | 6 => 977 | 7 => 988 | 8 => 994 | 9 => 997 | 10 => 998 | _ => 999

theorem udrQueryMilliBits_lt_1000 (lb : Nat) : udrQueryMilliBits lb < 1000 := by
  match lb with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => decide
  | _ + 11 => simp [udrQueryMilliBits]

theorem udrQueryMilliBits_lt_jbr {lb : Nat} (hlb : 1 ≤ lb) : udrQueryMilliBits lb < lb * 500 := by
  match lb with
  | 0 => omega
  | 1 => decide
  | k + 2 => have := udrQueryMilliBits_lt_1000 (k + 2); omega

/-- Unconditional Unique-Decoding Regime (`UDR`) query + grinding soundness in milli-bits. -/
def udrMilliBits (p : ZkmlSuiteProfile) : Nat :=
  p.numQueries * udrQueryMilliBits p.logBlowup + p.grindBits * 1000
/-- Proven Johnson-Bound Regime (`JBR`, `1 - √ρ`) query + grinding soundness in milli-bits. -/
def jbrMilliBits (p : ZkmlSuiteProfile) : Nat :=
  p.numQueries * (p.logBlowup * 500) + p.grindBits * 1000
/-- Legacy withdrawn Capacity-Bound Regime (`CBR`, `1 - ρ`) formula (`p3-security` `legacy_conjectured_error`). -/
def legacyWithdrawnCbrMilliBits (p : ZkmlSuiteProfile) : Nat :=
  p.logBlowup * p.numQueries * 1000 + p.grindBits * 1000

/-- Query + grinding soundness of `p` evaluated at `r`. -/
def regimeMilliBits (r : ZkmlSecurityRegime) (p : ZkmlSuiteProfile) : Nat :=
  match r with
  | .provenUdr => udrMilliBits p | .provenJbr => jbrMilliBits p
  | .withdrawnCbr => legacyWithdrawnCbrMilliBits p

/-- Extension-field LogUp / Schwartz–Zippel soundness ceiling in milli-bits. -/
def logupCeilingMilliBits (p : ZkmlSuiteProfile) : Nat :=
  (p.fieldModulusBits * p.extDegree - p.logTraceHeight) * 1000
/-- BCS Merkle commitment birthday-collision soundness ceiling in milli-bits. -/
def bcsDigestCeilingMilliBits (p : ZkmlSuiteProfile) : Nat := (p.digestBits / 2) * 1000

def deployedIr2BabyBearExt4 : ZkmlSuiteProfile := ⟨31, 4, 6, 19, 16, 20, 256⟩
def provenUdr86BabyBearExt4 : ZkmlSuiteProfile := { deployedIr2BabyBearExt4 with numQueries := 86 }
def tallTraceBabyBearExt4 : ZkmlSuiteProfile := { provenUdr86BabyBearExt4 with logTraceHeight := 25 }
def provenUdr86BabyBearExt5 : ZkmlSuiteProfile := { tallTraceBabyBearExt4 with extDegree := 5 }

/-- **`udr_strictly_below_withdrawn_cbr`**:
    For every suite with `1 ≤ logBlowup` and `1 ≤ numQueries`, unconditional `UDR` soundness is
    strictly below `JBR`, and `JBR` is strictly below withdrawn `CBR` — proving universally why
    quoting withdrawn `CBR` (`130` bits vs `34.563` bits `UDR`) overstates unconditional soundness. -/
theorem udr_strictly_below_withdrawn_cbr {p : ZkmlSuiteProfile}
    (hlb : 1 ≤ p.logBlowup) (hq : 1 ≤ p.numQueries) :
    udrMilliBits p < jbrMilliBits p ∧
    jbrMilliBits p < legacyWithdrawnCbrMilliBits p ∧
    udrMilliBits p < legacyWithdrawnCbrMilliBits p := by
  have hPos : 0 < p.numQueries := Nat.lt_of_lt_of_le (by decide) hq
  have hLbPos : 0 < p.logBlowup := Nat.lt_of_lt_of_le (by decide) hlb
  have h500 : p.logBlowup * 500 < p.logBlowup * 1000 :=
    Nat.mul_lt_mul_of_pos_left (by decide) hLbPos
  have hMul1 := Nat.mul_lt_mul_of_pos_left (udrQueryMilliBits_lt_jbr hlb) hPos
  have hMul2 := Nat.mul_lt_mul_of_pos_left h500 hPos
  have hComm : p.numQueries * (p.logBlowup * 1000) = p.logBlowup * p.numQueries * 1000 := by
    rw [← Nat.mul_assoc, Nat.mul_comm p.numQueries p.logBlowup]
  rw [hComm] at hMul2
  unfold udrMilliBits jbrMilliBits legacyWithdrawnCbrMilliBits
  have h1 := Nat.add_lt_add_right hMul1 (p.grindBits * 1000)
  have h2 := Nat.add_lt_add_right hMul2 (p.grindBits * 1000)
  exact ⟨h1, h2, Nat.lt_trans h1 h2⟩

theorem deployedIr2_three_regimes_and_86_minimality :
    udrMilliBits deployedIr2BabyBearExt4 = 34563 ∧
    jbrMilliBits deployedIr2BabyBearExt4 = 73000 ∧
    legacyWithdrawnCbrMilliBits deployedIr2BabyBearExt4 = 130000 ∧
    udrMilliBits { deployedIr2BabyBearExt4 with numQueries := 85 } = 99045 ∧
    udrMilliBits provenUdr86BabyBearExt4 = 100022 := by
  decide

/-- **`grind_bits_additive_and_regime_free`**:
    Adding `g` PoW grinding bits adds `+ 1000 * g` milli-bits identically across `UDR` and `JBR`,
    whereas query bits scale multiplicatively by regime (`udrQueryMilliBits lb ≠ lb * 500`). -/
theorem grind_bits_additive_and_regime_free (p : ZkmlSuiteProfile) (g : Nat) :
    udrMilliBits { p with grindBits := p.grindBits + g } = udrMilliBits p + 1000 * g ∧
    jbrMilliBits { p with grindBits := p.grindBits + g } = jbrMilliBits p + 1000 * g ∧
    (1 ≤ p.logBlowup →
      udrMilliBits { p with numQueries := p.numQueries + 1 } - udrMilliBits p ≠
      jbrMilliBits { p with numQueries := p.numQueries + 1 } - jbrMilliBits p) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold udrMilliBits
    simp only [Nat.add_mul]
    omega
  · unfold jbrMilliBits
    simp only [Nat.add_mul]
    omega
  · intro hlb
    have hlt := udrQueryMilliBits_lt_jbr hlb
    unfold udrMilliBits jbrMilliBits
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem extDegree_moves_logup_only (p : ZkmlSuiteProfile) (d' : Nat) :
    udrMilliBits { p with extDegree := d' } = udrMilliBits p ∧
    jbrMilliBits { p with extDegree := d' } = jbrMilliBits p := by
  exact ⟨rfl, rfl⟩

/-- Declarative SHE proven-floor specification: reportable regime and `≥ 100,000` milli-bits across
    query+grind, extension-field LogUp ceiling, and BCS Merkle digest ceiling. -/
@[expose] def ZkmlSuiteMeetsProvenFloor (r : ZkmlSecurityRegime) (p : ZkmlSuiteProfile) : Prop :=
  r.Reportable ∧
  provenFloorMilliBits ≤ regimeMilliBits r p ∧
  provenFloorMilliBits ≤ logupCeilingMilliBits p ∧
  provenFloorMilliBits ≤ bcsDigestCeilingMilliBits p

/-- Executable SHE suite floor gate. Unconditionally refuses `.withdrawnCbr`. -/
def checkZkmlSuiteProvenFloor (r : ZkmlSecurityRegime) (p : ZkmlSuiteProfile) : Bool :=
  match r with
  | .withdrawnCbr => false
  | .provenUdr =>
    decide (provenFloorMilliBits ≤ udrMilliBits p) &&
    decide (provenFloorMilliBits ≤ logupCeilingMilliBits p) &&
    decide (provenFloorMilliBits ≤ bcsDigestCeilingMilliBits p)
  | .provenJbr =>
    decide (provenFloorMilliBits ≤ jbrMilliBits p) &&
    decide (provenFloorMilliBits ≤ logupCeilingMilliBits p) &&
    decide (provenFloorMilliBits ≤ bcsDigestCeilingMilliBits p)

theorem checkZkmlSuiteProvenFloor_iff (r : ZkmlSecurityRegime) (p : ZkmlSuiteProfile) :
    checkZkmlSuiteProvenFloor r p = true ↔ ZkmlSuiteMeetsProvenFloor r p := by
  cases r with
  | withdrawnCbr =>
    simp [checkZkmlSuiteProvenFloor, ZkmlSuiteMeetsProvenFloor,
      ZkmlSecurityRegime.Reportable, ZkmlSecurityRegime.status]
  | provenUdr =>
    simp [checkZkmlSuiteProvenFloor, ZkmlSuiteMeetsProvenFloor, regimeMilliBits,
      provenUdr_reportable, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  | provenJbr =>
    simp [checkZkmlSuiteProvenFloor, ZkmlSuiteMeetsProvenFloor, regimeMilliBits,
      provenJbr_reportable, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- **`checkZkmlSuiteProvenFloor_sound`**:
    Any accepted `(r, p)` pair excludes `withdrawnCbr`, clears the `100,000` milli-bit floor across
    query+grind, LogUp, and BCS digest ceilings, and enforces `logTraceHeight + 100 ≤ fieldModulusBits * extDegree`
    and `200 ≤ digestBits`. -/
theorem checkZkmlSuiteProvenFloor_sound {r : ZkmlSecurityRegime} {p : ZkmlSuiteProfile}
    (h : checkZkmlSuiteProvenFloor r p = true) :
    ZkmlSuiteMeetsProvenFloor r p ∧
    r ≠ .withdrawnCbr ∧
    p.logTraceHeight + 100 ≤ p.fieldModulusBits * p.extDegree ∧
    200 ≤ p.digestBits := by
  have hm := (checkZkmlSuiteProvenFloor_iff r p).mp h
  have hRep := hm.1
  have hLog := hm.2.2.1
  have hBcs := hm.2.2.2
  have hNe : r ≠ .withdrawnCbr := by
    intro hEq
    rw [hEq] at hRep
    exact withdrawnCbr_not_reportable hRep
  unfold provenFloorMilliBits logupCeilingMilliBits at hLog
  unfold provenFloorMilliBits bcsDigestCeilingMilliBits at hBcs
  exact ⟨hm, hNe, by omega, by omega⟩

theorem withdrawnCbr_suite_always_refused (p : ZkmlSuiteProfile) :
    checkZkmlSuiteProvenFloor .withdrawnCbr p = false := by
  rfl

theorem suite_floor_admission_refusal_matrix :
    checkZkmlSuiteProvenFloor .provenUdr deployedIr2BabyBearExt4 = false ∧
    checkZkmlSuiteProvenFloor .provenJbr deployedIr2BabyBearExt4 = false ∧
    checkZkmlSuiteProvenFloor .withdrawnCbr deployedIr2BabyBearExt4 = false ∧
    checkZkmlSuiteProvenFloor .provenUdr tallTraceBabyBearExt4 = false ∧
    checkZkmlSuiteProvenFloor .provenUdr provenUdr86BabyBearExt4 = true ∧
    checkZkmlSuiteProvenFloor .provenUdr provenUdr86BabyBearExt5 = true := by
  decide

theorem checkZkmlSuiteProvenFloor_inhabited :
    ∃ r p, checkZkmlSuiteProvenFloor r p = true ∧ ZkmlSuiteMeetsProvenFloor r p :=
  ⟨.provenUdr, provenUdr86BabyBearExt4, by decide,
    (checkZkmlSuiteProvenFloor_iff .provenUdr provenUdr86BabyBearExt4).mp (by decide)⟩

/-! ## 2. Streaming Recurrent Chunk-Carry IVC (`OBEND.SHE.ZKML_CHUNK/v1`) -/

/-- Big-endian 8-byte `UInt64` encoding (`u64::to_be_bytes`). -/
def u64ToBe8 (w : UInt64) : List UInt8 :=
  be 8 w.toNat

theorem u64ToBe8_length (w : UInt64) : (u64ToBe8 w).length = 8 :=
  length_be ..

theorem u64ToBe8_injective {w₁ w₂ : UInt64} (h : u64ToBe8 w₁ = u64ToBe8 w₂) : w₁ = w₂ :=
  UInt64.toNat_inj.mp (be_injective (w := 8) w₁.toNat_lt w₂.toNat_lt h)

/-- Concatenate LEB128-length-framed byte fields (`encodeListField f = leb128 f.length ++ f`). -/
def encodeZkmlFields : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => encodeListField f ++ encodeZkmlFields fs

private theorem encodeListField_ne_nil (f : List UInt8) : encodeListField f ≠ [] := by
  unfold encodeListField leb128
  cases f.length with
  | zero => simp [leb128Aux]
  | succ _ =>
    simp only [leb128Aux]
    split <;> simp

theorem encodeZkmlFields_injective :
    ∀ {fs₁ fs₂ : List (List UInt8)},
      encodeZkmlFields fs₁ = encodeZkmlFields fs₂ → fs₁ = fs₂
  | [], [], _ => rfl
  | [], b :: _, h =>
    absurd h.symm (fun hemp => encodeListField_ne_nil b (List.append_eq_nil_iff.mp hemp).1)
  | a :: _, [], h =>
    absurd h (fun hemp => encodeListField_ne_nil a (List.append_eq_nil_iff.mp hemp).1)
  | _ :: _, _ :: _, h => by
    simp only [encodeZkmlFields] at h
    obtain ⟨hab, hrest⟩ := encodeListField_prefix_inj h
    rw [hab, encodeZkmlFields_injective hrest]

/-- Domain-separated 32-byte `cSHAKE256` commitment over LEB128-framed fields. -/
def zkmlDomainHash (domain : String) (fields : List (List UInt8)) : ByteArray :=
  cshake32ByteArray domain.toUTF8.data.toList (encodeZkmlFields fields)

/-- Constructive `0 Classical` collision extractor for `cshake32ByteArray`. -/
def extractZkmlCshake32 (customization p₁ p₂ : List UInt8)
    (h : cshake32ByteArray customization p₁ = cshake32ByteArray customization p₂) :
    PSum (PLift (p₁ = p₂))
      (PLift (CollisionAmong (cshake256Bytes customization) (fun x => x = p₁ ∨ x = p₂))) :=
  if hp : p₁ = p₂ then
    .inl ⟨hp⟩
  else
    .inr ⟨by
      have hl : (cshake32ByteArray customization p₁).data.toList =
          (cshake32ByteArray customization p₂).data.toList :=
        congrArg (fun b => b.data.toList) h
      simp only [cshake32ByteArray, Native.bytesOfList_toList] at hl
      exact ⟨p₁, p₂, .inl rfl, .inr rfl, hp, congrArg ofBE hl⟩⟩

/-- Streaming edge-inference chunk receipt carrying recurrent Gated-DeltaNet / SSM state commitments,
    pinned model weights & policy floor digests, and deterministic PoW nonce. -/
structure ZkmlChunkReceipt where
  modelWeightsRoot : ByteArray
  policyFloorDigest : ByteArray
  suiteDigest : ByteArray
  chunkIdx : UInt64
  stateInCommit : ByteArray
  inputCommit : ByteArray
  stateOutCommit : ByteArray
  outputCommit : ByteArray
  powNonce : UInt64
  deriving DecidableEq, Inhabited

/-- Canonical 256-bit (`32`-byte) width invariant for all 7 digest/commitment fields of `ZkmlChunkReceipt`. -/
@[expose] def ZkmlChunkReceipt.WellFormed32 (c : ZkmlChunkReceipt) : Prop :=
  c.modelWeightsRoot.size = 32 ∧ c.policyFloorDigest.size = 32 ∧ c.suiteDigest.size = 32 ∧
  c.stateInCommit.size = 32 ∧ c.inputCommit.size = 32 ∧ c.stateOutCommit.size = 32 ∧
  c.outputCommit.size = 32

/-- Ordered 9-field payload list for `OBEND.SHE.ZKML_CHUNK/v1` (matching `zkml_gate.rs`). -/
def ZkmlChunkReceipt.fields (c : ZkmlChunkReceipt) : List (List UInt8) :=
  [c.modelWeightsRoot.data.toList, c.policyFloorDigest.data.toList, c.suiteDigest.data.toList,
   u64ToBe8 c.chunkIdx, c.stateInCommit.data.toList, c.inputCommit.data.toList,
   c.stateOutCommit.data.toList, c.outputCommit.data.toList, u64ToBe8 c.powNonce]

/-- Exact 9-field LEB128-framed preimage hashed under `"OBEND.SHE.ZKML_CHUNK/v1"`. -/
def ZkmlChunkReceipt.preimage (c : ZkmlChunkReceipt) : List UInt8 :=
  encodeZkmlFields c.fields

/-- 32-byte `OBEND.SHE.ZKML_CHUNK/v1` `cSHAKE256` commitment to `c`. -/
def zkmlChunkDigest (c : ZkmlChunkReceipt) : ByteArray :=
  zkmlDomainHash "OBEND.SHE.ZKML_CHUNK/v1"
    [ c.modelWeightsRoot.data.toList
    , c.policyFloorDigest.data.toList
    , c.suiteDigest.data.toList
    , u64ToBe8 c.chunkIdx
    , c.stateInCommit.data.toList
    , c.inputCommit.data.toList
    , c.stateOutCommit.data.toList
    , c.outputCommit.data.toList
    , u64ToBe8 c.powNonce
    ]

theorem zkmlChunkDigest_eq_cshake (c : ZkmlChunkReceipt) :
    zkmlChunkDigest c =
      cshake32ByteArray "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList c.preimage := by
  rfl

theorem zkmlChunkDigest_size (c : ZkmlChunkReceipt) : (zkmlChunkDigest c).size = 32 := by
  unfold zkmlChunkDigest zkmlDomainHash
  exact cshake32ByteArray_size _ _

/-- **Unconditional 9-Field Framing Injectivity (`zkmlChunkReceipt_preimage_injective`)**:
    Equal preimages imply full structural equality across all 9 fields of `ZkmlChunkReceipt`. -/
theorem zkmlChunkReceipt_preimage_injective {c₁ c₂ : ZkmlChunkReceipt}
    (h : c₁.preimage = c₂.preimage) : c₁ = c₂ := by
  have hf := encodeZkmlFields_injective h
  simp only [ZkmlChunkReceipt.fields, List.cons.injEq, and_true] at hf
  obtain ⟨hw, hp, hs, hidx, hsin, hin, hsout, hout, hnonce⟩ := hf
  cases c₁
  cases c₂
  simp only [ZkmlChunkReceipt.mk.injEq]
  exact ⟨byteArray_eq_of_toList_eq hw, byteArray_eq_of_toList_eq hp,
    byteArray_eq_of_toList_eq hs, u64ToBe8_injective hidx,
    byteArray_eq_of_toList_eq hsin, byteArray_eq_of_toList_eq hin,
    byteArray_eq_of_toList_eq hsout, byteArray_eq_of_toList_eq hout,
    u64ToBe8_injective hnonce⟩

/-- Constructive `0 Classical` single-chunk commitment binding extractor. -/
def extractZkmlChunkBinding (c₁ c₂ : ZkmlChunkReceipt)
    (h : zkmlChunkDigest c₁ = zkmlChunkDigest c₂) :
    PSum (PLift (c₁ = c₂))
      (PLift (CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList)
        (fun x => x = c₁.preimage ∨ x = c₂.preimage))) :=
  match extractZkmlCshake32 "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList
      c₁.preimage c₂.preimage h with
  | .inl hp => .inl ⟨zkmlChunkReceipt_preimage_injective hp.down⟩
  | .inr hc => .inr hc

/-- **9-Field Single-Chunk Binding (`zkmlChunkDigest_binds`, `0 Classical`)**. -/
theorem zkmlChunkDigest_binds {c₁ c₂ : ZkmlChunkReceipt}
    (h : zkmlChunkDigest c₁ = zkmlChunkDigest c₂) :
    c₁ = c₂ ∨
      CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList)
        (fun x => x = c₁.preimage ∨ x = c₂.preimage) := by
  cases extractZkmlChunkBinding c₁ c₂ h with
  | inl heq => exact .inl heq.down
  | inr hcol => exact .inr hcol.down

/-- Little-endian 64-bit integer sample from bytes `0..7` of a 32-byte digest (`u64::from_le_bytes`). -/
def digestLow64LE (d : ByteArray) : Nat :=
  (d.data.getD 0 0).toNat + (d.data.getD 1 0).toNat * 256 +
  (d.data.getD 2 0).toNat * 65536 + (d.data.getD 3 0).toNat * 16777216 +
  (d.data.getD 4 0).toNat * 4294967296 + (d.data.getD 5 0).toNat * 1099511627776 +
  (d.data.getD 6 0).toNat * 281474976710656 + (d.data.getD 7 0).toNat * 72057594037927936

/-- Declarative per-chunk PoW grinding condition: `powBits ≤ 64` low zero bits in `zkmlChunkDigest c`. -/
@[expose] def ChunkMeetsPow (powBits : Nat) (c : ZkmlChunkReceipt) : Prop :=
  powBits ≤ 64 ∧ digestLow64LE (zkmlChunkDigest c) % (2 ^ powBits) = 0

/-- Executable per-chunk PoW verifier on an already-computed 32-byte chunk digest. -/
def checkChunkPow (powBits : Nat) (digest : ByteArray) : Bool :=
  decide (powBits ≤ 64) && decide (digestLow64LE digest % (2 ^ powBits) = 0)

theorem checkChunkPow_iff (powBits : Nat) (c : ZkmlChunkReceipt) :
    checkChunkPow powBits (zkmlChunkDigest c) = true ↔ ChunkMeetsPow powBits c := by
  simp [checkChunkPow, ChunkMeetsPow, Bool.and_eq_true, decide_eq_true_eq]

theorem chunkMeetsPow_zero (c : ZkmlChunkReceipt) : ChunkMeetsPow 0 c :=
  ⟨by decide, Nat.mod_one _⟩

/-- Public streaming recurrent inference statement (`CandidateComputation` boundary). -/
structure ZkmlStreamStatement where
  modelWeightsRoot : ByteArray
  policyFloorDigest : ByteArray
  suiteDigest : ByteArray
  initialStateCommit : ByteArray
  finalStateCommit : ByteArray
  numChunks : Nat
  requiredPowBits : Nat
  deriving DecidableEq, Inhabited

/-- Canonical 256-bit (`32`-byte) width & non-empty chunk-count invariant on `ZkmlStreamStatement`. -/
@[expose] def ZkmlStreamStatement.WellFormed32 (s : ZkmlStreamStatement) : Prop :=
  s.modelWeightsRoot.size = 32 ∧ s.policyFloorDigest.size = 32 ∧ s.suiteDigest.size = 32 ∧
  s.initialStateCommit.size = 32 ∧ s.finalStateCommit.size = 32 ∧
  1 ≤ s.numChunks ∧ s.numChunks < 2 ^ 64 ∧ s.requiredPowBits ≤ 64

/-- Inductive multi-chunk Gated-DeltaNet / SSM recurrent carry trace from `(idx, curState)` to `finalState`. -/
inductive RecurrentCarrySteps (weightsRoot policyDigest suiteDigest : ByteArray) (powBits : Nat) :
    Nat → ByteArray → List ZkmlChunkReceipt → ByteArray → Prop where
  | nil (idx : Nat) (st : ByteArray) :
      RecurrentCarrySteps weightsRoot policyDigest suiteDigest powBits idx st [] st
  | cons {idx : Nat} {finalSt : ByteArray} (c : ZkmlChunkReceipt) (rest : List ZkmlChunkReceipt) :
      c.WellFormed32 → c.modelWeightsRoot = weightsRoot → c.policyFloorDigest = policyDigest →
      c.suiteDigest = suiteDigest → c.chunkIdx.toNat = idx → ChunkMeetsPow powBits c →
      RecurrentCarrySteps weightsRoot policyDigest suiteDigest powBits (idx + 1) c.stateOutCommit rest finalSt →
      RecurrentCarrySteps weightsRoot policyDigest suiteDigest powBits idx c.stateInCommit (c :: rest) finalSt

/-- Declarative `Spec` of a valid `K`-chunk streaming recurrent IVC chain. -/
@[expose] def ValidZkmlChunkChainSpec (stmt : ZkmlStreamStatement) (chain : List ZkmlChunkReceipt) : Prop :=
  stmt.WellFormed32 ∧ chain.length = stmt.numChunks ∧
  RecurrentCarrySteps stmt.modelWeightsRoot stmt.policyFloorDigest stmt.suiteDigest
    stmt.requiredPowBits 0 stmt.initialStateCommit chain stmt.finalStateCommit

theorem recurrentCarrySteps_element_invariants
    {w p s : ByteArray} {pow idx : Nat} {stIn stOut : ByteArray} {chain : List ZkmlChunkReceipt}
    (h : RecurrentCarrySteps w p s pow idx stIn chain stOut) :
    (∀ i (hi : i < chain.length),
      chain[i].WellFormed32 ∧ chain[i].modelWeightsRoot = w ∧ chain[i].policyFloorDigest = p ∧
      chain[i].suiteDigest = s ∧ chain[i].chunkIdx.toNat = idx + i ∧ ChunkMeetsPow pow chain[i]) ∧
    (∀ i (hi1 : i + 1 < chain.length), chain[i].stateOutCommit = chain[i + 1].stateInCommit) ∧
    (∀ hne : chain ≠ [],
      (chain.head hne).stateInCommit = stIn ∧ (chain.getLast hne).stateOutCommit = stOut) := by
  induction h with
  | nil =>
    exact ⟨(fun _ hi => nomatch hi), (fun _ hi1 => nomatch hi1), (fun hne => absurd rfl hne)⟩
  | @cons idx' finalSt c rest hwf hw hp hs hidx hpow hrest ih =>
    obtain ⟨hElem, hAdj, hEnds⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        exact ⟨hwf, hw, hp, hs, hidx, hpow⟩
      | succ j =>
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        have hSub := hElem j hj
        have hShift : idx' + (j + 1) = idx' + 1 + j := by omega
        rw [hShift]
        simpa only [List.getElem_cons_succ] using hSub
    · intro i hi1
      cases i with
      | zero =>
        cases rest with
        | nil => simp at hi1
        | cons c₂ rs =>
          have hHead := (hEnds (List.cons_ne_nil c₂ rs)).1
          simpa [List.head_cons] using hHead.symm
      | succ j =>
        have hj1 : j + 1 < rest.length := Nat.lt_of_succ_lt_succ hi1
        simpa only [List.getElem_cons_succ] using hAdj j hj1
    · intro _
      refine ⟨rfl, ?_⟩
      cases rest with
      | nil =>
        generalize hcOut : c.stateOutCommit = stMid at hrest
        cases hrest
        exact hcOut
      | cons c₂ rs =>
        have hLast := (hEnds (List.cons_ne_nil c₂ rs)).2
        simpa [List.getLast_cons] using hLast

/-- **Multi-Chunk Recurrent Carry & Pinned-Weights Theorem (`validZkmlChunkChain_invariants`)**. -/
theorem validZkmlChunkChain_invariants {stmt : ZkmlStreamStatement} {chain : List ZkmlChunkReceipt}
    (h : ValidZkmlChunkChainSpec stmt chain) :
    1 ≤ chain.length ∧
    (∀ i (hi : i < chain.length),
      chain[i].modelWeightsRoot = stmt.modelWeightsRoot ∧
      chain[i].policyFloorDigest = stmt.policyFloorDigest ∧
      chain[i].suiteDigest = stmt.suiteDigest ∧
      chain[i].chunkIdx.toNat = i ∧
      ChunkMeetsPow stmt.requiredPowBits chain[i]) ∧
    (∀ i (hi1 : i + 1 < chain.length),
      chain[i].stateOutCommit = chain[i + 1].stateInCommit) ∧
    (∀ hne : chain ≠ [],
      (chain.head hne).stateInCommit = stmt.initialStateCommit ∧
      (chain.getLast hne).stateOutCommit = stmt.finalStateCommit) := by
  obtain ⟨hStmt, hLen, hSteps⟩ := h
  have hGe1 : 1 ≤ stmt.numChunks := hStmt.2.2.2.2.2.1
  have hAll := recurrentCarrySteps_element_invariants hSteps
  refine ⟨by omega, ?_, hAll.2.1, hAll.2.2⟩
  intro i hi
  obtain ⟨_, hw, hp, hs, hidx, hpow⟩ := hAll.1 i hi
  exact ⟨hw, hp, hs, by simpa using hidx, hpow⟩

/-- **`zkmlChunkChain_binds_endToEnd` (`0 Classical`, Scoped `CollisionAmong`)**:
    Equal chunk-digest chains across ANY two streaming inference runs `chain₁, chain₂` constructively
    establish `chain₁ = chain₂` across all chunks `0..K-1`, or extract an explicit scoped
    `CollisionAmong` restricted to `(chain₁ ++ chain₂).map preimage`. -/
theorem zkmlChunkChain_binds_endToEnd :
    ∀ {chain₁ chain₂ : List ZkmlChunkReceipt},
      chain₁.map zkmlChunkDigest = chain₂.map zkmlChunkDigest →
      chain₁ = chain₂ ∨
        CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList)
          (fun x => x ∈ (chain₁ ++ chain₂).map ZkmlChunkReceipt.preimage)
  | [], [], _ => .inl rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | c₁ :: rs₁, c₂ :: rs₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    cases extractZkmlChunkBinding c₁ c₂ h.1 with
    | inr hHeadCol =>
      right
      refine hHeadCol.down.mono ?_
      intro x hx
      simp only [List.cons_append, List.map_cons, List.mem_cons, List.map_append, List.mem_append]
      rcases hx with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inr (.inl rfl))
    | inl hHeadEq =>
      cases zkmlChunkChain_binds_endToEnd h.2 with
      | inl hTailEq =>
        left
        rw [hHeadEq.down, hTailEq]
      | inr hTailCol =>
        right
        refine hTailCol.mono ?_
        intro x hx
        simp only [List.map_append, List.mem_append] at hx
        simp only [List.cons_append, List.map_cons, List.mem_cons, List.map_append, List.mem_append]
        rcases hx with hx₁ | hx₂
        · exact .inr (.inl hx₁)
        · exact .inr (.inr (.inr hx₂))

/-! ## 3. Execution-Tier $O(K)$ Array Verifier, `provenZkmlJudge`, & Multi-Turn SHE Continuity -/

/-- Refusal clause vocabulary for `provenZkmlJudge`. -/
inductive ZkmlRefusalClause where
  | withdrawnCbrRejected
  | belowProven100BitFloor
  | weightRootDrift
  | brokenRecurrentCarry
  | insufficientPowGrind
  | certDigestMismatch
  deriving DecidableEq, Repr, Inhabited

/-- Clauses whose refusal refutes `ZkmlTurnMeaning q c'` for **every** certificate `c'`. -/
def provenZkmlRefutes : ZkmlRefusalClause → Bool
  | .withdrawnCbrRejected => true
  | .belowProven100BitFloor => true
  | .weightRootDrift => true
  | .brokenRecurrentCarry => true
  | .insufficientPowGrind => true
  | .certDigestMismatch => false

private def chunkRootMismatch (stmt : ZkmlStreamStatement) (c : ZkmlChunkReceipt) : Bool :=
  decide (c.modelWeightsRoot.size ≠ 32) ||
  decide (c.policyFloorDigest.size ≠ 32) ||
  decide (c.suiteDigest.size ≠ 32) ||
  decide (c.modelWeightsRoot ≠ stmt.modelWeightsRoot) ||
  decide (c.policyFloorDigest ≠ stmt.policyFloorDigest) ||
  decide (c.suiteDigest ≠ stmt.suiteDigest)

private def chunkCarryMismatch (idx : Nat) (curState : ByteArray) (c : ZkmlChunkReceipt) : Bool :=
  decide (c.stateInCommit.size ≠ 32) ||
  decide (c.inputCommit.size ≠ 32) ||
  decide (c.stateOutCommit.size ≠ 32) ||
  decide (c.outputCommit.size ≠ 32) ||
  decide (c.chunkIdx.toNat ≠ idx) ||
  decide (c.stateInCommit ≠ curState)

/-- Linear single-pass `Array` loop checking recurrent chunk carries and accumulating 32-byte digests. -/
def verifyChunksLoop (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt) :
    Nat → Nat → ByteArray → Array ByteArray → Except (ZkmlRefusalClause × List Nat) (Array ByteArray)
  | 0, idx, curState, acc =>
    if decide (curState = stmt.finalStateCommit) then .ok acc
    else .error (.brokenRecurrentCarry, [idx])
  | rem + 1, idx, curState, acc =>
    if hIdx : idx < chunks.size then
      let c := chunks[idx]
      if chunkRootMismatch stmt c then
        .error (.weightRootDrift, [idx])
      else if chunkCarryMismatch idx curState c then
        .error (.brokenRecurrentCarry, [idx])
      else
        let d := zkmlChunkDigest c
        if !checkChunkPow stmt.requiredPowBits d then
          .error (.insufficientPowGrind, [idx])
        else
          verifyChunksLoop stmt chunks rem (idx + 1) c.stateOutCommit (acc.push d)
    else
      .error (.brokenRecurrentCarry, [idx])

/-- $O(K)$ `Exec`-tier verifier over `Array ZkmlChunkReceipt`. -/
def verifyZkmlChunkChainExec (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt) :
    Except (ZkmlRefusalClause × List Nat) (Array ByteArray) :=
  if !decide (stmt.requiredPowBits ≤ 64) then
    .error (.insufficientPowGrind, [])
  else if decide (stmt.modelWeightsRoot.size ≠ 32) || decide (stmt.policyFloorDigest.size ≠ 32) ||
      decide (stmt.suiteDigest.size ≠ 32) then
    .error (.weightRootDrift, [])
  else if decide (stmt.initialStateCommit.size ≠ 32) || decide (stmt.finalStateCommit.size ≠ 32) ||
      !decide (1 ≤ stmt.numChunks) || !decide (stmt.numChunks < 2 ^ 64) ||
      decide (chunks.size ≠ stmt.numChunks) then
    .error (.brokenRecurrentCarry, [chunks.size])
  else
    verifyChunksLoop stmt chunks chunks.size 0 stmt.initialStateCommit #[]

private theorem verifyChunksLoop_sound (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt) :
    ∀ (rem idx : Nat) (curState : ByteArray) (acc out : Array ByteArray),
      chunks.size - idx = rem →
      verifyChunksLoop stmt chunks rem idx curState acc = .ok out →
      RecurrentCarrySteps stmt.modelWeightsRoot stmt.policyFloorDigest stmt.suiteDigest
        stmt.requiredPowBits idx curState (chunks.toList.drop idx) stmt.finalStateCommit ∧
      out.toList = acc.toList ++ (chunks.toList.drop idx).map zkmlChunkDigest
  | 0, idx, curState, acc, out, hRem, hOk => by
    have hDrop : chunks.toList.drop idx = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
    rw [hDrop]
    unfold verifyChunksLoop at hOk
    cases hEq : decide (curState = stmt.finalStateCommit)
    · simp [hEq] at hOk
    · simp only [hEq, ↓reduceIte, Except.ok.injEq] at hOk
      have hSt : curState = stmt.finalStateCommit := of_decide_eq_true hEq
      rw [hSt, ← hOk]
      exact ⟨.nil idx stmt.finalStateCommit, by simp⟩
  | rem + 1, idx, curState, acc, out, hRem, hOk => by
    have hIdx : idx < chunks.size := by omega
    have hDrop : chunks.toList.drop idx = chunks[idx] :: chunks.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact hIdx)]
      simp only [Array.getElem_toList]
    rw [hDrop]
    unfold verifyChunksLoop at hOk
    simp only [hIdx, ↓reduceDIte] at hOk
    cases hRoot : chunkRootMismatch stmt chunks[idx]
    · simp only [hRoot, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hCarry : chunkCarryMismatch idx curState chunks[idx]
      · simp only [hCarry, Bool.false_eq_true, ↓reduceIte] at hOk
        cases hPow : checkChunkPow stmt.requiredPowBits (zkmlChunkDigest chunks[idx])
        · simp [hPow] at hOk
        · simp only [hPow, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
          obtain ⟨hSteps, hOut⟩ := verifyChunksLoop_sound stmt chunks rem (idx + 1)
            chunks[idx].stateOutCommit (acc.push (zkmlChunkDigest chunks[idx])) out (by omega) hOk
          unfold chunkRootMismatch at hRoot
          unfold chunkCarryMismatch at hCarry
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not] at hRoot hCarry
          obtain ⟨⟨⟨⟨⟨hwSz, hpSz⟩, hsSz⟩, hwEq⟩, hpEq⟩, hsEq⟩ := hRoot
          obtain ⟨⟨⟨⟨⟨hsinSz, hinSz⟩, hsoutSz⟩, houtSz⟩, hIdxEq⟩, hSinEq⟩ := hCarry
          have hWf : chunks[idx].WellFormed32 :=
            ⟨hwSz, hpSz, hsSz, hsinSz, hinSz, hsoutSz, houtSz⟩
          have hPowSpec : ChunkMeetsPow stmt.requiredPowBits chunks[idx] :=
            (checkChunkPow_iff stmt.requiredPowBits chunks[idx]).mp hPow
          rw [← hSinEq]
          refine ⟨.cons chunks[idx] _ hWf hwEq hpEq hsEq hIdxEq hPowSpec hSteps, ?_⟩
          rw [hOut]
          simp [Array.toList_push, List.append_assoc]
      · simp [hCarry] at hOk
    · simp [hRoot] at hOk

private theorem verifyChunksLoop_complete (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt) :
    ∀ (rem idx : Nat) (curState : ByteArray) (acc : Array ByteArray),
      chunks.size - idx = rem →
      RecurrentCarrySteps stmt.modelWeightsRoot stmt.policyFloorDigest stmt.suiteDigest
        stmt.requiredPowBits idx curState (chunks.toList.drop idx) stmt.finalStateCommit →
      verifyChunksLoop stmt chunks rem idx curState acc =
        .ok ⟨acc.toList ++ (chunks.toList.drop idx).map zkmlChunkDigest⟩
  | 0, idx, _, acc, hRem, hSteps => by
    have hDrop : chunks.toList.drop idx = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
    rw [hDrop] at hSteps ⊢
    cases hSteps with
    | nil => unfold verifyChunksLoop; simp
  | rem + 1, idx, _, acc, hRem, hSteps => by
    have hIdx : idx < chunks.size := by omega
    have hDrop : chunks.toList.drop idx = chunks[idx] :: chunks.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact hIdx)]
      simp only [Array.getElem_toList]
    rw [hDrop] at hSteps ⊢
    cases hSteps with
    | cons _ _ hWf hwEq hpEq hsEq hIdxEq hPowSpec hTail =>
      obtain ⟨hwSz, hpSz, hsSz, hsinSz, hinSz, hsoutSz, houtSz⟩ := hWf
      have hRootF : chunkRootMismatch stmt chunks[idx] = false := by
        unfold chunkRootMismatch
        rw [hwSz, hpSz, hsSz, hwEq, hpEq, hsEq]
        simp
      have hCarryF : chunkCarryMismatch idx chunks[idx].stateInCommit chunks[idx] = false := by
        unfold chunkCarryMismatch
        rw [hsinSz, hinSz, hsoutSz, houtSz, hIdxEq]
        simp
      have hPow : checkChunkPow stmt.requiredPowBits (zkmlChunkDigest chunks[idx]) = true :=
        (checkChunkPow_iff stmt.requiredPowBits chunks[idx]).mpr hPowSpec
      unfold verifyChunksLoop
      simp only [hIdx, ↓reduceDIte, hRootF, hCarryF, Bool.false_eq_true, ↓reduceIte,
        hPow, Bool.not_true]
      rw [verifyChunksLoop_complete stmt chunks rem (idx + 1) chunks[idx].stateOutCommit
        (acc.push (zkmlChunkDigest chunks[idx])) (by omega) hTail]
      simp [Array.toList_push, List.append_assoc]

/-- **`Spec ↔ Exec` Equivalence (`verifyZkmlChunkChainExec_iff_spec`)**. -/
theorem verifyZkmlChunkChainExec_iff_spec (stmt : ZkmlStreamStatement)
    (chunks : Array ZkmlChunkReceipt) (out : Array ByteArray) :
    verifyZkmlChunkChainExec stmt chunks = .ok out ↔
      ValidZkmlChunkChainSpec stmt chunks.toList ∧
      out.toList = chunks.toList.map zkmlChunkDigest := by
  constructor
  · intro hOk
    unfold verifyZkmlChunkChainExec at hOk
    cases hPow64 : decide (stmt.requiredPowBits ≤ 64)
    · rw [hPow64] at hOk; cases hOk
    simp only [hPow64, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hR : (decide (stmt.modelWeightsRoot.size ≠ 32) ||
        decide (stmt.policyFloorDigest.size ≠ 32) || decide (stmt.suiteDigest.size ≠ 32))
    · simp only [hR, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hS : (decide (stmt.initialStateCommit.size ≠ 32) ||
          decide (stmt.finalStateCommit.size ≠ 32) ||
          !decide (1 ≤ stmt.numChunks) || !decide (stmt.numChunks < 2 ^ 64) ||
          decide (chunks.size ≠ stmt.numChunks))
      · simp only [hS, Bool.false_eq_true, ↓reduceIte] at hOk
        obtain ⟨hSteps, hOut⟩ := verifyChunksLoop_sound stmt chunks chunks.size 0
          stmt.initialStateCommit #[] out (Nat.sub_zero _) hOk
        simp only [List.drop_zero] at hSteps hOut
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not,
          decide_eq_true_eq, Decidable.not_not] at hR hS
        obtain ⟨⟨hwSz, hpSz⟩, hsSz⟩ := hR
        obtain ⟨⟨⟨⟨hInSz, hFinSz⟩, hGe1⟩, hLt64⟩, hSzEq⟩ := hS
        have hWf : stmt.WellFormed32 :=
          ⟨hwSz, hpSz, hsSz, hInSz, hFinSz, hGe1, hLt64, of_decide_eq_true hPow64⟩
        exact ⟨⟨hWf, by simpa only [Array.length_toList] using hSzEq, hSteps⟩, hOut⟩
      · rw [hS] at hOk; cases hOk
    · rw [hR] at hOk; cases hOk
  · rintro ⟨⟨hWf, hLen, hSteps⟩, hOutEq⟩
    obtain ⟨hwSz, hpSz, hsSz, hInSz, hFinSz, hGe1, hLt64, hPow64⟩ := hWf
    have hSzEq : chunks.size = stmt.numChunks := by simpa only [Array.length_toList] using hLen
    unfold verifyZkmlChunkChainExec
    simp only [hwSz, hpSz, hsSz, hInSz, hFinSz, hSzEq, ne_eq, not_true_eq_false,
      decide_false, decide_eq_true hPow64, decide_eq_true hGe1, decide_eq_true hLt64,
      Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    have hLoop := verifyChunksLoop_complete stmt chunks stmt.numChunks 0
      stmt.initialStateCommit #[] (by simp [hSzEq]) (by simpa [List.drop_zero] using hSteps)
    simp only [List.drop_zero] at hLoop
    rw [hLoop]
    cases out
    simp only [Except.ok.injEq, Array.mk.injEq]
    exact hOutEq.symm

/-- **`tampered_weights_or_hidden_carry_refused`**:
    Any chunk chain that tampers with `modelWeightsRoot`, `policyFloorDigest`, or `suiteDigest` at
    any index, or splices/teleports hidden recurrent state (`stateOutCommit[i] ≠ stateInCommit[i+1]`
    or boundary mismatch), is unconditionally refused by `verifyZkmlChunkChainExec`. -/
theorem tampered_weights_or_hidden_carry_refused
    (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt)
    (hTamper :
      (∃ i : Fin chunks.size,
        chunks[i].modelWeightsRoot ≠ stmt.modelWeightsRoot ∨
        chunks[i].policyFloorDigest ≠ stmt.policyFloorDigest ∨
        chunks[i].suiteDigest ≠ stmt.suiteDigest) ∨
      (∃ i : Nat, ∃ hi1 : i + 1 < chunks.size,
        (chunks[i]'(Nat.lt_of_succ_lt hi1)).stateOutCommit ≠ (chunks[i + 1]'hi1).stateInCommit) ∨
      (∃ h0 : 0 < chunks.size, (chunks[0]'h0).stateInCommit ≠ stmt.initialStateCommit) ∨
      (∃ hpos : 0 < chunks.size,
        (chunks[chunks.size - 1]'(Nat.sub_lt hpos (by decide))).stateOutCommit ≠ stmt.finalStateCommit)) :
    ¬ ValidZkmlChunkChainSpec stmt chunks.toList ∧
    ∀ out, verifyZkmlChunkChainExec stmt chunks ≠ .ok out := by
  have hNoSpec : ¬ ValidZkmlChunkChainSpec stmt chunks.toList := by
    intro hSpec
    obtain ⟨_, hElem, hAdj, hEnds⟩ := validZkmlChunkChain_invariants hSpec
    rcases hTamper with ⟨i, hDrift⟩ | ⟨i, hi1, hBreak⟩ | ⟨h0, hInit⟩ | ⟨hpos, hFin⟩
    · have hiL : i.val < chunks.toList.length := by simpa only [Array.length_toList] using i.isLt
      obtain ⟨hw, hp, hs, _, _⟩ := hElem i.val hiL
      simp only [Array.getElem_toList, Fin.getElem_fin] at hw hp hs hDrift
      rcases hDrift with h1 | h2 | h3
      · exact h1 hw
      · exact h2 hp
      · exact h3 hs
    · have hi1L : i + 1 < chunks.toList.length := by simpa only [Array.length_toList] using hi1
      have hEq := hAdj i hi1L
      simp only [Array.getElem_toList] at hEq
      exact hBreak hEq
    · cases chunks with
      | mk cs =>
        cases cs with
        | nil => simp at h0
        | cons c₀ rest =>
          have hHead := (hEnds (List.cons_ne_nil c₀ rest)).1
          exact hInit hHead
    · have hne : chunks.toList ≠ [] := by
        intro hemp
        have : chunks.toList.length = 0 := by simp [hemp]
        simp only [Array.length_toList] at this
        omega
      have hLast := (hEnds hne).2
      have hLastEq : chunks.toList.getLast hne =
          chunks[chunks.size - 1]'(Nat.sub_lt hpos (by decide)) := by
        rw [List.getLast_eq_getElem]
        simp only [Array.length_toList, Array.getElem_toList]
      exact hFin (hLastEq ▸ hLast)
  refine ⟨hNoSpec, fun out hOk => hNoSpec ((verifyZkmlChunkChainExec_iff_spec stmt chunks out).mp hOk).1⟩

/-- SHE turn query evaluated by `provenZkmlJudge`. -/
structure ZkmlTurnQuery where
  claimedRegime : ZkmlSecurityRegime
  suite : ZkmlSuiteProfile
  statement : ZkmlStreamStatement
  chunks : List ZkmlChunkReceipt
  deriving DecidableEq, Inhabited

/-- Independent commitment-chain certificate checked against `ZkmlTurnQuery`. -/
structure ZkmlTurnCert where
  chunkDigests : List ByteArray
  deriving DecidableEq, Inhabited

/-- Declarative semantic `Meaning` established when `provenZkmlJudge` accepts `(q, c)`. -/
@[expose] def ZkmlTurnMeaning (q : ZkmlTurnQuery) (c : ZkmlTurnCert) : Prop :=
  ZkmlSuiteMeetsProvenFloor q.claimedRegime q.suite ∧
  q.suite.grindBits ≤ q.statement.requiredPowBits ∧
  ValidZkmlChunkChainSpec q.statement q.chunks ∧
  c.chunkDigests = q.chunks.map zkmlChunkDigest

/-- Declarative input-domain `Fragment` over which `provenZkmlJudge` is complete. -/
@[expose] def ZkmlDecidableFragment (q : ZkmlTurnQuery) : Prop :=
  q.statement.WellFormed32 ∧ q.chunks ≠ []

/-- Fuel-graded deterministic checker for `provenZkmlJudge`. -/
def checkZkmlTurn (grade : Nat) (q : ZkmlTurnQuery) (c : ZkmlTurnCert) :
    Obend.Judge.Verdict ZkmlRefusalClause :=
  if decide (grade < q.chunks.length) then
    .uncovered
  else if decide (q.claimedRegime = .withdrawnCbr) then
    .refused .withdrawnCbrRejected []
  else if !checkZkmlSuiteProvenFloor q.claimedRegime q.suite then
    .refused .belowProven100BitFloor []
  else if !decide (q.suite.grindBits ≤ q.statement.requiredPowBits) then
    .refused .insufficientPowGrind []
  else
    match verifyZkmlChunkChainExec q.statement ⟨q.chunks⟩ with
    | .error (k, path) => .refused k path
    | .ok digests =>
      if decide (c.chunkDigests = digests.toList) then .ok
      else .refused .certDigestMismatch []

theorem provenZkmlJudge_sound {grade : Nat} {q : ZkmlTurnQuery} {c : ZkmlTurnCert}
    (h : checkZkmlTurn grade q c = .ok) : ZkmlTurnMeaning q c := by
  unfold checkZkmlTurn at h
  cases hG : decide (grade < q.chunks.length)
  · simp only [hG, Bool.false_eq_true, ↓reduceIte] at h
    cases hCbr : decide (q.claimedRegime = .withdrawnCbr)
    · simp only [hCbr, Bool.false_eq_true, ↓reduceIte] at h
      cases hFl : checkZkmlSuiteProvenFloor q.claimedRegime q.suite
      · simp [hFl] at h
      · simp only [hFl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hGr : decide (q.suite.grindBits ≤ q.statement.requiredPowBits)
        · simp [hGr] at h
        · simp only [hGr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hChain : verifyZkmlChunkChainExec q.statement ⟨q.chunks⟩ with
          | error kp => simp [hChain] at h
          | ok digests =>
            simp only [hChain] at h
            cases hDig : decide (c.chunkDigests = digests.toList)
            · simp [hDig] at h
            · obtain ⟨hValid, hDigList⟩ :=
                (verifyZkmlChunkChainExec_iff_spec q.statement ⟨q.chunks⟩ digests).mp hChain
              exact ⟨(checkZkmlSuiteProvenFloor_iff q.claimedRegime q.suite).mp hFl,
                of_decide_eq_true hGr, hValid, (of_decide_eq_true hDig).trans hDigList⟩
    · simp [hCbr] at h
  · simp [hG] at h

theorem provenZkmlJudge_refuted {grade : Nat} {q : ZkmlTurnQuery} {c : ZkmlTurnCert}
    {k : ZkmlRefusalClause} {path : List Nat}
    (hRef : checkZkmlTurn grade q c = .refused k path)
    (hMarks : provenZkmlRefutes k = true) :
    ∀ c' : ZkmlTurnCert, ¬ ZkmlTurnMeaning q c' := by
  intro c' hMean
  obtain ⟨hSuite, hGrind, hChain, _⟩ := hMean
  unfold checkZkmlTurn at hRef
  cases hG : decide (grade < q.chunks.length)
  · simp only [hG, Bool.false_eq_true, ↓reduceIte] at hRef
    cases hCbr : decide (q.claimedRegime = .withdrawnCbr)
    · simp only [hCbr, Bool.false_eq_true, ↓reduceIte] at hRef
      have hFlTrue : checkZkmlSuiteProvenFloor q.claimedRegime q.suite = true :=
        (checkZkmlSuiteProvenFloor_iff q.claimedRegime q.suite).mpr hSuite
      have hGrTrue : decide (q.suite.grindBits ≤ q.statement.requiredPowBits) = true :=
        decide_eq_true hGrind
      simp only [hFlTrue, hGrTrue, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
      have hExecOk : verifyZkmlChunkChainExec q.statement ⟨q.chunks⟩ =
          .ok ⟨q.chunks.map zkmlChunkDigest⟩ :=
        (verifyZkmlChunkChainExec_iff_spec q.statement ⟨q.chunks⟩
          ⟨q.chunks.map zkmlChunkDigest⟩).mpr ⟨hChain, rfl⟩
      rw [hExecOk] at hRef
      simp only at hRef
      cases hDig : decide (c.chunkDigests = q.chunks.map zkmlChunkDigest)
      · simp only [hDig, Bool.false_eq_true, ↓reduceIte, Obend.Judge.Verdict.refused.injEq] at hRef
        rcases hRef with ⟨rfl, _⟩
        simp [provenZkmlRefutes] at hMarks
      · simp [hDig] at hRef
    · have hEqCbr : q.claimedRegime = .withdrawnCbr := of_decide_eq_true hCbr
      have hRep := hSuite.1
      rw [hEqCbr] at hRep
      exact withdrawnCbr_not_reportable hRep
  · simp [hG] at hRef

theorem provenZkmlJudge_complete {q : ZkmlTurnQuery}
    (hFrag : ZkmlDecidableFragment q) (hEx : ∃ c, ZkmlTurnMeaning q c) :
    ∃ c r, checkZkmlTurn r q c = .ok := by
  obtain ⟨_, hSuite, hGrind, hChain, _⟩ := hEx
  have _hPos : 0 < q.chunks.length := List.length_pos_iff.mpr hFrag.2
  refine ⟨⟨q.chunks.map zkmlChunkDigest⟩, q.chunks.length, ?_⟩
  unfold checkZkmlTurn
  have hNotCbr : q.claimedRegime ≠ .withdrawnCbr := by
    intro hEq
    have hRep := hSuite.1
    rw [hEq] at hRep
    exact withdrawnCbr_not_reportable hRep
  have hFlTrue : checkZkmlSuiteProvenFloor q.claimedRegime q.suite = true :=
    (checkZkmlSuiteProvenFloor_iff q.claimedRegime q.suite).mpr hSuite
  have hExecOk : verifyZkmlChunkChainExec q.statement ⟨q.chunks⟩ =
      .ok ⟨q.chunks.map zkmlChunkDigest⟩ :=
    (verifyZkmlChunkChainExec_iff_spec q.statement ⟨q.chunks⟩
      ⟨q.chunks.map zkmlChunkDigest⟩).mpr ⟨hChain, rfl⟩
  simp [Nat.lt_irrefl, hNotCbr, hFlTrue, decide_eq_true hGrind, hExecOk]

theorem provenZkmlJudge_mono {r r' : Nat} {q : ZkmlTurnQuery} {c : ZkmlTurnCert}
    (hle : r ≤ r') (hDec : checkZkmlTurn r q c ≠ .uncovered) :
    checkZkmlTurn r' q c = checkZkmlTurn r q c := by
  unfold checkZkmlTurn at hDec ⊢
  if hLt : r < q.chunks.length then
    simp [hLt] at hDec
  else
    have hNotLt' : ¬ (r' < q.chunks.length) := by omega
    simp only [decide_eq_false hLt, decide_eq_false hNotLt']

/-- **Lawful `provenZkmlJudge` Instance (`Judge ZkmlTurnQuery ZkmlTurnCert`)**. -/
instance provenZkmlJudge : Obend.Judge ZkmlTurnQuery ZkmlTurnCert where
  Clause := ZkmlRefusalClause
  Meaning := ZkmlTurnMeaning
  check := checkZkmlTurn
  sound := provenZkmlJudge_sound
  refutes := provenZkmlRefutes
  refuted := provenZkmlJudge_refuted
  Fragment := ZkmlDecidableFragment
  complete := provenZkmlJudge_complete
  mono := provenZkmlJudge_mono

/-! ### Multi-Turn SHE Streaming Inference Session Invariant -/

/-- Persistent SHE edge-inference session state across arbitrarily many user turns. -/
structure ZkmlSessionState where
  sessionWeightsRoot : ByteArray
  sessionPolicyFloorDigest : ByteArray
  sessionSuiteDigest : ByteArray
  sessionStateCommit : ByteArray
  totalVerifiedChunks : Nat
  deriving DecidableEq, Inhabited

/-- Inductive multi-turn session trace validity across `List (ZkmlTurnQuery × ZkmlTurnCert)`. -/
inductive ValidZkmlSessionTrace :
    ZkmlSessionState → List (ZkmlTurnQuery × ZkmlTurnCert) → ZkmlSessionState → Prop where
  | nil (st : ZkmlSessionState) : ValidZkmlSessionTrace st [] st
  | cons {st finalSt : ZkmlSessionState} (q : ZkmlTurnQuery) (c : ZkmlTurnCert)
      (rest : List (ZkmlTurnQuery × ZkmlTurnCert)) :
      q.statement.modelWeightsRoot = st.sessionWeightsRoot →
      q.statement.policyFloorDigest = st.sessionPolicyFloorDigest →
      q.statement.suiteDigest = st.sessionSuiteDigest →
      q.statement.initialStateCommit = st.sessionStateCommit →
      ZkmlTurnMeaning q c →
      ValidZkmlSessionTrace
        { st with
          sessionStateCommit := q.statement.finalStateCommit
          totalVerifiedChunks := st.totalVerifiedChunks + q.chunks.length }
        rest finalSt →
      ValidZkmlSessionTrace st ((q, c) :: rest) finalSt

/-- Single-turn SHE session step verifier. -/
def verifyZkmlSessionStep (grade : Nat) (st : ZkmlSessionState)
    (qc : ZkmlTurnQuery × ZkmlTurnCert) :
    Except (ZkmlRefusalClause × List Nat) ZkmlSessionState :=
  let (q, c) := qc
  if decide (q.statement.modelWeightsRoot ≠ st.sessionWeightsRoot) ||
      decide (q.statement.policyFloorDigest ≠ st.sessionPolicyFloorDigest) ||
      decide (q.statement.suiteDigest ≠ st.sessionSuiteDigest) then
    .error (.weightRootDrift, [])
  else if decide (q.statement.initialStateCommit ≠ st.sessionStateCommit) then
    .error (.brokenRecurrentCarry, [])
  else
    match checkZkmlTurn grade q c with
    | .ok =>
      .ok { st with
        sessionStateCommit := q.statement.finalStateCommit
        totalVerifiedChunks := st.totalVerifiedChunks + q.chunks.length }
    | .refused k path => .error (k, path)
    | .uncovered => .error (.certDigestMismatch, [])

/-- Multi-turn SHE session trace verifier across an unbounded turn list. -/
def verifyZkmlSessionTrace (grade : Nat) (st : ZkmlSessionState) :
    List (ZkmlTurnQuery × ZkmlTurnCert) → Except (ZkmlRefusalClause × List Nat) ZkmlSessionState
  | [] => .ok st
  | qc :: rest =>
    match verifyZkmlSessionStep grade st qc with
    | .error err => .error err
    | .ok st' => verifyZkmlSessionTrace grade st' rest

/-- **Multi-Turn SHE Session Trace Soundness (`verifyZkmlSessionTrace_sound`)**. -/
theorem verifyZkmlSessionTrace_sound {grade : Nat} {init finalSt : ZkmlSessionState}
    {trace : List (ZkmlTurnQuery × ZkmlTurnCert)}
    (h : verifyZkmlSessionTrace grade init trace = .ok finalSt) :
    ValidZkmlSessionTrace init trace finalSt ∧
    finalSt.sessionWeightsRoot = init.sessionWeightsRoot ∧
    finalSt.sessionPolicyFloorDigest = init.sessionPolicyFloorDigest ∧
    finalSt.sessionSuiteDigest = init.sessionSuiteDigest ∧
    init.totalVerifiedChunks ≤ finalSt.totalVerifiedChunks := by
  induction trace generalizing init with
  | nil =>
    simp only [verifyZkmlSessionTrace, Except.ok.injEq] at h
    subst h
    exact ⟨.nil init, rfl, rfl, rfl, Nat.le_refl _⟩
  | cons qc rest ih =>
    obtain ⟨q, c⟩ := qc
    simp only [verifyZkmlSessionTrace, verifyZkmlSessionStep] at h
    cases hDr : (decide (q.statement.modelWeightsRoot ≠ init.sessionWeightsRoot) ||
        decide (q.statement.policyFloorDigest ≠ init.sessionPolicyFloorDigest) ||
        decide (q.statement.suiteDigest ≠ init.sessionSuiteDigest))
    · simp only [hDr, Bool.false_eq_true, ↓reduceIte] at h
      cases hIn : decide (q.statement.initialStateCommit ≠ init.sessionStateCommit)
      · simp only [hIn, Bool.false_eq_true, ↓reduceIte] at h
        cases hChk : checkZkmlTurn grade q c with
        | refused k path => rw [hChk] at h; cases h
        | uncovered => rw [hChk] at h; cases h
        | ok =>
          simp only [hChk] at h
          obtain ⟨hRest, hwEq, hpEq, hsEq, hMono⟩ := ih h
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not] at hDr hIn
          obtain ⟨⟨hw, hp⟩, hs⟩ := hDr
          exact ⟨.cons q c rest hw hp hs hIn (provenZkmlJudge_sound hChk) hRest,
            hwEq, hpEq, hsEq, Nat.le_trans (Nat.le_add_right _ _) hMono⟩
      · rw [hIn] at h; simp at h
    · rw [hDr] at h; simp at h

/-! ## 4. Constructive Inhabitedness Witnesses (`0` Vacuous Premises) -/

private def sampleBytes32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩

private theorem sampleBytes32_size (b : UInt8) : (sampleBytes32 b).size = 32 := by
  simp [sampleBytes32, ByteArray.size]

private def sampleChunk0 : ZkmlChunkReceipt :=
  ⟨sampleBytes32 0x11, sampleBytes32 0x22, sampleBytes32 0x33, 0,
   sampleBytes32 0x40, sampleBytes32 0x50, sampleBytes32 0x41, sampleBytes32 0x60, 331⟩

private def sampleChunk1 : ZkmlChunkReceipt :=
  ⟨sampleBytes32 0x11, sampleBytes32 0x22, sampleBytes32 0x33, 1,
   sampleBytes32 0x41, sampleBytes32 0x51, sampleBytes32 0x42, sampleBytes32 0x61, 348⟩

private def sampleStreamStmt : ZkmlStreamStatement :=
  ⟨sampleBytes32 0x11, sampleBytes32 0x22, sampleBytes32 0x33,
   sampleBytes32 0x40, sampleBytes32 0x42, 2, 0⟩

private theorem sampleStreamStmt_valid :
    ValidZkmlChunkChainSpec sampleStreamStmt [sampleChunk0, sampleChunk1] :=
  ⟨⟨sampleBytes32_size _, sampleBytes32_size _, sampleBytes32_size _,
    sampleBytes32_size _, sampleBytes32_size _, by decide, by decide, by decide⟩, rfl,
   .cons sampleChunk0 [sampleChunk1]
     ⟨sampleBytes32_size _, sampleBytes32_size _, sampleBytes32_size _,
      sampleBytes32_size _, sampleBytes32_size _, sampleBytes32_size _, sampleBytes32_size _⟩
     rfl rfl rfl rfl (chunkMeetsPow_zero sampleChunk0)
     (.cons sampleChunk1 []
       ⟨sampleBytes32_size _, sampleBytes32_size _, sampleBytes32_size _,
        sampleBytes32_size _, sampleBytes32_size _, sampleBytes32_size _, sampleBytes32_size _⟩
       rfl rfl rfl rfl (chunkMeetsPow_zero sampleChunk1) (.nil 2 (sampleBytes32 0x42)))⟩

theorem validZkmlChunkChain_inhabited :
    ∃ stmt chain out,
      ValidZkmlChunkChainSpec stmt chain ∧
      verifyZkmlChunkChainExec stmt ⟨chain⟩ = .ok out :=
  ⟨sampleStreamStmt, [sampleChunk0, sampleChunk1],
   #[zkmlChunkDigest sampleChunk0, zkmlChunkDigest sampleChunk1], sampleStreamStmt_valid,
   (verifyZkmlChunkChainExec_iff_spec sampleStreamStmt
     #[sampleChunk0, sampleChunk1]
     #[zkmlChunkDigest sampleChunk0, zkmlChunkDigest sampleChunk1]).mpr
     ⟨sampleStreamStmt_valid, rfl⟩⟩

theorem provenZkmlJudge_inhabited :
    ∃ q c,
      ZkmlDecidableFragment q ∧
      ZkmlTurnMeaning q c ∧
      provenZkmlJudge.check 2 q c = .ok := by
  let suite0 : ZkmlSuiteProfile := { deployedIr2BabyBearExt4 with numQueries := 103, grindBits := 0 }
  let q : ZkmlTurnQuery := ⟨.provenUdr, suite0, sampleStreamStmt, [sampleChunk0, sampleChunk1]⟩
  let c : ZkmlTurnCert := ⟨[zkmlChunkDigest sampleChunk0, zkmlChunkDigest sampleChunk1]⟩
  have hFl : checkZkmlSuiteProvenFloor .provenUdr suite0 = true := by decide
  have hSuite : ZkmlSuiteMeetsProvenFloor .provenUdr suite0 :=
    (checkZkmlSuiteProvenFloor_iff .provenUdr suite0).mp hFl
  have hMean : ZkmlTurnMeaning q c := ⟨hSuite, by decide, sampleStreamStmt_valid, rfl⟩
  have hFrag : ZkmlDecidableFragment q := ⟨sampleStreamStmt_valid.1, List.cons_ne_nil _ _⟩
  have hExec : verifyZkmlChunkChainExec q.statement ⟨q.chunks⟩ = .ok ⟨c.chunkDigests⟩ :=
    (verifyZkmlChunkChainExec_iff_spec q.statement ⟨q.chunks⟩ ⟨c.chunkDigests⟩).mpr
      ⟨sampleStreamStmt_valid, rfl⟩
  have hOk2 : checkZkmlTurn 2 q c = .ok := by
    unfold checkZkmlTurn
    rw [hExec]
    simp [q, suite0, sampleStreamStmt, hFl]
  exact ⟨q, c, hFrag, hMean, hOk2⟩

theorem validZkmlSessionTrace_inhabited :
    ∃ init trace finalSt,
      trace ≠ [] ∧
      verifyZkmlSessionTrace 2 init trace = .ok finalSt ∧
      ValidZkmlSessionTrace init trace finalSt := by
  obtain ⟨q, c, _, _, hOk⟩ := provenZkmlJudge_inhabited
  let init : ZkmlSessionState :=
    ⟨q.statement.modelWeightsRoot, q.statement.policyFloorDigest,
     q.statement.suiteDigest, q.statement.initialStateCommit, 0⟩
  have hChk : checkZkmlTurn 2 q c = .ok := hOk
  have hStep : verifyZkmlSessionTrace 2 init [(q, c)] =
      .ok { init with
        sessionStateCommit := q.statement.finalStateCommit
        totalVerifiedChunks := q.chunks.length } := by
    simp [verifyZkmlSessionTrace, verifyZkmlSessionStep, init, hChk]
  exact ⟨init, [(q, c)], _, List.cons_ne_nil _ _, hStep, (verifyZkmlSessionTrace_sound hStep).1⟩

end Obend.SymbolicZk.ProvenZkmlGate
end
