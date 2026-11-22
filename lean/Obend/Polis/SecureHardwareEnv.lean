module
/- # Obend.Polis.SecureHardwareEnv — Multi-Turn Sovereign SHE ("Anti-Vaz") Ceremony
Closes *Rainbows End* SHE Gap #5: `vaz_coercive_floor_downgrade_refused`, 8-gate multi-turn
`she_trace_end_to_end_safe_and_anti_vaz`, `sheTurnEnvelope_binds`, `seL4` coupling & `sheCeremonyJudge`. -/
public import Obend.Judge.Class
public import Obend.Judge.Genealogy
public import Obend.OS.Sel4MicrokitKernel
public import Obend.Polis.SandboxDomainTags

public section
namespace Obend.Polis.SecureHardwareEnv

open Obend.Crypto Obend.Digest.Cshake256 Obend.Digest.HashBytes
open Obend.OS.Sel4MicrokitKernel Obend.Polis.SandboxDomainTags
set_option autoImplicit false

/-! ## 1. Sovereign Safety & Privacy Floors and Unconditional zkML Soundness Accounting -/
inductive SheFloor where
  | sensorRoiRedaction (minRedactedRois : Nat)
  | consentBandNonOcclusion (minBandHeightPx : Nat)
  | zkmlProvenSoundnessMilliBits (minMilliBits : Nat)
  | physicalProximityMaxTicks (maxTicks : Nat)
  | e2eeTeeChannelBound (minAttestedGpus : Nat)
  | operatorLocalRevert (maxRevertSteps : Nat)
  deriving DecidableEq, Repr

def SheFloor.isBedrock : SheFloor → Bool | .operatorLocalRevert _ => true | _ => false
def SheFloor.wellFormed : SheFloor → Bool
  | .sensorRoiRedaction _ | .e2eeTeeChannelBound _ => true
  | .consentBandNonOcclusion px => decide (0 < px)
  | .zkmlProvenSoundnessMilliBits mb => decide (100000 ≤ mb)
  | .physicalProximityMaxTicks t => decide (0 < t)
  | .operatorLocalRevert r => decide (0 < r)

inductive ZkmlSoundnessRegime where
  | uniqueDecodingUdr
  | johnsonBoundJbr
  | withdrawnCapacityBoundCbr
  deriving DecidableEq, Repr

def udrPerQueryMilliBits : Nat → Nat
  | 0 => 0 | 1 => 415 | 2 => 678 | 3 => 830 | 4 => 912
  | 5 => 955 | 6 => 977 | 7 => 988 | _ + 8 => 994
def jbrPerQueryMilliBits (logBlowup : Nat) : Nat := logBlowup * 500

structure CandidateComputation where
  statementDigest : ByteArray
  modelWeightsRoot : ByteArray
  boundFloorsDigest : ByteArray
  sensorSealDigest : ByteArray
  actionPayloadDigest : ByteArray
  regime : ZkmlSoundnessRegime
  logBlowup : Nat
  numQueries : Nat
  grindBits : Nat
  extFieldBits : Nat
  proofVerified : Bool
  deriving DecidableEq

/-- Realized proven soundness in milli-bits (`100,000` = `100` bits); withdrawn `CBR` scores `0`,
    and PoW grinding credit is capped at `24` bits so query soundness carries `≥ 76` bits. -/
@[expose] def provenZkmlMilliBits (c : CandidateComputation) : Nat :=
  if !c.proofVerified || c.logBlowup == 0 || c.numQueries == 0 then 0 else
    let cap := Nat.min (c.extFieldBits * 1000) 256000
    let grindMbit := Nat.min c.grindBits 24 * 1000
    match c.regime with
    | .withdrawnCapacityBoundCbr => 0
    | .uniqueDecodingUdr => Nat.min (c.numQueries * udrPerQueryMilliBits c.logBlowup + grindMbit) cap
    | .johnsonBoundJbr => Nat.min (c.numQueries * jbrPerQueryMilliBits c.logBlowup + grindMbit) cap

def legacyWithdrawnCbrMilliBits (c : CandidateComputation) : Nat :=
  c.logBlowup * c.numQueries * 1000 + c.grindBits * 1000

theorem udr_strictly_below_legacy_cbr (c : CandidateComputation)
    (hlb : 0 < c.logBlowup) (hq : 0 < c.numQueries) :
    provenZkmlMilliBits { c with regime := .uniqueDecodingUdr } < legacyWithdrawnCbrMilliBits c := by
  have hPerQ : udrPerQueryMilliBits c.logBlowup < c.logBlowup * 1000 := by
    match c.logBlowup, hlb with
    | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [udrPerQueryMilliBits]
    | k + 8, _ => simp [udrPerQueryMilliBits]; omega
  have hMul := Nat.mul_lt_mul_of_pos_left hPerQ hq
  rw [← Nat.mul_assoc, Nat.mul_comm c.numQueries c.logBlowup] at hMul
  have hGrind := Nat.mul_le_mul_right 1000 (Nat.min_le_left c.grindBits 24)
  have hSum := Nat.add_lt_add_of_lt_of_le hMul hGrind
  have hPos : 0 < c.logBlowup * c.numQueries * 1000 + c.grindBits * 1000 :=
    Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos hlb hq) (by decide)) (Nat.le_add_right _ _)
  unfold provenZkmlMilliBits legacyWithdrawnCbrMilliBits; dsimp only; split
  · exact hPos
  · exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hSum

/-! ## 2. Sovereign SHE Turn Vocabulary, Persistent State & `OBEND.SHE.TURN/v1` Wire Framing -/
inductive UpgradeAuthorityClaim where
  | localCustodianCeremony
  | vendorRootDirective (vendorSig : ByteArray)
  | agencyEmergencyOrder (agencyId : ByteArray) (agencySig : ByteArray)
  deriving DecidableEq

structure ActuationTurnProposal where
  sensorSeq : Nat
  sensorSealDigest : ByteArray
  candidate : CandidateComputation
  nullifier : ByteArray
  mandateCost : Nat
  redactedRoiCount : Nat
  consentBandHeightPx : Nat
  attestedGpuCount : Nat
  sharedRingAtCopy : ByteArray
  privateFrameCopy : ByteArray
  dispatchedPayload : ByteArray
  simplexCommitteeN : Nat
  simplexFaultyF : Nat
  simplexFinalizeSigners : List Nat
  custodianEpoch : Nat
  custodianSigners : List Nat
  tofRoundTripTicks : Nat
  deriving DecidableEq

structure UpgradeJudgeProposal where
  newJudgeDigest : ByteArray
  newModelWeightsRoot : ByteArray
  newFloors : List SheFloor
  newRevertWindowSteps : Nat
  newCustodianEpoch : Nat
  custodianSigners : List Nat
  tofRoundTripTicks : Nat
  authorityClaim : UpgradeAuthorityClaim
  deriving DecidableEq

structure MandateAttenuation where
  newBudgetCap : Nat
  newMaxProximityTicks : Nat
  newlyRevokedCustodians : List Nat
  reasonDigest : ByteArray
  deriving DecidableEq

inductive SheTurn where
  | proposeAndSettleActuation (proposal : ActuationTurnProposal)
  | upgradeHabitatJudge (upgrade : UpgradeJudgeProposal)
  | revokeOrAttenuateMandate (attenuation : MandateAttenuation)
  deriving DecidableEq

structure SettledActuationRecord where
  sensorSeq : Nat
  sensorSealDigest : ByteArray
  nullifier : ByteArray
  mandateCost : Nat
  redactedRoiCount : Nat
  consentBandHeightPx : Nat
  attestedGpuCount : Nat
  provenZkmlMilliBits : Nat
  zkmlRegime : ZkmlSoundnessRegime
  modelWeightsRoot : ByteArray
  activeFloorsAtSettlement : List SheFloor
  boundFloorsDigest : ByteArray
  revertWindowAtSettlement : Nat
  sharedRingAtCopy : ByteArray
  privateFrameCopy : ByteArray
  dispatchedPayload : ByteArray
  simplexCommitteeN : Nat
  simplexFaultyF : Nat
  simplexQuorumCount : Nat
  custodianEpoch : Nat
  custodianSigners : List Nat
  tofRoundTripTicks : Nat
  maxProximityTicksAtSettle : Nat
  turnEnvelopeDigest : ByteArray
  deriving DecidableEq

structure SheState where
  habitatJudgeDigest : ByteArray
  pinnedModelWeightsRoot : ByteArray
  monoSensorSeq : Nat
  consumedNullifiers : List ByteArray
  remainingMandateBudget : Nat
  activeSafetyAndPrivacyFloors : List SheFloor
  settledOutboxActions : List SettledActuationRecord
  custodianThresholdT : Nat
  custodianTotalN : Nat
  custodianQuorumEpoch : Nat
  revokedCustodians : List Nat
  maxProximityTicks : Nat
  revertWindowSteps : Nat
  deriving DecidableEq

@[expose] def settledTotalCost : List SettledActuationRecord → Nat
  | [] => 0 | r :: rs => r.mandateCost + settledTotalCost rs
@[simp] theorem settledTotalCost_append (xs ys : List SettledActuationRecord) :
    settledTotalCost (xs ++ ys) = settledTotalCost xs + settledTotalCost ys := by
  induction xs with | nil => simp [settledTotalCost] | cons _ _ ih => simp [settledTotalCost, ih, Nat.add_assoc]
abbrev encodeSheFields : List (List UInt8) → List UInt8 := encodeSandboxFields
theorem encodeSheFields_injective {fs₁ fs₂ : List (List UInt8)}
    (h : encodeSheFields fs₁ = encodeSheFields fs₂) : fs₁ = fs₂ := encodeSandboxFields_injective h
def SheFloor.encode : SheFloor → List UInt8
  | .sensorRoiRedaction k => 0x01 :: leb128 k | .consentBandNonOcclusion px => 0x02 :: leb128 px
  | .zkmlProvenSoundnessMilliBits mb => 0x03 :: leb128 mb | .physicalProximityMaxTicks t => 0x04 :: leb128 t
  | .e2eeTeeChannelBound g => 0x05 :: leb128 g | .operatorLocalRevert r => 0x06 :: leb128 r
theorem SheFloor.encode_injective {φ₁ φ₂ : SheFloor} (h : φ₁.encode = φ₂.encode) : φ₁ = φ₂ := by
  cases φ₁ <;> cases φ₂ <;> simp only [SheFloor.encode, List.cons.injEq] at h
  all_goals first | exact absurd h.1 (by decide) | exact congrArg _ (leb128_injective h.2)
def encodeFloors (floors : List SheFloor) : List UInt8 := encodeSheFields (floors.map SheFloor.encode)
theorem encodeFloors_injective {fs₁ fs₂ : List SheFloor} (h : encodeFloors fs₁ = encodeFloors fs₂) :
    fs₁ = fs₂ := (List.map_inj_right (fun _ _ => SheFloor.encode_injective)).mp (encodeSheFields_injective h)
def floorsDigest (floors : List SheFloor) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.FLOORS/v1") (encodeFloors floors)
theorem floorsDigest_size (floors : List SheFloor) : (floorsDigest floors).size = 32 := cshake32ByteArray_size _ _
theorem floorsDigest_binds {fs₁ fs₂ : List SheFloor} (h : floorsDigest fs₁ = floorsDigest fs₂) :
    fs₁ = fs₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.FLOORS/v1"))
      (fun x => x = encodeFloors fs₁ ∨ x = encodeFloors fs₂) := by
  cases extractCshake32 (asciiTagBytes "OBEND.SHE.FLOORS/v1") (encodeFloors fs₁) (encodeFloors fs₂) h with
  | inl hp => exact .inl (encodeFloors_injective hp.down) | inr hc => exact .inr hc.down
def shePayloadDigest (payload : ByteArray) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.PAYLOAD/v1") (encodeSheFields [payload.data.toList])
theorem shePayloadDigest_size (payload : ByteArray) : (shePayloadDigest payload).size = 32 := cshake32ByteArray_size _ _
theorem shePayloadDigest_binds {p₁ p₂ : ByteArray} (h : shePayloadDigest p₁ = shePayloadDigest p₂) :
    p₁ = p₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.PAYLOAD/v1"))
      (fun x => x = encodeSheFields [p₁.data.toList] ∨ x = encodeSheFields [p₂.data.toList]) := by
  cases extractCshake32 (asciiTagBytes "OBEND.SHE.PAYLOAD/v1")
      (encodeSheFields [p₁.data.toList]) (encodeSheFields [p₂.data.toList]) h with
  | inr hc => exact .inr hc.down
  | inl hp =>
    have hf := encodeSheFields_injective hp.down; simp only [List.cons.injEq, and_true] at hf
    exact .inl (byteArray_eq_of_toList_eq hf)
def ZkmlSoundnessRegime.tagByte : ZkmlSoundnessRegime → UInt8
  | .uniqueDecodingUdr => 0x01 | .johnsonBoundJbr => 0x02 | .withdrawnCapacityBoundCbr => 0x03
theorem ZkmlSoundnessRegime.tagByte_injective {r₁ r₂ : ZkmlSoundnessRegime}
    (h : r₁.tagByte = r₂.tagByte) : r₁ = r₂ := by cases r₁ <;> cases r₂ <;> first | rfl | cases h
private theorem bool_flag_injective {b₁ b₂ : Bool}
    (h : (if b₁ then (1 : UInt8) else 0) = (if b₂ then (1 : UInt8) else 0)) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> first | rfl | cases h
def encodeCandidateComputation (c : CandidateComputation) : List UInt8 :=
  encodeSheFields [c.statementDigest.data.toList, c.modelWeightsRoot.data.toList,
    c.boundFloorsDigest.data.toList, c.sensorSealDigest.data.toList, c.actionPayloadDigest.data.toList,
    [c.regime.tagByte], leb128 c.logBlowup, leb128 c.numQueries, leb128 c.grindBits,
    leb128 c.extFieldBits, [if c.proofVerified then (1 : UInt8) else 0]]
theorem encodeCandidateComputation_injective {c₁ c₂ : CandidateComputation}
    (h : encodeCandidateComputation c₁ = encodeCandidateComputation c₂) : c₁ = c₂ := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf
  obtain ⟨hStmt, hW, hFl, hSen, hPay, hReg, hLb, hQ, hG, hExt, hVer⟩ := hf
  cases c₁; cases c₂; simp only [CandidateComputation.mk.injEq]
  exact ⟨byteArray_eq_of_toList_eq hStmt, byteArray_eq_of_toList_eq hW, byteArray_eq_of_toList_eq hFl,
    byteArray_eq_of_toList_eq hSen, byteArray_eq_of_toList_eq hPay,
    ZkmlSoundnessRegime.tagByte_injective hReg, leb128_injective hLb, leb128_injective hQ,
    leb128_injective hG, leb128_injective hExt, bool_flag_injective hVer⟩
def encodeNatList (xs : List Nat) : List UInt8 := encodeSheFields (xs.map leb128)
theorem encodeNatList_injective {xs₁ xs₂ : List Nat} (h : encodeNatList xs₁ = encodeNatList xs₂) :
    xs₁ = xs₂ := (List.map_inj_right (fun _ _ => leb128_injective)).mp (encodeSheFields_injective h)
def encodeAuthorityClaim : UpgradeAuthorityClaim → List UInt8
  | .localCustodianCeremony => encodeSheFields [[0x01]]
  | .vendorRootDirective sig => encodeSheFields [[0x02], sig.data.toList]
  | .agencyEmergencyOrder id sig => encodeSheFields [[0x03], id.data.toList, sig.data.toList]
theorem encodeAuthorityClaim_injective {a₁ a₂ : UpgradeAuthorityClaim}
    (h : encodeAuthorityClaim a₁ = encodeAuthorityClaim a₂) : a₁ = a₂ := by
  cases a₁ <;> cases a₂ <;> dsimp only [encodeAuthorityClaim] at h
  all_goals
    have hf := encodeSheFields_injective h
    try (cases (List.cons.inj (List.cons.inj hf).1).1)
  · rfl
  · simp only [List.cons.injEq, and_true] at hf
    exact congrArg UpgradeAuthorityClaim.vendorRootDirective (byteArray_eq_of_toList_eq hf.2)
  · simp only [List.cons.injEq, and_true] at hf
    rw [byteArray_eq_of_toList_eq hf.2.1, byteArray_eq_of_toList_eq hf.2.2]

def sheTurnWireFields : SheTurn → List (List UInt8)
  | .proposeAndSettleActuation act =>
    [ [0x01], leb128 act.sensorSeq, act.sensorSealDigest.data.toList, encodeCandidateComputation act.candidate,
      act.nullifier.data.toList, leb128 act.mandateCost, leb128 act.redactedRoiCount,
      leb128 act.consentBandHeightPx, leb128 act.attestedGpuCount, act.sharedRingAtCopy.data.toList,
      act.privateFrameCopy.data.toList, act.dispatchedPayload.data.toList, leb128 act.simplexCommitteeN,
      leb128 act.simplexFaultyF, encodeNatList act.simplexFinalizeSigners, leb128 act.custodianEpoch,
      encodeNatList act.custodianSigners, leb128 act.tofRoundTripTicks ]
  | .upgradeHabitatJudge up =>
    [ [0x02], up.newJudgeDigest.data.toList, up.newModelWeightsRoot.data.toList, encodeFloors up.newFloors,
      leb128 up.newRevertWindowSteps, leb128 up.newCustodianEpoch, encodeNatList up.custodianSigners,
      leb128 up.tofRoundTripTicks, encodeAuthorityClaim up.authorityClaim ]
  | .revokeOrAttenuateMandate rev =>
    [ [0x03], leb128 rev.newBudgetCap, leb128 rev.newMaxProximityTicks,
      encodeNatList rev.newlyRevokedCustodians, rev.reasonDigest.data.toList ]
def sheTurnPreimage (turn : SheTurn) : List UInt8 := encodeSheFields (sheTurnWireFields turn)
theorem sheTurnPreimage_injective {t₁ t₂ : SheTurn} (h : sheTurnPreimage t₁ = sheTurnPreimage t₂) : t₁ = t₂ := by
  have hf := encodeSheFields_injective h
  cases t₁ with
  | proposeAndSettleActuation a₁ =>
    cases t₂ with
    | proposeAndSettleActuation a₂ =>
      simp only [sheTurnWireFields, List.cons.injEq, true_and, and_true] at hf
      obtain ⟨hSeq, hSeal, hCand, hNul, hCost, hRoi, hBand, hGpu, hRing, hPriv, hDisp,
              hComN, hComF, hQc, hEp, hCust, hTof⟩ := hf
      cases a₁; cases a₂; simp only [SheTurn.proposeAndSettleActuation.injEq, ActuationTurnProposal.mk.injEq]
      exact ⟨leb128_injective hSeq, byteArray_eq_of_toList_eq hSeal, encodeCandidateComputation_injective hCand,
        byteArray_eq_of_toList_eq hNul, leb128_injective hCost, leb128_injective hRoi, leb128_injective hBand,
        leb128_injective hGpu, byteArray_eq_of_toList_eq hRing, byteArray_eq_of_toList_eq hPriv,
        byteArray_eq_of_toList_eq hDisp, leb128_injective hComN, leb128_injective hComF,
        encodeNatList_injective hQc, leb128_injective hEp, encodeNatList_injective hCust, leb128_injective hTof⟩
    | upgradeHabitatJudge _ | revokeOrAttenuateMandate _ =>
      dsimp only [sheTurnWireFields] at hf; cases (List.cons.inj (List.cons.inj hf).1).1
  | upgradeHabitatJudge u₁ =>
    cases t₂ with
    | proposeAndSettleActuation _ | revokeOrAttenuateMandate _ =>
      dsimp only [sheTurnWireFields] at hf; cases (List.cons.inj (List.cons.inj hf).1).1
    | upgradeHabitatJudge u₂ =>
      simp only [sheTurnWireFields, List.cons.injEq, true_and, and_true] at hf
      obtain ⟨hJd, hMw, hFl, hRev, hEp, hCust, hTof, hAuth⟩ := hf
      cases u₁; cases u₂; simp only [SheTurn.upgradeHabitatJudge.injEq, UpgradeJudgeProposal.mk.injEq]
      exact ⟨byteArray_eq_of_toList_eq hJd, byteArray_eq_of_toList_eq hMw, encodeFloors_injective hFl,
        leb128_injective hRev, leb128_injective hEp, encodeNatList_injective hCust,
        leb128_injective hTof, encodeAuthorityClaim_injective hAuth⟩
  | revokeOrAttenuateMandate r₁ =>
    cases t₂ with
    | proposeAndSettleActuation _ | upgradeHabitatJudge _ =>
      dsimp only [sheTurnWireFields] at hf; cases (List.cons.inj (List.cons.inj hf).1).1
    | revokeOrAttenuateMandate r₂ =>
      simp only [sheTurnWireFields, List.cons.injEq, true_and, and_true] at hf
      obtain ⟨hBud, hProx, hRevC, hRsn⟩ := hf
      cases r₁; cases r₂; simp only [SheTurn.revokeOrAttenuateMandate.injEq, MandateAttenuation.mk.injEq]
      exact ⟨leb128_injective hBud, leb128_injective hProx, encodeNatList_injective hRevC,
        byteArray_eq_of_toList_eq hRsn⟩

def sheTurnEnvelopeDigest (turn : SheTurn) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.TURN/v1") (sheTurnPreimage turn)
theorem sheTurnEnvelopeDigest_size (turn : SheTurn) : (sheTurnEnvelopeDigest turn).size = 32 := cshake32ByteArray_size _ _
def extractSheTurnEnvelope (t₁ t₂ : SheTurn) (h : sheTurnEnvelopeDigest t₁ = sheTurnEnvelopeDigest t₂) :
    PSum (PLift (t₁ = t₂)) (PLift (CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.TURN/v1"))
      (fun x => x = sheTurnPreimage t₁ ∨ x = sheTurnPreimage t₂))) :=
  match extractCshake32 (asciiTagBytes "OBEND.SHE.TURN/v1") (sheTurnPreimage t₁) (sheTurnPreimage t₂) h with
  | .inl hp => .inl ⟨sheTurnPreimage_injective hp.down⟩ | .inr hc => .inr hc
/-- **Complete `OBEND.SHE.TURN/v1` Envelope Binding (`sheTurnEnvelope_binds`, `0 Classical`)**. -/
theorem sheTurnEnvelope_binds {t₁ t₂ : SheTurn} (h : sheTurnEnvelopeDigest t₁ = sheTurnEnvelopeDigest t₂) :
    t₁ = t₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.TURN/v1"))
      (fun x => x = sheTurnPreimage t₁ ∨ x = sheTurnPreimage t₂) := by
  cases extractSheTurnEnvelope t₁ t₂ h with | inl heq => exact .inl heq.down | inr hcol => exact .inr hcol.down

/-! ## 3. Deterministic Multi-Turn Sovereign SHE Transition Gate & Declarative Step Equivalence -/

inductive SheRefusal where
  | malformedInitialState
  | invalidDigestWidth
  | nonMonotoneSensorSeq (currentSeq proposedSeq : Nat)
  | sensorSealMismatch
  | zkmlProofUnverified
  | withdrawnCbrRegimeRefused
  | belowProven100BitFloor (actualMilliBits : Nat)
  | modelWeightsRootMismatch
  | floorsDigestMismatch
  | payloadDigestMismatch
  | floorConstraintViolated (floor : SheFloor)
  | nullifierReplayed
  | mandateBudgetExceeded (requested available : Nat)
  | privateFrameCopyMismatch
  | invalidSimplexCommittee (committeeN faultyF : Nat)
  | invalidSimplexFinalityQc (signedCount requiredQuorum : Nat)
  | custodianEpochMismatch (expected actual : Nat)
  | duplicateOrOutOfRangeSigner
  | revokedCustodianSigner (signer : Nat)
  | insufficientCustodianQuorum (signedCount requiredT : Nat)
  | tofProximityExceeded (actualTicks maxTicks : Nat)
  | coerciveFloorDowngrade (droppedFloor : SheFloor)
  | malformedFloorSet
  | nonMonotoneCustodianEpoch (currentEpoch proposedEpoch : Nat)
  | mandateAmplificationRefused
  | proximityWideningRefused (proposedTicks currentMaxTicks : Nat)
  | missingTargetFloor (floor : SheFloor)
  | terminalStateMismatch
  deriving DecidableEq, Repr

def checkListNodup {α : Type} [DecidableEq α] : List α → Bool
  | [] => true | x :: xs => !xs.contains x && checkListNodup xs
theorem checkListNodup_iff {α : Type} [DecidableEq α] : ∀ (xs : List α), checkListNodup xs = true ↔ xs.Nodup
  | [] => by simp [checkListNodup]
  | x :: xs => by
    cases hc : xs.contains x with
    | true => simp [checkListNodup, List.nodup_cons, List.contains_iff_mem.mp hc]
    | false =>
      have hNot : x ∉ xs := fun hm => Bool.false_ne_true (hc.symm.trans (List.contains_iff_mem.mpr hm))
      simp [checkListNodup, checkListNodup_iff xs, List.nodup_cons, hNot]
abbrev checkNatNodup : List Nat → Bool := checkListNodup
abbrev checkFloorNodup : List SheFloor → Bool := checkListNodup

def checkFloorOnActuation (revertSteps : Nat) (act : ActuationTurnProposal) : SheFloor → Bool
  | .sensorRoiRedaction minRois => decide (minRois ≤ act.redactedRoiCount)
  | .consentBandNonOcclusion minBandPx => decide (0 < minBandPx ∧ minBandPx ≤ act.consentBandHeightPx)
  | .zkmlProvenSoundnessMilliBits minMb => decide (minMb ≤ provenZkmlMilliBits act.candidate)
  | .physicalProximityMaxTicks maxTicks => decide (act.tofRoundTripTicks ≤ maxTicks)
  | .e2eeTeeChannelBound minGpus => decide (minGpus ≤ act.attestedGpuCount)
  | .operatorLocalRevert maxRev => decide (revertSteps ≤ maxRev)
def holdsOnSettledRecord (φ : SheFloor) (rec : SettledActuationRecord) : Bool := match φ with
  | .sensorRoiRedaction minRois => decide (minRois ≤ rec.redactedRoiCount)
  | .consentBandNonOcclusion minBandPx => decide (0 < minBandPx ∧ minBandPx ≤ rec.consentBandHeightPx)
  | .zkmlProvenSoundnessMilliBits minMb => decide (minMb ≤ rec.provenZkmlMilliBits)
  | .physicalProximityMaxTicks maxTicks => decide (rec.tofRoundTripTicks ≤ maxTicks)
  | .e2eeTeeChannelBound minGpus => decide (minGpus ≤ rec.attestedGpuCount)
  | .operatorLocalRevert maxRev => decide (rec.revertWindowAtSettlement ≤ maxRev)

def mergeRevokedCustodians (cur incoming : List Nat) : List Nat :=
  incoming.foldl (fun acc c => if acc.contains c then acc else acc ++ [c]) cur
theorem mem_mergeRevokedCustodians {cur incoming : List Nat} {x : Nat} :
    x ∈ mergeRevokedCustodians cur incoming ↔ x ∈ cur ∨ x ∈ incoming := by
  unfold mergeRevokedCustodians; induction incoming generalizing cur with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]; split
    · rename_i hIn; rw [ih]; have ha := List.contains_iff_mem.mp hIn
      exact ⟨fun | .inl hc => .inl hc | .inr hs => .inr (List.mem_cons_of_mem _ hs),
             fun | .inl hc => .inl hc | .inr h => match List.mem_cons.mp h with
               | .inl heq => heq ▸ .inl ha | .inr hs => .inr hs⟩
    · rw [ih]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨fun | .inl (.inl hc) => .inl hc | .inl (.inr ha) => .inr (.inl ha) | .inr hs => .inr (.inr hs),
             fun | .inl hc => .inl (.inl hc) | .inr (.inl ha) => .inl (.inr ha) | .inr (.inr hs) => .inr hs⟩

def guardE (cond : Bool) (err : SheRefusal) : Except SheRefusal Unit :=
  if cond then .ok () else .error err
@[simp] private theorem bind_guardE_ok {α : Type} {b : Bool} {e : SheRefusal}
    {k : Unit → Except SheRefusal α} {v : α} : (guardE b e >>= k) = .ok v ↔ b = true ∧ k () = .ok v := by
  cases b <;> simp [guardE, Bind.bind, Except.bind]
@[simp] private theorem guardE_ok {b : Bool} {e : SheRefusal} {u : Unit} :
    guardE b e = .ok u ↔ b = true := by cases b <;> cases u <;> simp [guardE]
@[simp] private theorem bind_ok_unit {α : Type} {k : Unit → Except SheRefusal α} :
    (Except.ok () >>= k) = k () := rfl
@[simp] private theorem pure_except_ok {α : Type} {x y : α} :
    (pure x : Except SheRefusal α) = .ok y ↔ x = y := by simp [Pure.pure, Except.pure]

def checkCustodianQuorum (st : SheState) (signers : List Nat) : Except SheRefusal Unit := do
  guardE (decide (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN))
    (.insufficientCustodianQuorum signers.length st.custodianThresholdT)
  guardE (checkNatNodup signers && signers.all (fun s => decide (s < st.custodianTotalN)))
    .duplicateOrOutOfRangeSigner
  match signers.find? (fun s => st.revokedCustodians.contains s) with
  | some rev => .error (.revokedCustodianSigner rev)
  | none => guardE (decide (st.custodianThresholdT ≤ signers.length))
              (.insufficientCustodianQuorum signers.length st.custodianThresholdT)

theorem checkCustodianQuorum_ok_iff (st : SheState) (signers : List Nat) :
    checkCustodianQuorum st signers = .ok () ↔
      (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN) ∧
      signers.Nodup ∧ (∀ s ∈ signers, s < st.custodianTotalN) ∧
      (∀ s ∈ signers, s ∉ st.revokedCustodians) ∧ st.custodianThresholdT ≤ signers.length := by
  unfold checkCustodianQuorum
  cases hFind : signers.find? (fun s => st.revokedCustodians.contains s) with
  | some rev =>
    have hMem := List.mem_of_find?_eq_some hFind
    have hRev := List.contains_iff_mem.mp (List.find?_some hFind)
    simp only [bind_guardE_ok]
    exact ⟨fun ⟨_, _, hErr⟩ => (nomatch hErr), fun ⟨_, _, _, hNo, _⟩ => absurd hRev (hNo rev hMem)⟩
  | none =>
    have hNone : ∀ s ∈ signers, s ∉ st.revokedCustodians := fun s hs hIn =>
      List.find?_eq_none.mp hFind s hs (List.contains_iff_mem.mpr hIn)
    simp only [bind_guardE_ok, guardE_ok, Bool.and_eq_true, checkListNodup_iff, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨h1, ⟨h2, h3⟩, h4⟩ => ⟨h1, h2, h3, hNone, h4⟩, fun ⟨h1, h2, h3, _, h4⟩ => ⟨h1, ⟨h2, h3⟩, h4⟩⟩

def buildSettledRecord (st : SheState) (act : ActuationTurnProposal) : SettledActuationRecord :=
  { sensorSeq := act.sensorSeq, sensorSealDigest := act.sensorSealDigest, nullifier := act.nullifier
    mandateCost := act.mandateCost, redactedRoiCount := act.redactedRoiCount
    consentBandHeightPx := act.consentBandHeightPx, attestedGpuCount := act.attestedGpuCount
    provenZkmlMilliBits := provenZkmlMilliBits act.candidate, zkmlRegime := act.candidate.regime
    modelWeightsRoot := act.candidate.modelWeightsRoot, activeFloorsAtSettlement := st.activeSafetyAndPrivacyFloors
    boundFloorsDigest := act.candidate.boundFloorsDigest, revertWindowAtSettlement := st.revertWindowSteps
    sharedRingAtCopy := act.sharedRingAtCopy, privateFrameCopy := act.privateFrameCopy
    dispatchedPayload := act.dispatchedPayload, simplexCommitteeN := act.simplexCommitteeN
    simplexFaultyF := act.simplexFaultyF, simplexQuorumCount := act.simplexFinalizeSigners.length
    custodianEpoch := act.custodianEpoch, custodianSigners := act.custodianSigners
    tofRoundTripTicks := act.tofRoundTripTicks, maxProximityTicksAtSettle := st.maxProximityTicks
    turnEnvelopeDigest := sheTurnEnvelopeDigest (.proposeAndSettleActuation act) }

@[expose] def applySheTurn (st : SheState) (turn : SheTurn) : Except SheRefusal SheState := match turn with
  | .proposeAndSettleActuation act => do
    guardE (decide (act.sensorSealDigest.size = 32 ∧ act.candidate.statementDigest.size = 32 ∧
                    act.candidate.modelWeightsRoot.size = 32 ∧ act.candidate.boundFloorsDigest.size = 32 ∧
                    act.candidate.sensorSealDigest.size = 32 ∧ act.candidate.actionPayloadDigest.size = 32 ∧
                    act.nullifier.size = 32)) .invalidDigestWidth
    guardE (decide (st.monoSensorSeq < act.sensorSeq)) (.nonMonotoneSensorSeq st.monoSensorSeq act.sensorSeq)
    guardE (act.candidate.sensorSealDigest == act.sensorSealDigest) .sensorSealMismatch
    guardE act.candidate.proofVerified .zkmlProofUnverified
    guardE (act.candidate.regime != .withdrawnCapacityBoundCbr) .withdrawnCbrRegimeRefused
    guardE (decide (100000 ≤ provenZkmlMilliBits act.candidate)) (.belowProven100BitFloor (provenZkmlMilliBits act.candidate))
    guardE (act.candidate.modelWeightsRoot == st.pinnedModelWeightsRoot) .modelWeightsRootMismatch
    guardE (act.candidate.boundFloorsDigest == floorsDigest st.activeSafetyAndPrivacyFloors) .floorsDigestMismatch
    guardE (act.candidate.actionPayloadDigest == shePayloadDigest act.privateFrameCopy) .payloadDigestMismatch
    guardE (decide (act.tofRoundTripTicks ≤ st.maxProximityTicks)) (.tofProximityExceeded act.tofRoundTripTicks st.maxProximityTicks)
    match st.activeSafetyAndPrivacyFloors.find? (fun φ => !checkFloorOnActuation st.revertWindowSteps act φ) with
    | some violated => .error (.floorConstraintViolated violated)
    | none => do
      guardE (!st.consumedNullifiers.contains act.nullifier) .nullifierReplayed
      guardE (decide (act.mandateCost ≤ st.remainingMandateBudget)) (.mandateBudgetExceeded act.mandateCost st.remainingMandateBudget)
      guardE (act.privateFrameCopy == act.sharedRingAtCopy && act.dispatchedPayload == act.privateFrameCopy) .privateFrameCopyMismatch
      guardE (decide (3 * act.simplexFaultyF + 1 ≤ act.simplexCommitteeN)) (.invalidSimplexCommittee act.simplexCommitteeN act.simplexFaultyF)
      guardE (checkNatNodup act.simplexFinalizeSigners &&
              act.simplexFinalizeSigners.all (fun v => decide (v < act.simplexCommitteeN)) &&
              decide (act.simplexCommitteeN - act.simplexFaultyF ≤ act.simplexFinalizeSigners.length))
        (.invalidSimplexFinalityQc act.simplexFinalizeSigners.length (act.simplexCommitteeN - act.simplexFaultyF))
      guardE (decide (act.custodianEpoch = st.custodianQuorumEpoch)) (.custodianEpochMismatch st.custodianQuorumEpoch act.custodianEpoch)
      checkCustodianQuorum st act.custodianSigners
      pure { st with monoSensorSeq := act.sensorSeq, consumedNullifiers := st.consumedNullifiers ++ [act.nullifier]
                     remainingMandateBudget := st.remainingMandateBudget - act.mandateCost
                     settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
  | .upgradeHabitatJudge up =>
    match st.activeSafetyAndPrivacyFloors.find? (fun φ => !up.newFloors.contains φ) with
    | some dropped => .error (.coerciveFloorDowngrade dropped)
    | none => do
      guardE (decide (up.newJudgeDigest.size = 32 ∧ up.newModelWeightsRoot.size = 32)) .invalidDigestWidth
      guardE (checkFloorNodup up.newFloors && up.newFloors.any SheFloor.isBedrock && up.newFloors.all SheFloor.wellFormed &&
              up.newFloors.all (fun φ => match φ with
                | .operatorLocalRevert maxRev => decide (up.newRevertWindowSteps ≤ maxRev) | _ => true)) .malformedFloorSet
      guardE (decide (st.custodianQuorumEpoch < up.newCustodianEpoch)) (.nonMonotoneCustodianEpoch st.custodianQuorumEpoch up.newCustodianEpoch)
      checkCustodianQuorum st up.custodianSigners
      guardE (decide (up.tofRoundTripTicks ≤ st.maxProximityTicks)) (.tofProximityExceeded up.tofRoundTripTicks st.maxProximityTicks)
      pure { st with habitatJudgeDigest := up.newJudgeDigest, pinnedModelWeightsRoot := up.newModelWeightsRoot
                     activeSafetyAndPrivacyFloors := up.newFloors, revertWindowSteps := up.newRevertWindowSteps
                     custodianQuorumEpoch := up.newCustodianEpoch }
  | .revokeOrAttenuateMandate rev => do
    guardE (decide (rev.reasonDigest.size = 32)) .invalidDigestWidth
    guardE (decide (rev.newBudgetCap ≤ st.remainingMandateBudget)) .mandateAmplificationRefused
    guardE (decide (0 < rev.newMaxProximityTicks ∧ rev.newMaxProximityTicks ≤ st.maxProximityTicks))
      (.proximityWideningRefused rev.newMaxProximityTicks st.maxProximityTicks)
    guardE (rev.newlyRevokedCustodians.all (fun c => decide (c < st.custodianTotalN))) .duplicateOrOutOfRangeSigner
    pure { st with remainingMandateBudget := rev.newBudgetCap, maxProximityTicks := rev.newMaxProximityTicks
                   revokedCustodians := mergeRevokedCustodians st.revokedCustodians rev.newlyRevokedCustodians }

@[expose] def runSheTurns (st : SheState) (turns : List SheTurn) : Except (Nat × SheRefusal) SheState := go 0 st turns
where
  go (idx : Nat) (cur : SheState) : List SheTurn → Except (Nat × SheRefusal) SheState
    | [] => .ok cur
    | t :: ts => match applySheTurn cur t with | .error r => .error (idx, r) | .ok next => go (idx + 1) next ts
@[expose] def ValidSheTrace : SheState → List SheTurn → SheState → Prop
  | st, [], stFinal => stFinal = st
  | st, t :: ts, stFinal => ∃ stNext, applySheTurn st t = .ok stNext ∧ ValidSheTrace stNext ts stFinal
theorem runSheTurns_go_ok_iff :
    ∀ (turns : List SheTurn) (idx : Nat) (st endSt : SheState),
      runSheTurns.go idx st turns = .ok endSt ↔ ValidSheTrace st turns endSt
  | [], _, _, _ => by simp [runSheTurns.go, ValidSheTrace, eq_comm]
  | t :: ts, idx, st, endSt => by
    simp only [runSheTurns.go, ValidSheTrace]; cases applySheTurn st t with
    | error _ => simp | ok next => simp [runSheTurns_go_ok_iff ts (idx + 1) next endSt]
theorem runSheTurns_ok_iff (st : SheState) (turns : List SheTurn) (endSt : SheState) :
    runSheTurns st turns = .ok endSt ↔ ValidSheTrace st turns endSt := runSheTurns_go_ok_iff turns 0 st endSt

inductive InductiveSheStep : SheState → SheTurn → SheState → Prop where
  | settleActuation (st : SheState) (act : ActuationTurnProposal)
      (hWidths : act.sensorSealDigest.size = 32 ∧ act.candidate.statementDigest.size = 32 ∧
                 act.candidate.modelWeightsRoot.size = 32 ∧ act.candidate.boundFloorsDigest.size = 32 ∧
                 act.candidate.sensorSealDigest.size = 32 ∧ act.candidate.actionPayloadDigest.size = 32 ∧
                 act.nullifier.size = 32)
      (hSeq : st.monoSensorSeq < act.sensorSeq) (hSeal : act.candidate.sensorSealDigest = act.sensorSealDigest)
      (hVer : act.candidate.proofVerified = true) (hRegime : act.candidate.regime ≠ .withdrawnCapacityBoundCbr)
      (hBits : 100000 ≤ provenZkmlMilliBits act.candidate)
      (hWeights : act.candidate.modelWeightsRoot = st.pinnedModelWeightsRoot)
      (hFlDig : act.candidate.boundFloorsDigest = floorsDigest st.activeSafetyAndPrivacyFloors)
      (hPayDig : act.candidate.actionPayloadDigest = shePayloadDigest act.privateFrameCopy)
      (hTof : act.tofRoundTripTicks ≤ st.maxProximityTicks)
      (hFloors : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, checkFloorOnActuation st.revertWindowSteps act φ = true)
      (hFresh : act.nullifier ∉ st.consumedNullifiers) (hBudget : act.mandateCost ≤ st.remainingMandateBudget)
      (hCopy : act.privateFrameCopy = act.sharedRingAtCopy ∧ act.dispatchedPayload = act.privateFrameCopy)
      (hSimpC : 3 * act.simplexFaultyF + 1 ≤ act.simplexCommitteeN)
      (hSimpQc : act.simplexFinalizeSigners.Nodup ∧ (∀ v ∈ act.simplexFinalizeSigners, v < act.simplexCommitteeN) ∧
                 act.simplexCommitteeN - act.simplexFaultyF ≤ act.simplexFinalizeSigners.length)
      (hEp : act.custodianEpoch = st.custodianQuorumEpoch)
      (hCust : (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN) ∧
               act.custodianSigners.Nodup ∧ (∀ s ∈ act.custodianSigners, s < st.custodianTotalN) ∧
               (∀ s ∈ act.custodianSigners, s ∉ st.revokedCustodians) ∧
               st.custodianThresholdT ≤ act.custodianSigners.length) :
      InductiveSheStep st (.proposeAndSettleActuation act)
        { st with monoSensorSeq := act.sensorSeq, consumedNullifiers := st.consumedNullifiers ++ [act.nullifier]
                  remainingMandateBudget := st.remainingMandateBudget - act.mandateCost
                  settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
  | upgradeJudge (st : SheState) (up : UpgradeJudgeProposal)
      (hNonReg : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, φ ∈ up.newFloors)
      (hWidths : up.newJudgeDigest.size = 32 ∧ up.newModelWeightsRoot.size = 32)
      (hFlWf : up.newFloors.Nodup ∧ (∃ φ ∈ up.newFloors, φ.isBedrock = true) ∧
               (∀ φ ∈ up.newFloors, φ.wellFormed = true) ∧
               (∀ φ ∈ up.newFloors, (match φ with
                 | .operatorLocalRevert maxRev => decide (up.newRevertWindowSteps ≤ maxRev) | _ => true) = true))
      (hEp : st.custodianQuorumEpoch < up.newCustodianEpoch)
      (hCust : (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN) ∧
               up.custodianSigners.Nodup ∧ (∀ s ∈ up.custodianSigners, s < st.custodianTotalN) ∧
               (∀ s ∈ up.custodianSigners, s ∉ st.revokedCustodians) ∧
               st.custodianThresholdT ≤ up.custodianSigners.length)
      (hTof : up.tofRoundTripTicks ≤ st.maxProximityTicks) :
      InductiveSheStep st (.upgradeHabitatJudge up)
        { st with habitatJudgeDigest := up.newJudgeDigest, pinnedModelWeightsRoot := up.newModelWeightsRoot
                  activeSafetyAndPrivacyFloors := up.newFloors, revertWindowSteps := up.newRevertWindowSteps
                  custodianQuorumEpoch := up.newCustodianEpoch }
  | attenuateMandate (st : SheState) (rev : MandateAttenuation)
      (hWidth : rev.reasonDigest.size = 32) (hBud : rev.newBudgetCap ≤ st.remainingMandateBudget)
      (hProx : 0 < rev.newMaxProximityTicks ∧ rev.newMaxProximityTicks ≤ st.maxProximityTicks)
      (hRevRange : ∀ c ∈ rev.newlyRevokedCustodians, c < st.custodianTotalN) :
      InductiveSheStep st (.revokeOrAttenuateMandate rev)
        { st with remainingMandateBudget := rev.newBudgetCap, maxProximityTicks := rev.newMaxProximityTicks
                  revokedCustodians := mergeRevokedCustodians st.revokedCustodians rev.newlyRevokedCustodians }

theorem applySheTurn_ok_iff_inductiveStep (st : SheState) (turn : SheTurn) (st' : SheState) :
    applySheTurn st turn = .ok st' ↔ InductiveSheStep st turn st' := by
  constructor
  · intro hOk; cases turn with
    | proposeAndSettleActuation act =>
      unfold applySheTurn at hOk; simp only [bind_guardE_ok] at hOk
      obtain ⟨hWidths, hSeq, hSeal, hVer, hReg, hBits, hW, hFlD, hPayD, hTof, hRest⟩ := hOk
      cases hFlFind : st.activeSafetyAndPrivacyFloors.find? (fun φ => !checkFloorOnActuation st.revertWindowSteps act φ) with
      | some _ => rw [hFlFind] at hRest; cases hRest
      | none =>
        rw [hFlFind] at hRest; simp only [bind_guardE_ok] at hRest
        cases hCust : checkCustodianQuorum st act.custodianSigners with
        | error _ => rw [hCust] at hRest; simp [Bind.bind, Except.bind] at hRest
        | ok _ =>
          rw [hCust] at hRest
          simp only [Bind.bind, Except.bind, pure_except_ok, decide_eq_true_eq, beq_iff_eq,
            bne_iff_ne, Bool.and_eq_true, checkListNodup_iff, List.all_eq_true] at hWidths hSeq hSeal hReg hBits hW hFlD hPayD hTof hRest
          obtain ⟨hNotNul, hBud, hCopy, hSimpC, ⟨⟨hQcNd, hQcBnd⟩, hQcLen⟩, hEp, rfl⟩ := hRest
          have hFresh : act.nullifier ∉ st.consumedNullifiers := fun hIn => by
            rw [List.contains_iff_mem.mpr hIn] at hNotNul; cases hNotNul
          have hFloors : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, checkFloorOnActuation st.revertWindowSteps act φ = true :=
            fun φ hφ => by
              have hf := List.find?_eq_none.mp hFlFind φ hφ
              cases hc : checkFloorOnActuation st.revertWindowSteps act φ with
              | true => rfl | false => rw [hc] at hf; exact absurd rfl hf
          exact .settleActuation st act hWidths hSeq hSeal hVer hReg hBits hW hFlD hPayD hTof hFloors hFresh
            hBud hCopy hSimpC ⟨hQcNd, hQcBnd, hQcLen⟩ hEp ((checkCustodianQuorum_ok_iff st act.custodianSigners).mp hCust)
    | upgradeHabitatJudge up =>
      unfold applySheTurn at hOk; dsimp only at hOk
      cases hDrop : st.activeSafetyAndPrivacyFloors.find? (fun ψ => !up.newFloors.contains ψ) with
      | some _ => rw [hDrop] at hOk; cases hOk
      | none =>
        rw [hDrop] at hOk; simp only [bind_guardE_ok] at hOk
        obtain ⟨hW, hFlAll, hEp, hRest⟩ := hOk
        generalize hCust : checkCustodianQuorum st up.custodianSigners = cRes at hRest
        cases cRes with
        | error _ => simp [Bind.bind, Except.bind] at hRest
        | ok u =>
          cases u; simp only [bind_ok_unit, bind_guardE_ok, pure_except_ok] at hRest
          simp only [decide_eq_true_eq, Bool.and_eq_true, checkListNodup_iff, List.any_eq_true,
            List.all_eq_true] at hW hFlAll hEp hRest
          obtain ⟨⟨⟨hNd, hBed⟩, hWf⟩, hRevBnd⟩ := hFlAll; obtain ⟨hTof, rfl⟩ := hRest
          have hNonReg : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, φ ∈ up.newFloors := fun φ hφ => by
            have hf := List.find?_eq_none.mp hDrop φ hφ
            cases hc : up.newFloors.contains φ with
            | true => exact List.contains_iff_mem.mp hc | false => rw [hc] at hf; exact absurd rfl hf
          exact .upgradeJudge st up hNonReg hW ⟨hNd, hBed, hWf, hRevBnd⟩ hEp
            ((checkCustodianQuorum_ok_iff st up.custodianSigners).mp hCust) hTof
    | revokeOrAttenuateMandate rev =>
      unfold applySheTurn at hOk; dsimp only at hOk
      simp only [bind_guardE_ok, pure_except_ok, decide_eq_true_eq, List.all_eq_true] at hOk
      obtain ⟨hW, hBud, hProx, hRange, rfl⟩ := hOk; exact .attenuateMandate st rev hW hBud hProx hRange
  · intro hInd; cases hInd with
    | settleActuation act hWidths hSeq hSeal hVer hReg hBits hW hFlD hPayD hTof
        hFloors hFresh hBud hCopy hSimpC hSimpQc hEp hCust =>
      unfold applySheTurn; dsimp only
      have hFlNone : st.activeSafetyAndPrivacyFloors.find?
          (fun φ => !checkFloorOnActuation st.revertWindowSteps act φ) = none :=
        List.find?_eq_none.mpr fun φ hφ => by simp [hFloors φ hφ]
      have hNotCont : (!st.consumedNullifiers.contains act.nullifier) = true := by
        cases hc : st.consumedNullifiers.contains act.nullifier with
        | false => rfl | true => exact absurd (List.contains_iff_mem.mp hc) hFresh
      have hCustOk := (checkCustodianQuorum_ok_iff st act.custodianSigners).mpr hCust
      simp only [bind_guardE_ok]; rw [hFlNone]; simp only [bind_guardE_ok]; rw [hCustOk]
      simp only [bind_ok_unit, pure_except_ok, decide_eq_true_eq, beq_iff_eq,
        bne_iff_ne, Bool.and_eq_true, checkListNodup_iff, List.all_eq_true]
      exact ⟨hWidths, hSeq, hSeal, hVer, hReg, hBits, hW, hFlD, hPayD, hTof, hNotCont, hBud,
        hCopy, hSimpC, ⟨⟨hSimpQc.1, hSimpQc.2.1⟩, hSimpQc.2.2⟩, hEp, trivial⟩
    | upgradeJudge up hNonReg hWidths hFlWf hEp hCust hTof =>
      unfold applySheTurn; dsimp only
      have hDropNone : st.activeSafetyAndPrivacyFloors.find? (fun ψ => !up.newFloors.contains ψ) = none :=
        List.find?_eq_none.mpr fun φ hφ => by rw [List.contains_iff_mem.mpr (hNonReg φ hφ)]; decide
      have hCustOk := (checkCustodianQuorum_ok_iff st up.custodianSigners).mpr hCust
      rw [hDropNone]; simp only [bind_guardE_ok]; rw [hCustOk]
      simp only [bind_ok_unit, bind_guardE_ok, pure_except_ok,
        decide_eq_true_eq, Bool.and_eq_true, checkListNodup_iff, List.any_eq_true, List.all_eq_true]
      exact ⟨hWidths, ⟨⟨⟨hFlWf.1, hFlWf.2.1⟩, hFlWf.2.2.1⟩, hFlWf.2.2.2⟩, hEp, hTof, trivial⟩
    | attenuateMandate rev hWidth hBud hProx hRevRange =>
      unfold applySheTurn; dsimp only
      simp only [bind_guardE_ok, pure_except_ok, decide_eq_true_eq, List.all_eq_true]
      exact ⟨hWidth, hBud, hProx, hRevRange, trivial⟩

theorem applySheTurn_skip_implies_contract_violation (st : SheState) (turn : SheTurn)
    (r : SheRefusal) (hErr : applySheTurn st turn = .error r) :
    ∀ st', ¬ InductiveSheStep st turn st' := fun st' hStep => by
  have hOk := (applySheTurn_ok_iff_inductiveStep st turn st').mpr hStep
  rw [hErr] at hOk; cases hOk

/-! ## 4. Flagship Theorems: `vaz_coercive_floor_downgrade_refused` & `she_trace_end_to_end_safe_and_anti_vaz` -/

private theorem step_preserves_floors {st st' : SheState} {turn : SheTurn}
    (h : applySheTurn st turn = .ok st') :
    ∀ φ ∈ st.activeSafetyAndPrivacyFloors, φ ∈ st'.activeSafetyAndPrivacyFloors := by
  cases (applySheTurn_ok_iff_inductiveStep st turn st').mp h with
  | settleActuation | attenuateMandate => exact fun _ hφ => hφ
  | upgradeJudge _ hNonReg => exact hNonReg

/-- **Flagship Anti-Vaz Constitutional Non-Regression Theorem (`vaz_coercive_floor_downgrade_refused`)**. -/
theorem vaz_coercive_floor_downgrade_refused
    (initState endState : SheState) (turns : List SheTurn) :
    (∀ (st : SheState) (up : UpgradeJudgeProposal) (φ : SheFloor),
      φ ∈ st.activeSafetyAndPrivacyFloors → φ ∉ up.newFloors →
      (∃ dropped ∈ st.activeSafetyAndPrivacyFloors,
        dropped ∉ up.newFloors ∧
        applySheTurn st (.upgradeHabitatJudge up) = .error (.coerciveFloorDowngrade dropped)) ∧
      ∀ st', applySheTurn st (.upgradeHabitatJudge up) ≠ .ok st') ∧
    (ValidSheTrace initState turns endState →
      initState.activeSafetyAndPrivacyFloors ⊆ endState.activeSafetyAndPrivacyFloors) := by
  refine ⟨fun st up φ hMem hNotMem => ?_, fun hTrace => ?_⟩
  · have hPred : (!up.newFloors.contains φ) = true := by
      cases hc : up.newFloors.contains φ with
      | false => rfl | true => exact absurd (List.contains_iff_mem.mp hc) hNotMem
    cases hFind : st.activeSafetyAndPrivacyFloors.find? (fun ψ => !up.newFloors.contains ψ) with
    | none => exact absurd hPred (List.find?_eq_none.mp hFind φ hMem)
    | some dropped =>
      have hDropPred := List.find?_some hFind
      have hDropNotIn : dropped ∉ up.newFloors := fun hin => by
        rw [List.contains_iff_mem.mpr hin] at hDropPred; cases hDropPred
      have hStepErr : applySheTurn st (.upgradeHabitatJudge up) =
          .error (.coerciveFloorDowngrade dropped) := by unfold applySheTurn; dsimp only; rw [hFind]
      exact ⟨⟨dropped, List.mem_of_find?_eq_some hFind, hDropNotIn, hStepErr⟩,
        fun _ hOk => by rw [hStepErr] at hOk; cases hOk⟩
  · induction turns generalizing initState with
    | nil => simp only [ValidSheTrace] at hTrace; subst hTrace; exact fun _ h => h
    | cons _ _ ih =>
      obtain ⟨stNext, hStep, hRest⟩ := hTrace
      exact fun φ hφ => ih stNext hRest (step_preserves_floors hStep φ hφ)

private def removeFirstNat (a : Nat) : List Nat → List Nat
  | [] => [] | y :: ys => if y = a then ys else y :: removeFirstNat a ys
private theorem removeFirstNat_length_of_mem {a : Nat} :
    ∀ {ys : List Nat}, a ∈ ys → (removeFirstNat a ys).length + 1 = ys.length
  | [], h => nomatch h
  | y :: ys, h => by
    simp only [removeFirstNat]; cases Nat.decEq y a with
    | isTrue hy => simp [hy]
    | isFalse hy =>
      simp only [hy, ↓reduceIte, List.length_cons]; rcases List.mem_cons.mp h with rfl | hm
      · exact absurd rfl hy
      · have := removeFirstNat_length_of_mem hm; omega
private theorem mem_removeFirstNat_of_ne {x a : Nat} : ∀ {ys : List Nat}, x ∈ ys → x ≠ a → x ∈ removeFirstNat a ys
  | [], h, _ => nomatch h
  | y :: ys, h, hne => by
    simp only [removeFirstNat]; cases Nat.decEq y a with
    | isTrue hy => subst hy; simp only [↓reduceIte]; exact match List.mem_cons.mp h with | .inl e => absurd e hne | .inr m => m
    | isFalse hy => simp only [hy, ↓reduceIte, List.mem_cons]
                    exact match List.mem_cons.mp h with | .inl e => .inl e | .inr m => .inr (mem_removeFirstNat_of_ne m hne)
private theorem nodup_subset_length_le : ∀ {xs ys : List Nat}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | a :: as, ys, hnd, hsub => by
    obtain ⟨haNotAs, hasNd⟩ := List.nodup_cons.mp hnd
    have := nodup_subset_length_le hasNd fun x hx =>
      mem_removeFirstNat_of_ne (hsub x (List.mem_cons_of_mem _ hx)) (fun heq => by subst heq; exact haNotAs hx)
    have := removeFirstNat_length_of_mem (hsub a List.mem_cons_self); simp only [List.length_cons]; omega

theorem coerced_subthreshold_coalition_omits_honest_signer {signers coerced : List Nat} {t : Nat}
    (hNodup : signers.Nodup) (hQuorum : t ≤ signers.length) (hCoerced : coerced.length < t) :
    ∃ h ∈ signers, h ∉ coerced := by
  cases hf : signers.find? (fun s => !coerced.contains s) with
  | some h =>
    have hPred := List.find?_some hf
    exact ⟨h, List.mem_of_find?_eq_some hf, fun hIn => by rw [List.contains_iff_mem.mpr hIn] at hPred; cases hPred⟩
  | none =>
    have hAll : ∀ s ∈ signers, s ∈ coerced := fun s hs => by
      have hp := List.find?_eq_none.mp hf s hs
      cases hc : coerced.contains s with
      | true => exact List.contains_iff_mem.mp hc | false => rw [hc] at hp; exact absurd rfl hp
    have := nodup_subset_length_le hNodup hAll; omega

private theorem pairwise_lt_snoc {xs : List Nat} {x : Nat}
    (hp : List.Pairwise (· < ·) xs) (hall : ∀ y ∈ xs, y < x) : List.Pairwise (· < ·) (xs ++ [x]) := by
  induction xs with
  | nil => exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | cons a as ih =>
    cases hp with | cons ha hpas =>
      refine List.Pairwise.cons (fun z hz => ?_) (ih hpas (fun y hy => hall y (List.mem_cons_of_mem _ hy)))
      rcases List.mem_append.mp hz with hzas | hzx
      · exact ha z hzas
      · simp only [List.mem_singleton] at hzx; exact hzx ▸ hall a List.mem_cons_self
private theorem nodup_snoc {α : Type} {xs : List α} {x : α} (hd : xs.Nodup) (hnot : x ∉ xs) :
    (xs ++ [x]).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | cons a as ih =>
    cases hd with | cons ha hdas =>
      refine List.Pairwise.cons (fun z hz => ?_) (ih hdas (fun hm => hnot (List.mem_cons_of_mem _ hm)))
      rcases List.mem_append.mp hz with hzas | hzx
      · exact ha z hzas
      · simp only [List.mem_singleton] at hzx; exact fun heq => hnot ((heq.trans hzx).symm ▸ List.mem_cons_self)

private structure SheTraceInv (init cur : SheState) : Prop where
  floorsSub       : init.activeSafetyAndPrivacyFloors ⊆ cur.activeSafetyAndPrivacyFloors
  seqMonoInit     : init.monoSensorSeq ≤ cur.monoSensorSeq
  proxLeInit      : cur.maxProximityTicks ≤ init.maxProximityTicks
  threshEq        : cur.custodianThresholdT = init.custodianThresholdT
  totalEq         : cur.custodianTotalN = init.custodianTotalN
  epochMonoInit   : init.custodianQuorumEpoch ≤ cur.custodianQuorumEpoch
  revokedMono     : ∀ r ∈ init.revokedCustodians, r ∈ cur.revokedCustodians
  budgetConserve  : settledTotalCost cur.settledOutboxActions + cur.remainingMandateBudget ≤
                      settledTotalCost init.settledOutboxActions + init.remainingMandateBudget
  consumedNodup   : cur.consumedNullifiers.Nodup
  settledNodup    : (cur.settledOutboxActions.map SettledActuationRecord.nullifier).Nodup
  settledInCons   : ∀ rec ∈ cur.settledOutboxActions, rec.nullifier ∈ cur.consumedNullifiers
  seqPairwise     : List.Pairwise (· < ·) (cur.settledOutboxActions.map SettledActuationRecord.sensorSeq)
  settledSeqBound : ∀ rec ∈ cur.settledOutboxActions, rec.sensorSeq ≤ cur.monoSensorSeq
  settledSafe     : ∀ rec ∈ cur.settledOutboxActions,
    rec ∈ init.settledOutboxActions ∨
    (init.monoSensorSeq < rec.sensorSeq ∧ rec.sensorSealDigest.size = 32 ∧
     rec.zkmlRegime ≠ .withdrawnCapacityBoundCbr ∧ 100000 ≤ rec.provenZkmlMilliBits ∧
     rec.boundFloorsDigest = floorsDigest rec.activeFloorsAtSettlement ∧
     init.activeSafetyAndPrivacyFloors ⊆ rec.activeFloorsAtSettlement ∧
     (∀ φ ∈ rec.activeFloorsAtSettlement, holdsOnSettledRecord φ rec = true) ∧
     rec.dispatchedPayload = rec.privateFrameCopy ∧ rec.privateFrameCopy = rec.sharedRingAtCopy ∧
     3 * rec.simplexFaultyF + 1 ≤ rec.simplexCommitteeN ∧
     rec.simplexCommitteeN - rec.simplexFaultyF ≤ rec.simplexQuorumCount ∧
     rec.custodianSigners.Nodup ∧ init.custodianThresholdT ≤ rec.custodianSigners.length ∧
     (∀ s ∈ rec.custodianSigners, s < init.custodianTotalN) ∧
     (∀ s ∈ rec.custodianSigners, s ∉ init.revokedCustodians) ∧
     rec.tofRoundTripTicks ≤ rec.maxProximityTicksAtSettle ∧
     rec.maxProximityTicksAtSettle ≤ init.maxProximityTicks)
private theorem checkFloor_eq_holdsOnSettledRecord (st : SheState) (act : ActuationTurnProposal) (φ : SheFloor) :
    holdsOnSettledRecord φ (buildSettledRecord st act) = checkFloorOnActuation st.revertWindowSteps act φ := by
  cases φ <;> rfl
private theorem sheTraceInv_step {init cur next : SheState} {turn : SheTurn}
    (hInv : SheTraceInv init cur) (hStep : applySheTurn cur turn = .ok next) :
    SheTraceInv init next := by
  cases (applySheTurn_ok_iff_inductiveStep cur turn next).mp hStep with
  | settleActuation act hWidths hSeqLt _ _ hNoCbr h100 _ hFlDig _ hTof hFloors hNulFresh
      hBud hCopy hSimpComm hSimpQc _ hCust =>
    have hNulNotSettled : act.nullifier ∉ cur.settledOutboxActions.map SettledActuationRecord.nullifier := by
      rintro hMap; obtain ⟨r, hr, hEq⟩ := List.mem_map.mp hMap; exact hNulFresh (hEq ▸ hInv.settledInCons r hr)
    refine
      { floorsSub := hInv.floorsSub, seqMonoInit := by dsimp only; have := hInv.seqMonoInit; omega
        proxLeInit := hInv.proxLeInit, threshEq := hInv.threshEq, totalEq := hInv.totalEq
        epochMonoInit := hInv.epochMonoInit, revokedMono := hInv.revokedMono
        budgetConserve := by
          dsimp only; rw [settledTotalCost_append]; simp only [settledTotalCost, buildSettledRecord]
          have := hInv.budgetConserve; omega
        consumedNodup := nodup_snoc hInv.consumedNodup hNulFresh
        settledNodup := by dsimp only; rw [List.map_append]; exact nodup_snoc hInv.settledNodup hNulNotSettled
        settledInCons := fun rec hrec => by
          dsimp only at hrec ⊢; rcases List.mem_append.mp hrec with hold | hnew
          · exact List.mem_append_left _ (hInv.settledInCons rec hold)
          · simp only [List.mem_singleton] at hnew; subst hnew
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        seqPairwise := by
          dsimp only; rw [List.map_append]; refine pairwise_lt_snoc hInv.seqPairwise fun y hy => ?_
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
          have := hInv.settledSeqBound r hr; dsimp only [buildSettledRecord]; omega
        settledSeqBound := fun rec hrec => by
          dsimp only at hrec ⊢; rcases List.mem_append.mp hrec with hold | hnew
          · have := hInv.settledSeqBound rec hold; omega
          · simp only [List.mem_singleton] at hnew; subst hnew; exact Nat.le_refl _
        settledSafe := fun rec hrec => by
          dsimp only at hrec ⊢; rcases List.mem_append.mp hrec with hold | hnew
          · exact hInv.settledSafe rec hold
          · simp only [List.mem_singleton] at hnew; subst hnew; right; dsimp only [buildSettledRecord]
            exact ⟨by have := hInv.seqMonoInit; omega, hWidths.1, hNoCbr, h100, hFlDig, hInv.floorsSub,
              fun φ hφ => (checkFloor_eq_holdsOnSettledRecord cur act φ).trans (hFloors φ hφ),
              hCopy.2, hCopy.1, hSimpComm, hSimpQc.2.2, hCust.2.1, hInv.threshEq ▸ hCust.2.2.2.2,
              fun s hs => hInv.totalEq ▸ hCust.2.2.1 s hs,
              fun s hs hInInit => hCust.2.2.2.1 s hs (hInv.revokedMono s hInInit), hTof, hInv.proxLeInit⟩ }
  | upgradeJudge _ hNonReg _ _ hEpLt _ _ =>
    exact { floorsSub := fun φ hφ => hNonReg φ (hInv.floorsSub hφ), seqMonoInit := hInv.seqMonoInit
            proxLeInit := hInv.proxLeInit, threshEq := hInv.threshEq, totalEq := hInv.totalEq
            epochMonoInit := by dsimp only; have := hInv.epochMonoInit; omega
            revokedMono := hInv.revokedMono, budgetConserve := hInv.budgetConserve
            consumedNodup := hInv.consumedNodup, settledNodup := hInv.settledNodup
            settledInCons := hInv.settledInCons, seqPairwise := hInv.seqPairwise
            settledSeqBound := hInv.settledSeqBound, settledSafe := hInv.settledSafe }
  | attenuateMandate _ _ hBudLe hProx _ =>
    exact { floorsSub := hInv.floorsSub, seqMonoInit := hInv.seqMonoInit
            proxLeInit := Nat.le_trans hProx.2 hInv.proxLeInit
            threshEq := hInv.threshEq, totalEq := hInv.totalEq, epochMonoInit := hInv.epochMonoInit
            revokedMono := fun r hr => mem_mergeRevokedCustodians.mpr (.inl (hInv.revokedMono r hr))
            budgetConserve := by dsimp only; have := hInv.budgetConserve; omega
            consumedNodup := hInv.consumedNodup, settledNodup := hInv.settledNodup
            settledInCons := hInv.settledInCons, seqPairwise := hInv.seqPairwise
            settledSeqBound := hInv.settledSeqBound, settledSafe := hInv.settledSafe }

private theorem sheTraceInv_run :
    ∀ {turns : List SheTurn} {init cur endSt : SheState},
      SheTraceInv init cur → ValidSheTrace cur turns endSt → SheTraceInv init endSt
  | [], _, _, _, hInv, hEq => hEq ▸ hInv
  | _ :: _, _, _, _, hInv, ⟨_, hStep, hRest⟩ => sheTraceInv_run (sheTraceInv_step hInv hStep) hRest

/-- **Flagship Multi-Turn Sovereign SHE Safety & Anti-Vaz Theorem (`she_trace_end_to_end_safe_and_anti_vaz`)**. -/
theorem she_trace_end_to_end_safe_and_anti_vaz
    {initState endState : SheState} {turns : List SheTurn}
    (hGenesisActions : initState.settledOutboxActions = [])
    (hGenesisNullifiers : initState.consumedNullifiers = [])
    (hTrace : ValidSheTrace initState turns endState) :
    initState.activeSafetyAndPrivacyFloors ⊆ endState.activeSafetyAndPrivacyFloors ∧
    List.Pairwise (· < ·) (endState.settledOutboxActions.map SettledActuationRecord.sensorSeq) ∧
    settledTotalCost endState.settledOutboxActions + endState.remainingMandateBudget ≤
      initState.remainingMandateBudget ∧
    (endState.settledOutboxActions.map SettledActuationRecord.nullifier).Nodup ∧
    endState.consumedNullifiers.Nodup ∧
    ∀ rec ∈ endState.settledOutboxActions,
      initState.monoSensorSeq < rec.sensorSeq ∧ rec.sensorSeq ≤ endState.monoSensorSeq ∧
      rec.sensorSealDigest.size = 32 ∧ rec.zkmlRegime ≠ .withdrawnCapacityBoundCbr ∧
      100000 ≤ rec.provenZkmlMilliBits ∧
      rec.boundFloorsDigest = floorsDigest rec.activeFloorsAtSettlement ∧
      initState.activeSafetyAndPrivacyFloors ⊆ rec.activeFloorsAtSettlement ∧
      (∀ φ ∈ initState.activeSafetyAndPrivacyFloors, holdsOnSettledRecord φ rec = true) ∧
      rec.dispatchedPayload = rec.privateFrameCopy ∧ rec.privateFrameCopy = rec.sharedRingAtCopy ∧
      3 * rec.simplexFaultyF + 1 ≤ rec.simplexCommitteeN ∧
      rec.simplexCommitteeN - rec.simplexFaultyF ≤ rec.simplexQuorumCount ∧
      rec.custodianSigners.Nodup ∧ initState.custodianThresholdT ≤ rec.custodianSigners.length ∧
      (∀ s ∈ rec.custodianSigners, s < initState.custodianTotalN) ∧
      (∀ s ∈ rec.custodianSigners, s ∉ initState.revokedCustodians) ∧
      (∀ coerced : List Nat, coerced.length < initState.custodianThresholdT →
        ∃ h ∈ rec.custodianSigners, h ∉ coerced) ∧
      rec.tofRoundTripTicks ≤ rec.maxProximityTicksAtSettle ∧
      rec.maxProximityTicksAtSettle ≤ initState.maxProximityTicks := by
  have hInitInv : SheTraceInv initState initState :=
    { floorsSub := fun _ h => h, seqMonoInit := Nat.le_refl _, proxLeInit := Nat.le_refl _
      threshEq := rfl, totalEq := rfl, epochMonoInit := Nat.le_refl _, revokedMono := fun _ h => h
      budgetConserve := Nat.le_refl _
      consumedNodup := by rw [hGenesisNullifiers]; exact List.Pairwise.nil
      settledNodup := by rw [hGenesisActions]; exact List.Pairwise.nil
      settledInCons := by rw [hGenesisActions]; intro _ h; cases h
      seqPairwise := by rw [hGenesisActions]; exact List.Pairwise.nil
      settledSeqBound := by rw [hGenesisActions]; intro _ h; cases h
      settledSafe := fun _ hr => .inl hr }
  have hEnd := sheTraceInv_run hInitInv hTrace
  have hBud : settledTotalCost endState.settledOutboxActions + endState.remainingMandateBudget ≤
      initState.remainingMandateBudget := by
    have hb := hEnd.budgetConserve; rw [hGenesisActions] at hb; simpa [settledTotalCost] using hb
  refine ⟨hEnd.floorsSub, hEnd.seqPairwise, hBud, hEnd.settledNodup, hEnd.consumedNodup, fun rec hrec => ?_⟩
  rcases hEnd.settledSafe rec hrec with hInInit | hNew
  · rw [hGenesisActions] at hInInit; cases hInInit
  · obtain ⟨hSeq, hSealSz, hNoCbr, h100, hFlDig, hFlSub, hHoldsAll, hDisp, hPriv,
            hSimp1, hSimp2, hCustNd, hCustLen, hCustRange, hCustUnrev, hTof1, hTof2⟩ := hNew
    exact ⟨hSeq, hEnd.settledSeqBound rec hrec, hSealSz, hNoCbr, h100, hFlDig, hFlSub,
      fun φ hφ => hHoldsAll φ (hFlSub hφ), hDisp, hPriv, hSimp1, hSimp2, hCustNd, hCustLen,
      hCustRange, hCustUnrev,
      fun coerced hLt => coerced_subthreshold_coalition_omits_honest_signer hCustNd hCustLen hLt,
      hTof1, hTof2⟩

theorem she_trace_coupled_sel4_private_frame_safe
    {k₀ k₁ : KState} {cfg : IngressCfg} {da₀ : Nat} {ring d : ByteArray} {mid : List KEvent}
    (hU : VUnique k₀.maps) (hP₀ : translate k₀.maps (.cpu cfg.vpd) cfg.privV true = some da₀)
    (hInv : PrivInv k₀ cfg.vpd (da₀ / pageSize) k₁)
    (hRing : readVia k₁ cfg.vpd cfg.sharedV cfg.len = some ring)
    (hCopy : (translate k₁.maps (.cpu cfg.vpd) cfg.privV true).isSome = true)
    (hAdv : ∀ ev ∈ mid, ev.actor ≠ some cfg.vpd)
    (hD : readVia (runK (ingressCopy cfg k₁) mid) cfg.vpd (dispatchVaddr cfg) cfg.len = some d)
    {initState endState : SheState} {turns : List SheTurn}
    (hGenesisActions : initState.settledOutboxActions = [])
    (hGenesisNullifiers : initState.consumedNullifiers = [])
    (hTrace : ValidSheTrace initState turns endState) :
    d = ring ∧ PrivInv k₀ cfg.vpd (da₀ / pageSize) (runK (ingressCopy cfg k₁) mid) ∧
    initState.activeSafetyAndPrivacyFloors ⊆ endState.activeSafetyAndPrivacyFloors ∧
    ∀ rec ∈ endState.settledOutboxActions,
      rec.privateFrameCopy = d → rec.dispatchedPayload = ring := by
  obtain ⟨hdRing, hPrivAfter⟩ := copy_into_private_pd_frame_before_verify hU hP₀ hInv hRing hCopy mid hAdv hD
  obtain ⟨hFloors, _, _, _, _, hRecs⟩ := she_trace_end_to_end_safe_and_anti_vaz hGenesisActions hGenesisNullifiers hTrace
  exact ⟨hdRing, hPrivAfter, hFloors, fun rec hrec hEqD =>
    (hRecs rec hrec).2.2.2.2.2.2.2.2.1.trans (hEqD.trans hdRing)⟩

/-! ## 5. `sheCeremonyJudge` (`Obend.Judge`) & Constructive Inhabitedness Witnesses -/
structure SheStateWellFormed (st : SheState) : Prop where
  judgeDigest32  : st.habitatJudgeDigest.size = 32
  weightsRoot32  : st.pinnedModelWeightsRoot.size = 32
  floorsNodup    : st.activeSafetyAndPrivacyFloors.Nodup
  hasBedrock     : ∃ φ ∈ st.activeSafetyAndPrivacyFloors, φ.isBedrock = true
  floorsWf       : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, φ.wellFormed = true
  thresholdValid : 1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN
  proximityPos   : 0 < st.maxProximityTicks

def checkSheStateWellFormed (st : SheState) : Bool :=
  decide (st.habitatJudgeDigest.size = 32) && decide (st.pinnedModelWeightsRoot.size = 32) &&
  checkFloorNodup st.activeSafetyAndPrivacyFloors && st.activeSafetyAndPrivacyFloors.any SheFloor.isBedrock &&
  st.activeSafetyAndPrivacyFloors.all SheFloor.wellFormed &&
  decide (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN) &&
  decide (0 < st.maxProximityTicks)
theorem checkSheStateWellFormed_iff (st : SheState) :
    checkSheStateWellFormed st = true ↔ SheStateWellFormed st := by
  unfold checkSheStateWellFormed
  simp only [Bool.and_eq_true, decide_eq_true_eq, checkListNodup_iff, List.any_eq_true, List.all_eq_true]
  exact ⟨fun ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩,
         fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩

inductive InductiveSheTrace : SheState → List SheTurn → SheState → Prop where
  | nil (st : SheState) : InductiveSheTrace st [] st
  | cons {st stMid stEnd : SheState} {t : SheTurn} {ts : List SheTurn} :
      InductiveSheStep st t stMid → InductiveSheTrace stMid ts stEnd → InductiveSheTrace st (t :: ts) stEnd
theorem inductiveSheTrace_iff_validSheTrace :
    ∀ {turns : List SheTurn} {st endSt : SheState},
      InductiveSheTrace st turns endSt ↔ ValidSheTrace st turns endSt
  | [], st, _ => by simp only [ValidSheTrace]; exact ⟨fun h => by cases h; rfl, fun h => h ▸ .nil st⟩
  | _ :: _, _, _ => by
    simp only [ValidSheTrace]
    exact ⟨fun h => by cases h with | cons hs hr => exact ⟨_, (applySheTurn_ok_iff_inductiveStep _ _ _).mpr hs,
             inductiveSheTrace_iff_validSheTrace.mp hr⟩,
           fun ⟨_, hOk, hr⟩ => .cons ((applySheTurn_ok_iff_inductiveStep _ _ _).mp hOk)
             (inductiveSheTrace_iff_validSheTrace.mpr hr)⟩

structure SheCeremonyObj where
  initState : SheState
  turns : List SheTurn
  targetFloors : List SheFloor
structure CeremonyMeaning (o : SheCeremonyObj) (endSt : SheState) : Prop where
  wfInit : SheStateWellFormed o.initState
  validTrace : InductiveSheTrace o.initState o.turns endSt
  achievesFloors : ∀ φ ∈ o.targetFloors, φ ∈ endSt.activeSafetyAndPrivacyFloors

def sheRefusalRefutes : SheRefusal → Bool | .terminalStateMismatch => false | _ => true
def checkSheCeremony (grade : Nat) (o : SheCeremonyObj) (certEnd : SheState) : Judge.Verdict SheRefusal :=
  if grade < o.turns.length then .uncovered
  else if !checkSheStateWellFormed o.initState then .refused .malformedInitialState []
  else match runSheTurns o.initState o.turns with
    | .error (stepIdx, r) =>
      .refused (match r with | .terminalStateMismatch => .malformedInitialState | other => other) [stepIdx]
    | .ok computedEnd =>
      match o.targetFloors.find? (fun φ => !computedEnd.activeSafetyAndPrivacyFloors.contains φ) with
      | some missing => .refused (.missingTargetFloor missing) []
      | none => if computedEnd == certEnd then .ok else .refused .terminalStateMismatch []

instance sheCeremonyJudge : Judge SheCeremonyObj SheState where
  Clause := SheRefusal
  Meaning := CeremonyMeaning
  check := checkSheCeremony
  sound {r o c} h := by
    unfold checkSheCeremony at h; split at h; · cases h
    split at h; · cases h
    rename_i hNotWf
    have hWfBool : checkSheStateWellFormed o.initState = true := by
      cases hw : checkSheStateWellFormed o.initState with | true => rfl | false => simp [hw] at hNotWf
    cases hRun : runSheTurns o.initState o.turns with
    | error _ => rw [hRun] at h; cases h
    | ok compEnd =>
      rw [hRun] at h; dsimp only at h
      cases hMiss : o.targetFloors.find? (fun φ => !compEnd.activeSafetyAndPrivacyFloors.contains φ) with
      | some _ => rw [hMiss] at h; cases h
      | none =>
        rw [hMiss] at h; dsimp only at h; cases hEq : compEnd == c with
        | false => simp [hEq] at h
        | true =>
          have hCompEq := beq_iff_eq.mp hEq; subst hCompEq
          refine ⟨(checkSheStateWellFormed_iff _).mp hWfBool,
            inductiveSheTrace_iff_validSheTrace.mpr ((runSheTurns_ok_iff _ _ _).mp hRun), fun φ hφ => ?_⟩
          have hf := List.find?_eq_none.mp hMiss φ hφ
          cases hc : compEnd.activeSafetyAndPrivacyFloors.contains φ with
          | true => exact List.contains_iff_mem.mp hc | false => rw [hc] at hf; exact absurd rfl hf
  refutes := sheRefusalRefutes
  refuted {r o c k p} h hr c' hm := by
    unfold checkSheCeremony at h; split at h; · cases h
    split at h
    · rename_i hNotWf; simp [(checkSheStateWellFormed_iff _).mpr hm.wfInit] at hNotWf
    · rw [(runSheTurns_ok_iff _ _ _).mpr (inductiveSheTrace_iff_validSheTrace.mp hm.validTrace)] at h; dsimp only at h
      cases hMiss : o.targetFloors.find? (fun φ => !c'.activeSafetyAndPrivacyFloors.contains φ) with
      | some missing =>
        have hPred := List.find?_some hMiss
        rw [List.contains_iff_mem.mpr (hm.achievesFloors missing (List.mem_of_find?_eq_some hMiss))] at hPred
        cases hPred
      | none => rw [hMiss] at h; dsimp only at h; split at h <;> (cases h; try simp [sheRefusalRefutes] at hr)
  Fragment o := SheStateWellFormed o.initState
  complete {o} hFrag hEx := by
    obtain ⟨endSt, hm⟩ := hEx; refine ⟨endSt, o.turns.length, ?_⟩; unfold checkSheCeremony
    have hMiss : o.targetFloors.find? (fun φ => !endSt.activeSafetyAndPrivacyFloors.contains φ) = none :=
      List.find?_eq_none.mpr fun φ hφ => by rw [List.contains_iff_mem.mpr (hm.achievesFloors φ hφ)]; decide
    simp only [Nat.lt_irrefl, ↓reduceIte, (checkSheStateWellFormed_iff _).mpr hFrag, Bool.not_true]
    rw [(runSheTurns_ok_iff _ _ _).mpr (inductiveSheTrace_iff_validSheTrace.mp hm.validTrace)]; dsimp only
    rw [hMiss]; simp
  mono {r r' o c} hle hdec := by
    unfold checkSheCeremony at hdec ⊢; cases Nat.decLt r o.turns.length with
    | isTrue hlt => simp [hlt] at hdec
    | isFalse hlt => have hlt' : ¬ r' < o.turns.length := by omega
                     simp [hlt, hlt']
theorem checkSheCeremony_refutes_sound (grade : Nat) (o : SheCeremonyObj) (certEnd c' : SheState)
    (k : SheRefusal) (p : List Nat) (h : checkSheCeremony grade o certEnd = .refused k p)
    (hr : sheRefusalRefutes k = true) : ¬ CeremonyMeaning o c' := sheCeremonyJudge.refuted h hr c'
theorem sheRefusalRefutes_inhabited (φ : SheFloor) : sheRefusalRefutes (.coerciveFloorDowngrade φ) = true := by rfl
private def sampleBytes32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩
private theorem sampleBytes32_size (b : UInt8) : (sampleBytes32 b).size = 32 := by simp [sampleBytes32, ByteArray.size]
def canonicalGenesisFloors : List SheFloor :=
  [ .sensorRoiRedaction 2, .consentBandNonOcclusion 32, .zkmlProvenSoundnessMilliBits 100000
  , .physicalProximityMaxTicks 50, .e2eeTeeChannelBound 1, .operatorLocalRevert 8 ]
def canonicalGenesisSheState (extraBudget : Nat) : SheState :=
  { habitatJudgeDigest := sampleBytes32 0x10, pinnedModelWeightsRoot := sampleBytes32 0x22
    monoSensorSeq := 0, consumedNullifiers := [], remainingMandateBudget := 100 + extraBudget
    activeSafetyAndPrivacyFloors := canonicalGenesisFloors, settledOutboxActions := []
    custodianThresholdT := 3, custodianTotalN := 5, custodianQuorumEpoch := 1
    revokedCustodians := [], maxProximityTicks := 50, revertWindowSteps := 4 }
theorem sheCeremonyJudge_fragment_inhabited (extraBudget : Nat) :
    SheStateWellFormed (canonicalGenesisSheState extraBudget) := by
  apply (checkSheStateWellFormed_iff _).mp
  simp [checkSheStateWellFormed, canonicalGenesisSheState, canonicalGenesisFloors,
    sampleBytes32_size, checkFloorNodup, checkListNodup, SheFloor.isBedrock, SheFloor.wellFormed]

private def sampleAct1 (flDig payDig pay : ByteArray) : ActuationTurnProposal :=
  { sensorSeq := 1, sensorSealDigest := sampleBytes32 0x33, nullifier := sampleBytes32 0x44, mandateCost := 25
    candidate := { statementDigest := sampleBytes32 0x11, modelWeightsRoot := sampleBytes32 0x22
                   boundFloorsDigest := flDig, sensorSealDigest := sampleBytes32 0x33, actionPayloadDigest := payDig
                   regime := .uniqueDecodingUdr, logBlowup := 6, numQueries := 86, grindBits := 16
                   extFieldBits := 100, proofVerified := true }
    redactedRoiCount := 3, consentBandHeightPx := 40, attestedGpuCount := 2, sharedRingAtCopy := pay
    privateFrameCopy := pay, dispatchedPayload := pay, simplexCommitteeN := 4, simplexFaultyF := 1
    simplexFinalizeSigners := [0, 1, 2], custodianEpoch := 1, custodianSigners := [0, 2, 3], tofRoundTripTicks := 18 }
private theorem sampleAct1_step (extraBudget : Nat) (flDig payDig pay : ByteArray)
    (hFlSz : flDig.size = 32) (hPaySz : payDig.size = 32)
    (hFlEq : flDig = floorsDigest canonicalGenesisFloors) (hPayEq : payDig = shePayloadDigest pay) :
    let st₀ := canonicalGenesisSheState extraBudget; let act₁ := sampleAct1 flDig payDig pay
    applySheTurn st₀ (.proposeAndSettleActuation act₁) = .ok
      { st₀ with monoSensorSeq := 1, consumedNullifiers := [sampleBytes32 0x44]
                 remainingMandateBudget := 100 + extraBudget - 25, settledOutboxActions := [buildSettledRecord st₀ act₁] } := by
  dsimp only; have h100 : 100000 ≤ provenZkmlMilliBits (sampleAct1 flDig payDig pay).candidate := by
    dsimp only [sampleAct1, provenZkmlMilliBits, udrPerQueryMilliBits]
    have hIf : (!true || (6 == 0) || (86 == 0)) = false := rfl; rw [hIf]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine Nat.le_min.mpr ⟨?_, Nat.le_min.mpr ⟨by omega, by omega⟩⟩; rw [show Nat.min 16 24 = 16 by decide]; omega
  refine (applySheTurn_ok_iff_inductiveStep _ _ _).mpr (.settleActuation _ _
    ⟨sampleBytes32_size _, sampleBytes32_size _, sampleBytes32_size _, hFlSz, sampleBytes32_size _, hPaySz, sampleBytes32_size _⟩
    (by dsimp [sampleAct1, canonicalGenesisSheState]; omega) rfl rfl (fun h => nomatch h) h100 rfl hFlEq hPayEq
    (by dsimp [sampleAct1, canonicalGenesisSheState]; omega) ?_
    (by simp [canonicalGenesisSheState]) (by dsimp [sampleAct1, canonicalGenesisSheState]; omega) ⟨rfl, rfl⟩
    (by dsimp [sampleAct1]; omega) ⟨(checkListNodup_iff [0, 1, 2]).mp (by decide), by simp [sampleAct1], by dsimp [sampleAct1]; omega⟩ rfl
    ⟨by dsimp [canonicalGenesisSheState]; omega, (checkListNodup_iff [0, 2, 3]).mp (by decide),
     by simp [sampleAct1, canonicalGenesisSheState], by simp [canonicalGenesisSheState], by dsimp [sampleAct1, canonicalGenesisSheState]; omega⟩)
  intro φ hφ; simp only [canonicalGenesisSheState, canonicalGenesisFloors, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact decide_eq_true_eq.mpr h100 | exact decide_eq_true_eq.mpr (by dsimp [sampleAct1, canonicalGenesisSheState]; omega)
theorem validSheTrace_multiTurn_inhabited (extraBudget : Nat) :
    ∃ (turns : List SheTurn) (endState : SheState),
      turns.length = 3 ∧ ValidSheTrace (canonicalGenesisSheState extraBudget) turns endState ∧
      endState.settledOutboxActions.length = 1 ∧ endState.custodianQuorumEpoch = 2 := by
  let st₀ := canonicalGenesisSheState extraBudget; let pay : ByteArray := ⟨#[0x41, 0x43, 0x54, 0x31]⟩
  let act₁ := sampleAct1 (floorsDigest canonicalGenesisFloors) (shePayloadDigest pay) pay
  let st₁ : SheState := { st₀ with monoSensorSeq := 1, consumedNullifiers := [sampleBytes32 0x44]
                                   remainingMandateBudget := 100 + extraBudget - 25, settledOutboxActions := [buildSettledRecord st₀ act₁] }
  let up₂ : UpgradeJudgeProposal := { newJudgeDigest := sampleBytes32 0x55, newModelWeightsRoot := sampleBytes32 0x22
                                      newFloors := canonicalGenesisFloors ++ [.sensorRoiRedaction 4], newRevertWindowSteps := 6
                                      newCustodianEpoch := 2, custodianSigners := [0, 1, 3], tofRoundTripTicks := 15, authorityClaim := .localCustodianCeremony }
  let st₂ : SheState := { st₁ with habitatJudgeDigest := sampleBytes32 0x55, revertWindowSteps := 6, custodianQuorumEpoch := 2
                                   pinnedModelWeightsRoot := sampleBytes32 0x22, activeSafetyAndPrivacyFloors := canonicalGenesisFloors ++ [.sensorRoiRedaction 4] }
  let rev₃ : MandateAttenuation := { newBudgetCap := 50, newMaxProximityTicks := 30, newlyRevokedCustodians := [4], reasonDigest := sampleBytes32 0x66 }
  have hs₁ : applySheTurn st₀ (.proposeAndSettleActuation act₁) = .ok st₁ :=
    sampleAct1_step extraBudget _ _ pay (floorsDigest_size _) (shePayloadDigest_size _) rfl rfl
  have hs₂ : applySheTurn st₁ (.upgradeHabitatJudge up₂) = .ok st₂ := by
    refine (applySheTurn_ok_iff_inductiveStep _ _ _).mpr (.upgradeJudge st₁ up₂ (fun φ hφ => List.mem_append_left _ hφ)
      ⟨sampleBytes32_size _, sampleBytes32_size _⟩
      ⟨(checkListNodup_iff _).mp (by dsimp [up₂, canonicalGenesisFloors]; decide), ⟨.operatorLocalRevert 8, by simp [up₂, canonicalGenesisFloors], rfl⟩, ?_, ?_⟩
      (by dsimp [st₁, st₀, up₂, canonicalGenesisSheState]; omega)
      ⟨by dsimp [st₁, st₀, canonicalGenesisSheState]; omega, (checkListNodup_iff _).mp (by decide),
       by simp [st₁, st₀, up₂, canonicalGenesisSheState], by simp [st₁, st₀, canonicalGenesisSheState], by dsimp [st₁, st₀, up₂, canonicalGenesisSheState]; omega⟩
      (by dsimp [st₁, st₀, up₂, canonicalGenesisSheState]; omega))
    · intro φ hφ; simp only [up₂, canonicalGenesisFloors, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;> first | rfl | exact decide_eq_true_eq.mpr (by dsimp [SheFloor.wellFormed]; omega)
    · intro φ hφ; simp only [up₂, canonicalGenesisFloors, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;> first | rfl | exact decide_eq_true_eq.mpr (by dsimp [up₂]; omega)
  have hs₃ : applySheTurn st₂ (.revokeOrAttenuateMandate rev₃) = .ok
      { st₂ with remainingMandateBudget := 50, maxProximityTicks := 30, revokedCustodians := mergeRevokedCustodians st₂.revokedCustodians [4] } := by
    refine (applySheTurn_ok_iff_inductiveStep _ _ _).mpr (.attenuateMandate st₂ rev₃ (sampleBytes32_size _) ?_
      (by dsimp [st₂, st₁, st₀, rev₃, canonicalGenesisSheState]; omega) (by simp [st₂, st₁, st₀, rev₃, canonicalGenesisSheState]))
    dsimp [st₂, st₁, st₀, rev₃, canonicalGenesisSheState]; omega
  exact ⟨[.proposeAndSettleActuation act₁, .upgradeHabitatJudge up₂, .revokeOrAttenuateMandate rev₃], _, rfl, ⟨st₁, hs₁, ⟨st₂, hs₂, ⟨_, hs₃, rfl⟩⟩⟩, rfl, rfl⟩

end Obend.Polis.SecureHardwareEnv
end
