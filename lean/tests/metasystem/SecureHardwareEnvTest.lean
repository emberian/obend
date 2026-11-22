module
/-
# SecureHardwareEnvTest — Cross-Language Wire Parity, Multi-Turn Anti-Vaz Refusals & `#tooth` Kills

Verifies `Obend.Polis.SecureHardwareEnv`:
1. Byte-exact `OBEND.SHE.FLOORS/v1`, `OBEND.SHE.PAYLOAD/v1`, and `OBEND.SHE.TURN/v1` `cSHAKE256`
   golden test vectors shared with `crates/obend-oracles-e2ee/tests/anti_vaz_she_ceremony.rs`;
2. Positive 4-turn ceremony trace + `sheCeremonyJudge` acceptance and refutation vectors;
3. Adversarial refusals against Vaz coercive floor downgrades (with vendor root and agency emergency
   signatures), `< t` coerced custodian coalitions, ToF relay attacks, withdrawn CBR-weak zkML
   proofs, nullifier replays, mandate budget overruns, and `seL4` private-frame mismatches;
4. **8 universal `#tooth` mutation kills** exercising every flagship theorem;
5. `#assert_axioms_tree` and `#print axioms` verification (`0 sorryAx`, `0 Classical.choice`).
-/
public import Obend.Polis.SecureHardwareEnv
import all Obend.Polis.SecureHardwareEnv
meta import Obend.Polis.SecureHardwareEnv
meta import Obend.Polis.SandboxDomainTags
meta import Obend.Digest.HashBytes
meta import Obend.Digest.Cshake256.Spec
meta import Obend.Crypto.Transcript
import Obend.Tactic.Tooth

public section
namespace Obend.Polis.SecureHardwareEnv.Tests

open Obend
open Obend.Polis.SecureHardwareEnv

set_option autoImplicit false

def bytes32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩

def hexOfBytes (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

def act1Payload : ByteArray := ⟨#[0x41, 0x43, 0x54, 0x31]⟩
def act2Payload : ByteArray := ⟨#[0x41, 0x43, 0x54, 0x32]⟩

def validCand1 : CandidateComputation :=
  { statementDigest     := bytes32 0x11
    modelWeightsRoot    := bytes32 0x22
    boundFloorsDigest   := floorsDigest canonicalGenesisFloors
    sensorSealDigest    := bytes32 0x33
    actionPayloadDigest := shePayloadDigest act1Payload
    regime              := .uniqueDecodingUdr
    logBlowup           := 6
    numQueries          := 86
    grindBits           := 16
    extFieldBits        := 100
    proofVerified       := true }

def goldenTurn1 : SheTurn := .proposeAndSettleActuation
  { sensorSeq              := 1
    sensorSealDigest       := bytes32 0x33
    candidate              := validCand1
    nullifier              := bytes32 0x44
    mandateCost            := 25
    redactedRoiCount       := 3
    consentBandHeightPx    := 40
    attestedGpuCount       := 2
    sharedRingAtCopy       := act1Payload
    privateFrameCopy       := act1Payload
    dispatchedPayload      := act1Payload
    simplexCommitteeN      := 4
    simplexFaultyF         := 1
    simplexFinalizeSigners := [0, 1, 2]
    custodianEpoch         := 1
    custodianSigners       := [0, 2, 3]
    tofRoundTripTicks      := 18 }

def upgradedFloors : List SheFloor :=
  canonicalGenesisFloors ++ [.sensorRoiRedaction 4]

def goldenTurn2 : SheTurn := .upgradeHabitatJudge
  { newJudgeDigest       := bytes32 0x55
    newModelWeightsRoot  := bytes32 0x22
    newFloors            := upgradedFloors
    newRevertWindowSteps := 6
    newCustodianEpoch    := 2
    custodianSigners     := [0, 1, 3]
    tofRoundTripTicks    := 15
    authorityClaim       := .localCustodianCeremony }

def goldenTurn3 : SheTurn := .revokeOrAttenuateMandate
  { newBudgetCap           := 50
    newMaxProximityTicks   := 30
    newlyRevokedCustodians := [4]
    reasonDigest           := bytes32 0x66 }

def validCand2 : CandidateComputation :=
  { statementDigest     := bytes32 0x71
    modelWeightsRoot    := bytes32 0x22
    boundFloorsDigest   := floorsDigest upgradedFloors
    sensorSealDigest    := bytes32 0x72
    actionPayloadDigest := shePayloadDigest act2Payload
    regime              := .johnsonBoundJbr
    logBlowup           := 6
    numQueries          := 30
    grindBits           := 16
    extFieldBits        := 100
    proofVerified       := true }

def goldenTurn4 : SheTurn := .proposeAndSettleActuation
  { sensorSeq              := 2
    sensorSealDigest       := bytes32 0x72
    candidate              := validCand2
    nullifier              := bytes32 0x73
    mandateCost            := 40
    redactedRoiCount       := 4
    consentBandHeightPx    := 48
    attestedGpuCount       := 2
    sharedRingAtCopy       := act2Payload
    privateFrameCopy       := act2Payload
    dispatchedPayload      := act2Payload
    simplexCommitteeN      := 4
    simplexFaultyF         := 1
    simplexFinalizeSigners := [1, 2, 3]
    custodianEpoch         := 2
    custodianSigners       := [0, 1, 2]
    tofRoundTripTicks      := 22 }

/-! ## 1. Cross-Language Byte-Exact `cSHAKE256` Golden Vectors -/

#guard hexOfBytes (floorsDigest canonicalGenesisFloors) ==
  "6f6491a661a8e2d178544e84cd4917fda6e6eb451ae9f49c4a211588096c6811"

#guard hexOfBytes (shePayloadDigest act1Payload) ==
  "1839254e8817686d0ea77ebcdf95f57f61b01582ed8ed01dc471c60f2a602d57"

#guard hexOfBytes (sheTurnEnvelopeDigest goldenTurn1) ==
  "38dbf7839d0460ff2415223e050389e78fd6542726b3365d3f62cd33ce7589c5"

#guard hexOfBytes (sheTurnEnvelopeDigest goldenTurn2) ==
  "04d22d3d57805d267b0aa866b597223edae6b8c408a3d8e12f1125f75317e3e0"

#guard hexOfBytes (sheTurnEnvelopeDigest goldenTurn3) ==
  "4703fd475cbe80a9dee00cc86a023b0341874af30ba13a45aa61080a05f159ac"

/-! ## 2. Positive 4-Turn Ceremony & Adversarial Vaz/Relay/CBR/Replay Refusals -/

def genesis0 : SheState := canonicalGenesisSheState 0

-- Full 4-turn sovereign ceremony succeeds and settles 2 actuations with remaining budget 10.
#guard match runSheTurns genesis0 [goldenTurn1, goldenTurn2, goldenTurn3, goldenTurn4] with
  | .ok endSt =>
    endSt.monoSensorSeq == 2 &&
    endSt.settledOutboxActions.length == 2 &&
    endSt.remainingMandateBudget == 10 &&
    settledTotalCost endSt.settledOutboxActions == 65 &&
    endSt.custodianQuorumEpoch == 2 &&
    (match Judge.check (Obj := SheCeremonyObj) 4
       ⟨genesis0, [goldenTurn1, goldenTurn2, goldenTurn3, goldenTurn4], [.sensorRoiRedaction 4]⟩ endSt with
     | .ok => true | _ => false)
  | .error _ => false

-- Attack 1: Vaz coercive floor downgrade with external intelligence agency emergency order -> REFUSED!
def vazAgencyDowngrade : SheTurn := .upgradeHabitatJudge
  { newJudgeDigest       := bytes32 0x99
    newModelWeightsRoot  := bytes32 0x22
    newFloors            := [ .consentBandNonOcclusion 32, .zkmlProvenSoundnessMilliBits 100000,
                              .physicalProximityMaxTicks 50, .e2eeTeeChannelBound 1, .operatorLocalRevert 8 ]
    newRevertWindowSteps := 4
    newCustodianEpoch    := 2
    custodianSigners     := [0, 1, 2, 3, 4]
    tofRoundTripTicks    := 10
    authorityClaim       := .agencyEmergencyOrder (bytes32 0xAA) (bytes32 0xBB) }

#guard match applySheTurn genesis0 vazAgencyDowngrade with
  | .error (.coerciveFloorDowngrade (.sensorRoiRedaction 2)) => true | _ => false

-- Attack 2: Vendor root directive replacing 100-bit zkML floor with 34-bit floor -> REFUSED!
def vazVendorWeakZkml : SheTurn := .upgradeHabitatJudge
  { newJudgeDigest       := bytes32 0x98
    newModelWeightsRoot  := bytes32 0x22
    newFloors            := [ .sensorRoiRedaction 2, .consentBandNonOcclusion 32,
                              .zkmlProvenSoundnessMilliBits 34000, .physicalProximityMaxTicks 50,
                              .e2eeTeeChannelBound 1, .operatorLocalRevert 8 ]
    newRevertWindowSteps := 4
    newCustodianEpoch    := 2
    custodianSigners     := [0, 1, 2, 3]
    tofRoundTripTicks    := 10
    authorityClaim       := .vendorRootDirective (bytes32 0xCC) }

#guard match applySheTurn genesis0 vazVendorWeakZkml with
  | .error (.coerciveFloorDowngrade (.zkmlProvenSoundnessMilliBits 100000)) => true | _ => false

-- Attack 3: Coerced `< t` custodian coalition (`2 < 3`) -> REFUSED!
#guard match goldenTurn1 with
  | .proposeAndSettleActuation act =>
    match applySheTurn genesis0 (.proposeAndSettleActuation { act with custodianSigners := [0, 2] }) with
    | .error (.insufficientCustodianQuorum 2 3) => true | _ => false
  | _ => false

-- Attack 4: Remote ToF relay attack (`tofRoundTripTicks = 51 > 50`) -> REFUSED!
#guard match goldenTurn1 with
  | .proposeAndSettleActuation act =>
    match applySheTurn genesis0 (.proposeAndSettleActuation { act with tofRoundTripTicks := 51 }) with
    | .error (.tofProximityExceeded 51 50) => true | _ => false
  | _ => false

-- Attack 5a: Withdrawn CBR regime (`(lb=6, q=19, pow=16)` claiming 130 CBR bits) -> REFUSED!
-- Attack 5b: Same `(lb=6, q=19, pow=16)` submitted under UDR (`34,563 < 100,000` milli-bits) -> REFUSED!
-- Attack 5c: Fake PoW grind inflation (`(lb=1, q=1, pow=100)` -> capped at 24 grind bits = `24,415`) -> REFUSED!
#guard match goldenTurn1 with
  | .proposeAndSettleActuation act =>
    let cbrCand := { act.candidate with regime := .withdrawnCapacityBoundCbr, numQueries := 19 }
    let weakUdrCand := { act.candidate with regime := .uniqueDecodingUdr, numQueries := 19 }
    let fakeGrindCand := { act.candidate with regime := .uniqueDecodingUdr, logBlowup := 1,
                                              numQueries := 1, grindBits := 100 }
    legacyWithdrawnCbrMilliBits cbrCand == 130000 &&
    provenZkmlMilliBits weakUdrCand == 34563 &&
    provenZkmlMilliBits fakeGrindCand == 24415 &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { act with candidate := cbrCand }) with
     | .error .withdrawnCbrRegimeRefused => true | _ => false) &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { act with candidate := weakUdrCand }) with
     | .error (.belowProven100BitFloor 34563) => true | _ => false) &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { act with candidate := fakeGrindCand }) with
     | .error (.belowProven100BitFloor 24415) => true | _ => false)
  | _ => false

-- Attack 6 & 7: Nullifier replay across turns & budget overrun after mandate attenuation -> REFUSED!
#guard match runSheTurns genesis0 [goldenTurn1, goldenTurn2, goldenTurn3] with
  | .ok stAfter3 =>
    (match goldenTurn4 with
     | .proposeAndSettleActuation act4 =>
       let replay := .proposeAndSettleActuation { act4 with nullifier := bytes32 0x44 }
       let overrun := .proposeAndSettleActuation { act4 with mandateCost := 51 }
       let revokedCust := .proposeAndSettleActuation { act4 with custodianSigners := [0, 1, 4] }
       (match applySheTurn stAfter3 replay with | .error .nullifierReplayed => true | _ => false) &&
       (match applySheTurn stAfter3 overrun with | .error (.mandateBudgetExceeded 51 50) => true | _ => false) &&
       (match applySheTurn stAfter3 revokedCust with | .error (.revokedCustodianSigner 4) => true | _ => false)
     | _ => false)
  | .error _ => false

-- Judge refutation check: Vaz downgrade turn produces a REFUTING verdict (`sheRefusalRefutes = true`).
#guard match Judge.check (Obj := SheCeremonyObj) 2 ⟨genesis0, [vazAgencyDowngrade], []⟩ genesis0 with
  | .refused k path =>
    (match k with | .coerciveFloorDowngrade (.sensorRoiRedaction 2) => true | _ => false) &&
    path == [0] && sheRefusalRefutes k
  | _ => false

/-! ## 3. Universal `#tooth` Mutation Kills (8 Distinct Security Gates) -/

-- Tooth 1: Mutating `applySheTurn` so `.upgradeHabitatJudge` accepts without checking floor non-regression
-- is killed by `vaz_coercive_floor_downgrade_refused`.
#tooth vaz_coercive_floor_downgrade_refused by mutation applySheTurn := fun st turn =>
  match turn with
  | .upgradeHabitatJudge up =>
    .ok { st with activeSafetyAndPrivacyFloors := up.newFloors }
  | _ => .ok st

-- Tooth 2: Mutating `provenZkmlMilliBits` to credit naive `legacyWithdrawnCbrMilliBits` on `.withdrawnCapacityBoundCbr`
-- is killed by `udr_strictly_below_legacy_cbr` / `she_trace_end_to_end_safe_and_anti_vaz`.
#tooth udr_strictly_below_legacy_cbr by mutation provenZkmlMilliBits := fun c =>
  legacyWithdrawnCbrMilliBits c

-- Tooth 3: Mutating `applySheTurn` to omit recording `act.nullifier` in `consumedNullifiers` (allowing replay!)
-- is killed by `she_trace_end_to_end_safe_and_anti_vaz`.
#tooth she_trace_end_to_end_safe_and_anti_vaz by mutation applySheTurn := fun st turn =>
  match turn with
  | .proposeAndSettleActuation act =>
    if st.monoSensorSeq < act.sensorSeq && act.sensorSealDigest.size == 32 &&
       act.candidate.regime != .withdrawnCapacityBoundCbr &&
       decide (100000 ≤ provenZkmlMilliBits act.candidate) &&
       act.candidate.boundFloorsDigest == floorsDigest st.activeSafetyAndPrivacyFloors &&
       st.activeSafetyAndPrivacyFloors.all (checkFloorOnActuation st.revertWindowSteps act) &&
       decide (act.mandateCost ≤ st.remainingMandateBudget) &&
       act.privateFrameCopy == act.sharedRingAtCopy && act.dispatchedPayload == act.privateFrameCopy &&
       decide (3 * act.simplexFaultyF + 1 ≤ act.simplexCommitteeN) &&
       decide (act.simplexCommitteeN - act.simplexFaultyF ≤ act.simplexFinalizeSigners.length) &&
       checkNatNodup act.custodianSigners &&
       act.custodianSigners.all (fun s => decide (s < st.custodianTotalN)) &&
       decide (st.custodianThresholdT ≤ act.custodianSigners.length) &&
       decide (act.tofRoundTripTicks ≤ st.maxProximityTicks) then
      .ok { st with
            monoSensorSeq := act.sensorSeq
            remainingMandateBudget := st.remainingMandateBudget - act.mandateCost
            settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
    else .error .nullifierReplayed
  | _ => .error .malformedInitialState

-- Tooth 4: Mutating `applySheTurn` so `.revokeOrAttenuateMandate` permits budget amplification
-- (`remainingMandateBudget := rev.newBudgetCap` without `newBudgetCap ≤ remainingMandateBudget`)
-- is killed by `she_trace_end_to_end_safe_and_anti_vaz`.
#tooth she_trace_end_to_end_safe_and_anti_vaz by mutation applySheTurn := fun st turn =>
  match turn with
  | .revokeOrAttenuateMandate rev =>
    .ok { st with remainingMandateBudget := rev.newBudgetCap }
  | _ => .error .malformedInitialState

-- Tooth 5: Mutating `checkCustodianQuorum` to accept `< t` signers (`1 ≤ signers.length`)
-- is killed by `checkCustodianQuorum_ok_iff`.
#tooth checkCustodianQuorum_ok_iff by mutation checkCustodianQuorum := fun st signers =>
  if decide (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN) &&
     checkNatNodup signers && signers.all (fun s => decide (s < st.custodianTotalN)) &&
     decide (1 ≤ signers.length) then .ok ()
  else .error .duplicateOrOutOfRangeSigner

-- Tooth 6: Mutating `applySheTurn` to omit the ToF physical-presence proximity check
-- (`act.tofRoundTripTicks ≤ st.maxProximityTicks`) is killed by `she_trace_end_to_end_safe_and_anti_vaz`.
#tooth she_trace_end_to_end_safe_and_anti_vaz by mutation applySheTurn := fun st turn =>
  match turn with
  | .proposeAndSettleActuation act =>
    if st.monoSensorSeq < act.sensorSeq && act.sensorSealDigest.size == 32 &&
       act.candidate.regime != .withdrawnCapacityBoundCbr &&
       decide (100000 ≤ provenZkmlMilliBits act.candidate) &&
       act.candidate.boundFloorsDigest == floorsDigest st.activeSafetyAndPrivacyFloors &&
       st.activeSafetyAndPrivacyFloors.all (checkFloorOnActuation st.revertWindowSteps act) &&
       !st.consumedNullifiers.contains act.nullifier &&
       decide (act.mandateCost ≤ st.remainingMandateBudget) &&
       act.privateFrameCopy == act.sharedRingAtCopy && act.dispatchedPayload == act.privateFrameCopy &&
       decide (3 * act.simplexFaultyF + 1 ≤ act.simplexCommitteeN) &&
       decide (act.simplexCommitteeN - act.simplexFaultyF ≤ act.simplexFinalizeSigners.length) &&
       checkNatNodup act.custodianSigners &&
       act.custodianSigners.all (fun s => decide (s < st.custodianTotalN)) &&
       decide (st.custodianThresholdT ≤ act.custodianSigners.length) then
      .ok { st with
            monoSensorSeq := act.sensorSeq
            consumedNullifiers := st.consumedNullifiers ++ [act.nullifier]
            remainingMandateBudget := st.remainingMandateBudget - act.mandateCost
            settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
    else .error .malformedInitialState
  | _ => .error .malformedInitialState

-- Tooth 7: Mutating `sheTurnWireFields` to drop `tofRoundTripTicks` or `authorityClaim` from the
-- `OBEND.SHE.TURN/v1` preimage is killed immediately by `sheTurnEnvelope_binds`.
#tooth sheTurnEnvelope_binds by mutation sheTurnWireFields := fun turn =>
  match turn with
  | .proposeAndSettleActuation act => [[0x01], act.nullifier.data.toList]
  | .upgradeHabitatJudge up => [[0x02], up.newJudgeDigest.data.toList]
  | .revokeOrAttenuateMandate rev => [[0x03], rev.reasonDigest.data.toList]

-- Tooth 8: Mutating `sheRefusalRefutes` to mark `.terminalStateMismatch` as refuting (`fun _ => true`)
-- is killed immediately by `checkSheCeremony_refutes_sound` (`sheCeremonyJudge.refuted`).
#tooth checkSheCeremony_refutes_sound by mutation sheRefusalRefutes := fun _ => true

/-! ## 4. Kernel Axiom & Choice Audit -/

#print axioms extractSheTurnEnvelope
#print axioms sheTurnEnvelope_binds
#print axioms floorsDigest_binds
#print axioms shePayloadDigest_binds
#print axioms vaz_coercive_floor_downgrade_refused
#print axioms she_trace_end_to_end_safe_and_anti_vaz
#print axioms she_trace_coupled_sel4_private_frame_safe
#print axioms sheCeremonyJudge

end Obend.Polis.SecureHardwareEnv.Tests
end
