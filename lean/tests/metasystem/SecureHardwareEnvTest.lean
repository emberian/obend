module
/-
# SecureHardwareEnvTest — Cross-Language Wire Parity, Grounded `UD-100` + `fpaudit` (`s8 × E2M1`) + 256-Bit PQ Ceremony & `#tooth` Kills

Verifies `Obend.Polis.SecureHardwareEnv`:
1. Byte-exact `OBEND.SHE.FLOORS/v1`, `OBEND.SHE.PAYLOAD/v1`, `OBEND.SHE.ZKML_SUITE/v1`,
   `OBEND.SHE.FPAUDIT_WEIGHTS/v1`, `OBEND.SHE.STATE/v1`, `OBEND.SHE.CUSTODIAN_SIG/v1`,
   `OBEND.SHE.SIMPLEX_QC/v1`, `OBEND.PQ.SUITE.CSHAKE256/v1` (256-bit `w=4, ell1=128`), and
   `OBEND.SHE.TURN/v1` `cSHAKE256` vectors shared byte-for-byte with
   `crates/obend-oracles-e2ee/tests/anti_vaz_she_ceremony.rs`;
2. Grounded `ZkmlSuiteArtifact` (`UD-100` small `(lb=6, q=86, pow=16)` = `100,022` mbit and
   wide-leaf `(lb=2, q=148, pow=0)` = `100,344` mbit) + bit-exact `s8 × E2M1` (`MXFP4`)
   commit-before-coin sampled recompute audit (`fpaudit`), including tolerance-vs-exact
   steering separation, commit-after-coin refusal, non-`E2M1` / out-of-`s8` refusal,
   unpinned `observedNumQueries`, `logArity = 0`, and withdrawn `CBR` refusal;
3. Positive 4-turn ceremony with REAL 256-bit `cshake256Suite` `TSW` (`WOTS+C`, `w=4, ell1=128`)
   + `XMSS` signatures and refusal of weak 16-bit `compactLeanSigParams`, forged/replayed PQ
   signatures, reused stateful XMSS leaves, Vaz coercive floor downgrades, `< t` coalitions,
   ToF relays, nullifier replays, budget overruns, and `seL4` frame mismatches;
4. **12 universal `#tooth` mutation kills** exercising every flagship security gate;
5. `#print axioms` verification (`0 sorryAx`, `0 Classical.choice`).
-/
public import Obend.Polis.SecureHardwareEnv
import all Obend.Polis.SecureHardwareEnv
import all Obend.Crypto.PqHashSignatures
meta import Obend.Polis.SecureHardwareEnv
meta import Obend.Crypto.PqHashSignatures
meta import Obend.Polis.SandboxDomainTags
meta import Obend.Digest.HashBytes
meta import Obend.Digest.Cshake256.Spec
meta import Obend.Crypto.Transcript
import Obend.Tactic.Tooth

public section
namespace Obend.Polis.SecureHardwareEnv.Tests

open Obend
open Obend.Crypto.PqHashSignatures
open Obend.Polis.SecureHardwareEnv

set_option autoImplicit false

def bytes32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩

def hexOfBytes (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

def hexOfList (bs : List UInt8) : String := hexOfBytes ⟨bs.toArray⟩

def optRandBytes : List UInt8 := List.replicate 32 0x5A
def maxGrindIters : Nat := 16384

def custSk (i : Nat) : PqSecretKey :=
  let b := UInt8.ofNat i
  ⟨List.replicate 32 (0xA0 + b), List.replicate 32 (0xB0 + b), List.replicate 32 (0xC0 + b)⟩

def simpSk (i : Nat) : PqSecretKey :=
  let b := UInt8.ofNat i
  ⟨List.replicate 32 (0xD0 + b), List.replicate 32 (0xE0 + b), List.replicate 32 (0xF0 + b)⟩

def canonicalWeightRows : List (List Int) :=
  [[2, -1, 4, 3], [-2, 1, 2, -4], [6, -3, 1, 2]]

def canonicalBlockShifts : List Nat := [0, 1, 0]

def canonicalRoundInputsT1 : List (List Int) :=
  [[3, -2, 5, -1], [4, 1, -2, 6], [-1, 3, 2, 4]]

def canonicalRoundInputsT4 : List (List Int) :=
  [[2, 5, -3, 1], [-4, 2, 3, -1], [1, -2, 4, 3]]

def canonicalWeightsRoot : ByteArray :=
  fpauditWeightsRoot canonicalWeightRows canonicalBlockShifts

def act1Payload : ByteArray := ⟨#[0x41, 0x43, 0x54, 0x31]⟩
def act2Payload : ByteArray := ⟨#[0x41, 0x43, 0x54, 0x32]⟩
def upgradedFloors : List SheFloor := canonicalGenesisFloors ++ [.sensorRoiRedaction 4]

def validCand1 : CandidateComputation :=
  buildHonestCandidate
    canonicalUd100SmallSuite
    (bytes32 0x33)
    (floorsDigest canonicalGenesisFloors)
    (shePayloadDigest act1Payload)
    (bytes32 0x19)
    8268
    canonicalRoundInputsT1
    canonicalWeightRows
    canonicalBlockShifts

def validCand4 : CandidateComputation :=
  buildHonestCandidate
    canonicalUd100WideLeafSuite
    (bytes32 0x72)
    (floorsDigest upgradedFloors)
    (shePayloadDigest act2Payload)
    (bytes32 0x29)
    0
    canonicalRoundInputsT4
    canonicalWeightRows
    canonicalBlockShifts

def signCust (msg : ByteArray) (pairs : List (Nat × Nat)) : List (Nat × PqHashSig) :=
  pairs.map fun (idx, leaf) =>
    match evalSingleSign cshake256Suite sheStatefulPqParams (custSk idx) msg.data.toList optRandBytes leaf maxGrindIters with
    | some sig => (idx, sig)
    | none => (idx, ⟨[], 0, leaf, [], []⟩)

def signSimp (msg : ByteArray) (pairs : List (Nat × Nat)) : List (Nat × PqHashSig) :=
  pairs.map fun (idx, leaf) =>
    match evalSingleSign cshake256Suite sheStatefulPqParams (simpSk idx) msg.data.toList optRandBytes leaf maxGrindIters with
    | some sig => (idx, sig)
    | none => (idx, ⟨[], 0, leaf, [], []⟩)

/-! ## 1. Fast Non-PQ Grounded `UD-100` + `fpaudit` (`s8 × E2M1`) + Wire Parity Guards -/

#guard hexOfBytes (floorsDigest canonicalGenesisFloors) ==
  "6f6491a661a8e2d178544e84cd4917fda6e6eb451ae9f49c4a211588096c6811" &&
  hexOfBytes (shePayloadDigest act1Payload) ==
  "1839254e8817686d0ea77ebcdf95f57f61b01582ed8ed01dc471c60f2a602d57" &&
  hexOfBytes (suiteArtifactDigest canonicalUd100SmallSuite) ==
  "fb1c5f28ef8774797858dbb4268130ff259c6ae77a8c75b4d2ecdda06ef278a7" &&
  hexOfBytes (suiteArtifactDigest canonicalUd100WideLeafSuite) ==
  "372ae7d6c020c55d8f2b86cb240771dd07ce5b76ed3515552b79e385fca8e84c" &&
  hexOfBytes canonicalWeightsRoot ==
  "b254bd4c5833be2e57d92953d8cd6f2e3b7c20297c7cf7875c3430d150e1da51"

#guard shePqParamsValid sheStatefulPqParams &&
  !shePqParamsValid sheStatelessPqParams &&
  !shePqParamsValid { sheStatefulPqParams with w := 16, ell1 := 64 } &&
  !shePqParamsValid compactLeanSigParams &&
  !shePqParamsValid compactGoldenParams

#guard checkSuiteArtifact canonicalUd100SmallSuite &&
  suiteProvenMilliBits canonicalUd100SmallSuite == 100022 &&
  checkSuiteArtifact canonicalUd100WideLeafSuite &&
  suiteProvenMilliBits canonicalUd100WideLeafSuite == 100344 &&
  !checkSuiteArtifact { canonicalUd100SmallSuite with regime := .withdrawnCapacityBoundCbr } &&
  !checkSuiteArtifact { canonicalUd100SmallSuite with regime := .johnsonBoundJbr, logBlowup := 200, pinnedNumQueries := 1, powBits := 0, extFieldBits := 100 } &&
  !checkSuiteArtifact { canonicalUd100SmallSuite with logArity := 0 } &&
  !checkSuiteArtifact { canonicalUd100SmallSuite with logBlowup := 0 } &&
  !checkSuiteArtifact { canonicalUd100SmallSuite with powBits := 25 } &&
  verifyCandidateComputation validCand1 &&
  provenZkmlMilliBits validCand1 == 100022 &&
  verifyCandidateComputation validCand4 &&
  provenZkmlMilliBits validCand4 == 100344

-- Exact `s8 × E2M1` integer recompute separation, steering refusal, commit-after-coin,
-- non-`E2M1`, out-of-`s8`, unpinned `observedNumQueries`, and PoW tampering refusals.
#guard
  let actual := [10, 9]
  let steered := [9, 10]
  let tolBypass := toleranceLogitCheck 1 actual steered && argmaxIdx actual != argmaxIdx steered && (actual != steered)
  let revInv := exactIntDot [3, -2, 5, -1].reverse [2, -1, 4, 3].reverse == exactIntDot [3, -2, 5, -1] [2, -1, 4, 3]
  let openIdx := validCand1.recomputeAudit.openedRoundIdx
  let steeredRounds := validCand1.recomputeAudit.committedRounds.map fun r =>
    if r.roundIdx == openIdx then
      let flipped := match r.claimedLogits with | a :: b :: rest => (a - 1) :: (b + 1) :: rest | xs => xs
      { r with claimedLogits := flipped, claimedArgmax := argmaxIdx flipped }
    else r
  let steeredCand := { validCand1 with recomputeAudit := { validCand1.recomputeAudit with committedRounds := steeredRounds, commitRoot := fpauditCommitRoot steeredRounds }, outputRoot := fpauditOutputRoot steeredRounds }
  let steeredCandBound := { steeredCand with statementDigest := candidateStatementDigest steeredCand.suite steeredCand.modelWeightsRoot steeredCand.inputRoot steeredCand.recomputeAudit.commitRoot steeredCand.outputRoot steeredCand.recomputeAudit.committedRounds.length steeredCand.boundFloorsDigest steeredCand.actionPayloadDigest }
  let coinTamper := { validCand1 with recomputeAudit := { validCand1.recomputeAudit with openedRoundIdx := (openIdx + 1) % 3 } }
  let unpinnedQ := { validCand1 with observedNumQueries := 85 }
  let badPow := { validCand1 with powNonce := validCand1.powNonce + 1 }
  let badZeroPow := buildHonestCandidate canonicalUd100WideLeafSuite (bytes32 0x72) (floorsDigest upgradedFloors) (shePayloadDigest act2Payload) (bytes32 0x29) 1 canonicalRoundInputsT4 canonicalWeightRows canonicalBlockShifts
  let badE2m1 := buildHonestCandidate canonicalUd100WideLeafSuite (bytes32 0x72) (floorsDigest upgradedFloors) (shePayloadDigest act2Payload) (bytes32 0x29) 0 canonicalRoundInputsT4 [[5, -1, 4, 3], [-2, 1, 2, -4], [6, -3, 1, 2]] canonicalBlockShifts
  let badS8 := buildHonestCandidate canonicalUd100WideLeafSuite (bytes32 0x72) (floorsDigest upgradedFloors) (shePayloadDigest act2Payload) (bytes32 0x29) 0 [[128, 5, -3, 1]] canonicalWeightRows canonicalBlockShifts
  tolBypass && revInv &&
  !verifyCandidateComputation steeredCandBound &&
  !verifyCandidateComputation coinTamper &&
  !verifyCandidateComputation unpinnedQ &&
  !verifyCandidateComputation badPow &&
  !verifyCandidateComputation badZeroPow &&
  !verifyCandidateComputation badE2m1 &&
  !verifyCandidateComputation badS8

/-! ## 2. Single-Pass 256-Bit `PqHashSignatures` Ceremony, Wire Parity & Adversarial Refusals -/
-- All 256-bit XMSS keygen (`ell1=128`) and TSW signing executes ONCE inside this single `#guard`!

#guard
  let realCustodianPks := (List.range 5).map fun i => derivePublicKey cshake256Suite sheStatefulPqParams (custSk i)
  let realSimplexPks := (List.range 4).map fun i => derivePublicKey cshake256Suite sheStatefulPqParams (simpSk i)
  let genesis0 : SheState :=
    { canonicalGenesisSheState 0 with
      pinnedModelWeightsRoot := canonicalWeightsRoot
      custodianPks := realCustodianPks
      simplexValidatorPks := realSimplexPks }
  let act1Unsigned : ActuationTurnProposal :=
    { sensorSeq           := 1
      sensorSealDigest    := bytes32 0x33
      candidate           := validCand1
      nullifier           := bytes32 0x44
      mandateCost         := 25
      redactedRoiCount    := 3
      consentBandHeightPx := 40
      attestedGpuCount    := 2
      sharedRingAtCopy    := act1Payload
      privateFrameCopy    := act1Payload
      dispatchedPayload   := act1Payload
      simplexCommitteeN   := 4
      simplexFaultyF      := 1
      simplexQcSignatures := []
      custodianEpoch      := 1
      custodianSignatures := []
      tofRoundTripTicks   := 18 }
  let signedAct1 : ActuationTurnProposal :=
    { act1Unsigned with
      simplexQcSignatures := signSimp (sheSimplexQcMsg genesis0 act1Unsigned) [(0, 0), (1, 0), (2, 0)]
      custodianSignatures := signCust (sheCustodianActuationMsg genesis0 act1Unsigned) [(0, 0), (2, 0), (3, 0)] }
  let turn1 : SheTurn := .proposeAndSettleActuation signedAct1
  let stAfter1 := match applySheTurn genesis0 turn1 with | .ok st => st | .error _ => genesis0
  let up2Unsigned : UpgradeJudgeProposal :=
    { newJudgeDigest       := bytes32 0x55
      newModelWeightsRoot  := canonicalWeightsRoot
      newZkmlSuiteDigest   := suiteArtifactDigest canonicalUd100WideLeafSuite
      newFloors            := upgradedFloors
      newRevertWindowSteps := 6
      newCustodianEpoch    := 2
      custodianSignatures  := []
      tofRoundTripTicks    := 15
      authorityClaim       := .localCustodianCeremony }
  let signedUp2 : UpgradeJudgeProposal :=
    { up2Unsigned with
      custodianSignatures := signCust (sheCustodianUpgradeMsg stAfter1 up2Unsigned) [(0, 1), (1, 1), (3, 1)] }
  let turn2 : SheTurn := .upgradeHabitatJudge signedUp2
  let stAfter2 := match applySheTurn stAfter1 turn2 with | .ok st => st | .error _ => stAfter1
  let turn3 : SheTurn := .revokeOrAttenuateMandate
    { newBudgetCap           := 50
      newMaxProximityTicks   := 30
      newlyRevokedCustodians := [4]
      reasonDigest           := bytes32 0x66 }
  let stAfter3 := match applySheTurn stAfter2 turn3 with | .ok st => st | .error _ => stAfter2
  let act4Unsigned : ActuationTurnProposal :=
    { sensorSeq           := 2
      sensorSealDigest    := bytes32 0x72
      candidate           := validCand4
      nullifier           := bytes32 0x73
      mandateCost         := 40
      redactedRoiCount    := 4
      consentBandHeightPx := 48
      attestedGpuCount    := 2
      sharedRingAtCopy    := act2Payload
      privateFrameCopy    := act2Payload
      dispatchedPayload   := act2Payload
      simplexCommitteeN   := 4
      simplexFaultyF      := 1
      simplexQcSignatures := []
      custodianEpoch      := 2
      custodianSignatures := []
      tofRoundTripTicks   := 22 }
  let signedAct4 : ActuationTurnProposal :=
    { act4Unsigned with
      simplexQcSignatures := signSimp (sheSimplexQcMsg stAfter3 act4Unsigned) [(1, 1), (2, 1), (3, 1)]
      custodianSignatures := signCust (sheCustodianActuationMsg stAfter3 act4Unsigned) [(0, 2), (1, 2), (2, 2)] }
  let turn4 : SheTurn := .proposeAndSettleActuation signedAct4
  -- Locked byte-exact cross-language vectors shared with `anti_vaz_she_ceremony.rs`
  let vectorsOk :=
    (match realCustodianPks.head? with | some pk => hexOfList pk.pkRoot | none => "") == "890b7e07b96ce870b8e5e09f91f7f1b2652d9e6024d425d4dd6e9679c61ea854" &&
    (match realSimplexPks.head? with | some pk => hexOfList pk.pkRoot | none => "") == "3461a82d0f7fd72aa3bd6f1ce4fb77961d0b0fe0ef8873ee83c5ff4f2fdd8bec" &&
    hexOfBytes (sheStateDigest genesis0) == "291c9e627a693fa89b6d01041e08eaeda2e4eb50cf43e93828ee0e3365e1b1d6" &&
    hexOfBytes (sheCustodianActuationMsg genesis0 signedAct1) == "42b97c049002fd5fb7525043d22d7d993f9014a79f48f8c770303ce8d8753d89" &&
    hexOfBytes (sheSimplexQcMsg genesis0 signedAct1) == "64219a5a05909884b06f5fdeaaa92de2bb91f9364b7696587ff93a856a137198" &&
    hexOfBytes (sheTurnEnvelopeDigest turn1) == "280faa8cf6ec0297adb3d805b43291770ca4ab2f59ca0e958bafa1fb2fbd47b3" &&
    hexOfBytes (sheTurnEnvelopeDigest turn2) == "2543e5d467c29c5b99cac0900a64ebf0d759fc8623c8a99c2c662ad11cf35ca4" &&
    hexOfBytes (sheTurnEnvelopeDigest turn3) == "4703fd475cbe80a9dee00cc86a023b0341874af30ba13a45aa61080a05f159ac" &&
    hexOfBytes (sheTurnEnvelopeDigest turn4) == "4ab8149d6eac0744b4696844bb2ce0d872ccc5976859911896e982d6bc4770dc"
  -- Full 4-turn positive ceremony + `sheCeremonyJudge` acceptance + non-empty genesis refusal
  let positiveOk :=
    !checkSheStateWellFormed { genesis0 with pqParams := compactLeanSigParams } &&
    !checkSheStateWellFormed stAfter1 &&
    match runSheTurns genesis0 [turn1, turn2, turn3, turn4] with
    | .ok endSt =>
      endSt.monoSensorSeq == 2 &&
      endSt.settledOutboxActions.length == 2 &&
      endSt.remainingMandateBudget == 10 &&
      settledTotalCost endSt.settledOutboxActions == 65 &&
      endSt.custodianQuorumEpoch == 2 &&
      endSt.consumedCustodianLeaves.length == 9 &&
      endSt.consumedSimplexLeaves.length == 6 &&
      (match Judge.check (Obj := SheCeremonyObj) 4
         ⟨genesis0, [turn1, turn2, turn3, turn4], [.sensorRoiRedaction 4]⟩ endSt with
       | .ok => true | _ => false)
    | .error _ => false
  -- Forged 256-bit PQ custodian sig, permuted quorum, cross-turn tamper, XMSS leaf reuse, Vaz downgrade,
  -- external authority refusal, unpinned suite refusal, `< t` coalition, ToF relay, nullifier replay, budget overrun, revoked custodian, Judge refusal
  let corruptSig : PqHashSig :=
    match signedAct1.custodianSignatures[1]? with
    | some (_, s) =>
      match s.layerSigs with
      | ls :: rest =>
        let badChs := match ls.wotsChains with | c :: cs => (c.map (· ^^^ 0x01)) :: cs | [] => []
        { s with layerSigs := { ls with wotsChains := badChs } :: rest }
      | [] => s
    | none => ⟨[], 0, 0, [], []⟩
  let badCustSigs := signedAct1.custodianSignatures.set 1 (2, corruptSig)
  let permutedCustSigs := signedAct1.custodianSignatures.reverse
  let reuseSigs := signCust (sheCustodianUpgradeMsg stAfter1 up2Unsigned) [(0, 0), (1, 1), (3, 1)]
  let revSigs := signCust (sheCustodianActuationMsg stAfter3 act4Unsigned) [(0, 2), (1, 2), (4, 2)]
  let vazAgencyDowngrade : SheTurn := .upgradeHabitatJudge
    { newJudgeDigest       := bytes32 0x99
      newModelWeightsRoot  := canonicalWeightsRoot
      newZkmlSuiteDigest   := suiteArtifactDigest canonicalUd100SmallSuite
      newFloors            := [ .consentBandNonOcclusion 32, .zkmlProvenSoundnessMilliBits 100000,
                                .physicalProximityMaxTicks 50, .e2eeTeeChannelBound 1, .operatorLocalRevert 8 ]
      newRevertWindowSteps := 4
      newCustodianEpoch    := 2
      custodianSignatures  := []
      tofRoundTripTicks    := 10
      authorityClaim       := .agencyEmergencyOrder (bytes32 0xAA) (bytes32 0xBB) }
  let externalNoDrop : SheTurn := .upgradeHabitatJudge
    { newJudgeDigest       := bytes32 0x98
      newModelWeightsRoot  := canonicalWeightsRoot
      newZkmlSuiteDigest   := suiteArtifactDigest canonicalUd100SmallSuite
      newFloors            := canonicalGenesisFloors
      newRevertWindowSteps := 4
      newCustodianEpoch    := 2
      custodianSignatures  := []
      tofRoundTripTicks    := 10
      authorityClaim       := .vendorRootDirective (bytes32 0xCC) }
  let unpinnedSuiteCand := buildHonestCandidate canonicalUd100WideLeafSuite (bytes32 0x33) (floorsDigest canonicalGenesisFloors) (shePayloadDigest act1Payload) (bytes32 0x19) 0 canonicalRoundInputsT1 canonicalWeightRows canonicalBlockShifts
  let attacksRefused :=
    (match applySheTurn genesis0 (.proposeAndSettleActuation { signedAct1 with candidate := { validCand1 with powNonce := validCand1.powNonce + 1 } }) with
     | .error .zkmlProofUnverified => true | _ => false) &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { signedAct1 with candidate := unpinnedSuiteCand }) with
     | .error .zkmlSuiteNotPinned => true | _ => false) &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { signedAct1 with custodianSignatures := badCustSigs }) with
     | .error (.invalidCustodianPqSignature 2) => true | _ => false) &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { signedAct1 with custodianSignatures := permutedCustSigs }) with
     | .error .duplicateOrOutOfRangeSigner => true | _ => false) &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { signedAct1 with nullifier := bytes32 0x99 }) with
     | .error (.invalidSimplexPqSignature 0) => true | _ => false) &&
    (match applySheTurn stAfter1 (.upgradeHabitatJudge { up2Unsigned with custodianSignatures := reuseSigs }) with
     | .error (.reusedStatefulPqLeaf 0 0) => true | _ => false) &&
    (match applySheTurn genesis0 vazAgencyDowngrade with
     | .error (.coerciveFloorDowngrade (.sensorRoiRedaction 2)) => true | _ => false) &&
    (match applySheTurn genesis0 externalNoDrop with
     | .error .externalAuthorityRefused => true | _ => false) &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { signedAct1 with custodianSignatures := signedAct1.custodianSignatures.take 2 }) with
     | .error (.insufficientCustodianQuorum 2 3) => true | _ => false) &&
    (match applySheTurn genesis0 (.proposeAndSettleActuation { signedAct1 with tofRoundTripTicks := 51 }) with
     | .error (.tofProximityExceeded 51 50) => true | _ => false) &&
    (match applySheTurn stAfter3 (.proposeAndSettleActuation { signedAct4 with nullifier := bytes32 0x44 }) with
     | .error .nullifierReplayed => true | _ => false) &&
    (match applySheTurn stAfter3 (.proposeAndSettleActuation { signedAct4 with mandateCost := 51 }) with
     | .error (.mandateBudgetExceeded 51 50) => true | _ => false) &&
    (match applySheTurn stAfter3 (.proposeAndSettleActuation { signedAct4 with custodianSignatures := revSigs }) with
     | .error (.revokedCustodianSigner 4) => true | _ => false) &&
    (match Judge.check (Obj := SheCeremonyObj) 2 ⟨genesis0, [vazAgencyDowngrade], []⟩ genesis0 with
     | .refused k path =>
       (match k with | .coerciveFloorDowngrade (.sensorRoiRedaction 2) => true | _ => false) &&
       path == [0] && sheRefusalRefutes k
     | _ => false)
  vectorsOk && positiveOk && attacksRefused

/-! ## 3. Universal `#tooth` Mutation Kills (12 Distinct Cryptographic & Ceremony Security Gates) -/

-- Tooth 1: Bypassing floor non-regression in `applySheTurn` -> killed by `vaz_coercive_floor_downgrade_refused`.
#tooth vaz_coercive_floor_downgrade_refused by mutation applySheTurn := fun st turn =>
  match turn with
  | .upgradeHabitatJudge up => .ok { st with activeSafetyAndPrivacyFloors := up.newFloors }
  | _ => .ok st

-- Tooth 2: Crediting withdrawn CBR bits in `suiteProvenMilliBits` -> killed by `udr_strictly_below_legacy_cbr`.
#tooth udr_strictly_below_legacy_cbr by mutation suiteProvenMilliBits := fun s =>
  legacyWithdrawnCbrMilliBits s

-- Tooth 3: Rubber-stamping `verifyCandidateComputation` to `true` (resurrecting `proofVerified : Bool` cosplay!)
-- is killed immediately by `verifyCandidateComputation_sound`.
#tooth verifyCandidateComputation_sound by mutation verifyCandidateComputation := fun _ => true

-- Tooth 4: Rubber-stamping `verifyExactRecomputeAudit` to `true` (accepting steered/forged `fpaudit` logits!)
-- is killed immediately by `lying_caught_at_opened_round`.
#tooth lying_caught_at_opened_round by mutation verifyExactRecomputeAudit := fun _ => true

-- Tooth 5: Rubber-stamping `verifyShePqSig` to `true` (bypassing real `PqHashSignatures` verification!)
-- is killed immediately by `verifyShePqSig_sound`.
#tooth verifyShePqSig_sound by mutation verifyShePqSig := fun _ _ _ _ => true

-- Tooth 5b: Rubber-stamping `checkSuiteArtifact` to `true` (admitting withdrawn CBR / unbounded `logBlowup`)
-- is killed immediately by `verifyCandidateComputation_sound`.
#tooth verifyCandidateComputation_sound by mutation checkSuiteArtifact := fun _ => true

-- Tooth 6: Mutating `checkCustodianPqQuorum` to accept `< t` signers (`1 ≤ sigs.length`) without verifying PQ sigs
-- is killed immediately by `checkCustodianPqQuorum_ok_iff`.
#tooth checkCustodianPqQuorum_ok_iff by mutation checkCustodianPqQuorum := fun st _ sigs =>
  if decide (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN) &&
     decide (1 ≤ sigs.length) then .ok ()
  else .error .duplicateOrOutOfRangeSigner

-- Tooth 7: Mutating `applySheTurn` to drop `consumedNullifiers` recording (allowing replay!)
-- is killed by `she_trace_end_to_end_safe_and_anti_vaz`.
#tooth she_trace_end_to_end_safe_and_anti_vaz by mutation applySheTurn := fun st turn =>
  match turn with
  | .proposeAndSettleActuation act =>
    if st.monoSensorSeq < act.sensorSeq && act.sensorSealDigest.size == 32 then
      .ok { st with
            monoSensorSeq := act.sensorSeq
            remainingMandateBudget := st.remainingMandateBudget - act.mandateCost
            settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
    else .error .nullifierReplayed
  | _ => .error .malformedInitialState

-- Tooth 8: Mutating `applySheTurn` to allow mandate budget amplification in `.revokeOrAttenuateMandate`
-- is killed by `she_trace_end_to_end_safe_and_anti_vaz`.
#tooth she_trace_end_to_end_safe_and_anti_vaz by mutation applySheTurn := fun st turn =>
  match turn with
  | .revokeOrAttenuateMandate rev => .ok { st with remainingMandateBudget := rev.newBudgetCap }
  | _ => .error .malformedInitialState

-- Tooth 9: Mutating `applySheTurn` to skip PQ quorum verification on `.proposeAndSettleActuation`
-- is killed immediately by `she_ceremony_pq_quorum_unforgeable`.
#tooth she_ceremony_pq_quorum_unforgeable by mutation applySheTurn := fun st turn =>
  match turn with
  | .proposeAndSettleActuation act =>
    .ok { st with
          monoSensorSeq := act.sensorSeq
          settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
  | _ => .error .malformedInitialState

-- Tooth 10: Mutating `applySheTurn` to omit the ToF physical-presence proximity check
-- is killed by `she_trace_end_to_end_safe_and_anti_vaz`.
#tooth she_trace_end_to_end_safe_and_anti_vaz by mutation applySheTurn := fun st turn =>
  match turn with
  | .proposeAndSettleActuation act =>
    if st.monoSensorSeq < act.sensorSeq && act.sensorSealDigest.size == 32 &&
       verifyCandidateComputation act.candidate &&
       act.candidate.suite.regime != .withdrawnCapacityBoundCbr &&
       decide (100000 ≤ provenZkmlMilliBits act.candidate) &&
       !st.consumedNullifiers.contains act.nullifier &&
       decide (act.mandateCost ≤ st.remainingMandateBudget) then
      .ok { st with
            monoSensorSeq := act.sensorSeq
            consumedNullifiers := st.consumedNullifiers ++ [act.nullifier]
            remainingMandateBudget := st.remainingMandateBudget - act.mandateCost
            settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
    else .error .malformedInitialState
  | _ => .error .malformedInitialState

-- Tooth 11: Mutating `sheTurnWireFields` to drop zkML suite/fpaudit & PQ signature fields from `OBEND.SHE.TURN/v1`
-- is killed immediately by `sheTurnEnvelope_binds`.
#tooth sheTurnEnvelope_binds by mutation sheTurnWireFields := fun turn =>
  match turn with
  | .proposeAndSettleActuation act => [[0x01], act.nullifier.data.toList]
  | .upgradeHabitatJudge up => [[0x02], up.newJudgeDigest.data.toList]
  | .revokeOrAttenuateMandate rev => [[0x03], rev.reasonDigest.data.toList]

-- Tooth 12: Mutating `sheRefusalRefutes` to mark `.terminalStateMismatch` as refuting
-- is killed immediately by `checkSheCeremony_refutes_sound`.
#tooth checkSheCeremony_refutes_sound by mutation sheRefusalRefutes := fun _ => true

/-! ## 4. Kernel Axiom & Choice Audit -/

#print axioms extractSheTurnEnvelope
#print axioms sheTurnEnvelope_binds
#print axioms suiteArtifactDigest_binds
#print axioms exactIntDot_reverse
#print axioms tolerance_checker_admits_steered_argmax_while_exact_refuses
#print axioms verifyCandidateComputation_sound
#print axioms lying_caught_at_opened_round
#print axioms buildHonestCandidate_1round_complete
#print axioms verifyCandidateComputation_inhabited
#print axioms verifyShePqSig_sound
#print axioms extractSheCeremonyPqForgery
#print axioms she_ceremony_pq_quorum_unforgeable
#print axioms floorsDigest_binds
#print axioms shePayloadDigest_binds
#print axioms vaz_coercive_floor_downgrade_refused
#print axioms she_trace_end_to_end_safe_and_anti_vaz
#print axioms she_trace_coupled_sel4_private_frame_safe
#print axioms sheCeremonyJudge

end Obend.Polis.SecureHardwareEnv.Tests
end
