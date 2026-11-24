module
/-
# PoliswareAndEnvHarnessTest — Open-World `EnvHarness`, `HermesEnv` `WhyTrue`/`WhyFalse`, `DecentralizedRulesMesh` & P1 Hardening Suite

Compile-time `#guard`, `#tooth` mutation-killing, and `#print axioms` verification suite covering:
1. `Obend.Logic.EnvHarness`: the `SortedU64Set` revocation set, `skip_implies_contract_violation`,
   `most_general_client_multi_turn_safe`, and `multi_handle_reachability_inhabited`.
2. `Obend.Polis.HermesEnv`: constructive `evalWhy_sound_and_complete` (`WhyTrue` / `WhyFalse` over
   boolean + `threshold k ps` policies) and `hermesRoom_multi_turn_attenuation_sound`.
3. `Obend.Polis.DecentralizedRulesMesh`: `bridgingQuorumCheck` (`polarized_supermajority_refused`,
   `sybil_cluster_stuffing_non_amplifying`), `no_self_lockout_multi_turn`, full 256-bit
   `exPostRulesReceipt_digest_binding`, `ex_post_rules_compliance_multi_turn_sound`, `poliswareMeshJudge`.
4. Cross-layer P1 regression checks (`PrivatePredicate` `k3p` caveat encryption/location authentication,
   `DecoAndCallTree` `sessionKeys` scrubbing & pinned trusted notaries, `Hardware.Judge` non-tautological meanings).
-/
public import Obend.Tactic.Tooth
public import Obend.Logic.EnvHarness
public import Obend.Polis.HermesEnv
public import Obend.Polis.DecentralizedRulesMesh
public import Obend.Polis.PrivatePredicate
public import Obend.Judge.DecoAndCallTree
public import Obend.Hardware.Judge
import all Obend.Logic.EnvHarness
import all Obend.Core.SortedArray
import all Obend.Polis.HermesEnv
import all Obend.Polis.DecentralizedRulesMesh
import all Obend.Polis.PrivatePredicate
import all Obend.Judge.DecoAndCallTree
meta import Obend.Logic.EnvHarness
meta import Obend.Core.SortedArray
meta import Obend.Polis.HermesEnv
meta import Obend.Polis.DecentralizedRulesMesh
meta import Obend.Polis.PrivatePredicate
meta import Obend.Judge.DecoAndCallTree
meta import Obend.Judge.Class

public section
namespace Obend.Tests.Metasystem.PoliswareAndEnvHarnessTest

open Obend.Logic.EnvHarness
open Obend.Core.SortedArray (SortedU64Set insertKey)
open Obend.Polis.HermesEnv
open Obend.Polis.DecentralizedRulesMesh
open Obend.Polis.EpistemicVouchMarket (CapEdge TrustNode)

set_option autoImplicit false

/-! ## 1. `EnvHarness` Binary Search & Multi-Handle Open-World Execution -/

def demoRevokedSet : SortedU64Set :=
  (((SortedU64Set.empty.insert 42).insert 7).insert 19).insert 7

#guard demoRevokedSet.data == #[7, 19, 42]
#guard demoRevokedSet.contains 19 == true
#guard demoRevokedSet.contains 42 == true
#guard demoRevokedSet.contains 18 == false

def demoWorld5 : MultiHandleWorld × Nat × List (OpenEnvTurn × Sum UInt64 EnvRefusal) :=
  runDemonicClient demoAdaptiveClient 5 0 (initMultiHandleWorld 100)

#guard demoWorld5.1.revoked.contains 0 == true
#guard demoWorld5.1.revoked.contains 1 == false
#guard demoWorld5.1.mandateUsed == 40
#guard (stepMultiHandle demoWorld5.1 (.invoke 0 0x01 10)) == .inr (.handleRevoked 0)
#guard (stepMultiHandle demoWorld5.1 (.invoke 99 0x01 10)) == .inr (.unknownHandle 99)
#guard (stepMultiHandle demoWorld5.1 (.invoke 1 0x05 70)) == .inr (.handleLimitExceeded 1)

/-! ## 2. `HermesEnv` Constructive `WhyTrue` / `WhyFalse` & Threshold Anti-Duplication -/

def sampleThresholdPolicy : PolicyPred Nat :=
  .threshold 2 (PolicyList.ofList [.atom 10, .neg (.atom 20), .atom 30])

def sampleEnvPass : Nat → Bool
  | 10 => true
  | 20 => false
  | _ => false

def sampleEnvFail : Nat → Bool
  | 10 => true
  | 20 => true
  | _ => false

#guard (match evalWhy sampleEnvPass sampleThresholdPolicy with
  | .inl wt => checkWhyTrue sampleEnvPass sampleThresholdPolicy wt
  | .inr _ => false)

#guard (match evalWhy sampleEnvFail sampleThresholdPolicy with
  | .inl _ => false
  | .inr wf => checkWhyFalse sampleEnvFail sampleThresholdPolicy wf)

-- Duplicate child index `[0, 0]` attempting to forge a 2-of-3 threshold from a single true atom is refused!
def forgedDuplicateThresholdWitness : WhyTrue Nat :=
  .thresholdSat (.cons 0 (.atomTrue 10) (.cons 0 (.atomTrue 10) .nil))

#guard checkWhyTrue sampleEnvFail sampleThresholdPolicy forgedDuplicateThresholdWitness == false

def sampleHermesTrace : HermesRoomState Nat × List (Option (HermesPostReceipt Nat)) :=
  runHermesTurns (initHermesRoom (.atom 1))
    [ .delegateSubRoom 0 (.atom 2)
    , .postMessage 1 0xABCD#256 (fun a => a == 1 || a == 2)
    , .postMessage 1 0xDEAD#256 (fun a => a == 1)
    , .revokeSubRoom 1
    , .postMessage 1 0xBEEF#256 (fun _ => true) ]

#guard sampleHermesTrace.1.log.length == 1
#guard sampleHermesTrace.1.revoked.contains 1 == true

/-! ## 3. `DecentralizedRulesMesh`: Bridging Quorum, Anti-Lockout & 256-Bit Receipts -/

def demoMeshNet : List CapEdge :=
  [ ⟨.principal 0, .principal 1, 900⟩
  , ⟨.principal 0, .principal 2, 100⟩ ]

def demoMeshCfg : QuorumConfig :=
  { rootId := 0, minClusterCap := 50, minActiveClusters := 2, supermajorityBps := 6667 }

def demoVoters : List (Nat × Nat) := [(1, 10), (2, 20)]
def demoClusters : List Nat := [10, 20]

-- Polarized 90% global majority (Cluster 10 = 900/900 yes, Cluster 20 = 0/100 yes) is REFUSED!
#guard bridgingQuorumCheck demoMeshCfg demoMeshNet demoClusters demoVoters (fun v => v == 1) == false
-- Bridging cross-cluster consensus (Cluster 10 & Cluster 20 both yes) PASSES!
#guard bridgingQuorumCheck demoMeshCfg demoMeshNet demoClusters demoVoters (fun _ => true) == true
-- Self-lockout quorum (`supermajorityBps := 10001`) is REFUSED by `checkQuorumViable`!
#guard checkQuorumViable { demoMeshCfg with supermajorityBps := 10001 } demoMeshNet demoClusters demoVoters == false

def demoRuleDig : BitVec 256 := computeRuleEpochDigest256 1 (.atom 7)
def demoNextRoot : BitVec 256 := advanceStateRoot256 0x11#256 demoRuleDig 0x22#256
def demoReceipt : ExPostRulesReceipt :=
  { epoch := 1
    prevStateRoot256 := 0x11#256
    nextStateRoot256 := demoNextRoot
    ruleEpochDigest256 := demoRuleDig
    turnDigest256 := 0x22#256
    admitted := true
    explanation := .inl (.atomTrue 7) }

def demoQuery : MeshComplianceQuery :=
  { epoch := 1
    quorumBps := 6667
    policy := .atom 7
    env := fun a => a == 7
    prevStateRoot256 := 0x11#256
    expectedReceiptDigest256 := exPostRulesReceiptDigest256 demoReceipt }

#guard (checkPoliswareMesh 0 demoQuery demoReceipt) == .ok
#guard (checkPoliswareMesh 0 { demoQuery with quorumBps := 10001 } demoReceipt) ==
  .refused .invalidQuorumBounds []

/-! ## 4. Cross-Layer P1 Regression Guards (`PrivatePredicate` `k3p` & `DecoAndCallTree` Scrubbing) -/

section P1Regressions
open Obend.Polis.PrivatePredicate
open Obend.Judge.DecoAndCallTree

def testLocA : ByteArray := "vat://alpha".toUTF8
def testLocB : ByteArray := "vat://evil".toUTF8
def testK3p : ByteArray := ⟨(List.replicate 32 (5 : UInt8)).toArray⟩
def testWrongK3p : ByteArray := ⟨(List.replicate 32 (6 : UInt8)).toArray⟩
def testR : ByteArray := ⟨(List.replicate 32 (9 : UInt8)).toArray⟩
def testParent : ByteArray := ⟨#[77]⟩
def testPred : VkId := ⟨(DistPred.eq 0 1).digest⟩

def testCavK3p : ThirdPartyCaveat :=
  issueCaveatUnderK3p testLocA testK3p ⟨#[1]⟩ ⟨#[2]⟩ testParent testR testPred

#guard openTicket testK3p testCavK3p == some (testR, testPred)
-- Location swap is rejected by `openTicket` under `k3p`!
#guard (openTicket testK3p { testCavK3p with location := testLocB }).isNone
-- `recoverKeyUnderK3p` succeeds under `testK3p` and fails under `testWrongK3p` (even with `testParent`)!
#guard recoverKeyUnderK3p testK3p testCavK3p testParent == some testR
#guard (recoverKeyUnderK3p testWrongK3p testCavK3p testParent).isNone

-- `exportPublicCallTreeTranscript` scrubs `sessionKeys` and `decodePublicCallTreeTranscript` rejects leaked keys!
def claimWithSecretKey : CallTreeClaim :=
  { plantedClaim with policy := { plantedClaim.policy with deco :=
      { plantedClaim.policy.deco with
        sessionKeys := [(⟨#[1, 2]⟩, Obend.Crypto.BinaryTower256.towerZero 7)]
        notaries := [⟨#[9]⟩] } } }

#guard (decodePublicCallTreeTranscript [] [⟨#[9]⟩] (encodeCallTreeClaim claimWithSecretKey)).isOk == false
#guard (decodePublicCallTreeTranscript [] [⟨#[9]⟩] (exportPublicCallTreeTranscript claimWithSecretKey)).isOk == true
#guard (decodePublicCallTreeTranscript [] [] (exportPublicCallTreeTranscript claimWithSecretKey)).isOk == false

end P1Regressions

/-! ## 5. `#tooth` Mutation-Sensitivity Witnesses -/

-- Tooth 1: Mutating `stepMultiHandle` to skip the revocation check is caught by `most_general_client_multi_turn_safe`.
#tooth Obend.Logic.EnvHarness.most_general_client_multi_turn_safe by mutation
  Obend.Logic.EnvHarness.stepMultiHandle := fun w t =>
    match t with
    | .invoke handle _ _ => .inl (w, handle)
    | .revoke handle => .inl ({ w with revoked := w.revoked.insert handle, revokedSpec := insertKey handle w.revokedSpec }, handle)
    | .mint _ _ _ => .inr .handleSpaceExhausted
    | .attenuate _ _ _ => .inr .handleSpaceExhausted

-- Tooth 2: Mutating `stepHermesRoom` to admit messages on revoked capabilities breaks `hermesRoom_multi_turn_attenuation_sound`.
#tooth Obend.Polis.HermesEnv.hermesRoom_multi_turn_attenuation_sound by mutation
  Obend.Polis.HermesEnv.stepHermesRoom := fun st _ =>
    (st, some (.admitted 0 0#256 .ttIntro))

-- Tooth 3: Mutating `bridgingQuorumCheck` to ignore per-cluster supermajority is killed by `polarized_supermajority_refused`.
#tooth Obend.Polis.DecentralizedRulesMesh.polarized_supermajority_refused by mutation
  Obend.Polis.DecentralizedRulesMesh.bridgingQuorumCheck := fun cfg net clusters voters _ =>
    checkQuorumViable cfg net clusters voters

-- Tooth 4: Mutating `stepRulesMesh` to accept unviable (`supermajorityBps > 10000`) quorums is killed by `no_self_lockout_multi_turn`.
#tooth Obend.Polis.DecentralizedRulesMesh.no_self_lockout_multi_turn by mutation
  Obend.Polis.DecentralizedRulesMesh.stepRulesMesh := fun _ st _ =>
    ({ st with epoch := st.epoch + 1 }, none)

-- Tooth 5: Omitting `ruleEpochDigest256` from `ExPostRulesReceipt.encode` breaks `exPostRulesReceipt_digest_binding`!
#tooth Obend.Polis.DecentralizedRulesMesh.exPostRulesReceipt_digest_binding by mutation
  Obend.Polis.DecentralizedRulesMesh.ExPostRulesReceipt.encode := fun r =>
    encodeFields
      [ Obend.Crypto.leb128 r.epoch
      , Obend.Digest.HashBytes.be 32 r.prevStateRoot256.toNat
      , Obend.Digest.HashBytes.be 32 r.nextStateRoot256.toNat
      , Obend.Digest.HashBytes.be 32 r.turnDigest256.toNat ]

-- Tooth 6: Mutating `exportPublicCallTreeTranscript` to omit `scrubCallTreeClaim` breaks `exportPublicCallTreeTranscript_scrubs_sessionKeys`.
#tooth Obend.Judge.DecoAndCallTree.exportPublicCallTreeTranscript_scrubs_sessionKeys by mutation
  Obend.Judge.DecoAndCallTree.exportPublicCallTreeTranscript := Obend.Judge.DecoAndCallTree.encodeCallTreeClaim

-- Tooth 7: Mutating `openTicket` to skip location verification breaks `openTicket_tampered_location_refused`.
#tooth Obend.Polis.PrivatePredicate.openTicket_tampered_location_refused by mutation
  Obend.Polis.PrivatePredicate.openTicket := fun _ _ =>
    some (ByteArray.empty, ⟨ByteArray.empty⟩)

/-! ## 6. Kernel Axiom Verification (`0 sorryAx`, `0` custom axioms) -/

#print axioms Obend.Core.SortedArray.search_eq_spec
#print axioms Obend.Logic.EnvHarness.skip_implies_contract_violation
#print axioms Obend.Logic.EnvHarness.most_general_client_multi_turn_safe
#print axioms Obend.Logic.EnvHarness.multi_handle_reachability_inhabited
#print axioms Obend.Polis.HermesEnv.evalWhy
#print axioms Obend.Polis.HermesEnv.evalWhy_sound_and_complete
#print axioms Obend.Polis.HermesEnv.hermesRoom_multi_turn_attenuation_sound
#print axioms Obend.Polis.DecentralizedRulesMesh.polarized_supermajority_refused
#print axioms Obend.Polis.DecentralizedRulesMesh.sybil_cluster_stuffing_non_amplifying
#print axioms Obend.Polis.DecentralizedRulesMesh.no_self_lockout_multi_turn
#print axioms Obend.Polis.DecentralizedRulesMesh.exPostRulesReceiptExtract
#print axioms Obend.Polis.DecentralizedRulesMesh.exPostRulesReceipt_digest_binding
#print axioms Obend.Polis.DecentralizedRulesMesh.ex_post_rules_compliance_multi_turn_sound

end Obend.Tests.Metasystem.PoliswareAndEnvHarnessTest
end
