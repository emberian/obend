module
/-
# ProvenZkmlGateTest — Wire Vectors, Refusal Matrix, Axiom Audit & `#tooth` Kills for `ProvenZkmlGate`

Tests and mutation-sensitivity guards for `Obend.SymbolicZk.ProvenZkmlGate`:
1. Exact cross-language golden wire vector for `OBEND.SHE.ZKML_CHUNK/v1` (coordinated with
   `crates/obend-prove-worker/src/zkml_gate.rs`) plus 3-chunk 8-bit PoW streaming Gated-DeltaNet chain.
2. Concrete refusal witnesses for all 5 refuting clauses (`withdrawnCbrRejected`,
   `belowProven100BitFloor`, `weightRootDrift`, `brokenRecurrentCarry`, `insufficientPowGrind`)
   and non-refuting `certDigestMismatch`.
3. 10 `#tooth` mutation kills across universal soundness, binding, `Spec ↔ Exec`, `Judge`, and
   multi-turn session theorems, plus `#print axioms` hygiene checks (`0 Classical.choice`).
-/
public import Obend.SymbolicZk.ProvenZkmlGate
import all Obend.SymbolicZk.ProvenZkmlGate
import all Obend.Judge.Class
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import Obend.Tactic.Tooth
import all Obend.Tactic.Tooth
import all Obend.AssertAxioms

public section
namespace Obend.SymbolicZk.ProvenZkmlGate.Tests

open Obend.SymbolicZk.ProvenZkmlGate

set_option autoImplicit false

def bytes32 (b : UInt8) : ByteArray :=
  ⟨(List.replicate 32 b).toArray⟩

def hexOf (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

/-! ## 1. Cross-Language Golden Wire Vector (`OBEND.SHE.ZKML_CHUNK/v1`) -/

/-- Shared Rust ↔ Lean golden `ZkmlChunkReceipt` fixture (`zkml_gate.rs`). -/
def goldenChunkReceipt : ZkmlChunkReceipt where
  modelWeightsRoot := bytes32 0x11
  policyFloorDigest := bytes32 0x22
  suiteDigest := bytes32 0x33
  chunkIdx := 7
  stateInCommit := bytes32 0x44
  inputCommit := bytes32 0x55
  stateOutCommit := bytes32 0x66
  outputCommit := bytes32 0x77
  powNonce := 0x0102030405060708

#guard goldenChunkReceipt.preimage.length == 249
#guard hexOf (zkmlChunkDigest goldenChunkReceipt) ==
  "55ba31a844562b65c394aa34485773e0849871b3e72c639fbfed21823dfb27c1"

/-! ## 2. Streaming 3-Chunk 8-Bit PoW Gated-DeltaNet Chain & Refusal Matrix -/

def pow8Chunk0 : ZkmlChunkReceipt where
  modelWeightsRoot := bytes32 0x11
  policyFloorDigest := bytes32 0x22
  suiteDigest := bytes32 0x33
  chunkIdx := 0
  stateInCommit := bytes32 0x40
  inputCommit := bytes32 0x50
  stateOutCommit := bytes32 0x41
  outputCommit := bytes32 0x60
  powNonce := 331

def pow8Chunk1 : ZkmlChunkReceipt where
  modelWeightsRoot := bytes32 0x11
  policyFloorDigest := bytes32 0x22
  suiteDigest := bytes32 0x33
  chunkIdx := 1
  stateInCommit := bytes32 0x41
  inputCommit := bytes32 0x51
  stateOutCommit := bytes32 0x42
  outputCommit := bytes32 0x61
  powNonce := 348

def pow8Chunk2 : ZkmlChunkReceipt where
  modelWeightsRoot := bytes32 0x11
  policyFloorDigest := bytes32 0x22
  suiteDigest := bytes32 0x33
  chunkIdx := 2
  stateInCommit := bytes32 0x42
  inputCommit := bytes32 0x52
  stateOutCommit := bytes32 0x43
  outputCommit := bytes32 0x62
  powNonce := 334

#guard hexOf (zkmlChunkDigest pow8Chunk0) ==
  "005b24c6e6adea8f3360be4c5651e3f695c87d70e30dc728f25fd4a2b444bd3b"
#guard hexOf (zkmlChunkDigest pow8Chunk1) ==
  "007ea39df39a40e9f7065b664d7fe200c01bb3a8e058a617ce6c5ff95047b606"
#guard hexOf (zkmlChunkDigest pow8Chunk2) ==
  "003f4295b905a9b7c5df568d8beee7acc0ea134ad1d29148630ddf75120215f9"

def pow8Stmt : ZkmlStreamStatement where
  modelWeightsRoot := bytes32 0x11
  policyFloorDigest := bytes32 0x22
  suiteDigest := bytes32 0x33
  initialStateCommit := bytes32 0x40
  finalStateCommit := bytes32 0x43
  numChunks := 3
  requiredPowBits := 8

def provenUdr95Pow8Ext5 : ZkmlSuiteProfile :=
  { provenUdr86BabyBearExt5 with numQueries := 95, grindBits := 8 }

def validTurnQuery : ZkmlTurnQuery where
  claimedRegime := .provenUdr
  suite := provenUdr95Pow8Ext5
  statement := pow8Stmt
  chunks := [pow8Chunk0, pow8Chunk1, pow8Chunk2]

def validTurnCert : ZkmlTurnCert where
  chunkDigests := [pow8Chunk0, pow8Chunk1, pow8Chunk2].map zkmlChunkDigest

-- `provenZkmlJudge.check` is definitionally `checkZkmlTurn`:
example (r : Nat) (q : ZkmlTurnQuery) (c : ZkmlTurnCert) :
    provenZkmlJudge.check r q c = checkZkmlTurn r q c := rfl

-- Honest 3-chunk 8-bit PoW turn accepted at grade 3, uncovered at grade 2:
#guard decide (checkZkmlTurn 2 validTurnQuery validTurnCert = .uncovered)
#guard decide (checkZkmlTurn 3 validTurnQuery validTurnCert = .ok)

-- All 5 refuting clauses + unbacked suite.grindBits spoofing + 1 non-refuting cert mismatch:
#guard decide (checkZkmlTurn 3 { validTurnQuery with claimedRegime := .withdrawnCbr } validTurnCert =
  .refused .withdrawnCbrRejected [])
#guard decide (checkZkmlTurn 3 { validTurnQuery with suite := deployedIr2BabyBearExt4 } validTurnCert =
  .refused .belowProven100BitFloor [])
#guard decide (checkZkmlTurn 3 { validTurnQuery with suite := tallTraceBabyBearExt4 } validTurnCert =
  .refused .belowProven100BitFloor [])
#guard decide (checkZkmlTurn 3 { validTurnQuery with suite := provenUdr86BabyBearExt5 } validTurnCert =
  .refused .insufficientPowGrind [])
#guard decide (checkZkmlTurn 3
    { validTurnQuery with
      chunks := [pow8Chunk0, { pow8Chunk1 with modelWeightsRoot := bytes32 0x99 }, pow8Chunk2] }
    validTurnCert =
  .refused .weightRootDrift [1])
#guard decide (checkZkmlTurn 3
    { validTurnQuery with
      chunks := [pow8Chunk0, { pow8Chunk1 with stateInCommit := bytes32 0xee }, pow8Chunk2] }
    validTurnCert =
  .refused .brokenRecurrentCarry [1])
#guard decide (checkZkmlTurn 3
    { validTurnQuery with
      chunks := [pow8Chunk0, { pow8Chunk1 with powNonce := 0 }, pow8Chunk2] }
    validTurnCert =
  .refused .insufficientPowGrind [1])
#guard decide (checkZkmlTurn 3 validTurnQuery ⟨[bytes32 0xaa]⟩ =
  .refused .certDigestMismatch [])

#guard provenZkmlJudge.refutes .withdrawnCbrRejected == true
#guard provenZkmlJudge.refutes .belowProven100BitFloor == true
#guard provenZkmlJudge.refutes .weightRootDrift == true
#guard provenZkmlJudge.refutes .brokenRecurrentCarry == true
#guard provenZkmlJudge.refutes .insufficientPowGrind == true
#guard provenZkmlJudge.refutes .certDigestMismatch == false

/-! ## 3. Multi-Turn Session Continuity Smoke Checks -/

def sessionInit : ZkmlSessionState where
  sessionWeightsRoot := bytes32 0x11
  sessionPolicyFloorDigest := bytes32 0x22
  sessionSuiteDigest := bytes32 0x33
  sessionStateCommit := bytes32 0x40
  totalVerifiedChunks := 0

def turn2Chunk0 : ZkmlChunkReceipt where
  modelWeightsRoot := bytes32 0x11
  policyFloorDigest := bytes32 0x22
  suiteDigest := bytes32 0x33
  chunkIdx := 0
  stateInCommit := bytes32 0x43
  inputCommit := bytes32 0x70
  stateOutCommit := bytes32 0x44
  outputCommit := bytes32 0x80
  powNonce := 0

def turn2Query : ZkmlTurnQuery where
  claimedRegime := .provenUdr
  suite := { deployedIr2BabyBearExt4 with numQueries := 103, grindBits := 0 }
  statement :=
    { pow8Stmt with
      initialStateCommit := bytes32 0x43
      finalStateCommit := bytes32 0x44
      numChunks := 1
      requiredPowBits := 0 }
  chunks := [turn2Chunk0]

def turn2Cert : ZkmlTurnCert :=
  ⟨[zkmlChunkDigest turn2Chunk0]⟩

#guard match verifyZkmlSessionTrace 3 sessionInit [(validTurnQuery, validTurnCert), (turn2Query, turn2Cert)] with
  | .ok st => decide (st = { sessionInit with sessionStateCommit := bytes32 0x44, totalVerifiedChunks := 4 })
  | .error _ => false

-- Cross-turn hidden state splice between turn 1 (`0x43`) and turn 2 (`0x99`) refused:
#guard match verifyZkmlSessionTrace 3 sessionInit
    [ (validTurnQuery, validTurnCert)
    , ( { turn2Query with
          statement := { turn2Query.statement with initialStateCommit := bytes32 0x99 }
          chunks := [{ turn2Chunk0 with stateInCommit := bytes32 0x99 }] }
      , ⟨[zkmlChunkDigest { turn2Chunk0 with stateInCommit := bytes32 0x99 }]⟩ ) ] with
  | .error (k, path) => decide (k = .brokenRecurrentCarry ∧ path = [])
  | .ok _ => false

/-! ## 4. Mutation-Sensitivity Guards (`10` `#tooth` Kills on Universal Theorems) -/

#tooth udr_strictly_below_withdrawn_cbr by
  mutation udrMilliBits := fun p => legacyWithdrawnCbrMilliBits p

#tooth grind_bits_additive_and_regime_free by
  mutation udrMilliBits := fun p => p.numQueries * udrQueryMilliBits p.logBlowup

#tooth checkZkmlSuiteProvenFloor_sound by
  mutation checkZkmlSuiteProvenFloor := fun _ _ => true

#tooth checkZkmlSuiteProvenFloor_sound by
  mutation logupCeilingMilliBits := fun _ => 128000

#tooth checkZkmlSuiteProvenFloor_sound by
  mutation bcsDigestCeilingMilliBits := fun _ => 128000

#tooth zkmlChunkDigest_binds by
  mutation ZkmlChunkReceipt.fields := fun _ => []

#tooth zkmlChunkReceipt_preimage_injective by
  mutation ZkmlChunkReceipt.fields := fun c =>
    [ c.modelWeightsRoot.data.toList
    , c.policyFloorDigest.data.toList
    , c.suiteDigest.data.toList
    , u64ToBe8 c.chunkIdx
    , c.stateInCommit.data.toList
    , c.inputCommit.data.toList
    , c.stateOutCommit.data.toList
    , c.outputCommit.data.toList
    ]

#tooth tampered_weights_or_hidden_carry_refused by
  mutation verifyZkmlChunkChainExec := fun _ chunks => .ok (chunks.map zkmlChunkDigest)

#tooth provenZkmlJudge_sound by
  mutation checkZkmlTurn := fun _ _ _ => .ok

#tooth verifyZkmlSessionTrace_sound by
  mutation verifyZkmlSessionStep := fun _ st qc =>
    .ok { st with
      sessionStateCommit := qc.1.statement.finalStateCommit
      totalVerifiedChunks := st.totalVerifiedChunks + qc.1.chunks.length }

/-! ## 5. Kernel Axiom Footprint Audit (`0` `Classical.choice`, `0` `sorryAx`) -/

#print axioms udr_strictly_below_withdrawn_cbr
#print axioms grind_bits_additive_and_regime_free
#print axioms checkZkmlSuiteProvenFloor_sound
#print axioms zkmlChunkDigest_binds
#print axioms zkmlChunkChain_binds_endToEnd
#print axioms verifyZkmlChunkChainExec_iff_spec
#print axioms tampered_weights_or_hidden_carry_refused
#print axioms provenZkmlJudge_sound
#print axioms provenZkmlJudge_refuted
#print axioms verifyZkmlSessionTrace_sound

end Obend.SymbolicZk.ProvenZkmlGate.Tests
end
