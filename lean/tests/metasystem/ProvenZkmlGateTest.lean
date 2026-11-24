module
/-
# ProvenZkmlGateTest — `EinSumcheck` + Native `MXFP4` (`E2M1`) Golden Vectors, `UD-100` Matrix & `#tooth` Kills

Tests and mutation-sensitivity guards for `Obend.SymbolicZk.EinSumcheckMxfp4` & `ProvenZkmlGate`:
1. Byte-for-byte cross-language golden wire vectors (`OBEND.SHE.ZKML_SUITE/v1`, `OBEND.SHE.ZKML_WEIGHTS/v1`,
   `OBEND.SHE.ZKML_MERKLE/v1`, `SuccinctMxfp4IopProof` with round degrees `(2^logB, 3^logK, 3^logJ)`,
   and `OBEND.SHE.ZKML_CHUNK/v1`) locked with `crates/obend-prove-worker/tests/zkml_she_gate_test.rs`.
2. Real 2-layer 8-bit post-commit PoW `MXFP4` contraction stream (`nonces = [145, 289]`, with `w - 1`
   provably invalid: `144` and `288` rejected!), `UD-100` small-leaf `(6, 86, 16)` vs `q=85` and
   wide-leaf `(2, 148, 0, logArity=4)` vs `q=147`, plus concrete refusal witnesses across all
   7 refuting clauses (including truncated prefix & out-of-order `layerIdx` refusal!).
3. `#tooth` mutation kills across `EinSumcheckMxfp4` & `ProvenZkmlGate` + programmatic `run_cmd`
   verifier asserting `0 Classical.choice` / `0 noncomputable` on all `Type`-valued extractors and
   `0 sorryAx` across all flagship soundness theorems.
-/
public import Obend.SymbolicZk.ProvenZkmlGate
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import all Obend.SymbolicZk.ProvenZkmlGate
meta import all Obend.SymbolicZk.EinSumcheckMxfp4
meta import all Obend.Judge.Class
meta import all Obend.Crypto.PCS
meta import all Obend.Crypto.Sumcheck
meta import all Obend.Crypto.Multilinear
meta import all Obend.Crypto.Transcript
meta import all Obend.Apps.ZkNtt.Goldilocks
meta import all Obend.Digest.Cshake256
meta import all Obend.Digest.Cshake256.Fast
meta import all Obend.Digest.Cshake256.Seam
meta import all Obend.Digest.Cshake256.Spec
meta import all Obend.Digest.HashBytes
meta import all Obend.Codec.Hex
import all Obend.SymbolicZk.EinSumcheckMxfp4
import all Obend.SymbolicZk.ProvenZkmlGate
import all Obend.Judge.Class
import all Obend.Crypto.Transcript
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.PCS
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Codec.Hex
import all Obend.Tactic.Tooth
import all Obend.AssertAxioms

public section
namespace Obend.SymbolicZk.ProvenZkmlGate.Tests

open Obend.Apps.ZkNtt Obend.Crypto Obend.SymbolicZk.ProvenZkmlGate

set_option autoImplicit false

def bytes32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩


/-! ## 1. Cross-Language Golden `MXFP4` `EinSumcheck` Vectors (`zkml_she_gate_test.rs` Parity) -/

-- Exact `MXFP4` contraction table `[71, 13, p - 80, 88]` on `(logI=1, logJ=1, logK=1, logB=1)`:
#guard sampleMxfp4Witness0.dTbl ==
  [ Goldilocks.ofNat 71
  , Goldilocks.ofNat 13
  , CommRingOps.sub Goldilocks.zero (Goldilocks.ofNat 80)
  , Goldilocks.ofNat 88 ]

-- Exact `(2^logB, 3^logK, 3^logJ)` degree schedule (never degree 4!):
#guard mxfp4DegSchedule 5 3 2 == [2, 2, 2, 2, 2, 3, 3, 3, 3, 3]
#guard isValidE2m1Mantissa (-12) == true
#guard isValidE2m1Mantissa 5 == false
#guard isValidMxfp4Shift 30 == true
#guard isValidMxfp4Shift 31 == false

def assertKat (label : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError s!"ProvenZkmlGateTest KAT failed: {label}")

-- `UD-100` boundary pricing: `q=85` (`99,045` mbit) vs `q=86` (`100,022` mbit) on `(lb=6, pow=16)`
-- and `q=147` (`99,666` mbit) vs `q=148` (`100,344` mbit) on wide-leaf `(lb=2, pow=0, logArity=4)`:
#guard checkZkmlSuiteProvenFloor .provenUdr { provenUdrGoldilocksExt2 with numQueries := 85 } == false
#guard checkZkmlSuiteProvenFloor .provenUdr provenUdrGoldilocksExt2 == true
#guard checkZkmlSuiteProvenFloor .provenUdr { wideLeafUdr148GoldilocksExt2 with numQueries := 147 } == false
#guard checkZkmlSuiteProvenFloor .provenUdr wideLeafUdr148GoldilocksExt2 == true
#guard checkZkmlSuiteProvenFloor .provenUdr zeroLogArityGoldilocksExt2 == false
#guard checkZkmlSuiteProvenFloor .withdrawnCbr deployedIr2BabyBearExt4 == false

/-! ## 2. Cross-Language Golden KATs, 8-Bit PoW (`[145, 289]`), Refusals & Session Continuity -/

#eval show IO Unit from do
  -- 1. Byte-for-byte parity with `crates/obend-prove-worker/tests/zkml_she_gate_test.rs`:
  let goldenIopSuite : ZkmlSuiteProfile := ⟨64, 2, 2, 2, 0, 20, 256, 4⟩
  let goldenChunk0 := proveMxfp4ChunkIop goldenIopSuite (bytes32 0x22) goldenIopSuite.digest 0 sampleChainWitness0 0
  let goldenChunk1 := proveMxfp4ChunkIop goldenIopSuite (bytes32 0x22) goldenIopSuite.digest 1 sampleChainWitness1 0
  assertKat "goldenChunk0 degrees"
    ((goldenChunk0.iopProof.sumcheckRounds.map fun r => r.coeffs.length) == [3, 4, 4, 4])
  assertKat "goldenChunk1 degrees"
    ((goldenChunk1.iopProof.sumcheckRounds.map fun r => r.coeffs.length) == [3, 4, 4])
  assertKat "golden carry" (goldenChunk0.stateOutCommit == goldenChunk1.stateInCommit)
  assertKat "goldenIopSuite.digest"
    (Obend.Codec.Hex.byteArrayToHex goldenIopSuite.digest == "34a5a0f8a1b87b1c386f07b60e44574cf021693c388890d404565d56a3144499")
  assertKat "sampleChainModel.root"
    (Obend.Codec.Hex.byteArrayToHex sampleChainModel.root == "762f45dde0a05eed9cd34395e82a02a6a62308ffe0bdd625485225e0b373eae5")
  assertKat "goldenChunk0.stateInCommit"
    (Obend.Codec.Hex.byteArrayToHex goldenChunk0.stateInCommit == "ba697cdee5e9c34eba685d0bed9067e6326a4da6b2d586e645328a42cef8ef1e")
  assertKat "goldenChunk0.stateOutCommit"
    (Obend.Codec.Hex.byteArrayToHex goldenChunk0.stateOutCommit == "9ad1dbd66b7c9169ddc14ceb281d8b754a33345506add4b9533eaf1fcacee467")
  assertKat "goldenChunk1.stateOutCommit"
    (Obend.Codec.Hex.byteArrayToHex goldenChunk1.stateOutCommit == "384c2c6b9d228ec4a7823b3619867d96f22a51cfbbbbbd1851e9b7e35f2d0c3b")
  assertKat "goldenChunk0 iopProof bytes"
    ((encodeSuccinctMxfp4IopProof goldenChunk0.iopProof).length == 3063)
  assertKat "goldenChunk0 preimage bytes" (goldenChunk0.preimage.length == 3314)
  assertKat "goldenChunk0 digest"
    (Obend.Codec.Hex.byteArrayToHex (zkmlChunkDigest goldenChunk0) == "46f7fb825d329096db84770071f1cadad8900ab87b89476c42a40e310ea5cd58")
  assertKat "goldenChunk1 digest"
    (Obend.Codec.Hex.byteArrayToHex (zkmlChunkDigest goldenChunk1) == "514ba9e346519b4f80831bdf63171581100e5c55963c9ef190232627429fecd7")
  assertKat "verify goldenChunk0" (verifyMxfp4ChunkIop goldenIopSuite sampleChainModel 0 goldenChunk0)
  assertKat "verify goldenChunk1" (verifyMxfp4ChunkIop goldenIopSuite sampleChainModel 0 goldenChunk1)
  assertKat "zero-pow nonzero nonce refused"
    (!verifyMxfp4ChunkIop goldenIopSuite sampleChainModel 0
      { goldenChunk0 with iopProof := { goldenChunk0.iopProof with powNonce := 1 } })

  -- 2. 8-bit post-commit PoW grinding (`[145, 289]`), zero-span `none`, and `w - 1` (`144`, `288`) invalid:
  let pow8Suite : ZkmlSuiteProfile := ⟨64, 2, 6, 95, 8, 20, 256, 1⟩
  assertKat "pow8Suite.digest"
    (Obend.Codec.Hex.byteArrayToHex pow8Suite.digest == "0143dab34e24656cc84341a732c5300bf03943afa6b33248b6d2bfc78e7033b1")
  let pow8Chunk0 := proveMxfp4ChunkIop pow8Suite (bytes32 0x22) pow8Suite.digest 0 sampleChainWitness0 145
  let pow8Chunk1 := proveMxfp4ChunkIop pow8Suite (bytes32 0x22) pow8Suite.digest 1 sampleChainWitness1 289
  assertKat "grindChunkPowWindowed chunk0 = 145 & span=0 none"
    (match runMxfp4SumcheckPhase pow8Suite pow8Chunk0 with
     | some (_, _, _, _, _, _, trPF) =>
       grindChunkPowWindowed 0 0 1 trPF == none && grindChunkPowWindowed 8 512 64 trPF == some 145
     | none => false)
  assertKat "grindChunkPowWindowed chunk1 = 289"
    (match runMxfp4SumcheckPhase pow8Suite pow8Chunk1 with
     | some (_, _, _, _, _, _, trPF) => grindChunkPowWindowed 8 512 64 trPF == some 289
     | none => false)
  assertKat "pow8Chunk0 pow valid" (checkMxfp4ChunkPow pow8Suite 8 pow8Chunk0)
  assertKat "pow8Chunk0 w-1=144 invalid"
    (!checkMxfp4ChunkPow pow8Suite 8 { pow8Chunk0 with iopProof := { pow8Chunk0.iopProof with powNonce := 144 } })
  assertKat "pow8Chunk1 pow valid" (checkMxfp4ChunkPow pow8Suite 8 pow8Chunk1)
  assertKat "pow8Chunk1 w-1=288 invalid"
    (!checkMxfp4ChunkPow pow8Suite 8 { pow8Chunk1 with iopProof := { pow8Chunk1.iopProof with powNonce := 288 } })
  assertKat "pow8Chunk0 digest"
    (Obend.Codec.Hex.byteArrayToHex (zkmlChunkDigest pow8Chunk0) == "f237251918da6520f706e72c8748e5cad6c4c3e3213994984ff81eca78ba0e3e")
  assertKat "pow8Chunk1 digest"
    (Obend.Codec.Hex.byteArrayToHex (zkmlChunkDigest pow8Chunk1) == "73b5c347c45dc42989521240f69c4bfc5f99544aa7b78835d9a89cd92150f774")

  -- 3. `checkZkmlTurn` acceptance & full 7-clause refusal matrix:
  let pow8Stmt : ZkmlStreamStatement :=
    { modelWeightsRoot := sampleChainModel.root, policyFloorDigest := bytes32 0x22
      suiteDigest := pow8Suite.digest, initialStateCommit := pow8Chunk0.stateInCommit
      finalStateCommit := pow8Chunk1.stateOutCommit, numChunks := 2, requiredPowBits := 8, pinnedNumQueries := some 95 }
  let validTurnQuery : ZkmlTurnQuery :=
    { claimedRegime := .provenUdr, suite := pow8Suite, model := sampleChainModel
      statement := pow8Stmt, chunks := [pow8Chunk0, pow8Chunk1] }
  let validTurnCert : ZkmlTurnCert := ⟨[zkmlChunkDigest pow8Chunk0, zkmlChunkDigest pow8Chunk1]⟩
  assertKat "validTurnQuery ok" (checkZkmlTurn 2 validTurnQuery validTurnCert == .ok)
  assertKat "withdrawnCbr refused"
    (checkZkmlTurn 2 { validTurnQuery with claimedRegime := .withdrawnCbr } validTurnCert ==
      .refused .withdrawnCbrRejected [])
  assertKat "provenJbr refused"
    (checkZkmlTurn 2 { validTurnQuery with claimedRegime := .provenJbr } validTurnCert ==
      .refused .belowProven100BitFloor [])
  assertKat "zeroLogArity refused"
    (checkZkmlTurn 2 { validTurnQuery with suite := zeroLogArityGoldilocksExt2 } validTurnCert ==
      .refused .unpinnedOrZeroAritySuite [])
  assertKat "unpinnedNumQueries refused"
    (checkZkmlTurn 2 { validTurnQuery with statement := { pow8Stmt with pinnedNumQueries := none } } validTurnCert ==
      .refused .unpinnedOrZeroAritySuite [])
  assertKat "weightRootDrift refused"
    (checkZkmlTurn 2 { validTurnQuery with statement := { pow8Stmt with modelWeightsRoot := bytes32 0xee } }
      validTurnCert == .refused .weightRootDrift [])
  assertKat "suiteDigest spoof refused"
    (checkZkmlTurn 2 { validTurnQuery with statement := { pow8Stmt with suiteDigest := bytes32 0x99 } }
      validTurnCert == .refused .weightRootDrift [])
  assertKat "insufficientPowGrind w-1=144 refused"
    (checkZkmlTurn 2
      { validTurnQuery with chunks :=
          [{ pow8Chunk0 with iopProof := { pow8Chunk0.iopProof with powNonce := 144 } }, pow8Chunk1] }
      validTurnCert == .refused .insufficientPowGrind [0])
  let r0 := pow8Chunk0.iopProof.sumcheckRounds[0]!
  let deg3InBRoundChunk0 : ZkmlChunkReceipt :=
    { pow8Chunk0 with iopProof :=
        { pow8Chunk0.iopProof with sumcheckRounds := ⟨r0.coeffs ++ [Goldilocks.zero]⟩ :: pow8Chunk0.iopProof.sumcheckRounds.drop 1 } }
  assertKat "degree-3 in b-round refused" (!verifyMxfp4ChunkIop pow8Suite sampleChainModel 8 deg3InBRoundChunk0)
  let q0 := pow8Chunk0.iopProof.queryOpenings[0]!
  let badE2m1Chunk0 : ZkmlChunkReceipt :=
    { pow8Chunk0 with iopProof :=
        { pow8Chunk0.iopProof with queryOpenings := { q0 with qMantissa := 5 } :: pow8Chunk0.iopProof.queryOpenings.drop 1 } }
  assertKat "invalid E2M1 mantissa 5 refused"
    (checkZkmlTurn 2 { validTurnQuery with chunks := [badE2m1Chunk0, pow8Chunk1] } validTurnCert ==
      .refused .invalidChunkIopProof [0])
  assertKat "broken inter-layer carry refused"
    (checkZkmlTurn 2
      { validTurnQuery with chunks := [pow8Chunk0, { pow8Chunk1 with stateInCommit := bytes32 0xaa }] }
      validTurnCert == .refused .brokenRecurrentCarry [1])
  assertKat "truncated 1-chunk prefix of 2-layer model refused"
    (checkZkmlTurn 2
      { validTurnQuery with
        statement := { pow8Stmt with finalStateCommit := pow8Chunk0.stateOutCommit, numChunks := 1 }
        chunks := [pow8Chunk0] }
      ⟨[zkmlChunkDigest pow8Chunk0]⟩ == .refused .brokenRecurrentCarry [1])
  assertKat "out-of-order layerIdx refused"
    (checkZkmlTurn 2
      { validTurnQuery with chunks := [pow8Chunk0, { pow8Chunk1 with layerIdx := 0 }] }
      validTurnCert == .refused .brokenRecurrentCarry [1])

  -- 4. Multi-turn SHE session continuity (`8 -> 8 -> 8`) & cross-turn splice refusal:
  let sessionModel1 : Mxfp4ModelManifest := ⟨[sampleChainLayer0]⟩
  let sessionW1 := buildHonestMxfp4Witness sessionModel1 0 1 2 1 1 sampleMxfp4X0 sampleChainQ0 sampleChainS0
  let sessionW2 := buildHonestMxfp4Witness sessionModel1 0 1 2 1 1 sessionW1.dTbl sampleChainQ0 sampleChainS0
  let sessionChunk1 := proveMxfp4ChunkIop wideLeafUdr148GoldilocksExt2 (bytes32 0x22) wideLeafUdr148GoldilocksExt2.digest 0 sessionW1 0
  let sessionChunk2 := proveMxfp4ChunkIop wideLeafUdr148GoldilocksExt2 (bytes32 0x22) wideLeafUdr148GoldilocksExt2.digest 0 sessionW2 0
  let sessionInit : ZkmlSessionState :=
    { sessionWeightsRoot := sessionModel1.root, sessionPolicyFloorDigest := bytes32 0x22
      sessionSuiteDigest := wideLeafUdr148GoldilocksExt2.digest
      sessionStateCommit := sessionChunk1.stateInCommit, totalVerifiedChunks := 0 }
  let turn1Query : ZkmlTurnQuery :=
    { claimedRegime := .provenUdr, suite := wideLeafUdr148GoldilocksExt2, model := sessionModel1
      statement :=
        { modelWeightsRoot := sessionModel1.root, policyFloorDigest := bytes32 0x22
          suiteDigest := wideLeafUdr148GoldilocksExt2.digest
          initialStateCommit := sessionChunk1.stateInCommit, finalStateCommit := sessionChunk1.stateOutCommit
          numChunks := 1, requiredPowBits := 0, pinnedNumQueries := some 148 }
      chunks := [sessionChunk1] }
  let turn2Query : ZkmlTurnQuery :=
    { turn1Query with
      statement := { turn1Query.statement with
        initialStateCommit := sessionChunk2.stateInCommit, finalStateCommit := sessionChunk2.stateOutCommit }
      chunks := [sessionChunk2] }
  let turn1Cert : ZkmlTurnCert := ⟨[zkmlChunkDigest sessionChunk1]⟩
  let turn2Cert : ZkmlTurnCert := ⟨[zkmlChunkDigest sessionChunk2]⟩
  assertKat "2-turn session continuity"
    (match verifyZkmlSessionTrace 1 sessionInit [(turn1Query, turn1Cert), (turn2Query, turn2Cert)] with
     | .ok st => decide (st = { sessionInit with
         sessionStateCommit := sessionChunk2.stateOutCommit, totalVerifiedChunks := 2 })
     | .error _ => false)
  assertKat "cross-turn hidden state splice refused"
    (match verifyZkmlSessionTrace 1 sessionInit
        [ (turn1Query, turn1Cert)
        , ({ turn2Query with statement := { turn2Query.statement with initialStateCommit := bytes32 0x99 } }, turn2Cert) ] with
     | .error (k, path) => decide (k = .brokenRecurrentCarry ∧ path = [])
     | .ok _ => false)

/-! ## 4. Mutation-Sensitivity Guards (`#tooth` Kills Across `EinSumcheckMxfp4` & `ProvenZkmlGate`) -/

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

#tooth zkmlSuiteProfile_digest_binds by
  mutation ZkmlSuiteProfile.encode := fun p => encodeZkmlFields [leb128 p.logBlowup]

#tooth mxfp4DegSchedule_never_deg_four by
  mutation mxfp4DegSchedule := fun _ _ _ => [4]

#tooth windowedFindMapFirst_minimal_and_pred_invalid by
  mutation windowedFindMapLoop := fun scan _ base _ =>
    match scan (base + 1) with | some v => some (base + 1, v) | none => none

#tooth grindChunkPowWindowed_sound_and_pred_invalid by
  mutation grindChunkPowWindowed := fun _ _ _ _ => some 1

#tooth proveQuadRounds_no_rootHit by
  mutation proveQuadRounds := fun _ A B tr => ([⟨[CommRingOps.one]⟩], [], A, B, tr)

#tooth verifyFoldWalk_deviates_pair by
  mutation verifyFoldWalk := fun _ _ _ _ _ _ _ _ => true

#tooth encodeSuccinctMxfp4IopProof_injective by
  mutation encodeSuccinctMxfp4IopProof := fun p => encodeZkmlFields [leb128 p.logI]

#tooth zkmlChunkDigest_binds by
  mutation ZkmlChunkReceipt.fields := fun _ => []

#tooth zkmlChunkReceipt_preimage_injective by
  mutation ZkmlChunkReceipt.fields := fun c =>
    [ c.modelWeightsRoot.data.toList, c.policyFloorDigest.data.toList, c.suiteDigest.data.toList ]

#tooth proveMxfp4ChunkIop_complete by
  mutation buildFoldRoots := fun _ _ _ _ => []

#tooth verifyMxfp4ChunkIop_sound by
  mutation verifyMxfp4ChunkIop := fun _ _ _ _ => true

#tooth verifyMxfp4ChunkIop_sound by
  mutation checkChunkPow := fun _ _ => true

#tooth verifyMxfp4ChunkIop_sound by
  mutation verifyMxfp4QueryLocal := fun _ _ _ => true

#tooth tampered_weights_or_hidden_carry_refused by
  mutation verifyZkmlChunkChainExec := fun _ _ _ chunks => .ok (chunks.map zkmlChunkDigest)

#tooth provenZkmlJudge_sound by
  mutation checkZkmlTurn := fun _ _ _ => .ok

#tooth verifyZkmlSessionTrace_sound by
  mutation verifyZkmlSessionStep := fun _ st qc =>
    .ok { st with
      sessionStateCommit := qc.1.statement.finalStateCommit
      totalVerifiedChunks := st.totalVerifiedChunks + qc.1.chunks.length }

/-! ## 5. Kernel Axiom Footprint Audit (`0` `Classical.choice` in Extractors, `0` `sorryAx`) -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for decl in [``extractZkmlCshake32, ``extractZkmlSuiteProfileBinding,
               ``extractMxfp4ModelBinding, ``extractZkmlMerkleAt, ``extractZkmlChunkBinding] do
    if Lean.isNoncomputable env decl then
      throwError m!"{decl} is noncomputable (must be constructive executable Type data!)"
    let axs ← collectAxioms decl
    for ax in axs do
      if ax == ``Classical.choice || !Obend.AssertAxioms.standard.contains ax then
        throwError m!"{decl} depends on forbidden axiom {ax}: {axs.toList}"
  for thm in [``windowedFindMapFirst_minimal_and_pred_invalid, ``grindChunkPowWindowed_sound_and_pred_invalid,
              ``einsum2Op_mle_identity, ``naive_batched_matmul_incomplete, ``gqa_rounds_and_kv_savings,
              ``mxfp4DegSchedule_never_deg_four, ``proveQuadRounds_no_rootHit, ``openFoldWalk_no_discrepancy,
              ``verifyFoldWalk_deviates_pair, ``proveMxfp4Sumcheck_complete, ``verifyMxfp4Sumcheck_sound,
              ``proveMxfp4ChunkIop_complete, ``verifyMxfp4ChunkIop_sound, ``verifyMxfp4ChunkIop_registered_sound,
              ``udr_strictly_below_withdrawn_cbr, ``ud100_small_and_wide_leaf_minimality,
              ``grind_bits_additive_and_regime_free, ``checkZkmlSuiteProvenFloor_sound,
              ``zkmlChunkDigest_binds, ``zkmlChunkChain_binds_endToEnd, ``verifyZkmlChunkChainExec_iff_spec,
              ``tampered_weights_or_hidden_carry_refused, ``provenZkmlJudge_sound,
              ``zkmlTurnMeaning_contraction_sound, ``provenZkmlJudge_refuted, ``verifyZkmlSessionTrace_sound] do
    let axs ← collectAxioms thm
    for ax in axs do
      if !Obend.AssertAxioms.standard.contains ax then
        throwError m!"{thm} depends on non-standard axiom {ax}: {axs.toList}"

end Obend.SymbolicZk.ProvenZkmlGate.Tests
end
