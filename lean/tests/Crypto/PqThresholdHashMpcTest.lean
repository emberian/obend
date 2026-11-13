module
/-
# Tests.Crypto.PqThresholdHashMpcTest — `#tooth` Mutation Witnesses, Inhabitedness & Cross-Lang Wire Vectors
Verifies `ThresholdMpcUcGames`, `PqHashSignatures`, and `ThresholdHashMpc`:
1. All 5 mandatory `#tooth` mutation-sensitivity witnesses (`checkTargetSum`, `stepEpochLatch`,
   `encodeAdrs`, `formBdozPartyMacShare` + `verifyBatchTowerMac2Lane`, `checkHybridPinning`);
2. Inhabitedness & query-regime characterization (`lazyRo_query_regime_characterization`, `not_universal_romFaithful`,
   `shamir_tower_rebalance_involutive`, `full_collusion_breaks_hiding`, `unpadded_open_refutes_hiding`,
   `ValidPqCustodyMpcTrace` multi-turn sign + crash-retry + double-sign refusal + membrane revocation);
3. Byte-exact cross-language golden vectors shared with `crates/obend-pq-mpc`;
4. `#print axioms` kernel audit (`0 Classical.choice` in `extractPqHashForgery` & `bdoz_cheater_identified_or_mac_forged`).
-/
public import Obend.Crypto.ThresholdMpcUcGames
public import Obend.Crypto.PqHashSignatures
public import Obend.Polis.PqThresholdCustody
import all Obend.Polis.PqThresholdCustody
import all Obend.Crypto.ThresholdHashMpc
meta import Obend.Crypto.ThresholdMpcUcGames
meta import Obend.Crypto.PqHashSignatures
meta import Obend.Polis.PqThresholdCustody
import all Init.Data.String.Defs
import all Init.Data.ByteArray.Basic
import all Init.Data.Array.Basic
import all Init.Data.UInt.Basic
import all Init.Data.UInt.Bitwise
import all Init.Data.BitVec.Basic
import all Init.Data.List.Basic
import all Init.Data.List.Impl
import all Obend.Crypto.ThresholdMpcUcGames
import all Obend.Crypto.PqHashSignatures
import all Obend.Crypto.BinaryTower256
import all Obend.Crypto.Poseidon2Goldilocks
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Judge.Computational
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Polis.GrainPowerbox
import all Obend.Polis.ZkBiscuit
import all Obend.Polis.CapTP
import all Obend.OS.Sel4MicrokitKernel
import all Obend.Hardware.PipelinedRisc
import all Obend.Hardware.GlitchAndTempestSafe
import all Obend.AssertAxioms
import all Obend.Tactic.Tooth

public section
namespace Obend.Tests.Crypto.PqThresholdHashMpcTest

open Obend
open Obend.Apps.ZkNtt
open Obend.Crypto
open Obend.Crypto.BinaryTower256
open Obend.Crypto.ThresholdMpcUcGames
open Obend.Crypto.PqHashSignatures
open Obend.Crypto.ThresholdHashMpc
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Judge.Computational
open Obend.Polis
open Obend.Polis.GrainPowerbox

set_option autoImplicit false
set_option Elab.async false

/-- Hex encoder for byte-exact cross-language wire vector parity with `crates/obend-pq-mpc`. -/
def hexBytes (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun x =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

/-! ## 1. `ThresholdMpcUcGames` Inhabitedness & Non-Vacuity Witnesses -/

example :
    deployedCardGoldilocks4 ≠ deployedCardBitVec256 ∧
    2 ^ 255 < deployedCardGoldilocks4 ∧ deployedCardGoldilocks4 < deployedCardBitVec256 :=
  deployedCardGoldilocks4_ne_bitVec256

example :
    natAbsDiff (keyedPrfRealAccept 8 (fun _ => false) true (zeroQueryHardcoder 8 false))
               (keyedPrfIdealAccept 8 (fun _ => false) (zeroQueryHardcoder 8 false)) = 0 ∧
    (0 < natAbsDiff (keyedPrfRealAccept 8 (fun _ => false) true (oneQueryGuesser 8 (by decide)))
                    (keyedPrfIdealAccept 8 (fun _ => false) (oneQueryGuesser 8 (by decide))) ∧
     QueryBounded 1 (oneQueryGuesser 8 (by decide))) ∧
    2 * 1 < natAbsDiff (keyedPrfRealAccept 8 (fun _ => false) true (buildFullTableReader 8 8 (Nat.le_refl 8)))
                       (keyedPrfIdealAccept 8 (fun _ => false) (buildFullTableReader 8 8 (Nat.le_refl 8))) :=
  lazyRo_query_regime_characterization 8 (by decide) false

example :
    ∃ A : OracleComp Nat (Fin 4) (Fin 4),
      QueryBounded 0 A ∧ ¬ RomFaithfulInstantiation (fun _ => (⟨0, by decide⟩ : Fin 4)) 0 0 A :=
  not_universal_romFaithful (by decide) (fun _ => ⟨0, by decide⟩) 0

example (t : Nat) (corruptPts : List (TowerElem 3)) (w : TowerElem 3)
    (hCard : corruptPts.length + 1 ≤ t) (P : ShamirPadPoly (TowerElem 3) t) :
    let eqv := shamir_rebalanceEquiv (towerInv 3) t corruptPts w hCard
    eqv.toFun (eqv.toFun P) = P :=
  shamir_tower_rebalance_involutive 3 t corruptPts w hCard P

example (P Q : ShamirPadPoly Goldilocks 2)
    (hSame : ∀ xc ∈ [Goldilocks.ofNat 1, Goldilocks.ofNat 2],
      RoundPoly.evalCoeffs P.1 xc = RoundPoly.evalCoeffs Q.1 xc) :
    CommRingOps.add (Goldilocks.ofNat 5) (RoundPoly.evalCoeffs P.1 CommRingOps.zero) ≠
      CommRingOps.add (Goldilocks.ofNat 9) (RoundPoly.evalCoeffs Q.1 CommRingOps.zero) :=
  full_collusion_breaks_hiding 2 [Goldilocks.ofNat 1, Goldilocks.ofNat 2]
    rfl (by decide) (Goldilocks.ofNat 5) (Goldilocks.ofNat 9) (by decide) P Q hSame

example (s1 s2 : Goldilocks) (hNe : s1 ≠ s2) :
    CommRingOps.add s1 CommRingOps.zero ≠ CommRingOps.add s2 CommRingOps.zero :=
  unpadded_open_refutes_hiding s1 s2 hNe

/-! ## 2. Compact End-to-End `PqHashSignatures` & `ThresholdHashMpc` Execution Fixtures -/

def goldenSk : PqSecretKey where
  skSeed := List.range 32 |>.map fun i => UInt8.ofNat (i + 1)
  skPrf  := List.range 32 |>.map fun i => UInt8.ofNat (i + 33)
  pkSeed := List.range 32 |>.map fun i => UInt8.ofNat (i + 65)

def goldenMsg1 : List UInt8 := "obend-pq-mpc-golden-msg-v1".toUTF8.data.toList
def goldenMsg2 : List UInt8 := "obend-pq-mpc-golden-msg-v2".toUTF8.data.toList
def goldenOptRand : List UInt8 := List.replicate 32 (0xA5 : UInt8)

def goldenAdrsSample : HashAdrs where
  layer := 3
  tree := 0x0102030405060708
  kind := .wotsHash
  keyPair := 7
  chainIdx := 11
  hashStep := 2

#guard (encodeAdrs goldenAdrsSample).length == 32
#guard hexBytes (encodeAdrs goldenAdrsSample) ==
  "0000000300000000010203040506070800000000000000070000000b00000002"

#guard hexBytes (encodeMultiFrame [[1, 2], [3, 4, 5]]) == "0202010203030405"

-- Verify concrete `cshake256Suite` stateless `leanSPHINCS` (`compactGoldenParams`) sign + verify + cut-batch:
def goldenPkCshake : PqPublicKey := derivePublicKey cshake256Suite compactGoldenParams goldenSk
def goldenSigCshakeOpt : Option PqHashSig :=
  evalSingleSign cshake256Suite compactGoldenParams goldenSk goldenMsg1 goldenOptRand 1 256

#guard goldenSigCshakeOpt.isSome
#guard match goldenSigCshakeOpt with
  | some sig => verifyPqHashSig cshake256Suite compactGoldenParams goldenPkCshake goldenMsg1 sig
  | none => false
#guard match goldenSigCshakeOpt with
  | some sig => !(verifyPqHashSig cshake256Suite compactGoldenParams goldenPkCshake goldenMsg2 sig)
  | none => false
#guard evalCutBatchSign cshake256Suite compactGoldenParams goldenSk goldenMsg1 goldenOptRand 1 256 ==
  goldenSigCshakeOpt

-- Verify concrete `poseidon2Suite` stateful `leanSig` (`compactLeanSigParams`) sign + verify + STARK batch:
def goldenPkPoseidon : PqPublicKey := derivePublicKey poseidon2Suite compactLeanSigParams goldenSk
def goldenSigPoseidonOpt : Option PqHashSig :=
  evalSingleSign poseidon2Suite compactLeanSigParams goldenSk goldenMsg1 goldenOptRand 2 256

#guard goldenSigPoseidonOpt.isSome
#guard match goldenSigPoseidonOpt with
  | some sig => verifyPqHashSig poseidon2Suite compactLeanSigParams goldenPkPoseidon goldenMsg1 sig
  | none => false
#guard match goldenSigPoseidonOpt with
  | some sig => ValidLeanSigBatch compactLeanSigParams [⟨goldenPkPoseidon, goldenMsg1, sig⟩]
  | none => false
#guard evalCutBatchSign poseidon2Suite compactLeanSigParams goldenSk goldenMsg1 goldenOptRand 2 256 ==
  goldenSigPoseidonOpt

-- Verify 1-round Binomial Power-7 Goldilocks identity on concrete field elements:
#guard
  let x := Goldilocks.ofNat 0x123456789ABCDEF0
  let r := Goldilocks.ofNat 0x0FEDCBA987654321
  let d := CommRingOps.sub x r
  let r2 := CommRingOps.mul r r
  let r3 := CommRingOps.mul r2 r
  let r4 := CommRingOps.mul r2 r2
  let r5 := CommRingOps.mul r4 r
  let r6 := CommRingOps.mul r4 r2
  let r7 := CommRingOps.mul r3 r4
  power7BinomialEval d r r2 r3 r4 r5 r6 r7 == pow7Goldilocks x

-- Verify `HybridPinnedSig` committed-identity pinning & self-carried substitution refusal:
def dummyClassicalPk : List UInt8 := List.replicate 32 (0x11 : UInt8)
def attackerPqSk : PqSecretKey :=
  { skSeed := List.replicate 32 (0xEE : UInt8)
    skPrf  := List.replicate 32 (0xDD : UInt8)
    pkSeed := List.replicate 32 (0xCC : UInt8) }
def attackerPqPk : PqPublicKey := derivePublicKey cshake256Suite compactGoldenParams attackerPqSk

#guard checkHybridPinning id encodePublicKeyWire
  (computeHybridIdCommit dummyClassicalPk (encodePublicKeyWire goldenPkCshake))
  dummyClassicalPk goldenPkCshake
#guard !(checkHybridPinning id encodePublicKeyWire
  (computeHybridIdCommit dummyClassicalPk (encodePublicKeyWire goldenPkCshake))
  dummyClassicalPk attackerPqPk)

-- Verify tri-state `VerifyReply` (`accept`, `reject`, and all 4 `.wireMalformed` fault stages):
#guard match goldenSigCshakeOpt with
  | some sig =>
    verifyPqWireEnvelope cshake256Suite compactGoldenParams
      (encodePublicKeyWire goldenPkCshake) goldenMsg1 pqWireMagic sig == .accept
  | none => false

#guard match goldenSigCshakeOpt with
  | some sig =>
    verifyPqWireEnvelope cshake256Suite compactGoldenParams
      (encodePublicKeyWire goldenPkCshake) goldenMsg2 pqWireMagic sig == .reject
  | none => false

#guard match goldenSigCshakeOpt with
  | some sig =>
    verifyPqWireEnvelope cshake256Suite compactGoldenParams
      (encodePublicKeyWire goldenPkCshake) goldenMsg1 [0x00, 0x01] sig == .wireMalformed .headerMagicOrVersion
  | none => false

#guard match goldenSigCshakeOpt with
  | some sig =>
    verifyPqWireEnvelope cshake256Suite compactGoldenParams
      [0x01, 0x02] goldenMsg1 pqWireMagic sig == .wireMalformed .publicKeyLength
  | none => false

#guard match goldenSigCshakeOpt with
  | some sig =>
    verifyPqWireEnvelope cshake256Suite compactGoldenParams
      (encodePublicKeyWire goldenPkCshake) goldenMsg1 pqWireMagic { sig with rRand := [0x01] } ==
      .wireMalformed .signatureFraming
  | none => false

#guard match goldenSigCshakeOpt with
  | some sig =>
    verifyPqWireEnvelope cshake256Suite compactGoldenParams
      (encodePublicKeyWire goldenPkCshake) goldenMsg1 pqWireMagic { sig with layerSigs := [] } ==
      .wireMalformed .layerCountMismatch
  | none => false

-- Stage-2 Adversarial Degenerate Parameter & Framing Guards:
def degenerateZeroEll1Params : PqHashParams :=
  { w := 2, ell1 := 0, subtreeHeight := 1, numLayers := 1,
    forsTrees := 1, forsHeight := 1, maxSigsLog2 := 1, statefulLeanSig := true }
def degenerateZeroForsParams : PqHashParams :=
  { w := 2, ell1 := 1, subtreeHeight := 1, numLayers := 1,
    forsTrees := 0, forsHeight := 0, maxSigsLog2 := 1, statefulLeanSig := false }

#guard !(degenerateZeroEll1Params.wellFormed)
#guard !(degenerateZeroForsParams.wellFormed)
#guard !(({ compactGoldenParams with w := 512 } : PqHashParams).wellFormed)
#guard (evalSingleSign cshake256Suite degenerateZeroEll1Params goldenSk goldenMsg1 goldenOptRand 0 8).isNone
#guard match goldenSigPoseidonOpt with
  | some sig =>
    !(verifyPqHashSig poseidon2Suite compactLeanSigParams goldenPkPoseidon goldenMsg1 { sig with msgTswCtr := 7 }) &&
    verifyPqWireEnvelope poseidon2Suite compactLeanSigParams
      (encodePublicKeyWire goldenPkPoseidon) goldenMsg1 pqWireMagic { sig with msgTswCtr := 7 } ==
      .wireMalformed .signatureFraming
  | none => false
#guard match goldenSigCshakeOpt with
  | some sig =>
    let badLayer : LayerXmssSig := { tswCtr := 0, wotsChains := [[0x01]], authPath := [] }
    verifyPqWireEnvelope cshake256Suite ⟨2, 1, 0, 1, 0, 0, 1, true⟩
      (encodePublicKeyWire goldenPkCshake) goldenMsg1 pqWireMagic
      { sig with forsOpenings := [], layerSigs := [badLayer] } == .wireMalformed .signatureFraming
  | none => false

/-! ## 3. Multi-Turn `ValidPqCustodyMpcTrace` Inhabitedness (Sign + Crash Retry + Double-Sign Refusal + Revocation) -/

def maskA : List UInt8 := List.replicate 32 (0x5A : UInt8)
def maskB : List UInt8 := List.replicate 32 (0xC3 : UInt8)

def goldenRssBundle : SharedSecretKeyBundle where
  pkSeed := goldenSk.pkSeed
  skSeedShares := [List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) goldenSk.skSeed maskA) maskB, maskA, maskB]
  skPrfShares  := [List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) goldenSk.skPrf maskA) maskB, maskA, maskB]
  reconstructBytes := fun
    | [s0, s1, s2] => reconstructXorBytes s0 s1 s2
    | _ => []

#guard goldenRssBundle.reconstructSk == goldenSk

def sampleCap : CapDescriptor :=
  { root := { rights := 1, caveat := .const true, holder := ByteArray.mk #[], channel := ByteArray.mk #[] }
    hops := #[]
    membranes := [42] }

def sampleHost : PowerboxHost :=
  GrainPowerbox.genesis [0] (fun _ => .true3)

def sampleSysCfg : CustodyMpcSysConfig where
  engine := .rss2of3Cshake
  params := compactGoldenParams
  committee := [0, 1, 2, 3]
  maxFaulty := 1
  faulty := fun v => decide (v = 3)
  needRights := 1
  sharedBundle := goldenRssBundle
  logicalSk := goldenSk

def sampleInitSys : CustodyMpcSysState where
  powerbox := sampleHost
  latches := fun _ => initEpochLatch
  latchLogs := fun _ => []
  signedHistory := []

-- Turn 1: Quorum {0, 1, 2} signs `goldenMsg1` at epoch 0 -> succeeds!
def stAfterTurn1 : Option CustodyMpcSysState :=
  stepCustodyMpcSys sampleSysCfg sampleInitSys
    (.thresholdSignTurn sampleCap 0 goldenMsg1 goldenOptRand 256 (fun v => decide (v ≤ 2)))

#guard stAfterTurn1.isSome

-- Turn 2a (Adversarial Double-Sign Attempt): Quorum {1, 2, 3} tries to sign `goldenMsg2` at SAME epoch 0 -> REFUSED (`none`)!
#guard match stAfterTurn1 with
  | some s1 => (stepCustodyMpcSys sampleSysCfg s1
      (.thresholdSignTurn sampleCap 0 goldenMsg2 goldenOptRand 256 (fun v => decide (1 ≤ v)))).isNone
  | none => false

-- Turn 2b (Idempotent Crash-Recovery Retry): Quorum {1, 2, 3} retries SAME `goldenMsg1` at epoch 0 -> SUCCEEDS!
def stAfterRetry : Option CustodyMpcSysState :=
  stAfterTurn1.bind fun s1 =>
    stepCustodyMpcSys sampleSysCfg s1
      (.thresholdSignTurn sampleCap 0 goldenMsg1 goldenOptRand 256 (fun v => decide (1 ≤ v)))

#guard stAfterRetry.isSome

-- Turn 3: Revoke membrane 42, then attempt epoch 1 signing -> REFUSED (`none`)!
def stAfterRevoke : Option CustodyMpcSysState :=
  stAfterRetry.bind fun s2 =>
    stepCustodyMpcSys sampleSysCfg s2 (.revokeCustodyMembrane 42)

#guard stAfterRevoke.isSome
#guard match stAfterRevoke with
  | some s3 => (stepCustodyMpcSys sampleSysCfg s3
      (.thresholdSignTurn sampleCap 1 goldenMsg2 goldenOptRand 256 (fun v => decide (v ≤ 2)))).isNone
  | none => false

-- Proved inhabited 3-turn `ValidPqCustodyMpcTrace` witness (epoch 0 sign + epoch 1 sign + membrane revocation):
def fastKernelTestSuite : TweakableHashSuite where
  suiteId := [0x4B, 0x54]
  rawHash := fun _ => List.replicate 32 0
  rawHash_len := fun _ => by simp

def kernelTraceParams : PqHashParams :=
  { w := 2, ell1 := 1, subtreeHeight := 1, numLayers := 1,
    forsTrees := 0, forsHeight := 0, maxSigsLog2 := 1, statefulLeanSig := true }

def kernelTraceSk : PqSecretKey := ⟨[1], [2], [3]⟩
def kernelTraceBundle : SharedSecretKeyBundle :=
  ⟨[3], [[1], [0], [0]], [[2], [0], [0]], fun | [a, b, c] => reconstructXorBytes a b c | _ => []⟩

def kernelTraceSysCfg : CustodyMpcSysConfig :=
  { sampleSysCfg with
    engine := .customRss fastKernelTestSuite
    params := kernelTraceParams
    sharedBundle := kernelTraceBundle
    logicalSk := kernelTraceSk }

def ktAfterTurn1 : Option CustodyMpcSysState :=
  stepCustodyMpcSys kernelTraceSysCfg sampleInitSys
    (.thresholdSignTurn sampleCap 0 [0xaa] [0x01] 2 (fun v => decide (v ≤ 2)))

def ktAfterTurn2 : Option CustodyMpcSysState :=
  ktAfterTurn1.bind fun s1 =>
    stepCustodyMpcSys kernelTraceSysCfg s1
      (.thresholdSignTurn sampleCap 1 [0xbb] [0x01] 2 (fun v => decide (1 ≤ v)))

def ktAfterRevoke : Option CustodyMpcSysState :=
  ktAfterTurn2.bind fun s2 =>
    stepCustodyMpcSys kernelTraceSysCfg s2 (.revokeCustodyMembrane 42)

private theorem ktAfterRevoke_check :
    (match ktAfterRevoke with | some s => s.signedHistory.length == 2 | none => false) = true := by
  decide +kernel

example :
    ∃ stFinal : CustodyMpcSysState,
      stFinal.signedHistory.length = 2 ∧
      stFinal.powerbox.revokedMembranes.contains 42 = true ∧
      ValidPqCustodyMpcTrace kernelTraceSysCfg sampleInitSys
        [ .thresholdSignTurn sampleCap 0 [0xaa] [0x01] 2 (fun v => decide (v ≤ 2)),
          .thresholdSignTurn sampleCap 1 [0xbb] [0x01] 2 (fun v => decide (1 ≤ v)),
          .revokeCustodyMembrane 42 ]
        stFinal := by
  have hCheck := ktAfterRevoke_check
  cases hs1 : ktAfterTurn1 with
  | none => simp [ktAfterRevoke, ktAfterTurn2, hs1] at hCheck
  | some s1 =>
    cases hs2 : stepCustodyMpcSys kernelTraceSysCfg s1
        (.thresholdSignTurn sampleCap 1 [0xbb] [0x01] 2 (fun v => decide (1 ≤ v))) with
    | none => simp [ktAfterRevoke, ktAfterTurn2, hs1, hs2] at hCheck
    | some s2 =>
      let s3 : CustodyMpcSysState :=
        { powerbox := { s2.powerbox with revokedMembranes := s2.powerbox.revokedMembranes.insert 42 }
          latches := s2.latches
          latchLogs := s2.latchLogs
          signedHistory := s2.signedHistory }
      have hs3 : stepCustodyMpcSys kernelTraceSysCfg s2 (.revokeCustodyMembrane 42) = some s3 := by
        simp [stepCustodyMpcSys, s3]
      have hLen : s3.signedHistory.length = 2 := by
        have hEq : ktAfterRevoke = some s3 := by simp [ktAfterRevoke, ktAfterTurn2, hs1, hs2, hs3]
        rw [hEq] at hCheck
        simpa using hCheck
      have hRev : s3.powerbox.revokedMembranes.contains 42 = true :=
        RevokedSet.contains_insert_self s2.powerbox.revokedMembranes 42
      exact ⟨s3, hLen, hRev, ⟨s1, hs1, ⟨s2, hs2, ⟨s3, hs3, rfl⟩⟩⟩⟩

/-! ## 4. Cross-Language Golden Vectors (`crates/obend-pq-mpc` Byte-for-Byte Parity) -/

def goldenCshakePrfVec : List UInt8 :=
  thSecretPrf cshake256Suite goldenSk.pkSeed goldenSk.skSeed goldenAdrsSample

def goldenPoseidonPrfVec : List UInt8 :=
  thSecretPrf poseidon2Suite goldenSk.pkSeed goldenSk.skSeed goldenAdrsSample

def goldenHybridIdCommitVec : List UInt8 :=
  computeHybridIdCommit dummyClassicalPk (encodePublicKeyWire goldenPkCshake)

def goldenDkgCommitVec : List UInt8 :=
  dkgCommitShare 1 2 (List.replicate 32 (0x77 : UInt8)) (List.replicate 16 (0x88 : UInt8))

#guard hexBytes (encodeAdrs goldenAdrsSample) == "0000000300000000010203040506070800000000000000070000000b00000002"
#guard hexBytes (encodeMultiFrame [[1, 2], [3, 4, 5]]) == "0202010203030405"
#guard hexBytes goldenCshakePrfVec == "c461f210265b042ab4a95566bee3f8f012369b504f0d613db3fe5950abb95e3f"
#guard hexBytes goldenPoseidonPrfVec == "5c2e630c43432f25df376a8bcb589bfd06a2c6b30ca0e47cec2d96c1b4cce3d7"
#guard hexBytes goldenPkCshake.pkRoot == "060cabbcc13f5548d6d75596ce5eecba3ebaf1f07b117ebcf7e2a74fae387e4c"
#guard hexBytes goldenPkPoseidon.pkRoot == "a4c3a2637318e059316d52679d376050ee63b46a85c13d99d13d917d425bd86a"
#guard hexBytes goldenHybridIdCommitVec == "66094e4608c0f029966c719bfe27a34d07ee4b4d936da1a440aa7ae03afdb349"
#guard hexBytes goldenDkgCommitVec == "3db80075c4e7c88b9e218161e7b98ecc51f6af1b808c82a4d63b0f0dbb07b62d"
#guard match goldenSigCshakeOpt with
  | some s => s.msgTswCtr == 1 && hexBytes s.rRand == "aac835eedf6da763c8db059bfb5d2f25a9a52f55eccd2a5c5698da3a2f7d193f"
  | none => false

/-! ## 5. All 5 Mandatory `#tooth` Mutation-Sensitivity Witnesses (+ Structural Teeth) -/

-- Mandatory Tooth #1: Drop target-sum equality `sumDigits digits = target` from `checkTargetSum`!
#tooth tsw_incomparable_no_chain_forgery by mutation checkTargetSum :=
  fun w ell1 _ digits => decide (digits.length = ell1) && digits.all (fun d => decide (d < w))

#tooth transcript_shape_depends_only_on_public_params by mutation checkTargetSum :=
  fun w ell1 _ digits => decide (digits.length = ell1) && digits.all (fun d => decide (d < w))

-- Mandatory Tooth #2: Drop `st.boundDigest = some mu` on `ep = hw` in `stepEpochLatch`!
#tooth leanSig_quorum_never_double_signs by mutation stepEpochLatch :=
  fun st ep mu =>
    match st.highWater with
    | none => some { highWater := some ep, boundDigest := some mu }
    | some hw =>
      if hw < ep then some { highWater := some ep, boundDigest := some mu }
      else if ep = hw then some st
      else none

#tooth pq_threshold_custody_multi_turn_safe by mutation stepEpochLatch :=
  fun st ep mu =>
    match st.highWater with
    | none => some { highWater := some ep, boundDigest := some mu }
    | some hw =>
      if hw < ep then some { highWater := some ep, boundDigest := some mu }
      else if ep = hw then some st
      else none

-- Mandatory Tooth #3: Drop `chainIdx` from `encodeAdrs` (zeroing bytes `[24..28)`)!
#tooth encodeAdrs_injective by mutation encodeAdrs :=
  fun a =>
    be 4 a.layer.toNat ++ (be 4 0 ++ (be 8 a.tree.toNat ++
      (be 4 a.kind.toCode.toNat ++ (be 4 a.keyPair.toNat ++
        (be 4 0 ++ be 4 a.hashStep.toNat)))))

-- Mandatory Tooth #4a & #4b: Drop off-diagonal correlated-OT cross-terms in `formBdozPartyMacShare`
-- AND weaken `verifyBatchTowerMac2Lane`!
#tooth bdoz_2party_cross_terms_sound by mutation formBdozPartyMacShare :=
  fun _ _ alpha_i x_i _ => towerMul 7 alpha_i x_i

#tooth batchTowerMac2Lane_sound_roots_bound by mutation verifyBatchTowerMac2Lane :=
  fun _ _ _ _ _ _ => true

-- Mandatory Tooth #5: Weaken `checkHybridPinning` to accept self-carried `pk₂` without checking `idCommit`!
#tooth hybrid_ucRealizes_if_either_secure by mutation checkHybridPinning :=
  fun _ _ _ _ _ => true

-- Additional Structural Teeth (`verifyPqHashSig`, `verifyPqWireEnvelope`, `checkCustodySignAuth`):
#tooth verifyPqHashSig_evalSingleSign by mutation verifyPqHashSig :=
  fun _ _ _ _ _ => false

#tooth verifyWire_malformed_iff by mutation verifyPqWireEnvelope :=
  fun _ _ _ _ _ _ => .accept

#tooth revoked_membrane_blocks_threshold_sign by mutation checkCustodySignAuth :=
  fun _ _ _ => true

#guard match evalSingleSign poseidon2Suite compactLeanSigParams ⟨[1], [2], [3]⟩ [9] [8] 0 256 with
  | some s => ValidLeanSigBatch compactLeanSigParams [⟨derivePublicKey poseidon2Suite compactLeanSigParams ⟨[1], [2], [3]⟩, [9], s⟩]
  | none => false

/-! ## 6. Zero-Axiom Kernel Audit (`#print axioms`) -/

#print axioms unifiedTreeGame_birthday_le
#print axioms hidingAdv_le_deployed
#print axioms pad_bijection_masked_openings_uniform
#print axioms ucRealizes_iff_eufCma
#print axioms multi_session_uc_realizes
#print axioms uc_composition_theorem
#print axioms encodeAdrs_injective
#print axioms tsw_incomparable_no_chain_forgery
#print axioms verifyPqHashSig_evalSingleSign
#print axioms extractPqHashForgery
#print axioms hybrid_ucRealizes_if_either_secure
#print axioms verifyWire_malformed_iff
#print axioms evalCutBatchSign_eq_naiveSign
#print axioms transcript_shape_depends_only_on_public_params
#print axioms thresholdSign_eq_singleSign
#print axioms power7BinomialEval_eq_pow7
#print axioms bdoz_2party_cross_terms_sound
#print axioms batchTowerMac2Lane_sound_roots_bound
#print axioms bdoz_cheater_identified_or_mac_forged
#print axioms dkg_reed_solomon_consistency_sound
#print axioms proactive_refresh_preserves_secret_and_pk
#print axioms leanSig_quorum_never_double_signs
#print axioms pq_threshold_custody_multi_turn_safe

end Obend.Tests.Crypto.PqThresholdHashMpcTest
end
