module
public import Obend.Hardware.DprStutter
public import Obend.ClusterGov.LucidEnvelope
import all Obend.Hardware.DprStutter
import all Obend.ClusterGov.LucidEnvelope
import Obend.Tactic.Tooth
import all Obend.Judge.SvenvsCorrigibility
meta import all Obend.Hardware.DprStutter
meta import all Obend.ClusterGov.LucidEnvelope
meta import all Obend.Trailblaze.ClusterGov
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam

public section
set_option pp.maxSteps 2000
namespace Obend.Tests.DprStutterAndLucidGov

open Obend.Hardware.DprStutter Obend.ClusterGov.LucidEnvelope
open Obend.Trailblaze.ClusterGov Obend.Crypto

-- LUTs exercise both truth-table extraction and the switch-matrix PIP indices.
def lowTile : TechmappedTile := ⟨0#16, false, 0, 1, 2, 3⟩
def highTile : TechmappedTile := ⟨65535#16, false, 3, 2, 1, 0⟩
def xorTile : TechmappedTile := ⟨0x6666#16, false, 0, 1, 4, 5⟩
def oldBank : Array TechmappedTile := #[lowTile, xorTile]
def newBank : Array TechmappedTile := #[highTile, xorTile]

theorem bank_roundtrip : decodeTileFrames 2 (encodeTileFrames newBank) = some newBank :=
  decodeTileFrames_encodeTileFrames newBank

example : (evalDecodedFabric oldBank #[false, true, false, true] #[false, true]).toList =
    [false, true] := by decide
example : (evalDecodedFabric newBank #[false, true, false, true] #[false, true]).toList =
    [true, true] := by decide
example : decodeTileFrames 1 (encodeTileFrames newBank) = none := by
  simp [decodeTileFrames, encodeTileFrames, newBank]

def initialFabric : DprFabric :=
  { specSlot := 1, phase := .active, activeTiles := oldBank,
    sram := encodeTileFrames oldBank, pending := none, clampedOut := false,
    inputs := #[false, true, false, true], targetRegs := #[false, false],
    neighbors := ⟨#[highTile, xorTile], #[false, false], #[⟨2, 17#64, 0⟩], false⟩ }

def fenced : DprFabric := stepDprFabric initialFabric .isolateClamped
def loaded : DprFabric := stepDprFabric fenced (.loadFrames (encodeTileFrames newBank))
def released : DprFabric := stepDprFabric loaded .releaseFence

example : fenced.phase = .isolateClamped := rfl
example : observedBoundaryPort fenced = false := rfl
example : loaded.phase = .loadFrames := by
  simp [loaded, stepDprFabric, administer, fenced, initialFabric,
    oldBank, bank_roundtrip]
example : observedBoundaryPort loaded = false := by
  exact (clampedPortStable fenced (encodeTileFrames newBank) (by decide)).2
example : released.phase = .active := by
  have h := release_specialization fenced (encodeTileFrames newBank) newBank newBank.toList
    (by decide) bank_roundtrip (by rfl)
  exact h.1
example : observedBoundaryPort released = true := by
  simp [released, loaded, stepDprFabric, administer, fenced, initialFabric,
    oldBank, bank_roundtrip, observedBoundaryPort,
    unfencedBoundary, evalDecodedFabric, evalDecodedTile, highTile]
  rfl
example : released.neighbors.packets[0]?.map (·.hops) = some 3 := by
  simp [released, loaded, stepDprFabric, administer, fenced, initialFabric, oldBank, bank_roundtrip, tickNeighbors]
example : (stepDprFabric released .compute).neighbors.packets[0]?.map (·.hops) = some 4 := by
  simp [released, loaded, stepDprFabric, administer, fenced, initialFabric, oldBank, bank_roundtrip, tickNeighbors]

-- CRC mismatch is recomputed, not a caller-supplied crcOk flag.
def corruptFrames : Array TileFrame := (encodeTileFrames newBank).modify 0 fun f =>
  { f with crc := f.crc ^^^ 1#64 }
theorem corrupt_rejected : decodeTileFrames 2 corruptFrames = none := by
  simp [decodeTileFrames, corruptFrames, encodeTileFrames, newBank,
    Array.mapM_eq_mapM_toList, frame_crc_bit_flip_rejected]
example : (stepDprFabric (stepDprFabric fenced (.loadFrames corruptFrames)) .releaseFence).phase =
    .isolateClamped := failed_decode_quarantines fenced corruptFrames (by decide) corrupt_rejected

-- Valid CRC cannot launder an invalid physical PIP select (6 and 7 are reserved).
def badPip : TileFrame :=
  let w := BitVec.ofNat 64 (536870912 * 0xFAB + 131072 * 6)
  ⟨w, frameCrc w⟩
example : decodeTileFrames 1 #[badPip] = none := by
  simp [decodeTileFrames, Array.mapM_eq_mapM_toList, decodeTileFrame, badPip]

example : Obend.Category.StutterSimulates abstractNeighborStepSys dprFabricStepSys
    (fun n s => n = s.neighbors) 1 (0 : Nat) :=
  (dpr_preserves_neighbor_tiles_stutter fenced #[] (by decide)).1

#tooth evalDecodedFabric_eq_techmapped by mutation evalDecodedTile :=
  fun t inp reg => if t.registered then reg else
    t.lut.getLsbD ((inp t.a).toNat + 2 * (inp t.b).toNat +
      4 * (inp t.c).toNat + 8 * (inp t.d).toNat + 1)

#tooth dpr_preserves_neighbor_tiles_stutter by mutation observedBoundaryPort :=
  fun s => if s.phase = .loadFrames then s.clampedOut else unfencedBoundary s

-- Real Ariadne context and domain-separated payload/state commitment.
def payload : ByteArray := "swarm-job-output".toUTF8
def receipt : JudgedReceipt :=
  { context := validClusterStepCtx,
    stateHash := hashBytes "OBEND.LUCID.STATE/v1" payload,
    provenOps := 7500000, epoch := 7, jobId := 42, host := "hbox".toUTF8 }
def log : JudgedReceiptLog := commitReceiptLog #[receipt] 0 7
def opening : ReceiptInclusionProof := ⟨0, #[]⟩
def packet : EgressPacket := ⟨payload, receipt.stateHash⟩

theorem judged_receipt : checkJudgedReceipt receipt = true := by
  have hj : verifyClusterStep validClusterStepCtx = true := rfl
  unfold checkJudgedReceipt
  change (verifyClusterStep validClusterStepCtx && decide (_ ∧ _ ∧ _)) = true
  rw [hj]
  simp [receipt, hashBytes_size, validClusterStepCtx]

theorem receipt_inclusion : verifyReceiptInclusion log opening = true := by
  have hep : receipt.epoch = 7 := rfl
  simp [verifyReceiptInclusion, log, opening, judged_receipt, verifyOpening,
    logRoot, commitReceiptLog, merkleRoot, climbMerkle, receiptDigest, hashBytes_size, hep]

theorem admitted_packet : checkCommitBeforeForward log packet opening = true := by
  unfold checkCommitBeforeForward
  change (verifyReceiptInclusion log opening && decide (_ ∧ _)) = true
  rw [receipt_inclusion]
  simp [packet, receipt, log, opening, commitReceiptLog]

example : checkCommitBeforeForward log packet ⟨1, #[]⟩ = false := rfl
example : checkCommitBeforeForward (commitReceiptLog #[] 0 7) packet opening = false := rfl

def claim : LocationClaim := ⟨receipt, "hbox-gpu-0".toUTF8,
  pageDigest 0 "sealed-page".toUTF8, 50000⟩
example : verifyRttEnvelope (rackHardwarePolicy claim.hardwareId) claim 52000 = false :=
  relay_5000km_rejected claim claim.hardwareId

def hardware : HardwareClassPolicy := ⟨claim.hardwareId, 1000, 2000, 1, 0, 1⟩
def challenge : VramChallenge := ⟨"fresh-inspector-nonce".toUTF8, 7, claim.vramMerkleRoot⟩
def pages : Array VramPageOpening := #[⟨"sealed-page".toUTF8, opening⟩]

-- A singleton memory tree still derives a real transcript challenge; n % 1 = 0
-- permits kernel checking without evaluating cSHAKE inside the proof kernel.
theorem challenge_offset : deriveVramChallengeOffsets hardware challenge claim = #[0] := by
  simp [deriveVramChallengeOffsets, hardware, challengeOffsets]
  exact Nat.mod_one _

theorem sealed_page : verifySealedVram hardware challenge claim 100 pages = true := by
  unfold verifySealedVram
  rw [challenge_offset]
  simp [verifyRttEnvelope, hardware, claim, challenge,
    receipt, pages, verifyVramPage, verifyOpening, opening, climbMerkle, pageDigest, hashBytes_size]

example : checkEnergyEnvelope bandCalibration receipt 40 0 = true := rfl
example : checkEnergyEnvelope bandCalibration receipt 100 0 = false := rfl
example : residualEnergy bandCalibration receipt.provenOps 100 = 60 := rfl
example : 100 - bandCalibration.eHi receipt.provenOps = 0 := rfl
example : (makeFabulousRackReceipt ⟨"rack-1".toUTF8, 7, receipt.context.step⟩ true).receiptBytes.size = 32 :=
  (makeFabulousRackReceipt ⟨"rack-1".toUTF8, 7, receipt.context.step⟩ true).size32

def authority : LucidAuthority := ⟨log, hardware, challenge, bandCalibration, 0⟩
def evidence : LucidEvidence := ⟨packet, opening, claim, 100, pages, 40⟩

theorem lucid_admitted : checkLucidEnvelope authority evidence = true := by
  simp only [checkLucidEnvelope, authority, evidence]
  rw [admitted_packet, sealed_page]
  simp [checkEnergyEnvelope, residualEnergy, bandCalibration, claim, packet, log, opening,
    challenge, receipt, commitReceiptLog]

def cleanRow : SwarmJobRow :=
  { jobId := 42, host := "hbox".toUTF8, gpuSecondsMetered := 40, tokensMetered := 1234,
    landedReceiptHash := receiptDigest receipt, provenOps := 7500000,
    receiptIndex := 0, inclusion := opening }

theorem clean_meter_row : checkMeterRow log bandCalibration 0 cleanRow = none := by
  apply (checkMeterRow_iff log bandCalibration 0 cleanRow).2
  exact ⟨receipt, rfl, rfl, receipt_inclusion, rfl, rfl, rfl, rfl, by decide⟩

theorem clean_meter : auditSwarmComputeMeter log bandCalibration 0 #[cleanRow] =
    .clean ⟨1, 40, 1234⟩ := by
  simp [auditSwarmComputeMeter, clean_meter_row]
  rfl

example : auditSwarmComputeMeter log bandCalibration 0 #[{ cleanRow with gpuSecondsMetered := 100 }] =
    .violation (.residualBreach 42 60 0) := by
  have hv : checkMeterRow log bandCalibration 0 { cleanRow with gpuSecondsMetered := 100 } =
      some (.residualBreach 42 60 0) := by
    simp only [checkMeterRow, cleanRow, show log.entries[0]? = some receipt from rfl,
      receipt_inclusion]
    simp [opening, receipt, residualEnergy, bandCalibration]
  simp [auditSwarmComputeMeter, hv]
example : auditSwarmComputeMeter log bandCalibration 0 #[{ cleanRow with receiptIndex := 1 }] =
    .violation (.missingReceipt 42) := by rfl

-- A receipt hash of the wrong length cannot match any cSHAKE commitment.
example : auditSwarmComputeMeter log bandCalibration 0
    #[{ cleanRow with landedReceiptHash := ByteArray.empty }] =
    .violation (.mismatchedReceipt 42) := by
  have hne : ByteArray.empty ≠ receiptDigest receipt := by
    intro he
    have hs := congrArg ByteArray.size he
    simp [receiptDigest, hashBytes_size] at hs
  have hv : checkMeterRow log bandCalibration 0 { cleanRow with landedReceiptHash := ByteArray.empty } =
      some (.mismatchedReceipt 42) := by
    simp only [checkMeterRow, cleanRow, show log.entries[0]? = some receipt from rfl,
      receipt_inclusion]
    simp [hne]
  simp [auditSwarmComputeMeter, hv]

-- Exercise an actual sibling digest and the depth/index checks of a binary log.
def secondReceipt : JudgedReceipt := { receipt with jobId := 43 }
def twoLog : JudgedReceiptLog := commitReceiptLog #[receipt, secondReceipt] 1 7
def twoOpening : ReceiptInclusionProof := ⟨0, #[receiptDigest secondReceipt]⟩
example : verifyReceiptInclusion twoLog twoOpening = true := by
  have hep : receipt.epoch = 7 := rfl
  simp [verifyReceiptInclusion, twoLog, twoOpening, judged_receipt, hep,
    verifyOpening, logRoot, commitReceiptLog, merkleRoot, climbMerkle, receiptDigest, nodeDigest, hashBytes_size]
example : verifyReceiptInclusion twoLog opening = false := by
  simp [verifyReceiptInclusion, twoLog, opening, verifyOpening, commitReceiptLog]

example : clockDecodedFabric #[{ highTile with registered := true }] #[] #[false] = #[true] := by decide
example : evalDecodedFabric #[{ highTile with registered := true }] #[] #[false] = #[false] := by decide

#tooth commitBeforeForward_sound by mutation checkCommitBeforeForward := fun _ _ _ => true
#tooth authorityPinnedRtt_sound by mutation verifyRttEnvelope :=
  fun policy claim measured => decide (claim.hardwareId = policy.hardwareId ∧
    measured ≤ claim.claimedProcBudgetMicros + policy.maxPropagationMicros)
#tooth sealedVramOpening_sound by mutation verifyRttEnvelope :=
  fun policy claim measured => decide (claim.hardwareId = policy.hardwareId ∧
    measured ≤ claim.claimedProcBudgetMicros + policy.maxPropagationMicros)
#tooth energyConservation_bounds_hidden_ops by mutation residualEnergy :=
  fun cal ops meter => (meter + cal.eta) - (cal.eIdle + cal.eHi ops)
#tooth auditSwarmComputeMeter_sound_iff by mutation checkMeterRow := fun _ _ _ _ => none

-- A concrete plant checks that the policy composition is inhabited: true is
-- an unsafe actuator state, and the fallback returns home in one step.
open Obend.Judge.SvenvsCorrigibility

def plantStep (_ : Bool) (act : Bool) : Bool := act
def recovery (_ : Bool) : Bool := false
def atHome (s : Bool) : Prop := s = false
def plantPolicy (_ : Bool) (act : Bool) : Bool := !act

theorem recovery_witness (s : Bool) : CWithin plantStep recovery atHome 1 s := by
  exact ⟨1, by decide, rfl⟩

example : ∀ ctrl, Invariant plantStep atHome
    (enveloped (lucidPolicy authority (fun _ _ => evidence) plantPolicy 1 ⟨100, 20, 40, 10⟩) recovery ctrl)
    (fun s => atHome s ∧ CWithin plantStep recovery atHome 1 s) := by
  apply lucidEnvelope_corrigibility_safe plantStep atHome atHome atHome recovery
    authority (fun _ _ => evidence) plantPolicy 1 ⟨100, 20, 40, 10⟩
  · intro s hs
    exact ⟨hs, recovery_witness s⟩
  · intro s a _ ha
    cases a with
    | false => exact ⟨rfl, recovery_witness false⟩
    | true => cases ha
  · intro s _
    exact ⟨rfl, recovery_witness false⟩

/-- Reference path construction used to test eight transcript-selected pages
in a sixteen-page physical-memory image, including both branch directions. -/
def testMerkleSiblings : Nat → Array ByteArray → Nat → Array ByteArray
  | 0, _, _ => #[]
  | d+1, leaves, index =>
      let left := leaves.extract 0 (2^d)
      let right := leaves.extract (2^d) leaves.size
      if index < 2^d then testMerkleSiblings d left index |>.push (merkleRoot d right)
      else testMerkleSiblings d right (index - 2^d) |>.push (merkleRoot d left)

#print axioms decodeTileFrames_encodeTileFrames
#print axioms evalDecodedFabric_eq_techmapped
#print axioms dpr_preserves_neighbor_tiles_stutter
#print axioms commitBeforeForward_sound
#print axioms sealedVramOpening_sound
#print axioms energyConservation_bounds_hidden_ops
#print axioms fabulousRackReceipt_at_most_two_states
#print axioms lucidEnvelope_corrigibility_safe
#print axioms auditSwarmComputeMeter_sound_iff

-- Interpreter execution uses the verified cSHAKE Array/UInt64 path. It is
-- supplementary to the kernel proofs above, never a proof-producing shortcut.
set_option interpreter.prefer_native false in
#eval do
  unless checkCommitBeforeForward log packet opening do throw (IO.userError "receipt gate")
  unless verifySealedVram hardware challenge claim 100 pages do throw (IO.userError "sealed VRAM")
  unless checkLucidEnvelope authority evidence do throw (IO.userError "Lucid envelope")
  unless auditSwarmComputeMeter log bandCalibration 0 #[cleanRow] == SwarmMeterResult.clean ⟨1, 40, 1234⟩ do
    throw (IO.userError "swarm meter")
  unless released.phase == DprPhase.active && observedBoundaryPort released do throw (IO.userError "DPR release")
  let memory := (Array.range 16).map (fun i => ("sealed-vram-page-" ++ toString i).toUTF8)
  let leaves := memory.mapIdx (fun i page => pageDigest i page)
  let pinned := rackHardwarePolicy claim.hardwareId
  let probeClaim := { claim with vramMerkleRoot := merkleRoot 4 leaves }
  let probeChallenge := { challenge with sealedRoot := probeClaim.vramMerkleRoot }
  let offsets := deriveVramChallengeOffsets pinned probeChallenge probeClaim
  let proofs := offsets.map fun i =>
    ({ page := memory[i]!, proof := ⟨i, testMerkleSiblings 4 leaves i⟩ } : VramPageOpening)
  unless offsets.size == 8 && verifySealedVram pinned probeChallenge probeClaim 100 proofs do
    throw (IO.userError "sixteen-page sealed VRAM")
  let corruptProofs := proofs.modify 0 fun o => { o with page := "forged-page".toUTF8 }
  if verifySealedVram pinned probeChallenge probeClaim 100 corruptProofs then
    throw (IO.userError "forged page accepted")
  if verifySealedVram pinned { probeChallenge with sealedRoot := ByteArray.empty } probeClaim 100 proofs then
    throw (IO.userError "unsealed root accepted")
  IO.println "DPR / Lucid integration: receipt, 8-of-16 VRAM, forged-page rejection, envelope, meter and hot-swap passed"

end Obend.Tests.DprStutterAndLucidGov
