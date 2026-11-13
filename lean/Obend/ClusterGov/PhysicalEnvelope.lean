module
public import Obend.Trailblaze.CathedralApex
public import Obend.Crypto.Transcript
public import Obend.Hardware.SafePhysicalShield
import all Obend.Hardware.SafePhysicalShield
import all Obend.Hardware.CurrentLoop
public import Obend.Judge.SvenvsCorrigibility
import all Obend.Judge.SvenvsCorrigibility

public section
namespace Obend.ClusterGov.PhysicalEnvelope

open Obend.Trailblaze.ClusterGov Obend.Crypto

/-! The trust boundary is explicit: the verifier owns the committed log,
hardware policy, nonce and meter calibration. Hash verification establishes byte
openings, not a claim of collision impossibility. Physical residency, sensor
coverage, local-work attribution, and non-bypassable NIC mediation are deployment
assumptions; none is manufactured from a prover Boolean. -/

def hashBytes (domain : String) (bytes : ByteArray) : ByteArray :=
  cshake32ByteArray domain.toUTF8.data.toList bytes.data.toList

theorem hashBytes_size (domain : String) (bytes : ByteArray) :
    (hashBytes domain bytes).size = 32 := by
  unfold hashBytes
  apply cshake32ByteArray_size

def natBytes (n : Nat) : ByteArray := ⟨(leb128 n).toArray⟩

def stepBytes (s : AriadneStep) : ByteArray :=
  encodeFrame (natBytes s.prevWeightsRoot) (natBytes s.batchCallTreeRoot)
    (encodeFrame (natBytes s.nextWeightsRoot) (natBytes s.flopsUsed) (natBytes s.flopsCap))

structure JudgedReceipt where
  context : ClusterStepContext
  stateHash : ByteArray
  provenOps : Nat
  epoch : Nat
  jobId : Nat
  host : ByteArray

def stepHash (r : JudgedReceipt) : ByteArray := hashBytes "OBEND.ARIADNE.STEP/v1" (stepBytes r.context.step)

def receiptDigest (r : JudgedReceipt) : ByteArray :=
  hashBytes "OBEND.ENVELOPE.RECEIPT/v1"
    (encodeFrame (stepHash r) r.stateHash (encodeFrame (natBytes r.provenOps) (natBytes r.epoch)
      (encodeFrame (natBytes r.jobId) r.host ByteArray.empty)))

/-- The existing arithmetic/Reasons checker judges the actual AriadneStep.
Additional checks bind the meter credit and the 256-bit state commitment. -/
def checkJudgedReceipt (r : JudgedReceipt) : Bool :=
  verifyClusterStep r.context && decide (r.stateHash.size = 32 ∧
    r.provenOps = r.context.step.flopsUsed ∧ r.context.step.flopsUsed ≤ r.context.step.flopsCap)

def nodeDigest (left right : ByteArray) : ByteArray :=
  hashBytes "OBEND.ENVELOPE.NODE/v1" (encodeFrame left right ByteArray.empty)

def emptyDigest : ByteArray := hashBytes "OBEND.ENVELOPE.EMPTY/v1" ByteArray.empty

/-- Complete binary tree, padded with domain-separated empty leaves. Depth is
verifier-owned; the entry count is checked before any receipt is admitted. -/
def merkleRoot : Nat → Array ByteArray → ByteArray
  | 0, leaves => leaves[0]?.getD emptyDigest
  | d + 1, leaves => nodeDigest (merkleRoot d (leaves.extract 0 (2^d)))
      (merkleRoot d (leaves.extract (2^d) leaves.size))

structure JudgedReceiptLog where
  entries : Array JudgedReceipt
  depth : Nat
  epoch : Nat
  root : ByteArray
  root_correct : root = merkleRoot depth (entries.map receiptDigest)

/-- Compute the root once at commit time. The consistency proof is erased;
per-packet/per-job checks traverse only their logarithmic membership paths. -/
@[expose] def commitReceiptLog (entries : Array JudgedReceipt) (depth epoch : Nat) : JudgedReceiptLog :=
  ⟨entries, depth, epoch, merkleRoot depth (entries.map receiptDigest), rfl⟩

/-- Durable root and epoch are pinned by the trusted NIC supervisor. -/
def logRoot (log : JudgedReceiptLog) : ByteArray := log.root

structure ReceiptInclusionProof where
  index : Nat
  siblings : Array ByteArray

/-- Siblings are ordered leaf-to-root. Index bits fix left/right ordering. -/
def climbMerkle (leaf : ByteArray) (index : Nat) (siblings : Array ByteArray) : ByteArray :=
  (siblings.foldl (fun (acc : ByteArray × Nat) sibling =>
    (if acc.2 % 2 = 0 then nodeDigest acc.1 sibling else nodeDigest sibling acc.1,
     acc.2 / 2)) (leaf, index)).1

def verifyOpening (root leaf : ByteArray) (depth : Nat) (proof : ReceiptInclusionProof) : Bool :=
  decide (root.size = 32 ∧ leaf.size = 32 ∧ proof.index < 2^depth ∧ proof.siblings.size = depth) &&
    proof.siblings.all (fun b => decide (b.size = 32)) &&
    decide (climbMerkle leaf proof.index proof.siblings = root)

def verifyReceiptInclusion (log : JudgedReceiptLog) (proof : ReceiptInclusionProof) : Bool :=
  match log.entries[proof.index]? with
  | none => false
  | some r => decide (log.entries.size ≤ 2^log.depth ∧ r.epoch = log.epoch) &&
      checkJudgedReceipt r && verifyOpening (logRoot log) (receiptDigest r) log.depth proof

structure EgressPacket where
  pktPayload : ByteArray
  pktStateHash : ByteArray

/-- State serialization is committed; the packet cannot use a receipted state
hash to send unrelated payload bytes. -/
def checkCommitBeforeForward (log : JudgedReceiptLog) (pkt : EgressPacket)
    (proof : ReceiptInclusionProof) : Bool :=
  match log.entries[proof.index]? with
  | none => false
  | some r => verifyReceiptInclusion log proof &&
      decide (pkt.pktStateHash = r.stateHash ∧
        hashBytes "OBEND.ENVELOPE.STATE/v1" pkt.pktPayload = pkt.pktStateHash)

/-- Constructive witness into the actual committed array, existing judgment,
compute cap, matching state bytes, and a recomputed cSHAKE Merkle opening. -/
theorem commitBeforeForward_sound (log : JudgedReceiptLog) (pkt : EgressPacket)
    (proof : ReceiptInclusionProof) (h : checkCommitBeforeForward log pkt proof = true) :
    ∃ r, log.entries[proof.index]? = some r ∧ verifyClusterStep r.context = true ∧
      r.context.step.flopsUsed ≤ r.context.step.flopsCap ∧
      r.provenOps = r.context.step.flopsUsed ∧ r.epoch = log.epoch ∧
      pkt.pktStateHash = r.stateHash ∧
      hashBytes "OBEND.ENVELOPE.STATE/v1" pkt.pktPayload = pkt.pktStateHash ∧
      climbMerkle (receiptDigest r) proof.index proof.siblings = logRoot log := by
  unfold checkCommitBeforeForward at h
  cases he : log.entries[proof.index]? with
  | none => simp [he] at h
  | some r =>
    simp only [he, verifyReceiptInclusion, checkJudgedReceipt, verifyOpening,
      Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨_, hep⟩, hj, _, hops, hcap⟩, _, hpath⟩, hstate, hpayload⟩
    exact ⟨r, rfl, hj, hcap, hops, hep, hstate, hpayload, hpath⟩

/-- Constructive admission for arbitrary payload/host bytes, using the existing
nontrivial Sable/Ozaki/Reasons-judged Ariadne context. -/
theorem checkCommitBeforeForward_inhabited (payload host : ByteArray) (epoch job : Nat) :
    ∃ (log : JudgedReceiptLog) (proof : ReceiptInclusionProof),
      checkCommitBeforeForward log
        ⟨payload, hashBytes "OBEND.ENVELOPE.STATE/v1" payload⟩ proof = true := by
  let r : JudgedReceipt := ⟨validClusterStepCtx, hashBytes "OBEND.ENVELOPE.STATE/v1" payload,
    7500000, epoch, job, host⟩
  let log : JudgedReceiptLog := commitReceiptLog #[r] 0 epoch
  let proof : ReceiptInclusionProof := ⟨0, #[]⟩
  have hj : checkJudgedReceipt r = true := by
    unfold checkJudgedReceipt
    have hctx : verifyClusterStep validClusterStepCtx = true := rfl
    change (verifyClusterStep validClusterStepCtx && decide (_ ∧ _ ∧ _)) = true
    rw [hctx]
    simp [r, hashBytes_size, validClusterStepCtx]
  have hi : verifyReceiptInclusion log proof = true := by
    have hep : r.epoch = epoch := rfl
    simp [verifyReceiptInclusion, log, proof, hj, hep, verifyOpening,
      logRoot, commitReceiptLog, merkleRoot, climbMerkle, receiptDigest, hashBytes_size]
  refine ⟨log, proof, ?_⟩
  unfold checkCommitBeforeForward
  change (verifyReceiptInclusion log proof && decide (_ ∧ _)) = true
  rw [hi]
  simp [log, proof, r, commitReceiptLog]

/-- Only this modeled NIC transition can append a forwarded packet. A deployed
capability cut must ensure that no other egress path exists. -/
inductive EgressTrace (log : JudgedReceiptLog) : List EgressPacket → Prop where
  | nil : EgressTrace log []
  | forward {packets : List EgressPacket} (pkt : EgressPacket) (proof : ReceiptInclusionProof) :
      EgressTrace log packets → checkCommitBeforeForward log pkt proof = true →
      EgressTrace log (pkt :: packets)

theorem egress_trace_receipted (log : JudgedReceiptLog) (packets : List EgressPacket)
    (h : EgressTrace log packets) :
    ∀ pkt ∈ packets, ∃ (proof : ReceiptInclusionProof) (r : JudgedReceipt), log.entries[proof.index]? = some r ∧
      pkt.pktStateHash = r.stateHash ∧ r.context.step.flopsUsed ≤ r.context.step.flopsCap := by
  induction h with
  | nil => simp
  | @forward packets pkt proof ht hg ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨r, hr, _, hc, _, _, hs, _⟩ := commitBeforeForward_sound log p proof hg
      exact ⟨proof, r, hr, hs, hc⟩
    · exact ih p hp

structure HardwareClassPolicy where
  hardwareId : ByteArray
  procBudgetMicros : Nat
  maxPropagationMicros : Nat
  pageCount : Nat
  treeDepth : Nat
  challengeCount : Nat

/-- Claimed budgets are untrusted metadata and are never used for acceptance. -/
structure LocationClaim where
  receipt : JudgedReceipt
  hardwareId : ByteArray
  vramMerkleRoot : ByteArray
  claimedProcBudgetMicros : Nat

/-- Issued by the verifier after sealing the root and before accepting a
response. The nonce and root are not fields of the prover's location claim. -/
structure VramChallenge where
  epochNonce : ByteArray
  logEpoch : Nat
  sealedRoot : ByteArray

def vramTranscript (challenge : VramChallenge) (claim : LocationClaim) : Transcript .relationBound :=
  bindRelation "OBEND.ENVELOPE.VRAM/v1"
    (encodeFrame claim.vramMerkleRoot claim.hardwareId (stepHash claim.receipt))
    (natBytes challenge.logEpoch) (Transcript.newUnseeded challenge.epochNonce)

def verifyRttEnvelope (policy : HardwareClassPolicy) (claim : LocationClaim) (measured : Nat) : Bool :=
  decide (claim.hardwareId = policy.hardwareId ∧
    measured ≤ policy.procBudgetMicros + policy.maxPropagationMicros)

theorem authorityPinnedRtt_sound (policy : HardwareClassPolicy) (claim : LocationClaim)
    (measured : Nat) (h : verifyRttEnvelope policy claim measured = true) :
    measured ≤ policy.procBudgetMicros + policy.maxPropagationMicros ∧
      ∀ budget, verifyRttEnvelope policy { claim with claimedProcBudgetMicros := budget } measured = true := by
  have hh := of_decide_eq_true h
  exact ⟨hh.2, fun _ => h⟩

theorem verifyRttEnvelope_inhabited (policy : HardwareClassPolicy) (r : JudgedReceipt) :
    ∃ claim : LocationClaim, verifyRttEnvelope policy claim policy.procBudgetMicros = true := by
  refine ⟨⟨r, policy.hardwareId, r.stateHash, 50000⟩, ?_⟩
  simp [verifyRttEnvelope]

def rackHardwarePolicy (hardwareId : ByteArray) : HardwareClassPolicy :=
  ⟨hardwareId, 1000, 2000, 16, 4, 8⟩

theorem relay_5000km_rejected (claim : LocationClaim) (verifierHardwareId : ByteArray) :
    verifyRttEnvelope (rackHardwarePolicy verifierHardwareId) claim 52000 = false := by
  simp [verifyRttEnvelope, rackHardwarePolicy]

/-- All 256 challenge bits feed the offset; modulo bias and duplicate samples
are explicit (no assertion of independent uniform offsets or full residency). -/
def digestNat (bytes : ByteArray) : Nat := bytes.data.foldl (fun n b => 256*n + b.toNat) 0

def challengeOffsets : Nat → Nat → Transcript .relationBound → Array Nat
  | 0, _, _ => #[]
  | k+1, pages, tr =>
      let (out, next) := squeezeChallenge256 tr
      #[digestNat out.val % pages] ++ challengeOffsets k pages next

theorem challengeOffsets_size (count pages : Nat) (tr : Transcript .relationBound) :
    (challengeOffsets count pages tr).size = count := by
  induction count generalizing tr with
  | zero => rfl
  | succ k ih => simp [challengeOffsets, ih, Nat.add_comm]

def deriveVramChallengeOffsets (policy : HardwareClassPolicy) (challenge : VramChallenge)
    (claim : LocationClaim) : Array Nat :=
  challengeOffsets policy.challengeCount policy.pageCount (vramTranscript challenge claim)

structure VramPageOpening where
  page : ByteArray
  proof : ReceiptInclusionProof

def pageDigest (index : Nat) (page : ByteArray) : ByteArray :=
  hashBytes "OBEND.ENVELOPE.PAGE/v1" (encodeFrame (natBytes index) page ByteArray.empty)

def verifyVramPage (policy : HardwareClassPolicy) (claim : LocationClaim)
    (offset : Nat) (opening : VramPageOpening) : Bool :=
  decide (opening.proof.index = offset ∧ offset < policy.pageCount) &&
    verifyOpening claim.vramMerkleRoot (pageDigest offset opening.page) policy.treeDepth opening.proof

def verifySealedVram (policy : HardwareClassPolicy) (challenge : VramChallenge)
    (claim : LocationClaim) (measured : Nat) (openings : Array VramPageOpening) : Bool :=
  let offsets := deriveVramChallengeOffsets policy challenge claim
  verifyRttEnvelope policy claim measured &&
    decide (0 < policy.pageCount ∧ policy.pageCount ≤ 2^policy.treeDepth ∧
      0 < policy.challengeCount ∧ claim.receipt.epoch = challenge.logEpoch ∧
      claim.vramMerkleRoot = challenge.sealedRoot ∧ openings.size = offsets.size) &&
    (openings.zip offsets).all (fun (o, i) => verifyVramPage policy claim i o)

/-- Every requested, challenge-derived offset has an opening in the pinned root.
This is availability of sampled bytes within the measured window, not SM-PUF
unclonability or an assertion about unobserved/off-site computation. -/
theorem sealedVramOpening_sound (policy : HardwareClassPolicy) (challenge : VramChallenge)
    (claim : LocationClaim) (measured : Nat) (openings : Array VramPageOpening)
    (h : verifySealedVram policy challenge claim measured openings = true) :
    measured ≤ policy.procBudgetMicros + policy.maxPropagationMicros ∧
      claim.vramMerkleRoot = challenge.sealedRoot ∧
      openings.size = (deriveVramChallengeOffsets policy challenge claim).size ∧
      ∀ pair ∈ openings.zip (deriveVramChallengeOffsets policy challenge claim),
        pair.1.proof.index = pair.2 ∧ pair.2 < policy.pageCount ∧
          climbMerkle (pageDigest pair.2 pair.1.page) pair.1.proof.index pair.1.proof.siblings =
            claim.vramMerkleRoot := by
  simp only [verifySealedVram, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr, _, _, _, _, hroot, hsize⟩, hall⟩ := h
  refine ⟨(authorityPinnedRtt_sound policy claim measured hr).1, hroot, hsize, ?_⟩
  intro pair hp
  have hh := Array.all_eq_true'.mp hall pair hp
  simp only [verifyVramPage, verifyOpening, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact ⟨hh.1.1, hh.1.2, hh.2.2⟩

/-- The singleton-tree base case is inhabited for every page and fresh nonce;
the transcript is still bound and squeezed, with its offset reduced modulo one. -/
theorem verifySealedVram_inhabited (r : JudgedReceipt) (page nonce hardwareId : ByteArray) :
    ∃ (policy : HardwareClassPolicy) (challenge : VramChallenge) (claim : LocationClaim)
      (openings : Array VramPageOpening),
      verifySealedVram policy challenge claim 0 openings = true := by
  let policy : HardwareClassPolicy := ⟨hardwareId, 1000, 2000, 1, 0, 1⟩
  let challenge : VramChallenge := ⟨nonce, r.epoch, pageDigest 0 page⟩
  let claim : LocationClaim := ⟨r, hardwareId, pageDigest 0 page, 50000⟩
  let openings : Array VramPageOpening := #[⟨page, ⟨0, #[]⟩⟩]
  have offsets : deriveVramChallengeOffsets policy challenge claim = #[0] := by
    simp [deriveVramChallengeOffsets, policy, challengeOffsets]
    exact Nat.mod_one _
  refine ⟨policy, challenge, claim, openings, ?_⟩
  unfold verifySealedVram
  rw [offsets]
  simp [verifyRttEnvelope, policy, challenge, claim, openings, verifyVramPage,
    verifyOpening, climbMerkle, pageDigest, hashBytes_size]

structure EnergyCalibration where
  eMinPerOp : Nat
  eMinPositive : 0 < eMinPerOp
  eIdle : Nat
  eta : Nat
  eLo : Nat → Nat
  eHi : Nat → Nat
  ordered : ∀ ops, eLo ops ≤ eHi ops

def residualEnergy (cal : EnergyCalibration) (localProvenOps meter : Nat) : Nat :=
  (meter + cal.eta) - (cal.eIdle + cal.eLo localProvenOps)

def checkEnergyEnvelope (cal : EnergyCalibration) (receipt : JudgedReceipt)
    (meter maxResidual : Nat) : Bool :=
  decide (cal.eIdle + cal.eLo receipt.provenOps ≤ meter + cal.eta) &&
  decide (residualEnergy cal receipt.provenOps meter ≤ maxResidual)

theorem checkEnergyEnvelope_refuses_undermetered (cal : EnergyCalibration) (receipt : JudgedReceipt)
    (meter maxResidual : Nat) (hUnder : meter + cal.eta < cal.eIdle + cal.eLo receipt.provenOps) :
    checkEnergyEnvelope cal receipt meter maxResidual = false := by
  simp only [checkEnergyEnvelope, Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega

/-- The lower curve is credited only for work independently attributed to this
rack. Sensor coverage, stored energy and the minimum energy cost are the stated
physical premise, not a cryptographic consequence of the Ariadne receipt. -/
theorem energyConservation_bounds_hidden_ops (cal : EnergyCalibration) (receipt : JudgedReceipt)
    (meter hidden maxResidual : Nat)
    (physical : cal.eIdle + cal.eLo receipt.provenOps + cal.eMinPerOp * hidden ≤ meter + cal.eta)
    (accepted : checkEnergyEnvelope cal receipt meter maxResidual = true) :
    cal.eMinPerOp * hidden ≤ residualEnergy cal receipt.provenOps meter ∧
      residualEnergy cal receipt.provenOps meter ≤ maxResidual ∧
      hidden ≤ maxResidual / cal.eMinPerOp ∧ (maxResidual < cal.eMinPerOp → hidden = 0) := by
  simp only [checkEnergyEnvelope, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have hb : residualEnergy cal receipt.provenOps meter ≤ maxResidual := accepted.2
  have he : cal.eMinPerOp * hidden ≤ residualEnergy cal receipt.provenOps meter := by
    unfold residualEnergy; omega
  have hm := Nat.le_trans he hb
  have hd : hidden ≤ maxResidual / cal.eMinPerOp :=
    (Nat.le_div_iff_mul_le cal.eMinPositive).2 (by simpa [Nat.mul_comm] using hm)
  refine ⟨he, hb, hd, ?_⟩
  intro hsmall
  have hz : maxResidual / cal.eMinPerOp = 0 := Nat.div_eq_of_lt hsmall
  omega

def bandCalibration : EnergyCalibration :=
  ⟨1, by decide, 0, 0, fun _ => 40, fun _ => 100, fun _ => by decide⟩

/-- The real receipt carrier credits its provenOps under both calibration
curves. Sixty hidden operations fit the physical inequality, but only the buggy
upper-curve subtraction reports zero. -/
theorem subtracting_eHi_hides_covert_ops (receipt : JudgedReceipt) :
    100 - bandCalibration.eHi receipt.provenOps = 0 ∧
    bandCalibration.eLo receipt.provenOps + bandCalibration.eMinPerOp * 60 ≤ 100 ∧
    residualEnergy bandCalibration receipt.provenOps 100 = 60 ∧
    checkEnergyEnvelope bandCalibration receipt 100 0 = false := by
  simp [bandCalibration, residualEnergy, checkEnergyEnvelope]

structure RackContext where
  rackId : ByteArray
  epoch : Nat
  step : AriadneStep

/-- Public commitment, not an unauthenticated claim to be a MAC. The local
verifier owns the fixed context; the private witness never enters these bytes. -/
def rackReceiptBytes (ctx : RackContext) (verdict : Bool) : ByteArray :=
  hashBytes "OBEND.ENVELOPE.RACK.VERDICT/v1"
    (encodeFrame ctx.rackId (natBytes ctx.epoch)
      (encodeFrame (stepBytes ctx.step) ⟨#[if verdict then 1 else 0]⟩ ByteArray.empty))

structure FabulousRackReceipt where
  receiptBytes : ByteArray
  size32 : receiptBytes.size = 32

def makeFabulousRackReceipt (ctx : RackContext) (verdict : Bool) : FabulousRackReceipt :=
  ⟨rackReceiptBytes ctx verdict, by
    unfold rackReceiptBytes hashBytes
    apply cshake32ByteArray_size⟩

/-- The local full-proof checker is the existing ClusterStep auditor. The fixed
public context is derived from the actual judged step, never the witness. -/
def verifyInRack (rackId : ByteArray) (epoch : Nat) (ctx : ClusterStepContext) : FabulousRackReceipt :=
  makeFabulousRackReceipt ⟨rackId, epoch, ctx.step⟩ (verifyClusterStep ctx)

theorem fabulousRackReceipt_at_most_two_states (ctx : RackContext) (verdict : Bool) :
    (makeFabulousRackReceipt ctx verdict).receiptBytes = rackReceiptBytes ctx false ∨
      (makeFabulousRackReceipt ctx verdict).receiptBytes = rackReceiptBytes ctx true := by
  cases verdict
  · exact Or.inl rfl
  · exact Or.inr rfl

structure EnvelopeEvidence where
  packet : EgressPacket
  inclusion : ReceiptInclusionProof
  location : LocationClaim
  measuredRtt : Nat
  pages : Array VramPageOpening
  energyMeter : Nat

structure EnvelopeAuthority where
  log : JudgedReceiptLog
  hardware : HardwareClassPolicy
  challenge : VramChallenge
  calibration : EnergyCalibration
  maxResidual : Nat

/-- Tie all three envelopes to the same committed step/state/epoch. A local
decoy cannot substitute a different receipted workload in the other gates. -/
def checkPhysicalEnvelope (authority : EnvelopeAuthority) (e : EnvelopeEvidence) : Bool :=
  checkCommitBeforeForward authority.log e.packet e.inclusion &&
  verifySealedVram authority.hardware authority.challenge e.location e.measuredRtt e.pages &&
  checkEnergyEnvelope authority.calibration e.location.receipt e.energyMeter authority.maxResidual &&
  decide (e.location.receipt.stateHash = e.packet.pktStateHash ∧
    e.location.receipt.epoch = authority.log.epoch ∧
    authority.challenge.logEpoch = authority.log.epoch) &&
  match authority.log.entries[e.inclusion.index]? with
  | none => false
  | some r => decide (stepBytes r.context.step = stepBytes e.location.receipt.context.step ∧
      r.provenOps = e.location.receipt.provenOps)

open Obend.Judge.SvenvsCorrigibility

structure BarrierTiming where
  tau : Nat
  lDetect : Nat
  lProve : Nat
  lActuate : Nat

/-- All physical evidence participates in the actual Svenvs policy. Timing is
an admission condition, not evidence of a safe plant by itself. -/
def envelopePolicy {S A : Type} (authority : EnvelopeAuthority) (evidence : S → A → EnvelopeEvidence)
    (plantPolicy : Policy S A) (B : Nat) (timing : BarrierTiming) : Policy S A :=
  fun s a => decide (timing.lDetect + timing.lProve + timing.lActuate ≤ B * timing.tau) &&
    checkPhysicalEnvelope authority (evidence s a) && plantPolicy s a

theorem checkPhysicalEnvelope_sound (authority : EnvelopeAuthority) (e : EnvelopeEvidence)
    (h : checkPhysicalEnvelope authority e = true) :
    checkCommitBeforeForward authority.log e.packet e.inclusion = true ∧
    verifySealedVram authority.hardware authority.challenge e.location e.measuredRtt e.pages = true ∧
    checkEnergyEnvelope authority.calibration e.location.receipt e.energyMeter authority.maxResidual = true ∧
    e.location.receipt.stateHash = e.packet.pktStateHash ∧
    e.location.receipt.epoch = authority.log.epoch ∧
    authority.challenge.logEpoch = authority.log.epoch ∧
    ∃ r, authority.log.entries[e.inclusion.index]? = some r ∧
      stepBytes r.context.step = stepBytes e.location.receipt.context.step ∧
      r.provenOps = e.location.receipt.provenOps := by
  unfold checkPhysicalEnvelope at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc, hv⟩, he⟩, hs, hep, hch⟩, hm⟩ := h
  cases hr : authority.log.entries[e.inclusion.index]? with
  | none => simp [hr] at hm
  | some r =>
    simp only [hr, decide_eq_true_eq] at hm
    exact ⟨hc, hv, he, hs, hep, hch, r, rfl, hm.1, hm.2⟩

theorem enveloped_nonfallback_requires_envelope {S A : Type}
    (authority : EnvelopeAuthority) (evidence : S → A → EnvelopeEvidence)
    (plantPolicy : Policy S A) (B : Nat) (timing : BarrierTiming)
    (recov : S → A) (ctrl : S → A) (s : S)
    (hNonFallback : enveloped (envelopePolicy authority evidence plantPolicy B timing) recov ctrl s ≠ recov s) :
    timing.lDetect + timing.lProve + timing.lActuate ≤ B * timing.tau ∧
    checkPhysicalEnvelope authority (evidence s (ctrl s)) = true ∧
    plantPolicy s (ctrl s) = true := by
  unfold enveloped at hNonFallback
  split at hNonFallback
  · rename_i hPol
    simp only [envelopePolicy, Bool.and_eq_true, decide_eq_true_eq] at hPol
    exact ⟨hPol.1.1, hPol.1.2, hPol.2⟩
  · exact False.elim (hNonFallback rfl)

/-- Plant safety and bounded recovery are preserved along every selected run.
The plant policy must preserve BOTH invariants, and the fallback must too;
receipt validity and a positive timing margin cannot replace these obligations. -/
theorem physicalEnvelope_corrigibility_safe {S A : Type}
    (step : S → A → S) (init safe home : S → Prop) (recov : S → A)
    (authority : EnvelopeAuthority) (evidence : S → A → EnvelopeEvidence)
    (plantPolicy : Policy S A) (B : Nat) (timing : BarrierTiming)
    (initial : InitSafe init (fun s => safe s ∧ CWithin step recov home B s))
    (sound : SoundPolicy step (fun s => safe s ∧ CWithin step recov home B s) plantPolicy)
    (shield : SafeShield step (fun s => safe s ∧ CWithin step recov home B s) recov) :
    ∀ ctrl, Invariant step init
      (enveloped (envelopePolicy authority evidence plantPolicy B timing) recov ctrl)
      (fun s => safe s ∧ CWithin step recov home B s) := by
  apply safety_preservation initial _ shield
  intro s a hs ha
  simp only [envelopePolicy, Bool.and_eq_true] at ha
  exact sound s a hs ha.2

structure SwarmJobRow where
  jobId : Nat
  host : ByteArray
  gpuSecondsMetered : Nat
  tokensMetered : Nat
  landedReceiptHash : ByteArray
  provenOps : Nat
  receiptIndex : Nat
  inclusion : ReceiptInclusionProof

inductive SwarmMeterViolation where
  | missingReceipt (jobId : Nat)
  | mismatchedReceipt (jobId : Nat)
  | residualBreach (jobId residual allowed : Nat)
  | duplicateReceipt (jobId receiptIndex : Nat)
  deriving DecidableEq, Repr

structure SwarmMeterSummary where
  jobs : Nat
  gpuSeconds : Nat
  tokens : Nat
  deriving DecidableEq, Repr

inductive SwarmMeterResult where
  | clean (summary : SwarmMeterSummary)
  | violation (reason : SwarmMeterViolation)
  deriving DecidableEq, Repr

/-- GPU-seconds use the same lower-curve arithmetic in calibrated meter units.
A row with positive work and no committed receipt, or meter reading below `eIdle + eLo`, is always refused. -/
def checkMeterRow (log : JudgedReceiptLog) (cal : EnergyCalibration) (maxResidual : Nat)
    (row : SwarmJobRow) : Option SwarmMeterViolation :=
  match log.entries[row.receiptIndex]? with
  | none => some (.missingReceipt row.jobId)
  | some r =>
      if row.inclusion.index ≠ row.receiptIndex ∨ verifyReceiptInclusion log row.inclusion ≠ true ∨
          row.landedReceiptHash ≠ receiptDigest r ∨ row.provenOps ≠ r.provenOps ∨
          row.jobId ≠ r.jobId ∨ row.host ≠ r.host ∨
          row.gpuSecondsMetered + cal.eta < cal.eIdle + cal.eLo r.provenOps then
        some (.mismatchedReceipt row.jobId)
      else if residualEnergy cal r.provenOps row.gpuSecondsMetered ≤ maxResidual then none
      else some (.residualBreach row.jobId (residualEnergy cal r.provenOps row.gpuSecondsMetered) maxResidual)

/-- Independent mathematical row semantics, stated with existential membership
and the unsaturated two-sided conservation inequality (`eIdle + eLo ≤ meter + eta ≤ eIdle + eLo + maxResidual`). -/
def MeterRowSpec (log : JudgedReceiptLog) (cal : EnergyCalibration) (maxResidual : Nat)
    (row : SwarmJobRow) : Prop :=
  ∃ r, log.entries[row.receiptIndex]? = some r ∧
    row.inclusion.index = row.receiptIndex ∧ verifyReceiptInclusion log row.inclusion = true ∧
    row.landedReceiptHash = receiptDigest r ∧ row.provenOps = r.provenOps ∧
    row.jobId = r.jobId ∧ row.host = r.host ∧
    (cal.eIdle + cal.eLo r.provenOps ≤ row.gpuSecondsMetered + cal.eta ∧
      row.gpuSecondsMetered + cal.eta ≤ cal.eIdle + cal.eLo r.provenOps + maxResidual)

def SwarmMeterSpec (log : JudgedReceiptLog) (cal : EnergyCalibration) (maxResidual : Nat)
    (rows : List SwarmJobRow) : Prop := ∀ row ∈ rows, MeterRowSpec log cal maxResidual row

def meterSummary (rows : Array SwarmJobRow) : SwarmMeterSummary :=
  rows.foldl (fun acc row => ⟨acc.jobs + 1, acc.gpuSeconds + row.gpuSecondsMetered,
    acc.tokens + row.tokensMetered⟩) ⟨0, 0, 0⟩

def auditSwarmComputeMeter (log : JudgedReceiptLog) (cal : EnergyCalibration)
    (maxResidual : Nat) (rows : Array SwarmJobRow) : SwarmMeterResult :=
  match rows.findSome? (checkMeterRow log cal maxResidual) with
  | none => .clean (meterSummary rows)
  | some v => .violation v

def findDupReceiptRow : List Nat → List SwarmJobRow → Option SwarmMeterViolation
  | _, [] => none
  | seen, row :: rest =>
    if row.receiptIndex ∈ seen then some (.duplicateReceipt row.jobId row.receiptIndex)
    else findDupReceiptRow (row.receiptIndex :: seen) rest

/-- Deduplicated swarm meter audit refusing multiple meter rows claiming the same `receiptIndex`. -/
def auditSwarmComputeMeterDedup (log : JudgedReceiptLog) (cal : EnergyCalibration)
    (maxResidual : Nat) (rows : Array SwarmJobRow) : SwarmMeterResult :=
  match findDupReceiptRow [] rows.toList with
  | some dup => .violation dup
  | none => auditSwarmComputeMeter log cal maxResidual rows

private theorem findDupReceiptRow_mem_ne_none :
    ∀ (xs : List SwarmJobRow) (acc : List Nat) {r' : SwarmJobRow},
      r'.receiptIndex ∈ acc → r' ∈ xs → findDupReceiptRow acc xs ≠ none
  | [], _, _, _, hm => by cases hm
  | x :: xs, acc, r', hIn, hm => by
    unfold findDupReceiptRow
    by_cases hx : x.receiptIndex ∈ acc
    · simp [hx]
    · simp only [hx, ↓reduceIte]
      rcases List.mem_cons.mp hm with rfl | hTail
      · exact absurd hIn hx
      · exact findDupReceiptRow_mem_ne_none xs (x.receiptIndex :: acc) (List.mem_cons_of_mem _ hIn) hTail

private theorem findDupReceiptRow_none_nodup :
    ∀ (seen : List Nat) (rs : List SwarmJobRow),
      findDupReceiptRow seen rs = none → (rs.map (·.receiptIndex)).Nodup
  | _, [], _ => List.Pairwise.nil
  | seen, r :: rest, hNone => by
    unfold findDupReceiptRow at hNone
    by_cases hc : r.receiptIndex ∈ seen
    · simp [hc] at hNone
    · simp only [hc, ↓reduceIte] at hNone
      refine List.Pairwise.cons (fun idx hMem hEq => ?_) (findDupReceiptRow_none_nodup (r.receiptIndex :: seen) rest hNone)
      obtain ⟨r', hr', hIdx⟩ := List.mem_map.mp hMem
      have hIn : r'.receiptIndex ∈ r.receiptIndex :: seen := by
        rw [hIdx, ← hEq]; exact List.Mem.head _
      exact findDupReceiptRow_mem_ne_none rest (r.receiptIndex :: seen) hIn hr' hNone

theorem auditSwarmComputeMeterDedup_sound (log : JudgedReceiptLog) (cal : EnergyCalibration)
    (maxResidual : Nat) (rows : Array SwarmJobRow) (summary : SwarmMeterSummary)
    (hOk : auditSwarmComputeMeterDedup log cal maxResidual rows = .clean summary) :
    (rows.toList.map (·.receiptIndex)).Nodup ∧ SwarmMeterSpec log cal maxResidual rows.toList := by
  unfold auditSwarmComputeMeterDedup at hOk
  cases hd : findDupReceiptRow [] rows.toList with
  | some v => simp [hd] at hOk
  | none =>
    simp only [hd] at hOk
    have hNd := findDupReceiptRow_none_nodup [] rows.toList hd
    unfold auditSwarmComputeMeter at hOk
    cases hf : rows.findSome? (checkMeterRow log cal maxResidual) with
    | some v => simp [hf] at hOk
    | none =>
      refine ⟨hNd, ?_⟩
      intro row hr
      have hNone := Array.findSome?_eq_none_iff.mp hf row (Array.mem_def.mpr hr)
      unfold checkMeterRow at hNone
      cases he : log.entries[row.receiptIndex]? with
      | none => simp [he] at hNone
      | some r =>
        simp only [he] at hNone
        split at hNone
        · cases hNone
        · rename_i hGood; simp only [not_or, ne_eq, Decidable.not_not] at hGood
          split at hNone
          · rename_i hRes
            refine ⟨r, he, hGood.1, hGood.2.1, hGood.2.2.1, hGood.2.2.2.1, hGood.2.2.2.2.1,
              hGood.2.2.2.2.2.1, ?_, ?_⟩
            · omega
            · unfold residualEnergy at hRes; omega
          · cases hNone

theorem checkMeterRow_iff (log : JudgedReceiptLog) (cal : EnergyCalibration) (maxResidual : Nat)
    (row : SwarmJobRow) :
    checkMeterRow log cal maxResidual row = none ↔ MeterRowSpec log cal maxResidual row := by
  unfold checkMeterRow MeterRowSpec
  cases he : log.entries[row.receiptIndex]? with
  | none => simp
  | some r =>
    simp only [Option.some.injEq, exists_eq_left']
    split
    · rename_i bad
      simp only [Option.some_ne_none, false_iff]
      intro good
      rcases good with ⟨hi, hv, hh, hp, hj, hhost, hlo, _⟩
      rcases bad with b | b | b | b | b | b | b
      · exact b hi
      · exact b hv
      · exact b hh
      · exact b hp
      · exact b hj
      · exact b hhost
      · omega
    · rename_i good
      simp only [not_or, ne_eq, Decidable.not_not] at good
      have hlo : cal.eIdle + cal.eLo r.provenOps ≤ row.gpuSecondsMetered + cal.eta := by omega
      simp only [good.1, good.2.1, good.2.2.1, good.2.2.2.1, good.2.2.2.2.1, good.2.2.2.2.2.1, hlo, true_and]
      split <;> simp_all [residualEnergy] <;> omega

theorem auditSwarmComputeMeter_sound_iff (log : JudgedReceiptLog) (cal : EnergyCalibration)
    (maxResidual : Nat) (rows : Array SwarmJobRow) :
    auditSwarmComputeMeter log cal maxResidual rows = .clean (meterSummary rows) ↔
      SwarmMeterSpec log cal maxResidual rows.toList := by
  unfold auditSwarmComputeMeter
  have hn : rows.findSome? (checkMeterRow log cal maxResidual) = none ↔
      SwarmMeterSpec log cal maxResidual rows.toList := by
    simp only [Array.findSome?_eq_none_iff, checkMeterRow_iff, SwarmMeterSpec, Array.mem_def]
  cases h : rows.findSome? (checkMeterRow log cal maxResidual) <;> simp_all


open Obend.Analysis Obend.Hardware.SafePhysicalShield Obend.Hardware.CurrentLoop
open Obend.Hardware.SiliconOuroboros
/-- Two overlapping ADC zones cover the entire current core. -/
def currentLoopEnvelopeZone (i : CanonicalRat) : HWState := if i ≤ 2 then 1 else 2
def currentLoopEnvelopeStep (i : CanonicalRat) (u : HWAct) : CanonicalRat :=
  stepZoh currentLoopShieldZoh i (currentLoopShieldVoltage u)
def currentLoopEnvelopeSafe (i : CanonicalRat) : Prop := i ∈ mkCurrentLoopShieldSpec.core
def currentLoopEnvelopeHome (i : CanonicalRat) : Prop := 1/100 ≤ i ∧ i ≤ 399/100
def currentLoopEnvelopeInit (i : CanonicalRat) : Prop := currentLoopEnvelopeHome i
def currentLoopEnvelopeRecovery (i : CanonicalRat) : HWAct := currentLoopShieldRoot (currentLoopEnvelopeZone i)
def currentLoopEnvelopePolicy (i : CanonicalRat) (u : HWAct) : Bool :=
  mkCurrentLoopShieldSpec.actionOk (currentLoopEnvelopeZone i) u
private theorem currentLoopEnvelope_bounds {i : CanonicalRat} (h : currentLoopEnvelopeSafe i) :
    0 ≤ i ∧ i ≤ 4 := by
  have hc : mkCurrentLoopShieldSpec.core = ⟨0, 4⟩ := by decide +kernel
  simpa only [currentLoopEnvelopeSafe, hc, Interval.mem_iff] using h
private theorem currentLoopEnvelope_cell {i : CanonicalRat} (h : currentLoopEnvelopeSafe i) :
    i ∈ mkCurrentLoopShieldSpec.cell (currentLoopEnvelopeZone i) := by
  have hb := currentLoopEnvelope_bounds h
  unfold currentLoopEnvelopeZone
  split
  · have hc : mkCurrentLoopShieldSpec.cell 1 = ⟨0, 15/4⟩ := by decide +kernel
    rw [hc, Interval.mem_iff]; grind
  · have hc : mkCurrentLoopShieldSpec.cell 2 = ⟨5/4, 4⟩ := by decide +kernel
    rw [hc, Interval.mem_iff]; grind
private theorem currentLoopEnvelope_step_safe {i : CanonicalRat} {u : HWAct}
    (h : currentLoopEnvelopeSafe i) (ha : currentLoopEnvelopePolicy i u = true) :
    currentLoopEnvelopeSafe (currentLoopEnvelopeStep i u) := by
  have hf := flow_in_tube ha (by simpa only [currentLoopShieldFlow_zero] using currentLoopEnvelope_cell h)
    (currentLoopInterSampleFlow_sound _ u i (currentLoopEnvelope_cell h))
  simpa only [currentLoopShieldFlow_endpoint, currentLoopEnvelopeSafe, currentLoopEnvelopeStep] using hf.2
/-- Sensor-and-ADC-mediated current-loop step safety through `SensorReads` + `adcCode` + `zoneOf`. -/
theorem currentLoopShield_adc_step_safe {i : CanonicalRat} {vInMv : Nat} {u : HWAct}
    (hs : currentLoopEnvelopeSafe i) (hSens : mkCurrentLoopShieldSpec.SensorReads i vInMv)
    (ha : mkCurrentLoopShieldSpec.actionOk (mkCurrentLoopShieldSpec.zoneOf (mkCurrentLoopShieldSpec.adcCode vInMv)) u = true) :
    currentLoopEnvelopeSafe (currentLoopEnvelopeStep i u) := by
  have hCell := state_in_cell mkCurrentLoopShieldSpec currentLoopShield_wf hs hSens
  have hf := flow_in_tube ha (by simpa only [currentLoopShieldFlow_zero] using hCell)
    (currentLoopInterSampleFlow_sound _ u i hCell)
  simpa only [currentLoopShieldFlow_endpoint, currentLoopEnvelopeSafe, currentLoopEnvelopeStep] using hf.2
/-- The fallback moves every core state into a strict interior home interval in one sample. -/
theorem currentLoopEnvelope_recovery_home {i : CanonicalRat} (h : currentLoopEnvelopeSafe i) :
    currentLoopEnvelopeHome (currentLoopEnvelopeStep i (currentLoopEnvelopeRecovery i)) := by
  have hb := currentLoopEnvelope_bounds h
  unfold currentLoopEnvelopeRecovery currentLoopEnvelopeZone
  split <;> simp only [currentLoopEnvelopeHome, currentLoopEnvelopeStep, stepZoh,
    currentLoopShieldZoh, currentLoopShieldRoot, currentLoopShieldVoltage] <;> grind
private theorem currentLoopEnvelope_recoverable {i : CanonicalRat} (h : currentLoopEnvelopeSafe i) :
    CWithin currentLoopEnvelopeStep currentLoopEnvelopeRecovery currentLoopEnvelopeHome 1 i :=
  ⟨1, Nat.le_refl _, currentLoopEnvelope_recovery_home h⟩
/-- Concrete initialization, policy and fallback proofs for the RL shield over the entire home interval. -/
theorem instPhysicalEnvelopeCurrentLoopShield :
    InitSafe currentLoopEnvelopeInit (fun i => currentLoopEnvelopeSafe i ∧
      CWithin currentLoopEnvelopeStep currentLoopEnvelopeRecovery currentLoopEnvelopeHome 1 i) ∧
    SoundPolicy currentLoopEnvelopeStep (fun i => currentLoopEnvelopeSafe i ∧
      CWithin currentLoopEnvelopeStep currentLoopEnvelopeRecovery currentLoopEnvelopeHome 1 i) currentLoopEnvelopePolicy ∧
    SafeShield currentLoopEnvelopeStep (fun i => currentLoopEnvelopeSafe i ∧
      CWithin currentLoopEnvelopeStep currentLoopEnvelopeRecovery currentLoopEnvelopeHome 1 i) currentLoopEnvelopeRecovery := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hc : mkCurrentLoopShieldSpec.core = ⟨0, 4⟩ := by decide +kernel
    have hs : currentLoopEnvelopeSafe i := by
      unfold currentLoopEnvelopeInit currentLoopEnvelopeHome at hi
      rw [currentLoopEnvelopeSafe, hc, Interval.mem_iff]; grind
    exact ⟨hs, currentLoopEnvelope_recoverable hs⟩
  · intro i u hi hu
    have hn := currentLoopEnvelope_step_safe hi.1 hu
    exact ⟨hn, currentLoopEnvelope_recoverable hn⟩
  · intro i hi
    have ha : currentLoopEnvelopePolicy i (currentLoopEnvelopeRecovery i) = true :=
      currentLoopShieldRoot_passes _
    have hn := currentLoopEnvelope_step_safe hi.1 ha
    exact ⟨hn, currentLoopEnvelope_recoverable hn⟩
/-- Arbitrarily many envelope-controlled RL samples preserve safety and one-sample recovery. -/
theorem currentLoopPhysicalEnvelope_corrigibility_safe (authority : EnvelopeAuthority)
    (evidence : CanonicalRat → HWAct → EnvelopeEvidence) (timing : BarrierTiming) :
    ∀ ctrl, Invariant currentLoopEnvelopeStep currentLoopEnvelopeInit
      (enveloped (envelopePolicy authority evidence currentLoopEnvelopePolicy 1 timing) currentLoopEnvelopeRecovery ctrl)
      (fun i => currentLoopEnvelopeSafe i ∧
        CWithin currentLoopEnvelopeStep currentLoopEnvelopeRecovery currentLoopEnvelopeHome 1 i) := by
  obtain ⟨hi, hp, hs⟩ := instPhysicalEnvelopeCurrentLoopShield
  exact physicalEnvelope_corrigibility_safe _ _ _ _ _ authority evidence _ 1 timing hi hp hs
/-- Between each pair of reachable samples, the selected RL reconstruction stays in the physical envelope. -/
theorem currentLoopPhysicalEnvelope_continuous_safe (authority : EnvelopeAuthority)
    (evidence : CanonicalRat → HWAct → EnvelopeEvidence) (timing : BarrierTiming)
    (ctrl : CanonicalRat → HWAct) (i : CanonicalRat)
    (hr : Reach currentLoopEnvelopeStep currentLoopEnvelopeInit
      (enveloped (envelopePolicy authority evidence currentLoopEnvelopePolicy 1 timing) currentLoopEnvelopeRecovery ctrl) i) :
    ∀ t, 0 ≤ t → t ≤ mkCurrentLoopShieldSpec.Ts →
      currentLoopShieldFlow i
        (enveloped (envelopePolicy authority evidence currentLoopEnvelopePolicy 1 timing) currentLoopEnvelopeRecovery ctrl i) t
          ∈ mkCurrentLoopShieldSpec.phys := by
  have hs := (currentLoopPhysicalEnvelope_corrigibility_safe authority evidence timing ctrl i hr).1
  apply currentLoopShieldFlow_safe _ _ _ (currentLoopEnvelope_cell hs)
  unfold enveloped
  split
  · rename_i h
    simp only [envelopePolicy, Bool.and_eq_true] at h
    exact h.2
  · exact currentLoopShieldRoot_passes _

theorem checkPhysicalEnvelope_inhabited (payload host page nonce hardwareId : ByteArray)
    (epoch job : Nat) :
    ∃ (auth : EnvelopeAuthority) (ev : EnvelopeEvidence), checkPhysicalEnvelope auth ev = true := by
  let stateH := hashBytes "OBEND.ENVELOPE.STATE/v1" payload
  let r : JudgedReceipt := ⟨validClusterStepCtx, stateH, 7500000, epoch, job, host⟩
  let log := commitReceiptLog #[r] 0 epoch
  let policy : HardwareClassPolicy := ⟨hardwareId, 1000, 2000, 1, 0, 1⟩
  let challenge : VramChallenge := ⟨nonce, epoch, pageDigest 0 page⟩
  let claim : LocationClaim := ⟨r, hardwareId, pageDigest 0 page, 50000⟩
  let openings : Array VramPageOpening := #[⟨page, ⟨0, #[]⟩⟩]
  let pkt : EgressPacket := ⟨payload, stateH⟩
  let inc : ReceiptInclusionProof := ⟨0, #[]⟩
  let auth : EnvelopeAuthority := ⟨log, policy, challenge, bandCalibration, 0⟩
  let ev : EnvelopeEvidence := ⟨pkt, inc, claim, 0, openings, 40⟩
  have hj : checkJudgedReceipt r = true := by
    unfold checkJudgedReceipt
    have hctx : verifyClusterStep validClusterStepCtx = true := rfl
    change (verifyClusterStep validClusterStepCtx && decide (_ ∧ _ ∧ _)) = true
    rw [hctx]
    simp [r, stateH, hashBytes_size, validClusterStepCtx]
  have hi : verifyReceiptInclusion log inc = true := by
    have hep : r.epoch = epoch := rfl
    simp [verifyReceiptInclusion, log, inc, hj, hep, verifyOpening,
      logRoot, commitReceiptLog, merkleRoot, climbMerkle, receiptDigest, hashBytes_size]
  have hcbf : checkCommitBeforeForward log pkt inc = true := by
    unfold checkCommitBeforeForward
    change (verifyReceiptInclusion log inc && decide (_ ∧ _)) = true
    rw [hi]
    simp [log, inc, pkt, r, stateH, commitReceiptLog]
  have offsets : deriveVramChallengeOffsets policy challenge claim = #[0] := by
    simp [deriveVramChallengeOffsets, policy, challengeOffsets]
    exact Nat.mod_one _
  have hvram : verifySealedVram policy challenge claim 0 openings = true := by
    unfold verifySealedVram
    rw [offsets]
    simp [verifyRttEnvelope, policy, challenge, claim, r, openings, verifyVramPage,
      verifyOpening, climbMerkle, pageDigest, hashBytes_size]
  refine ⟨auth, ev, ?_⟩
  unfold checkPhysicalEnvelope
  dsimp only [auth, ev]
  rw [hcbf, hvram]
  simp [log, pkt, inc, commitReceiptLog, challenge, claim, r, stateH,
    checkEnergyEnvelope, residualEnergy, bandCalibration]

example (log : JudgedReceiptLog) (cal : EnergyCalibration) :
    auditSwarmComputeMeterDedup log cal 0 #[] = .clean ⟨0, 0, 0⟩ := rfl
example : currentLoopEnvelopeSafe 2 ∧ mkCurrentLoopShieldSpec.SensorReads (5/2) 2 ∧
    mkCurrentLoopShieldSpec.actionOk (mkCurrentLoopShieldSpec.zoneOf (mkCurrentLoopShieldSpec.adcCode 2)) 0 = true := by
  refine ⟨by unfold currentLoopEnvelopeSafe; decide +kernel, by decide +kernel, by decide +kernel⟩

end Obend.ClusterGov.PhysicalEnvelope
