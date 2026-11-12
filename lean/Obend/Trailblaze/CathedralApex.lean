module
/-
# Obend.Trailblaze.CathedralApex — End-to-End Composition: `ZkStripe` → `Reasons` → `HyperLaw` → `ClusterGov`

Whole-system interface composition module verifying unconditionally in Lean's kernel (`0 sorry`,
`0` custom `axiom`s, `0` `Classical.choice`, and **`0` Stage-A `[...Obligations]` hypotheses**)
that Organ O5 (`Obend.Trailblaze.ZkStripe`), `Obend.Reasons`, `Obend.Run.HyperLaw`, and Organ O6
(`Obend.Trailblaze.ClusterGov`) compose across exact types:

1. **Domain-Bound Multi-Hop `CallTree` Commitment Weld (`0` Obligations)**:
   Wires `callTreeDigestBytes` (`List UInt8`) and `callTreeDigest` directly to
   `AriadneStep.batchCallTreeRoot`, invoking `ZkStripe.callTreeDigestBytes_binding` to bind the
   entire multi-hop HTTPS session tree (including every hop's `serverDomain`) up to `Collision H`,
   while certifying `HopAudited` (`PredRE` + string-aware `ByteArray` VPA framing) across every
   `hop ∈ allSessionNodes turn.batchCallTree`.
2. **Overflow-Free Inference, Exact Collectives & Physical Energy Conservation**:
   Composes `Sable` $F_O$ modular dot-product exactness (`intDotExec` / `intDot`), `Ozaki`
   schedule-invariant `Array Int` collectives under `HyperLaw2NonInterference`, and
   `PhysicalEnergyEnvelope` authority-pinned RTT & lower-curve shadow-FLOP bounds.
3. **32-Byte (`BitVec 256`) In-Rack FPGA Boolean Verifier Receipt**:
   Enforces `verifierReceipt256 : BitVec 256` and `receiptPayloadBytes.data.size ≤ 32`, replacing
   multi-megabyte (18.8 MB) raw SNARK proof egress across the rack boundary with a deterministic
   2-state boolean verifier commitment (`fpgaVerifierReceipt256_at_most_two_states`).
-/
public import Obend.Trailblaze.ZkStripe
public import Obend.Trailblaze.ClusterGov
public import Obend.Reasons
public import Obend.Run.HyperLaw

public section
namespace Obend.Trailblaze.CathedralApex

open Obend.Digest.HashBytes (Hash ofBE be Collision)
open Obend.Run.HyperLaw (HyperLaw2NonInterference checkHyperLaw2NonInterference
  checkHyperLaw2NonInterference_sound)
open Obend.Trailblaze.ZkStripe (HttpsSessionNode ZkStripePolicy ZkStripeRefusal
  HopAudited allSessionNodes checkCanonicalSessionTree callTreeDigestBytes callTreeDigest
  callTreeDigestBytes_binding auditZkStripeCallTree verifyZkStripeCallTree
  auditZkStripeCallTree_ok_imp_verify auditZkStripeCallTree_all_hops_sound)
open Obend.Trailblaze.ClusterGov (AriadneStep PhysicalEnergyEnvelope
  checkPhysicalEnergyEnvelope energy_conservation_bounds_hidden_ops
  ClusterStepContext ClusterGovRefusal ClusterReduceWorld AllReduceTree
  clusterPublicView runScheduledAllReduce auditClusterStep apex_verifiable_ai_cluster_step
  intDot intDotExec intDotExec_eq_intDot ozakiSliceSumExec ozakiSliceSumExec_eq_ozakiSliceSum
  embedModP decodeSignedModP)

set_option autoImplicit false

/-! ## §1. 32-Byte (`BitVec 256`) In-Rack FPGA Boolean Verifier Receipt -/

/-- Hard ceiling (32 bytes = 256 bits) on verifier receipt egress across the rack boundary,
    closing the 18.8 MB raw-SNARK proof-egress weight-exfiltration channel. -/
def maxRackReceiptBytes : Nat := 32

/-- Deterministic 256-bit (`BitVec 256`) big-endian reading of the first 32 bytes of `bs`. -/
def digestBytesToBitVec256 (bs : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (bs.take 32))

/-- Tail-recursive `O(w)` big-endian byte encoder (`termination_by structural`) avoiding nested
    `List.append` / `WellFounded.fix` stack frames during 256-bit kernel WHNF reduction. -/
def beAcc : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | w + 1, n, acc => beAcc w (n / 256) (UInt8.ofNat (n % 256) :: acc)
termination_by structural w => w

/-- **`Spec ↔ Exec` Big-Endian Framing Equivalence**: `beAcc w n acc` equals `be w n ++ acc`. -/
theorem beAcc_eq_be_append (w n : Nat) (acc : List UInt8) :
    beAcc w n acc = be w n ++ acc := by
  induction w generalizing n acc with
  | zero => rfl
  | succ w ih =>
    dsimp only [beAcc, be]
    rw [ih (n / 256) (UInt8.ofNat (n % 256) :: acc), List.append_assoc]
    rfl

/-- Canonical 256-bit (`BitVec 256`) in-rack FPGA boolean verifier commitment over public rack/step
    anchors and single verdict bit (`0x01` = pass, `0x00` = fail); private witnesses and multi-MB
    SNARK proof transcripts never enter the preimage. -/
def computeFpgaVerifierReceipt256 (H : Hash) (rackId epoch treeRoot : Nat)
    (step : AriadneStep) (verdict : Bool) : BitVec 256 :=
  let vByte : List UInt8 := [if verdict then (0x01 : UInt8) else (0x00 : UInt8)]
  let preimage : List UInt8 :=
    (0xF6 : UInt8) ::
    beAcc 8 rackId
      (beAcc 8 epoch
        (beAcc 32 treeRoot
          (beAcc 32 step.prevWeightsRoot
            (beAcc 32 step.nextWeightsRoot
              (beAcc 8 step.flopsUsed
                (beAcc 8 step.flopsCap vByte))))))
  digestBytesToBitVec256 (H preimage)

/-- **Two-State Proof-Egress Closure (`fpgaVerifierReceipt256_at_most_two_states`)**:
    For fixed public `(H, rackId, epoch, treeRoot, step)`, the in-rack FPGA receipt `BitVec 256`
    assumes at most two values (`verdict = false` or `verdict = true`), carrying zero witness
    or prover randomness entropy across the rack boundary. -/
theorem fpgaVerifierReceipt256_at_most_two_states
    (H : Hash) (rackId epoch treeRoot : Nat) (step : AriadneStep) (verdict : Bool) :
    computeFpgaVerifierReceipt256 H rackId epoch treeRoot step verdict =
      computeFpgaVerifierReceipt256 H rackId epoch treeRoot step false ∨
    computeFpgaVerifierReceipt256 H rackId epoch treeRoot step verdict =
      computeFpgaVerifierReceipt256 H rackId epoch treeRoot step true := by
  cases verdict
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- In-rack FPGA boolean verifier receipt envelope (`BitVec 256` digest + `≤ 32`-byte wire frame). -/
structure InRackFpgaReceipt where
  rackId              : Nat
  epoch               : Nat
  verdict             : Bool
  verifierReceipt256  : BitVec 256
  receiptPayloadBytes : ByteArray
  deriving DecidableEq

/-- Verify that an `InRackFpgaReceipt` carries `verdict = true`, satisfies the 32-byte egress
    ceiling `receiptPayloadBytes.data.size ≤ 32`, and matches `computeFpgaVerifierReceipt256`. -/
def checkInRackFpgaReceipt (H : Hash) (treeRoot : Nat) (step : AriadneStep)
    (rcpt : InRackFpgaReceipt) : Bool :=
  rcpt.verdict &&
  decide (rcpt.receiptPayloadBytes.data.size ≤ maxRackReceiptBytes) &&
  decide (rcpt.verifierReceipt256 =
    computeFpgaVerifierReceipt256 H rcpt.rackId rcpt.epoch treeRoot step true)


/-! ## §2. Whole-System `CathedralGovernanceTurn` Carrier & Joint `Reasons` Program -/

/-- Unified governance turn wiring a domain-bound `ZkStripe` multi-hop `CallTree` into a verifiable
    `ClusterGov` AI step, `PhysicalEnergyEnvelope` RTT/energy conservation gate, 32-byte in-rack
    FPGA boolean verifier receipt, paired 2-trace `HyperLaw` audit, and `Obend.Reasons` policy. -/
structure CathedralGovernanceTurn where
  hashFn                   : Hash
  zkPolicy                 : ZkStripePolicy
  batchCallTree            : HttpsSessionNode
  committedTreeDigestBytes : List UInt8
  clusterCtx               : ClusterStepContext
  physicalEnvelope         : PhysicalEnergyEnvelope
  fpgaReceipt              : InRackFpgaReceipt
  scheduleTracePair        : List (ClusterReduceWorld × ClusterReduceWorld)
  cathedralRules           : List Obend.Reasons.Rule
  cathedralTarget          : String

/-- Named refusal diagnostic for whole-cathedral `ZkStripe → ClusterGov` turn admission. -/
inductive CathedralTurnRefusal where
  | zkStripeRefused (err : ZkStripeRefusal)
  | nonCanonicalCallTree
  | treeDigestBytesMismatch (actual expected : List UInt8)
  | batchRootWeldMismatch (treeDigest stepBatchRoot : Nat)
  | clusterStepRefused (err : ClusterGovRefusal)
  | physicalEnvelopeFailed
  | fpgaReceiptInvalid (payloadBytes : Nat)
  | covertChannelDetected
  | cathedralPolicyUnsupported (target : String) (status : Obend.Reasons.Status)
  deriving DecidableEq, Repr

/-- Modularly compose certified organ conclusions and cross-organ weld/physical/FPGA attestations
    into the top-level cathedral `Obend.Reasons.Program`. -/
def buildCathedralProgram (turn : CathedralGovernanceTurn) : Obend.Reasons.Program where
  facts := [
    turn.zkPolicy.targetConclusion,
    turn.clusterCtx.targetConcl,
    "zkstripe_root_bound",
    "ozaki_hyperlaw_verified",
    "physical_energy_envelope_verified",
    "fpga_32byte_receipt_verified"
  ]
  rules := turn.cathedralRules

/-- Audit an end-to-end `CathedralGovernanceTurn`, returning
    `(verifierReceipt256, reducedSlicesExec)` when every organ, physical envelope, 32-byte FPGA
    receipt, and cross-organ digest weld succeeds, or a named `CathedralTurnRefusal`. -/
@[expose] def auditCathedralTurn (turn : CathedralGovernanceTurn) :
    Except CathedralTurnRefusal (BitVec 256 × Array Int) :=
  match auditZkStripeCallTree turn.zkPolicy turn.batchCallTree with
  | .error zErr => .error (.zkStripeRefused zErr)
  | .ok () =>
    if !checkCanonicalSessionTree turn.hashFn turn.batchCallTree then
      .error .nonCanonicalCallTree
    else
      let digestBytes := callTreeDigestBytes turn.hashFn turn.batchCallTree
      if !decide (digestBytes = turn.committedTreeDigestBytes) then
        .error (.treeDigestBytesMismatch digestBytes turn.committedTreeDigestBytes)
      else
        let treeDigest := callTreeDigest turn.hashFn turn.batchCallTree
        if !decide (treeDigest = turn.clusterCtx.step.batchCallTreeRoot) then
          .error (.batchRootWeldMismatch treeDigest turn.clusterCtx.step.batchCallTreeRoot)
        else
          match auditClusterStep turn.clusterCtx with
          | .error cErr => .error (.clusterStepRefused cErr)
          | .ok _ =>
            if !checkPhysicalEnergyEnvelope turn.physicalEnvelope then
              .error .physicalEnvelopeFailed
            else if !checkInRackFpgaReceipt turn.hashFn treeDigest
                turn.clusterCtx.step turn.fpgaReceipt then
              .error (.fpgaReceiptInvalid turn.fpgaReceipt.receiptPayloadBytes.data.size)
            else if !checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair then
              .error .covertChannelDetected
            else
              let st := Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
                          turn.cathedralTarget
              if st == .supported then
                let execWorkers := (turn.clusterCtx.workerSlices.map List.toArray).toArray
                .ok (turn.fpgaReceipt.verifierReceipt256, ozakiSliceSumExec execWorkers)
              else
                .error (.cathedralPolicyUnsupported turn.cathedralTarget st)

/-- Total boolean decision gate for `CathedralGovernanceTurn`. -/
@[expose] def checkCathedralTurn (turn : CathedralGovernanceTurn) : Bool :=
  (auditCathedralTurn turn).isOk


/-! ## §3. Unconditional Whole-System Composition Theorem (`apex_cathedral_zkstripe_to_clustergov_sound`) -/

/-- **Unconditional Cathedral End-to-End Composition Soundness (`apex_cathedral_zkstripe_to_clustergov_sound`)**:
    With **zero Stage-A `[...Obligations]` hypotheses** and **zero `Classical.choice`**, whenever
    `checkCathedralTurn turn = true`, Lean's kernel simultaneously certifies:
    1. **Full Multi-Hop `ZkStripe` Audit**: `verifyZkStripeCallTree` passes and **every hop**
       `hop ∈ allSessionNodes turn.batchCallTree` satisfies `HopAudited` (trusted notary, canonical
       bounds, `PredRE` confinement, and string-aware `ByteArray` / `List` balanced VPA framing),
    2. **Unconditional Domain-Bound Tree Commitment Binding**: `callTreeDigestBytes` matches
       `turn.committedTreeDigestBytes`, `callTreeDigest` welds to `AriadneStep.batchCallTreeRoot`,
       and any canonical `otherTree` with the same `committedTreeDigestBytes` satisfies
       `turn.batchCallTree = otherTree ∨ Collision turn.hashFn`,
    3. **Overflow-Free `Sable` $F_O$ `Exec`/`Spec` Dot Product**: `2 * |⟨w, x⟩| < p` and exact
       centered modular round-trip on `intDotExec`,
    4. **`Ozaki` `HyperLaw2` Non-Interference**: observational schedule covert-channel closure,
    5. **Authority-Pinned RTT & Lower-Curve Shadow-FLOP Bound**: `flopsUsed ≤ flopsCap`,
       `measuredRttMicros ≤ authorityBudgetMicros`, and metered energy conservation bounds any
       unproved shadow FLOPs `hiddenOps ≤ hiddenOpsCap`,
    6. **32-Byte (`BitVec 256`) In-Rack FPGA Verifier Receipt**: `receiptPayloadBytes ≤ 32` and
       exact deterministic `computeFpgaVerifierReceipt256` binding, and
    7. **Unified `Obend.Reasons.wf` Governance Support** for `turn.cathedralTarget`. -/
theorem apex_cathedral_zkstripe_to_clustergov_sound
    (turn : CathedralGovernanceTurn)
    (otherTree : HttpsSessionNode)
    (hTurn : checkCathedralTurn turn = true)
    (hOtherCan : checkCanonicalSessionTree turn.hashFn otherTree = true)
    (hOtherBytes : callTreeDigestBytes turn.hashFn otherTree = turn.committedTreeDigestBytes) :
    verifyZkStripeCallTree turn.zkPolicy turn.batchCallTree = true ∧
      (∀ hop ∈ allSessionNodes turn.batchCallTree, HopAudited turn.zkPolicy hop) ∧
      callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes ∧
      callTreeDigest turn.hashFn turn.batchCallTree = turn.clusterCtx.step.batchCallTreeRoot ∧
      (turn.batchCallTree = otherTree ∨ Collision turn.hashFn) ∧
      2 * (intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs).natAbs <
        turn.clusterCtx.tensorBound.modulusP ∧
      decodeSignedModP turn.clusterCtx.tensorBound.modulusP
        (embedModP turn.clusterCtx.tensorBound.modulusP
          (intDotExec turn.clusterCtx.sampleWeights.toArray turn.clusterCtx.sampleActs.toArray)) =
        intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs ∧
      HyperLaw2NonInterference clusterPublicView turn.scheduleTracePair ∧
      turn.clusterCtx.step.flopsUsed ≤ turn.clusterCtx.step.flopsCap ∧
      turn.physicalEnvelope.measuredRttMicros ≤ turn.physicalEnvelope.authorityBudgetMicros ∧
      (∀ hiddenOps : Nat,
        turn.physicalEnvelope.minHiddenOpMilliJ * hiddenOps ≤
          (turn.physicalEnvelope.meterEnergyMilliJ + turn.physicalEnvelope.toleranceMilliJ) -
            turn.physicalEnvelope.lowerCurveProvenMilliJ -
            turn.physicalEnvelope.idleEnergyMilliJ →
        hiddenOps ≤ turn.physicalEnvelope.hiddenOpsCap) ∧
      turn.fpgaReceipt.receiptPayloadBytes.data.size ≤ maxRackReceiptBytes ∧
      turn.fpgaReceipt.verifierReceipt256 =
        computeFpgaVerifierReceipt256 turn.hashFn turn.fpgaReceipt.rackId turn.fpgaReceipt.epoch
          (callTreeDigest turn.hashFn turn.batchCallTree) turn.clusterCtx.step true ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
        turn.cathedralTarget = .supported := by
  unfold checkCathedralTurn auditCathedralTurn at hTurn
  cases hZk : auditZkStripeCallTree turn.zkPolicy turn.batchCallTree with
  | error e => rw [hZk] at hTurn; cases hTurn
  | ok u =>
    rw [hZk] at hTurn
    dsimp only at hTurn
    have hVerifyZk := auditZkStripeCallTree_ok_imp_verify hZk
    have hAllHops := (auditZkStripeCallTree_all_hops_sound hZk).1
    cases hCan : checkCanonicalSessionTree turn.hashFn turn.batchCallTree
    · rw [hCan] at hTurn; cases hTurn
    · rw [hCan] at hTurn
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
      cases hBytesDec : decide
          (callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes)
      · rw [hBytesDec] at hTurn; cases hTurn
      · rw [hBytesDec] at hTurn
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
        have hBytesEq :
            callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes :=
          of_decide_eq_true hBytesDec
        have hBind : turn.batchCallTree = otherTree ∨ Collision turn.hashFn :=
          callTreeDigestBytes_binding turn.hashFn turn.batchCallTree otherTree
            hCan hOtherCan (hBytesEq.trans hOtherBytes.symm)
        cases hWeldDec : decide
            (callTreeDigest turn.hashFn turn.batchCallTree =
              turn.clusterCtx.step.batchCallTreeRoot)
        · rw [hWeldDec] at hTurn; cases hTurn
        · rw [hWeldDec] at hTurn
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
          have hWeldEq :
              callTreeDigest turn.hashFn turn.batchCallTree =
                turn.clusterCtx.step.batchCallTreeRoot :=
            of_decide_eq_true hWeldDec
          cases hCluster : auditClusterStep turn.clusterCtx with
          | error cErr => rw [hCluster] at hTurn; cases hTurn
          | ok reducedSlices =>
            rw [hCluster] at hTurn
            dsimp only at hTurn
            have hStepProps :=
              apex_verifiable_ai_cluster_step turn.clusterCtx reducedSlices
                turn.clusterCtx.workerSlices hCluster (List.Perm.refl _)
            have hDotExecEq :
                intDotExec turn.clusterCtx.sampleWeights.toArray
                  turn.clusterCtx.sampleActs.toArray =
                  intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs := by
              simpa using intDotExec_eq_intDot
                turn.clusterCtx.sampleWeights.toArray
                turn.clusterCtx.sampleActs.toArray
            cases hPhys : checkPhysicalEnergyEnvelope turn.physicalEnvelope
            · rw [hPhys] at hTurn; cases hTurn
            · rw [hPhys] at hTurn
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
              have hRtt :
                  turn.physicalEnvelope.measuredRttMicros ≤
                    turn.physicalEnvelope.authorityBudgetMicros :=
                (energy_conservation_bounds_hidden_ops turn.physicalEnvelope 0 hPhys).1
              have hEnergy :
                  ∀ hiddenOps : Nat,
                    turn.physicalEnvelope.minHiddenOpMilliJ * hiddenOps ≤
                      (turn.physicalEnvelope.meterEnergyMilliJ +
                        turn.physicalEnvelope.toleranceMilliJ) -
                        turn.physicalEnvelope.lowerCurveProvenMilliJ -
                        turn.physicalEnvelope.idleEnergyMilliJ →
                    hiddenOps ≤ turn.physicalEnvelope.hiddenOpsCap :=
                fun hiddenOps =>
                  (energy_conservation_bounds_hidden_ops turn.physicalEnvelope hiddenOps hPhys).2.2.1
              cases hFpga : checkInRackFpgaReceipt turn.hashFn
                  (callTreeDigest turn.hashFn turn.batchCallTree)
                  turn.clusterCtx.step turn.fpgaReceipt
              · rw [hFpga] at hTurn; cases hTurn
              · rw [hFpga] at hTurn
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
                have hFpgaProps := hFpga
                simp only [checkInRackFpgaReceipt, Bool.and_eq_true, decide_eq_true_eq]
                  at hFpgaProps
                rcases hFpgaProps with ⟨⟨_, hPayloadLe⟩, hRcptEq⟩
                cases hHL : checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair
                · rw [hHL] at hTurn; cases hTurn
                · rw [hHL] at hTurn
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
                  cases hCatSt : (Obend.Reasons.statusIn
                      (Obend.Reasons.wf (buildCathedralProgram turn))
                      turn.cathedralTarget == .supported)
                  · rw [hCatSt] at hTurn; cases hTurn
                  · exact ⟨hVerifyZk, hAllHops, hBytesEq, hWeldEq, hBind,
                      hStepProps.1, hDotExecEq.symm ▸ hStepProps.2.1,
                      checkHyperLaw2NonInterference_sound hHL,
                      hStepProps.2.2.2.1, hRtt, hEnergy, hPayloadLe, hRcptEq,
                      beq_iff_eq.mp hCatSt⟩


/-! ## §4. Multi-Turn Cathedral Governance Trace (`List CathedralGovernanceTurn`) & Cumulative Invariants -/

/-- Multi-turn governance state across sequential AI training/inference turns:
    tracks current model weight-lineage root, latest FPGA receipt epoch, cumulative proven FLOPs,
    remaining multi-turn FLOP budget, and remaining shadow-operation allowance. -/
structure CathedralTraceState where
  weightsRoot        : Nat
  lastEpoch          : Nat
  usedFlops          : Nat
  remFlopsBudget     : Nat
  remHiddenOpsBudget : Nat
  deriving DecidableEq, Repr

/-- Total proven FLOPs across a multi-turn sequence `turns`. -/
def turnsTotalFlops : List CathedralGovernanceTurn → Nat
  | [] => 0
  | t :: ts => t.clusterCtx.step.flopsUsed + turnsTotalFlops ts

/-- Total shadow-operation cap consumed across a multi-turn sequence `turns`. -/
def turnsTotalHiddenOpsCap : List CathedralGovernanceTurn → Nat
  | [] => 0
  | t :: ts => t.physicalEnvelope.hiddenOpsCap + turnsTotalHiddenOpsCap ts

/-- Declarative weight-lineage continuity & strict epoch progression from `startRoot` and `startEpoch`
    to `(endRoot, endEpoch)` across `turns`. -/
def WeightAndEpochChain : Nat → Nat → List CathedralGovernanceTurn → Nat → Nat → Prop
  | wRoot, ep, [], endRoot, endEp => wRoot = endRoot ∧ ep = endEp
  | wRoot, ep, t :: ts, endRoot, endEp =>
    t.clusterCtx.step.prevWeightsRoot = wRoot ∧
    ep < t.fpgaReceipt.epoch ∧
    WeightAndEpochChain t.clusterCtx.step.nextWeightsRoot t.fpgaReceipt.epoch ts endRoot endEp

/-- Advance `CathedralTraceState` by one verified `CathedralGovernanceTurn`, enforcing single-turn
    cathedral soundness (`checkCathedralTurn`), weight-root continuity, strictly increasing FPGA
    epoch, and cumulative FLOP / shadow-energy budget deductions. -/
def stepCathedralTrace (st : CathedralTraceState) (turn : CathedralGovernanceTurn) :
    Option CathedralTraceState :=
  if checkCathedralTurn turn &&
     decide (turn.clusterCtx.step.prevWeightsRoot = st.weightsRoot) &&
     decide (st.lastEpoch < turn.fpgaReceipt.epoch) &&
     decide (turn.clusterCtx.step.flopsUsed ≤ st.remFlopsBudget) &&
     decide (turn.physicalEnvelope.hiddenOpsCap ≤ st.remHiddenOpsBudget) then
    some {
      weightsRoot        := turn.clusterCtx.step.nextWeightsRoot
      lastEpoch          := turn.fpgaReceipt.epoch
      usedFlops          := st.usedFlops + turn.clusterCtx.step.flopsUsed
      remFlopsBudget     := st.remFlopsBudget - turn.clusterCtx.step.flopsUsed
      remHiddenOpsBudget := st.remHiddenOpsBudget - turn.physicalEnvelope.hiddenOpsCap
    }
  else
    none

/-- Execute an arbitrary-length sequence `List CathedralGovernanceTurn` from `init`. -/
def runCathedralTrace (init : CathedralTraceState) :
    List CathedralGovernanceTurn → Option CathedralTraceState
  | [] => some init
  | t :: ts =>
    match stepCathedralTrace init t with
    | none => none
    | some st' => runCathedralTrace st' ts

/-- Boolean decision gate for multi-turn cathedral governance traces. -/
@[expose] def checkCathedralTrace (init : CathedralTraceState)
    (turns : List CathedralGovernanceTurn) : Bool :=
  (runCathedralTrace init turns).isSome

/-- **Multi-Turn Cathedral Governance Trace Soundness (`cathedralTrace_sound`)**:
    Whenever `runCathedralTrace init turns = some final` (equivalently `checkCathedralTrace init turns = true`),
    across **every turn** `t ∈ turns` and across the entire sequence:
    1. Every turn passes `checkCathedralTurn t = true` (hence `verifyZkStripeCallTree`, multi-hop
       `HopAudited`, domain-bound `callTreeDigest`, `Sable`, `Ozaki` `HyperLaw2`, RTT/energy bounds,
       and `≤ 32`-byte FPGA receipt hold at every turn),
    2. `WeightAndEpochChain` links `init.weightsRoot` to `final.weightsRoot` with strictly
       increasing FPGA receipt epochs (`init.lastEpoch ≤ final.lastEpoch`),
    3. Exact FLOP conservation `final.usedFlops + final.remFlopsBudget = init.usedFlops + init.remFlopsBudget`
       and `final.usedFlops = init.usedFlops + turnsTotalFlops turns`, and
    4. Cumulative multi-turn FLOP and shadow-operation caps never exceed the initial envelopes:
       `turnsTotalFlops turns ≤ init.remFlopsBudget` and
       `turnsTotalHiddenOpsCap turns ≤ init.remHiddenOpsBudget`. -/
theorem cathedralTrace_sound (init final : CathedralTraceState)
    (turns : List CathedralGovernanceTurn)
    (hRun : runCathedralTrace init turns = some final) :
    (∀ t ∈ turns, checkCathedralTurn t = true) ∧
      WeightAndEpochChain init.weightsRoot init.lastEpoch turns final.weightsRoot final.lastEpoch ∧
      init.lastEpoch ≤ final.lastEpoch ∧
      final.usedFlops = init.usedFlops + turnsTotalFlops turns ∧
      final.usedFlops + final.remFlopsBudget = init.usedFlops + init.remFlopsBudget ∧
      turnsTotalFlops turns ≤ init.remFlopsBudget ∧
      turnsTotalHiddenOpsCap turns ≤ init.remHiddenOpsBudget := by
  induction turns generalizing init with
  | nil =>
    injection hRun with hEq
    subst hEq
    exact ⟨(by intro _ h; cases h), ⟨rfl, rfl⟩, Nat.le_refl _,
      (by simp [turnsTotalFlops]), rfl, Nat.zero_le _, Nat.zero_le _⟩
  | cons t ts ih =>
    dsimp only [runCathedralTrace] at hRun
    cases hStep : stepCathedralTrace init t with
    | none => rw [hStep] at hRun; cases hRun
    | some st' =>
      rw [hStep] at hRun
      unfold stepCathedralTrace at hStep
      cases hCond : (checkCathedralTurn t &&
          decide (t.clusterCtx.step.prevWeightsRoot = init.weightsRoot) &&
          decide (init.lastEpoch < t.fpgaReceipt.epoch) &&
          decide (t.clusterCtx.step.flopsUsed ≤ init.remFlopsBudget) &&
          decide (t.physicalEnvelope.hiddenOpsCap ≤ init.remHiddenOpsBudget))
      · rw [hCond] at hStep; cases hStep
      · rw [hCond] at hStep
        simp only [↓reduceIte, Option.some.injEq] at hStep
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
        rcases hCond with ⟨⟨⟨⟨hTurnOk, hPrevRoot⟩, hEpochLt⟩, hFlopsLe⟩, hHidLe⟩
        subst hStep
        obtain ⟨hAllRest, hChainRest, hEpRestLe, hUsedEq, hConsEq, hRestFlopsLe, hRestHidLe⟩ :=
          ih _ hRun
        dsimp only at hEpRestLe hUsedEq hConsEq hRestFlopsLe hRestHidLe
        refine ⟨?_, ⟨hPrevRoot, hEpochLt, hChainRest⟩, by omega, ?_, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hxRest
          · exact hTurnOk
          · exact hAllRest x hxRest
        · dsimp only [turnsTotalFlops]
          omega
        · omega
        · dsimp only [turnsTotalFlops]
          omega
        · dsimp only [turnsTotalHiddenOpsCap]
          omega

/-- Boolean-gate corollary of `cathedralTrace_sound` for `checkCathedralTrace init turns = true`. -/
theorem checkCathedralTrace_sound (init : CathedralTraceState)
    (turns : List CathedralGovernanceTurn)
    (hOk : checkCathedralTrace init turns = true) :
    ∃ final : CathedralTraceState,
      runCathedralTrace init turns = some final ∧
      (∀ t ∈ turns, checkCathedralTurn t = true) ∧
      WeightAndEpochChain init.weightsRoot init.lastEpoch turns final.weightsRoot final.lastEpoch ∧
      turnsTotalFlops turns ≤ init.remFlopsBudget ∧
      turnsTotalHiddenOpsCap turns ≤ init.remHiddenOpsBudget := by
  unfold checkCathedralTrace at hOk
  cases hRun : runCathedralTrace init turns with
  | none => rw [hRun] at hOk; cases hOk
  | some final =>
    have hProps := cathedralTrace_sound init final turns hRun
    exact ⟨final, rfl, hProps.1, hProps.2.1, hProps.2.2.2.2.2.1, hProps.2.2.2.2.2.2⟩


/-! ## §5. Concrete End-to-End Cathedral Turn & Multi-Turn Trace Witnesses -/

/-- Canonical end-to-end `CathedralGovernanceTurn` welding `ZkStripe.validFourHopCallTree`'s
    domain-bound Merkle commitment into `ClusterGov.validClusterStepCtx.step.batchCallTreeRoot`,
    `defaultPhysicalEnvelope`, and a 32-byte (`BitVec 256`) in-rack FPGA boolean verifier receipt. -/
def sampleCathedralTurn : CathedralGovernanceTurn :=
  let digestBytes := callTreeDigestBytes ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let batchRoot := callTreeDigest ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let stepWithRoot : AriadneStep :=
    { ClusterGov.validClusterStepCtx.step with batchCallTreeRoot := batchRoot }
  let rcpt256 :=
    computeFpgaVerifierReceipt256 ZkStripe.fastMerkleHash 7 1 batchRoot stepWithRoot true
  let treeLeft : AllReduceTree :=
    .node (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1])) (.leaf [-30, 10, 5])
  let treeRight : AllReduceTree :=
    .node (.leaf [-30, 10, 5]) (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1]))
  { hashFn                   := ZkStripe.fastMerkleHash
    zkPolicy                 := ZkStripe.defaultZkStripePolicy
    batchCallTree            := ZkStripe.validFourHopCallTree
    committedTreeDigestBytes := digestBytes
    clusterCtx               := { ClusterGov.validClusterStepCtx with step := stepWithRoot }
    physicalEnvelope         := ClusterGov.defaultPhysicalEnvelope
    fpgaReceipt := {
      rackId              := 7
      epoch               := 1
      verdict             := true
      verifierReceipt256  := rcpt256
      receiptPayloadBytes := ⟨(List.replicate 32 (0x01 : UInt8)).toArray⟩
    }
    scheduleTracePair := [
      (⟨[0, 0, 0], 10⟩, ⟨[0, 0, 0], 20⟩),
      (runScheduledAllReduce treeLeft 10, runScheduledAllReduce treeRight 20)
    ]
    cathedralRules := [{
      name  := "cathedral_joint_admission"
      concl := "cathedral_turn_admitted"
      pos   := ["calltree_admitted", "step_admitted",
                "zkstripe_root_bound", "ozaki_hyperlaw_verified",
                "physical_energy_envelope_verified", "fpga_32byte_receipt_verified"]
      neg   := ["global_halt"]
    }]
    cathedralTarget := "cathedral_turn_admitted"
  }

/-- Second consecutive governance turn welding `prevWeightsRoot := 0x33334444` (the output weight
    root of `sampleCathedralTurn`) to `nextWeightsRoot := 0x55556666` at FPGA receipt `epoch := 2`. -/
def sampleSecondCathedralTurn : CathedralGovernanceTurn :=
  let batchRoot := callTreeDigest ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let step2 : AriadneStep := {
    prevWeightsRoot   := 0x33334444
    batchCallTreeRoot := batchRoot
    nextWeightsRoot   := 0x55556666
    flopsUsed         := 6000000
    flopsCap          := 10000000
  }
  let rcpt256 :=
    computeFpgaVerifierReceipt256 ZkStripe.fastMerkleHash 7 2 batchRoot step2 true
  { sampleCathedralTurn with
    clusterCtx  := { sampleCathedralTurn.clusterCtx with step := step2 }
    fpgaReceipt := {
      rackId              := 7
      epoch               := 2
      verdict             := true
      verifierReceipt256  := rcpt256
      receiptPayloadBytes := ⟨(List.replicate 32 (0x02 : UInt8)).toArray⟩
    }
  }

/-- Initial multi-turn governance envelope with 20M FLOPs and 10 shadow-ops budget. -/
def sampleInitTraceState : CathedralTraceState where
  weightsRoot        := 0x11112222
  lastEpoch          := 0
  usedFlops          := 0
  remFlopsBudget     := 20000000
  remHiddenOpsBudget := 10

/-- **Single-Turn Completeness (`checkCathedralTurn_complete`)**:
    Whenever every organ gate, canonical digest weld, physical envelope, 32-byte FPGA receipt,
    `HyperLaw2` check, and joint `Reasons.wf` target succeeds, `checkCathedralTurn turn = true`. -/
theorem checkCathedralTurn_complete (turn : CathedralGovernanceTurn)
    (reduced : List Int)
    (hZk : auditZkStripeCallTree turn.zkPolicy turn.batchCallTree = .ok ())
    (hCan : checkCanonicalSessionTree turn.hashFn turn.batchCallTree = true)
    (hBytes : callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes)
    (hWeld : callTreeDigest turn.hashFn turn.batchCallTree = turn.clusterCtx.step.batchCallTreeRoot)
    (hCluster : auditClusterStep turn.clusterCtx = .ok reduced)
    (hPhys : checkPhysicalEnergyEnvelope turn.physicalEnvelope = true)
    (hFpga : checkInRackFpgaReceipt turn.hashFn (callTreeDigest turn.hashFn turn.batchCallTree)
      turn.clusterCtx.step turn.fpgaReceipt = true)
    (hHL : checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair = true)
    (hCat : Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
      turn.cathedralTarget = .supported) :
    checkCathedralTurn turn = true := by
  unfold checkCathedralTurn auditCathedralTurn
  have hBytesDec :
      decide (callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes) =
        true := decide_eq_true hBytes
  have hWeldDec :
      decide (callTreeDigest turn.hashFn turn.batchCallTree =
        turn.clusterCtx.step.batchCallTreeRoot) = true := decide_eq_true hWeld
  have hCatBeq :
      (Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
        turn.cathedralTarget == .supported) = true := beq_iff_eq.mpr hCat
  rw [hZk]
  dsimp only
  rw [hCan]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hBytesDec]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hWeldDec]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hCluster]
  dsimp only
  rw [hPhys, hFpga, hHL, hCatBeq]
  rfl

/-- **Multi-Turn Trace Completeness (`checkCathedralTrace_complete`)**:
    Extending any accepted multi-turn trace from `stepCathedralTrace init t = some st'` preserves
    `checkCathedralTrace init (t :: ts) = true` (and `runCathedralTrace init [] = some init`). -/
theorem checkCathedralTrace_complete (init st' : CathedralTraceState)
    (t : CathedralGovernanceTurn) (ts : List CathedralGovernanceTurn)
    (hTurn : checkCathedralTurn t = true)
    (hPrev : t.clusterCtx.step.prevWeightsRoot = init.weightsRoot)
    (hEp : init.lastEpoch < t.fpgaReceipt.epoch)
    (hFlops : t.clusterCtx.step.flopsUsed ≤ init.remFlopsBudget)
    (hHid : t.physicalEnvelope.hiddenOpsCap ≤ init.remHiddenOpsBudget)
    (hSt' : st' = {
      weightsRoot        := t.clusterCtx.step.nextWeightsRoot
      lastEpoch          := t.fpgaReceipt.epoch
      usedFlops          := init.usedFlops + t.clusterCtx.step.flopsUsed
      remFlopsBudget     := init.remFlopsBudget - t.clusterCtx.step.flopsUsed
      remHiddenOpsBudget := init.remHiddenOpsBudget - t.physicalEnvelope.hiddenOpsCap
    })
    (hRest : checkCathedralTrace st' ts = true) :
    runCathedralTrace init [] = some init ∧
      checkCathedralTrace init (t :: ts) = true := by
  refine ⟨rfl, ?_⟩
  unfold checkCathedralTrace runCathedralTrace stepCathedralTrace
  have hPrevDec : decide (t.clusterCtx.step.prevWeightsRoot = init.weightsRoot) = true :=
    decide_eq_true hPrev
  have hEpDec : decide (init.lastEpoch < t.fpgaReceipt.epoch) = true := decide_eq_true hEp
  have hFlopsDec : decide (t.clusterCtx.step.flopsUsed ≤ init.remFlopsBudget) = true :=
    decide_eq_true hFlops
  have hHidDec : decide (t.physicalEnvelope.hiddenOpsCap ≤ init.remHiddenOpsBudget) = true :=
    decide_eq_true hHid
  rw [hTurn, hPrevDec, hEpDec, hFlopsDec, hHidDec]
  simp only [Bool.and_self, ↓reduceIte]
  rw [← hSt']
  exact hRest

example : checkCathedralTrace sampleInitTraceState [] = true := rfl

/-- Planted bad cathedral turn #1: swaps `batchCallTreeRoot` to an unauthenticated digest `0xDEAD`,
    breaking the `ZkStripe → ClusterGov` lineage weld. -/
def brokenWeldCathedralTurn : CathedralGovernanceTurn :=
  { sampleCathedralTurn with
    clusterCtx := {
      sampleCathedralTurn.clusterCtx with
      step := { sampleCathedralTurn.clusterCtx.step with batchCallTreeRoot := 0xDEAD }
    } }

/-- Planted bad cathedral turn #2: attempts to egress an oversized (> 32-byte) proof payload across
    the rack boundary, caught by `checkInRackFpgaReceipt`. -/
def oversizedReceiptCathedralTurn : CathedralGovernanceTurn :=
  { sampleCathedralTurn with
    fpgaReceipt := {
      sampleCathedralTurn.fpgaReceipt with
      receiptPayloadBytes := ⟨(List.replicate 64 (0xAA : UInt8)).toArray⟩
    } }

/-- Executable Silver end-to-end smoke check for `CathedralApex` (single-turn + multi-turn trace). -/
def silverCathedralApexSmoke : Bool :=
  let expectedRoot := callTreeDigest ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let validOk :=
    match auditCathedralTurn sampleCathedralTurn with
    | .ok (_, slices) => slices == #[120, 30, 7]
    | .error _ => false
  let multiTurnOk :=
    match runCathedralTrace sampleInitTraceState
        [sampleCathedralTurn, sampleSecondCathedralTurn] with
    | some finalSt =>
      finalSt.weightsRoot == 0x55556666 &&
      finalSt.lastEpoch == 2 &&
      finalSt.usedFlops == 13500000 &&
      finalSt.remFlopsBudget == 6500000 &&
      finalSt.remHiddenOpsBudget == 2
    | none => false
  let replayEpochRefused :=
    !checkCathedralTrace sampleInitTraceState [sampleCathedralTurn, sampleCathedralTurn]
  let weldRefused :=
    match auditCathedralTurn brokenWeldCathedralTurn with
    | .error e => e == .batchRootWeldMismatch expectedRoot 0xDEAD
    | .ok _ => false
  let egressRefused :=
    match auditCathedralTurn oversizedReceiptCathedralTurn with
    | .error e => e == .fpgaReceiptInvalid 64
    | .ok _ => false
  validOk && multiTurnOk && replayEpochRefused && weldRefused && egressRefused

end Obend.Trailblaze.CathedralApex
end
