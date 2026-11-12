module
/-
# Obend.Trailblaze.CathedralApex — End-to-End Composition: `ZkStripe` → `Reasons` → `HyperLaw` → `ClusterGov`

Whole-system interface composition module verifying in Lean's kernel today (with `0 sorry` and `0`
custom `axiom`s) that Organ O5 (`Obend.Trailblaze.ZkStripe`), `Obend.Reasons`, `Obend.Run.HyperLaw`,
and Organ O6 (`Obend.Trailblaze.ClusterGov`) compose seamlessly across exact types:

- `CathedralGovernanceTurn` binds an authenticated multi-hop `tlsn` HTTPS `CallTree` directly to
  `AriadneStep.batchCallTreeRoot` via `ZkStripe.callTreeDigest`, audits `Sable` $F_O$ overflow-free
  integer inference and `Ozaki` schedule-invariant collectives under `HyperLaw2NonInterference`,
  and requires joint well-founded support in `Obend.Reasons.wf`.
- `apex_cathedral_zkstripe_to_clustergov_sound` proves end-to-end soundness over
  `[ZkStripeObligations]` and `[ClusterGovObligations]`.
-/
public import Obend.Trailblaze.ZkStripe
public import Obend.Trailblaze.ClusterGov
public import Obend.Reasons
public import Obend.Run.HyperLaw

public section
namespace Obend.Trailblaze.CathedralApex

open Obend.Digest.HashBytes (Hash Collision)
open Obend.Run.HyperLaw (HyperLaw2NonInterference checkHyperLaw2NonInterference
  checkHyperLaw2NonInterference_sound)
open Obend.Trailblaze.ZkStripe (HttpsSessionNode ZkStripePolicy ZkStripeRefusal
  ZkStripeObligations callTreeDigest auditZkStripeCallTree verifyZkStripeCallTree
  IsBalancedVpaTrace lexJsonVpaSymbols auditNodes_root_props buildCallTreeProgram)
open Obend.Trailblaze.ClusterGov (ClusterStepContext ClusterGovRefusal ClusterGovObligations
  ClusterReduceWorld AllReduceTree clusterPublicView runScheduledAllReduce
  auditClusterStep apex_verifiable_ai_cluster_step intDot embedModP decodeSignedModP)

set_option autoImplicit false

/-! ## §1. Whole-System `CathedralGovernanceTurn` Carrier & Joint `Reasons` Program -/

/-- Unified governance turn wiring an authenticated `ZkStripe` dataset/webhook `CallTree` into a
    verifiable `ClusterGov` AI step (`AriadneStep.batchCallTreeRoot`), paired 2-trace `HyperLaw`
    schedule audit, and `Obend.Reasons` policy admission. -/
structure CathedralGovernanceTurn where
  hashFn            : Hash
  zkPolicy          : ZkStripePolicy
  batchCallTree     : HttpsSessionNode
  clusterCtx        : ClusterStepContext
  scheduleTracePair : List (ClusterReduceWorld × ClusterReduceWorld)
  cathedralRules    : List Obend.Reasons.Rule
  cathedralTarget   : String

/-- Named refusal diagnostic for whole-cathedral `ZkStripe → ClusterGov` turn admission. -/
inductive CathedralTurnRefusal where
  | zkStripeRefused (err : ZkStripeRefusal)
  | batchRootWeldMismatch (treeDigest stepBatchRoot : Nat)
  | clusterStepRefused (err : ClusterGovRefusal)
  | covertChannelDetected
  | cathedralPolicyUnsupported (target : String) (status : Obend.Reasons.Status)
  deriving DecidableEq, Repr

/-- Modularly compose the certified `ZkStripe` conclusion (`turn.zkPolicy.targetConclusion`),
    certified `ClusterGov` conclusion (`turn.clusterCtx.targetConcl`), and cross-organ weld/HyperLaw
    attestations into the top-level cathedral `Obend.Reasons.Program`. -/
@[expose] def buildCathedralProgram (turn : CathedralGovernanceTurn) : Obend.Reasons.Program where
  facts := [
    turn.zkPolicy.targetConclusion,
    turn.clusterCtx.targetConcl,
    "zkstripe_root_bound",
    "ozaki_hyperlaw_verified"
  ]
  rules := turn.cathedralRules

/-- Audit an end-to-end `CathedralGovernanceTurn`, returning `(committedTreeDigest, reducedSlices)`
    when every organ and cross-organ digest weld succeeds, or a named `CathedralTurnRefusal`. -/
@[expose] def auditCathedralTurn (turn : CathedralGovernanceTurn) :
    Except CathedralTurnRefusal (Nat × List Int) :=
  match auditZkStripeCallTree turn.zkPolicy turn.batchCallTree with
  | .error zErr => .error (.zkStripeRefused zErr)
  | .ok () =>
    let treeDigest := callTreeDigest turn.hashFn turn.batchCallTree
    if treeDigest != turn.clusterCtx.step.batchCallTreeRoot then
      .error (.batchRootWeldMismatch treeDigest turn.clusterCtx.step.batchCallTreeRoot)
    else
      match auditClusterStep turn.clusterCtx with
      | .error cErr => .error (.clusterStepRefused cErr)
      | .ok reducedSlices =>
        if !checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair then
          .error .covertChannelDetected
        else
          let st := Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
                      turn.cathedralTarget
          if st == .supported then
            .ok (treeDigest, reducedSlices)
          else
            .error (.cathedralPolicyUnsupported turn.cathedralTarget st)

/-- Total boolean decision gate for `CathedralGovernanceTurn`. -/
@[expose] def checkCathedralTurn (turn : CathedralGovernanceTurn) : Bool :=
  (auditCathedralTurn turn).isOk


/-! ## §2. Whole-System Composition Theorem (`apex_cathedral_zkstripe_to_clustergov_sound`) -/

/-- **Cathedral End-to-End Composition Soundness (`apex_cathedral_zkstripe_to_clustergov_sound`)**:
    Whenever `checkCathedralTurn turn = true`, Lean's kernel certifies across all four composed
    subsystems (`ZkStripe`, `Reasons`, `HyperLaw`, `ClusterGov`) simultaneously:
    1. `ZkStripe` notarized `CallTree` verification passes with balanced VPA response framing,
    2. `AriadneStep.batchCallTreeRoot` equals `callTreeDigest turn.hashFn turn.batchCallTree`,
       binding any matching tree `otherTree` up to `Collision turn.hashFn`,
    3. `Sable` $F_O$ modular dot-product round-trip is exact with zero wraparound modulo `p`,
    4. `Ozaki` collective reduction is permutation-invariant and satisfies `HyperLaw2NonInterference`,
    5. `AriadneStep` compute ceiling `flopsUsed ≤ flopsCap` holds, and
    6. Unified `Obend.Reasons.wf` supports `turn.cathedralTarget`. -/
theorem apex_cathedral_zkstripe_to_clustergov_sound
    [ZkStripeObligations] [ClusterGovObligations]
    (turn : CathedralGovernanceTurn)
    (otherTree : HttpsSessionNode)
    (hTurn : checkCathedralTurn turn = true)
    (hOtherRoot : callTreeDigest turn.hashFn otherTree = turn.clusterCtx.step.batchCallTreeRoot) :
    verifyZkStripeCallTree turn.zkPolicy turn.batchCallTree = true ∧
      IsBalancedVpaTrace (lexJsonVpaSymbols turn.batchCallTree.redactedResponse) ∧
      callTreeDigest turn.hashFn turn.batchCallTree = turn.clusterCtx.step.batchCallTreeRoot ∧
      (turn.batchCallTree = otherTree ∨ Collision turn.hashFn) ∧
      2 * (intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs).natAbs <
        turn.clusterCtx.tensorBound.modulusP ∧
      decodeSignedModP turn.clusterCtx.tensorBound.modulusP
        (embedModP turn.clusterCtx.tensorBound.modulusP
          (intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs)) =
        intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs ∧
      HyperLaw2NonInterference clusterPublicView turn.scheduleTracePair ∧
      turn.clusterCtx.step.flopsUsed ≤ turn.clusterCtx.step.flopsCap ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
        turn.cathedralTarget = .supported := by
  unfold checkCathedralTurn auditCathedralTurn at hTurn
  cases hZk : auditZkStripeCallTree turn.zkPolicy turn.batchCallTree with
  | error e =>
    rw [hZk] at hTurn
    cases hTurn
  | ok u =>
    rw [hZk] at hTurn
    have hVerifyZk : verifyZkStripeCallTree turn.zkPolicy turn.batchCallTree = true := by
      simp [verifyZkStripeCallTree, hZk, Except.isOk, Except.toBool]
    have hVpaBal : IsBalancedVpaTrace (lexJsonVpaSymbols turn.batchCallTree.redactedResponse) := by
      unfold auditZkStripeCallTree at hZk
      cases hNodes : ZkStripe.auditNodes turn.zkPolicy turn.batchCallTree with
      | error e => rw [hNodes] at hZk; cases hZk
      | ok u' => exact (auditNodes_root_props hNodes).2.2.2
    simp only at hTurn
    split at hTurn
    · cases hTurn
    · next hNotMismatch =>
      have hWeldEq :
          callTreeDigest turn.hashFn turn.batchCallTree =
            turn.clusterCtx.step.batchCallTreeRoot := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hNotMismatch
        exact hNotMismatch
      have hSameDigest :
          callTreeDigest turn.hashFn turn.batchCallTree =
            callTreeDigest turn.hashFn otherTree :=
        hWeldEq.trans hOtherRoot.symm
      have hBind :=
        ZkStripeObligations.tlsnAeadCommitmentBinding
          turn.hashFn turn.batchCallTree otherTree hSameDigest
      cases hCluster : auditClusterStep turn.clusterCtx with
      | error cErr =>
        rw [hCluster] at hTurn
        cases hTurn
      | ok reducedSlices =>
        rw [hCluster] at hTurn
        have hStepProps :=
          apex_verifiable_ai_cluster_step turn.clusterCtx reducedSlices
            turn.clusterCtx.workerSlices hCluster (List.Perm.refl _)
        simp only at hTurn
        split at hTurn
        · cases hTurn
        · next hNotHL =>
          have hHL :
              checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair = true := by
            cases h : checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair <;>
              simp_all
          split at hTurn
          · next hCatSt =>
            exact ⟨hVerifyZk, hVpaBal, hWeldEq, hBind, hStepProps.1, hStepProps.2.1,
              checkHyperLaw2NonInterference_sound hHL, hStepProps.2.2.2.1,
              beq_iff_eq.mp hCatSt⟩
          · cases hTurn


/-! ## §3. Concrete End-to-End Cathedral Turn Witness & Silver Smoke Runner -/

/-- Canonical end-to-end `CathedralGovernanceTurn` welding `ZkStripe.validFourHopCallTree`'s
    exact Merkle digest into `ClusterGov.validClusterStepCtx.step.batchCallTreeRoot`. -/
@[expose] def sampleCathedralTurn : CathedralGovernanceTurn :=
  let batchRoot := callTreeDigest ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let treeLeft : AllReduceTree :=
    .node (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1])) (.leaf [-30, 10, 5])
  let treeRight : AllReduceTree :=
    .node (.leaf [-30, 10, 5]) (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1]))
  { hashFn        := ZkStripe.fastMerkleHash
    zkPolicy      := ZkStripe.defaultZkStripePolicy
    batchCallTree := ZkStripe.validFourHopCallTree
    clusterCtx    := {
      ClusterGov.validClusterStepCtx with
      step := { ClusterGov.validClusterStepCtx.step with batchCallTreeRoot := batchRoot }
    }
    scheduleTracePair := [
      (⟨[0, 0, 0], 10⟩, ⟨[0, 0, 0], 20⟩),
      (runScheduledAllReduce treeLeft 10, runScheduledAllReduce treeRight 20)
    ]
    cathedralRules := [{
      name  := "cathedral_joint_admission"
      concl := "cathedral_turn_admitted"
      pos   := ["calltree_admitted", "step_admitted",
                "zkstripe_root_bound", "ozaki_hyperlaw_verified"]
      neg   := ["global_halt"]
    }]
    cathedralTarget := "cathedral_turn_admitted"
  }

/-- Planted bad cathedral turn: swaps `batchCallTreeRoot` to an unauthenticated digest `0xDEAD`,
    breaking the `ZkStripe → ClusterGov` lineage weld. -/
@[expose] def brokenWeldCathedralTurn : CathedralGovernanceTurn :=
  { sampleCathedralTurn with
    clusterCtx := {
      sampleCathedralTurn.clusterCtx with
      step := { sampleCathedralTurn.clusterCtx.step with batchCallTreeRoot := 0xDEAD }
    } }

/-- Executable Silver end-to-end smoke check for `CathedralApex`. -/
@[expose] def silverCathedralApexSmoke : Bool :=
  let expectedRoot := callTreeDigest ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let validOk :=
    match auditCathedralTurn sampleCathedralTurn with
    | .ok (r, slices) => r == expectedRoot && slices == [120, 30, 7]
    | .error _ => false
  let weldRefused :=
    match auditCathedralTurn brokenWeldCathedralTurn with
    | .error e => e == .batchRootWeldMismatch expectedRoot 0xDEAD
    | .ok _ => false
  validOk && weldRefused

example : checkCathedralTurn sampleCathedralTurn = true := by decide
example : silverCathedralApexSmoke = true := by decide

end Obend.Trailblaze.CathedralApex
end
