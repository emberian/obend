import Obend.Vault.Rehydration
import Obend.Consensus.Simplex
import Obend.Analysis.Hybrid
import Obend.Core.PrototypeProvenance
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/InnerSeamWeldTest.lean` — Inner-System Seam Weld Verification & Axiom Audit

End-to-end verification of the four inner-system welds:
1. **`Obend.Vault.Rehydration`** — `FrozenMembrane` / `LiveMembrane` `Core.Data` codecs,
   `Obend.Slot` (`membraneSlot`, `membranePayload`, `membraneEnvelope`), `membraneRehydrationLaw`,
   `membraneCellContract`, and `rehydrate_satisfies_law`.
2. **`Obend.Consensus.Simplex`** — `SimplexState` / `Cert` `Core.Data` codecs,
   `simplexViewMonotoneLaw`, `simplexQuorumLaw`, `simplexCellContract`, and `simplex_step_respects_law`.
3. **`Obend.Analysis.Hybrid`** — `HybridProblem` / `HybridCert` `Core.Data` codecs,
   `stepHybrid`, `verifyFlowpipe` + unsafe-zone disjointness check, and
   `hybridFlowpipeFormat : Obend.Judge.Format` (`"hybrid-flowpipe@1"`).
4. **`Obend.Core.PrototypeProvenance` (`LT4`)** — `PrototypeProvenance`, `HasPrototypeProvenance`,
   `checkPrototypeWithProvenance`, `checkPrototypeWithProvenance_sound`, and `forged_prototype_refused`.
-/

namespace Obend.Tests.InnerSeamWeldTest

open Obend.Core
open Obend.Law
open Obend.Spec.Law
open Obend.Vault.Rehydration
open Obend.Consensus.Simplex
open Obend.Analysis
open Obend.Core.PrototypeProvenance

-- ============================================================================
-- 1. Vault Rehydration Inner-System Weld Tests
-- ============================================================================

-- Roundtrip check for `FrozenMembrane.toData` / `FrozenMembrane.ofData?`.
#guard FrozenMembrane.ofData? demoFrozenBase.toData == some demoFrozenBase
#guard FrozenMembrane.ofData? (rehydrateAndStep demoFrozenBase 3).toData ==
  some (rehydrateAndStep demoFrozenBase 3)
#guard FrozenMembrane.ofData? (.natural 999) == none

-- Roundtrip check for `LiveMembrane.toData` / `LiveMembrane.ofData?`.
def sampleLiveMembrane : LiveMembrane :=
  { surfaceId  := "council-surface"
    epoch      := 5
    capDigest  := 101
    depDigest  := 202
    activeCaps := [.read, .control]
    liveness   := .Live }

#guard LiveMembrane.ofData? sampleLiveMembrane.toData == some sampleLiveMembrane
#guard LiveMembrane.ofData? (.label "malformed") == none

example (m : FrozenMembrane) : FrozenMembrane.ofData? m.toData = some m :=
  FrozenMembrane.ofData_toData m

example (m : LiveMembrane) : LiveMembrane.ofData? m.toData = some m :=
  LiveMembrane.ofData_toData m

-- `membraneSlot` admits a well-formed `FrozenMembrane` when its dependency digest and
-- capability boundary hold, and blocks/rejects a membrane with a mismatched digest or missing cap.
#guard (membraneSlot 202 [.read, .write]).usable (fun _ => true) demoFrozenBase == true
#guard (membraneSlot 999 [.read, .write]).usable (fun _ => true) demoFrozenBase == false
#guard (membraneSlot 202 [.read, .control]).usable (fun _ => true) demoFrozenBase == false

example :
    (membraneSlot 202 [.read, .write]).read (fun _ => true) (some demoFrozenBase) =
      .usable demoFrozenBase
        [(.depDigestValid 202, true),
         (.capBoundaryHolds .read, true),
         (.capBoundaryHolds .write, true)] := rfl

example :
    (membraneSlot 999 [.read, .write]).read (fun _ => true) (some demoFrozenBase) =
      .rejected demoFrozenBase :=
  membraneSlot_rejected_of_bad_depDigest (fun _ => true) 999 [.read, .write] demoFrozenBase rfl

example :
    (membraneSlot 202 [.read, .control]).read (fun _ => true) (some demoFrozenBase) =
      .rejected demoFrozenBase :=
  membraneSlot_rejected_of_missing_cap (fun _ => true) 202 [.read, .control] demoFrozenBase rfl

-- Valid `rehydrateAndStep` satisfies `membraneRehydrationLaw`.
#guard evalMembraneRehydrationLaw demoMembraneFacts demoFrozenBase (rehydrateAndStep demoFrozenBase 1) == true
#guard evalMembraneRehydrationLaw demoMembraneFacts demoFrozenBase (rehydrateAndStep demoFrozenBase 0) == true
#guard evalMembraneRehydrationLaw demoMembraneFacts demoFrozenBase demoFrozenTamperedDigest == false
#guard evalMembraneRehydrationLaw demoMembraneFacts
  { demoFrozenBase with capDigest := 0 }
  { demoFrozenBase with capDigest := 999 } == false
#guard evalMembraneRehydrationLaw demoMembraneFacts demoFrozenBase demoFrozenRegressedEpoch == false

example (fm : FrozenMembrane) (delta : Nat) :
    evalMembraneRehydrationLaw demoMembraneFacts fm (rehydrateAndStep fm delta) = true :=
  rehydrate_satisfies_law demoMembraneFacts fm delta

-- `#tooth` probes for `membraneRehydrationLaw`.
theorem test_membrane_tampered_digest_rejected :
    evalMembraneRehydrationLaw demoMembraneFacts demoFrozenBase demoFrozenTamperedDigest = false := rfl

theorem test_membrane_regressed_epoch_rejected :
    evalMembraneRehydrationLaw demoMembraneFacts demoFrozenBase demoFrozenRegressedEpoch = false := rfl

#tooth test_membrane_tampered_digest_rejected by mutation
  membraneRehydrationLaw := LawExpr.monotone "epoch"

#tooth test_membrane_regressed_epoch_rejected by mutation
  membraneRehydrationLaw := LawExpr.writeOnce "capDigest"

-- ============================================================================
-- 2. Consensus Simplex BFT Inner-System Weld Tests
-- ============================================================================

-- Roundtrip check for `Cert.toData` / `Cert.ofData?` and `SimplexState.toData` / `SimplexState.ofData?`.
#guard Cert.ofData? demoSimplexCert.toData == some demoSimplexCert
#guard Cert.ofData? (.natural 0) == none
#guard SimplexState.ofData? demoSimplexBase.toData == some demoSimplexBase
#guard SimplexState.ofData? (stepSimplexState demoSimplexBase 1 1 demoSimplexCert).toData ==
  some (stepSimplexState demoSimplexBase 1 1 demoSimplexCert)
#guard SimplexState.ofData? (.record []) == none

example (c : Cert) : Cert.ofData? c.toData = some c :=
  Cert.ofData_toData c

example (s : SimplexState) : SimplexState.ofData? s.toData = some s :=
  SimplexState.ofData_toData s

-- Valid Simplex transition satisfies `simplexViewMonotoneLaw` and `simplexQuorumLaw`.
#guard evalSimplexLaw demoSimplexFacts demoSimplexBase
  (stepSimplexState demoSimplexBase 2 1 demoSimplexCert) == true
#guard evalSimplexLaw demoSimplexFacts demoSimplexBase demoSimplexViewRegressed == false
#guard evalSimplexLaw demoSimplexFacts demoSimplexBase demoSimplexUnderQuorum == false
#guard evalSimplexLaw demoSimplexFacts demoSimplexBase demoSimplexLoweredThreshold == false

example :
    evalSimplexLawExpr demoSimplexFacts (some demoSimplexBase.toData)
      (stepSimplexState demoSimplexBase 2 1 demoSimplexCert).toData simplexViewMonotoneLaw = true ∧
    evalSimplexLawExpr demoSimplexFacts (some demoSimplexBase.toData)
      (stepSimplexState demoSimplexBase 2 1 demoSimplexCert).toData simplexQuorumLaw = true ∧
    evalSimplexLaw demoSimplexFacts demoSimplexBase
      (stepSimplexState demoSimplexBase 2 1 demoSimplexCert) = true :=
  simplex_step_respects_law demoSimplexFacts demoSimplexBase 2 1 demoSimplexCert (by decide)

-- `#tooth` probes for `simplexViewMonotoneLaw` and `simplexQuorumLaw`.
theorem test_simplex_view_regression_rejected :
    evalSimplexLaw demoSimplexFacts demoSimplexBase demoSimplexViewRegressed = false := rfl

theorem test_simplex_under_quorum_rejected :
    evalSimplexLaw demoSimplexFacts demoSimplexBase demoSimplexUnderQuorum = false := rfl

#tooth test_simplex_view_regression_rejected by mutation
  simplexViewMonotoneLaw := LawExpr.monotone "finalizedHeight"

#tooth test_simplex_under_quorum_rejected by mutation
  simplexQuorumLaw := LawExpr.monotone "finalizedHeight"

-- ============================================================================
-- 3. Hybrid Flowpipe Judge (`"hybrid-flowpipe@1"`) Inner-System Weld Tests
-- ============================================================================

-- Format name and roundtrip codecs for `HybridProblem` and `HybridCert`.
#guard hybridFlowpipeFormat.name == "hybrid-flowpipe@1"
#guard HybridProblem.ofData? demoHybridProblem.toData == some demoHybridProblem
#guard HybridProblem.ofData? (.natural 42) == none
#guard HybridCert.ofData? validHybridCert.toData == some validHybridCert
#guard HybridCert.ofData? badHybridCert.toData == some badHybridCert
#guard HybridCert.ofData? (.label "bad") == none

example (p : HybridProblem) : HybridProblem.ofData? p.toData = some p :=
  HybridProblem.ofData_toData p

example (c : HybridCert) : HybridCert.ofData? c.toData = some c :=
  HybridCert.ofData_toData c

-- `verifyFlowpipe` and `checkHybridFlowpipe` accept `validHybridCert` and boundary intervals
-- (`lo = envLo`, `hi = unsafeLo - 1`) while rejecting `badHybridCert`, `badStepCountHybridCert`,
-- inverted intervals (`initLo > initHi`), bogus modes, and unsafe-zone collisions (`hi = unsafeLo`).
#guard verifyFlowpipe demoHybridProblem validHybridCert == true
#guard verifyFlowpipe { demoHybridProblem with unsafeLo := 31, unsafeHi := 50 } validHybridCert == true
#guard verifyFlowpipe { demoHybridProblem with unsafeLo := 30, unsafeHi := 50 } validHybridCert == false
#guard verifyFlowpipe
  { demoHybridProblem with initMode := "cooling", initLo := 17, initHi := 20 }
  { schedule := [.flowStep], expectedFinalMode := "cooling", claimedSteps := 1 } == true
#guard verifyFlowpipe
  { demoHybridProblem with initMode := "cooling", initLo := 15, initHi := 20 }
  { schedule := [.flowStep], expectedFinalMode := "cooling", claimedSteps := 1 } == false
#guard verifyFlowpipe { demoHybridProblem with initLo := 26, initHi := 24 } validHybridCert == false
#guard verifyFlowpipe
  { demoHybridProblem with initMode := "bogus", initLo := 20, initHi := 22 }
  { schedule := [], expectedFinalMode := "bogus", claimedSteps := 0 } == false
#guard verifyFlowpipe
  { demoHybridProblem with initMode := "heating", initLo := 34, initHi := 35 }
  { schedule := [], expectedFinalMode := "heating", claimedSteps := 0 } == false
#guard verifyFlowpipe demoHybridProblem badHybridCert == false
#guard verifyFlowpipe demoHybridProblem badStepCountHybridCert == false
#guard verifyFlowpipe { demoHybridProblem with unsafeLo := 25, unsafeHi := 30 } validHybridCert == false
#guard checkHybridFlowpipe 0 demoHybridProblem validHybridCert == .ok
#guard checkHybridFlowpipe 0 demoHybridProblem badHybridCert ==
  .refused "flowpipe_invariant_or_unsafe_zone_violation" []

example :
    ∃ msg cs,
      Obend.Judge.check hybridFlowpipeFormat.badGrade
        hybridFlowpipeFormat.bad.1 hybridFlowpipeFormat.bad.2 = .refused msg cs :=
  hybridFlowpipeFormat.bad_refused

-- `#tooth` probe: `verifyFlowpipe` rejects `badHybridCert`.
theorem test_badHybridCert_rejected :
    verifyFlowpipe demoHybridProblem badHybridCert = false := rfl

#tooth test_badHybridCert_rejected by mutation
  verifyFlowpipe := fun _ _ => true

-- ============================================================================
-- 4. LT4 Intrinsic Prototype Fixpoint Provenance (`PrototypeProvenance`) Tests
-- ============================================================================

-- `PrototypeProvenance` accepts genuine unfolding of `Term.fix constSpec42 zeroSeed` (2 steps)
-- and multi-step `Term.fix branchingSpec42 branchingSeed11` (4 steps: beta -> beta -> ifZero -> add),
-- and rejects forged targets (`forgedTarget999`) or insufficient-fuel checks.
#guard PrototypeProvenance 2 constSpec42 zeroSeed genuineTarget42 == true
#guard PrototypeProvenance 4 branchingSpec42 branchingSeed11 genuineTarget42 == true
#guard PrototypeProvenance 3 branchingSpec42 branchingSeed11 genuineTarget42 == false
#guard PrototypeProvenance 5 constSpec42 zeroSeed forgedTarget999 == false
#guard PrototypeProvenance 0 constSpec42 zeroSeed genuineTarget42 == false

-- `checkPrototypeWithProvenance` accepts the genuine prototypes and refuses forged targets or ill-typed seeds.
#guard (checkPrototypeWithProvenance 2 constSpec42Env [] constSpec42 zeroSeed genuineTarget42).isOk == true
#guard (checkPrototypeWithProvenance 4 constSpec42Env [] branchingSpec42 branchingSeed11 genuineTarget42).isOk == true
#guard (checkPrototypeWithProvenance 2 constSpec42Env [] constSpec42 (.bound 999) genuineTarget42).isOk == false
#guard (checkPrototypeWithProvenance 5 constSpec42Env [] constSpec42 zeroSeed forgedTarget999).isOk == false

example :
    HasPrototypeProvenance constSpec42 zeroSeed genuineTarget42 ∧
    Term.PositiveSteps (.fix constSpec42 zeroSeed) genuineTarget42 ∧
    ProtoTyping constSpec42Env [] (.prototype constSpec42 genuineTarget42)
      (.prototype
        (.arrow .reusable .unrestricted .natural (.arrow .reusable .unrestricted .natural .natural))
        .natural) :=
  checkPrototypeWithProvenance_sound genuine_prototype_accepted

example (env : Env) (ctx : Ctx) :
    checkPrototypeWithProvenance 5 env ctx constSpec42 zeroSeed forgedTarget999 =
      .error (.forgedPrototypeProvenance constSpec42 zeroSeed forgedTarget999) :=
  forged_prototype_refused env ctx

-- `#tooth` probe: `PrototypeProvenance` rejects `forgedTarget999`.
theorem test_forged_prototype_provenance_false :
    PrototypeProvenance 5 constSpec42 zeroSeed forgedTarget999 = false := by
  decide +kernel

#tooth test_forged_prototype_provenance_false by mutation
  PrototypeProvenance := fun _ _ _ _ => true

-- ============================================================================
-- 5. Axiom Audit (`0 sorryAx`, `0 Classical.choice`)
-- ============================================================================

#print axioms FrozenMembrane.ofData_toData
#print axioms LiveMembrane.ofData_toData
#print axioms rehydrate_satisfies_law
#print axioms membraneCellContract
#print axioms Cert.ofData_toData
#print axioms SimplexState.ofData_toData
#print axioms simplex_step_respects_law
#print axioms simplexCellContract
#print axioms HybridProblem.ofData_toData
#print axioms HybridCert.ofData_toData
#print axioms hybridFlowpipeFormat
#print axioms checkPrototypeWithProvenance_sound
#print axioms genuine_prototype_accepted
#print axioms branching_prototype_accepted
#print axioms illTyped_seed_refused
#print axioms forged_prototype_refused

end Obend.Tests.InnerSeamWeldTest
