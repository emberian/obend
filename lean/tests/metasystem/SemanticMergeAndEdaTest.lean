import Obend.Tactic.Tooth
import Obend.Doc.Patch
import Obend.Doc.Merge
import Obend.Doc.Backlinks
import Obend.Receipt.Merkle
import Obend.Receipt.Negotiation
import Obend.Hardware.AgenticEDA

/-!
# `tests/metasystem/SemanticMergeAndEdaTest.lean` — WS-L End-to-End Verification Suite

Comprehensive verification of the WS-L deliverables:
1. **`Obend.Doc.Patch` & `Obend.Doc.Merge`** — 3-Way Keyed Section/Cell LCA Merge (`MergeCellResult`,
   `MergeConflict`, `mergeCell3`, `mergeKeyedCells3`, `mergeCell3_idempotent`,
   `mergeCell3_commutative`, `mergeCell3_disjoint_edits_succeed`, `Patch.supersedeCell`,
   `Patch.diffKeyedCells`) + `#tooth` mutation probes.
2. **`Obend.Doc.Backlinks`** — Transitive `#^block` Citation Impact Closure (`impactedBacklinksFuel`,
   `impactedBacklinksFuel_mono`, `impactedBacklinksFuel_fixedPoint_sound`).
3. **`Obend.Receipt.Merkle`** — Batch Merkle Multi-Proof Inclusion Verification (`MerkleBatchEntry`,
   `MerkleBatchProof`, `verifySingleMerkleLeaf`, `verifyMerkleBatchProof`,
   `verifyMerkleBatchProof_sound`).
4. **`Obend.Receipt.Negotiation`** — Pareto-Optimal / Minimum-Cost Cross-World Judge Negotiation
   (`NegotiatedJudgeFormat`, `selectMinCostCommonJudge`,
   `selectMinCostCommonJudge_supported_by_both`, `selectMinCostCommonJudge_minimal`).
5. **`Obend.Hardware.AgenticEDA`** — Multi-Agent Concurrent PCB/BOM Co-Design over 3-Way Merge &
   Merkle Receipts (`MultiAgentBoardMergeProposal`, `mergeAndJudgeAgenticEdaBoard`,
   `mergeAndJudgeAgenticEdaBoard_sound`, `conflictingAgentBoardEdits_refused`).
-/

namespace Obend.Tests.SemanticMergeAndEdaTest

open Obend.Core.Data (Data)
open Obend.Doc
open Obend.Receipt.Merkle
open Obend.Receipt.Negotiation
open Obend.Hardware.AgenticEDA

-- ============================================================================
-- 1. 3-Way Keyed Section/Cell LCA Merge (`Obend.Doc.Patch`, `Obend.Doc.Merge`)
-- ============================================================================

example {α : Type} [DecidableEq α] (base a : α) :
    mergeCell3 base a a = .merged a :=
  mergeCell3_idempotent base a

example {α : Type} [DecidableEq α] (base vL vR : α) :
    (∀ v, mergeCell3 base vL vR = .merged v ↔ mergeCell3 base vR vL = .merged v) ∧
    (mergeCell3 base vL vR = .conflict base vL vR ↔
      mergeCell3 base vR vL = .conflict base vR vL) :=
  mergeCell3_commutative base vL vR

example {α : Type} [DecidableEq α] (base1 base2 vL1 vR2 : α) :
    mergeCell3 base1 vL1 base1 = .merged vL1 ∧
    mergeCell3 base2 base2 vR2 = .merged vR2 :=
  mergeCell3_disjoint_edits_succeed base1 base2 vL1 vR2

-- Concrete 3-way keyed cell document merge checks:
def sampleBaseDoc : List (String × Data) :=
  [ ("cell_power", .natural 3300)
  , ("cell_rf", .natural 1350)
  , ("cell_shared", .label "v1") ]

def sampleLeftBranch : List (String × Data) :=
  [ ("cell_power", .natural 2950) -- modified only by Left
  , ("cell_rf", .natural 1350)    -- unchanged
  , ("cell_shared", .label "v2")  -- modified identically by both Left and Right
  , ("cell_new_left", .boolean true) ]

def sampleRightBranch : List (String × Data) :=
  [ ("cell_power", .natural 3300) -- unchanged
  , ("cell_rf", .natural 1280)    -- modified only by Right
  , ("cell_shared", .label "v2")  -- modified identically by both Left and Right
  , ("cell_new_right", .boolean false) ]

def sampleConflictRightBranch : List (String × Data) :=
  [ ("cell_power", .natural 3100) -- conflicts with Left's 2950 vs Base's 3300
  , ("cell_rf", .natural 1280)
  , ("cell_shared", .label "v2") ]

-- Disjoint + idempotent convergent edits merge with 0 conflicts:
#guard (mergeKeyedCells3 sampleBaseDoc sampleLeftBranch sampleRightBranch).conflicts == []
#guard (mergeKeyedCells3 sampleBaseDoc sampleLeftBranch sampleRightBranch).mergedCells ==
  [ ("cell_power", .natural 2950)
  , ("cell_rf", .natural 1280)
  , ("cell_shared", .label "v2")
  , ("cell_new_left", .boolean true)
  , ("cell_new_right", .boolean false) ]

-- Conflicting edits on `"cell_power"` localize the exact conflict while merging `"cell_rf"` and `"cell_shared"`:
#guard (mergeKeyedCells3 sampleBaseDoc sampleLeftBranch sampleConflictRightBranch).conflicts ==
  [ { key := "cell_power"
      baseVal := some (.natural 3300)
      leftVal := some (.natural 2950)
      rightVal := some (.natural 3100) } ]
#guard (mergeKeyedCells3 sampleBaseDoc sampleLeftBranch sampleConflictRightBranch).mergedCells ==
  [ ("cell_rf", .natural 1280)
  , ("cell_shared", .label "v2")
  , ("cell_new_left", .boolean true) ]

-- Edge case: empty document merge
#guard (mergeKeyedCells3 [] [] []).mergedCells == []
#guard (mergeKeyedCells3 [] [] []).conflicts == []

-- Edge case: key deletion in one branch while unchanged in the other branch merges cleanly to deletion:
def sampleDeletedLeftBranch : List (String × Data) :=
  [ ("cell_rf", .natural 1350)
  , ("cell_shared", .label "v1") ]

#guard (mergeKeyedCells3 sampleBaseDoc sampleDeletedLeftBranch sampleBaseDoc).conflicts == []
#guard (mergeKeyedCells3 sampleBaseDoc sampleDeletedLeftBranch sampleBaseDoc).mergedCells ==
  [ ("cell_rf", .natural 1350)
  , ("cell_shared", .label "v1") ]

-- Edge case: key deletion in left branch (`none`) vs concurrent modification in right branch (`some v'`)
-- reports a localized delete/modify conflict:
#guard (mergeKeyedCells3 sampleBaseDoc sampleDeletedLeftBranch sampleConflictRightBranch).conflicts ==
  [ { key := "cell_power"
      baseVal := some (.natural 3300)
      leftVal := none
      rightVal := some (.natural 3100) } ]

-- `Patch.diffKeyedCells` and `Patch.supersedeCell` checks:
#guard Patch.diffKeyedCells sampleBaseDoc sampleBaseDoc == []
#guard Patch.diffKeyedCells sampleBaseDoc sampleLeftBranch ==
  [ ("cell_power", some (.natural 2950))
  , ("cell_shared", some (.label "v2"))
  , ("cell_new_left", some (.boolean true)) ]

example (base a : List (String × Data)) :
    (mergeKeyedCells3 base a a).conflicts = [] ∧
    ∀ k, ((mergeKeyedCells3 base a a).mergedCells).lookup k = a.lookup k :=
  mergeKeyedCells3_idempotent base a

example (base left right : List (String × Data)) :
    (∀ k, ((mergeKeyedCells3 base left right).mergedCells).lookup k =
          ((mergeKeyedCells3 base right left).mergedCells).lookup k) ∧
    (∀ k b l r,
      (⟨k, b, l, r⟩ : MergeConflict) ∈ (mergeKeyedCells3 base left right).conflicts ↔
      (⟨k, b, r, l⟩ : MergeConflict) ∈ (mergeKeyedCells3 base right left).conflicts) :=
  mergeKeyedCells3_commutative base left right

example (base left right : List (String × Data))
    (hDisj : ∀ k, left.lookup k = base.lookup k ∨
                  right.lookup k = base.lookup k ∨
                  left.lookup k = right.lookup k) :
    (mergeKeyedCells3 base left right).conflicts = [] :=
  mergeKeyedCells3_disjoint_edits_no_conflicts base left right hDisj

-- ============================================================================
-- 2. Transitive Citation Impact Closure (`Obend.Doc.Backlinks`)
-- ============================================================================

-- Citation graph:
-- `cell_b` cites `#^cell_a`
-- `cell_c` cites `#^cell_b`
-- `cell_d` cites `#^cell_c`
-- `cell_isolated` cites `#^cell_other`
def sampleCiteDeps : List (String × String) :=
  [ ("cell_b", "cell_a")
  , ("cell_c", "cell_b")
  , ("cell_d", "cell_c")
  , ("cell_isolated", "cell_other") ]

#guard impactedBacklinksFuel 0 sampleCiteDeps "cell_a" == ["cell_a"]
#guard impactedBacklinksFuel 1 sampleCiteDeps "cell_a" == ["cell_a", "cell_b"]
#guard impactedBacklinksFuel 2 sampleCiteDeps "cell_a" == ["cell_a", "cell_b", "cell_c"]
#guard impactedBacklinksFuel 3 sampleCiteDeps "cell_a" == ["cell_a", "cell_b", "cell_c", "cell_d"]
-- Fixed point reached at fuel = 3:
#guard impactedBacklinksFuel 4 sampleCiteDeps "cell_a" == impactedBacklinksFuel 3 sampleCiteDeps "cell_a"

-- Cyclic citation graph terminates cleanly at fixed point without duplicating cells:
def cyclicCiteDeps : List (String × String) :=
  [ ("cell_y", "cell_x")
  , ("cell_x", "cell_y") ]

#guard impactedBacklinksFuel 2 cyclicCiteDeps "cell_x" == ["cell_x", "cell_y"]
#guard impactedBacklinksFuel 3 cyclicCiteDeps "cell_x" == ["cell_x", "cell_y"]

-- Self-loop citation graph (`(k, k) ∈ deps`) terminates at `[k]` with no duplicates:
def selfLoopCiteDeps : List (String × String) :=
  [ ("cell_self", "cell_self") ]

#guard impactedBacklinksFuel 1 selfLoopCiteDeps "cell_self" == ["cell_self"]
#guard impactedBacklinksFuel 3 selfLoopCiteDeps "cell_self" == ["cell_self"]

-- Diamond citation topology (`cell_b1` and `cell_b2` both cite `cell_a`; `cell_d` cites both
-- `cell_b1` and `cell_b2`) emits `"cell_d"` exactly once (`Nodup`):
def diamondCiteDeps : List (String × String) :=
  [ ("cell_b1", "cell_a")
  , ("cell_b2", "cell_a")
  , ("cell_d", "cell_b1")
  , ("cell_d", "cell_b2") ]

#guard impactedBacklinksFuel 1 diamondCiteDeps "cell_a" == ["cell_a", "cell_b1", "cell_b2"]
#guard impactedBacklinksFuel 2 diamondCiteDeps "cell_a" == ["cell_a", "cell_b1", "cell_b2", "cell_d"]
#guard impactedBacklinksFuel 3 diamondCiteDeps "cell_a" == ["cell_a", "cell_b1", "cell_b2", "cell_d"]

example (fuel : Nat) (deps : List (String × String)) (k : String) :
    (impactedBacklinksFuel fuel deps k).Nodup :=
  impactedBacklinksFuel_nodup fuel deps k

example {m n : Nat} (hLe : m ≤ n) (deps : List (String × String)) (k : String) :
    ∀ x ∈ impactedBacklinksFuel m deps k, x ∈ impactedBacklinksFuel n deps k :=
  impactedBacklinksFuel_mono hLe deps k

example (fuel : Nat) (deps : List (String × String)) (k : String)
    (hFix : impactedBacklinksFuel (fuel + 1) deps k = impactedBacklinksFuel fuel deps k) :
    let S := impactedBacklinksFuel fuel deps k
    k ∈ S ∧
    (∀ citingCell citedBlock, (citingCell, citedBlock) ∈ deps → citedBlock ∈ S → citingCell ∈ S) ∧
    (∀ d, impactedBacklinksFuel (fuel + d) deps k = S) :=
  impactedBacklinksFuel_fixedPoint_sound fuel deps k hFix

example (fuel : Nat) (deps : List (String × String)) (k : String)
    (hFix : impactedBacklinksFuel (fuel + 1) deps k = impactedBacklinksFuel fuel deps k)
    (x : String) :
    x ∈ impactedBacklinksFuel fuel deps k ↔ CiteReachable deps k x :=
  impactedBacklinksFuel_fixedPoint_iff_reachable fuel deps k hFix x

-- ============================================================================
-- 3. Batch Merkle Multi-Proof Verification (`Obend.Receipt.Merkle`)
-- ============================================================================

/-- Lightweight polynomial rolling byte hash for fast kernel (`decide +kernel`) and `#guard`
Merkle tree evaluations. -/
@[expose] def fastMerkleTestHash : Obend.Digest.HashBytes.Hash :=
  fun bytes => [UInt8.ofNat ((bytes.foldl (fun acc b => (acc * 31 + b.toNat) % 251) 7) % 251)]

def sampleMerkleLeaves : List Nat :=
  leaves fastMerkleTestHash [100, 200, 300, 400]

def sampleMerkleRoot : Nat :=
  root fastMerkleTestHash sampleMerkleLeaves

def validBatchProof : MerkleBatchProof :=
  honestBatchProof fastMerkleTestHash sampleMerkleLeaves [0, 2, 3]

def duplicateIndexBatchProof : MerkleBatchProof :=
  { treeSize := 4
    entries :=
      [ honestBatchEntry fastMerkleTestHash sampleMerkleLeaves 1
      , honestBatchEntry fastMerkleTestHash sampleMerkleLeaves 1 ] }

def tamperedDigestBatchProof : MerkleBatchProof :=
  { treeSize := 4
    entries :=
      [ honestBatchEntry fastMerkleTestHash sampleMerkleLeaves 0
      , { (honestBatchEntry fastMerkleTestHash sampleMerkleLeaves 2) with
          leafDigest := 999999 } ] }

-- Valid multi-leaf batch proof verifies against `sampleMerkleRoot`:
#guard verifyMerkleBatchProof fastMerkleTestHash validBatchProof sampleMerkleRoot == true
theorem validBatchProof_verifies :
    verifyMerkleBatchProof fastMerkleTestHash validBatchProof sampleMerkleRoot = true := by
  decide +kernel

-- Duplicate leaf indices are rejected:
#guard verifyMerkleBatchProof fastMerkleTestHash duplicateIndexBatchProof sampleMerkleRoot == false
theorem duplicateIndexBatchProof_rejected :
    verifyMerkleBatchProof fastMerkleTestHash duplicateIndexBatchProof sampleMerkleRoot = false := by
  decide +kernel

-- Tampered leaf digest is rejected:
#guard verifyMerkleBatchProof fastMerkleTestHash tamperedDigestBatchProof sampleMerkleRoot == false
theorem tamperedDigestBatchProof_rejected :
    verifyMerkleBatchProof fastMerkleTestHash tamperedDigestBatchProof sampleMerkleRoot = false := by
  decide +kernel

-- Symbolic proof at the deployed cSHAKE256 hash (`Obend.Core.Digest.deployed`) for any 2-leaf tree:
theorem deployed_batch_two_leaves_verifies (v0 v1 : Nat) :
    let ls := leaves Obend.Core.Digest.deployed [v0, v1]
    let r := root Obend.Core.Digest.deployed ls
    let batch : MerkleBatchProof := honestBatchProof Obend.Core.Digest.deployed ls [0, 1]
    verifyMerkleBatchProof Obend.Core.Digest.deployed batch r = true := by
  intro ls r batch
  have hSmall : ∀ x ∈ ls, x < 2 ^ 256 := leaves_small deployed_bounded [v0, v1]
  have hLen : ls.length = 2 := by simp [ls, leaves_length]
  have hLenSmall : ls.length < 2 ^ 256 := by rw [hLen]; decide
  exact verifyMerkleBatchProof_honest deployed_bounded ls hSmall hLenSmall [0, 1]
    (by decide) (by intro i hi; rw [hLen]; simp at hi; omega)

example (H : Obend.Digest.HashBytes.Hash) (batch : MerkleBatchProof) (expectedRoot : Nat)
    (hBatch : verifyMerkleBatchProof H batch expectedRoot = true) :
    (batch.entries.map MerkleBatchEntry.leafIndex).Nodup ∧
    ∀ e ∈ batch.entries,
      verifySingleMerkleLeaf H batch.treeSize e expectedRoot = true ∧
      climb H batch.treeSize e.leafIndex e.leafDigest e.auditPath = some expectedRoot :=
  verifyMerkleBatchProof_sound H batch expectedRoot hBatch

theorem test_verifyMerkleBatchProof_sound_probe :
    ∀ (H : Obend.Digest.HashBytes.Hash) (batch : MerkleBatchProof) (expectedRoot : Nat),
      verifyMerkleBatchProof H batch expectedRoot = true →
      (batch.entries.map MerkleBatchEntry.leafIndex).Nodup ∧
      ∀ e ∈ batch.entries,
        verifySingleMerkleLeaf H batch.treeSize e expectedRoot = true ∧
        climb H batch.treeSize e.leafIndex e.leafDigest e.auditPath = some expectedRoot :=
  verifyMerkleBatchProof_sound

#tooth test_verifyMerkleBatchProof_sound_probe by mutation
  verifyMerkleBatchProof := fun _ _ _ => true

-- ============================================================================
-- 4. Pareto-Optimal / Minimum-Cost Judge Negotiation (`Obend.Receipt.Negotiation`)
-- ============================================================================

def jfFullReplay : NegotiatedJudgeFormat :=
  { format := "obend.full-replay", version := "1", base := .kernel, costWeight := 500 }

def jfMerkleCited : NegotiatedJudgeFormat :=
  { format := "obend.merkle-cited", version := "1", base := .compiled, costWeight := 45 }

def jfLutTable : NegotiatedJudgeFormat :=
  { format := "obend.lut-certificate", version := "1", base := .kernel, costWeight := 12 }

def jfProducerOnly : NegotiatedJudgeFormat :=
  { format := "obend.custom-zk", version := "1", base := .kernel, costWeight := 5 }

def sampleProducerFormats : List NegotiatedJudgeFormat :=
  [jfFullReplay, jfProducerOnly, jfMerkleCited, jfLutTable]

def sampleVerifierFormats : List NegotiatedJudgeFormat :=
  [jfFullReplay, jfMerkleCited, jfLutTable]

-- Selects `jfLutTable` (costWeight = 12), ignoring `jfProducerOnly` (costWeight = 5, not supported by verifier):
#guard selectMinCostCommonJudge sampleProducerFormats sampleVerifierFormats == some jfLutTable

-- Disjoint format sets return `none`:
#guard selectMinCostCommonJudge [jfProducerOnly] [jfFullReplay] == none

example {producerSupported verifierSupported : List NegotiatedJudgeFormat}
    {chosen : NegotiatedJudgeFormat}
    (h : selectMinCostCommonJudge producerSupported verifierSupported = some chosen) :
    chosen ∈ producerSupported ∧ chosen ∈ verifierSupported :=
  selectMinCostCommonJudge_supported_by_both h

example {producerSupported verifierSupported : List NegotiatedJudgeFormat}
    {chosen : NegotiatedJudgeFormat}
    (h : selectMinCostCommonJudge producerSupported verifierSupported = some chosen) :
    ∀ jf, jf ∈ producerSupported → jf ∈ verifierSupported →
      chosen.costWeight ≤ jf.costWeight :=
  selectMinCostCommonJudge_minimal h

example {producerSupported verifierSupported : List NegotiatedJudgeFormat}
    {jf : NegotiatedJudgeFormat}
    (hProd : jf ∈ producerSupported) (hVer : jf ∈ verifierSupported) :
    ∃ chosen,
      selectMinCostCommonJudge producerSupported verifierSupported = some chosen ∧
      chosen ∈ producerSupported ∧
      chosen ∈ verifierSupported ∧
      chosen.costWeight ≤ jf.costWeight :=
  selectMinCostCommonJudge_complete hProd hVer

theorem test_selectMinCostCommonJudge_minimal_probe :
    ∀ (producerSupported verifierSupported : List NegotiatedJudgeFormat)
      (chosen : NegotiatedJudgeFormat),
      selectMinCostCommonJudge producerSupported verifierSupported = some chosen →
      ∀ jf, jf ∈ producerSupported → jf ∈ verifierSupported →
        chosen.costWeight ≤ jf.costWeight :=
  fun _ _ _ h => selectMinCostCommonJudge_minimal h

#tooth test_selectMinCostCommonJudge_minimal_probe by mutation
  minCostJudgeFormat := fun l => l.head?

theorem test_selectMinCostCommonJudge_complete_probe :
    ∀ (producerSupported verifierSupported : List NegotiatedJudgeFormat)
      (jf : NegotiatedJudgeFormat),
      jf ∈ producerSupported → jf ∈ verifierSupported →
      ∃ chosen,
        selectMinCostCommonJudge producerSupported verifierSupported = some chosen ∧
        chosen ∈ producerSupported ∧
        chosen ∈ verifierSupported ∧
        chosen.costWeight ≤ jf.costWeight :=
  fun _ _ _ hP hV => selectMinCostCommonJudge_complete hP hV

#tooth test_selectMinCostCommonJudge_complete_probe by mutation
  selectMinCostCommonJudge := fun _ _ => none

-- ============================================================================
-- 5. Multi-Agent Concurrent PCB/BOM Co-Design (`Obend.Hardware.AgenticEDA`)
-- ============================================================================

-- Disjoint Power/Analog and RF/Layout agent edits merge cleanly into `goldenSecondSourcePart` and pass judge:
#guard edaBoardConflictFields goldenBaselinePart goldenPowerAgentBranch goldenRfLayoutAgentBranch == []
#guard mergeEdaPartFields3 goldenBaselinePart goldenPowerAgentBranch goldenRfLayoutAgentBranch ==
  goldenSecondSourcePart
#guard mergeAndJudgeAgenticEdaBoard goldenMultiAgentCoDesignProposal == .admitted

-- Commutativity of multi-agent board merge & judge:
example (prop : MultiAgentBoardMergeProposal) :
    mergeAndJudgeAgenticEdaBoard
      { prop with
        powerAgentBoard := prop.rfLayoutAgentBoard
        rfLayoutAgentBoard := prop.powerAgentBoard } =
    mergeAndJudgeAgenticEdaBoard prop :=
  mergeAndJudgeAgenticEdaBoard_commutative prop

-- Merkle batch receipt verification over merged EDA board scalar fields (`voh_min_mv`, `max_temp_mc`, `vswr_milli`, `cost_cents`):
#guard verifyMerkleBatchProof
  fastMerkleTestHash
  (buildEdaBoardBatchProof fastMerkleTestHash goldenSecondSourcePart [0, 8, 9, 11])
  (commitEdaBoardMerkleRoot fastMerkleTestHash goldenSecondSourcePart) == true

theorem deployed_goldenSecondSourceBoard_batch_verifies :
    verifyMerkleBatchProof Obend.Core.Digest.deployed
      (buildEdaBoardBatchProof Obend.Core.Digest.deployed goldenSecondSourcePart [0, 8, 9, 11])
      (commitEdaBoardMerkleRoot Obend.Core.Digest.deployed goldenSecondSourcePart) = true :=
  deployed_edaBoardBatchProof_verifies goldenSecondSourcePart [0, 8, 9, 11]
    (by decide) (by intro i hi; simp at hi; omega)

-- Conflicting agent edits on `costCents` are localized and deterministically refused:
#guard edaBoardConflictFields
  conflictingMultiAgentCoDesignProposal.baseBoard
  conflictingMultiAgentCoDesignProposal.powerAgentBoard
  conflictingMultiAgentCoDesignProposal.rfLayoutAgentBoard == ["cost_cents"]
#guard mergeAndJudgeAgenticEdaBoard conflictingMultiAgentCoDesignProposal ==
  .refusedByPhysics "concurrent-field-merge-conflict"

-- Disjoint agent edits where the RF/BOM agent exceeds the BOM budget (`costCents = 320 > 250`)
-- merge cleanly at the 3-way LCA layer but are refused by the `.obend` `"bom_budget"` smart contract:
def overbudgetMultiAgentProposal : MultiAgentBoardMergeProposal :=
  { goldenMultiAgentCoDesignProposal with
    rfLayoutAgentBoard := { goldenRfLayoutAgentBranch with costCents := 320 } }

#guard edaBoardConflictFields
  overbudgetMultiAgentProposal.baseBoard
  overbudgetMultiAgentProposal.powerAgentBoard
  overbudgetMultiAgentProposal.rfLayoutAgentBoard == []
#guard mergeAndJudgeAgenticEdaBoard overbudgetMultiAgentProposal ==
  .refusedBySmartContract "bom_budget" "bom_budget"

-- Soundness & conflict-refusal theorems:
example (prop : MultiAgentBoardMergeProposal)
    (hAdmit : mergeAndJudgeAgenticEdaBoard prop = .admitted) :
    let mergedBoard := mergeEdaPartFields3 prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard
    let baseData := Obend.Vault.stateOf edaStateKeys prop.baseBoard.toScalarFields
    let mergedData := Obend.Vault.stateOf edaStateKeys mergedBoard.toScalarFields
    edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard = [] ∧
    (∀ p ∈ prop.laws, p.2.denote prop.facts (some baseData) mergedData = true) ∧
    prop.citePin.pinnedBlockHash = prop.citePin.currentDatasheetHash ∧
    prop.downstreamReceiver.vihMinMv + prop.minNoiseMarginMv ≤ mergedBoard.toLogicFamilySpec.vohMinMv ∧
    mergedBoard.toLogicFamilySpec.volMaxMv + prop.minNoiseMarginMv ≤ prop.downstreamReceiver.vilMaxMv :=
  mergeAndJudgeAgenticEdaBoard_sound prop hAdmit

example (prop : MultiAgentBoardMergeProposal)
    (hConflict : edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard ≠ []) :
    mergeAndJudgeAgenticEdaBoard prop = .refusedByPhysics "concurrent-field-merge-conflict" ∧
    mergeAndJudgeAgenticEdaBoard prop ≠ .admitted :=
  conflictingAgentBoardEdits_refused prop hConflict

theorem test_conflictingAgentBoardEdits_refused_probe :
    ∀ (prop : MultiAgentBoardMergeProposal),
      edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard ≠ [] →
      mergeAndJudgeAgenticEdaBoard prop = .refusedByPhysics "concurrent-field-merge-conflict" ∧
      mergeAndJudgeAgenticEdaBoard prop ≠ .admitted :=
  conflictingAgentBoardEdits_refused

#tooth test_conflictingAgentBoardEdits_refused_probe by mutation
  mergeAndJudgeAgenticEdaBoard := fun _ => .admitted

end Obend.Tests.SemanticMergeAndEdaTest
