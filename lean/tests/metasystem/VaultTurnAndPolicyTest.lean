import Obend.Law.Contract
import Obend.Vault.Hyperedge
import Obend.Vault.Projection
import Obend.Vault.DragonsExchange
import Obend.Judge.TranscriptPolicy
import Obend.Lower.PolicyToGrain
import Obend.Consensus.Simplex
import Obend.Consensus.Epistemic
import Obend.Consensus.Finality
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/VaultTurnAndPolicyTest.lean` — Metasystem Regression & Verification Suite (`WS-F`)

Exercises all 5 concrete architectural deliverables for `WS-F`:
1. Goal-Bound `ContractCert` verification (`checkContractCertGoalBound`,
   `checkContractCertGoalBound_refuses_swapped_goal`, `classifyLawDialPreserves`).
2. State-Derived Balanced Deltas (`CellDelta.accountingConsistent`,
   `turn_conserves_total_state_balance`), Judge-Certified `VaultTurn` (`TurnWitness`,
   `ValidAtWithWitnesses`, `no_toctou_with_witnesses`), and Metadata-Bound Blinded
   Merkle Projections (`cellBlindMetadataBound`, `projectedMerkleRoot`,
   `tampered_metadata_opening_refused`).
3. TLSNotary Selective-Disclosure Byte Transcript Confinement
   (`selective_disclosure_redaction_confinement`, `tlsnTranscriptFormat`) and
   Policy-to-Grain Compiler (`compilePolicyToGrainProg_sound`).
4. Dragon's Exchange & Multilateral Credit-Ring Netting (`settleRing`,
   `settleRing_conserves_net_worth`, `settleRing_never_triggers_liquidation`,
   `stepDragonsExchangeEpoch_preserves_invariant`).
5. Accountable Safety (`SlashingReceipt`, `extractSlashingReceipt`,
   `simplex_accountable_safety`), Weighted Trust-Graph Sybil Seed-Cut Bound
   (`sybilSeedCutBound`, `epistemic_sybil_bounded_by_seed_cut`), and Quorum/Root-Bound
   Finality Promotion (`advanceQuorumBoundGate_formQC_sound`).
-/

namespace Obend.Tests.VaultTurnAndPolicyTest

open Obend.Core.Data (Data)
open Obend.Core.Term (Term)
open Obend.Law
open Obend.Vault
open Obend.Vault.Projection
open Obend.Judge
open Obend.Lower
open Obend.Consensus.Simplex
open Obend.Consensus.Epistemic
open Obend.Consensus.Finality

-- ============================================================================
-- 1. Goal-Bound `ContractCert` Verification & Soundness Bridge
-- ============================================================================

def sampleInvA : Term := .lam (.boolean true)
def sampleLawA : Term := law3 (Obend.Law.guard (.app sampleInvA (.bound 1)) "bad" okT)

def sampleInvB : Term := .lam (.boolean false)
def sampleLawB : Term := law3 (Obend.Law.guard (.app sampleInvB (.bound 1)) "bad" okT)

def goalA : ContractGoal := .preserves sampleLawA sampleInvA
def goalB : ContractGoal := .preserves sampleLawB sampleInvB

def validCertForA : ContractCert :=
  .bySyntacticGuard sampleLawA sampleInvA

def isCertValid : CertVerdict → Bool
  | .valid => true
  | .invalid _ => false

-- Positive pole: `validCertForA` is accepted for `goalA`.
#guard isCertValid (checkContractCertGoalBound goalA validCertForA) == true

-- Negative pole: `validCertForA` is strictly refused when checked against `goalB ≠ goalA`!
#guard isCertValid (checkContractCertGoalBound goalB validCertForA) == false

-- Roundtrip test for `ContractGoal.toTerm` / `ContractGoal.ofTerm?`:
#guard ContractGoal.ofTerm? goalA.toTerm == some goalA

theorem goalB_ne_goalA : goalB ≠ goalA := by
  intro h
  injection h with _ h_inv
  cases h_inv

-- Theorem instantiation: swapped goal is strictly refused.
example (h_valid : checkContractCertGoalBound goalA validCertForA = .valid) :
    checkContractCertGoalBound goalB validCertForA ≠ .valid :=
  checkContractCertGoalBound_refuses_swapped_goal goalA goalB validCertForA h_valid goalB_ne_goalA

-- Goal-bound decider receipt refuses forged digest or swapped goal.
def receiptBytesForA : ByteArray :=
  mkGoalBoundDeciderReceipt "sample_contract_A" "decider@1" goalA

def deciderCertForA : ContractCert :=
  .byLoweredDecider "sample_contract_A" [] receiptBytesForA

#guard isCertValid (checkContractCertGoalBound goalA deciderCertForA) == true
#guard isCertValid (checkContractCertGoalBound goalB deciderCertForA) == false

-- Attack 1: `.byLoweredLean` with a trivial `.boolean true` claim and `goalA.toTerm` spoofed in `pins.head?` is strictly refused!
def spoofedLoweredLeanCert : ContractCert :=
  .byLoweredLean
    ⟨.boolLit true, []⟩
    ⟨Obend.Lower.sourceDigest (.boolLit true), Obend.Lower.lowerProp (.boolLit true), [], []⟩
    [⟨.layer "spoof", goalA.toTerm⟩]

#guard isCertValid (checkContractCertGoalBound goalA spoofedLoweredLeanCert) == false

-- Attack 2: JSON receipt carrying a `"statement"` for `goalB` whose outer `"goal"` field was overwritten with `goalA` is strictly refused!
def forgedGoalOverwriteReceipt : ByteArray :=
  let stmtB : Obend.Logic.ClaimObj :=
    { comp := { top := { name := "test", metadata := .record [], fields := [] }, below := [], seed := [] }
    , layer := 0
    , claim := goalB.toTerm
    , arity := 0 }
  let j := Lean.Json.mkObj [
    ("schema", Lean.toJson "obend.receipt.v1"),
    ("claim", Lean.toJson "sample_contract_A"),
    ("verdict", Lean.toJson "ok"),
    ("format", Lean.toJson "rewrite@1"),
    ("goal", goalA.toJson),
    ("statement", Obend.Logic.statementJson stmtB)
  ]
  j.compress.toUTF8

#guard deciderReceiptEmbeddedGoal? forgedGoalOverwriteReceipt == none
#guard isCertValid (checkContractCertGoalBound goalA (.byLoweredDecider "sample_contract_A" [] forgedGoalOverwriteReceipt)) == false

-- Bounded counterexample sampling is distinguished from universal validity (including conjunctive laws).
def isUniversalVerdict : LawDialSearchVerdict → Bool
  | .universalValid => true
  | _ => false

def isBoundedSampledVerdict : LawDialSearchVerdict → Bool
  | .boundedSampled _ => true
  | _ => false

#guard isUniversalVerdict (classifyLawDialPreserves (.leC (.field "x") 10) (.leC (.field "x") 10) ["x"]) == true
#guard isBoundedSampledVerdict (classifyLawDialPreserves (.leC (.field "x") 10) (.leC (.field "x") 20) ["x"]) == false
#guard isUniversalVerdict (classifyLawDialPreserves (.leC (.field "x") 10) (.leC (.field "x") 20) ["x"]) == true
#guard isUniversalVerdict
  (classifyLawDialPreserves
    (.and (.leC (.field "x") 5) (.leC (.field "y") 5))
    (.and (.leC (.field "x") 10) (.leC (.field "y") 10))
    ["x", "y"]) == true

theorem test_untagged_lrat_cert_refused (cnf : Obend.Judge.Lrat.Cnf) :
    isCertValid (checkContractCertGoalBound goalA (.byLrat cnf [])) = false := rfl

#tooth test_untagged_lrat_cert_refused by mutation
  checkContractCertGoalBound := fun _ _ => .valid

-- ============================================================================
-- 2. State-Derived Balanced Deltas, Judge-Certified `VaultTurn`, & Metadata-Bound Projections
-- ============================================================================

def mkBalanceState (bal : Nat) : Data :=
  .record [("USDC", .natural bal)]

def aliceDeltaGood : CellDelta :=
  { cell := "alice"
  , preState := mkBalanceState 100
  , postState := mkBalanceState 50
  , halfEdges := [("USDC", -50)] }

def bobDeltaGood : CellDelta :=
  { cell := "bob"
  , preState := mkBalanceState 20
  , postState := mkBalanceState 70
  , halfEdges := [("USDC", 50)] }

-- Inflation bug caught: `postState` increases from 20 to 999 while `halfEdges := []`!
def bobDeltaInflated : CellDelta :=
  { cell := "bob"
  , preState := mkBalanceState 20
  , postState := mkBalanceState 999
  , halfEdges := [] }

#guard aliceDeltaGood.accountingConsistent "USDC" == true
#guard bobDeltaGood.accountingConsistent "USDC" == true
#guard bobDeltaInflated.accountingConsistent "USDC" == false

theorem test_inflated_delta_rejected :
    bobDeltaInflated.accountingConsistent "USDC" = false := rfl

#tooth test_inflated_delta_rejected by mutation
  CellDelta.accountingConsistent := fun _ _ => true

-- Total balance across all touched cells is strictly conserved (100 + 20 = 50 + 70 = 120).
#guard sumPreStateBalance [aliceDeltaGood, bobDeltaGood] "USDC" ==
  sumPostStateBalance [aliceDeltaGood, bobDeltaGood] "USDC"

-- Witness verification via registered `Judge.Format`:
#guard checkTurnWitness [tlsnTranscriptFormat]
  { formatName := "tlsn-transcript-policy"
  , version := "1"
  , grade := 16
  , objBytes := "valid"
  , certBytes := "valid" } == true

#guard checkTurnWitness [tlsnTranscriptFormat]
  { formatName := "tlsn-transcript-policy"
  , version := "1"
  , grade := 16
  , objBytes := "valid"
  , certBytes := "bad" } == false

-- Metadata-bound blinded Merkle projection:
def toyHash : Obend.Digest.HashBytes.Hash :=
  fun bs => Obend.Digest.HashBytes.be 4 (bs.foldl (fun acc b => (acc * 257 + b.toNat + 1) % 65537) 1)

def sampleVaultCell1 : VaultCell :=
  { id := 10, required := [.read], salt := 111, content := 5000 }

def sampleVaultCell2 : VaultCell :=
  { id := 20, required := [.read, .write], salt := 222, content := 9000 }

def tamperedIdCell1 : VaultCell :=
  { sampleVaultCell1 with id := 99 }

#guard cellBlindMetadataBound toyHash sampleVaultCell1 !=
  cellBlindMetadataBound toyHash tamperedIdCell1
#guard projectedMerkleRoot toyHash [.read] [sampleVaultCell1, sampleVaultCell2] ==
  Obend.Receipt.Merkle.mapRoot toyHash
    (vaultCommitsMetadataBound toyHash [sampleVaultCell1, sampleVaultCell2])

-- ============================================================================
-- 3. TLSNotary Selective-Disclosure Confinement & Policy-to-Grain Compiler
-- ============================================================================

def isTlsnOk : Judge.Verdict TlsnTranscriptRefusal → Bool
  | .ok => true
  | _ => false

#guard isTlsnOk (verifyTlsnTranscriptPolicy validTlsnQuery validTlsnCert) == true
#guard isTlsnOk (verifyTlsnTranscriptPolicy badTlsnQuery badTlsnCert) == false

theorem test_bad_tlsn_mask_rejected :
    isTlsnOk (verifyTlsnTranscriptPolicy badTlsnQuery badTlsnCert) = false := rfl

#tooth test_bad_tlsn_mask_rejected by mutation
  verifyTlsnTranscriptPolicy := fun _ _ => .ok

-- Selective-disclosure redaction confinement theorem instantiation:
def sampleSafeSpan : RedactedSpan :=
  { offset := 25, length := 3, merkleCommitment := 12345, byteClassMask := 2 }

example (secretBytes : List Nat)
    (h_len : secretBytes.length = sampleSafeSpan.length)
    (h_match : ∀ b ∈ secretBytes, byteMatchesMask sampleSafeSpan.byteClassMask b = true) :
    extractStructuralTokens
      (spliceSecretIntoSlots validTlsnQuery.segs secretBytes) =
    extractStructuralTokens
      (renderRedactedSkeleton validTlsnQuery.segs sampleSafeSpan) :=
  selective_disclosure_redaction_confinement
    validTlsnQuery.segs
    sampleSafeSpan
    secretBytes
    rfl
    h_len
    h_match

-- PolicyToGrain compiler soundness:
def samplePolicyDfa : TableDfa :=
  { start := 0
  , accepting := [2]
  , transitions := [((0, "HDR"), 1), ((1, "SLOT:api_key"), 2)]
  , stateDefaults := []
  , defaultSink := 99 }

def sampleTokensAccept : List String := ["HDR", "SLOT:api_key"]
def sampleTokensReject : List String := ["HDR", "INJECTED"]

#guard evalGrainProg (compilePolicyToGrainProg samplePolicyDfa 4) sampleTokensAccept ==
  some (dfaAccepts samplePolicyDfa sampleTokensAccept)
#guard evalGrainProg (compilePolicyToGrainProg samplePolicyDfa 4) sampleTokensReject ==
  some (dfaAccepts samplePolicyDfa sampleTokensReject)

example (tokens : List String) :
    evalGrainProg (compilePolicyToGrainProg samplePolicyDfa tokens.length) tokens =
      some (dfaAccepts samplePolicyDfa tokens) :=
  compilePolicyToGrainProg_sound samplePolicyDfa tokens.length tokens

-- ============================================================================
-- 4. Dragon's Exchange & Multilateral Credit-Ring Netting (`settleRing`)
-- ============================================================================

def sampleBalances : List Int := [100, 200, 150]
def sampleCreditLimits : List Int := [500, 500, 500]
def sampleRing : List Nat := [0, 1, 2]

#guard settleRing sampleBalances sampleCreditLimits 40 sampleRing == some sampleBalances
#guard settleRing sampleBalances sampleCreditLimits 40 [] == none
#guard settleRing sampleBalances sampleCreditLimits 40 [0, 0] == none
#guard (mkClosedRingLegs sampleRing 40).length == 3
#guard grossDebtAfterRing 155 sampleRing 40 == 155 - 3 * 40

theorem test_empty_ring_rejected :
    settleRing sampleBalances sampleCreditLimits 40 [] = none := rfl

#tooth test_empty_ring_rejected by mutation
  settleRing := fun bs _ _ _ => some bs

def sampleLeg : CreditLeg := { debtor := 0, creditor := 1, amount := 50 }
#guard CreditLeg.ofData? sampleLeg.toData == some sampleLeg

def initDragonsState : DragonsExchangeState :=
  { epoch := 0
  , hoardState := { outcomes := 2, hoard := 1000, supply := [1000, 1000] }
  , balances := [100, 200, 150]
  , creditLimits := [500, 500, 500]
  , grossExposure := 155 }

#guard DragonsExchangeState.ofData? initDragonsState.toData == some initDragonsState

-- ============================================================================
-- 5. Accountable `Simplex` (`SlashingReceipt`), Epistemic Seed-Cut & Finality
-- ============================================================================

def committee4 : List Nat := [0, 1, 2, 3]
def votedBlockA (v : Nat) : Bool := v == 0 || v == 1 || v == 2
def votedBlockB (v : Nat) : Bool := v == 1 || v == 2 || v == 3

def slashReceipt : SlashingReceipt :=
  extractSlashingReceipt 7 101 202 committee4 votedBlockA votedBlockB

#guard slashReceipt.equivocatingVoters == [1, 2]
#guard slashReceipt.equivocatingVoters.length ≥ 2
#guard SlashingReceipt.ofData? slashReceipt.toData == some slashReceipt

example :
    let r := extractSlashingReceipt 7 101 202 committee4 votedBlockA votedBlockB
    r.blockA ≠ r.blockB ∧
    1 + 1 ≤ r.equivocatingVoters.length ∧
    (∀ v ∈ r.equivocatingVoters, v ∈ committee4 ∧ votedBlockA v = true ∧ votedBlockB v = true) :=
  simplex_accountable_safety 7 101 202 1 committee4 votedBlockA votedBlockB
    (by decide) (by decide) (by decide) (by decide)

-- Epistemic Sybil seed-cut bound:
def sampleIsSybil (n : Nat) : Bool := decide (10 ≤ n)

def sampleTrustEdges : List TrustEdge :=
  [ { source := 1, target := 2, flow := 50, capacity := 50 }   -- honest -> honest
  , { source := 2, target := 10, flow := 12, capacity := 15 }  -- honest -> Sybil (seed cut!)
  , { source := 3, target := 11, flow := 8, capacity := 10 }   -- honest -> Sybil (seed cut!)
  , { source := 10, target := 12, flow := 999, capacity := 999 } ] -- Sybil -> Sybil (internal cloning!)

#guard sybilSeedCutBound sampleIsSybil sampleTrustEdges == 25
#guard sybilTotalInfluence sampleIsSybil sampleTrustEdges == 20
#guard sybilTotalInfluence sampleIsSybil sampleTrustEdges ≤
  sybilSeedCutBound sampleIsSybil sampleTrustEdges

-- Quorum-bound finality gate:
def sampleGate0 : QuorumBoundFinalityGate :=
  { turnId := 1
  , currentTier := .attested
  , faults := 1
  , stateRoot := 0xCAFE
  , attestSigners := [0]
  , qcSigners := []
  , qcDigest := none
  , merkleRoot := none }

#guard (advanceQuorumBoundGate sampleGate0 (.formQC 999 [0, 1, 2] 0xCAFE)).isSome == true
#guard advanceQuorumBoundGate sampleGate0 (.formQC 999 [] 0xCAFE) == none
#guard advanceQuorumBoundGate sampleGate0 (.formQC 999 [0, 1, 2] 0xDEAD) == none

-- ============================================================================
-- 6. Axiom Audit (`0 sorryAx`, `0 Classical.choice`)
-- ============================================================================

#print axioms checkContractCertGoalBound_refuses_swapped_goal
#print axioms ContractGoal.ofTerm?_toTerm
#print axioms turn_conserves_total_state_balance
#print axioms tampered_metadata_opening_refused
#print axioms selective_disclosure_redaction_confinement
#print axioms tlsnTranscriptFormat
#print axioms compilePolicyToGrainProg_sound
#print axioms settleRing_conserves_net_worth
#print axioms settleRing_never_triggers_liquidation
#print axioms stepDragonsExchangeEpoch_preserves_invariant
#print axioms CreditLeg.ofData?_toData
#print axioms DragonsExchangeState.ofData?_toData
#print axioms simplex_accountable_safety
#print axioms simplex_accountable_safety_nodup
#print axioms SlashingReceipt.ofData_toData
#print axioms epistemic_sybil_bounded_by_seed_cut
#print axioms sybilSeedCutBound_invariant_under_sybil_cloning
#print axioms advanceQuorumBoundGate_formQC_sound

end Obend.Tests.VaultTurnAndPolicyTest
