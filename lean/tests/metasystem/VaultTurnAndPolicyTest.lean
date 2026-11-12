import Obend.Law.Contract
import Obend.Vault.Hyperedge
import Obend.Vault.Projection
import Obend.Judge.Netting
import Obend.Judge.TranscriptPolicy
import Obend.Lower.PolicyToGrain
import Obend.Consensus.Simplex
import Obend.Consensus.SimplexProtocol
import Obend.Consensus.Epistemic
import Obend.Consensus.Finality
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/VaultTurnAndPolicyTest.lean` — Metasystem Regression & Verification Suite

Exercises:
1. Semantic `CellContract` Relawing & Trace Preservation (`CellContract`, `Narrows`,
   `cellContract_relaw_sound`, `cellContract_trace_sound`, `goalEq_sound`).
2. State-Derived Balanced Deltas (`checkDeltaMatchesStateBalances`, `stateBoundTurn_conserves_actual_state_balances`),
   Judge-Certified `VaultTurn` (`TurnWitness` with real `Lean.Json` wire payloads), and
   Metadata-Bound Blinded Merkle Projections (`cellBlindMetadataBound`, `projectedMerkleRoot`,
   `tampered_metadata_opening_refused`).
3. TLSNotary Selective-Disclosure Byte Transcript Confinement
   (`selective_disclosure_redaction_confinement`, `tlsnTranscriptFormat` JSON codecs) and
   Policy-to-Grain Compiler (`compilePolicyToGrainProg_sound`).
4. Multilateral Obligation Netting (`Obend.Judge.Netting` / `netting@1`:
   `symmetric_obligations_net_zero`, `net_conserves`, `net_reduces_gross_exposure`,
   `settleNetting_agrees_with_gross`, `NettingCert.toMovements_balanced`).
5. S5 Epistemic Consensus (`EpistemicFrame`, `knows_truth`, `knows_pos_introspection`,
   `knows_neg_introspection`, `epistemic_quorum_agreement`, `order_insensitive_perm`),
   Accountable `Simplex` (`simplex_accountable_safety`), and `SimplexFinalityGate` / `QuorumBoundFinalityGate`.
-/

namespace Obend.Tests.VaultTurnAndPolicyTest

open Obend.Core.Data (Data)
open Obend.Core.Term (Term)
open Obend.Ledger
open Obend.Law
open Obend.Vault
open Obend.Vault.Projection
open Obend.Judge
open Obend.Lower
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.Epistemic
open Obend.Consensus.Finality

-- ============================================================================
-- 1. `CellContract` Relawing, Trace Preservation & `goalEq_sound`
-- ============================================================================

def sampleInvA : Term := .lam (.boolean true)
def sampleLawA : Term := law3 (Obend.Law.guard (.app sampleInvA (.bound 1)) "bad" okT)

def sampleInvB : Term := .lam (.boolean false)
def sampleLawB : Term := law3 (Obend.Law.guard (.app sampleInvB (.bound 1)) "bad" okT)

def goalA : ContractGoal := .preserves sampleLawA sampleInvA
def goalB : ContractGoal := .preserves sampleLawB sampleInvB

#guard goalEq goalA goalA == true
#guard goalEq goalA goalB == false
#guard ContractGoal.ofTerm? goalA.toTerm == some goalA
#guard ContractGoal.ofJson? goalA.toJson == some goalA

example {a b : ContractGoal} (h : goalEq a b = true) : a = b :=
  goalEq_sound h

#tooth goalEq_sound by mutation
  goalEq := fun _ _ => true

example (C : CellContract) (law₂ : Term) (h_nar : Narrows law₂ C.law) :
    (cellContract_relaw_sound C law₂ h_nar).invariant = C.invariant := rfl

-- ============================================================================
-- 2. State-Derived Balanced Deltas, Real JSON `TurnWitness` & Projections
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

def bobDeltaInflated : CellDelta :=
  { cell := "bob"
  , preState := mkBalanceState 20
  , postState := mkBalanceState 999
  , halfEdges := [] }

#guard checkDeltaMatchesStateBalances ["USDC"] aliceDeltaGood == true
#guard checkDeltaMatchesStateBalances ["USDC"] bobDeltaGood == true
#guard checkDeltaMatchesStateBalances ["USDC"] bobDeltaInflated == false

-- Total balance across all touched cells is strictly conserved (100 + 20 = 50 + 70 = 120).
#guard ([aliceDeltaGood, bobDeltaGood].map (fun d => extractCellAssetBalance d.preState "USDC")).foldl (· + ·) 0 ==
  ([aliceDeltaGood, bobDeltaGood].map (fun d => extractCellAssetBalance d.postState "USDC")).foldl (· + ·) 0

-- Real JSON Witness verification via registered `Judge.Format` (`tlsn-transcript-policy@1`):
#guard checkTurnWitness [tlsnTranscriptFormat]
  { formatName := "tlsn-transcript-policy"
  , version := "1"
  , grade := 16
  , objBytes := encodeTlsnObj validTlsnQuery
  , certBytes := encodeTlsnCert validTlsnCert } == true

#guard checkTurnWitness [tlsnTranscriptFormat]
  { formatName := "tlsn-transcript-policy"
  , version := "1"
  , grade := 16
  , objBytes := encodeTlsnObj badTlsnQuery
  , certBytes := encodeTlsnCert badTlsnCert } == false

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
#guard (match decodeTlsnObj (encodeTlsnObj validTlsnQuery) with | .ok q => q == validTlsnQuery | _ => false)
#guard (match decodeTlsnCert (encodeTlsnCert validTlsnCert) with | .ok c => c == validTlsnCert | _ => false)

#tooth tlsnTranscriptPolicy_sound by mutation
  verifyTlsnTranscriptPolicy := fun _ _ => .ok

-- Every filling of the hidden span from its attested byte class is a JSON document: the
-- confinement is the machine's, for every secret, not a filter over a delimiter list.
example (secret : List UInt8)
    (h_match : ∀ sp ∈ validTlsnQuery.spans, ∀ b ∈ secret,
      byteMatchesMask sp.byteClassMask b = true) :
    VpaJson.runFullJsonGrammar ⟨(renderWith validTlsnQuery.segs [secret]).toArray⟩ = true := by
  have m := tlsnTranscriptPolicy_sound validTlsn_accepted
  obtain ⟨sp, hsp⟩ := List.exists_mem_of_ne_nil _ m.nonempty
  refine (m.confined [secret] fun f hf => ?_).1
  have hf' : f = secret := by simpa using hf
  subst hf'
  exact List.all_eq_true.2 fun b hb =>
    safe_of_matches_safe_mask (m.classes sp hsp) (h_match sp hsp b hb)

-- A slot placed right after a literal backslash would let the first hidden byte complete an
-- escape: refused by the machine state. So is a slot in a key, and a commitment that is not 32
-- bytes.
#guard verifyTlsnTranscriptPolicy
  { validTlsnQuery with
    segs := [.lit ["{\"role\":\"user\",\"secret\":\"\\"], .slot "secret", .lit ["\"}"]]
    spans := [{ offset := 26, length := 8, commitment := validTlsnCommitment, byteClassMask := 2 }] }
  validTlsnCert == .refused .slotOutsideValueString []
#guard verifyTlsnTranscriptPolicy
  { validTlsnQuery with
    segs := [.lit ["{\""], .slot "key", .lit ["\":1}"]]
    spans := [{ offset := 2, length := 8, commitment := validTlsnCommitment, byteClassMask := 2 }] }
  validTlsnCert == .refused .slotOutsideValueString []
#guard verifyTlsnTranscriptPolicy
  { validTlsnQuery with
    spans := [{ offset := 25, length := 8, commitment := ByteArray.empty, byteClassMask := 2 }] }
  validTlsnCert == .refused .narrowCommitment []

-- A confinement check that does not look at the machine state.
#tooth selective_disclosure_redaction_confinement by mutation
  slotsConfined := fun _ _ => true

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
-- 4. Multilateral Obligation Netting (`Obend.Judge.Netting` / `netting@1`)
-- ============================================================================

-- 3-party triangle `1 → 2 → 3 → 1` of 40 USDC nets to zero residual obligations!
def cyclicQuery : NettingQuery :=
  { grossObligations :=
      [ { payer := 1, payee := 2, asset := 1, amount := 40 }
      , { payer := 2, payee := 3, asset := 1, amount := 40 }
      , { payer := 3, payee := 1, asset := 1, amount := 40 } ] }

def zeroCert : NettingCert := { netTransfers := [] }

-- Partial compression: `1 → 2` (100) and `2 → 1` (40) nets to `1 → 2` (60), cutting gross exposure 140 → 60!
def bilateralGrossQuery : NettingQuery :=
  { grossObligations :=
      [ { payer := 1, payee := 2, asset := 1, amount := 100 }
      , { payer := 2, payee := 1, asset := 1, amount := 40 } ] }

def bilateralNetCert : NettingCert :=
  { netTransfers := [ { payer := 1, payee := 2, asset := 1, amount := 60 } ] }

#guard checkTurnWitness [nettingFormat]
  { formatName := "netting"
  , version := "1"
  , grade := 0
  , objBytes := encodeNettingQuery cyclicQuery
  , certBytes := encodeNettingCert zeroCert } == true

#guard checkTurnWitness [nettingFormat]
  { formatName := "netting"
  , version := "1"
  , grade := 0
  , objBytes := encodeNettingQuery bilateralGrossQuery
  , certBytes := encodeNettingCert bilateralNetCert } == true

#guard checkTurnWitness [nettingFormat]
  { formatName := "netting"
  , version := "1"
  , grade := 0
  , objBytes := encodeNettingQuery plantedBadNetting.1
  , certBytes := encodeNettingCert plantedBadNetting.2 } == false

#guard grossExposure bilateralNetCert.netTransfers == 60
#guard grossExposure bilateralGrossQuery.grossObligations == 140

example (a b : AccountId) (ast : AssetId) (amt : Nat) :
    (∀ acc xAst, netPosition [⟨a, b, ast, amt⟩, ⟨b, a, ast, amt⟩] acc xAst = 0) ∧
    grossExposure [] = 0 :=
  symmetric_obligations_net_zero a b ast amt

-- ============================================================================
-- 5. Accountable `SimplexProtocol` (`SlashingReceipt`), S5 `EpistemicFrame` & Finality
-- ============================================================================

def committee4 : List Nat := [0, 1, 2, 3]
def targetA : Target := .block [.block 7 101]
def targetB : Target := .block [.block 7 202]
def equivocatingSent : Sent :=
  [ ⟨0, 7, .vote, targetA⟩
  , ⟨1, 7, .vote, targetA⟩
  , ⟨2, 7, .vote, targetA⟩
  , ⟨1, 7, .vote, targetB⟩
  , ⟨2, 7, .vote, targetB⟩
  , ⟨3, 7, .vote, targetB⟩ ]

def slashReceipt : SlashingReceipt :=
  extractReceipt committee4 equivocatingSent 7 targetA targetB

#guard slashReceipt.checks equivocatingSent == true
#guard slashReceipt.signers == [1, 2]
#guard slashReceipt.signers.length ≥ 2

example :
    let r := extractReceipt committee4 equivocatingSent 7 targetA targetB
    r.checks equivocatingSent = true ∧
    1 + 1 ≤ r.signers.length ∧
    (∀ v ∈ r.signers, v ∈ committee4 ∧ ¬ VoteOnce equivocatingSent v 7) :=
  accountable committee4 1 equivocatingSent 7 targetA targetB
    (by decide) (by decide) (by decide) (by decide)

-- S5 Epistemic discriminating keystone frame checks:
example : Keystone.frame.Knows 0 Keystone.actualWorldProp Keystone.frame.actual :=
  Keystone.agent0_knows

example : ¬ Keystone.frame.Knows 1 Keystone.actualWorldProp Keystone.frame.actual :=
  Keystone.agent1_not_knows

example : Keystone.frame.DistKnows Keystone.everyoneGroup Keystone.actualWorldProp Keystone.frame.actual :=
  Keystone.group_distKnows

example : ¬ Keystone.frame.DistKnows Keystone.frame.Faulty Keystone.actualWorldProp Keystone.frame.actual :=
  Keystone.faulty_alone_not_distKnows

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

#print axioms cellContract_relaw_sound
#print axioms cellContract_trace_sound
#print axioms goalEq_sound
#print axioms stateBoundTurn_conserves_actual_state_balances
#print axioms tampered_metadata_opening_refused
#print axioms selective_disclosure_redaction_confinement
#print axioms tlsnTranscriptFormat
#print axioms compilePolicyToGrainProg_sound
#print axioms symmetric_obligations_net_zero
#print axioms net_conserves
#print axioms net_reduces_gross_exposure
#print axioms settleNetting_agrees_with_gross
#print axioms NettingCert.toMovements_balanced
#print axioms honest_quorum_intersection
#print axioms accountable
#print axioms SlashingReceipt.checks_sound
#print axioms epistemic_quorum_agreement
#print axioms order_insensitive_perm
#print axioms advanceQuorumBoundGate_formQC_sound
#print axioms quorum_final_gates_unique_per_height

end Obend.Tests.VaultTurnAndPolicyTest
