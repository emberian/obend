import Obend.Law.Contract
import Obend.Vault.Hyperedge
import Obend.Vault.Projection
import Obend.Vault.Carry
import Obend.Vault.SovereignEngine
import Obend.Logic.Obligation
import Obend.Judge.TranscriptPolicy
import Obend.Lower.PolicyToGrain
import Obend.Tactic.Tooth

/-!
# `tests/VaultConsensusTest.lean` — End-to-End Sovereign Vault & Consensus Verification Suite (`WS-V`)

Exercises all 5 concrete architectural deliverables for `WS-V`:
1. In-place `Contract` (`checkContractCert`, `.byLrat` wired to `Obend.Judge.Lrat.check`,
   kernel-checked `checkDeciderReceipt`, `checkContractCert_refuses_swapped_goal`).
2. In-place witness-bound `Hyperedge` (`ValidAt`, `ValidAt.witness_sound`, `no_toctou`).
3. In-place metadata-bound `Projection` (`cellBlind`, `projectedCommit`, `cellBlind_binds`,
   `tampered_metadata_opening_refused`).
4. Live World `K-CARRY` (`Obend.Vault.Carry`, `"world-carry@1"` in `defaultExternalFormats`,
   and the 5 keystone theorems).
5. Unified Sovereign Execution Engine (`Obend.Vault.SovereignEngine` and the 3 master
   compositional theorems).
-/

namespace Obend.Tests.VaultConsensusTest

open Obend.Core.Data (Data)
open Obend.Core.Term (Term)
open Obend.Law
open Obend.Vault
open Obend.Vault.Projection
open Obend.Judge
open Obend.Lower
open Obend.Logic

-- ============================================================================
-- 1. In-Place `Contract` Verification (`.byLrat`, `checkDeciderReceipt`, `checkContractCert`)
-- ============================================================================

def invA : Term := .lam (.boolean true)
def lawA : Term := law3 (Obend.Law.guard (.app invA (.bound 1)) "bad" okT)

def invB : Term := .lam (.boolean false)
def lawB : Term := law3 (Obend.Law.guard (.app invB (.bound 1)) "bad" okT)

def goalA : ContractGoal := .preserves lawA invA
def goalB : ContractGoal := .preserves lawB invB

def isValid : CertVerdict → Bool
  | .valid => true
  | .invalid _ => false

-- Tier 0: Syntactic guard
def certSyntacticA : ContractCert := .bySyntacticGuard lawA invA
#guard isValid (checkContractCert goalA certSyntacticA) == true
#guard isValid (checkContractCert goalB certSyntacticA) == false

-- Tier 1: In-place universal LawDial
def lawDialExpr1 : Obend.Spec.Law.LawExpr := .leC (.field "x") 10
def lawDialExpr2 : Obend.Spec.Law.LawExpr := .leC (.field "x") 20
def goalLawDial : ContractGoal := .preserves (lawExprToTerm lawDialExpr1) (lawExprToTerm lawDialExpr2)
def certLawDial : ContractCert := .byLawDial lawDialExpr1 lawDialExpr2 ["x"]

#guard isValid (checkContractCert goalLawDial certLawDial) == true
#guard isValid (checkContractCert goalA certLawDial) == false

-- Tier 2a: Kernel-checked `checkDeciderReceipt` (without unkeyed SHA-256 digest fallback)
def deciderReceiptA : ByteArray :=
  mkGoalBoundDeciderReceipt "contract_A_preserves" "decider@1" goalA
def certDeciderA : ContractCert :=
  .byLoweredDecider "contract_A_preserves" [] deciderReceiptA

#guard isValid (checkContractCert goalA certDeciderA) == true
#guard isValid (checkContractCert goalB certDeciderA) == false

-- Tier 2b: Goal-bound `.byLrat` wired to `Obend.Judge.Lrat.check`
def validLratCnfA : Obend.Judge.Lrat.Cnf :=
  mkGoalBoundLratCnf goalA ⟨1, [[1], [-1]]⟩
def validLratProof : List Obend.Judge.Lrat.Step :=
  [.add 4 [] [1, 2]]
def certLratA : ContractCert :=
  .byLrat validLratCnfA validLratProof

-- Positive pole: valid LRAT refutation for `goalA` returns `.valid`!
#guard isValid (checkContractCert goalA certLratA) == true
-- Negative pole 1: swapped goal `goalB` is refused!
#guard isValid (checkContractCert goalB certLratA) == false
-- Negative pole 2: empty LRAT proof is refused!
#guard isValid (checkContractCert goalA (.byLrat validLratCnfA [])) == false
-- Negative pole 3: broken LRAT hint is refused!
#guard isValid (checkContractCert goalA (.byLrat validLratCnfA [.add 4 [1] [1]])) == false

theorem test_empty_lrat_refused (cnf : Obend.Judge.Lrat.Cnf) :
    isValid (checkContractCert goalA (.byLrat cnf [])) = false := rfl

#tooth test_empty_lrat_refused by mutation
  checkContractCert := fun _ _ => .valid

theorem goalB_ne_goalA : goalB ≠ goalA := by
  intro h
  injection h with _ h_inv
  cases h_inv

example (h_valid : checkContractCert goalA certLratA = .valid) :
    checkContractCert goalB certLratA ≠ .valid :=
  checkContractCert_refuses_swapped_goal goalA goalB certLratA h_valid goalB_ne_goalA

-- ============================================================================
-- 2. In-Place Witness-Bound `Hyperedge` (`ValidAt` & `no_toctou`)
-- ============================================================================

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

-- Instantiate in-place `no_toctou` and `ValidAt.witness_sound`:
example (s₀ s : VaultStore) (turn : VaultTurn)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format)
    (h_cover : ∀ d ∈ turn.writeCells, ∃ p ∈ turn.readPins, p.cell = d.cell ∧ p.observed = some d.preState)
    (h_fp_s0 : Footprint.Holds s₀ turn.readPins)
    (h_fp_s : Footprint.Holds s turn.readPins) :
    (ValidAt s₀ turn contracts formats ↔ ValidAt s turn contracts formats) ∧
    (∀ c, applyTurn s turn c =
      if c ∈ turn.writeFootprint then applyTurn s₀ turn c else s c) :=
  no_toctou s₀ s turn contracts formats h_cover h_fp_s0 h_fp_s

-- ============================================================================
-- 3. In-Place Metadata-Bound `Projection` (`cellBlind` & `tampered_metadata_opening_refused`)
-- ============================================================================

def testHash : Obend.Digest.HashBytes.Hash :=
  fun bs => Obend.Digest.HashBytes.be 4 (bs.foldl (fun acc b => (acc * 257 + b.toNat + 1) % 65537) 1)

def cell1 : VaultCell :=
  { id := 10, required := [.read], salt := 111, content := 5000 }
def cell2 : VaultCell :=
  { id := 20, required := [.read, .write], salt := 222, content := 9000 }
def cell1TamperedId : VaultCell :=
  { cell1 with id := 99 }
def cell1TamperedCap : VaultCell :=
  { cell1 with required := [] }

#guard cellBlind testHash cell1 != cellBlind testHash cell1TamperedId
#guard cellBlind testHash cell1 != cellBlind testHash cell1TamperedCap
#guard projectedMerkleRoot testHash [.read] [cell1, cell2] ==
  Obend.Receipt.Merkle.mapRoot testHash (vaultCommits testHash [cell1, cell2])

example {H : Obend.Digest.HashBytes.Hash} (hb : Obend.Receipt.Merkle.Bounded H)
    (h_no_coll : ¬ Obend.Digest.HashBytes.Collision H)
    (v : List Obend.Vault.Projection.Auth) (cells : List VaultCell) (j : Nat) (c_tampered : VaultCell)
    (hj : j < cells.length) (hjs : j < 2 ^ 256)
    (hid_orig : (cells.getD j default).id < 2 ^ 256)
    (hsalt_orig : (cells.getD j default).salt < 2 ^ 256)
    (hid_tamp : c_tampered.id < 2 ^ 256)
    (hsalt_tamp : c_tampered.salt < 2 ^ 256)
    (h_tampered : c_tampered.id ≠ (cells.getD j default).id ∨
                  c_tampered.readCap ≠ (cells.getD j default).readCap) :
    verifyBlindedOpening H
      { mkBlindedOpening H v cells j with cell := projectCell H v c_tampered }
      (projectedMerkleRoot H v cells) = false :=
  tampered_metadata_opening_refused hb h_no_coll v cells j c_tampered
    hj hjs hid_orig hsalt_orig hid_tamp hsalt_tamp h_tampered

-- ============================================================================
-- 4. Live World `K-CARRY` (`"world-carry@1"`) & 5 Keystone Theorems
-- ============================================================================

-- Verify `"world-carry@1"` is registered in `Obend.Logic.defaultExternalFormats`:
#guard (findFormat defaultExternalFormats "world-carry@1").isSome == true
#guard checkTurnWitness defaultExternalFormats
  { formatName := "world-carry"
  , version := "1"
  , grade := 0
  , objBytes := "valid"
  , certBytes := "valid" } == true
#guard checkTurnWitness defaultExternalFormats
  { formatName := "world-carry"
  , version := "1"
  , grade := 0
  , objBytes := "valid"
  , certBytes := "bad" } == false

-- Verify `Obend.Vault.worldCarryFormat` and `executeWorldCarry`:
#guard (executeWorldCarry sampleValidLiveWorld sampleValidCarryPlan).isOk == true
#guard (executeWorldCarry sampleValidLiveWorld sampleBadCarryPlan).isOk == false
#guard checkTurnWitness [Obend.Vault.worldCarryFormat]
  { formatName := "world-carry"
  , version := "1"
  , grade := 0
  , objBytes := "valid"
  , certBytes := "valid" } == true
#guard checkTurnWitness [Obend.Vault.worldCarryFormat]
  { formatName := "world-carry"
  , version := "1"
  , grade := 0
  , objBytes := "valid"
  , certBytes := "bad" } == false

theorem test_silent_cell_drop_refused :
    (executeWorldCarry sampleValidLiveWorld sampleBadCarryPlan).isOk = false := rfl

#tooth test_silent_cell_drop_refused by mutation
  executeWorldCarry := fun W _ => .ok W

-- Instantiate the 5 `K-CARRY` Keystone Theorems:
#check @carry_no_silent_drop
#check @carry_conserves_total_book
#check @carry_preserves_forever_crowns
#check @carry_preserves_zoe_offer_safety
#check @carry_rehydrates_sturdyrefs

-- ============================================================================
-- 5. Unified Sovereign Execution Engine (`Obend.Vault.SovereignEngine`)
-- ============================================================================

def sampleIsarCert : Obend.Spec.Elaborate.ElaboratedIsarCert where
  contractName := "treasury_contract"
  targetType   := "Vault"
  conclusion   := .bool true
  steps        := [.byMethod .weave]
  scriptValid  := true
  judgeTags    := []
  claim        := .keeps "Vault" "treasury_contract"

def sampleStepGoal : ContractGoal :=
  .stepSound lawA invA lawA

def sampleStepCert : ContractCert :=
  .byLoweredDecider "treasury_step_sound" []
    (mkGoalBoundDeciderReceipt "treasury_step_sound" "decider@1" sampleStepGoal)

def sampleDeployedContract : DeployedGrainContract where
  contractId    := "contract.treasury.v1"
  isarCert      := sampleIsarCert
  law           := lawA
  invariant     := invA
  stepRel       := lawA
  preservesCert := certSyntacticA
  stepSoundCert := sampleStepCert
  oraclePolicy  := validTlsnQuery.policyDfa
  maxTokens     := 16
  grainProg     := compilePolicyToGrainProg validTlsnQuery.policyDfa 16

#guard sampleDeployedContract.wellFormedB == true

def sampleOracleEnvelope : ZkOracleFactEnvelope where
  contractId      := "contract.treasury.v1"
  tlsnQuery       := validTlsnQuery
  tlsnCert        := validTlsnCert
  turnWitness     := {
    formatName := "tlsn-transcript-policy"
    version    := "1"
    grade      := 16
    objBytes   := "valid"
    certBytes  := "valid"
  }
  extractedTokens := structuralBytesToStrings (renderRedactedSkeleton validTlsnQuery.segs (validTlsnQuery.spans.headD default))

#guard verifyZkOracleEnvelope sampleDeployedContract sampleOracleEnvelope == true

def sampleSovereignWorld : SovereignWorldState where
  height     := 10
  store      := fun _ => none
  vaultCells := [cell1, cell2]
  contracts  := []
  ledger     := sampleValidLiveWorld.ledger
  seats      := sampleValidLiveWorld.seats
  dragons    := {
    epoch         := 1
    hoardState    := { outcomes := 2, hoard := 100, supply := [100, 100] }
    balances      := [50, -20, 30]
    creditLimits  := [100, 100, 100]
    grossExposure := 300
  }
  assets     := [0]

-- Execute `deployContract` on `sampleSovereignWorld`:
#guard (stepSovereignEngine sampleSovereignWorld (.deployContract sampleDeployedContract)).isSome == true

-- Instantiate the 3 Master Compositional Theorems:
#check @sovereignEngine_step_conserves_all_assets
#check @sovereignEngine_enforces_zoe_and_mandates
#check @sovereignEngine_blinded_view_non_forgeable

-- Verify zero `sorryAx` and zero custom axioms on all keystone theorems:
#print axioms checkContractCert_refuses_swapped_goal
#print axioms no_toctou
#print axioms cellBlind_binds
#print axioms tampered_metadata_opening_refused
#print axioms carry_no_silent_drop
#print axioms carry_conserves_total_book
#print axioms carry_preserves_forever_crowns
#print axioms carry_preserves_zoe_offer_safety
#print axioms carry_rehydrates_sturdyrefs
#print axioms sovereignEngine_step_conserves_all_assets
#print axioms sovereignEngine_enforces_zoe_and_mandates
#print axioms sovereignEngine_blinded_view_non_forgeable

end Obend.Tests.VaultConsensusTest
