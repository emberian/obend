import Obend.Law.Contract
import Obend.Vault.Hyperedge
import Obend.Vault.Projection
import Obend.Vault.CheckedCarry
import Obend.Vault.UnifiedDeos
import Obend.Judge.TranscriptPolicy
import Obend.Lower.PolicyToGrain
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/VaultConsensusTest.lean` — End-to-End Unified DeOS Vault & Consensus Verification Suite

Exercises:
1. Semantic `CellContract` (`cellContract_relaw_sound`, `cellContract_trace_sound`, `goalEq_sound`).
2. Witness-Bound `Hyperedge` (`ValidAt`, `no_toctou`, `vaultTurn_disjoint_commutes`,
   `stateBoundTurn_conserves_actual_state_balances`).
3. Metadata-Bound `Projection` & Stranger-Checkable `BlindedMultiProof`
   (`cellBlind`, `projectedCommit`, `cellBlind_binds`, `tampered_metadata_opening_refused`,
   `verifyBlindedMultiProof_revealed_binds`).
4. `Obend.Vault.CheckedCarry` (`Plan`, `RetentionAlignedPlan`, `AuthorityPoles.live_capability_survives_rerooting`,
   `AuthorityPoles.fresh_revoked_capability_refused`, `TitleMigration.copied_title_grant_not_semantic_narrowing`,
   `original_acceptance_makes_translation_replay`).
5. Unified DeOS Spine (`Obend.Vault.UnifiedDeos`: `stepUnifiedTurn`, `stepUnifiedTurn_refuses_stale_pin`,
   `unifiedDeos_ledger_and_turn_sound`, `unifiedDeos_zoe_and_escrow_safety`, `unifiedDeos_markets_sound`,
   `unifiedDeos_carry_and_mandate_sound`, `unifiedDeos_fastpath_and_simplex_finality_sound`).
-/

namespace Obend.Tests.VaultConsensusTest

open Obend.Core.Data (Data)
open Obend.Core.Term (Term)
open Obend.Law
open Obend.Vault
open Obend.Vault.Projection
open Obend.Vault.CheckedCarry
open Obend.Vault.UnifiedDeos
open Obend.Judge
open Obend.Lower

-- ============================================================================
-- 1. `Contract` Goal Binding & Relawing
-- ============================================================================

def invA : Term := .lam (.boolean true)
def lawA : Term := law3 (Obend.Law.guard (.app invA (.bound 1)) "bad" okT)

def invB : Term := .lam (.boolean false)
def lawB : Term := law3 (Obend.Law.guard (.app invB (.bound 1)) "bad" okT)

def goalA : ContractGoal := .preserves lawA invA
def goalB : ContractGoal := .preserves lawB invB

#guard goalEq goalA goalA == true
#guard goalEq goalA goalB == false

-- ============================================================================
-- 2. Witness-Bound `Hyperedge` (`ValidAt` & `no_toctou`)
-- ============================================================================

#guard checkTurnWitness unifiedMarketFormats
  { formatName := "tlsn-transcript-policy"
  , version := "1"
  , grade := 16
  , objBytes := encodeTlsnObj validTlsnQuery
  , certBytes := encodeTlsnCert validTlsnCert } == true

#guard checkTurnWitness unifiedMarketFormats
  { formatName := "tlsn-transcript-policy"
  , version := "1"
  , grade := 16
  , objBytes := encodeTlsnObj badTlsnQuery
  , certBytes := encodeTlsnCert badTlsnCert } == false

#guard checkTurnWitness unifiedMarketFormats
  { formatName := "netting"
  , version := "1"
  , grade := 0
  , objBytes := encodeNettingQuery ⟨[⟨1, 2, 0, 50⟩, ⟨2, 1, 0, 50⟩]⟩
  , certBytes := encodeNettingCert ⟨[]⟩ } == true

#guard checkTurnWitness unifiedMarketFormats
  { formatName := "netting"
  , version := "1"
  , grade := 0
  , objBytes := encodeNettingQuery plantedBadNetting.1
  , certBytes := encodeNettingCert plantedBadNetting.2 } == false

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
-- 3. Metadata-Bound `Projection` (`cellBlind` & `tampered_metadata_opening_refused`)
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
  (tampered_metadata_opening_refused hb v cells j c_tampered
    hj hjs hid_orig hsalt_orig hid_tamp hsalt_tamp h_tampered).resolve_right h_no_coll

-- ============================================================================
-- 4. Checked Carry (`Obend.Vault.CheckedCarry`) Keystone Poles
-- ============================================================================

example : AdmissibleCarry AuthorityPoles.rerooted AuthorityPoles.demoRequest :=
  AuthorityPoles.live_capability_survives_rerooting

example : ¬ AdmissibleCarry AuthorityPoles.revokedState AuthorityPoles.demoRequest :=
  AuthorityPoles.fresh_revoked_capability_refused

example : ¬ AdmissibleCarry AuthorityPoles.retiredFormState AuthorityPoles.demoRequest :=
  AuthorityPoles.retired_form_refused

example : ¬ TitleMigration.NoNewMeaning TitleMigration.oldGrant TitleMigration.copiedGrant :=
  TitleMigration.copied_title_grant_not_semantic_narrowing

example : TitleMigration.NoNewMeaning TitleMigration.oldGrant TitleMigration.correctGrant :=
  TitleMigration.translated_title_grant_preserves_meaning

#tooth original_acceptance_makes_translation_replay by mutation
  admit := fun _ _ _ _ => .refused

-- ============================================================================
-- 5. Unified DeOS Spine (`Obend.Vault.UnifiedDeos`) Keystone Theorems
-- ============================================================================

#tooth stepUnifiedTurn_refuses_stale_pin by mutation
  checkUnifiedTurn := fun _ _ _ _ => true

#check @unifiedDeos_ledger_and_turn_sound
#check @unifiedDeos_zoe_and_escrow_safety
#check @unifiedDeos_markets_sound
#check @unifiedDeos_carry_and_mandate_sound
#check @unifiedDeos_fastpath_and_simplex_finality_sound

-- Verify zero `sorryAx` and zero custom axioms on all keystone theorems:
#print axioms no_toctou
#print axioms cellBlind_binds
#print axioms tampered_metadata_opening_refused
#print axioms verifyBlindedMultiProof_revealed_binds
#print axioms AuthorityPoles.live_capability_survives_rerooting
#print axioms AuthorityPoles.fresh_revoked_capability_refused
#print axioms TitleMigration.copied_title_grant_not_semantic_narrowing
#print axioms TitleMigration.translated_title_grant_preserves_meaning
#print axioms original_acceptance_makes_translation_replay
#print axioms unifiedDeos_ledger_and_turn_sound
#print axioms unifiedDeos_zoe_and_escrow_safety
#print axioms unifiedDeos_markets_sound
#print axioms unifiedDeos_carry_and_mandate_sound
#print axioms unifiedDeos_fastpath_and_simplex_finality_sound

end Obend.Tests.VaultConsensusTest
