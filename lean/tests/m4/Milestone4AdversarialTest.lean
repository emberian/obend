import Obend.Consensus.Simplex
import Obend.Consensus.Finality
import Obend.Consensus.Epistemic
import Obend.Fold.Collapse
import Obend.Receipt.Merkle
import Obend.Vault.Hyperedge
import Obend.Digest.HashBytes

open Obend.Consensus.Simplex
open Obend.Consensus.Finality
open Obend.Consensus.Epistemic
open Obend.Fold.Collapse
open Obend.Receipt.Merkle (Opening Bounded opens)
open Obend.Vault (VaultStore)
open Obend.Digest.HashBytes (Hash Collision)

set_option autoImplicit false

/-! # Milestone 4 Adversarial Test Suite (10 Attack Defenses) -/

-- 1. Adversarial Attack 1: Consensus Split / Double Commit Attack Defeated
theorem adv_same_view_conflicting_qc_impossible {α : Type} {val1 val2 : α} (f : Nat) (committee : List Nat)
    (p1 p2 faulty : Nat → Bool)
    (h_size : committee.length = 3 * f + 1)
    (h_p1 : 2 * f + 1 ≤ (committee.filter p1).length)
    (h_p2 : 2 * f + 1 ≤ (committee.filter p2).length)
    (h_faulty : (committee.filter faulty).length ≤ f)
    (vote : Nat → Option α)
    (h_v1 : ∀ s ∈ committee, p1 s = true → faulty s = false → vote s = some val1)
    (h_v2 : ∀ s ∈ committee, p2 s = true → faulty s = false → vote s = some val2) :
    val1 = val2 := by
  exact qc_same_view_unique f committee p1 p2 faulty h_size h_p1 h_p2 h_faulty vote h_v1 h_v2

-- 2. Adversarial Attack 2: Double-Voting Equivocation Attack Ignored
theorem adv_double_voting_ignored (s : State) (number : View) (block : Block)
    (hv : (viewAt s number).voted = true) :
    castVote s number block = s := by
  exact castVote_already_voted s number block hv

-- 3. Adversarial Attack 3: Sub-Quorum Partition Sybil Attack Defeated
theorem adv_quorum_intersection_has_honest {α : Type} (l : List α) (f : Nat)
    (p q faulty : α → Bool)
    (h_size : l.length = 3 * f + 1)
    (h_p : 2 * f + 1 ≤ (l.filter p).length)
    (h_q : 2 * f + 1 ≤ (l.filter q).length)
    (h_faulty : (l.filter faulty).length ≤ f) :
    ∃ x ∈ l, p x = true ∧ q x = true ∧ faulty x = false := by
  exact honest_quorum_intersection l f p q faulty h_size h_p h_q h_faulty

-- 4. Adversarial Attack 4: View Timeout Backoff Evasion Attack Defeated
theorem adv_exponential_backoff_bounded (baseTimeout views cap : Nat) :
    viewTimeout baseTimeout views cap ≤ baseTimeout * 2 ^ cap := by
  exact exponential_backoff_timing baseTimeout views cap

-- 5. Adversarial Attack 5: Finality Ladder Downgrade / Rollback Attack Defeated
theorem adv_finality_downgrade_unreachable :
    ¬ FinalitySteps .quorum_final .speculative := by
  exact downgrade_unreachable

-- 6. Adversarial Attack 6: Direct Single-Step Finality Regression Defeated
theorem adv_downgrade_not_a_step :
    (¬ FinalityStep .quorum_final .speculative) ∧ (¬ FinalityStep .collapsed .attested) := by
  exact ⟨downgrade_not_a_step, collapsed_downgrade_not_a_step⟩

-- 7. Adversarial Attack 7: Collapsed State Tampering / Re-opening Attack Defeated
theorem adv_collapsed_state_terminal (t : FinalityTier) (hrun : FinalitySteps .collapsed t) :
    t = .collapsed := by
  exact collapsed_is_terminal t hrun

-- 8. Adversarial Attack 8: Solver Race Front-Running / Race Malleability Defeated
theorem adv_frontrunning_attack_defeated {Q Cert : Type} [instRace : VerifiableRace Q Cert]
    (q : Q) (w b : Cert)
    (hw_val : certValid q w = true)
    (hbetter : betterCert q w b = true) :
    selectWinner q [w, b] = some w := by
  exact frontrunning_resistant_pair hw_val hbetter

-- 9. Adversarial Attack 9: Byzantine Subset Knowledge Forgery Defeated
theorem adv_byzantine_forgery_of_invalid_refuted {Q Cert Ω Agent : Type}
    [instRace : VerifiableRace Q Cert] (F : EpistemicFrame Ω Agent)
    (q : Q) (c : Cert) (hinval : certValid q c = false) :
    ¬ F.DistKnows F.Honest (verifiedProp q c) F.actual := by
  exact EpistemicFrame.no_dist_knowledge_of_invalid F q c hinval

-- 10. Adversarial Attack 10: Collapsed Merkle Opening Forgery Defeated
theorem adv_collapsed_merkle_forgery_defeated {H : Hash} (hb : Bounded H)
    (schema : List String) (val : StoreValuation) (s : VaultStore) (o : Opening) (k : String)
    (h_open : opens H o (collapseRoot H schema val s) = true)
    (h_sz : o.size = schema.length) (h_idx : o.index < schema.length)
    (h_key : schema[o.index]'h_idx = k) (h_forged : o.value ≠ val s k) :
    Collision H := by
  have h_binds := (collapseRoot_binds_scoped hb schema val s o k h_open h_sz h_idx h_key).imp_right
    Obend.Digest.HashBytes.CollisionAmong.global
  rcases h_binds with he | hcol
  · contradiction
  · exact hcol

def main : IO Unit := do
  IO.println "[PASS] Milestone4AdversarialTest: All 10 adversarial attacks defeated mathematically."
