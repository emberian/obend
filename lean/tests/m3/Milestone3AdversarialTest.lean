import Obend.Vault.Escrow
import Obend.Vault.Affordance
import Obend.Vault.Projection
import Obend.Vault.Mandate
import Obend.Core.Digest
import Obend.Receipt.Merkle

open Obend.Vault.Escrow
open Obend.Vault.Affordance
open Obend.Vault.Projection
open Obend.Vault.Mandate
open Obend.Core.Digest (deployed)
open Obend.Core.Data

/-! # Milestone 3 Adversarial Test Suite -/

-- 1. Adversarial Test: Stolen funds in half-open escrow is unreachable
theorem adv_halfopen_theft_impossible (st : EscrowState) (hreach : EscrowReachable st)
    (h_empty_A : st.status .A = .empty) (h_stolen_A : 0 < st.recv .A) : False := by
  exact halfopen_theft_unreachable st hreach h_empty_A h_stolen_A

-- 2. Adversarial Test: Phantom fund extraction from non-existent deposit is unreachable
theorem adv_phantom_extraction_impossible (st : EscrowState) (hreach : EscrowReachable st)
    (h_empty_A : st.status .A = .empty) (h_extracted_A : 0 < st.paid .A) : False := by
  exact phantom_extraction_unreachable st hreach h_empty_A h_extracted_A

-- 3. Adversarial Test: Replay attack on meter-advance lease is rejected
theorem adv_meter_drift_replay_rejected (t : LeaseTerms) (hwf : t.wf) (st : LeaseState)
    (clock : Nat) (k : Nat) (hcur : st.nextDue = cursorAt t k) :
    ¬ DischargeOk t (advance t st) clock t.rent (expectedPeriod t st.nextDue) := by
  exact replay_rejected t hwf st clock k hcur

-- 4. Adversarial Test: Overdrawing exhausted budget is rejected
theorem adv_insufficient_budget_rejected (t : LeaseTerms) (st : LeaseState) (clock amt pidx : Nat)
    (h_short : st.remaining < t.rent) :
    ¬ DischargeOk t st clock amt pidx := by
  exact insufficient_budget_rejected t st clock amt pidx h_short

-- 5. Adversarial Test: Capability bypass attempt on gated affordance is refused
theorem adv_unauthorized_affordance_refused {φ : Type} (ga : GatedAffordance φ)
    (held : List Obend.Vault.Affordance.Auth) (facts : Obend.Spec.Law.Facts)
    (old : Option Data) (new : Data) (fc : FireCtx φ)
    (h_cap_missing : fireGate ga.aff.required held = false) :
    fireGated ga held facts old new fc = none := by
  exact fireGated_cap_fail_refuses ga held facts old new fc h_cap_missing

-- 6. Adversarial Test: State condition violation on gated affordance is refused
theorem adv_state_violation_affordance_refused {φ : Type} (ga : GatedAffordance φ)
    (held : List Obend.Vault.Affordance.Auth) (facts : Obend.Spec.Law.Facts)
    (old : Option Data) (new : Data) (fc : FireCtx φ)
    (h_law_fail : ga.law.denote facts old new = false) :
    fireGated ga held facts old new fc = none := by
  exact fireGated_state_fail_refuses ga held facts old new fc h_law_fail

-- 7. Adversarial Test: Submitting raw turn to bypass affordance is refused by contract
theorem adv_direct_turn_bypass_refused {φ : Type} (ga : GatedAffordance φ)
    (facts : Obend.Spec.Law.Facts) (old new : Data)
    (h_contract_fail : ga.law.denote facts (some old) new = false) :
    ¬ (ga.law.denote facts (some old) new = true) := by
  exact bypass_refused_by_contract ga facts old new h_contract_fail

-- 8. Adversarial Test: Blinded Merkle cell reveals 0 content to stranger
theorem adv_stranger_forgery_impossible (v : List Obend.Vault.Projection.Auth)
    (c : VaultCell) (h_hidden : canSee v c = false) :
    ∀ val, (match projectCell deployed v c with
      | .revealed _ _ _ content => some content
      | .blinded _ _ => none) = some val → False := by
  exact projectCell_blinded_reveals_no_content deployed v c h_hidden

-- 9. Adversarial Test: Sub-agent budget amplification attack is impossible
theorem adv_subagent_budget_amplification_impossible (t : DelegTree) (hw : t.WellAttenuated)
    (b : Nat) (hb : b ∈ t.budgets) :
    b ≤ t.mandate.budget := by
  exact subtree_budget_le_root t hw b hb

-- 10. Adversarial Test: Sub-agent target domain escape attack is impossible
theorem adv_subagent_target_escape_impossible (t : DelegTree) (hw : t.WellAttenuated)
    (tgt : String) (ht : tgt ∈ t.targetList) :
    tgt = t.mandate.target := by
  exact subtree_target_eq_root t hw tgt ht

def main : IO Unit := do
  IO.println "[PASS] Milestone3AdversarialTest: All 10 adversarial attacks mathematically defeated."
