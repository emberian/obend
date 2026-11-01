import Obend.Vault.Escrow
import Obend.Vault.Affordance
import Obend.Vault.Projection
import Obend.Vault.Mandate

open Obend.Vault.Escrow
open Obend.Vault.Affordance
open Obend.Vault.Projection
open Obend.Vault.Mandate

-- Escrow & PrepaidLease metatheorems
#print axioms sealedescrow_no_theft
#print axioms no_phantom_extraction
#print axioms escrow_solvent
#print axioms halfopen_theft_unreachable
#print axioms phantom_extraction_unreachable
#print axioms budget_never_overdrawn
#print axioms drawn_eq_count_rent
#print axioms remaining_plus_drawn_conserved
#print axioms cursor_strict_mono
#print axioms advance_strictly_increases
#print axioms replay_rejected
#print axioms insufficient_budget_rejected
#print axioms escrow_settle_conserves_book
#print axioms lease_advance_conserves_book

-- Affordance & Constructive Repair metatheorems
#print axioms fireGate_iff_subset
#print axioms fireGate_refl
#print axioms fireGate_trans
#print axioms fireGated_iff
#print axioms fireGated_both_pass
#print axioms fireGated_cap_fail_refuses
#print axioms fireGated_state_fail_refuses
#print axioms fireGated_needs_both
#print axioms fireGated_carries_real_effect
#print axioms fireGated_binds_attested_root
#print axioms fireGated_reactive
#print axioms projectGatedFor_all_fireable
#print axioms projectGatedFor_monotone
#print axioms constructive_repair_sound
#print axioms bypass_refused_by_contract

-- Projection & Stranger Blinded Multiproof metatheorems
#print axioms fog_of_war_noninterference
#print axioms hiddenCell_absent
#print axioms cons_hidden_invisible
#print axioms hidden_change_invisible
#print axioms vision_monotone
#print axioms rerender_idempotent
#print axioms projectCell_commit_eq
#print axioms projectVault_mapRoot_eq
#print axioms verify_blinded_opening_complete
#print axioms stranger_verification_sound
#print axioms projectCell_blinded_reveals_no_content

-- Mandate & Delegation Tree metatheorems
#print axioms attenuates_refl
#print axioms attenuates_trans
#print axioms subDelegate_attenuates
#print axioms authorizedBy_attenuates
#print axioms children_no_oversubscribe
#print axioms subtree_authorized_by_root
#print axioms subtree_budget_le_root
#print axioms subtree_expires_le_root
#print axioms subtree_target_eq_root
#print axioms mandateNarrows_refl
#print axioms mandateNarrows_trans
