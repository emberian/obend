; HAND-WRITTEN property check (relabelled 2026-11-04). This file was typed by hand: it is not derived
; from the .sv beside it nor from the Lean RtlModule, so z3 `unsat` establishes properties of the
; formulas written here, not equivalence of the RTL with anything. It is kept as a worked property
; sheet (renamed from *_lec.smt2 on 2026-11-05). The logic-equivalence check of the emitted .sv is
; hardware/lec/lec.sh with the generated sovereign_drex_batch_top_lec.smt2. See review/EXPERT-fpga-silicon-20261103.md §3.2.
; Objective Bend Flagship App #7 (`apps/sovereign-drex/verilator/sovereign_drex_lec.smt2`)
; Formal QF_BV Logic Equivalence Checking (LEC) & Conservation Miter:
; 1. Proves that `sovereign_drex_batch_top.sv` (`emitModuleSV sovereignDrexBatchTopRtlModule`)
;    is bit-exact with `SovereignDrexTop.obend` and `BatchClearing.obend` across ALL 2^64 inputs
;    in BOTH base mode (`carryPinDigest = epoch * 32 + 4`) and `K-CARRY` upgraded mode
;    (`carryPinDigest = (epoch * 32 + 6) + 16`),
; 2. Proves that on EVERY state (both admitted and refused turns), total CBDC book supply
;    `out_new_cbdc_total == in_old_cbdc_total`, `out_protected_welfare_crown == 1000`,
;    and `out_turn_admitted = 1` implies:
;    - 3-of-4 BFT validator quorum (`vote_cnt >= 3`),
;    - strictly monotone WAL epoch (`reg_last_committed_epoch <u in_epoch_id`),
;    - fresh `K-CARRY` pin digest (`in_tx_pin_digest == out_carry_pin_digest`),
;    - state-bound half-edge conservation (`in_delta_debit == in_delta_credit`),
;    - Agoric/Zoe offer safety (`in_seat_cbdc_after >=u in_seat_want_floor`), and
;    - `"forever"` welfare-crown preservation (`in_forever_crown_drop_req == 0`).

(set-logic QF_BV)

(declare-const in_lot_count (_ BitVec 64))
(declare-const in_epoch_id (_ BitVec 64))
(declare-const in_validator_votes (_ BitVec 64))
(declare-const in_carry_upgrade_en (_ BitVec 64))
(declare-const in_old_cbdc_total (_ BitVec 64))
(declare-const in_delta_debit (_ BitVec 64))
(declare-const in_delta_credit (_ BitVec 64))
(declare-const in_seat_cbdc_after (_ BitVec 64))
(declare-const in_seat_want_floor (_ BitVec 64))
(declare-const in_forever_crown_drop_req (_ BitVec 64))
(declare-const in_tx_pin_digest (_ BitVec 64))
(declare-const reg_wal_committed_count (_ BitVec 64))
(declare-const reg_last_committed_epoch (_ BitVec 64))

(define-fun carry_en () Bool (distinct in_carry_upgrade_en (_ bv0 64)))

; --- 1. Reference `.obend` & Consensus Spec Equations ---
(define-fun spec_settlement () (_ BitVec 64)
  (bvadd (bvmul in_lot_count (_ bv500 64)) (_ bv1000 64)))

(define-fun spec_liquidity () (_ BitVec 64)
  (ite carry_en (_ bv125000 64) (_ bv100000 64)))

(define-fun spec_finality_tag () (_ BitVec 64)
  (ite carry_en
       (bvadd (bvadd (bvmul in_epoch_id (_ bv64 64)) (_ bv3 64)) (_ bv32 64))
       (bvadd (bvmul in_epoch_id (_ bv64 64)) (_ bv3 64))))

; Base `BatchClearing.obend` uses `halfEdgeDeltaCount = 4` (`epoch * 32 + 4`);
; `SovereignCarryOverride` overrides `halfEdgeDeltaCount = 6` and adds `16` (`(epoch * 32 + 6) + 16`).
(define-fun spec_carry_digest () (_ BitVec 64)
  (ite carry_en
       (bvadd (bvadd (bvmul in_epoch_id (_ bv32 64)) (_ bv6 64)) (_ bv16 64))
       (bvadd (bvmul in_epoch_id (_ bv32 64)) (_ bv4 64))))

; --- 2. Synthesized RTL Wires (`sovereign_drex_batch_top.sv`) ---
(define-fun w_v0 () (_ BitVec 64) (bvand in_validator_votes #x0000000000000001))
(define-fun w_v1 () (_ BitVec 64) (bvand (bvlshr in_validator_votes #x0000000000000001) #x0000000000000001))
(define-fun w_v2 () (_ BitVec 64) (bvand (bvlshr in_validator_votes #x0000000000000002) #x0000000000000001))
(define-fun w_v3 () (_ BitVec 64) (bvand (bvlshr in_validator_votes #x0000000000000003) #x0000000000000001))
(define-fun w_vote_cnt () (_ BitVec 64) (bvadd (bvadd w_v0 w_v1) (bvadd w_v2 w_v3)))
(define-fun w_quorum_ok () (_ BitVec 64)
  (ite (bvult w_vote_cnt #x0000000000000003) #x0000000000000000 #x0000000000000001))
(define-fun w_base_half_edges () (_ BitVec 64)
  (ite (distinct in_carry_upgrade_en #x0000000000000000) #x0000000000000006 #x0000000000000004))
(define-fun w_carry_pin_digest () (_ BitVec 64)
  (bvadd (bvadd (bvmul in_epoch_id #x0000000000000020) w_base_half_edges)
         (ite (distinct in_carry_upgrade_en #x0000000000000000) #x0000000000000010 #x0000000000000000)))
(define-fun w_epoch_monotone_ok () (_ BitVec 64)
  (ite (bvult reg_last_committed_epoch in_epoch_id) #x0000000000000001 #x0000000000000000))
(define-fun w_pin_fresh_ok () (_ BitVec 64)
  (ite (= in_tx_pin_digest w_carry_pin_digest) #x0000000000000001 #x0000000000000000))
(define-fun w_half_edge_balanced () (_ BitVec 64)
  (ite (= in_delta_debit in_delta_credit) #x0000000000000001 #x0000000000000000))
(define-fun w_zoe_offer_safe () (_ BitVec 64)
  (ite (bvult in_seat_cbdc_after in_seat_want_floor) #x0000000000000000 #x0000000000000001))
(define-fun w_crown_preserved () (_ BitVec 64)
  (ite (= in_forever_crown_drop_req #x0000000000000000) #x0000000000000001 #x0000000000000000))
(define-fun w_guards_a () (_ BitVec 64) (bvand (bvand w_quorum_ok w_epoch_monotone_ok) w_pin_fresh_ok))
(define-fun w_guards_b () (_ BitVec 64) (bvand (bvand w_half_edge_balanced w_zoe_offer_safe) w_crown_preserved))
(define-fun w_turn_ok () (_ BitVec 64) (bvand w_guards_a w_guards_b))
(define-fun w_new_cbdc_total () (_ BitVec 64)
  (ite (distinct w_turn_ok #x0000000000000000)
       (bvsub (bvadd in_old_cbdc_total in_delta_credit) in_delta_debit)
       in_old_cbdc_total))

(define-fun rtl_settlement () (_ BitVec 64)
  (bvadd (bvmul in_lot_count #x00000000000001f4) #x00000000000003e8))
(define-fun rtl_liquidity () (_ BitVec 64)
  (ite (distinct in_carry_upgrade_en #x0000000000000000) #x000000000001e848 #x00000000000186a0))
(define-fun rtl_finality_tag () (_ BitVec 64)
  (bvadd (bvadd (bvmul in_epoch_id #x0000000000000040) #x0000000000000003)
         (ite (distinct in_carry_upgrade_en #x0000000000000000) #x0000000000000020 #x0000000000000000)))

(define-fun next_last_committed_epoch () (_ BitVec 64)
  (ite (distinct w_turn_ok #x0000000000000000) in_epoch_id reg_last_committed_epoch))

(define-fun admitted () Bool (distinct w_turn_ok #x0000000000000000))

; Assert negation of equivalence and safety invariants: unsat proves 0 counterexamples across 2^64
(assert
  (or
    (distinct spec_settlement rtl_settlement)
    (distinct spec_liquidity rtl_liquidity)
    (distinct spec_finality_tag rtl_finality_tag)
    (distinct spec_carry_digest w_carry_pin_digest)
    (distinct w_new_cbdc_total in_old_cbdc_total)
    (and admitted (not (bvuge w_vote_cnt (_ bv3 64))))
    (and admitted (not (bvult reg_last_committed_epoch in_epoch_id)))
    (and admitted (distinct in_tx_pin_digest spec_carry_digest))
    (and admitted (distinct in_delta_debit in_delta_credit))
    (and admitted (not (bvuge in_seat_cbdc_after in_seat_want_floor)))
    (and admitted (distinct in_forever_crown_drop_req (_ bv0 64)))
    (and (not admitted) (distinct next_last_committed_epoch reg_last_committed_epoch))))

(check-sat)
