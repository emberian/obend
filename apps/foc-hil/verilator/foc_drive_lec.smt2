; HAND-WRITTEN property check (relabelled 2026-11-04). This file was typed by hand: it is not derived
; from the .sv beside it nor from the Lean RtlModule, so z3 `unsat` establishes properties of the
; formulas written here, not equivalence of the RTL with anything. It is kept as a worked property
; sheet; a logic-equivalence check of the emitted .sv needs Yosys write_smt2 against the Lean emitter
; (not done yet). See review/EXPERT-fpga-silicon-20261103.md §3.2.
; Z3 QF_BV Logic Equivalence & Safety Barrier Check (LEC) for Flagship App #2
; Closed-Loop 20 kHz FOC Motor Drive & 6-Level SiC FCML Inverter Controller
; Verifies:
;   1. Equivalence between .obend lowered spec (Obend.Apps.FocHil) and RTL datapath
;   2. 1-cycle 155 C over-temperature gate-kill safety barrier (fault_trip = 1, pwm_gate_en = 0)
;   3. Glitch-free mid-run ICAP DPR partial reconfiguration isolation hold
(set-logic QF_BV)

(declare-const id_err_ma (_ BitVec 64))
(declare-const iq_err_ma (_ BitVec 64))
(declare-const cap_err_mv (_ BitVec 64))
(declare-const winding_temp_c (_ BitVec 64))
(declare-const dpr_isolate_en (_ BitVec 1))
(declare-const dpr_high_bw_sel (_ BitVec 1))

(declare-const int_d (_ BitVec 64))
(declare-const int_q (_ BitVec 64))
(declare-const fcml_cap_err (_ BitVec 64))
(declare-const thermal_trip_latch (_ BitVec 1))
(declare-const skid_vq_hold (_ BitVec 64))
(declare-const skid_vd_hold (_ BitVec 64))

; --- Spec Model (Obend.Apps.FocHil.focHilSequentialRtlModule) ---
(define-fun spec_kp_gain () (_ BitVec 64)
  (ite (= dpr_high_bw_sel #b1) (_ bv480 64) (_ bv400 64)))

(define-fun spec_vq_active () (_ BitVec 64)
  (bvadd (bvmul iq_err_ma spec_kp_gain) int_q))

(define-fun spec_vd_active () (_ BitVec 64)
  (bvadd (bvmul id_err_ma (_ bv400 64)) int_d))

(define-fun spec_overtemp_now () (_ BitVec 1)
  (ite (bvult (_ bv154 64) winding_temp_c) #b1 #b0))

(define-fun spec_fault_trip () (_ BitVec 1)
  (bvor thermal_trip_latch spec_overtemp_now))

(define-fun spec_pwm_gate_en () (_ BitVec 1)
  (bvnot spec_fault_trip))

(define-fun spec_vq_cmd_mv () (_ BitVec 64)
  (ite (= spec_fault_trip #b1)
       (_ bv0 64)
       (ite (= dpr_isolate_en #b1) skid_vq_hold spec_vq_active)))

(define-fun spec_vd_cmd_mv () (_ BitVec 64)
  (ite (= spec_fault_trip #b1)
       (_ bv0 64)
       (ite (= dpr_isolate_en #b1) skid_vd_hold spec_vd_active)))

(define-fun spec_int_q_next () (_ BitVec 64)
  (ite (= dpr_isolate_en #b1) int_q (bvadd int_q (bvmul iq_err_ma (_ bv65 64)))))

(define-fun spec_cap_err_next () (_ BitVec 64)
  (ite (= dpr_isolate_en #b1) fcml_cap_err (bvmul cap_err_mv (_ bv800 64))))

; --- Synthesized RTL Gate-Level Netlist Model ---
(define-fun rtl_kp_gain () (_ BitVec 64)
  (bvor (bvand (bvneg ((_ zero_extend 63) dpr_high_bw_sel)) (_ bv480 64))
        (bvand (bvnot (bvneg ((_ zero_extend 63) dpr_high_bw_sel))) (_ bv400 64))))

(define-fun rtl_vq_active () (_ BitVec 64)
  (bvadd (bvmul iq_err_ma rtl_kp_gain) int_q))

(define-fun rtl_vd_active () (_ BitVec 64)
  (bvadd (bvmul id_err_ma (_ bv400 64)) int_d))

(define-fun rtl_overtemp_now () (_ BitVec 1)
  (ite (bvugt winding_temp_c (_ bv154 64)) #b1 #b0))

(define-fun rtl_fault_trip () (_ BitVec 1)
  (bvor thermal_trip_latch rtl_overtemp_now))

(define-fun rtl_pwm_gate_en () (_ BitVec 1)
  (ite (= rtl_fault_trip #b1) #b0 #b1))

(define-fun rtl_vq_dpr_mux () (_ BitVec 64)
  (bvor (bvand (bvneg ((_ zero_extend 63) dpr_isolate_en)) skid_vq_hold)
        (bvand (bvnot (bvneg ((_ zero_extend 63) dpr_isolate_en))) rtl_vq_active)))

(define-fun rtl_vq_cmd_mv () (_ BitVec 64)
  (bvand (bvnot (bvneg ((_ zero_extend 63) rtl_fault_trip))) rtl_vq_dpr_mux))

(define-fun rtl_vd_dpr_mux () (_ BitVec 64)
  (bvor (bvand (bvneg ((_ zero_extend 63) dpr_isolate_en)) skid_vd_hold)
        (bvand (bvnot (bvneg ((_ zero_extend 63) dpr_isolate_en))) rtl_vd_active)))

(define-fun rtl_vd_cmd_mv () (_ BitVec 64)
  (bvand (bvnot (bvneg ((_ zero_extend 63) rtl_fault_trip))) rtl_vd_dpr_mux))

(define-fun rtl_int_q_next () (_ BitVec 64)
  (bvor (bvand (bvneg ((_ zero_extend 63) dpr_isolate_en)) int_q)
        (bvand (bvnot (bvneg ((_ zero_extend 63) dpr_isolate_en)))
               (bvadd int_q (bvmul iq_err_ma (_ bv65 64))))))

(define-fun rtl_cap_err_next () (_ BitVec 64)
  (bvor (bvand (bvneg ((_ zero_extend 63) dpr_isolate_en)) fcml_cap_err)
        (bvand (bvnot (bvneg ((_ zero_extend 63) dpr_isolate_en)))
               (bvmul cap_err_mv (_ bv800 64)))))

; Assert miter negation: any divergence between .obend spec and RTL, or any violation
; of the 155 C 1-cycle gate-kill barrier (including during ICAP DPR isolation) or
; fault-free ICAP DPR isolation hold
(assert
  (or
    (distinct spec_vq_cmd_mv rtl_vq_cmd_mv)
    (distinct spec_vd_cmd_mv rtl_vd_cmd_mv)
    (distinct spec_int_q_next rtl_int_q_next)
    (distinct spec_cap_err_next rtl_cap_err_next)
    (distinct spec_fault_trip rtl_fault_trip)
    (distinct spec_pwm_gate_en rtl_pwm_gate_en)
    ; Safety Barrier 1: winding_temp_c >= 155 MUST unconditionally force fault_trip = 1,
    ; pwm_gate_en = 0, vq_cmd_mv = 0, and vd_cmd_mv = 0 (even when dpr_isolate_en = 1)
    (and (bvuge winding_temp_c (_ bv155 64))
         (or (= rtl_fault_trip #b0)
             (= rtl_pwm_gate_en #b1)
             (distinct rtl_vq_cmd_mv (_ bv0 64))
             (distinct rtl_vd_cmd_mv (_ bv0 64))))
    ; Safety Barrier 2: fault-free dpr_isolate_en = 1 MUST freeze int_q and hold skid_vq/skid_vd
    (and (= dpr_isolate_en #b1)
         (= rtl_fault_trip #b0)
         (or (distinct rtl_vq_cmd_mv skid_vq_hold)
             (distinct rtl_vd_cmd_mv skid_vd_hold)
             (distinct rtl_int_q_next int_q)))))

(check-sat)
