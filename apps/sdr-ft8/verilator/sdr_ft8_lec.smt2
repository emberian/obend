; Z3 QF_BV Logic Equivalence & Datapath Signoff Check (LEC) for Flagship App #3
; All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver
; Verifies:
;   1. Equivalence between .obend lowered spec (Obend.Apps.SdrFt8.sdrFt8SequentialRtlModule)
;      and the synthesized SystemVerilog RTL datapath (sdr_ft8_top.sv)
;   2. Exact Tayloe quadrature opposite-sideband image cancellation (i_mix_mv == q_mix_mv => image_cancel_mv == 0)
;   3. Folded symmetric FIR multiplier halving equivalence:
;        (comb_out + fir_tap_d1) * 256 == comb_out * 256 + fir_tap_d1 * 256
;        (x0 + x3) + 3 * (x1 + x2)     == x0 + 3*x1 + 3*x2 + x3
;   4. Vectoring CORDIC Stage-0 atan2 / hypot rotation equivalence (+/- 785 mrad)
;   5. Stateful always_ff delta-phase FT8 tone discriminator equivalence
(set-logic QF_BV)

(declare-const i_mix_mv (_ BitVec 64))
(declare-const q_mix_mv (_ BitVec 64))
(declare-const cordic_phase_mrad (_ BitVec 64))
(declare-const decim_strobe (_ BitVec 1))

(declare-const cic_int1 (_ BitVec 64))
(declare-const cic_int2 (_ BitVec 64))
(declare-const cic_int3 (_ BitVec 64))
(declare-const cic_comb_d1 (_ BitVec 64))
(declare-const fir_tap_d1 (_ BitVec 64))
(declare-const prev_phase_mrad (_ BitVec 64))

(declare-const bb_x0 (_ BitVec 64))
(declare-const bb_x1 (_ BitVec 64))
(declare-const bb_x2 (_ BitVec 64))
(declare-const bb_x3 (_ BitVec 64))

(declare-const cordic_cx0 (_ BitVec 64))
(declare-const cordic_cy0 (_ BitVec 64))
(declare-const cordic_cz0 (_ BitVec 64))

; --- Spec Model (Obend.Apps.SdrFt8.sdrFt8SequentialRtlModule + DSP.goldenCordic4Stages) ---
(define-fun spec_desired_usb_mv () (_ BitVec 64)
  (bvadd i_mix_mv q_mix_mv))

(define-fun spec_image_cancel_mv () (_ BitVec 64)
  (bvsub i_mix_mv q_mix_mv))

(define-fun spec_cic_int1_next () (_ BitVec 64)
  (bvadd cic_int1 (bvadd i_mix_mv q_mix_mv)))

(define-fun spec_cic_int2_next () (_ BitVec 64)
  (bvadd cic_int2 spec_cic_int1_next))

(define-fun spec_cic_int3_next () (_ BitVec 64)
  (bvadd cic_int3 spec_cic_int2_next))

(define-fun spec_comb_diff () (_ BitVec 64)
  (bvsub cic_int3 cic_comb_d1))

(define-fun spec_cic_comb_d1_next () (_ BitVec 64)
  (ite (= decim_strobe #b1) cic_int3 cic_comb_d1))

(define-fun spec_fir_tap_d1_next () (_ BitVec 64)
  (ite (= decim_strobe #b1) spec_comb_diff fir_tap_d1))

(define-fun spec_prev_phase_next () (_ BitVec 64)
  (ite (= decim_strobe #b1) cordic_phase_mrad prev_phase_mrad))

(define-fun spec_folded_fir_out () (_ BitVec 64)
  (bvmul (bvadd spec_comb_diff fir_tap_d1) (_ bv256 64)))

(define-fun spec_direct_fir_out () (_ BitVec 64)
  (bvadd (bvmul spec_comb_diff (_ bv256 64))
         (bvmul fir_tap_d1 (_ bv256 64))))

(define-fun spec_direct_bb_fir4 () (_ BitVec 64)
  (bvadd (bvadd bb_x0 (bvadd (bvshl bb_x1 (_ bv1 64)) bb_x1))
         (bvadd (bvadd (bvshl bb_x2 (_ bv1 64)) bb_x2) bb_x3)))

(define-fun spec_cordic_cx1 () (_ BitVec 64)
  (ite (bvsge cordic_cy0 (_ bv0 64))
       (bvadd cordic_cx0 cordic_cy0)
       (bvsub cordic_cx0 cordic_cy0)))

(define-fun spec_cordic_cy1 () (_ BitVec 64)
  (ite (bvsge cordic_cy0 (_ bv0 64))
       (bvsub cordic_cy0 cordic_cx0)
       (bvadd cordic_cy0 cordic_cx0)))

(define-fun spec_cordic_cz1 () (_ BitVec 64)
  (ite (bvsge cordic_cy0 (_ bv0 64))
       (bvadd cordic_cz0 (_ bv785 64))
       (bvsub cordic_cz0 (_ bv785 64))))

(define-fun spec_delta_phase_mrad () (_ BitVec 64)
  (bvsub cordic_phase_mrad prev_phase_mrad))

; --- Synthesized RTL Gate-Level Netlist Model ---
(define-fun rtl_desired_usb_mv () (_ BitVec 64)
  (bvadd i_mix_mv q_mix_mv))

(define-fun rtl_image_cancel_mv () (_ BitVec 64)
  (bvsub i_mix_mv q_mix_mv))

(define-fun rtl_cic_int1_next () (_ BitVec 64)
  (bvadd cic_int1 rtl_desired_usb_mv))

(define-fun rtl_cic_int2_next () (_ BitVec 64)
  (bvadd cic_int2 (bvadd cic_int1 rtl_desired_usb_mv)))

(define-fun rtl_cic_int3_next () (_ BitVec 64)
  (bvadd cic_int3 (bvadd cic_int2 (bvadd cic_int1 rtl_desired_usb_mv))))

(define-fun rtl_cic_comb_d1_next () (_ BitVec 64)
  (bvor (bvand (bvneg ((_ zero_extend 63) decim_strobe)) cic_int3)
        (bvand (bvnot (bvneg ((_ zero_extend 63) decim_strobe))) cic_comb_d1)))

(define-fun rtl_fir_tap_d1_next () (_ BitVec 64)
  (bvor (bvand (bvneg ((_ zero_extend 63) decim_strobe)) (bvsub cic_int3 cic_comb_d1))
        (bvand (bvnot (bvneg ((_ zero_extend 63) decim_strobe))) fir_tap_d1)))

(define-fun rtl_prev_phase_next () (_ BitVec 64)
  (bvor (bvand (bvneg ((_ zero_extend 63) decim_strobe)) cordic_phase_mrad)
        (bvand (bvnot (bvneg ((_ zero_extend 63) decim_strobe))) prev_phase_mrad)))

(define-fun rtl_folded_fir_out () (_ BitVec 64)
  (bvshl (bvadd (bvsub cic_int3 cic_comb_d1) fir_tap_d1) (_ bv8 64)))

(define-fun rtl_folded_bb_fir4 () (_ BitVec 64)
  (let ((s12 (bvadd bb_x1 bb_x2)))
    (bvadd (bvadd bb_x0 bb_x3)
           (bvadd (bvshl s12 (_ bv1 64)) s12))))

(define-fun rtl_cy0_nonneg_mask () (_ BitVec 64)
  (ite (= ((_ extract 63 63) cordic_cy0) #b0)
       (bvnot (_ bv0 64))
       (_ bv0 64)))

(define-fun rtl_cordic_cx1 () (_ BitVec 64)
  (bvor (bvand rtl_cy0_nonneg_mask (bvadd cordic_cx0 cordic_cy0))
        (bvand (bvnot rtl_cy0_nonneg_mask) (bvsub cordic_cx0 cordic_cy0))))

(define-fun rtl_cordic_cy1 () (_ BitVec 64)
  (bvor (bvand rtl_cy0_nonneg_mask (bvsub cordic_cy0 cordic_cx0))
        (bvand (bvnot rtl_cy0_nonneg_mask) (bvadd cordic_cy0 cordic_cx0))))

(define-fun rtl_cordic_cz1 () (_ BitVec 64)
  (bvor (bvand rtl_cy0_nonneg_mask (bvadd cordic_cz0 (_ bv785 64)))
        (bvand (bvnot rtl_cy0_nonneg_mask) (bvsub cordic_cz0 (_ bv785 64)))))

(define-fun rtl_delta_phase_mrad () (_ BitVec 64)
  (bvsub cordic_phase_mrad prev_phase_mrad))

; Assert miter negation: any divergence between .obend spec, direct FIR, CORDIC Stage-0, and RTL,
; or failure of Tayloe image cancellation under matched I/Q channels
(assert
  (or
    (distinct spec_desired_usb_mv rtl_desired_usb_mv)
    (distinct spec_image_cancel_mv rtl_image_cancel_mv)
    (distinct spec_cic_int1_next rtl_cic_int1_next)
    (distinct spec_cic_int2_next rtl_cic_int2_next)
    (distinct spec_cic_int3_next rtl_cic_int3_next)
    (distinct spec_cic_comb_d1_next rtl_cic_comb_d1_next)
    (distinct spec_fir_tap_d1_next rtl_fir_tap_d1_next)
    (distinct spec_prev_phase_next rtl_prev_phase_next)
    (distinct spec_folded_fir_out rtl_folded_fir_out)
    (distinct spec_direct_fir_out rtl_folded_fir_out)
    (distinct spec_direct_bb_fir4 rtl_folded_bb_fir4)
    (distinct spec_cordic_cx1 rtl_cordic_cx1)
    (distinct spec_cordic_cy1 rtl_cordic_cy1)
    (distinct spec_cordic_cz1 rtl_cordic_cz1)
    (distinct spec_delta_phase_mrad rtl_delta_phase_mrad)
    ; Property 1: Matched Tayloe I/Q channels (i_mix_mv == q_mix_mv) MUST cancel opposite sideband to 0
    (and (= i_mix_mv q_mix_mv)
         (distinct rtl_image_cancel_mv (_ bv0 64)))))

(check-sat)
