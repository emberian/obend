; Z3 QF_BV Logic Equivalence & Datapath Signoff Check (LEC) for Flagship App #3
; All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver
; Verifies across all 5 pipeline stages:
;   1. Tayloe quadrature I/Q calibration & Hartley/Weaver combiner equivalence + exact opposite-sideband
;      image cancellation (matched I/Q + matched gain => image_cancel_mv == 0;
;      anti-phase LSB image q_mix = -i_mix => desired_usb_mv == 0)
;   2. 3-stage Hogenauer CIC integrator & R=64 decimation comb register-transfer equivalence
;   3. Folded symmetric FIR multiplier-halving equivalence:
;        (comb_out + fir_tap_d1) * 256 == comb_out * 256 + fir_tap_d1 * 256
;        (x0 + x3) + 3 * (x1 + x2)     == x0 + 3*x1 + 3*x2 + x3
;   4. Inductive 4-stage unrolled vectoring CORDIC (Stages 0..3: [785, 464, 245, 124] mrad, shifts 0..3)
;   5. Stateful always_ff 2*pi-wrapped delta-phase FT8 discriminator equivalence
(set-logic QF_BV)

; Stage 1 inputs: 16-bit signed Tayloe I/Q mixer samples & calibration trim
(declare-const i_mix_16 (_ BitVec 16))
(declare-const q_mix_16 (_ BitVec 16))
(declare-const cal_trim_sel (_ BitVec 1))

; Stage 2 & 3 inputs: CIC + Folded Symmetric FIR datapath state
(declare-const usb_in_mv (_ BitVec 64))
(declare-const decim_strobe (_ BitVec 1))
(declare-const cic_int1 (_ BitVec 64))
(declare-const cic_int2 (_ BitVec 64))
(declare-const cic_int3 (_ BitVec 64))
(declare-const cic_comb_d1 (_ BitVec 64))
(declare-const fir_tap_d1 (_ BitVec 64))
(declare-const bb_x0 (_ BitVec 64))
(declare-const bb_x1 (_ BitVec 64))
(declare-const bb_x2 (_ BitVec 64))
(declare-const bb_x3 (_ BitVec 64))

; Stage 4 inputs: Per-stage arbitrary 64-bit state inputs for 4-stage vectoring CORDIC
(declare-const s0_x (_ BitVec 64)) (declare-const s0_y (_ BitVec 64)) (declare-const s0_z (_ BitVec 64))
(declare-const s1_x (_ BitVec 64)) (declare-const s1_y (_ BitVec 64)) (declare-const s1_z (_ BitVec 64))
(declare-const s2_x (_ BitVec 64)) (declare-const s2_y (_ BitVec 64)) (declare-const s2_z (_ BitVec 64))
(declare-const s3_x (_ BitVec 64)) (declare-const s3_y (_ BitVec 64)) (declare-const s3_z (_ BitVec 64))

; Stage 5 inputs: Stateful always_ff delta-phase FT8 tone discriminator
(declare-const phase_ref_strobe (_ BitVec 1))
(declare-const symbol_strobe (_ BitVec 1))
(declare-const prev_phase_mrad (_ BitVec 64))
(declare-const cordic_cz4_in (_ BitVec 64))

; Hardware constant wire shifts (exact 64-bit 2's-complement wire slices matching sdr_ft8_top.sv)
(define-fun shl1_64  ((v (_ BitVec 64))) (_ BitVec 64) (concat ((_ extract 62 0) v) #b0))
(define-fun shl8_64  ((v (_ BitVec 64))) (_ BitVec 64) (concat ((_ extract 55 0) v) #x00))
(define-fun ashr1_64 ((v (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 1) ((_ extract 63 1) v)))
(define-fun ashr2_64 ((v (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 2) ((_ extract 63 2) v)))
(define-fun ashr3_64 ((v (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 3) ((_ extract 63 3) v)))

; CSD shift-add calibrated gain *500 (= 512 - 8 - 4) and uncalibrated *450 (= 512 - 64 + 2)
(define-fun mul500_32 ((v16 (_ BitVec 16))) (_ BitVec 32)
  (let ((v ((_ sign_extend 16) v16)))
    (bvsub (bvsub (concat ((_ extract 22 0) v) #b000000000)
                  (concat ((_ extract 28 0) v) #b000))
           (concat ((_ extract 29 0) v) #b00))))

(define-fun mul450_32 ((v16 (_ BitVec 16))) (_ BitVec 32)
  (let ((v ((_ sign_extend 16) v16)))
    (bvadd (bvsub (concat ((_ extract 22 0) v) #b000000000)
                  (concat ((_ extract 25 0) v) #b000000))
           (concat ((_ extract 30 0) v) #b0))))

; --- Spec Model (Obend.Apps.SdrFt8.sdrFt8SequentialRtlModule + DSP.goldenCordic4Stages) ---
(define-fun spec_i_cal () (_ BitVec 64)
  ((_ sign_extend 32) (mul500_32 i_mix_16)))
(define-fun spec_q_cal () (_ BitVec 64)
  (ite (= cal_trim_sel #b1)
       ((_ sign_extend 32) (mul500_32 q_mix_16))
       ((_ sign_extend 32) (mul450_32 q_mix_16))))

(define-fun spec_desired_usb_mv () (_ BitVec 64)
  (bvadd spec_i_cal spec_q_cal))

(define-fun spec_image_cancel_mv () (_ BitVec 64)
  (bvsub spec_i_cal spec_q_cal))

(define-fun spec_cic_int1_next () (_ BitVec 64)
  (bvadd cic_int1 usb_in_mv))

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

; Direct post-CIC symmetric FIR: comb_diff * 256 + fir_tap_d1 * 256
(define-fun spec_direct_fir_out () (_ BitVec 64)
  (bvadd (shl8_64 spec_comb_diff) (shl8_64 fir_tap_d1)))

; Direct 4-tap symmetric baseband FIR [1, 3, 3, 1]: x0 + 3*x1 + 3*x2 + x3
(define-fun spec_direct_bb_fir4 () (_ BitVec 64)
  (bvadd (bvadd bb_x0 (bvadd (shl1_64 bb_x1) bb_x1))
         (bvadd (bvadd (shl1_64 bb_x2) bb_x2) bb_x3)))

; Inductive 4-Stage Vectoring CORDIC Spec ([785, 464, 245, 124] mrad, shifts 0..3)
(define-fun spec_c1_x () (_ BitVec 64) (ite (bvsge s0_y (_ bv0 64)) (bvadd s0_x s0_y) (bvsub s0_x s0_y)))
(define-fun spec_c1_y () (_ BitVec 64) (ite (bvsge s0_y (_ bv0 64)) (bvsub s0_y s0_x) (bvadd s0_y s0_x)))
(define-fun spec_c1_z () (_ BitVec 64) (ite (bvsge s0_y (_ bv0 64)) (bvadd s0_z (_ bv785 64)) (bvsub s0_z (_ bv785 64))))

(define-fun spec_c2_x () (_ BitVec 64) (ite (bvsge s1_y (_ bv0 64)) (bvadd s1_x (bvashr s1_y (_ bv1 64))) (bvsub s1_x (bvashr s1_y (_ bv1 64)))))
(define-fun spec_c2_y () (_ BitVec 64) (ite (bvsge s1_y (_ bv0 64)) (bvsub s1_y (bvashr s1_x (_ bv1 64))) (bvadd s1_y (bvashr s1_x (_ bv1 64)))))
(define-fun spec_c2_z () (_ BitVec 64) (ite (bvsge s1_y (_ bv0 64)) (bvadd s1_z (_ bv464 64)) (bvsub s1_z (_ bv464 64))))

(define-fun spec_c3_x () (_ BitVec 64) (ite (bvsge s2_y (_ bv0 64)) (bvadd s2_x (bvashr s2_y (_ bv2 64))) (bvsub s2_x (bvashr s2_y (_ bv2 64)))))
(define-fun spec_c3_y () (_ BitVec 64) (ite (bvsge s2_y (_ bv0 64)) (bvsub s2_y (bvashr s2_x (_ bv2 64))) (bvadd s2_y (bvashr s2_x (_ bv2 64)))))
(define-fun spec_c3_z () (_ BitVec 64) (ite (bvsge s2_y (_ bv0 64)) (bvadd s2_z (_ bv245 64)) (bvsub s2_z (_ bv245 64))))

(define-fun spec_c4_x () (_ BitVec 64) (ite (bvsge s3_y (_ bv0 64)) (bvadd s3_x (bvashr s3_y (_ bv3 64))) (bvsub s3_x (bvashr s3_y (_ bv3 64)))))
(define-fun spec_c4_y () (_ BitVec 64) (ite (bvsge s3_y (_ bv0 64)) (bvsub s3_y (bvashr s3_x (_ bv3 64))) (bvadd s3_y (bvashr s3_x (_ bv3 64)))))
(define-fun spec_c4_z () (_ BitVec 64) (ite (bvsge s3_y (_ bv0 64)) (bvadd s3_z (_ bv124 64)) (bvsub s3_z (_ bv124 64))))

(define-fun spec_prev_phase_next () (_ BitVec 64)
  (ite (= (bvor phase_ref_strobe symbol_strobe) #b1) cordic_cz4_in prev_phase_mrad))

(define-fun spec_raw_diff_mrad () (_ BitVec 64)
  (bvsub cordic_cz4_in prev_phase_mrad))

(define-fun spec_wrapped_delta_1 () (_ BitVec 64)
  (ite (bvslt spec_raw_diff_mrad (_ bv0 64))
       (bvadd spec_raw_diff_mrad (_ bv6283 64))
       spec_raw_diff_mrad))

(define-fun spec_wrapped_delta_mrad () (_ BitVec 64)
  (ite (bvsge spec_wrapped_delta_1 (_ bv6283 64))
       (bvsub spec_wrapped_delta_1 (_ bv6283 64))
       spec_wrapped_delta_1))

; --- Synthesized RTL Datapath Model (sdr_ft8_top.sv) ---
(define-fun mux64 ((m (_ BitVec 64)) (t (_ BitVec 64)) (f (_ BitVec 64))) (_ BitVec 64)
  (bvor (bvand m t) (bvand (bvnot m) f)))

(define-fun bit_mask ((b (_ BitVec 1))) (_ BitVec 64)
  (bvneg ((_ zero_extend 63) b)))

(define-fun rtl_i_cal () (_ BitVec 64)
  ((_ sign_extend 32) (mul500_32 i_mix_16)))
(define-fun rtl_q_cal () (_ BitVec 64)
  (mux64 (bit_mask cal_trim_sel)
         ((_ sign_extend 32) (mul500_32 q_mix_16))
         ((_ sign_extend 32) (mul450_32 q_mix_16))))

(define-fun rtl_desired_usb_mv () (_ BitVec 64)
  (bvadd rtl_i_cal rtl_q_cal))

(define-fun rtl_image_cancel_mv () (_ BitVec 64)
  (bvsub rtl_i_cal rtl_q_cal))

(define-fun rtl_cic_int1_next () (_ BitVec 64)
  (bvadd cic_int1 usb_in_mv))

(define-fun rtl_cic_int2_next () (_ BitVec 64)
  (bvadd cic_int2 (bvadd cic_int1 usb_in_mv)))

(define-fun rtl_cic_int3_next () (_ BitVec 64)
  (bvadd cic_int3 (bvadd cic_int2 (bvadd cic_int1 usb_in_mv))))

(define-fun rtl_cic_comb_d1_next () (_ BitVec 64)
  (mux64 (bit_mask decim_strobe) cic_int3 cic_comb_d1))

(define-fun rtl_fir_tap_d1_next () (_ BitVec 64)
  (mux64 (bit_mask decim_strobe) (bvsub cic_int3 cic_comb_d1) fir_tap_d1))

(define-fun rtl_folded_fir_out () (_ BitVec 64)
  (shl8_64 (bvadd (bvsub cic_int3 cic_comb_d1) fir_tap_d1)))

(define-fun rtl_folded_bb_fir4 () (_ BitVec 64)
  (let ((s12 (bvadd bb_x1 bb_x2)))
    (bvadd (bvadd bb_x0 bb_x3)
           (bvadd (shl1_64 s12) s12))))

(define-fun rtl_c1_x () (_ BitVec 64) (ite (= ((_ extract 63 63) s0_y) #b0) (bvadd s0_x s0_y) (bvsub s0_x s0_y)))
(define-fun rtl_c1_y () (_ BitVec 64) (ite (= ((_ extract 63 63) s0_y) #b0) (bvsub s0_y s0_x) (bvadd s0_y s0_x)))
(define-fun rtl_c1_z () (_ BitVec 64) (ite (= ((_ extract 63 63) s0_y) #b0) (bvadd s0_z (_ bv785 64)) (bvsub s0_z (_ bv785 64))))

(define-fun rtl_c2_x () (_ BitVec 64) (ite (= ((_ extract 63 63) s1_y) #b0) (bvadd s1_x (ashr1_64 s1_y)) (bvsub s1_x (ashr1_64 s1_y))))
(define-fun rtl_c2_y () (_ BitVec 64) (ite (= ((_ extract 63 63) s1_y) #b0) (bvsub s1_y (ashr1_64 s1_x)) (bvadd s1_y (ashr1_64 s1_x))))
(define-fun rtl_c2_z () (_ BitVec 64) (ite (= ((_ extract 63 63) s1_y) #b0) (bvadd s1_z (_ bv464 64)) (bvsub s1_z (_ bv464 64))))

(define-fun rtl_c3_x () (_ BitVec 64) (ite (= ((_ extract 63 63) s2_y) #b0) (bvadd s2_x (ashr2_64 s2_y)) (bvsub s2_x (ashr2_64 s2_y))))
(define-fun rtl_c3_y () (_ BitVec 64) (ite (= ((_ extract 63 63) s2_y) #b0) (bvsub s2_y (ashr2_64 s2_x)) (bvadd s2_y (ashr2_64 s2_x))))
(define-fun rtl_c3_z () (_ BitVec 64) (ite (= ((_ extract 63 63) s2_y) #b0) (bvadd s2_z (_ bv245 64)) (bvsub s2_z (_ bv245 64))))

(define-fun rtl_c4_x () (_ BitVec 64) (ite (= ((_ extract 63 63) s3_y) #b0) (bvadd s3_x (ashr3_64 s3_y)) (bvsub s3_x (ashr3_64 s3_y))))
(define-fun rtl_c4_y () (_ BitVec 64) (ite (= ((_ extract 63 63) s3_y) #b0) (bvsub s3_y (ashr3_64 s3_x)) (bvadd s3_y (ashr3_64 s3_x))))
(define-fun rtl_c4_z () (_ BitVec 64) (ite (= ((_ extract 63 63) s3_y) #b0) (bvadd s3_z (_ bv124 64)) (bvsub s3_z (_ bv124 64))))

(define-fun rtl_prev_phase_next () (_ BitVec 64)
  (mux64 (bit_mask (bvor phase_ref_strobe symbol_strobe)) cordic_cz4_in prev_phase_mrad))

(define-fun rtl_raw_diff_mrad () (_ BitVec 64)
  (bvsub cordic_cz4_in prev_phase_mrad))

(define-fun rtl_wrapped_delta_1 () (_ BitVec 64)
  (ite (= ((_ extract 63 63) rtl_raw_diff_mrad) #b1)
       (bvadd rtl_raw_diff_mrad (_ bv6283 64))
       rtl_raw_diff_mrad))

(define-fun rtl_wrapped_delta_mrad () (_ BitVec 64)
  (ite (bvsge rtl_wrapped_delta_1 (_ bv6283 64))
       (bvsub rtl_wrapped_delta_1 (_ bv6283 64))
       rtl_wrapped_delta_1))

; Assert miter negation across ALL 5 pipeline stages:
(assert
  (or
    (distinct spec_desired_usb_mv rtl_desired_usb_mv)
    (distinct spec_image_cancel_mv rtl_image_cancel_mv)
    (distinct spec_cic_int1_next rtl_cic_int1_next)
    (distinct spec_cic_int2_next rtl_cic_int2_next)
    (distinct spec_cic_int3_next rtl_cic_int3_next)
    (distinct spec_cic_comb_d1_next rtl_cic_comb_d1_next)
    (distinct spec_fir_tap_d1_next rtl_fir_tap_d1_next)
    (distinct spec_direct_fir_out rtl_folded_fir_out)
    (distinct spec_direct_bb_fir4 rtl_folded_bb_fir4)
    (distinct spec_c1_x rtl_c1_x) (distinct spec_c1_y rtl_c1_y) (distinct spec_c1_z rtl_c1_z)
    (distinct spec_c2_x rtl_c2_x) (distinct spec_c2_y rtl_c2_y) (distinct spec_c2_z rtl_c2_z)
    (distinct spec_c3_x rtl_c3_x) (distinct spec_c3_y rtl_c3_y) (distinct spec_c3_z rtl_c3_z)
    (distinct spec_c4_x rtl_c4_x) (distinct spec_c4_y rtl_c4_y) (distinct spec_c4_z rtl_c4_z)
    (distinct spec_prev_phase_next rtl_prev_phase_next)
    (distinct spec_wrapped_delta_mrad rtl_wrapped_delta_mrad)
    ; Property 1: Matched 16-bit Tayloe I/Q channels at calibrated gain (cal_trim_sel = 1) cancel image_cancel_mv to 0
    (and (= i_mix_16 q_mix_16)
         (= cal_trim_sel #b1)
         (distinct rtl_image_cancel_mv (_ bv0 64)))
    ; Property 2: Anti-phase LSB image (q_mix_16 = -i_mix_16) at calibrated gain (cal_trim_sel = 1) cancels desired_usb_mv to 0
    (and (= q_mix_16 (bvneg i_mix_16))
         (distinct i_mix_16 #x8000)
         (= cal_trim_sel #b1)
         (distinct rtl_desired_usb_mv (_ bv0 64)))))

(check-sat)
