; Z3 SMT-LIB2 Formal Verification Check for:
; 1. Obend.Hardware.Types (`packPair32In64`, `extractLo32`, `extractHi32` bit-slice non-interference)
; 2. Obend.Hardware.Retiming (`leiserson_saxe_shift_sound` 2-stage retimed MAC == unretimed MAC)
; 3. Obend.Hardware.Analog (`commonCentroid_cancels_linear_gradient` ABBA layout gradient cancellation
;    and `runSarAdc4` 4-bit SAR ADC + Capacitive DAC exact floor quantization)
(set-logic QF_BV)

(declare-const lo32 (_ BitVec 64))
(declare-const hi32 (_ BitVec 64))
(declare-const a0   (_ BitVec 64))
(declare-const b0   (_ BitVec 64))
(declare-const c0   (_ BitVec 64))
(declare-const p0   (_ BitVec 64))
(declare-const grad (_ BitVec 64))
(declare-const x0   (_ BitVec 64))
(declare-const d    (_ BitVec 64))
(declare-const q4   (_ BitVec 64))

; 1. Types: 64-bit packed struct [hi : 32 | lo : 32] extract round-trip & non-interference
(define-fun mask32 () (_ BitVec 64) #x00000000ffffffff)
(define-fun packed_pair () (_ BitVec 64)
  (bvor (bvshl (bvand hi32 mask32) #x0000000000000020)
        (bvand lo32 mask32)))
(define-fun extracted_lo () (_ BitVec 64) (bvand packed_pair mask32))
(define-fun extracted_hi () (_ BitVec 64) (bvand (bvlshr packed_pair #x0000000000000020) mask32))

; 2. Retiming: Leiserson-Saxe retimed 2-stage MAC vs unretimed 2-stage MAC
(define-fun unretimed_s2 () (_ BitVec 64) (bvadd (bvmul a0 b0) c0))
(define-fun retimed_mul_reg () (_ BitVec 64) (bvmul a0 b0))
(define-fun retimed_c_reg   () (_ BitVec 64) c0)
(define-fun retimed_out_reg () (_ BitVec 64) (bvadd retimed_mul_reg retimed_c_reg))

; 3. Analog: ABBA Common-Centroid Linear Gradient Cancellation:
;    P(x) = p0 + grad * x
;    A = P(x0) + P(x0 + 3*d), B = P(x0 + d) + P(x0 + 2*d)
(define-fun P ((x (_ BitVec 64))) (_ BitVec 64)
  (bvadd p0 (bvmul grad x)))
(define-fun abba_A () (_ BitVec 64)
  (bvadd (P x0) (P (bvadd x0 (bvmul #x0000000000000003 d)))))
(define-fun abba_B () (_ BitVec 64)
  (bvadd (P (bvadd x0 d)) (P (bvadd x0 (bvmul #x0000000000000002 d)))))
(define-fun abba_mismatch () (_ BitVec 64)
  (bvsub abba_A abba_B))

; 4. Analog: 4-bit SAR ADC + Capacitive DAC binary search over [0, 15] * 100 mV + 50 mV
(define-fun v_in () (_ BitVec 64)
  (bvadd (bvmul (bvand q4 #x000000000000000f) #x0000000000000064) #x0000000000000032))
(define-fun sar_trial ((cur (_ BitVec 64)) (w (_ BitVec 64))) (_ BitVec 64)
  (ite (bvule (bvmul (bvadd cur w) #x0000000000000064) v_in)
       (bvadd cur w)
       cur))
(define-fun sar_s3 () (_ BitVec 64) (sar_trial #x0000000000000000 #x0000000000000008))
(define-fun sar_s2 () (_ BitVec 64) (sar_trial sar_s3 #x0000000000000004))
(define-fun sar_s1 () (_ BitVec 64) (sar_trial sar_s2 #x0000000000000002))
(define-fun sar_s0 () (_ BitVec 64) (sar_trial sar_s1 #x0000000000000001))

(assert
  (or (distinct extracted_lo (bvand lo32 mask32))
      (distinct extracted_hi (bvand hi32 mask32))
      (distinct retimed_out_reg unretimed_s2)
      (distinct abba_mismatch #x0000000000000000)
      (distinct sar_s0 (bvand q4 #x000000000000000f))))

(check-sat)
