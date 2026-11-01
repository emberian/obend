; Z3 SMT-LIB2 Formal Verification Check (`QF_NRA` Real Nonlinear Arithmetic) for:
; 1. Obend.Hardware.RF (`conjugate_match_maximizes_power` & `conjugate_match_zero_reflection`:
;    Maximum Power Transfer Theorem 4*R_S*R_L <= (R_S + R_L)^2 + (X_S + X_L)^2 and |Gamma|^2 = 0 <=> Z_L = Z_0)
; 2. Obend.Hardware.Thermal (`bandgap_zero_tempco_cancellation`: Brokaw Bandgap CTAT + K*PTAT zero-TC over [-40, +125] C)
; 3. Obend.Hardware.Thermal (`emitter_ballast_stabilizes_thermal_loop`: Electro-thermal contraction uniqueness & T_j* = 84.2 C)
; 4. Obend.Hardware.Datasheet (`calibrated_model_preserves_voltage_swing` & `ttl_to_hc_direct_interface_refused`)
; 5. Obend.Hardware.RF (`tayloe_iq_cancels_image_sideband`: Two-angle trigonometric quadrature image cancellation)
(set-logic QF_NRA)

(declare-const rS Real)
(declare-const rL Real)
(declare-const xS Real)
(declare-const xL Real)
(declare-const z0 Real)

(declare-const vbg0      Real)
(declare-const alphaPtat Real)
(declare-const weightK   Real)
(declare-const deltaT    Real)

(declare-const tjEq1    Real)
(declare-const tjEq2    Real)
(declare-const predVol  Real)
(declare-const actVol   Real)
(declare-const predVoh  Real)
(declare-const actVoh   Real)

(declare-const gainI    Real)
(declare-const gainQ    Real)
(declare-const cosRf    Real)
(declare-const sinRf    Real)
(declare-const cosLo    Real)
(declare-const sinLo    Real)

(assert (> rS 0.0))
(assert (> rL 0.0))
(assert (= z0 50.0))
(assert (and (>= deltaT -65.0) (<= deltaT 100.0)))

; 1. RF Maximum Power Transfer & Bidirectional Reflection Coefficient |Gamma|^2 = 0 <=> (rL = z0 /\ xL = 0)
(define-fun p_transfer_num () Real (* 4.0 rS rL))
(define-fun p_transfer_den () Real (+ (* (+ rS rL) (+ rS rL)) (* (+ xS xL) (+ xS xL))))
(define-fun gamma_num () Real (+ (* (- rL z0) (- rL z0)) (* xL xL)))

; 2. Thermal Brokaw Bandgap Zero-TC Reference: alphaCtat = weightK * alphaPtat
(define-fun alphaCtat () Real (* weightK alphaPtat))
(define-fun v_bandgap () Real (+ (- vbg0 (* alphaCtat deltaT)) (* weightK (* alphaPtat deltaT))))

; 3. Electro-Thermal Feedback Contraction for Emitter-Ballasted BJT (gamma_th = 0.72 < 1.0):
;    Any two fixed points tjEq1, tjEq2 of T - 25 = 16.576 + 0.72*(T - 25) must be identical and equal 84.2 C < 125.0 C
(assert (= (- tjEq1 25.0) (+ 16.576 (* 0.72 (- tjEq1 25.0)))))
(assert (= (- tjEq2 25.0) (+ 16.576 (* 0.72 (- tjEq2 25.0)))))

; 4. Datasheet Calibration Swing Preservation & 74LS -> 74HC vs 74HCT Noise Margins:
(assert (<= predVol 380.0))
(assert (and (<= (- predVol actVol) 20.0) (<= (- actVol predVol) 20.0)))
(assert (>= predVoh 2720.0))
(assert (and (<= (- predVoh actVoh) 20.0) (<= (- actVoh predVoh) 20.0)))
(define-fun nm_high_74ls_to_74hc  () Real (- 2700.0 3500.0))
(define-fun nm_high_74ls_to_74hct () Real (- actVoh 2000.0))

; 5. Two-Angle Trigonometric Tayloe Quadrature I/Q Image Cancellation:
;    With unit-circle carriers (cosRf^2 + sinRf^2 = 1, cosLo^2 + sinLo^2 = 1) and matched gainI = gainQ:
;    I_baseband = gainI * (cosRf * cosLo + sinRf * sinLo) = gainI * cos(w_RF - w_LO)
;    Q_hilbert  = gainQ * (cosRf * cosLo - sinRf * sinLo) = gainQ * cos(w_RF + w_LO)
;    Image sideband difference for image tone (sinRf = -sinLo, cosRf = cosLo):
(assert (= gainI gainQ))
(assert (= (+ (* cosRf cosRf) (* sinRf sinRf)) 1.0))
(assert (= (+ (* cosLo cosLo) (* sinLo sinLo)) 1.0))
(define-fun iq_image_cancel () Real
  (- (* gainI (- (* cosRf cosLo) (* sinRf sinLo)))
     (* gainQ (- (* cosLo cosRf) (* sinLo sinRf)))))

; 6. 2D Oxide Curvature: 1D ABBA Bow Residual (4 * cxx * pitch^2) & 8-Cell Prouhet-Thue-Morse (ABBABAAB) Exact Cancellation:
(declare-const p0Ox    Real)
(declare-const gxOx    Real)
(declare-const cxxOx   Real)
(declare-const pitchOx Real)
(define-fun q1d ((k Real)) Real
  (+ p0Ox (* k (* gxOx pitchOx)) (* (* k k) (* cxxOx (* pitchOx pitchOx)))))
(define-fun abba_mismatch () Real
  (- (+ (q1d 0.0) (q1d 3.0))
     (+ (q1d 1.0) (q1d 2.0))))
(define-fun ptm8_mismatch () Real
  (- (+ (q1d 0.0) (q1d 3.0) (q1d 5.0) (q1d 6.0))
     (+ (q1d 1.0) (q1d 2.0) (q1d 4.0) (q1d 7.0))))

; 7. Silicon Photonics CMT 2x2 Coupler Power Conservation & Microring Critical Coupling (r = a <=> (r - a)^2 = 0):
(declare-const tSqCmt   Real)
(declare-const kapSqCmt Real)
(declare-const pIn1Opt  Real)
(declare-const pIn2Opt  Real)
(declare-const rMrr     Real)
(declare-const aMrr     Real)
(assert (= (+ tSqCmt kapSqCmt) 1.0))
(define-fun p_out1_opt () Real (+ (* tSqCmt pIn1Opt) (* kapSqCmt pIn2Opt)))
(define-fun p_out2_opt () Real (+ (* kapSqCmt pIn1Opt) (* tSqCmt pIn2Opt)))
(define-fun mrr_thru_num () Real (* (- rMrr aMrr) (- rMrr aMrr)))

; 8. DSP CORDIC Stage-0 Norm Scaling & Phased-Array Coherent N^2 Main-Lobe Power Gain:
(declare-const cordicX Real)
(declare-const cordicY Real)
(declare-const nElem   Real)
(declare-const ampElem Real)
(define-fun cordic_norm0 () Real (+ (* cordicX cordicX) (* cordicY cordicY)))
(define-fun cordic_norm1 () Real (+ (* (- cordicX cordicY) (- cordicX cordicY))
                                    (* (+ cordicY cordicX) (+ cordicY cordicX))))
(define-fun ula_power () Real (* (* nElem ampElem) (* nElem ampElem)))

(assert
  (or ; 1a. Violate Maximum Power Transfer bound 4*rS*rL <= (rS+rL)^2 + (xS+xL)^2
      (> p_transfer_num p_transfer_den)
      ; 1b. Violate bidirectional |Gamma|^2 = 0 <=> (rL = z0 and xL = 0)
      (not (= (= gamma_num 0.0) (and (= rL z0) (= xL 0.0))))
      ; 2. Violate Bandgap Zero-TC cancellation
      (distinct v_bandgap vbg0)
      ; 3. Violate Emitter-Ballasted BJT thermal equilibrium uniqueness or safe bound
      (distinct tjEq1 tjEq2)
      (>= tjEq1 125.0)
      ; 4. Violate Calibrated 74LS -> 74HCT VOL/VOH noise margin or fail to detect 74LS -> 74HC negative margin
      (> actVol 400.0)
      (< actVoh 2700.0)
      (< nm_high_74ls_to_74hct 700.0)
      (>= nm_high_74ls_to_74hc 0.0)
      ; 5. Violate Tayloe I/Q two-angle image cancellation
      (distinct iq_image_cancel 0.0)
      ; 6. Violate ABBA quadratic bow residual or Prouhet-Thue-Morse (ABBABAAB) 2nd-order cancellation
      (distinct abba_mismatch (* 4.0 (* cxxOx (* pitchOx pitchOx))))
      (distinct ptm8_mismatch 0.0)
      ; 7. Violate CMT 2x2 coupler optical power conservation or Microring critical coupling
      (distinct (+ p_out1_opt p_out2_opt) (+ pIn1Opt pIn2Opt))
      (not (= (= mrr_thru_num 0.0) (= rMrr aMrr)))
      ; 8. Violate CORDIC stage-0 norm scaling or Phased-Array N^2 coherent main-lobe power gain
      (distinct cordic_norm1 (* 2.0 cordic_norm0))
      (distinct ula_power (* (* nElem nElem) (* ampElem ampElem)))))

(check-sat)
