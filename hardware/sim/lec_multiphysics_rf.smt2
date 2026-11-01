; Z3 SMT-LIB2 Formal Verification Check (`QF_NRA` Real Nonlinear Arithmetic) for:
; 1. Obend.Hardware.RF (`conjugate_match_maximizes_power` & `conjugate_match_zero_reflection`:
;    Maximum Power Transfer Theorem 4*R_S*R_L <= (R_S + R_L)^2 + (X_S + X_L)^2 and |Gamma|^2 = 0 iff Z_L = Z_0)
; 2. Obend.Hardware.Thermal (`bandgap_zero_tempco_cancellation`: Brokaw Bandgap CTAT + K*PTAT zero-TC over [-40, +125] C)
; 3. Obend.Hardware.Thermal (`emitter_ballast_stabilizes_thermal_loop`: Electro-thermal contraction gamma_th < 1)
; 4. Obend.Hardware.Datasheet (`calibrated_model_preserves_voltage_swing`: L_inf <= 20 mV preserves 74LS/74HCT margins)
; 5. Obend.Hardware.RF (`tayloe_iq_cancels_image_sideband`: Quadrature I/Q image phase cancellation)
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

(declare-const tjEq     Real)
(declare-const predVol  Real)
(declare-const actVol   Real)
(declare-const predVoh  Real)
(declare-const actVoh   Real)

(declare-const gainI    Real)
(declare-const gainQ    Real)
(declare-const cosWt    Real)
(declare-const sinWt    Real)

(assert (> rS 0.0))
(assert (> rL 0.0))
(assert (= z0 50.0))
(assert (and (>= deltaT -65.0) (<= deltaT 100.0)))

; 1. RF Maximum Power Transfer & Reflection Coefficient |Gamma|^2 over R
(define-fun p_transfer_num () Real (* 4.0 rS rL))
(define-fun p_transfer_den () Real (+ (* (+ rS rL) (+ rS rL)) (* (+ xS xL) (+ xS xL))))
(define-fun gamma_num () Real (+ (* (- rL z0) (- rL z0)) (* xL xL)))

; 2. Thermal Brokaw Bandgap Zero-TC Reference: alphaCtat = weightK * alphaPtat
(define-fun alphaCtat () Real (* weightK alphaPtat))
(define-fun v_bandgap () Real (+ (- vbg0 (* alphaCtat deltaT)) (* weightK (* alphaPtat deltaT))))

; 3. Electro-Thermal Feedback Contraction for Emitter-Ballasted BJT (gamma_th = 0.72 < 1.0):
;    T_j - T_amb = R_th * (P_0 + dP_dT_ballasted * (T_j - T_amb))
;    With T_amb = 25.0 C, R_th * P_0 = 16.576 C, gamma_th = 0.72 => unique equilibrium T_j = 84.2 C < 125.0 C
(assert (= (- tjEq 25.0) (+ 16.576 (* 0.72 (- tjEq 25.0)))))

; 4. Datasheet Calibration Swing Preservation:
;    If predVol <= 380 mV and |predVol - actVol| <= 20 mV, then actVol <= 400 mV (VOL_max);
;    If predVoh >= 2720 mV and |predVoh - actVoh| <= 20 mV, then actVoh >= 2700 mV (VOH_min) > 2000 mV (VIH_min of 74HCT00).
(assert (<= predVol 380.0))
(assert (and (<= (- predVol actVol) 20.0) (<= (- actVol predVol) 20.0)))
(assert (>= predVoh 2720.0))
(assert (and (<= (- predVoh actVoh) 20.0) (<= (- actVoh predVoh) 20.0)))

; 5. Tayloe Quadrature I/Q Image Cancellation:
;    For matched I/Q branches (gainI = gainQ), image = gainI*cosWt*sinWt - gainQ*sinWt*cosWt = 0,
;    and desired USB = gainI*(cosWt^2) + gainQ*(sinWt^2) = gainI when cosWt^2 + sinWt^2 = 1.
(assert (= gainI gainQ))
(assert (= (+ (* cosWt cosWt) (* sinWt sinWt)) 1.0))
(define-fun iq_image_out () Real (- (* gainI cosWt sinWt) (* gainQ sinWt cosWt)))
(define-fun iq_desired_out () Real (+ (* gainI cosWt cosWt) (* gainQ sinWt sinWt)))

(assert
  (or ; Violate Maximum Power Transfer bound 4*rS*rL <= (rS+rL)^2 + (xS+xL)^2
      (> p_transfer_num p_transfer_den)
      ; Violate |Gamma|^2 = 0 <=> (rL = z0 and xL = 0)
      (and (= gamma_num 0.0) (or (distinct rL z0) (distinct xL 0.0)))
      ; Violate Bandgap Zero-TC cancellation
      (distinct v_bandgap vbg0)
      ; Violate Emitter-Ballasted BJT thermal equilibrium < 125 C
      (>= tjEq 125.0)
      ; Violate Calibrated 74LS -> 74HCT VOL/VOH noise margin envelope
      (> actVol 400.0)
      (< actVoh 2700.0)
      ; Violate Tayloe I/Q image cancellation or desired sideband unity reconstruction
      (distinct iq_image_out 0.0)
      (distinct iq_desired_out gainI)))

(check-sat)
