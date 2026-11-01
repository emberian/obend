module
/-
# Obend.Hardware.Circuits — Classic `74LS00` Totem-Pole TTL, Pt100 RTD Bridge + 3-Op-Amp Instrumentation Amplifier & Synchronous Buck Power Converter

Formalizes classic **digital TTL, precision sensor analog instrumentation, and switched-mode power
electronics** within `Obend.Hardware`:

1. **Classic `SN74LS00` Schottky TTL Totem-Pole 2-Input NAND Gate (`TtlTotemPoleParams`, `evalTtlNandMv`)**:
   - Models the Schottky diode input AND array, phase-splitter BJT $Q_2$, Darlington high-side pull-up
     $Q_4$, and Baker-clamped low-side saturating driver $Q_3$ as a function of input voltages
     $(V_A, V_B)$ and fanout load $N_{\text{fanout}}$,
   - Proves **`ttl74ls00_nand_truth_and_swing_sound`**: for any inputs obeying `sn74ls00Datasheet`
     thresholds ($V_{IH} \ge 2000\,\text{mV}$, $V_{IL} \le 800\,\text{mV}$) and fanout $N \le 10$,
     the output voltage strictly satisfies $V_Y \le V_{OL,\max}$ ($400\,\text{mV}$) when both inputs
     are high and $V_Y \ge V_{OH,\min}$ ($2700\,\text{mV}$) when either input is low!
   - Proves `fanout_overload_degrades_vol_refused`: overloading the output with $N = 25 > 10$ LS-TTL
     unit loads pulls $V_{OL}$ to $430\,\text{mV} > 400\,\text{mV}$ and is refused by `checkTtlFanout`.
2. **Pt100 RTD Wheatstone Bridge + 3-Op-Amp Instrumentation Amplifier (`InaParams`, `evalInaOutputUv`)**:
   - Models a platinum resistance thermometer ($R(T) = R_0 (1 + \alpha T)$, $100.0\,\Omega$ at $0^\circ\text{C}$,
     $138.5\,\Omega$ at $100^\circ\text{C}$) feeding a 3-Op-Amp Instrumentation Amplifier in the presence
     of $60\,\text{Hz}$ common-mode hum $V_{\text{cm}}$ and thermal offset drift $V_{OS}(T)$,
   - Proves **`ina_common_mode_cancelled_at_matched_bridge`**: when the laser-trimmed differential/common-mode
     resistor network satisfies `p.gainCmRaw = p.trimCmCancel`, arbitrary common-mode hum $V_{\text{cm}}$
     contributes identically `0` to the amplifier output! (Targeted by `#tooth`.)
   - Proves `opamp_negative_feedback_stabilizes_gain`: increasing open-loop gain $A_{\text{OL}}$
     monotonically increases negative-feedback loop gain $1 + A_{\text{OL}} \beta$.
3. **Synchronous Buck DC-DC Power Converter (`BuckSpec`, `evalBuckSteadyVoutMv`, `checkBuckCcmSafe`)**:
   - Models steady-state inductor volt-second balance $V_{\text{out}} = D \cdot V_{\text{in}}$, peak-to-peak
     inductor current ripple $\Delta I_L$, Continuous Conduction Mode (CCM), and ferrite core saturation
     bounds $I_{\text{load}} + \Delta I_L / 2 \le I_{\text{sat}}$,
   - Proves `buck_volt_second_balance_bounded`, `buck_ccm_safe_prevents_core_saturation`, and
     `buck_overcurrent_saturation_refused`.
4. **Unified Datasheet-Fit & Circuit Calibration Certificate (`DatasheetFitCert`, `checkDatasheetFitSignoff`)**.
-/
public import Obend.Hardware.Thermal
public import Obend.Hardware.Datasheet
@[expose] public section

namespace Obend.Hardware.Circuits
open Obend.Hardware.Thermal Obend.Hardware.Datasheet
set_option autoImplicit false

/-! ## 1. Classic `SN74LS00` Schottky TTL Totem-Pole 2-Input NAND Gate (`evalTtlNandMv`) -/

/-- Physical BJT / Schottky-diode macro-model parameters for a `74LS00` totem-pole NAND gate:
* `vccMv`: nominal supply rail ($5000\,\text{mV}$),
* `vbeSatMv`: BJT base-emitter active/Darlington drop ($750\,\text{mV}$),
* `vceSatSchottkyMv`: Baker-clamped low-side Schottky BJT collector-emitter saturation voltage at zero load ($250\,\text{mV}$),
* `rOutLowOhm`: low-side saturation dynamic output resistance ($18\,\Omega$),
* `rOutHighOhm`: high-side Darlington emitter-follower output resistance ($120\,\Omega$),
* `iilPerGateUa`: unit low-state input source current per driven `74LS` fanout load ($400\,\mu\text{A}$),
* `iihPerGateUa`: unit high-state input leakage current per driven `74LS` fanout load ($20\,\mu\text{A}$),
* `maxFanout`: rated standard `74LS` fanout limit ($10$ loads $= 4.0\,\text{mA}$ nominal, $8.0\,\text{mA}$ max). -/
structure TtlTotemPoleParams where
  vccMv            : Int
  vbeSatMv         : Int
  vceSatSchottkyMv : Int
  rOutLowOhm       : Int
  rOutHighOhm      : Int
  iilPerGateUa     : Int
  iihPerGateUa     : Int
  maxFanout        : Nat
  deriving DecidableEq, Repr

/-- Canonical `SN74LS00` Schottky TTL totem-pole physical parameter set. -/
def sn74ls00TotemParams : TtlTotemPoleParams where
  vccMv            := 5000
  vbeSatMv         := 750
  vceSatSchottkyMv := 250
  rOutLowOhm       := 18
  rOutHighOhm      := 120
  iilPerGateUa     := 400
  iihPerGateUa     := 20
  maxFanout        := 10

/-- Evaluate the DC output voltage $V_Y$ (in $\text{mV}$) of a 2-input `74LS00` totem-pole NAND gate
at input voltages `(vAMv, vBMv)` driving `fanout` unit LS-TTL loads:
* When both inputs are recognized high (`2000 ≤ vAMv` and `2000 ≤ vBMv`), the phase splitter drives
  the lower Schottky-clamped BJT into saturation, sinking `fanout * iilPerGateUa` ($\mu\text{A}$)
  through `rOutLowOhm`,
* When either input is recognized low (`vAMv ≤ 800` or `vBMv ≤ 800`), the lower BJT cuts off and
  the upper Darlington pair sources `fanout * iihPerGateUa` ($\mu\text{A}$) below $V_{CC} - 2 V_{BE}$,
* In the intermediate transition zone (`800 < min(vA, vB) < 2000`), models the active phase-splitter
  transfer slope. -/
def evalTtlNandMv (p : TtlTotemPoleParams) (vAMv vBMv : Int) (fanout : Nat) : Int :=
  let fInt : Int := fanout
  if decide (2000 ≤ vAMv) && decide (2000 ≤ vBMv) then
    p.vceSatSchottkyMv + (fInt * p.iilPerGateUa * p.rOutLowOhm) / 1000
  else if decide (vAMv ≤ 800) || decide (vBMv ≤ 800) then
    p.vccMv - 2 * p.vbeSatMv - (fInt * p.iihPerGateUa * p.rOutHighOhm) / 1000
  else
    let vMin := if vAMv ≤ vBMv then vAMv else vBMv
    3460 - ((vMin - 800) * 2600) / 1200

/-- Evaluate propagation delay $t_{pd}$ (in picoseconds $\text{ps}$) of a `74LS00` gate as a function of
base internal delay `baseTpPs` ($8000\,\text{ps}$), fanout count `fanout`, and capacitive load per input
`capPerFanoutFf` ($15000\,\text{fF} = 15\,\text{pF}$). -/
def evalTtlPropDelayPs (baseTpPs fanout capPerFanoutFf : Nat) : Nat :=
  baseTpPs + (fanout * capPerFanoutFf) / 25

/-- Check that a `74LS00` gate's fanout load `fanout` obeys both the rated unit-load count
(`fanout ≤ p.maxFanout`) and keeps the worst-case saturated $V_{OL}$ within the $400\,\text{mV}$
TTL threshold. -/
def checkTtlFanout (p : TtlTotemPoleParams) (fanout : Nat) : Bool :=
  decide (fanout ≤ p.maxFanout) &&
  decide (evalTtlNandMv p 2000 2000 fanout ≤ 400)

/-- Theorem (`ttl74ls00_nand_truth_and_swing_sound`):
For ANY input voltages `vAMv, vBMv : Int` and ANY legal fanout `fanout ≤ 10`:
1. **NAND High-High $\to$ Low (`1 ∧ 1 ↦ 0`)**: if `2000 ≤ vAMv` and `2000 ≤ vBMv`, the totem-pole
   output voltage satisfies `evalTtlNandMv sn74ls00TotemParams vAMv vBMv fanout ≤ 400` ($V_{OL,\max}$),
2. **NAND Low-X $\to$ High (`0 ∧ X ↦ 1`)**: if `vAMv ≤ 800`, the totem-pole output voltage satisfies
   `2700 ≤ evalTtlNandMv sn74ls00TotemParams vAMv vBMv fanout` ($V_{OH,\min}$),
3. **NAND X-Low $\to$ High (`X ∧ 0 ↦ 1`)**: if `vBMv ≤ 800`, the totem-pole output voltage satisfies
   `2700 ≤ evalTtlNandMv sn74ls00TotemParams vAMv vBMv fanout` ($V_{OH,\min}$)! -/
theorem ttl74ls00_nand_truth_and_swing_sound
    (vAMv vBMv : Int) (fanout : Nat)
    (hFanout : fanout ≤ 10) :
    (2000 ≤ vAMv → 2000 ≤ vBMv →
      evalTtlNandMv sn74ls00TotemParams vAMv vBMv fanout ≤ sn74ls00Datasheet.logic.volMaxMv) ∧
    (vAMv ≤ 800 →
      sn74ls00Datasheet.logic.vohMinMv ≤ evalTtlNandMv sn74ls00TotemParams vAMv vBMv fanout) ∧
    (vBMv ≤ 800 →
      sn74ls00Datasheet.logic.vohMinMv ≤ evalTtlNandMv sn74ls00TotemParams vAMv vBMv fanout) := by
  dsimp only [evalTtlNandMv, sn74ls00TotemParams, sn74ls00Datasheet]
  refine ⟨?_, ?_, ?_⟩
  · intro hA hB
    have hCond : (decide (2000 ≤ vAMv) && decide (2000 ≤ vBMv)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨hA, hB⟩
    rw [if_pos hCond]
    omega
  · intro hA
    have hNotA : decide (2000 ≤ vAMv) = false := by
      rw [decide_eq_false_iff_not]
      omega
    have hCond1 : ¬ ((decide (2000 ≤ vAMv) && decide (2000 ≤ vBMv)) = true) := by
      rw [hNotA, Bool.false_and]
      decide
    have hLowA : decide (vAMv ≤ 800) = true := by
      rw [decide_eq_true_eq]
      exact hA
    have hCond2 : (decide (vAMv ≤ 800) || decide (vBMv ≤ 800)) = true := by
      rw [hLowA]
      rfl
    rw [if_neg hCond1, if_pos hCond2]
    omega
  · intro hB
    have hNotB : decide (2000 ≤ vBMv) = false := by
      rw [decide_eq_false_iff_not]
      omega
    have hCond1 : ¬ ((decide (2000 ≤ vAMv) && decide (2000 ≤ vBMv)) = true) := by
      rw [hNotB, Bool.and_false]
      decide
    have hLowB : decide (vBMv ≤ 800) = true := by
      rw [decide_eq_true_eq]
      exact hB
    have hCond2 : (decide (vAMv ≤ 800) || decide (vBMv ≤ 800)) = true := by
      rw [hLowB, Bool.or_true]
    rw [if_neg hCond1, if_pos hCond2]
    omega

/-- Theorem (`fanout_overload_degrades_vol_refused`):
Overloading an `SN74LS00` output with `fanout = 25` unit loads ($10\,\text{mA}$ sink current) degrades
$V_{OL}$ to $430\,\text{mV} > 400\,\text{mV}$ and is refused by `checkTtlFanout`. -/
theorem fanout_overload_degrades_vol_refused :
    evalTtlNandMv sn74ls00TotemParams 2000 2000 25 = 430 ∧
    checkTtlFanout sn74ls00TotemParams 25 = false :=
  ⟨rfl, rfl⟩

/-! ## 2. Pt100 RTD Sensor Bridge + 3-Op-Amp Instrumentation Amplifier (`evalInaOutputUv`) -/

/-- Callendar–Van Dusen linear platinum RTD resistance $R_{\text{Pt100}}(T) = R_0 (1 + \alpha T)$
in milliohms ($\text{m}\Omega$), where $R_0 = 100000\,\text{m}\Omega = 100.000\,\Omega$ at $0^\circ\text{C}$
and temperature coefficient $\alpha = 0.00385\,^\circ\text{C}^{-1}$ ($385\,\text{m}\Omega/^\circ\text{C}$). -/
def evalPt100Mohm (tempC : Int) : Int :=
  100000 + 385 * tempC

/-- Theorem (`pt100_ice_and_boiling_points`):
The Pt100 RTD sensor model evaluates to $100.000\,\Omega$ at $0^\circ\text{C}$ (ice point),
$138.500\,\Omega$ at $100^\circ\text{C}$ (boiling point), and $84.600\,\Omega$ at $-40^\circ\text{C}$. -/
theorem pt100_ice_and_boiling_points :
    evalPt100Mohm 0 = 100000 ∧
    evalPt100Mohm 100 = 138500 ∧
    evalPt100Mohm (-40) = 84600 :=
  ⟨rfl, rfl, rfl⟩

/-- Parameters of a 3-Op-Amp Instrumentation Amplifier (INA) conditioning a Wheatstone sensor bridge:
* `gainDiff`: differential voltage gain $G_{\text{diff}} = (1 + \frac{2 R_1}{R_G}) \cdot \frac{R_3}{R_2}$,
* `gainCmRaw`: untrimmed common-mode feedthrough gain due to resistor bridge mismatch,
* `trimCmCancel`: laser-trimmed common-mode cancellation factor (equals `gainCmRaw` at balanced trim),
* `vos0Uv`: room-temperature input offset voltage $V_{OS}(T_0)$ ($\mu\text{V}$),
* `dVosDtUvPerC`: input offset thermal drift slope $\frac{d V_{OS}}{d T}$ ($\mu\text{V}/^\circ\text{C}$). -/
structure InaParams where
  gainDiff     : Int
  gainCmRaw    : Int
  trimCmCancel : Int
  vos0Uv       : Int
  dVosDtUvPerC : Int
  deriving DecidableEq, Repr

/-- Precision laser-trimmed 3-Op-Amp Instrumentation Amplifier specification ($G_{\text{diff}} = 100$,
matched bridge trim `gainCmRaw = trimCmCancel = 1`, low offset $V_{OS0} = 25\,\mu\text{V}$). -/
def precisionMatchedIna : InaParams where
  gainDiff     := 100
  gainCmRaw    := 1
  trimCmCancel := 1
  vos0Uv       := 25
  dVosDtUvPerC := 0

/-- Evaluate the output voltage (in microvolts $\mu\text{V}$) of the 3-Op-Amp Instrumentation Amplifier
for differential bridge signal `vDiffUv`, common-mode $60\,\text{Hz}$ interference `vCmUv`, and
temperature excursion `deltaTC`:
$$V_{\text{out}} = G_{\text{diff}} \cdot \bigl(V_{\text{diff}} + V_{OS0} + \tfrac{d V_{OS}}{d T} \Delta T\bigr) + (G_{\text{cm,raw}} - G_{\text{cm,trim}}) \cdot V_{\text{cm}}.$$ -/
def evalInaOutputUv (p : InaParams) (vDiffUv vCmUv deltaTC : Int) : Int :=
  p.gainDiff * (vDiffUv + p.vos0Uv + p.dVosDtUvPerC * deltaTC) +
  (p.gainCmRaw - p.trimCmCancel) * vCmUv

/-- Theorem (`ina_common_mode_cancelled_at_matched_bridge`):
When the subtractor bridge trim matches the raw common-mode feedthrough (`p.gainCmRaw = p.trimCmCancel`),
ANY common-mode interference `vCmUv : Int` (such as $1\,\text{V}_{\text{pp}}$ $60\,\text{Hz}$ mains hum)
is rejected identically to zero in `evalInaOutputUv`!
Written via `dsimp only` + `omega` + `rw` (zero `simp` aux defs) so `#tooth` can mutate `evalInaOutputUv`. -/
theorem ina_common_mode_cancelled_at_matched_bridge
    (p : InaParams) (vDiffUv vCmUv deltaTC : Int)
    (hTrim : p.gainCmRaw = p.trimCmCancel) :
    evalInaOutputUv p vDiffUv vCmUv deltaTC =
      p.gainDiff * (vDiffUv + p.vos0Uv + p.dVosDtUvPerC * deltaTC) := by
  dsimp only [evalInaOutputUv]
  have hZero : p.gainCmRaw - p.trimCmCancel = 0 := by omega
  rw [hZero, Int.zero_mul, Int.add_zero]

/-- Negative-feedback loop factor $1000 + A_{\text{OL}} \cdot \beta_{\text{permille}}$ of an operational
amplifier with open-loop gain `aOl` and feedback attenuation network $\beta \in [0, 1000]\,\text{permille}$.
Higher loop factor directly suppresses closed-loop gain error $\frac{1}{1 + A_{\text{OL}} \beta}$,
nonlinear harmonic distortion, and output impedance. -/
def evalFeedbackLoopFactor (aOl betaPermille : Int) : Int :=
  1000 + aOl * betaPermille

/-- Theorem (`opamp_negative_feedback_stabilizes_gain`):
For any non-negative feedback factor `0 ≤ betaPermille`, increasing the op-amp open-loop gain
`aOl1 ≤ aOl2` monotonically increases the negative-feedback loop desensitivity factor
`evalFeedbackLoopFactor aOl1 betaPermille ≤ evalFeedbackLoopFactor aOl2 betaPermille`. -/
theorem opamp_negative_feedback_stabilizes_gain
    (aOl1 aOl2 betaPermille : Int)
    (hGain : aOl1 ≤ aOl2)
    (hBeta : 0 ≤ betaPermille) :
    evalFeedbackLoopFactor aOl1 betaPermille ≤ evalFeedbackLoopFactor aOl2 betaPermille := by
  dsimp only [evalFeedbackLoopFactor]
  have hMul := int_mul_le_mul_of_nonneg_right aOl1 aOl2 betaPermille hGain hBeta
  omega

/-! ## 3. Synchronous Buck DC-DC Power Converter (`BuckSpec`, `checkBuckCcmSafe`) -/

/-- Specification of a synchronous step-down (Buck) switched-mode DC-DC converter:
* `vinMv`: input supply voltage $V_{\text{in}}$ ($\text{mV}$, e.g., $12000\,\text{mV}$),
* `dutyPermille`: PWM high-side switch duty cycle $D \in [0, 1000]$ (in per-mille, e.g. $417 \mapsto 5.0\,\text{V}$),
* `inductanceUh`: filter inductor value $L$ ($\mu\text{H}$),
* `fswKhz`: PWM switching frequency $f_{\text{sw}}$ ($\text{kHz}$),
* `iLoadMa`: DC output load current $I_{\text{load}}$ ($\text{mA}$),
* `iSatMaxMa`: inductor magnetic core saturation current rating $I_{\text{sat}}$ ($\text{mA}$). -/
structure BuckSpec where
  stageName    : String
  vinMv        : Nat
  dutyPermille : Nat
  inductanceUh : Nat
  fswKhz       : Nat
  iLoadMa      : Nat
  iSatMaxMa    : Nat
  deriving DecidableEq, Repr

/-- Steady-state Buck output voltage $V_{\text{out}} = \lfloor \frac{D \cdot V_{\text{in}}}{1000} \rfloor$ ($\text{mV}$)
derived from inductor volt-second balance ($V_L = V_{\text{in}} - V_{\text{out}}$ during $D T_{\text{sw}}$ and
$V_L = -V_{\text{out}}$ during $(1 - D) T_{\text{sw}}$). -/
def evalBuckSteadyVoutMv (b : BuckSpec) : Nat :=
  (b.dutyPermille * b.vinMv) / 1000

/-- Peak-to-peak inductor current ripple $\Delta I_L = \frac{V_{\text{out}} \cdot (1000 - D)}{L_{\mu\text{H}} \cdot f_{\text{sw,kHz}}}$ ($\text{mA}$). -/
def evalBuckRippleMa (b : BuckSpec) : Nat :=
  let voutMv := evalBuckSteadyVoutMv b
  (voutMv * (1000 - b.dutyPermille)) / (b.inductanceUh * b.fswKhz)

/-- Peak inductor current $I_{L,\text{peak}} = I_{\text{load}} + \frac{\Delta I_L}{2}$ ($\text{mA}$). -/
def evalBuckPeakInductorMa (b : BuckSpec) : Nat :=
  b.iLoadMa + evalBuckRippleMa b / 2

/-- Verify that a synchronous Buck converter operates safely in Continuous Conduction Mode (CCM)
without saturating its inductor core:
1. Valid PWM duty cycle `dutyPermille ≤ 1000`, positive $L$ and $f_{\text{sw}}$,
2. Continuous Conduction Mode (`evalBuckRippleMa b ≤ 2 * b.iLoadMa`, so $I_{L,\text{valley}} \ge 0$),
3. Magnetic core saturation safety (`evalBuckPeakInductorMa b ≤ b.iSatMaxMa`). -/
def checkBuckCcmSafe (b : BuckSpec) : Bool :=
  decide (b.dutyPermille ≤ 1000) &&
  decide (0 < b.inductanceUh) &&
  decide (0 < b.fswKhz) &&
  decide (evalBuckRippleMa b ≤ 2 * b.iLoadMa) &&
  decide (evalBuckPeakInductorMa b ≤ b.iSatMaxMa)

/-- Canonical $12\,\text{V} \to 5.0\,\text{V}$ ($2\,\text{A}$ load, $L = 10\,\mu\text{H}$, $f_{\text{sw}} = 500\,\text{kHz}$,
$I_{\text{sat}} = 3500\,\text{mA}$) synchronous Buck supply for a TTL/CMOS board. -/
def golden5vBuckSpec : BuckSpec where
  stageName    := "buck_12v_to_5v_2a"
  vinMv        := 12000
  dutyPermille := 417
  inductanceUh := 10
  fswKhz       := 500
  iLoadMa      := 2000
  iSatMaxMa    := 3500

/-- Overloaded Buck stage (`iLoadMa = 3400 mA`, `I_peak = 3691 mA > I_sat = 3500 mA`): drives the
ferrite inductor into magnetic core saturation! -/
def overloadedSaturatingBuckSpec : BuckSpec :=
  { golden5vBuckSpec with iLoadMa := 3400 }

/-- Theorem (`buck_volt_second_balance_bounded`):
For any Buck converter with valid duty cycle `b.dutyPermille ≤ 1000`, the steady-state output voltage
never exceeds the input supply (`evalBuckSteadyVoutMv b ≤ b.vinMv`). -/
theorem buck_volt_second_balance_bounded (b : BuckSpec) (hDuty : b.dutyPermille ≤ 1000) :
    evalBuckSteadyVoutMv b ≤ b.vinMv := by
  dsimp only [evalBuckSteadyVoutMv]
  have hMul : b.dutyPermille * b.vinMv ≤ 1000 * b.vinMv :=
    Nat.mul_le_mul_right b.vinMv hDuty
  have hDiv : (b.dutyPermille * b.vinMv) / 1000 ≤ (1000 * b.vinMv) / 1000 :=
    Nat.div_le_div_right hMul
  omega

/-- Theorem (`buck_ccm_safe_prevents_core_saturation`):
Any Buck converter accepted by `checkBuckCcmSafe` satisfies `evalBuckPeakInductorMa b ≤ b.iSatMaxMa`
and remains in Continuous Conduction Mode (`evalBuckRippleMa b ≤ 2 * b.iLoadMa`). -/
theorem buck_ccm_safe_prevents_core_saturation
    (b : BuckSpec) (hOk : checkBuckCcmSafe b = true) :
    evalBuckRippleMa b ≤ 2 * b.iLoadMa ∧
    evalBuckPeakInductorMa b ≤ b.iSatMaxMa := by
  dsimp only [checkBuckCcmSafe] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  rw [decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hOk
  exact ⟨hOk.1.2, hOk.2⟩

/-- Theorem (`buck_overcurrent_saturation_refused`):
`golden5vBuckSpec` regulates to $5004\,\text{mV}$ with ripple $583\,\text{mA}$ and passes `checkBuckCcmSafe`,
whereas `overloadedSaturatingBuckSpec` exceeds $I_{\text{sat}} = 3500\,\text{mA}$ and is refused! -/
theorem buck_overcurrent_saturation_refused :
    evalBuckSteadyVoutMv golden5vBuckSpec = 5004 ∧
    checkBuckCcmSafe golden5vBuckSpec = true ∧
    checkBuckCcmSafe overloadedSaturatingBuckSpec = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## 4. Unified Datasheet-Fit & Mixed-Signal Circuit Calibration Certificate (`DatasheetFitCert`) -/

/-- Complete verification certificate for the `datasheet-fit@1` judge combining:
1. Cross-family logic noise-margin verification (`checkLogicInterface`),
2. `SN74LS00` totem-pole fanout & saturation verification (`checkTtlFanout`),
3. Empirical $L_\infty$ transfer-curve calibration (`checkModelCalibration`),
4. Instrumentation amplifier common-mode hum cancellation (`gainCmRaw == trimCmCancel`),
5. Synchronous Buck power-rail CCM and core-saturation safety (`checkBuckCcmSafe`). -/
structure DatasheetFitCert where
  suiteName       : String
  driverSpec      : LogicFamilySpec
  receiverSpec    : LogicFamilySpec
  pullupBoostMv   : Int
  minMarginMv     : Int
  ttlParams       : TtlTotemPoleParams
  fanout          : Nat
  modelPreds      : List Int
  datasheetPoints : List DatasheetCurvePoint
  maxCalErrMv     : Int
  inaSpec         : InaParams
  buckStage       : BuckSpec
  deriving DecidableEq, Repr

/-- Complete kernel checker for a `DatasheetFitCert`. -/
def checkDatasheetFitSignoff (cert : DatasheetFitCert) : Bool :=
  checkLogicInterface cert.driverSpec cert.receiverSpec cert.pullupBoostMv cert.minMarginMv &&
  checkTtlFanout cert.ttlParams cert.fanout &&
  checkModelCalibration cert.modelPreds cert.datasheetPoints cert.maxCalErrMv &&
  (cert.inaSpec.gainCmRaw == cert.inaSpec.trimCmCancel) &&
  checkBuckCcmSafe cert.buckStage

/-- Golden calibrated `SN74LS00` $\to$ `CD74HCT00` + Pt100 INA + 5V Buck certificate. -/
def goldenDatasheetFitCert : DatasheetFitCert where
  suiteName       := "obend_74ls_hct_ina_calibrated"
  driverSpec      := sn74ls00Datasheet.logic
  receiverSpec    := cd74hct00Datasheet.logic
  pullupBoostMv   := 0
  minMarginMv     := 400
  ttlParams       := sn74ls00TotemParams
  fanout          := 8
  modelPreds      := calibrated74ls00ModelPreds
  datasheetPoints := sn74ls00Datasheet.transferCurve
  maxCalErrMv     := 25
  inaSpec         := precisionMatchedIna
  buckStage       := golden5vBuckSpec

/-- Bad certificate attempting to drive `CD74HC00` directly from `SN74LS00` without a pull-up
($\text{NM}_H = -800\,\text{mV}$). -/
def badDirect74HcFitCert : DatasheetFitCert :=
  { goldenDatasheetFitCert with
    receiverSpec  := cd74hc00Datasheet.logic
    pullupBoostMv := 0 }

/-- Bad certificate with uncalibrated model drift ($\varepsilon_\infty = 620\,\text{mV} > 25\,\text{mV}$). -/
def badUncalibratedDriftFitCert : DatasheetFitCert :=
  { goldenDatasheetFitCert with
    modelPreds := uncalibratedDrifted74ls00Preds }

/-- Theorem (`datasheet_fit_signoff_poles`):
`checkDatasheetFitSignoff` accepts `goldenDatasheetFitCert` and refuses both `badDirect74HcFitCert`
(direct `74LS` $\to$ `74HC` negative noise margin) and `badUncalibratedDriftFitCert`! -/
theorem datasheet_fit_signoff_poles :
    checkDatasheetFitSignoff goldenDatasheetFitCert = true ∧
    checkDatasheetFitSignoff badDirect74HcFitCert = false ∧
    checkDatasheetFitSignoff badUncalibratedDriftFitCert = false :=
  ⟨rfl, rfl, rfl⟩

end Obend.Hardware.Circuits
