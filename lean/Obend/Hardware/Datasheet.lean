module
/-
# Obend.Hardware.Datasheet — Automated Datasheet Capture, Logic Family Noise-Margin Algebra, Timing Windows & Model-vs-Datasheet Calibration

Formalizes **automated semiconductor datasheet capture, cross-family logic interfacing, timing-diagram
window verification, and $L_\infty$ model-to-datasheet calibration certificates** within `Obend.Hardware`:

1. **Structured Component Datasheets (`LogicFamilySpec`, `TimingDiagramSpec`, `DatasheetCurvePoint`, `ComponentDatasheet`)**:
   - Captures DC voltage & current specifications ($V_{CC}$, $V_{IH,\min}$, $V_{IL,\max}$, $V_{OH,\min}$,
     $V_{OL,\max}$, $I_{IH}$, $I_{IL}$, $I_{OH}$, $I_{OL}$), AC switching timing windows ($t_{pLH}$, $t_{pHL}$,
     $t_{\text{setup}}$, $t_{\text{hold}}$, overshoot), and digitized $V_{\text{in}} \to V_{\text{out}}$
     empirical transfer curve points for:
     * `sn74ls00Datasheet` (Texas Instruments `SN74LS00` Low-Power Schottky Quad 2-Input NAND),
     * `cd74hc00Datasheet` (High-Speed 5V CMOS Quad 2-Input NAND),
     * `cd74hct00Datasheet` (TTL-Input-Compatible 5V CMOS Quad 2-Input NAND).
2. **Noise-Margin Algebra & Cross-Family Interfacing (`noiseMarginHigh`, `noiseMarginLow`, `checkLogicInterface`)**:
   - Proves `ttl_to_hc_direct_interface_refused`: a `74LS00` output ($V_{OH,\min} = 2700\,\text{mV}$)
     driving a `74HC00` CMOS input ($V_{IH,\min} = 3500\,\text{mV}$) directly suffers negative high-state
     noise margin $\text{NM}_H = -800\,\text{mV}$ and is refused,
   - Proves `ttl_to_hct_interface_verified` ($\text{NM}_H = +700\,\text{mV}, \text{NM}_L = +400\,\text{mV}$)
     and `pullup_restores_ttl_to_hc_margin` (external pull-up resistor to $V_{CC}$ restores $\text{NM}_H = +1300\,\text{mV}$),
   - Proves **`checkLogicInterface_guarantees_valid_thresholds`** (targeted by `#tooth`).
3. **Automated Model-vs-Datasheet $L_\infty$ Error Minimization & Calibration (`pointAbsError`, `maxCurveErrorLInf`, `checkModelCalibration`)**:
   - Computes the worst-case $L_\infty$ residual $\varepsilon_{\max} = \max_i |\hat{y}_i - y_i|$ between a
     physics circuit macro-model and captured datasheet curve points,
   - Proves **`calibrated_model_preserves_voltage_swing`**: if a calibrated model prediction lies inside
     the tightened swing envelope `[volMaxMv - errBound]` / `[vohMinMv + errBound]` and
     `pointAbsError pred actual ≤ errBound`, then the physical device output is guaranteed to obey
     the datasheet DC thresholds!
4. **Timing Diagram Setup/Hold & Propagation Delay Window Verifier (`WaveformTransition`, `checkTimingWindow`)**:
   - Proves `timing_diagram_window_sound` and `setup_hold_violation_refused`.
-/
@[expose] public section

namespace Obend.Hardware.Datasheet
set_option autoImplicit false

/-! ## 1. Structured Component Datasheet Specifications (`LogicFamilySpec`, `ComponentDatasheet`) -/

/-- DC voltage and current operating envelope extracted from a digital/mixed-signal IC datasheet
(voltages in millivolts $\text{mV}$, currents in microamps $\mu\text{A}$):
* `vccMinMv`, `vccNomMv`, `vccMaxMv`: supply voltage window (e.g., $4750..5250\,\text{mV}$ for commercial 74LS),
* `vihMinMv`: minimum high-level input voltage guaranteed to be recognized as logic `1`,
* `vilMaxMv`: maximum low-level input voltage guaranteed to be recognized as logic `0`,
* `vohMinMv`: minimum high-level output voltage guaranteed at rated $I_{OH}$ load,
* `volMaxMv`: maximum low-level output voltage guaranteed at rated $I_{OL}$ sink load. -/
structure LogicFamilySpec where
  familyName : String
  vccMinMv   : Int
  vccNomMv   : Int
  vccMaxMv   : Int
  vihMinMv   : Int
  vilMaxMv   : Int
  vohMinMv   : Int
  volMaxMv   : Int
  iihMaxUa   : Int
  iilMaxUa   : Int
  iohMaxUa   : Int
  iolMaxUa   : Int
  deriving DecidableEq, Repr

/-- AC switching & synchronous timing diagram parameters (times in picoseconds $\text{ps}$,
overshoot in millivolts $\text{mV}$). -/
structure TimingDiagramSpec where
  tpLHMaxPs      : Nat
  tpHLMaxPs      : Nat
  tSetupMinPs    : Nat
  tHoldMinPs     : Nat
  maxOvershootMv : Int
  deriving DecidableEq, Repr

/-- A single digitized $(x, y)$ sample point captured from a datasheet characteristic curve
(e.g., $V_{\text{in}}\,(\text{mV}) \mapsto V_{\text{out}}\,(\text{mV})$ voltage transfer curve at $T_A = 25^\circ\text{C}$). -/
structure DatasheetCurvePoint where
  inputX    : Int
  measuredY : Int
  deriving DecidableEq, Repr

/-- Complete captured semiconductor datasheet record combining DC levels, AC timing diagram bounds,
empirical characteristic curve points, and rated operating temperature window $[T_{\min}, T_{\max}]$. -/
structure ComponentDatasheet where
  partNumber    : String
  logic         : LogicFamilySpec
  timing        : TimingDiagramSpec
  transferCurve : List DatasheetCurvePoint
  tempMinC      : Int
  tempMaxC      : Int
  deriving DecidableEq, Repr

/-- Canonical datasheet for the Texas Instruments `SN74LS00` Low-Power Schottky TTL Quad 2-Input NAND:
* $V_{CC} \in [4750, 5250]\,\text{mV}$, $V_{IH,\min} = 2000\,\text{mV}$, $V_{IL,\max} = 800\,\text{mV}$,
* $V_{OH,\min} = 2700\,\text{mV}$ (at $I_{OH} = -400\,\mu\text{A}$), $V_{OL,\max} = 400\,\text{mV}$ (at $I_{OL} = 8000\,\mu\text{A}$),
* $t_{pLH,\max} = 15000\,\text{ps}$ ($15\,\text{ns}$), $t_{pHL,\max} = 15000\,\text{ps}$ ($15\,\text{ns}$),
* 7-point digitized $V_{\text{in}} \mapsto V_{\text{out}}$ totem-pole transfer curve across $[0, 5000]\,\text{mV}$. -/
def sn74ls00Datasheet : ComponentDatasheet where
  partNumber := "SN74LS00"
  logic :=
    { familyName := "74LS_Schottky_TTL"
    , vccMinMv   := 4750
    , vccNomMv   := 5000
    , vccMaxMv   := 5250
    , vihMinMv   := 2000
    , vilMaxMv   := 800
    , vohMinMv   := 2700
    , volMaxMv   := 400
    , iihMaxUa   := 20
    , iilMaxUa   := 400
    , iohMaxUa   := 400
    , iolMaxUa   := 8000 }
  timing :=
    { tpLHMaxPs      := 15000
    , tpHLMaxPs      := 15000
    , tSetupMinPs    := 20000
    , tHoldMinPs     := 5000
    , maxOvershootMv := 500 }
  transferCurve :=
    [ { inputX := 0,    measuredY := 3480 }
    , { inputX := 600,  measuredY := 3470 }
    , { inputX := 800,  measuredY := 3460 }
    , { inputX := 1200, measuredY := 2150 }
    , { inputX := 1500, measuredY := 980  }
    , { inputX := 2000, measuredY := 330  }
    , { inputX := 5000, measuredY := 320  } ]
  tempMinC := 0
  tempMaxC := 70

/-- Canonical datasheet for the `CD74HC00` High-Speed 5V CMOS Quad 2-Input NAND:
* Symmetric CMOS input thresholds ($V_{IH,\min} = 3500\,\text{mV}$, $V_{IL,\max} = 1000\,\text{mV}$),
* Rail-to-rail CMOS output swing ($V_{OH,\min} = 4400\,\text{mV}$ under load, $V_{OL,\max} = 100\,\text{mV}$). -/
def cd74hc00Datasheet : ComponentDatasheet where
  partNumber := "CD74HC00"
  logic :=
    { familyName := "74HC_5V_CMOS"
    , vccMinMv   := 4500
    , vccNomMv   := 5000
    , vccMaxMv   := 5500
    , vihMinMv   := 3500
    , vilMaxMv   := 1000
    , vohMinMv   := 4400
    , volMaxMv   := 100
    , iihMaxUa   := 1
    , iilMaxUa   := 1
    , iohMaxUa   := 4000
    , iolMaxUa   := 4000 }
  timing :=
    { tpLHMaxPs      := 18000
    , tpHLMaxPs      := 18000
    , tSetupMinPs    := 15000
    , tHoldMinPs     := 3000
    , maxOvershootMv := 400 }
  transferCurve :=
    [ { inputX := 0,    measuredY := 4990 }
    , { inputX := 1000, measuredY := 4950 }
    , { inputX := 2500, measuredY := 2500 }
    , { inputX := 3500, measuredY := 50   }
    , { inputX := 5000, measuredY := 10   } ]
  tempMinC := -40
  tempMaxC := 125

/-- Canonical datasheet for the `CD74HCT00` TTL-Compatible High-Speed 5V CMOS Quad 2-Input NAND:
* Asymmetric PFET/NFET input stage shifted to TTL thresholds ($V_{IH,\min} = 2000\,\text{mV}$, $V_{IL,\max} = 800\,\text{mV}$),
* Full CMOS output swing ($V_{OH,\min} = 4400\,\text{mV}$, $V_{OL,\max} = 100\,\text{mV}$). -/
def cd74hct00Datasheet : ComponentDatasheet where
  partNumber := "CD74HCT00"
  logic :=
    { familyName := "74HCT_TTL_Compatible_CMOS"
    , vccMinMv   := 4500
    , vccNomMv   := 5000
    , vccMaxMv   := 5500
    , vihMinMv   := 2000
    , vilMaxMv   := 800
    , vohMinMv   := 4400
    , volMaxMv   := 100
    , iihMaxUa   := 1
    , iilMaxUa   := 1
    , iohMaxUa   := 4000
    , iolMaxUa   := 4000 }
  timing :=
    { tpLHMaxPs      := 18000
    , tpHLMaxPs      := 18000
    , tSetupMinPs    := 15000
    , tHoldMinPs     := 3000
    , maxOvershootMv := 400 }
  transferCurve :=
    [ { inputX := 0,    measuredY := 4990 }
    , { inputX := 800,  measuredY := 4920 }
    , { inputX := 1400, measuredY := 2400 }
    , { inputX := 2000, measuredY := 60   }
    , { inputX := 5000, measuredY := 10   } ]
  tempMinC := -40
  tempMaxC := 125

/-! ## 2. Noise-Margin Algebra & Cross-Family Logic Interfacing (`checkLogicInterface`) -/

/-- High-state DC noise margin $\text{NM}_H = (V_{OH,\min}^{\text{drv}} + \Delta V_{\text{pullup}}) - V_{IH,\min}^{\text{rcv}}$
(in millivolts $\text{mV}$), where `pullupBoostMv` is `0` for a direct totem-pole connection or positive
when an external pull-up resistor to $V_{CC}$ is attached. -/
def noiseMarginHigh (drv rcv : LogicFamilySpec) (pullupBoostMv : Int) : Int :=
  (drv.vohMinMv + pullupBoostMv) - rcv.vihMinMv

/-- Low-state DC noise margin $\text{NM}_L = V_{IL,\max}^{\text{rcv}} - V_{OL,\max}^{\text{drv}}$
(in millivolts $\text{mV}$). -/
def noiseMarginLow (drv rcv : LogicFamilySpec) : Int :=
  rcv.vilMaxMv - drv.volMaxMv

/-- Verify that a driver logic family `drv` can safely drive a receiver logic family `rcv` with
pull-up boost `pullupBoostMv` and minimum required noise immunity `minMarginMv` (typically $400\,\text{mV}$):
1. $\text{NM}_H \ge \text{minMarginMv}$,
2. $\text{NM}_L \ge \text{minMarginMv}$, and
3. Strict logic threshold separation ($V_{OL,\max}^{\text{drv}} < V_{IH,\min}^{\text{rcv}}$). -/
def checkLogicInterface (drv rcv : LogicFamilySpec) (pullupBoostMv minMarginMv : Int) : Bool :=
  decide (minMarginMv ≤ noiseMarginHigh drv rcv pullupBoostMv) &&
  decide (minMarginMv ≤ noiseMarginLow drv rcv) &&
  decide (drv.volMaxMv < rcv.vihMinMv)

/-- Theorem (`ttl_to_hc_direct_interface_refused`):
Connecting an `SN74LS00` TTL output ($V_{OH,\min} = 2700\,\text{mV}$) directly to a `CD74HC00` 5V CMOS
input ($V_{IH,\min} = 3500\,\text{mV}$) without a pull-up resistor (`pullupBoostMv = 0`) yields a
negative high-state noise margin $\text{NM}_H = -800\,\text{mV}$ and is refused by `checkLogicInterface`! -/
theorem ttl_to_hc_direct_interface_refused :
    noiseMarginHigh sn74ls00Datasheet.logic cd74hc00Datasheet.logic 0 = -800 ∧
    checkLogicInterface sn74ls00Datasheet.logic cd74hc00Datasheet.logic 0 400 = false :=
  ⟨rfl, rfl⟩

/-- Theorem (`ttl_to_hct_interface_verified`):
Replacing the receiver with a TTL-compatible `CD74HCT00` ($V_{IH,\min} = 2000\,\text{mV}, V_{IL,\max} = 800\,\text{mV}$)
achieves $\text{NM}_H = +700\,\text{mV} \ge 400\,\text{mV}$ and $\text{NM}_L = +400\,\text{mV} \ge 400\,\text{mV}$,
and is accepted by `checkLogicInterface`! -/
theorem ttl_to_hct_interface_verified :
    noiseMarginHigh sn74ls00Datasheet.logic cd74hct00Datasheet.logic 0 = 700 ∧
    noiseMarginLow sn74ls00Datasheet.logic cd74hct00Datasheet.logic = 400 ∧
    checkLogicInterface sn74ls00Datasheet.logic cd74hct00Datasheet.logic 0 400 = true :=
  ⟨rfl, rfl, rfl⟩

/-- Theorem (`pullup_restores_ttl_to_hc_margin`):
Adding a $2.2\,\text{k}\Omega$ external pull-up resistor to the `5.0V` rail (`pullupBoostMv = 2100`,
pulling $V_{OH}$ from $2700\,\text{mV}$ to $4800\,\text{mV}$) restores $\text{NM}_H = +1300\,\text{mV}$
and allows `SN74LS00` to safely drive `CD74HC00`! -/
theorem pullup_restores_ttl_to_hc_margin :
    noiseMarginHigh sn74ls00Datasheet.logic cd74hc00Datasheet.logic 2100 = 1300 ∧
    checkLogicInterface sn74ls00Datasheet.logic cd74hc00Datasheet.logic 2100 400 = true :=
  ⟨rfl, rfl⟩

/-- Theorem (`checkLogicInterface_guarantees_valid_thresholds`):
Whenever `checkLogicInterface drv rcv pullupBoostMv minMarginMv = true`, the high output level
exceeds the receiver high threshold by at least `minMarginMv`, the receiver low threshold exceeds
the low output level by at least `minMarginMv`, and $V_{OL,\max}^{\text{drv}} < V_{IH,\min}^{\text{rcv}}$.
Written via `dsimp only` + `rw` + `omega` (zero `simp` auxiliary defs) so `#tooth` can mutate `checkLogicInterface`. -/
theorem checkLogicInterface_guarantees_valid_thresholds
    (drv rcv : LogicFamilySpec) (pullupBoostMv minMarginMv : Int)
    (hOk : checkLogicInterface drv rcv pullupBoostMv minMarginMv = true) :
    rcv.vihMinMv + minMarginMv ≤ drv.vohMinMv + pullupBoostMv ∧
    drv.volMaxMv + minMarginMv ≤ rcv.vilMaxMv ∧
    drv.volMaxMv < rcv.vihMinMv := by
  dsimp only [checkLogicInterface] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true] at hOk
  rw [decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hOk
  have h1 : minMarginMv ≤ drv.vohMinMv + pullupBoostMv - rcv.vihMinMv := hOk.1.1
  have h2 : minMarginMv ≤ rcv.vilMaxMv - drv.volMaxMv := hOk.1.2
  have h3 : drv.volMaxMv < rcv.vihMinMv := hOk.2
  refine ⟨by omega, by omega, h3⟩

/-! ## 3. Automated Model-vs-Datasheet $L_\infty$ Calibration & Swing Preservation -/

/-- Absolute point-wise residual $|\hat{y} - y|$ between a circuit model prediction `predY` and an
empirical datasheet curve point `actualY`. -/
def pointAbsError (predY actualY : Int) : Int :=
  if predY ≥ actualY then predY - actualY else actualY - predY

/-- Theorem (`pointAbsError_nonneg_and_symm`):
`pointAbsError` is non-negative and symmetric (`|a - b| = |b - a|`). -/
theorem pointAbsError_nonneg_and_symm (a b : Int) :
    0 ≤ pointAbsError a b ∧ pointAbsError a b = pointAbsError b a := by
  dsimp only [pointAbsError]
  by_cases hab : a ≥ b <;> by_cases hba : b ≥ a
  · rw [if_pos hab, if_pos hba]
    refine ⟨by omega, by omega⟩
  · rw [if_pos hab, if_neg hba]
    refine ⟨by omega, rfl⟩
  · rw [if_neg hab, if_pos hba]
    refine ⟨by omega, rfl⟩
  · omega

/-- Compute the worst-case $L_\infty$ error $\varepsilon_{\max} = \max_i |\hat{y}_i - y_i|$ across a list
of model predictions and captured `DatasheetCurvePoint`s. -/
def maxCurveErrorLInf : List Int → List DatasheetCurvePoint → Int
  | [], [] => 0
  | p :: ps, pt :: pts =>
    let eCur := pointAbsError p pt.measuredY
    let eRest := maxCurveErrorLInf ps pts
    if eCur ≥ eRest then eCur else eRest
  | _, _ => 1000000

/-- Check that a circuit model's predictions `preds` match the captured datasheet curve `pts`
within worst-case $L_\infty$ tolerance `tolMv` ($\text{mV}$). -/
def checkModelCalibration (preds : List Int) (pts : List DatasheetCurvePoint) (tolMv : Int) : Bool :=
  decide (preds.length = pts.length) &&
  decide (0 ≤ tolMv) &&
  decide (maxCurveErrorLInf preds pts ≤ tolMv)

/-- Calibrated Ebers–Moll / Schottky macro-model predictions for the 7 points of `sn74ls00Datasheet.transferCurve`:
achieves worst-case residual $\varepsilon_{\max} = 14\,\text{mV} \le 25\,\text{mV}$! -/
def calibrated74ls00ModelPreds : List Int :=
  [3476, 3476, 3472, 2136, 992, 322, 322]

/-- Uncalibrated drifted model predictions (e.g., ignoring Schottky Baker clamp & Darlington drop):
suffers worst-case residual $\varepsilon_{\max} = 620\,\text{mV} > 25\,\text{mV}$! -/
def uncalibratedDrifted74ls00Preds : List Int :=
  [4100, 4100, 4050, 2500, 1200, 580, 550]

/-- Theorem (`sn74ls00_calibration_certificate_verified`):
`calibrated74ls00ModelPreds` has exact $L_\infty$ error $14\,\text{mV} \le 25\,\text{mV}$ against
`sn74ls00Datasheet.transferCurve` and is accepted by `checkModelCalibration`, whereas
`uncalibratedDrifted74ls00Preds` ($620\,\text{mV}$ error) is refused! -/
theorem sn74ls00_calibration_certificate_verified :
    maxCurveErrorLInf calibrated74ls00ModelPreds sn74ls00Datasheet.transferCurve = 14 ∧
    checkModelCalibration calibrated74ls00ModelPreds sn74ls00Datasheet.transferCurve 25 = true ∧
    checkModelCalibration uncalibratedDrifted74ls00Preds sn74ls00Datasheet.transferCurve 25 = false :=
  ⟨rfl, rfl, rfl⟩

/-- Theorem (`calibrated_model_preserves_voltage_swing`):
If a circuit model has bounded point-wise calibration error `pointAbsError predMv actualMv ≤ errBound`:
1. Whenever the model predicts a low output with safety margin (`predMv ≤ volMaxMv - errBound`),
   the actual physical voltage satisfies `actualMv ≤ volMaxMv`,
2. Whenever the model predicts a high output with safety margin (`vohMinMv + errBound ≤ predMv`),
   the actual physical voltage satisfies `vohMinMv ≤ actualMv`, and
3. Whenever the model prediction lies within `[volMaxMv + errBound, vohMinMv - errBound]`,
   the actual physical voltage lies within `[volMaxMv, vohMinMv]`! -/
theorem calibrated_model_preserves_voltage_swing
    (predMv actualMv volMaxMv vohMinMv errBound : Int)
    (hCal : pointAbsError predMv actualMv ≤ errBound) :
    (predMv ≤ volMaxMv - errBound → actualMv ≤ volMaxMv) ∧
    (vohMinMv + errBound ≤ predMv → vohMinMv ≤ actualMv) ∧
    (volMaxMv + errBound ≤ predMv → predMv ≤ vohMinMv - errBound →
      volMaxMv ≤ actualMv ∧ actualMv ≤ vohMinMv) := by
  dsimp only [pointAbsError] at hCal
  by_cases hGe : predMv ≥ actualMv
  · rw [if_pos hGe] at hCal
    refine ⟨by omega, by omega, by omega⟩
  · rw [if_neg hGe] at hCal
    refine ⟨by omega, by omega, by omega⟩

/-! ## 4. Timing Diagram Setup/Hold & Propagation Delay Window Verifier (`checkTimingWindow`) -/

/-- A digital waveform transition event measured relative to a reference clock edge:
* `dataStableBeforePs`: time data input was stable prior to the active clock edge ($t_{\text{setup}}$),
* `dataStableAfterPs`: time data input remained stable after the active clock edge ($t_{\text{hold}}$),
* `outputValidAfterPs`: time from input/clock transition to valid output settling ($t_{pLH}$ or $t_{pHL}$),
* `measuredOvershootMv`: peak transient ringing overshoot above $V_{CC}$ or undershoot below $\text{GND}$. -/
structure WaveformTransition where
  signalName          : String
  dataStableBeforePs  : Nat
  dataStableAfterPs   : Nat
  outputValidAfterPs  : Nat
  measuredOvershootMv : Int
  deriving DecidableEq, Repr

/-- Check that a measured `WaveformTransition` satisfies all datasheet AC timing & overshoot limits. -/
def checkTimingWindow (spec : TimingDiagramSpec) (tr : WaveformTransition) : Bool :=
  decide (spec.tSetupMinPs ≤ tr.dataStableBeforePs) &&
  decide (spec.tHoldMinPs ≤ tr.dataStableAfterPs) &&
  decide (tr.outputValidAfterPs ≤ spec.tpLHMaxPs) &&
  decide (tr.outputValidAfterPs ≤ spec.tpHLMaxPs) &&
  decide (tr.measuredOvershootMv ≤ spec.maxOvershootMv)

/-- Theorem (`timing_diagram_window_sound`):
Any waveform transition accepted by `checkTimingWindow spec tr` satisfies the setup time, hold time,
propagation delay (`tpLHMaxPs`, `tpHLMaxPs`), and overshoot bounds of `spec`. -/
theorem timing_diagram_window_sound
    (spec : TimingDiagramSpec) (tr : WaveformTransition)
    (hOk : checkTimingWindow spec tr = true) :
    spec.tSetupMinPs ≤ tr.dataStableBeforePs ∧
    spec.tHoldMinPs ≤ tr.dataStableAfterPs ∧
    tr.outputValidAfterPs ≤ spec.tpLHMaxPs ∧
    tr.outputValidAfterPs ≤ spec.tpHLMaxPs ∧
    tr.measuredOvershootMv ≤ spec.maxOvershootMv := by
  dsimp only [checkTimingWindow] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  rw [decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hOk
  exact ⟨hOk.1.1.1.1, hOk.1.1.1.2, hOk.1.1.2, hOk.1.2, hOk.2⟩

/-- Theorem (`setup_hold_violation_refused`):
A metastability-inducing waveform transition on `SN74LS00` with only $8000\,\text{ps} < 20000\,\text{ps}$
setup margin is refused by `checkTimingWindow`. -/
theorem setup_hold_violation_refused :
    checkTimingWindow sn74ls00Datasheet.timing
      { signalName := "D_meta", dataStableBeforePs := 8000, dataStableAfterPs := 6000
      , outputValidAfterPs := 9200, measuredOvershootMv := 180 } = false :=
  rfl

end Obend.Hardware.Datasheet
