module
/-
# Obend.Hardware.Thermal — Electro-Thermal Multiphysics, Cauer/Foster RC Networks, CTAT/PTAT Bandgap Cancellation, Thermal Runaway & Schmitt TSD Protection

Formalizes coupled **electro-thermal multiphysics** for silicon integrated circuits and discrete power
stages within `Obend.Hardware`:

1. **Cauer / Foster RC Thermal Networks (`ThermalRCStage`, `ThermalNode`, `steadyStateTempMk`, `stepThermalNode`)**:
   - Models steady-state junction heat flow $T_j = T_{\text{amb}} + P_{\text{diss}} \cdot R_{\text{th},JA}$
     (in millikelvin / millidegrees C, milliwatts, and $\text{mK/mW}$) and discrete-time first-order
     thermal relaxation $T_{k+1} = T_k + \Delta t \cdot (P_{\text{diss}} R_{\text{th}} - (T_k - T_{\text{amb}})) / \tau_{\text{th}}$,
   - Proves `steadyStateTemp_monotone_power` ($P_1 \le P_2 \implies T_{\text{ss}}(P_1) \le T_{\text{ss}}(P_2)$)
     and `thermalRelaxation_bounded` (when $T_0 \le T_{\text{ss}}$ and $0 \le \Delta t \le \tau_{\text{th}}$,
     the relaxed junction temperature satisfies $T_0 \le T_1 \le T_{\text{ss}}$ with zero thermal overshoot).
2. **Temperature-Dependent Semiconductor Physics & Brokaw Bandgap Reference (`evalBandgapRef`)**:
   - Models BJT base-emitter voltage $V_{BE}(T) = V_{BG0} - \alpha_{\text{CTAT}} \cdot \Delta T$
     (Complementary-To-Absolute-Temperature, $\approx -2\,\text{mV/K}$) and thermal voltage difference
     $\Delta V_{BE}(T) = \alpha_{\text{PTAT}} \cdot \Delta T$ (Proportional-To-Absolute-Temperature,
     $\frac{k_B T}{q} \ln N \approx +0.086\,\text{mV/K} \cdot \ln N$),
   - Proves **`bandgap_zero_tempco_cancellation`**: when the PTAT scaling resistor ratio satisfies
     $\alpha_{\text{CTAT}} = K \cdot \alpha_{\text{PTAT}}$, `evalBandgapRef` cancels the temperature
     deviation $\Delta T$ identically to `vbg0` ($1.220\,\text{V}$) across all $\Delta T \in \mathbb{Z}$
     (including the full automotive temperature range $[-40^\circ\text{C}, +125^\circ\text{C}]$).
3. **Electro-Thermal Feedback: Thermal Runaway vs. Emitter-Ballasted BJT Stability (`ElectroThermalBjtSpec`)**:
   - Models positive electro-thermal feedback loop gain $\gamma_{\text{th}} = \frac{\partial P}{\partial T_j} R_{\text{th},JA}$
     in a bipolar power transistor and proves how adding an emitter degeneration ballast resistor $R_E$
     suppresses $\gamma_{\text{th}} < 1$ (`emitter_ballast_stabilizes_thermal_loop` vs
     `unballasted_bjt_thermal_runaway_detected`).
4. **Hysteretic Thermal Shutdown (TSD) Schmitt Protection (`TsdSpec`, `TsdState`, `stepTsdProtection`)**:
   - Models an on-die thermal shutdown Schmitt trigger that trips the power stage off at
     $T_{\text{trip}} = 150^\circ\text{C}$ and only re-enables at $T_{\text{recover}} = 130^\circ\text{C}$,
   - Proves `tsd_cutoff_zeros_power_above_trip` and `tsd_hysteresis_deadband_preserves_state`
     (guaranteeing zero oscillation/chatter inside the $(130^\circ\text{C}, 150^\circ\text{C})$ deadband).
-/
@[expose] public section

namespace Obend.Hardware.Thermal
set_option autoImplicit false

/-! ## 1. Integer Arithmetic Helpers for Multiphysics Monotonicity & Convexity -/

/-- The product of two non-negative integers `a ≥ 0` and `b ≥ 0` is non-negative (`0 ≤ a * b`).
Written via constructor case analysis on `Int` so no external algebra tactics are needed. -/
theorem int_mul_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      exact Int.ofNat_nonneg (m * n)
    | negSucc n => omega
  | negSucc m => omega

/-- For any integer `a : Int`, its square is non-negative (`0 ≤ a * a`). -/
theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases a with
  | ofNat n =>
    exact Int.ofNat_nonneg (n * n)
  | negSucc n =>
    exact Int.ofNat_nonneg (Nat.succ n * Nat.succ n)

/-- Monotonicity of integer multiplication by a non-negative left factor `c ≥ 0`:
if `a ≤ b` and `0 ≤ c`, then `c * a ≤ c * b`. -/
theorem int_mul_le_mul_of_nonneg_left (a b c : Int) (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  have hDiff : 0 ≤ c * (b - a) := int_mul_nonneg c (b - a) hc (by omega)
  have hSplit : a + (b - a) = b := by omega
  have hExpand : c * (a + (b - a)) = c * a + c * (b - a) := Int.mul_add c a (b - a)
  rw [hSplit] at hExpand
  omega

/-- Monotonicity of integer multiplication by a non-negative factor `c ≥ 0`:
if `a ≤ b` and `0 ≤ c`, then `a * c ≤ b * c`. -/
theorem int_mul_le_mul_of_nonneg_right (a b c : Int) (hab : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  rw [Int.mul_comm a c, Int.mul_comm b c]
  exact int_mul_le_mul_of_nonneg_left a b c hab hc

/-! ## 2. Cauer / Foster RC Thermal Network & Transient Relaxation (`ThermalNode`) -/

/-- A single lump in a Cauer or Foster RC thermal equivalent circuit:
* `rThMkPerMw`: thermal resistance $R_{\text{th}}$ in millikelvin per milliwatt ($\text{mK/mW} = \text{K/W}$),
* `cThMjPerK`: thermal capacitance $C_{\text{th}}$ in millijoules per kelvin ($\text{mJ/K}$),
* `tauThMs`: thermal time constant $\tau_{\text{th}} = R_{\text{th}} \cdot C_{\text{th}}$ in milliseconds ($\text{ms}$). -/
structure ThermalRCStage where
  stageName  : String
  rThMkPerMw : Int
  cThMjPerK  : Int
  tauThMs    : Int
  deriving DecidableEq, Repr

/-- Total steady-state junction-to-ambient thermal resistance $R_{\text{th},JA} = \sum_i R_{\text{th},i}$
across a multi-stage Cauer/Foster cascade (e.g., die-to-attach + attach-to-leadframe + leadframe-to-PCB + PCB-to-air). -/
def totalCascadeRth : List ThermalRCStage → Int
  | [] => 0
  | s :: rest => s.rThMkPerMw + totalCascadeRth rest

/-- Dynamic state and parameters of an electro-thermal silicon junction node:
* `tempAmbMk`: ambient temperature $T_{\text{amb}}$ in millidegrees C ($25000 = 25.000^\circ\text{C}$),
* `tempJunctionMk`: current die junction temperature $T_j$ in millidegrees C,
* `rThJaMkPerMw`: junction-to-ambient thermal resistance $R_{\text{th},JA}$ ($\text{mK/mW}$),
* `tauThMs`: dominant thermal time constant $\tau_{\text{th}}$ ($\text{ms}$),
* `maxSafeTjMk`: maximum rated junction temperature ($125000 = 125.000^\circ\text{C}$ industrial,
  $150000 = 150.000^\circ\text{C}$ automotive Grade 0). -/
structure ThermalNode where
  nodeName       : String
  tempAmbMk      : Int
  tempJunctionMk : Int
  rThJaMkPerMw   : Int
  tauThMs        : Int
  maxSafeTjMk    : Int
  deriving DecidableEq, Repr

/-- Steady-state junction temperature $T_{\text{ss}} = T_{\text{amb}} + P_{\text{diss}} \cdot R_{\text{th},JA}$
(in millidegrees C) for constant power dissipation `powerMw` ($\text{mW}$). -/
def steadyStateTempMk (tempAmbMk powerMw rThJaMkPerMw : Int) : Int :=
  tempAmbMk + powerMw * rThJaMkPerMw

/-- Theorem (`steadyStateTemp_monotone_power`):
For any ambient temperature `tempAmbMk` and non-negative thermal resistance `0 ≤ rThJa`,
increasing dissipated power `p1 ≤ p2` monotonically increases steady-state junction temperature:
$T_{\text{ss}}(P_1) \le T_{\text{ss}}(P_2)$. -/
theorem steadyStateTemp_monotone_power
    (tempAmbMk p1 p2 rThJa : Int)
    (hPower : p1 ≤ p2)
    (hRth : 0 ≤ rThJa) :
    steadyStateTempMk tempAmbMk p1 rThJa ≤ steadyStateTempMk tempAmbMk p2 rThJa := by
  dsimp only [steadyStateTempMk]
  have hMul := int_mul_le_mul_of_nonneg_right p1 p2 rThJa hPower hRth
  omega

/-- Scaled discrete-time first-order thermal relaxation numerator:
$\tau_{\text{th}} \cdot T_{k+1} = (\tau_{\text{th}} - \Delta t) \cdot T_k + \Delta t \cdot T_{\text{ss}}$,
which represents the exact convex combination of current junction temperature $T_k$ and steady-state
target $T_{\text{ss}} = T_{\text{amb}} + P_{\text{diss}} R_{\text{th},JA}$ over time step $\Delta t \in [0, \tau_{\text{th}}]$. -/
def stepThermalScaled (tempCurMk tempAmbMk powerMw rThJa dtMs tauMs : Int) : Int :=
  (tauMs - dtMs) * tempCurMk + dtMs * steadyStateTempMk tempAmbMk powerMw rThJa

/-- Discrete-time forward-Euler thermal relaxation step on a `ThermalNode`:
$T_{k+1} = T_k + \frac{\Delta t \cdot ((T_{\text{amb}} + P_{\text{diss}} R_{\text{th},JA}) - T_k)}{\tau_{\text{th}}}$. -/
def stepThermalNode (node : ThermalNode) (powerMw dtMs : Int) : ThermalNode :=
  let tSs := steadyStateTempMk node.tempAmbMk powerMw node.rThJaMkPerMw
  let nextTj := node.tempJunctionMk + (dtMs * (tSs - node.tempJunctionMk)) / node.tauThMs
  { node with tempJunctionMk := nextTj }

/-- Theorem (`thermalRelaxation_bounded`):
When a junction starts below or at its steady-state equilibrium ($T_0 \le T_{\text{ss}}$) and the
integration time step obeys the explicit stability condition $0 \le \Delta t \le \tau_{\text{th}}$,
one step of thermal relaxation is bounded both below by $T_0$ and above by $T_{\text{ss}}$:
$$\tau_{\text{th}} \cdot T_0 \le \text{stepThermalScaled}(T_0, T_{\text{amb}}, P, R_{\text{th}}, \Delta t, \tau_{\text{th}}) \le \tau_{\text{th}} \cdot T_{\text{ss}}.$$
In particular, passive RC heat flow never overshoots $T_{\text{ss}}$! -/
theorem thermalRelaxation_bounded
    (tempCurMk tempAmbMk powerMw rThJa dtMs tauMs : Int)
    (hBelowSs : tempCurMk ≤ steadyStateTempMk tempAmbMk powerMw rThJa)
    (hDtNonneg : 0 ≤ dtMs)
    (hDtLeTau  : dtMs ≤ tauMs) :
    tauMs * tempCurMk ≤ stepThermalScaled tempCurMk tempAmbMk powerMw rThJa dtMs tauMs ∧
    stepThermalScaled tempCurMk tempAmbMk powerMw rThJa dtMs tauMs ≤
      tauMs * steadyStateTempMk tempAmbMk powerMw rThJa := by
  dsimp only [stepThermalScaled]
  have h1 : dtMs * tempCurMk ≤ dtMs * steadyStateTempMk tempAmbMk powerMw rThJa :=
    int_mul_le_mul_of_nonneg_left tempCurMk (steadyStateTempMk tempAmbMk powerMw rThJa) dtMs hBelowSs hDtNonneg
  have h2 : (tauMs - dtMs) * tempCurMk ≤ (tauMs - dtMs) * steadyStateTempMk tempAmbMk powerMw rThJa :=
    int_mul_le_mul_of_nonneg_left tempCurMk (steadyStateTempMk tempAmbMk powerMw rThJa) (tauMs - dtMs) hBelowSs (by omega)
  have hSplitTau : (tauMs - dtMs) + dtMs = tauMs := by omega
  have hIdCur : tempCurMk * ((tauMs - dtMs) + dtMs) = tempCurMk * (tauMs - dtMs) + tempCurMk * dtMs :=
    Int.mul_add tempCurMk (tauMs - dtMs) dtMs
  rw [hSplitTau, Int.mul_comm tempCurMk tauMs, Int.mul_comm tempCurMk (tauMs - dtMs), Int.mul_comm tempCurMk dtMs] at hIdCur
  have hIdSs : steadyStateTempMk tempAmbMk powerMw rThJa * ((tauMs - dtMs) + dtMs) =
      steadyStateTempMk tempAmbMk powerMw rThJa * (tauMs - dtMs) + steadyStateTempMk tempAmbMk powerMw rThJa * dtMs :=
    Int.mul_add (steadyStateTempMk tempAmbMk powerMw rThJa) (tauMs - dtMs) dtMs
  rw [hSplitTau, Int.mul_comm (steadyStateTempMk tempAmbMk powerMw rThJa) tauMs,
      Int.mul_comm (steadyStateTempMk tempAmbMk powerMw rThJa) (tauMs - dtMs),
      Int.mul_comm (steadyStateTempMk tempAmbMk powerMw rThJa) dtMs] at hIdSs
  refine ⟨by omega, by omega⟩

/-! ## 3. Semiconductor CTAT vs PTAT Physics & Brokaw Bandgap Reference (`evalBandgapRef`) -/

/-- BJT base-emitter forward voltage $V_{BE}(T) = V_{BG0} - \alpha_{\text{CTAT}} \cdot \Delta T$
(in microvolts $\mu\text{V}$), where:
* `vbg0Uv`: extrapolated $0\,\text{K}$ / reference silicon bandgap voltage ($\approx 1220000\,\mu\text{V}$),
* `alphaCtatUvPerK`: Complementary-To-Absolute-Temperature slope ($\approx 2000\,\mu\text{V/K} = 2\,\text{mV/K}$),
* `deltaTK`: temperature excursion $T - T_0$ (in kelvin / degrees C). -/
def evalBjtVbeUv (vbg0Uv alphaCtatUvPerK deltaTK : Int) : Int :=
  vbg0Uv - alphaCtatUvPerK * deltaTK

/-- Differential BJT thermal voltage $\Delta V_{BE}(T) = V_{PTAT0} + \alpha_{\text{PTAT}} \cdot \Delta T$
generated across two bipolar transistors operating at collector current density ratio $N : 1$
($\Delta V_{BE} = \frac{k_B T}{q} \ln N$, with slope $\alpha_{\text{PTAT}} = \frac{k_B}{q} \ln N \approx 86.17\,\mu\text{V/K} \cdot \ln N$). -/
def evalPtatDeltaVbeUv (vPtat0Uv alphaPtatUvPerK deltaTK : Int) : Int :=
  vPtat0Uv + alphaPtatUvPerK * deltaTK

/-- Brokaw / Widlar bandgap voltage reference output (in $\mu\text{V}$):
$$V_{\text{ref}}(T) = \underbrace{(V_{BG0} - \alpha_{\text{CTAT}} \cdot \Delta T)}_{V_{BE,\text{CTAT}}} + K \cdot \underbrace{(\alpha_{\text{PTAT}} \cdot \Delta T)}_{\Delta V_{BE,\text{PTAT}}}.$$ -/
def evalBandgapRef (vbg0 alphaCtat alphaPtat weightK _temp deltaT : Int) : Int :=
  (vbg0 - alphaCtat * deltaT) + weightK * (alphaPtat * deltaT)

/-- Theorem (`bandgap_zero_tempco_cancellation`):
When the PTAT gain resistor ratio `weightK` satisfies `alphaCtat = weightK * alphaPtat`
(e.g., $\alpha_{\text{CTAT}} = 2000\,\mu\text{V/K}$, $\alpha_{\text{PTAT}} = 200\,\mu\text{V/K}$, $K = 10$),
the negative CTAT slope of $V_{BE}$ and the amplified positive PTAT slope of $\Delta V_{BE}$ cancel
identically, yielding `evalBandgapRef vbg0 alphaCtat alphaPtat weightK temp deltaT = vbg0`
for EVERY temperature excursion `deltaT : Int`!
Written without `simp` auxiliary constants so `#tooth` can directly mutate `evalBandgapRef`. -/
theorem bandgap_zero_tempco_cancellation
    (vbg0 alphaCtat alphaPtat weightK temp deltaT : Int)
    (hCancel : alphaCtat = weightK * alphaPtat) :
    evalBandgapRef vbg0 alphaCtat alphaPtat weightK temp deltaT = vbg0 := by
  dsimp only [evalBandgapRef]
  have hMul : weightK * (alphaPtat * deltaT) = alphaCtat * deltaT := by
    rw [← Int.mul_assoc, ← hCancel]
  rw [hMul]
  omega

/-- Theorem (`ctat_and_ptat_opposing_slopes`):
For positive temperature coefficients `0 ≤ alphaCtat` and `0 ≤ alphaPtat`, increasing temperature
`dt1 ≤ dt2` decreases $V_{BE}$ (CTAT) while increasing $\Delta V_{BE}$ (PTAT). -/
theorem ctat_and_ptat_opposing_slopes
    (vbg0 vPtat0 alphaCtat alphaPtat dt1 dt2 : Int)
    (hTemp : dt1 ≤ dt2)
    (hCtat : 0 ≤ alphaCtat)
    (hPtat : 0 ≤ alphaPtat) :
    evalBjtVbeUv vbg0 alphaCtat dt2 ≤ evalBjtVbeUv vbg0 alphaCtat dt1 ∧
    evalPtatDeltaVbeUv vPtat0 alphaPtat dt1 ≤ evalPtatDeltaVbeUv vPtat0 alphaPtat dt2 := by
  dsimp only [evalBjtVbeUv, evalPtatDeltaVbeUv]
  have h1 := int_mul_le_mul_of_nonneg_left dt1 dt2 alphaCtat hTemp hCtat
  have h2 := int_mul_le_mul_of_nonneg_left dt1 dt2 alphaPtat hTemp hPtat
  refine ⟨by omega, by omega⟩

/-! ## 4. Electro-Thermal Feedback: Thermal Runaway vs. Emitter-Ballasted Stability -/

/-- Coupled electro-thermal specification of a bipolar power stage (e.g., HF RF Power Amplifier or
linear pass transistor):
* `vceMv`: collector-emitter supply voltage $V_{CE}$ ($\text{mV}$),
* `ic0Ma`: quiescent collector bias current $I_{C0}$ ($\text{mA}$),
* `dIcDtUaPerK`: unballasted collector current thermal sensitivity $\frac{\partial I_C}{\partial T_j}\big|_{R_E=0}$ ($\mu\text{A/K}$),
* `rThJaKPerW`: junction-to-ambient thermal resistance $R_{\text{th},JA}$ ($\text{K/W}$),
* `rBallastMohm`: emitter degeneration ballast resistance $R_E$ ($\text{m}\Omega$).
Without emitter ballasting ($R_E = 0$), heating increases $I_C$, which increases $P = V_{CE} I_C$,
which further heats the junction. Thermal runaway occurs when the open-loop thermal gain exceeds $1$:
$$\gamma_{\text{th}} = \frac{V_{CE} \cdot (\partial I_C / \partial T_j) \cdot R_{\text{th},JA}}{1 + R_E \cdot g_{\text{ballast}}} \ge 1.$$ -/
structure ElectroThermalBjtSpec where
  stageName    : String
  vceMv        : Int
  ic0Ma        : Int
  dIcDtUaPerK  : Int
  rThJaKPerW   : Int
  rBallastMohm : Int
  deriving DecidableEq, Repr

/-- Unballasted thermal power-temperature product numerator $V_{CE,\text{mV}} \cdot (\partial I_C / \partial T_j)_{\mu\text{A/K}} \cdot R_{\text{th},JA}$
(in $\text{nW/K} \cdot \text{K/W} = 10^{-9}$ units; threshold for unity loop gain at $R_E = 0$ is $10^9$). -/
def thermalLoopNum (spec : ElectroThermalBjtSpec) : Int :=
  spec.vceMv * spec.dIcDtUaPerK * spec.rThJaKPerW

/-- Emitter-ballast negative-feedback denominator $10^9 + R_{E,\text{m}\Omega} \cdot (\partial I_C / \partial T_j)_{\mu\text{A/K}} \cdot 500$
(representing local negative feedback $1 + g_m R_E$ that opposes thermal current growth). -/
def thermalLoopDenom (spec : ElectroThermalBjtSpec) : Int :=
  1000000000 + spec.rBallastMohm * spec.dIcDtUaPerK * 500

/-- Electro-thermal loop gain $\gamma_{\text{th}}$ in per-mille ($\text{permille}$, where $1000 = 1.0$ unity loop gain).
Thermal stability requires $\gamma_{\text{th}} < 1000$; $\gamma_{\text{th}} \ge 1000$ triggers positive-feedback
thermal runaway and second breakdown! -/
def evalThermalLoopGainPermille (spec : ElectroThermalBjtSpec) : Int :=
  (1000 * thermalLoopNum spec) / thermalLoopDenom spec

/-- Check that an electro-thermal BJT stage is protected against thermal runaway:
requires positive emitter ballasting (`rBallastMohm > 0`) and strict contraction of the coupled
electro-thermal feedback loop (`thermalLoopNum spec < thermalLoopDenom spec`, i.e., $\gamma_{\text{th}} < 1$). -/
def checkThermalLoopStable (spec : ElectroThermalBjtSpec) : Bool :=
  decide (0 < spec.rBallastMohm) &&
  decide (0 < thermalLoopDenom spec) &&
  decide (thermalLoopNum spec < thermalLoopDenom spec)

/-- Canonical unballasted power BJT (`Vce = 12V`, `dIc/dT = 4 mA/K`, `Rth = 30 K/W`, `Re = 0 mOhm`):
suffers loop gain $\gamma_{\text{th}} = 1440\,\text{permille} = 1.44 \ge 1.0$ (thermal runaway!). -/
def unballastedPowerBjt : ElectroThermalBjtSpec where
  stageName    := "pa_bjt_unballasted"
  vceMv        := 12000
  ic0Ma        := 500
  dIcDtUaPerK  := 4000
  rThJaKPerW   := 30
  rBallastMohm := 0

/-- Canonical emitter-ballasted power BJT (`Vce = 12V`, `dIc/dT = 4 mA/K`, `Rth = 30 K/W`, `Re = 500 mOhm`):
emitter degeneration reduces loop gain to $\gamma_{\text{th}} = 720\,\text{permille} = 0.72 < 1.0$ (thermally stable!). -/
def emitterBallastedPowerBjt : ElectroThermalBjtSpec where
  stageName    := "pa_bjt_ballasted_0r5"
  vceMv        := 12000
  ic0Ma        := 500
  dIcDtUaPerK  := 4000
  rThJaKPerW   := 30
  rBallastMohm := 500

/-- Theorem (`unballasted_bjt_thermal_runaway_detected`):
The unballasted power BJT stage has loop gain $1440 \ge 1000$ and is refused by `checkThermalLoopStable`. -/
theorem unballasted_bjt_thermal_runaway_detected :
    evalThermalLoopGainPermille unballastedPowerBjt = 1440 ∧
    checkThermalLoopStable unballastedPowerBjt = false :=
  ⟨rfl, rfl⟩

/-- Theorem (`emitter_ballast_stabilizes_thermal_loop`):
Adding a $0.5\,\Omega$ ($500\,\text{m}\Omega$) emitter ballast resistor reduces the electro-thermal
loop gain from $1440$ to $720 < 1000$ and passes `checkThermalLoopStable`! -/
theorem emitter_ballast_stabilizes_thermal_loop :
    evalThermalLoopGainPermille emitterBallastedPowerBjt = 720 ∧
    checkThermalLoopStable emitterBallastedPowerBjt = true :=
  ⟨rfl, rfl⟩

/-- Theorem (`ballast_monotonically_increases_feedback_denom`):
Increasing the emitter ballast resistance `r1 ≤ r2` for a stage with `0 ≤ dIcDtUaPerK` monotonically
increases the negative-feedback denominator `thermalLoopDenom`. -/
theorem ballast_monotonically_increases_feedback_denom
    (s1 s2 : ElectroThermalBjtSpec)
    (hSameSens : s1.dIcDtUaPerK = s2.dIcDtUaPerK)
    (hSensPos  : 0 ≤ s2.dIcDtUaPerK)
    (hBallast  : s1.rBallastMohm ≤ s2.rBallastMohm) :
    thermalLoopDenom s1 ≤ thermalLoopDenom s2 := by
  dsimp only [thermalLoopDenom]
  rw [hSameSens]
  have hMul1 := int_mul_le_mul_of_nonneg_right s1.rBallastMohm s2.rBallastMohm s2.dIcDtUaPerK hBallast hSensPos
  omega

/-! ## 5. Hysteretic Thermal Shutdown (TSD) Schmitt Protection (`TsdSpec`, `TsdState`, `stepTsdProtection`) -/

/-- Threshold parameters of an on-die Hysteretic Thermal Shutdown (TSD) Schmitt comparator:
* `tRecoverMk`: lower recovery threshold ($130000 = 130.0^\circ\text{C}$),
* `tTripMk`: upper trip cutoff threshold ($150000 = 150.0^\circ\text{C}$), with $T_{\text{recover}} < T_{\text{trip}}$. -/
structure TsdSpec where
  tRecoverMk : Int
  tTripMk    : Int
  deriving DecidableEq, Repr

/-- Standard automotive/industrial TSD protection specification ($T_{\text{trip}} = 150^\circ\text{C}$,
$T_{\text{recover}} = 130^\circ\text{C}$, $20^\circ\text{C}$ Schmitt hysteresis window). -/
def standardTsdSpec : TsdSpec where
  tRecoverMk := 130000
  tTripMk    := 150000

/-- State of the hysteretic Thermal Shutdown (TSD) latch. -/
structure TsdState where
  stageEnabled : Bool
  tripCount    : Nat
  deriving DecidableEq, Repr

/-- Step the hysteretic TSD protection circuit at measured junction temperature `tjMk`:
* If `tjMk ≥ spec.tTripMk`, immediately disables the power stage (`stageEnabled := false`) and increments `tripCount`,
* Else if `tjMk ≤ spec.tRecoverMk`, re-enables the power stage (`stageEnabled := true`),
* Otherwise (`tRecoverMk < tjMk < tTripMk`), holds the current state `st` without chattering! -/
def stepTsdProtection (spec : TsdSpec) (st : TsdState) (tjMk : Int) : TsdState :=
  if spec.tTripMk ≤ tjMk then
    { stageEnabled := false
    , tripCount    := if st.stageEnabled then st.tripCount + 1 else st.tripCount }
  else if tjMk ≤ spec.tRecoverMk then
    { st with stageEnabled := true }
  else
    st

/-- Gated power dissipation (in mW) after the TSD protection switch: `0` when tripped off. -/
def effectiveStagePowerMw (st : TsdState) (requestedPowerMw : Int) : Int :=
  if st.stageEnabled then requestedPowerMw else 0

/-- Theorem (`tsd_cutoff_zeros_power_above_trip`):
Whenever the junction temperature reaches or exceeds the trip point (`spec.tTripMk ≤ tjMk`),
`stepTsdProtection` immediately forces `stageEnabled = false` and cuts dissipated stage power to `0`! -/
theorem tsd_cutoff_zeros_power_above_trip
    (spec : TsdSpec) (st : TsdState) (tjMk requestedPowerMw : Int)
    (hOvertemp : spec.tTripMk ≤ tjMk) :
    (stepTsdProtection spec st tjMk).stageEnabled = false ∧
    effectiveStagePowerMw (stepTsdProtection spec st tjMk) requestedPowerMw = 0 := by
  dsimp only [stepTsdProtection, effectiveStagePowerMw]
  rw [if_pos hOvertemp]
  exact ⟨rfl, rfl⟩

/-- Theorem (`tsd_hysteresis_deadband_preserves_state`):
For any junction temperature strictly inside the Schmitt hysteresis deadband
(`spec.tRecoverMk < tjMk` and `tjMk < spec.tTripMk`), `stepTsdProtection` preserves `st` unchanged,
preventing thermal relay/MOSFET limit-cycle chatter around the trip threshold! -/
theorem tsd_hysteresis_deadband_preserves_state
    (spec : TsdSpec) (st : TsdState) (tjMk : Int)
    (hAboveRec  : spec.tRecoverMk < tjMk)
    (hBelowTrip : tjMk < spec.tTripMk) :
    stepTsdProtection spec st tjMk = st := by
  dsimp only [stepTsdProtection]
  have hNotTrip : ¬ (spec.tTripMk ≤ tjMk) := by omega
  have hNotRec  : ¬ (tjMk ≤ spec.tRecoverMk) := by omega
  rw [if_neg hNotTrip, if_neg hNotRec]

/-- Theorem (`tsd_recovery_reenables_below_recover`):
When the junction cools to or below `spec.tRecoverMk` (with `spec.tRecoverMk < spec.tTripMk`),
`stepTsdProtection` cleanly re-enables the power stage (`stageEnabled = true`). -/
theorem tsd_recovery_reenables_below_recover
    (spec : TsdSpec) (st : TsdState) (tjMk : Int)
    (hValidWindow : spec.tRecoverMk < spec.tTripMk)
    (hCooled      : tjMk ≤ spec.tRecoverMk) :
    (stepTsdProtection spec st tjMk).stageEnabled = true := by
  dsimp only [stepTsdProtection]
  have hNotTrip : ¬ (spec.tTripMk ≤ tjMk) := by omega
  rw [if_neg hNotTrip, if_pos hCooled]

/-! ## 6. Temperature-Dependent Copper TCR Joule Heating & Thermal Runaway vs. Equilibrium Dichotomy -/

/-- Evaluates temperature-dependent copper Joule heating power (in permille-scaled units)
with positive Temperature Coefficient of Resistance (TCR) $\alpha_{\text{permille}}$:
$$P_{\text{Cu}}(I, T) = I^2 R_0 \left(1000 + \alpha_{\text{permille}} (T - T_0)\right).$$ -/
def evalCopperJouleHeatingTcr
    (iAmp r0Mohm alphaPermille tRef tCur : Int) : Int :=
  (iAmp * iAmp * r0Mohm) * (1000 + alphaPermille * (tCur - tRef))

/-- Evaluates the positive-feedback electro-thermal copper Joule heating slope
$$\beta_{\text{Cu}} = \frac{\partial P_{\text{Cu}}}{\partial T} = I^2 R_0 \alpha_{\text{permille}}.$$ -/
def evalCopperJouleSlope
    (iAmp r0Mohm alphaPermille : Int) : Int :=
  (iAmp * iAmp * r0Mohm) * alphaPermille

/-- Evaluates microchannel convective heat removal rate:
$$Q_{\text{cool}}(T) = G_{\text{th}} (T - T_{\text{coolant}}).$$ -/
def evalConvectiveHeatRemoval (gTh tCoolant tCur : Int) : Int :=
  gTh * (tCur - tCoolant)

/-- Discrete-time coupled electro-thermal state transition map:
$$T_{k+1} = T_k + \Delta t \left(P_{\text{Cu}}(I, T_k) + P_{\text{core}} + P_{\text{inv}} - Q_{\text{cool}}(T_k)\right).$$ -/
def stepCoupledElectroThermalMap
    (iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tCur : Int) : Int :=
  tCur + dt * (evalCopperJouleHeatingTcr iAmp r0Mohm alphaPermille tRef tCur + pCore + pInv -
               evalConvectiveHeatRemoval gTh tCoolant tCur)

/-- Monotonicity of copper Joule heating with temperature under positive TCR (`0 ≤ r0Mohm`, `0 ≤ alphaPermille`). -/
theorem copperJouleHeatingTcr_monotone_temp
    (iAmp r0Mohm alphaPermille tRef t1 t2 : Int)
    (hR0 : 0 ≤ r0Mohm) (hAlpha : 0 ≤ alphaPermille) (hTemp : t1 ≤ t2) :
    evalCopperJouleHeatingTcr iAmp r0Mohm alphaPermille tRef t1 ≤
      evalCopperJouleHeatingTcr iAmp r0Mohm alphaPermille tRef t2 := by
  dsimp only [evalCopperJouleHeatingTcr]
  have hIsq : 0 ≤ iAmp * iAmp := int_sq_nonneg iAmp
  have hI2R : 0 ≤ iAmp * iAmp * r0Mohm := int_mul_nonneg (iAmp * iAmp) r0Mohm hIsq hR0
  have hAlphaDiff : alphaPermille * (t1 - tRef) ≤ alphaPermille * (t2 - tRef) :=
    int_mul_le_mul_of_nonneg_left (t1 - tRef) (t2 - tRef) alphaPermille (by omega) hAlpha
  exact int_mul_le_mul_of_nonneg_left
    (1000 + alphaPermille * (t1 - tRef))
    (1000 + alphaPermille * (t2 - tRef))
    (iAmp * iAmp * r0Mohm)
    (by omega)
    hI2R

/-- **Exact Algebraic Perturbation Identity for the Coupled Electro-Thermal Map (`electroThermal_step_diff_identity`)**:
For any two operating temperatures $T_1, T_2 \in \mathbb{Z}$ (in particular $T_2 = T^\star$ at steady state),
the constant heat loads $P_{\text{core}}$, $P_{\text{inv}}$, $1000 I^2 R_0$, and reference temperatures
$T_0, T_{\text{coolant}}$ cancel identically, leaving:
$$\text{step}(T_1) - \text{step}(T_2) = (T_1 - T_2) - \Delta t \cdot \left(G_{\text{th}} - I^2 R_0 \alpha_{\text{permille}}\right) (T_1 - T_2).$$ -/
theorem electroThermal_step_diff_identity
    (iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 t2 : Int) :
    stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2 =
    (t1 - t2) - dt * (gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille) * (t1 - t2) := by
  dsimp only [stepCoupledElectroThermalMap, evalCopperJouleHeatingTcr,
              evalConvectiveHeatRemoval, evalCopperJouleSlope]
  grind

/-- **Explicit-Euler contraction with its step-size condition (`electroThermal_explicit_euler_contracts`)**:
the one-step map on temperature differences is `(1 − dt·(G − β))·(T₁ − T₂)`
(`electroThermal_step_diff_identity`), so it is a *contraction* iff `0 < dt·(G − β) < 2`. The dichotomy
theorem below only states `step(T₁) − step(T₂) < T₁ − T₂`, which also holds when `dt·(G − β) ≥ 2` and
the iteration oscillates and diverges; this theorem is the two-sided statement a discrete-time
stability claim needs. -/
theorem electroThermal_explicit_euler_contracts
    (iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 t2 : Int)
    (hLo : 0 < dt * (gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille))
    (hHi : dt * (gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille) < 2)
    (hOrder : t2 < t1) :
    -(t1 - t2) <
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2 ∧
    stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2 <
      t1 - t2 := by
  have hId := electroThermal_step_diff_identity iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 t2
  rw [hId]
  have hDiffPos : 0 < t1 - t2 := by omega
  -- 0 < k < 2 with k = dt·(G − β): 0 < k·(t1 − t2) < 2·(t1 − t2)
  have hk1 : 0 < dt * (gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille) * (t1 - t2) :=
    Int.mul_pos hLo hDiffPos
  have hk2 : dt * (gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille) * (t1 - t2) < 2 * (t1 - t2) :=
    Int.mul_lt_mul_of_pos_right hHi hDiffPos
  constructor <;> omega

/-- **Thermal Runaway vs. Stable Equilibrium Dichotomy Theorem (`electroThermal_equilibrium_stability_dichotomy`)**
(one-sided; see `electroThermal_explicit_euler_contracts` for the two-sided contraction):
For any positive integration time step $\Delta t > 0$ and any ordered temperature pair $T_2 < T_1$
(such as $T_1 > T^\star$ above steady-state equilibrium $T_2 = T^\star$):
1. **Stable Equilibrium Contraction ($G_{\text{th}} > I^2 R_0 \alpha_{\text{permille}}$)**:
   When microchannel convective thermal conductance strictly exceeds the positive-feedback copper TCR
   Joule heating slope (`evalCopperJouleSlope iAmp r0Mohm alphaPermille < gTh`), the temperature
   deviation strictly contracts in one step (`step(T1) - step(T2) < T1 - T2`), and if $T_2 = T^\star$ is
   a steady-state fixed point (`step(T*) = T*`), the excess temperature above equilibrium strictly decreases
   (`step(T1) - T* < T1 - T*`).
2. **Thermal Runaway Divergence ($G_{\text{th}} < I^2 R_0 \alpha_{\text{permille}}$)**:
   Conversely, when convective thermal conductance is strictly below the copper TCR Joule heating slope
   (`gTh < evalCopperJouleSlope iAmp r0Mohm alphaPermille`), the temperature deviation grows strictly
   monotonically (`T1 - T2 < step(T1) - step(T2)`), causing positive-feedback thermal runaway!
3. **Neutral Boundary Invariance ($G_{\text{th}} = I^2 R_0 \alpha_{\text{permille}}$)**:
   At the exact neutral threshold `gTh = evalCopperJouleSlope iAmp r0Mohm alphaPermille`, the
   temperature perturbation is invariant (`step(T1) - step(T2) = T1 - T2`). -/
theorem electroThermal_equilibrium_stability_dichotomy
    (iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 t2 : Int)
    (hDt : 0 < dt)
    (hOrder : t2 < t1) :
    (evalCopperJouleSlope iAmp r0Mohm alphaPermille < gTh →
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2 <
      t1 - t2) ∧
    (gTh < evalCopperJouleSlope iAmp r0Mohm alphaPermille →
      t1 - t2 <
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2) ∧
    (gTh = evalCopperJouleSlope iAmp r0Mohm alphaPermille →
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 -
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t2 =
      t1 - t2) := by
  have hId := electroThermal_step_diff_identity
    iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt t1 t2
  have hDiffPos : 0 < t1 - t2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro hStable
    have hMarginPos : 0 < gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille := by omega
    have hDtMargin : 0 < dt * (gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille) :=
      Int.mul_pos hDt hMarginPos
    have hDampPos : 0 < dt * (gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille) * (t1 - t2) :=
      Int.mul_pos hDtMargin hDiffPos
    omega
  · intro hRunaway
    have hDeficitPos : 0 < evalCopperJouleSlope iAmp r0Mohm alphaPermille - gTh := by omega
    have hDtDeficit : 0 < dt * (evalCopperJouleSlope iAmp r0Mohm alphaPermille - gTh) :=
      Int.mul_pos hDt hDeficitPos
    have hAmpPos : 0 < dt * (evalCopperJouleSlope iAmp r0Mohm alphaPermille - gTh) * (t1 - t2) :=
      Int.mul_pos hDtDeficit hDiffPos
    have hNegExpand :
        dt * (gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille) * (t1 - t2) +
        dt * (evalCopperJouleSlope iAmp r0Mohm alphaPermille - gTh) * (t1 - t2) = 0 := by
      grind
    omega
  · intro hNeutral
    have hZeroMargin : gTh - evalCopperJouleSlope iAmp r0Mohm alphaPermille = 0 := by omega
    rw [hZeroMargin, Int.mul_zero, Int.zero_mul] at hId
    omega

/-- **Uniqueness of Steady-State Operating Temperature $T^\star$ & Fixed-Point Excess Contraction
(`electroThermal_steady_state_unique_and_contraction`)**:
For any positive time step $\Delta t > 0$:
1. Whenever $G_{\text{th}} \ne I^2 R_0 \alpha_{\text{permille}}$ (in particular whenever
   $G_{\text{th}} > I^2 R_0 \alpha_{\text{permille}}$), the steady-state equilibrium temperature
   $T^\star$ satisfying $\text{step}(T^\star) = T^\star$ is **unique** ($T_1^\star = T_2^\star$).
2. At any steady-state equilibrium $T^\star$ ($\text{step}(T^\star) = T^\star$) and perturbed
   temperature $T > T^\star$, excess temperature $T - T^\star$ strictly contracts toward $T^\star$
   when $G_{\text{th}} > I^2 R_0 \alpha_{\text{permille}}$ and strictly diverges (thermal runaway)
   when $G_{\text{th}} < I^2 R_0 \alpha_{\text{permille}}$. -/
theorem electroThermal_steady_state_unique_and_contraction
    (iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar1 tStar2 tCur : Int)
    (hDt : 0 < dt)
    (hFix1 : stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar1 = tStar1) :
    (evalCopperJouleSlope iAmp r0Mohm alphaPermille ≠ gTh →
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar2 = tStar2 →
      tStar1 = tStar2) ∧
    (tStar1 < tCur →
      evalCopperJouleSlope iAmp r0Mohm alphaPermille < gTh →
      stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tCur - tStar1 <
        tCur - tStar1) ∧
    (tStar1 < tCur →
      gTh < evalCopperJouleSlope iAmp r0Mohm alphaPermille →
      tCur - tStar1 <
        stepCoupledElectroThermalMap iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tCur - tStar1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hNe hFix2
    have hTri : tStar1 = tStar2 ∨ tStar2 < tStar1 ∨ tStar1 < tStar2 := by omega
    rcases hTri with hEq | hGt | hLt
    · exact hEq
    · have hDich := electroThermal_equilibrium_stability_dichotomy
        iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar1 tStar2 hDt hGt
      rw [hFix1, hFix2] at hDich
      have hSlopeOrder : evalCopperJouleSlope iAmp r0Mohm alphaPermille < gTh ∨
                         gTh < evalCopperJouleSlope iAmp r0Mohm alphaPermille := by omega
      rcases hSlopeOrder with hS | hR
      · have h1 := hDich.1 hS; omega
      · have h2 := hDich.2.1 hR; omega
    · have hDich := electroThermal_equilibrium_stability_dichotomy
        iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tStar2 tStar1 hDt hLt
      rw [hFix1, hFix2] at hDich
      have hSlopeOrder : evalCopperJouleSlope iAmp r0Mohm alphaPermille < gTh ∨
                         gTh < evalCopperJouleSlope iAmp r0Mohm alphaPermille := by omega
      rcases hSlopeOrder with hS | hR
      · have h1 := hDich.1 hS; omega
      · have h2 := hDich.2.1 hR; omega
  · intro hOrder hStable
    have hDich := (electroThermal_equilibrium_stability_dichotomy
      iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tCur tStar1 hDt hOrder).1 hStable
    rw [hFix1] at hDich
    exact hDich
  · intro hOrder hRunaway
    have hDich := (electroThermal_equilibrium_stability_dichotomy
      iAmp r0Mohm alphaPermille tRef pCore pInv gTh tCoolant dt tCur tStar1 hDt hOrder).2.1 hRunaway
    rw [hFix1] at hDich
    exact hDich

end Obend.Hardware.Thermal


