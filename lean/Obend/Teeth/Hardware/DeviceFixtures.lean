module
/-
# Obend.Teeth.Hardware.DeviceFixtures — the sky130 diode certificates, checked; the dose-change refusal

Tier 2. The bytes are devsim's (`Obend/Teeth/Hardware/DeviceCertificates.lean`, generated from
`apps/sky130-diode/certs/`); the checker is `Obend.Hardware.Device.checkDd` through the format's
decoders, run as compiled code (`native_decide`; the format's trust is `.compiled`).

Device A: the recipe of `Obend.Hardware.Device.Sky130Diode` at p-well dose `1.3·10¹³ cm⁻²`;
device B: the same at `2.6·10¹³`. One mesh of 180 nodes for both, so that a certificate of A can be
judged on B. devsim's forward currents (A/cm², at the n⁺ contact, negative is forward):

| bias | A (1.3e13) | B (2.6e13) |
|---|---|---|
| −0.30 V | 1.85·10⁻⁶ | 8.80·10⁻⁷ |
| −0.50 V | 4.19·10⁻³ | 1.54·10⁻³ |
| −0.60 V | 2.00·10⁻¹ | 7.36·10⁻² |
| −0.70 V | 9.51 | 3.51 |
| +1.00 V | −3.0·10⁻⁷ (reverse) | +2.9·10⁻⁷ (reverse, at the rounding floor) |

The certified current bound (`terminal_current_bound`) at `tolRel = 10⁻¹²` is `0.030 A/cm²` for both
devices: it pins the current to 0.3 % at −0.7 V, 15 % at −0.6 V, and says nothing below −0.55 V
(the budget is the rounding floor of the Scharfetter–Gummel terms at the `10²⁰ cm⁻³` contact,
`~3·10¹⁰ A/cm²` per node, times the tolerance; a scaled formulation is the next brief's item).
-/
public import Obend.Hardware.Device.Sky130Diode
public import Obend.Teeth.Hardware.DeviceCertificates
public import Lean
meta import Lean
public meta import Obend.Analysis.RealAnalysis
public meta import Obend.Judge.Class
public meta import Obend.Hardware.Device.Enclosure
public meta import Obend.Hardware.Device.Constants
public meta import Obend.Hardware.Device.Wafer
public meta import Obend.Hardware.Device.DriftDiffusion
public meta import Obend.Hardware.Device.Sky130Diode
public meta import Obend.Teeth.Hardware.DeviceCertificates
public section

namespace Obend.Teeth.Hardware.DeviceFixtures
open Obend.Hardware.Device Obend.Teeth.Hardware.DeviceCertificates Obend.Judge

/-- Bytes in, verdict out, as the format runs it. -/
def verdictOf (spec cert : String) : Option (Verdict DdClause) :=
  match decodeDdSpec spec, decodeDdSolution cert with
  | .ok o, .ok c => some (checkDd o c)
  | _, _ => none

/-- The object's recipe is the Lean-stated one. -/
def recipeIs (spec : String) (r : List ProcessStep) : Bool :=
  match decodeDdSpec spec with
  | .ok o => decide (o.recipe = r)
  | .error _ => false

-- fixture kept (2026-11-04): the certificate check of device A at −0.5 V, bytes through the format's decoders
example : (verdictOf spec_a_m0_50 cert_a_m0_50).map isOk = some true := by native_decide

-- fixture kept (2026-11-04): device A at −0.7 V, where the certified current bound is 0.3 % of the current
example : (verdictOf spec_a_m0_70 cert_a_m0_70).map isOk = some true := by native_decide

-- fixture kept (2026-11-04): device B (p-well dose doubled) at −0.5 V
example : (verdictOf spec_b_m0_50 cert_b_m0_50).map isOk = some true := by native_decide

-- fixture kept (2026-11-04): the dose-change test: A's certificate against B's device is refused at the first node, as doping
example : (verdictOf spec_b_m0_50 cert_a_m0_50).map (isRefusedDoping 0) = some true := by native_decide

-- fixture kept (2026-11-04): the objects state the Lean recipe, at each dose
example : recipeIs spec_a_m0_50 (sky130DiodeRecipe 1.3e13) = true := by native_decide
example : recipeIs spec_b_m0_50 (sky130DiodeRecipe 2.6e13) = true := by native_decide

/-! ## The constants against the measurements they came from -/

/-- Deal–Grove 1965 Table II measured `B = 0.0117 µm²/h` in dry O₂ at 1000 °C; the Arrhenius fit of
Plummer's table gives, at that temperature, a value whose enclosure the check below brackets: within
`[0.0095, 0.0115]` (the fit is 10 % under the measurement; stated, not hidden). -/
def dealGroveBAt1000CDry : Obend.Analysis.Interval :=
  Obend.Analysis.Interval.scale ((dealGrove100 .dryO2).parabolic.d0 / um2PerHour)
    (expEnclosure (-(dealGrove100 .dryO2).parabolic.eaEv / (silicon300K.kBEv * 1273.15)))

-- fixture kept (2026-11-04): the Plummer fit lands within 20 % of Deal–Grove's measured B at 1000 °C dry
example : decide (0.0095 ≤ dealGroveBAt1000CDry.lo ∧ dealGroveBAt1000CDry.hi ≤ 0.0115) = true := by native_decide

-- fixture kept (2026-11-04): the four range tables increase in energy, range and straggle
example : (rangeTableSorted (rangeTable .boron) && rangeTableSorted (rangeTable .phosphorus) &&
    rangeTableSorted (rangeTable .arsenic) && rangeTableSorted (rangeTable .antimony)) = true := by decide +kernel

/-- The certificate's `n_i` (derived from Green's `N_c, N_v, E_g` at 300 K, checked by `niOk` inside
`checkDd`) lies in `[1.073, 1.075]·10¹⁰ cm⁻³`, where Green 1990 puts it. -/
def niWhereGreenPutsIt (cert : String) : Bool :=
  match decodeDdSolution cert with
  | .ok c => decide (1.073e10 ≤ c.ni ∧ c.ni ≤ 1.075e10)
  | .error _ => false

-- fixture kept (2026-11-04): the intrinsic density is derived, not typed, and lands at Green's value
example : niWhereGreenPutsIt cert_a_m0_50 = true := by native_decide

end Obend.Teeth.Hardware.DeviceFixtures
end
