module
/-
# Obend.Hardware.SafePhysicalShield — a sampled hardware gatekeeper whose guarantee holds between the samples

A continuous plant, a quantizing sensor, an untrusted policy proposing actuator commands, and a
LUT shield in reconfigurable fabric that decides once per sample period which command reaches the
actuator. The policy generator is not trusted at all: every theorem below quantifies over its output.
What is trusted is stated here once.

**The plant** (`SampledPhysicalPlantSpec`). One state variable `x` (a temperature, a current) with
dynamics `ẋ = field u (x)` under the held command `u`, a `RealExpr` in `"x"` per command; the physical
envelope `phys = [x_min, x_max]`; the sample period `Ts`; a declared speed bound `speed` (`M`), which
fixes the inter-sample pad `M·Ts`.

**The sensor.** The front end presents the ADC with an integer millivolt input `v` with
`|x − (offset + gain·v)| ≤ epsSensor` (`SensorReads`); the converter is `Analog.evalSarAdcN`, and
`Analog.runSarAdcN_exact_quantization_bounds` gives `|estimate(code) − x| ≤ epsAdc = epsSensor + gain·vLsb`
(`adc_estimate_within_eps`). That the input is in range is derived, not assumed (`wf` checks that the
converter's full scale covers the core).

**The sets.** `core = [x_min + M·Ts, x_max − M·Ts]` is the sample-instant invariant. The gate sees only
the top two bits of the code, a zone `z`; `cell z` is every true state consistent with a reading in
`z` (the zone's estimates widened by `epsAdc`, cut to the core), and `tube z` is the cell widened by
`M·Ts`, which lies inside `phys` because the cell lies inside the core (`tube_subset_phys`).

**The check** (`actionOk z u`, decidable, run at design time and inside every upgrade certificate).
`Flowpipe.verifyPicardAPriori` on `ẋ = field u` from `cell z` with a-priori enclosure `tube z` over
`[0, Ts]`: `cell ⊕ [0, Ts]·F(tube) ⊆ tube`; and re-entry: `cell ⊕ Ts·F(tube) ⊆ core`. The first makes
`M` a checked bound (`flow_excursion_le_pad`), not an assumption.

**The trajectories** (`InterSampleFlow`). A trajectory over one period is a function of rational
time with the mean-value property over the tube: `x τ = x 0 + τ·v` for some `v ∈ F(tube)`. This is
`Flowpipe.IsPicardSegmentState` with the time made explicit (`interSampleFlow_isPicardSegment`), the
form in which the library, having no `ℝ`, states that `x` solves the differential equation: a C¹
solution starting in the cell satisfies it once the Picard inclusion holds (the classical a-priori
enclosure argument, which is the one real-analysis step not proved here).

**The gate.** `SiliconOuroboros.cageAction` on the zone: the proposal passes when the fabric is
`active` and the live LUT bit for `(zone, proposal)` is set, and the frozen `rootShield zone` is
applied otherwise, so every period of an ICAP reconfiguration (`isolateClamped`, `loadFrames`), and
every period after CRC-failing bus traffic has quarantined the slot, runs the root shield.
Upgrades go through `amendShieldPolicy`: a candidate LUT is loaded only with a certificate the
kernel checker accepts for `shieldSequent`, the reflected statement that every action the candidate
permits passes `actionOk`.

**The theorems.** `sampled_shield_implies_continuous_tube`: one period, any reading the sensor can
produce, any proposal, any fabric state: the trajectory stays in `phys` at every instant, within
`M·Ts` of its start, and ends in the core. `continuous_plant_trace_safe_all_t`: along any valid
trace of periods, each carrying an administrative operation (idle, isolate, load with certificate,
release, bus fault), every instant of every period is in `phys`. `rejected_ota_leaves_shield_untouched`,
`override_implies_fenced_or_lut_reject` (the gate overrides only when fenced or when the live LUT
rejects), `interSampleFlow_exists` (the trajectory class is inhabited at every gated step),
`ota_install_completes`. §7 is a thermal stage with a 12-bit converter and a five-period valid trace.
-/
public import Obend.Hardware.SiliconOuroboros
public import Obend.Hardware.Analog
public import Obend.Analysis.Flowpipe
import all Obend.Judge.SvenvsCorrigibility
import all Obend.Judge.CertifierRatchet
import all Obend.Judge.ReflectiveGate
import all Obend.Hardware.DprStutter
import all Obend.Hardware.SiliconOuroboros
import all Obend.Hardware.Analog
import all Obend.Hardware.HDL

public section
namespace Obend.Hardware.SafePhysicalShield
open HDL DprStutter SiliconOuroboros Obend.Analysis
open Obend.Judge.SvenvsCorrigibility Obend.Judge.CertifierRatchet Obend.Judge.ReflectiveGate
set_option autoImplicit false

/-! ## 1. The plant, the sensor, the sets -/

/-- `max a b` and `min a b`, by cases (so that every use is a `split`). -/
def clampLo (a b : CanonicalRat) : CanonicalRat := if a ≤ b then b else a
def clampHi (a b : CanonicalRat) : CanonicalRat := if a ≤ b then a else b

theorem clampLo_spec (a b : CanonicalRat) : a ≤ clampLo a b ∧ b ≤ clampLo a b ∧ (clampLo a b = a ∨ clampLo a b = b) := by
  unfold clampLo
  split <;> grind

theorem clampHi_spec (a b : CanonicalRat) : clampHi a b ≤ a ∧ clampHi a b ≤ b ∧ (clampHi a b = a ∨ clampHi a b = b) := by
  unfold clampHi
  split <;> grind

/-- A sampled plant with its sensor chain. `field u` is `ẋ` under the held command `u`, an expression
in the variable `"x"`. Sensor: `x ≈ sensOffset + sensGain · (input in mV)` to `epsSensor`; converter:
`adcBits` bits at `vLsbMv` per code. -/
structure SampledPhysicalPlantSpec where
  Ts : CanonicalRat
  phys : Interval
  speed : CanonicalRat
  field : HWAct → RealExpr
  adcBits : Nat
  vLsbMv : Nat
  sensOffset : CanonicalRat
  sensGain : CanonicalRat
  epsSensor : CanonicalRat

namespace SampledPhysicalPlantSpec

/-- The inter-sample pad `M·Ts`. -/
def pad (p : SampledPhysicalPlantSpec) : CanonicalRat := p.speed * p.Ts

/-- The sample-instant invariant core: `phys` tightened by the pad. -/
def core (p : SampledPhysicalPlantSpec) : Interval := ⟨p.phys.lo + p.pad, p.phys.hi - p.pad⟩

/-- Quantization plus sensor uncertainty: one LSB in physical units on top of `epsSensor`. -/
def epsAdc (p : SampledPhysicalPlantSpec) : CanonicalRat := p.epsSensor + p.sensGain * (p.vLsbMv : CanonicalRat)

/-- The physical value a code stands for. -/
def estimate (p : SampledPhysicalPlantSpec) (code : Nat) : CanonicalRat :=
  p.sensOffset + p.sensGain * ((code * p.vLsbMv : Nat) : CanonicalRat)

/-- Codes per zone: the gate reads the top two bits. -/
def zoneCodes (p : SampledPhysicalPlantSpec) : Nat := 2 ^ (p.adcBits - 2)

def zoneOf (p : SampledPhysicalPlantSpec) (code : Nat) : HWState := BitVec.ofNat 2 (code / p.zoneCodes)

/-- The estimates of a zone's codes. -/
def zoneEst (p : SampledPhysicalPlantSpec) (z : HWState) : Interval :=
  ⟨p.estimate (z.toNat * p.zoneCodes), p.estimate ((z.toNat + 1) * p.zoneCodes)⟩

/-- Every true state consistent with a reading in zone `z` at a sample instant: within `epsAdc` of one
of the zone's estimates, and in the core. -/
def cell (p : SampledPhysicalPlantSpec) (z : HWState) : Interval :=
  ⟨clampLo ((p.zoneEst z).lo - p.epsAdc) p.core.lo, clampHi ((p.zoneEst z).hi + p.epsAdc) p.core.hi⟩

/-- The a-priori inter-sample enclosure from zone `z`: the cell widened by the pad. -/
def tube (p : SampledPhysicalPlantSpec) (z : HWState) : Interval := ⟨(p.cell z).lo - p.pad, (p.cell z).hi + p.pad⟩

/-- The plant under the held command `u`, as a `Flowpipe` system over one period. -/
def ode (p : SampledPhysicalPlantSpec) (u : HWAct) : OdeSystem := { fields := [("x", p.field u)], dt := p.Ts }

/-- Well-formedness: a positive period, nonnegative bound, gain and sensor error, at least the two zone
bits, a positive LSB, and a full scale that covers the core with the sensor error. -/
def wf (p : SampledPhysicalPlantSpec) : Bool :=
  decide (0 < p.Ts) && decide (0 ≤ p.speed) && decide (0 ≤ p.sensGain) && decide (0 ≤ p.epsSensor) &&
  decide (2 ≤ p.adcBits) && decide (0 < p.vLsbMv) &&
  decide (p.core.hi + p.epsSensor - p.sensOffset < p.sensGain * ((2 ^ p.adcBits * p.vLsbMv : Nat) : CanonicalRat))

/-- **The check of one (zone, command) pair.** The Picard a-priori inclusion of `tube z` from `cell z`
over one period, and re-entry of the period's endpoint into the core. -/
def actionOk (p : SampledPhysicalPlantSpec) (z : HWState) (u : HWAct) : Bool :=
  verifyPicardAPriori (p.ode u) [("x", p.cell z)] [("x", p.tube z)] p.Ts &&
  match evalInterval [("x", p.tube z)] (p.field u) with
  | some F => Interval.subset (Interval.add (p.cell z) (Interval.mul (Interval.ofPoint p.Ts) F)) p.core
  | none => false

/-- The sensor front end's contract: the millivolt input stands for the state to `epsSensor`. -/
def SensorReads (p : SampledPhysicalPlantSpec) (x : CanonicalRat) (vInMv : Nat) : Prop :=
  ratAbs (x - (p.sensOffset + p.sensGain * (vInMv : CanonicalRat))) ≤ p.epsSensor

/-- The converter: `Analog.evalSarAdcN`. -/
def adcCode (p : SampledPhysicalPlantSpec) (vInMv : Nat) : Nat := Analog.evalSarAdcN p.adcBits vInMv p.vLsbMv

instance (p : SampledPhysicalPlantSpec) (x : CanonicalRat) (vInMv : Nat) : Decidable (p.SensorReads x vInMv) :=
  inferInstanceAs (Decidable (ratAbs (x - (p.sensOffset + p.sensGain * (vInMv : CanonicalRat))) ≤ p.epsSensor))

end SampledPhysicalPlantSpec

open SampledPhysicalPlantSpec

theorem wf_iff (p : SampledPhysicalPlantSpec) : p.wf = true ↔
    0 < p.Ts ∧ 0 ≤ p.speed ∧ 0 ≤ p.sensGain ∧ 0 ≤ p.epsSensor ∧ 2 ≤ p.adcBits ∧ 0 < p.vLsbMv ∧
    p.core.hi + p.epsSensor - p.sensOffset < p.sensGain * ((2 ^ p.adcBits * p.vLsbMv : Nat) : CanonicalRat) := by
  simp only [wf, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem estimate_mono (p : SampledPhysicalPlantSpec) (hg : 0 ≤ p.sensGain) {a b : Nat} (h : a ≤ b) :
    p.estimate a ≤ p.estimate b := by
  have hn : a * p.vLsbMv ≤ b * p.vLsbMv := Nat.mul_le_mul_right _ h
  have hq : ((a * p.vLsbMv : Nat) : CanonicalRat) ≤ ((b * p.vLsbMv : Nat) : CanonicalRat) := by exact_mod_cast hn
  have := Rat.mul_le_mul_of_nonneg_left hq hg
  unfold estimate
  grind

/-! ## 2. The sensor chain: the estimate is within `epsAdc`, the zone's cell contains the state -/

/-- **The ADC's part of the uncertainty, discharged by the converter's theorem.** For a state in the
core and any input the sensor contract allows, the code's estimate is within `epsAdc` of the state and
the code is in range. -/
theorem adc_estimate_within_eps (p : SampledPhysicalPlantSpec) (hwf : p.wf = true) {x : CanonicalRat} {vInMv : Nat}
    (hx : x ∈ p.core) (hs : p.SensorReads x vInMv) :
    ratAbs (p.estimate (p.adcCode vInMv) - x) ≤ p.epsAdc ∧ p.adcCode vInMv < 2 ^ p.adcBits := by
  obtain ⟨_, _, hg, he, _, hlsb, hrange⟩ := (wf_iff p).1 hwf
  rw [SensorReads, ratAbs_le_iff] at hs
  rw [Interval.mem_iff] at hx
  have hq := Analog.runSarAdcN_exact_quantization_bounds p.adcBits vInMv p.vLsbMv hlsb
  have hin : vInMv < 2 ^ p.adcBits * p.vLsbMv := by
    apply Nat.lt_of_not_le
    intro hle
    have hc : ((2 ^ p.adcBits * p.vLsbMv : Nat) : CanonicalRat) ≤ (vInMv : CanonicalRat) := by exact_mod_cast hle
    have := Rat.mul_le_mul_of_nonneg_left hc hg
    grind
  have hlo : p.adcCode vInMv * p.vLsbMv ≤ vInMv := hq.1
  have hhi : vInMv < p.adcCode vInMv * p.vLsbMv + p.vLsbMv := by
    have := hq.2.2 hin
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  have hloq : ((p.adcCode vInMv * p.vLsbMv : Nat) : CanonicalRat) ≤ (vInMv : CanonicalRat) := by exact_mod_cast hlo
  have hhiq : (vInMv : CanonicalRat) ≤ ((p.adcCode vInMv * p.vLsbMv : Nat) : CanonicalRat) + (p.vLsbMv : CanonicalRat) := by
    have : (vInMv : CanonicalRat) ≤ ((p.adcCode vInMv * p.vLsbMv + p.vLsbMv : Nat) : CanonicalRat) := by
      exact_mod_cast Nat.le_of_lt hhi
    rw [Rat.natCast_add] at this
    exact this
  have h1 := Rat.mul_le_mul_of_nonneg_left hloq hg
  have h2 := Rat.mul_le_mul_of_nonneg_left hhiq hg
  refine ⟨?_, hq.2.1⟩
  rw [ratAbs_le_iff]
  unfold estimate epsAdc
  grind

/-- A code in range reads as the zone whose codes contain it. -/
theorem zoneOf_bounds (p : SampledPhysicalPlantSpec) (hbits : 2 ≤ p.adcBits) {code : Nat} (hc : code < 2 ^ p.adcBits) :
    (p.zoneOf code).toNat * p.zoneCodes ≤ code ∧ code ≤ ((p.zoneOf code).toNat + 1) * p.zoneCodes := by
  have hpos : 0 < p.zoneCodes := Nat.pow_pos (by decide)
  have hfull : 2 ^ p.adcBits = 4 * p.zoneCodes := by
    unfold zoneCodes
    obtain ⟨k, hk⟩ : ∃ k, p.adcBits = k + 2 := ⟨p.adcBits - 2, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.pow_add]
    omega
  have hdiv : code / p.zoneCodes < 4 := by
    apply (Nat.div_lt_iff_lt_mul hpos).2
    omega
  have hz : (p.zoneOf code).toNat = code / p.zoneCodes := by
    simp only [zoneOf, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hdiv
  rw [hz]
  refine ⟨Nat.div_mul_le_self code p.zoneCodes, ?_⟩
  have := Nat.lt_mul_div_succ code hpos
  rw [Nat.mul_comm] at this
  exact Nat.le_of_lt this

/-- **The zone's cell contains the true state**: the content of the `epsAdc` margin. -/
theorem state_in_cell (p : SampledPhysicalPlantSpec) (hwf : p.wf = true) {x : CanonicalRat} {vInMv : Nat}
    (hx : x ∈ p.core) (hs : p.SensorReads x vInMv) : x ∈ p.cell (p.zoneOf (p.adcCode vInMv)) := by
  obtain ⟨hest, hrange⟩ := adc_estimate_within_eps p hwf hx hs
  obtain ⟨_, _, hg, _, hbits, _, _⟩ := (wf_iff p).1 hwf
  obtain ⟨hzlo, hzhi⟩ := zoneOf_bounds p hbits hrange
  have h1 := estimate_mono p hg hzlo
  have h2 := estimate_mono p hg hzhi
  rw [ratAbs_le_iff] at hest
  rw [Interval.mem_iff] at hx ⊢
  simp only [cell, zoneEst]
  have hl := clampLo_spec (p.estimate ((p.zoneOf (p.adcCode vInMv)).toNat * p.zoneCodes) - p.epsAdc) p.core.lo
  have hh := clampHi_spec (p.estimate (((p.zoneOf (p.adcCode vInMv)).toNat + 1) * p.zoneCodes) + p.epsAdc) p.core.hi
  constructor
  · rcases hl.2.2 with h | h <;> rw [h] <;> grind
  · rcases hh.2.2 with h | h <;> rw [h] <;> grind

/-- The tube lies in the physical envelope: its cell lies in the core. -/
theorem tube_subset_phys (p : SampledPhysicalPlantSpec) (z : HWState) {x : CanonicalRat} (hx : x ∈ p.tube z) :
    x ∈ p.phys := by
  rw [Interval.mem_iff] at hx ⊢
  simp only [tube, cell, core] at hx
  obtain ⟨h1, h2⟩ := hx
  have hl := (clampLo_spec ((p.zoneEst z).lo - p.epsAdc) p.core.lo).2.1
  have hh := (clampHi_spec ((p.zoneEst z).hi + p.epsAdc) p.core.hi).2.1
  simp only [core] at hl hh
  constructor <;> grind

/-! ## 3. One period of the plant -/

/-- **A trajectory over one period under the held command `u`, read from zone `z`**: the mean-value
form of `ẋ = field u (x)` over the tube. -/
def InterSampleFlow (p : SampledPhysicalPlantSpec) (z : HWState) (u : HWAct) (x : CanonicalRat → CanonicalRat) : Prop :=
  ∃ F, evalInterval [("x", p.tube z)] (p.field u) = some F ∧
    ∀ τ, 0 ≤ τ → τ ≤ p.Ts → ∃ vel, vel ∈ F ∧ x τ = x 0 + τ * vel

theorem lookup_single {v : String} {I J : Interval} (h : [("x", J)].lookup v = some I) : v = "x" ∧ I = J := by
  simp only [List.lookup] at h
  split at h
  · rename_i heq
    refine ⟨by simpa using heq, ?_⟩
    cases h; rfl
  · cases h

theorem boxMem_single {x : CanonicalRat} {J : Interval} (hx : x ∈ J) : BoxMem (fun _ => x) [("x", J)] := by
  intro v I hl
  obtain ⟨_, rfl⟩ := lookup_single hl
  exact hx

/-- An `InterSampleFlow` is a `Flowpipe` Picard segment at every instant of the period. -/
theorem interSampleFlow_isPicardSegment {p : SampledPhysicalPlantSpec} {z : HWState} {u : HWAct}
    {x : CanonicalRat → CanonicalRat} (h : InterSampleFlow p z u x) {τ : CanonicalRat} (h0 : 0 ≤ τ) (h1 : τ ≤ p.Ts) :
    IsPicardSegmentState (p.ode u) [("x", p.cell z)] [("x", p.tube z)] p.Ts (fun _ => x 0) (fun _ => x τ) := by
  obtain ⟨F, hF, hall⟩ := h
  obtain ⟨vel, hvel, hx⟩ := hall τ h0 h1
  intro v I hl
  obtain ⟨rfl, rfl⟩ := lookup_single hl
  exact ⟨p.field u, p.cell z, F, τ, vel, by simp [ode], by simp [List.lookup], hF,
    by rw [Interval.mem_iff]; exact ⟨h0, h1⟩, hvel, hx⟩

/-- **One checked period.** From a state in the cell, under a command that passes `actionOk`, every
instant of every trajectory is in the tube, within the pad of the start, and the endpoint is in the core. -/
theorem flow_in_tube {p : SampledPhysicalPlantSpec} {z : HWState} {u : HWAct} (hok : p.actionOk z u = true)
    {x : CanonicalRat → CanonicalRat} (hx0 : x 0 ∈ p.cell z) (hflow : InterSampleFlow p z u x) :
    (∀ τ, 0 ≤ τ → τ ≤ p.Ts → x τ ∈ p.tube z ∧ ratAbs (x τ - x 0) ≤ p.pad) ∧ x p.Ts ∈ p.core := by
  simp only [actionOk, Bool.and_eq_true] at hok
  obtain ⟨hpic, hre⟩ := hok
  have hTs : 0 ≤ p.Ts := by
    simp only [verifyPicardAPriori, Bool.and_eq_true, decide_eq_true_eq] at hpic
    exact hpic.1
  obtain ⟨F, hF, hall⟩ := hflow
  rw [hF] at hre
  have hcell := hx0
  rw [Interval.mem_iff] at hcell
  have hlo : (p.cell z).lo ∈ p.cell z := by rw [Interval.mem_iff]; exact ⟨Rat.le_refl, Rat.le_trans hcell.1 hcell.2⟩
  have hhi : (p.cell z).hi ∈ p.cell z := by rw [Interval.mem_iff]; exact ⟨Rat.le_trans hcell.1 hcell.2, Rat.le_refl⟩
  have henc : ∀ {x_init τ vel : CanonicalRat}, x_init ∈ p.cell z → 0 ≤ τ → τ ≤ p.Ts → vel ∈ F →
      x_init + τ * vel ∈ p.tube z := by
    intro x_init τ vel hi h0 h1 hv
    exact verifyPicardAPriori_encloses (p.ode u) [("x", p.cell z)] [("x", p.tube z)] p.Ts hpic
      (name := "x") (rhsExpr := p.field u) (by simp [ode]) (by simp [List.lookup]) (by simp [List.lookup]) hF
      hi (by rw [Interval.mem_iff]; exact ⟨h0, h1⟩) hv
  refine ⟨?_, ?_⟩
  · intro τ h0 h1
    obtain ⟨vel, hvel, hx⟩ := hall τ h0 h1
    have ha := henc hx0 h0 h1 hvel
    have hb := henc hlo h0 h1 hvel
    have hc := henc hhi h0 h1 hvel
    rw [← hx] at ha
    refine ⟨ha, ?_⟩
    rw [ratAbs_le_iff, hx]
    rw [Interval.mem_iff] at hb hc
    simp only [tube] at hb hc
    grind
  · obtain ⟨vel, hvel, hx⟩ := hall p.Ts hTs Rat.le_refl
    rw [hx]
    exact Interval.subset_sound hre (Interval.add_mem hx0 (Interval.mul_mem (Interval.ofPoint_mem p.Ts) hvel))

/-- The declared speed bound is a checked one: over a checked period the excursion is at most `M·Ts`. -/
theorem flow_excursion_le_pad {p : SampledPhysicalPlantSpec} {z : HWState} {u : HWAct} (hok : p.actionOk z u = true)
    {x : CanonicalRat → CanonicalRat} (hx0 : x 0 ∈ p.cell z) (hflow : InterSampleFlow p z u x)
    {τ : CanonicalRat} (h0 : 0 ≤ τ) (h1 : τ ≤ p.Ts) : ratAbs (x τ - x 0) ≤ p.speed * p.Ts :=
  ((flow_in_tube hok hx0 hflow).1 τ h0 h1).2

/-- **The trajectory class is inhabited at every checked step**: the straight line at the field's value
at the start is an `InterSampleFlow`. -/
theorem interSampleFlow_exists (p : SampledPhysicalPlantSpec) {z : HWState} {u : HWAct} (hok : p.actionOk z u = true)
    {x0 : CanonicalRat} (hx0 : x0 ∈ p.tube z) : ∃ x, x 0 = x0 ∧ InterSampleFlow p z u x := by
  simp only [actionOk, Bool.and_eq_true] at hok
  obtain ⟨_, hre⟩ := hok
  split at hre
  · rename_i F hF
    have hv := evalInterval_sound [("x", p.tube z)] (fun _ => x0) (boxMem_single hx0) (p.field u) F hF
    refine ⟨fun τ => x0 + τ * evalExpr (fun _ => x0) (p.field u), by grind, F, hF, ?_⟩
    intro τ _ _
    exact ⟨_, hv, by grind⟩
  · cases hre

/-! ## 4. The gate: live LUT, frozen root, fail closed -/

/-- A policy every permitted action of which passes the check. -/
def ShieldPolicySound (p : SampledPhysicalPlantSpec) (pol : Policy HWState HWAct) : Prop :=
  ∀ z a, pol z a = true → p.actionOk z a = true

/-- A bank of tiles that is the lowering of a sound policy. -/
def BankSound (p : SampledPhysicalPlantSpec) (tiles : Array TechmappedTile) : Prop :=
  ∃ pol, tiles = lowerPolicyToTiles pol ∧ ShieldPolicySound p pol

/-- The frozen fallback passes the check in every zone. -/
def RootSound (p : SampledPhysicalPlantSpec) (root : HWState → HWAct) : Prop :=
  ∀ z, p.actionOk z (root z) = true

/-- The live LUT bit for `(zone, proposal)`. -/
def liveLut (dpr : DprFabric) (z : HWState) (a : HWAct) : Bool :=
  (evalDecodedFabric dpr.activeTiles (packInputs z a) dpr.targetRegs)[0]?.getD false

/-- **Whatever is proposed and whatever the fabric's phase, the applied command passes the check.** -/
theorem gate_action_ok (p : SampledPhysicalPlantSpec) {dpr : DprFabric} {root : HWState → HWAct}
    (hb : BankSound p dpr.activeTiles) (hr : RootSound p root) (z : HWState) (a : HWAct) :
    p.actionOk z (cageAction ⟨z, dpr, root⟩ a) = true := by
  obtain ⟨pol, hpol, hs⟩ := hb
  unfold cageAction
  dsimp only
  rw [hpol, evalDecodedFabric_lowerPolicyToTiles]
  split
  · next h => exact hs _ _ (by simpa using (Bool.and_eq_true_iff.mp h).2)
  · exact hr z

/-- The cage on a fabric holding a policy's lowering, as the policy. -/
theorem cageAction_lowered (pol : Policy HWState HWAct) (dpr : DprFabric) (root : HWState → HWAct) (z : HWState)
    (a : HWAct) (h : dpr.activeTiles = lowerPolicyToTiles pol) :
    cageAction ⟨z, dpr, root⟩ a = if (decide (dpr.phase = .active) && pol z a) = true then a else root z := by
  unfold cageAction
  dsimp only
  rw [h, evalDecodedFabric_lowerPolicyToTiles]
  simp

/-- **The gate overrides only when fenced or when the live LUT rejects the proposal.** -/
theorem override_implies_fenced_or_lut_reject (dpr : DprFabric) (root : HWState → HWAct) (z : HWState) (a : HWAct)
    (h : cageAction ⟨z, dpr, root⟩ a ≠ a) : dpr.phase ≠ .active ∨ liveLut dpr z a = false := by
  unfold cageAction at h
  dsimp only at h
  split at h
  · exact absurd rfl h
  · rename_i hc
    by_cases hp : dpr.phase = .active
    · right
      simpa [liveLut, hp] using hc
    · exact Or.inl hp

/-- An active fabric whose live LUT accepts the proposal passes it unchanged. -/
theorem gate_transparent (dpr : DprFabric) (root : HWState → HWAct) (z : HWState) (a : HWAct)
    (hp : dpr.phase = .active) (hl : liveLut dpr z a = true) : cageAction ⟨z, dpr, root⟩ a = a := by
  unfold liveLut at hl
  simp [cageAction, hp, hl]

/-- A proposal that is the root's own choice is applied in every phase. -/
theorem cageAction_root (dpr : DprFabric) (root : HWState → HWAct) (z : HWState) :
    cageAction ⟨z, dpr, root⟩ (root z) = root z := by
  unfold cageAction
  split <;> rfl

/-! ## 5. Upgrades through the reflective gate, the administrative channel, the stage -/

/-- The reflected plant of the upgrade obligation: a permitted action that fails the check steps to
the one unsafe word. -/
def shieldStep4 (p : SampledPhysicalPlantSpec) (s a : BitVec 4) : BitVec 4 :=
  if p.actionOk (s.setWidth 2) (a.setWidth 2) then 0 else 15

def shieldSafe4 (s : BitVec 4) : Bool := s != 15

/-- **The upgrade obligation as a sequent**: every action the candidate permits passes `actionOk`. -/
def shieldSequent (p : SampledPhysicalPlantSpec) (newp : Policy HWState HWAct) : Sequent :=
  reflectAdmissibleSequent (shieldStep4 p) shieldSafe4 (fun _ _ => false)
    (fun s a => newp (s.setWidth 2) (a.setWidth 2))

theorem shieldSequent_encodes (p : SampledPhysicalPlantSpec) (newp : Policy HWState HWAct)
    (h : SemValid (shieldSequent p newp)) : ShieldPolicySound p newp := by
  have hh := ((reflectAdmissible_iff _ _ _ _).1 h).1
  intro z a hp
  have ht := hh (z.setWidth 4) (a.setWidth 4)
    (by rcases bv2_cases z with rfl | rfl | rfl | rfl <;> decide) (by simpa using hp)
  simp only [shieldStep4, shieldSafe4] at ht
  have hz : (z.setWidth 4).setWidth 2 = z := by rcases bv2_cases z with rfl | rfl | rfl | rfl <;> decide
  have ha : (a.setWidth 4).setWidth 2 = a := by rcases bv2_cases a with rfl | rfl | rfl | rfl <;> decide
  rw [hz, ha] at ht
  cases hok : p.actionOk z a with
  | true => rfl
  | false => rw [hok] at ht; exact absurd ht (by decide)

/-- The shield's state: the kernel checker in force, the fabric, the frozen root, and the plant's true
state at the sample instant (which the gate never reads). -/
structure ShieldStage where
  verifier : KernelChecker
  dpr : DprFabric
  root : HWState → HWAct
  x : CanonicalRat

/-- **The reflective gate on the shield.** A candidate LUT reaches the configuration port only with a
certificate the checker in force accepts for its `shieldSequent`; otherwise nothing changes. -/
def amendShieldPolicy (p : SampledPhysicalPlantSpec) (st : ShieldStage) (candidate : RtlExpr) (cert : FastProofCert)
    (promoteVerifier : Bool) : ShieldStage :=
  if st.verifier cert (shieldSequent p (policyOfRtl candidate)) then
    { st with
        verifier := if promoteVerifier then FastKernel else st.verifier
        dpr := stepDprFabric st.dpr (.loadFrames (compilePolicyFrames (policyOfRtl candidate))) }
  else st

/-- What the administrator (or a fault) does to the fabric at a sample boundary. -/
inductive AdminOp where
  | idle
  | isolate
  | load (candidate : RtlExpr) (cert : FastProofCert) (promoteVerifier : Bool)
  | release
  | busFault (frames : Array TileFrame)

def adminStep (p : SampledPhysicalPlantSpec) (st : ShieldStage) : AdminOp → ShieldStage
  | .idle => { st with dpr := stepDprFabric st.dpr .compute }
  | .isolate => { st with dpr := stepDprFabric st.dpr .isolateClamped }
  | .load candidate cert promote => amendShieldPolicy p st candidate cert promote
  | .release => { st with dpr := stepDprFabric st.dpr .releaseFence }
  | .busFault frames =>
    if decodeTileFrames st.dpr.activeTiles.size frames = none then
      { st with dpr := stepDprFabric (stepDprFabric st.dpr .isolateClamped) (.loadFrames frames) }
    else st

/-- The fabric invariant: the active bank and any decoded pending bank are lowerings of sound policies. -/
def FabricSound (p : SampledPhysicalPlantSpec) (d : DprFabric) : Prop :=
  BankSound p d.activeTiles ∧ ∀ t, d.pending = some t → BankSound p t

theorem fabric_compute {p : SampledPhysicalPlantSpec} {d : DprFabric} (h : FabricSound p d) :
    FabricSound p (stepDprFabric d .compute) := by
  unfold stepDprFabric administer
  dsimp only
  split <;> exact h

theorem fabric_isolate {p : SampledPhysicalPlantSpec} {d : DprFabric} (h : FabricSound p d) :
    FabricSound p (stepDprFabric d .isolateClamped) ∧
      (stepDprFabric d .isolateClamped).activeTiles = d.activeTiles := by
  unfold stepDprFabric administer
  dsimp only
  split
  · exact ⟨⟨h.1, fun t ht => by cases ht⟩, rfl⟩
  · exact ⟨h, rfl⟩

theorem fabric_release {p : SampledPhysicalPlantSpec} {d : DprFabric} (h : FabricSound p d) :
    FabricSound p (stepDprFabric d .releaseFence) := by
  unfold stepDprFabric administer
  dsimp only
  split
  · rename_i decoded _ hpend
    exact ⟨h.2 decoded hpend, fun t ht => by cases ht⟩
  · exact h

/-- Loading frames keeps the invariant when whatever they decode to is a sound bank. -/
theorem fabric_load {p : SampledPhysicalPlantSpec} {d : DprFabric} (h : FabricSound p d) (frames : Array TileFrame)
    (hdec : ∀ t, decodeTileFrames d.activeTiles.size frames = some t → BankSound p t) :
    FabricSound p (stepDprFabric d (.loadFrames frames)) := by
  unfold stepDprFabric administer
  dsimp only
  split
  · exact h
  · split
    · exact ⟨h.1, fun t ht => by cases ht⟩
    · rename_i decoded hd
      exact ⟨h.1, fun t ht => by cases ht; exact hdec _ hd⟩

/-- The stage invariant. -/
structure ShieldSound (p : SampledPhysicalPlantSpec) (st : ShieldStage) : Prop where
  kernel : SoundKernel st.verifier
  fabric : FabricSound p st.dpr
  root : RootSound p st.root
  core : st.x ∈ p.core

theorem adminStep_root (p : SampledPhysicalPlantSpec) (st : ShieldStage) (op : AdminOp) :
    (adminStep p st op).root = st.root ∧ (adminStep p st op).x = st.x := by
  cases op with
  | load candidate cert promote =>
    simp only [adminStep, amendShieldPolicy]
    split <;> exact ⟨rfl, rfl⟩
  | busFault frames =>
    simp only [adminStep]
    split <;> exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

/-- **Every administrative operation preserves the invariant**: idle clocks, the three ICAP edges, an
upgrade with any certificate, arbitrary traffic on the configuration bus. -/
theorem adminStep_sound (p : SampledPhysicalPlantSpec) {st : ShieldStage} (h : ShieldSound p st) (op : AdminOp) :
    ShieldSound p (adminStep p st op) := by
  cases op with
  | idle => exact ⟨h.kernel, fabric_compute h.fabric, h.root, h.core⟩
  | isolate => exact ⟨h.kernel, (fabric_isolate h.fabric).1, h.root, h.core⟩
  | release => exact ⟨h.kernel, fabric_release h.fabric, h.root, h.core⟩
  | load candidate cert promote =>
    simp only [adminStep, amendShieldPolicy]
    split
    · next accepted =>
      have hs := shieldSequent_encodes p _ (h.kernel _ _ accepted)
      refine ⟨?_, ?_, h.root, h.core⟩
      · dsimp only
        split
        · exact fastKernel_sound
        · exact h.kernel
      · apply fabric_load h.fabric
        intro t ht
        obtain ⟨pol0, hpol0, _⟩ := h.fabric.1
        have hsz : st.dpr.activeTiles.size = (lowerPolicyToTiles (policyOfRtl candidate)).size := by
          rw [hpol0]; rfl
        rw [hsz, decode_compilePolicyFrames] at ht
        cases ht
        exact ⟨_, rfl, hs⟩
    · exact h
  | busFault frames =>
    simp only [adminStep]
    split
    · next bad =>
      refine ⟨h.kernel, ?_, h.root, h.core⟩
      apply fabric_load (fabric_isolate h.fabric).1
      intro t ht
      rw [(fabric_isolate h.fabric).2, bad] at ht
      cases ht
    · exact h

/-- **A rejected certificate leaves the live shield untouched**: checker, fabric, root and plant. -/
theorem rejected_ota_leaves_shield_untouched (p : SampledPhysicalPlantSpec) (st : ShieldStage) (candidate : RtlExpr)
    (cert : FastProofCert) (promote : Bool)
    (h : st.verifier cert (shieldSequent p (policyOfRtl candidate)) = false) :
    adminStep p st (.load candidate cert promote) = st := by
  simp [adminStep, amendShieldPolicy, h]

/-- **An accepted upgrade completes**: isolate, load, release from an active fabric ends active on the
candidate's bank, three sample periods later. -/
theorem ota_install_completes (p : SampledPhysicalPlantSpec) {st : ShieldStage} (h : ShieldSound p st)
    (active : st.dpr.phase = .active) (candidate : RtlExpr) (cert : FastProofCert) (promote : Bool)
    (accepted : st.verifier cert (shieldSequent p (policyOfRtl candidate)) = true) :
    let st3 := adminStep p (adminStep p (adminStep p st .isolate) (.load candidate cert promote)) .release
    st3.dpr.phase = .active ∧ st3.dpr.activeTiles = lowerPolicyToTiles (policyOfRtl candidate) := by
  obtain ⟨pol0, hpol0, _⟩ := h.fabric.1
  have hsz : (lowerPolicyToTiles (policyOfRtl candidate)).size = st.dpr.activeTiles.size := by rw [hpol0]; rfl
  have hinst := silicon_do_install_stutter_safe st.dpr (lowerPolicyToTiles (policyOfRtl candidate)) active hsz
  have heq : (adminStep p (adminStep p (adminStep p st .isolate) (.load candidate cert promote)) .release).dpr =
      siliconDoInstall st.dpr (compilePolicyFrames (policyOfRtl candidate)) := by
    simp [adminStep, amendShieldPolicy, accepted, siliconDoInstall]
  dsimp only
  rw [heq]
  exact ⟨hinst.1, hinst.2.1⟩

/-! ## 6. The period, the trace, the two safety theorems -/

/-- The command that reaches the actuator: the cage on the reading's zone. -/
def gateAction (p : SampledPhysicalPlantSpec) (st : ShieldStage) (vInMv : Nat) (proposal : HWAct) : HWAct :=
  cageAction ⟨p.zoneOf (p.adcCode vInMv), st.dpr, st.root⟩ proposal

/-- **The single-period theorem.** For any true state in the core, any sensor input the contract
allows, any proposal from the untrusted policy, and a fabric in any phase holding a sound bank: every
trajectory of the plant under the gated command stays in the physical envelope at every instant of
the period, within `M·Ts` of its start, and is back in the core at the period's end. -/
theorem sampled_shield_implies_continuous_tube (p : SampledPhysicalPlantSpec) (hwf : p.wf = true)
    (dpr : DprFabric) (root : HWState → HWAct) (hb : BankSound p dpr.activeTiles) (hr : RootSound p root)
    (x0 : CanonicalRat) (hcore : x0 ∈ p.core) (vInMv : Nat) (hs : p.SensorReads x0 vInMv)
    (proposal : HWAct) (x : CanonicalRat → CanonicalRat) (hx0 : x 0 = x0)
    (hflow : InterSampleFlow p (p.zoneOf (p.adcCode vInMv))
      (cageAction ⟨p.zoneOf (p.adcCode vInMv), dpr, root⟩ proposal) x) :
    (∀ τ, 0 ≤ τ → τ ≤ p.Ts → x τ ∈ p.phys ∧ ratAbs (x τ - x 0) ≤ p.speed * p.Ts) ∧ x p.Ts ∈ p.core := by
  have hcell := state_in_cell p hwf hcore hs
  rw [← hx0] at hcell
  have hok := gate_action_ok p hb hr (p.zoneOf (p.adcCode vInMv)) proposal
  have h := flow_in_tube hok hcell hflow
  exact ⟨fun τ h0 h1 => ⟨tube_subset_phys p _ (h.1 τ h0 h1).1, (h.1 τ h0 h1).2⟩, h.2⟩

/-- One sample period: the administrative operation at its boundary, the sensor's input, the
untrusted proposal, and the plant's trajectory over `[0, Ts]`. -/
structure ShieldStepEvent where
  admin : AdminOp
  vInMv : Nat
  proposal : HWAct
  traj : CanonicalRat → CanonicalRat

def stepShield (p : SampledPhysicalPlantSpec) (st : ShieldStage) (ev : ShieldStepEvent) : ShieldStage :=
  { adminStep p st ev.admin with x := ev.traj p.Ts }

/-- The environment's contract for one period: the sensor reads the state, the trajectory starts
there, and it is a flow of the plant under the command the gate applied. -/
def StepValid (p : SampledPhysicalPlantSpec) (st : ShieldStage) (ev : ShieldStepEvent) : Prop :=
  p.SensorReads st.x ev.vInMv ∧ ev.traj 0 = st.x ∧
  InterSampleFlow p (p.zoneOf (p.adcCode ev.vInMv))
    (gateAction p (adminStep p st ev.admin) ev.vInMv ev.proposal) ev.traj

def ValidTrace (p : SampledPhysicalPlantSpec) : ShieldStage → List ShieldStepEvent → Prop
  | _, [] => True
  | st, ev :: rest => StepValid p st ev ∧ ValidTrace p (stepShield p st ev) rest

def runShield (p : SampledPhysicalPlantSpec) : ShieldStage → List ShieldStepEvent → ShieldStage
  | st, [] => st
  | st, ev :: rest => runShield p (stepShield p st ev) rest

/-- One valid period: safe at every instant, and the invariant holds at the next sample. -/
theorem shield_step_safe (p : SampledPhysicalPlantSpec) (hwf : p.wf = true) {st : ShieldStage} (h : ShieldSound p st)
    {ev : ShieldStepEvent} (hv : StepValid p st ev) :
    (∀ τ, 0 ≤ τ → τ ≤ p.Ts → ev.traj τ ∈ p.phys) ∧ ShieldSound p (stepShield p st ev) := by
  obtain ⟨hs, h0, hflow⟩ := hv
  have ha := adminStep_sound p h ev.admin
  have hr := adminStep_root p st ev.admin
  have hstep := sampled_shield_implies_continuous_tube p hwf (adminStep p st ev.admin).dpr
    (adminStep p st ev.admin).root ha.fabric.1 ha.root st.x h.core ev.vInMv hs ev.proposal ev.traj h0 hflow
  exact ⟨fun τ t0 t1 => (hstep.1 τ t0 t1).1, ⟨ha.kernel, ha.fabric, ha.root, hstep.2⟩⟩

/-- **The trace theorem.** Along any valid trace from a sound stage, of any length, with any
proposals, any interleaving of idle periods, ICAP edges, certified or rejected upgrades and bus faults:
every instant of every period is inside the physical envelope, and the invariant holds at the end. -/
theorem continuous_plant_trace_safe_all_t (p : SampledPhysicalPlantSpec) (hwf : p.wf = true) :
    ∀ (evs : List ShieldStepEvent) (st : ShieldStage), ShieldSound p st → ValidTrace p st evs →
      (∀ k (hk : k < evs.length) τ, 0 ≤ τ → τ ≤ p.Ts → (evs[k]).traj τ ∈ p.phys) ∧
      ShieldSound p (runShield p st evs)
  | [], st, h, _ => ⟨fun k hk => absurd hk (Nat.not_lt_zero k), h⟩
  | ev :: rest, st, h, hv => by
    obtain ⟨hstep, hrest⟩ := hv
    have h1 := shield_step_safe p hwf h hstep
    have ih := continuous_plant_trace_safe_all_t p hwf rest (stepShield p st ev) h1.2 hrest
    refine ⟨?_, ih.2⟩
    intro k hk τ t0 t1
    cases k with
    | zero => exact h1.1 τ t0 t1
    | succ k => exact ih.1 k (Nat.lt_of_succ_lt_succ hk) τ t0 t1

/-- Mid-reconfiguration and in quarantine the root shield drives the actuator. -/
theorem gate_fails_closed (p : SampledPhysicalPlantSpec) (st : ShieldStage) (vInMv : Nat) (proposal : HWAct)
    (h : st.dpr.phase ≠ .active) : gateAction p st vInMv proposal = st.root (p.zoneOf (p.adcCode vInMv)) :=
  cage_fails_closed _ _ h

/-! ## 7. A thermal stage with a 12-bit converter -/

/-- Heater drive per command, in °C/s: off, trickle, half, full. -/
def thermalHeat (u : HWAct) : CanonicalRat :=
  match u.toNat with
  | 0 => 0
  | 1 => 2
  | 2 => 5
  | _ => 10

/-- A heated stage: `Ṫ = (20 − T)/10 + heat u` (°C, s), envelope `[0, 100]` °C, 100 ms period, declared
speed bound 12 °C/s (pad 1.2 °C); a front end of 40 mV/°C into a 12-bit converter at 1 mV per code
(full scale 102.4 °C, zones of 25.6 °C), sensor error 0.5 °C. -/
def thermalStage : SampledPhysicalPlantSpec where
  Ts := 1 / 10
  phys := ⟨0, 100⟩
  speed := 12
  field := fun u => .add (.mul (.const (1 / 10)) (.sub (.const 20) (.var "x"))) (.const (thermalHeat u))
  adcBits := 12
  vLsbMv := 1
  sensOffset := 0
  sensGain := 1 / 40
  epsSensor := 1 / 2

/-- The frozen fallback: trickle heat in the coldest zone, heater off elsewhere. -/
def thermalRoot (z : HWState) : HWAct := if z = 0 then 1 else 0

/-- The genesis LUT: only the trickle command passes. -/
def trickleOnlyRtl : RtlExpr := .alu .eq (.inputPort 1) (.const 1)

/-- An upgrade: trickle or half power. -/
def trickleOrHalfRtl : RtlExpr :=
  .alu .bitOr (.alu .eq (.inputPort 1) (.const 1)) (.alu .eq (.inputPort 1) (.const 2))

/-- A candidate that permits everything, full power in the hottest zone included. -/
def permitAllRtl : RtlExpr := .const 1

theorem thermalStage_wf : thermalStage.wf = true := by decide +kernel

theorem thermalRoot_passes : RootSound thermalStage thermalRoot := by
  intro z
  rcases bv2_cases z with rfl | rfl | rfl | rfl <;> decide +kernel

/-- The genesis LUT's certificate, checked by the kernel checker. -/
theorem trickleOnly_certified :
    FastKernel .fastDecideClosed (shieldSequent thermalStage (policyOfRtl trickleOnlyRtl)) = true := by
  decide +kernel

theorem trickleOrHalf_certified :
    FastKernel .fastDecideClosed (shieldSequent thermalStage (policyOfRtl trickleOrHalfRtl)) = true := by
  decide +kernel

/-- No certificate of either kernel rule that decides closed sequents passes the permit-all LUT. -/
theorem permitAll_rejected :
    FastKernel .fastDecideClosed (shieldSequent thermalStage (policyOfRtl permitAllRtl)) = false := by
  decide +kernel

theorem trickleOnly_passes : ShieldPolicySound thermalStage (policyOfRtl trickleOnlyRtl) :=
  shieldSequent_encodes _ _ (fastKernel_sound _ _ trickleOnly_certified)

/-- The fabric at power-on: active, holding the genesis LUT. -/
def thermalFabric : DprFabric where
  specSlot := 0
  phase := .active
  activeTiles := lowerPolicyToTiles (policyOfRtl trickleOnlyRtl)
  sram := #[]
  pending := none
  clampedOut := false
  inputs := #[]
  targetRegs := #[false]
  neighbors := ⟨#[], #[], #[], false⟩

/-- Power-on at 50 °C. -/
def thermalGenesis : ShieldStage := ⟨FastKernel, thermalFabric, thermalRoot, 50⟩

theorem thermalGenesis_invariant : ShieldSound thermalStage thermalGenesis :=
  ⟨fastKernel_sound, ⟨⟨_, rfl, trickleOnly_passes⟩, fun t ht => by cases ht⟩, thermalRoot_passes, by decide +kernel⟩

/-- A straight line at a velocity inside the field's enclosure is a flow. -/
theorem affine_flow (p : SampledPhysicalPlantSpec) (z : HWState) (u : HWAct) (x0 v : CanonicalRat)
    (hsome : (evalInterval [("x", p.tube z)] (p.field u)).isSome = true)
    (hv : v ∈ (evalInterval [("x", p.tube z)] (p.field u)).getD (Interval.ofPoint 0)) :
    InterSampleFlow p z u (fun τ => x0 + τ * v) := by
  cases hF : evalInterval [("x", p.tube z)] (p.field u) with
  | none => rw [hF] at hsome; cases hsome
  | some F =>
    rw [hF] at hv
    exact ⟨F, hF, fun τ _ _ => ⟨v, hv, by grind⟩⟩

/-- One period of the stage cooling at 2 °C/s in zone 1 with the heater-off command proposed (which is
the root's choice there, so the gate applies it in every phase). -/
def coolingPeriod (admin : AdminOp) (vInMv : Nat) (x0 : CanonicalRat) : ShieldStepEvent :=
  ⟨admin, vInMv, 0, fun τ => x0 + τ * (-2)⟩

theorem coolingPeriod_valid (st : ShieldStage) (hroot : st.root = thermalRoot) (admin : AdminOp) (vInMv : Nat)
    (hz : thermalStage.zoneOf (thermalStage.adcCode vInMv) = 1)
    (hs : thermalStage.SensorReads st.x vInMv) : StepValid thermalStage st (coolingPeriod admin vInMv st.x) := by
  refine ⟨hs, by simp only [coolingPeriod]; grind, ?_⟩
  simp only [coolingPeriod, gateAction]
  rw [hz, (adminStep_root thermalStage st admin).1, hroot]
  have hr : cageAction ⟨1, (adminStep thermalStage st admin).dpr, thermalRoot⟩ 0 = 0 :=
    cageAction_root _ thermalRoot 1
  rw [hr]
  exact affine_flow thermalStage 1 0 st.x (-2) (by decide +kernel) (by decide +kernel)

/-- Five periods: idle, isolate, a certified upgrade loaded, release, CRC-failing bus traffic. -/
def thermalTrace : List ShieldStepEvent :=
  [ coolingPeriod .idle 2000 50
  , coolingPeriod .isolate 1992 (249 / 5)
  , coolingPeriod (.load trickleOrHalfRtl .fastDecideClosed false) 1984 (248 / 5)
  , coolingPeriod .release 1976 (247 / 5)
  , coolingPeriod (.busFault #[]) 1968 (246 / 5) ]

theorem stepShield_root (p : SampledPhysicalPlantSpec) (st : ShieldStage) (ev : ShieldStepEvent) :
    (stepShield p st ev).root = st.root ∧ (stepShield p st ev).x = ev.traj p.Ts :=
  ⟨(adminStep_root p st ev.admin).1, rfl⟩

/-- **The contract is inhabited over a trace that exercises every administrative operation.** -/
theorem thermalTrace_valid : ValidTrace thermalStage thermalGenesis thermalTrace := by
  have step : ∀ (st : ShieldStage) (admin : AdminOp) (vInMv : Nat) (x0 : CanonicalRat),
      st.root = thermalRoot → st.x = x0 →
      thermalStage.zoneOf (thermalStage.adcCode vInMv) = 1 → thermalStage.SensorReads x0 vInMv →
      StepValid thermalStage st (coolingPeriod admin vInMv x0) ∧
        (stepShield thermalStage st (coolingPeriod admin vInMv x0)).root = thermalRoot ∧
        (stepShield thermalStage st (coolingPeriod admin vInMv x0)).x = x0 + thermalStage.Ts * (-2) := by
    intro st admin vInMv x0 hroot hx hz hs
    subst hx
    exact ⟨coolingPeriod_valid st hroot admin vInMv hz hs,
      (stepShield_root _ _ _).1.trans hroot, rfl⟩
  obtain ⟨v1, r1, x1⟩ := step thermalGenesis .idle 2000 50 rfl rfl (by decide +kernel) (by decide +kernel)
  obtain ⟨v2, r2, x2⟩ := step _ .isolate 1992 (249 / 5) r1 (x1.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  obtain ⟨v3, r3, x3⟩ := step _ (.load trickleOrHalfRtl .fastDecideClosed false) 1984 (248 / 5) r2
    (x2.trans (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  obtain ⟨v4, r4, x4⟩ := step _ .release 1976 (247 / 5) r3 (x3.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  obtain ⟨v5, _, _⟩ := step _ (.busFault #[]) 1968 (246 / 5) r4 (x4.trans (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  exact ⟨v1, v2, v3, v4, v5, trivial⟩

/-- The thermal stage is safe at every instant of the five periods, by the trace theorem. -/
theorem thermalTrace_safe (k : Nat) (hk : k < thermalTrace.length) (τ : CanonicalRat) (h0 : 0 ≤ τ)
    (h1 : τ ≤ thermalStage.Ts) : (thermalTrace[k]).traj τ ∈ thermalStage.phys :=
  (continuous_plant_trace_safe_all_t thermalStage thermalStage_wf thermalTrace thermalGenesis
    thermalGenesis_invariant thermalTrace_valid).1 k hk τ h0 h1

-- the Boolean premises of the theorems above are inhabited on the thermal stage
example : ShieldSound thermalStage thermalGenesis := thermalGenesis_invariant
example : thermalStage.actionOk 3 0 = true ∧ thermalStage.actionOk 3 3 = false := by decide +kernel
example : thermalStage.SensorReads 50 2000 := by decide +kernel
example : ∃ x, x 0 = 50 ∧ InterSampleFlow thermalStage 1 0 x :=
  interSampleFlow_exists thermalStage (by decide +kernel) (by decide +kernel)

end Obend.Hardware.SafePhysicalShield
end
