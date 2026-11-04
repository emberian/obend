module
/-
# Obend.Hardware.CurrentLoop — the LC Drives stator current loop as a chain of theorems over its parameters

The one device that gets the low-level-model-to-valid-approximation treatment first (decision of
2026-11-04, `review/DECISIONS-20261031.md`). The chain, each link a theorem over free rational
parameters, the integer literals confined to §6:

1. **The device.** One stator axis is `L di/dt = v − R i` (`RlPlant`: `R` in Ω, `L` in H).
2. **The sampled plant.** Under a zero-order hold of period `Ts` the exact discretization is
   `i⁺ = a i + b v` with `a = e^{−R Ts/L}` and `b R = 1 − a`. This library has no `exp`: the pole
   enters as the hypothesis `ZohRl.Spec`, which places `a` in the alternating-series enclosure
   `expNegEnclosure (R Ts/L) = [1 − x, 1 − x + x²/2]` (valid for `0 ≤ x ≤ 1`). **That hypothesis is
   the only physics assumed and not proved here**; everything below is a theorem over any `a` in it.
   `zoh_pole_in_unit` and `zoh_gain_pos` derive `0 < a < 1`, `0 < b` from it; `zoh_fixed_point` and
   `zoh_open_loop_contracts` are the open-loop facts.
3. **The controller.** `stepLoop` is the PI step the RTL computes (`foc_drive_top.sv`): `e = r − i`,
   `int⁺ = int + Ki e`, `v = Kp e + int⁺ + vff`, then the plant. `stepLoop_error_dynamics` is the
   exact closed-loop error recurrence: in `(x, z) = (i − r, int − (R r − vff))` the loop is the linear
   map `M = [[a − b(Kp+Ki), b], [−Ki, 1]]`, for all parameters with `b R = 1 − a`.
4. **Stability as a certificate.** `discrete_lyapunov_decay`: for any `2×2` map `M` and any rational
   `P, ε, c, m` passing the Sylvester-minor checks, `V(Ms) ≤ ρ V(s)` with `ρ c = c − ε`, hence
   (`lyapunov_trajectory_bound`) `m x_k² ≤ ρ^k c (x₀² + z₀²)` along every trajectory: exponential
   convergence of the tracking error with an explicit rational rate, for every initial state.
5. **The parameter box.** `checkLoopLyapunovBox` evaluates the minors by interval arithmetic over a
   box in `(a, b, Kp, Ki)`; `checkLoopLyapunovBox_sound` (via `evalInterval_sound`) turns one
   `decide` into the universal statement for every rational point of the box.
6. **The instantiation.** `lcDrivesPlant` (`R = 12 mΩ`, `L = 150 µH`, `Ts = 50 µs`), the `.obend` gains
   (`Kp = 0.4 V/A`, `Ki = 0.05 V/A` per sample), the box containing the LC Drives pole, and the
   certificate `P = [[112/25, −2247/1000],[−2247/1000, 3291/100]]`, `ε = 1/4`, `c = 34`, `m = 4`,
   `ρ = 135/136`. `lc_drives_current_loop_converges` is the end-to-end statement quantified over the
   box; `lc_drives_zoh_spec` shows the LC Drives numbers are in it.
7. **The RTL arithmetic.** `rtlPiStep` is the integer step of `foc_drive_top.sv` (mA, mV, mΩ,
   truncating `/1000`); `rtlPiStep_within_lsb` bounds each truncation below one LSB (1 mV) against
   the exact step. What is *not* here: the effect of that 1 mV disturbance on the bound of §4 (an
   input-to-state version of `discrete_lyapunov_decay`), the inverter between `v` and the winding,
   and the mechanical equation. They are named in `review/EXPERT-physics-numerics-20261103.md`.
-/
public import Obend.Analysis.RealAnalysis
public section

namespace Obend.Hardware.CurrentLoop
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. The device -/

/-- One stator axis seen by the current loop: `L di/dt = v − R i`. `rOhm` in ohms, `lHenry` in henries. -/
structure RlPlant where
  rOhm   : CanonicalRat
  lHenry : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-! ## 2. The sampled plant and where the exponential enters -/

/-- Alternating-series enclosure of `e^{−x}` for `0 ≤ x ≤ 1`: `[1 − x, 1 − x + x²/2]`. This is a fact
about the real exponential, stated here as the interval a ZOH pole must lie in; it is not proved in
this library (no `ℝ`). -/
@[expose] def expNegEnclosure (x : CanonicalRat) : Interval :=
  ⟨1 - x, 1 - x + x * x / 2⟩

/-- The zero-order-hold discretization of an `RlPlant` at sample time `tsSec`: `i⁺ = a i + b v`. -/
structure ZohRl where
  plant : RlPlant
  tsSec : CanonicalRat
  /-- the ZOH pole `e^{−R Ts/L}` -/
  a : CanonicalRat
  /-- the ZOH input gain `(1 − a)/R` -/
  b : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- The dimensionless sample-to-time-constant ratio `x = R Ts / L`. -/
@[expose] def ZohRl.x (d : ZohRl) : CanonicalRat :=
  d.plant.rOhm * d.tsSec / d.plant.lHenry

/-- **The physical hypothesis.** The discretization is consistent with its plant: positive `R`, `L`,
`Ts`; `x = R Ts/L < 1` (the sample is shorter than the electrical time constant); the pole lies in
the exponential's enclosure; and `b R = 1 − a` exactly. -/
@[expose] def ZohRl.Spec (d : ZohRl) : Prop :=
  0 < d.plant.rOhm ∧ 0 < d.plant.lHenry ∧ 0 < d.tsSec ∧ 0 < d.x ∧ d.x < 1 ∧
  d.a ∈ expNegEnclosure d.x ∧ d.b * d.plant.rOhm = 1 - d.a

instance (d : ZohRl) : Decidable d.Spec := by
  unfold ZohRl.Spec; infer_instance

/-- One sample of the open-loop plant under a held voltage `v`. -/
@[expose] def stepZoh (d : ZohRl) (i v : CanonicalRat) : CanonicalRat :=
  d.a * i + d.b * v

/-- From the hypothesis: the pole is strictly inside the unit interval. -/
theorem zoh_pole_in_unit (d : ZohRl) (h : d.Spec) : 0 < d.a ∧ d.a < 1 := by
  obtain ⟨_, _, _, hx0, hx1, ha, _⟩ := h
  rw [Interval.mem_iff] at ha
  dsimp [expNegEnclosure] at ha
  have hxx : d.x * d.x ≤ d.x * 1 := Rat.mul_le_mul_of_nonneg_left (by grind) (by grind)
  constructor
  · grind
  · grind

/-- From the hypothesis: the input gain is positive. -/
theorem zoh_gain_pos (d : ZohRl) (h : d.Spec) : 0 < d.b := by
  have hR : 0 < d.plant.rOhm := h.1
  have hbR : d.b * d.plant.rOhm = 1 - d.a := h.2.2.2.2.2.2
  have ha1 : d.a < 1 := (zoh_pole_in_unit d h).2
  rcases @Rat.le_total d.b 0 with hb | hb
  · have hle : d.b * d.plant.rOhm ≤ 0 * d.plant.rOhm :=
      Rat.mul_le_mul_of_nonneg_right hb (by grind)
    grind
  · by_cases hb0 : d.b = 0
    · rw [hb0] at hbR
      grind
    · grind

/-- Open loop, the held voltage `v = R i*` has the fixed point `i*`: Ohm's law survives sampling. -/
theorem zoh_fixed_point (d : ZohRl) (h : d.Spec) (iStar : CanonicalRat) :
    stepZoh d iStar (d.plant.rOhm * iStar) = iStar := by
  have hbR : d.b * d.plant.rOhm = 1 - d.a := h.2.2.2.2.2.2
  have hkey : d.b * d.plant.rOhm * iStar = (1 - d.a) * iStar := by rw [hbR]
  unfold stepZoh
  grind

/-- Open loop, two trajectories under the same voltage approach each other by the factor `a` a sample. -/
theorem zoh_open_loop_contracts (d : ZohRl) (i j v : CanonicalRat) :
    stepZoh d i v - stepZoh d j v = d.a * (i - j) := by
  unfold stepZoh
  grind

/-! ## 3. The controller the RTL computes -/

/-- PI gains in the units the loop works in: `kp` in V/A, `ki` in V/A per sample. -/
structure PiGains where
  kp : CanonicalRat
  ki : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- The loop state: the winding current `i` (A) and the integrator `int` (V). -/
structure LoopState where
  i   : CanonicalRat
  int : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- One control sample as `foc_drive_top.sv` computes it: `e = r − i`, `int⁺ = int + Ki e`,
`v = Kp e + int⁺ + vff`, then the plant `i⁺ = a i + b v`. `vff` is whatever feed-forward the RTL adds
(the cross-coupling and back-EMF terms); here it is any constant. -/
@[expose] def stepLoop (d : ZohRl) (g : PiGains) (r vff : CanonicalRat) (s : LoopState) : LoopState :=
  let e := r - s.i
  let int' := s.int + g.ki * e
  let v := g.kp * e + int' + vff
  ⟨d.a * s.i + d.b * v, int'⟩

/-- `k` samples of the closed loop. -/
@[expose] def iterateLoop (d : ZohRl) (g : PiGains) (r vff : CanonicalRat) : Nat → LoopState → LoopState
  | 0, s => s
  | k + 1, s => iterateLoop d g r vff k (stepLoop d g r vff s)

/-- Tracking error `x = i − r`. -/
@[expose] def errX (r : CanonicalRat) (s : LoopState) : CanonicalRat := s.i - r

/-- Integrator error `z = int − (R r − vff)`: the integrator must settle to the Ohmic drop less the
feed-forward. -/
@[expose] def errZ (d : ZohRl) (r vff : CanonicalRat) (s : LoopState) : CanonicalRat :=
  s.int - (d.plant.rOhm * r - vff)

/-- The closed-loop error map `M = [[a − b(Kp+Ki), b], [−Ki, 1]]`, written out. -/
@[expose] def m11 (d : ZohRl) (g : PiGains) : CanonicalRat := d.a - d.b * (g.kp + g.ki)
@[expose] def m12 (d : ZohRl) : CanonicalRat := d.b
@[expose] def m21 (g : PiGains) : CanonicalRat := -g.ki
@[expose] def m22 : CanonicalRat := 1

/-- **The closed-loop error dynamics.** For every plant, discretization with `b R = 1 − a`, gains,
reference, feed-forward and state, the next errors are the linear map `M` of the current errors.
The reference, the feed-forward and the Ohmic drop cancel exactly; nothing numeric is assumed. -/
theorem stepLoop_error_dynamics (d : ZohRl) (g : PiGains) (r vff : CanonicalRat) (s : LoopState)
    (hbR : d.b * d.plant.rOhm = 1 - d.a) :
    errX r (stepLoop d g r vff s) = m11 d g * errX r s + m12 d * errZ d r vff s ∧
    errZ d r vff (stepLoop d g r vff s) = m21 g * errX r s + m22 * errZ d r vff s := by
  have hkey : d.b * d.plant.rOhm * r = (1 - d.a) * r := by rw [hbR]
  unfold errX errZ stepLoop m11 m12 m21 m22
  dsimp only
  constructor
  · grind
  · grind

/-! ## 4. A discrete quadratic Lyapunov certificate, universal over `ℚ²` -/

/-- The quadratic form `[x z] P [x z]ᵀ` of the symmetric `P = [[p11, p12], [p12, p22]]`. -/
@[expose] def quadForm (p11 p12 p22 x z : CanonicalRat) : CanonicalRat :=
  p11 * x * x + 2 * p12 * x * z + p22 * z * z

/-- Sylvester's criterion for a `2×2` symmetric form: `q11 > 0` and `q11 q22 − q12² ≥ 0` make it
positive semidefinite, by `q11 · Q(x,z) = (q11 x + q12 z)² + (q11 q22 − q12²) z²`. -/
theorem quadForm_nonneg_of_minors (q11 q12 q22 x z : CanonicalRat)
    (h11 : 0 < q11) (hdet : 0 ≤ q11 * q22 - q12 * q12) :
    0 ≤ quadForm q11 q12 q22 x z := by
  have hid : q11 * quadForm q11 q12 q22 x z =
      (q11 * x + q12 * z) * (q11 * x + q12 * z) + (q11 * q22 - q12 * q12) * (z * z) := by
    unfold quadForm
    grind
  have hsq1 := Interval.rat_sq_nonneg (q11 * x + q12 * z)
  have hsq2 := Interval.rat_sq_nonneg z
  have hprod : 0 ≤ (q11 * q22 - q12 * q12) * (z * z) := Rat.mul_nonneg hdet hsq2
  have hscaled : q11 * 0 ≤ q11 * quadForm q11 q12 q22 x z := by
    rw [hid]
    grind
  exact Rat.le_of_mul_le_mul_left hscaled h11

/-- Entries of `Q = P − MᵀPM − εI` for `M = [[a11, a12], [a21, a22]]`. -/
@[expose] def lyapQ11 (p11 p12 p22 a11 _a12 a21 _a22 eps : CanonicalRat) : CanonicalRat :=
  p11 - (a11 * a11 * p11 + 2 * a11 * a21 * p12 + a21 * a21 * p22) - eps
@[expose] def lyapQ12 (p11 p12 p22 a11 a12 a21 a22 : CanonicalRat) : CanonicalRat :=
  p12 - (a11 * a12 * p11 + (a11 * a22 + a12 * a21) * p12 + a21 * a22 * p22)
@[expose] def lyapQ22 (p11 p12 p22 _a11 a12 _a21 a22 eps : CanonicalRat) : CanonicalRat :=
  p22 - (a12 * a12 * p11 + 2 * a12 * a22 * p12 + a22 * a22 * p22) - eps

/-- The image of `(x, z)` under `M`. -/
@[expose] def mapX (a11 a12 x z : CanonicalRat) : CanonicalRat := a11 * x + a12 * z
@[expose] def mapZ (a21 a22 x z : CanonicalRat) : CanonicalRat := a21 * x + a22 * z

/-- The static side of a certificate `(P, ε, c, m)`: `0 < ε ≤ c`, `cI − P ⪰ 0` and `P − mI ⪰ 0` by
Sylvester minors, `0 < m`. -/
@[expose] def lyapStaticOk (p11 p12 p22 eps c m : CanonicalRat) : Bool :=
  decide (0 < eps) && decide (eps ≤ c) && decide (0 < m) &&
  decide (0 < c - p11) && decide (0 ≤ (c - p11) * (c - p22) - p12 * p12) &&
  decide (0 < p11 - m) && decide (0 ≤ (p11 - m) * (p22 - m) - p12 * p12)

/-- The dynamic side at one parameter point: `Q = P − MᵀPM − εI ⪰ 0` by Sylvester minors. -/
@[expose] def lyapDynamicOk (p11 p12 p22 a11 a12 a21 a22 eps : CanonicalRat) : Bool :=
  let q11 := lyapQ11 p11 p12 p22 a11 a12 a21 a22 eps
  let q12 := lyapQ12 p11 p12 p22 a11 a12 a21 a22
  let q22 := lyapQ22 p11 p12 p22 a11 a12 a21 a22 eps
  decide (0 < q11) && decide (0 ≤ q11 * q22 - q12 * q12)

/-- **One-step Lyapunov decay.** If the certificate checks at `M`, then for every state
`V(Ms) ≤ ρ V(s)` where `ρ c = c − ε`, and `m|s|² ≤ V(s) ≤ c|s|²`. -/
theorem discrete_lyapunov_decay
    (p11 p12 p22 a11 a12 a21 a22 eps c m rho x z : CanonicalRat)
    (hStatic : lyapStaticOk p11 p12 p22 eps c m = true)
    (hDyn : lyapDynamicOk p11 p12 p22 a11 a12 a21 a22 eps = true)
    (hrho : rho * c = c - eps) :
    quadForm p11 p12 p22 (mapX a11 a12 x z) (mapZ a21 a22 x z) ≤ rho * quadForm p11 p12 p22 x z ∧
    m * (x * x + z * z) ≤ quadForm p11 p12 p22 x z ∧
    quadForm p11 p12 p22 x z ≤ c * (x * x + z * z) := by
  unfold lyapStaticOk at hStatic
  unfold lyapDynamicOk at hDyn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hStatic hDyn
  obtain ⟨⟨⟨⟨⟨⟨hEps, hEpsC⟩, hm⟩, hc1⟩, hc2⟩, hm1⟩, hm2⟩ := hStatic
  obtain ⟨hq11, hqdet⟩ := hDyn
  -- Q ⪰ 0 gives V(s) − V(Ms) − ε|s|² ≥ 0
  have hQ := quadForm_nonneg_of_minors _ _ _ x z hq11 hqdet
  have hQid : quadForm (lyapQ11 p11 p12 p22 a11 a12 a21 a22 eps) (lyapQ12 p11 p12 p22 a11 a12 a21 a22)
      (lyapQ22 p11 p12 p22 a11 a12 a21 a22 eps) x z =
      quadForm p11 p12 p22 x z - quadForm p11 p12 p22 (mapX a11 a12 x z) (mapZ a21 a22 x z) -
        eps * (x * x + z * z) := by
    unfold quadForm lyapQ11 lyapQ12 lyapQ22 mapX mapZ
    grind
  rw [hQid] at hQ
  -- cI − P ⪰ 0 gives c|s|² − V(s) ≥ 0
  have hC := quadForm_nonneg_of_minors (c - p11) (-p12) (c - p22) x z hc1 (by grind)
  have hCid : quadForm (c - p11) (-p12) (c - p22) x z = c * (x * x + z * z) - quadForm p11 p12 p22 x z := by
    unfold quadForm
    grind
  rw [hCid] at hC
  -- P − mI ⪰ 0 gives V(s) − m|s|² ≥ 0
  have hM := quadForm_nonneg_of_minors (p11 - m) p12 (p22 - m) x z hm1 hm2
  have hMid : quadForm (p11 - m) p12 (p22 - m) x z = quadForm p11 p12 p22 x z - m * (x * x + z * z) := by
    unfold quadForm
    grind
  rw [hMid] at hM
  refine ⟨?_, by grind, by grind⟩
  -- multiply the target by c > 0: c V(Ms) ≤ c V − c ε|s|² ≤ c V − ε V = ρ c V
  have hcpos : 0 < c := by grind
  have hεnn : 0 ≤ eps := by grind
  have hEpsScaled : eps * quadForm p11 p12 p22 x z ≤ eps * (c * (x * x + z * z)) :=
    Rat.mul_le_mul_of_nonneg_left (by grind) hεnn
  have hcV : c * quadForm p11 p12 p22 (mapX a11 a12 x z) (mapZ a21 a22 x z) ≤
      c * (rho * quadForm p11 p12 p22 x z) := by
    have h1 : c * quadForm p11 p12 p22 (mapX a11 a12 x z) (mapZ a21 a22 x z) ≤
        c * (quadForm p11 p12 p22 x z - eps * (x * x + z * z)) :=
      Rat.mul_le_mul_of_nonneg_left (by grind) (by grind)
    have h2 : c * (rho * quadForm p11 p12 p22 x z) = (c - eps) * quadForm p11 p12 p22 x z := by
      grind
    grind
  exact Rat.le_of_mul_le_mul_left hcV hcpos

/-- Rational powers, structurally. -/
@[expose] def ratPow (r : CanonicalRat) : Nat → CanonicalRat
  | 0 => 1
  | k + 1 => r * ratPow r k

theorem ratPow_nonneg (r : CanonicalRat) (hr : 0 ≤ r) : ∀ k, 0 ≤ ratPow r k
  | 0 => by dsimp [ratPow]; grind
  | k + 1 => by
    dsimp [ratPow]
    exact Rat.mul_nonneg hr (ratPow_nonneg r hr k)

/-- Iterate the error map `k` times. -/
@[expose] def iterateMap (a11 a12 a21 a22 : CanonicalRat) : Nat → CanonicalRat × CanonicalRat → CanonicalRat × CanonicalRat
  | 0, s => s
  | k + 1, (x, z) => iterateMap a11 a12 a21 a22 k (mapX a11 a12 x z, mapZ a21 a22 x z)

/-- **The trajectory bound.** Under the certificate, `V` decays geometrically along every trajectory
of `M`, so the tracking error obeys `m x_k² ≤ ρ^k c (x₀² + z₀²)`. -/
theorem lyapunov_trajectory_bound
    (p11 p12 p22 a11 a12 a21 a22 eps c m rho : CanonicalRat)
    (hStatic : lyapStaticOk p11 p12 p22 eps c m = true)
    (hDyn : lyapDynamicOk p11 p12 p22 a11 a12 a21 a22 eps = true)
    (hrho : rho * c = c - eps) (hrho0 : 0 ≤ rho) :
    ∀ (k : Nat) (x0 z0 : CanonicalRat),
      quadForm p11 p12 p22 (iterateMap a11 a12 a21 a22 k (x0, z0)).1 (iterateMap a11 a12 a21 a22 k (x0, z0)).2 ≤
        ratPow rho k * quadForm p11 p12 p22 x0 z0 ∧
      m * ((iterateMap a11 a12 a21 a22 k (x0, z0)).1 * (iterateMap a11 a12 a21 a22 k (x0, z0)).1) ≤
        ratPow rho k * (c * (x0 * x0 + z0 * z0)) := by
  intro k
  induction k with
  | zero =>
    intro x0 z0
    dsimp [iterateMap, ratPow]
    have h := discrete_lyapunov_decay p11 p12 p22 a11 a12 a21 a22 eps c m rho x0 z0 hStatic hDyn hrho
    have hz := Interval.rat_sq_nonneg z0
    have hmz : 0 ≤ m * (z0 * z0) := by
      have hm : 0 < m := by
        unfold lyapStaticOk at hStatic
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hStatic
        exact hStatic.1.1.1.1.2
      exact Rat.mul_nonneg (by grind) hz
    refine ⟨by grind, ?_⟩
    grind
  | succ k ih =>
    intro x0 z0
    dsimp only [iterateMap]
    have hstep := discrete_lyapunov_decay p11 p12 p22 a11 a12 a21 a22 eps c m rho x0 z0 hStatic hDyn hrho
    have hk := ih (mapX a11 a12 x0 z0) (mapZ a21 a22 x0 z0)
    have hpow := ratPow_nonneg rho hrho0 k
    have hV1 : ratPow rho k * quadForm p11 p12 p22 (mapX a11 a12 x0 z0) (mapZ a21 a22 x0 z0) ≤
        ratPow rho k * (rho * quadForm p11 p12 p22 x0 z0) :=
      Rat.mul_le_mul_of_nonneg_left hstep.1 hpow
    have hV0 : quadForm p11 p12 p22 x0 z0 ≤ c * (x0 * x0 + z0 * z0) := hstep.2.2
    have hpowS : ratPow rho (k + 1) = rho * ratPow rho k := rfl
    have hmono : ratPow rho (k + 1) * quadForm p11 p12 p22 x0 z0 ≤ ratPow rho (k + 1) * (c * (x0 * x0 + z0 * z0)) :=
      Rat.mul_le_mul_of_nonneg_left hV0 (ratPow_nonneg rho hrho0 (k + 1))
    -- the lower bound m x² ≤ V at the iterate, from the decay theorem at that point
    have hlow := (discrete_lyapunov_decay p11 p12 p22 a11 a12 a21 a22 eps c m rho
      (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).1
      (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).2 hStatic hDyn hrho).2.1
    have hm : 0 < m := by
      unfold lyapStaticOk at hStatic
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hStatic
      exact hStatic.1.1.1.1.2
    have hzz := Interval.rat_sq_nonneg (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).2
    have hmz : 0 ≤ m * ((iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).2 *
        (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).2) :=
      Rat.mul_nonneg (by grind) hzz
    -- chain: V_k(Ms) ≤ ρ^k V(Ms) ≤ ρ^k ρ V(s) = ρ^{k+1} V(s)
    have hVk : quadForm p11 p12 p22 (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).1
        (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).2 ≤
        ratPow rho (k + 1) * quadForm p11 p12 p22 x0 z0 := by
      rw [hpowS]
      have := hk.1
      grind
    refine ⟨hVk, ?_⟩
    have hmx : m * ((iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).1 *
        (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).1) ≤
        quadForm p11 p12 p22 (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).1
          (iterateMap a11 a12 a21 a22 k (mapX a11 a12 x0 z0, mapZ a21 a22 x0 z0)).2 := by
      grind
    grind

/-- The loop's error trajectory is the iterated error map: `errX`/`errZ` of the `k`-th loop state
are the `k`-th image of the initial errors under `M`. -/
theorem iterateLoop_errors (d : ZohRl) (g : PiGains) (r vff : CanonicalRat)
    (hbR : d.b * d.plant.rOhm = 1 - d.a) :
    ∀ (k : Nat) (s : LoopState),
      (errX r (iterateLoop d g r vff k s), errZ d r vff (iterateLoop d g r vff k s)) =
        iterateMap (m11 d g) (m12 d) (m21 g) m22 k (errX r s, errZ d r vff s)
  | 0, s => rfl
  | k + 1, s => by
    dsimp only [iterateLoop, iterateMap]
    have h := stepLoop_error_dynamics d g r vff s hbR
    rw [iterateLoop_errors d g r vff hbR k (stepLoop d g r vff s)]
    simp only [mapX, mapZ, h.1, h.2]

/-! ## 5. The certificate over a parameter box, by interval arithmetic -/

/-- `RealExpr`s for the error-map entries over the variables `"a"`, `"b"`, `"kp"`, `"ki"`. -/
@[expose] def exprM11 : RealExpr := .sub (.var "a") (.mul (.var "b") (.add (.var "kp") (.var "ki")))
@[expose] def exprM12 : RealExpr := .var "b"
@[expose] def exprM21 : RealExpr := .sub (.const 0) (.var "ki")
@[expose] def exprM22 : RealExpr := .const 1

/-- `Q = P − MᵀPM − εI` entries as `RealExpr`s, for a fixed rational `P`, `ε`. -/
@[expose] def exprQ11 (p11 p12 p22 eps : CanonicalRat) : RealExpr :=
  .sub (.sub (.const p11)
      (.add (.add (.mul (.mul exprM11 exprM11) (.const p11))
                  (.mul (.mul (.mul (.const 2) exprM11) exprM21) (.const p12)))
            (.mul (.mul exprM21 exprM21) (.const p22))))
    (.const eps)
@[expose] def exprQ12 (p11 p12 p22 : CanonicalRat) : RealExpr :=
  .sub (.const p12)
    (.add (.add (.mul (.mul exprM11 exprM12) (.const p11))
                (.mul (.add (.mul exprM11 exprM22) (.mul exprM12 exprM21)) (.const p12)))
          (.mul (.mul exprM21 exprM22) (.const p22)))
@[expose] def exprQ22 (p11 p12 p22 eps : CanonicalRat) : RealExpr :=
  .sub (.sub (.const p22)
      (.add (.add (.mul (.mul exprM12 exprM12) (.const p11))
                  (.mul (.mul (.mul (.const 2) exprM12) exprM22) (.const p12)))
            (.mul (.mul exprM22 exprM22) (.const p22))))
    (.const eps)
@[expose] def exprQdet (p11 p12 p22 eps : CanonicalRat) : RealExpr :=
  .sub (.mul (exprQ11 p11 p12 p22 eps) (exprQ22 p11 p12 p22 eps))
       (.mul (exprQ12 p11 p12 p22) (exprQ12 p11 p12 p22))

/-- The box checker: static minors on `(P, ε, c, m)` and interval evaluation of `q11 > 0`,
`q11 q22 − q12² ≥ 0` over the box. -/
@[expose] def checkLoopLyapunovBox (box : List (String × Interval)) (p11 p12 p22 eps c m : CanonicalRat) : Bool :=
  lyapStaticOk p11 p12 p22 eps c m &&
  (match evalInterval box (exprQ11 p11 p12 p22 eps), evalInterval box (exprQdet p11 p12 p22 eps) with
   | some q11Iv, some detIv => decide (0 < q11Iv.lo) && decide (0 ≤ detIv.lo)
   | _, _ => false)

/-- The point assignment of a parameter quadruple. -/
@[expose] def paramRho (a b kp ki : CanonicalRat) : String → CanonicalRat :=
  fun v => if v = "a" then a else if v = "b" then b else if v = "kp" then kp else if v = "ki" then ki else 0

/-- The box is the product of the four parameter intervals, in a fixed order. -/
@[expose] def paramBox (aIv bIv kpIv kiIv : Interval) : List (String × Interval) :=
  [("a", aIv), ("b", bIv), ("kp", kpIv), ("ki", kiIv)]

/-- `∀ v I, box.lookup v = some I → rho v ∈ I` (the hypothesis of `evalInterval_sound`). -/
@[expose] def BoxMemParams (box : List (String × Interval)) (rho : String → CanonicalRat) : Prop :=
  ∀ v I, box.lookup v = some I → rho v ∈ I

theorem paramRho_mem (aIv bIv kpIv kiIv : Interval) (a b kp ki : CanonicalRat)
    (ha : a ∈ aIv) (hb : b ∈ bIv) (hkp : kp ∈ kpIv) (hki : ki ∈ kiIv) :
    BoxMemParams (paramBox aIv bIv kpIv kiIv) (paramRho a b kp ki) := by
  intro v I hv
  simp only [paramBox, List.lookup] at hv
  by_cases h1 : v = "a"
  · subst h1; simp at hv; subst hv; simp [paramRho]; exact ha
  · by_cases h2 : v = "b"
    · subst h2; simp at hv; subst hv; simp [paramRho]; exact hb
    · by_cases h3 : v = "kp"
      · subst h3; simp at hv; subst hv; simp [paramRho]; exact hkp
      · by_cases h4 : v = "ki"
        · subst h4; simp at hv; subst hv; simp [paramRho]; exact hki
        · have e1 : (v == "a") = false := beq_eq_false_iff_ne.mpr h1
          have e2 : (v == "b") = false := beq_eq_false_iff_ne.mpr h2
          have e3 : (v == "kp") = false := beq_eq_false_iff_ne.mpr h3
          have e4 : (v == "ki") = false := beq_eq_false_iff_ne.mpr h4
          simp [e1, e2, e3, e4] at hv

/-- The `RealExpr`s evaluate to the entries. -/
theorem exprM_eval (a b kp ki : CanonicalRat) :
    evalExpr (paramRho a b kp ki) exprM11 = a - b * (kp + ki) ∧
    evalExpr (paramRho a b kp ki) exprM12 = b ∧
    evalExpr (paramRho a b kp ki) exprM21 = -ki ∧
    evalExpr (paramRho a b kp ki) exprM22 = 1 := by
  simp [exprM11, exprM12, exprM21, exprM22, evalExpr, paramRho]
  try grind

theorem exprQ_eval (p11 p12 p22 eps a b kp ki : CanonicalRat) :
    evalExpr (paramRho a b kp ki) (exprQ11 p11 p12 p22 eps) = lyapQ11 p11 p12 p22 (a - b * (kp + ki)) b (-ki) 1 eps ∧
    evalExpr (paramRho a b kp ki) (exprQ12 p11 p12 p22) = lyapQ12 p11 p12 p22 (a - b * (kp + ki)) b (-ki) 1 ∧
    evalExpr (paramRho a b kp ki) (exprQ22 p11 p12 p22 eps) = lyapQ22 p11 p12 p22 (a - b * (kp + ki)) b (-ki) 1 eps := by
  have hm := exprM_eval a b kp ki
  refine ⟨?_, ?_, ?_⟩
  · simp only [exprQ11, evalExpr, hm.1, hm.2.2.1, lyapQ11]
    try grind
  · simp only [exprQ12, evalExpr, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, lyapQ12]
    try grind
  · simp only [exprQ22, evalExpr, hm.2.1, hm.2.2.2, lyapQ22]
    try grind

/-- **Soundness of the box checker.** If it passes, the dynamic minors are positive at every rational
parameter point of the box, i.e. `lyapDynamicOk` holds there. -/
theorem checkLoopLyapunovBox_sound (aIv bIv kpIv kiIv : Interval) (p11 p12 p22 eps c m : CanonicalRat)
    (hCheck : checkLoopLyapunovBox (paramBox aIv bIv kpIv kiIv) p11 p12 p22 eps c m = true)
    (a b kp ki : CanonicalRat)
    (ha : a ∈ aIv) (hb : b ∈ bIv) (hkp : kp ∈ kpIv) (hki : ki ∈ kiIv) :
    lyapStaticOk p11 p12 p22 eps c m = true ∧
    lyapDynamicOk p11 p12 p22 (a - b * (kp + ki)) b (-ki) 1 eps = true := by
  unfold checkLoopLyapunovBox at hCheck
  rcases (Bool.and_eq_true _ _).mp hCheck with ⟨hStatic, hDynIv⟩
  refine ⟨hStatic, ?_⟩
  have hMem := paramRho_mem aIv bIv kpIv kiIv a b kp ki ha hb hkp hki
  cases h11 : evalInterval (paramBox aIv bIv kpIv kiIv) (exprQ11 p11 p12 p22 eps) with
  | none => rw [h11] at hDynIv; cases hDynIv
  | some q11Iv =>
    cases hdet : evalInterval (paramBox aIv bIv kpIv kiIv) (exprQdet p11 p12 p22 eps) with
    | none => rw [h11, hdet] at hDynIv; cases hDynIv
    | some detIv =>
      rw [h11, hdet] at hDynIv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hDynIv
      have hq := exprQ_eval p11 p12 p22 eps a b kp ki
      have h11mem := evalInterval_sound _ _ hMem _ _ h11
      have hdetmem := evalInterval_sound _ _ hMem _ _ hdet
      rw [Interval.mem_iff] at h11mem hdetmem
      have hdetEval : evalExpr (paramRho a b kp ki) (exprQdet p11 p12 p22 eps) =
          lyapQ11 p11 p12 p22 (a - b * (kp + ki)) b (-ki) 1 eps *
            lyapQ22 p11 p12 p22 (a - b * (kp + ki)) b (-ki) 1 eps -
          lyapQ12 p11 p12 p22 (a - b * (kp + ki)) b (-ki) 1 *
            lyapQ12 p11 p12 p22 (a - b * (kp + ki)) b (-ki) 1 := by
        simp only [exprQdet, evalExpr, hq.1, hq.2.1, hq.2.2]
        try grind
      rw [hq.1] at h11mem
      rw [hdetEval] at hdetmem
      unfold lyapDynamicOk
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by grind, by grind⟩

/-- **The end-to-end statement over a box.** For every rational `(a, b, Kp, Ki)` in a box whose
checker passes, every plant resistance `R` with `b R = 1 − a`, every reference, feed-forward and
initial state, the current loop's tracking error satisfies
`m (i_k − r)² ≤ ρ^k c ((i₀ − r)² + (int₀ − (R r − vff))²)` for all `k`. -/
theorem current_loop_converges_on_box
    (aIv bIv kpIv kiIv : Interval) (p11 p12 p22 eps c m rho : CanonicalRat)
    (hCheck : checkLoopLyapunovBox (paramBox aIv bIv kpIv kiIv) p11 p12 p22 eps c m = true)
    (hrho : rho * c = c - eps) (hrho0 : 0 ≤ rho)
    (d : ZohRl) (g : PiGains)
    (ha : d.a ∈ aIv) (hb : d.b ∈ bIv) (hkp : g.kp ∈ kpIv) (hki : g.ki ∈ kiIv)
    (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (r vff : CanonicalRat) (s0 : LoopState) (k : Nat) :
    m * (errX r (iterateLoop d g r vff k s0) * errX r (iterateLoop d g r vff k s0)) ≤
      ratPow rho k * (c * (errX r s0 * errX r s0 + errZ d r vff s0 * errZ d r vff s0)) := by
  obtain ⟨hStatic, hDyn⟩ := checkLoopLyapunovBox_sound aIv bIv kpIv kiIv p11 p12 p22 eps c m hCheck
    d.a d.b g.kp g.ki ha hb hkp hki
  have hTraj := (lyapunov_trajectory_bound p11 p12 p22 (d.a - d.b * (g.kp + g.ki)) d.b (-g.ki) 1 eps c m rho
    hStatic hDyn hrho hrho0 k (errX r s0) (errZ d r vff s0)).2
  have hErr := iterateLoop_errors d g r vff hbR k s0
  have hX : errX r (iterateLoop d g r vff k s0) =
      (iterateMap (d.a - d.b * (g.kp + g.ki)) d.b (-g.ki) 1 k (errX r s0, errZ d r vff s0)).1 := by
    have := congrArg Prod.fst hErr
    simpa [m11, m12, m21, m22] using this
  rw [hX]
  exact hTraj

/-! ## 6. The instantiation: LC Drives numbers, the `.obend` gains, one certificate -/

/-- LC Drives IPM stator axis: `R = 12 mΩ`, `L = 150 µH` (`apps/foc-hil/verilator/rk4_pmsm_plant.hpp`, the
d-axis inductance). -/
@[expose] def lcDrivesPlant : RlPlant where
  rOhm   := CanonicalRat.mk 12 1000
  lHenry := CanonicalRat.mk 150 1000000

/-- `x = R Ts/L = 0.012 · 50e-6 / 150e-6 = 1/250`. -/
@[expose] def lcDrivesX : CanonicalRat := CanonicalRat.mk 1 250

/-- The 20 kHz discretization. The pole is taken at the upper end of its enclosure
`[1 − x, 1 − x + x²/2] = [249/250, 124501/125000]`; `b = (1 − a)/R`. -/
@[expose] def lcDrivesZoh : ZohRl where
  plant := lcDrivesPlant
  tsSec := CanonicalRat.mk 50 1000000
  a     := CanonicalRat.mk 124501 125000
  b     := CanonicalRat.mk 499 1500

/-- The gains of `apps/foc-hil/PiCurrentLoop.obend` (`kpGainPermille 400`, `kiGainPermille 50`):
`Kp = 0.4 V/A`, `Ki = 0.05 V/A` per sample. -/
@[expose] def lcDrivesGains : PiGains where
  kp := CanonicalRat.mk 2 5
  ki := CanonicalRat.mk 1 20

/-- The parameter box: `a` in the exponential's enclosure, `b = (1 − a)/R` over that enclosure
(`[(1 − a_hi)/R, (1 − a_lo)/R] = [499/1500, 1/3]`), the gains as points. -/
@[expose] def lcDrivesBox : List (String × Interval) :=
  paramBox ⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩
           ⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩
           ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 2 5⟩
           ⟨CanonicalRat.mk 1 20, CanonicalRat.mk 1 20⟩

/-- The certificate: `P` is the rounded solution of `MᵀPM − P = −I` at the box centre; `ε = 1/4`;
`c = 34 ≥ λ_max(P) ≈ 33.09`; `m = 4 ≤ λ_min(P) ≈ 4.30`; `ρ = 1 − ε/c = 135/136`. -/
@[expose] def lcP11 : CanonicalRat := CanonicalRat.mk 112 25
@[expose] def lcP12 : CanonicalRat := CanonicalRat.mk (-2247) 1000
@[expose] def lcP22 : CanonicalRat := CanonicalRat.mk 3291 100
@[expose] def lcEps : CanonicalRat := CanonicalRat.mk 1 4
@[expose] def lcC : CanonicalRat := 34
@[expose] def lcM : CanonicalRat := 4
@[expose] def lcRho : CanonicalRat := CanonicalRat.mk 135 136

/-- The LC Drives numbers satisfy the physical hypothesis (`x = 1/250 < 1`, `a` in the enclosure,
`b R = 1 − a`). -/
-- fixture kept (2026-11-04): the ZOH plant satisfies its `Spec` predicate, which `lc_drives_current_loop_converges` consumes
example : lcDrivesZoh.Spec := by
  decide +kernel

/-- The certificate checks over the box, and the parameters of `lcDrivesZoh`/`lcDrivesGains` lie in it. -/
-- fixture kept (2026-11-04): the Lyapunov box certificate the convergence theorem consumes
theorem lc_drives_box_certificate :
    checkLoopLyapunovBox lcDrivesBox lcP11 lcP12 lcP22 lcEps lcC lcM = true ∧
    lcRho * lcC = lcC - lcEps ∧
    lcDrivesZoh.a ∈ (⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩ : Interval) ∧
    lcDrivesZoh.b ∈ (⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩ : Interval) ∧
    lcDrivesZoh.b * lcDrivesZoh.plant.rOhm = 1 - lcDrivesZoh.a := by
  decide +kernel

/-- **LC Drives current loop, end to end.** For every reference `r`, feed-forward `vff`, initial state
and sample count `k`: `4 (i_k − r)² ≤ (135/136)^k · 34 · ((i₀ − r)² + (int₀ − (R r − vff))²)`. The
rate is the certificate's, not the loop's (the closed-loop poles have modulus ≈ 0.929); the
statement holds for every pole `a` in the exponential's enclosure, not only the one in `lcDrivesZoh`. -/
theorem lc_drives_current_loop_converges (r vff : CanonicalRat) (s0 : LoopState) (k : Nat) :
    lcM * (errX r (iterateLoop lcDrivesZoh lcDrivesGains r vff k s0) *
             errX r (iterateLoop lcDrivesZoh lcDrivesGains r vff k s0)) ≤
      ratPow lcRho k * (lcC * (errX r s0 * errX r s0 +
        errZ lcDrivesZoh r vff s0 * errZ lcDrivesZoh r vff s0)) := by
  have hc := lc_drives_box_certificate
  exact current_loop_converges_on_box
    ⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩
    ⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩
    ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 2 5⟩
    ⟨CanonicalRat.mk 1 20, CanonicalRat.mk 1 20⟩
    lcP11 lcP12 lcP22 lcEps lcC lcM lcRho hc.1 hc.2.1 (by decide +kernel)
    lcDrivesZoh lcDrivesGains hc.2.2.1 hc.2.2.2.1 (by decide +kernel) (by decide +kernel)
    hc.2.2.2.2 r vff s0 k

/-! ## 7. The RTL arithmetic -/

/-- The integer PI step of `foc_drive_top.sv` in its own units: currents in mA, voltages in mV,
gains in mΩ (`kp_milli`) and mΩ per sample (`ki_milli`), products truncated by `/ 1000`:
`int⁺ = int + (err · ki)/1000`, `v = (err · kp)/1000 + int⁺`. -/
@[expose] def rtlPiStep (kpMilli kiMilli errMa intMv : Int) : Int × Int :=
  let int' := intMv + (errMa * kiMilli) / 1000
  (int', (errMa * kpMilli) / 1000 + int')

/-- Each truncation loses less than one LSB (1 mV): `1000 · (p / 1000) ≤ p < 1000 · (p / 1000) + 1000`
for the two products. In volts and amps this is the exact step `int + Ki e`, `Kp e + int⁺`, each
perturbed by a disturbance in `[0, 1 mV)`. -/
theorem rtlPiStep_within_lsb (kpMilli kiMilli errMa intMv : Int) :
    let (int', v) := rtlPiStep kpMilli kiMilli errMa intMv
    1000 * (int' - intMv) ≤ errMa * kiMilli ∧ errMa * kiMilli < 1000 * (int' - intMv) + 1000 ∧
    1000 * (v - int') ≤ errMa * kpMilli ∧ errMa * kpMilli < 1000 * (v - int') + 1000 := by
  dsimp only [rtlPiStep]
  have h1 := Int.ediv_mul_le (errMa * kiMilli) (b := 1000) (by decide)
  have h2 := Int.lt_ediv_add_one_mul_self (errMa * kiMilli) (b := 1000) (by decide)
  have h3 := Int.ediv_mul_le (errMa * kpMilli) (b := 1000) (by decide)
  have h4 := Int.lt_ediv_add_one_mul_self (errMa * kpMilli) (b := 1000) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end Obend.Hardware.CurrentLoop
end
