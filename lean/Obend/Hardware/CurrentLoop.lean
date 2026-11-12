module
/-
# Obend.Hardware.CurrentLoop — the LC Drives stator current loop as a chain of theorems over its parameters

1. **The device.** One stator axis is `L di/dt = v − R i` (`RlPlant`: `R` in Ω, `L` in H).
2. **The sampled plant.** Under ZOH of period `Ts`, `i⁺ = a i + b v` with `a ∈ expNegEnclosure (R Ts/L)`
   and `b R = 1 − a` (`ZohRl.Spec`). `zoh_pole_in_unit`, `zoh_gain_pos`, `zoh_fixed_point`, and
   `zoh_open_loop_contracts` follow universally.
3. **The controller.** `stepLoop` models `foc_drive_top.sv`: `e = r − i`, `int⁺ = int + Ki e`,
   `v = Kp e + int⁺ + vff`, and `stepLoop_error_dynamics` gives the exact linear error map `M`.
4. **Stability & box certificate.** `discrete_lyapunov_decay`, `lyapunov_trajectory_bound`, and
   `checkLoopLyapunovBox_sound` certify exponential convergence across any parameter box.
5. **LC Drives instantiation.** `lcDrivesPlant` (`R = 12 mΩ`, `L = 150 µH`, `Ts = 50 µs`),
   `Kp = 0.4 V/A`, `Ki = 0.05 V/A`, `ρ = 135/136` (`lc_drives_current_loop_converges`).
6. **RTL quantization, dead-time, coupled rotor back-EMF & continuous inter-sample tube.**
   `rtlPiStep` (`/1000`), `rtlPiStepQ32` (`>>> 32`), `adcFloorMa_within_lsb`, `discrete_lyapunov_iss_ball`,
   `lc_drives_quantized_current_loop_iss_ball`, `currentLoop_deadTime_and_quant_iss_ball`
   (SiC dead-time `±(2 td / Tpwm) Vdc` + Q32 + 1-mA ADC), `currentLoop_backEmf_coupled_iss_ball`
   (`L di_q/dt = v_q − R i_q − λ_m ω_e` under `|Δω_e| ≤ α_max Ts`), and
   `zoh_intersample_convex_hull_bound` (exact continuous ZOH convex-hull tube on `[k Ts, (k+1) Ts]`).
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
  deriving DecidableEq, Repr

/-! ## 2. The sampled plant and where the exponential enters -/

/-- Alternating-series enclosure of `e^{−x}` for `0 ≤ x ≤ 1`: `[1 − x, 1 − x + x²/2]`. This is a fact
about the real exponential, stated here as the interval a ZOH pole must lie in; it is not proved in
this library (no `ℝ`). -/
def expNegEnclosure (x : CanonicalRat) : Interval :=
  ⟨1 - x, 1 - x + x * x / 2⟩

/-- The zero-order-hold discretization of an `RlPlant` at sample time `tsSec`: `i⁺ = a i + b v`. -/
structure ZohRl where
  plant : RlPlant
  tsSec : CanonicalRat
  /-- the ZOH pole `e^{−R Ts/L}` -/
  a : CanonicalRat
  /-- the ZOH input gain `(1 − a)/R` -/
  b : CanonicalRat
  deriving DecidableEq, Repr

/-- The dimensionless sample-to-time-constant ratio `x = R Ts / L`. -/
def ZohRl.x (d : ZohRl) : CanonicalRat :=
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
def stepZoh (d : ZohRl) (i v : CanonicalRat) : CanonicalRat :=
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
  deriving DecidableEq, Repr

/-- The loop state: the winding current `i` (A) and the integrator `int` (V). -/
structure LoopState where
  i   : CanonicalRat
  int : CanonicalRat
  deriving DecidableEq, Repr

/-- One control sample as `foc_drive_top.sv` computes it: `e = r − i`, `int⁺ = int + Ki e`,
`v = Kp e + int⁺ + vff`, then the plant `i⁺ = a i + b v`. `vff` is whatever feed-forward the RTL adds
(the cross-coupling and back-EMF terms); here it is any constant. -/
def stepLoop (d : ZohRl) (g : PiGains) (r vff : CanonicalRat) (s : LoopState) : LoopState :=
  let e := r - s.i
  let int' := s.int + g.ki * e
  let v := g.kp * e + int' + vff
  ⟨d.a * s.i + d.b * v, int'⟩

/-- `k` samples of the closed loop. -/
def iterateLoop (d : ZohRl) (g : PiGains) (r vff : CanonicalRat) : Nat → LoopState → LoopState
  | 0, s => s
  | k + 1, s => iterateLoop d g r vff k (stepLoop d g r vff s)

/-- Tracking error `x = i − r`. -/
def errX (r : CanonicalRat) (s : LoopState) : CanonicalRat := s.i - r

/-- Integrator error `z = int − (R r − vff)`: the integrator must settle to the Ohmic drop less the
feed-forward. -/
def errZ (d : ZohRl) (r vff : CanonicalRat) (s : LoopState) : CanonicalRat :=
  s.int - (d.plant.rOhm * r - vff)

/-- The closed-loop error map `M = [[a − b(Kp+Ki), b], [−Ki, 1]]`, written out. -/
def m11 (d : ZohRl) (g : PiGains) : CanonicalRat := d.a - d.b * (g.kp + g.ki)
def m12 (d : ZohRl) : CanonicalRat := d.b
def m21 (g : PiGains) : CanonicalRat := -g.ki
def m22 : CanonicalRat := 1

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
def quadForm (p11 p12 p22 x z : CanonicalRat) : CanonicalRat :=
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
def lyapQ11 (p11 p12 p22 a11 _a12 a21 _a22 eps : CanonicalRat) : CanonicalRat :=
  p11 - (a11 * a11 * p11 + 2 * a11 * a21 * p12 + a21 * a21 * p22) - eps
def lyapQ12 (p11 p12 p22 a11 a12 a21 a22 : CanonicalRat) : CanonicalRat :=
  p12 - (a11 * a12 * p11 + (a11 * a22 + a12 * a21) * p12 + a21 * a22 * p22)
def lyapQ22 (p11 p12 p22 _a11 a12 _a21 a22 eps : CanonicalRat) : CanonicalRat :=
  p22 - (a12 * a12 * p11 + 2 * a12 * a22 * p12 + a22 * a22 * p22) - eps

/-- The image of `(x, z)` under `M`. -/
def mapX (a11 a12 x z : CanonicalRat) : CanonicalRat := a11 * x + a12 * z
def mapZ (a21 a22 x z : CanonicalRat) : CanonicalRat := a21 * x + a22 * z

/-- The static side of a certificate `(P, ε, c, m)`: `0 < ε ≤ c`, `cI − P ⪰ 0` and `P − mI ⪰ 0` by
Sylvester minors, `0 < m`. -/
def lyapStaticOk (p11 p12 p22 eps c m : CanonicalRat) : Bool :=
  decide (0 < eps) && decide (eps ≤ c) && decide (0 < m) &&
  decide (0 < c - p11) && decide (0 ≤ (c - p11) * (c - p22) - p12 * p12) &&
  decide (0 < p11 - m) && decide (0 ≤ (p11 - m) * (p22 - m) - p12 * p12)

/-- The dynamic side at one parameter point: `Q = P − MᵀPM − εI ⪰ 0` by Sylvester minors. -/
def lyapDynamicOk (p11 p12 p22 a11 a12 a21 a22 eps : CanonicalRat) : Bool :=
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
def ratPow (r : CanonicalRat) : Nat → CanonicalRat
  | 0 => 1
  | k + 1 => r * ratPow r k

theorem ratPow_nonneg (r : CanonicalRat) (hr : 0 ≤ r) : ∀ k, 0 ≤ ratPow r k
  | 0 => by dsimp [ratPow]; grind
  | k + 1 => by
    dsimp [ratPow]
    exact Rat.mul_nonneg hr (ratPow_nonneg r hr k)

/-- Iterate the error map `k` times. -/
def iterateMap (a11 a12 a21 a22 : CanonicalRat) : Nat → CanonicalRat × CanonicalRat → CanonicalRat × CanonicalRat
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
def exprM11 : RealExpr := .sub (.var "a") (.mul (.var "b") (.add (.var "kp") (.var "ki")))
def exprM12 : RealExpr := .var "b"
def exprM21 : RealExpr := .sub (.const 0) (.var "ki")
def exprM22 : RealExpr := .const 1

/-- `Q = P − MᵀPM − εI` entries as `RealExpr`s, for a fixed rational `P`, `ε`. -/
def exprQ11 (p11 p12 p22 eps : CanonicalRat) : RealExpr :=
  .sub (.sub (.const p11)
      (.add (.add (.mul (.mul exprM11 exprM11) (.const p11))
                  (.mul (.mul (.mul (.const 2) exprM11) exprM21) (.const p12)))
            (.mul (.mul exprM21 exprM21) (.const p22))))
    (.const eps)
def exprQ12 (p11 p12 p22 : CanonicalRat) : RealExpr :=
  .sub (.const p12)
    (.add (.add (.mul (.mul exprM11 exprM12) (.const p11))
                (.mul (.add (.mul exprM11 exprM22) (.mul exprM12 exprM21)) (.const p12)))
          (.mul (.mul exprM21 exprM22) (.const p22)))
def exprQ22 (p11 p12 p22 eps : CanonicalRat) : RealExpr :=
  .sub (.sub (.const p22)
      (.add (.add (.mul (.mul exprM12 exprM12) (.const p11))
                  (.mul (.mul (.mul (.const 2) exprM12) exprM22) (.const p12)))
            (.mul (.mul exprM22 exprM22) (.const p22))))
    (.const eps)
def exprQdet (p11 p12 p22 eps : CanonicalRat) : RealExpr :=
  .sub (.mul (exprQ11 p11 p12 p22 eps) (exprQ22 p11 p12 p22 eps))
       (.mul (exprQ12 p11 p12 p22) (exprQ12 p11 p12 p22))

/-- The box checker: static minors on `(P, ε, c, m)` and interval evaluation of `q11 > 0`,
`q11 q22 − q12² ≥ 0` over the box. -/
def checkLoopLyapunovBox (box : List (String × Interval)) (p11 p12 p22 eps c m : CanonicalRat) : Bool :=
  lyapStaticOk p11 p12 p22 eps c m &&
  (match evalInterval box (exprQ11 p11 p12 p22 eps), evalInterval box (exprQdet p11 p12 p22 eps) with
   | some q11Iv, some detIv => decide (0 < q11Iv.lo) && decide (0 ≤ detIv.lo)
   | _, _ => false)

/-- The point assignment of a parameter quadruple. -/
def paramRho (a b kp ki : CanonicalRat) : String → CanonicalRat :=
  fun v => if v = "a" then a else if v = "b" then b else if v = "kp" then kp else if v = "ki" then ki else 0

/-- The box is the product of the four parameter intervals, in a fixed order. -/
def paramBox (aIv bIv kpIv kiIv : Interval) : List (String × Interval) :=
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
def lcDrivesPlant : RlPlant where
  rOhm   := CanonicalRat.mk 12 1000
  lHenry := CanonicalRat.mk 150 1000000

/-- `x = R Ts/L = 0.012 · 50e-6 / 150e-6 = 1/250`. -/
def lcDrivesX : CanonicalRat := CanonicalRat.mk 1 250

/-- The 20 kHz discretization. The pole is taken at the upper end of its enclosure
`[1 − x, 1 − x + x²/2] = [249/250, 124501/125000]`; `b = (1 − a)/R`. -/
def lcDrivesZoh : ZohRl where
  plant := lcDrivesPlant
  tsSec := CanonicalRat.mk 50 1000000
  a     := CanonicalRat.mk 124501 125000
  b     := CanonicalRat.mk 499 1500

/-- The gains of `apps/foc-hil/PiCurrentLoop.obend` (`kpGainPermille 400`, `kiGainPermille 50`):
`Kp = 0.4 V/A`, `Ki = 0.05 V/A` per sample. -/
def lcDrivesGains : PiGains where
  kp := CanonicalRat.mk 2 5
  ki := CanonicalRat.mk 1 20

/-- The parameter box: `a` in the exponential's enclosure, `b = (1 − a)/R` over that enclosure
(`[(1 − a_hi)/R, (1 − a_lo)/R] = [499/1500, 1/3]`), the gains as points. -/
def lcDrivesBox : List (String × Interval) :=
  paramBox ⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩
           ⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩
           ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 2 5⟩
           ⟨CanonicalRat.mk 1 20, CanonicalRat.mk 1 20⟩

/-- The certificate: `P` is the rounded solution of `MᵀPM − P = −I` at the box centre; `ε = 1/4`;
`c = 34 ≥ λ_max(P) ≈ 33.09`; `m = 4 ≤ λ_min(P) ≈ 4.30`; `ρ = 1 − ε/c = 135/136`. -/
def lcP11 : CanonicalRat := CanonicalRat.mk 112 25
def lcP12 : CanonicalRat := CanonicalRat.mk (-2247) 1000
def lcP22 : CanonicalRat := CanonicalRat.mk 3291 100
def lcEps : CanonicalRat := CanonicalRat.mk 1 4
def lcC : CanonicalRat := 34
def lcM : CanonicalRat := 4
def lcRho : CanonicalRat := CanonicalRat.mk 135 136

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
def rtlPiStep (kpMilli kiMilli errMa intMv : Int) : Int × Int :=
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

/-- Hardware Q32 fixed-point PI step matching `HDL.evalAluOp .qmul32` (`((err * k_q32) >>> 32)`):
gains scaled by $2^{32} / 1000$, products shifted right by 32 bits (`Int` Euclidean floor `/ 2^32`). -/
def rtlPiStepQ32 (kpQ32 kiQ32 errMa intMv : Int) : Int × Int :=
  let int' := intMv + (errMa * kiQ32) / 4294967296
  (int', (errMa * kpQ32) / 4294967296 + int')

/-- Each Q32 fixed-point shift loses strictly less than 1 LSB (`1 mV`). -/
theorem rtlPiStepQ32_within_lsb (kpQ32 kiQ32 errMa intMv : Int) :
    let (int', v) := rtlPiStepQ32 kpQ32 kiQ32 errMa intMv
    4294967296 * (int' - intMv) ≤ errMa * kiQ32 ∧
    errMa * kiQ32 < 4294967296 * (int' - intMv) + 4294967296 ∧
    4294967296 * (v - int') ≤ errMa * kpQ32 ∧
    errMa * kpQ32 < 4294967296 * (v - int') + 4294967296 := by
  dsimp only [rtlPiStepQ32]
  have h1 := Int.ediv_mul_le (errMa * kiQ32) (b := 4294967296) (by decide)
  have h2 := Int.lt_ediv_add_one_mul_self (errMa * kiQ32) (b := 4294967296) (by decide)
  have h3 := Int.ediv_mul_le (errMa * kpQ32) (b := 4294967296) (by decide)
  have h4 := Int.lt_ediv_add_one_mul_self (errMa * kpQ32) (b := 4294967296) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Strict interior of signed register and DAC rails; products are checked before shifting. -/
@[expose] def CurrentLoopNoSaturation (w : Nat) (dacMaxMv : Int) (q32 : Bool)
    (kp ki err intMv : Int) : Prop :=
  let lim : Int := 2 ^ (w - 1)
  let out := if q32 then rtlPiStepQ32 kp ki err intMv else rtlPiStep kp ki err intMv
  (-lim < intMv ∧ intMv < lim - 1) ∧
  (-lim < err * kp ∧ err * kp < lim - 1) ∧
  (-lim < err * ki ∧ err * ki < lim - 1) ∧
  (-lim < out.1 ∧ out.1 < lim - 1) ∧
  (-lim < out.2 ∧ out.2 < lim - 1) ∧
  (-dacMaxMv < out.2 ∧ out.2 < dacMaxMv)
instance (w : Nat) (dac : Int) (q : Bool) (kp ki e i : Int) :
    Decidable (CurrentLoopNoSaturation w dac q kp ki e i) := by
  unfold CurrentLoopNoSaturation; infer_instance
/-- For nonnegative PI gains the two ordered corners bound every intermediate state/error.
The check covers full multiplier products, accumulator and command, before finite-width encoding. -/
def checkCurrentLoopNoSaturation (w : Nat) (dacMaxMv : Int) (q32 : Bool)
    (kp ki errLo errHi intLo intHi : Int) : Bool :=
  decide (0 < w ∧ 0 < dacMaxMv ∧ 0 ≤ kp ∧ 0 ≤ ki ∧ errLo ≤ errHi ∧ intLo ≤ intHi) &&
  decide (CurrentLoopNoSaturation w dacMaxMv q32 kp ki errLo intLo) &&
  decide (CurrentLoopNoSaturation w dacMaxMv q32 kp ki errHi intHi)
theorem checkCurrentLoopNoSaturation_sound (w : Nat) (dac : Int) (q : Bool)
    (kp ki elo ehi ilo ihi : Int)
    (h : checkCurrentLoopNoSaturation w dac q kp ki elo ehi ilo ihi = true)
    (e i : Int) (he : elo ≤ e ∧ e ≤ ehi) (hi : ilo ≤ i ∧ i ≤ ihi) :
    CurrentLoopNoSaturation w dac q kp ki e i := by
  simp only [checkCurrentLoopNoSaturation, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, _, hkp, hki, _, _⟩, hlo⟩, hhi⟩ := h
  have hp0 := Int.mul_le_mul_of_nonneg_right he.1 hkp
  have hp1 := Int.mul_le_mul_of_nonneg_right he.2 hkp
  have hk0 := Int.mul_le_mul_of_nonneg_right he.1 hki
  have hk1 := Int.mul_le_mul_of_nonneg_right he.2 hki
  cases q <;> simp only [CurrentLoopNoSaturation, Bool.false_eq_true, ↓reduceIte,
    rtlPiStep, rtlPiStepQ32] at hlo hhi ⊢ <;> omega

/-- Encoding either accepted PI output in an actual signed register preserves its integer value. -/
theorem checkCurrentLoopNoSaturation_noWrap (w : Nat) (dac : Int) (q : Bool)
    (kp ki elo ehi ilo ihi : Int)
    (h : checkCurrentLoopNoSaturation w dac q kp ki elo ehi ilo ihi = true)
    (e i : Int) (he : elo ≤ e ∧ e ≤ ehi) (hi : ilo ≤ i ∧ i ≤ ihi) :
    let out := if q then rtlPiStepQ32 kp ki e i else rtlPiStep kp ki e i
    (BitVec.ofInt w out.1).toInt = out.1 ∧ (BitVec.ofInt w out.2).toInt = out.2 := by
  have hs := checkCurrentLoopNoSaturation_sound w dac q kp ki elo ehi ilo ihi h e i he hi
  have hw : 0 < w := by
    simp only [checkCurrentLoopNoSaturation, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1
  dsimp only [CurrentLoopNoSaturation] at hs
  dsimp only
  exact ⟨BitVec.toInt_ofInt_eq_self hw (by omega) (by omega),
    BitVec.toInt_ofInt_eq_self hw (by omega) (by omega)⟩
example : checkCurrentLoopNoSaturation 32 100 false 400 50 (-10) 10 (-20) 20 = true := by decide +kernel

/-! ## 8. Input-to-State Stability (ISS) & Quantized `rtlPiStep` Ultimate-Boundedness Ball -/

/-- Positive semidefiniteness of $V_P$ from `lyapStaticOk` (`P - m I ⪰ 0` and `m > 0`). -/
theorem quadForm_nonneg_of_static
    (p11 p12 p22 eps c m y1 y2 : CanonicalRat)
    (hStatic : lyapStaticOk p11 p12 p22 eps c m = true) :
    0 ≤ quadForm p11 p12 p22 y1 y2 := by
  unfold lyapStaticOk at hStatic
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hStatic
  obtain ⟨⟨⟨⟨⟨_, hm⟩, _⟩, _⟩, hm1⟩, hm2⟩ := hStatic
  have hM := quadForm_nonneg_of_minors (p11 - m) p12 (p22 - m) y1 y2 hm1 hm2
  have hMid : quadForm (p11 - m) p12 (p22 - m) y1 y2 =
      quadForm p11 p12 p22 y1 y2 - m * (y1 * y1 + y2 * y2) := by unfold quadForm; grind
  rw [hMid] at hM
  have hy1 := Interval.rat_sq_nonneg y1
  have hy2 := Interval.rat_sq_nonneg y2
  have hSum : 0 ≤ m * (y1 * y1 + y2 * y2) := Rat.mul_nonneg (by grind) (by grind)
  grind

/-- Exact rational Peter–Paul inequality: $\theta V_P(u + w) \le \theta(1 + \theta) V_P(u) + (1 + \theta) V_P(w)$. -/
theorem quadForm_peter_paul
    (p11 p12 p22 eps c m theta ux uz wx wz : CanonicalRat)
    (hStatic : lyapStaticOk p11 p12 p22 eps c m = true) :
    theta * quadForm p11 p12 p22 (ux + wx) (uz + wz) ≤
      theta * (1 + theta) * quadForm p11 p12 p22 ux uz + (1 + theta) * quadForm p11 p12 p22 wx wz := by
  have hNonneg := quadForm_nonneg_of_static p11 p12 p22 eps c m (theta * ux - wx) (theta * uz - wz) hStatic
  have hId : theta * (1 + theta) * quadForm p11 p12 p22 ux uz + (1 + theta) * quadForm p11 p12 p22 wx wz -
      theta * quadForm p11 p12 p22 (ux + wx) (uz + wz) =
      quadForm p11 p12 p22 (theta * ux - wx) (theta * uz - wz) := by unfold quadForm; grind
  grind

/-- **One-Step Perturbed Lyapunov ISS Inequality (`discrete_lyapunov_iss_step`)**. -/
theorem discrete_lyapunov_iss_step
    (p11 p12 p22 a11 a12 a21 a22 eps c m rho theta thetaInv x z wx wz : CanonicalRat)
    (hStatic : lyapStaticOk p11 p12 p22 eps c m = true)
    (hDyn : lyapDynamicOk p11 p12 p22 a11 a12 a21 a22 eps = true)
    (hrho : rho * c = c - eps) (hTheta : 0 < theta) (hInv : theta * thetaInv = 1) :
    quadForm p11 p12 p22 (mapX a11 a12 x z + wx) (mapZ a21 a22 x z + wz) ≤
      ((1 + theta) * rho) * quadForm p11 p12 p22 x z + ((1 + thetaInv) * c) * (wx * wx + wz * wz) := by
  have hPP := quadForm_peter_paul p11 p12 p22 eps c m theta (mapX a11 a12 x z) (mapZ a21 a22 x z) wx wz hStatic
  have hDec := discrete_lyapunov_decay p11 p12 p22 a11 a12 a21 a22 eps c m rho x z hStatic hDyn hrho
  have hWBound := (discrete_lyapunov_decay p11 p12 p22 a11 a12 a21 a22 eps c m rho wx wz hStatic hDyn hrho).2.2
  have h1 : theta * (1 + theta) * quadForm p11 p12 p22 (mapX a11 a12 x z) (mapZ a21 a22 x z) ≤
      theta * (1 + theta) * (rho * quadForm p11 p12 p22 x z) :=
    Rat.mul_le_mul_of_nonneg_left hDec.1 (Rat.mul_nonneg (by grind) (by grind))
  have h2 : (1 + theta) * quadForm p11 p12 p22 wx wz ≤ (1 + theta) * (c * (wx * wx + wz * wz)) :=
    Rat.mul_le_mul_of_nonneg_left hWBound (by grind)
  have hGainEq : theta * ((1 + thetaInv) * c) = (1 + theta) * c := by
    calc theta * ((1 + thetaInv) * c) = (theta + theta * thetaInv) * c := by grind
      _ = (1 + theta) * c := by rw [hInv]; grind
  have hScaled : theta * quadForm p11 p12 p22 (mapX a11 a12 x z + wx) (mapZ a21 a22 x z + wz) ≤
      theta * (((1 + theta) * rho) * quadForm p11 p12 p22 x z + ((1 + thetaInv) * c) * (wx * wx + wz * wz)) := by
    have hRhs : theta * (((1 + theta) * rho) * quadForm p11 p12 p22 x z + ((1 + thetaInv) * c) * (wx * wx + wz * wz)) =
        theta * (1 + theta) * (rho * quadForm p11 p12 p22 x z) + (1 + theta) * (c * (wx * wx + wz * wz)) := by
      calc theta * (((1 + theta) * rho) * quadForm p11 p12 p22 x z + ((1 + thetaInv) * c) * (wx * wx + wz * wz))
          = theta * (1 + theta) * (rho * quadForm p11 p12 p22 x z) + (theta * ((1 + thetaInv) * c)) * (wx * wx + wz * wz) := by grind
        _ = theta * (1 + theta) * (rho * quadForm p11 p12 p22 x z) + (1 + theta) * (c * (wx * wx + wz * wz)) := by rw [hGainEq]; grind
    rw [hRhs]; grind
  exact Rat.le_of_mul_le_mul_left hScaled hTheta

/-- **Universal Multi-Step ISS Ultimate-Boundedness Ball (`discrete_lyapunov_iss_ball`)**. -/
theorem discrete_lyapunov_iss_ball
    (p11 p12 p22 a11 a12 a21 a22 eps c m rho theta thetaInv rhoIss dSq rBall : CanonicalRat)
    (hStatic : lyapStaticOk p11 p12 p22 eps c m = true)
    (hDyn : lyapDynamicOk p11 p12 p22 a11 a12 a21 a22 eps = true)
    (hrho : rho * c = c - eps) (hTheta : 0 < theta) (hInv : theta * thetaInv = 1)
    (hRhoIssDef : rhoIss = (1 + theta) * rho) (hRhoIss0 : 0 ≤ rhoIss) (hRhoIss1 : rhoIss < 1)
    (hdSq0 : 0 ≤ dSq) (hBall : (1 - rhoIss) * rBall = ((1 + thetaInv) * c) * dSq)
    (traj : Nat → CanonicalRat × CanonicalRat)
    (hStep : ∀ j, ∃ wx wz,
      traj (j + 1) = (mapX a11 a12 (traj j).1 (traj j).2 + wx, mapZ a21 a22 (traj j).1 (traj j).2 + wz) ∧
      wx * wx + wz * wz ≤ dSq) :
    (∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 - rBall ≤
      ratPow rhoIss k * (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 - rBall)) ∧
    (∀ k, rBall < quadForm p11 p12 p22 (traj k).1 (traj k).2 →
      quadForm p11 p12 p22 (traj (k + 1)).1 (traj (k + 1)).2 < quadForm p11 p12 p22 (traj k).1 (traj k).2) ∧
    (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 ≤ rBall →
      ∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 ≤ rBall) ∧
    (∀ k, m * ((traj k).1 * (traj k).1) ≤
      ratPow rhoIss k * (c * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + rBall) := by
  have hcPos : 0 < c := by unfold lyapStaticOk at hStatic; simp only [Bool.and_eq_true, decide_eq_true_eq] at hStatic; grind
  have hmPos : 0 < m := by unfold lyapStaticOk at hStatic; simp only [Bool.and_eq_true, decide_eq_true_eq] at hStatic; exact hStatic.1.1.1.1.2
  have hThetaInvPos : 0 < thetaInv := by
    rcases @Rat.le_total thetaInv 0 with hle | hge
    · have := Rat.mul_le_mul_of_nonneg_left hle (by grind : 0 ≤ theta); grind
    · by_cases hz : thetaInv = 0; · rw [hz] at hInv; grind
      · grind
  have hKappaNonneg : 0 ≤ (1 + thetaInv) * c := Rat.mul_nonneg (by grind) (by grind)
  have hrBallNonneg : 0 ≤ rBall := by
    have hProd : (1 - rhoIss) * 0 ≤ (1 - rhoIss) * rBall := by
      rw [hBall]; have := Rat.mul_nonneg hKappaNonneg hdSq0; grind
    exact Rat.le_of_mul_le_mul_left hProd (by grind)
  have hOneStep : ∀ j, quadForm p11 p12 p22 (traj (j + 1)).1 (traj (j + 1)).2 - rBall ≤
      rhoIss * (quadForm p11 p12 p22 (traj j).1 (traj j).2 - rBall) := by
    intro j; obtain ⟨wx, wz, hEq, hwSq⟩ := hStep j
    have hIss := discrete_lyapunov_iss_step p11 p12 p22 a11 a12 a21 a22 eps c m rho theta thetaInv
      (traj j).1 (traj j).2 wx wz hStatic hDyn hrho hTheta hInv
    have hwScaled := Rat.mul_le_mul_of_nonneg_left hwSq hKappaNonneg
    have hNextEq : quadForm p11 p12 p22 (traj (j + 1)).1 (traj (j + 1)).2 =
        quadForm p11 p12 p22 (mapX a11 a12 (traj j).1 (traj j).2 + wx) (mapZ a21 a22 (traj j).1 (traj j).2 + wz) := by rw [hEq]
    rw [← hNextEq, ← hRhoIssDef] at hIss; rw [← hBall] at hwScaled; grind
  have hExcess : ∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 - rBall ≤
      ratPow rhoIss k * (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 - rBall) := by
    intro k; induction k with
    | zero => dsimp [ratPow]; grind
    | succ j ih =>
      have hj := hOneStep j; have hMul := Rat.mul_le_mul_of_nonneg_left ih hRhoIss0
      have hPow : ratPow rhoIss (j + 1) = rhoIss * ratPow rhoIss j := rfl
      rw [hPow]; grind
  refine ⟨hExcess, ?_, ?_, ?_⟩
  · intro k hOut; have hk := hOneStep k
    have hPos : 0 < (1 - rhoIss) * (quadForm p11 p12 p22 (traj k).1 (traj k).2 - rBall) :=
      Rat.mul_pos (by grind) (by grind)
    grind
  · intro hIn0 k; have hk := hExcess k
    have hNonpos := Rat.mul_le_mul_of_nonneg_left (by grind : quadForm p11 p12 p22 (traj 0).1 (traj 0).2 - rBall ≤ 0)
      (ratPow_nonneg rhoIss hRhoIss0 k)
    grind
  · intro k; have hk := hExcess k; have hPow := ratPow_nonneg rhoIss hRhoIss0 k
    have hDecK := discrete_lyapunov_decay p11 p12 p22 a11 a12 a21 a22 eps c m rho (traj k).1 (traj k).2 hStatic hDyn hrho
    have hDec0 := discrete_lyapunov_decay p11 p12 p22 a11 a12 a21 a22 eps c m rho (traj 0).1 (traj 0).2 hStatic hDyn hrho
    have hmzk : 0 ≤ m * ((traj k).2 * (traj k).2) := Rat.mul_nonneg (by grind) (Interval.rat_sq_nonneg (traj k).2)
    have hDropBall := Rat.mul_le_mul_of_nonneg_left
      (by grind : quadForm p11 p12 p22 (traj 0).1 (traj 0).2 - rBall ≤ quadForm p11 p12 p22 (traj 0).1 (traj 0).2) hPow
    have hUp0 := Rat.mul_le_mul_of_nonneg_left hDec0.2.2 hPow
    grind

/-- Convert milli-units (`mA`, `mV`, `mΩ`) to `CanonicalRat` SI units (`A`, `V`, `Ω`). -/
@[expose] def ratMilli (n : Int) : CanonicalRat := (n : CanonicalRat) / 1000

/-- 1-mA ADC floor quantizer mapping continuous stator current `i` (A) to integer `mA`. -/
def adcFloorMa (i : CanonicalRat) : Int :=
  (1000 * i).floor

/-- `adcFloorMa i` under-approximates `1000 * i` within 1 mA (`1 LSB`):
`ratMilli (adcFloorMa i) ≤ i ∧ i ≤ ratMilli (adcFloorMa i) + ratMilli 1`. -/
theorem adcFloorMa_within_lsb (i : CanonicalRat) :
    ratMilli (adcFloorMa i) ≤ i ∧ i ≤ ratMilli (adcFloorMa i) + ratMilli 1 := by
  unfold adcFloorMa ratMilli
  have hLo : (((1000 * i).floor : Int) : CanonicalRat) ≤ 1000 * i := Rat.floor_le (1000 * i)
  have hHi : 1000 * i ≤ (((1000 * i).floor : Int) : CanonicalRat) + 1 := by
    have hLt := Rat.lt_floor_add_one (1000 * i)
    rw [Rat.intCast_add] at hLt
    exact Rat.le_of_lt hLt
  refine ⟨?_, ?_⟩ <;> grind

/-- Hybrid sampled-data state of the quantized RTL PI current loop:
continuous-amplitude physical current `i : CanonicalRat` (A) coupled to the exact integer hardware
integrator register `intMv : Int` (mV). -/
structure QuantizedLoopState where
  i     : CanonicalRat
  intMv : Int
  deriving DecidableEq, Repr

/-- Embed a `QuantizedLoopState` into the continuous `LoopState` (`int = ratMilli intMv`). -/
@[expose] def QuantizedLoopState.toLoopState (qs : QuantizedLoopState) : LoopState :=
  ⟨qs.i, ratMilli qs.intMv⟩

/-- One 20 kHz sample of the physical ZOH RL plant driven by the integer `rtlPiStep` controller
with 1-mA ADC quantization `adcFloorMa`:
1. `errMa = rMa - adcFloorMa qs.i`,
2. `(intMv', vPiMv) = rtlPiStep kpMilli kiMilli errMa qs.intMv`,
3. `i' = d.a * qs.i + d.b * ratMilli (vPiMv + vffMv)`. -/
def stepQuantizedRtlLoop
    (d : ZohRl) (kpMilli kiMilli rMa vffMv : Int) (qs : QuantizedLoopState) : QuantizedLoopState :=
  let errMa := rMa - adcFloorMa qs.i
  let (intMv', vPiMv) := rtlPiStep kpMilli kiMilli errMa qs.intMv
  ⟨d.a * qs.i + d.b * ratMilli (vPiMv + vffMv), intMv'⟩

/-- Iterate `stepQuantizedRtlLoop` for `k` 20 kHz control ticks. -/
def iterateQuantizedRtlLoop
    (d : ZohRl) (kpMilli kiMilli rMa vffMv : Int) : Nat → QuantizedLoopState → QuantizedLoopState
  | 0, qs => qs
  | k + 1, qs => iterateQuantizedRtlLoop d kpMilli kiMilli rMa vffMv k
      (stepQuantizedRtlLoop d kpMilli kiMilli rMa vffMv qs)

private theorem sq_le_of_bounds (w bnd : CanonicalRat)
    (hLo : -bnd ≤ w) (hHi : w ≤ bnd) : w * w ≤ bnd * bnd := by
  have hNonneg : 0 ≤ (bnd - w) * (bnd + w) := Rat.mul_nonneg (by grind) (by grind)
  grind

/-- **Exact Quantization Perturbation Theorem (`stepQuantizedRtlLoop_error_perturbation`)**. -/
theorem stepQuantizedRtlLoop_error_perturbation
    (d : ZohRl) (kpMilli kiMilli rMa vffMv : Int)
    (hKp0 : 0 ≤ kpMilli) (hKi0 : 0 ≤ kiMilli)
    (hb0 : 0 ≤ d.b) (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (qs : QuantizedLoopState) :
    let r := ratMilli rMa
    let vff := ratMilli vffMv
    let g : PiGains := ⟨ratMilli kpMilli, ratMilli kiMilli⟩
    let s := qs.toLoopState
    let sNext := (stepQuantizedRtlLoop d kpMilli kiMilli rMa vffMv qs).toLoopState
    ∃ wx wz : CanonicalRat,
      errX r sNext = mapX (m11 d g) (m12 d) (errX r s) (errZ d r vff s) + wx ∧
      errZ d r vff sNext = mapZ (m21 g) m22 (errX r s) (errZ d r vff s) + wz ∧
      wx * wx + wz * wz ≤
        (d.b * d.b * ((2 + g.kp + g.ki) * (2 + g.kp + g.ki)) + (1 + g.ki) * (1 + g.ki)) / 1000000 := by
  intro r vff g s sNext
  let errMa := rMa - adcFloorMa qs.i
  have hLsb := rtlPiStep_within_lsb kpMilli kiMilli errMa qs.intMv
  let intMv' := (rtlPiStep kpMilli kiMilli errMa qs.intMv).1
  let vPiMv := (rtlPiStep kpMilli kiMilli errMa qs.intMv).2
  have hAdc := adcFloorMa_within_lsb qs.i
  have hIdeal := stepLoop_error_dynamics d g r vff s hbR
  let sIdeal := stepLoop d g r vff s
  let wx := errX r sNext - errX r sIdeal
  let wz := errZ d r vff sNext - errZ d r vff sIdeal
  refine ⟨wx, wz, ?_, ?_, ?_⟩
  · unfold mapX; rw [← hIdeal.1]; dsimp [wx]; grind
  · unfold mapZ; rw [← hIdeal.2]; dsimp [wz]; grind
  · have hKiLoRat : (1000 : CanonicalRat) * ((intMv' : CanonicalRat) - (qs.intMv : CanonicalRat)) ≤
        (errMa : CanonicalRat) * (kiMilli : CanonicalRat) := by
      have h : 1000 * (intMv' - qs.intMv) ≤ errMa * kiMilli := hLsb.1
      simpa [Rat.intCast_mul, Rat.intCast_sub] using Rat.intCast_le_intCast.mpr h
    have hKiHiRat : (errMa : CanonicalRat) * (kiMilli : CanonicalRat) ≤
        (1000 : CanonicalRat) * ((intMv' : CanonicalRat) - (qs.intMv : CanonicalRat)) + 1000 := by
      have h : errMa * kiMilli ≤ 1000 * (intMv' - qs.intMv) + 1000 := Int.le_of_lt hLsb.2.1
      simpa [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_sub] using Rat.intCast_le_intCast.mpr h
    have hKpLoRat : (1000 : CanonicalRat) * ((vPiMv : CanonicalRat) - (intMv' : CanonicalRat)) ≤
        (errMa : CanonicalRat) * (kpMilli : CanonicalRat) := by
      have h : 1000 * (vPiMv - intMv') ≤ errMa * kpMilli := hLsb.2.2.1
      simpa [Rat.intCast_mul, Rat.intCast_sub] using Rat.intCast_le_intCast.mpr h
    have hKpHiRat : (errMa : CanonicalRat) * (kpMilli : CanonicalRat) ≤
        (1000 : CanonicalRat) * ((vPiMv : CanonicalRat) - (intMv' : CanonicalRat)) + 1000 := by
      have h : errMa * kpMilli ≤ 1000 * (vPiMv - intMv') + 1000 := Int.le_of_lt hLsb.2.2.2
      simpa [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_sub] using Rat.intCast_le_intCast.mpr h
    have hKpNonneg : 0 ≤ g.kp := by dsimp [g, ratMilli]; have := Rat.intCast_le_intCast.mpr hKp0; grind
    have hKiNonneg : 0 ≤ g.ki := by dsimp [g, ratMilli]; have := Rat.intCast_le_intCast.mpr hKi0; grind
    have hSub : ((rMa - adcFloorMa qs.i : Int) : CanonicalRat) = (rMa : CanonicalRat) - (adcFloorMa qs.i : CanonicalRat) :=
      Rat.intCast_sub rMa (adcFloorMa qs.i)
    have hErrHatLo : r - qs.i ≤ ratMilli errMa := by dsimp [r, errMa, ratMilli] at hAdc ⊢; rw [hSub]; grind
    have hErrHatHi : ratMilli errMa ≤ (r - qs.i) + 1 / 1000 := by dsimp [r, errMa, ratMilli] at hAdc ⊢; rw [hSub]; grind
    have hKiAdcLo := Rat.mul_le_mul_of_nonneg_left hErrHatLo hKiNonneg
    have hKiAdcHi := Rat.mul_le_mul_of_nonneg_left hErrHatHi hKiNonneg
    have hKpAdcLo := Rat.mul_le_mul_of_nonneg_left hErrHatLo hKpNonneg
    have hKpAdcHi := Rat.mul_le_mul_of_nonneg_left hErrHatHi hKpNonneg
    have hKiProdEq : g.ki * ratMilli errMa = ((errMa : CanonicalRat) * (kiMilli : CanonicalRat)) / 1000000 := by dsimp [g, ratMilli]; grind
    have hKpProdEq : g.kp * ratMilli errMa = ((errMa : CanonicalRat) * (kpMilli : CanonicalRat)) / 1000000 := by dsimp [g, ratMilli]; grind
    rw [hKiProdEq] at hKiAdcLo hKiAdcHi; rw [hKpProdEq] at hKpAdcLo hKpAdcHi
    have hwzEq : wz = ratMilli intMv' - ratMilli qs.intMv - g.ki * (r - qs.i) := by
      dsimp [wz, sNext, sIdeal, s, QuantizedLoopState.toLoopState, stepQuantizedRtlLoop, stepLoop, errZ, intMv', errMa]; grind
    have hwxEq : wx = d.b * ((ratMilli vPiMv - ratMilli intMv' - g.kp * (r - qs.i)) + wz) := by
      dsimp [wx, wz, sNext, sIdeal, s, QuantizedLoopState.toLoopState, stepQuantizedRtlLoop, stepLoop, errX, errZ, vff, intMv', vPiMv, errMa]
      have hAdd : ratMilli (vPiMv + vffMv) = ratMilli vPiMv + ratMilli vffMv := by dsimp [ratMilli]; rw [Rat.intCast_add]; grind
      rw [hAdd]; grind
    have hIntStepLo : ((errMa : CanonicalRat) * (kiMilli : CanonicalRat)) / 1000000 - 1 / 1000 ≤
        ratMilli intMv' - ratMilli qs.intMv := by dsimp [ratMilli]; grind
    have hIntStepHi : ratMilli intMv' - ratMilli qs.intMv ≤
        ((errMa : CanonicalRat) * (kiMilli : CanonicalRat)) / 1000000 := by dsimp [ratMilli]; grind
    have hPropStepLo : ((errMa : CanonicalRat) * (kpMilli : CanonicalRat)) / 1000000 - 1 / 1000 ≤
        ratMilli vPiMv - ratMilli intMv' := by dsimp [ratMilli]; grind
    have hPropStepHi : ratMilli vPiMv - ratMilli intMv' ≤
        ((errMa : CanonicalRat) * (kpMilli : CanonicalRat)) / 1000000 := by dsimp [ratMilli]; grind
    have hwzLo : -((1 + g.ki) / 1000) ≤ wz := by rw [hwzEq]; grind
    have hwzHi : wz ≤ (1 + g.ki) / 1000 := by rw [hwzEq]; grind
    have hvDiffLo : -((2 + g.kp + g.ki) / 1000) ≤ (ratMilli vPiMv - ratMilli intMv' - g.kp * (r - qs.i)) + wz := by grind
    have hvDiffHi : (ratMilli vPiMv - ratMilli intMv' - g.kp * (r - qs.i)) + wz ≤ (2 + g.kp + g.ki) / 1000 := by grind
    have hwxLo : -(d.b * ((2 + g.kp + g.ki) / 1000)) ≤ wx := by
      rw [hwxEq]; have := Rat.mul_le_mul_of_nonneg_left hvDiffLo hb0; grind
    have hwxHi : wx ≤ d.b * ((2 + g.kp + g.ki) / 1000) := by
      rw [hwxEq]; exact Rat.mul_le_mul_of_nonneg_left hvDiffHi hb0
    have hwzSq := sq_le_of_bounds wz ((1 + g.ki) / 1000) hwzLo hwzHi
    have hwxSq := sq_le_of_bounds wx (d.b * ((2 + g.kp + g.ki) / 1000)) hwxLo hwxHi
    grind

/-- **Universal Quantized Closed-Loop ISS Ball Theorem (`quantized_current_loop_iss_ball`)**. -/
theorem quantized_current_loop_iss_ball
    (aIv bIv kpIv kiIv : Interval)
    (p11 p12 p22 eps c m rho theta thetaInv rhoIss dSq rBall : CanonicalRat)
    (hCheck : checkLoopLyapunovBox (paramBox aIv bIv kpIv kiIv) p11 p12 p22 eps c m = true)
    (hrho : rho * c = c - eps) (hTheta : 0 < theta) (hInv : theta * thetaInv = 1)
    (hRhoIssDef : rhoIss = (1 + theta) * rho) (hRhoIss0 : 0 ≤ rhoIss) (hRhoIss1 : rhoIss < 1)
    (hBall : (1 - rhoIss) * rBall = ((1 + thetaInv) * c) * dSq)
    (d : ZohRl) (kpMilli kiMilli : Int)
    (hKp0 : 0 ≤ kpMilli) (hKi0 : 0 ≤ kiMilli) (hb0 : 0 ≤ d.b)
    (ha : d.a ∈ aIv) (hb : d.b ∈ bIv)
    (hkp : ratMilli kpMilli ∈ kpIv) (hki : ratMilli kiMilli ∈ kiIv)
    (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (hdSqBound :
      (d.b * d.b * ((2 + ratMilli kpMilli + ratMilli kiMilli) * (2 + ratMilli kpMilli + ratMilli kiMilli)) +
        (1 + ratMilli kiMilli) * (1 + ratMilli kiMilli)) / 1000000 ≤ dSq)
    (rMa vffMv : Int) (qs0 : QuantizedLoopState) :
    let r := ratMilli rMa
    let vff := ratMilli vffMv
    let traj : Nat → CanonicalRat × CanonicalRat := fun k =>
      let s := (iterateQuantizedRtlLoop d kpMilli kiMilli rMa vffMv k qs0).toLoopState
      (errX r s, errZ d r vff s)
    (∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 - rBall ≤
      ratPow rhoIss k * (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 - rBall)) ∧
    (∀ k, rBall < quadForm p11 p12 p22 (traj k).1 (traj k).2 →
      quadForm p11 p12 p22 (traj (k + 1)).1 (traj (k + 1)).2 < quadForm p11 p12 p22 (traj k).1 (traj k).2) ∧
    (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 ≤ rBall →
      ∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 ≤ rBall) ∧
    (∀ k, m * ((traj k).1 * (traj k).1) ≤
      ratPow rhoIss k * (c * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + rBall) := by
  intro r vff traj
  obtain ⟨hStatic, hDyn⟩ := checkLoopLyapunovBox_sound aIv bIv kpIv kiIv p11 p12 p22 eps c m hCheck
    d.a d.b (ratMilli kpMilli) (ratMilli kiMilli) ha hb hkp hki
  have hIterStep : ∀ j (qs : QuantizedLoopState),
      iterateQuantizedRtlLoop d kpMilli kiMilli rMa vffMv (j + 1) qs =
        stepQuantizedRtlLoop d kpMilli kiMilli rMa vffMv (iterateQuantizedRtlLoop d kpMilli kiMilli rMa vffMv j qs) := by
    intro j; induction j with
    | zero => intro qs; rfl
    | succ n ih => intro qs; exact ih (stepQuantizedRtlLoop d kpMilli kiMilli rMa vffMv qs)
  have hdSq0 : 0 ≤ dSq := by
    have hSq1 := Interval.rat_sq_nonneg (d.b * (2 + ratMilli kpMilli + ratMilli kiMilli))
    have hSq2 := Interval.rat_sq_nonneg (1 + ratMilli kiMilli); grind
  apply discrete_lyapunov_iss_ball p11 p12 p22
    (d.a - d.b * (ratMilli kpMilli + ratMilli kiMilli)) d.b (-ratMilli kiMilli) 1
    eps c m rho theta thetaInv rhoIss dSq rBall
    hStatic hDyn hrho hTheta hInv hRhoIssDef hRhoIss0 hRhoIss1 hdSq0 hBall traj
  intro j
  obtain ⟨wx, wz, hEx, hEz, hwSq⟩ := stepQuantizedRtlLoop_error_perturbation d kpMilli kiMilli rMa vffMv hKp0 hKi0 hb0 hbR
    (iterateQuantizedRtlLoop d kpMilli kiMilli rMa vffMv j qs0)
  refine ⟨wx, wz, ?_, by grind⟩
  dsimp only [traj]; rw [hIterStep j qs0]
  exact Prod.ext (by simpa [m11, m12] using hEx) (by simpa [m21, m22] using hEz)

/-- LC Drives quantized ISS parameters (`ρ_iss = 271/272`, `dSq = 2/10^6`, `R_ball = 626552/125000`). -/
def lcTheta : CanonicalRat := CanonicalRat.mk 1 270
def lcThetaInv : CanonicalRat := 270
def lcRhoIss : CanonicalRat := CanonicalRat.mk 271 272
def lcQuantDSq : CanonicalRat := CanonicalRat.mk 2 1000000
def lcIssBallRadius : CanonicalRat := CanonicalRat.mk 626552 125000

/-- **LC Drives 20 kHz Quantized `rtlPiStep` ISS Ultimate-Boundedness (`lc_drives_quantized_current_loop_iss_ball`)**. -/
theorem lc_drives_quantized_current_loop_iss_ball
    (d : ZohRl)
    (ha : d.a ∈ (⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩ : Interval))
    (hb : d.b ∈ (⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩ : Interval))
    (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (rMa vffMv : Int) (qs0 : QuantizedLoopState) :
    let r := ratMilli rMa
    let vff := ratMilli vffMv
    let traj : Nat → CanonicalRat × CanonicalRat := fun k =>
      let s := (iterateQuantizedRtlLoop d 400 50 rMa vffMv k qs0).toLoopState
      (errX r s, errZ d r vff s)
    (∀ k, quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 - lcIssBallRadius ≤
      ratPow lcRhoIss k * (quadForm lcP11 lcP12 lcP22 (traj 0).1 (traj 0).2 - lcIssBallRadius)) ∧
    (∀ k, lcIssBallRadius < quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 →
      quadForm lcP11 lcP12 lcP22 (traj (k + 1)).1 (traj (k + 1)).2 <
        quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2) ∧
    (quadForm lcP11 lcP12 lcP22 (traj 0).1 (traj 0).2 ≤ lcIssBallRadius →
      ∀ k, quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 ≤ lcIssBallRadius) ∧
    (∀ k, lcM * ((traj k).1 * (traj k).1) ≤
      ratPow lcRhoIss k * (lcC * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + lcIssBallRadius) := by
  have hc := lc_drives_box_certificate
  have hb0 : 0 ≤ d.b := by
    rw [Interval.mem_iff] at hb; have : (0 : CanonicalRat) ≤ CanonicalRat.mk 499 1500 := by decide +kernel
    grind
  have hbHi : d.b ≤ CanonicalRat.mk 1 3 := (Interval.mem_iff _ _).mp hb |>.2
  have hdSq :
      (d.b * d.b * ((2 + ratMilli 400 + ratMilli 50) * (2 + ratMilli 400 + ratMilli 50)) +
        (1 + ratMilli 50) * (1 + ratMilli 50)) / 1000000 ≤ lcQuantDSq := by
    have hbsq : d.b * d.b ≤ CanonicalRat.mk 1 3 * CanonicalRat.mk 1 3 := by
      have h1 := Rat.mul_le_mul_of_nonneg_left hbHi hb0
      have h2 := Rat.mul_le_mul_of_nonneg_right hbHi (by decide +kernel : (0 : CanonicalRat) ≤ CanonicalRat.mk 1 3); grind
    have hK1 : (2 + ratMilli 400 + ratMilli 50) * (2 + ratMilli 400 + ratMilli 50) = CanonicalRat.mk 2401 400 := by decide +kernel
    have hK2 : (1 + ratMilli 50) * (1 + ratMilli 50) = CanonicalRat.mk 441 400 := by decide +kernel
    rw [hK1, hK2]
    have hScaled := Rat.mul_le_mul_of_nonneg_right hbsq (by decide +kernel : (0 : CanonicalRat) ≤ CanonicalRat.mk 2401 400)
    have hTop : CanonicalRat.mk 1 3 * CanonicalRat.mk 1 3 * CanonicalRat.mk 2401 400 + CanonicalRat.mk 441 400 ≤ 2 := by decide +kernel
    dsimp [lcQuantDSq]
    have hConst : CanonicalRat.mk 2 1000000 = (2 : CanonicalRat) / 1000000 := by decide +kernel
    rw [hConst]; grind
  exact quantized_current_loop_iss_ball
    ⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩ ⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩
    ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 2 5⟩ ⟨CanonicalRat.mk 1 20, CanonicalRat.mk 1 20⟩
    lcP11 lcP12 lcP22 lcEps lcC lcM lcRho lcTheta lcThetaInv lcRhoIss lcQuantDSq lcIssBallRadius
    hc.1 hc.2.1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    d 400 50 (by decide) (by decide) hb0 ha hb (by decide +kernel) (by decide +kernel) hbR hdSq rMa vffMv qs0

/-! ## 9. SiC Dead-Time + Q32 Quantization ISS, Coupled Rotor Back-EMF & Continuous Inter-Sample Tube -/

/-- Convert Q32 fixed-point gain (`kpQ32`, `kiQ32`) into SI `CanonicalRat` gain (`V/A`). -/
@[expose] def ratQ32 (n : Int) : CanonicalRat := (n : CanonicalRat) / 4294967296

/-- Peak phase-voltage disturbance magnitude `Δv_dt = (2 td / T_pwm) V_dc` introduced by SiC half-bridge
interlocking blanking dead-time `td` over switching period `tPwm` at DC-link voltage `vdc`. -/
def deadTimeVoltBound (vdc td tPwm : CanonicalRat) : CanonicalRat :=
  (2 * td / tPwm) * vdc

/-- One hybrid sample of the ZOH stator axis driven by hardware Q32 fixed-point `rtlPiStepQ32`,
1-mA ADC floor quantization `adcFloorMa`, and SiC inverter dead-time voltage disturbance `vDt`. -/
def stepDeadTimeQ32Loop
    (d : ZohRl) (kpQ32 kiQ32 rMa vffMv : Int) (vDt : CanonicalRat) (qs : QuantizedLoopState) :
    QuantizedLoopState :=
  let errMa := rMa - adcFloorMa qs.i
  let (intMv', vPiMv) := rtlPiStepQ32 kpQ32 kiQ32 errMa qs.intMv
  ⟨d.a * qs.i + d.b * (ratMilli (vPiMv + vffMv) + vDt), intMv'⟩

/-- Multi-step trajectory of `stepDeadTimeQ32Loop` under time-varying dead-time sequence `vDtSeq`. -/
def runDeadTimeQ32Loop
    (d : ZohRl) (kpQ32 kiQ32 rMa vffMv : Int) (vDtSeq : Nat → CanonicalRat)
    (qs0 : QuantizedLoopState) : Nat → QuantizedLoopState
  | 0 => qs0
  | k + 1 => stepDeadTimeQ32Loop d kpQ32 kiQ32 rMa vffMv (vDtSeq k)
      (runDeadTimeQ32Loop d kpQ32 kiQ32 rMa vffMv vDtSeq qs0 k)

/-- **Composite Dead-Time + Q32 Quantization Perturbation Bound (`stepDeadTimeQ32Loop_error_perturbation`)**:
Under `rtlPiStepQ32_within_lsb`, `adcFloorMa_within_lsb`, and `|vDt| ≤ vDtMax`, one sample of
`stepDeadTimeQ32Loop` equals the linear error map `M` plus disturbance `(wx, wz)` satisfying
`wx² + wz² ≤ d.b² ((2 + Kp + Ki)/1000 + vDtMax)² + ((1 + Ki)/1000)²`. -/
theorem stepDeadTimeQ32Loop_error_perturbation
    (d : ZohRl) (kpQ32 kiQ32 rMa vffMv : Int) (vDt vDtMax : CanonicalRat)
    (hKp0 : 0 ≤ kpQ32) (hKi0 : 0 ≤ kiQ32) (hb0 : 0 ≤ d.b)
    (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (hDtLo : -vDtMax ≤ vDt) (hDtHi : vDt ≤ vDtMax)
    (qs : QuantizedLoopState) :
    let r := ratMilli rMa
    let vff := ratMilli vffMv
    let g : PiGains := ⟨ratQ32 kpQ32, ratQ32 kiQ32⟩
    let s := qs.toLoopState
    let sNext := (stepDeadTimeQ32Loop d kpQ32 kiQ32 rMa vffMv vDt qs).toLoopState
    ∃ wx wz : CanonicalRat,
      errX r sNext = mapX (m11 d g) (m12 d) (errX r s) (errZ d r vff s) + wx ∧
      errZ d r vff sNext = mapZ (m21 g) m22 (errX r s) (errZ d r vff s) + wz ∧
      wx * wx + wz * wz ≤
        d.b * d.b * (((2 + g.kp + g.ki) / 1000 + vDtMax) * ((2 + g.kp + g.ki) / 1000 + vDtMax)) +
          ((1 + g.ki) / 1000) * ((1 + g.ki) / 1000) := by
  intro r vff g s sNext
  let errMa := rMa - adcFloorMa qs.i
  have hLsb := rtlPiStepQ32_within_lsb kpQ32 kiQ32 errMa qs.intMv
  let intMv' := (rtlPiStepQ32 kpQ32 kiQ32 errMa qs.intMv).1
  let vPiMv := (rtlPiStepQ32 kpQ32 kiQ32 errMa qs.intMv).2
  have hAdc := adcFloorMa_within_lsb qs.i
  have hIdeal := stepLoop_error_dynamics d g r vff s hbR
  let sIdeal := stepLoop d g r vff s
  let wx := errX r sNext - errX r sIdeal
  let wz := errZ d r vff sNext - errZ d r vff sIdeal
  refine ⟨wx, wz, ?_, ?_, ?_⟩
  · unfold mapX; rw [← hIdeal.1]; dsimp [wx]; grind
  · unfold mapZ; rw [← hIdeal.2]; dsimp [wz]; grind
  · have hKiLoRat : (4294967296 : CanonicalRat) * ((intMv' : CanonicalRat) - (qs.intMv : CanonicalRat)) ≤
        (errMa : CanonicalRat) * (kiQ32 : CanonicalRat) := by
      have h : 4294967296 * (intMv' - qs.intMv) ≤ errMa * kiQ32 := hLsb.1
      simpa [Rat.intCast_mul, Rat.intCast_sub] using Rat.intCast_le_intCast.mpr h
    have hKiHiRat : (errMa : CanonicalRat) * (kiQ32 : CanonicalRat) ≤
        (4294967296 : CanonicalRat) * ((intMv' : CanonicalRat) - (qs.intMv : CanonicalRat)) + 4294967296 := by
      have h : errMa * kiQ32 ≤ 4294967296 * (intMv' - qs.intMv) + 4294967296 := Int.le_of_lt hLsb.2.1
      simpa [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_sub] using Rat.intCast_le_intCast.mpr h
    have hKpLoRat : (4294967296 : CanonicalRat) * ((vPiMv : CanonicalRat) - (intMv' : CanonicalRat)) ≤
        (errMa : CanonicalRat) * (kpQ32 : CanonicalRat) := by
      have h : 4294967296 * (vPiMv - intMv') ≤ errMa * kpQ32 := hLsb.2.2.1
      simpa [Rat.intCast_mul, Rat.intCast_sub] using Rat.intCast_le_intCast.mpr h
    have hKpHiRat : (errMa : CanonicalRat) * (kpQ32 : CanonicalRat) ≤
        (4294967296 : CanonicalRat) * ((vPiMv : CanonicalRat) - (intMv' : CanonicalRat)) + 4294967296 := by
      have h : errMa * kpQ32 ≤ 4294967296 * (vPiMv - intMv') + 4294967296 := Int.le_of_lt hLsb.2.2.2
      simpa [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_sub] using Rat.intCast_le_intCast.mpr h
    have hKpNonneg : 0 ≤ g.kp := by
      dsimp [g, ratQ32]; have := Rat.intCast_le_intCast.mpr hKp0; grind
    have hKiNonneg : 0 ≤ g.ki := by
      dsimp [g, ratQ32]; have := Rat.intCast_le_intCast.mpr hKi0; grind
    have hSub : ((rMa - adcFloorMa qs.i : Int) : CanonicalRat) = (rMa : CanonicalRat) - (adcFloorMa qs.i : CanonicalRat) :=
      Rat.intCast_sub rMa (adcFloorMa qs.i)
    have hErrHatLo : r - qs.i ≤ ratMilli errMa := by
      dsimp [r, errMa, ratMilli] at hAdc ⊢; rw [hSub]; grind
    have hErrHatHi : ratMilli errMa ≤ (r - qs.i) + 1 / 1000 := by
      dsimp [r, errMa, ratMilli] at hAdc ⊢; rw [hSub]; grind
    have hKiAdcLo := Rat.mul_le_mul_of_nonneg_left hErrHatLo hKiNonneg
    have hKiAdcHi := Rat.mul_le_mul_of_nonneg_left hErrHatHi hKiNonneg
    have hKpAdcLo := Rat.mul_le_mul_of_nonneg_left hErrHatLo hKpNonneg
    have hKpAdcHi := Rat.mul_le_mul_of_nonneg_left hErrHatHi hKpNonneg
    have hKiProd : g.ki * ratMilli errMa = ((errMa : CanonicalRat) * (kiQ32 : CanonicalRat)) / 4294967296000 := by
      dsimp [g, ratQ32, ratMilli]; grind
    have hKpProd : g.kp * ratMilli errMa = ((errMa : CanonicalRat) * (kpQ32 : CanonicalRat)) / 4294967296000 := by
      dsimp [g, ratQ32, ratMilli]; grind
    rw [hKiProd] at hKiAdcLo hKiAdcHi
    rw [hKpProd] at hKpAdcLo hKpAdcHi
    have hwzEq : wz = ratMilli intMv' - ratMilli qs.intMv - g.ki * (r - qs.i) := by
      dsimp [wz, sNext, sIdeal, s, QuantizedLoopState.toLoopState, stepDeadTimeQ32Loop, stepLoop, errZ, intMv', errMa]
      grind
    have hwxEq : wx = d.b * ((ratMilli vPiMv - ratMilli intMv' - g.kp * (r - qs.i)) + wz + vDt) := by
      dsimp [wx, wz, sNext, sIdeal, s, QuantizedLoopState.toLoopState, stepDeadTimeQ32Loop, stepLoop, errX, errZ, vff, intMv', vPiMv, errMa]
      have hAdd : ratMilli (vPiMv + vffMv) = ratMilli vPiMv + ratMilli vffMv := by
        dsimp [ratMilli]; rw [Rat.intCast_add]; grind
      rw [hAdd]; grind
    have hIntLo : ((errMa : CanonicalRat) * (kiQ32 : CanonicalRat)) / 4294967296000 - 1 / 1000 ≤
        ratMilli intMv' - ratMilli qs.intMv := by dsimp [ratMilli]; grind
    have hIntHi : ratMilli intMv' - ratMilli qs.intMv ≤
        ((errMa : CanonicalRat) * (kiQ32 : CanonicalRat)) / 4294967296000 := by dsimp [ratMilli]; grind
    have hPropLo : ((errMa : CanonicalRat) * (kpQ32 : CanonicalRat)) / 4294967296000 - 1 / 1000 ≤
        ratMilli vPiMv - ratMilli intMv' := by dsimp [ratMilli]; grind
    have hPropHi : ratMilli vPiMv - ratMilli intMv' ≤
        ((errMa : CanonicalRat) * (kpQ32 : CanonicalRat)) / 4294967296000 := by dsimp [ratMilli]; grind
    have hwzLo : -((1 + g.ki) / 1000) ≤ wz := by rw [hwzEq]; grind
    have hwzHi : wz ≤ (1 + g.ki) / 1000 := by rw [hwzEq]; grind
    have hvTotLo : -((2 + g.kp + g.ki) / 1000 + vDtMax) ≤
        (ratMilli vPiMv - ratMilli intMv' - g.kp * (r - qs.i)) + wz + vDt := by grind
    have hvTotHi : (ratMilli vPiMv - ratMilli intMv' - g.kp * (r - qs.i)) + wz + vDt ≤
        (2 + g.kp + g.ki) / 1000 + vDtMax := by grind
    have hwxLo : -(d.b * ((2 + g.kp + g.ki) / 1000 + vDtMax)) ≤ wx := by
      rw [hwxEq]; have := Rat.mul_le_mul_of_nonneg_left hvTotLo hb0; grind
    have hwxHi : wx ≤ d.b * ((2 + g.kp + g.ki) / 1000 + vDtMax) := by
      rw [hwxEq]; exact Rat.mul_le_mul_of_nonneg_left hvTotHi hb0
    have hwzSq := sq_le_of_bounds wz ((1 + g.ki) / 1000) hwzLo hwzHi
    have hwxSq := sq_le_of_bounds wx (d.b * ((2 + g.kp + g.ki) / 1000 + vDtMax)) hwxLo hwxHi
    grind

/-- **Composite SiC Dead-Time + Q32 Quantized ISS Theorem (`currentLoop_deadTime_and_quant_iss_ball`)**:
Under hardware Q32 PI truncation (`rtlPiStepQ32`), 1-mA ADC quantization (`adcFloorMa`), and SiC
half-bridge dead-time distortion `|vDtSeq k| ≤ (2 td / tPwm) vdc`, the closed-loop trajectory
contracts geometrically at rate `rhoIss` into the forward-invariant ISS ball `rBall`. -/
theorem currentLoop_deadTime_and_quant_iss_ball
    (aIv bIv kpIv kiIv : Interval)
    (p11 p12 p22 eps c m rho theta thetaInv rhoIss vdc td tPwm dSq rBall : CanonicalRat)
    (hCheck : checkLoopLyapunovBox (paramBox aIv bIv kpIv kiIv) p11 p12 p22 eps c m = true)
    (hrho : rho * c = c - eps)
    (hTheta : 0 < theta) (hInv : theta * thetaInv = 1)
    (hRhoIssDef : rhoIss = (1 + theta) * rho) (hRhoIss0 : 0 ≤ rhoIss) (hRhoIss1 : rhoIss < 1)
    (hBall : (1 - rhoIss) * rBall = ((1 + thetaInv) * c) * dSq)
    (d : ZohRl) (kpQ32 kiQ32 : Int)
    (hKp0 : 0 ≤ kpQ32) (hKi0 : 0 ≤ kiQ32) (hb0 : 0 ≤ d.b)
    (ha : d.a ∈ aIv) (hb : d.b ∈ bIv)
    (hkp : ratQ32 kpQ32 ∈ kpIv) (hki : ratQ32 kiQ32 ∈ kiIv)
    (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (hdSqBound :
      d.b * d.b * (((2 + ratQ32 kpQ32 + ratQ32 kiQ32) / 1000 + deadTimeVoltBound vdc td tPwm) *
        ((2 + ratQ32 kpQ32 + ratQ32 kiQ32) / 1000 + deadTimeVoltBound vdc td tPwm)) +
      ((1 + ratQ32 kiQ32) / 1000) * ((1 + ratQ32 kiQ32) / 1000) ≤ dSq)
    (rMa vffMv : Int) (vDtSeq : Nat → CanonicalRat)
    (hDtSeq : ∀ k, -deadTimeVoltBound vdc td tPwm ≤ vDtSeq k ∧ vDtSeq k ≤ deadTimeVoltBound vdc td tPwm)
    (qs0 : QuantizedLoopState) :
    let r := ratMilli rMa
    let vff := ratMilli vffMv
    let traj : Nat → CanonicalRat × CanonicalRat := fun k =>
      let s := (runDeadTimeQ32Loop d kpQ32 kiQ32 rMa vffMv vDtSeq qs0 k).toLoopState
      (errX r s, errZ d r vff s)
    (∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 - rBall ≤
      ratPow rhoIss k * (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 - rBall)) ∧
    (∀ k, rBall < quadForm p11 p12 p22 (traj k).1 (traj k).2 →
      quadForm p11 p12 p22 (traj (k + 1)).1 (traj (k + 1)).2 <
        quadForm p11 p12 p22 (traj k).1 (traj k).2) ∧
    (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 ≤ rBall →
      ∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 ≤ rBall) ∧
    (∀ k, m * ((traj k).1 * (traj k).1) ≤
      ratPow rhoIss k * (c * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + rBall) := by
  intro r vff traj
  obtain ⟨hStatic, hDyn⟩ := checkLoopLyapunovBox_sound aIv bIv kpIv kiIv p11 p12 p22 eps c m hCheck
    d.a d.b (ratQ32 kpQ32) (ratQ32 kiQ32) ha hb hkp hki
  have hdSq0 : 0 ≤ dSq := by
    have hSq1 := Interval.rat_sq_nonneg (d.b * ((2 + ratQ32 kpQ32 + ratQ32 kiQ32) / 1000 + deadTimeVoltBound vdc td tPwm))
    have hSq2 := Interval.rat_sq_nonneg ((1 + ratQ32 kiQ32) / 1000)
    grind
  apply discrete_lyapunov_iss_ball
    p11 p12 p22
    (d.a - d.b * (ratQ32 kpQ32 + ratQ32 kiQ32)) d.b (-ratQ32 kiQ32) 1
    eps c m rho theta thetaInv rhoIss dSq rBall
    hStatic hDyn hrho hTheta hInv hRhoIssDef hRhoIss0 hRhoIss1 hdSq0 hBall traj
  intro j
  obtain ⟨wx, wz, hEx, hEz, hwSq⟩ := stepDeadTimeQ32Loop_error_perturbation
    d kpQ32 kiQ32 rMa vffMv (vDtSeq j) (deadTimeVoltBound vdc td tPwm)
    hKp0 hKi0 hb0 hbR (hDtSeq j).1 (hDtSeq j).2
    (runDeadTimeQ32Loop d kpQ32 kiQ32 rMa vffMv vDtSeq qs0 j)
  refine ⟨wx, wz, ?_, by grind⟩
  exact Prod.ext (by simpa [traj, runDeadTimeQ32Loop, m11, m12] using hEx)
    (by simpa [traj, runDeadTimeQ32Loop, m21, m22] using hEz)

/-- One ZOH sample of the coupled q-axis stator current loop `L di_q/dt = v_q - R i_q - λ_m ω_e`. -/
def stepBackEmfLoop
    (d : ZohRl) (g : PiGains) (r vff lambdaM omegaE : CanonicalRat) (s : LoopState) : LoopState :=
  let e := r - s.i
  let int' := s.int + g.ki * e
  let vq := g.kp * e + int' + vff
  ⟨d.a * s.i + d.b * (vq - lambdaM * omegaE), int'⟩

/-- Multi-step trajectory of `stepBackEmfLoop` under time-varying rotor electrical speed `omegaSeq`. -/
def runBackEmfLoop
    (d : ZohRl) (g : PiGains) (r vff lambdaM : CanonicalRat)
    (omegaSeq : Nat → CanonicalRat) (s0 : LoopState) : Nat → LoopState
  | 0 => s0
  | k + 1 => stepBackEmfLoop d g r vff lambdaM (omegaSeq k)
      (runBackEmfLoop d g r vff lambdaM omegaSeq s0 k)

/-- Speed-referenced integrator error `int - (R r + λ_m ω_e - vff)` tracking moving rotor back-EMF. -/
def errZBackEmf (d : ZohRl) (r vff lambdaM omegaE : CanonicalRat) (s : LoopState) : CanonicalRat :=
  s.int - (d.plant.rOhm * r + lambdaM * omegaE - vff)

/-- **Coupled Rotor Speed `ω_e` Back-EMF ISS Theorem (`currentLoop_backEmf_coupled_iss_ball`)**:
For `L di_q/dt = v_q - R i_q - λ_m ω_e` under bounded rotor angular acceleration
`|ω_e[k+1] - ω_e[k]| ≤ α_max Ts`, the tracking error contracts geometrically into `rBall`
(and converges exponentially to `0` at constant speed `α_max = 0`). -/
theorem currentLoop_backEmf_coupled_iss_ball
    (aIv bIv kpIv kiIv : Interval)
    (p11 p12 p22 eps c m rho theta thetaInv rhoIss lambdaM alphaMax dSq rBall : CanonicalRat)
    (hCheck : checkLoopLyapunovBox (paramBox aIv bIv kpIv kiIv) p11 p12 p22 eps c m = true)
    (hrho : rho * c = c - eps)
    (hTheta : 0 < theta) (hInv : theta * thetaInv = 1)
    (hRhoIssDef : rhoIss = (1 + theta) * rho) (hRhoIss0 : 0 ≤ rhoIss) (hRhoIss1 : rhoIss < 1)
    (hBall : (1 - rhoIss) * rBall = ((1 + thetaInv) * c) * dSq)
    (d : ZohRl) (g : PiGains)
    (ha : d.a ∈ aIv) (hb : d.b ∈ bIv) (hkp : g.kp ∈ kpIv) (hki : g.ki ∈ kiIv)
    (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (hLam0 : 0 ≤ lambdaM)
    (hdSqBound : (lambdaM * (alphaMax * d.tsSec)) * (lambdaM * (alphaMax * d.tsSec)) ≤ dSq)
    (r vff : CanonicalRat) (omegaSeq : Nat → CanonicalRat)
    (hAccel : ∀ k, -(alphaMax * d.tsSec) ≤ omegaSeq (k + 1) - omegaSeq k ∧
      omegaSeq (k + 1) - omegaSeq k ≤ alphaMax * d.tsSec)
    (s0 : LoopState) :
    let traj : Nat → CanonicalRat × CanonicalRat := fun k =>
      let s := runBackEmfLoop d g r vff lambdaM omegaSeq s0 k
      (errX r s, errZBackEmf d r vff lambdaM (omegaSeq k) s)
    (∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 - rBall ≤
      ratPow rhoIss k * (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 - rBall)) ∧
    (∀ k, rBall < quadForm p11 p12 p22 (traj k).1 (traj k).2 →
      quadForm p11 p12 p22 (traj (k + 1)).1 (traj (k + 1)).2 <
        quadForm p11 p12 p22 (traj k).1 (traj k).2) ∧
    (quadForm p11 p12 p22 (traj 0).1 (traj 0).2 ≤ rBall →
      ∀ k, quadForm p11 p12 p22 (traj k).1 (traj k).2 ≤ rBall) ∧
    (∀ k, m * ((traj k).1 * (traj k).1) ≤
      ratPow rhoIss k * (c * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + rBall) := by
  intro traj
  obtain ⟨hStatic, hDyn⟩ := checkLoopLyapunovBox_sound aIv bIv kpIv kiIv p11 p12 p22 eps c m hCheck
    d.a d.b g.kp g.ki ha hb hkp hki
  have hdSq0 : 0 ≤ dSq := by
    have := Interval.rat_sq_nonneg (lambdaM * (alphaMax * d.tsSec)); grind
  apply discrete_lyapunov_iss_ball
    p11 p12 p22 (d.a - d.b * (g.kp + g.ki)) d.b (-g.ki) 1
    eps c m rho theta thetaInv rhoIss dSq rBall
    hStatic hDyn hrho hTheta hInv hRhoIssDef hRhoIss0 hRhoIss1 hdSq0 hBall traj
  intro j
  let sj := runBackEmfLoop d g r vff lambdaM omegaSeq s0 j
  have hStepEq : stepBackEmfLoop d g r vff lambdaM (omegaSeq j) sj =
      stepLoop d g r (vff - lambdaM * omegaSeq j) sj := by
    unfold stepBackEmfLoop stepLoop; congr 1; grind
  have hIdeal := stepLoop_error_dynamics d g r (vff - lambdaM * omegaSeq j) sj hbR
  let wz := -lambdaM * (omegaSeq (j + 1) - omegaSeq j)
  have hwzLo : -(lambdaM * (alphaMax * d.tsSec)) ≤ wz := by
    dsimp [wz]; have := Rat.mul_le_mul_of_nonneg_left (hAccel j).2 hLam0; grind
  have hwzHi : wz ≤ lambdaM * (alphaMax * d.tsSec) := by
    dsimp [wz]; have := Rat.mul_le_mul_of_nonneg_left (hAccel j).1 hLam0; grind
  have hwzSq := sq_le_of_bounds wz (lambdaM * (alphaMax * d.tsSec)) hwzLo hwzHi
  refine ⟨0, wz, ?_, by grind⟩
  apply Prod.ext
  · dsimp only [traj, runBackEmfLoop]
    rw [hStepEq, hIdeal.1]
    unfold mapX m11 m12 errZ errZBackEmf; grind
  · dsimp only [traj, runBackEmfLoop]
    rw [hStepEq]
    have hZShift : errZBackEmf d r vff lambdaM (omegaSeq (j + 1)) (stepLoop d g r (vff - lambdaM * omegaSeq j) sj) =
        errZ d r (vff - lambdaM * omegaSeq j) (stepLoop d g r (vff - lambdaM * omegaSeq j) sj) + wz := by
      unfold errZBackEmf errZ; dsimp [wz]; grind
    rw [hZShift, hIdeal.2]
    unfold mapZ m21 m22 errZ errZBackEmf; grind

/-- Continuous-time ZOH ODE current `i(k Ts + τ) = a_τ i_k + b_τ v_k` at inter-sample offset `τ ∈ [0, Ts]`. -/
def zohIntersampleCurrent (aTau bTau ik vk : CanonicalRat) : CanonicalRat :=
  aTau * ik + bTau * vk

/-- **Continuous-Time Inter-Sample Convex-Hull & Zero-Overshoot Theorem (`zoh_intersample_convex_hull_bound`)**:
Along the exact ZOH ODE solution `i(k Ts + τ) = e^{-Rτ/L} i_k + ((1 - e^{-Rτ/L})/R) v_k` for `τ ∈ [0, Ts]`
(where `d.a ≤ aTau ≤ 1` and `bTau * R = 1 - aTau`), `i(k Ts + τ)` is an exact convex combination of
`i_k` and `i_{k+1} = stepZoh d i_k v_k`, lies strictly between `i_k` and `i_{k+1}` for interior `d.a < aTau < 1`
whenever `i_k ≠ i_{k+1}`, and never overshoots `max((i_k - r)², (i_{k+1} - r)²)`. -/
theorem zoh_intersample_convex_hull_bound
    (d : ZohRl) (aTau bTau ik vk r : CanonicalRat)
    (hR : 0 < d.plant.rOhm) (ha1 : d.a < 1) (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (hLo : d.a ≤ aTau) (hHi : aTau ≤ 1) (hbTauR : bTau * d.plant.rOhm = 1 - aTau) :
    let iNext := stepZoh d ik vk
    let iTau := zohIntersampleCurrent aTau bTau ik vk
    let lam := (1 - aTau) / (1 - d.a)
    (0 ≤ lam ∧ lam ≤ 1) ∧
    iTau = (1 - lam) * ik + lam * iNext ∧
    (min ik iNext ≤ iTau ∧ iTau ≤ max ik iNext) ∧
    (d.a < aTau → aTau < 1 → ik ≠ iNext → min ik iNext < iTau ∧ iTau < max ik iNext) ∧
    (iTau - r) * (iTau - r) ≤ max ((ik - r) * (ik - r)) ((iNext - r) * (iNext - r)) := by
  intro iNext iTau lam
  have hDenPos : 0 < 1 - d.a := by grind
  have hLamCancel : lam * (1 - d.a) = 1 - aTau := by
    dsimp [lam]; grind
  have hLam0 : 0 ≤ lam := by
    have hMul : (1 - d.a) * 0 ≤ (1 - d.a) * lam := by
      have : (1 - d.a) * lam = 1 - aTau := by grind
      grind
    exact Rat.le_of_mul_le_mul_left hMul hDenPos
  have hLam1 : lam ≤ 1 := by
    have hMul : (1 - d.a) * lam ≤ (1 - d.a) * 1 := by
      have : (1 - d.a) * lam = 1 - aTau := by grind
      grind
    exact Rat.le_of_mul_le_mul_left hMul hDenPos
  have hScaledEq : d.plant.rOhm * iTau = d.plant.rOhm * ((1 - lam) * ik + lam * iNext) := by
    dsimp [iTau, iNext, zohIntersampleCurrent, stepZoh]
    have h1 : d.plant.rOhm * (aTau * ik + bTau * vk) =
        d.plant.rOhm * aTau * ik + (bTau * d.plant.rOhm) * vk := by grind
    have h2 : d.plant.rOhm * ((1 - lam) * ik + lam * (d.a * ik + d.b * vk)) =
        d.plant.rOhm * ((1 - lam * (1 - d.a)) * ik) + lam * ((d.b * d.plant.rOhm) * vk) := by grind
    rw [h1, hbTauR, h2, hbR, hLamCancel]
    grind
  have hConv : iTau = (1 - lam) * ik + lam * iNext :=
    Rat.le_antisymm
      (Rat.le_of_mul_le_mul_left (by grind) hR)
      (Rat.le_of_mul_le_mul_left (by grind) hR)
  have hBracket : min ik iNext ≤ iTau ∧ iTau ≤ max ik iNext := by
    rw [hConv]
    rcases @Rat.le_total ik iNext with hOrd | hOrd
    · have h1 := Rat.mul_le_mul_of_nonneg_left hOrd hLam0
      have h2 := Rat.mul_le_mul_of_nonneg_left hOrd (by grind : 0 ≤ 1 - lam)
      exact ⟨by grind, by grind⟩
    · have h1 := Rat.mul_le_mul_of_nonneg_left hOrd hLam0
      have h2 := Rat.mul_le_mul_of_nonneg_left hOrd (by grind : 0 ≤ 1 - lam)
      exact ⟨by grind, by grind⟩
  refine ⟨⟨hLam0, hLam1⟩, hConv, hBracket, ?_, ?_⟩
  · intro hStrictLo hStrictHi hNe
    have hLamPos : 0 < lam := by
      rcases @Rat.le_total lam 0 with hle | _
      · have := Rat.mul_le_mul_of_nonneg_right hle (by grind : 0 ≤ 1 - d.a); grind
      · by_cases hz : lam = 0
        · rw [hz] at hLamCancel; grind
        · grind
    have hOneSubPos : 0 < 1 - lam := by
      have hDiff : (1 - lam) * (1 - d.a) = aTau - d.a := by grind
      rcases @Rat.le_total (1 - lam) 0 with hle | _
      · have := Rat.mul_le_mul_of_nonneg_right hle (by grind : 0 ≤ 1 - d.a); grind
      · by_cases hz : 1 - lam = 0
        · rw [hz] at hDiff; grind
        · grind
    rw [hConv]
    rcases @Rat.le_total ik iNext with hOrd | hOrd
    · have hLt : ik < iNext := by grind
      have hP1 : 0 < lam * (iNext - ik) := Rat.mul_pos hLamPos (by grind)
      have hP2 : 0 < (1 - lam) * (iNext - ik) := Rat.mul_pos hOneSubPos (by grind)
      exact ⟨by grind, by grind⟩
    · have hLt : iNext < ik := by grind
      have hP1 : 0 < (1 - lam) * (ik - iNext) := Rat.mul_pos hOneSubPos (by grind)
      have hP2 : 0 < lam * (ik - iNext) := Rat.mul_pos hLamPos (by grind)
      exact ⟨by grind, by grind⟩
  · let u := ik - r
    let v := iNext - r
    have hShift : iTau - r = (1 - lam) * u + lam * v := by
      rw [hConv]; dsimp [u, v]; grind
    rw [hShift]
    have hQuadId : ((1 - lam) * u + lam * v) * ((1 - lam) * u + lam * v) =
        (1 - lam) * (u * u) + lam * (v * v) - lam * (1 - lam) * ((u - v) * (u - v)) := by grind
    have hNonnegTerm : 0 ≤ lam * (1 - lam) * ((u - v) * (u - v)) :=
      Rat.mul_nonneg (Rat.mul_nonneg hLam0 (by grind)) (Interval.rat_sq_nonneg (u - v))
    let mSq := max (u * u) (v * v)
    have hU : (1 - lam) * (u * u) ≤ (1 - lam) * mSq :=
      Rat.mul_le_mul_of_nonneg_left (by dsimp [mSq]; grind) (by grind)
    have hV : lam * (v * v) ≤ lam * mSq :=
      Rat.mul_le_mul_of_nonneg_left (by dsimp [mSq]; grind) hLam0
    change ((1 - lam) * u + lam * v) * ((1 - lam) * u + lam * v) ≤ mSq
    grind

end Obend.Hardware.CurrentLoop
end
