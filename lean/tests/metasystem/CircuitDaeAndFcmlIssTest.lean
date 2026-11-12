import Obend.Hardware.CircuitDae
import Obend.Hardware.CurrentLoop
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/CircuitDaeAndFcmlIssTest.lean`

End-to-end concrete & universal verification of:
1. **LC Drives Stator Current Loop (`R = 12 mΩ`, `L = 150 µH`, `Ts = 50 µs`, `Vdc = 800 V`, `td = 200 ns` SiC dead-time)**:
   - Composite Q32 hardware PI + 1-mA ADC + 6.4 V SiC dead-time ISS ultimate-boundedness (`currentLoop_deadTime_and_quant_iss_ball`),
   - Coupled rotor electrical speed `ω_e` back-EMF ISS tracking under bounded acceleration (`currentLoop_backEmf_coupled_iss_ball`),
   - Continuous-time inter-sample ZOH current convex-hull & zero-overshoot tube (`zoh_intersample_convex_hull_bound`).
2. **5-Cell (6-Level) 800 V SiC Flying-Capacitor Multilevel (`FCML`) Hybrid Capacitor Balance (`160 V, 320 V, 480 V, 640 V`)**:
   - Exact 6-level KVL ladder, instantaneous KCL/KVL power conservation, symmetric 5-phase PSP zero-net-charge-drift (`fcml_psp_nominal_zero_drift`),
   - Saturated active duty-trim Lyapunov contraction & per-cell SiC FET blocking safety (`fcml_active_trim_contracts_unbalance`).
3. **Index-1 MNA Circuit DAE Judge (`"mna-dae@1"`, `mnaCircuitDaeJudge`, `mnaCircuitDaeFormat`)**:
   - Backward-Euler & Trapezoidal RC + passive half-wave diode rectifier traces, wire JSON roundtrip, monotonic stored energy decay,
   - Planted non-passive negative-conductance and residual-violating refusals with universal semantic impossibility.
4. **`#tooth` Mutation Kills (`6` witnesses) & `#assert_axioms_tree` Purity Census.**
-/

namespace Obend.Tests.CircuitDaeAndFcmlIssTest

open Obend
open Obend.Analysis
open Obend.Hardware.CircuitDae
open Obend.Hardware.CurrentLoop

set_option autoImplicit false

-- ============================================================================
-- 1. LC Drives (`R = 12 mΩ`, `L = 150 µH`, `Ts = 50 µs`, `Vdc = 800 V`, `td = 200 ns`)
-- ============================================================================

/-- 800 V DC bus, 200 ns SiC interlocking dead-time, and 50 µs (20 kHz) PWM period (`Δv_dt = 32/5 = 6.4 V`). -/
def lcVdc800 : CanonicalRat := 800
def lcSicDeadTime200ns : CanonicalRat := CanonicalRat.mk 1 5000000
def lcPwmPeriod50us : CanonicalRat := CanonicalRat.mk 1 20000

/-- Hardware Q32 fixed-point PI gains corresponding to `Kp ≈ 0.4 V/A` and `Ki ≈ 0.05 V/A`. -/
def lcKpQ32 : Int := 1717986918
def lcKiQ32 : Int := 214748365

/-- Composite disturbance energy bound `dSq = 5` and corresponding ISS ball `rBall = 12531040`. -/
def lcDeadTimeDSq : CanonicalRat := 5
def lcDeadTimeIssBall : CanonicalRat := 12531040

example :
    lcDrivesPlant.rOhm = CanonicalRat.mk 12 1000 ∧
    lcDrivesPlant.lHenry = CanonicalRat.mk 150 1000000 ∧
    lcDrivesZoh.tsSec = lcPwmPeriod50us ∧
    deadTimeVoltBound lcVdc800 lcSicDeadTime200ns lcPwmPeriod50us = CanonicalRat.mk 32 5 := by
  decide +kernel

/-- **Universal LC Drives 800 V / 200 ns SiC Dead-Time + Q32 Quantization ISS Theorem**:
Across every ZOH plant `d` in the certified LC Drives enclosure `[249/250, 124501/125000] × [499/1500, 1/3]`
and every bounded 200 ns SiC dead-time distortion sequence `|vDtSeq k| ≤ 6.4 V`, the Q32 hardware loop
contracts geometrically at rate `271/272` into `lcDeadTimeIssBall`. -/
theorem test_lc_drives_sic_deadtime_q32_iss
    (d : ZohRl)
    (ha : d.a ∈ (⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩ : Interval))
    (hb : d.b ∈ (⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩ : Interval))
    (hbR : d.b * d.plant.rOhm = 1 - d.a)
    (rMa vffMv : Int) (vDtSeq : Nat → CanonicalRat)
    (hDtSeq : ∀ k,
      -deadTimeVoltBound lcVdc800 lcSicDeadTime200ns lcPwmPeriod50us ≤ vDtSeq k ∧
      vDtSeq k ≤ deadTimeVoltBound lcVdc800 lcSicDeadTime200ns lcPwmPeriod50us)
    (qs0 : QuantizedLoopState) :
    let r := ratMilli rMa
    let vff := ratMilli vffMv
    let traj : Nat → CanonicalRat × CanonicalRat := fun k =>
      let s := (runDeadTimeQ32Loop d lcKpQ32 lcKiQ32 rMa vffMv vDtSeq qs0 k).toLoopState
      (errX r s, errZ d r vff s)
    (quadForm lcP11 lcP12 lcP22 (traj 0).1 (traj 0).2 ≤ lcDeadTimeIssBall →
      ∀ k, quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 ≤ lcDeadTimeIssBall) ∧
    (∀ k, lcM * ((traj k).1 * (traj k).1) ≤
      ratPow lcRhoIss k * (lcC * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + lcDeadTimeIssBall) := by
  have hbBounds := (Interval.mem_iff _ _).mp hb
  have hb0 : 0 ≤ d.b := by
    have : (0 : CanonicalRat) ≤ CanonicalRat.mk 499 1500 := by decide +kernel
    grind
  have hbSq : d.b * d.b ≤ CanonicalRat.mk 1 3 * CanonicalRat.mk 1 3 := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hbBounds.2 hb0
    have h2 := Rat.mul_le_mul_of_nonneg_right hbBounds.2 (by decide +kernel : (0 : CanonicalRat) ≤ CanonicalRat.mk 1 3)
    grind
  have hdSqBound :
      d.b * d.b * (((2 + ratQ32 lcKpQ32 + ratQ32 lcKiQ32) / 1000 +
        deadTimeVoltBound lcVdc800 lcSicDeadTime200ns lcPwmPeriod50us) *
        ((2 + ratQ32 lcKpQ32 + ratQ32 lcKiQ32) / 1000 +
          deadTimeVoltBound lcVdc800 lcSicDeadTime200ns lcPwmPeriod50us)) +
      ((1 + ratQ32 lcKiQ32) / 1000) * ((1 + ratQ32 lcKiQ32) / 1000) ≤ lcDeadTimeDSq := by
    let vSq := ((2 + ratQ32 lcKpQ32 + ratQ32 lcKiQ32) / 1000 +
        deadTimeVoltBound lcVdc800 lcSicDeadTime200ns lcPwmPeriod50us) *
      ((2 + ratQ32 lcKpQ32 + ratQ32 lcKiQ32) / 1000 +
        deadTimeVoltBound lcVdc800 lcSicDeadTime200ns lcPwmPeriod50us)
    have hvSqNonneg : 0 ≤ vSq := Interval.rat_sq_nonneg _
    have hMul := Rat.mul_le_mul_of_nonneg_right hbSq hvSqNonneg
    have hCeil : CanonicalRat.mk 1 3 * CanonicalRat.mk 1 3 * vSq +
        ((1 + ratQ32 lcKiQ32) / 1000) * ((1 + ratQ32 lcKiQ32) / 1000) ≤ lcDeadTimeDSq := by
      dsimp [vSq]; decide +kernel
    grind
  have hIss := currentLoop_deadTime_and_quant_iss_ball
    ⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩
    ⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩
    ⟨ratQ32 lcKpQ32, ratQ32 lcKpQ32⟩
    ⟨ratQ32 lcKiQ32, ratQ32 lcKiQ32⟩
    lcP11 lcP12 lcP22 lcEps lcC lcM lcRho lcTheta lcThetaInv lcRhoIss
    lcVdc800 lcSicDeadTime200ns lcPwmPeriod50us lcDeadTimeDSq lcDeadTimeIssBall
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    d lcKpQ32 lcKiQ32 (by decide) (by decide) hb0 ha hb
    (by decide +kernel) (by decide +kernel) hbR hdSqBound rMa vffMv vDtSeq hDtSeq qs0
  exact ⟨hIss.2.2.1, hIss.2.2.2⟩

/-- **Coupled Rotor Speed `ω_e` Back-EMF ISS Tracking (`λ_m = 50 mWb`, `α_max = 4000 rad/s²`)**:
Proves bounded q-axis current error under time-varying rotor acceleration `|Δω_e| ≤ 0.2 rad/s` per 50 µs sample. -/
def lcLambdaM : CanonicalRat := CanonicalRat.mk 1 20
def lcAlphaMax : CanonicalRat := 4000
def lcBackEmfDSq : CanonicalRat := CanonicalRat.mk 1 10000
def lcBackEmfIssBall : CanonicalRat := CanonicalRat.mk 156638 625

theorem test_lc_drives_coupled_backemf_iss
    (r vff : CanonicalRat) (omegaSeq : Nat → CanonicalRat)
    (hAccel : ∀ k,
      -(lcAlphaMax * lcDrivesZoh.tsSec) ≤ omegaSeq (k + 1) - omegaSeq k ∧
      omegaSeq (k + 1) - omegaSeq k ≤ lcAlphaMax * lcDrivesZoh.tsSec)
    (s0 : LoopState) :
    let traj : Nat → CanonicalRat × CanonicalRat := fun k =>
      let s := runBackEmfLoop lcDrivesZoh lcDrivesGains r vff lcLambdaM omegaSeq s0 k
      (errX r s, errZBackEmf lcDrivesZoh r vff lcLambdaM (omegaSeq k) s)
    (quadForm lcP11 lcP12 lcP22 (traj 0).1 (traj 0).2 ≤ lcBackEmfIssBall →
      ∀ k, quadForm lcP11 lcP12 lcP22 (traj k).1 (traj k).2 ≤ lcBackEmfIssBall) ∧
    (∀ k, lcM * ((traj k).1 * (traj k).1) ≤
      ratPow lcRhoIss k * (lcC * ((traj 0).1 * (traj 0).1 + (traj 0).2 * (traj 0).2)) + lcBackEmfIssBall) := by
  have hc := lc_drives_box_certificate
  have hIss := currentLoop_backEmf_coupled_iss_ball
    ⟨CanonicalRat.mk 249 250, CanonicalRat.mk 124501 125000⟩
    ⟨CanonicalRat.mk 499 1500, CanonicalRat.mk 1 3⟩
    ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 2 5⟩
    ⟨CanonicalRat.mk 1 20, CanonicalRat.mk 1 20⟩
    lcP11 lcP12 lcP22 lcEps lcC lcM lcRho lcTheta lcThetaInv lcRhoIss
    lcLambdaM lcAlphaMax lcBackEmfDSq lcBackEmfIssBall
    hc.1 hc.2.1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lcDrivesZoh lcDrivesGains hc.2.2.1 hc.2.2.2.1 (by decide +kernel) (by decide +kernel)
    hc.2.2.2.2 (by decide +kernel) (by decide +kernel) r vff omegaSeq hAccel s0
  exact ⟨hIss.2.2.1, hIss.2.2.2⟩

/-- **Continuous-Time Inter-Sample Tube on LC Drives (`τ = Ts/2`, `a_τ = 499/500`, `b_τ = 1/6`)**:
Zero inter-sample current overshoot and strict interior bracketing between `i_k` and `i_{k+1}`. -/
theorem test_lc_drives_intersample_zero_overshoot (ik vk r : CanonicalRat) :
    let iNext := stepZoh lcDrivesZoh ik vk
    let iMid := zohIntersampleCurrent (CanonicalRat.mk 499 500) (CanonicalRat.mk 1 6) ik vk
    (min ik iNext ≤ iMid ∧ iMid ≤ max ik iNext) ∧
    (ik ≠ iNext → min ik iNext < iMid ∧ iMid < max ik iNext) ∧
    (iMid - r) * (iMid - r) ≤ max ((ik - r) * (ik - r)) ((iNext - r) * (iNext - r)) := by
  have h := zoh_intersample_convex_hull_bound
    lcDrivesZoh (CanonicalRat.mk 499 500) (CanonicalRat.mk 1 6) ik vk r
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨h.2.2.1, h.2.2.2.1 (by decide +kernel) (by decide +kernel), h.2.2.2.2⟩

-- ============================================================================
-- 2. 5-Cell (6-Level) 800 V SiC FCML (`160 V, 320 V, 480 V, 640 V`, `C = 40 µF`)
-- ============================================================================

/-- 800 V 5-cell SiC FCML phase leg with `40 µF = 1/25000 F` flying capacitors. -/
def fcml800Spec : FcmlCapSpec4 :=
  ⟨CanonicalRat.mk 1 25000, CanonicalRat.mk 1 25000, CanonicalRat.mk 1 25000, CanonicalRat.mk 1 25000, 800⟩

/-- Concrete verification of the `(160 V, 320 V, 480 V, 640 V)` balanced ladder and all 6 KVL output levels. -/
example :
    fcmlNominalLadder 800 = ⟨160, 320, 480, 640⟩ ∧
    fcmlSwitchNodeVoltage 800 ⟨false, false, false, false, false⟩ (fcmlNominalLadder 800) = 0 ∧
    fcmlSwitchNodeVoltage 800 ⟨true,  false, false, false, false⟩ (fcmlNominalLadder 800) = 160 ∧
    fcmlSwitchNodeVoltage 800 ⟨true,  true,  false, false, false⟩ (fcmlNominalLadder 800) = 320 ∧
    fcmlSwitchNodeVoltage 800 ⟨true,  true,  true,  false, false⟩ (fcmlNominalLadder 800) = 480 ∧
    fcmlSwitchNodeVoltage 800 ⟨true,  true,  true,  true,  false⟩ (fcmlNominalLadder 800) = 640 ∧
    fcmlSwitchNodeVoltage 800 ⟨true,  true,  true,  true,  true⟩  (fcmlNominalLadder 800) = 800 := by
  decide +kernel

/-- **Universal 5-Cell FCML Symmetric 5-Phase PSP Zero-Net-Charge-Drift**:
Over any symmetric 72°-shifted 5-phase PSP cycle `fcmlSymmetricPsp5Cycle s0`, exact switched-capacitor
KCL integration preserves every flying-capacitor voltage identically (`v_final = v0`). -/
theorem test_fcml800_symmetric_psp_zero_drift
    (dt iL : CanonicalRat) (s0 : FcmlSwitchState5) (v0 : FcmlCapState4) :
    runFcmlSubintervals fcml800Spec dt iL (fcmlSymmetricPsp5Cycle s0) v0 = v0 := by
  obtain ⟨h1, h2, h3, h4⟩ := fcml_psp_cyclic_diff_sum_zero s0
  exact fcml_psp_nominal_zero_drift fcml800Spec dt iL
    s0 (fcmlCyclicShift s0) (fcmlCyclicShift (fcmlCyclicShift s0))
    (fcmlCyclicShift (fcmlCyclicShift (fcmlCyclicShift s0)))
    (fcmlCyclicShift (fcmlCyclicShift (fcmlCyclicShift (fcmlCyclicShift s0))))
    v0 h1 h2 h3 h4

/-- **800 V 5-Cell SiC FCML Active Duty-Trim Contraction & `240 V` SiC FET Blocking Safety**:
For `10 A ≤ |i_L[n]| ≤ 80 A`, `K_trim = 1/200`, `δ_max = 1/10`, `E_max = 20 V`, `η_max = 1/16 V`,
capacitor unbalance contracts geometrically at rate `15/16` into `R_bal = 1 V` and every SiC FET
across all 5 cells stays strictly within `[0, 240 V]`. -/
theorem test_fcml800_active_trim_contraction_and_sic_fet_safety
    (iLSeq : Nat → CanonicalRat)
    (hILRange : ∀ n, 10 ≤ ratAbs (iLSeq n) ∧ ratAbs (iLSeq n) ≤ 80)
    (etaSeq : Nat → FcmlCapState4)
    (hEta : ∀ n,
      ratAbs (etaSeq n).vc1 ≤ CanonicalRat.mk 1 16 ∧ ratAbs (etaSeq n).vc2 ≤ CanonicalRat.mk 1 16 ∧
      ratAbs (etaSeq n).vc3 ≤ CanonicalRat.mk 1 16 ∧ ratAbs (etaSeq n).vc4 ≤ CanonicalRat.mk 1 16)
    (v0 : FcmlCapState4) (hInit : fcmlMaxUnbalance 800 v0 ≤ 20) :
    let traj := runFcmlActiveBalance fcml800Spec lcPwmPeriod50us
      (CanonicalRat.mk 1 200) (CanonicalRat.mk 1 10) iLSeq etaSeq v0
    (∀ n, fcmlMaxUnbalance 800 (traj n) - 1 ≤
      fcmlRatPow (CanonicalRat.mk 15 16) n * (fcmlMaxUnbalance 800 v0 - 1)) ∧
    (∀ n,
      let b := fcmlCellBlockingVoltages 800 (traj n)
      (0 ≤ b.vb1 ∧ b.vb1 ≤ 240) ∧ (0 ≤ b.vb2 ∧ b.vb2 ≤ 240) ∧
      (0 ≤ b.vb3 ∧ b.vb3 ≤ 240) ∧ (0 ≤ b.vb4 ∧ b.vb4 ≤ 240) ∧
      (0 ≤ b.vb5 ∧ b.vb5 ≤ 240)) := by
  have hNoOver : ∀ n,
      (lcPwmPeriod50us / fcml800Spec.c1) * ratAbs (iLSeq n) * CanonicalRat.mk 1 200 ≤ 1 ∧
      (lcPwmPeriod50us / fcml800Spec.c2) * ratAbs (iLSeq n) * CanonicalRat.mk 1 200 ≤ 1 ∧
      (lcPwmPeriod50us / fcml800Spec.c3) * ratAbs (iLSeq n) * CanonicalRat.mk 1 200 ≤ 1 ∧
      (lcPwmPeriod50us / fcml800Spec.c4) * ratAbs (iLSeq n) * CanonicalRat.mk 1 200 ≤ 1 := by
    intro n
    have hHi := (hILRange n).2
    have hGain : lcPwmPeriod50us / fcml800Spec.c1 = CanonicalRat.mk 5 4 := by decide +kernel
    have hBound : CanonicalRat.mk 5 4 * ratAbs (iLSeq n) * CanonicalRat.mk 1 200 ≤ 1 := by
      have h1 := Rat.mul_le_mul_of_nonneg_left hHi (by decide +kernel : (0 : CanonicalRat) ≤ CanonicalRat.mk 5 4)
      have h2 := Rat.mul_le_mul_of_nonneg_right h1 (by decide +kernel : (0 : CanonicalRat) ≤ CanonicalRat.mk 1 200)
      exact Rat.le_trans h2 (by decide +kernel)
    have hcEq : fcml800Spec.c2 = fcml800Spec.c1 ∧ fcml800Spec.c3 = fcml800Spec.c1 ∧ fcml800Spec.c4 = fcml800Spec.c1 :=
      ⟨rfl, rfl, rfl⟩
    rw [hcEq.1, hcEq.2.1, hcEq.2.2, hGain]
    exact ⟨hBound, hBound, hBound, hBound⟩
  have hSpec : fcml800Spec.Spec :=
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have hMain := fcml_active_trim_contracts_unbalance
    fcml800Spec hSpec
    lcPwmPeriod50us (CanonicalRat.mk 1 200) (CanonicalRat.mk 1 10) 10 20
    (CanonicalRat.mk 1 16) (CanonicalRat.mk 1 16) 1 240
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    iLSeq hNoOver (fun n => (hILRange n).1)
    ⟨by decide +kernel, by decide +kernel⟩ ⟨by decide +kernel, by decide +kernel⟩
    ⟨by decide +kernel, by decide +kernel⟩ ⟨by decide +kernel, by decide +kernel⟩
    etaSeq hEta v0 hInit
  have hRate : 1 - CanonicalRat.mk 1 16 = CanonicalRat.mk 15 16 := by decide +kernel
  rw [hRate] at hMain
  exact ⟨hMain.2.1, hMain.2.2⟩

-- ============================================================================
-- 3. Index-1 MNA Circuit DAE Judge (`"mna-dae@1"`, RC + Passive Diode Rectifier & Refusals)
-- ============================================================================

/-- Trapezoidal-rule step on `rcDiodeRectifierMnaSpec` (`dt = 2/5 s`, `E: 12 J → 6 J`, exact `0` residual). -/
def rcDiodeRectifierTrapStep : MnaTraceStep :=
  ⟨CanonicalRat.mk 2 5, [4, 2], [2, 2], [0], [2], [0], 0⟩

def rcDiodeRectifierTrapProblem : MnaDaeProblem :=
  ⟨rcDiodeRectifierMnaSpec, .trapezoidal, [rcDiodeRectifierTrapStep]⟩

/-- Planted residual-violating MNA trace (`xNext = [5, 5]` violates KCL at `residualTol = 1/10`). -/
def badResidualMnaProblem : MnaDaeProblem :=
  ⟨rcDiodeRectifierMnaSpec, .backwardEuler,
    [⟨1, [6, CanonicalRat.mk 1 2], [5, 5], [0], [0], [0], CanonicalRat.mk 1 10⟩]⟩

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (h ▸ rfl) else isFalse (fun heq => by injection heq; contradiction)
  | .ok a1, .ok a2 =>
    if h : a1 = a2 then isTrue (h ▸ rfl) else isFalse (fun heq => by injection heq; contradiction)
  | .error _, .ok _ => isFalse (fun heq => by injection heq)
  | .ok _, .error _ => isFalse (fun heq => by injection heq)

/-- Wire JSON roundtrip (`mnaCircuitDaeFormat.checkBytes`), Backward-Euler & Trapezoidal 2-node
RC/diode rectifier acceptance, stored-energy dissipation (`12 J → 6 J`), and refusal checks. -/
example :
    mnaCircuitDaeFormat.name ++ "@" ++ mnaCircuitDaeFormat.version = "mna-dae@1" ∧
    mnaCircuitDaeFormat.checkBytes 1
      (encodeMnaDaeProblem rcDiodeRectifierMnaProblem)
      (encodeMnaDaeCert rcDiodeRectifierMnaCert) = .ok ∧
    mnaCircuitDaeFormat.checkBytes 0
      (encodeMnaDaeProblem nonPassiveNegCondMnaProblem)
      (encodeMnaDaeCert rcDiodeRectifierMnaCert) =
        .refused (.judge (.negativeConductanceDiag 0)) [0] ∧
    checkMnaDaeProblem 1 rcDiodeRectifierMnaProblem rcDiodeRectifierMnaCert = .ok ∧
    checkMnaDaeProblem 1 rcDiodeRectifierTrapProblem rcDiodeRectifierMnaCert = .ok ∧
    mnaStoredEnergy 2 rcDiodeRectifierMnaSpec.matC rcDiodeRectifierBeStep.xNext <
      mnaStoredEnergy 2 rcDiodeRectifierMnaSpec.matC rcDiodeRectifierBeStep.xPrev ∧
    mnaStoredEnergy 2 rcDiodeRectifierMnaSpec.matC rcDiodeRectifierTrapStep.xPrev = 12 ∧
    mnaStoredEnergy 2 rcDiodeRectifierMnaSpec.matC rcDiodeRectifierTrapStep.xNext = 6 ∧
    checkMnaDaeProblem 0 nonPassiveNegCondMnaProblem rcDiodeRectifierMnaCert =
      .refused (.negativeConductanceDiag 0) [0] ∧
    checkMnaDaeProblem 1 badResidualMnaProblem rcDiodeRectifierMnaCert =
      .refused (.stepResidualViolation 0) [0] := by
  have hDecBe : decodeMnaDaeProblem (encodeMnaDaeProblem rcDiodeRectifierMnaProblem) =
      .ok rcDiodeRectifierMnaProblem := by decide +kernel
  have hDecNeg : decodeMnaDaeProblem (encodeMnaDaeProblem nonPassiveNegCondMnaProblem) =
      .ok nonPassiveNegCondMnaProblem := by decide +kernel
  have hDecCert : decodeMnaDaeCert (encodeMnaDaeCert rcDiodeRectifierMnaCert) =
      .ok rcDiodeRectifierMnaCert := by decide +kernel
  have hOkBe : checkMnaDaeProblem 1 rcDiodeRectifierMnaProblem rcDiodeRectifierMnaCert = .ok := by decide +kernel
  have hRefNeg : checkMnaDaeProblem 0 nonPassiveNegCondMnaProblem rcDiodeRectifierMnaCert =
      .refused (.negativeConductanceDiag 0) [0] := by decide +kernel
  have hBytesOk : mnaCircuitDaeFormat.checkBytes 1
      (encodeMnaDaeProblem rcDiodeRectifierMnaProblem)
      (encodeMnaDaeCert rcDiodeRectifierMnaCert) = .ok := by
    unfold Judge.Format.checkBytes mnaCircuitDaeFormat mnaCircuitDaeJudge
    dsimp only [Judge.check]; rw [hDecBe, hDecCert]; dsimp only; rw [hOkBe]; rfl
  have hBytesRef : mnaCircuitDaeFormat.checkBytes 0
      (encodeMnaDaeProblem nonPassiveNegCondMnaProblem)
      (encodeMnaDaeCert rcDiodeRectifierMnaCert) =
        .refused (.judge (.negativeConductanceDiag 0)) [0] := by
    unfold Judge.Format.checkBytes mnaCircuitDaeFormat mnaCircuitDaeJudge
    dsimp only [Judge.check]; rw [hDecNeg, hDecCert]; dsimp only; rw [hRefNeg]; rfl
  exact ⟨rfl, hBytesOk, hBytesRef, by decide +kernel⟩

/-- **Universal Refutation Impossibility for Planted Negative Conductance & Residual Violations**:
No Gram passivity certificate `c'` can ever satisfy `MnaDaeMeaning` on either planted invalid DAE trace. -/
theorem test_mna_planted_refusals_impossible (c' : MnaDaeCert) :
    ¬ MnaDaeMeaning nonPassiveNegCondMnaProblem c' ∧
    ¬ MnaDaeMeaning badResidualMnaProblem c' :=
  ⟨mnaCircuitDaeJudge.refuted (nonPassiveNegCond_refused 0 rcDiodeRectifierMnaCert) rfl c',
   mnaCircuitDaeJudge.refuted (c := rcDiodeRectifierMnaCert) (r := 1)
     (by decide +kernel : checkMnaDaeProblem 1 badResidualMnaProblem rcDiodeRectifierMnaCert =
       .refused (.stepResidualViolation 0) [0]) rfl c'⟩

-- ============================================================================
-- 4. `#tooth` Mutation Sensitivity Proofs (`6` universal theorem kills)
-- ============================================================================

#tooth Obend.Hardware.CircuitDae.checkMnaStepEnclosure_sound by
  mutation Obend.Hardware.CircuitDae.checkMnaStepEnclosure := fun _ _ _ => true

#tooth Obend.Hardware.CircuitDae.checkMnaDaeProblem_sound by
  mutation Obend.Hardware.CircuitDae.checkMnaDaeProblem := fun _ _ _ => .ok

#tooth Obend.Hardware.CircuitDae.fcml_psp_nominal_zero_drift by
  mutation Obend.Hardware.CircuitDae.stepFcmlSwitchSubinterval := fun _ _ _ _ v =>
    ⟨v.vc1 + 1, v.vc2, v.vc3, v.vc4⟩

#tooth Obend.Hardware.CircuitDae.fcmlSynthesizeZeroSumTrim_exact by
  mutation Obend.Hardware.CircuitDae.fcmlSynthesizeZeroSumTrim := fun d1 d2 d3 d4 =>
    ⟨d1, d2, d3, d4, 1⟩

#tooth Obend.Hardware.CurrentLoop.stepDeadTimeQ32Loop_error_perturbation by
  mutation Obend.Hardware.CurrentLoop.stepDeadTimeQ32Loop := fun _ _ _ _ _ _ qs =>
    ⟨qs.i + 10, qs.intMv⟩

#tooth Obend.Hardware.CurrentLoop.zoh_intersample_convex_hull_bound by
  mutation Obend.Hardware.CurrentLoop.zohIntersampleCurrent := fun _ _ ik _ => ik + 1

-- ============================================================================
-- 5. Axiom Purity Census (`0 sorryAx`, `0` custom axioms across entire import cone)
-- ============================================================================

#assert_axioms_tree

end Obend.Tests.CircuitDaeAndFcmlIssTest
