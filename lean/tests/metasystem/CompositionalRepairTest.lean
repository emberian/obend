module
/-
# Compositional Proof Engineering, `(Co)Algebra`/Realizability Repair & Metaprogramming Test Suite (`G2`)

End-to-end verification of Groundwork Shard G2 across:
1. `Obend.Category.Refines` + `by compose_sim`:
   - `GradeMonoid` (`Unit`, `Nat`, `Int`, `RatSlack`, `ε₁ × ε₂`), `Simulates`, `StutterSimulates`,
     `GaloisRefinement`, `Simulates.trace_safety`, and automated proof synthesis via `by compose_sim`.
2. `Obend.Category.OpenSystem`:
   - `OpenDissipativeSys`, `parallelCompose`, `feedbackInterconnect`, `skewFeedbackInterconnect`,
     `energy_bounded_along_trajectory`, and `autonomous_lyapunov_nonincreasing`.
3. `Obend.Category.GradedLogic` + `by graded_vcg`:
   - 5-axis `CompositeGrade`, `GradedM`, `GradedTriple` (`pure_triple`, `bind_triple`,
     `conseq_triple`, `frame_triple`, `loop_triple`), and symbolic VCG via `by graded_vcg`.
4. `Obend.Repair.AlgConfig` + `#assert_no_scar`:
   - `UnaryNat ↔ BinNat`, `AlgEquiv`, Proposition 3.15 (`repair_by_instantiation`),
     dependent elimination repair (`elim_repair_ok`, `elimProp_repair_ok`), positive scar-free
     checks (`binIsZero`, `binAdd`, `bin_add_zero`), and negative scar-detection audit.
5. `Obend.Repair.CoalgConfig` + `paco` + `#assert_no_scar`:
   - Parameterized coinduction (`paco_coind`, `paco_acc`, `paco_mult`, `FinalPCoalg.paco_eq`),
     Proposition 4.19 (`destr_ok`, `iota_ok`, `corec_ok`, `coind_ok`), `SeqStream ↔ Simd2Stream`,
     and positive/negative `#assert_no_scar` checks (`simd2Cons`, `simd2_eta`).
6. `Obend.Repair.QuotAssembly`:
   - `EffectiveQuotient.liftHom`, `doubleModQuotHom`, choice-free & `Quot.sound`-free computational
     `tracker` reducing by `rfl` in the Lean kernel on distinct equivalent representatives.
7. `Obend.Tactic.Compositional` (`Judge.ofSoundCheck`, `Judge.ofCounterexampleCheck`, `Format.ofCodec`):
   - Lawful fuel-deepened modular quadratic-residue judge with counterexample refutation (`mod 4`)
     and lawful bitstring wire `Codec` + `Format.ofCodec`.
8. `#tooth` kernel mutation probes on universal theorems & compile-time `0 sorryAx` / `0 _native` audit.
-/
public import Obend.Category.Refines
public import Obend.Category.OpenSystem
public import Obend.Category.GradedLogic
public import Obend.Repair.AlgConfig
public import Obend.Repair.CoalgConfig
public import Obend.Repair.QuotAssembly
public import Obend.Tactic.Compositional
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Judge.Class
import all Obend.Category.Refines
import all Obend.Category.OpenSystem
import all Obend.Category.GradedLogic
import all Obend.Repair.AlgConfig
import all Obend.Repair.CoalgConfig
import all Obend.Repair.QuotAssembly
import all Obend.Tactic.Compositional

public section
open Obend
open Obend.Category
open Obend.Repair
open Obend.Tactic.Compositional

set_option autoImplicit false

namespace Obend.Tests.Metasystem.CompositionalRepairTest

/-! ## 1. Quantitative Simulation, Stutter Simulation, Galois Refinement & `by compose_sim` -/

/-- Fine concrete counter system with bounded quantization offset `≤ 1`. -/
def sysFine : StepSystem (Nat × Bool) Nat Nat where
  step s u s' := s'.1 = s.1 + u ∧ (s'.2 = false ∨ s'.2 = true)
  observe s := s.1 + (if s.2 then 1 else 0)

/-- Intermediate pipeline model with offset `≤ 2` relative to ideal accumulator. -/
def sysMid : StepSystem (Nat × Fin 3) Nat Nat where
  step s u s' := s'.1 = s.1 + u
  observe s := s.1 + s.2.1

/-- Ideal abstract accumulator `s' = s + u`. -/
def sysIdeal : StepSystem Nat Nat Nat :=
  StepSystem.ofDet (fun s u => s + u) (fun s => s)

/-- Auxiliary saturating telemetry channel with `Nat` observable readout. -/
def sysAux : StepSystem Nat Int Nat :=
  StepSystem.ofDet (fun s u => Int.toNat ((s : Int) + u)) (fun s => s)

def relFineMid (s₁ : Nat × Bool) (s₂ : Nat × Fin 3) : Prop :=
  s₁.1 = s₂.1 ∧ s₂.2 = ⟨0, by omega⟩

def relMidIdeal (s₂ : Nat × Fin 3) (s₃ : Nat) : Prop :=
  s₂.1 = s₃

theorem sim_fine_mid : Simulates sysFine sysMid relFineMid (1 : Nat) where
  obs_bound := by
    rintro ⟨n₁, b⟩ ⟨n₂, f⟩ ⟨rfl, rfl⟩
    cases b
    · simp [sysFine, sysMid, ObsMetric.dist]
    · have hNotLe : ¬ (n₁ + 1 ≤ n₁) := by omega
      simp [sysFine, sysMid, ObsMetric.dist, hNotLe]
  step_sim := by
    rintro ⟨n₁, b⟩ ⟨n₁', b'⟩ ⟨n₂, f⟩ u ⟨rfl, rfl⟩ ⟨rfl, _⟩
    exact ⟨(n₁ + u, ⟨0, by omega⟩), rfl, ⟨rfl, rfl⟩⟩

theorem sim_mid_ideal : Simulates sysMid sysIdeal relMidIdeal (2 : Nat) where
  obs_bound := by
    rintro ⟨n₂, ⟨v, hv⟩⟩ n₃ rfl
    change (if n₂ + v ≤ n₂ then n₂ - (n₂ + v) else (n₂ + v) - n₂) ≤ 2
    by_cases h : n₂ + v ≤ n₂ <;> simp [h] <;> omega
  step_sim := by
    rintro ⟨n₂, f⟩ ⟨n₂', f'⟩ n₃ u rfl hn
    dsimp only [sysMid] at hn
    exact ⟨n₂ + u, rfl, hn⟩

/-- **One-line `by compose_sim` synthesis**: chains `Simulates.trans`, `Simulates.prod`,
    `Simulates.refl`, and slack relaxation `1 + 2 + 0 ≤ 5` automatically! -/
theorem composed_two_channel_sim :
    Simulates
      (sysFine.prod sysAux)
      (sysIdeal.prod sysAux)
      (RelProd (RelComp relFineMid relMidIdeal) Eq)
      (5 : Nat) := by
  have h₁ := sim_fine_mid
  have h₂ := sim_mid_ideal
  compose_sim

/-- **One-line `by compose_sim` over interleaved `StepSystem.indepProd`**. -/
theorem composed_indep_channel_sim :
    Simulates
      (sysFine.indepProd sysAux)
      (sysIdeal.indepProd sysAux)
      (RelProd (RelComp relFineMid relMidIdeal) Eq)
      (3 : Nat) := by
  have h₁ := sim_fine_mid
  have h₂ := sim_mid_ideal
  compose_sim

/-- Pullback of safety invariant `s ≤ bound` and quantitative observation defect across
    arbitrary-length concrete traces via `Simulates.trace_safety` and `by compose_sim`. -/
theorem composed_trace_safety_pullback
    (bound : Nat) (sFine sFine' : Nat × Bool) (sIdeal₀ : Nat) (tr : List Nat)
    (hRel₀ : RelComp relFineMid relMidIdeal sFine sIdeal₀)
    (hInitBound : sIdeal₀ ≤ bound)
    (hTrace : StepTrace
      { step := fun s a s' => a = 0 ∧ sysFine.step s a s', observe := sysFine.observe }
      sFine tr sFine') :
    sFine'.1 ≤ bound ∧ ObsMetric.dist (sysFine.observe sFine') sFine'.1 ≤ 4 := by
  let sysFineZero : StepSystem (Nat × Bool) Nat Nat :=
    { step := fun s a s' => a = 0 ∧ sysFine.step s a s', observe := sysFine.observe }
  let sysIdealZero : StepSystem Nat Nat Nat :=
    { step := fun s a s' => a = 0 ∧ sysIdeal.step s a s', observe := sysIdeal.observe }
  have hSimBase : Simulates sysFine sysIdeal (RelComp relFineMid relMidIdeal) (3 : Nat) := by
    have h₁ := sim_fine_mid
    have h₂ := sim_mid_ideal
    compose_sim
  have hSimZero : Simulates sysFineZero sysIdealZero (RelComp relFineMid relMidIdeal) (3 : Nat) :=
    { obs_bound := fun hr => hSimBase.obs_bound hr
      step_sim := fun hr ⟨ha0, hs⟩ => by
        obtain ⟨s₃', haStep, hr'⟩ := hSimBase.step_sim hr hs
        exact ⟨s₃', ⟨ha0, haStep⟩, hr'⟩ }
  have hInvStep : ∀ {s₂ s₂' : Nat} {a : Nat}, s₂ ≤ bound → sysIdealZero.step s₂ a s₂' → s₂' ≤ bound := by
    intro s₂ s₂' a hInv ⟨ha0, hStep⟩
    dsimp only [sysIdealZero, sysIdeal, StepSystem.ofDet] at hStep
    omega
  obtain ⟨s₃', _, hInv', hRel', hDist'⟩ :=
    hSimZero.trace_safety hInvStep hRel₀ hInitBound hTrace
  obtain ⟨⟨m, _⟩, ⟨hmEq, _⟩, rfl⟩ := hRel'
  refine ⟨by omega, ?_⟩
  have hLe4 : (3 : Nat) ≤ 4 := by omega
  rw [← hmEq] at hDist'
  exact Nat.le_trans hDist' hLe4

-- Rational slack monoid check: `1/2 + 1/3 ≤ 1`.
example : (⟨1, 1⟩ : RatSlack) + ⟨1, 2⟩ ≤ ⟨1, 0⟩ := by
  decide

/-- Stutter simulation composition: concrete micro-system steps by `+1` twice (`K₁ = 2`) per mid-step
    `+2`, and mid-system steps by `+2` three times (`K₂ = 3`) per macro-step `+6`, composing via
    `StutterSimulates.trans` to horizon `2 * 3 = 6`. -/
def microSys : StepSystem Nat Unit Nat := StepSystem.ofDet (fun n _ => n + 1) (fun n => n)
def midMacroSys : StepSystem Nat Unit Nat := StepSystem.ofDet (fun n _ => n + 2) (fun n => n)
def topMacroSys : StepSystem Nat Unit Nat := StepSystem.ofDet (fun n _ => n + 6) (fun n => n)

theorem stutter_micro_mid : StutterSimulates microSys midMacroSys Eq 2 (0 : Nat) where
  horizon_pos := by omega
  obs_bound h := by
    subst h
    change ObsMetric.dist (ε := Nat) _ _ ≤ 0
    exact ObsMetric.dist_self _
  stutter_step := by
    intro s₁ s₂ s₂' _ hEq hStep
    subst hEq
    dsimp only [midMacroSys, StepSystem.ofDet] at hStep
    subst hStep
    refine ⟨2, s₁ + 2, by omega, by omega, ?_, rfl⟩
    exact .succ (s₂ := s₁ + 1) rfl (.succ rfl (.zero _))

theorem stutter_mid_top : StutterSimulates midMacroSys topMacroSys Eq 3 (0 : Nat) where
  horizon_pos := by omega
  obs_bound h := by
    subst h
    change ObsMetric.dist (ε := Nat) _ _ ≤ 0
    exact ObsMetric.dist_self _
  stutter_step := by
    intro s₁ s₂ s₂' _ hEq hStep
    subst hEq
    dsimp only [topMacroSys, StepSystem.ofDet] at hStep
    subst hStep
    refine ⟨3, s₁ + 6, by omega, by omega, ?_, rfl⟩
    exact .succ (s₂ := s₁ + 2) rfl (.succ (s₂ := s₁ + 4) rfl (.succ rfl (.zero _)))

theorem stutter_composed_six (n : Nat) :
    ∃ (k : Nat) (n' : Nat),
      1 ≤ k ∧ k ≤ 6 ∧ StepCount microSys () k n n' ∧ RelComp Eq Eq n' (n + 6) := by
  have hComp := stutter_micro_mid.trans stutter_mid_top
  exact hComp.stutter_step ⟨n, rfl, rfl⟩ rfl

/-- Galois refinement adjunction check (`GaloisRefinement.ofRel`). -/
theorem galois_refinement_adjunction_holds (P : (Nat × Bool) → Prop) (Q : (Nat × Fin 3) → Prop) :
    PredLe ((GaloisRefinement.ofRel relFineMid).alpha P) Q ↔
      PredLe P ((GaloisRefinement.ofRel relFineMid).gamma Q) :=
  (GaloisRefinement.ofRel relFineMid).adj P Q

/-! ## 2. Port-Hamiltonian / Dissipative Open Systems (`OpenSystem`) -/

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases x with
  | ofNat n =>
    exact Int.ofNat_le.mpr (Nat.zero_le (n * n))
  | negSucc n =>
    exact Int.ofNat_le.mpr (Nat.zero_le ((n + 1) * (n + 1)))

theorem int_mul_two_right (a b : Int) : a * (2 * b) = b * a + b * a := by
  rw [← Int.mul_assoc, Int.mul_comm a 2, Int.two_mul, Int.add_mul, Int.mul_comm a b]

/-- Lossless wave-scattering storage element (`H(x) = x^2`, `w(u, y) = u^2 - y^2`, `step x u = (u, x)`). -/
def waveDelaySys : OpenDissipativeSys Int Int Int where
  energy x := x * x
  energy_nonneg x := int_sq_nonneg x
  supply u y := u * u - y * y
  step x u := (u, x)
  dissipative x u := Int.le_refl (u * u - x * x)

/-- Strictly dissipative two-cell wave resonator (`H(x, z) = x^2 + z^2`, dissipating `-x^2 ≤ 0`). -/
def dampedPipeSys : OpenDissipativeSys (Int × Int) Int Int where
  energy s := s.1 * s.1 + s.2 * s.2
  energy_nonneg s := Int.add_nonneg (int_sq_nonneg s.1) (int_sq_nonneg s.2)
  supply u y := u * u - y * y
  step s u := ((u, 0), s.2)
  dissipative s u := by
    have hx : 0 ≤ s.1 * s.1 := int_sq_nonneg s.1
    dsimp only
    omega

/-- Power-conserving interconnection via `feedbackInterconnect`: internal port wave power `s₁^2`
    cancels identically (`(e^2 - s₁^2) + (s₁^2 - y₂^2) = e^2 - y₂^2`), certifying global passivity
    and autonomous Lyapunov decay with **zero per-system re-proving**! -/
def coupledPlant : OpenDissipativeSys (Int × (Int × Int)) Int Int :=
  OpenDissipativeSys.feedbackInterconnect waveDelaySys dampedPipeSys
    { resolveInputs := fun s₁ _ e => (e, s₁)
      mergeOutputs := fun _ _ y₂ => y₂
      supplyExt := fun e yExt => e * e - yExt * yExt
      power_conserving := fun s₁ s₂ e => by
        dsimp only [waveDelaySys, dampedPipeSys]
        omega }

theorem coupledPlant_global_lyapunov (s₀ : Int × (Int × Int)) (us : List Int) :
    0 ≤ coupledPlant.energy (coupledPlant.runTrajectory s₀ us) ∧
      coupledPlant.energy (coupledPlant.runTrajectory s₀ us) ≤
        coupledPlant.energy s₀ + coupledPlant.trajectorySupply s₀ us :=
  coupledPlant.energy_bounded_along_trajectory s₀ us

theorem coupledPlant_zero_input_nonincreasing (s₀ : Int × (Int × Int)) (horizon : Nat) :
    coupledPlant.energy
        (coupledPlant.runTrajectory s₀ (List.replicate horizon (0 : Int))) ≤
      coupledPlant.energy s₀ := by
  refine (coupledPlant.autonomous_lyapunov_nonincreasing s₀
    (List.replicate horizon (0 : Int)) ?_).2
  intro s u hu
  have hZero : u = 0 := List.eq_of_mem_replicate hu
  subst hZero
  dsimp only [coupledPlant, OpenDissipativeSys.feedbackInterconnect, dampedPipeSys]
  have hyNonneg : 0 ≤ s.2.2 * s.2.2 := int_sq_nonneg s.2.2
  omega

/-- Implicit-midpoint Port-Hamiltonian capacitor (`H(x) = x^2`, bilinear effort/flow `u * y` with
    midpoint readout `y = 2x + u`, satisfying `(x + u)^2 - x^2 = u * (2x + u)`). -/
def midpointCapSys : OpenDissipativeSys Int Int Int where
  energy x := x * x
  energy_nonneg x := int_sq_nonneg x
  supply u y := u * y
  step x u := (x + u, 2 * x + u)
  dissipative x u := by
    dsimp only
    have hExpand : (x + u) * (x + u) - x * x = u * (2 * x + u) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add]
      have hcomm : u * x = x * u := Int.mul_comm u x
      have htwo : u * (2 * x) = x * u + x * u := int_mul_two_right u x
      omega
    rw [hExpand]
    exact Int.le_refl _

/-- Damped Port-Hamiltonian inductor (`H(x) = x^2`, `y = 2x + 2u`, dissipating `-u^2 ≤ 0`). -/
def dampedIndSys : OpenDissipativeSys Int Int Int where
  energy x := x * x
  energy_nonneg x := int_sq_nonneg x
  supply u y := u * y
  step x u := (x + u, 2 * x + 2 * u)
  dissipative x u := by
    dsimp only
    have huSq : 0 ≤ u * u := int_sq_nonneg u
    have hId : u * (2 * x + 2 * u) - ((x + u) * (x + u) - x * x) = u * u := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add]
      have hcomm : u * x = x * u := Int.mul_comm u x
      have htwo : u * (2 * x) = x * u + x * u := int_mul_two_right u x
      have htwoU : u * (2 * u) = u * u + u * u := int_mul_two_right u u
      omega
    omega

def parallelPlant : OpenDissipativeSys (Int × Int) (Int × Int) (Int × Int) :=
  midpointCapSys.parallelCompose dampedIndSys

theorem parallelPlant_global_lyapunov (s₀ : Int × Int) (us : List (Int × Int)) :
    0 ≤ parallelPlant.energy (parallelPlant.runTrajectory s₀ us) ∧
      parallelPlant.energy (parallelPlant.runTrajectory s₀ us) ≤
        parallelPlant.energy s₀ + parallelPlant.trajectorySupply s₀ us :=
  parallelPlant.energy_bounded_along_trajectory s₀ us

theorem gyrator_skew_cancellation_check (k e₁ e₂ y₁ y₂ : Int) :
    (e₁ - k * y₂) * y₁ + (e₂ + k * y₁) * y₂ = e₁ * y₁ + e₂ * y₂ :=
  OpenDissipativeSys.skew_gyrator_power_cancels k e₁ e₂ y₁ y₂

/-! ## 3. 5-Axis `CompositeGrade` & `by graded_vcg` (`GradedLogic`) -/

/-- Calibrated FHE sensor stage: reads current accumulator, adds `delta` with fixed-point rounding
    `errorNum := 2`, ciphertext `noise := 5`, `cycles := 12`, `uses := 1`, `exergy := -3`, then
    charges key-switching `tick` and emits scaled readout. -/
def fheSensorStage (delta : Int) : GradedM CompositeGrade Int Int := do
  let cur ← GradedM.get
  GradedM.modifyCost (fun s => s + delta)
    { uses := 1, errorNum := 2, noise := 5, cycles := 12, exergy := -3 }
  GradedM.tick
    { uses := 0, errorNum := 1, noise := 3, cycles := 8, exergy := -1 }
  let _ ← GradedM.actionCost (fun s => (s + s, s + 1))
    { uses := 1, errorNum := 1, noise := 4, cycles := 10, exergy := -2 }
  return cur + delta

/-- **One-line `by graded_vcg`** discharging a 5-step `do`-block over 5-axis `CompositeGrade`! -/
theorem fheSensorStage_triple (delta : Int) :
    GradedTriple
      (fun s => 0 ≤ s ∧ 0 ≤ delta)
      (fheSensorStage delta)
      { uses := 2, errorNum := 5, noise := 15, cycles := 35, exergy := -5 }
      (fun ret s' => ret + 1 = s' ∧ 1 ≤ s') := by
  unfold fheSensorStage
  graded_vcg

/-- Caller pipeline composing `fheSensorStage` as a modular `GradedTriple` sub-specification with
    post-processing, discharged in **one line** via `by graded_vcg`! -/
def fheCallerPipeline (delta : Int) : GradedM CompositeGrade Int Int := do
  let mid ← fheSensorStage delta
  GradedM.modifyCost (fun s => s + mid)
    { uses := 1, errorNum := 1, noise := 2, cycles := 6, exergy := -1 }
  GradedM.get

theorem fheCallerPipeline_triple (delta : Int) :
    GradedTriple
      (fun s => 0 ≤ s ∧ 0 ≤ delta)
      (fheCallerPipeline delta)
      { uses := 4, errorNum := 6, noise := 18, cycles := 45, exergy := -6 }
      (fun out s' => out = s' ∧ 1 ≤ out) := by
  have hStage := fheSensorStage_triple delta
  unfold fheCallerPipeline
  graded_vcg

/-- Separating `frame_triple` over `StateLens.fst Int Nat` preserving disjoint audit counter `audit ≥ 10`. -/
theorem fheSensorStage_preserves_audit_frame (delta : Int) :
    GradedTriple
      (fun ω : Int × Nat => (0 ≤ ω.1 ∧ 0 ≤ delta) ∧ 10 ≤ ω.2)
      ((fheSensorStage delta).zoom (StateLens.fst Int Nat))
      { uses := 2, errorNum := 5, noise := 15, cycles := 35, exergy := -5 }
      (fun ret ω' => (ret + 1 = ω'.1 ∧ 1 ≤ ω'.1) ∧ 10 ≤ ω'.2) :=
  frame_triple (StateLens.fst Int Nat) (fun audit => 10 ≤ audit) (fheSensorStage_triple delta)

/-- Bounded `N`-iteration loop `repeatN` accumulating `N • g` via `loop_triple`. -/
def bumpLoopBody (acc : Nat) : GradedM CompositeGrade Nat Nat :=
  GradedM.actionCost (fun s => (acc + 1, s + 1))
    { uses := 1, errorNum := 0, noise := 2, cycles := 4, exergy := -1 }

theorem bumpLoop_triple (N : Nat) (a₀ : Nat) :
    GradedTriple
      (fun s => s = a₀)
      (GradedM.repeatN N bumpLoopBody a₀)
      (GradeMonoid.nsmul N { uses := 1, errorNum := 0, noise := 2, cycles := 4, exergy := -1 })
      (fun a s => s = a) := by
  apply loop_triple N (fun a s => s = a) ?_ a₀
  intro a
  unfold bumpLoopBody
  graded_vcg

/-! ## 4. Scar-Free Algebraic Proof Repair (`AlgConfig`) & `#assert_no_scar` -/

-- Compile-time negative helper verifying that `findScarPath?` DOES detect retired types in naive
-- equivalence-wrapped definitions.
open Lean Elab Command in
elab "#assert_scar_detected " scar:ident " in " target:ident : command => do
  let scarName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo scar
  let targetName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let env ← getEnv
  match ← liftCoreM <| findScarPath? env scarName targetName with
  | some chain =>
    logInfo m!"#assert_scar_detected: confirmed scar '{scarName}' in '{targetName}' via {chain}"
  | none =>
    throwError "#assert_scar_detected failed: expected '{targetName}' to reference '{scarName}', but no scar was found!"

-- Positive scar-free elaborator guarantees on repaired `BinNat` definitions and proofs!
#assert_no_scar UnaryNat in BinNat.initPAlg
#assert_no_scar UnaryNat in binIsZero
#assert_no_scar UnaryNat in binAdd
#assert_no_scar UnaryNat in bin_add_zero

/-- Naive transport-with-scars wrapper: converts `BinNat → UnaryNat`, runs `unaryAdd`, and converts back. -/
def naiveScarredBinAdd (x y : BinNat) : BinNat :=
  unaryBinConfig.forward (unaryAdd (unaryBinConfig.backward x) (unaryBinConfig.backward y))

-- Verify `#assert_no_scar`'s engine catches the `UnaryNat` scar in `naiveScarredBinAdd`!
#assert_scar_detected UnaryNat in naiveScarredBinAdd

/-- Dependent propositional elimination repair (`AlgConfig.elimProp_repair_ok`). -/
theorem bin_zero_add (b : BinNat) : binAdd .zero b = b := by
  unfold binAdd peanoAdd
  exact BinNat.initPAlg.fold_beta (mkPeanoAlg b BinNat.succ) ⟨false, PEmpty.elim⟩

theorem unary_bin_elimProp_coherence (u : UnaryNat) :
    let P : BinNat → Prop := fun b => binAdd .zero b = b
    let casesD : (a : Bool) → (k : PeanoPos a → BinNat) → ((p : PeanoPos a) → P (k p)) →
        P (unaryBinConfig.algD.op ⟨a, k⟩) :=
      fun _ _ _ => bin_zero_add _
    UnaryNat.initPAlg.elimProp (fun c => P (unaryBinConfig.forward c))
      (fun a k ih => (unaryBinConfig.constr_ok ⟨a, k⟩).symm ▸
        casesD a (fun b => unaryBinConfig.forward (k b)) ih) u =
      BinNat.initPAlg.elimProp P casesD (unaryBinConfig.forward u) := by
  intro P casesD
  exact unaryBinConfig.elimProp_repair_ok P casesD u

/-- Dependent `Type`-valued elimination coherence (`AlgConfig.elim_repair_ok`). -/
theorem unary_bin_dependent_elim_coherence (u : UnaryNat) :
    let P : BinNat → Type := fun _ => Nat
    let casesD : (a : Bool) → (k : PeanoPos a → BinNat) → ((p : PeanoPos a) → P (k p)) →
        P (unaryBinConfig.algD.op ⟨a, k⟩) :=
      fun a _ rec => match a with | false => 0 | true => rec PUnit.unit + 1
    UnaryNat.initPAlg.elim (fun c => P (unaryBinConfig.forward c))
      (unaryBinConfig.pullbackCases P casesD) u =
      BinNat.initPAlg.elim P casesD (unaryBinConfig.forward u) := by
  intro P casesD
  exact unaryBinConfig.elim_repair_ok P casesD u

/-! ## 5. Coalgebraic Proof Repair (`CoalgConfig`), `paco` & `#assert_no_scar` -/

-- Positive scar-free elaborator guarantees on repaired `Simd2Stream` definitions and proofs!
#assert_no_scar SeqStream in Simd2Stream.finalPCoalg
#assert_no_scar SeqStream in simd2Cons
#assert_no_scar SeqStream in simd2_eta

/-- Naive scarred stream `cons` roundtripping through `SeqStream`. -/
def naiveScarredSimd2Cons {α : Type} (a : α) (w : Simd2Stream α) : Simd2Stream α :=
  (seqSimd2StreamConfig α).forward
    (streamConsVia (SeqStream.finalPCoalg α) a ((seqSimd2StreamConfig α).backward w))

-- Verify `#assert_no_scar`'s engine catches the `SeqStream` scar in `naiveScarredSimd2Cons`!
#assert_scar_detected SeqStream in naiveScarredSimd2Cons

/-- Constant stream `repeatVia` over any `FinalPCoalg α StreamPos S`, repaired scar-free to `Simd2Stream`. -/
def streamRepeatSeed {α : Type} (a : α) : PCoalg α StreamPos PUnit where
  out _ := ⟨a, fun _ => PUnit.unit⟩

def simd2Repeat {α : Type} (a : α) : Simd2Stream α :=
  (Simd2Stream.finalPCoalg α).corec (streamRepeatSeed a) PUnit.unit

#assert_no_scar SeqStream in simd2Repeat

/-- Incremental parameterized coinduction (`paco_coind` + `paco_acc` + `paco_mult` + `FinalPCoalg.paco_eq`)
    proving `simd2Repeat a = simd2Cons a (simd2Repeat a)`! -/
theorem simd2Repeat_unfold {α : Type} (a : α) :
    simd2Repeat a = simd2Cons a (simd2Repeat a) := by
  let F := Simd2Stream.finalPCoalg α
  let M := BisimStep.toMonoRel F.coalg
  apply F.paco_eq
  -- Exercise `paco_mult` AND `paco_acc` incrementally!
  apply paco_mult M (RelBot (Simd2Stream α))
  have hInner : paco M (paco M (RelBot (Simd2Stream α))) (simd2Repeat a) (simd2Repeat a) := by
    apply paco_coind M (R := Eq) ?_ _ _ rfl
    intro x y hxy
    subst hxy
    exact ⟨rfl, fun _ => .inl rfl⟩
  have hAcc : upaco M (RelBot (Simd2Stream α)) (simd2Repeat a) (simd2Repeat a) :=
    .inl (paco_acc M (RelBot (Simd2Stream α)) _ _ hInner)
  apply paco_coind M (R := fun x y => x = simd2Repeat a ∧ y = simd2Cons a (simd2Repeat a)) ?_
    _ _ ⟨rfl, rfl⟩
  rintro x y ⟨rfl, rfl⟩
  have hShapeL : F.coalg.shape (simd2Repeat a) = a :=
    F.corec_shape (streamRepeatSeed a) PUnit.unit
  have hShapeR : F.coalg.shape (simd2Cons a (simd2Repeat a)) = a :=
    F.corec_shape (streamConsSeed F.coalg) (.inl (a, simd2Repeat a))
  refine ⟨hShapeL.trans hShapeR.symm, fun b => .inr ?_⟩
  cases b
  have hPosL : F.coalg.pos (simd2Repeat a) PUnit.unit = simd2Repeat a :=
    F.corec_pos (streamRepeatSeed a) PUnit.unit PUnit.unit
  have hTailId : F.corec (streamConsSeed F.coalg) (.inr (simd2Repeat a)) = simd2Repeat a := by
    have hCorec : F.corec (streamConsSeed F.coalg) (.inr (simd2Repeat a)) = F.corec F.coalg (simd2Repeat a) := by
      apply F.corec_uniq F.coalg (fun z => F.corec (streamConsSeed F.coalg) (.inr z)) ?_ (simd2Repeat a)
      intro z
      rw [F.corec_out (streamConsSeed F.coalg) (.inr z), F.coalg.out_eq_mk z]
      rfl
    exact hCorec.trans (F.corec_self _)
  have hPosR : F.coalg.pos (simd2Cons a (simd2Repeat a)) PUnit.unit = simd2Repeat a := by
    have hp := F.corec_pos (streamConsSeed F.coalg) (.inl (a, simd2Repeat a)) PUnit.unit
    exact hp.trans hTailId
  change upaco M (RelBot (Simd2Stream α))
    (F.coalg.pos (simd2Repeat a) PUnit.unit)
    (F.coalg.pos (simd2Cons a (simd2Repeat a)) PUnit.unit)
  rw [hPosL, hPosR]
  exact hAcc

/-- Proposition 4.19 (`destr_ok`, `iota_ok`, `corec_ok`, AND `coind_ok`) verified on `seqSimd2StreamConfig`. -/
theorem seqSimd2_prop_4_19_coind_ok {α : Type}
    (R : SeqStream α → SeqStream α → Prop)
    (hB : Bisim α StreamPos (seqSimd2StreamConfig α).coalgC R)
    {x y : SeqStream α} (r : R x y) :
    congrArg (seqSimd2StreamConfig α).forward ((seqSimd2StreamConfig α).1.coind R hB r) =
      (seqSimd2StreamConfig α).2.coind
        (CoalgConfig.pushRel (seqSimd2StreamConfig α).forward R)
        ((seqSimd2StreamConfig α).pushRel_isBisim R hB)
        (CoalgConfig.pushRel_step (seqSimd2StreamConfig α).forward R r) :=
  (seqSimd2StreamConfig α).coind_ok R hB r

/-! ## 6. Realizability `Asm(P)` Quotient Escape Hatch (`QuotAssembly`) -/

-- Kernel `rfl` reduction across distinct equivalent representatives (`2 ≡ 7 (mod 5)`)!
-- Neither `Classical.choice` nor `Quot.sound` blocks computation on `tracker`.
example : CanonCode.eval (doubleModQuotHom 4).tracker (.nat 2) = some (.nat 4) := rfl
example : CanonCode.eval (doubleModQuotHom 4).tracker (.nat 7) = some (.nat 4) := rfl

theorem doubleModQuotHom_agrees_on_equiv_reps (m a b : Nat) (hEqv : ModRel m a b) :
    (doubleModQuotHom m).specFun (Quot.mk (ModRel m) a) =
      (doubleModQuotHom m).specFun (Quot.mk (ModRel m) b) ∧
    CanonCode.eval (doubleModQuotHom m).tracker (.nat a) =
      CanonCode.eval (doubleModQuotHom m).tracker (.nat b) := by
  refine ⟨congrArg (doubleModQuotHom m).specFun (Quot.sound hEqv), ?_⟩
  dsimp only [doubleModQuotHom, EffectiveQuotient.liftHom, modEffectiveQuotient,
    doubleModRawHom, CodeTracker.compCode, CanonCode.eval]
  dsimp only [ModRel] at hEqv
  rw [hEqv]

/-- Standalone bytecode tracker synthesized by `EffectiveQuotient.liftHom`: definitionally equal
    (`rfl`) to `(doubleModQuotHom m).tracker` with **zero axioms** (`[]`). -/
@[expose] def doubleModTrackerPure (m : Nat) : CanonCode :=
  .comp (.comp (.modCanon m) (.mulConst 2)) (.modCanon m)

theorem doubleModTrackerPure_eq_liftHom_tracker (m : Nat) :
    doubleModTrackerPure m = (doubleModQuotHom m).tracker := by rfl

open Lean Elab Command in
elab "#verify_choice_and_quot_free_tracker" : command => do
  let axsPure ← liftCoreM <| collectAxioms ``doubleModTrackerPure
  unless axsPure.isEmpty do
    throwError m!"Expected doubleModTrackerPure to have 0 axioms, but found: {axsPure}"
  let axsHom ← liftCoreM <| collectAxioms ``doubleModQuotHom
  if axsHom.contains ``Classical.choice then
    throwError m!"Expected doubleModQuotHom to be 100% choice-free, but found Classical.choice!"
  logInfo m!"[PASS] doubleModTrackerPure has 0 axioms ({axsPure}) and doubleModQuotHom is 100% choice-free!"

#verify_choice_and_quot_free_tracker

/-! ## 7. `Judge.ofSoundCheck`, `Judge.ofCounterexampleCheck` & `Format.ofCodec` -/

def binPosToNat : BinPos → Nat
  | .one => 1
  | .bit0 p => 2 * binPosToNat p
  | .bit1 p => 2 * binPosToNat p + 1

def binNatToNat : BinNat → Nat
  | .zero => 0
  | .pos p => binPosToNat p

/-- Modular quadratic-residue query `(modulusPred, target)` encoded as `BinNat × BinNat`. -/
structure ModQuadQuery where
  modulusPred : BinNat
  target : BinNat
  deriving DecidableEq, Repr

inductive ModQuadClause where
  | nonResidueMod4
  | witnessMismatch
  deriving DecidableEq, Repr

def modQuadMeaning (q : ModQuadQuery) (c : BinNat) : Prop :=
  let m := binNatToNat q.modulusPred + 1
  (binNatToNat c * binNatToNat c) % m = binNatToNat q.target % m

def modQuadCounterexample (q : ModQuadQuery) (k : ModQuadClause) : Prop :=
  k = .nonResidueMod4 ∧ binNatToNat q.modulusPred + 1 = 4 ∧ binNatToNat q.target % 4 = 2

/-- Universal number-theoretic lemma: no natural square is congruent to `2 (mod 4)`. -/
theorem sq_mod_four_ne_two (n : Nat) : (n * n) % 4 ≠ 2 := by
  have hMod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rw [Nat.mul_mod]
  rcases hMod with h | h | h | h <;> rw [h] <;> omega

def modQuadFragment (q : ModQuadQuery) : Prop :=
  binNatToNat q.modulusPred ≤ 64

def modQuadStep (fuel : Nat) (q : ModQuadQuery) (c : BinNat) : Judge.Verdict ModQuadClause :=
  let m := binNatToNat q.modulusPred + 1
  if m = 4 ∧ binNatToNat q.target % 4 = 2 then
    .refused .nonResidueMod4 [0]
  else if 65 < m then
    .refused .witnessMismatch [2]
  else if binNatToNat c ≤ fuel then
    if (binNatToNat c * binNatToNat c) % m = binNatToNat q.target % m then
      .ok
    else
      .refused .witnessMismatch [1]
  else
    .uncovered

def modQuadRefutes : ModQuadClause → Bool
  | .nonResidueMod4 => true
  | .witnessMismatch => false

theorem modQuadStep_sound {r : Nat} {q : ModQuadQuery} {c : BinNat}
    (h : modQuadStep r q c = .ok) : modQuadMeaning q c := by
  unfold modQuadStep at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · rename_i _ _ _ hEq
          exact hEq
        · cases h
      · cases h

theorem modQuadStep_counterexample {r : Nat} {q : ModQuadQuery} {c : BinNat}
    {k : ModQuadClause} {p : List Nat}
    (h : modQuadStep r q c = .refused k p) (hk : modQuadRefutes k = true) :
    modQuadCounterexample q k := by
  unfold modQuadStep at h
  dsimp only at h
  split at h
  · rename_i hBad
    injection h with hkEq _
    subst hkEq
    exact ⟨rfl, hBad.1, hBad.2⟩
  · split at h
    · injection h with hkEq _
      subst hkEq
      cases hk
    · split at h
      · split at h
        · cases h
        · injection h with hkEq _
          subst hkEq
          cases hk
      · cases h

theorem modQuadCounterexample_disjoint {q : ModQuadQuery} {k : ModQuadClause} {c' : BinNat}
    (hce : modQuadCounterexample q k) : ¬ modQuadMeaning q c' := by
  obtain ⟨_, hm4, ht2⟩ := hce
  unfold modQuadMeaning
  dsimp only
  rw [hm4, ht2]
  exact sq_mod_four_ne_two (binNatToNat c')

theorem modQuadStep_no_false_reject {r : Nat} {q : ModQuadQuery} {c : BinNat}
    {k : ModQuadClause} {p : List Nat}
    (hFrag : modQuadFragment q) (hMean : modQuadMeaning q c) : modQuadStep r q c ≠ .refused k p := by
  unfold modQuadStep
  dsimp only
  split
  · rename_i hBad
    intro _
    exact modQuadCounterexample_disjoint (c' := c) ⟨rfl, hBad.1, hBad.2⟩ hMean
  · split
    · rename_i _ hGt65
      unfold modQuadFragment at hFrag
      omega
    · split
      · have hMeanEq : (binNatToNat c * binNatToNat c) % (binNatToNat q.modulusPred + 1) =
            binNatToNat q.target % (binNatToNat q.modulusPred + 1) := hMean
        simp only [hMeanEq, ↓reduceIte]
        intro h; cases h
      · intro h; cases h

theorem modQuadStep_complete {q : ModQuadQuery}
    (hFrag : modQuadFragment q) (hEx : ∃ c : BinNat, modQuadMeaning q c) :
    ∃ (c : BinNat) (r : Nat), modQuadStep r q c = .ok := by
  obtain ⟨c, hMean⟩ := hEx
  refine ⟨c, binNatToNat c, ?_⟩
  unfold modQuadStep
  dsimp only
  split
  · rename_i hBad
    exact False.elim (modQuadCounterexample_disjoint (c' := c) ⟨rfl, hBad.1, hBad.2⟩ hMean)
  · split
    · rename_i _ hGt65
      unfold modQuadFragment at hFrag
      omega
    · have hLe : binNatToNat c ≤ binNatToNat c := Nat.le_refl _
      have hMeanEq : (binNatToNat c * binNatToNat c) % (binNatToNat q.modulusPred + 1) =
          binNatToNat q.target % (binNatToNat q.modulusPred + 1) := hMean
      simp only [hLe, hMeanEq, ↓reduceIte]

/-- **Single-declaration `Judge` instance via `Judge.ofCounterexampleCheck`** (`mono` & `refuted`
    discharged automatically!). -/
instance instJudgeModQuad : Judge ModQuadQuery BinNat :=
  Judge.ofCounterexampleCheck
    modQuadMeaning
    modQuadCounterexample
    modQuadStep
    modQuadRefutes
    modQuadStep_sound
    modQuadStep_counterexample
    modQuadCounterexample_disjoint
    modQuadFragment
    modQuadStep_no_false_reject
    modQuadStep_complete

/-- Genuine recursive bitstring wire encoder/decoder for `BinPos` & `BinNat` (zero hardcoded fixtures!). -/
def encodeBinPosChars : BinPos → List Char
  | .one => ['1']
  | .bit0 p => '0' :: encodeBinPosChars p
  | .bit1 p => '1' :: encodeBinPosChars p

theorem encodeBinPosChars_ne_nil (p : BinPos) : encodeBinPosChars p ≠ [] := by
  cases p <;> simp [encodeBinPosChars]

def decodeBinPosChars : List Char → Except String BinPos
  | ['1'] => .ok .one
  | '0' :: h :: t => BinPos.bit0 <$> decodeBinPosChars (h :: t)
  | '1' :: h :: t => BinPos.bit1 <$> decodeBinPosChars (h :: t)
  | _ => .error "invalid BinPos bitstring"

theorem decodeBinPosChars_encode (p : BinPos) :
    decodeBinPosChars (encodeBinPosChars p) = .ok p := by
  induction p with
  | one => rfl
  | bit0 q ih =>
    cases hq : encodeBinPosChars q with
    | nil => exact False.elim (encodeBinPosChars_ne_nil q hq)
    | cons h t =>
      simp only [encodeBinPosChars, hq, decodeBinPosChars]
      rw [← hq, ih]
      rfl
  | bit1 q ih =>
    cases hq : encodeBinPosChars q with
    | nil => exact False.elim (encodeBinPosChars_ne_nil q hq)
    | cons h t =>
      simp only [encodeBinPosChars, hq, decodeBinPosChars]
      rw [← hq, ih]
      rfl

def encodeBinNatChars : BinNat → List Char
  | .zero => ['Z']
  | .pos p => 'P' :: encodeBinPosChars p

def decodeBinNatChars : List Char → Except String BinNat
  | ['Z'] => .ok .zero
  | 'P' :: rest => BinNat.pos <$> decodeBinPosChars rest
  | _ => .error "invalid BinNat wire"

theorem decodeBinNatChars_encode (b : BinNat) :
    decodeBinNatChars (encodeBinNatChars b) = .ok b := by
  cases b with
  | zero => rfl
  | pos p =>
    simp only [encodeBinNatChars, decodeBinNatChars, decodeBinPosChars_encode p]
    rfl

theorem encodeBinPosChars_no_colon (p : BinPos) : ':' ∉ encodeBinPosChars p := by
  induction p with
  | one => decide
  | bit0 q ih =>
    simp only [encodeBinPosChars, List.mem_cons]
    rintro (h | h)
    · cases h
    · exact ih h
  | bit1 q ih =>
    simp only [encodeBinPosChars, List.mem_cons]
    rintro (h | h)
    · cases h
    · exact ih h

theorem encodeBinNatChars_no_colon (b : BinNat) : ':' ∉ encodeBinNatChars b := by
  cases b with
  | zero => decide
  | pos p =>
    simp only [encodeBinNatChars, List.mem_cons]
    rintro (h | h)
    · cases h
    · exact encodeBinPosChars_no_colon p h

def splitOnColon : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if c == ':' then
        some ([], rest)
      else
        match splitOnColon rest with
        | some (lhs, rhs) => some (c :: lhs, rhs)
        | none => none

theorem splitOnColon_append {xs ys : List Char} (hNo : ':' ∉ xs) :
    splitOnColon (xs ++ ':' :: ys) = some (xs, ys) := by
  induction xs with
  | nil => rfl
  | cons c rest ih =>
    have hcNe : (c == ':') = false := by
      cases hEq : (c == ':') with
      | false => rfl
      | true => exact False.elim (hNo ((beq_iff_eq.1 hEq) ▸ List.mem_cons_self))
    have hRest : ':' ∉ rest := fun h => hNo (List.mem_cons_of_mem c h)
    simp only [List.cons_append, splitOnColon, hcNe, Bool.false_eq_true, ↓reduceIte, ih hRest]

def binNatCodec : Codec BinNat where
  encode b := String.ofList (encodeBinNatChars b)
  decode s := decodeBinNatChars s.toList
  decode_encode b := by
    rw [String.toList_ofList]
    exact decodeBinNatChars_encode b

def modQuadQueryCodec : Codec ModQuadQuery where
  encode q :=
    String.ofList (encodeBinNatChars q.modulusPred ++ ':' :: encodeBinNatChars q.target)
  decode s :=
    match splitOnColon s.toList with
    | some (mChars, tChars) =>
        match decodeBinNatChars mChars, decodeBinNatChars tChars with
        | .ok m, .ok t => .ok ⟨m, t⟩
        | .error e, _ => .error e
        | _, .error e => .error e
    | none => .error "missing ':' delimiter in ModQuadQuery"
  decode_encode q := by
    cases q with
    | mk m t =>
      dsimp only
      rw [String.toList_ofList, splitOnColon_append (encodeBinNatChars_no_colon m)]
      dsimp only
      rw [decodeBinNatChars_encode m, decodeBinNatChars_encode t]

/-- **Single-declaration `Format` registration via `Format.ofCodec`** (`bad_refused` discharged by `rfl`!). -/
def modQuadFormat : Format :=
  Format.ofCodec
    "mod-quad"
    "1"
    modQuadQueryCodec
    binNatCodec
    (⟨.pos (.bit1 .one), .pos (.bit0 .one)⟩, .zero)
    0

-- Byte-level roundtrip acceptance (`3^2 ≡ 4 (mod 5)`) reduced directly in the kernel!
example :
    let q : ModQuadQuery := ⟨.pos (.bit0 (.bit0 .one)), .pos (.bit0 (.bit0 .one))⟩
    let c : BinNat := .pos (.bit1 .one)
    modQuadFormat.checkBytes 3 (modQuadQueryCodec.encode q) (binNatCodec.encode c) = .ok := rfl

/-- Refutation guarantee: `x^2 ≡ 2 (mod 4)` is refuted at grade `0`, proving `∀ c', ¬ modQuadMeaning q c'`. -/
theorem modQuad_nonresidue_refutes_all (c' : BinNat) :
    ¬ modQuadMeaning ⟨.pos (.bit1 .one), .pos (.bit0 .one)⟩ c' := by
  have hRef :
      Judge.check 0 (⟨.pos (.bit1 .one), .pos (.bit0 .one)⟩ : ModQuadQuery) BinNat.zero =
        .refused ModQuadClause.nonResidueMod4 [0] := rfl
  exact Judge.refuted hRef rfl c'

/-! ## 8. `#tooth` Kernel Mutation Probes & Compile-Time Axiom Audit -/

-- Mutating `RelComp` to drop `R₂` breaks `Simulates.trans`.
#tooth Obend.Category.Simulates.trans by
  mutation Obend.Category.RelComp := fun {α β γ} (R₁ : α → β → Prop) (_R₂ : β → γ → Prop) x _z =>
    ∃ y : β, R₁ x y

-- Mutating `OpenDissipativeSys.trajectorySupply` to `0` breaks `energy_bounded_along_trajectory`.
#tooth Obend.Category.OpenDissipativeSys.energy_bounded_along_trajectory by
  mutation Obend.Category.OpenDissipativeSys.trajectorySupply :=
    fun {State PortIn PortOut} (_sys : OpenDissipativeSys State PortIn PortOut) (_s : State) (_us : List PortIn) =>
      (0 : Int)

-- Mutating `GradedM.modifyCost` to leave state unchanged (`s` instead of `f s`) breaks `sym_modifyCost_bind`.
#tooth Obend.Tactic.Compositional.sym_modifyCost_bind by
  mutation Obend.Category.GradedM.modifyCost := fun {G σ} (_f : σ → σ) (cost : G) =>
    ({ run := fun s => ((), s, cost) } : GradedM G σ Unit)

-- Mutating `peanoAdd` to ignore its second operand breaks `bin_add_zero`.
#tooth Obend.Repair.bin_add_zero by
  mutation Obend.Repair.peanoAdd := fun {X} (I : InitPAlg Bool PeanoPos X) (x _y : X) =>
    I.alg.op ⟨true, fun _ => x⟩

-- Mutating `Simd2Stream.tl` to repeat `.1` instead of shifting `.2` breaks `simd2_eta`.
#tooth Obend.Repair.simd2_eta by
  mutation Obend.Repair.Simd2Stream.tl := fun {α} (w : Simd2Stream α) =>
    ({ wordAt := fun k => ((w.wordAt k).1, (w.wordAt k).1) } : Simd2Stream α)

-- Mutating `modQuadStep` to accept unconditionally breaks `modQuadStep_sound`.
#tooth modQuadStep_sound by
  mutation modQuadStep := fun _ _ _ => Judge.Verdict.ok

open Lean Elab Command in
elab "#verify_compositional_repair_axioms" : command => do
  let targets : List Name := [
    ``Obend.Category.Simulates.refl,
    ``Obend.Category.Simulates.trans,
    ``Obend.Category.Simulates.prod,
    ``Obend.Category.Simulates.indepProd,
    ``Obend.Category.Simulates.trace_safety,
    ``Obend.Category.StutterSimulates.trans,
    ``Obend.Category.GaloisRefinement.sim_preserves_galois,
    ``Obend.Category.OpenDissipativeSys.energy_bounded_along_trajectory,
    ``Obend.Category.OpenDissipativeSys.autonomous_lyapunov_nonincreasing,
    ``Obend.Category.OpenDissipativeSys.skew_gyrator_power_cancels,
    ``Obend.Category.pure_triple,
    ``Obend.Category.bind_triple,
    ``Obend.Category.conseq_triple,
    ``Obend.Category.frame_triple,
    ``Obend.Category.loop_triple,
    ``Obend.Repair.AlgConfig.constr_ok,
    ``Obend.Repair.AlgConfig.repair_by_instantiation,
    ``Obend.Repair.AlgConfig.backward_forward,
    ``Obend.Repair.AlgConfig.forward_backward,
    ``Obend.Repair.AlgConfig.elim_repair_ok,
    ``Obend.Repair.AlgConfig.elimProp_repair_ok,
    ``Obend.Repair.bin_add_zero,
    ``Obend.Repair.unary_bin_add_coherence,
    ``Obend.Repair.paco_coind,
    ``Obend.Repair.paco_mult,
    ``Obend.Repair.FinalPCoalg.coind,
    ``Obend.Repair.FinalPCoalg.paco_eq,
    ``Obend.Repair.CoalgConfig.destr_ok,
    ``Obend.Repair.CoalgConfig.iota_ok,
    ``Obend.Repair.CoalgConfig.corec_ok,
    ``Obend.Repair.CoalgConfig.coind_ok,
    ``Obend.Repair.simd2_eta,
    ``Obend.Repair.EffectiveQuotient.liftHom,
    ``Obend.Judge.ofSoundCheck,
    ``Obend.Judge.ofCounterexampleCheck,
    ``Obend.Judge.Format.ofCodec_checkBytes_encode,
    ``Obend.Judge.Format.ofCodec_encode_sound,
    ``composed_two_channel_sim,
    ``composed_indep_channel_sim,
    ``composed_trace_safety_pullback,
    ``coupledPlant_global_lyapunov,
    ``coupledPlant_zero_input_nonincreasing,
    ``parallelPlant_global_lyapunov,
    ``fheSensorStage_triple,
    ``fheCallerPipeline_triple,
    ``fheSensorStage_preserves_audit_frame,
    ``bumpLoop_triple,
    ``unary_bin_elimProp_coherence,
    ``unary_bin_dependent_elim_coherence,
    ``simd2Repeat_unfold,
    ``seqSimd2_prop_4_19_coind_ok,
    ``doubleModQuotHom_agrees_on_equiv_reps,
    ``doubleModTrackerPure_eq_liftHom_tracker,
    ``modQuad_nonresidue_refutes_all
  ]
  let allowedStandard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for t in targets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    for a in axs do
      if Obend.AssertAxioms.isCompilerTrust a then
        throwError m!"AXIOM AUDIT FAILED: {t} depends on compiler trust {a} (expected 0 native_decide)"
      if !allowedStandard.contains a then
        throwError m!"AXIOM AUDIT FAILED: {t} depends on non-standard axiom {a}"
  logInfo m!"[PASS] Compositional & Repair axiom audit verified: {targets.length} theorems & instances have 0 sorryAx, 0 native_decide, and 0 non-standard axioms!"

#verify_compositional_repair_axioms

end Obend.Tests.Metasystem.CompositionalRepairTest
end
