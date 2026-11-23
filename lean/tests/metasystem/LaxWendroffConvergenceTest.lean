/-
# `tests/metasystem/LaxWendroffConvergenceTest.lean`
End-to-end instantiations (`Burgers1D`, `EulerGas3D`, `ShallowWater1D`, `BonaMassoZ4c1D`), `#guard`
dyadic mesh-refinement & Judge vectors, `#tooth` kills, closed-theorem / `0 Classical.choice`
audit, and `#assert_axioms_tree` for `LaxWendroffDefs` and `LaxWendroffConvergence`.
-/
import Lean
import Obend.Analysis.LaxWendroffDefs
import Obend.Analysis.LaxWendroffConvergence
import Obend.Hardware.PdeSolvers
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Tests.LaxWendroffConvergenceTest

open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws Obend.Analysis.NonlinearErrorTube
open Obend.Analysis.LaxWendroffDefs Obend.Analysis.LaxWendroffConvergence
open Obend.Hardware.Gpu.StencilTile Obend.Hardware.BalanceLawLowering Obend.Hardware.MultiDStencilTile
open Obend.Hardware.MultiDStencilCorrect Obend.Hardware.PdeSolvers Obend.Tactic.SymDiffAndFlux
open Obend.Hardware.ArrayHypergraph (Word)

set_option autoImplicit false

/-! ## 1. Consistency, Lipschitz & Local Truncation Instantiations on All 4 Canonical Solvers -/

def burgersState : Vec | 0 => 1 | _ => 0
def eulerState : Vec | 0 => 3 / 2 | 1 => 1 / 8 | 2 => -(1 / 16) | 3 => 1 / 16 | 4 => 2 | _ => 0
def shallowWaterState : Vec | 0 => 3 / 2 | 1 => 1 / 4 | 2 => 0 | _ => 0
def z4cState : Vec | 0 => 1 | 1 => 2 | 2 => 1 / 8 | 3 => -(1 / 8) | 4 => 1 / 8 | 5 => 1 / 16 | _ => 0

-- 1a. `Burgers1D.spec`: Rusanov & MUSCL-`minmod` consistency (`F(1) = 1/2`) and steady preservation.
example :
    DenomNonzero (fluxComp Burgers1D.spec 0 0) ⟨burgersState, Burgers1D.spec.paramEnv⟩ ∧
    rusanovNonlinearFlux (getOr Burgers1D.spec.fluxes 0 []) Burgers1D.spec.paramEnv
      Burgers1D.spec.aMax burgersState burgersState 0 = 1 / 2 ∧
    faceFlux4 Burgers1D.spec 0 burgersState burgersState burgersState burgersState 0 = 1 / 2 ∧
    evalAxisCellRat Burgers1D.spec 0 (1 / 4) (fun _ => burgersState) 0 = 1 := by
  have hValid := Burgers1D.endToEnd_certified.rung1_continuum_ad_and_wavespeed.1
  have hDom : DomainValid Burgers1D.spec.domain ⟨burgersState, Burgers1D.spec.paramEnv⟩ := by
    intro t ht; simp [Burgers1D.spec] at ht
  have hM := musclMinmodFlux_consistent Burgers1D.spec hValid 0 0 (by decide +kernel)
    (by decide +kernel) (1 / 4) burgersState hDom
  have hR := rusanovFlux_consistent Burgers1D.spec hValid 0 0 (by decide +kernel)
    (by decide +kernel) burgersState hDom
  have hExact : evalFlux (fluxComp Burgers1D.spec 0 0) ⟨burgersState, Burgers1D.spec.paramEnv⟩ = 1 / 2 := by
    decide +kernel
  exact ⟨hM.1, hR.2.trans hExact, hM.2.1.trans hExact, hM.2.2⟩

-- 1b. `EulerGas3D.spec`: 3D domain-valid (`rho = 3/2 > 0`) consistency across all 3 axes & 5 vars.
example :
    ∀ (axis : Fin 3) (c : Fin 5),
      DenomNonzero (fluxComp EulerGas3D.spec axis.val c.val)
        ⟨eulerState, EulerGas3D.spec.paramEnv⟩ ∧
      faceFlux4 EulerGas3D.spec axis.val eulerState eulerState eulerState eulerState c.val =
        evalFlux (fluxComp EulerGas3D.spec axis.val c.val) ⟨eulerState, EulerGas3D.spec.paramEnv⟩ ∧
      evalAxisCellRat EulerGas3D.spec axis.val (1 / 8) (fun _ => eulerState) c.val =
        eulerState c.val := by
  intro axis c
  have hValid := EulerGas3D.endToEnd_certified.rung1_continuum_ad_and_wavespeed.1
  have hDom : DomainValid EulerGas3D.spec.domain ⟨eulerState, EulerGas3D.spec.paramEnv⟩ := by
    intro t ht
    have hdomEq : EulerGas3D.spec.domain = [.stateVar 0] := by decide +kernel
    rw [hdomEq] at ht; simp only [List.mem_singleton] at ht; subst ht; decide +kernel
  have hDims : EulerGas3D.spec.numDims = 3 := by decide +kernel
  have hVars : EulerGas3D.spec.numVars = 5 := by decide +kernel
  exact musclMinmodFlux_consistent EulerGas3D.spec hValid axis.val c.val
    (by omega) (by omega) (1 / 8) eulerState hDom

-- 1c. `ShallowWater1D.spec`: Saint-Venant (`h = 3/2 > 0`) consistency & equilibrium steady state.
example :
    ∀ c : Fin 3,
      DenomNonzero (fluxComp ShallowWater1D.spec 0 c.val)
        ⟨shallowWaterState, ShallowWater1D.spec.paramEnv⟩ ∧
      faceFlux4 ShallowWater1D.spec 0 shallowWaterState shallowWaterState
        shallowWaterState shallowWaterState c.val =
        evalFlux (fluxComp ShallowWater1D.spec 0 c.val)
          ⟨shallowWaterState, ShallowWater1D.spec.paramEnv⟩ ∧
      evalSchemeStepRat ShallowWater1D.spec .periodic [4] (1 / 8) true
        (fun _ => shallowWaterState) 0 c.val = shallowWaterState c.val := by
  intro c
  have hValid := ShallowWater1D.endToEnd_certified.rung1_continuum_ad_and_wavespeed.1
  have hDom : DomainValid ShallowWater1D.spec.domain ⟨shallowWaterState, ShallowWater1D.spec.paramEnv⟩ := by
    intro t ht
    have hdomEq : ShallowWater1D.spec.domain = [.stateVar 0] := by decide +kernel
    rw [hdomEq] at ht; simp only [List.mem_singleton] at ht; subst ht; decide +kernel
  have hVars : ShallowWater1D.spec.numVars = 3 := by decide +kernel
  have hM := musclMinmodFlux_consistent ShallowWater1D.spec hValid 0 c.val
    (by decide +kernel) (by omega) (1 / 8) shallowWaterState hDom
  have hSteady := evalSchemeStepRat_steady_constant ShallowWater1D.spec .periodic [4] (1 / 8) true
    shallowWaterState (Or.inr fun j => by
      cases j with
      | zero => decide +kernel
      | succ j => cases j with
        | zero => decide +kernel
        | succ j => cases j with
          | zero => decide +kernel
          | succ _ => rfl)
  exact ⟨hM.1, hM.2.1, congrFun (congrFun hSteady 0) c.val⟩

-- 1d. `BonaMassoZ4c1D.spec`: 6-variable curved-spacetime Z4c (`alpha = 1 > 0, gxx = 2 > 0`) consistency.
example :
    ∀ c : Fin 6,
      DenomNonzero (fluxComp BonaMassoZ4c1D.spec 0 c.val)
        ⟨z4cState, BonaMassoZ4c1D.spec.paramEnv⟩ ∧
      rusanovNonlinearFlux (getOr BonaMassoZ4c1D.spec.fluxes 0 []) BonaMassoZ4c1D.spec.paramEnv
        BonaMassoZ4c1D.spec.aMax z4cState z4cState c.val =
        evalFlux (fluxComp BonaMassoZ4c1D.spec 0 c.val) ⟨z4cState, BonaMassoZ4c1D.spec.paramEnv⟩ ∧
      evalAxisCellRat BonaMassoZ4c1D.spec 0 (1 / 10) (fun _ => z4cState) c.val = z4cState c.val := by
  intro c
  have hValid := BonaMassoZ4c1D.endToEnd_certified.rung1_continuum_ad_and_wavespeed.1
  have hDom : DomainValid BonaMassoZ4c1D.spec.domain ⟨z4cState, BonaMassoZ4c1D.spec.paramEnv⟩ := by
    intro t ht
    have hdomEq : BonaMassoZ4c1D.spec.domain = [.stateVar 0, .stateVar 1] := by decide +kernel
    rw [hdomEq] at ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · decide +kernel
    · simp only [List.mem_singleton] at ht'; subst ht'; decide +kernel
  have hVars : BonaMassoZ4c1D.spec.numVars = 6 := by decide +kernel
  have hM := musclMinmodFlux_consistent BonaMassoZ4c1D.spec hValid 0 c.val
    (by decide +kernel) (by omega) (1 / 10) z4cState hDom
  have hR := rusanovFlux_consistent BonaMassoZ4c1D.spec hValid 0 c.val
    (by decide +kernel) (by omega) z4cState hDom
  exact ⟨hM.1, hR.2, hM.2.2⟩

-- 1e. Quantitative Lipschitz continuity (`rusanovFlux_lipschitz_in_states` & `musclMinmodFlux_lipschitz_in_stencil`).
example :
    let u2 : Vec := fun | 0 => 1 / 2 | _ => 0
    ratAbs (rusanovNonlinearFlux (getOr Burgers1D.spec.fluxes 0 []) Burgers1D.spec.paramEnv
        Burgers1D.spec.aMax burgersState u2 0 -
      rusanovNonlinearFlux (getOr Burgers1D.spec.fluxes 0 []) Burgers1D.spec.paramEnv
        Burgers1D.spec.aMax u2 burgersState 0) ≤
      Burgers1D.spec.aMax * ((1 / 2 + 1 / 2) * weightOf Burgers1D.spec 0) ∧
    ratAbs (faceFlux4 Burgers1D.spec 0 burgersState burgersState u2 u2 0 -
      faceFlux4 Burgers1D.spec 0 u2 u2 burgersState burgersState 0) ≤
      2 * faceKappa Burgers1D.spec * Burgers1D.spec.aMax * ((1 / 2) * weightOf Burgers1D.spec 0) := by
  intro u2
  have hLip : verifyFluxLipschitz Burgers1D.spec = true := by decide +kernel
  have hVars1 : Burgers1D.spec.numVars = 1 := by decide +kernel
  have hIn1 : InBox Burgers1D.spec.numVars (effectiveStateBox Burgers1D.spec) burgersState :=
    fun c hc => by cases (show c = 0 by omega); decide +kernel
  have hIn2 : InBox Burgers1D.spec.numVars (effectiveStateBox Burgers1D.spec) u2 :=
    fun c hc => by cases (show c = 0 by omega); decide +kernel
  have hd12 : ∀ j, j < Burgers1D.spec.numVars → ratAbs (burgersState j - u2 j) ≤ (1 / 2) * weightOf Burgers1D.spec j :=
    fun j hj => by cases (show j = 0 by omega); decide +kernel
  have hd21 : ∀ j, j < Burgers1D.spec.numVars → ratAbs (u2 j - burgersState j) ≤ (1 / 2) * weightOf Burgers1D.spec j :=
    fun j hj => by cases (show j = 0 by omega); decide +kernel
  exact ⟨rusanovFlux_lipschitz_in_states Burgers1D.spec hLip (by decide +kernel) 0 (by decide +kernel)
           burgersState u2 u2 burgersState (1 / 2) (1 / 2) hIn1 hIn2 hIn2 hIn1 hd12 hd21 0 (by decide +kernel),
         musclMinmodFlux_lipschitz_in_stencil Burgers1D.spec hLip (by decide +kernel) 0 (by decide +kernel)
           burgersState burgersState u2 u2 u2 u2 burgersState burgersState (1 / 2)
           hIn1 hIn1 hIn2 hIn2 hIn2 hIn2 hIn1 hIn1 hd12 hd12 hd21 hd21 0 (by decide +kernel)⟩

-- 1f. 2nd-order smooth MUSCL spatial truncation on `Burgers1D.spec` (exact `0` error on linear ramp!).
example (dx : Rat) (hdx : 0 < dx) :
    let u0 : Vec := fun | 0 => 1 | _ => 0
    let ux : Vec := fun | 0 => 1 / 2 | _ => 0
    let sample : Int → Vec := fun off k =>
      if k < Burgers1D.spec.numVars then u0 k + (off : Rat) * dx * ux k else u0 k
    C3NonExtremaStencil5 Burgers1D.spec dx u0 ux (fun _ => 0) sample (fun _ => 0) ∧
    ratAbs ((faceFlux4 Burgers1D.spec 0 (sample (-1)) (sample 0) (sample 1) (sample 2) 0 -
        faceFlux4 Burgers1D.spec 0 (sample (-2)) (sample (-1)) (sample 0) (sample 1) 0) / dx -
      mulVec Burgers1D.spec.numVars (jacMat Burgers1D.spec 0 u0) ux 0) ≤
      (3 * Burgers1D.spec.aMax * weightOf Burgers1D.spec 0 * 0 + (1 / 4 : Rat) * 0) * (dx * dx) := by
  intro u0 ux sample
  have hVars1 : Burgers1D.spec.numVars = 1 := by decide +kernel
  have hSt := c3NonExtremaStencil5_linear_inhabited Burgers1D.spec (by decide +kernel) dx hdx u0 ux
    (fun k hk => by cases (show k = 0 by omega); grind)
  have hSt0 : C3NonExtremaStencil5 Burgers1D.spec dx u0 ux (fun _ => 0) sample
      (fun k => 0 * weightOf Burgers1D.spec k) := by simpa [Rat.zero_mul] using hSt
  have hBox0 : ∀ k, k < Burgers1D.spec.numVars → (effectiveStateBox Burgers1D.spec k).contains (u0 k) :=
    fun k hk => by cases (show k = 0 by omega); decide +kernel
  have hDomEmpty : ∀ v : Vec, DomainValid Burgers1D.spec.domain ⟨v, Burgers1D.spec.paramEnv⟩ :=
    fun _ t ht => by simp [Burgers1D.spec] at ht
  have hRemConst : ∀ V : Vec, V 0 = 1 / 2 → ∀ h : Rat,
      symDirectionalRem Burgers1D.spec.numVars (fluxComp Burgers1D.spec 0 0)
        ⟨u0, Burgers1D.spec.paramEnv⟩ V h = 1 / 8 := by
    intro V hV0 h
    have hSpecFlux : fluxComp Burgers1D.spec 0 0 = .mul (.const (1 / 2)) (.mul (.var 0) (.var 0)) := by
      decide +kernel
    rw [hSpecFlux, hVars1]
    simp [symDirectionalRem, evalDirectionalDeriv, symPartial, evalFlux, sumTo, u0, hV0]; grind
  have hh0 : dx / 2 ≠ 0 := by grind
  have hnh0 : -(dx / 2) ≠ 0 := by grind
  have hSlopeEq : ∀ a b c : Int, b = a + 1 → c = b + 1 →
      slopeAt Burgers1D.spec (sample a) (sample b) (sample c) 0 = dx * (1 / 2) := by
    intro a b c hb hc; subst hb hc
    have hLim : Burgers1D.spec.limiter = .minmod := by decide +kernel
    unfold slopeAt; rw [hLim]; simp only [reduceCtorEq, ↓reduceIte]
    have hd1 : sample (a + 1) 0 - sample a 0 = dx * (1 / 2) := by
      simp only [sample, hVars1, Nat.zero_lt_one, ↓reduceIte, u0, ux, Rat.intCast_add, Rat.intCast_ofNat]; grind
    have hd2 : sample (a + 1 + 1) 0 - sample (a + 1) 0 = dx * (1 / 2) := by
      simp only [sample, hVars1, Nat.zero_lt_one, ↓reduceIte, u0, ux, Rat.intCast_add, Rat.intCast_ofNat]; grind
    rw [hd1, hd2, minmod_self]
  have hVLp : (faceLRat Burgers1D.spec (sample (-1)) (sample 0) (sample 1) 0 - u0 0) / (dx / 2) = 1 / 2 := by
    unfold faceLRat; rw [hSlopeEq (-1) 0 1 rfl rfl]
    simp only [sample, hVars1, Nat.zero_lt_one, ↓reduceIte, u0, ux]
    exact rat_eq_of_mul_cancel hh0 (by rw [Rat.div_mul_cancel hh0]; grind)
  have hVLm : (faceLRat Burgers1D.spec (sample (-2)) (sample (-1)) (sample 0) 0 - u0 0) / -(dx / 2) = 1 / 2 := by
    unfold faceLRat; rw [hSlopeEq (-2) (-1) 0 rfl rfl]
    simp only [sample, hVars1, Nat.zero_lt_one, ↓reduceIte, u0, ux]
    exact rat_eq_of_mul_cancel hnh0 (by rw [Rat.div_mul_cancel hnh0]; grind)
  have hVRp : (faceRRat Burgers1D.spec (sample 0) (sample 1) (sample 2) 0 - u0 0) / (dx / 2) = 1 / 2 := by
    unfold faceRRat; rw [hSlopeEq 0 1 2 rfl rfl]
    simp only [sample, hVars1, Nat.zero_lt_one, ↓reduceIte, u0, ux]
    exact rat_eq_of_mul_cancel hh0 (by rw [Rat.div_mul_cancel hh0]; grind)
  have hVRm : (faceRRat Burgers1D.spec (sample (-1)) (sample 0) (sample 1) 0 - u0 0) / -(dx / 2) = 1 / 2 := by
    unfold faceRRat; rw [hSlopeEq (-1) 0 1 rfl rfl]
    simp only [sample, hVars1, Nat.zero_lt_one, ↓reduceIte, u0, ux]
    exact rat_eq_of_mul_cancel hnh0 (by rw [Rat.div_mul_cancel hnh0]; grind)
  refine ⟨hSt, muscl_nonextrema_second_order_truncation Burgers1D.spec (by decide +kernel)
    (by decide +kernel) 0 0 (by decide +kernel) (by decide +kernel) dx 0 0 Rat.le_refl
    u0 ux (fun _ => 0) sample hBox0 (hDomEmpty _) (hDomEmpty _) (hDomEmpty _) (hDomEmpty _) (hDomEmpty _)
    hSt0 ?_ ?_⟩
  · rw [hRemConst _ hVLp, hRemConst _ hVLm, ratAbs_sub_self]; grind
  · rw [hRemConst _ hVRp, hRemConst _ hVRm, ratAbs_sub_self]; grind

-- 1g. Inhabitedness witnesses for `C2GridSample` and non-commuting Strang vs. Lie splitting.
example :
    C2GridSample 1 (1 / 4) burgersState burgersState
      (fun k => if k < 1 then burgersState k - (1 / 4) * burgersState k + (1 / 2) * ((1 / 4) * (1 / 4)) * 2 else burgersState k)
      (fun k => if k < 1 then burgersState k + (1 / 4) * burgersState k + (1 / 2) * ((1 / 4) * (1 / 4)) * 2 else burgersState k)
      (fun _ => ratAbs 2) ∧
    ∃ (L1 L2 : MultiDGrid → MultiDGrid) (U : MultiDGrid),
      IsLinearGridOp L1 ∧ IsLinearGridOp L2 ∧ commutatorGrid L1 L2 U 0 0 ≠ 0 := by
  obtain ⟨L1, L2, U, h1, h2, hc, _⟩ := noncommuting_linearGridOps_inhabited (1 / 4) (by grind)
  exact ⟨c2GridSample_quadratic_inhabited 1 (1 / 4) (by grind) burgersState burgersState (fun _ => 2),
         ⟨L1, L2, U, h1, h2, hc⟩⟩

/-! ## 2. Summation-by-Parts, Lax–Wendroff Weak Residual & End-to-End Q32 Silicon Bounds -/

-- 2a. Exact discrete summation-by-parts across all 4 canonical PDE solvers (including 3D Euler & Z4c).
example (ψ : MultiDGrid) :
    (sumTo (gridCellCount [8]) (fun idx =>
      (evalSchemeStepRat Burgers1D.spec .periodic [8] (1 / 4) false
        (fun _ => burgersState) idx 0 - burgersState 0) * ψ idx 0) =
      schemeWeakFluxPairing Burgers1D.spec [8] (1 / 8) (1 / 4) false (fun _ => burgersState) ψ 0 +
      schemeWeakSourcePairing Burgers1D.spec [8] (1 / 4) false (fun _ => burgersState) ψ 0) ∧
    (sumTo (gridCellCount [2, 2, 2]) (fun idx =>
      (evalSchemeStepRat EulerGas3D.spec .periodic [2, 2, 2] (1 / 8) true
        (fun _ => eulerState) idx 0 - eulerState 0) * ψ idx 0) =
      schemeWeakFluxPairing EulerGas3D.spec [2, 2, 2] (1 / 4) (1 / 8) true (fun _ => eulerState) ψ 0 +
      schemeWeakSourcePairing EulerGas3D.spec [2, 2, 2] (1 / 8) true (fun _ => eulerState) ψ 0) ∧
    (sumTo (gridCellCount [4]) (fun idx =>
      (evalSchemeStepRat ShallowWater1D.spec .periodic [4] (1 / 8) true
        (fun _ => shallowWaterState) idx 1 - shallowWaterState 1) * ψ idx 1) =
      schemeWeakFluxPairing ShallowWater1D.spec [4] 1 (1 / 8) true (fun _ => shallowWaterState) ψ 1 +
      schemeWeakSourcePairing ShallowWater1D.spec [4] (1 / 8) true (fun _ => shallowWaterState) ψ 1) ∧
    (sumTo (gridCellCount [4]) (fun idx =>
      (evalSchemeStepRat BonaMassoZ4c1D.spec .periodic [4] (1 / 10) true
        (fun _ => z4cState) idx 5 - z4cState 5) * ψ idx 5) =
      schemeWeakFluxPairing BonaMassoZ4c1D.spec [4] 1 (1 / 10) true (fun _ => z4cState) ψ 5 +
      schemeWeakSourcePairing BonaMassoZ4c1D.spec [4] (1 / 10) true (fun _ => z4cState) ψ 5) :=
  ⟨evalSchemeStepRat_summation_by_parts Burgers1D.spec [8]
     (by intro N hN; simp at hN; omega) (1 / 8) (1 / 4) (by grind) false (fun _ => burgersState) ψ 0,
   evalSchemeStepRat_summation_by_parts EulerGas3D.spec [2, 2, 2]
     (by intro N hN; simp at hN; omega) (1 / 4) (1 / 8) (by grind) true (fun _ => eulerState) ψ 0,
   evalSchemeStepRat_summation_by_parts ShallowWater1D.spec [4]
     (by intro N hN; simp at hN; omega) 1 (1 / 8) (by grind) true (fun _ => shallowWaterState) ψ 1,
   evalSchemeStepRat_summation_by_parts BonaMassoZ4c1D.spec [4]
     (by intro N hN; simp at hN; omega) 1 (1 / 10) (by grind) true (fun _ => z4cState) ψ 5⟩

-- 2b. Executable `#guard`: dyadic mesh refinement (`N = 4, 8, 16`) on a discontinuous `Burgers1D`
-- Riemann jump shrinks `totalOscillation` monotonically as `Δx = 1/N → 0`!
def riemannStepGrid (N : Nat) : MultiDGrid :=
  fun idx c => if c == 0 && idx < N / 2 then 1 else 0

#guard
  let osc (N : Nat) : Rat :=
    let dx : Rat := 1 / (N : Rat)
    let dt : Rat := dx / 4
    -- Materialize each scalar time slice once so shared stencil reads cost O(1).
    let initial := (Array.range N).map fun i => riemannStepGrid N i 0
    let grid (xs : Array Rat) : MultiDGrid := fun i c => if c == 0 then xs[i]?.getD 0 else 0
    let levels := (List.range (N / 2)).foldl (fun (acc : Array (Array Rat)) _ =>
      let next := evalSchemeStepRat Burgers1D.spec .periodic [N] (1 / 4) false (grid acc.back!)
      acc.push ((Array.range N).map fun i => next i 0)) #[initial]
    totalOscillation Burgers1D.spec [N] dx dt false (N / 2) (fun n => grid levels[n]!)
  let o4 := osc 4; let o8 := osc 8; let o16 := osc 16
  0 < o16 && o16 < o8 && o8 < o4 && 2 * o16 ≤ o8 + (1 / 100)

-- 2c. Q32 scheme error bounds on all 4 solvers; `endToEnd_q32_silicon_weak_form_bound` and
-- `lax_wendroff_1d_tvd_shock_rate` with every hypothesis discharged on a steady `Burgers1D` state.
def terminalTest : SpaceTimeTestFn := ⟨1, fun n _ _ => if n = 0 then 0 else 1⟩

#guard
  (computeSchemeQ32ErrorBound Burgers1D.spec [4] (1 / 4) false).isSome &&
  (computeSchemeQ32ErrorBound EulerGas3D.spec [2, 2, 2] (1 / 8) true).isSome &&
  (computeSchemeQ32ErrorBound ShallowWater1D.spec [4] (1 / 8) false).isSome &&
  (computeSchemeQ32ErrorBound BonaMassoZ4c1D.spec [4] (1 / 10) false).isSome

-- Compare two fused GPU sweeps with the Q32 trajectory used by the residual on a periodic jump.
#guard
  let S := Burgers1D.spec
  let W := fun i c => ratToQ32Word (riemannStepGrid 4 i c)
  let pack (w : Nat → Nat → Word) := [(List.range 4).map fun i => w i 0]
  let kernel := buildSpecFusedGpuKernel S .periodic [4] 0
  let sweep (g : List (List Word)) := Obend.Hardware.Gpu.SoacOptimize.evalFused (fun c => g.getD c []) kernel
  let g₁ := sweep (pack W)
  let Q := q32SchemeTrajectory S .periodic [4] S.cfl false W
  g₁ != pack W && g₁ == pack (Q 1) && sweep g₁ == pack (Q 2)

def burgersWordGrid : Nat → Nat → Word := fun _ c => if c == 0 then ratToQ32Word 1 else 0#64

example :
    ∃ (εB Lsrc : Rat),
      computeSchemeQ32ErrorBound Burgers1D.spec [4] ((1 / 16 : Rat) / (1 / 4)) false = some εB ∧
      computeSourceLip Burgers1D.spec = some Lsrc ∧
      (let ν := (1 / 16 : Rat) / (1 / 4)
       let U_exact := exactTrajectory (evalSchemeStepRat Burgers1D.spec .periodic [4] ν false)
         (decodeGrid burgersWordGrid)
       let U_q32 : Nat → MultiDGrid :=
         fun k => decodeGrid (q32SchemeTrajectory Burgers1D.spec .periodic [4] ν false burgersWordGrid k)
       let E : Nat → Rat :=
         nonlinearDefectTube (schemeLip Burgers1D.spec [4] ν false Lsrc) 0 (fun _ => εB)
       ratAbs (discreteWeakResidual Burgers1D.spec [4] (1 / 4) (1 / 16) U_q32 terminalTest) ≤
         laxWendroffConst Burgers1D.spec Lsrc 0 1 *
           totalOscillation Burgers1D.spec [4] (1 / 4) (1 / 16) false 1 U_exact +
         q32WeakPerturbationBound Burgers1D.spec [4] (1 / 4) (1 / 16) Lsrc 1 16 0 1 E ∧
       ratAbs (discreteWeakResidual Burgers1D.spec [4] (1 / 4) (1 / 16) U_exact terminalTest) ≤
         laxWendroffConst Burgers1D.spec 0 0 1 * (((3 / 2 : Rat) / weightOf Burgers1D.spec 0) *
           ((terminalTest.steps : Rat) * (1 / 16) * 0) * (1 / 4))) := by
  let εB := (computeSchemeQ32ErrorBound Burgers1D.spec [4] (1 / 4) false).getD 0
  have hεB : computeSchemeQ32ErrorBound Burgers1D.spec [4] ((1 / 16 : Rat) / (1 / 4)) false = some εB := by
    decide +kernel
  have hDiv : ((1 / 16 : Rat) / (1 / 4)) = 1 / 4 := by grind
  have hVars1 : Burgers1D.spec.numVars = 1 := by decide +kernel
  have hInW : ∀ idx j, j < Burgers1D.spec.numVars → InBoxW Burgers1D.spec (burgersWordGrid idx j) j :=
    fun _ j hj => by have : j = 0 := by omega
                     subst this; exact (by decide +kernel : InBoxW Burgers1D.spec (burgersWordGrid 0 0) 0)
  have hInR : ∀ idx, InBox Burgers1D.spec.numVars (effectiveStateBox Burgers1D.spec)
      (decodeGrid burgersWordGrid idx) :=
    fun _ c hc => by have : c = 0 := by omega
                     subst this; exact (by decide +kernel : (effectiveStateBox Burgers1D.spec 0).contains (decodeGrid burgersWordGrid 0 0))
  have hStepW : stepQ32Scheme Burgers1D.spec .periodic [4] (1 / 4) false burgersWordGrid = burgersWordGrid := by
    funext idx c
    by_cases hc0 : c = 0
    · subst hc0
      have h0 : stepQ32Scheme Burgers1D.spec .periodic [4] (1 / 4) false burgersWordGrid 0 0 =
          ratToQ32Word 1 := by decide +kernel
      have hSame : stepQ32Scheme Burgers1D.spec .periodic [4] (1 / 4) false burgersWordGrid idx 0 =
          stepQ32Scheme Burgers1D.spec .periodic [4] (1 / 4) false burgersWordGrid 0 0 := rfl
      rw [hSame, h0]; rfl
    · let words := evalNonlinearFluxCellQ32 { Burgers1D.spec with cfl := 1 / 4 }
          (stepDag { Burgers1D.spec with cfl := 1 / 4 } 0) (fun _ => burgersWordGrid 0)
      change words.getD c 0#64 = (if c == 0 then ratToQ32Word 1 else 0#64)
      have hLen : words.length = 1 := by rfl
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : words.length ≤ c), hc0]
  have hConstQ32 : ∀ k, q32SchemeTrajectory Burgers1D.spec .periodic [4] ((1 / 16 : Rat) / (1 / 4))
      false burgersWordGrid k = burgersWordGrid := by
    rw [hDiv]; intro k; induction k with
    | zero => rfl
    | succ k ih => simp [q32SchemeTrajectory, ih, hStepW]
  have hConstRat : ∀ k, exactTrajectory (evalSchemeStepRat Burgers1D.spec .periodic [4]
      ((1 / 16 : Rat) / (1 / 4)) false) (decodeGrid burgersWordGrid) k = decodeGrid burgersWordGrid := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      simp only [exactTrajectory, ih]
      exact evalSchemeStepRat_steady_constant Burgers1D.spec .periodic [4] _ false (decV (burgersWordGrid 0))
        (Or.inl (by decide +kernel))
  have hTurnW : ∀ k, SchemeTurnInBoxW Burgers1D.spec .periodic [4] ((1 / 16 : Rat) / (1 / 4)) false
      (q32SchemeTrajectory Burgers1D.spec .periodic [4] ((1 / 16 : Rat) / (1 / 4)) false burgersWordGrid k) := by
    intro k; rw [hConstQ32 k, hDiv]
    simp only [SchemeTurnInBoxW, Bool.false_eq_true, ↓reduceIte, schemeAxisSchedule,
      List.length_cons, List.length_nil, show List.range 1 = [0] from rfl,
      List.map_cons, List.map_nil, ScheduleTurnInBoxW]
    have hSameW : stepQ32AxisAt Burgers1D.spec .periodic [4] 0 (1 / 4) burgersWordGrid = burgersWordGrid := by
      have hemp : Burgers1D.spec.sources.isEmpty = true := by decide +kernel
      simpa [stepQ32Scheme, stepQ32SourceAt, hemp, stepQ32Schedule, schemeAxisSchedule] using hStepW
    have hSameR : evalAxisStepRat Burgers1D.spec .periodic [4] 0 (1 / 4) (decodeGrid burgersWordGrid) =
        decodeGrid burgersWordGrid := evalAxisStepRat_constant Burgers1D.spec .periodic [4] 0 (1 / 4) (decV (burgersWordGrid 0))
    rw [hSameW, hSameR]
    exact ⟨hInW, hInR, hInR, hInW, hInR, hInR⟩
  have hStepEx : ∀ k, SchemeStepInBox Burgers1D.spec .periodic [4] ((1 / 16 : Rat) / (1 / 4)) false
      (exactTrajectory (evalSchemeStepRat Burgers1D.spec .periodic [4] ((1 / 16 : Rat) / (1 / 4)) false)
        (decodeGrid burgersWordGrid) k) :=
    fun k => by
      rw [hConstRat k]
      exact schemeTurnInBoxW_implies_schemeStepInBox _ _ _ _ _ burgersWordGrid (hTurnW 0)
  have hClose0 : GridClose Burgers1D.spec.numVars (weightOf Burgers1D.spec) 0
      (decodeGrid burgersWordGrid) (decodeGrid burgersWordGrid) := by
    intro idx c _; rw [ratAbs_sub_self]; grind
  have hVal : ∀ k idx c, k ≤ terminalTest.steps → idx < gridCellCount [4] → c < Burgers1D.spec.numVars →
      ratAbs (terminalTest.val k idx c) ≤ 1 := fun k _ _ _ _ _ => by
    cases k <;> simp only [terminalTest, ↓reduceIte, Nat.succ_ne_zero] <;> decide +kernel
  have hGrad : ∀ n d idx c, n < terminalTest.steps → d < [4].length → idx < gridCellCount [4] →
      c < Burgers1D.spec.numVars → ratAbs (spatialDiffTest [4] (1 / 4) (terminalTest.val n) d idx c) ≤ 0 :=
    fun n _ _ _ _ _ _ _ => by
      cases n <;> simp only [spatialDiffTest, terminalTest, ↓reduceIte, Nat.succ_ne_zero] <;> decide +kernel
  obtain ⟨Lsrc, hLsrc, hMain, _, _⟩ := endToEnd_q32_silicon_weak_form_bound Burgers1D.spec
    Burgers1D.endToEnd_certified [4] (by intro N hN; simp at hN; omega) (by decide +kernel)
    (1 / 4) (1 / 16) 1 16 0 (by grind) (by grind) (by decide +kernel)
    false (Or.inl (by decide +kernel)) εB hεB
    burgersWordGrid (decodeGrid burgersWordGrid) 0 hTurnW hStepEx hClose0 terminalTest hVal
    (fun n _ _ hn _ _ => by
      have : n = 0 := by change n < 1 at hn; omega
      subst n; exact (by decide +kernel : ratAbs ((1 - 0) / (1 / 16)) ≤ 16)) hGrad
  have hRate := lax_wendroff_1d_tvd_shock_rate Burgers1D.spec hVars1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 4 (by decide) (1 / 4) (1 / 16) 0 1 0 (by grind) (by grind)
    Rat.le_refl (decodeGrid burgersWordGrid) terminalTest (fun n _ => hStepEx n) hGrad
    (fun n i c hn hi hc => hVal n i c (Nat.le_of_lt hn) hi hc) (fun n _ => by rw [hConstRat n]; decide +kernel)
  exact ⟨εB, Lsrc, hεB, hLsrc, hMain, hRate⟩

-- 2d. `laxWendroffWeakJudge` on a Riemann jump against `φ(x) = x (1 - x)` (`|φ| ≤ 1/4`, `|Dφ| ≤ 1`):
-- each dyadic turn is accepted at its a-priori tolerance `C · totalOscillation`, which shrinks with
-- the mesh, and refused at tolerance `0`; shape and CFL faults are refused by the shape clause.
#guard
  let S := Burgers1D.spec
  let mkQuery (N : Nat) (cfl tol : Rat) : LaxWendroffAuditQuery :=
    let dx : Rat := 1 / (N : Rat)
    { spec := S, dims := [N], dx := dx, dt := dx * cfl, useStrang := false, steps := 1, tolerance := tol,
      initGrid := (List.range N).map (fun i => [if i < N / 2 then 1 else 0]),
      testGrid := List.replicate 2 ((List.range N).map fun (i : Nat) => [(i : Rat) * dx * (1 - (i : Rat) * dx)]) }
  let apriori (N : Nat) : Rat :=
    let q := mkQuery N (1 / 4) 0
    laxWendroffConst S 0 1 (1 / 4) * totalOscillation S [N] q.dx q.dt false 1 (queryTrajectory q)
  let turn (N : Nat) : MeshRefinementTurn := ⟨mkQuery N (1 / 4) (apriori N)⟩
  (runMeshRefinementTrace ⟨1 / 2, 0, 0⟩ [turn 4, turn 8, turn 16]).isSome &&
  (runMeshRefinementTrace ⟨1 / 2, 0, 0⟩ [turn 4, turn 4]).isNone &&
  0 < apriori 16 && apriori 16 < apriori 8 && apriori 8 < apriori 4 &&
  checkLaxWendroffAudit { (turn 4).query with initGrid := [] } == .refused .invalidQueryShape [] &&
  checkLaxWendroffAudit { (turn 4).query with testGrid := [[[]], [[]]] } == .refused .invalidQueryShape [] &&
  checkLaxWendroffAudit (mkQuery 4 2 1) == .refused .invalidQueryShape [] &&
  checkLaxWendroffAudit (mkQuery 4 (1 / 4) 0) == .refused .residualExceedsTolerance []

/-! ## 2b. Initial-TV-Only Weak-Residual Bound & Discrete Lax–Tadmor Entropy Inequality -/

-- Initial-TV-only `O(Δx)` weak-residual bound on nonlinear `Burgers1D.spec` Riemann step (0 external per-step TV or box assumptions!).
def burgersInitStep : MultiDGrid := fun idx _ => if idx % 4 < 2 then 1 / 2 else 0
def burgersBumpTest : SpaceTimeTestFn := ⟨2, fun n idx _ => if n == 1 && idx == 1 then 1 else 0⟩

example :
    let dt := (1 : Rat) / (8 * Burgers1D.spec.aMax)
    let U := exactTrajectory (evalSchemeStepRat Burgers1D.spec .periodic [4] (dt / (1 / 4)) false) burgersInitStep
    spatialTV1D 4 burgersInitStep = 1 ∧
    (∀ n, spatialTV1D 4 (U n) ≤ 1) ∧
    ratAbs (discreteWeakResidual Burgers1D.spec [4] (1 / 4) dt U burgersBumpTest) ≤
      laxWendroffConst Burgers1D.spec 0 4 1 *
        (((3 / 2 : Rat) / weightOf Burgers1D.spec 0) * ((2 : Rat) * dt * 1) * (1 / 4)) := by
  have haPos := Burgers1D.endToEnd_certified.rung1_continuum_ad_and_wavespeed.2.1
  have ha0 : 0 < Burgers1D.spec.aMax := haPos.1
  have hdt : 0 < (1 : Rat) / (8 * Burgers1D.spec.aMax) :=
    rat_inv_one_div_pos (by grind)
  have hcfl : 2 * (((1 : Rat) / (8 * Burgers1D.spec.aMax)) / (1 / 4)) * Burgers1D.spec.aMax ≤ 1 := by
    have hc := Rat.div_mul_cancel (by grind : 8 * Burgers1D.spec.aMax ≠ 0) (a := (1 : Rat)); grind
  have hInitBox : ∀ idx, InBox Burgers1D.spec.numVars (effectiveStateBox Burgers1D.spec) (burgersInitStep idx) := by
    intro idx c hc
    have hVars : Burgers1D.spec.numVars = 1 := by decide +kernel
    cases (show c = 0 by omega)
    unfold burgersInitStep
    by_cases hlt : idx % 4 < 2 <;> simp only [hlt, ↓reduceIte] <;> decide +kernel
  have hGrad : ∀ n d i c, n < burgersBumpTest.steps → d < [4].length → i < gridCellCount [4] → c < Burgers1D.spec.numVars →
      ratAbs (spatialDiffTest [4] (1 / 4) (burgersBumpTest.val n) d i c) ≤ 4 := by
    intro n d i c hn hd hi hc
    have hVars : Burgers1D.spec.numVars = 1 := by decide +kernel
    have hn2 : n = 0 ∨ n = 1 := by simp [burgersBumpTest] at hn; omega
    cases (show d = 0 by simp at hd; omega)
    cases (show c = 0 by omega)
    have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp [gridCellCount] at hi; omega
    rcases hn2 with rfl | rfl <;> rcases hi4 with rfl | rfl | rfl | rfl <;> decide +kernel
  have hVal : ∀ n i c, n < burgersBumpTest.steps → i < gridCellCount [4] → c < Burgers1D.spec.numVars →
      ratAbs (burgersBumpTest.val n i c) ≤ 1 := by
    intro n i c hn hi hc
    have hVars : Burgers1D.spec.numVars = 1 := by decide +kernel
    have hn2 : n = 0 ∨ n = 1 := by simp [burgersBumpTest] at hn; omega
    cases (show c = 0 by omega)
    have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp [gridCellCount] at hi; omega
    rcases hn2 with rfl | rfl <;> rcases hi4 with rfl | rfl | rfl | rfl <;> decide +kernel
  have hTV0 : spatialTV1D 4 burgersInitStep = 1 := by decide +kernel
  have hRate := lax_wendroff_1d_initial_tv_convergence_rate Burgers1D.spec
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (Rat.le_of_lt ha0)
    4 (by decide) (1 / 4) ((1 : Rat) / (8 * Burgers1D.spec.aMax)) 4 1 (by grind) hdt hcfl (by grind)
    burgersInitStep hInitBox burgersBumpTest hGrad hVal
  dsimp only [burgersBumpTest] at hRate
  rw [hTV0] at hRate
  exact ⟨hTV0, hRate.1, hRate.2⟩

-- Quadratic Burgers convex entropy `(η(u) = u²/2, q(u) = u³/3)` with Tadmor EC flux `fEC = (uL² + uL uR + uR²)/6`:
-- initial-data-only `O(Δx)` entropy residual bound + `discreteEntropyWeakPairing` discrimination of stationary expansion vs compression shocks!
def burgersEntropyInit : MultiDGrid := fun idx _ => if idx < 2 then -(1 / 2) else 1 / 2
def burgersNonnegTest : SpaceTimeTestFn := ⟨2, fun n idx _ => if n == 1 && idx == 1 then 1 else 0⟩

example :
    let U := exactTrajectory (evalTadmorStep1D burgersTadmorEC 1 ((1 / 16) / (1 / 4)) 4) burgersEntropyInit
    let Uexp : MultiDGrid := fun idx _ => if idx < 2 then -1 else 1
    let Ucomp : MultiDGrid := fun idx _ => if idx < 2 then 1 else -1
    -- Against the same non-negative compact `burgersShockTest`, stationary expansion shock `(-1, 1)` yields `> 0` (`= +1/24`),
    -- whereas stationary compressive shock `(1, -1)` yields `≤ 0` (`= -1/24`):
    (0 < discreteEntropyWeakPairing burgersEta burgersEntQ 4 (1 / 4) (1 / 16) (fun _ => Uexp) burgersShockTest ∧
      discreteEntropyWeakPairing burgersEta burgersEntQ 4 (1 / 4) (1 / 16) (fun _ => Ucomp) burgersShockTest ≤ 0 ∧
      -1 < evalTadmorStep1D burgersTadmorEC 1 ((1 / 16) / (1 / 4)) 4 Uexp 1 0) ∧
    -- Initial-data-only Burgers box invariance, TVD non-increase, and `O(Δx)` entropy weak-residual bound:
    (∀ k idx, idx < 4 → burgersEntDom 1 (U k idx)) ∧
    (∀ k, spatialTV1D 4 (U k) ≤ spatialTV1D 4 burgersEntropyInit) ∧
    discreteEntropyWeakPairing burgersEta burgersEntQ 4 (1 / 4) (1 / 16) U burgersNonnegTest ≤
      ((1 * 1) * 4 * ((2 : Rat) * (1 / 16) * spatialTV1D 4 burgersEntropyInit)) * (1 / 4) := by
  have hRef := burgers_stationary_expansion_shock_refused 1 (1 / 4) (1 / 16) (by grind) (by grind) (by grind)
  have hInitDom : ∀ idx, idx < 4 → burgersEntDom 1 (burgersEntropyInit idx) := by
    intro idx _; unfold burgersEntDom burgersEntropyInit; split <;> grind
  have hComp : CompactInTime burgersNonnegTest := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hNonneg : ∀ n idx, 0 ≤ burgersNonnegTest.val n idx 0 := by intro n idx; unfold burgersNonnegTest; dsimp only; split <;> grind
  have hGrad : ∀ n idx, n < burgersNonnegTest.steps → idx < 4 →
      ratAbs (spatialDiffTest [4] (1 / 4) (burgersNonnegTest.val n) 0 idx 0) ≤ 4 := by
    intro n idx hn hidx
    have hn2 : n = 0 ∨ n = 1 := by simp [burgersNonnegTest] at hn; omega
    have hi4 : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hn2 with rfl | rfl <;> rcases hi4 with rfl | rfl | rfl | rfl <;> decide +kernel
  have hConv := burgers_tadmor_initial_data_entropy_convergence 4 (by decide) 1 (1 / 4) (1 / 16) 4
    (by grind) (by grind) (by grind) (by grind) (by grind) burgersEntropyInit hInitDom
    burgersNonnegTest hComp hNonneg hGrad
  exact ⟨⟨hRef.2.2.2.2.1, hRef.2.2.2.2.2.2.1, hRef.2.2.2.2.2.2.2⟩, hConv⟩

/-! ## 3. Universal `#tooth` Kernel Mutation Kills Across Both Modules -/

#tooth strang_local_commutator_second_order by mutation commutatorGrid := fun _ _ _ _ _ => (0 : Rat)
#tooth strang_local_commutator_second_order by mutation strangSplitStep := fun s1 s2 dt U => s2 dt (s1 dt U)
#tooth strang_local_commutator_second_order by mutation jointTaylor2Step := fun L1 L2 dt U idx c => U idx c + dt * (L1 U idx c + L2 U idx c)
#tooth nonExtremaSlopeRatio_same_sign by mutation NonExtremaSlopeRatio := fun _ _ => True
#tooth evalAxisStepRat_summation_by_parts by mutation spatialDiffTest := fun dims dx ψ d idx c => (ψ idx c - ψ (axisNeighbor .periodic dims d 1 idx) c) / dx
#tooth evalSchemeStepRat_summation_by_parts by mutation schemeWeakSourcePairing := fun _ _ _ _ _ _ _ => (0 : Rat)
-- Planted faults: flux pairing dropped from the residual; cell volume dropped from the oscillation;
-- both time-endpoint errors dropped from the Q32 perturbation bound; dyadic guard dropped from a turn.
#tooth lax_wendroff_weak_residual_bound by mutation weakCellIntegrand := fun S _ _ dt U φ n idx c => U (n + 1) idx c * timeDiffTest dt φ n idx c + evalSourceComp S (U n idx) c * φ.val n idx c
#tooth lax_wendroff_1d_tvd_shock_rate by mutation totalOscillation := fun S dims dx dt useStrang K U => sumTo K (fun n => stepOscillation S dims dx dt useStrang (U n))
#tooth lax_wendroff_1d_initial_tv_convergence_rate by mutation spatialTV1D := fun _ _ => (0 : Rat)
#tooth lax_wendroff_discrete_entropy_weak_inequality by mutation discreteEntropyWeakPairing := fun eta q N dx dt U φ => dt * dx * sumTo φ.steps (fun n => sumTo N (fun idx => eta (U (n + 1) idx) * timeDiffTest dt φ n idx 0 + q (U n idx) * spatialDiffTest [N] dx (φ.val n) 0 idx 0))
#tooth lax_wendroff_discrete_entropy_weak_inequality by mutation evalTadmorStep1D := fun _ _ _ _ G => G
#tooth burgers_tadmor_initial_data_entropy_convergence by mutation burgersTadmorEC := fun _ _ _ => (0 : Rat)
#tooth burgers_stationary_expansion_shock_refused by mutation burgersEntQ := fun u => -((u 0 * u 0 * u 0) / 3)
#tooth endToEnd_q32_silicon_weak_form_bound by mutation q32WeakPerturbationBound := fun S dims dx dt Lsrc Mφ Mt Mx steps E => sumTo S.numVars (weightOf S) * cellVolume dims dx * (gridCellCount dims : Rat) * (dt * sumTo steps (fun n => E (n + 1) * Mt + E n * ((dims.length : Rat) * S.aMax * Mx + Lsrc * Mφ)))
#tooth runMeshRefinementTrace_sound by mutation stepMeshRefinement := fun st turn => if checkLaxWendroffAudit turn.query == .ok then some ⟨turn.query.dx, st.acceptedLevels + 1, rmax st.maxCertifiedResidual turn.query.tolerance⟩ else none
#tooth checkLaxWendroffAudit_sound by mutation checkLaxWendroffAudit := fun _ => Obend.Judge.Verdict.ok
#tooth stepMeshRefinement_none_iff_violation by mutation stepMeshRefinement := fun st _ => some st

/-! ## 4. Kernel Axiom, Closed-Theorem & `0 Classical.choice` Computational Audit -/

private meta partial def auditComputationalChoice (e : Lean.Expr) :
    StateRefT Lean.NameSet Lean.Meta.MetaM Unit := do
  if (← Lean.Meta.isProof e) || (← Lean.Meta.isType e) then return
  match e with
  | .const name _ =>
      if name == ``Classical.choice then throwError "Computational choice: {name}"
      if (← get).contains name then return
      modify (·.insert name)
      unless (← Lean.collectAxioms name).contains ``Classical.choice do return
      let info ← Lean.getConstInfo name
      if info matches .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ then return
      match info.value? (allowOpaque := true) with
      | some body => auditComputationalChoice body
      | none => throwError "Cannot inspect choice-dependent computational body: {name}"
  | .app f a => auditComputationalChoice f; auditComputationalChoice a
  | .lam name ty body bi =>
      Lean.Meta.withLocalDecl name bi ty fun x => auditComputationalChoice (body.instantiate1 x)
  | .letE name ty val body _ =>
      auditComputationalChoice val
      Lean.Meta.withLetDecl name ty val fun x => auditComputationalChoice (body.instantiate1 x)
  | .mdata _ body => auditComputationalChoice body
  | .proj _ _ body => auditComputationalChoice body
  | _ => pure ()

run_cmd do
  let env ← Lean.getEnv
  let ownModules := [`Obend.Analysis.LaxWendroffDefs, `Obend.Analysis.LaxWendroffConvergence]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.contains ``sorryAx then
      throwError "sorryAx dependency in {name}"
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if info matches .defnInfo _ | .opaqueInfo _ then
      Lean.Elab.Command.liftTermElabM do
        discard <| (auditComputationalChoice (.const name (info.levelParams.map Lean.Level.param))).run {}
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  Lean.logInfo "LaxWendroffDefs + LaxWendroffConvergence audit passed: 0 sorryAx, 0 compiler-trust, 0 closed library theorems, 0 computational choice."

#assert_axioms_tree

end Obend.Tests.LaxWendroffConvergenceTest
