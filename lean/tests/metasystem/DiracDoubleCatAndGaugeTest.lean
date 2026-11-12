import Obend.Geometry.CochainAndGauge
import Obend.Geometry.DiracDoubleCat
import Obend.Tactic.Tooth
import Obend.AssertAxioms

/-!
# `tests/metasystem/DiracDoubleCatAndGaugeTest.lean` — End-to-End Verification, Cross-Organ Welds & `#tooth` Kills

Verifies `Obend.Geometry.CochainAndGauge` and `Obend.Geometry.DiracDoubleCat`:
1. `#assert_axioms_tree` whole-cone axiom purity (`0` stub axioms, `0` custom axioms, `0` compiler trust).
2. Concrete `#guard` & inhabitedness witnesses exercising every deliverable:
   - 3D unit cube DEC cell complex (`unitCubeComplex3D`), `coboundary_sq_zero`, `discrete_stokes_exact`,
     multi-step staggered Yee `runDecMaxwellSteps` preserving $\nabla \cdot B = 0$ (`decMaxwell_divB_invariant`)
     and Gauss's law (`decMaxwell_charge_continuity`), `hodgeLaplacian0_psd`, and `UndirectedWalk` kernel.
   - Non-commuting cellular gauge connection (`[D_x, D_y] = F_{xy} ≠ 0`), local `GL_2(ℚ)` gauge
     covariance + Wilson-loop trace invariance, and 6-face non-Abelian `discrete_bianchi_identity`.
   - Three cross-organ welds: Scharfetter–Gummel Slotboom semiconductor gauge, rational Cayley `SO(2)`
     Park/Clarke rotating motor frame on `Obend.Hardware.CurrentLoop.RlPlant`, and cellular sheaf
     `H^0 / H^1` circular arbitrage refutation.
   - Four concrete certified Dirac structures (`hypergraphJunctionDirac`, `gyratorMotorDirac`,
     `idealTransformerDirac`, `decMaxwellLineCellDirac`), resistive Port-Hamiltonian closure bridged to
     `Obend.Category.OpenDissipativeSys`, horizontal/vertical double-category composition, non-trivial
     $2 \times 2$ `doubleCat_interchange_law` grid, `GradedTriple` lifting, and the worked multiscale
     telegrapher-to-MNA square certified `.ok` by `Obend.Hardware.CircuitDae.checkMnaDaeProblem`.
3. **9 `#tooth` kernel mutation kills** across DEC exactness, Yee Maxwell Faraday updates, Hodge SPD
   positivity, non-Abelian curvature, gauge parallel transport, Dirac bond pairing, Dirac isotropy/rank,
   resistive passivity, and double-categorical pasting grades.
-/

namespace Obend.Tests.Metasystem.DiracDoubleCatAndGauge

open Obend.Analysis
open Obend.Category
open Obend.Hardware.CurrentLoop
open Obend.Hardware.CircuitDae
open Obend.Hardware.OpenHypergraph
open Obend.Geometry.CochainAndGauge
open Obend.Geometry.DiracDoubleCat

set_option autoImplicit false

/-! ## 0. Whole-Cone Axiom Purity Audit (`0` Stub Axioms, `0` Custom Axioms, `0` Compiler Trust) -/

#assert_axioms_tree

/-! ## 1. DEC Cell Complex, Yee Maxwell Multi-Step Invariants & SPD Hodge–Laplacian Witnesses -/

def unitCubeMetric : DecHodgeMetric where
  star0 := mkVec 8  (fun _ => 1)
  star1 := mkVec 12 (fun e => (e + 1 : Nat))
  star2 := mkVec 6  (fun _ => 2)

#guard checkComplexExact unitCubeComplex3D
#guard checkHodgeSpd unitCubeComplex3D unitCubeMetric

#guard
  let φ : List CanonicalRat := [1, 3, -2, 5, 0, 4, -1, 7]
  let α : List CanonicalRat := [2, -1, 3, 0, 4, -2, 1, 5, -3, 2, 0, -4]
  let c1 : List CanonicalRat := [1, 0, -1, 2, 1, -2, 0, 1, 3, -1, 2, 1]
  let c2 : List CanonicalRat := [2, -1, 3, 1, -2, 4]
  let β  : List CanonicalRat := d1 unitCubeComplex3D α
  let c3 : List CanonicalRat := [5]
  d1 unitCubeComplex3D (d0 unitCubeComplex3D φ) == zeroCochain 6 &&
  d2 unitCubeComplex3D (d1 unitCubeComplex3D α) == zeroCochain 1 &&
  vecDotN 12 (d0 unitCubeComplex3D φ) c1 == vecDotN 8 φ (bdry1 unitCubeComplex3D c1) &&
  vecDotN 6  (d1 unitCubeComplex3D α) c2 == vecDotN 12 α (bdry2 unitCubeComplex3D c2) &&
  vecDotN 1  (d2 unitCubeComplex3D β) c3 == vecDotN 6 β (bdry3 unitCubeComplex3D c3) &&
  decide (0 < vecDotN 8 φ (hodgeLaplacian0 unitCubeComplex3D unitCubeMetric φ))

-- Multi-step Yee DEC Maxwell trajectory witness: 3 variable-`dt` steps with non-zero currents
-- preserve `d2 B = [0]` and discrete Gauss's law `d_0*(star_1 E) = rho` with zero cleaning variables.
#guard
  let K := unitCubeComplex3D
  let M := unitCubeMetric
  let e0 : List CanonicalRat := [1, -1, 2, 0, -2, 1, 0, 3, -1, 2, -2, 1]
  let b0 : List CanonicalRat := d1 K [1, 2, -1, 0, 3, -2, 1, 0, -1, 2, 1, -3]
  let st0 : DecMaxwellState := { eField := e0, bField := b0 }
  let ρ0 := divDual0 K (applyHodge M.star1 K.numE e0)
  let j1 : List CanonicalRat := [1, 0, -1, 2, 0, 1, -1, 0, 2, -1, 0, 1]
  let j2 : List CanonicalRat := [0, 2, 1, -1, 1, 0, 2, -2, 0, 1, -1, 0]
  let j3 : List CanonicalRat := [-1, 1, 0, 1, -2, 2, 0, 1, -1, 0, 2, -1]
  let dt1 : CanonicalRat := 1 / 4
  let dt2 : CanonicalRat := 1 / 2
  let dt3 : CanonicalRat := 1 / 3
  let ρ1 := vecSubN K.numV ρ0 (vecScaleN K.numV dt1 (divDual0 K j1))
  let ρ2 := vecSubN K.numV ρ1 (vecScaleN K.numV dt2 (divDual0 K j2))
  let ρ3 := vecSubN K.numV ρ2 (vecScaleN K.numV dt3 (divDual0 K j3))
  let stFin := runDecMaxwellSteps K M st0 [(dt1, j1), (dt2, j2), (dt3, j3)]
  d2 K b0 == zeroCochain 1 &&
  d2 K stFin.bField == zeroCochain 1 &&
  divDual0 K (applyHodge M.star1 K.numE stFin.eField) == ρ3 &&
  stFin.bField != b0

/-- Inhabitedness witness for `UndirectedWalk` and `hodgeLaplacian0_kernel_iff_locally_constant`
    connecting opposite corners `0` and `7` of `unitCubeComplex3D`. -/
def cubeCornerWalk07 : UndirectedWalk unitCubeComplex3D 0 7 :=
  .stepFwd 0 rfl (.stepFwd 5 rfl (.stepFwd 11 rfl (.refl 7)))

example (φ : List CanonicalRat)
    (hKer : hodgeLaplacian0 unitCubeComplex3D unitCubeMetric φ = zeroCochain 8) :
    vecEntry φ 0 = vecEntry φ 7 :=
  (hodgeLaplacian0_kernel_iff_locally_constant unitCubeComplex3D unitCubeMetric
    (by decide +kernel) (by decide +kernel) φ).2 hKer ⟨cubeCornerWalk07⟩

/-! ## 2. Non-Commuting Gauge Curvature, Wilson-Loop Invariance, Bianchi & 3 Cross-Organ Welds -/

def lowerShearElem (k : Int) : GaugeElem2 where
  fwd := ⟨1, 0, (k : CanonicalRat), 1⟩
  inv := ⟨1, 0, -(k : CanonicalRat), 1⟩
  inv_l := by simp only [Mat2Rat.mul, Mat2Rat.id, Mat2Rat.mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩
  inv_r := by simp only [Mat2Rat.mul, Mat2Rat.id, Mat2Rat.mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩

/-- Non-Abelian `GL_2(ℚ)` cube links (mixing non-commuting upper and lower shears!). -/
def nonAbelianCubeLinks : CubeGaugeLinks where
  e0  := shearGaugeElem 1
  e1  := lowerShearElem 2
  e2  := shearGaugeElem (-1)
  e3  := lowerShearElem 3
  e4  := lowerShearElem (-1)
  e5  := shearGaugeElem 2
  e6  := lowerShearElem 1
  e7  := shearGaugeElem 3
  e8  := shearGaugeElem (-2)
  e9  := lowerShearElem (-2)
  e10 := shearGaugeElem 1
  e11 := lowerShearElem (-3)

#guard
  let ψ : Int → Int → Vec2Rat := fun i j => ⟨(i : CanonicalRat) + 1, 2 * (j : CanonicalRat) + 1⟩
  let g : Int → Int → GaugeElem2 := fun i j =>
    if (i + j) % 2 == 0 then shearGaugeElem (i + 1) else lowerShearElem (j - 2)
  let conn := curvedShearConnection
  let conn' := gaugeTransformConn g conn
  let ψ' := gaugeTransformSec g ψ
  -- 1. Non-zero curvature & non-commuting covariant partials:
  plaquetteCurvature conn 0 0 != Mat2Rat.zero &&
  covDiffX conn (covDiffY conn ψ) 0 0 != covDiffY conn (covDiffX conn ψ) 0 0 &&
  Vec2Rat.sub (covDiffX conn (covDiffY conn ψ) 0 0) (covDiffY conn (covDiffX conn ψ) 0 0) ==
    Mat2Rat.mulVec (plaquetteCurvature conn 0 0) (transportedCornerStalk conn ψ 0 0) &&
  -- 2. Local gauge covariance & Wilson-loop trace invariance:
  covDiffX conn' ψ' 0 0 == Mat2Rat.mulVec (g 0 0).fwd (covDiffX conn ψ 0 0) &&
  Mat2Rat.trace (wilsonPlaquette conn' 0 0) == Mat2Rat.trace (wilsonPlaquette conn 0 0) &&
  -- 3. Non-Abelian 6-face cube Bianchi identity with non-commuting links:
  Mat2Rat.mul nonAbelianCubeLinks.e0.fwd nonAbelianCubeLinks.e1.fwd !=
    Mat2Rat.mul nonAbelianCubeLinks.e1.fwd nonAbelianCubeLinks.e0.fwd &&
  cubeSixFaceHolonomyProduct nonAbelianCubeLinks == Mat2Rat.id

/-- Concrete `#guard` exercising all 3 cross-organ gauge instantiations:
    (1) Scharfetter–Gummel Slotboom drift-diffusion equilibrium,
    (2) Exact `3-4-5` rational Cayley `SO(2)` Park/Clarke motor frame on `RlPlant`,
    (3) Triangle FX market circular arbitrage obstruction (`2 * 2 * (1/2) = 2 ≠ 1`). -/
def triangleMarketComplex : CellComplex3D where
  numV    := 3
  edges   := [(0, 1), (1, 2), (2, 0)]
  faces   := []
  volumes := []

#guard
  -- (1) Scharfetter–Gummel Slotboom equilibrium (u = w⁻¹ n = [3, 3, 3] constant => zero current):
  let wBoltz : List CanonicalRat := [1, 2, 4]
  let nEq    : List CanonicalRat := [3, 6, 12]
  let nNonEq : List CanonicalRat := [3, 5, 12]
  -- (2) Cayley SO(2) rotator at α = 1/2 => R = [[3/5, 4/5], [-4/5, 3/5]]:
  let R := cayleyRot2 (1 / 2)
  let Ω := parkCoriolisConn (1 / 2) 3
  let iDq : Vec2Rat := ⟨5, -2⟩
  -- (3) Circular FX arbitrage holonomy on `triangleMarketComplex`:
  let fxRates : List CanonicalRat := [2, 2, 1 / 2]
  checkComplexExact triangleMarketComplex &&
  scharfetterGummelCovDiff triangleMarketComplex wBoltz nEq == zeroCochain 3 &&
  scharfetterGummelCovDiff triangleMarketComplex wBoltz nNonEq != zeroCochain 3 &&
  R == ⟨3 / 5, 4 / 5, -(4 / 5), 3 / 5⟩ &&
  Mat2Rat.mul R.transpose R == Mat2Rat.id &&
  Mat2Rat.det R == 1 &&
  Vec2Rat.dot iDq (Mat2Rat.mulVec Ω iDq) == 0 &&
  checkClosedDirectedCycle triangleMarketComplex [0, 1, 2] &&
  mulCycleHolonomy fxRates [0, 1, 2] == 2

example : ¬ ∃ prices, IsFlatMultiplicativeSection triangleMarketComplex [2, 2, 1 / 2] prices :=
  (sheaf_cycle_holonomy_obstruction triangleMarketComplex (by decide +kernel)).2.2
    [2, 2, 1 / 2] 0 1 2 0 1 2 (by decide) rfl rfl rfl (by decide +kernel)

/-! ## 3. Acausal Dirac Structures, `OpenDissipativeSys` Plant & `MultiscaleOpenDouble` Interchange -/

#guard
  junctionHypergraph3.wf &&
  checkDiracIsotropicAndRank (hypergraphJunctionDirac junctionHypergraph3 0) &&
  checkDiracIsotropicAndRank (gyratorMotorDirac (3 / 2)) &&
  checkDiracIsotropicAndRank (idealTransformerDirac (5 / 3)) &&
  checkDiracIsotropicAndRank decMaxwellLineCellDirac

/-- Concrete resistive closure terminating shaft port `1` of `gyratorMotorDirac 2` onto viscous
    damping $R = [[3]]$ ($e_1 = 3 f_1$), inducing passive reflected electrical impedance $e_0 = -\frac{4}{3} f_0$
    ($f_1 = \frac{2}{3} f_0 \implies e_0 = -2 f_1 = -\frac{4}{3} f_0$, dissipating $e_0 f_0 = -\frac{4}{3} f_0^2 \le 0$). -/
def dampedMotorClosure : ResistiveDiracClosure where
  extDim  := 1
  resDim  := 1
  core    := gyratorMotorDirac 2
  matR    := [[3]]
  resGram := [{ weight := 6, vec := [1] }]

#guard checkResistiveDiracClosure dampedMotorClosure

/-- Non-zero inhabited motor port witness `fExt = [3], eExt = [-4]` (`fRes = [2], eRes = [6]`,
    dissipating `eExt · fExt = -12 ≤ 0` into shaft viscous load `R = 3`). -/
theorem dampedMotorClosure_nonzero_extMem : dampedMotorClosure.ExtMem [3] [-4] := by
  refine ⟨[2], [6], ?_, fun j hj => ?_⟩
  · intro i hi; change i < 2 at hi
    match i with | 0 | 1 => decide +kernel | n + 2 => omega
  · change j < 1 at hj
    have hj0 : j = 0 := by omega
    subst hj0
    decide +kernel

/-- Concrete inhabited `DiracPortHamiltonianPlant` carrying active non-zero motor port dissipation `[3], [-4]`. -/
def activeMotorPlant : DiracPortHamiltonianPlant Nat Int Int where
  energy s := 12 * (s : Int)
  energy_nonneg s := by omega
  closure := dampedMotorClosure
  closure_ok := by decide +kernel
  step s u := (if 0 < s then s - 1 else 0, u)
  portWitness s _ := if 0 < s then ([3], [-4]) else ([0], [0])
  witness_mem s _ := by
    split
    · exact dampedMotorClosure_nonzero_extMem
    · refine ⟨[0], [0], ?_, fun j hj => ?_⟩
      · intro i hi; change i < 2 at hi; match i with | 0 | 1 => decide +kernel | n + 2 => omega
      · change j < 1 at hj
        have hj0 : j = 0 := by omega
        subst hj0
        decide +kernel
  supply u _ := if 0 ≤ u then u else 0
  dissipative_balance s u := by
    by_cases hs : 0 < s
    · simp only [hs, ↓reduceIte]
      have hDot : vecDotN dampedMotorClosure.extDim [-4] [3] = -12 := by decide +kernel
      rw [hDot]
      have hInt : (12 * ((s - 1 : Nat) : Int) - 12 * (s : Int)) ≤ (if 0 ≤ u then u else 0) + (-12) := by
        split <;> omega
      have hRat := Rat.intCast_le_intCast.mpr hInt
      grind
    · simp only [hs, ↓reduceIte]
      have hs0 : s = 0 := by omega
      subst hs0
      have hDot : vecDotN dampedMotorClosure.extDim [0] [0] = 0 := by decide +kernel
      rw [hDot]
      have hInt : (0 : Int) ≤ (if 0 ≤ u then u else 0) := by split <;> omega
      have hRat := Rat.intCast_le_intCast.mpr hInt
      grind

example (s0 : Nat) (us : List Int) :
    0 ≤ activeMotorPlant.energy (activeMotorPlant.toOpenDissipativeSys.runTrajectory s0 us) ∧
    activeMotorPlant.energy (activeMotorPlant.toOpenDissipativeSys.runTrajectory s0 us) ≤
      activeMotorPlant.energy s0 + activeMotorPlant.toOpenDissipativeSys.trajectorySupply s0 us :=
  diracPlant_trajectory_lyapunov activeMotorPlant s0 us

/-- Non-trivial $2 \times 2$ double-category interchange witness with 4 distinct positive `defectEps`
    values (`1/10, 1/20, 1/30, 1/40`) and 4 distinct 5-axis `CompositeGrade` vectors, plus worked
    telegrapher-to-MNA `checkMnaDaeProblem = .ok` verification. -/
def demoScaleObj : ScaleObj := lumpedMnaScaleObj

def mkDemoSquare (eps : CanonicalRat) (hNonneg : 0 ≤ eps) (g : CompositeGrade) :
    MultiscaleSquare (HorizOpenSys.id demoScaleObj) (HorizOpenSys.id demoScaleObj)
      (VertCoarseGrain.id demoScaleObj) (VertCoarseGrain.id demoScaleObj) where
  defectEps := eps
  defect_nonneg := hNonneg
  grade := g
  closure_bound x := by
    dsimp [HorizOpenSys.id, VertCoarseGrain.id]
    rw [vecMaxDist_refl]
    exact hNonneg

#guard
  let sqα := mkDemoSquare (1 / 10) (by decide +kernel) ⟨1, 2, 0, 3, -1⟩
  let sqβ := mkDemoSquare (1 / 20) (by decide +kernel) ⟨2, 1, 1, 4, -2⟩
  let sqγ := mkDemoSquare (1 / 30) (by decide +kernel) ⟨3, 0, 2, 1,  0⟩
  let sqδ := mkDemoSquare (1 / 40) (by decide +kernel) ⟨0, 4, 1, 2, -3⟩
  let vh := vPaste (hPaste sqα sqβ) (hPaste sqγ sqδ)
  let hv := hPaste (vPaste sqα sqγ) (vPaste sqβ sqδ)
  vh.defectEps == 25 / 120 &&
  vh.defectEps == hv.defectEps &&
  vh.grade == hv.grade &&
  vh.grade == ⟨6, 7, 4, 10, -6⟩ &&
  checkMnaDaeProblem 1 lumpedTelegrapherMnaProb lumpedTelegrapherMnaCert == .ok &&
  telegrapherToLumpedMnaSquare.defectEps == 1 / 10

/-- Master universal integration bundle linking DEC exactness, Yee Maxwell $\nabla \cdot B = 0$,
    gauge curvature commutator, Cayley `SO(2)` Coriolis neutrality, Dirac self-orthogonality,
    double-category interchange, and worked MNA circuit passivity. -/
theorem geometry_doubleCat_master_bundle
    (K : CellComplex3D) (M : DecHodgeMetric)
    (hExact : checkComplexExact K = true) (hSpd : checkHodgeSpd K M = true)
    (φ : List CanonicalRat)
    (steps : List (CanonicalRat × List CanonicalRat)) (st0 : DecMaxwellState)
    (hDiv0 : d2 K st0.bField = zeroCochain K.numC)
    (conn : GaugeConnection2D) (ψ : Int → Int → Vec2Rat) (i j : Int)
    (plant : RlPlant) (αRot dαRot : CanonicalRat) (iDq diDq : Vec2Rat)
    (D : KernelDirac) (hDirac : checkDiracIsotropicAndRank D = true) (f e : List CanonicalRat) :
    d1 K (d0 K φ) = zeroCochain K.numF ∧
    d2 K (runDecMaxwellSteps K M st0 steps).bField = zeroCochain K.numC ∧
    0 ≤ vecDotN K.numV φ (hodgeLaplacian0 K M φ) ∧
    Vec2Rat.sub (covDiffX conn (covDiffY conn ψ) i j) (covDiffY conn (covDiffX conn ψ) i j) =
      Mat2Rat.mulVec (plaquetteCurvature conn i j) (transportedCornerStalk conn ψ i j) ∧
    Vec2Rat.dot iDq (Mat2Rat.mulVec (parkCoriolisConn αRot dαRot) iDq) = 0 ∧
    (D.Mem f e ↔ D.Orthogonal f e) ∧
    checkMnaDaeProblem 1 lumpedTelegrapherMnaProb lumpedTelegrapherMnaCert = .ok := by
  exact ⟨(coboundary_sq_zero K hExact φ []).1,
         decMaxwell_divB_invariant K M hExact steps st0 hDiv0,
         hodgeLaplacian0_psd K M hSpd φ,
         covariant_commutator_eq_curvature conn ψ i j,
         (parkFrame_coriolis_connection_power_neutral plant αRot dαRot iDq diDq).2.2.2.2.1,
         dirac_self_orthogonal_iff D hDirac f e,
         (telegrapherToLumpedMna_worked_sound 2 (by omega) φ).1⟩

/-! ## 4. `#tooth` Kernel Mutation Kills (`9` Geometric, Gauge, Dirac & Double-Category Bugs Rejected) -/

-- 1. Bypassed Chain-Complex Exactness (`checkComplexExact := true`): lets non-closed faces
--    violate `bdry1 ∘ bdry2 = 0`, breaking `coboundary_sq_zero`.
#tooth Obend.Geometry.CochainAndGauge.coboundary_sq_zero
  by mutation Obend.Geometry.CochainAndGauge.checkComplexExact := fun _ => true

/-- 2. **Corrupted Faraday Update (`stepDecMaxwell` subtracts raw `eField` instead of `d1 K eField`):**
    destroys topological $\nabla \cdot B = 0$ invariance across staggered steps. -/
def stepDecMaxwellMissingCurl (K : CellComplex3D) (M : DecHodgeMetric)
    (dt : CanonicalRat) (jDual : List CanonicalRat) (st : DecMaxwellState) : DecMaxwellState :=
  let bNext := vecSubN K.numF st.bField (vecScaleN K.numF dt st.eField)
  let hNext := applyHodge M.star2 K.numF bNext
  let ampRhs := vecSubN K.numE (curlDual1 K hNext) jDual
  let eNext := vecAddN K.numE st.eField (vecScaleN K.numE dt (applyHodgeInv M.star1 K.numE ampRhs))
  { eField := eNext, bField := bNext }

#tooth Obend.Geometry.CochainAndGauge.decMaxwell_divB_invariant
  by mutation Obend.Geometry.CochainAndGauge.stepDecMaxwell := stepDecMaxwellMissingCurl

-- 3. Bypassed Hodge Star Positivity (`checkHodgeSpd := true`): admits indefinite/negative
--    `star_1 < 0` metrics, breaking `hodgeLaplacian0_psd`.
#tooth Obend.Geometry.CochainAndGauge.hodgeLaplacian0_psd
  by mutation Obend.Geometry.CochainAndGauge.checkHodgeSpd := fun _ _ => true

-- 4. Abelian/Flat Cosplay Curvature (`plaquetteCurvature := 0`): pretends covariant partial
--    derivatives always commute even on curved gauge bundles!
#tooth Obend.Geometry.CochainAndGauge.covariant_commutator_eq_curvature
  by mutation Obend.Geometry.CochainAndGauge.plaquetteCurvature := fun _ _ _ => Mat2Rat.zero

-- 5. Untransformed Gauge Connection (`gaugeTransformConn` leaves links `U_e` unchanged):
--    breaks local gauge covariance of `covDiffX`, `covDiffY`, and `plaquetteCurvature`.
#tooth Obend.Geometry.CochainAndGauge.gauge_transform_covariance
  by mutation Obend.Geometry.CochainAndGauge.gaugeTransformConn := fun _ conn => conn

/-- 6. **Skew Instead of Symmetric Dirac Bond Pairing (`e1 · f2 - e2 · f1`):** makes every vector
    isotropic regardless of Tellegen power $e \cdot f$, falsifying `dirac_self_orthogonal_iff` ($D = D^\perp$). -/
def diracPlusPairingSkew (n : Nat) (f1 e1 f2 e2 : List CanonicalRat) : CanonicalRat :=
  vecDotN n e1 f2 - vecDotN n e2 f1

#tooth Obend.Geometry.DiracDoubleCat.dirac_self_orthogonal_iff
  by mutation Obend.Geometry.DiracDoubleCat.diracPlusPairing := diracPlusPairingSkew

-- 7. Bypassed Dirac Isotropy & Rank Check (`checkDiracIsotropicAndRank := true`): admits
--    non-skew active matrices `K L^T + L K^T ≠ 0`, breaking `dirac_self_orthogonal_iff`.
#tooth Obend.Geometry.DiracDoubleCat.dirac_self_orthogonal_iff
  by mutation Obend.Geometry.DiracDoubleCat.checkDiracIsotropicAndRank := fun _ => true

-- 8. Bypassed Resistive Passivity Check (`checkResistiveDiracClosure := true`): admits active
--    negative resistances `R < 0`, breaking `resistiveDirac_dissipative_power`.
#tooth Obend.Geometry.DiracDoubleCat.resistiveDirac_dissipative_power
  by mutation Obend.Geometry.DiracDoubleCat.checkResistiveDiracClosure := fun _ => true

/-- 9. **Dropped Horizontal Grade Accumulation (`hPaste` drops `β.grade`):** breaks
    `hPaste_sound` grade additivity `(hPaste α β).grade = α.grade + β.grade`. -/
def hPasteDropRightGrade {F1 F2 F3 C1 C2 C3 : ScaleObj}
    {Sf1 : HorizOpenSys F1 F2} {Sf2 : HorizOpenSys F2 F3}
    {Sc1 : HorizOpenSys C1 C2} {Sc2 : HorizOpenSys C2 C3}
    {π1 : VertCoarseGrain F1 C1} {π2 : VertCoarseGrain F2 C2} {π3 : VertCoarseGrain F3 C3}
    (α : MultiscaleSquare Sf1 Sc1 π1 π2)
    (β : MultiscaleSquare Sf2 Sc2 π2 π3) :
    MultiscaleSquare (horizComp Sf1 Sf2) (horizComp Sc1 Sc2) π1 π3 where
  defectEps := α.defectEps + β.defectEps
  defect_nonneg := by have := α.defect_nonneg; have := β.defect_nonneg; grind
  grade := α.grade
  closure_bound x := by
    dsimp [horizComp]
    have hTri := vecMaxDist_triangle C3.obsDim
      (π3.projObs (Sf2.stepObs (Sf1.stepObs x)))
      (Sc2.stepObs (π2.projObs (Sf1.stepObs x)))
      (Sc2.stepObs (Sc1.stepObs (π1.projObs x)))
    have hBeta := β.closure_bound (Sf1.stepObs x)
    have hLip := Sc2.stepObs_nonexpansive (π2.projObs (Sf1.stepObs x)) (Sc1.stepObs (π1.projObs x))
    have hAlpha := α.closure_bound x
    grind

#tooth Obend.Geometry.DiracDoubleCat.hPaste_sound
  by mutation Obend.Geometry.DiracDoubleCat.hPaste := hPasteDropRightGrade

/-- 10. **Non-Medial Multiplicative Defect Pasting (`vPaste` adds `α.defectEps * γ.defectEps`):**
    genuinely violates Eckmann–Hilton mediality (`(a+b)(c+d) ≠ ac + bd`), breaking `doubleCat_interchange_law` (`vh = hv`). -/
def vPasteNonlinearDefect {F1 F2 M1 M2 C1 C2 : ScaleObj}
    {Sf : HorizOpenSys F1 F2} {Sm : HorizOpenSys M1 M2} {Sc : HorizOpenSys C1 C2}
    {π1L : VertCoarseGrain F1 M1} {π1R : VertCoarseGrain F2 M2}
    {π2L : VertCoarseGrain M1 C1} {π2R : VertCoarseGrain M2 C2}
    (α : MultiscaleSquare Sf Sm π1L π1R)
    (γ : MultiscaleSquare Sm Sc π2L π2R) :
    MultiscaleSquare Sf Sc (vertComp π1L π2L) (vertComp π1R π2R) where
  defectEps := α.defectEps + γ.defectEps + α.defectEps * γ.defectEps
  defect_nonneg := by
    have := α.defect_nonneg; have := γ.defect_nonneg
    have := Rat.mul_nonneg α.defect_nonneg γ.defect_nonneg; grind
  grade := α.grade + γ.grade
  closure_bound x := by
    dsimp [vertComp]
    have hTri := vecMaxDist_triangle C2.obsDim
      (π2R.projObs (π1R.projObs (Sf.stepObs x)))
      (π2R.projObs (Sm.stepObs (π1L.projObs x)))
      (Sc.stepObs (π2L.projObs (π1L.projObs x)))
    have hProj := π2R.projObs_nonexpansive (π1R.projObs (Sf.stepObs x)) (Sm.stepObs (π1L.projObs x))
    have hAlpha := α.closure_bound x
    have hGamma := γ.closure_bound (π1L.projObs x)
    have hProd := Rat.mul_nonneg α.defect_nonneg γ.defect_nonneg
    grind

#tooth Obend.Geometry.DiracDoubleCat.doubleCat_interchange_law
  by mutation Obend.Geometry.DiracDoubleCat.vPaste := vPasteNonlinearDefect

/-- 11. **Orientation-Blind Walk Integral (`walkIntegral` ignores backward `-` sign):**
    breaks `sheaf_spanning_tree_exact_iff` on undirected spanning trees with reversed edges. -/
def walkIntegralUnsigned (ω : List CanonicalRat) : List SignedEdgeStep → CanonicalRat
  | [] => 0
  | step :: rest => vecEntry ω step.edge + walkIntegralUnsigned ω rest

#tooth Obend.Geometry.CochainAndGauge.sheaf_spanning_tree_exact_iff
  by mutation Obend.Geometry.CochainAndGauge.walkIntegral := walkIntegralUnsigned

end Obend.Tests.Metasystem.DiracDoubleCatAndGauge
