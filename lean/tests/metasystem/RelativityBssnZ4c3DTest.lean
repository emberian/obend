/-
# `tests/metasystem/RelativityBssnZ4c3DTest.lean`

End-to-end integration, positive/negative `symmetricHyperbolicJudge` vectors, `≥ 8` universal
`#tooth` kernel mutation kills, zero-closed-theorem, zero-compiler-trust, and `0 Classical.choice`
computational audit covering:
1. `Obend.Analysis.SymmetricHyperbolicEnergy`:
   - Constructive SPD Gram coercivity (`checkSpdGramCoercive_sound`), rational $L^T D L$ synthesis
     (`computeShiftedLdl`), and indefinite witness extraction (`findIndefiniteWitness`),
   - Discrete skew-adjointness of centered spatial differences (`centeredDiff_h0_skew_adjoint`),
   - 4th-order Kreiss–Oliger dissipation negativity (`kreissOliger4_energy_nonpositive`),
   - Pure Friedrichs Rusanov energy dissipation (`rusanov_symmetric_energy_dissipative`),
   - Discrete Gronwall $H_0$-norm stability & strict contraction (`symmetricHyperbolic_gronwall_stability`),
   - Inhabited non-tautological `symmetricHyperbolicJudge` positive & negative refutation vectors.
2. `Obend.Analysis.RelativityBssnZ4c3D`:
   - 5-variable 3D linear Friedrichs constraint-model symmetric hyperbolicity (`z4c3d_constraint_symmetric_hyperbolic`),
   - Principal-symbol characteristic eigenpairs `{−β_n, −β_n ± α}` (`z4c3d_characteristic_eigenpairs`),
   - 3D spatial $C_3$ cyclic axis equivariance (`z4c3d_cyclic_axis_equivariant`),
   - Exponential 3D linear constraint-energy damping (`κ_1 > 0` vs undamped `κ_1 = 0`, `z4c3d_total_constraint_energy_damped`),
   - 3D `#pde_solver BssnZ4cConstraint3D` `EndToEndPdeCert` & 1D slab reduction (`z4c3d_slab_reduction_matches_1d`),
   - Spatially varying `(α(x), β^i(x))` Friedrichs commutator & Strand SBP + Olsson–Strand SAT open-box dissipation.
-/
import Lean
import Obend.Analysis.SymmetricHyperbolicEnergy
import Obend.Analysis.RelativityBssnZ4c3D
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Tests.RelativityBssnZ4c3DTest

open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox
open Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws
open Obend.Analysis.SymmetricHyperbolicEnergy
open Obend.Analysis.RelativityBssnZ4c3D
open Obend.Hardware.MultiDStencilCorrect
open Obend.Hardware.PdeSolvers
open Obend.Tactic.SymDiffAndFlux

set_option autoImplicit false

local instance : DecidableEq symmetricHyperbolicJudge.Clause :=
  inferInstanceAs (DecidableEq SymHypClause)

/-! ## 1. `SymmetricHyperbolicEnergy` Ground & `symmetricHyperbolicJudge` Positive/Negative Vectors -/

-- Non-diagonal 2×2 SPD matrix `H_0 = [[2, 1], [1, 2]]` with coercivity `μ = 1/2`:
-- `computeShiftedLdl` synthesizes `G = [[1, 2/3], [0, 1]]`, `pivots = [3/2, 5/6]` automatically!
def coupledH0 : List (List Rat) := [[2, 1], [1, 2]]

#guard
  match computeShiftedLdl 2 (matOf coupledH0) (1 / 2) with
  | some (G, pivs) => checkSpdGramCoercive 2 coupledH0 (1 / 2) G pivs
  | none => false

-- Positive vector 1: 3+1 Z4c 5-variable, 3D system accepted by `symmetricHyperbolicJudge`!
def sampleZ4cParams : Z4c3DParams :=
  { alpha := 1, betax := 1 / 5, betay := -(1 / 10), betaz := 1 / 20, kappa1 := 1 / 2, kappa2 := 0 }

example :
    symmetricHyperbolicJudge.check 0
      (z4c3dSymHypObj sampleZ4cParams 2 (1 / 10) 1) z4c3dSymHypCert = .ok :=
  (z4c3d_constraint_symmetric_hyperbolic sampleZ4cParams [4, 4, 4] (by simp)
    2 (1 / 10) 1 (1 / 16) (by decide +kernel) (fun _ _ => 0)).2.2.2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- Negative refutation vector 1: Indefinite off-diagonal symmetric `H_0 = [[1, 2], [2, 1]]`
-- (positive diagonal entries `1 > 0`, negative eigenvalue `-1` on `w = [-2, 1]`) -> `.h0NotPositiveDefinite`!
def indefiniteObj : SymHypObj where
  numDims := 1
  numVars := 2
  H0 := [[1, 2], [2, 1]]
  fluxMats := [[[1, 0], [0, 1]]]
  sourceMat := [[0, 0], [0, 0]]
  aMax := 2
  dt := 1 / 4
  dx := 1

example :
    symmetricHyperbolicJudge.check 0 indefiniteObj ⟨1 / 2, [[1, 0], [0, 1]], [0, 0]⟩ =
      .refused .h0NotPositiveDefinite [0] ∧
    symmetricHyperbolicJudge.refutes .h0NotPositiveDefinite = true := by
  decide +kernel

-- Kernel refutation theorem instantiated on `indefiniteObj`: NO certificate `c'` can ever certify it!
example (c' : SymHypCert) : ¬ CertifiedSymHyp indefiniteObj c' :=
  symmetricHyperbolicJudge.refuted (r := 0) (o := indefiniteObj)
    (c := ⟨1 / 2, [[1, 0], [0, 1]], [0, 0]⟩) (k := .h0NotPositiveDefinite) (p := [0])
    (by decide +kernel) (by decide +kernel) c'

-- Negative refutation vector 2: `H_0` is SPD (`I_2`), but `H_0 A_0 ≠ (H_0 A_0)^T` (`A_0 = [[0, 1], [2, 0]]`)!
def unsymmetrizedFluxObj : SymHypObj where
  numDims := 1
  numVars := 2
  H0 := [[1, 0], [0, 1]]
  fluxMats := [[[0, 1], [2, 0]]]
  sourceMat := [[0, 0], [0, 0]]
  aMax := 3
  dt := 1 / 4
  dx := 1

example :
    symmetricHyperbolicJudge.check 0 unsymmetrizedFluxObj ⟨1, [[1, 0], [0, 1]], [0, 0]⟩ =
      .refused .fluxNotSymmetrized [0, 0, 1] ∧
    symmetricHyperbolicJudge.refutes .fluxNotSymmetrized = true := by
  decide +kernel

example (c' : SymHypCert) : ¬ CertifiedSymHyp unsymmetrizedFluxObj c' :=
  symmetricHyperbolicJudge.refuted (r := 0) (o := unsymmetrizedFluxObj)
    (c := ⟨1, [[1, 0], [0, 1]], [0, 0]⟩) (k := .fluxNotSymmetrized) (p := [0, 0, 1])
    (by decide +kernel) (by decide +kernel) c'

-- Negative refutation vector 3: Asymmetric `H_0 ≠ H_0^T` -> `.h0NotSymmetric`!
def asymH0Obj : SymHypObj := { unsymmetrizedFluxObj with H0 := [[2, 1], [0, 2]] }

#guard
  symmetricHyperbolicJudge.check 0 asymH0Obj ⟨1, [[1, 0], [0, 1]], [0, 0]⟩ ==
    .refused .h0NotSymmetric [0, 1]

-- Negative refutation vector 4: CFL violation `dt * aMax > dx` -> `.shapeOrCflInvalid`!
#guard
  symmetricHyperbolicJudge.check 0 { z4c3dSymHypObj sampleZ4cParams 2 1 1 with dt := 1 }
    z4c3dSymHypCert == .refused .shapeOrCflInvalid []

-- Negative non-refuting vector 5: Valid object, wrong Gram certificate -> `.certGramMismatch` (`refutes = false`)!
#guard
  symmetricHyperbolicJudge.check 0 (z4c3dSymHypObj sampleZ4cParams 2 (1 / 10) 1)
    ⟨1, z4c3dGramRows, [0, 0, 0, 0, 0]⟩ == .refused .certGramMismatch [] &&
  symmetricHyperbolicJudge.refutes .certGramMismatch == false

-- Negative refutation vector 6: 3×3 symmetric matrix with ALL diagonal entries `> 0` and ALL 2×2 principal
-- minors `> 0` (`3, 1/5, 1/5 > 0`), but negative 3rd LDL pivot `d_2 = -1/15 < 0` -> caught by `scanPivot` + `backsolveUnitUpper`!
def indefinite3x3ScanPivotObj : SymHypObj where
  numDims := 1
  numVars := 3
  H0 := [[2, 1, 1], [1, 2, 1], [1, 1, 3 / 5]]
  fluxMats := [[[1, 0, 0], [0, 1, 0], [0, 0, 1]]]
  sourceMat := [[0, 0, 0], [0, 0, 0], [0, 0, 0]]
  aMax := 2
  dt := 1 / 4
  dx := 1

example (c' : SymHypCert) : ¬ CertifiedSymHyp indefinite3x3ScanPivotObj c' :=
  symmetricHyperbolicJudge.refuted (r := 0) (o := indefinite3x3ScanPivotObj)
    (c := ⟨1 / 10, [[1, 0, 0], [0, 1, 0], [0, 0, 1]], [0, 0, 0]⟩)
    (k := .h0NotPositiveDefinite) (p := [0])
    (by decide +kernel) (by decide +kernel) c'

-- Reflective `ConservationLawSpec` -> `SymmetricHyperbolicSystem` weld instantiated on `CurvedSpacetimeMaxwell`:
def maxwellH0 : List (List Rat) :=
  [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]

def maxwellSymHypSys : SymmetricHyperbolicSystem :=
  symmetricHyperbolicOfConservationLaw CurvedSpacetimeMaxwell.spec (by decide +kernel)
    maxwellH0 1 maxwellH0 [0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)
    (fun _ => 0) (by simp [DomainValid, CurvedSpacetimeMaxwell.spec]; decide +kernel)

#guard
  verifyConservationLawSymmetrizerReflective CurvedSpacetimeMaxwell.spec (liftConstSymMat maxwellH0) &&
  (maxwellSymHypSys.fluxMats 0 1 5 != 0)

/-! ## 2. 3+1 Z4c Light Cones, Damping vs Undamped ADM & `#pde_solver BssnZ4cConstraint3D` -/

-- Single-object 6-rung `EndToEndPdeCert` on `BssnZ4cConstraint3D.spec` + strict CSE FLOP savings!
example : EndToEndPdeCert BssnZ4cConstraint3D.spec := BssnZ4cConstraint3D.endToEnd_certified

#guard
  BssnZ4cConstraint3D.spec.numDims == 3 &&
  BssnZ4cConstraint3D.spec.numVars == 10 &&
  BssnZ4cConstraint3D.specializedPlan.specializedTotalFlops <
    BssnZ4cConstraint3D.specializedPlan.naiveTotalFlops

-- Exact weld between `BssnZ4cConstraint3D.spec`'s 5×5 constraint Jacobian block and `(z4c3dFluxMat, z4c3dSourceMat)`,
-- off-diagonal gauge-column decoupling on constraint-free backgrounds, conjugation, and semi-discrete dissipation:
example (u : Vec) (d i j : Nat) (hd : d < 3) (hi : i < 5) (hj : j < 5) :
    evalSymJacobianMat (getOr (specJacobians BssnZ4cConstraint3D.spec) d [])
      ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) (5 + j) =
      z4c3dFluxMat (bssnZ4c3dSolverParams (u 0)) d i j ∧
    evalSymJacobianMat (getOr (specJacobians BssnZ4cConstraint3D.spec) d [])
      ⟨fun k => if k < 5 then 1 else 0, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) j = 0 ∧
    toSymmetrizedZ4cState (mulVec 5 (z4c3dRawFluxMat sampleZ4cParams d) u) i =
      mulVec 5 (z4c3dFluxMat sampleZ4cParams d) (toSymmetrizedZ4cState u) i :=
  ⟨(bssnZ4cConstraint3D_constraint_sector_eq_z4c3d u d i j hd hi hj).1,
   ((bssnZ4cConstraint3D_constraint_sector_eq_z4c3d _ d i j hd hi hj).2.2
     (fun k _ => by simp)).1,
   (z4c3d_conformal_symmetrization_conjugates sampleZ4cParams d i hd hi u).1⟩

example (C : MultiDGrid) :
    2 * multiDH0Pair [2, 2, 2] 5 z4c3dSymmetrizer C (z4c3dSemiDiscreteRhs sampleZ4cParams [2, 2, 2] 1 C) ≤
      (-(2 * (sampleZ4cParams.kappa1 * sampleZ4cParams.alpha))) *
        multiDH0Energy [2, 2, 2] 5 z4c3dSymmetrizer C :=
  z4c3dSemiDiscreteRhs_energy_dissipative sampleZ4cParams [2, 2, 2] (by simp) 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) C

-- Pythagorean 3D oblique unit normal `n = (3/5, 4/5, 0)` (`(3/5)^2 + (4/5)^2 + 0^2 = 1`) light-cone check:
example :
    let n := ((3 / 5 : Rat), (4 / 5 : Rat), (0 : Rat))
    let betaN := n.1 * sampleZ4cParams.betax + n.2.1 * sampleZ4cParams.betay + n.2.2 * sampleZ4cParams.betaz
    ∀ i, i < 5 →
      mulVec 5 (z4c3dPrincipalSymbol sampleZ4cParams n.1 n.2.1 n.2.2)
        (z4cLightConePlus n.1 n.2.1 n.2.2) i =
      (-betaN + sampleZ4cParams.alpha) * z4cLightConePlus n.1 n.2.1 n.2.2 i :=
  (z4c3d_characteristic_eigenpairs sampleZ4cParams (3 / 5) (4 / 5) 0 (by decide +kernel)).1.2

-- Concrete oscillatory 3D constraint grid on `[2, 2, 2]`:
-- Kreiss–Oliger 4th-order energy rate is strictly negative (`< 0`), centered diff pairing is `= 0`,
-- `κ_1 = 1/2` Z4c rollout strictly damps 3D `H_Z4c`-energy, while `κ_1 = 0` ADM leaves static mode undamped!
def osc3dConstraintGrid : MultiDGrid := fun idx c =>
  if idx % 2 == 0 then (if c == 0 then 1 / 4 else if c == 1 then -(1 / 8) else 1 / 8)
  else (if c == 0 then -(1 / 8) else if c == 4 then 1 / 4 else 0)

def staticViolationVec : Vec
  | 0 => 1 / 4 | 1 => -(1 / 8) | 4 => 1 / 2 | _ => 0

-- Asymmetric 3-cell periodic profile on `[3, 2, 2]` (`nextCell ≠ prevCell` on axis 0):
-- pointwise flux-centered-difference pairing is non-zero, while total periodic pairing vanishes identically!
def skew3CellGrid : MultiDGrid := fun idx c =>
  match idx / 4 with
  | 0 => if c == 0 then 1 else if c == 1 then 1 / 4 else 0
  | 1 => if c == 0 then 1 / 3 else if c == 1 then -(1 / 2) else 1 / 8
  | _ => if c == 0 then -(1 / 5) else if c == 4 then 1 / 4 else 0

example :
    (let dims2 := [2, 2, 2]
     let dims3 := [3, 2, 2]
     let rhsSkew := applyGridMat 5 (z4c3dFluxMat sampleZ4cParams 0) (centeredDiffAxis dims3 0 1 skew3CellGrid)
     let localPair0 := h0Inner 5 z4c3dSymmetrizer (skew3CellGrid 0) (rhsSkew 0)
     let totalSkew := multiDH0Pair dims3 5 z4c3dSymmetrizer skew3CellGrid rhsSkew
     let koRate := -((1 / 16 : Rat) *
       multiDH0Pair dims2 5 z4c3dSymmetrizer osc3dConstraintGrid (kreissOliger4AxisOp dims2 2 osc3dConstraintGrid))
     let traceRes := runSymHypRolloutTrace (z4c3dConstraintSystem sampleZ4cParams) dims3 2 1
       ⟨skew3CellGrid, 0, 0⟩ [⟨1 / 10⟩, ⟨1 / 20⟩]
     let traceOk := match traceRes with
       | some stF => (stF.acceptedSteps == 2) && (stF.elapsedTime == 3 / 20) && (stF.grid 0 0 != skew3CellGrid 0 0)
       | none => false
     (localPair0 != 0) && (totalSkew == 0) && (koRate < 0) && traceOk) = true := by
  decide +kernel

example :
    let dims := [2, 2, 2]
    let energy := multiDH0Energy dims 5 z4c3dSymmetrizer
    let damped := z4c3dConstraintRollout sampleZ4cParams dims 2 1 (1 / 10) 4 osc3dConstraintGrid
    let uniform : MultiDGrid := fun _ => staticViolationVec
    let adm := z4c3dConstraintRollout { sampleZ4cParams with kappa1 := 0 } dims 2 1 (1 / 10) 4 uniform
    energy damped < energy osc3dConstraintGrid ∧ energy adm = energy uniform ∧ 0 < energy adm := by
  have h := z4c3d_total_constraint_energy_damped sampleZ4cParams [2, 2, 2] rfl (by simp)
    2 1 (1 / 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    4 osc3dConstraintGrid staticViolationVec
  exact ⟨h.2.1 (by decide) ⟨0, 0, by decide +kernel, by decide, by decide +kernel⟩,
    congrArg (multiDH0Energy [2, 2, 2] 5 z4c3dSymmetrizer) h.2.2.1,
    h.2.2.2 ⟨0, by decide, by decide +kernel⟩⟩

-- Concrete 1D -> 3D planar slab reduction check on `[4, 2, 2]` with spatially varying `Theta`!
def sample1DSlabGrid : MultiDGrid := fun ix c =>
  match c with
  | 0 => 1 + (if ix % 2 == 0 then 1 / 8 else -(1 / 8))
  | 1 => 2
  | 2 => if ix == 0 then 1 / 10 else -(1 / 10)
  | 3 => 1 / 5
  | 4 => -(1 / 8)
  | 5 => if ix % 2 == 0 then 1 / 8 else -(1 / 16)
  | _ => 0

example (ix iy iz c : Nat) (hix : ix < 4) (hiy : iy < 2) (hiz : iz < 2) (hc : c < 6) :
    BssnZ4cConstraint3D.schemeStepRat .periodic [4, 2, 2] (1 / 10) false
      (embedZ4cPlanarSlab 2 2 sample1DSlabGrid) (ix * 4 + (iy * 2 + iz)) c =
    BonaMassoZ4c1D.schemeStepRat .periodic [4] (1 / 10) false sample1DSlabGrid ix c :=
  (z4c3d_slab_reduction_matches_1d 4 2 2 (by decide) (by decide) (by decide)
    (1 / 10) sample1DSlabGrid (fun _ => 1) ix iy iz c hix hiy hiz).2.1 hc

-- Multi-step (`∀ n : Nat`) planar slab rollout invariance on a non-uniform 1D Bona–Massó gauge wave (`Theta = 0`):
def sample1DBonaMassoWave : MultiDGrid := fun ix c =>
  if c == 5 then 0 else sample1DSlabGrid ix c

example (n ix iy iz c : Nat) (hix : ix < 4) (hiy : iy < 2) (hiz : iz < 2) :
    pdeGridRollout (BssnZ4cConstraint3D.schemeStepRat .periodic [4, 2, 2] (1 / 10) false) n
      (embedZ4cPlanarSlab 2 2 sample1DBonaMassoWave) (ix * 4 + (iy * 2 + iz)) c =
    embedZ4cVec1DTo3D
      (pdeGridRollout (BonaMassoZ4c1D.schemeStepRat .periodic [4] (1 / 10) false) n sample1DBonaMassoWave ix) c :=
  (z4c3d_slab_reduction_matches_1d 4 2 2 (by decide) (by decide) (by decide)
    (1 / 10) sample1DBonaMassoWave (fun _ => 1) ix iy iz c hix hiy hiz).2.2
    (fun _ _ => by simp [sample1DBonaMassoWave]) n

/-! ## 3. Universal `#tooth` Kernel Mutation Kills (`14 ≥ 8` Universal Theorems) -/

def alwaysSpd (_ : Nat) (_ : List (List Rat)) (_ : Rat)
    (_ : List (List Rat)) (_ : List Rat) : Bool := true

def forwardSkewDiff (dims : List Nat) (d : Nat) (_ : Rat) (U : MultiDGrid) : MultiDGrid :=
  forwardDiffAxis dims d U

def signFlippedKo4 (dims : List Nat) (d : Nat) (U : MultiDGrid) : MultiDGrid :=
  let second := secondDiffAxis dims d U
  fun idx c => -(secondDiffAxis dims d second idx c)

def antiViscousRusanov (dims : List Nat) (m : Nat) (A : Mat) (a ν : Rat) (d : Nat)
    (U : MultiDGrid) : MultiDGrid :=
  if ν == 0 then U
  else if d < dims.length then
    fun idx c =>
      let uNext := U (axisPeriodicNeighbor dims d true idx)
      let uPrev := U (axisPeriodicNeighbor dims d false idx)
      U idx c - (ν / 2) * mulVec m A (fun j => uNext j - uPrev j) c -
        (ν * a / 2) * (uNext c - 2 * U idx c + uPrev c)
  else U

-- A two-cell jump diffuses to its mean. Reversing viscosity doubles its amplitude.
example :
    (let U : MultiDGrid := fun idx _ => if idx == 0 then 0 else 1
     let A : Mat := fun _ _ => 0
     let step := rusanovSymmetricAxisStep [2] 1 A 1 (1 / 2) 0 U
     let mutant := antiViscousRusanov [2] 1 A 1 (1 / 2) 0 U
     step 0 0 == 1 / 2 && step 1 0 == 1 / 2 && mutant 0 0 == -(1 / 2) && mutant 1 0 == 3 / 2) = true := by
  decide +kernel

def frozenRollout (_ : SymmetricHyperbolicSystem) (_ : List Nat)
    (_ _ _ : Rat) (_ : Nat) (U : MultiDGrid) : MultiDGrid := U

def rubberStampSymHyp (_ : SymHypObj) (_ : SymHypCert) : Obend.Judge.Verdict SymHypClause := .ok

def overRefutingSymHyp (_ : SymHypClause) : Bool := true

def brokenZ4cSymmetrizerRows : List (List Rat) :=
  [[1, 0, 0, 0, 0], [0, 8, 0, 0, 0], [0, 0, 8, 0, 0], [0, 0, 0, 8, 0], [0, 0, 0, 0, 1]]

def idZ4cPerm (_ i : Nat) : Nat := i

def badEmbedZ4cVec (u : Vec) : Vec := fun c => if c < 6 then u c else 1

def frozenZ4cRollout (_ : Z4c3DParams) (_ : List Nat) (_ _ _ : Rat) (_ : Nat) (U : MultiDGrid) : MultiDGrid := U

def antiDampedRhs (_ : Z4c3DParams) (_ : List Nat) (_ : Rat) (C : MultiDGrid) : MultiDGrid := C

def badBssnSolverParams (alpha : Rat) : Z4c3DParams :=
  { alpha := alpha, betax := 0, betay := 0, betaz := 0, kappa1 := 0, kappa2 := 0 }

#tooth checkSpdGramCoercive_sound by mutation checkSpdGramCoercive := alwaysSpd
#tooth centeredDiff_h0_skew_adjoint by mutation centeredDiffAxis := forwardSkewDiff
#tooth kreissOliger4_energy_nonpositive by mutation kreissOliger4AxisOp := signFlippedKo4
#tooth rusanov_symmetric_energy_dissipative by mutation rusanovSymmetricAxisStep := antiViscousRusanov
#tooth symmetricHyperbolic_gronwall_stability by mutation symHypRollout := frozenRollout
#tooth checkSymHyp_sound by mutation checkSymHyp := rubberStampSymHyp
#tooth checkSymHyp_refuted by mutation symHypRefutes := overRefutingSymHyp
#tooth z4c3d_constraint_symmetric_hyperbolic by mutation z4c3dSymmetrizerRows := brokenZ4cSymmetrizerRows
#tooth z4c3d_characteristic_eigenpairs by mutation z4cLightConePlus := z4cLightConeMinus
#tooth z4c3d_cyclic_axis_equivariant by mutation z4cVarPerm := idZ4cPerm
#tooth z4c3dSemiDiscreteRhs_energy_dissipative by mutation z4c3dSemiDiscreteRhs := antiDampedRhs
#tooth z4c3d_total_constraint_energy_damped by mutation z4c3dConstraintRollout := frozenZ4cRollout
#tooth bssnZ4cConstraint3D_constraint_sector_eq_z4c3d by mutation bssnZ4c3dSolverParams := badBssnSolverParams
#tooth z4c3d_slab_reduction_matches_1d by mutation embedZ4cVec1DTo3D := badEmbedZ4cVec

/-! ## 3b. Spatially Varying `(α(x), β^i(x))` Commutator & Open-Box SBP+SAT Boundary Tests -/

-- Spatially inhomogeneous 3D parameter field on `[3, 2, 2]` (`α(x) ∈ {3/4, 1, 5/4}`, `β^x(x) ∈ {0, 1/8, 1/4}`).
def inhomogeneousGaugeField (idx : Nat) : Z4c3DParams :=
  let ix := (idx / 4) % 3
  let iy := ((idx % 4) / 2) % 2
  { alpha := if ix == 0 then 3 / 4 else if ix == 1 then 1 else 5 / 4
  , betax := if ix == 0 then 0 else if ix == 1 then 1 / 8 else 1 / 4
  , betay := if iy == 0 then 0 else 1 / 16
  , betaz := -(1 / 20)
  , kappa1 := 1 / 2
  , kappa2 := 0 }

theorem inhomogeneousGaugeField_valid : VariableGaugeField3D [3, 2, 2] 1 (3 / 4) 2 (1 / 2) inhomogeneousGaugeField := by
  refine {
    alphaMin_pos := by grind
    lGauge_nonneg := by grind
    lapse_lower := fun idx hidx => ?_
    speed_bound := fun idx d hidx hd => ?_
    grad_alpha_lip := fun d idx hd hidx => ?_
    grad_shift_lip := fun d idx hd hidx => ?_
  }
  · have hi : idx < 12 := by simpa [gridCellCount] using hidx
    rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have hi : idx < 12 := by simpa [gridCellCount] using hidx
    have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd3 with rfl | rfl | rfl <;>
      rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have hi : idx < 12 := by simpa [gridCellCount] using hidx
    have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd3 with rfl | rfl | rfl <;>
      rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have hi : idx < 12 := by simpa [gridCellCount] using hidx
    have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd3 with rfl | rfl | rfl <;>
      rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

example (U0 : MultiDGrid) :
    ratAbs (sumTo 3 fun d => multiDH0Pair [3, 2, 2] 5 z4c3dSymmetrizer U0
      (fun idx => mulVec 5 (z4c3dFluxMat (inhomogeneousGaugeField idx) d) (centeredDiffAxis [3, 2, 2] d 1 U0 idx))) ≤
      (3 * (1 / 2 : Rat)) * multiDH0Energy [3, 2, 2] 5 z4c3dSymmetrizer U0 ∧
    multiDH0Energy [3, 2, 2] 5 z4c3dSymmetrizer (z4c3dVarGaugeRollout inhomogeneousGaugeField [3, 2, 2] 2 1 (1 / 8) 3 U0) ≤
      ((((1 + 2 * (1 / 2 : Rat) * (1 / 8)) ^ 3) * (1 - (1 / 2 : Rat) * (3 / 4) * (1 / 8))) ^ 3) *
        multiDH0Energy [3, 2, 2] 5 z4c3dSymmetrizer U0 := by
  have hDamp : ∀ idx, idx < gridCellCount [3, 2, 2] →
      1 / 2 ≤ (inhomogeneousGaugeField idx).kappa1 ∧ -1 ≤ (inhomogeneousGaugeField idx).kappa2 ∧ z4c3dMaxDampRate (inhomogeneousGaugeField idx) ≤ 5 / 4 := by
    intro idx hidx; have hi : idx < 12 := by simpa [gridCellCount] using hidx
    rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hMain := z4c3d_variable_gauge_commutator_energy_bound [3, 2, 2] rfl (by simp)
    1 (1 / 8) (3 / 4) 2 (1 / 2) (1 / 2) (5 / 4) (by grind) (by grind) (by grind)
    inhomogeneousGaugeField inhomogeneousGaugeField_valid (by grind) hDamp (by grind) (by grind) 3 U0 U0
  exact ⟨hMain.1, hMain.2.2⟩

-- Open-box `[3, 3, 3]` Olsson–Strand SBP+SAT radiative boundary test:
-- 1. Unconditional `≤ 0` open-box energy dissipation for **arbitrary** `U : MultiDGrid` (even with incoming boundary modes!),
-- 2. Strict `< 0` (`= -16`) energy radiation on outgoing `+α` light-cone pulse `(1, 1, 0, 0, 2)` at `(2, 1, 1)` (`idx = 22`) with `κ_1 = 0`,
-- 3. Vanishing SAT penalty whenever `SommerfeldNoIncoming3D` holds!
def undampedOpenBoxParams : Z4c3DParams :=
  { alpha := 1, betax := 0, betay := 0, betaz := 0, kappa1 := 0, kappa2 := 0 }

def outgoingLightConeGrid : MultiDGrid :=
  fun idx => if idx == 22 then z4cLightConePlus 1 0 0 else fun _ => 0

example (Uany : MultiDGrid) :
    -- Unconditional for EVERY `Uany : MultiDGrid` (including incoming waves!):
    2 * openBoxH0Pair 3 3 3 Uany (z4c3dOpenBoxRhs undampedOpenBoxParams 3 3 3 1 Uany) ≤ 0 ∧
    -- Concrete outgoing light-cone pulse at `(2, 1, 1)` strictly radiates energy `< 0` (`= -16`):
    SommerfeldNoIncoming3D undampedOpenBoxParams 3 3 3 outgoingLightConeGrid ∧
    2 * openBoxH0Pair 3 3 3 outgoingLightConeGrid
      (openBoxSbpSatAxis3D undampedOpenBoxParams 3 3 3 0 1 outgoingLightConeGrid) < 0 ∧
    2 * openBoxH0Pair 3 3 3 outgoingLightConeGrid
      (z4c3dOpenBoxRhs undampedOpenBoxParams 3 3 3 1 outgoingLightConeGrid) = -16 := by
  have hAny := (z4c3d_sommerfeld_boundary_dissipative undampedOpenBoxParams 3 3 3
    (by decide) (by decide) (by decide) 1 (by grind) Uany).2.2.2.1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hAny0 : 2 * openBoxH0Pair 3 3 3 Uany (z4c3dOpenBoxRhs undampedOpenBoxParams 3 3 3 1 Uany) ≤ 0 := by
    have : -(2 * (undampedOpenBoxParams.kappa1 * undampedOpenBoxParams.alpha)) = 0 := by decide +kernel
    rw [this, Rat.zero_mul] at hAny; exact hAny
  have hZeroAmp : ∀ d m, z4cCharAmplitudes d (fun _ => 0) m = 0 :=
    fun _ _ => by unfold z4cCharAmplitudes mulVec; simp [sumTo, Rat.zero_add, Rat.mul_zero]
  have hSomm : SommerfeldNoIncoming3D undampedOpenBoxParams 3 3 3 outgoingLightConeGrid := by
    intro ix iy iz hix hiy hiz
    by_cases h22 : ix * 9 + (iy * 3 + iz) = 22
    · have hx2 : ix = 2 := by omega
      have hy1 : iy = 1 := by omega
      have hz1 : iz = 1 := by omega
      subst hx2 hy1 hz1
      refine ⟨fun h => by omega, fun _ m hm hNeg => ?_, fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩
      have hm5 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
      rcases hm5 with rfl | rfl | rfl | rfl | rfl <;>
        (first | decide +kernel | (exfalso; revert hNeg; decide +kernel))
    · have hCellZero : outgoingLightConeGrid (ix * (3 * 3) + (iy * 3 + iz)) = (fun _ => 0) := by
        unfold outgoingLightConeGrid; simp [show (ix * 9 + (iy * 3 + iz) == 22) = false by simp [beq_eq_false_iff_ne, h22]]
      dsimp only; rw [hCellZero]
      exact ⟨fun _ m _ _ => hZeroAmp 0 m, fun _ m _ _ => hZeroAmp 0 m, fun _ m _ _ => hZeroAmp 1 m,
             fun _ m _ _ => hZeroAmp 1 m, fun _ m _ _ => hZeroAmp 2 m, fun _ m _ _ => hZeroAmp 2 m⟩
  have hStrict := (z4c3d_sommerfeld_boundary_dissipative undampedOpenBoxParams 3 3 3
    (by decide) (by decide) (by decide) 1 (by grind) outgoingLightConeGrid).2.2.2.2.1
    (by decide +kernel) ⟨1, 1, by decide, by decide, by decide +kernel⟩
  exact ⟨hAny0, hSomm, hStrict, by decide +kernel⟩

def antiDampedVarGaugeRhs (gField : Nat → Z4c3DParams) (dims : List Nat) (dx : Rat) (C : MultiDGrid) : MultiDGrid :=
  fun idx c => -mulVec 5 (z4c3dSourceMat (gField idx)) (C idx) c +
    sumTo 3 fun d => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx C idx) c

#tooth z4c3d_variable_gauge_commutator_energy_bound by mutation z4c3dVarGaugeSemiDiscreteRhs := antiDampedVarGaugeRhs
#tooth z4c3d_variable_gauge_commutator_energy_bound by mutation z4c3dVarGaugeRollout := fun _ _ _ _ _ _ U0 => fun idx c => 2 * U0 idx c
#tooth z4c3d_sommerfeld_boundary_dissipative by mutation z4cCharAmplitudes := fun _ _ _ => (0 : Rat)
#tooth z4c3d_sommerfeld_boundary_dissipative by mutation sbpSatPenalty1D := fun _ _ _ _ _ _ _ => (1 : Rat)
#tooth z4c3d_sommerfeld_boundary_dissipative by mutation sbpDiff1D := fun _ _ _ _ => (0 : Rat)

/-! ## 4. Kernel Axiom, Zero-Closed-Theorem & `0 Classical.choice` Computational Audit -/

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
      match info.value? with
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
  let ownModules := [`Obend.Analysis.SymmetricHyperbolicEnergy, `Obend.Analysis.RelativityBssnZ4c3D]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.contains ``sorryAx then
      throwError "sorryAx dependency in {name}"
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    -- The solver command emits one closed certificate for this concrete spec.
    if name == ``BssnZ4cConstraint3D.endToEnd_certified then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
    if info matches .defnInfo _ then
      if (← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)).contains ``Classical.choice then
        Lean.Elab.Command.liftTermElabM do
          match info.value? with
          | some body =>
              let _ ← (auditComputationalChoice body).run {}
              pure ()
          | none => pure ()
  for name in [
      ``checkSpdGramCoercive,
      ``computeShiftedLdl,
      ``findIndefiniteWitness,
      ``checkSymHyp,
      ``symHypRollout,
      ``z4c3dSymHypObj,
      ``z4c3dConstraintRollout,
      ``z4c3dVarGaugeRollout,
      ``z4c3dOpenBoxRhs,
      ``embedZ4cPlanarSlab,
      ``BssnZ4cConstraint3D.spec,
      ``BssnZ4cConstraint3D.specializedPlan,
      ``BssnZ4cConstraint3D.balanceSystolicRtl
    ] do
    Lean.Elab.Command.liftTermElabM do
      let _ ← (auditComputationalChoice (Lean.mkConst name)).run {}
      pure ()
  Lean.logInfo "SymmetricHyperbolicEnergy + RelativityBssnZ4c3D audit passed: 0 compiler-trust axioms, 0 sorryAx, 0 closed application theorems (generated solver certificate excluded), 0 computational choice in audited entry points."

#assert_axioms_tree

end Obend.Tests.RelativityBssnZ4c3DTest
