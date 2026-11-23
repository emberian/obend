module
public import Obend.Analysis.SymmetricHyperbolicEnergy
public import Obend.Analysis.HyperbolicBalanceLaws
public import Obend.Hardware.BalanceLawLowering
public import Obend.Analysis.NonlinearErrorTube
public import Obend.Hardware.MultiDStencilTile
public import Obend.Hardware.MultiDStencilCorrect
public import Obend.Hardware.PdeSolvers
meta import Obend.Elab.PdeSolverElab
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Analysis.NonlinearErrorTube
import all Obend.Analysis.SymmetricHyperbolicEnergy
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.MultiDStencilCorrect
import all Obend.Hardware.BalanceLawLowering
import all Obend.Hardware.PdeSolvers
import all Obend.Tactic.SymDiffAndFlux

/-! # 5-Variable 3D Variable-Coefficient Symmetric-Hyperbolic PDE Constraint Model & Olsson–Strand SAT Boundaries (`Obend.Analysis.RelativityBssnZ4c3D`) -/

public section
namespace Obend.Analysis.RelativityBssnZ4c3D

open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws Obend.Analysis.NonlinearErrorTube Obend.Analysis.SymmetricHyperbolicEnergy
open Obend.Hardware.HDL Obend.Hardware.Gpu.StencilTile Obend.Hardware.MultiDStencilTile
open Obend.Hardware.MultiDStencilCorrect Obend.Hardware.BalanceLawLowering Obend.Hardware.PdeSolvers Obend.Tactic.SymDiffAndFlux

set_option autoImplicit false

/-! ## 1. 5-Variable 3D Linear Constraint-Subsystem PDE Carriers (`diag(4, 8, 8, 8, 1)` Symmetrizer) -/
structure Z4c3DParams where
  (alpha : Rat) (betax : Rat) (betay : Rat) (betaz : Rat) (kappa1 : Rat) (kappa2 : Rat := 0)
  deriving DecidableEq, Repr
def Z4c3DParams.shiftAxis (p : Z4c3DParams) : Nat → Rat | 0 => p.betax | 1 => p.betay | 2 => p.betaz | _ => 0
def toSymmetrizedZ4cState (raw : Vec) : Vec | 0 => 2 * raw 0 | 1 => raw 1 | 2 => raw 2 | 3 => raw 3 | 4 => -2 * raw 4 | c => raw c
def fromSymmetrizedZ4cState (sym : Vec) : Vec | 0 => (1 / 2 : Rat) * sym 0 | 1 => sym 1 | 2 => sym 2 | 3 => sym 3 | 4 => -(1 / 2 : Rat) * sym 4 | c => sym c
theorem symmetrizedZ4cState_roundtrip (v : Vec) (c : Nat) :
    fromSymmetrizedZ4cState (toSymmetrizedZ4cState v) c = v c ∧ toSymmetrizedZ4cState (fromSymmetrizedZ4cState v) c = v c := by
  rcases c with _ | _ | _ | _ | _ | k <;> simp [fromSymmetrizedZ4cState, toSymmetrizedZ4cState] <;> grind
@[expose] def z4c3dSymmetrizerRows : List (List Rat) := [[4, 0, 0, 0, 0], [0, 8, 0, 0, 0], [0, 0, 8, 0, 0], [0, 0, 0, 8, 0], [0, 0, 0, 0, 1]]
@[expose] def z4c3dSymmetrizer : Mat := matOf z4c3dSymmetrizerRows
def z4c3dGramRows : List (List Rat) := [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]
def z4c3dPivots : List Rat := [3, 7, 7, 7, 0]
def z4c3dFluxRows (p : Z4c3DParams) : Nat → List (List Rat)
  | 0 => let b := -p.betax; let a := p.alpha; [[b, a, 0, 0, 0], [(1 / 2 : Rat) * a, b, 0, 0, (1 / 4 : Rat) * a], [0, 0, b, 0, 0], [0, 0, 0, b, 0], [0, 2 * a, 0, 0, b]]
  | 1 => let b := -p.betay; let a := p.alpha; [[b, 0, a, 0, 0], [0, b, 0, 0, 0], [(1 / 2 : Rat) * a, 0, b, 0, (1 / 4 : Rat) * a], [0, 0, 0, b, 0], [0, 0, 2 * a, 0, b]]
  | 2 => let b := -p.betaz; let a := p.alpha; [[b, 0, 0, a, 0], [0, b, 0, 0, 0], [0, 0, b, 0, 0], [(1 / 2 : Rat) * a, 0, 0, b, (1 / 4 : Rat) * a], [0, 0, 0, 2 * a, b]]
  | _ => List.replicate 5 (List.replicate 5 0)
def z4c3dFluxMat (p : Z4c3DParams) (d : Nat) : Mat := matOf (z4c3dFluxRows p d)
def z4c3dSourceRows (p : Z4c3DParams) : List (List Rat) :=
  let dTheta := -(p.kappa1 * (2 + p.kappa2) * p.alpha); let dZ := -(p.kappa1 * p.alpha); let dH := -(2 * p.kappa1 * p.alpha)
  [[dTheta, 0, 0, 0, 0], [0, dZ, 0, 0, 0], [0, 0, dZ, 0, 0], [0, 0, 0, dZ, 0], [0, 0, 0, 0, dH]]
def z4c3dSourceMat (p : Z4c3DParams) : Mat := matOf (z4c3dSourceRows p)
def z4c3dRawFluxRows (p : Z4c3DParams) : Nat → List (List Rat)
  | 0 => let b := -p.betax; let a := p.alpha; [[b, (1 / 2 : Rat) * a, 0, 0, 0], [a, b, 0, 0, -(1 / 2 : Rat) * a], [0, 0, b, 0, 0], [0, 0, 0, b, 0], [0, -a, 0, 0, b]]
  | 1 => let b := -p.betay; let a := p.alpha; [[b, 0, (1 / 2 : Rat) * a, 0, 0], [0, b, 0, 0, 0], [a, 0, b, 0, -(1 / 2 : Rat) * a], [0, 0, 0, b, 0], [0, 0, -a, 0, b]]
  | 2 => let b := -p.betaz; let a := p.alpha; [[b, 0, 0, (1 / 2 : Rat) * a, 0], [0, b, 0, 0, 0], [0, 0, b, 0, 0], [a, 0, 0, b, -(1 / 2 : Rat) * a], [0, 0, 0, -a, b]]
  | _ => List.replicate 5 (List.replicate 5 0)
def z4c3dRawFluxMat (p : Z4c3DParams) (d : Nat) : Mat := matOf (z4c3dRawFluxRows p d)
theorem z4c3d_conformal_symmetrization_conjugates (p : Z4c3DParams) (d c : Nat) (hd : d < 3) (hc : c < 5) (v : Vec) :
    toSymmetrizedZ4cState (mulVec 5 (z4c3dRawFluxMat p d) v) c = mulVec 5 (z4c3dFluxMat p d) (toSymmetrizedZ4cState v) c ∧
    toSymmetrizedZ4cState (mulVec 5 (z4c3dSourceMat p) v) c = mulVec 5 (z4c3dSourceMat p) (toSymmetrizedZ4cState v) c := by
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := (by omega); have hc5 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := (by omega)
  rcases hd3 with rfl | rfl | rfl <;> rcases hc5 with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [toSymmetrizedZ4cState, mulVec, z4c3dRawFluxMat, z4c3dRawFluxRows, z4c3dFluxMat, z4c3dFluxRows, z4c3dSourceMat, z4c3dSourceRows, matOf, getOr, sumTo]; constructor <;> grind)
@[expose] def z4c3dSemiDiscreteRhs (p : Z4c3DParams) (dims : List Nat) (dx : Rat) (C : MultiDGrid) : MultiDGrid :=
  fun idx c => mulVec 5 (z4c3dSourceMat p) (C idx) c - sumTo 3 fun d => mulVec 5 (z4c3dFluxMat p d) (centeredDiffAxis dims d dx C idx) c
/-! ## 2. Constant-Coefficient Friedrichs Symmetric Hyperbolicity (`z4c3d_constraint_symmetric_hyperbolic`) -/

private theorem z4c3d_flux_symm_entry (p : Z4c3DParams) (d i j : Nat) (hd : d < 3) (hi : i < 5) (hj : j < 5) :
    matMul 5 z4c3dSymmetrizer (z4c3dFluxMat p d) i j = matMul 5 z4c3dSymmetrizer (z4c3dFluxMat p d) j i := by
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := (by omega); have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := (by omega); have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := (by omega)
  rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [matMul, z4c3dSymmetrizer, z4c3dSymmetrizerRows, z4c3dFluxMat, z4c3dFluxRows, matOf, getOr, sumTo] <;> grind)

def z4c3dConstraintSystem (p : Z4c3DParams) : SymmetricHyperbolicSystem :=
  let spd := checkSpdGramCoercive_sound 5 z4c3dSymmetrizerRows 1 z4c3dGramRows z4c3dPivots (by decide +kernel)
  { numDims := 3, numVars := 5, H0 := z4c3dSymmetrizer, fluxMats := z4c3dFluxMat p,
    sourceMat := z4c3dSourceMat p, mu := 1, hDimsPos := by decide, hVarsPos := spd.1,
    hMuPos := spd.2.1, hH0Symm := spd.2.2.1, hH0Coercive := spd.2.2.2.2.1, hFluxSymm := z4c3d_flux_symm_entry p }

def z4c3dSymHypObj (p : Z4c3DParams) (aMax dt dx : Rat) : SymHypObj :=
  { numDims := 3, numVars := 5, H0 := z4c3dSymmetrizerRows, fluxMats := [z4c3dFluxRows p 0, z4c3dFluxRows p 1, z4c3dFluxRows p 2],
    sourceMat := z4c3dSourceRows p, aMax := aMax, dt := dt, dx := dx }
def z4c3dSymHypCert : SymHypCert := { mu := 1, gramFactor := z4c3dGramRows, pivots := z4c3dPivots }

theorem z4c3dSymmetrizer_quadratic_form (v : Vec) :
    h0Inner 5 z4c3dSymmetrizer v v = 4 * (v 0 * v 0) + 8 * (v 1 * v 1) + 8 * (v 2 * v 2) + 8 * (v 3 * v 3) + (v 4 * v 4) := by
  simp only [h0Inner, dot, mulVec, z4c3dSymmetrizer, z4c3dSymmetrizerRows, matOf, getOr, sumTo]; grind

theorem z4c3d_constraint_symmetric_hyperbolic (p : Z4c3DParams) (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (aMax dt dx sigmaKO : Rat) (hSigma : 0 ≤ sigmaKO) (U : MultiDGrid) :
    (∀ v : Vec, dot 5 v v ≤ h0Inner 5 z4c3dSymmetrizer v v) ∧
    (∀ d i j, d < 3 → i < 5 → j < 5 → matMul 5 z4c3dSymmetrizer (z4c3dFluxMat p d) i j = matMul 5 z4c3dSymmetrizer (z4c3dFluxMat p d) j i) ∧
    (∀ d, d < 3 → multiDH0Pair dims 5 z4c3dSymmetrizer U (applyGridMat 5 (z4c3dFluxMat p d) (centeredDiffAxis dims d dx U)) = 0 ∧
      -(sigmaKO * multiDH0Pair dims 5 z4c3dSymmetrizer U (kreissOliger4AxisOp dims d U)) ≤ 0) ∧
    (0 < aMax → 0 ≤ dt → 0 < dx → dt * aMax ≤ dx → symmetricHyperbolicJudge.check 0 (z4c3dSymHypObj p aMax dt dx) z4c3dSymHypCert = .ok) := by
  let sys := z4c3dConstraintSystem p
  refine ⟨fun v => by simpa only [sys, z4c3dConstraintSystem, Rat.one_mul] using sys.hH0Coercive v, z4c3d_flux_symm_entry p,
          fun d hd => ⟨centeredDiff_h0_skew_adjoint sys dims hPos d hd dx U, (kreissOliger4_energy_nonpositive sys dims hPos d sigmaKO hSigma U).2.2⟩,
          fun haMax hdt hdx hcfl => ?_⟩
  have hCert : CertifiedSymHyp (z4c3dSymHypObj p aMax dt dx) z4c3dSymHypCert := by
    have hSpdRaw : checkSpdGramCoercive 5 z4c3dSymmetrizerRows 1 z4c3dGramRows z4c3dPivots = true := by decide +kernel
    have spd := checkSpdGramCoercive_sound 5 z4c3dSymmetrizerRows 1 z4c3dGramRows z4c3dPivots hSpdRaw
    unfold checkSpdGramCoercive at hSpdRaw; simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hSpdRaw
    refine { wf := ?_, muPos := by decide, pivotsNonneg := hSpdRaw.1.2, gramDecomp := fun i j hi hj => hSpdRaw.2 i hi j hj,
             h0Symm := spd.2.2.1, coercive := spd.2.2.2.2.1, fluxSymm := ?_ }
    · dsimp only [z4c3dSymHypObj, SymHypObj.WellFormed]
      refine ⟨by decide, by decide, rfl, rfl, fun d hd => ?_, rfl, haMax, hdt, hdx, hcfl⟩
      have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
      rcases hd3 with rfl | rfl | rfl <;> rfl
    · intro d i j hd hi hj; change d < 3 at hd; have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
      rcases hd3 with rfl | rfl | rfl
      · exact z4c3d_flux_symm_entry p 0 i j (by decide) hi hj
      · exact z4c3d_flux_symm_entry p 1 i j (by decide) hi hj
      · exact z4c3d_flux_symm_entry p 2 i j (by decide) hi hj
  have hComp := checkSymHyp_complete hCert
  have hCanEq : canonicalSymHypCert 5 z4c3dSymHypCert = z4c3dSymHypCert := by decide +kernel
  change checkSymHyp _ (canonicalSymHypCert 5 z4c3dSymHypCert) = .ok at hComp
  rw [hCanEq] at hComp; exact hComp
/-! ## 3. Principal-Symbol Characteristic Eigenpairs `{−β_n, −β_n ± α}` (`z4c3d_characteristic_eigenpairs`) -/
def z4c3dPrincipalSymbol (p : Z4c3DParams) (nx ny nz : Rat) : Mat :=
  fun i j => nx * z4c3dFluxMat p 0 i j + ny * z4c3dFluxMat p 1 i j + nz * z4c3dFluxMat p 2 i j
@[expose] def z4cLightConePlus (nx ny nz : Rat) : Vec | 0 => 1 | 1 => nx | 2 => ny | 3 => nz | 4 => 2 | _ => 0
def z4cLightConeMinus (nx ny nz : Rat) : Vec | 0 => 1 | 1 => -nx | 2 => -ny | 3 => -nz | 4 => 2 | _ => 0
def z4cLongitudinalAdvected : Vec | 0 => 1 | 4 => -2 | _ => 0
def z4cTransverseAdvected (wx wy wz : Rat) : Vec | 1 => wx | 2 => wy | 3 => wz | _ => 0
def z4c3dEigVecRows : Nat → List (List Rat)
  | 0 => [[1, 1, 1, 0, 0], [1, -1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [2, 2, -2, 0, 0]]
  | 1 => [[1, 1, 1, 0, 0], [0, 0, 0, 1, 0], [1, -1, 0, 0, 0], [0, 0, 0, 0, 1], [2, 2, -2, 0, 0]]
  | 2 => [[1, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [1, -1, 0, 0, 0], [2, 2, -2, 0, 0]]
  | _ => z4c3dGramRows
def z4c3dEigInvRows : Nat → List (List Rat)
  | 0 => [[1 / 4, 1 / 2, 0, 0, 1 / 8], [1 / 4, -(1 / 2), 0, 0, 1 / 8], [1 / 2, 0, 0, 0, -(1 / 4)], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0]]
  | 1 => [[1 / 4, 0, 1 / 2, 0, 1 / 8], [1 / 4, 0, -(1 / 2), 0, 1 / 8], [1 / 2, 0, 0, 0, -(1 / 4)], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0]]
  | 2 => [[1 / 4, 0, 0, 1 / 2, 1 / 8], [1 / 4, 0, 0, -(1 / 2), 1 / 8], [1 / 2, 0, 0, 0, -(1 / 4)], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]]
  | _ => z4c3dGramRows
def z4c3dEigVecMat (d : Nat) : Mat := matOf (z4c3dEigVecRows d)
def z4c3dEigInvMat (d : Nat) : Mat := matOf (z4c3dEigInvRows d)
def z4c3dEigVals (p : Z4c3DParams) (d : Nat) : Vec := let b := -(p.shiftAxis d); vecOf [b + p.alpha, b - p.alpha, b, b, b]
def z4c3dCharWeights : Vec := vecOf [16, 16, 8, 8, 8]
theorem z4c3d_axis_isEigenSystem (p : Z4c3DParams) (d : Nat) (hd : d < 3) :
    IsEigenSystem 5 (z4c3dFluxMat p d) (z4c3dEigVecMat d) (z4c3dEigInvMat d) (z4c3dEigVals p d) ∧
    (∀ i j, i < 5 → j < 5 → gram 5 z4c3dCharWeights (z4c3dEigInvMat d) i j = z4c3dSymmetrizer i j) := by
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  refine ⟨⟨fun i k hi hk => ?_, fun i j hi hj => ?_, fun i j hi hj => ?_⟩, fun i j hi hj => ?_⟩
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := (by omega); have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := (by omega)
    rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hk5 with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [z4c3dFluxMat, z4c3dFluxRows, z4c3dEigVecMat, z4c3dEigVecRows, z4c3dEigVals, Z4c3DParams.shiftAxis, matOf, vecOf, getOr, sumTo]; grind)
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := (by omega); have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := (by omega)
    rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := (by omega); have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := (by omega)
    rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := (by omega); have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := (by omega)
    rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem z4c3d_characteristic_eigenpairs (p : Z4c3DParams) (nx ny nz : Rat) (hUnit : nx * nx + ny * ny + nz * nz = 1) :
    let betaN := nx * p.betax + ny * p.betay + nz * p.betaz; let An := z4c3dPrincipalSymbol p nx ny nz
    (z4cLightConePlus nx ny nz 0 = 1 ∧ ∀ i, i < 5 → mulVec 5 An (z4cLightConePlus nx ny nz) i = (-betaN + p.alpha) * z4cLightConePlus nx ny nz i) ∧
    (z4cLightConeMinus nx ny nz 0 = 1 ∧ ∀ i, i < 5 → mulVec 5 An (z4cLightConeMinus nx ny nz) i = (-betaN - p.alpha) * z4cLightConeMinus nx ny nz i) ∧
    (z4cLongitudinalAdvected 0 = 1 ∧ ∀ i, i < 5 → mulVec 5 An z4cLongitudinalAdvected i = (-betaN) * z4cLongitudinalAdvected i) ∧
    (∀ wx wy wz : Rat, nx * wx + ny * wy + nz * wz = 0 → ∀ i, i < 5 → mulVec 5 An (z4cTransverseAdvected wx wy wz) i = (-betaN) * z4cTransverseAdvected wx wy wz i) ∧
    (∀ d, d < 3 → IsEigenSystem 5 (z4c3dFluxMat p d) (z4c3dEigVecMat d) (z4c3dEigInvMat d) (z4c3dEigVals p d)) := by
  refine ⟨⟨rfl, fun i hi => ?_⟩, ⟨rfl, fun i hi => ?_⟩, ⟨rfl, fun i hi => ?_⟩, fun wx wy wz hOrth i hi => ?_, fun d hd => (z4c3d_axis_isEigenSystem p d hd).1⟩
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have h1 : nx * (p.alpha * nx) + ny * (p.alpha * ny) + nz * (p.alpha * nz) = p.alpha := by rw [show nx * (p.alpha * nx) + ny * (p.alpha * ny) + nz * (p.alpha * nz) = p.alpha * (nx * nx + ny * ny + nz * nz) by grind, hUnit]; grind
    have h2 : nx * (2 * p.alpha * nx) + ny * (2 * p.alpha * ny) + nz * (2 * p.alpha * nz) = 2 * p.alpha := by rw [show nx * (2 * p.alpha * nx) + ny * (2 * p.alpha * ny) + nz * (2 * p.alpha * nz) = 2 * p.alpha * (nx * nx + ny * ny + nz * nz) by grind, hUnit]; grind
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [mulVec, z4c3dPrincipalSymbol, z4c3dFluxMat, z4c3dFluxRows, z4cLightConePlus, matOf, getOr, sumTo]; grind)
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have h1 : nx * (p.alpha * -nx) + ny * (p.alpha * -ny) + nz * (p.alpha * -nz) = -p.alpha := by rw [show nx * (p.alpha * -nx) + ny * (p.alpha * -ny) + nz * (p.alpha * -nz) = -(p.alpha * (nx * nx + ny * ny + nz * nz)) by grind, hUnit]; grind
    have h2 : nx * (2 * p.alpha * -nx) + ny * (2 * p.alpha * -ny) + nz * (2 * p.alpha * -nz) = -(2 * p.alpha) := by rw [show nx * (2 * p.alpha * -nx) + ny * (2 * p.alpha * -ny) + nz * (2 * p.alpha * -nz) = -(2 * p.alpha * (nx * nx + ny * ny + nz * nz)) by grind, hUnit]; grind
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [mulVec, z4c3dPrincipalSymbol, z4c3dFluxMat, z4c3dFluxRows, z4cLightConeMinus, matOf, getOr, sumTo]; grind)
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [mulVec, z4c3dPrincipalSymbol, z4c3dFluxMat, z4c3dFluxRows, z4cLongitudinalAdvected, matOf, getOr, sumTo]; grind)
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have h1 : nx * (p.alpha * wx) + ny * (p.alpha * wy) + nz * (p.alpha * wz) = 0 := by rw [show nx * (p.alpha * wx) + ny * (p.alpha * wy) + nz * (p.alpha * wz) = p.alpha * (nx * wx + ny * wy + nz * wz) by grind, hOrth]; grind
    have h2 : nx * (2 * p.alpha * wx) + ny * (2 * p.alpha * wy) + nz * (2 * p.alpha * wz) = 0 := by rw [show nx * (2 * p.alpha * wx) + ny * (2 * p.alpha * wy) + nz * (2 * p.alpha * wz) = 2 * p.alpha * (nx * wx + ny * wy + nz * wz) by grind, hOrth]; grind
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [mulVec, z4c3dPrincipalSymbol, z4c3dFluxMat, z4c3dFluxRows, z4cTransverseAdvected, matOf, getOr, sumTo]; grind)

/-! ## 4. 3D Spatial $C_3$ Axis Permutation Equivariance (`z4c3d_cyclic_axis_equivariant`) -/

def z4cVarPerm (shift i : Nat) : Nat :=
  let s := shift % 3
  if s == 1 then (if i == 1 then 2 else if i == 2 then 3 else if i == 3 then 1 else i)
  else if s == 2 then (if i == 1 then 3 else if i == 2 then 1 else if i == 3 then 2 else i) else i
@[expose] def permuteZ4cVec (shift : Nat) (C : Vec) : Vec := fun i => C (z4cVarPerm shift i)
def cycleZ4cParams (shift : Nat) (p : Z4c3DParams) : Z4c3DParams :=
  let s := shift % 3
  if s == 1 then { p with betax := p.betay, betay := p.betaz, betaz := p.betax }
  else if s == 2 then { p with betax := p.betaz, betay := p.betax, betaz := p.betay } else p
theorem z4cVarPerm_add (s1 s2 i : Nat) : z4cVarPerm s2 (z4cVarPerm s1 i) = z4cVarPerm (s1 + s2) i := by
  have h1 : s1 % 3 = 0 ∨ s1 % 3 = 1 ∨ s1 % 3 = 2 := (by omega); have h2 : s2 % 3 = 0 ∨ s2 % 3 = 1 ∨ s2 % 3 = 2 := (by omega)
  have hadd : (s1 + s2) % 3 = (s1 % 3 + s2 % 3) % 3 := Nat.add_mod s1 s2 3
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    (by_cases hi1 : i = 1 <;> by_cases hi2 : i = 2 <;> by_cases hi3 : i = 3 <;> simp [z4cVarPerm, h1, h2, hadd, hi1, hi2, hi3])
theorem permuteZ4cVec_comp (s1 s2 : Nat) (C : Vec) : permuteZ4cVec s1 (permuteZ4cVec s2 C) = permuteZ4cVec (s1 + s2) C := by
  funext i; simp only [permuteZ4cVec, z4cVarPerm_add]
theorem z4c3d_cyclic_axis_equivariant (p : Z4c3DParams) (shift : Nat) (u v C : Vec) :
    (permuteZ4cVec 0 C = C ∧ ∀ s2, permuteZ4cVec shift (permuteZ4cVec s2 C) = permuteZ4cVec (shift + s2) C) ∧
    h0Inner 5 z4c3dSymmetrizer (permuteZ4cVec shift u) (permuteZ4cVec shift v) = h0Inner 5 z4c3dSymmetrizer u v ∧
    (∀ i, i < 5 → mulVec 5 (z4c3dSourceMat (cycleZ4cParams shift p)) (permuteZ4cVec shift C) i = permuteZ4cVec shift (mulVec 5 (z4c3dSourceMat p) C) i) ∧
    (∀ (axis : Fin 3) (i : Nat), i < 5 → mulVec 5 (z4c3dFluxMat p axis.val) C i =
      permuteZ4cVec ((3 - axis.val) % 3) (mulVec 5 (z4c3dFluxMat (cycleZ4cParams axis.val p) 0) (permuteZ4cVec axis.val C)) i) := by
  have hs : shift % 3 = 0 ∨ shift % 3 = 1 ∨ shift % 3 = 2 := by omega
  refine ⟨⟨by funext i; simp [permuteZ4cVec, z4cVarPerm], fun s2 => permuteZ4cVec_comp shift s2 C⟩, ?_, ?_, ?_⟩
  · rcases hs with h | h | h <;> (simp only [h0Inner, dot, mulVec, permuteZ4cVec, z4cVarPerm, h, z4c3dSymmetrizer, z4c3dSymmetrizerRows, matOf, getOr, sumTo]; grind)
  · intro i hi; have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hs with h | h | h <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      (simp [mulVec, z4c3dSourceMat, z4c3dSourceRows, cycleZ4cParams, permuteZ4cVec, z4cVarPerm, h, matOf, getOr, sumTo] <;> grind)
  · rintro ⟨a, ha⟩ i hi; have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := (by omega); have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := (by omega)
    rcases ha3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      (simp [mulVec, z4c3dFluxMat, z4c3dFluxRows, cycleZ4cParams, permuteZ4cVec, z4cVarPerm, matOf, getOr, sumTo] <;> grind)
/-! ## 5. Exponential Damping of Periodic Constant-Coefficient Constraint Energy (`z4c3d_total_constraint_energy_damped`) -/
def z4c3dMaxDampRate (p : Z4c3DParams) : Rat := (2 + rmax 0 p.kappa2) * p.kappa1 * p.alpha
@[expose] def z4c3dConstraintRollout (p : Z4c3DParams) (dims : List Nat) (a dx dt : Rat) (n : Nat) (U0 : MultiDGrid) : MultiDGrid :=
  symHypRollout (z4c3dConstraintSystem p) dims a dx dt n U0
theorem z4c3d_flux_speed_bound (p : Z4c3DParams) (a : Rat) (hAlpha : 0 ≤ p.alpha)
    (hBx : ratAbs p.betax + p.alpha ≤ a) (hBy : ratAbs p.betay + p.alpha ≤ a) (hBz : ratAbs p.betaz + p.alpha ≤ a) (d : Nat) (hd : d < 3) (v : Vec) :
    h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dFluxMat p d) v) (mulVec 5 (z4c3dFluxMat p d) v) ≤ (a * a) * h0Inner 5 z4c3dSymmetrizer v v := by
  obtain ⟨hEig, hGram⟩ := z4c3d_axis_isEigenSystem p d hd
  have hFormEq : ∀ u : Vec, h0Inner 5 z4c3dSymmetrizer u u = charForm 5 z4c3dCharWeights (z4c3dEigInvMat d) u u := fun u => by
    rw [h0Inner_congr_mat (fun i j hi hj => (hGram i j hi hj).symm) u u]; exact dot_gram 5 z4c3dCharWeights (z4c3dEigInvMat d) u u
  rw [hFormEq, hFormEq]; unfold charForm; rw [← sumTo_mul_left]
  have hShiftLe : ratAbs (p.shiftAxis d) + p.alpha ≤ a := by have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := (by omega); rcases hd3 with rfl | rfl | rfl <;> assumption
  obtain ⟨hbLo, hbHi⟩ := ratAbs_bounds_iff.mp (Rat.le_refl (a := ratAbs (p.shiftAxis d)))
  refine sumTo_le fun k hk => ?_; rw [hEig.char_flux v k hk]
  have hwNN : 0 ≤ z4c3dCharWeights k := by have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := (by omega); rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hLamSq : z4c3dEigVals p d k * z4c3dEigVals p d k ≤ a * a := by
    have hLamBounds : -a ≤ z4c3dEigVals p d k ∧ z4c3dEigVals p d k ≤ a := by
      have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [z4c3dEigVals, vecOf, getOr]; constructor <;> grind)
    have haNN : 0 ≤ a := by have := ratAbs_nonneg (p.shiftAxis d); grind
    by_cases hPosL : 0 ≤ z4c3dEigVals p d k
    · exact rat_mul_le_mul hPosL hLamBounds.2 hPosL hLamBounds.2
    · have hm := rat_mul_le_mul (show 0 ≤ -z4c3dEigVals p d k by grind) (show -z4c3dEigVals p d k ≤ a by grind)
        (show 0 ≤ -z4c3dEigVals p d k by grind) (show -z4c3dEigVals p d k ≤ a by grind); grind
  let y := mulVec 5 (z4c3dEigInvMat d) v k
  have hm := Rat.mul_le_mul_of_nonneg_right hLamSq (Rat.mul_nonneg hwNN (rat_mul_self_nonneg y)); dsimp [y] at hm; grind

theorem z4c3d_source_dissipation_bounds (p : Z4c3DParams) (hAlpha : 0 < p.alpha) (hK1 : 0 < p.kappa1) (hK2 : -1 ≤ p.kappa2) :
    let eta := p.kappa1 * p.alpha; let rMax := z4c3dMaxDampRate p
    0 < eta ∧ 0 ≤ rMax * rMax ∧
    (∀ v : Vec, h0Inner 5 (symSourceFormMat 5 z4c3dSymmetrizer (z4c3dSourceMat p)) v v ≤ (-(2 * eta)) * h0Inner 5 z4c3dSymmetrizer v v) ∧
    (∀ v : Vec, h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dSourceMat p) v) (mulVec 5 (z4c3dSourceMat p) v) ≤ (rMax * rMax) * h0Inner 5 z4c3dSymmetrizer v v) := by
  have heta : 0 < p.kappa1 * p.alpha := Rat.mul_pos hK1 hAlpha
  refine ⟨heta, rat_mul_self_nonneg _, fun v => ?_, fun v => ?_⟩
  · rw [z4c3dSymmetrizer_quadratic_form]
    simp only [h0Inner, dot, mulVec, symSourceFormMat, matMul, matTranspose, z4c3dSymmetrizer, z4c3dSymmetrizerRows, z4c3dSourceMat, z4c3dSourceRows, matOf, getOr, sumTo]
    have hr0 : p.kappa1 * p.alpha ≤ p.kappa1 * (2 + p.kappa2) * p.alpha := by
      have hm := Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_left (show 1 ≤ 2 + p.kappa2 by grind) (Rat.le_of_lt hK1)) (Rat.le_of_lt hAlpha); grind
    have := Rat.mul_le_mul_of_nonneg_right hr0 (rat_mul_self_nonneg (v 0)); have := Rat.mul_nonneg (Rat.le_of_lt heta) (rat_mul_self_nonneg (v 4)); grind
  · rw [z4c3dSymmetrizer_quadratic_form, z4c3dSymmetrizer_quadratic_form]
    simp only [mulVec, z4c3dSourceMat, z4c3dSourceRows, z4c3dMaxDampRate, matOf, getOr, sumTo]
    have hrm0 := le_rmax_left 0 p.kappa2; have hrm2 := le_rmax_right 0 p.kappa2
    have hd0Pos : 0 ≤ p.kappa1 * (2 + p.kappa2) * p.alpha := Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt hK1) (by grind)) (Rat.le_of_lt hAlpha)
    have hd0Le : p.kappa1 * (2 + p.kappa2) * p.alpha ≤ (2 + rmax 0 p.kappa2) * p.kappa1 * p.alpha := by
      have := Rat.mul_le_mul_of_nonneg_right (show 2 + p.kappa2 ≤ 2 + rmax 0 p.kappa2 by grind) (Rat.le_of_lt heta); grind
    have hd1Le : p.kappa1 * p.alpha ≤ (2 + rmax 0 p.kappa2) * p.kappa1 * p.alpha := by
      have := Rat.mul_le_mul_of_nonneg_right (show (1 : Rat) ≤ 2 + rmax 0 p.kappa2 by grind) (Rat.le_of_lt heta); grind
    have hd4Le : 2 * p.kappa1 * p.alpha ≤ (2 + rmax 0 p.kappa2) * p.kappa1 * p.alpha := by
      have := Rat.mul_le_mul_of_nonneg_right (show (2 : Rat) ≤ 2 + rmax 0 p.kappa2 by grind) (Rat.le_of_lt heta); grind
    have sq0 := rat_mul_le_mul hd0Pos hd0Le hd0Pos hd0Le; have sq1 := rat_mul_le_mul (Rat.le_of_lt heta) hd1Le (Rat.le_of_lt heta) hd1Le
    have sq4 := rat_mul_le_mul (by grind : 0 ≤ 2 * p.kappa1 * p.alpha) hd4Le (by grind : 0 ≤ 2 * p.kappa1 * p.alpha) hd4Le
    have := Rat.mul_le_mul_of_nonneg_right sq0 (rat_mul_self_nonneg (v 0)); have := Rat.mul_le_mul_of_nonneg_right sq1 (rat_mul_self_nonneg (v 1))
    have := Rat.mul_le_mul_of_nonneg_right sq1 (rat_mul_self_nonneg (v 2)); have := Rat.mul_le_mul_of_nonneg_right sq1 (rat_mul_self_nonneg (v 3))
    have := Rat.mul_le_mul_of_nonneg_right sq4 (rat_mul_self_nonneg (v 4)); grind

theorem z4c3dSemiDiscreteRhs_energy_dissipative (p : Z4c3DParams) (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) (dx : Rat)
    (hAlpha : 0 < p.alpha) (hK1 : 0 < p.kappa1) (hK2 : -1 ≤ p.kappa2) (C : MultiDGrid) :
    2 * multiDH0Pair dims 5 z4c3dSymmetrizer C (z4c3dSemiDiscreteRhs p dims dx C) ≤ (-(2 * (p.kappa1 * p.alpha))) * multiDH0Energy dims 5 z4c3dSymmetrizer C := by
  let sys := z4c3dConstraintSystem p
  have hSk0 := centeredDiff_h0_skew_adjoint sys dims hPos 0 (show 0 < 3 by decide) dx C
  have hSk1 := centeredDiff_h0_skew_adjoint sys dims hPos 1 (show 1 < 3 by decide) dx C
  have hSk2 := centeredDiff_h0_skew_adjoint sys dims hPos 2 (show 2 < 3 by decide) dx C
  dsimp only [sys, z4c3dConstraintSystem, multiDH0Pair, applyGridMat] at hSk0 hSk1 hSk2
  have hPairEq : multiDH0Pair dims 5 z4c3dSymmetrizer C (z4c3dSemiDiscreteRhs p dims dx C) =
      sumTo (gridCellCount dims) (fun idx => h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dSourceMat p) (C idx))) := by
    unfold multiDH0Pair z4c3dSemiDiscreteRhs
    have hCell : ∀ idx, h0Inner 5 z4c3dSymmetrizer (C idx) (fun c => mulVec 5 (z4c3dSourceMat p) (C idx) c - sumTo 3 fun d => mulVec 5 (z4c3dFluxMat p d) (centeredDiffAxis dims d dx C idx) c) =
        h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dSourceMat p) (C idx)) +
        ((-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dFluxMat p 0) (centeredDiffAxis dims 0 dx C idx)) +
         ((-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dFluxMat p 1) (centeredDiffAxis dims 1 dx C idx)) +
          (-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dFluxMat p 2) (centeredDiffAxis dims 2 dx C idx)))) := fun idx => by
      rw [show (fun c => mulVec 5 (z4c3dSourceMat p) (C idx) c - sumTo 3 fun d => mulVec 5 (z4c3dFluxMat p d) (centeredDiffAxis dims d dx C idx) c) =
          vecSub (mulVec 5 (z4c3dSourceMat p) (C idx)) (vecAdd (mulVec 5 (z4c3dFluxMat p 0) (centeredDiffAxis dims 0 dx C idx))
            (vecAdd (mulVec 5 (z4c3dFluxMat p 1) (centeredDiffAxis dims 1 dx C idx)) (mulVec 5 (z4c3dFluxMat p 2) (centeredDiffAxis dims 2 dx C idx)))) by
          funext c; simp only [sumTo, vecSub, vecAdd]; grind, h0Inner_sub_right, h0Inner_add_right, h0Inner_add_right]; grind
    rw [show (fun idx => h0Inner 5 z4c3dSymmetrizer (C idx) _) = _ from funext hCell, sumTo_add, sumTo_add, sumTo_add, sumTo_mul_left, sumTo_mul_left, sumTo_mul_left, hSk0, hSk1, hSk2]; grind
  rw [hPairEq, ← sumTo_mul_left]; unfold multiDH0Energy; rw [← sumTo_mul_left]
  have hDiss := (z4c3d_source_dissipation_bounds p hAlpha hK1 hK2).2.2.1; refine sumTo_le fun idx _ => ?_
  have hSym := sys.h0_bilinear_symm (C idx) (mulVec 5 (z4c3dSourceMat p) (C idx))
  have hPart := h0Inner_source_sym_part sys.hH0Symm (z4c3dSourceMat p) (C idx)
  dsimp only [sys, z4c3dConstraintSystem] at hSym hPart; have := hDiss (C idx); grind

private theorem adm_undamped_preserves_const (p : Z4c3DParams) (dims : List Nat) (a dx dt : Rat) (C0 : Vec) (n : Nat) :
    z4c3dConstraintRollout { p with kappa1 := 0 } dims a dx dt n (fun _ => C0) = (fun _ => C0) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold z4c3dConstraintRollout at ih ⊢; simp only [symHypRollout]
    have hOne : symHypFullStep (z4c3dConstraintSystem { p with kappa1 := 0 }) dims a dx dt (fun _ => C0) = (fun _ => C0) := by
      have hAxisConst : ∀ d : Nat, rusanovSymmetricAxisStep dims 5 (z4c3dFluxMat { p with kappa1 := 0 } d) a (dt / dx) d (fun _ => C0) = (fun _ => C0) := fun d => by
        unfold rusanovSymmetricAxisStep; split
        · funext idx c; dsimp only
          rw [show (fun j : Nat => C0 j - C0 j) = (fun _ => 0) by funext j; grind,
              show mulVec 5 (z4c3dFluxMat { p with kappa1 := 0 } d) (fun _ => 0) c = 0 by
                unfold mulVec; rw [show (fun j => z4c3dFluxMat { p with kappa1 := 0 } d c j * 0) = (fun _ => 0) by funext j; grind, sumTo_zero]]; grind
        · rfl
      have hSweepConst : ∀ ds : List Nat, rusanovSymmetricMultiDSweepAux dims 5 (z4c3dFluxMat { p with kappa1 := 0 }) a (dt / dx) ds (fun _ => C0) = (fun _ => C0) := by
        intro ds; induction ds with | nil => rfl | cons d rest ihs => simp [rusanovSymmetricMultiDSweepAux, hAxisConst, ihs]
      unfold symHypFullStep rusanovSymmetricMultiDSweep; dsimp only [z4c3dConstraintSystem]; rw [hSweepConst]; funext idx c; unfold symHypSourceStep; dsimp only
      have hSrcZero : mulVec 5 (z4c3dSourceMat { p with kappa1 := 0 }) C0 c = 0 := by
        unfold mulVec; rw [show (fun j => z4c3dSourceMat { p with kappa1 := 0 } c j * C0 j) = (fun _ => 0) by
          funext j; rcases c with _ | _ | _ | _ | _ | c <;> rcases j with _ | _ | _ | _ | _ | j <;>
            simp [z4c3dSourceMat, z4c3dSourceRows, matOf, getOr, Rat.zero_mul, Rat.neg_zero]]; exact sumTo_zero 5
      rw [hSrcZero]; grind
    rw [hOne]; exact ih

theorem z4c3d_total_constraint_energy_damped (p : Z4c3DParams) (dims : List Nat) (hDims : dims.length = 3) (hPos : ∀ N ∈ dims, 0 < N)
    (a dx dt : Rat) (hAlpha : 0 < p.alpha) (hK1 : 0 < p.kappa1) (hK2 : -1 ≤ p.kappa2)
    (hBx : ratAbs p.betax + p.alpha ≤ a) (hBy : ratAbs p.betay + p.alpha ≤ a) (hBz : ratAbs p.betaz + p.alpha ≤ a)
    (hdx : 0 < dx) (hdt : 0 < dt) (hcfl : dt * a ≤ dx)
    (hDampStep : dt * (z4c3dMaxDampRate p * z4c3dMaxDampRate p) ≤ p.kappa1 * p.alpha)
    (hEtaStep : (p.kappa1 * p.alpha) * dt ≤ 1) (n : Nat) (U0 : MultiDGrid) (C0 : Vec) :
    let eta := p.kappa1 * p.alpha
    multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dConstraintRollout p dims a dx dt n U0) ≤ ((1 - eta * dt) ^ n) * multiDH0Energy dims 5 z4c3dSymmetrizer U0 ∧
    (0 < n → (∃ idx c, idx < gridCellCount dims ∧ c < 5 ∧ U0 idx c ≠ 0) →
      multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dConstraintRollout p dims a dx dt n U0) < multiDH0Energy dims 5 z4c3dSymmetrizer U0) ∧
    (z4c3dConstraintRollout { p with kappa1 := 0 } dims a dx dt n (fun _ => C0) = (fun _ => C0) ∧
      ((∃ c, c < 5 ∧ C0 c ≠ 0) → 0 < multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dConstraintRollout { p with kappa1 := 0 } dims a dx dt n (fun _ => C0)))) := by
  have haNN : 0 ≤ a := by have := ratAbs_nonneg p.betax; grind
  obtain ⟨heta, hrSq, hDiss, hBnd⟩ := z4c3d_source_dissipation_bounds p hAlpha hK1 hK2
  have hGron := symmetricHyperbolic_gronwall_stability (z4c3dConstraintSystem p) dims hDims hPos
    a dx dt (z4c3dMaxDampRate p * z4c3dMaxDampRate p) haNN hdx (Rat.le_of_lt hdt) hcfl
    (z4c3d_flux_speed_bound p a (Rat.le_of_lt hAlpha) hBx hBy hBz) hBnd hrSq n U0
  obtain ⟨hDecay, hStrict⟩ := hGron.2 (p.kappa1 * p.alpha) heta hdt hDampStep hEtaStep hDiss
  refine ⟨hDecay, hStrict, adm_undamped_preserves_const p dims a dx dt C0 n, fun ⟨c, hc, hNe⟩ => ?_⟩
  rw [adm_undamped_preserves_const]
  exact sumTo_pos (fun _ _ => (z4c3dConstraintSystem p).h0_nonneg C0) 0 (gridCellCount_pos dims hPos) ((z4c3dConstraintSystem p).h0_pos_of_ne C0 c hc hNe)

/-! ## 6. 10-Variable `#pde_solver BssnZ4cConstraint3D`, Jacobian Sub-Block Weld & 1D Planar-Slab Reduction -/

#pde_solver BssnZ4cConstraint3D :=
  "(conservation-law (name BssnZ4cConstraint3D) (coords x y z) (vars alpha gxx Ax Dx Kxx Theta Zx Zy Zz Hham)
     (params (fBM 2) (beta 1/5) (kappa1 1/2) (betay 1/10) (betaz -1/10) (kappa2 -1)) (domain (> alpha 0) (> gxx 0))
     (fluxes
       (x (let ((trK (/ Kxx gxx)) (kHat (- trK (* 2 Theta))))
            (- (* beta alpha)) (- (* beta gxx)) (+ (- (* beta Ax)) (* fBM (* alpha kHat))) (+ (- (* beta Dx)) (* alpha trK))
            (+ (- (* beta Kxx)) (* alpha Ax)) (+ (- (* beta Theta)) (* alpha Zx))
            (+ (+ (- (* beta Zx)) (* 1/2 (* alpha Theta))) (* 1/4 (* alpha Hham))) (- (* beta Zy)) (- (* beta Zz)) (+ (- (* beta Hham)) (* 2 (* alpha Zx)))))
       (y (- (* betay alpha)) (- (* betay gxx)) (- (* betay Ax)) (- (* betay Dx)) (- (* betay Kxx)) (+ (- (* betay Theta)) (* alpha Zy)) (- (* betay Zx))
          (+ (+ (- (* betay Zy)) (* 1/2 (* alpha Theta))) (* 1/4 (* alpha Hham))) (- (* betay Zz)) (+ (- (* betay Hham)) (* 2 (* alpha Zy))))
       (z (- (* betaz alpha)) (- (* betaz gxx)) (- (* betaz Ax)) (- (* betaz Dx)) (- (* betaz Kxx)) (+ (- (* betaz Theta)) (* alpha Zz)) (- (* betaz Zx)) (- (* betaz Zy))
          (+ (+ (- (* betaz Zz)) (* 1/2 (* alpha Theta))) (* 1/4 (* alpha Hham))) (+ (- (* betaz Hham)) (* 2 (* alpha Zz)))))
     (sources (- (* (sq alpha) fBM (- (/ Kxx gxx) (* 2 Theta)))) (- (* 2 alpha Kxx)) 0 0 (- (* alpha (- (* Ax Dx) (/ (sq Kxx) gxx))) (* kappa1 (* alpha Theta)))
       (- (* (* kappa1 (+ 2 kappa2)) (* alpha Theta))) (- (* kappa1 (* alpha Zx))) (- (* kappa1 (* alpha Zy))) (- (* kappa1 (* alpha Zz))) (- (* 2 (* kappa1 (* alpha Hham)))))
     (max-wavespeed 9) (cfl 1/10)
     (state-box (alpha 1/2 2) (gxx 1 4) (Ax -1/2 1/2) (Dx -1/2 1/2) (Kxx -1/2 1/2) (Theta -1/4 1/4) (Zx -1/4 1/4) (Zy -1/4 1/4) (Zz -1/4 1/4) (Hham -1/4 1/4))
     (wavespeed-weights 1/4 1/4 1 1 1 1/4 1/4 1/4 1/4 1/4) (limiter minmod))"

@[expose] def bssnZ4c3dSolverParams (alpha : Rat) : Z4c3DParams :=
  { alpha := alpha, betax := 1 / 5, betay := 1 / 10, betaz := -(1 / 10), kappa1 := 1 / 2, kappa2 := -1 }

private def isZeroExpr : FluxExpr → Bool
  | .const k => k == 0 | .neg a => isZeroExpr a | .add a b | .sub a b => isZeroExpr a && isZeroExpr b | .mul a b => isZeroExpr a || isZeroExpr b | _ => false

private theorem evalFlux_of_isZeroExpr (e : FluxExpr) (env : FluxEnv) (h : isZeroExpr e = true) : evalFlux e env = 0 := by
  induction e with
  | const k => simp only [isZeroExpr, beq_iff_eq] at h; simp [evalFlux, h]
  | neg a iha => simp only [isZeroExpr] at h; simp only [evalFlux, iha h]; grind
  | add a b iha ihb | sub a b iha ihb => simp only [isZeroExpr, Bool.and_eq_true] at h; simp only [evalFlux, iha h.1, ihb h.2]; grind
  | mul a b iha ihb =>
    simp only [isZeroExpr, Bool.or_eq_true] at h
    cases h with | inl ha => simp only [evalFlux, iha ha]; grind | inr hb => simp only [evalFlux, ihb hb]; grind
  | var _ | param _ | invSafe _ => simp [isZeroExpr] at h

private def isConstExpr : FluxExpr → Bool
  | .const _ | .param _ => true | .neg a => isConstExpr a | .add a b | .sub a b | .mul a b => isConstExpr a && isConstExpr b | _ => false

private theorem evalFlux_of_isConstExpr (e : FluxExpr) (u v : Vec) (p : Nat → Rat) (h : isConstExpr e = true) : evalFlux e ⟨u, p⟩ = evalFlux e ⟨v, p⟩ := by
  induction e with
  | const _ | param _ => rfl
  | neg a iha => simp only [isConstExpr] at h; simp [evalFlux, iha h]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb => simp only [isConstExpr, Bool.and_eq_true] at h; simp [evalFlux, iha h.1, ihb h.2]
  | var _ | invSafe _ => simp [isConstExpr] at h

private def isAffineVar0 : FluxExpr → Bool
  | .const _ | .param _ => true | .var i => i == 0 | .neg a => isAffineVar0 a | .add a b | .sub a b => isAffineVar0 a && isAffineVar0 b
  | .mul a b => (isZeroExpr a) || ((isZeroExpr b) || ((isConstExpr a && isAffineVar0 b) || (isAffineVar0 a && isConstExpr b))) | .invSafe _ => false

private theorem evalFlux_of_isAffineVar0 (e : FluxExpr) (u : Vec) (p : Nat → Rat) (h : isAffineVar0 e = true) :
    evalFlux e ⟨u, p⟩ = evalFlux e ⟨fun _ => 0, p⟩ + (evalFlux e ⟨fun _ => 1, p⟩ - evalFlux e ⟨fun _ => 0, p⟩) * u 0 := by
  induction e with
  | const _ | param _ => simp only [evalFlux]; grind
  | var i => simp only [isAffineVar0, beq_iff_eq] at h; subst h; simp only [evalFlux]; grind
  | neg a iha => simp only [isAffineVar0] at h; have := iha h; simp only [evalFlux] at this ⊢; grind
  | add a b iha ihb | sub a b iha ihb => simp only [isAffineVar0, Bool.and_eq_true] at h; have ea := iha h.1; have eb := ihb h.2; simp only [evalFlux] at ea eb ⊢; grind
  | mul a b iha ihb =>
    simp only [isAffineVar0, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with hza | hzb | ⟨hca, hab⟩ | ⟨haa, hcb⟩
    · simp only [evalFlux, evalFlux_of_isZeroExpr a _ hza]; grind
    · simp only [evalFlux, evalFlux_of_isZeroExpr b _ hzb]; grind
    · have ca0 := evalFlux_of_isConstExpr a u (fun _ => 0) p hca; have ca1 := evalFlux_of_isConstExpr a (fun _ => 1) (fun _ => 0) p hca
      have eb := ihb hab; simp only [evalFlux] at eb ⊢; rw [ca0, ca1, eb]; grind
    · have cb0 := evalFlux_of_isConstExpr b u (fun _ => 0) p hcb; have cb1 := evalFlux_of_isConstExpr b (fun _ => 1) (fun _ => 0) p hcb
      have ea := iha haa; simp only [evalFlux] at ea ⊢; rw [cb0, cb1, ea]; grind
  | invSafe _ => simp [isAffineVar0] at h

private def vanishesOnZeroConstraints : FluxExpr → Bool
  | .const k => k == 0 | .var i => decide (5 ≤ i) && decide (i < 10) | .neg a => vanishesOnZeroConstraints a
  | .add a b | .sub a b => vanishesOnZeroConstraints a && vanishesOnZeroConstraints b | .mul a b => vanishesOnZeroConstraints a || vanishesOnZeroConstraints b | _ => false

private theorem evalFlux_of_vanishesOnZeroConstraints (e : FluxExpr) (u : Vec) (p : Nat → Rat)
    (hZero : ∀ k, k < 5 → u (5 + k) = 0) (h : vanishesOnZeroConstraints e = true) : evalFlux e ⟨u, p⟩ = 0 := by
  induction e with
  | const k => simp only [vanishesOnZeroConstraints, beq_iff_eq] at h; simp [evalFlux, h]
  | var i => simp only [vanishesOnZeroConstraints, Bool.and_eq_true, decide_eq_true_eq] at h; dsimp only [evalFlux]; rw [← show 5 + (i - 5) = i by omega]; exact hZero (i - 5) (by omega)
  | neg a iha => simp only [vanishesOnZeroConstraints] at h; simp only [evalFlux, iha h]; grind
  | add a b iha ihb | sub a b iha ihb => simp only [vanishesOnZeroConstraints, Bool.and_eq_true] at h; simp only [evalFlux, iha h.1, ihb h.2]; grind
  | mul a b iha ihb =>
    simp only [vanishesOnZeroConstraints, Bool.or_eq_true] at h
    cases h with | inl ha => simp only [evalFlux, iha ha]; grind | inr hb => simp only [evalFlux, ihb hb]; grind
  | param _ | invSafe _ => simp [vanishesOnZeroConstraints] at h

private def checkConstraintSubJacAt (J : List (List FluxExpr)) (M0 M1 : Mat) (i j : Nat) : Bool :=
  let e := getOr (getOr J (5 + i) []) (5 + j) (.const 0); let p := BssnZ4cConstraint3D.spec.paramEnv
  (isAffineVar0 e) && ((evalFlux e ⟨fun _ => 0, p⟩ == M0 i j) && ((evalFlux e ⟨fun _ => 1, p⟩ == M1 i j) && vanishesOnZeroConstraints (getOr (getOr J (5 + i) []) j (.const 0))))

private def checkAllConstraintSubJacs : Bool :=
  let Js := specJacobians BssnZ4cConstraint3D.spec; let J0 := getOr Js 0 []; let J1 := getOr Js 1 []; let J2 := getOr Js 2 []
  let JS := symJacobian BssnZ4cConstraint3D.spec.numVars BssnZ4cConstraint3D.spec.sources
  (List.range 5).all fun i => (List.range 5).all fun j =>
    (checkConstraintSubJacAt J0 (z4c3dFluxMat (bssnZ4c3dSolverParams 0) 0) (z4c3dFluxMat (bssnZ4c3dSolverParams 1) 0) i j) &&
    ((checkConstraintSubJacAt J1 (z4c3dFluxMat (bssnZ4c3dSolverParams 0) 1) (z4c3dFluxMat (bssnZ4c3dSolverParams 1) 1) i j) &&
    ((checkConstraintSubJacAt J2 (z4c3dFluxMat (bssnZ4c3dSolverParams 0) 2) (z4c3dFluxMat (bssnZ4c3dSolverParams 1) 2) i j) &&
     (checkConstraintSubJacAt JS (z4c3dSourceMat (bssnZ4c3dSolverParams 0)) (z4c3dSourceMat (bssnZ4c3dSolverParams 1)) i j)))

theorem bssnZ4cConstraint3D_constraint_sector_eq_z4c3d (u : Vec) (d i j : Nat) (hd : d < 3) (hi : i < 5) (hj : j < 5) :
    evalSymJacobianMat (getOr (specJacobians BssnZ4cConstraint3D.spec) d []) ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) (5 + j) =
      z4c3dFluxMat (bssnZ4c3dSolverParams (u 0)) d i j ∧
    evalSymJacobianMat (symJacobian BssnZ4cConstraint3D.spec.numVars BssnZ4cConstraint3D.spec.sources) ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) (5 + j) =
      z4c3dSourceMat (bssnZ4c3dSolverParams (u 0)) i j ∧
    ((∀ k, k < 5 → u (5 + k) = 0) →
      evalSymJacobianMat (getOr (specJacobians BssnZ4cConstraint3D.spec) d []) ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) j = 0 ∧
      evalSymJacobianMat (symJacobian BssnZ4cConstraint3D.spec.numVars BssnZ4cConstraint3D.spec.sources) ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) j = 0) := by
  have hAll : checkAllConstraintSubJacs = true := by decide +kernel
  unfold checkAllConstraintSubJacs at hAll; simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hAll
  obtain ⟨hc0, hc1, hc2, hcS⟩ := hAll i hi j hj
  unfold checkConstraintSubJacAt at hc0 hc1 hc2 hcS; simp only [Bool.and_eq_true, beq_iff_eq] at hc0 hc1 hc2 hcS
  obtain ⟨ha0, he00, he01, hv0⟩ := hc0; obtain ⟨ha1, he10, he11, hv1⟩ := hc1; obtain ⟨ha2, he20, he21, hv2⟩ := hc2; obtain ⟨haS, heS0, heS1, hvS⟩ := hcS
  unfold evalSymJacobianMat; let pE := BssnZ4cConstraint3D.spec.paramEnv
  have hSrcAff := evalFlux_of_isAffineVar0 _ u pE haS; rw [heS0, heS1] at hSrcAff
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := (by omega); have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := (by omega); have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := (by omega)
  rcases hd3 with rfl | rfl | rfl
  · have hFlAff := evalFlux_of_isAffineVar0 _ u pE ha0; rw [he00, he01] at hFlAff; rw [hFlAff, hSrcAff]
    refine ⟨?_, ?_, fun hZ => ⟨evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hv0, evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hvS⟩⟩
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [z4c3dFluxMat, z4c3dFluxRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [z4c3dSourceMat, z4c3dSourceRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
  · have hFlAff := evalFlux_of_isAffineVar0 _ u pE ha1; rw [he10, he11] at hFlAff; rw [hFlAff, hSrcAff]
    refine ⟨?_, ?_, fun hZ => ⟨evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hv1, evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hvS⟩⟩
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [z4c3dFluxMat, z4c3dFluxRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [z4c3dSourceMat, z4c3dSourceRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
  · have hFlAff := evalFlux_of_isAffineVar0 _ u pE ha2; rw [he20, he21] at hFlAff; rw [hFlAff, hSrcAff]
    refine ⟨?_, ?_, fun hZ => ⟨evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hv2, evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hvS⟩⟩
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [z4c3dFluxMat, z4c3dFluxRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [z4c3dSourceMat, z4c3dSourceRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)

@[expose] def embedZ4cVec1DTo3D (u : Vec) : Vec := fun c => if c < 6 then u c else 0
@[expose] def embedZ4cPlanarSlab (Ny Nz : Nat) (U1D : MultiDGrid) : MultiDGrid := fun idx => embedZ4cVec1DTo3D (U1D (idx / (Ny * Nz)))
def pdeGridRollout (step : MultiDGrid → MultiDGrid) : Nat → MultiDGrid → MultiDGrid | 0, U => U | n + 1, U => pdeGridRollout step n (step U)

private def usesOnlyPrefixVarsAndParams : FluxExpr → Bool
  | .const _ => true | .var i => decide (i < 6) | .param p => decide (p < 3) | .neg a | .invSafe a => usesOnlyPrefixVarsAndParams a
  | .add a b | .sub a b | .mul a b => usesOnlyPrefixVarsAndParams a && usesOnlyPrefixVarsAndParams b

private theorem evalFlux_prefix_agree (e : FluxExpr) (hPre : usesOnlyPrefixVarsAndParams e = true) (u3 u1 : Vec) (hState : ∀ i, i < 6 → u3 i = u1 i) :
    evalFlux e ⟨u3, BssnZ4cConstraint3D.spec.paramEnv⟩ = evalFlux e ⟨u1, BonaMassoZ4c1D.spec.paramEnv⟩ := by
  have hParam : ∀ p, p < 3 → BssnZ4cConstraint3D.spec.paramEnv p = BonaMassoZ4c1D.spec.paramEnv p := fun p hp => by
    have hp3 : p = 0 ∨ p = 1 ∨ p = 2 := (by omega); rcases hp3 with rfl | rfl | rfl <;> decide +kernel
  induction e with
  | const _ => rfl
  | var i => simp only [usesOnlyPrefixVarsAndParams, decide_eq_true_eq] at hPre; exact hState i hPre
  | param p => simp only [usesOnlyPrefixVarsAndParams, decide_eq_true_eq] at hPre; exact hParam p hPre
  | neg a iha | invSafe a iha => simp only [usesOnlyPrefixVarsAndParams] at hPre; simp [evalFlux, iha hPre]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb => simp only [usesOnlyPrefixVarsAndParams, Bool.and_eq_true] at hPre; simp [evalFlux, iha hPre.1, ihb hPre.2]

private theorem bssn3d_xflux_matches_1d (u : Vec) (c : Nat) (hc : c < 6) :
    evalFlux (fluxComp BssnZ4cConstraint3D.spec 0 c) ⟨embedZ4cVec1DTo3D u, BssnZ4cConstraint3D.spec.paramEnv⟩ =
    evalFlux (fluxComp BonaMassoZ4c1D.spec 0 c) ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩ := by
  have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  have hSt : ∀ i, i < 6 → embedZ4cVec1DTo3D u i = u i := fun i hi => by simp [embedZ4cVec1DTo3D, hi]
  rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 0 = fluxComp BonaMassoZ4c1D.spec 0 0 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 1 = fluxComp BonaMassoZ4c1D.spec 0 1 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 2 = fluxComp BonaMassoZ4c1D.spec 0 2 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 3 = fluxComp BonaMassoZ4c1D.spec 0 3 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 4 = fluxComp BonaMassoZ4c1D.spec 0 4 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · have h3 : fluxComp BssnZ4cConstraint3D.spec 0 5 = .add (.neg (.mul (.param 1) (.var 5))) (.mul (.var 0) (.var 6)) := by decide +kernel
    have h1 : fluxComp BonaMassoZ4c1D.spec 0 5 = .neg (.mul (.param 1) (.var 5)) := by decide +kernel
    have hp1 : BssnZ4cConstraint3D.spec.paramEnv 1 = BonaMassoZ4c1D.spec.paramEnv 1 := by decide +kernel
    rw [h3, h1]; simp only [evalFlux, embedZ4cVec1DTo3D, show (5 : Nat) < 6 by decide, show ¬ ((6 : Nat) < 6) by decide, ↓reduceIte, hp1]; grind

private theorem bssn3d_source_matches_1d (u3 u1 : Vec) (hSt : ∀ i, i < 6 → u3 i = u1 i) (c : Nat) (hc : c < 6) :
    evalFlux (getOr BssnZ4cConstraint3D.spec.sources c (.const 0)) ⟨u3, BssnZ4cConstraint3D.spec.paramEnv⟩ =
    evalFlux (getOr BonaMassoZ4c1D.spec.sources c (.const 0)) ⟨u1, BonaMassoZ4c1D.spec.paramEnv⟩ := by
  have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 0 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 0 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 1 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 1 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 2 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 2 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 3 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 3 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 4 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 4 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · have h3 : getOr BssnZ4cConstraint3D.spec.sources 5 (.const 0) = .neg (.mul (.mul (.param 2) (.add (.const 2) (.param 5))) (.mul (.var 0) (.var 5))) := by decide +kernel
    have h1 : getOr BonaMassoZ4c1D.spec.sources 5 (.const 0) = .neg (.mul (.param 2) (.mul (.var 0) (.var 5))) := by decide +kernel
    have hp2 : BssnZ4cConstraint3D.spec.paramEnv 2 = BonaMassoZ4c1D.spec.paramEnv 2 := by decide +kernel
    have hp5 : BssnZ4cConstraint3D.spec.paramEnv 5 = -1 := by decide +kernel
    rw [h3, h1]; simp only [evalFlux, hp2, hp5, hSt 0 (by decide), hSt 5 (by decide)]; grind

private theorem evalAxisCellRat_const_sample (S : ConservationLawSpec) (axis : Nat) (ν : Rat) (v : Vec) (c : Nat) :
    evalAxisCellRat S axis ν (fun _ => v) c = v c := by unfold evalAxisCellRat faceFlux4; simp only [rusanovNonlinearFlux]; grind

private theorem slab3d_div_eq (Ny Nz ix iy iz : Nat) (hiy : iy < Ny) (hiz : iz < Nz) :
    (ix * (Ny * Nz) + (iy * Nz + iz)) / (Ny * Nz) = ix := by
  have hBlock : 0 < Ny * Nz := Nat.mul_pos (by omega) (by omega)
  have hrem : iy * Nz + iz < Ny * Nz := by have h2 := Nat.mul_le_mul_right Nz (show iy + 1 ≤ Ny by omega); rw [Nat.add_mul, Nat.one_mul] at h2; omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBlock, Nat.div_eq_of_lt hrem, Nat.zero_add]

private theorem bssn3d_zero_constraints_flux_source (v : Vec) (hv : ∀ j, 5 ≤ j → v j = 0) (c : Nat) (hc : 5 ≤ c) :
    evalFlux (fluxComp BssnZ4cConstraint3D.spec 0 c) ⟨v, BssnZ4cConstraint3D.spec.paramEnv⟩ = 0 ∧
    evalFlux (getOr BssnZ4cConstraint3D.spec.sources c (.const 0)) ⟨v, BssnZ4cConstraint3D.spec.paramEnv⟩ = 0 := by
  by_cases hlt : c < 10
  · have hc5 : c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 := (by omega); have hZ5 : ∀ k, k < 5 → v (5 + k) = 0 := fun k _ => hv (5 + k) (by omega)
    rcases hc5 with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨evalFlux_of_vanishesOnZeroConstraints _ v _ hZ5 (by decide +kernel), evalFlux_of_vanishesOnZeroConstraints _ v _ hZ5 (by decide +kernel)⟩
  · have hRowGe : ∀ (xs : List FluxExpr) (k : Nat), xs.length ≤ k → getOr xs k (.const 0) = .const 0 := by
      intro xs; induction xs with | nil => intro _ _; rfl | cons _ rs ihr => intro k hk; cases k with | zero => simp at hk | succ k' => exact ihr k' (by simpa using hk)
    have hLenF : (getOr BssnZ4cConstraint3D.spec.fluxes 0 []).length = 10 := by decide +kernel
    have hLenS : BssnZ4cConstraint3D.spec.sources.length = 10 := by decide +kernel
    unfold fluxComp; rw [hRowGe _ c (by omega), hRowGe _ c (by omega)]; exact ⟨rfl, rfl⟩

theorem z4c3d_slab_reduction_matches_1d (Nx Ny Nz : Nat) (hNx : 0 < Nx) (hNy : 0 < Ny) (hNz : 0 < Nz)
    (dt : Rat) (U1D : MultiDGrid) (u : Vec) (ix iy iz c : Nat) (hix : ix < Nx) (hiy : iy < Ny) (hiz : iz < Nz) :
    (c < 6 → evalFlux (fluxComp BssnZ4cConstraint3D.spec 0 c) ⟨embedZ4cVec1DTo3D u, BssnZ4cConstraint3D.spec.paramEnv⟩ =
      evalFlux (fluxComp BonaMassoZ4c1D.spec 0 c) ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩) ∧
    (c < 6 → BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false (embedZ4cPlanarSlab Ny Nz U1D) (ix * (Ny * Nz) + (iy * Nz + iz)) c =
      BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false U1D ix c) ∧
    ((∀ kx, kx < Nx → U1D kx 5 = 0) → ∀ (n : Nat),
      pdeGridRollout (BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false) n (embedZ4cPlanarSlab Ny Nz U1D) (ix * (Ny * Nz) + (iy * Nz + iz)) c =
      embedZ4cVec1DTo3D (pdeGridRollout (BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false) n U1D ix) c) := by
  have hStepCore : ∀ (G : MultiDGrid) (W1D : MultiDGrid),
      (∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz → G (kx * (Ny * Nz) + (ky * Nz + kz)) = embedZ4cVec1DTo3D (W1D kx)) →
      (∀ (kx ky kz c' : Nat), kx < Nx → ky < Ny → kz < Nz → c' < 6 →
        BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' =
          BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx c') ∧
      ((∀ kx, kx < Nx → W1D kx 5 = 0) →
        (∀ kx, kx < Nx → BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx 5 = 0) ∧
        (∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz →
          BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) =
            embedZ4cVec1DTo3D (BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx))) := by
    intro G W1D hGSlab
    let Gx := evalAxisStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] 0 dt G
    let Gxy := evalAxisStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] 1 dt Gx
    let Gxyz := evalAxisStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] 2 dt Gxy
    let cell1D : Nat → Vec := fun kx c' =>
      evalAxisCellRat BssnZ4cConstraint3D.spec 0 dt (fun off => embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + off)))) c'
    have hGx_slab : ∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz → Gx (kx * (Ny * Nz) + (ky * Nz + kz)) = cell1D kx := by
      intro kx ky kz hkx hky hkz; funext c'; dsimp only [Gx]; unfold evalAxisStepRat; simp only [show 0 < ([Nx, Ny, Nz] : List Nat).length by simp, ↓reduceIte]
      have hFib : axisFiberDims [Nx, Ny, Nz] 0 = ⟨1, Nx, Ny * Nz⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      have hrLt : ky * Nz + kz < Ny * Nz := by have h2 := Nat.mul_le_mul_right Nz (show ky + 1 ≤ Ny by omega); rw [Nat.add_mul, Nat.one_mul] at h2; omega
      rw [show (fun off : Int => G (axisNeighbor .periodic [Nx, Ny, Nz] 0 off (kx * (Ny * Nz) + (ky * Nz + kz)))) =
          (fun off : Int => embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + off)))) by
        funext off; unfold axisNeighbor; rw [hFib]; dsimp only
        rw [show kx * (Ny * Nz) + (ky * Nz + kz) = 0 * (Nx * (Ny * Nz)) + (kx * (Ny * Nz) + (ky * Nz + kz)) by simp,
            fiberNeighbor_cell .periodic Nx (Ny * Nz) off 0 kx (ky * Nz + kz) hkx hrLt]
        simp only [Nat.zero_mul, Nat.zero_add]; exact hGSlab _ ky kz (resolveStencilIdx_lt .periodic Nx hNx _) hky hkz]
    have hGxy_slab : ∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz → Gxy (kx * (Ny * Nz) + (ky * Nz + kz)) = cell1D kx := by
      intro kx ky kz hkx hky hkz; funext c'; dsimp only [Gxy]; unfold evalAxisStepRat; simp only [show 1 < ([Nx, Ny, Nz] : List Nat).length by simp, ↓reduceIte]
      have hFib1 : axisFiberDims [Nx, Ny, Nz] 1 = ⟨Nx, Ny, Nz⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      rw [show (fun off : Int => Gx (axisNeighbor .periodic [Nx, Ny, Nz] 1 off (kx * (Ny * Nz) + (ky * Nz + kz)))) = (fun _ => cell1D kx) by
        funext off; unfold axisNeighbor; rw [hFib1]; dsimp only
        rw [fiberNeighbor_cell .periodic Ny Nz off kx ky kz hky hkz]; exact hGx_slab kx _ kz hkx (resolveStencilIdx_lt .periodic Ny hNy _) hkz,
        evalAxisCellRat_const_sample]
    have hGxyz_at : ∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz → Gxyz (kx * (Ny * Nz) + (ky * Nz + kz)) = cell1D kx := by
      intro kx ky kz hkx hky hkz; funext c'; dsimp only [Gxyz]; unfold evalAxisStepRat; simp only [show 2 < ([Nx, Ny, Nz] : List Nat).length by simp, ↓reduceIte]
      have hFib2 : axisFiberDims [Nx, Ny, Nz] 2 = ⟨Nx * Ny, Nz, 1⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      rw [show (fun off : Int => Gxy (axisNeighbor .periodic [Nx, Ny, Nz] 2 off (kx * (Ny * Nz) + (ky * Nz + kz)))) = (fun _ => cell1D kx) by
        funext off; unfold axisNeighbor; rw [hFib2]; dsimp only
        rw [show kx * (Ny * Nz) + (ky * Nz + kz) = (kx * Ny + ky) * (Nz * 1) + (kz * 1 + 0) by simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc],
            fiberNeighbor_cell .periodic Nz 1 off (kx * Ny + ky) kz 0 hkz (by decide),
            show (kx * Ny + ky) * (Nz * 1) + (resolveStencilIdx .periodic Nz ((kz : Int) + off) * 1 + 0) =
              kx * (Ny * Nz) + (ky * Nz + resolveStencilIdx .periodic Nz ((kz : Int) + off)) by simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]]
        exact hGxy_slab kx ky _ hkx hky (resolveStencilIdx_lt .periodic Nz hNz _), evalAxisCellRat_const_sample]
    have hLim3 : BssnZ4cConstraint3D.spec.limiter = .minmod := by decide +kernel
    have hLim1 : BonaMassoZ4c1D.spec.limiter = .minmod := by decide +kernel
    have hRecEq : ∀ u0 u1 um1 u2 : Vec,
        (fun j => embedZ4cVec1DTo3D u0 j + (1 / 2 : Rat) * slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D um1) (embedZ4cVec1DTo3D u0) (embedZ4cVec1DTo3D u1) j) =
          embedZ4cVec1DTo3D (fun j => u0 j + (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec um1 u0 u1 j) ∧
        (fun j => embedZ4cVec1DTo3D u1 j - (1 / 2 : Rat) * slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D u0) (embedZ4cVec1DTo3D u1) (embedZ4cVec1DTo3D u2) j) =
          embedZ4cVec1DTo3D (fun j => u1 j - (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec u0 u1 u2 j) := by
      intro u0 u1 um1 u2; constructor <;> funext j <;> by_cases hj : j < 6 <;>
        simp [embedZ4cVec1DTo3D, slopeAt, hLim3, hLim1, hj, minmod_self, Rat.sub_self, Rat.zero_add]
    have hCell1D_eq : ∀ kx, kx < Nx → ∀ c', c' < 6 → cell1D kx c' = evalAxisStepRat BonaMassoZ4c1D.spec .periodic [Nx] 0 dt W1D kx c' := by
      intro kx hkx c' hc'; unfold evalAxisStepRat; simp only [show 0 < ([Nx] : List Nat).length by simp, ↓reduceIte]
      have hFib1D : axisFiberDims [Nx] 0 = ⟨1, Nx, 1⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      rw [show (fun off : Int => W1D (axisNeighbor .periodic [Nx] 0 off kx)) = (fun off : Int => W1D (resolveStencilIdx .periodic Nx ((kx : Int) + off))) by
        funext off; unfold axisNeighbor; rw [hFib1D]; dsimp only
        simp [fiberNeighbor, Nat.ne_of_gt hNx, Nat.div_eq_of_lt hkx, Nat.mod_eq_of_lt hkx, Nat.mod_one]]
      dsimp only [cell1D]; unfold evalAxisCellRat faceFlux4
      have hFaceEq : ∀ um1 u0 u1 u2 : Vec,
          rusanovNonlinearFlux (getOr BssnZ4cConstraint3D.spec.fluxes 0 []) BssnZ4cConstraint3D.spec.paramEnv BssnZ4cConstraint3D.spec.aMax
            (fun j => embedZ4cVec1DTo3D u0 j + (1 / 2 : Rat) * slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D um1) (embedZ4cVec1DTo3D u0) (embedZ4cVec1DTo3D u1) j)
            (fun j => embedZ4cVec1DTo3D u1 j - (1 / 2 : Rat) * slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D u0) (embedZ4cVec1DTo3D u1) (embedZ4cVec1DTo3D u2) j) c' =
          rusanovNonlinearFlux (getOr BonaMassoZ4c1D.spec.fluxes 0 []) BonaMassoZ4c1D.spec.paramEnv BonaMassoZ4c1D.spec.aMax
            (fun j => u0 j + (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec um1 u0 u1 j)
            (fun j => u1 j - (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec u0 u1 u2 j) c' := by
        intro um1 u0 u1 u2; obtain ⟨hL, hR⟩ := hRecEq u0 u1 um1 u2; rw [hL, hR]; unfold rusanovNonlinearFlux
        rw [show BssnZ4cConstraint3D.spec.aMax = BonaMassoZ4c1D.spec.aMax by decide +kernel]
        have hfL := bssn3d_xflux_matches_1d (fun j => u0 j + (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec um1 u0 u1 j) c' hc'
        have hfR := bssn3d_xflux_matches_1d (fun j => u1 j - (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec u0 u1 u2 j) c' hc'
        unfold fluxComp at hfL hfR; rw [hfL, hfR]; simp [embedZ4cVec1DTo3D, hc']
      rw [hFaceEq, hFaceEq]; simp [embedZ4cVec1DTo3D, hc']
    have hSrcNe3 : BssnZ4cConstraint3D.spec.sources.isEmpty = false := by decide +kernel
    have hSrcNe1 : BonaMassoZ4c1D.spec.sources.isEmpty = false := by decide +kernel
    have hSchemeLt6 : ∀ kx ky kz c', kx < Nx → ky < Ny → kz < Nz → c' < 6 →
        BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' =
          BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx c' := by
      intro kx ky kz c' hkx hky hkz hc'
      change evalSchemeStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' =
        evalSchemeStepRat BonaMassoZ4c1D.spec .periodic [Nx] dt false W1D kx c'
      unfold evalSchemeStepRat; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show List.range ([Nx, Ny, Nz] : List Nat).length = [0, 1, 2] from rfl, show List.range ([Nx] : List Nat).length = [0] from rfl]
      simp only [List.map, evalAxisSchedule]
      change evalSourceStepRat BssnZ4cConstraint3D.spec dt Gxyz (kx * (Ny * Nz) + (ky * Nz + kz)) c' =
        evalSourceStepRat BonaMassoZ4c1D.spec dt (evalAxisStepRat BonaMassoZ4c1D.spec .periodic [Nx] 0 dt W1D) kx c'
      unfold evalSourceStepRat; rw [hSrcNe3, hSrcNe1]
      simp only [Bool.false_eq_true, ↓reduceIte, hGxyz_at kx ky kz hkx hky hkz, hCell1D_eq kx hkx c' hc']
      rw [bssn3d_source_matches_1d (cell1D kx) _ (hCell1D_eq kx hkx) c' hc']
    refine ⟨hSchemeLt6, fun hZero5 => ?_⟩
    have hCellGe5Zero : ∀ kx, kx < Nx → ∀ c', 5 ≤ c' → cell1D kx c' = 0 := by
      intro kx _ c' hc'; dsimp only [cell1D]; unfold evalAxisCellRat faceFlux4
      have hEmbZero : ∀ off : Int, ∀ j, 5 ≤ j → embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + off))) j = 0 := by
        intro off j hj; by_cases hj6 : j < 6
        · have hj5 : j = 5 := by omega
          subst hj5; simp [embedZ4cVec1DTo3D, hZero5 _ (resolveStencilIdx_lt .periodic Nx hNx _)]
        · simp [embedZ4cVec1DTo3D, hj6]
      have hSlZ : ∀ o1 o2 o3 : Int, ∀ j, 5 ≤ j →
          slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
            (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))))
            (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o3)))) j = 0 :=
        fun _ _ _ j hj => by simp [slopeAt, hLim3, hEmbZero _ j hj, minmod_self, Rat.sub_self]
      have hRusZ : ∀ o0 o1 o2 o3 : Int,
          rusanovNonlinearFlux (getOr BssnZ4cConstraint3D.spec.fluxes 0 []) BssnZ4cConstraint3D.spec.paramEnv BssnZ4cConstraint3D.spec.aMax
            (fun j => embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))) j + (1 / 2 : Rat) *
              slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o0))))
                (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
                (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2)))) j)
            (fun j => embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))) j - (1 / 2 : Rat) *
              slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
                (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))))
                (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o3)))) j) c' = 0 := by
        intro o0 o1 o2 o3; unfold rusanovNonlinearFlux
        have hLZ : ∀ j, 5 ≤ j → embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))) j + (1 / 2 : Rat) *
            slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o0))))
              (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
              (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2)))) j = 0 := fun j hj => by rw [hEmbZero _ j hj, hSlZ o0 o1 o2 j hj]; grind
        have hRZ : ∀ j, 5 ≤ j → embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))) j - (1 / 2 : Rat) *
            slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
              (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))))
              (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o3)))) j = 0 := fun j hj => by rw [hEmbZero _ j hj, hSlZ o1 o2 o3 j hj]; grind
        have hfL := (bssn3d_zero_constraints_flux_source _ hLZ c' hc').1; have hfR := (bssn3d_zero_constraints_flux_source _ hRZ c' hc').1
        unfold fluxComp at hfL hfR; rw [hfL, hfR]; dsimp only; rw [hLZ c' hc', hRZ c' hc']; grind
      dsimp only; rw [hRusZ, hRusZ, hEmbZero 0 c' hc']; grind
    have hStep3DGe5Zero : ∀ kx ky kz c', kx < Nx → ky < Ny → kz < Nz → 5 ≤ c' →
        BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' = 0 := by
      intro kx ky kz c' hkx hky hkz hc'
      change evalSchemeStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' = 0
      unfold evalSchemeStepRat; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show List.range ([Nx, Ny, Nz] : List Nat).length = [0, 1, 2] from rfl]; simp only [List.map, evalAxisSchedule]
      change evalSourceStepRat BssnZ4cConstraint3D.spec dt Gxyz (kx * (Ny * Nz) + (ky * Nz + kz)) c' = 0
      unfold evalSourceStepRat; rw [hSrcNe3]; simp only [Bool.false_eq_true, ↓reduceIte, hGxyz_at kx ky kz hkx hky hkz]
      rw [hCellGe5Zero kx hkx c' hc', (bssn3d_zero_constraints_flux_source (cell1D kx) (hCellGe5Zero kx hkx) c' hc').2]; grind
    refine ⟨fun kx hkx => by rw [← hSchemeLt6 kx 0 0 5 hkx hNy hNz (by decide)]; exact hStep3DGe5Zero kx 0 0 5 hkx hNy hNz (by decide),
            fun kx ky kz hkx hky hkz => funext fun c' => ?_⟩
    by_cases hc6 : c' < 6
    · simp [embedZ4cVec1DTo3D, hc6, hSchemeLt6 kx ky kz c' hkx hky hkz hc6]
    · simp [embedZ4cVec1DTo3D, hc6, hStep3DGe5Zero kx ky kz c' hkx hky hkz (by omega)]
  have hInitSlab : ∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz →
      embedZ4cPlanarSlab Ny Nz U1D (kx * (Ny * Nz) + (ky * Nz + kz)) = embedZ4cVec1DTo3D (U1D kx) :=
    fun kx ky kz _ hky hkz => by simp only [embedZ4cPlanarSlab, slab3d_div_eq Ny Nz kx ky kz hky hkz]
  refine ⟨fun hc => bssn3d_xflux_matches_1d u c hc, fun hc => (hStepCore _ U1D hInitSlab).1 ix iy iz c hix hiy hiz hc, fun hZero0 n => ?_⟩
  have hInv : ∀ (k : Nat) (G : MultiDGrid) (W1D : MultiDGrid), (∀ kx, kx < Nx → W1D kx 5 = 0) →
      (∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz → G (kx * (Ny * Nz) + (ky * Nz + kz)) = embedZ4cVec1DTo3D (W1D kx)) →
      ∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz →
        pdeGridRollout (BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false) k G (kx * (Ny * Nz) + (ky * Nz + kz)) =
          embedZ4cVec1DTo3D (pdeGridRollout (BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false) k W1D kx) := by
    intro k; induction k with
    | zero => intro G W1D _ hSl kx ky kz hkx hky hkz; exact hSl kx ky kz hkx hky hkz
    | succ k ih => intro G W1D hZ5 hSl kx ky kz hkx hky hkz; obtain ⟨hZ5', hSl'⟩ := (hStepCore G W1D hSl).2 hZ5; exact ih _ _ hZ5' hSl' kx ky kz hkx hky hkz
  exact congrFun (hInv n _ U1D hZero0 hInitSlab ix iy iz hix hiy hiz) c

/-! ## 7. Spatially Varying Coefficient Friedrichs Commutator & Open-Box Strand SBP + Olsson–Strand SAT Boundaries -/
/-- Spatially inhomogeneous `(α(x), β^i(x))` parameter field on a periodic 3D grid with Lipschitz discrete differences. -/
structure VariableGaugeField3D (dims : List Nat) (dx alphaMin a lGauge : Rat) (gField : Nat → Z4c3DParams) : Prop where
  (alphaMin_pos : 0 < alphaMin) (lGauge_nonneg : 0 ≤ lGauge)
  lapse_lower : ∀ idx, idx < gridCellCount dims → alphaMin ≤ (gField idx).alpha
  speed_bound : ∀ idx d, idx < gridCellCount dims → d < 3 → ratAbs ((gField idx).shiftAxis d) + (gField idx).alpha ≤ a
  grad_alpha_lip : ∀ d idx, d < 3 → idx < gridCellCount dims → ratAbs ((gField (axisPeriodicNeighbor dims d true idx)).alpha - (gField idx).alpha) ≤ lGauge * dx
  grad_shift_lip : ∀ d idx, d < 3 → idx < gridCellCount dims → ratAbs ((gField (axisPeriodicNeighbor dims d true idx)).shiftAxis d - (gField idx).shiftAxis d) ≤ lGauge * dx
def z4c3dVarGaugeSemiDiscreteRhs (gField : Nat → Z4c3DParams) (dims : List Nat) (dx : Rat) (C : MultiDGrid) : MultiDGrid :=
  fun idx c => mulVec 5 (z4c3dSourceMat (gField idx)) (C idx) c - sumTo 3 fun d => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx C idx) c
def z4c3dVarGaugeAxisStep (gField : Nat → Z4c3DParams) (dims : List Nat) (a ν : Rat) (d : Nat) (U : MultiDGrid) : MultiDGrid :=
  if d < dims.length then fun idx c =>
    let uNext := U (axisPeriodicNeighbor dims d true idx); let uPrev := U (axisPeriodicNeighbor dims d false idx)
    U idx c - (ν / 2) * mulVec 5 (z4c3dFluxMat (gField idx) d) (fun j => uNext j - uPrev j) c + (ν * a / 2) * (uNext c - 2 * U idx c + uPrev c)
  else U
def z4c3dVarGaugeSweep (gField : Nat → Z4c3DParams) (dims : List Nat) (a ν : Rat) (U : MultiDGrid) : MultiDGrid :=
  z4c3dVarGaugeAxisStep gField dims a ν 2 (z4c3dVarGaugeAxisStep gField dims a ν 1 (z4c3dVarGaugeAxisStep gField dims a ν 0 U))
@[expose] def z4c3dVarGaugeRollout (gField : Nat → Z4c3DParams) (dims : List Nat) (a dx dt : Rat) (n : Nat) (U : MultiDGrid) : MultiDGrid :=
  match n with
  | 0 => U
  | k + 1 => let U1 := z4c3dVarGaugeSweep gField dims a (dt / dx) U; z4c3dVarGaugeRollout gField dims a dx dt k (fun idx c => U1 idx c + dt * mulVec 5 (z4c3dSourceMat (gField idx)) (U1 idx) c)
termination_by structural n
private theorem ratAbs_eq_pde (x : Rat) : ratAbs x = PdeSexprAndApprox.ratAbs x := by unfold ratAbs PdeSexprAndApprox.ratAbs; split <;> split <;> grind (ematch := 0)
private theorem z4c3dSymmetrizer_symm : ∀ i j, i < 5 → j < 5 → z4c3dSymmetrizer i j = z4c3dSymmetrizer j i := by
  intro i j hi hj; have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := (by omega); have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := (by omega)
  rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem z4c3dSymmetrizer_nonneg (v : Vec) : 0 ≤ h0Inner 5 z4c3dSymmetrizer v v := by
  rw [z4c3dSymmetrizer_quadratic_form]; have := rat_mul_self_nonneg (v 0); have := rat_mul_self_nonneg (v 1)
  have := rat_mul_self_nonneg (v 2); have := rat_mul_self_nonneg (v 3); have := rat_mul_self_nonneg (v 4); grind (ematch := 0)
private theorem z4c3dFluxMat_self_adjoint (p : Z4c3DParams) (d : Nat) (hd : d < 3) (u v : Vec) :
    h0Inner 5 z4c3dSymmetrizer u (mulVec 5 (z4c3dFluxMat p d) v) = h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dFluxMat p d) u) v := by
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := (by omega)
  rcases hd3 with rfl | rfl | rfl <;> (simp only [h0Inner, dot, mulVec, z4c3dSymmetrizer, z4c3dSymmetrizerRows, z4c3dFluxMat, z4c3dFluxRows, matOf, getOr, sumTo]; grind (ematch := 0))
private theorem z4c3d_flux_diff_bilinear_bound (pR pL : Z4c3DParams) (d : Nat) (hd : d < 3) (u w : Vec) :
    ratAbs (h0Inner 5 z4c3dSymmetrizer u (mulVec 5 (fun i j => z4c3dFluxMat pR d i j - z4c3dFluxMat pL d i j) w)) ≤
      (ratAbs (pR.alpha - pL.alpha) + ratAbs (pR.shiftAxis d - pL.shiftAxis d)) * ((1 / 2 : Rat) * (h0Inner 5 z4c3dSymmetrizer u u + h0Inner 5 z4c3dSymmetrizer w w)) := by
  simp only [ratAbs_eq_pde]; rw [z4c3dSymmetrizer_quadratic_form u, z4c3dSymmetrizer_quadratic_form w]
  have s0p := rat_mul_self_nonneg (u 0 + w 0); have s0m := rat_mul_self_nonneg (u 0 - w 0); have s1p := rat_mul_self_nonneg (u 1 + w 1); have s1m := rat_mul_self_nonneg (u 1 - w 1)
  have s2p := rat_mul_self_nonneg (u 2 + w 2); have s2m := rat_mul_self_nonneg (u 2 - w 2); have s3p := rat_mul_self_nonneg (u 3 + w 3); have s3m := rat_mul_self_nonneg (u 3 - w 3)
  have s4p := rat_mul_self_nonneg (u 4 + w 4); have s4m := rat_mul_self_nonneg (u 4 - w 4)
  have hShiftPair : PdeSexprAndApprox.ratAbs (4 * u 0 * w 0 + 8 * u 1 * w 1 + 8 * u 2 * w 2 + 8 * u 3 * w 3 + u 4 * w 4) ≤
      (1 / 2 : Rat) * ((4 * (u 0 * u 0) + 8 * (u 1 * u 1) + 8 * (u 2 * u 2) + 8 * (u 3 * u 3) + u 4 * u 4) +
        (4 * (w 0 * w 0) + 8 * (w 1 * w 1) + 8 * (w 2 * w 2) + 8 * (w 3 * w 3) + w 4 * w 4)) := ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩
  have c1p := rat_mul_self_nonneg (2 * u 0 + 2 * w (d + 1)); have c1m := rat_mul_self_nonneg (2 * u 0 - 2 * w (d + 1))
  have c2p := rat_mul_self_nonneg (2 * u (d + 1) + 2 * w 0); have c2m := rat_mul_self_nonneg (2 * u (d + 1) - 2 * w 0)
  have c3p := rat_mul_self_nonneg (2 * u (d + 1) + w 4); have c3m := rat_mul_self_nonneg (2 * u (d + 1) - w 4)
  have c4p := rat_mul_self_nonneg (u 4 + 2 * w (d + 1)); have c4m := rat_mul_self_nonneg (u 4 - 2 * w (d + 1))
  have u1sq := rat_mul_self_nonneg (u 1); have u2sq := rat_mul_self_nonneg (u 2); have u3sq := rat_mul_self_nonneg (u 3)
  have w1sq := rat_mul_self_nonneg (w 1); have w2sq := rat_mul_self_nonneg (w 2); have w3sq := rat_mul_self_nonneg (w 3)
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  have hAlphaPair : PdeSexprAndApprox.ratAbs (4 * u 0 * w (d + 1) + 4 * u (d + 1) * w 0 + 2 * u (d + 1) * w 4 + 2 * u 4 * w (d + 1)) ≤
      (1 / 2 : Rat) * ((4 * (u 0 * u 0) + 8 * (u 1 * u 1) + 8 * (u 2 * u 2) + 8 * (u 3 * u 3) + u 4 * u 4) +
        (4 * (w 0 * w 0) + 8 * (w 1 * w 1) + 8 * (w 2 * w 2) + 8 * (w 3 * w 3) + w 4 * w 4)) := by rcases hd3 with rfl | rfl | rfl <;> exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩
  have hId : h0Inner 5 z4c3dSymmetrizer u (mulVec 5 (fun i j => z4c3dFluxMat pR d i j - z4c3dFluxMat pL d i j) w) =
      (pR.alpha - pL.alpha) * (4 * u 0 * w (d + 1) + 4 * u (d + 1) * w 0 + 2 * u (d + 1) * w 4 + 2 * u 4 * w (d + 1)) +
      (-(pR.shiftAxis d - pL.shiftAxis d)) * (4 * u 0 * w 0 + 8 * u 1 * w 1 + 8 * u 2 * w 2 + 8 * u 3 * w 3 + u 4 * w 4) := by
    rcases hd3 with rfl | rfl | rfl <;> (simp only [h0Inner, dot, mulVec, z4c3dSymmetrizer, z4c3dSymmetrizerRows, z4c3dFluxMat, z4c3dFluxRows, Z4c3DParams.shiftAxis, matOf, getOr, sumTo]; grind)
  rw [hId]; have ht := NonlinearMultiDPde.ratAbs_add_le
    ((pR.alpha - pL.alpha) * (4 * u 0 * w (d + 1) + 4 * u (d + 1) * w 0 + 2 * u (d + 1) * w 4 + 2 * u 4 * w (d + 1)))
    ((-(pR.shiftAxis d - pL.shiftAxis d)) * (4 * u 0 * w 0 + 8 * u 1 * w 1 + 8 * u 2 * w 2 + 8 * u 3 * w 3 + u 4 * w 4))
  rw [ratAbs_mul, ratAbs_mul, ratAbs_neg] at ht
  have := rat_mul_mono (PdeSexprAndApprox.ratAbs_nonneg (pR.alpha - pL.alpha)) hAlphaPair
  have := rat_mul_mono (PdeSexprAndApprox.ratAbs_nonneg (pR.shiftAxis d - pL.shiftAxis d)) hShiftPair; grind
private theorem mulVec_mat_sub (A B : Mat) (v : Vec) : vecSub (mulVec 5 A v) (mulVec 5 B v) = mulVec 5 (fun i c => A i c - B i c) v := by
  funext i; unfold vecSub mulVec
  rw [show sumTo 5 (fun c => A i c * v c) - sumTo 5 (fun c => B i c * v c) = sumTo 5 (fun c => A i c * v c) + (-1) * sumTo 5 (fun c => B i c * v c) by grind,
      ← sumTo_mul_left, ← sumTo_add]; exact sumTo_congr fun c _ => by grind
private theorem ring_var_flux_commutator (N : Nat) (hN : 0 < N) (H0 : Mat)
    (hSymm : ∀ i j, i < 5 → j < 5 → H0 i j = H0 j i) (A : Nat → Mat)
    (hAdj : ∀ k u v, h0Inner 5 H0 u (mulVec 5 (A k) v) = h0Inner 5 H0 (mulVec 5 (A k) u) v) (u : Nat → Vec) :
    sumTo N (fun k => h0Inner 5 H0 (u k) (mulVec 5 (A k) (vecSub (u (nextCell N k)) (u (prevCell N k))))) =
    -(sumTo N fun k => h0Inner 5 H0 (u k) (mulVec 5 (fun i j => A (nextCell N k) i j - A k i j) (u (nextCell N k)))) := by
  have hSubS : ∀ a b : Nat → Rat, sumTo N (fun k => a k - b k) = sumTo N a - sumTo N b :=
    fun a b => by rw [show (fun k => a k - b k) = (fun k => a k + (-1) * b k) by funext k; grind, sumTo_add, sumTo_mul_left]; grind
  have hSp : ∀ k, h0Inner 5 H0 (u k) (mulVec 5 (A k) (vecSub (u (nextCell N k)) (u (prevCell N k)))) =
      h0Inner 5 H0 (u k) (mulVec 5 (A k) (u (nextCell N k))) - h0Inner 5 H0 (u k) (mulVec 5 (A k) (u (prevCell N k))) := fun k => by
    rw [show vecSub (u (nextCell N k)) (u (prevCell N k)) = (fun c => 1 * u (nextCell N k) c + (-1) * u (prevCell N k) c) by funext c; dsimp [vecSub]; grind,
        show mulVec 5 (A k) (fun c => 1 * u (nextCell N k) c + (-1) * u (prevCell N k) c) =
          (fun i => 1 * mulVec 5 (A k) (u (nextCell N k)) i + (-1) * mulVec 5 (A k) (u (prevCell N k)) i) by
          funext i; exact mulVec_lin _ _ _ _ _ _ i, h0Inner_lin_right]; grind
  have hSh : sumTo N (fun k => h0Inner 5 H0 (u k) (mulVec 5 (A k) (u (prevCell N k)))) =
      sumTo N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (A (nextCell N j)) (u (nextCell N j)))) := by
    rw [sumTo_congr (fun k hk => show h0Inner 5 H0 (u k) (mulVec 5 (A k) (u (prevCell N k))) =
          h0Inner 5 H0 (u (nextCell N (prevCell N k))) (mulVec 5 (A (nextCell N (prevCell N k))) (u (prevCell N k))) by rw [nextCell_prevCell N k hN hk]),
        sumTo_prev N (fun j => h0Inner 5 H0 (u (nextCell N j)) (mulVec 5 (A (nextCell N j)) (u j)))]
    exact sumTo_congr fun j _ => by rw [hAdj (nextCell N j), h0Inner_symm hSymm]
  have hEach : ∀ k, h0Inner 5 H0 (u k) (mulVec 5 (A k) (u (nextCell N k))) - h0Inner 5 H0 (u k) (mulVec 5 (A (nextCell N k)) (u (nextCell N k))) =
      (-1 : Rat) * h0Inner 5 H0 (u k) (mulVec 5 (fun i j => A (nextCell N k) i j - A k i j) (u (nextCell N k))) := fun k => by
    rw [← mulVec_mat_sub (A (nextCell N k)) (A k) (u (nextCell N k)), h0Inner_sub_right]; grind
  rw [sumTo_congr (fun k _ => hSp k), hSubS, hSh, ← hSubS, sumTo_congr (fun k _ => hEach k), sumTo_mul_left]; grind
private def lfMid1D (N : Nat) (p q : Rat) (u : Nat → Vec) (k : Nat) : Vec :=
  fun c => p * u k c + q * u (nextCell N k) c + q * u (prevCell N k) c
private def lfFlux1D (N : Nat) (ν : Rat) (A : Nat → Mat) (u : Nat → Vec) (k : Nat) : Vec :=
  vecScale (ν / 2) (mulVec 5 (A k) (vecSub (u (nextCell N k)) (u (prevCell N k))))
private theorem z4c3d_var_gauge_1d_ring_step (N : Nat) (hN : 0 < N)
    (a dx dt lGauge : Rat) (ha : 0 ≤ a) (hdx0 : dx ≠ 0) (hν : 0 ≤ dt / dx) (hνa : (dt / dx) * a ≤ 1)
    (H0 : Mat) (hSymm : ∀ i j, i < 5 → j < 5 → H0 i j = H0 j i) (hNN : ∀ v, 0 ≤ h0Inner 5 H0 v v)
    (A : Nat → Mat) (hAdj : ∀ k u v, h0Inner 5 H0 u (mulVec 5 (A k) v) = h0Inner 5 H0 (mulVec 5 (A k) u) v) (u : Nat → Vec)
    (hSp : ∀ k, k < N → ∀ w : Vec, h0Inner 5 H0 (mulVec 5 (A k) w) (mulVec 5 (A k) w) ≤ (a * a) * h0Inner 5 H0 w w)
    (hEdge : ∀ k, k < N → ∀ x w : Vec,
      PdeSexprAndApprox.ratAbs (h0Inner 5 H0 x (mulVec 5 (fun i j => A (nextCell N k) i j - A k i j) w)) ≤
      (lGauge * dx) * (h0Inner 5 H0 x x + h0Inner 5 H0 w w)) :
    let ν := dt / dx; let p := 1 - ν * a; let q := ν * a / 2
    sumTo N (fun k => h0Inner 5 H0 (vecSub (lfMid1D N p q u k) (lfFlux1D N ν A u k)) (vecSub (lfMid1D N p q u k) (lfFlux1D N ν A u k))) ≤
      (1 + 2 * lGauge * dt) * sumTo N (fun k => h0Inner 5 H0 (u k) (u k)) := by
  intro ν p q
  have hp_nn : 0 ≤ p := (by dsimp [p]; grind (ematch := 0))
  have hq_nn : 0 ≤ q := (by dsimp [q]; have := Rat.mul_nonneg hν ha; grind (ematch := 0))
  have hpq : p + 2 * q = 1 := (by dsimp [p, q]; grind (ematch := 0))
  have hExp : ∀ k, k < N → h0Inner 5 H0 (vecSub (lfMid1D N p q u k) (lfFlux1D N ν A u k)) (vecSub (lfMid1D N p q u k) (lfFlux1D N ν A u k)) =
      (h0Inner 5 H0 (lfMid1D N p q u k) (lfMid1D N p q u k) + h0Inner 5 H0 (lfFlux1D N ν A u k) (lfFlux1D N ν A u k)) +
      (-2 : Rat) * h0Inner 5 H0 (lfMid1D N p q u k) (lfFlux1D N ν A u k) := fun k _ => by
    rw [h0Inner_sub_left, h0Inner_sub_right, h0Inner_sub_right, h0Inner_symm hSymm (lfFlux1D N ν A u k) (lfMid1D N p q u k)]; grind (ematch := 0)
  rw [sumTo_congr hExp, sumTo_add, sumTo_mul_left]
  have hSubS : ∀ x y : Nat → Rat, sumTo N (fun k => x k - y k) = sumTo N x - sumTo N y :=
    fun x y => by rw [show (fun k => x k - y k) = (fun k => x k + (-1) * y k) by funext k; grind (ematch := 0), sumTo_add, sumTo_mul_left]; grind (ematch := 0)
  have hMF_diag : sumTo N (fun k => h0Inner 5 H0 (lfMid1D N p q u k) (lfMid1D N p q u k) + h0Inner 5 H0 (lfFlux1D N ν A u k) (lfFlux1D N ν A u k)) ≤
      sumTo N (fun k => h0Inner 5 H0 (u k) (u k)) := by
    rw [sumTo_add]
    have hPtM : ∀ k, h0Inner 5 H0 (lfMid1D N p q u k) (lfMid1D N p q u k) ≤
        (p * h0Inner 5 H0 (u k) (u k) + q * h0Inner 5 H0 (u (nextCell N k)) (u (nextCell N k)) +
          q * h0Inner 5 H0 (u (prevCell N k)) (u (prevCell N k))) -
        (q * q) * h0Inner 5 H0 (vecSub (u (nextCell N k)) (u (prevCell N k))) (vecSub (u (nextCell N k)) (u (prevCell N k))) := fun k => by
      have hid := h0Inner_three_convex_identity hSymm p q hpq (u k) (u (nextCell N k)) (u (prevCell N k))
      have := Rat.mul_nonneg (Rat.mul_nonneg hp_nn hq_nn) (hNN (vecSub (u k) (u (nextCell N k))))
      have := Rat.mul_nonneg (Rat.mul_nonneg hp_nn hq_nn) (hNN (vecSub (u k) (u (prevCell N k))))
      unfold lfMid1D; grind (ematch := 0)
    have hPtF : ∀ k, k < N → h0Inner 5 H0 (lfFlux1D N ν A u k) (lfFlux1D N ν A u k) ≤
        (q * q) * h0Inner 5 H0 (vecSub (u (nextCell N k)) (u (prevCell N k))) (vecSub (u (nextCell N k)) (u (prevCell N k))) := fun k hk => by
      let w := vecSub (u (nextCell N k)) (u (prevCell N k))
      unfold lfFlux1D; rw [h0Inner_scale_left, h0Inner_scale_right]
      have h1 := Rat.mul_le_mul_of_nonneg_left (hSp k hk w) (Rat.le_of_lt (show (0 : Rat) < 1 by decide) |> fun _ => Rat.mul_nonneg (show 0 ≤ ν / 2 by grind (ematch := 0)) (show 0 ≤ ν / 2 by grind (ematch := 0)))
      have h2 : ((ν / 2) * (ν / 2)) * ((a * a) * h0Inner 5 H0 w w) = (q * q) * h0Inner 5 H0 w w := by dsimp only [q]; grind (ematch := 0)
      dsimp only [w] at h1 h2; grind (ematch := 0)
    have hsM := sumTo_le (n := N) (fun k _ => hPtM k); have hsF := sumTo_le hPtF
    rw [hSubS, sumTo_shift3 N p q q (fun k => h0Inner 5 H0 (u k) (u k)), show p + q + q = 1 by grind (ematch := 0), Rat.one_mul] at hsM; grind (ematch := 0)
  have hCrossBound : (-2 : Rat) * sumTo N (fun k => h0Inner 5 H0 (lfMid1D N p q u k) (lfFlux1D N ν A u k)) ≤
      (2 * lGauge * dt) * sumTo N (fun k => h0Inner 5 H0 (u k) (u k)) := by
    have hSplitMF : ∀ k, h0Inner 5 H0 (lfMid1D N p q u k) (lfFlux1D N ν A u k) =
        (p * (ν / 2)) * h0Inner 5 H0 (u k) (mulVec 5 (A k) (vecSub (u (nextCell N k)) (u (prevCell N k)))) +
        (q * (ν / 2)) * (h0Inner 5 H0 (u (nextCell N k)) (mulVec 5 (A k) (u (nextCell N k))) -
          h0Inner 5 H0 (u (prevCell N k)) (mulVec 5 (A k) (u (prevCell N k)))) := fun k => by
      rw [show lfMid1D N p q u k = (fun c => p * u k c + q * vecAdd (u (nextCell N k)) (u (prevCell N k)) c) by funext c; unfold lfMid1D vecAdd; grind (ematch := 0),
          lfFlux1D, h0Inner_lin_left, h0Inner_scale_right, h0Inner_scale_right]
      have hDiffSq : h0Inner 5 H0 (vecAdd (u (nextCell N k)) (u (prevCell N k))) (mulVec 5 (A k) (vecSub (u (nextCell N k)) (u (prevCell N k)))) =
          h0Inner 5 H0 (u (nextCell N k)) (mulVec 5 (A k) (u (nextCell N k))) -
          h0Inner 5 H0 (u (prevCell N k)) (mulVec 5 (A k) (u (prevCell N k))) := by
        rw [h0Inner_add_left, show vecSub (u (nextCell N k)) (u (prevCell N k)) =
            (fun c => 1 * u (nextCell N k) c + (-1) * u (prevCell N k) c) by funext c; dsimp [vecSub]; grind (ematch := 0),
          show mulVec 5 (A k) (fun c => 1 * u (nextCell N k) c + (-1) * u (prevCell N k) c) =
            (fun i => 1 * mulVec 5 (A k) (u (nextCell N k)) i + (-1) * mulVec 5 (A k) (u (prevCell N k)) i) by funext i; exact mulVec_lin _ _ _ _ _ _ i,
          h0Inner_lin_right, h0Inner_lin_right, hAdj k (u (prevCell N k)) (u (nextCell N k)),
          h0Inner_symm hSymm (mulVec 5 (A k) (u (prevCell N k))) (u (nextCell N k))]; grind (ematch := 0)
      rw [hDiffSq]; grind (ematch := 0)
    rw [sumTo_congr (fun k _ => hSplitMF k), sumTo_add, sumTo_mul_left, sumTo_mul_left, ring_var_flux_commutator N hN H0 hSymm A hAdj u]
    have hTerm2 : sumTo N (fun k => h0Inner 5 H0 (u (nextCell N k)) (mulVec 5 (A k) (u (nextCell N k))) -
          h0Inner 5 H0 (u (prevCell N k)) (mulVec 5 (A k) (u (prevCell N k)))) =
        -(sumTo N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (fun i c => A j i c - A (prevCell N j) i c) (u j))) +
          sumTo N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (fun i c => A (nextCell N j) i c - A j i c) (u j)))) := by
      rw [hSubS, sumTo_congr (fun k _ => show h0Inner 5 H0 (u (nextCell N k)) (mulVec 5 (A k) (u (nextCell N k))) =
            h0Inner 5 H0 (u (nextCell N k)) (mulVec 5 (A (prevCell N (nextCell N k))) (u (nextCell N k))) by rw [prevCell_nextCell N k]),
        sumTo_next N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (A (prevCell N j)) (u j))),
        sumTo_congr (fun k hk => show h0Inner 5 H0 (u (prevCell N k)) (mulVec 5 (A k) (u (prevCell N k))) =
            h0Inner 5 H0 (u (prevCell N k)) (mulVec 5 (A (nextCell N (prevCell N k))) (u (prevCell N k))) by rw [nextCell_prevCell N k hN hk]),
        sumTo_prev N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (A (nextCell N j)) (u j))), ← hSubS]
      have hEach2 : ∀ j, h0Inner 5 H0 (u j) (mulVec 5 (A (prevCell N j)) (u j)) - h0Inner 5 H0 (u j) (mulVec 5 (A (nextCell N j)) (u j)) =
          (-1 : Rat) * (h0Inner 5 H0 (u j) (mulVec 5 (fun i c => A j i c - A (prevCell N j) i c) (u j)) +
            h0Inner 5 H0 (u j) (mulVec 5 (fun i c => A (nextCell N j) i c - A j i c) (u j))) := fun j => by
        rw [← mulVec_mat_sub (A j) (A (prevCell N j)) (u j), ← mulVec_mat_sub (A (nextCell N j)) (A j) (u j), h0Inner_sub_right, h0Inner_sub_right]; grind (ematch := 0)
      rw [sumTo_congr (fun j _ => hEach2 j), sumTo_mul_left, sumTo_add]; grind (ematch := 0)
    let S := sumTo N (fun k => h0Inner 5 H0 (u k) (u k))
    have hB1 : sumTo N (fun k => h0Inner 5 H0 (u k) (mulVec 5 (fun i j => A (nextCell N k) i j - A k i j) (u (nextCell N k)))) ≤ (2 * lGauge * dx) * S := by
      have hs := sumTo_le (n := N) fun k hk => (ratAbs_bounds_iff.mp (hEdge k hk (u k) (u (nextCell N k)))).2
      rw [sumTo_mul_left, sumTo_add, sumTo_next N (fun k => h0Inner 5 H0 (u k) (u k))] at hs; dsimp only [S]; grind (ematch := 0)
    have hB2a : sumTo N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (fun i c => A j i c - A (prevCell N j) i c) (u j))) ≤ (2 * lGauge * dx) * S := by
      have hs := sumTo_le (n := N) fun j hj => by
        have hb := hEdge (prevCell N j) (prevCell_lt N j hj) (u j) (u j); rw [nextCell_prevCell N j hN hj] at hb; exact (ratAbs_bounds_iff.mp hb).2
      rw [sumTo_mul_left, sumTo_add] at hs; dsimp only [S]; grind (ematch := 0)
    have hB2b : sumTo N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (fun i c => A (nextCell N j) i c - A j i c) (u j))) ≤ (2 * lGauge * dx) * S := by
      have hs := sumTo_le (n := N) fun j hj => (ratAbs_bounds_iff.mp (hEdge j hj (u j) (u j))).2
      rw [sumTo_mul_left, sumTo_add] at hs; dsimp only [S]; grind (ematch := 0)
    rw [hTerm2]
    have hB2 : sumTo N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (fun i c => A j i c - A (prevCell N j) i c) (u j))) +
        sumTo N (fun j => h0Inner 5 H0 (u j) (mulVec 5 (fun i c => A (nextCell N j) i c - A j i c) (u j))) ≤ (2 * lGauge * dx) * S + (2 * lGauge * dx) * S := by grind (ematch := 0)
    have hm1 := rat_mul_mono (Rat.mul_nonneg hp_nn (show 0 ≤ ν / 2 by grind (ematch := 0))) hB1
    have hm2 := rat_mul_mono (Rat.mul_nonneg hq_nn (show 0 ≤ ν / 2 by grind (ematch := 0))) hB2
    have hcNu : ν * dx = dt := Rat.div_mul_cancel hdx0 (a := dt)
    have hComb : (-2 : Rat) * ((p * (ν / 2)) * -((2 * lGauge * dx) * S) + (q * (ν / 2)) * -((2 * lGauge * dx) * S + (2 * lGauge * dx) * S)) =
        (2 * lGauge * dt) * S := by rw [← hcNu]; have := hpq; grind (ematch := 0)
    dsimp only [S] at hm1 hm2 hComb ⊢; grind (ematch := 0)
  grind (ematch := 0)
private theorem z4c3d_var_gauge_axis_commutator_and_step (dims : List Nat) (hDims : dims.length = 3)
    (hPos : ∀ N ∈ dims, 0 < N) (dx alphaMin a lGauge : Rat) (hdx : 0 < dx)
    (gField : Nat → Z4c3DParams) (hG : VariableGaugeField3D dims dx alphaMin a lGauge gField) (d : Nat) (hd : d < 3) (U : MultiDGrid) :
    ratAbs (multiDH0Pair dims 5 z4c3dSymmetrizer U (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx U idx))) ≤
      lGauge * multiDH0Energy dims 5 z4c3dSymmetrizer U ∧
    ∀ dt : Rat, 0 ≤ dt → dt * a ≤ dx →
      multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dVarGaugeAxisStep gField dims a (dt / dx) d U) ≤
        (1 + 2 * lGauge * dt) * multiDH0Energy dims 5 z4c3dSymmetrizer U := by
  have hAxis : d < dims.length := (by omega); have hdx0 : dx ≠ 0 := (by grind (ematch := 0))
  let f := axisFiberDims dims d; have hN : 0 < f.axisLen := hPos _ (getOr_mem_of_lt dims d 1 hAxis)
  have hCellLt : ∀ o k r, o < f.outer → k < f.axisLen → r < f.inner → o * (f.axisLen * f.inner) + (k * f.inner + r) < gridCellCount dims := by
    intro o k r ho hk hr; rw [axisFiberDims_prod dims d hAxis]
    have hkr : k * f.inner + r < f.axisLen * f.inner := by have h2 := Nat.mul_le_mul_right f.inner (show k + 1 ≤ f.axisLen by omega); rw [Nat.add_mul, Nat.one_mul] at h2; omega
    have ho2 := Nat.mul_le_mul_right (f.axisLen * f.inner) (show o + 1 ≤ f.outer by omega); rw [Nat.add_mul, Nat.one_mul] at ho2; dsimp only [f] at *; omega
  have hEdgeDiff : ∀ o k r, o < f.outer → k < f.axisLen → r < f.inner →
      let c0 := o * (f.axisLen * f.inner) + (k * f.inner + r); let c1 := o * (f.axisLen * f.inner) + (nextCell f.axisLen k * f.inner + r)
      ∀ u w : Vec, PdeSexprAndApprox.ratAbs (h0Inner 5 z4c3dSymmetrizer u (mulVec 5 (fun i j => z4c3dFluxMat (gField c1) d i j - z4c3dFluxMat (gField c0) d i j) w)) ≤
        (lGauge * dx) * (h0Inner 5 z4c3dSymmetrizer u u + h0Inner 5 z4c3dSymmetrizer w w) := by
    intro o k r ho hk hr c0 c1 u w; have hc0Lt := hCellLt o k r ho hk hr
    have hNextEq : axisPeriodicNeighbor dims d true c0 = c1 := by simpa only [↓reduceIte] using axisPeriodicNeighbor_fiber dims d true hAxis hPos o k r hk hr
    have hb := z4c3d_flux_diff_bilinear_bound (gField c1) (gField c0) d hd u w
    have hga := hG.grad_alpha_lip d c0 hd hc0Lt; rw [hNextEq] at hga
    have hgs := hG.grad_shift_lip d c0 hd hc0Lt; rw [hNextEq] at hgs
    have hE_nn : 0 ≤ (1 / 2 : Rat) * (h0Inner 5 z4c3dSymmetrizer u u + h0Inner 5 z4c3dSymmetrizer w w) := by
      have := z4c3dSymmetrizer_nonneg u; have := z4c3dSymmetrizer_nonneg w; grind (ematch := 0)
    simp only [ratAbs_eq_pde] at hb hga hgs ⊢
    have := rat_mul_mono hE_nn (show PdeSexprAndApprox.ratAbs ((gField c1).alpha - (gField c0).alpha) + PdeSexprAndApprox.ratAbs ((gField c1).shiftAxis d - (gField c0).shiftAxis d) ≤ 2 * (lGauge * dx) by grind (ematch := 0)); grind (ematch := 0)
  refine ⟨?_, fun dt hdt hcfl => ?_⟩
  · unfold multiDH0Pair multiDH0Energy centeredDiffAxis; simp only [hAxis, ↓reduceIte, ratAbs_eq_pde]
    rw [sumGrid_fibers dims d hAxis, sumGrid_fibers dims d hAxis]
    have hFib : ∀ o, o < f.outer → ∀ r, r < f.inner → PdeSexprAndApprox.ratAbs (sumTo f.axisLen fun k =>
          let cell := o * (f.axisLen * f.inner) + (k * f.inner + r)
          h0Inner 5 z4c3dSymmetrizer (U cell) (mulVec 5 (z4c3dFluxMat (gField cell) d)
            (fun c => (1 / (2 * dx)) * (U (axisPeriodicNeighbor dims d true cell) c - U (axisPeriodicNeighbor dims d false cell) c)))) ≤
        lGauge * sumTo f.axisLen (fun k => h0Inner 5 z4c3dSymmetrizer (U (o * (f.axisLen * f.inner) + (k * f.inner + r)))
          (U (o * (f.axisLen * f.inner) + (k * f.inner + r)))) := by
      intro o ho r hr; let cellAt := fun k => o * (f.axisLen * f.inner) + (k * f.inner + r)
      have hTerm : ∀ k, k < f.axisLen →
          h0Inner 5 z4c3dSymmetrizer (U (cellAt k)) (mulVec 5 (z4c3dFluxMat (gField (cellAt k)) d)
            (fun c => (1 / (2 * dx)) * (U (axisPeriodicNeighbor dims d true (cellAt k)) c - U (axisPeriodicNeighbor dims d false (cellAt k)) c))) =
          (1 / (2 * dx)) * h0Inner 5 z4c3dSymmetrizer (U (cellAt k))
            (mulVec 5 (z4c3dFluxMat (gField (cellAt k)) d) (vecSub (U (cellAt (nextCell f.axisLen k))) (U (cellAt (prevCell f.axisLen k))))) := by
        intro k hk
        rw [axisPeriodicNeighbor_fiber dims d true hAxis hPos o k r hk hr, axisPeriodicNeighbor_fiber dims d false hAxis hPos o k r hk hr]
        simp only [↓reduceIte, Bool.false_eq_true]
        rw [show (fun c => (1 / (2 * dx)) * (U (cellAt (nextCell f.axisLen k)) c - U (cellAt (prevCell f.axisLen k)) c)) =
            vecScale (1 / (2 * dx)) (vecSub (U (cellAt (nextCell f.axisLen k))) (U (cellAt (prevCell f.axisLen k)))) from rfl,
          show mulVec 5 (z4c3dFluxMat (gField (cellAt k)) d) (vecScale (1 / (2 * dx)) (vecSub (U (cellAt (nextCell f.axisLen k))) (U (cellAt (prevCell f.axisLen k))))) =
            vecScale (1 / (2 * dx)) (mulVec 5 (z4c3dFluxMat (gField (cellAt k)) d) (vecSub (U (cellAt (nextCell f.axisLen k))) (U (cellAt (prevCell f.axisLen k))))) by
            funext i; unfold vecScale mulVec; rw [← sumTo_mul_left]; exact sumTo_congr fun j _ => by grind (ematch := 0), h0Inner_scale_right]
      have hInvNN : 0 ≤ 1 / (2 * dx) := Rat.le_of_lt (rat_inv_one_div_pos (show 0 < 2 * dx by grind (ematch := 0)))
      rw [sumTo_congr hTerm, sumTo_mul_left,
          ring_var_flux_commutator f.axisLen hN z4c3dSymmetrizer z4c3dSymmetrizer_symm (fun k => z4c3dFluxMat (gField (cellAt k)) d) (fun k u v => z4c3dFluxMat_self_adjoint _ d hd u v) (fun k => U (cellAt k)),
          ratAbs_mul, ratAbs_of_nonneg hInvNN, ratAbs_neg]
      have hSumEdge := Rat.le_trans (ratAbs_sumTo_le f.axisLen _) (sumTo_le fun k hk => hEdgeDiff o k r ho hk hr (U (cellAt k)) (U (cellAt (nextCell f.axisLen k))))
      rw [sumTo_mul_left, sumTo_add, sumTo_next f.axisLen (fun k => h0Inner 5 z4c3dSymmetrizer (U (cellAt k)) (U (cellAt k)))] at hSumEdge
      have hm := rat_mul_mono hInvNN hSumEdge
      have hc2 := Rat.div_mul_cancel (show 2 * dx ≠ 0 by grind (ematch := 0)) (a := (1 : Rat))
      let S := sumTo f.axisLen (fun k => h0Inner 5 z4c3dSymmetrizer (U (cellAt k)) (U (cellAt k)))
      have hAlg : (1 / (2 * dx)) * ((lGauge * dx) * (S + S)) = lGauge * S := by
        calc (1 / (2 * dx)) * ((lGauge * dx) * (S + S)) = ((1 / (2 * dx)) * (2 * dx)) * (lGauge * S) := by grind (ematch := 0)
          _ = 1 * (lGauge * S) := by rw [hc2]
          _ = lGauge * S := by grind (ematch := 0)
      dsimp only [S] at hAlg; grind (ematch := 0)
    have hIn : ∀ o, o < f.outer → PdeSexprAndApprox.ratAbs (sumTo f.inner fun r => sumTo f.axisLen fun k => _) ≤ lGauge * sumTo f.inner (fun r => _) := fun o ho => by
      have hs := Rat.le_trans (ratAbs_sumTo_le f.inner _) (sumTo_le (hFib o ho)); rw [sumTo_mul_left] at hs; exact hs
    have hsO := Rat.le_trans (ratAbs_sumTo_le f.outer _) (sumTo_le hIn); rw [sumTo_mul_left] at hsO; exact hsO
  · have hν : 0 ≤ dt / dx := rat_le_of_mul_le_mul hdx (by rw [Rat.div_mul_cancel hdx0]; grind (ematch := 0))
    have hνa : (dt / dx) * a ≤ 1 := rat_le_of_mul_le_mul hdx (by calc ((dt / dx) * a) * dx = ((dt / dx) * dx) * a := by grind (ematch := 0)
      _ = dt * a := by rw [Rat.div_mul_cancel hdx0]
      _ ≤ 1 * dx := by grind (ematch := 0))
    unfold multiDH0Energy z4c3dVarGaugeAxisStep; simp only [hAxis, ↓reduceIte]
    rw [sumGrid_fibers dims d hAxis, sumGrid_fibers dims d hAxis, ← sumTo_mul_left]
    refine sumTo_le fun o ho => ?_; rw [← sumTo_mul_left]; refine sumTo_le fun r hr => ?_
    let cellAt := fun k => o * (f.axisLen * f.inner) + (k * f.inner + r)
    have ha : 0 ≤ a := by
      have hc0 := hCellLt o 0 r ho hN hr
      have := hG.lapse_lower (cellAt 0) hc0; have := hG.alphaMin_pos
      have hs0 := hG.speed_bound (cellAt 0) 0 hc0 (by decide)
      have := PdeSexprAndApprox.ratAbs_nonneg ((gField (cellAt 0)).shiftAxis 0)
      rw [ratAbs_eq_pde] at hs0; grind (ematch := 0)
    have hStepCell : ∀ k, k < f.axisLen →
        (fun c => U (cellAt k) c - ((dt / dx) / 2) * mulVec 5 (z4c3dFluxMat (gField (cellAt k)) d)
            (fun j => U (axisPeriodicNeighbor dims d true (cellAt k)) j - U (axisPeriodicNeighbor dims d false (cellAt k)) j) c +
          ((dt / dx) * a / 2) * (U (axisPeriodicNeighbor dims d true (cellAt k)) c - 2 * U (cellAt k) c + U (axisPeriodicNeighbor dims d false (cellAt k)) c)) =
        vecSub (lfMid1D f.axisLen (1 - (dt / dx) * a) ((dt / dx) * a / 2) (fun q => U (cellAt q)) k)
               (lfFlux1D f.axisLen (dt / dx) (fun q => z4c3dFluxMat (gField (cellAt q)) d) (fun q => U (cellAt q)) k) := by
      intro k hk; funext c
      rw [axisPeriodicNeighbor_fiber dims d true hAxis hPos o k r hk hr, axisPeriodicNeighbor_fiber dims d false hAxis hPos o k r hk hr]
      simp only [↓reduceIte, Bool.false_eq_true]; unfold lfMid1D lfFlux1D vecScale vecSub; dsimp only; grind (ematch := 0)
    rw [sumTo_congr fun k hk => by rw [hStepCell k hk]]
    exact z4c3d_var_gauge_1d_ring_step f.axisLen hN a dx dt lGauge ha hdx0 hν hνa
      z4c3dSymmetrizer z4c3dSymmetrizer_symm z4c3dSymmetrizer_nonneg
      (fun q => z4c3dFluxMat (gField (cellAt q)) d) (fun k u v => z4c3dFluxMat_self_adjoint _ d hd u v) (fun q => U (cellAt q))
      (fun k hk w => by
        have hcLt := hCellLt o k r ho hk hr
        have hAlNN : 0 ≤ (gField (cellAt k)).alpha := by have := hG.lapse_lower (cellAt k) hcLt; have := hG.alphaMin_pos; grind (ematch := 0)
        exact z4c3d_flux_speed_bound (gField (cellAt k)) a hAlNN
          (hG.speed_bound (cellAt k) 0 hcLt (by decide)) (hG.speed_bound (cellAt k) 1 hcLt (by decide)) (hG.speed_bound (cellAt k) 2 hcLt (by decide)) d hd w)
      (fun k hk => hEdgeDiff o k r ho hk hr)

/-- **Discrete Friedrichs Commutator & Spatially Varying `(α(x), β^i(x))` Energy Bound (`z4c3d_variable_gauge_commutator_energy_bound`)**:
On a periodic 3D grid with constant `H_0 = diag(4, 8, 8, 8, 1)` and spatially varying `(α(x), β^i(x), κ_1(x), κ_2(x))`
satisfying Lipschitz differences `|D_+ α| ≤ L_gauge`, `|D_+ β^d| ≤ L_gauge`, bounds the discrete skew-symmetry defect
by `3 · L_gauge · E(U)` without state-derivative loss, plus semi-discrete and dimensionally split Lax–Friedrichs + Euler rollout bounds. -/
theorem z4c3d_variable_gauge_commutator_energy_bound (dims : List Nat) (hDims : dims.length = 3)
    (hPos : ∀ N ∈ dims, 0 < N) (dx dt alphaMin a lGauge kappa1 rMax : Rat)
    (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : dt * a ≤ dx)
    (gField : Nat → Z4c3DParams) (hG : VariableGaugeField3D dims dx alphaMin a lGauge gField) (hK1 : 0 ≤ kappa1)
    (hGaugeDamp : ∀ idx, idx < gridCellCount dims → kappa1 ≤ (gField idx).kappa1 ∧ -1 ≤ (gField idx).kappa2 ∧ z4c3dMaxDampRate (gField idx) ≤ rMax)
    (hDampStep : dt * (rMax * rMax) ≤ kappa1 * alphaMin) (hEtaStep : (kappa1 * alphaMin) * dt ≤ 1)
    (n : Nat) (U U0 : MultiDGrid) :
    ratAbs (sumTo 3 fun d => multiDH0Pair dims 5 z4c3dSymmetrizer U
      (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx U idx))) ≤
      (3 * lGauge) * multiDH0Energy dims 5 z4c3dSymmetrizer U ∧
    2 * multiDH0Pair dims 5 z4c3dSymmetrizer U (z4c3dVarGaugeSemiDiscreteRhs gField dims dx U) ≤
      (6 * lGauge - 2 * (kappa1 * alphaMin)) * multiDH0Energy dims 5 z4c3dSymmetrizer U ∧
    multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dVarGaugeRollout gField dims a dx dt n U0) ≤
      ((((1 + 2 * lGauge * dt) ^ 3) * (1 - kappa1 * alphaMin * dt)) ^ n) * multiDH0Energy dims 5 z4c3dSymmetrizer U0 := by
  have hc0 := z4c3d_var_gauge_axis_commutator_and_step dims hDims hPos dx alphaMin a lGauge hdx gField hG 0 (by decide)
  have hc1 := z4c3d_var_gauge_axis_commutator_and_step dims hDims hPos dx alphaMin a lGauge hdx gField hG 1 (by decide)
  have hc2 := z4c3d_var_gauge_axis_commutator_and_step dims hDims hPos dx alphaMin a lGauge hdx gField hG 2 (by decide)
  have hComm3 : ratAbs (sumTo 3 fun d => multiDH0Pair dims 5 z4c3dSymmetrizer U
        (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx U idx))) ≤
      (3 * lGauge) * multiDH0Energy dims 5 z4c3dSymmetrizer U := by
    simp only [sumTo, Rat.zero_add]
    have ht1 := ratAbs_add_le
      (multiDH0Pair dims 5 z4c3dSymmetrizer U (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) 0) (centeredDiffAxis dims 0 dx U idx)) +
       multiDH0Pair dims 5 z4c3dSymmetrizer U (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) 1) (centeredDiffAxis dims 1 dx U idx)))
      (multiDH0Pair dims 5 z4c3dSymmetrizer U (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) 2) (centeredDiffAxis dims 2 dx U idx)))
    have ht2 := ratAbs_add_le
      (multiDH0Pair dims 5 z4c3dSymmetrizer U (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) 0) (centeredDiffAxis dims 0 dx U idx)))
      (multiDH0Pair dims 5 z4c3dSymmetrizer U (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) 1) (centeredDiffAxis dims 1 dx U idx)))
    have := (hc0 U).1; have := (hc1 U).1; have := (hc2 U).1; grind (ematch := 0)
  have hPtSrc : ∀ idx, idx < gridCellCount dims → ∀ v : Vec,
      h0Inner 5 (symSourceFormMat 5 z4c3dSymmetrizer (z4c3dSourceMat (gField idx))) v v ≤ (-(2 * (kappa1 * alphaMin))) * h0Inner 5 z4c3dSymmetrizer v v ∧
      h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dSourceMat (gField idx)) v) (mulVec 5 (z4c3dSourceMat (gField idx)) v) ≤ (rMax * rMax) * h0Inner 5 z4c3dSymmetrizer v v := by
    intro idx hidx v; obtain ⟨hk1Ge, hk2Ge, hrLe⟩ := hGaugeDamp idx hidx
    have hAlGe := hG.lapse_lower idx hidx; have hAlPos : 0 < (gField idx).alpha := by have := hG.alphaMin_pos; grind (ematch := 0)
    by_cases hkPos : 0 < (gField idx).kappa1
    · obtain ⟨_, _, hD, hB⟩ := z4c3d_source_dissipation_bounds (gField idx) hAlPos hkPos hk2Ge
      have hetaGe : kappa1 * alphaMin ≤ (gField idx).kappa1 * (gField idx).alpha := rat_mul_le_mul hK1 hk1Ge (Rat.le_of_lt hG.alphaMin_pos) hAlGe
      have hr0 : 0 ≤ z4c3dMaxDampRate (gField idx) := by
        unfold z4c3dMaxDampRate; have := le_rmax_left 0 (gField idx).kappa2
        exact Rat.mul_nonneg (Rat.mul_nonneg (by grind (ematch := 0)) (Rat.le_of_lt hkPos)) (Rat.le_of_lt hAlPos)
      have hvNN := z4c3dSymmetrizer_nonneg v
      have := rat_mul_mono hvNN (show -(2 * ((gField idx).kappa1 * (gField idx).alpha)) ≤ -(2 * (kappa1 * alphaMin)) by grind (ematch := 0))
      have := rat_mul_mono hvNN (rat_mul_le_mul hr0 hrLe hr0 hrLe)
      exact ⟨Rat.le_trans (hD v) (by grind (ematch := 0)), Rat.le_trans (hB v) (by grind (ematch := 0))⟩
    · have hk1Z : (gField idx).kappa1 = 0 := by grind (ematch := 0)
      have hkZ : kappa1 = 0 := by grind (ematch := 0)
      have hSrcZ : ∀ c, c < 5 → mulVec 5 (z4c3dSourceMat (gField idx)) v c = vecZero c := fun c hc => by
        have hc5 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
        rcases hc5 with rfl | rfl | rfl | rfl | rfl <;> (simp only [mulVec, vecZero, z4c3dSourceMat, z4c3dSourceRows, hk1Z, matOf, getOr, sumTo]; grind (ematch := 0))
      rw [← h0Inner_source_sym_part z4c3dSymmetrizer_symm,
          h0Inner_congr_vec z4c3dSymmetrizer (v2 := vecZero) (fun _ _ => rfl) hSrcZ,
          h0Inner_congr_vec z4c3dSymmetrizer (u2 := vecZero) hSrcZ (fun _ _ => rfl),
          h0Inner_congr_vec z4c3dSymmetrizer (u2 := vecZero) (v2 := vecZero) hSrcZ hSrcZ,
          h0Inner_zero_right, h0Inner_zero_left, h0Inner_zero_right, hkZ]
      have := Rat.mul_nonneg (rat_mul_self_nonneg rMax) (z4c3dSymmetrizer_nonneg v); exact ⟨by grind (ematch := 0), by grind (ematch := 0)⟩
  have hSemi : 2 * multiDH0Pair dims 5 z4c3dSymmetrizer U (z4c3dVarGaugeSemiDiscreteRhs gField dims dx U) ≤
      (6 * lGauge - 2 * (kappa1 * alphaMin)) * multiDH0Energy dims 5 z4c3dSymmetrizer U := by
    have hPairSplit : multiDH0Pair dims 5 z4c3dSymmetrizer U (z4c3dVarGaugeSemiDiscreteRhs gField dims dx U) =
        sumTo (gridCellCount dims) (fun idx => h0Inner 5 z4c3dSymmetrizer (U idx) (mulVec 5 (z4c3dSourceMat (gField idx)) (U idx))) -
        sumTo 3 (fun d => multiDH0Pair dims 5 z4c3dSymmetrizer U (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx U idx))) := by
      unfold multiDH0Pair z4c3dVarGaugeSemiDiscreteRhs
      have hCell : ∀ idx, h0Inner 5 z4c3dSymmetrizer (U idx) (fun c => mulVec 5 (z4c3dSourceMat (gField idx)) (U idx) c -
            sumTo 3 fun d => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx U idx) c) =
          h0Inner 5 z4c3dSymmetrizer (U idx) (mulVec 5 (z4c3dSourceMat (gField idx)) (U idx)) +
          ((-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (U idx) (mulVec 5 (z4c3dFluxMat (gField idx) 0) (centeredDiffAxis dims 0 dx U idx)) +
           ((-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (U idx) (mulVec 5 (z4c3dFluxMat (gField idx) 1) (centeredDiffAxis dims 1 dx U idx)) +
            (-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (U idx) (mulVec 5 (z4c3dFluxMat (gField idx) 2) (centeredDiffAxis dims 2 dx U idx)))) := fun idx => by
        rw [show (fun c => mulVec 5 (z4c3dSourceMat (gField idx)) (U idx) c - sumTo 3 fun d => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx U idx) c) =
            vecSub (mulVec 5 (z4c3dSourceMat (gField idx)) (U idx)) (vecAdd (mulVec 5 (z4c3dFluxMat (gField idx) 0) (centeredDiffAxis dims 0 dx U idx))
              (vecAdd (mulVec 5 (z4c3dFluxMat (gField idx) 1) (centeredDiffAxis dims 1 dx U idx))
                (mulVec 5 (z4c3dFluxMat (gField idx) 2) (centeredDiffAxis dims 2 dx U idx)))) by funext c; simp only [sumTo, vecSub, vecAdd]; grind (ematch := 0),
            h0Inner_sub_right, h0Inner_add_right, h0Inner_add_right]; grind (ematch := 0)
      rw [sumTo_congr (fun idx _ => hCell idx), sumTo_add, sumTo_add, sumTo_add, sumTo_mul_left, sumTo_mul_left, sumTo_mul_left]; simp only [sumTo]; grind (ematch := 0)
    have hSrcSum : 2 * sumTo (gridCellCount dims) (fun idx => h0Inner 5 z4c3dSymmetrizer (U idx) (mulVec 5 (z4c3dSourceMat (gField idx)) (U idx))) ≤
        (-(2 * (kappa1 * alphaMin))) * multiDH0Energy dims 5 z4c3dSymmetrizer U := by
      unfold multiDH0Energy; rw [← sumTo_mul_left, ← sumTo_mul_left]; refine sumTo_le fun idx hidx => ?_
      have hSym := h0Inner_symm z4c3dSymmetrizer_symm (U idx) (mulVec 5 (z4c3dSourceMat (gField idx)) (U idx))
      have hPart := h0Inner_source_sym_part z4c3dSymmetrizer_symm (z4c3dSourceMat (gField idx)) (U idx)
      have := (hPtSrc idx hidx (U idx)).1; grind (ematch := 0)
    have hC_lo : -((3 * lGauge) * multiDH0Energy dims 5 z4c3dSymmetrizer U) ≤
        sumTo 3 fun d => multiDH0Pair dims 5 z4c3dSymmetrizer U (fun idx => mulVec 5 (z4c3dFluxMat (gField idx) d) (centeredDiffAxis dims d dx U idx)) :=
      (ratAbs_bounds_iff.mp (by simpa only [ratAbs_eq_pde] using hComm3)).1
    rw [hPairSplit]; grind (ematch := 0)
  refine ⟨hComm3, hSemi, ?_⟩
  let qStep := ((1 + 2 * lGauge * dt) ^ 3) * (1 - kappa1 * alphaMin * dt)
  have h1g : 0 ≤ 1 + 2 * lGauge * dt := by have := Rat.mul_nonneg hG.lGauge_nonneg hdt; grind (ematch := 0)
  have h1e : 0 ≤ 1 - kappa1 * alphaMin * dt := by grind (ematch := 0)
  have hqNN : 0 ≤ qStep := by dsimp [qStep]; simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]; exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg h1g h1g) h1g) h1e
  have hOneStep : ∀ V : MultiDGrid, multiDH0Energy dims 5 z4c3dSymmetrizer
      (let U1 := z4c3dVarGaugeSweep gField dims a (dt / dx) V; fun idx c => U1 idx c + dt * mulVec 5 (z4c3dSourceMat (gField idx)) (U1 idx) c) ≤
      qStep * multiDH0Energy dims 5 z4c3dSymmetrizer V := by
    intro V
    have hSw : multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dVarGaugeSweep gField dims a (dt / dx) V) ≤ ((1 + 2 * lGauge * dt) ^ 3) * multiDH0Energy dims 5 z4c3dSymmetrizer V := by
      unfold z4c3dVarGaugeSweep
      have s0 := (hc0 V).2 dt hdt hcfl
      have s1 := (hc1 (z4c3dVarGaugeAxisStep gField dims a (dt / dx) 0 V)).2 dt hdt hcfl
      have s2 := (hc2 (z4c3dVarGaugeAxisStep gField dims a (dt / dx) 1 (z4c3dVarGaugeAxisStep gField dims a (dt / dx) 0 V))).2 dt hdt hcfl
      have m2 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans s1 (Rat.mul_le_mul_of_nonneg_left s0 h1g)) h1g
      simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]; exact Rat.le_trans s2 (by grind (ematch := 0))
    have hSrc : ∀ W : MultiDGrid, multiDH0Energy dims 5 z4c3dSymmetrizer (fun idx c => W idx c + dt * mulVec 5 (z4c3dSourceMat (gField idx)) (W idx) c) ≤
        (1 - kappa1 * alphaMin * dt) * multiDH0Energy dims 5 z4c3dSymmetrizer W := fun W => by
      unfold multiDH0Energy; rw [← sumTo_mul_left]; refine sumTo_le fun idx hidx => ?_; dsimp only
      obtain ⟨hD, hB⟩ := hPtSrc idx hidx (W idx)
      rw [show (fun c => W idx c + dt * mulVec 5 (z4c3dSourceMat (gField idx)) (W idx) c) =
          (fun c => 1 * W idx c + dt * mulVec 5 (z4c3dSourceMat (gField idx)) (W idx) c) by funext c; grind (ematch := 0),
        h0Inner_lin_left, h0Inner_lin_right, h0Inner_lin_right]
      have hPart := h0Inner_source_sym_part z4c3dSymmetrizer_symm (z4c3dSourceMat (gField idx)) (W idx)
      have hLhs : 1 * (1 * h0Inner 5 z4c3dSymmetrizer (W idx) (W idx) + dt * h0Inner 5 z4c3dSymmetrizer (W idx) (mulVec 5 (z4c3dSourceMat (gField idx)) (W idx))) +
          dt * (1 * h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dSourceMat (gField idx)) (W idx)) (W idx) +
            dt * h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dSourceMat (gField idx)) (W idx)) (mulVec 5 (z4c3dSourceMat (gField idx)) (W idx))) =
          h0Inner 5 z4c3dSymmetrizer (W idx) (W idx) + dt * h0Inner 5 (symSourceFormMat 5 z4c3dSymmetrizer (z4c3dSourceMat (gField idx))) (W idx) (W idx) +
          (dt * dt) * h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dSourceMat (gField idx)) (W idx)) (mulVec 5 (z4c3dSourceMat (gField idx)) (W idx)) := by rw [← hPart]; grind (ematch := 0)
      rw [hLhs]; have hd1 := Rat.mul_le_mul_of_nonneg_left hD hdt; have hb1 := Rat.mul_le_mul_of_nonneg_left hB (Rat.mul_nonneg hdt hdt)
      have hm := rat_mul_mono (z4c3dSymmetrizer_nonneg (W idx)) (Rat.mul_le_mul_of_nonneg_left hDampStep hdt)
      have hEqB : (dt * dt) * ((rMax * rMax) * h0Inner 5 z4c3dSymmetrizer (W idx) (W idx)) = h0Inner 5 z4c3dSymmetrizer (W idx) (W idx) * (dt * (dt * (rMax * rMax))) := by grind (ematch := 0)
      have hEqD : h0Inner 5 z4c3dSymmetrizer (W idx) (W idx) + dt * (-(2 * (kappa1 * alphaMin)) * h0Inner 5 z4c3dSymmetrizer (W idx) (W idx)) +
          h0Inner 5 z4c3dSymmetrizer (W idx) (W idx) * (dt * (kappa1 * alphaMin)) = (1 - kappa1 * alphaMin * dt) * h0Inner 5 z4c3dSymmetrizer (W idx) (W idx) := by grind (ematch := 0)
      grind (ematch := 0)
    have hSrcW := hSrc (z4c3dVarGaugeSweep gField dims a (dt / dx) V)
    have hmSw : (1 - kappa1 * alphaMin * dt) * multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dVarGaugeSweep gField dims a (dt / dx) V) ≤
        qStep * multiDH0Energy dims 5 z4c3dSymmetrizer V := by have := rat_mul_mono h1e hSw; dsimp only [qStep]; grind (ematch := 0)
    exact Rat.le_trans hSrcW hmSw
  have hPowNN : ∀ k : Nat, 0 ≤ qStep ^ k := fun k => by induction k with | zero => simp [Rat.pow_zero]; decide | succ k ih => rw [Rat.pow_succ]; exact Rat.mul_nonneg ih hqNN
  induction n generalizing U0 with
  | zero => rw [z4c3dVarGaugeRollout.eq_def]; simp only [Rat.pow_zero, Rat.one_mul]; exact Rat.le_refl
  | succ k ih => rw [z4c3dVarGaugeRollout.eq_def]; dsimp only; rw [Rat.pow_succ, Rat.mul_assoc]; exact Rat.le_trans (ih _) (Rat.mul_le_mul_of_nonneg_left (hOneStep U0) (hPowNN k))
def sbpWeight1D (N k : Nat) : Rat := if k = 0 ∨ k + 1 = N then 1 / 2 else 1
def sbpDiff1D (N : Nat) (dx : Rat) (u : Nat → Rat) (k : Nat) : Rat :=
  if k = 0 then (1 / dx) * (u 1 - u 0) else if k + 1 = N then (1 / dx) * (u (N - 1) - u (N - 2)) else (1 / (2 * dx)) * (u (k + 1) - u (k - 1))
def openBoxWeight3D (Nx Ny Nz idx : Nat) : Rat :=
  let ix := idx / (Ny * Nz); let rem := idx % (Ny * Nz); sbpWeight1D Nx ix * sbpWeight1D Ny (rem / Nz) * sbpWeight1D Nz (rem % Nz)
def openBoxH0Energy (Nx Ny Nz : Nat) (U : MultiDGrid) : Rat := sumTo (Nx * (Ny * Nz)) fun idx => openBoxWeight3D Nx Ny Nz idx * h0Inner 5 z4c3dSymmetrizer (U idx) (U idx)
def openBoxH0Pair (Nx Ny Nz : Nat) (U V : MultiDGrid) : Rat := sumTo (Nx * (Ny * Nz)) fun idx => openBoxWeight3D Nx Ny Nz idx * h0Inner 5 z4c3dSymmetrizer (U idx) (V idx)
def openBoxSbpDiff3D (Nx Ny Nz d : Nat) (dx : Rat) (U : MultiDGrid) (idx c : Nat) : Rat :=
  let ix := idx / (Ny * Nz); let rem := idx % (Ny * Nz); let iy := rem / Nz; let iz := rem % Nz
  match d with
  | 0 => sbpDiff1D Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz)) c) ix
  | 1 => sbpDiff1D Ny dx (fun ky => U (ix * (Ny * Nz) + (ky * Nz + iz)) c) iy
  | 2 => sbpDiff1D Nz dx (fun kz => U (ix * (Ny * Nz) + (iy * Nz + kz)) c) iz
  | _ => 0
def z4cCharAmplitudes (d : Nat) (u : Vec) : Vec := mulVec 5 (z4c3dEigInvMat d) u
/-- 1D Olsson–Strand characteristic SAT absorbing boundary penalty (`τ = 1/2`, `1 / (2 w_b dx) = 1 / dx`). -/
def sbpSatPenalty1D (p : Z4c3DParams) (d N : Nat) (dx : Rat) (u : Nat → Vec) (k : Nat) : Vec :=
  if k = 0 then vecScale (-(1 / dx)) (mulVec 5 (z4c3dEigVecMat d) (fun m => rmax 0 (z4c3dEigVals p d m) * z4cCharAmplitudes d (u 0) m))
  else if k + 1 = N then vecScale (-(1 / dx)) (mulVec 5 (z4c3dEigVecMat d) (fun m => rmax 0 (-(z4c3dEigVals p d m)) * z4cCharAmplitudes d (u (N - 1)) m))
  else vecZero
/-- 3D open-box non-periodic Strand SBP + Olsson–Strand characteristic SAT directional operator along axis `d ∈ {0, 1, 2}`. -/
def openBoxSbpSatAxis3D (p : Z4c3DParams) (Nx Ny Nz d : Nat) (dx : Rat) (U : MultiDGrid) (idx : Nat) : Vec :=
  let ix := idx / (Ny * Nz); let rem := idx % (Ny * Nz); let iy := rem / Nz; let iz := rem % Nz
  let pen : Vec := match d with
    | 0 => sbpSatPenalty1D p 0 Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz))) ix
    | 1 => sbpSatPenalty1D p 1 Ny dx (fun ky => U (ix * (Ny * Nz) + (ky * Nz + iz))) iy
    | 2 => sbpSatPenalty1D p 2 Nz dx (fun kz => U (ix * (Ny * Nz) + (iy * Nz + kz))) iz
    | _ => vecZero
  vecSub pen (mulVec 5 (z4c3dFluxMat p d) (openBoxSbpDiff3D Nx Ny Nz d dx U idx))
/-- Constant-coefficient open-box 3D semi-discrete RHS with Strand SBP derivatives and Olsson–Strand characteristic SAT penalties. -/
@[expose] def z4c3dOpenBoxRhs (p : Z4c3DParams) (Nx Ny Nz : Nat) (dx : Rat) (C : MultiDGrid) : MultiDGrid :=
  fun idx c => mulVec 5 (z4c3dSourceMat p) (C idx) c + sumTo 3 fun d => openBoxSbpSatAxis3D p Nx Ny Nz d dx C idx c
abbrev z4c3dOpenBoxSatRhs := z4c3dOpenBoxRhs
def SommerfeldNoIncoming3D (p : Z4c3DParams) (Nx Ny Nz : Nat) (U : MultiDGrid) : Prop :=
  ∀ ix iy iz, ix < Nx → iy < Ny → iz < Nz →
    let cell := ix * (Ny * Nz) + (iy * Nz + iz)
    (ix = 0 → ∀ m, m < 5 → 0 < z4c3dEigVals p 0 m → z4cCharAmplitudes 0 (U cell) m = 0) ∧
    (ix + 1 = Nx → ∀ m, m < 5 → z4c3dEigVals p 0 m < 0 → z4cCharAmplitudes 0 (U cell) m = 0) ∧
    (iy = 0 → ∀ m, m < 5 → 0 < z4c3dEigVals p 1 m → z4cCharAmplitudes 1 (U cell) m = 0) ∧
    (iy + 1 = Ny → ∀ m, m < 5 → z4c3dEigVals p 1 m < 0 → z4cCharAmplitudes 1 (U cell) m = 0) ∧
    (iz = 0 → ∀ m, m < 5 → 0 < z4c3dEigVals p 2 m → z4cCharAmplitudes 2 (U cell) m = 0) ∧
    (iz + 1 = Nz → ∀ m, m < 5 → z4c3dEigVals p 2 m < 0 → z4cCharAmplitudes 2 (U cell) m = 0)
private theorem sumTo_telescope_nat (K : Nat) (f : Nat → Rat) : sumTo K (fun j => f (j + 1) - f j) = f K - f 0 := by
  induction K with | zero => simp [sumTo]; grind (ematch := 0) | succ K ih => simp only [sumTo, ih]; grind (ematch := 0)
private theorem sbp_1d_gauss_green_mat (H0 B : Mat) (hSymm : ∀ i j, i < 5 → j < 5 → H0 i j = H0 j i)
    (hAdj : ∀ u v, h0Inner 5 H0 u (mulVec 5 B v) = h0Inner 5 H0 (mulVec 5 B u) v)
    (N : Nat) (hN2 : 2 ≤ N) (dx : Rat) (hdx : 0 < dx) (u : Nat → Vec) :
    2 * dx * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 H0 (u k) (mulVec 5 B (fun c => sbpDiff1D N dx (fun j => u j c) k))) =
    h0Inner 5 H0 (u (N - 1)) (mulVec 5 B (u (N - 1))) - h0Inner 5 H0 (u 0) (mulVec 5 B (u 0)) := by
  have hc1 := Rat.div_mul_cancel (by grind (ematch := 0) : dx ≠ 0) (a := (1 : Rat)); have hc2 := Rat.div_mul_cancel (by grind (ematch := 0) : 2 * dx ≠ 0) (a := (1 : Rat))
  have hSymPair : ∀ x y : Vec, h0Inner 5 H0 x (mulVec 5 B y) = h0Inner 5 H0 y (mulVec 5 B x) := fun x y => by rw [hAdj, h0Inner_symm hSymm]
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 2 := ⟨N - 2, by omega⟩
  rw [show K + 2 = 1 + K + 1 by omega, sumTo_add_len (1 + K) 1, sumTo_add_len 1 K]; simp only [sumTo, Rat.zero_add, Nat.add_zero]
  have h0Term : 2 * dx * (sbpWeight1D (1 + K + 1) 0 * h0Inner 5 H0 (u 0) (mulVec 5 B (fun c => sbpDiff1D (1 + K + 1) dx (fun j => u j c) 0))) =
      h0Inner 5 H0 (u 0) (mulVec 5 B (u 1)) - h0Inner 5 H0 (u 0) (mulVec 5 B (u 0)) := by
    unfold sbpWeight1D sbpDiff1D; simp only [true_or, ↓reduceIte]
    rw [show (fun c => (1 / dx) * (u 1 c - u 0 c)) = (fun c => (1 / dx) * u 1 c + (-(1 / dx)) * u 0 c) by funext c; grind (ematch := 0),
        show mulVec 5 B (fun c => (1 / dx) * u 1 c + (-(1 / dx)) * u 0 c) =
          (fun i => (1 / dx) * mulVec 5 B (u 1) i + (-(1 / dx)) * mulVec 5 B (u 0) i) by funext i; exact mulVec_lin _ _ _ _ _ _ i,
        h0Inner_lin_right]; grind (ematch := 0)
  have hMidTerm : ∀ j, j < K → 2 * dx * (sbpWeight1D (1 + K + 1) (1 + j) * h0Inner 5 H0 (u (1 + j)) (mulVec 5 B (fun c => sbpDiff1D (1 + K + 1) dx (fun q => u q c) (1 + j)))) =
      h0Inner 5 H0 (u (j + 1)) (mulVec 5 B (u (j + 2))) - h0Inner 5 H0 (u j) (mulVec 5 B (u (j + 1))) := by
    intro j hj; rw [show 1 + j = j + 1 by omega, show 1 + K + 1 = K + 2 by omega]; unfold sbpWeight1D sbpDiff1D
    simp only [show j + 1 ≠ 0 by omega, show j + 1 + 1 ≠ K + 2 by omega, or_self, ↓reduceIte, show j + 1 - 1 = j by omega, show j + 1 + 1 = j + 2 by omega]
    rw [show (fun c => (1 / (2 * dx)) * (u (j + 2) c - u j c)) = (fun c => (1 / (2 * dx)) * u (j + 2) c + (-(1 / (2 * dx))) * u j c) by funext c; grind (ematch := 0),
        show mulVec 5 B (fun c => (1 / (2 * dx)) * u (j + 2) c + (-(1 / (2 * dx))) * u j c) =
          (fun i => (1 / (2 * dx)) * mulVec 5 B (u (j + 2)) i + (-(1 / (2 * dx))) * mulVec 5 B (u j) i) by funext i; exact mulVec_lin _ _ _ _ _ _ i,
        h0Inner_lin_right, hSymPair (u (j + 1)) (u j)]; grind (ematch := 0)
  have hLastTerm : 2 * dx * (sbpWeight1D (1 + K + 1) (1 + K) * h0Inner 5 H0 (u (1 + K)) (mulVec 5 B (fun c => sbpDiff1D (1 + K + 1) dx (fun j => u j c) (1 + K)))) =
      h0Inner 5 H0 (u (K + 1)) (mulVec 5 B (u (K + 1))) - h0Inner 5 H0 (u K) (mulVec 5 B (u (K + 1))) := by
    rw [show 1 + K + 1 = K + 2 by omega, show 1 + K = K + 1 by omega]; unfold sbpWeight1D sbpDiff1D
    simp only [show K + 1 ≠ 0 by omega, show K + 1 + 1 = K + 2 by omega, or_true, ↓reduceIte, show K + 2 - 1 = K + 1 by omega, show K + 2 - 2 = K by omega]
    rw [show (fun c => (1 / dx) * (u (K + 1) c - u K c)) = (fun c => (1 / dx) * u (K + 1) c + (-(1 / dx)) * u K c) by funext c; grind (ematch := 0),
        show mulVec 5 B (fun c => (1 / dx) * u (K + 1) c + (-(1 / dx)) * u K c) =
          (fun i => (1 / dx) * mulVec 5 B (u (K + 1)) i + (-(1 / dx)) * mulVec 5 B (u K) i) by funext i; exact mulVec_lin _ _ _ _ _ _ i,
        h0Inner_lin_right, hSymPair (u (K + 1)) (u K)]; grind (ematch := 0)
  rw [Rat.mul_add, Rat.mul_add, h0Term, hLastTerm, ← sumTo_mul_left, sumTo_congr hMidTerm,
      sumTo_telescope_nat K (fun j => h0Inner 5 H0 (u j) (mulVec 5 B (u (j + 1))))]; grind (ematch := 0)
private theorem sbp_1d_gauss_green (p : Z4c3DParams) (d N : Nat) (hd : d < 3) (hN2 : 2 ≤ N) (dx : Rat) (hdx : 0 < dx) (u : Nat → Vec) :
    2 * dx * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k) (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k))) =
    h0Inner 5 z4c3dSymmetrizer (u (N - 1)) (mulVec 5 (z4c3dFluxMat p d) (u (N - 1))) - h0Inner 5 z4c3dSymmetrizer (u 0) (mulVec 5 (z4c3dFluxMat p d) (u 0)) :=
  sbp_1d_gauss_green_mat z4c3dSymmetrizer (z4c3dFluxMat p d) z4c3dSymmetrizer_symm (z4c3dFluxMat_self_adjoint p d hd) N hN2 dx hdx u
private theorem z4c3d_char_flux_form (p : Z4c3DParams) (d : Nat) (hd : d < 3) (v : Vec) :
    h0Inner 5 z4c3dSymmetrizer v (mulVec 5 (z4c3dFluxMat p d) v) =
      sumTo 5 fun m => z4c3dCharWeights m * z4c3dEigVals p d m * (z4cCharAmplitudes d v m * z4cCharAmplitudes d v m) := by
  obtain ⟨hEig, hGram⟩ := z4c3d_axis_isEigenSystem p d hd
  rw [h0Inner_congr_mat (fun i j hi hj => (hGram i j hi hj).symm)]; unfold h0Inner; rw [dot_gram]
  unfold charForm z4cCharAmplitudes; exact sumTo_congr fun m hm => by rw [hEig.char_flux v m hm]; grind (ematch := 0)
private theorem h0Inner_eigVec_right (d : Nat) (hd : d < 3) (v z : Vec) :
    h0Inner 5 z4c3dSymmetrizer v (mulVec 5 (z4c3dEigVecMat d) z) = sumTo 5 fun m => z4c3dCharWeights m * z4cCharAmplitudes d v m * z m := by
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd3 with rfl | rfl | rfl <;>
    (simp only [h0Inner, dot, mulVec, z4c3dSymmetrizer, z4c3dSymmetrizerRows, z4c3dEigVecMat, z4c3dEigVecRows,
       z4cCharAmplitudes, z4c3dEigInvMat, z4c3dEigInvRows, z4c3dCharWeights, matOf, vecOf, getOr, sumTo]; grind (ematch := 0))
private theorem sbp_1d_sat_identity (p : Z4c3DParams) (d N : Nat) (hd : d < 3) (hN2 : 2 ≤ N) (dx : Rat) (hdx : 0 < dx) (u : Nat → Vec) :
    2 * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k)
      (vecSub (sbpSatPenalty1D p d N dx u k) (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k)))) =
    (-(1 / dx)) * sumTo 5 (fun m => z4c3dCharWeights m *
      (rmax 0 (-(z4c3dEigVals p d m)) * (z4cCharAmplitudes d (u 0) m * z4cCharAmplitudes d (u 0) m) +
       rmax 0 (z4c3dEigVals p d m) * (z4cCharAmplitudes d (u (N - 1)) m * z4cCharAmplitudes d (u (N - 1)) m))) := by
  have hdx0 : dx ≠ 0 := by grind (ematch := 0)
  have hc1 := Rat.div_mul_cancel hdx0 (a := (1 : Rat))
  have hSubSum : ∀ a b : Nat → Rat, sumTo N (fun k => a k - b k) = sumTo N a - sumTo N b :=
    fun a b => by rw [show (fun k => a k - b k) = (fun k => a k + (-1) * b k) by funext k; grind (ematch := 0), sumTo_add, sumTo_mul_left]; grind (ematch := 0)
  rw [sumTo_congr (fun k _ => show sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k)
        (vecSub (sbpSatPenalty1D p d N dx u k) (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k))) =
      sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k) (sbpSatPenalty1D p d N dx u k) -
      sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k) (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k)) by
        rw [h0Inner_sub_right]; grind (ematch := 0)), hSubSum]
  have hPenSum : 2 * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k) (sbpSatPenalty1D p d N dx u k)) =
      (-(1 / dx)) * (sumTo 5 (fun m => z4c3dCharWeights m * rmax 0 (z4c3dEigVals p d m) * (z4cCharAmplitudes d (u 0) m * z4cCharAmplitudes d (u 0) m)) +
                     sumTo 5 (fun m => z4c3dCharWeights m * rmax 0 (-(z4c3dEigVals p d m)) * (z4cCharAmplitudes d (u (N - 1)) m * z4cCharAmplitudes d (u (N - 1)) m))) := by
    obtain ⟨K, rfl⟩ : ∃ K, N = K + 2 := ⟨N - 2, by omega⟩
    have hSum1 : ∀ f : Nat → Rat, sumTo 1 f = f 0 := fun f => by simp [sumTo, Rat.zero_add]
    rw [show K + 2 - 1 = K + 1 by omega, show K + 2 = 1 + K + 1 by omega, sumTo_add_len (1 + K) 1, sumTo_add_len 1 K, hSum1, hSum1]; simp only [Nat.add_zero]
    have hMid0 : sumTo K (fun j => sbpWeight1D (1 + K + 1) (1 + j) * h0Inner 5 z4c3dSymmetrizer (u (1 + j)) (sbpSatPenalty1D p d (1 + K + 1) dx u (1 + j))) = 0 := by
      rw [← sumTo_zero K]; refine sumTo_congr fun j _ => ?_
      unfold sbpSatPenalty1D; simp only [show 1 + j ≠ 0 by omega, show 1 + j + 1 ≠ 1 + K + 1 by omega, ↓reduceIte, h0Inner_zero_right]; grind (ematch := 0)
    rw [hMid0, show 1 + K + 1 = K + 2 by omega, show 1 + K = K + 1 by omega]; unfold sbpWeight1D sbpSatPenalty1D
    simp only [true_or, or_true, show K + 1 ≠ 0 by omega, show K + 1 + 1 = K + 2 by omega, ↓reduceIte, show K + 2 - 1 = K + 1 by omega]
    have hL : sumTo 5 (fun m => z4c3dCharWeights m * z4cCharAmplitudes d (u 0) m * (rmax 0 (z4c3dEigVals p d m) * z4cCharAmplitudes d (u 0) m)) =
        sumTo 5 (fun m => z4c3dCharWeights m * rmax 0 (z4c3dEigVals p d m) * (z4cCharAmplitudes d (u 0) m * z4cCharAmplitudes d (u 0) m)) := sumTo_congr fun _ _ => by grind (ematch := 0)
    have hR : sumTo 5 (fun m => z4c3dCharWeights m * z4cCharAmplitudes d (u (K + 1)) m * (rmax 0 (-z4c3dEigVals p d m) * z4cCharAmplitudes d (u (K + 1)) m)) =
        sumTo 5 (fun m => z4c3dCharWeights m * rmax 0 (-z4c3dEigVals p d m) * (z4cCharAmplitudes d (u (K + 1)) m * z4cCharAmplitudes d (u (K + 1)) m)) := sumTo_congr fun _ _ => by grind (ematch := 0)
    rw [h0Inner_scale_right, h0Inner_scale_right, h0Inner_eigVec_right d hd, h0Inner_eigVec_right d hd, hL, hR]; grind (ematch := 0)
  have hGG := sbp_1d_gauss_green p d N hd hN2 dx hdx u
  have hDiffSum : -(2 * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k)
        (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k)))) =
      (1 / dx) * (sumTo 5 (fun m => z4c3dCharWeights m * z4c3dEigVals p d m * (z4cCharAmplitudes d (u 0) m * z4cCharAmplitudes d (u 0) m)) -
                  sumTo 5 (fun m => z4c3dCharWeights m * z4c3dEigVals p d m * (z4cCharAmplitudes d (u (N - 1)) m * z4cCharAmplitudes d (u (N - 1)) m))) := by
    rw [z4c3d_char_flux_form p d hd (u (N - 1)), z4c3d_char_flux_form p d hd (u 0)] at hGG; apply rat_eq_of_mul_cancel hdx0; grind (ematch := 0)
  have hRmaxId : ∀ lam : Rat, lam - rmax 0 lam = -(rmax 0 (-lam)) ∧ -lam - rmax 0 (-lam) = -(rmax 0 lam) :=
    fun lam => by unfold rmax; split <;> split <;> exact ⟨by grind (ematch := 0), by grind (ematch := 0)⟩
  have hSumSub5 : ∀ a b : Nat → Rat, sumTo 5 a - sumTo 5 b = sumTo 5 (fun m => a m - b m) :=
    fun a b => by rw [show (fun m => a m - b m) = (fun m => a m + (-1) * b m) by funext m; grind (ematch := 0), sumTo_add, sumTo_mul_left]; grind (ematch := 0)
  have hEq5 : sumTo 5 (fun m =>
        (z4c3dCharWeights m * z4c3dEigVals p d m * (z4cCharAmplitudes d (u 0) m * z4cCharAmplitudes d (u 0) m) -
         z4c3dCharWeights m * z4c3dEigVals p d m * (z4cCharAmplitudes d (u (N - 1)) m * z4cCharAmplitudes d (u (N - 1)) m)) -
        (z4c3dCharWeights m * rmax 0 (z4c3dEigVals p d m) * (z4cCharAmplitudes d (u 0) m * z4cCharAmplitudes d (u 0) m) +
         z4c3dCharWeights m * rmax 0 (-(z4c3dEigVals p d m)) * (z4cCharAmplitudes d (u (N - 1)) m * z4cCharAmplitudes d (u (N - 1)) m))) =
      (-1 : Rat) * sumTo 5 (fun m => z4c3dCharWeights m *
        (rmax 0 (-(z4c3dEigVals p d m)) * (z4cCharAmplitudes d (u 0) m * z4cCharAmplitudes d (u 0) m) +
         rmax 0 (z4c3dEigVals p d m) * (z4cCharAmplitudes d (u (N - 1)) m * z4cCharAmplitudes d (u (N - 1)) m))) := by
    rw [← sumTo_mul_left]; refine sumTo_congr fun m _ => ?_; obtain ⟨hr1, hr2⟩ := hRmaxId (z4c3dEigVals p d m); grind (ematch := 0)
  rw [← hSumSub5, ← hSumSub5, sumTo_add] at hEq5
  have : 2 * (sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k) (sbpSatPenalty1D p d N dx u k)) -
      sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k) (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k)))) =
      2 * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k) (sbpSatPenalty1D p d N dx u k)) +
      (-(2 * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k) (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k))))) := by grind (ematch := 0)
  rw [this, hPenSum, hDiffSum]; grind (ematch := 0)

/-- **Unconditional Constant-Coefficient Open-Box Strand SBP + Olsson–Strand Characteristic SAT Dissipation (`z4c3d_sommerfeld_boundary_dissipative`)**:
For every `U : MultiDGrid` on `[Nx, Ny, Nz]` (`2 ≤ Nx, Ny, Nz`), proves semi-discrete `H_0`-dissipativity `≤ -2 κ_1 α E_box(U)`
without any incoming-mode assumption on `U`, strict `< 0` boundary energy flux on outgoing `+α` modes, and SAT vanishing under `SommerfeldNoIncoming3D`. -/
theorem z4c3d_sommerfeld_boundary_dissipative (p : Z4c3DParams) (Nx Ny Nz : Nat)
    (hNx : 2 ≤ Nx) (hNy : 2 ≤ Ny) (hNz : 2 ≤ Nz) (dx : Rat) (hdx : 0 < dx) (U : MultiDGrid) :
    (∀ d, d < 3 → ∀ v : Vec, h0Inner 5 z4c3dSymmetrizer v (mulVec 5 (z4c3dFluxMat p d) v) =
      sumTo 5 fun m => z4c3dCharWeights m * z4c3dEigVals p d m * (z4cCharAmplitudes d v m * z4cCharAmplitudes d v m)) ∧
    (∀ d N, d < 3 → 2 ≤ N → ∀ u : Nat → Vec,
      2 * dx * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k)
        (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k))) =
      h0Inner 5 z4c3dSymmetrizer (u (N - 1)) (mulVec 5 (z4c3dFluxMat p d) (u (N - 1))) -
      h0Inner 5 z4c3dSymmetrizer (u 0) (mulVec 5 (z4c3dFluxMat p d) (u 0))) ∧
    (∀ d, d < 3 → 2 * openBoxH0Pair Nx Ny Nz U (openBoxSbpSatAxis3D p Nx Ny Nz d dx U) ≤ 0) ∧
    (0 ≤ p.alpha → 0 ≤ p.kappa1 → -1 ≤ p.kappa2 →
      2 * openBoxH0Pair Nx Ny Nz U (z4c3dOpenBoxRhs p Nx Ny Nz dx U) ≤ (-(2 * (p.kappa1 * p.alpha))) * openBoxH0Energy Nx Ny Nz U) ∧
    (ratAbs p.betax < p.alpha → (∃ iy iz, iy < Ny ∧ iz < Nz ∧ z4cCharAmplitudes 0 (U ((Nx - 1) * (Ny * Nz) + (iy * Nz + iz))) 0 ≠ 0) →
      2 * openBoxH0Pair Nx Ny Nz U (openBoxSbpSatAxis3D p Nx Ny Nz 0 dx U) < 0) ∧
    (SommerfeldNoIncoming3D p Nx Ny Nz U → ∀ d idx c, d < 3 → idx < Nx * (Ny * Nz) → c < 5 →
      openBoxSbpSatAxis3D p Nx Ny Nz d dx U idx c = -(mulVec 5 (z4c3dFluxMat p d) (openBoxSbpDiff3D Nx Ny Nz d dx U idx) c)) := by
  have hInvDxPos : 0 < 1 / dx := rat_inv_one_div_pos hdx
  have hW1Pos : ∀ N k, 0 < sbpWeight1D N k := fun N k => by unfold sbpWeight1D; split <;> grind (ematch := 0)
  have hwPos : ∀ m, m < 5 → 0 < z4c3dCharWeights m := fun m hm => by
    have hm5 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := (by omega); rcases hm5 with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have h1D_nonpos : ∀ d N, d < 3 → 2 ≤ N → ∀ u : Nat → Vec,
      2 * sumTo N (fun k => sbpWeight1D N k * h0Inner 5 z4c3dSymmetrizer (u k)
        (vecSub (sbpSatPenalty1D p d N dx u k) (mulVec 5 (z4c3dFluxMat p d) (fun c => sbpDiff1D N dx (fun j => u j c) k)))) ≤ 0 := by
    intro d N hd hN2 u; rw [sbp_1d_sat_identity p d N hd hN2 dx hdx u]
    have hS : 0 ≤ sumTo 5 (fun m => z4c3dCharWeights m *
        (rmax 0 (-(z4c3dEigVals p d m)) * (z4cCharAmplitudes d (u 0) m * z4cCharAmplitudes d (u 0) m) +
         rmax 0 (z4c3dEigVals p d m) * (z4cCharAmplitudes d (u (N - 1)) m * z4cCharAmplitudes d (u (N - 1)) m))) :=
      sumTo_nonneg fun m hm => Rat.mul_nonneg (Rat.le_of_lt (hwPos m hm)) (by
        have := Rat.mul_nonneg (le_rmax_left 0 (-(z4c3dEigVals p d m))) (rat_mul_self_nonneg (z4cCharAmplitudes d (u 0) m))
        have := Rat.mul_nonneg (le_rmax_left 0 (z4c3dEigVals p d m)) (rat_mul_self_nonneg (z4cCharAmplitudes d (u (N - 1)) m)); grind (ematch := 0))
    have := Rat.mul_nonneg (Rat.le_of_lt hInvDxPos) hS; grind (ematch := 0)
  have hIdxDecomp : ∀ ix iy iz, ix < Nx → iy < Ny → iz < Nz →
      let idx := ix * (Ny * Nz) + (iy * Nz + iz)
      idx / (Ny * Nz) = ix ∧ (idx % (Ny * Nz)) / Nz = iy ∧ (idx % (Ny * Nz)) % Nz = iz := by
    intro ix iy iz _ hiy hiz idx
    have hrem : iy * Nz + iz < Ny * Nz := by have h2 := Nat.mul_le_mul_right Nz (show iy + 1 ≤ Ny by omega); rw [Nat.add_mul, Nat.one_mul] at h2; omega
    have hm : idx % (Ny * Nz) = iy * Nz + iz := by dsimp [idx]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem]
    exact ⟨slab3d_div_eq Ny Nz ix iy iz hiy hiz, by rw [hm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hiz, Nat.zero_add],
           by rw [hm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hiz]⟩
  have hAxis0Eq : 2 * openBoxH0Pair Nx Ny Nz U (openBoxSbpSatAxis3D p Nx Ny Nz 0 dx U) =
      sumTo Ny (fun iy => sumTo Nz fun iz => (sbpWeight1D Ny iy * sbpWeight1D Nz iz) *
        (2 * sumTo Nx fun ix => sbpWeight1D Nx ix * h0Inner 5 z4c3dSymmetrizer (U (ix * (Ny * Nz) + (iy * Nz + iz)))
          (vecSub (sbpSatPenalty1D p 0 Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz))) ix)
            (mulVec 5 (z4c3dFluxMat p 0) (fun c => sbpDiff1D Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz)) c) ix))))) := by
    unfold openBoxH0Pair; rw [sumTo_mul_split Nx (Ny * Nz), sumTo_congr (fun _ _ => sumTo_mul_split Ny Nz _),
      sumTo_comm Nx Ny, sumTo_congr (fun _ _ => sumTo_comm Nx Nz _), ← sumTo_mul_left]
    refine sumTo_congr fun iy hiy => ?_; rw [← sumTo_mul_left]; refine sumTo_congr fun iz hiz => ?_
    rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_mul_left]; refine sumTo_congr fun ix hix => ?_
    obtain ⟨d1, d2, d3⟩ := hIdxDecomp ix iy iz hix hiy hiz; unfold openBoxWeight3D openBoxSbpSatAxis3D openBoxSbpDiff3D; dsimp only; rw [d1, d2, d3]; grind (ematch := 0)
  have hAxisNonpos : ∀ d, d < 3 → 2 * openBoxH0Pair Nx Ny Nz U (openBoxSbpSatAxis3D p Nx Ny Nz d dx U) ≤ 0 := by
    intro d hd; have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd3 with rfl | rfl | rfl
    · rw [hAxis0Eq, ← sumTo_zero Ny]; refine sumTo_le fun iy _ => ?_; rw [← sumTo_zero Nz]; refine sumTo_le fun iz _ => ?_
      have hm := rat_mul_mono (Rat.le_of_lt (Rat.mul_pos (hW1Pos Ny iy) (hW1Pos Nz iz))) (h1D_nonpos 0 Nx (by decide) hNx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz)))); grind (ematch := 0)
    · unfold openBoxH0Pair; rw [sumTo_mul_split Nx (Ny * Nz), sumTo_congr (fun _ _ => sumTo_mul_split Ny Nz _),
        sumTo_congr (fun _ _ => sumTo_comm Ny Nz _), ← sumTo_mul_left, ← sumTo_zero Nx]
      refine sumTo_le fun ix hix => ?_; rw [← sumTo_mul_left, ← sumTo_zero Nz]; refine sumTo_le fun iz hiz => ?_
      have hEqY : 2 * sumTo Ny (fun iy => openBoxWeight3D Nx Ny Nz (ix * (Ny * Nz) + (iy * Nz + iz)) *
            h0Inner 5 z4c3dSymmetrizer (U (ix * (Ny * Nz) + (iy * Nz + iz))) (openBoxSbpSatAxis3D p Nx Ny Nz 1 dx U (ix * (Ny * Nz) + (iy * Nz + iz)))) =
          (sbpWeight1D Nx ix * sbpWeight1D Nz iz) * (2 * sumTo Ny fun iy => sbpWeight1D Ny iy *
            h0Inner 5 z4c3dSymmetrizer (U (ix * (Ny * Nz) + (iy * Nz + iz)))
              (vecSub (sbpSatPenalty1D p 1 Ny dx (fun ky => U (ix * (Ny * Nz) + (ky * Nz + iz))) iy)
                (mulVec 5 (z4c3dFluxMat p 1) (fun c => sbpDiff1D Ny dx (fun ky => U (ix * (Ny * Nz) + (ky * Nz + iz)) c) iy)))) := by
        rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_mul_left]; refine sumTo_congr fun iy hiy => ?_
        obtain ⟨d1, d2, d3⟩ := hIdxDecomp ix iy iz hix hiy hiz; unfold openBoxWeight3D openBoxSbpSatAxis3D openBoxSbpDiff3D; dsimp only; rw [d1, d2, d3]; grind (ematch := 0)
      rw [hEqY]; have hm := rat_mul_mono (Rat.le_of_lt (Rat.mul_pos (hW1Pos Nx ix) (hW1Pos Nz iz))) (h1D_nonpos 1 Ny (by decide) hNy (fun ky => U (ix * (Ny * Nz) + (ky * Nz + iz)))); grind (ematch := 0)
    · unfold openBoxH0Pair; rw [sumTo_mul_split Nx (Ny * Nz), sumTo_congr (fun _ _ => sumTo_mul_split Ny Nz _), ← sumTo_mul_left, ← sumTo_zero Nx]
      refine sumTo_le fun ix hix => ?_; rw [← sumTo_mul_left, ← sumTo_zero Ny]; refine sumTo_le fun iy hiy => ?_
      have hEqZ : 2 * sumTo Nz (fun iz => openBoxWeight3D Nx Ny Nz (ix * (Ny * Nz) + (iy * Nz + iz)) *
            h0Inner 5 z4c3dSymmetrizer (U (ix * (Ny * Nz) + (iy * Nz + iz))) (openBoxSbpSatAxis3D p Nx Ny Nz 2 dx U (ix * (Ny * Nz) + (iy * Nz + iz)))) =
          (sbpWeight1D Nx ix * sbpWeight1D Ny iy) * (2 * sumTo Nz fun iz => sbpWeight1D Nz iz *
            h0Inner 5 z4c3dSymmetrizer (U (ix * (Ny * Nz) + (iy * Nz + iz)))
              (vecSub (sbpSatPenalty1D p 2 Nz dx (fun kz => U (ix * (Ny * Nz) + (iy * Nz + kz))) iz)
                (mulVec 5 (z4c3dFluxMat p 2) (fun c => sbpDiff1D Nz dx (fun kz => U (ix * (Ny * Nz) + (iy * Nz + kz)) c) iz)))) := by
        rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_mul_left]; refine sumTo_congr fun iz hiz => ?_
        obtain ⟨d1, d2, d3⟩ := hIdxDecomp ix iy iz hix hiy hiz; unfold openBoxWeight3D openBoxSbpSatAxis3D openBoxSbpDiff3D; dsimp only; rw [d1, d2, d3]; grind (ematch := 0)
      rw [hEqZ]; have hm := rat_mul_mono (Rat.le_of_lt (Rat.mul_pos (hW1Pos Nx ix) (hW1Pos Ny iy))) (h1D_nonpos 2 Nz (by decide) hNz (fun kz => U (ix * (Ny * Nz) + (iy * Nz + kz)))); grind (ematch := 0)
  refine ⟨fun d hd v => z4c3d_char_flux_form p d hd v, fun d N hd hN2 u => sbp_1d_gauss_green p d N hd hN2 dx hdx u,
          hAxisNonpos, fun hAlNN hK1NN hK2 => ?_, fun hSublum ⟨iy0, iz0, hiy0, hiz0, hOutNe⟩ => ?_, fun hSomm d idx c hd hidx _ => ?_⟩
  · have hSplit : 2 * openBoxH0Pair Nx Ny Nz U (z4c3dOpenBoxRhs p Nx Ny Nz dx U) =
        2 * openBoxH0Pair Nx Ny Nz U (fun idx => mulVec 5 (z4c3dSourceMat p) (U idx)) +
        (2 * openBoxH0Pair Nx Ny Nz U (openBoxSbpSatAxis3D p Nx Ny Nz 0 dx U) +
         2 * openBoxH0Pair Nx Ny Nz U (openBoxSbpSatAxis3D p Nx Ny Nz 1 dx U) +
         2 * openBoxH0Pair Nx Ny Nz U (openBoxSbpSatAxis3D p Nx Ny Nz 2 dx U)) := by
      unfold openBoxH0Pair z4c3dOpenBoxRhs
      have hCell : ∀ idx, openBoxWeight3D Nx Ny Nz idx * h0Inner 5 z4c3dSymmetrizer (U idx)
            (fun c => mulVec 5 (z4c3dSourceMat p) (U idx) c + sumTo 3 fun d => openBoxSbpSatAxis3D p Nx Ny Nz d dx U idx c) =
          openBoxWeight3D Nx Ny Nz idx * h0Inner 5 z4c3dSymmetrizer (U idx) (mulVec 5 (z4c3dSourceMat p) (U idx)) +
          (openBoxWeight3D Nx Ny Nz idx * h0Inner 5 z4c3dSymmetrizer (U idx) (openBoxSbpSatAxis3D p Nx Ny Nz 0 dx U idx) +
           (openBoxWeight3D Nx Ny Nz idx * h0Inner 5 z4c3dSymmetrizer (U idx) (openBoxSbpSatAxis3D p Nx Ny Nz 1 dx U idx) +
            openBoxWeight3D Nx Ny Nz idx * h0Inner 5 z4c3dSymmetrizer (U idx) (openBoxSbpSatAxis3D p Nx Ny Nz 2 dx U idx))) := fun idx => by
        rw [show (fun c => mulVec 5 (z4c3dSourceMat p) (U idx) c + sumTo 3 fun d => openBoxSbpSatAxis3D p Nx Ny Nz d dx U idx c) =
            vecAdd (mulVec 5 (z4c3dSourceMat p) (U idx)) (vecAdd (openBoxSbpSatAxis3D p Nx Ny Nz 0 dx U idx)
              (vecAdd (openBoxSbpSatAxis3D p Nx Ny Nz 1 dx U idx) (openBoxSbpSatAxis3D p Nx Ny Nz 2 dx U idx))) by funext c; simp only [sumTo, vecAdd]; grind (ematch := 0),
            h0Inner_add_right, h0Inner_add_right, h0Inner_add_right]; grind (ematch := 0)
      rw [sumTo_congr (fun idx _ => hCell idx), sumTo_add, sumTo_add, sumTo_add]; grind (ematch := 0)
    have hSrcLe : 2 * openBoxH0Pair Nx Ny Nz U (fun idx => mulVec 5 (z4c3dSourceMat p) (U idx)) ≤ (-(2 * (p.kappa1 * p.alpha))) * openBoxH0Energy Nx Ny Nz U := by
      unfold openBoxH0Pair openBoxH0Energy; rw [← sumTo_mul_left, ← sumTo_mul_left]; refine sumTo_le fun idx _ => ?_
      have hWPos : 0 ≤ openBoxWeight3D Nx Ny Nz idx := by
        unfold openBoxWeight3D; exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt (hW1Pos _ _)) (Rat.le_of_lt (hW1Pos _ _))) (Rat.le_of_lt (hW1Pos _ _))
      have hPt : 2 * h0Inner 5 z4c3dSymmetrizer (U idx) (mulVec 5 (z4c3dSourceMat p) (U idx)) ≤ (-(2 * (p.kappa1 * p.alpha))) * h0Inner 5 z4c3dSymmetrizer (U idx) (U idx) := by
        rw [z4c3dSymmetrizer_quadratic_form]
        simp only [h0Inner, dot, mulVec, z4c3dSymmetrizer, z4c3dSymmetrizerRows, z4c3dSourceMat, z4c3dSourceRows, matOf, getOr, sumTo]
        have hr0 : p.kappa1 * p.alpha ≤ p.kappa1 * (2 + p.kappa2) * p.alpha := by
          have := Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_left (show 1 ≤ 2 + p.kappa2 by grind (ematch := 0)) hK1NN) hAlNN; grind (ematch := 0)
        have := Rat.mul_le_mul_of_nonneg_right hr0 (rat_mul_self_nonneg (U idx 0))
        have := Rat.mul_nonneg (Rat.mul_nonneg hK1NN hAlNN) (rat_mul_self_nonneg (U idx 4)); grind (ematch := 0)
      have := rat_mul_mono hWPos hPt; grind (ematch := 0)
    have := hAxisNonpos 0 (by decide); have := hAxisNonpos 1 (by decide); have := hAxisNonpos 2 (by decide); rw [hSplit]; grind (ematch := 0)
  · rw [hAxis0Eq]
    let fibNeg := fun iy iz => -(sbpWeight1D Ny iy * sbpWeight1D Nz iz *
      (2 * sumTo Nx fun ix => sbpWeight1D Nx ix * h0Inner 5 z4c3dSymmetrizer (U (ix * (Ny * Nz) + (iy * Nz + iz)))
        (vecSub (sbpSatPenalty1D p 0 Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz))) ix)
          (mulVec 5 (z4c3dFluxMat p 0) (fun c => sbpDiff1D Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz)) c) ix)))))
    have hFibNN : ∀ iy iz, 0 ≤ fibNeg iy iz := fun iy iz => by
      dsimp only [fibNeg]
      have hm := rat_mul_mono (Rat.le_of_lt (Rat.mul_pos (hW1Pos Ny iy) (hW1Pos Nz iz))) (h1D_nonpos 0 Nx (by decide) hNx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz))))
      grind (ematch := 0)
    have hFibPos : 0 < fibNeg iy0 iz0 := by
      dsimp only [fibNeg]; rw [sbp_1d_sat_identity p 0 Nx (by decide) hNx dx hdx]
      let u0 := fun kx => U (kx * (Ny * Nz) + (iy0 * Nz + iz0))
      have hSumPos : 0 < sumTo 5 (fun m => z4c3dCharWeights m *
          (rmax 0 (-(z4c3dEigVals p 0 m)) * (z4cCharAmplitudes 0 (u0 0) m * z4cCharAmplitudes 0 (u0 0) m) +
           rmax 0 (z4c3dEigVals p 0 m) * (z4cCharAmplitudes 0 (u0 (Nx - 1)) m * z4cCharAmplitudes 0 (u0 (Nx - 1)) m))) := by
        refine sumTo_pos (fun m hm => Rat.mul_nonneg (Rat.le_of_lt (hwPos m hm)) ?_) 0 (by decide) ?_
        · have := Rat.mul_nonneg (le_rmax_left 0 (-(z4c3dEigVals p 0 m))) (rat_mul_self_nonneg (z4cCharAmplitudes 0 (u0 0) m))
          have := Rat.mul_nonneg (le_rmax_left 0 (z4c3dEigVals p 0 m)) (rat_mul_self_nonneg (z4cCharAmplitudes 0 (u0 (Nx - 1)) m)); grind (ematch := 0)
        · obtain ⟨_, hbHi⟩ := ratAbs_bounds_iff.mp (by simpa only [ratAbs_eq_pde] using Rat.le_of_lt hSublum)
          have hLam0 : 0 < z4c3dEigVals p 0 0 := by simp only [z4c3dEigVals, Z4c3DParams.shiftAxis, vecOf, getOr]; grind (ematch := 0)
          have hRm0 : 0 < rmax 0 (z4c3dEigVals p 0 0) := by have := le_rmax_right 0 (z4c3dEigVals p 0 0); grind (ematch := 0)
          have hSqPos : 0 < z4cCharAmplitudes 0 (u0 (Nx - 1)) 0 * z4cCharAmplitudes 0 (u0 (Nx - 1)) 0 := by
            have := rat_mul_self_nonneg (z4cCharAmplitudes 0 (u0 (Nx - 1)) 0); have := rat_mul_ne_zero hOutNe hOutNe; grind (ematch := 0)
          have hLeftNN := Rat.mul_nonneg (le_rmax_left 0 (-(z4c3dEigVals p 0 0))) (rat_mul_self_nonneg (z4cCharAmplitudes 0 (u0 0) 0))
          have hRightPos := Rat.mul_pos hRm0 hSqPos; exact Rat.mul_pos (hwPos 0 (by decide)) (by grind (ematch := 0))
      have hp := Rat.mul_pos (Rat.mul_pos (hW1Pos Ny iy0) (hW1Pos Nz iz0)) (Rat.mul_pos hInvDxPos hSumPos); dsimp [u0] at hp; grind (ematch := 0)
    have hPosAll : 0 < sumTo Ny (fun iy => sumTo Nz fun iz => fibNeg iy iz) :=
      sumTo_pos (fun iy _ => sumTo_nonneg fun iz _ => hFibNN iy iz) iy0 hiy0 (sumTo_pos (fun iz _ => hFibNN iy0 iz) iz0 hiz0 hFibPos)
    have hEqNeg : sumTo Ny (fun iy => sumTo Nz fun iz => (sbpWeight1D Ny iy * sbpWeight1D Nz iz) *
          (2 * sumTo Nx fun ix => sbpWeight1D Nx ix * h0Inner 5 z4c3dSymmetrizer (U (ix * (Ny * Nz) + (iy * Nz + iz)))
            (vecSub (sbpSatPenalty1D p 0 Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz))) ix)
              (mulVec 5 (z4c3dFluxMat p 0) (fun c => sbpDiff1D Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz)) c) ix))))) =
        -(sumTo Ny fun iy => sumTo Nz fun iz => fibNeg iy iz) := by
      have hNegS : ∀ K (g : Nat → Rat), sumTo K (fun j => -g j) = -sumTo K g :=
        fun K g => by rw [show (fun j => -g j) = (fun j => (-1) * g j) by funext j; grind (ematch := 0), sumTo_mul_left]; grind (ematch := 0)
      rw [← hNegS]; refine sumTo_congr fun iy _ => ?_; rw [← hNegS]; exact sumTo_congr fun iz _ => by dsimp [fibNeg]; grind (ematch := 0)
    rw [hEqNeg]; grind (ematch := 0)
  · let ix := idx / (Ny * Nz); let rem := idx % (Ny * Nz); let iy := rem / Nz; let iz := rem % Nz
    have hBlock : 0 < Ny * Nz := Nat.mul_pos (by omega) (by omega)
    have hix : ix < Nx := (Nat.div_lt_iff_lt_mul hBlock).mpr hidx
    have hrem : rem < Ny * Nz := Nat.mod_lt idx hBlock
    have hiy : iy < Ny := (Nat.div_lt_iff_lt_mul (by omega)).mpr hrem
    have hiz : iz < Nz := Nat.mod_lt rem (by omega)
    have hPen0 : (match d with
        | 0 => sbpSatPenalty1D p 0 Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz))) ix
        | 1 => sbpSatPenalty1D p 1 Ny dx (fun ky => U (ix * (Ny * Nz) + (ky * Nz + iz))) iy
        | 2 => sbpSatPenalty1D p 2 Nz dx (fun kz => U (ix * (Ny * Nz) + (iy * Nz + kz))) iz
        | _ => vecZero) c = 0 := by
      have hZeroMulVec : ∀ d' (w : Vec), (∀ m, m < 5 → w m = 0) → mulVec 5 (z4c3dEigVecMat d') w c = 0 := fun d' w hw => by
        unfold mulVec; rw [sumTo_congr fun m hm => show z4c3dEigVecMat d' c m * w m = 0 by rw [hw m hm]; grind (ematch := 0), sumTo_zero]
      have hRmLo : ∀ d' (v0 : Vec), (∀ m, m < 5 → 0 < z4c3dEigVals p d' m → z4cCharAmplitudes d' v0 m = 0) →
          ∀ m, m < 5 → rmax 0 (z4c3dEigVals p d' m) * z4cCharAmplitudes d' v0 m = 0 := fun d' v0 hL m hm => by
        by_cases hP : 0 < z4c3dEigVals p d' m
        · rw [hL m hm hP]; grind (ematch := 0)
        · unfold rmax; split <;> grind (ematch := 0)
      have hRmHi : ∀ d' (vN : Vec), (∀ m, m < 5 → z4c3dEigVals p d' m < 0 → z4cCharAmplitudes d' vN m = 0) →
          ∀ m, m < 5 → rmax 0 (-(z4c3dEigVals p d' m)) * z4cCharAmplitudes d' vN m = 0 := fun d' vN hH m hm => by
        by_cases hN : z4c3dEigVals p d' m < 0
        · rw [hH m hm hN]; grind (ematch := 0)
        · unfold rmax; split <;> grind (ematch := 0)
      have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
      rcases hd3 with rfl | rfl | rfl
      · change sbpSatPenalty1D p 0 Nx dx (fun kx => U (kx * (Ny * Nz) + (iy * Nz + iz))) ix c = 0
        unfold sbpSatPenalty1D; split
        · unfold vecScale; rw [hZeroMulVec 0 _ (hRmLo 0 _ ((hSomm 0 iy iz (by omega) hiy hiz).1 rfl))]; grind (ematch := 0)
        · split
          · unfold vecScale; rw [hZeroMulVec 0 _ (hRmHi 0 _ ((hSomm (Nx - 1) iy iz (by omega) hiy hiz).2.1 (by omega)))]; grind (ematch := 0)
          · rfl
      · change sbpSatPenalty1D p 1 Ny dx (fun ky => U (ix * (Ny * Nz) + (ky * Nz + iz))) iy c = 0
        unfold sbpSatPenalty1D; split
        · unfold vecScale; rw [hZeroMulVec 1 _ (hRmLo 1 _ ((hSomm ix 0 iz hix (by omega) hiz).2.2.1 rfl))]; grind (ematch := 0)
        · split
          · unfold vecScale; rw [hZeroMulVec 1 _ (hRmHi 1 _ ((hSomm ix (Ny - 1) iz hix (by omega) hiz).2.2.2.1 (by omega)))]; grind (ematch := 0)
          · rfl
      · change sbpSatPenalty1D p 2 Nz dx (fun kz => U (ix * (Ny * Nz) + (iy * Nz + kz))) iz c = 0
        unfold sbpSatPenalty1D; split
        · unfold vecScale; rw [hZeroMulVec 2 _ (hRmLo 2 _ ((hSomm ix iy 0 hix hiy (by omega)).2.2.2.2.1 rfl))]; grind (ematch := 0)
        · split
          · unfold vecScale; rw [hZeroMulVec 2 _ (hRmHi 2 _ ((hSomm ix iy (Nz - 1) hix hiy (by omega)).2.2.2.2.2 (by omega)))]; grind (ematch := 0)
          · rfl
    unfold openBoxSbpSatAxis3D vecSub; dsimp only [ix, rem, iy, iz] at hPen0; rw [hPen0]; grind (ematch := 0)

end Obend.Analysis.RelativityBssnZ4c3D
end
