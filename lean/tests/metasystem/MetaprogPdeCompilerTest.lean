module
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.MultiDStencilTile
public import Obend.Tactic.SymDiffAndFlux
public import Obend.Elab.PdeSolverElab
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Analysis.Diff
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.RealAnalysis
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.CanonicalExtension
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.LegacyAgreement
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RangeSafe
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.RuntimeOrigins
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Elab.PdeSolverElab
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.ArrayKernel
import all Obend.Hardware.ArrayKernelOwnership
import all Obend.Hardware.ArrayKernelUnique
import all Obend.Hardware.Compiler
import all Obend.Hardware.Gpu
import all Obend.Hardware.Gpu.ArrayEmit
import all Obend.Hardware.Gpu.ArrayEmitCorrect
import all Obend.Hardware.Gpu.ArraySchedule
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.BlockEmit
import all Obend.Hardware.Gpu.BlockLower
import all Obend.Hardware.Gpu.CollectiveArena
import all Obend.Hardware.Gpu.CollectiveArenaCorrect
import all Obend.Hardware.Gpu.CollectiveBlock
import all Obend.Hardware.Gpu.CollectiveBuildCorrect
import all Obend.Hardware.Gpu.CollectiveBuildFacts
import all Obend.Hardware.Gpu.CollectiveCompose
import all Obend.Hardware.Gpu.CollectiveCorrect
import all Obend.Hardware.Gpu.CollectiveExecute
import all Obend.Hardware.Gpu.CollectiveHierarchy
import all Obend.Hardware.Gpu.CollectiveReduceBuild
import all Obend.Hardware.Gpu.CollectiveReduceExec
import all Obend.Hardware.Gpu.CollectiveScanExec
import all Obend.Hardware.Gpu.CollectiveTrace
import all Obend.Hardware.Gpu.CollectiveTree
import all Obend.Hardware.Gpu.Limbs
import all Obend.Hardware.Gpu.Memory
import all Obend.Hardware.Gpu.PhaseSemantics
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.SourceProtocol
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.Gpu.Workgroup
import all Obend.Hardware.HDL
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.Types
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.UpTo
import all Obend.Logic.Claim
import all Obend.Logic.LateBinding
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Protocol
import all Obend.Spec.C4
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.SymDiffAndFlux
import all Obend.Tactic.Tooth

/-!
# Metaprogrammed Multi-Dimensional Nonlinear PDE Solver & Accelerator Test Suite

End-to-end verification of `#pde_solver` (`Obend.Elab.PdeSolverElab`), `SymDiffAndFlux`,
`NonlinearMultiDPde`, and `MultiDStencilTile` across 5 real nonlinear and multi-dimensional
conservation-law systems, adversarial boundary/domain/CFL edge cases, 20 `#tooth` mutation-kill
witnesses, and computational choice / axiom tree audits.
-/

public section
namespace Obend.Tests.MetaprogPdeCompiler
open Obend.Core
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox (ratAbs)
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile
open Obend.Tactic.SymDiffAndFlux
open Obend.Elab.PdeSolverElab
set_option autoImplicit false

/-! ## 1. Five Real Nonlinear & Multi-Dimensional Conservation-Law Systems via `#pde_solver` -/

-- 1.1: 1D Nonlinear Inviscid Burgers Equation: ∂_t u + ∂_x (1/2 u^2) = 0
#pde_solver Burgers1D :=
  "(conservation-law
     (name Burgers1D)
     (coords x)
     (vars u)
     (params)
     (domain)
     (fluxes
       (x (* 1/2 (sq u))))
     (wavespeed 2 1/4)
     (limiter minmod))"

-- 1.2: 3D Compressible Euler Gas Dynamics: (rho, rhou, rhov, rhow, E) with rho > 0
#pde_solver EulerGas3D :=
  "(conservation-law
     (name EulerGas3D)
     (coords x y z)
     (vars rho rhou rhov rhow E)
     (params (gamma 7/5))
     (domain (> rho 0))
     (fluxes
       (x (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (u (/ rhou rho)))
            rhou
            (+ (* rhou u) p)
            (* rhov u)
            (* rhow u)
            (* (+ E p) u)))
       (y (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (v (/ rhov rho)))
            rhov
            (* rhou v)
            (+ (* rhov v) p)
            (* rhow v)
            (* (+ E p) v)))
       (z (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (w (/ rhow rho)))
            rhow
            (* rhou w)
            (* rhov w)
            (+ (* rhow w) p)
            (* (+ E p) w))))
     (wavespeed 4 1/8)
     (limiter minmod))"

-- 1.3: 2D 8-Wave GLM Divergence-Cleaned Ideal Magnetohydrodynamics (9 state variables, rho > 0)
#pde_solver IdealMhd8Wave :=
  "(conservation-law
     (name IdealMhd8Wave)
     (coords x y)
     (vars rho rhou rhov rhow Bx By Bz E psi)
     (params (gamma 5/3) (ch 2))
     (domain (> rho 0))
     (fluxes
       (x (let ((u (/ rhou rho))
                (v (/ rhov rho))
                (w (/ rhow rho))
                (ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (me (* 1/2 (+ (sq Bx) (sq By) (sq Bz))))
                (pGas (* (- gamma 1) (- E (+ ke me))))
                (pTot (+ pGas me))
                (uDotB (+ (* u Bx) (* v By) (* w Bz))))
            rhou
            (- (+ (* rhou u) pTot) (sq Bx))
            (- (* rhov u) (* Bx By))
            (- (* rhow u) (* Bx Bz))
            psi
            (- (* u By) (* v Bx))
            (- (* u Bz) (* w Bx))
            (- (* (+ E pTot) u) (* Bx uDotB))
            (* (sq ch) Bx)))
       (y (let ((u (/ rhou rho))
                (v (/ rhov rho))
                (w (/ rhow rho))
                (ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (me (* 1/2 (+ (sq Bx) (sq By) (sq Bz))))
                (pGas (* (- gamma 1) (- E (+ ke me))))
                (pTot (+ pGas me))
                (uDotB (+ (* u Bx) (* v By) (* w Bz))))
            rhov
            (- (* rhou v) (* By Bx))
            (- (+ (* rhov v) pTot) (sq By))
            (- (* rhow v) (* By Bz))
            (- (* v Bx) (* u By))
            psi
            (- (* v Bz) (* w By))
            (- (* (+ E pTot) v) (* By uDotB))
            (* (sq ch) By))))
     (wavespeed 5 1/10)
     (limiter minmod))"

-- 1.4: 3+1 Curved-Spacetime ADM Electrodynamics (lapse alpha > 0, shift beta^i)
#pde_solver CurvedSpacetimeMaxwell :=
  "(conservation-law
     (name CurvedSpacetimeMaxwell)
     (coords x y z)
     (vars Dx Dy Dz Bx By Bz)
     (params (alpha 4/5) (betax 1/10) (betay -1/10) (betaz 1/20))
     (domain (> alpha 0))
     (fluxes
       (x (- (* betax Dx))
          (- (* alpha Bz) (* betax Dy))
          (- (- (* alpha By)) (* betax Dz))
          (- (* betax Bx))
          (- (- (* alpha Dz)) (* betax By))
          (- (* alpha Dy) (* betax Bz)))
       (y (- (- (* alpha Bz)) (* betay Dx))
          (- (* betay Dy))
          (- (* alpha Bx) (* betay Dz))
          (- (* alpha Dz) (* betay Bx))
          (- (* betay By))
          (- (- (* alpha Dx)) (* betay Bz)))
       (z (- (* alpha By) (* betaz Dx))
          (- (- (* alpha Bx)) (* betaz Dy))
          (- (* betaz Dz))
          (- (- (* alpha Dy)) (* betaz Bx))
          (- (* alpha Dx) (* betaz By))
          (- (* betaz Bz))))
     (wavespeed 2 1/5)
     (limiter minmod))"

-- 1.5: 2D Phase-Space (1x1v) Vlasov-Poisson Kinetic Advection (mMass > 0)
#pde_solver VlasovPoissonPhase :=
  "(conservation-law
     (name VlasovPoissonPhase)
     (coords x vx)
     (vars f Ex)
     (params (qCharge -1) (mMass 1) (vChar 3/2) (jCoef -1/4))
     (domain (> mMass 0))
     (fluxes
       (x (* vChar f) (* jCoef f))
       (vx (* (/ qCharge mMass) (* Ex f)) 0))
     (wavespeed 3 1/6)
     (limiter minmod))"

/-! ## 2. Inhabitedness, Exact Symbolic Fréchet AD, Tadmor Entropy & Symmetrizer Proofs -/

-- Strict compile-time Futamura + CSE FLOP reduction on nonlinear multi-D Euler & 8-wave MHD:
#guard Burgers1D.spec.numDims == 1 && Burgers1D.spec.numVars == 1
#guard EulerGas3D.spec.numDims == 3 && EulerGas3D.spec.numVars == 5
#guard IdealMhd8Wave.spec.numDims == 2 && IdealMhd8Wave.spec.numVars == 9
#guard CurvedSpacetimeMaxwell.spec.numDims == 3 && CurvedSpacetimeMaxwell.spec.numVars == 6
#guard VlasovPoissonPhase.spec.numDims == 2 && VlasovPoissonPhase.spec.numVars == 2
#guard EulerGas3D.specializedPlan.specializedTotalFlops < EulerGas3D.specializedPlan.naiveTotalFlops
#guard IdealMhd8Wave.specializedPlan.specializedTotalFlops < IdealMhd8Wave.specializedPlan.naiveTotalFlops
#guard CurvedSpacetimeMaxwell.specializedPlan.specializedTotalFlops <
  CurvedSpacetimeMaxwell.specializedPlan.naiveTotalFlops

-- Concrete positive-density 3D Euler state & perturbation (non-vacuous DomainValid witness!):
def eulerTestState : Vec
  | 0 => 2      -- rho = 2 > 0
  | 1 => 1      -- rhou = 1
  | 2 => -1     -- rhov = -1 (negative momentum!)
  | 3 => 1 / 2  -- rhow = 1/2
  | 4 => 5      -- E = 5
  | _ => 0

def eulerTestPerturb : Vec
  | 0 => -1 / 2
  | 1 => 1 / 4
  | 2 => -1 / 3
  | 3 => 1 / 5
  | 4 => 1
  | _ => 0

theorem eulerTestState_domainValid :
    DomainValid EulerGas3D.spec.domain ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ := by
  intro t ht
  have htEq : t = .stateVar 0 := by
    revert ht; decide +kernel +revert
  subst htEq
  decide +kernel

theorem eulerTestShifted_domainValid :
    DomainValid EulerGas3D.spec.domain
      (shiftVecEnv EulerGas3D.spec.numVars
        ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ (1 / 10) eulerTestPerturb) := by
  intro t ht
  have htEq : t = .stateVar 0 := by
    revert ht; decide +kernel +revert
  subst htEq
  simp only [shiftVecEnv]
  decide +kernel

-- Concrete instantiation of `EulerGas3D.jacobian_frechet_sound` on x-momentum flux (d=0, i=1):
example :
    let fluxX := getOr EulerGas3D.spec.fluxes 0 []
    let jacX := getOr EulerGas3D.jacobians 0 []
    let h : Rat := 1 / 10
    evalFlux (getOr fluxX 1 (.const 0))
        (shiftVecEnv EulerGas3D.spec.numVars ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ h eulerTestPerturb) -
      evalFlux (getOr fluxX 1 (.const 0)) ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ =
      h * mulVec EulerGas3D.spec.numVars
        (evalSymJacobianMat jacX ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩) eulerTestPerturb 1 +
      (h * h) * symDirectionalRem EulerGas3D.spec.numVars
        (getOr fluxX 1 (.const 0)) ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ eulerTestPerturb h :=
  EulerGas3D.jacobian_frechet_sound 0 1 (by decide) (by decide)
    eulerTestState eulerTestPerturb (1 / 10) eulerTestState_domainValid eulerTestShifted_domainValid

-- Concrete Tadmor Quadratic Entropy Dissipation for Nonlinear Burgers:
-- η(u) = 1/2 u^2, v(u) = u, q(u) = 1/3 u^3, ψ(u) = v(u)f(u) - q(u) = 1/6 u^3,
-- fEC(uL, uR) = 1/6 (uL^2 + uL*uR + uR^2)
def burgersEntropyVar (u : Vec) : Vec := fun c => if c == 0 then u 0 else 0
def burgersEntropyPotential (u : Vec) : Rat := (1 / 6 : Rat) * (u 0 * u 0 * u 0)
def burgersTadmorEcFlux (uL uR : Vec) : Vec := fun c =>
  if c == 0 then (1 / 6 : Rat) * (uL 0 * uL 0 + uL 0 * uR 0 + uR 0 * uR 0) else 0

theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hnx : 0 ≤ -x := by grind
    have hp := Rat.mul_nonneg hnx hnx
    grind

theorem burgers_tadmor_quadratic_entropy_dissipative (N : Nat) (lam : Rat) (hLam : 0 ≤ lam)
    (U : Nat → Vec) :
    let fES : Vec → Vec → Vec := fun uL uR c =>
      burgersTadmorEcFlux uL uR c - (lam / 2) * (uR c - uL c)
    0 ≤ sumTo N (fun i =>
      dot 1 (burgersEntropyVar (U i))
        (fun c => fES (U i) (U (nextCell N i)) c - fES (U (prevCell N i)) (U i) c)) := by
  refine (tadmor_rusanov_entropy_dissipative 1 N
    burgersEntropyVar burgersEntropyPotential burgersTadmorEcFlux lam hLam ?_ ?_ U).2
  · intro uL uR
    simp only [dot, sumTo, burgersEntropyVar, burgersEntropyPotential, burgersTadmorEcFlux,
      beq_self_eq_true, ↓reduceIte]
    let env2 : FluxEnv := ⟨fun k => if k == 0 then uL 0 else uR 0, fun _ => 0⟩
    have hPoly :
        evalFlux (.add (.const 0) (.mul (.sub (.var 1) (.var 0))
          (.mul (.const (1 / 6)) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 1)))
                                       (.mul (.var 1) (.var 1)))))) env2 =
        evalFlux (.sub (.mul (.const (1 / 6)) (.mul (.mul (.var 1) (.var 1)) (.var 1)))
                       (.mul (.const (1 / 6)) (.mul (.mul (.var 0) (.var 0)) (.var 0)))) env2 := by
      flux_eq_by_canon
    simpa [evalFlux, env2] using hPoly
  · intro uL uR
    have hsq := rat_sq_nonneg (uR 0 - uL 0)
    simp only [dot, sumTo, burgersEntropyVar, beq_self_eq_true, ↓reduceIte]
    grind

-- Reflective Friedrichs Identity Symmetrizer for 3+1 Curved-Spacetime ADM Electrodynamics:
def symIdentityMat (m : Nat) : List (List FluxExpr) :=
  (List.range m).map fun i =>
    (List.range m).map fun j => if i == j then .const 1 else .const 0

theorem curvedSpacetimeMaxwell_symmetrizer_symmetric
    (d : Nat) (hd : d < 3) (env : FluxEnv)
    (hDom : DomainValid CurvedSpacetimeMaxwell.spec.domain env)
    (i j : Nat) (hi : i < 6) (hj : j < 6) :
    let jacD := getOr CurvedSpacetimeMaxwell.jacobians d []
    let HJ := symMatMul 6 (symIdentityMat 6) jacD
    evalFlux (getOr (getOr HJ i []) j (.const 0)) env =
      evalFlux (getOr (getOr HJ j []) i (.const 0)) env := by
  have hAll : (List.range 3).all (fun ax =>
      checkSymmetrizerReflective CurvedSpacetimeMaxwell.spec.domain 6
        (symIdentityMat 6) (getOr CurvedSpacetimeMaxwell.jacobians ax [])) = true := by decide +kernel
  simp only [List.all_eq_true] at hAll
  exact symmetrizerReflective_sound CurvedSpacetimeMaxwell.spec.domain 6
    (symIdentityMat 6) (getOr CurvedSpacetimeMaxwell.jacobians d [])
    (hAll d (List.mem_range.mpr hd)) env hDom i j hi hj

/-! ## 3. Tactical Automation (`flux_eq_by_canon`, `sym_jacobian_frechet`) & Edge Cases -/

-- Tactic `flux_eq_by_canon` discharging rational conservation rearrangement with `invSafe`:
example (env : FluxEnv) (hDom : DomainValid [.stateVar 0] env) :
    let rho := FluxExpr.var 0
    let rhou := FluxExpr.var 1
    let E := FluxExpr.var 2
    let gamma := FluxExpr.const (7 / 5)
    let ke := FluxExpr.mul (.const (1 / 2)) (.divSafe (.mul rhou rhou) rho)
    let p := FluxExpr.mul (.sub gamma (.const 1)) (.sub E ke)
    evalFlux (.add (.mul rhou (.divSafe rhou rho)) p) env =
      evalFlux (.add (.mul (.const (2 / 5)) E)
                     (.mul (.const (4 / 5)) (.divSafe (.mul rhou rhou) rho))) env := by
  flux_eq_by_canon

-- Tactic `sym_jacobian_frechet` discharging closed multivariable Taylor expansion:
example (env : FluxEnv) (V : Vec) (h : Rat) :
    let e := FluxExpr.mul (.const (1 / 2)) (.mul (.var 0) (.var 0))
    evalFlux e (shiftVecEnv 1 env h V) - evalFlux e env =
      h * evalDirectionalDeriv 1 e env V + (h * h) * symDirectionalRem 1 e env V h := by
  sym_jacobian_frechet

-- Adversarial Edge Case 1: Non-multiple multi-D grids & brick tail dimensions!
-- 2D `[7, 5]` grid tiled by `[4, 4]` bricks (tail bricks `3×4`, `4×1`, `3×1`),
-- and 3D `[5, 3, 4]` grid tiled by `[2, 2, 3]` bricks:
def sampleGrid2D : List Word := (List.range 35).map fun k => BitVec.ofNat 64 (k * 17 + 3)
def sampleGrid3D : List Word := (List.range 60).map fun k => BitVec.ofNat 64 (k * 13 + 5)

theorem idealMhd_nonmultiple_brick_gpu_sound (grid : List Word) :
    let dims := [7, 5]
    let bricks := [4, 4]
    let e := multiDMinmodRusanovExpr 2 IdealMhd8Wave.spec.cfl.num IdealMhd8Wave.spec.aMax.num
    evalFused (fun _ => grid) (IdealMhd8Wave.fusedGpuKernel .periodic dims) =
      [evalMultiDBrickTiled bricks .periodic dims 2 (scalarStencil e) grid] ∧
    multiDBrickHbmReads bricks 2 dims < (2 * 2 + 1) ^ 2 * gridCellCount dims := by
  have h := IdealMhd8Wave.fusedGpuKernel_sound .periodic [7, 5] [4, 4] grid
    (by decide) (by decide) (by decide) (fun d hd => by
      match d with
      | 0 => decide
      | 1 => decide
      | n + 2 => simp at hd; omega)
  exact ⟨h.1, h.2.2⟩

theorem euler3D_nonmultiple_brick_gpu_sound (grid : List Word) :
    let dims := [5, 3, 4]
    let bricks := [2, 2, 3]
    let e := multiDMinmodRusanovExpr 3 EulerGas3D.spec.cfl.num EulerGas3D.spec.aMax.num
    evalFused (fun _ => grid) (EulerGas3D.fusedGpuKernel .clamp dims) =
      [evalMultiDBrickTiled bricks .clamp dims 2 (scalarStencil e) grid] ∧
    multiDBrickHbmReads bricks 2 dims < (2 * 2 + 1) ^ 3 * gridCellCount dims := by
  have h := EulerGas3D.fusedGpuKernel_sound .clamp [5, 3, 4] [2, 2, 3] grid
    (by decide) (by decide) (by decide) (fun d hd => by
      match d with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | n + 3 => simp at hd; omega)
  exact ⟨h.1, h.2.2⟩

-- Adversarial Edge Case 2: Negative slopes & negative velocities in MUSCL-`minmod` TVD:
#guard musclReconstructLeft (4 - (-3 / 2)) 4 (4 + (-3 / 2)) == 4 - (1 / 2 : Rat) * (-3 / 2)
#guard musclReconstructRight (4 - (-3 / 2)) 4 (4 + (-3 / 2)) == 4 + (1 / 2 : Rat) * (-3 / 2)

def negVelProfile : Nat → Rat
  | 0 => -3 / 2
  | 1 => 1 / 2
  | 2 => -1
  | _ => 1 / 4

#guard totalVariation1D 4
    (musclMinmodRusanov1DStep (fun w => (1 / 2 : Rat) * (w * w)) 2 (1 / 4) 4 negVelProfile) ≤
  totalVariation1D 4 negVelProfile

example (N : Nat) (u : Nat → Rat) :
    totalVariation1D N (musclMinmodRusanov1DStep (fun w => (-3 / 2 : Rat) * w) 2 (1 / 4) N u) ≤
      totalVariation1D N u := by
  have hTvd := (Burgers1D.minmod_tvd_sound 0 (-3 / 2)
    (fun w => (-3 / 2 : Rat) * w) (1 / 4) N u).2.2
  have haMax : Burgers1D.spec.aMax = 2 := by decide +kernel
  rw [haMax] at hTvd
  refine hTvd (by decide +kernel) (by decide +kernel) (fun x y => ?_)
  have hScale : (-3 / 2 : Rat) * y - (-3 / 2 : Rat) * x = (-3 / 2 : Rat) * (y - x) := by grind
  rw [hScale]
  unfold ratAbs
  by_cases hd : y - x < 0
  · have hpos : ¬ ((-3 / 2 : Rat) * (y - x) < 0) := by
      have hm := Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ 3 / 2) (by grind : 0 ≤ -(y - x))
      grind
    have hle := Rat.mul_le_mul_of_nonneg_right
      (by decide +kernel : (3 / 2 : Rat) ≤ 2) (by grind : 0 ≤ -(y - x))
    simp only [hd, hpos, ↓reduceIte]; grind
  · by_cases hz : y - x = 0
    · rw [hz]; decide +kernel
    · have hneg : (-3 / 2 : Rat) * (y - x) < 0 := by
        have hm := Rat.mul_pos (by decide +kernel : (0 : Rat) < 3 / 2) (by grind : 0 < y - x)
        grind
      have hle := Rat.mul_le_mul_of_nonneg_right
        (by decide +kernel : (3 / 2 : Rat) ≤ 2) (by grind : 0 ≤ y - x)
      simp only [hd, hneg, ↓reduceIte]; grind

-- Adversarial Edge Case 3: Compile-time parser domain-guard & CFL refusal checks:
-- (a) Unguarded division by `rho` (missing `(domain (> rho 0))`) MUST be refused:
#guard (parseConservationLawSexpr
  "(conservation-law (name BadEuler) (coords x) (vars rho rhou) (params) (domain)
     (fluxes (x rhou (/ (sq rhou) rho))) (wavespeed 2 1/4) (limiter minmod))").isNone

-- (b) CFL violation `cfl * aMax = 4 * 1/2 = 2 > 1` MUST be refused:
#guard (parseConservationLawSexpr
  "(conservation-law (name BadCfl) (coords x) (vars u) (params) (domain)
     (fluxes (x u)) (wavespeed 4 1/2) (limiter minmod))").isNone

-- (c) Duplicate state variable names MUST be refused:
#guard (parseConservationLawSexpr
  "(conservation-law (name DupVar) (coords x) (vars u u) (params) (domain)
     (fluxes (x u u)) (wavespeed 1 1/2) (limiter minmod))").isNone

-- (d) Flux component count mismatch MUST be refused:
#guard (parseConservationLawSexpr
  "(conservation-law (name BadRow) (coords x y) (vars u v) (params) (domain)
     (fluxes (x u v) (y u)) (wavespeed 1 1/2) (limiter minmod))").isNone

-- (e) Unready GPU LDS halo barrier phases refused:
#guard executeBrickHaloPhases 2 [4, 4] (scalarStencil (.const 1))
  (fun _ => sampleGrid2D.toArray) [.cooperativeLoad, .localCompute] #[] true == #[]
#guard executeBrickHaloPhases 2 [4, 4] (scalarStencil (.const 1))
  (fun _ => sampleGrid3D.toArray) [.localCompute] #[] false == #[]

-- (f) Multi-turn rollout rejects over-limit Courant step and accepts valid trace on Vlasov-Poisson:
def vpInitState : PdeRolloutState :=
  { grid := fun idx c => if idx == 0 && c == 0 then 2 else 1 / 2
    elapsedCourant := 0
    acceptedSteps := 0 }

#guard (stepPdeRolloutTurn VlasovPoissonPhase.spec [4, 4] vpInitState ⟨1 / 2, true⟩).isNone
#guard (runPdeRolloutTrace VlasovPoissonPhase.spec [4, 4] vpInitState
  [⟨1 / 6, false⟩, ⟨1 / 4, true⟩]).isSome

-- (g) `RangeSafe` Q32.32 magnitude bound propagation succeeds on bounded 3D Euler SSA DAG:
def boundedQ32Box : Nat → RangeSafe.Interval := fun _ => RangeSafe.Interval.mkNat 0 (16 * 2 ^ 32)
#guard (inferSsaDagMagnitudeIntervals boundedQ32Box
  (getOr EulerGas3D.specializedPlan.axisFluxDags 0 ⟨[], []⟩)).isSome
#guard checkRtlModule (EulerGas3D.systolicRtl 0) &&
       checkRtlModule (IdealMhd8Wave.systolicRtl 1) &&
       checkRtlModule (CurvedSpacetimeMaxwell.systolicRtl 2) &&
       checkRtlModule (VlasovPoissonPhase.systolicRtl 1)

/-! ## 4. Mutation-Sensitivity `#tooth` Suite (21 Kernel-Checked Mutation Kills) -/

def acceptPos (_ : List PosTarget) (_ : FluxExpr) : Bool := true
def zeroSymPartial (_ : Nat) (_ : FluxExpr) : FluxExpr := .const 0
def emptySymJac (_ : Nat) (_ : List FluxExpr) : List (List FluxExpr) := []
def acceptReflective (_ : List PosTarget) (_ _ : FluxExpr) : Bool := true
def brokenNumFlux (_ : List FluxExpr) (_ : Nat → Rat) (_ : Rat) (_ _ : Vec) (_ : Nat) : Rat := 1
def amplifyMinmodStep (_ : Rat → Rat) (_ _ : Rat) (_ : Nat) (u : Nat → Rat) (i : Nat) : Rat := 2 * u i
def nonConservativeSweep (_ : List Nat) (_ : Nat) (_ : Rat) (_ : Vec → Vec → Vec)
    (U : MultiDGrid) (idx c : Nat) : Rat := U idx c + 1
def ignoreCflTurn (_ : ConservationLawSpec) (_ : List Nat) (st : PdeRolloutState)
    (_ : PdeRolloutTurn) : Option PdeRolloutState := some st
def zeroSpecialize (_ : Option (Nat → Rat)) (_ : FluxExpr) : FluxExpr := .const 0
def emptySsaDag (_ : Option (Nat → Rat)) (_ : List FluxExpr) : FluxSsaDag := ⟨[], []⟩
def emptyBrickTiled (_ : List Nat) (_ : StencilBoundary) (_ : List Nat) (_ : Nat)
    (_ : List Word → Word) (_ : List Word) : List Word := []
def emptyFusedProg (_ : StencilBoundary) (_ : List Nat) (_ : Nat) (_ : ScalarExpr) :
    FusedProgram := .ret []
def brokenSystolicRtl (modName : String) (varNames : List String) (_ : FluxSsaDag) : RtlModule :=
  { name := modName
    inputNames := varNames
    wires := []
    regs := []
    outputs := [{ name := "dangling", expr := .wireRef 99, width := 64 }] }

def bogusParsedSpec (_ : String) : Option ConservationLawSpec :=
  some ⟨"bad", [], [], [], [], [], 0, 0, .firstOrder⟩

#tooth checkExprPositive_sound by mutation checkExprPositive := acceptPos
#tooth checkExprDomainSafe_implies_denomNonzero by mutation checkExprDomainSafe := acceptPos
#tooth symExpr_frechet_taylor by mutation symPartial := zeroSymPartial
#tooth symJacobian_frechet_taylor by mutation symJacobian := emptySymJac
#tooth checkFluxEqReflective_sound by mutation checkFluxEqReflective := acceptReflective
#tooth rusanovNonlinearFlux_consistent by mutation rusanovNonlinearFlux := brokenNumFlux
#tooth rusanovFluct_conservation by mutation rusanovFluctMinus := brokenNumFlux
#tooth muscl_minmod_linear_exact by mutation minmod := fun _ _ => 0
#tooth tvd_rusanov_minmod_step_nonincreasing by mutation musclMinmodRusanov1DStep := amplifyMinmodStep
#tooth multiDSweep_conserves_total_mass_momentum_energy by mutation evalDirectionalSweep := nonConservativeSweep
#tooth stepPdeRolloutTurn_none_iff_cfl_violation by mutation stepPdeRolloutTurn := ignoreCflTurn
#tooth specializeFluxExpr_sound by mutation specializeFluxExpr := zeroSpecialize
#tooth compileFluxSsaDag_sound by mutation checkFluxSsaDag := fun _ => false
#tooth specializeFluxSweep_sound by mutation compileFluxSsaDag := emptySsaDag
#tooth multiDBrickTiled_eq_global_sweep by mutation evalMultiDBrickTiled := emptyBrickTiled
#tooth compileMultiDSweepFused_sound by mutation compileMultiDSweepFused := emptyFusedProg
#tooth emitSystolicFluxCellRtlModule_ok by mutation emitSystolicFluxCellRtlModule := brokenSystolicRtl
#tooth parseConservationLawSexpr_valid by mutation parseConservationLawSexpr := bogusParsedSpec
#tooth spec_jacobian_frechet_sound by mutation ConservationLawSpec.checkValid := fun _ => true
#tooth fluctuationConservation_of_reflective by mutation verifyFluctuationsReflective := fun _ => true
#tooth symmetrizerReflective_sound by mutation checkSymmetrizerReflective := fun _ _ _ _ => true

/-! ## 5. Axiom Census, Zero-Closed-Theorem & Zero-Computational-Choice Audit -/

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
  let ownModules := [
    `Obend.Analysis.NonlinearMultiDPde,
    `Obend.Hardware.MultiDStencilTile,
    `Obend.Tactic.SymDiffAndFlux,
    `Obend.Elab.PdeSolverElab
  ]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  for name in [
      ``parseConservationLawSexpr,
      ``symPartial,
      ``symJacobian,
      ``checkFluxEqReflective,
      ``specializeFluxSweep,
      ``evalMultiDBrickTiled,
      ``compileMultiDSweepFused,
      ``emitSystolicFluxCellRtlModule
    ] do
    Lean.Elab.Command.liftTermElabM do
      let _ ← (auditComputationalChoice (Lean.mkConst name)).run {}
      pure ()
  Lean.logInfo "MetaprogPdeCompiler audit passed: 0 compiler-trust axioms, 0 closed library theorems, 0 computational choice."

#assert_axioms_tree
end Obend.Tests.MetaprogPdeCompiler
