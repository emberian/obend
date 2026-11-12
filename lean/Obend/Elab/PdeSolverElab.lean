module
public meta import Lean
public import Lean
public import Obend.Analysis.NonlinearMultiDPde
public meta import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.MultiDStencilTile
public meta import Obend.Hardware.MultiDStencilTile
public import Obend.Tactic.SymDiffAndFlux
public meta import Obend.Tactic.SymDiffAndFlux

/-!
# Compile-Time `#pde_solver` Conservation-Law Elaborator (`Obend.Elab.PdeSolverElab`)

Implements `#pde_solver <Name> := "<conservation-law S-expr>"` and `elabConservationLaw`:
1. Parses and statically checks the declarative multi-dimensional nonlinear conservation-law
   specification at elaboration time (rejecting malformed S-expressions, duplicate identifiers,
   unguarded rational denominators, dimension mismatches, and CFL violations with descriptive
   compile-time diagnostics).
2. Runs compile-time symbolic Fréchet differentiation, cleared-denominator `CanonPoly` fluctuation
   verification, Futamura parameter specialization + CSE SSA DAG lowering, single-pass vertical
   SOAC fusion, multi-dimensional brick halo tiling, and Q32.32 systolic `HDL.RtlModule` synthesis.
3. Emits and kernel-typechecks inside `namespace <Name>`:
   - `<Name>.spec : ConservationLawSpec` & `<Name>.spec_valid : <Name>.spec.checkValid = true`
   - `<Name>.jacobians` & `<Name>.jacobian_frechet_sound` (exact multivariable Fréchet Taylor proof)
   - `<Name>.fluctuation_reflective_ok` & `<Name>.fluctuation_conservative` (reflective `CanonPoly` proof)
   - `<Name>.sweep_conserves_integral` (Lie + Strang multi-D integral conservation + rollout trace safety)
   - `<Name>.minmod_tvd_sound` (2nd-order `minmod` affine exactness, mirror symmetry & MUSCL-Rusanov TVD)
   - `<Name>.specializedPlan`, `<Name>.specializedPlan_sound`, `<Name>.fusedGpuKernel`,
     `<Name>.fusedGpuKernel_sound`, `<Name>.systolicRtl`, and `<Name>.systolicRtl_ok`.
-/

public section
namespace Obend.Elab.PdeSolverElab
open Lean Elab Command Term Meta
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile
open Obend.Tactic.SymDiffAndFlux
set_option autoImplicit false

/-- Term-level compile-time parser & quoter producing a direct `ConservationLawSpec` constructor term. -/
elab "pde_spec_from_sexpr% " s:str : term => do
  match parseConservationLawSexprWithDiag s.getString with
  | .error msg => throwError "[#pde_solver] {msg}"
  | .ok spec => return quoteConservationLawSpec spec

/-- Human-readable summary of compile-time Futamura specialization and CSE FLOP savings. -/
meta def summarizeConservationLawSynthesis (spec : ConservationLawSpec) : String :=
  let plan := specializeFluxSweep spec
  s!"[#pde_solver `{spec.name}`] D={spec.numDims}, m={spec.numVars}, " ++
  s!"FLOPs: {plan.naiveTotalFlops} -> {plan.specializedTotalFlops} (specialized+CSE)"

/-- Programmatic `CommandElabM` entry point synthesizing the full verified solver & accelerator suite
under `namespace <solverId>`. -/
meta def elabConservationLaw (solverId : TSyntax `ident) (sexprLit : TSyntax `str) :
    CommandElabM Unit := do
  let rawText := sexprLit.getString
  let parsedSpec ← match parseConservationLawSexprWithDiag rawText with
    | .error msg =>
      throwErrorAt sexprLit "[#pde_solver `{solverId.getId}`] specification rejected: {msg}"
    | .ok s => pure s
  if !verifyFluctuationsReflective parsedSpec then
    throwErrorAt sexprLit
      "[#pde_solver `{solverId.getId}`] reflective CanonPoly fluctuation conservation check failed"
  let plan := specializeFluxSweep parsedSpec
  for d in List.range parsedSpec.numDims do
    let dag := getOr plan.axisFluxDags d ⟨[], []⟩
    if !checkFluxSsaDag dag then
      throwErrorAt sexprLit
        "[#pde_solver `{solverId.getId}`] internal SSA DAG topological check failed on axis {d}"
  let mkSubId (n : Name) : TSyntax `ident := mkIdentFrom solverId n
  let idSpec := mkSubId `spec
  let idSpecValid := mkSubId `spec_valid
  let idJacobians := mkSubId `jacobians
  let idJacSound := mkSubId `jacobian_frechet_sound
  let idFluctRefl := mkSubId `fluctuation_reflective_ok
  let idFluctCons := mkSubId `fluctuation_conservative
  let idSweepCons := mkSubId `sweep_conserves_integral
  let idMinmodTvd := mkSubId `minmod_tvd_sound
  let idSpecPlan := mkSubId `specializedPlan
  let idSpecPlanSound := mkSubId `specializedPlan_sound
  let idFusedKernel := mkSubId `fusedGpuKernel
  let idFusedKernelSound := mkSubId `fusedGpuKernel_sound
  let idSystolicRtl := mkSubId `systolicRtl
  let idSystolicRtlOk := mkSubId `systolicRtl_ok

  elabCommand (← `(command| namespace $solverId))

  elabCommand (← `(command|
    def $idSpec : Obend.Analysis.NonlinearMultiDPde.ConservationLawSpec :=
      pde_spec_from_sexpr% $sexprLit))

  elabCommand (← `(command|
    private theorem $idSpecValid : ($idSpec).checkValid = true := by decide +kernel))

  elabCommand (← `(command|
    def $idJacobians : List (List (List Obend.Analysis.NonlinearMultiDPde.FluxExpr)) :=
      Obend.Tactic.SymDiffAndFlux.specJacobians $idSpec))

  elabCommand (← `(command|
    theorem $idJacSound
        (d i : Nat) (hd : d < ($idSpec).numDims) (hi : i < ($idSpec).numVars)
        (u V : Obend.Analysis.HyperbolicPde.Vec) (h : Rat)
        (hDom0 : Obend.Analysis.NonlinearMultiDPde.DomainValid ($idSpec).domain ⟨u, ($idSpec).paramEnv⟩)
        (hDom1 : Obend.Analysis.NonlinearMultiDPde.DomainValid ($idSpec).domain
          (Obend.Analysis.NonlinearMultiDPde.shiftVecEnv ($idSpec).numVars ⟨u, ($idSpec).paramEnv⟩ h V)) :
        let fluxD := Obend.Analysis.HyperbolicPde.getOr ($idSpec).fluxes d []
        let jacD := Obend.Analysis.HyperbolicPde.getOr $idJacobians d []
        Obend.Analysis.NonlinearMultiDPde.evalFlux
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0))
            (Obend.Analysis.NonlinearMultiDPde.shiftVecEnv ($idSpec).numVars ⟨u, ($idSpec).paramEnv⟩ h V) -
          Obend.Analysis.NonlinearMultiDPde.evalFlux
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0)) ⟨u, ($idSpec).paramEnv⟩ =
          h * Obend.Analysis.HyperbolicPde.mulVec ($idSpec).numVars
            (Obend.Analysis.NonlinearMultiDPde.evalSymJacobianMat jacD ⟨u, ($idSpec).paramEnv⟩) V i +
          (h * h) * Obend.Analysis.NonlinearMultiDPde.symDirectionalRem ($idSpec).numVars
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0)) ⟨u, ($idSpec).paramEnv⟩ V h :=
      Obend.Tactic.SymDiffAndFlux.spec_jacobian_frechet_sound $idSpec $idSpecValid
        d i hd hi u V h hDom0 hDom1))

  elabCommand (← `(command|
    private theorem $idFluctRefl :
        Obend.Tactic.SymDiffAndFlux.verifyFluctuationsReflective $idSpec = true := by decide +kernel))

  elabCommand (← `(command|
    theorem $idFluctCons
        (d i : Nat) (hd : d < ($idSpec).numDims) (hi : i < ($idSpec).numVars)
        (uL uR : Obend.Analysis.HyperbolicPde.Vec)
        (hDomL : Obend.Analysis.NonlinearMultiDPde.DomainValid ($idSpec).domain ⟨uL, ($idSpec).paramEnv⟩)
        (hDomR : Obend.Analysis.NonlinearMultiDPde.DomainValid ($idSpec).domain ⟨uR, ($idSpec).paramEnv⟩) :
        let fluxD := Obend.Analysis.HyperbolicPde.getOr ($idSpec).fluxes d []
        Obend.Analysis.NonlinearMultiDPde.rusanovFluctMinus fluxD ($idSpec).paramEnv ($idSpec).aMax uL uR i +
          Obend.Analysis.NonlinearMultiDPde.rusanovFluctPlus fluxD ($idSpec).paramEnv ($idSpec).aMax uL uR i =
          Obend.Analysis.NonlinearMultiDPde.evalFlux
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0)) ⟨uR, ($idSpec).paramEnv⟩ -
          Obend.Analysis.NonlinearMultiDPde.evalFlux
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0)) ⟨uL, ($idSpec).paramEnv⟩ ∧
        Obend.Analysis.NonlinearMultiDPde.rusanovFluctMinus fluxD ($idSpec).paramEnv ($idSpec).aMax uL uL i = 0 ∧
        Obend.Analysis.NonlinearMultiDPde.rusanovFluctPlus fluxD ($idSpec).paramEnv ($idSpec).aMax uL uL i = 0 :=
      Obend.Tactic.SymDiffAndFlux.fluctuationConservation_of_reflective $idSpec $idFluctRefl
        d i hd hi uL uR hDomL hDomR))

  elabCommand (← `(command|
    theorem $idSweepCons (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) :
        let axisFlux := fun d =>
          Obend.Analysis.NonlinearMultiDPde.rusanovNonlinearFlux
            (Obend.Analysis.HyperbolicPde.getOr ($idSpec).fluxes d []) ($idSpec).paramEnv ($idSpec).aMax
        (∀ ν : Rat, ∀ U : Obend.Analysis.NonlinearMultiDPde.MultiDGrid, ∀ c : Nat,
          Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims
            (Obend.Analysis.NonlinearMultiDPde.evalMultiDSweep dims ν axisFlux U) c =
            Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims U c ∧
          Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims
            (Obend.Analysis.NonlinearMultiDPde.evalStrangSweep dims ν axisFlux U) c =
            Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims U c) ∧
        (∀ (st0 stF : Obend.Analysis.NonlinearMultiDPde.PdeRolloutState)
            (turns : List Obend.Analysis.NonlinearMultiDPde.PdeRolloutTurn),
          Obend.Analysis.NonlinearMultiDPde.runPdeRolloutTrace $idSpec dims st0 turns = some stF →
          (∀ c, Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims stF.grid c =
            Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims st0.grid c) ∧
          st0.elapsedCourant ≤ stF.elapsedCourant ∧
          stF.acceptedSteps = st0.acceptedSteps + turns.length) ∧
        (∀ (st : Obend.Analysis.NonlinearMultiDPde.PdeRolloutState)
            (turn : Obend.Analysis.NonlinearMultiDPde.PdeRolloutTurn),
          Obend.Analysis.NonlinearMultiDPde.stepPdeRolloutTurn $idSpec dims st turn = none ↔
            ¬ (0 ≤ turn.courant ∧ turn.courant * ($idSpec).aMax ≤ 1)) :=
      Obend.Tactic.SymDiffAndFlux.spec_sweep_conserves_integral $idSpec dims hPos))

  elabCommand (← `(command|
    theorem $idMinmodTvd (u0 s : Rat) (f : Rat → Rat) (ν : Rat) (N : Nat) (u : Nat → Rat) :
        (Obend.Analysis.NonlinearMultiDPde.musclReconstructLeft (u0 - s) u0 (u0 + s) =
          u0 - (1 / 2 : Rat) * s ∧
         Obend.Analysis.NonlinearMultiDPde.musclReconstructRight (u0 - s) u0 (u0 + s) =
          u0 + (1 / 2 : Rat) * s) ∧
        (∀ uPrev uCurr uNext : Rat,
          Obend.Analysis.NonlinearMultiDPde.musclReconstructLeft uNext uCurr uPrev =
            Obend.Analysis.NonlinearMultiDPde.musclReconstructRight uPrev uCurr uNext) ∧
        (0 ≤ ν → 2 * ν * ($idSpec).aMax ≤ 1 →
          (∀ x y : Rat,
            Obend.Analysis.PdeSexprAndApprox.ratAbs (f y - f x) ≤
              ($idSpec).aMax * Obend.Analysis.PdeSexprAndApprox.ratAbs (y - x)) →
          Obend.Analysis.NonlinearMultiDPde.totalVariation1D N
            (Obend.Analysis.NonlinearMultiDPde.musclMinmodRusanov1DStep f ($idSpec).aMax ν N u) ≤
          Obend.Analysis.NonlinearMultiDPde.totalVariation1D N u) := by
      have hBase := Obend.Tactic.SymDiffAndFlux.spec_minmod_tvd_sound $idSpec $idSpecValid
      exact ⟨hBase.1 u0 s, hBase.2.1, fun hν hcfl hLip => hBase.2.2 f ν hν hcfl hLip N u⟩))

  elabCommand (← `(command|
    def $idSpecPlan : Obend.Hardware.MultiDStencilTile.SpecializedSweepPlan :=
      Obend.Hardware.MultiDStencilTile.specializeFluxSweep $idSpec))

  elabCommand (← `(command|
    theorem $idSpecPlanSound (d : Nat) (hd : d < ($idSpec).fluxes.length)
        (u : Obend.Analysis.HyperbolicPde.Vec) :
        ($idSpecPlan).specializedTotalFlops ≤ ($idSpecPlan).naiveTotalFlops ∧
        Obend.Hardware.MultiDStencilTile.evalFluxSsaDag
          (Obend.Analysis.HyperbolicPde.getOr ($idSpecPlan).axisFluxDags d ⟨[], []⟩)
          ⟨u, ($idSpec).paramEnv⟩ =
        (Obend.Analysis.HyperbolicPde.getOr ($idSpec).fluxes d []).map
          (fun e => Obend.Analysis.NonlinearMultiDPde.evalFlux e ⟨u, ($idSpec).paramEnv⟩) := by
      have hBase := Obend.Hardware.MultiDStencilTile.specializeFluxSweep_sound $idSpec
      exact ⟨hBase.1, hBase.2 d hd u⟩))

  elabCommand (← `(command|
    def $idFusedKernel (b : Obend.Hardware.Gpu.StencilTile.StencilBoundary) (dims : List Nat) :
        Obend.Hardware.Gpu.SoacOptimize.FusedProgram :=
      Obend.Tactic.SymDiffAndFlux.buildSpecFusedGpuKernel $idSpec b dims))

  elabCommand (← `(command|
    theorem $idFusedKernelSound
        (b : Obend.Hardware.Gpu.StencilTile.StencilBoundary)
        (dims brickDims : List Nat)
        (grid : List Obend.Hardware.ArrayHypergraph.Word)
        (hNonEmpty : dims ≠ [])
        (hLen : brickDims.length = dims.length)
        (hB2 : ∀ B ∈ brickDims, 2 ≤ B)
        (hBN : ∀ d < dims.length,
          Obend.Analysis.HyperbolicPde.getOr brickDims d 0 ≤
          Obend.Analysis.HyperbolicPde.getOr dims d 0) :
        let e := Obend.Hardware.MultiDStencilTile.multiDMinmodRusanovExpr
          dims.length ($idSpec).cfl.num ($idSpec).aMax.num
        Obend.Hardware.Gpu.SoacOptimize.evalFused (fun _ => grid) ($idFusedKernel b dims) =
          [Obend.Hardware.MultiDStencilTile.evalMultiDBrickTiled brickDims b dims 2
            (Obend.Hardware.Gpu.StencilTile.scalarStencil e) grid] ∧
        Obend.Hardware.MultiDStencilTile.evalMultiDBrickTiled brickDims b dims 2
          (Obend.Hardware.Gpu.StencilTile.scalarStencil e) grid =
          Obend.Hardware.MultiDStencilTile.evalStencilMultiD b dims 2
            (Obend.Hardware.Gpu.StencilTile.scalarStencil e) grid ∧
        Obend.Hardware.MultiDStencilTile.multiDBrickHbmReads brickDims 2 dims <
          (2 * 2 + 1) ^ dims.length * Obend.Analysis.NonlinearMultiDPde.gridCellCount dims :=
      Obend.Tactic.SymDiffAndFlux.spec_fusedGpuKernel_sound $idSpec b dims brickDims grid
        hNonEmpty hLen hB2 hBN))

  elabCommand (← `(command|
    def $idSystolicRtl (axis : Nat) : Obend.Hardware.HDL.RtlModule :=
      Obend.Tactic.SymDiffAndFlux.buildSpecSystolicRtl $idSpec axis))

  elabCommand (← `(command|
    theorem $idSystolicRtlOk (axis : Nat) :
        Obend.Hardware.HDL.checkRtlModule ($idSystolicRtl axis) = true :=
      Obend.Tactic.SymDiffAndFlux.spec_systolicRtl_ok $idSpec axis))

  elabCommand (← `(command| end $solverId))

/-- `#pde_solver <Name> := "<conservation-law S-expr>"`:
Compile-time metaprogrammed multi-dimensional nonlinear conservation-law solver synthesizer and
multi-target accelerator lowering command. -/
syntax (name := pdeSolverCommand) "#pde_solver " ident " := " str : command

@[command_elab pdeSolverCommand]
meta def elabPdeSolverCommand : CommandElab
  | `(#pde_solver $solverId:ident := $sexprLit:str) =>
    elabConservationLaw solverId sexprLit
  | _ => throwUnsupportedSyntax

end Obend.Elab.PdeSolverElab
