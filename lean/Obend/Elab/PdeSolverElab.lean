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

/-- Pure compile-time gate checking structural/domain/CFL validity, reflective `CanonPoly`
two-state fluctuation conservation, and topological SSA DAG well-formedness across every axis. -/
def checkPdeSolverSpec (spec : ConservationLawSpec) : Bool :=
  spec.checkValid &&
  verifyFluctuationsReflective spec &&
  (List.range spec.numDims).all fun d =>
    checkFluxSsaDag (getOr (specializeFluxSweep spec).axisFluxDags d ⟨[], []⟩)

/-- Pure S-expression parser and compile-time conservation/SSA gate backing `elabConservationLaw`. -/
def validatePdeSolverSexpr (rawText : String) :
    Except String (ConservationLawSpec × SpecializedSweepPlan) := do
  let parsedSpec ← parseConservationLawSexprWithDiag rawText
  if !parsedSpec.checkValid then
    .error "invalid conservation-law specification"
  else if !verifyFluctuationsReflective parsedSpec then
    .error "reflective CanonPoly fluctuation conservation check failed"
  else
    let plan := specializeFluxSweep parsedSpec
    if !(List.range parsedSpec.numDims).all (fun d =>
        checkFluxSsaDag (getOr plan.axisFluxDags d ⟨[], []⟩)) then
      .error "internal SSA DAG topological check failed"
    else
      .ok (parsedSpec, plan)

theorem checkPdeSolverSpec_valid (spec : ConservationLawSpec)
    (h : checkPdeSolverSpec spec = true) :
    spec.checkValid = true ∧
    verifyFluctuationsReflective spec = true ∧
    ∀ d, d < spec.numDims →
      checkFluxSsaDag (getOr (specializeFluxSweep spec).axisFluxDags d ⟨[], []⟩) = true := by
  unfold checkPdeSolverSpec at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Kernel Soundness of `checkPdeSolverSpec` (`checkPdeSolverSpec_sound`)**:
Every `ConservationLawSpec` accepted by `checkPdeSolverSpec` satisfies:
1. Structural, domain-positivity, and CFL bounds (`0 < aMax`, `0 ≤ cfl`, `cfl * aMax ≤ 1`),
2. Exact nonlinear Rusanov fluctuation conservation across every coordinate axis and component,
3. Multi-dimensional Lie & Strang total integral conservation + multi-turn rollout CFL safety,
4. Certified Futamura/CSE SSA DAG lowering (`specializedTotalFlops ≤ naiveTotalFlops` & topological
   DAG well-formedness) and Q32.32 systolic RTL module validity on every axis. -/
theorem checkPdeSolverSpec_sound (spec : ConservationLawSpec) (dims : List Nat)
    (hCheck : checkPdeSolverSpec spec = true) (hPos : ∀ N ∈ dims, 0 < N) :
    spec.checkValid = true ∧
    (0 < spec.aMax ∧ 0 ≤ spec.cfl ∧ spec.cfl * spec.aMax ≤ 1) ∧
    (∀ d i, d < spec.numDims → i < spec.numVars →
      ∀ uL uR : Vec,
        DomainValid spec.domain ⟨uL, spec.paramEnv⟩ →
        DomainValid spec.domain ⟨uR, spec.paramEnv⟩ →
        let fluxD := getOr spec.fluxes d []
        rusanovFluctMinus fluxD spec.paramEnv spec.aMax uL uR i +
          rusanovFluctPlus fluxD spec.paramEnv spec.aMax uL uR i =
          evalFlux (getOr fluxD i (.const 0)) ⟨uR, spec.paramEnv⟩ -
          evalFlux (getOr fluxD i (.const 0)) ⟨uL, spec.paramEnv⟩) ∧
    (let axisFlux := fun d =>
        rusanovNonlinearFlux (getOr spec.fluxes d []) spec.paramEnv spec.aMax
      ∀ ν : Rat, ∀ U : MultiDGrid, ∀ c : Nat,
        totalGridIntegral dims (evalMultiDSweep dims ν axisFlux U) c = totalGridIntegral dims U c ∧
        totalGridIntegral dims (evalStrangSweep dims ν axisFlux U) c = totalGridIntegral dims U c) ∧
    ((specializeFluxSweep spec).specializedTotalFlops ≤ (specializeFluxSweep spec).naiveTotalFlops ∧
      ∀ d, d < spec.numDims →
        checkFluxSsaDag (getOr (specializeFluxSweep spec).axisFluxDags d ⟨[], []⟩) = true ∧
        checkRtlModule (buildSpecSystolicRtl spec d) = true) := by
  obtain ⟨hVal, hRefl, hDags⟩ := checkPdeSolverSpec_valid spec hCheck
  refine ⟨hVal, checkValid_cfl_bounds spec hVal, ?_, ?_, ?_⟩
  · intro d i hd hi uL uR hL hR
    exact (fluctuationConservation_of_reflective spec hRefl d i hd hi uL uR hL hR).1
  · exact (spec_sweep_conserves_integral spec dims hPos).1
  · exact ⟨(specializeFluxSweep_sound spec).1,
      fun d hd => ⟨hDags d hd, spec_systolicRtl_ok spec d⟩⟩

theorem validatePdeSolverSexpr_checks (rawText : String)
    (spec : ConservationLawSpec) (plan : SpecializedSweepPlan)
    (h : validatePdeSolverSexpr rawText = .ok (spec, plan)) :
    parseConservationLawSexprWithDiag rawText = .ok spec ∧
    checkPdeSolverSpec spec = true ∧
    plan = specializeFluxSweep spec := by
  unfold validatePdeSolverSexpr at h
  cases hParse : parseConservationLawSexprWithDiag rawText with
  | error _ => simp [hParse, bind, Except.bind] at h
  | ok parsed =>
    simp only [hParse, bind, Except.bind] at h
    cases hValid : parsed.checkValid with
    | false => simp [hValid] at h
    | true =>
      simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hFluct : verifyFluctuationsReflective parsed with
      | false => simp [hFluct] at h
      | true =>
        simp only [hFluct, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hDag : ((List.range parsed.numDims).all fun d =>
            checkFluxSsaDag (getOr (specializeFluxSweep parsed).axisFluxDags d ⟨[], []⟩)) with
        | false => simp [hDag] at h
        | true =>
          simp only [hDag, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, by simp [checkPdeSolverSpec, hValid, hFluct, hDag], rfl⟩

theorem validatePdeSolverSexpr_of_valid (rawText : String) (spec : ConservationLawSpec)
    (hParse : parseConservationLawSexprWithDiag rawText = .ok spec)
    (hCheck : checkPdeSolverSpec spec = true) :
    validatePdeSolverSexpr rawText = .ok (spec, specializeFluxSweep spec) := by
  obtain ⟨hVal, hRefl, hDags⟩ := checkPdeSolverSpec_valid spec hCheck
  have hAll : ((List.range spec.numDims).all fun d =>
      checkFluxSsaDag (getOr (specializeFluxSweep spec).axisFluxDags d ⟨[], []⟩)) = true := by
    rw [List.all_eq_true]
    intro d hd
    exact hDags d (List.mem_range.mp hd)
  simp [validatePdeSolverSexpr, bind, Except.bind, hParse, hVal, hRefl, hAll]

theorem validatePdeSolverSexpr_iff (rawText : String)
    (spec : ConservationLawSpec) (plan : SpecializedSweepPlan) :
    validatePdeSolverSexpr rawText = .ok (spec, plan) ↔
    (parseConservationLawSexprWithDiag rawText = .ok spec ∧
     checkPdeSolverSpec spec = true ∧
     plan = specializeFluxSweep spec) := by
  constructor
  · exact validatePdeSolverSexpr_checks rawText spec plan
  · rintro ⟨hParse, hCheck, rfl⟩
    exact validatePdeSolverSexpr_of_valid rawText spec hParse hCheck

/-- **End-to-End S-Expression Validation Corollary (`validatePdeSolverSexpr_certified`)**:
Any raw S-expression text accepted by `validatePdeSolverSexpr` parses to a valid
`ConservationLawSpec` passing `checkPdeSolverSpec`, inheriting CFL safety, exact Rusanov
fluctuation conservation, multi-D Lie/Strang integral conservation, SSA DAG FLOP monotonicity,
and verified systolic RTL emission. -/
theorem validatePdeSolverSexpr_certified (rawText : String)
    (spec : ConservationLawSpec) (plan : SpecializedSweepPlan) (dims : List Nat)
    (hOk : validatePdeSolverSexpr rawText = .ok (spec, plan))
    (hPos : ∀ N ∈ dims, 0 < N) :
    checkPdeSolverSpec spec = true ∧
    plan = specializeFluxSweep spec ∧
    spec.checkValid = true ∧
    (0 < spec.aMax ∧ 0 ≤ spec.cfl ∧ spec.cfl * spec.aMax ≤ 1) ∧
    plan.specializedTotalFlops ≤ plan.naiveTotalFlops ∧
    (∀ d, d < spec.numDims → checkRtlModule (buildSpecSystolicRtl spec d) = true) := by
  obtain ⟨_, hCheck, rfl⟩ := validatePdeSolverSexpr_checks rawText spec plan hOk
  have hSound := checkPdeSolverSpec_sound spec dims hCheck hPos
  exact ⟨hCheck, rfl, hSound.1, hSound.2.1, hSound.2.2.2.2.1,
    fun d hd => (hSound.2.2.2.2.2 d hd).2⟩

/-- **CFL Violation Refusal (`checkPdeSolverSpec_refuses_cfl_violation`)**:
Any specification violating `cfl * aMax ≤ 1` is deterministically refused by `checkPdeSolverSpec`. -/
theorem checkPdeSolverSpec_refuses_cfl_violation (spec : ConservationLawSpec)
    (hViol : ¬ (spec.cfl * spec.aMax ≤ 1)) :
    checkPdeSolverSpec spec = false := by
  cases h : checkPdeSolverSpec spec with
  | false => rfl
  | true =>
    have hCfl := (checkValid_cfl_bounds spec (checkPdeSolverSpec_valid spec h).1).2.2
    exact False.elim (hViol hCfl)

/-- **Malformed / Non-Conservative Input Refusal (`validatePdeSolverSexpr_refuses_invalid`)**:
Whenever `parseConservationLawSexprWithDiag` fails or produces a specification rejected by
`checkPdeSolverSpec`, `validatePdeSolverSexpr` refuses with `.error`. -/
theorem validatePdeSolverSexpr_refuses_invalid (rawText : String)
    (hBad : ∀ spec, parseConservationLawSexprWithDiag rawText = .ok spec → checkPdeSolverSpec spec = false) :
    ∀ p, validatePdeSolverSexpr rawText ≠ .ok p := by
  intro ⟨spec, plan⟩ hOk
  obtain ⟨hParse, hCheck, _⟩ := validatePdeSolverSexpr_checks rawText spec plan hOk
  rw [hBad spec hParse] at hCheck
  cases hCheck

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
