module
public meta import Lean
public import Obend.Analysis.PdeSexprAndApprox
public meta import Obend.Analysis.PdeSexprAndApprox
public import Obend.Analysis.NonlinearMultiDPde
public meta import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.MultiDStencilTile
public meta import Obend.Hardware.MultiDStencilTile
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.OpenHypergraph

/-!
# Symbolic PDE proofs and accelerator refinement

Symbolic Fréchet differentiation, reflective conservation and symmetrizers, Q32 arithmetic,
shared nonlinear source lowering, and accelerator soundness. Parsing lives with the elaborator
in `PdeSolverElab`; its existing declaration names remain unchanged.
-/

public section
namespace Obend.Hardware.MultiDStencilTile
open Obend.Hardware.HDL Obend.Analysis.HyperbolicPde Obend.Analysis.NonlinearMultiDPde
theorem checkExprDAG_mono (ni nr a b : Nat) (e : RtlExpr) (hab : a ≤ b)
    (h : checkExprDAG ni nr a e = true) : checkExprDAG ni nr b e = true := by
  induction e <;> simp_all [checkExprDAG] <;> omega

theorem ssaWireRef_dag (ni nr base bound a : Nat) (refs : Array Nat) (h : base ≤ bound) :
    checkExprDAG ni nr bound (ssaWireRef refs base a) = true := by
  unfold ssaWireRef
  split
  · split <;> simp_all [checkExprDAG] <;> omega
  · rfl

theorem assignRtlExprs_length (idx : Nat) (es : List RtlExpr) :
    (assignRtlExprs idx es).length = es.length := by
  induction es generalizing idx with
  | nil => rfl
  | cons e es ih => simp [assignRtlExprs, ih]

theorem reciprocalRtlExprs_dag (ni nr base : Nat) (d : RtlExpr)
    (h : checkExprDAG ni nr base d = true) :
    checkWireTableDAG.go ni nr base (assignRtlExprs base (reciprocalRtlExprs base d)) = true := by
  have h1 := checkExprDAG_mono ni nr base (base + 1) d (by omega) h
  simp [reciprocalRtlExprs, assignRtlExprs, checkWireTableDAG.go, checkExprDAG,
    h, h1, Nat.add_assoc]

theorem lowerSsaNodeToRtl_dag (ni nr base : Nat) (refs : Array Nat)
    (params : Nat → Rat) (n : FluxSsaNode) :
    checkWireTableDAG.go ni nr base
      (assignRtlExprs base (lowerSsaNodeToRtl ni base refs params n)) = true := by
  cases n with
  | invSafe d => exact reciprocalRtlExprs_dag ni nr base _ (ssaWireRef_dag _ _ _ _ _ _ (by omega))
  | var i => simp only [lowerSsaNodeToRtl]; split <;> simp_all [assignRtlExprs, checkWireTableDAG.go, checkExprDAG]
  | _ => simp [lowerSsaNodeToRtl, assignRtlExprs, checkWireTableDAG.go, checkExprDAG,
      ssaWireRef_dag ni nr base base _ refs (by omega)]

theorem checkWireTableDAG_go_append (ni nr idx : Nat) (xs ys : List WireAssign) :
    checkWireTableDAG.go ni nr idx (xs ++ ys) =
      (checkWireTableDAG.go ni nr idx xs && checkWireTableDAG.go ni nr (idx + xs.length) ys) := by
  induction xs generalizing idx with
  | nil => simp [checkWireTableDAG.go]
  | cons x xs ih => simp [checkWireTableDAG.go, ih, Bool.and_assoc, Nat.add_assoc, Nat.add_comm 1]

theorem lowerSsaNodesToWires_dag_go (ni nr idx : Nat) (refs : Array Nat)
    (params : Nat → Rat) (ns : List FluxSsaNode) :
    checkWireTableDAG.go ni nr idx (lowerSsaNodesToWires ni params idx refs ns).1 = true := by
  induction ns generalizing idx refs with
  | nil => rfl
  | cons n ns ih =>
    simp only [lowerSsaNodesToWires, checkWireTableDAG_go_append, assignRtlExprs_length]
    rw [lowerSsaNodeToRtl_dag, ih]
    rfl

/-- Every generated systolic module has topological wires and single-domain pipeline registers. -/
theorem emitSystolicFluxCellRtlModule_ok (modName : String) (varNames : List String)
    (dag : FluxSsaDag) (params : Nat → Rat := fun _ => 0) :
    checkRtlModule (emitSystolicFluxCellRtlModule modName varNames dag params) = true := by
  unfold emitSystolicFluxCellRtlModule checkRtlModule
  dsimp only
  have hWT := lowerSsaNodesToWires_dag_go varNames.length
    ((dag.roots.map (fun r => (lowerSsaNodesToWires varNames.length params 0 #[] dag.nodes).2.getD r 0)).filter
      (· < (lowerSsaNodesToWires varNames.length params 0 #[] dag.nodes).1.length)).length
    0 #[] params dag.nodes
  simp only [checkWireTableDAG, List.length_map, List.length_range, hWT,
    Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro r hr
    rw [List.mem_map] at hr; obtain ⟨k, hk, rfl⟩ := hr
    have hm := getOr_mem_of_lt _ k 0 (List.mem_range.mp hk)
    rw [List.mem_filter] at hm
    simpa [checkExprDAG] using of_decide_eq_true hm.2
  · rw [List.all_eq_true]
    intro o ho
    rw [List.mem_map] at ho; obtain ⟨k, hk, rfl⟩ := ho
    simpa [checkExprDAG] using List.mem_range.mp hk
  · unfold checkModuleCdc
    rw [List.all_eq_true]
    intro dst hdst
    rw [List.mem_map] at hdst; obtain ⟨k, _, rfl⟩ := hdst
    simp [checkRegCdc, exprReadRegs, exprReadRegsAndWires]

end Obend.Hardware.MultiDStencilTile

namespace Obend.Tactic.SymDiffAndFlux
open Lean Elab Tactic Meta
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.ArraySource
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile
set_option autoImplicit false

/-! ## 2. Certified Symbolic Jacobian, Reflective `CanonPoly` & Accelerator Lowering Theorems -/

/-- Exact symbolic Jacobian tensor `[J_0(U), …, J_{D-1}(U)]` across all spatial/phase-space axes. -/
@[expose] def specJacobians (spec : ConservationLawSpec) : List (List (List FluxExpr)) :=
  spec.fluxes.map (symJacobian spec.numVars)

theorem checkValid_flux_row_len (s : ConservationLawSpec) (hValid : s.checkValid = true)
    (d : Nat) (hd : d < s.numDims) :
    (getOr s.fluxes d []).length = s.numVars := by
  unfold ConservationLawSpec.checkValid at hValid
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hValid
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hFluxLen⟩, hRows⟩, _⟩ := hValid
  have hd' : d < s.fluxes.length := by unfold ConservationLawSpec.numDims at hd; omega
  exact (hRows (getOr s.fluxes d []) (getOr_mem_of_lt s.fluxes d [] hd')).1

theorem checkValid_cfl_bounds (s : ConservationLawSpec) (hValid : s.checkValid = true) :
    0 < s.aMax ∧ 0 ≤ s.cfl ∧ s.cfl * s.aMax ≤ 1 := by
  unfold ConservationLawSpec.checkValid at hValid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hValid
  exact hValid.2

theorem checkValid_fluxes_len (s : ConservationLawSpec) (hValid : s.checkValid = true) :
    s.fluxes.length = s.numDims := by
  unfold ConservationLawSpec.checkValid at hValid
  unfold ConservationLawSpec.numDims
  simp only [Bool.and_eq_true, beq_iff_eq] at hValid
  exact hValid.1.1.2

/-- **Directional Symbolic Jacobian Fréchet Soundness (`spec_jacobian_frechet_sound`)**:
For every coordinate axis `d < spec.numDims` and conserved component `i < spec.numVars`, row `d` of
`specJacobians spec` is the exact multivariable Fréchet derivative of `F_d(U)` with explicit
quadratic rational remainder `h² · R_{d,i}(U, V, h)` on `DomainValid spec.domain`. -/
theorem spec_jacobian_frechet_sound (spec : ConservationLawSpec) (hValid : spec.checkValid = true)
    (d i : Nat) (hd : d < spec.numDims) (hi : i < spec.numVars)
    (u V : Vec) (h : Rat)
    (hDom0 : DomainValid spec.domain ⟨u, spec.paramEnv⟩)
    (hDom1 : DomainValid spec.domain (shiftVecEnv spec.numVars ⟨u, spec.paramEnv⟩ h V)) :
    let fluxD := getOr spec.fluxes d []
    let jacD := getOr (specJacobians spec) d []
    evalFlux (getOr fluxD i (.const 0)) (shiftVecEnv spec.numVars ⟨u, spec.paramEnv⟩ h V) -
      evalFlux (getOr fluxD i (.const 0)) ⟨u, spec.paramEnv⟩ =
      h * mulVec spec.numVars (evalSymJacobianMat jacD ⟨u, spec.paramEnv⟩) V i +
      (h * h) * symDirectionalRem spec.numVars (getOr fluxD i (.const 0)) ⟨u, spec.paramEnv⟩ V h := by
  dsimp only [specJacobians]
  have hd' : d < spec.fluxes.length := by rw [checkValid_fluxes_len spec hValid]; exact hd
  rw [getOr_map_lt spec.fluxes (symJacobian spec.numVars) d [] [] hd']
  exact symJacobian_frechet_taylor spec.domain spec.numVars (getOr spec.fluxes d [])
    (checkValid_flux_row_len spec hValid d hd)
    (fun k hk => ConservationLawSpec.checkValid_flux_domainSafe spec hValid d k hd hk)
    ⟨u, spec.paramEnv⟩ V h hDom0 hDom1 i hi

/-- Interleave two state vectors `(uL, uR)` at even/odd variable slots and bind `.param 0 := aMax`
so two-state interface identities can be decided reflectively via `CanonPoly` / `RatCanon`. -/
def injLeftVars : FluxExpr → FluxExpr
  | .const q => .const q
  | .var k => .var (2 * k)
  | .param p => .param (p + 1)
  | .neg a => .neg (injLeftVars a)
  | .add a b => .add (injLeftVars a) (injLeftVars b)
  | .sub a b => .sub (injLeftVars a) (injLeftVars b)
  | .mul a b => .mul (injLeftVars a) (injLeftVars b)
  | .invSafe d => .invSafe (injLeftVars d)

def injRightVars : FluxExpr → FluxExpr
  | .const q => .const q
  | .var k => .var (2 * k + 1)
  | .param p => .param (p + 1)
  | .neg a => .neg (injRightVars a)
  | .add a b => .add (injRightVars a) (injRightVars b)
  | .sub a b => .sub (injRightVars a) (injRightVars b)
  | .mul a b => .mul (injRightVars a) (injRightVars b)
  | .invSafe d => .invSafe (injRightVars d)

def twoStateInterleavedEnv (params : Nat → Rat) (aMax : Rat) (uL uR : Vec) : FluxEnv where
  state := fun idx => if idx % 2 == 0 then uL (idx / 2) else uR (idx / 2)
  params := fun p => if p == 0 then aMax else params (p - 1)

def twoStateInterleavedDom (dom : List PosTarget) : List PosTarget :=
  dom.flatMap fun
    | .stateVar k => [.stateVar (2 * k), .stateVar (2 * k + 1)]
    | .paramVar p => [.paramVar (p + 1)]

theorem evalFlux_injLeftVars (params : Nat → Rat) (aMax : Rat) (uL uR : Vec) (e : FluxExpr) :
    evalFlux (injLeftVars e) (twoStateInterleavedEnv params aMax uL uR) =
      evalFlux e ⟨uL, params⟩ := by
  induction e with
  | const _ => rfl
  | var k =>
    simp [injLeftVars, evalFlux, twoStateInterleavedEnv,
      show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega]
  | param p =>
    simp [injLeftVars, evalFlux, twoStateInterleavedEnv]
  | neg a iha => simp [injLeftVars, evalFlux, iha]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | invSafe a iha =>
    simp_all [injLeftVars, evalFlux]

theorem evalFlux_injRightVars (params : Nat → Rat) (aMax : Rat) (uL uR : Vec) (e : FluxExpr) :
    evalFlux (injRightVars e) (twoStateInterleavedEnv params aMax uL uR) =
      evalFlux e ⟨uR, params⟩ := by
  induction e with
  | const _ => rfl
  | var k =>
    simp [injRightVars, evalFlux, twoStateInterleavedEnv,
      show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]
  | param p =>
    simp [injRightVars, evalFlux, twoStateInterleavedEnv]
  | neg a iha => simp [injRightVars, evalFlux, iha]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | invSafe a iha =>
    simp_all [injRightVars, evalFlux]

theorem domainValid_twoStateInterleaved (dom : List PosTarget) (params : Nat → Rat) (aMax : Rat)
    (uL uR : Vec)
    (hL : DomainValid dom ⟨uL, params⟩) (hR : DomainValid dom ⟨uR, params⟩) :
    DomainValid (twoStateInterleavedDom dom) (twoStateInterleavedEnv params aMax uL uR) := by
  intro t ht
  unfold twoStateInterleavedDom at ht
  rw [List.mem_flatMap] at ht
  obtain ⟨src, hSrcMem, hTarget⟩ := ht
  cases src with
  | stateVar k =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTarget
    rcases hTarget with rfl | rfl
    · simpa [twoStateInterleavedEnv, show (2 * k) % 2 = 0 by omega,
        show (2 * k) / 2 = k by omega] using hL (.stateVar k) hSrcMem
    · simpa [twoStateInterleavedEnv, show (2 * k + 1) % 2 = 1 by omega,
        show (2 * k + 1) / 2 = k by omega] using hR (.stateVar k) hSrcMem
  | paramVar p =>
    simp only [List.mem_singleton] at hTarget
    subst hTarget
    simpa [twoStateInterleavedEnv] using hL (.paramVar p) hSrcMem

/-- Construct the reflective two-state `FluxExpr` pair `(A⁻ΔQ + A⁺ΔQ, F(U_R) - F(U_L))` for `(d, i)`. -/
def fluctReflectiveExprPair (spec : ConservationLawSpec) (d i : Nat) : FluxExpr × FluxExpr :=
  let fExpr := getOr (getOr spec.fluxes d []) i (.const 0)
  let fL := injLeftVars fExpr
  let fR := injRightVars fExpr
  let fHat : FluxExpr :=
    .sub (.mul (.const (1 / 2)) (.add fL fR))
         (.mul (.mul (.param 0) (.const (1 / 2))) (.sub (.var (2 * i + 1)) (.var (2 * i))))
  let amdq := .sub fHat fL
  let apdq := .sub fR fHat
  (.add amdq apdq, .sub fR fL)

/-- Reflective `CanonPoly` fluctuation conservation check across all `D` axes and `m` components. -/
def verifyFluctuationsReflective (spec : ConservationLawSpec) : Bool :=
  let dom2 := twoStateInterleavedDom spec.domain
  (List.range spec.numDims).all fun d =>
    (List.range spec.numVars).all fun i =>
      let (lhs, rhs) := fluctReflectiveExprPair spec d i
      checkFluxEqReflective dom2 lhs rhs

/-- **Reflective `CanonPoly` Fluctuation Conservation (`fluctuationConservation_of_reflective`)**:
Discharges nonlinear rational LeVeque fluctuation conservation `A⁻ΔQ + A⁺ΔQ = F(U_R) - F(U_L)` across
all axes `d < spec.numDims` and components `i < spec.numVars` via `checkFluxEqReflective_sound`! -/
theorem fluctuationConservation_of_reflective (spec : ConservationLawSpec)
    (hRefl : verifyFluctuationsReflective spec = true)
    (d i : Nat) (hd : d < spec.numDims) (hi : i < spec.numVars)
    (uL uR : Vec)
    (hDomL : DomainValid spec.domain ⟨uL, spec.paramEnv⟩)
    (hDomR : DomainValid spec.domain ⟨uR, spec.paramEnv⟩) :
    let fluxD := getOr spec.fluxes d []
    rusanovFluctMinus fluxD spec.paramEnv spec.aMax uL uR i +
      rusanovFluctPlus fluxD spec.paramEnv spec.aMax uL uR i =
      evalFlux (getOr fluxD i (.const 0)) ⟨uR, spec.paramEnv⟩ -
      evalFlux (getOr fluxD i (.const 0)) ⟨uL, spec.paramEnv⟩ ∧
    rusanovFluctMinus fluxD spec.paramEnv spec.aMax uL uL i = 0 ∧
    rusanovFluctPlus fluxD spec.paramEnv spec.aMax uL uL i = 0 := by
  unfold verifyFluctuationsReflective at hRefl
  simp only [List.all_eq_true] at hRefl
  have hPair := (hRefl d (List.mem_range.mpr hd)) i (List.mem_range.mpr hi)
  have hDom2 := domainValid_twoStateInterleaved spec.domain spec.paramEnv spec.aMax uL uR hDomL hDomR
  have hSound := checkFluxEqReflective_sound (twoStateInterleavedDom spec.domain)
    (fluctReflectiveExprPair spec d i).1 (fluctReflectiveExprPair spec d i).2 hPair
    (twoStateInterleavedEnv spec.paramEnv spec.aMax uL uR) hDom2
  dsimp only [fluctReflectiveExprPair] at hSound
  simp only [evalFlux, evalFlux_injLeftVars, evalFlux_injRightVars] at hSound
  simp only [twoStateInterleavedEnv, beq_self_eq_true, ↓reduceIte,
    show (2 * i + 1) % 2 = 1 by omega, show ¬ (1 == 0) = true by decide,
    Bool.false_eq_true, show (2 * i + 1) / 2 = i by omega,
    show (2 * i) % 2 = 0 by omega, show (2 * i) / 2 = i by omega] at hSound
  refine ⟨?_, (rusanovFluct_conservation _ _ _ uL uL i).2.1,
    (rusanovFluct_conservation _ _ _ uL uL i).2.2⟩
  dsimp only [rusanovFluctMinus, rusanovFluctPlus, rusanovNonlinearFlux]
  rw [show spec.aMax / 2 = spec.aMax * (1 / 2 : Rat) by grind]
  exact hSound

/-- Symbolic `m × m` matrix product `A · B` over `FluxExpr`. -/
def symMatMul (m : Nat) (A B : List (List FluxExpr)) : List (List FluxExpr) :=
  (List.range m).map fun i =>
    (List.range m).map fun j =>
      (List.range m).foldl (fun acc k =>
        .add acc (.mul (getOr (getOr A i []) k (.const 0))
                       (getOr (getOr B k []) j (.const 0)))) (.const 0)

/-- Reflective `CanonPoly` check for Friedrichs symmetrizer symmetry `(H(U) J(U))_{ij} = (H(U) J(U))_{ji}`. -/
def checkSymmetrizerReflective (dom : List PosTarget) (m : Nat)
    (H jac : List (List FluxExpr)) : Bool :=
  let HJ := symMatMul m H jac
  (List.range m).all fun i =>
    (List.range m).all fun j =>
      checkFluxEqReflective dom
        (getOr (getOr HJ i []) j (.const 0))
        (getOr (getOr HJ j []) i (.const 0))

theorem symmetrizerReflective_sound (dom : List PosTarget) (m : Nat)
    (H jac : List (List FluxExpr))
    (hSym : checkSymmetrizerReflective dom m H jac = true)
    (env : FluxEnv) (hDom : DomainValid dom env)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    let HJ := symMatMul m H jac
    evalFlux (getOr (getOr HJ i []) j (.const 0)) env =
      evalFlux (getOr (getOr HJ j []) i (.const 0)) env := by
  unfold checkSymmetrizerReflective at hSym
  simp only [List.all_eq_true] at hSym
  exact checkFluxEqReflective_sound dom _ _
    ((hSym i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)) env hDom

/-- **Multi-Dimensional Sweep & Rollout Conservation (`spec_sweep_conserves_integral`)**:
Bundles exact Lie splitting conservation, 2nd-order Strang splitting conservation, multi-turn
adaptive rollout conservation + monotone Courant time, and CFL violation refusal completeness. -/
theorem spec_sweep_conserves_integral (spec : ConservationLawSpec)
    (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) :
    let axisFlux := fun d => rusanovNonlinearFlux (getOr spec.fluxes d []) spec.paramEnv spec.aMax
    (∀ ν : Rat, ∀ U : MultiDGrid, ∀ c : Nat,
      totalGridIntegral dims (evalMultiDSweep dims ν axisFlux U) c = totalGridIntegral dims U c ∧
      totalGridIntegral dims (evalStrangSweep dims ν axisFlux U) c = totalGridIntegral dims U c) ∧
    (∀ (st0 stF : PdeRolloutState) (turns : List PdeRolloutTurn),
      runPdeRolloutTrace spec dims st0 turns = some stF →
      (∀ c, totalGridIntegral dims stF.grid c = totalGridIntegral dims st0.grid c) ∧
      st0.elapsedCourant ≤ stF.elapsedCourant ∧
      stF.acceptedSteps = st0.acceptedSteps + turns.length) ∧
    (∀ (st : PdeRolloutState) (turn : PdeRolloutTurn),
      stepPdeRolloutTurn spec dims st turn = none ↔
        ¬ (0 ≤ turn.courant ∧ turn.courant * spec.aMax ≤ 1)) :=
  ⟨fun ν U c => multiDSweep_conserves_total_mass_momentum_energy dims hPos ν _ U c,
   fun st0 stF turns hRun => runPdeRolloutTrace_invariants spec dims hPos st0 stF turns hRun,
   fun st turn => stepPdeRolloutTurn_none_iff_cfl_violation spec dims st turn⟩

/-- **Nonlinear 2nd-Order MUSCL-`minmod` TVD Soundness (`spec_minmod_tvd_sound`)**:
Bundles 2nd-order affine reconstruction exactness (positive & negative slopes), mirror symmetry,
and nonlinear MUSCL-`minmod` Rusanov TVD non-increase under `2 * ν * spec.aMax ≤ 1`. -/
theorem spec_minmod_tvd_sound (spec : ConservationLawSpec) (hValid : spec.checkValid = true) :
    (∀ u0 s : Rat,
      musclReconstructLeft (u0 - s) u0 (u0 + s) = u0 - (1 / 2 : Rat) * s ∧
      musclReconstructRight (u0 - s) u0 (u0 + s) = u0 + (1 / 2 : Rat) * s) ∧
    (∀ uPrev uCurr uNext : Rat,
      musclReconstructLeft uNext uCurr uPrev = musclReconstructRight uPrev uCurr uNext) ∧
    (∀ (f : Rat → Rat) (ν : Rat),
      0 ≤ ν → 2 * ν * spec.aMax ≤ 1 →
      (∀ x y : Rat, ratAbs (f y - f x) ≤ spec.aMax * ratAbs (y - x)) →
      ∀ (N : Nat) (u : Nat → Rat),
        totalVariation1D N (musclMinmodRusanov1DStep f spec.aMax ν N u) ≤ totalVariation1D N u) := by
  have haPos := (checkValid_cfl_bounds spec hValid).1
  exact ⟨muscl_minmod_linear_exact, muscl_minmod_mirror_symm,
    fun f ν hν hcfl hLip N u =>
      tvd_rusanov_minmod_step_nonincreasing f spec.aMax ν (Rat.le_of_lt haPos) hν hcfl hLip N u⟩

/-- A spatially constant state is preserved exactly, even if intermediate word arithmetic wraps. -/
theorem evalNonlinearFluxCellQ32_constant (spec : ConservationLawSpec) (dag : FluxSsaDag)
    (u0 : Nat → Word) : evalNonlinearFluxCellQ32 spec dag (fun _ c => u0 c) =
      (List.range spec.numVars).map u0 := by
  simp [evalNonlinearFluxCellQ32, evalAluOp]

/-- Keep shared arithmetic as lexical source bindings. The graph backend fuses these into
register programs; eagerly substituting KernelInput trees would duplicate Newton iterates. -/
def pdeSourceFused : Program → FusedProgram
  | .ret arrays => .ret arrays
  | .letE rhs body => .letE (.source rhs) (pdeSourceFused body)

theorem pdeSourceFused_sound (source : Program) (env : Env) :
    evalFused env (pdeSourceFused source) = source.eval env := by
  induction source generalizing env with
  | ret arrays => rfl
  | letE rhs body ih => exact ih _

/-- All components of the selected nonlinear directional sweep, with shared SSA arithmetic. -/
def buildSpecFusedGpuKernel (spec : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) (axis : Nat := 0) : FusedProgram :=
  (pdeSourceFused (compileMultiDNonlinearFluxSweepSource spec b dims axis)).rename
    (fun c => spec.numVars-1-c)

/-- Compiler equivalence to the shared nonlinear array source. This statement covers source
lowering; refinement to an independent Q32 sweep and brick evaluation requires separate proofs. -/
theorem spec_fusedGpuKernel_sound (spec : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) (grids : Nat → List Word) (axis : Nat := 0) :
    evalFused grids (buildSpecFusedGpuKernel spec b dims axis) =
      (compileMultiDNonlinearFluxSweepSource spec b dims axis).eval (fun c => grids (spec.numVars-1-c)) := by
  rw [buildSpecFusedGpuKernel, FusedProgram.rename_sound, pdeSourceFused_sound]

/-- Q32 multiplication is the Euclidean-floored signed product, modulo 64 bits. -/
theorem qmul32_eq_ofInt (a b : Word) :
    evalAluOp .qmul32 a b = BitVec.ofInt 64 (a.toInt * b.toInt / (2 : Int)^32) := by
  let p := a.signExtend 128 * b.signExtend 128
  have hlo := BitVec.le_toInt_mul_toInt (x := a) (y := b)
  have hhi := BitVec.toInt_mul_toInt_le (x := a) (y := b)
  have hp : p.toInt = a.toInt * b.toInt := by
    dsimp [p]
    rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by decide),
      BitVec.toInt_signExtend_of_le (by decide)]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hn := BitVec.toInt_eq_toNat_cond p
  apply BitVec.eq_of_toInt_eq
  change ((p >>> 32).setWidth 64).toInt = _
  rw [BitVec.toInt_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toInt_ofInt]
  simp only [Int.bmod_def]
  split at hn <;> omega

private theorem q32_limb_identity (a b : Int) :
    a * b / 4294967296 =
      (a / 4294967296) * (b / 4294967296) * 4294967296 +
      (a / 4294967296) * (b % 4294967296) +
      (a % 4294967296) * (b / 4294967296) +
      ((a % 4294967296) * (b % 4294967296)) / 4294967296 := by
  have ha : a = (a / 4294967296) * 4294967296 + a % 4294967296 := by omega
  have hb : b = (b / 4294967296) * 4294967296 + b % 4294967296 := by omega
  have hab : a * b =
      ((a / 4294967296) * (b / 4294967296) * 4294967296 +
        (a / 4294967296) * (b % 4294967296) +
        (a % 4294967296) * (b / 4294967296)) * 4294967296 +
        (a % 4294967296) * (b % 4294967296) := by
    calc a * b = ((a / 4294967296) * 4294967296 + a % 4294967296) *
        ((b / 4294967296) * 4294967296 + b % 4294967296) := by rw [← ha, ← hb]
         _ = _ := by grind
  rw [hab, Int.mul_add_ediv_right _ _ (by decide)]

private theorem q32_low_word (a : Word) :
    a &&& 0xFFFFFFFF#64 = BitVec.ofInt 64 (a.toInt % 4294967296) := by
  have ha := BitVec.toInt_eq_toNat_cond a
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofInt]
  change a.toNat &&& (2^32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  split at ha <;> omega

private theorem q32_high_word (a : Word) :
    (a >>> 32) ||| (if a.ult 0x8000000000000000#64 then 0#64 else 0xFFFFFFFF00000000#64) =
      BitVec.ofInt 64 (a.toInt / 4294967296) := by
  have ha := BitVec.toInt_eq_toNat_cond a
  have hal := a.isLt
  have hor := Nat.two_pow_add_eq_or_of_lt
    (i := 32) (b := a.toNat / 4294967296) (by omega) 4294967295
  have hor' : a.toNat / 4294967296 ||| 18446744069414584320 =
      18446744069414584320 + a.toNat / 4294967296 := by
    rw [Nat.or_comm]
    exact hor.symm
  clear hor
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  split
  · change a.toNat / 4294967296 ||| 0 = _
    rw [Nat.or_zero]
    simp only [decide_eq_true_eq] at *
    split at ha <;> omega
  · change a.toNat / 4294967296 ||| 18446744069414584320 = _
    rw [hor']
    simp only [decide_eq_true_eq] at *
    split at ha <;> omega

private theorem q32_low_product (a b : Int) :
    (BitVec.ofInt 64 (a % 4294967296) * BitVec.ofInt 64 (b % 4294967296)) >>> 32 =
      BitVec.ofInt 64 ((a % 4294967296) * (b % 4294967296) / 4294967296) := by
  have ha := Int.emod_nonneg a (by decide : (4294967296 : Int) ≠ 0)
  have hb := Int.emod_nonneg b (by decide : (4294967296 : Int) ≠ 0)
  have hat := Int.emod_lt_of_pos a (by decide : (0 : Int) < 4294967296)
  have hbt := Int.emod_lt_of_pos b (by decide : (0 : Int) < 4294967296)
  have hp := Int.mul_nonneg ha hb
  have hpt := Int.mul_le_mul_of_nonneg_right
    (show a % 4294967296 ≤ 4294967295 by omega) hb
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul,
    BitVec.toNat_ofInt]
  have ha' : ((a % 4294967296) % 2^64).toNat = (a % 4294967296).toNat := by omega
  have hb' : ((b % 4294967296) % 2^64).toNat = (b % 4294967296).toNat := by omega
  change ((a % 4294967296 % 2^64).toNat * (b % 4294967296 % 2^64).toNat) % 2^64 / 2^32 =
    (a % 4294967296 * (b % 4294967296) / 4294967296 % 2^64).toNat
  rw [ha', hb', ← Int.toNat_mul ha hb]
  omega

/-- The limb implementation agrees with HDL for every pair of 64-bit words, including overflow. -/
theorem scalarQmul32_eval_eq_qmul32 (a b : ScalarExpr) (slots : Nat → Word) :
    (scalarQmul32 a b).eval slots = evalAluOp .qmul32 (a.eval slots) (b.eval slots) := by
  simp only [scalarQmul32, scalarAdd, scalarSelect, scalarLt, ScalarExpr.eval,
    Obend.Hardware.ArrayHypergraph.evalElemOp,
    Obend.Hardware.OpenHypergraph.evalHypergraphOpBv, List.getD_cons_zero,
    List.getD_cons_succ, Obend.Hardware.ArrayHypergraph.wordShl_eq,
    Obend.Hardware.ArrayHypergraph.wordShr_eq]
  have hmux : ∀ c : Bool, (if (if c then 1#64 else 0#64) != 0#64 then 0#64
      else 0xFFFFFFFF00000000#64) = if c then 0#64 else 0xFFFFFFFF00000000#64 := by
    intro c; cases c <;> rfl
  simp only [hmux, show (32#64).toNat = 32 from rfl]
  rw [q32_high_word, q32_high_word, q32_low_word, q32_low_word, q32_low_product,
    ← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
    BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofInt 64 _ * BitVec.ofInt 64 4294967296 + _ + _ + _ = _
  rw [← BitVec.ofInt_mul, ← BitVec.ofInt_add, ← BitVec.ofInt_add,
    ← BitVec.ofInt_add, ← q32_limb_identity, qmul32_eq_ofInt]
  rfl

/-- The linear lexical source program produces the same Q32 products pointwise. -/
theorem scalarQmul32Source_eval (size : Nat) (env : Env) :
    (scalarQmul32Source size).eval env =
      [(List.range size).map fun i => evalAluOp .qmul32
        ((env 0).getD i 0#64) ((env 1).getD i 0#64)] := by
  let leaf : Nat → Rhs := fun i => .map size (.scalar (.scale 1)) [i]
  obtain ⟨final, he, hv, _⟩ := compileScalar_eval
    (scalarQmul32 (.input 0) (.input 1)) size leaf env (.ret [0])
  change (compileScalar size leaf _ _).eval env = _
  rw [he]
  simp only [Program.eval, List.map_cons, List.map_nil, hv]
  rw [evalScalarArrays_pointwise _ size _ (by intro i; simp [leaf, Rhs.eval])]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [scalarQmul32_eval_eq_qmul32]
  simp [ScalarExpr.eval, leaf, Rhs.eval, Obend.Hardware.ArrayHypergraph.evalElemOp,
    Obend.Hardware.OpenHypergraph.evalHypergraphOpBv,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.mp hi)]

theorem qmul32_toInt (a b : Word)
    (h : -((2 : Int)^63) ≤ a.toInt * b.toInt / (2 : Int)^32 ∧
      a.toInt * b.toInt / (2 : Int)^32 < (2 : Int)^63) :
    (evalAluOp .qmul32 a b).toInt = a.toInt * b.toInt / (2 : Int)^32 := by
  rw [qmul32_eq_ofInt]
  exact BitVec.toInt_ofInt_eq_self (by decide) h.1 h.2

theorem q32Normalization_shift_exact (u : (BitVec 64)) (s : Nat) (hs : s ≤ 63)
    (hu : u.toNat < 2^(63-s)) :
    (u <<< s).toNat = u.toNat*2^s ∧ (u <<< s).toNat < 2^63 := by
  have hp : 2^(63-s)*2^s = (2:Nat)^63 := by rw [← Nat.pow_add]; congr 1; omega
  have hm : u.toNat*2^s < 2^63 := by
    rw [← hp]
    exact Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos s)
  have he : (u <<< s).toNat = u.toNat*2^s := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  exact ⟨he, by omega⟩

theorem q32NormalizeStep_correct (u : (BitVec 64)) (s k lo : Nat) (hs : s ≤ 63)
    (hl : 2^lo ≤ u.toNat) (hu : u.toNat < 2^63) :
    let result := q32NormalizeStep s u k
    2^(min (lo+s) (63-s)) ≤ result.1.toNat ∧ result.1.toNat < 2^63 ∧
      ∃ t, result.1.toNat = u.toNat*2^t ∧ result.2 = k+t := by
  have ht : (1#64 <<< (63-s)).toNat = 2^(63-s) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (1*(2:Nat)^(63-s)) % 2^64 = _
    rw [Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
  unfold q32NormalizeStep
  split
  · rename_i h
    have small : u.toNat < 2^(63-s) := by simpa only [BitVec.ult_iff_toNat_lt, ht] using h
    obtain ⟨he, hhi⟩ := q32Normalization_shift_exact u s hs small
    have hh := Nat.mul_le_mul_right (2^s) hl
    rw [← Nat.pow_add] at hh
    have hm := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (Nat.min_le_left (lo+s) (63-s))
    exact ⟨by dsimp only; omega, hhi, s, he, rfl⟩
  · rename_i h
    have large : 2^(63-s) ≤ u.toNat := by
      have hn : ¬u.toNat < 2^(63-s) := by simpa only [BitVec.ult_iff_toNat_lt, ht] using h
      omega
    have hm := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (Nat.min_le_right (lo+s) (63-s))
    exact ⟨Nat.le_trans hm large, hu, 0, by simp, by simp⟩
theorem q32NormalizeLoop_correct (shifts : List Nat) (u : BitVec 64) (k lo : Nat)
    (hs : ∀ s ∈ shifts, s ≤ 63) (hl : 2^lo ≤ u.toNat) (hu : u.toNat < 2^63) :
    let result := q32NormalizeLoop shifts u k
    2^(shifts.foldl (fun low s => min (low+s) (63-s)) lo) ≤ result.1.toNat ∧
      result.1.toNat < 2^63 ∧ ∃ t, result.1.toNat = u.toNat*2^t ∧ result.2 = k+t := by
  induction shifts generalizing u k lo with
  | nil => exact ⟨hl,hu,0,by simp [q32NormalizeLoop],by simp [q32NormalizeLoop]⟩
  | cons s ss ih =>
    simp only [q32NormalizeLoop, List.foldl_cons]
    obtain ⟨hb,hu',t,he,hk⟩ := q32NormalizeStep_correct u s k lo (hs s (by simp)) hl hu
    obtain ⟨hbF,huF,v,hv,hkv⟩ := ih (q32NormalizeStep s u k).1 (q32NormalizeStep s u k).2 (min (lo+s) (63-s))
      (fun s h => hs s (by simp [h])) hb hu'
    change _ ≤ (q32NormalizeLoop ss (q32NormalizeStep s u k).1 (q32NormalizeStep s u k).2).1.toNat ∧ _
    refine ⟨hbF,huF,t+v,?_,?_⟩
    · rw [hv,he,Nat.mul_assoc,← Nat.pow_add]
    · rw [hkv,hk,Nat.add_assoc]

theorem q32NormalizeLoop_bounds (d : BitVec 64) (hd : 16 ≤ d.toNat ∧ d.toNat ≤ 2^60) :
    let result := q32NormalizeLoop [32,16,8,4,2,1] d 0
    2^62 ≤ result.1.toNat ∧ result.1.toNat < 2^63 ∧
      result.1.toNat = d.toNat*2^result.2 ∧ 2 ≤ result.2 ∧ result.2 ≤ 58 := by
  let result := q32NormalizeLoop [32,16,8,4,2,1] d 0
  obtain ⟨hl,hu,t,he,hk⟩ := q32NormalizeLoop_correct [32,16,8,4,2,1] d 0 4 (by decide +kernel)
    (by omega) (by omega)
  change 2^62 ≤ result.1.toNat at hl
  change result.1.toNat < 2^63 at hu
  change result.1.toNat = d.toNat*2^t at he
  change result.2 = 0+t at hk
  have factor : result.1.toNat = d.toNat*2^result.2 := by simp only [Nat.zero_add] at hk; rw [hk]; exact he
  have lower : 2 ≤ result.2 := by
    by_cases h0 : result.2 = 0
    · rw [h0] at factor; simp only [Nat.pow_zero,Nat.mul_one] at factor; omega
    by_cases h1 : result.2 = 1
    · rw [h1] at factor; simp only [Nat.pow_one] at factor; omega
    omega
  have upper : result.2 ≤ 58 := by
    by_cases hn : result.2 ≤ 58
    · exact hn
    · have power := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show 59 ≤ result.2 by omega)
      have bound := Nat.mul_le_mul hd.1 power
      rw [← factor] at bound
      omega
  exact ⟨hl,hu,factor,lower,upper⟩

/-- Each hardware Newton step is exactly the rounded integer recurrence; no intermediate wraps. -/
theorem q32_nr_word_step (d x : Word)
    (hd : 2147483648 ≤ d.toInt ∧ d.toInt ≤ 4294967296)
    (hx : 0 ≤ x.toInt ∧ x.toInt ≤ 12884901888) :
    (evalAluOp .qmul32 x ((2#64 <<< 32) - evalAluOp .qmul32 d x)).toInt =
      x.toInt * (8589934592-d.toInt*x.toInt/4294967296)/4294967296 := by
  have hd0 : 0 ≤ d.toInt := by omega
  have hp0 := Int.mul_nonneg hd0 hx.1
  have hp1 := Int.mul_le_mul_of_nonneg_left hx.2 hd0
  have hy0 : 0 ≤ d.toInt*x.toInt/4294967296 := Int.ediv_nonneg hp0 (by decide)
  have hy1 : d.toInt*x.toInt/4294967296 ≤ 12884901888 := by omega
  have inner := qmul32_toInt d x (by omega)
  have correction : ((2#64 <<< 32)-evalAluOp .qmul32 d x).toInt =
      8589934592-d.toInt*x.toInt/4294967296 := by
    rw [BitVec.toInt_sub, inner]
    change (8589934592-d.toInt*x.toInt/4294967296).bmod 18446744073709551616 = _
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hlo : -4294967296 ≤ 8589934592-d.toInt*x.toInt/4294967296 := by omega
  have hhi : 8589934592-d.toInt*x.toInt/4294967296 ≤ 8589934592 := by omega
  have lower := Int.mul_le_mul_of_nonneg_left hlo hx.1
  have upper := Int.mul_le_mul_of_nonneg_left hhi hx.1
  rw [qmul32_toInt x _ (by rw [correction]; omega), correction]
  rfl

/-- Exact quadratic self-correction identity, including both Euclidean rounding remainders. -/
theorem q32_nr_residual_identity (d x : Int) :
    let y := d*x / 4294967296
    let z := x*(8589934592-y)
    18446744073709551616 * (18446744073709551616-d*(z/4294967296)) =
      (18446744073709551616-d*x)*(18446744073709551616-d*x) -
        d*x*(d*x % 4294967296) + d*4294967296*(z % 4294967296) := by
  have h1 : d*x / 4294967296 * 4294967296 + d*x % 4294967296 = d*x := by omega
  have h2 : (x*(8589934592-d*x/4294967296))/4294967296 * 4294967296 +
      (x*(8589934592-d*x/4294967296)) % 4294967296 = x*(8589934592-d*x/4294967296) := by omega
  dsimp only
  grind

/-- A Newton step squares the incoming residual and adds bounded rounding error. -/
theorem q32_nr_residual_bound (d x E : Int)
    (hd : 2147483648 ≤ d ∧ d ≤ 4294967296)
    (hx : 0 ≤ x ∧ x ≤ 12884901888)
    (he : -E ≤ 18446744073709551616-d*x ∧ 18446744073709551616-d*x ≤ E) :
    let z := x*(8589934592-d*x/4294967296);
    -12884901888 ≤ 18446744073709551616-d*(z/4294967296) ∧
      18446744073709551616-d*(z/4294967296) ≤ E*E/18446744073709551616 + 4294967296 := by
  let e := 18446744073709551616-d*x
  let a := d*x % 4294967296
  let z := x*(8589934592-d*x/4294967296)
  let b := z % 4294967296
  have ha0 : 0 ≤ a := Int.emod_nonneg _ (by decide)
  have ha1 : a ≤ 4294967296 := by have := Int.emod_lt_of_pos (d*x) (by decide : (0 : Int) < 4294967296); omega
  have hb0 : 0 ≤ b := Int.emod_nonneg _ (by decide)
  have hb1 : b ≤ 4294967296 := by have := Int.emod_lt_of_pos z (by decide : (0 : Int) < 4294967296); omega
  have hdx0 := Int.mul_nonneg (show 0 ≤ d by omega) hx.1
  have hdx1 := Int.mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ d by omega)
  have hA0 := Int.mul_nonneg hdx0 ha0
  have hA1 := Int.mul_le_mul_of_nonneg_left ha1 hdx0
  have hB0 := Int.mul_nonneg (show 0 ≤ d*4294967296 by omega) hb0
  have hB1 := Int.mul_le_mul_of_nonneg_left hb1 (show 0 ≤ d*4294967296 by omega)
  have he0 : 0 ≤ e*e := by
    by_cases hp : 0 ≤ e
    · exact Int.mul_nonneg hp hp
    · have hh := Int.mul_nonneg (show 0 ≤ -e by omega) (show 0 ≤ -e by omega)
      simpa only [Int.neg_mul, Int.mul_neg, Int.neg_neg] using hh
  have he1 : e*e ≤ E*E := by
    by_cases hp : 0 ≤ e
    · exact Int.mul_self_le_mul_self hp he.2
    · have hh := Int.mul_self_le_mul_self (show 0 ≤ -e by omega) (show -e ≤ E by omega)
      simpa only [Int.neg_mul, Int.mul_neg, Int.neg_neg] using hh
  have identity := q32_nr_residual_identity d x
  change 18446744073709551616 * (18446744073709551616-d*(z/4294967296)) =
    e*e-d*x*a+d*4294967296*b at identity
  change -12884901888 ≤ 18446744073709551616-d*(z/4294967296) ∧
    18446744073709551616-d*(z/4294967296) ≤ E*E/18446744073709551616 + 4294967296
  omega

private theorem q32_seed_identity (d q a : Int)
    (h : q*4294967296+a = 8084644321*d) :
    73014444032*(18446744073709551616-d*(12126966482-q)) =
      4294967296*(2*((4*d-12884901888)*(4*d-12884901888))-18446744073709551616) +
        60129542144*d-15*(d*d)-17*(a*d) := by
  grind

private theorem q32_seed_polynomial_bound (d u v w e : Int)
    (hd : 2147483648 ≤ d ∧ d ≤ 4294967296)
    (hu : 0 ≤ u ∧ u ≤ 18446744073709551616)
    (hv : 0 ≤ v ∧ v ≤ 18446744073709551616)
    (hw : 0 ≤ w ∧ w ≤ 4294967296*d)
    (he : 73014444032*e = 4294967296*(2*u-18446744073709551616) +
      60129542144*d-15*v-17*w) :
    -1152921504606846976 ≤ e ∧ e ≤ 1152921504606846976 := by
  have he' : 73014444032*e = 8589934592*u - 4294967296*18446744073709551616 +
      60129542144*d-15*v-17*w := by
    rw [Int.mul_sub, ← Int.mul_assoc] at he
    exact he
  have hUlo := Int.mul_nonneg (by decide : (0 : Int) ≤ 8589934592) hu.1
  have hUhi := Int.mul_le_mul_of_nonneg_left hu.2 (by decide : (0 : Int) ≤ 8589934592)
  have hd0 : 0 ≤ d := Int.le_trans (by decide) hd.1
  have hAlo := Int.mul_nonneg (by decide : (0 : Int) ≤ 60129542144) hd0
  have hAhi := Int.mul_le_mul_of_nonneg_left hd.2 (by decide : (0 : Int) ≤ 60129542144)
  have hBlo := Int.mul_nonneg (by decide : (0 : Int) ≤ 15) hv.1
  have hBhi := Int.mul_le_mul_of_nonneg_left hv.2 (by decide : (0 : Int) ≤ 15)
  have hClo := Int.mul_nonneg (by decide : (0 : Int) ≤ 17) hw.1
  have hw' : w ≤ 4294967296*4294967296 := Int.le_trans hw.2
    (Int.mul_le_mul_of_nonneg_left hd.2 (by decide))
  have hChi := Int.mul_le_mul_of_nonneg_left hw' (by decide : (0 : Int) ≤ 17)
  have upper := Int.sub_le_sub
    (Int.sub_le_sub (Int.add_le_add (Int.sub_le_sub_right hUhi (4294967296*18446744073709551616)) hAhi) hBlo) hClo
  have lower := Int.sub_le_sub
    (Int.sub_le_sub (Int.add_le_add (Int.sub_le_sub_right hUlo (4294967296*18446744073709551616)) hAlo) hBhi) hChi
  rw [← he'] at upper lower
  constructor
  · apply Int.le_of_mul_le_mul_left (a := 73014444032) _ (by decide)
    exact Int.le_trans (by decide +kernel) lower
  · apply Int.le_of_mul_le_mul_left (a := 73014444032) _ (by decide)
    exact Int.le_trans upper (by decide +kernel)

/-- The exact floored 48/17,32/17 seed satisfies the uniform normalized seed contract. -/
theorem q32_nr_seed_bound (d : Int) (hd : 2147483648 ≤ d ∧ d ≤ 4294967296) :
    let x := 12126966482-8084644321*d/4294967296;
    (0 ≤ x ∧ x ≤ 12884901888) ∧
      -1152921504606846976 ≤ 18446744073709551616-d*x ∧
      18446744073709551616-d*x ≤ 1152921504606846976 := by
  let x := 12126966482-8084644321*d/4294967296
  have hx : 0 ≤ x ∧ x ≤ 12884901888 := by
    have h0 : 0 ≤ 8084644321*d/4294967296 :=
      Int.ediv_nonneg (Int.mul_nonneg (by decide) (by omega)) (by decide)
    have h1 : 8084644321*d/4294967296 ≤ 8084644321 :=
      Int.ediv_le_of_le_mul (by decide) (Int.mul_le_mul_of_nonneg_left hd.2 (by decide))
    dsimp [x]
    omega
  let a := 8084644321*d % 4294967296
  let z := 4*d-12884901888
  have ha0 : 0 ≤ a := Int.emod_nonneg _ (by decide)
  have ha1 : a ≤ 4294967296 := by
    have := Int.emod_lt_of_pos (8084644321*d) (by decide : (0 : Int) < 4294967296)
    omega
  have hsq0 : 0 ≤ z*z := by
    by_cases hp : 0 ≤ z
    · exact Int.mul_nonneg hp hp
    · have hh := Int.mul_nonneg (show 0 ≤ -z by omega) (show 0 ≤ -z by omega)
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg] at hh
      omega
  have hsq1 : z*z ≤ 18446744073709551616 := by
    by_cases hp : 0 ≤ z
    · have hh := Int.mul_self_le_mul_self hp (show z ≤ 4294967296 by dsimp [z]; omega)
      omega
    · have hh := Int.mul_self_le_mul_self (show 0 ≤ -z by omega)
        (show -z ≤ 4294967296 by dsimp [z]; omega)
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg] at hh
      omega
  have hd0 : 0 ≤ d := by omega
  have hdSq0 := Int.mul_nonneg hd0 hd0
  have hdSq1 := Int.mul_self_le_mul_self hd0 hd.2
  have had0 := Int.mul_nonneg ha0 hd0
  have had1 := Int.mul_le_mul_of_nonneg_right ha1 hd0
  have rem : 8084644321*d/4294967296*4294967296 + a = 8084644321*d := by dsimp [a]; omega
  have identity := q32_seed_identity d (8084644321*d/4294967296) a rem
  change 73014444032*(18446744073709551616-d*x) =
      4294967296*(2*(z*z)-18446744073709551616) + 60129542144*d-15*(d*d)-17*(a*d) at identity
  change (0 ≤ x ∧ x ≤ 12884901888) ∧
    -1152921504606846976 ≤ 18446744073709551616-d*x ∧
      18446744073709551616-d*x ≤ 1152921504606846976
  refine ⟨hx, ?_⟩
  exact q32_seed_polynomial_bound d (z*z) (d*d) (a*d) _ hd
    ⟨hsq0, hsq1⟩ ⟨hdSq0, by omega⟩ ⟨had0, had1⟩ identity

/-- A normalized iterate whose residual stays below `2^63` stays in the working range. -/
theorem q32_nr_range_of_residual (d r E : Int) (hd : 2147483648 ≤ d ∧ d ≤ 4294967296)
    (hE : E ≤ 9223372036854775808)
    (hr : -E ≤ 18446744073709551616-d*r ∧ 18446744073709551616-d*r ≤ E) :
    0 ≤ r ∧ r ≤ 12884901888 := by
  have hr0 : 0 ≤ r := by
    by_cases hp : 0 ≤ r
    · exact hp
    · have hh := Int.mul_le_mul_of_nonneg_left (show r ≤ 0 by omega) (show 0 ≤ d by omega)
      simp only [Int.mul_zero] at hh
      omega
  have hh := Int.mul_le_mul_of_nonneg_right hd.1 hr0
  exact ⟨hr0, by omega⟩

/-- Four Newton steps reduce a 1/16 seed residual to three normalized word units. -/
theorem q32_nr_four_steps (d x0 : Int)
    (hd : 2147483648 ≤ d ∧ d ≤ 4294967296)
    (hx : 0 ≤ x0 ∧ x0 ≤ 12884901888)
    (he : -1152921504606846976 ≤ 18446744073709551616-d*x0 ∧
      18446744073709551616-d*x0 ≤ 1152921504606846976) :
    let step := fun x : Int => x*(8589934592-d*x/4294967296)/4294967296
    let x4 := step (step (step (step x0)));
    -12884901888 ≤ 18446744073709551616-d*x4 ∧
      18446744073709551616-d*x4 ≤ 12884901888 := by
  let step := fun x : Int => x*(8589934592-d*x/4294967296)/4294967296
  have range := fun r E => q32_nr_range_of_residual d r E hd
  have h1 := q32_nr_residual_bound d x0 1152921504606846976 hd hx he
  have e1 : -144115188075855872 ≤ 18446744073709551616-d*(step x0) ∧
      18446744073709551616-d*(step x0) ≤ 144115188075855872 := by
    change -12884901888 ≤ 18446744073709551616-d*(step x0) ∧
      18446744073709551616-d*(step x0) ≤ 1152921504606846976*1152921504606846976/18446744073709551616 + 4294967296 at h1
    omega
  have x1 := range (step x0) 144115188075855872 (by decide) e1
  have h2 := q32_nr_residual_bound d (step x0) 144115188075855872 hd x1 e1
  have e2 : -2251799813685248 ≤ 18446744073709551616-d*(step (step x0)) ∧
      18446744073709551616-d*(step (step x0)) ≤ 2251799813685248 := by
    change -12884901888 ≤ 18446744073709551616-d*(step (step x0)) ∧
      18446744073709551616-d*(step (step x0)) ≤ 144115188075855872*144115188075855872/18446744073709551616 + 4294967296 at h2
    omega
  have x2 := range (step (step x0)) 2251799813685248 (by decide) e2
  have h3 := q32_nr_residual_bound d (step (step x0)) 2251799813685248 hd x2 e2
  have e3 : -549755813888 ≤ 18446744073709551616-d*(step (step (step x0))) ∧
      18446744073709551616-d*(step (step (step x0))) ≤ 549755813888 := by
    change -12884901888 ≤ 18446744073709551616-d*(step (step (step x0))) ∧
      18446744073709551616-d*(step (step (step x0))) ≤ 2251799813685248*2251799813685248/18446744073709551616 + 4294967296 at h3
    omega
  have x3 := range (step (step (step x0))) 549755813888 (by decide) e3
  have h4 := q32_nr_residual_bound d (step (step (step x0))) 549755813888 hd x3 e3
  change -12884901888 ≤ 18446744073709551616-d*(step (step (step (step x0)))) ∧
    18446744073709551616-d*(step (step (step (step x0)))) ≤ 549755813888*549755813888/18446744073709551616 + 4294967296 at h4
  change -12884901888 ≤ 18446744073709551616-d*(step (step (step (step x0)))) ∧
    18446744073709551616-d*(step (step (step (step x0)))) ≤ 12884901888
  omega

/-- Symbolic normalized integer recurrence with the actual rational seed and four rounded steps. -/
theorem q32_nr_normalized_residual (d : Int) (hd : 2147483648 ≤ d ∧ d ≤ 4294967296) :
    let step := fun x : Int => x*(8589934592-d*x/4294967296)/4294967296
    let x4 := step (step (step (step (12126966482-8084644321*d/4294967296))));
    -12884901888 ≤ 18446744073709551616-d*x4 ∧
      18446744073709551616-d*x4 ≤ 12884901888 :=
  q32_nr_four_steps d _ hd (q32_nr_seed_bound d hd).1 (q32_nr_seed_bound d hd).2

/-- Rounding a normalized reciprocal down by a positive scale costs at most one output word.
The denominator rounding allowance is one normalized unit. -/
theorem q32_nr_postscale_residual (d dp x q : Int)
    (hd : 0 ≤ d) (hq : 0 < q) (hx : 0 ≤ x ∧ x ≤ 12884901888)
    (hround : -q ≤ d-dp*q ∧ d-dp*q ≤ q)
    (hnr : -12884901888 ≤ x*dp-18446744073709551616 ∧
      x*dp-18446744073709551616 ≤ 12884901888) :
    -(25769803776+d) ≤ (x/q)*d-18446744073709551616 ∧
      (x/q)*d-18446744073709551616 ≤ 25769803776+d := by
  let e := d-dp*q
  let rem := x % q
  have rem0 : 0 ≤ rem := Int.emod_nonneg _ (by omega)
  have rem1 : rem ≤ q := by have := Int.emod_lt_of_pos x hq; omega
  have loE := Int.mul_le_mul_of_nonneg_left hround.1 hx.1
  have hiE := Int.mul_le_mul_of_nonneg_left hround.2 hx.1
  have xq := Int.mul_le_mul_of_nonneg_right hx.2 (Int.le_of_lt hq)
  have loR := Int.mul_nonneg rem0 hd
  have hiR := Int.mul_le_mul_of_nonneg_right rem1 hd
  have loN := Int.mul_le_mul_of_nonneg_right hnr.1 (Int.le_of_lt hq)
  have hiN := Int.mul_le_mul_of_nonneg_right hnr.2 (Int.le_of_lt hq)
  have identity : ((x/q)*d-18446744073709551616)*q =
      (x*dp-18446744073709551616)*q + x*e-rem*d := by
    have divide : (x/q)*q+rem=x := Int.ediv_mul_add_emod x q
    dsimp [e]
    grind
  have bounded : -(25769803776*q+q*d) ≤ ((x/q)*d-18446744073709551616)*q ∧
      ((x/q)*d-18446744073709551616)*q ≤ 25769803776*q+q*d := by
    change x*(-q) ≤ x*e at loE
    change x*e ≤ x*q at hiE
    rw [Int.mul_neg] at loE
    omega
  constructor
  · apply Int.le_of_mul_le_mul_right _ hq
    rw [Int.neg_mul, Int.add_mul, Int.mul_comm d q]
    exact bounded.1
  · apply Int.le_of_mul_le_mul_right _ hq
    rw [Int.add_mul, Int.mul_comm d q]
    exact bounded.2

/-- Upscaling is exact when the integer normalized denominator is `d*t`. -/
theorem q32_nr_upscale_residual (d dp x t : Int) (hscale : dp = d*t)
    (hnr : -12884901888 ≤ x*dp-18446744073709551616 ∧
      x*dp-18446744073709551616 ≤ 12884901888) :
    -12884901888 ≤ (x*t)*d-18446744073709551616 ∧
      (x*t)*d-18446744073709551616 ≤ 12884901888 := by
  have h : (x*t)*d = x*dp := by rw [hscale]; ac_rfl
  simpa only [h] using hnr

/-- Positive interval enclosure derived from the scale-aware residual inequality. -/
theorem q32_interval_of_residual (lo hi d r : Int)
    (hlo : 16 ≤ lo) (hd : lo ≤ d ∧ d ≤ hi)
    (hr : -(16 * (2 : Int)^32 + 4*d) ≤ r*d - (2 : Int)^64 ∧
      r*d - (2 : Int)^64 ≤ 16 * (2 : Int)^32 + 4*d) :
    ((2 : Int)^64 - 16*(2 : Int)^32) / hi - 5 ≤ r ∧
      r ≤ ((2 : Int)^64 + 16*(2 : Int)^32) / lo + 4 := by
  let a := ((2 : Int)^64 - 16*(2 : Int)^32) / hi
  let b := ((2 : Int)^64 + 16*(2 : Int)^32) / lo
  have hd0 : 0 < d := by omega
  have ha0 : 0 ≤ a := Int.ediv_nonneg (by decide) (by omega)
  have hb0 : 0 ≤ b := Int.ediv_nonneg (by decide) (by omega)
  have ha := Int.ediv_mul_le ((2 : Int)^64 - 16*(2 : Int)^32) (by omega : hi ≠ 0)
  have hb := Int.lt_ediv_add_one_mul_self ((2 : Int)^64 + 16*(2 : Int)^32) (by omega : 0 < lo)
  have hal := Int.mul_le_mul_of_nonneg_left hd.2 ha0
  have hbu := Int.mul_le_mul_of_nonneg_left hd.1 (show 0 ≤ b+1 by omega)
  change a - 5 ≤ r ∧ r ≤ b + 4
  have hrl : a*d ≤ (r+4)*d := by
    dsimp [a] at *
    rw [Int.add_mul]
    omega
  have hru : (r-4)*d < (b+1)*d := by
    dsimp [b] at *
    simp only [Int.sub_mul, Int.add_mul, Int.one_mul] at *
    omega
  have h1 := Int.le_of_mul_le_mul_right hrl hd0
  have h2 := Int.lt_of_mul_lt_mul_right hru (Int.le_of_lt hd0)
  omega

private theorem word_toInt_eq_toNat (w : Word) (h : w.toNat < 2^63 ∨ 0 ≤ w.toInt) :
    w.toInt = (w.toNat : Int) := by
  have hn := BitVec.toInt_eq_toNat_cond w
  have hl := w.isLt
  split at hn <;> omega

/-- One hardware Newton step is the exact integer step and keeps the range and `2^60` envelope. -/
theorem q32NewtonStep_invariant (d x : Word)
    (hd : 2147483648 ≤ d.toInt ∧ d.toInt ≤ 4294967296)
    (hx : (0 ≤ x.toInt ∧ x.toInt ≤ 12884901888) ∧
      -1152921504606846976 ≤ 18446744073709551616-d.toInt*x.toInt ∧
      18446744073709551616-d.toInt*x.toInt ≤ 1152921504606846976) :
    (q32NewtonStep d x).toInt = x.toInt*(8589934592-d.toInt*x.toInt/4294967296)/4294967296 ∧
    (0 ≤ (q32NewtonStep d x).toInt ∧ (q32NewtonStep d x).toInt ≤ 12884901888) ∧
    -1152921504606846976 ≤ 18446744073709551616-d.toInt*(q32NewtonStep d x).toInt ∧
      18446744073709551616-d.toInt*(q32NewtonStep d x).toInt ≤ 1152921504606846976 := by
  have hw : (q32NewtonStep d x).toInt =
      x.toInt*(8589934592-d.toInt*x.toInt/4294967296)/4294967296 := q32_nr_word_step d x hd hx.1
  have hb := q32_nr_residual_bound d.toInt x.toInt 1152921504606846976 hd hx.1 hx.2
  dsimp only at hb
  rw [← hw] at hb
  exact ⟨hw, q32_nr_range_of_residual d.toInt _ 1152921504606846976 hd (by decide) (by omega),
    by omega⟩

/-- The word-level seed and four Newton steps meet the normalized three-unit residual. -/
theorem q32ReciprocalMantissa_residual (d : Word)
    (hd : 2147483648 ≤ d.toInt ∧ d.toInt ≤ 4294967296) :
    (0 ≤ (q32ReciprocalMantissa d).toInt ∧ (q32ReciprocalMantissa d).toInt ≤ 12884901888) ∧
    -12884901888 ≤ 18446744073709551616-d.toInt*(q32ReciprocalMantissa d).toInt ∧
      18446744073709551616-d.toInt*(q32ReciprocalMantissa d).toInt ≤ 12884901888 := by
  have hc : (ratToQ32Word (32/17)).toInt = 8084644321 := by decide +kernel
  have hs : (ratToQ32Word (48/17)).toInt = 12126966482 := by decide +kernel
  have hq := qmul32_toInt (ratToQ32Word (32/17)) d (by rw [hc]; omega)
  rw [hc] at hq
  have hx0 : (ratToQ32Word (48/17) - evalAluOp .qmul32 (ratToQ32Word (32/17)) d).toInt =
      12126966482 - 8084644321*d.toInt/4294967296 := by
    rw [BitVec.toInt_sub, hs, hq]
    change (12126966482 - 8084644321*d.toInt/4294967296).bmod 18446744073709551616 = _
    exact Int.bmod_eq_of_le (by omega) (by omega)
  obtain ⟨hr0, he0⟩ := q32_nr_seed_bound d.toInt hd
  have hn := q32_nr_normalized_residual d.toInt hd
  dsimp only at hn
  rw [← hx0] at hr0 he0 hn
  have s1 := q32NewtonStep_invariant d _ hd ⟨hr0, he0⟩
  have s2 := q32NewtonStep_invariant d _ hd s1.2
  have s3 := q32NewtonStep_invariant d _ hd s2.2
  have s4 := q32NewtonStep_invariant d _ hd s3.2
  rw [← s1.1, ← s2.1, ← s3.1, ← s4.1] at hn
  exact ⟨s4.2.1, hn⟩

private theorem q32_round_scale (A K Q u dp : Int) (hK : 0 < K) (hQK : Q*K = 2147483648)
    (hu : A*K = u)
    (hdp : dp*2147483648 ≤ u + 1073741824 ∧ u + 1073741824 < dp*2147483648 + 2147483648) :
    -Q ≤ A - dp*Q ∧ A - dp*Q ≤ Q := by
  have e : (A - dp*Q)*K = u - dp*2147483648 := by rw [Int.sub_mul, Int.mul_assoc, hQK, hu]
  exact ⟨Int.le_of_mul_le_mul_right (by rw [e, Int.neg_mul, hQK]; omega) hK,
    Int.le_of_mul_le_mul_right (by rw [e, hQK]; omega) hK⟩

/-- Unsigned magnitude path of `evalQ32Reciprocal`: normalize, Newton mantissa, rescale. -/
def q32ReciprocalMagnitude (a : Word) : Word :=
  match q32NormalizeLoop [32,16,8,4,2,1] a 0 with
  | (u, k) =>
    let x := q32ReciprocalMantissa ((u + (1#64 <<< 30)) >>> 31)
    if k < 31 then x >>> (31 - k) else x <<< (k - 31)

theorem evalQ32Reciprocal_eq_magnitude (d : Word) : evalQ32Reciprocal d =
    if d.slt 0#64 then -q32ReciprocalMagnitude (-d) else q32ReciprocalMagnitude d := by
  unfold evalQ32Reciprocal q32ReciprocalMagnitude
  conv => zeta
  cases d.slt 0#64
  · generalize hnk : q32NormalizeLoop [32,16,8,4,2,1] (if false = true then -d else d) 0 = nk
    rw [show (if false = true then -d else d) = d from rfl] at hnk
    rw [hnk]; obtain ⟨u, k⟩ := nk
    simp only [Bool.false_eq_true, ↓reduceIte]; rfl
  · generalize hnk : q32NormalizeLoop [32,16,8,4,2,1] (if true = true then -d else d) 0 = nk
    rw [show (if true = true then -d else d) = -d from rfl] at hnk
    rw [hnk]; obtain ⟨u, k⟩ := nk
    simp only [↓reduceIte]; rfl

/-- Full-range magnitude residual: `|mag * a - 2^64| ≤ 6 * 2^32 + a` for `16 ≤ a ≤ 2^60`. -/
theorem q32ReciprocalMagnitude_residual (a : Word) (ha : 16 ≤ a.toNat ∧ a.toNat ≤ 2^60) :
    (q32ReciprocalMagnitude a).toNat < 2^62 ∧
    -(6 * (2 : Int)^32 + a.toNat) ≤
        ((q32ReciprocalMagnitude a).toNat : Int) * a.toNat - (2 : Int)^64 ∧
      ((q32ReciprocalMagnitude a).toNat : Int) * a.toNat - (2 : Int)^64 ≤
        6 * (2 : Int)^32 + a.toNat := by
  obtain ⟨hu0, hu1, hfac, hk0, hk1⟩ := q32NormalizeLoop_bounds a ha
  unfold q32ReciprocalMagnitude
  generalize q32NormalizeLoop [32,16,8,4,2,1] a 0 = nk at hu0 hu1 hfac hk0 hk1 ⊢
  obtain ⟨u, k⟩ := nk
  dsimp only at hu0 hu1 hfac hk0 hk1 ⊢
  have h30 : (1#64 <<< 30).toNat = 1073741824 := by decide +kernel
  have hdp : ((u + (1#64 <<< 30)) >>> 31).toNat = (u.toNat + 1073741824) / 2147483648 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, h30, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega)]
  generalize (u + (1#64 <<< 30)) >>> 31 = dp at hdp ⊢
  have hdi := word_toInt_eq_toNat dp (Or.inl (by omega))
  obtain ⟨hx, hnr⟩ := q32ReciprocalMantissa_residual dp (by omega)
  generalize q32ReciprocalMantissa dp = x at hx hnr ⊢
  have hxi := word_toInt_eq_toNat x (Or.inr hx.1)
  rw [hxi] at hx
  rw [hxi, hdi, Int.mul_comm] at hnr
  by_cases hk : k < 31
  · rw [ite_eq_left hk, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hQK : (2 : Nat)^(31-k) * 2^k = 2147483648 := by
      rw [← Nat.pow_add, show 31 - k + k = 31 by omega]
    have hKpos := Nat.two_pow_pos k
    have hQpos := Nat.two_pow_pos (31-k)
    generalize (2 : Nat)^(31-k) = Q at hQK hQpos ⊢
    generalize (2 : Nat)^k = K at hQK hKpos hfac
    have hround := q32_round_scale a.toNat K Q u.toNat dp.toNat (by omega)
      (by omega) (by omega) (by omega)
    have hp := q32_nr_postscale_residual a.toNat dp.toNat x.toNat Q (Int.natCast_nonneg _)
      (by omega) hx hround (by omega)
    have hle := Nat.div_le_self x.toNat Q
    exact ⟨by omega, by rw [Int.natCast_ediv]; omega⟩
  · rw [ite_eq_right hk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hpow : (2 : Nat)^k = 2^(k-31) * 2147483648 := by
      rw [show (2147483648 : Nat) = 2^31 from rfl, ← Nat.pow_add, show k - 31 + 31 = k by omega]
    have hT : (2 : Nat)^(k-31) ≤ 2^27 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hpow, ← Nat.mul_assoc] at hfac
    generalize (2 : Nat)^(k-31) = T at hT hfac ⊢
    have hxT := Nat.mul_le_mul (show x.toNat ≤ 12884901888 by omega) hT
    rw [Nat.mod_eq_of_lt (by omega)]
    have hscale : (dp.toNat : Int) = a.toNat * T := by
      rw [show dp.toNat = a.toNat * T by omega, Int.natCast_mul]
    have hp := q32_nr_upscale_residual a.toNat dp.toNat x.toNat T hscale (by omega)
    exact ⟨by omega, by rw [Int.natCast_mul]; omega⟩

/-- **Full-range LUT-free reciprocal accuracy (`evalQ32Reciprocal_residual_bound`)**: for every
64-bit word with `16 ≤ |d| ≤ 2^60`, the normalized four-step Newton reciprocal `r` satisfies
`|r * d - 2^64| ≤ 6 * 2^32 + |d|`, with the sign restored and no intermediate wrap. -/
theorem evalQ32Reciprocal_residual_bound (d : Word)
    (hd : 16 ≤ d.toInt.natAbs ∧ d.toInt.natAbs ≤ 2^60) :
    -(6 * (2 : Int)^32 + d.toInt.natAbs) ≤
        (evalQ32Reciprocal d).toInt * d.toInt - (2 : Int)^64 ∧
      (evalQ32Reciprocal d).toInt * d.toInt - (2 : Int)^64 ≤
        6 * (2 : Int)^32 + d.toInt.natAbs := by
  have hc := BitVec.toInt_eq_toNat_cond d
  have hl := d.isLt
  rw [evalQ32Reciprocal_eq_magnitude]
  by_cases hneg : d.toInt < 0
  · have ha : ((-d).toNat : Int) = -d.toInt := by rw [BitVec.toNat_neg]; split at hc <;> omega
    obtain ⟨hm, hr⟩ := q32ReciprocalMagnitude_residual (-d) (by omega)
    rw [ha, Int.mul_neg, ← Int.neg_mul] at hr
    rw [ite_eq_left (by simp [BitVec.slt, hneg]), BitVec.toInt_neg, word_toInt_eq_toNat
      (q32ReciprocalMagnitude (-d)) (Or.inl (by omega)), Int.bmod_eq_of_le (by omega) (by omega)]
    omega
  · have ha : (d.toNat : Int) = d.toInt := by split at hc <;> omega
    obtain ⟨hm, hr⟩ := q32ReciprocalMagnitude_residual d (by omega)
    rw [ha] at hr
    rw [ite_eq_right (by simp [BitVec.slt, hneg]),
      word_toInt_eq_toNat (q32ReciprocalMagnitude d) (Or.inl (by omega))]
    omega

theorem checkedQ32Interval_bounds (lo hi : Int) (iv : Q32Interval)
    (h : checkedQ32Interval lo hi = some iv) :
    iv.lo = lo ∧ iv.hi = hi ∧ -((2 : Int)^62) < iv.lo ∧ iv.hi < (2 : Int)^62 := by
  unfold checkedQ32Interval at h
  split at h
  · rename_i hb
    cases Option.some.inj h
    exact ⟨rfl, rfl, hb.2⟩
  · contradiction

theorem reciprocalQ32Interval_refuses_small (iv : Q32Interval)
    (h : iv.lo < 16 ∧ -16 < iv.hi) : reciprocalQ32Interval iv = none := by
  unfold reciprocalQ32Interval
  split
  · omega
  · split
    · omega
    · rfl

theorem propagateSsaInterval_bounds (numVars : Nat) (box : Nat → Q32Interval)
    (params : Nat → Rat) (acc : Array Q32Interval) (n : FluxSsaNode) (iv : Q32Interval)
    (h : propagateSsaInterval numVars box params acc n = some iv) :
    -((2 : Int)^62) < iv.lo ∧ iv.hi < (2 : Int)^62 := by
  have hc : ∀ lo hi, checkedQ32Interval lo hi = some iv →
      -((2 : Int)^62) < iv.lo ∧ iv.hi < (2 : Int)^62 :=
    fun lo hi hh => (checkedQ32Interval_bounds lo hi iv hh).2.2
  cases n with
  | var i =>
    simp only [propagateSsaInterval] at h
    split at h <;> first | exact hc _ _ h | contradiction
  | const q | param q | neg a =>
    obtain ⟨x, _, hx⟩ := Option.bind_eq_some_iff.mp h
    exact hc _ _ hx
  | add a b | sub a b | mul a b =>
    obtain ⟨x, _, hx⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, _, hy⟩ := Option.bind_eq_some_iff.mp hx
    exact hc _ _ hy
  | invSafe a =>
    obtain ⟨x, _, hx⟩ := Option.bind_eq_some_iff.mp h
    unfold reciprocalQ32Interval at hx
    repeat' (split at hx <;> try contradiction)
    all_goals exact hc _ _ hx

theorem inferSsaDagQ32Intervals_bounds (numVars : Nat) (box : Nat → Q32Interval)
    (params : Nat → Rat) (dag : FluxSsaDag) (ivs : Array Q32Interval)
    (h : inferSsaDagQ32Intervals numVars box params dag = some ivs) :
    ∀ iv ∈ ivs, -((2 : Int)^62) < iv.lo ∧ iv.hi < (2 : Int)^62 := by
  suffices ∀ ns acc, (∀ iv ∈ acc, -((2 : Int)^62) < iv.lo ∧ iv.hi < (2 : Int)^62) →
      inferNodesQ32Intervals numVars box params ns acc = some ivs →
      ∀ iv ∈ ivs, -((2 : Int)^62) < iv.lo ∧ iv.hi < (2 : Int)^62 from
    this dag.nodes #[] (by simp) h
  intro ns
  induction ns with
  | nil => intro acc hb hh; cases Option.some.inj hh; exact hb
  | cons n ns ih =>
    intro acc hb hh
    obtain ⟨iv, hn, ht⟩ := Option.bind_eq_some_iff.mp hh
    exact ih (acc.push iv) (fun x hx => (Array.mem_push.mp hx).elim (hb x)
      (fun e => e ▸ propagateSsaInterval_bounds numVars box params acc n iv hn)) ht

private theorem int_mul_le_max (a lo hi t : Int) (h : lo ≤ t ∧ t ≤ hi) :
    a*t ≤ max (a*lo) (a*hi) := by
  by_cases h0 : 0 ≤ a
  · have h1 := Int.mul_le_mul_of_nonneg_left h.2 h0
    omega
  · have h1 := Int.mul_le_mul_of_nonneg_left h.1 (show 0 ≤ -a by omega)
    rw [Int.neg_mul, Int.neg_mul] at h1
    omega

private theorem int_mul_le_corner (xl xh yl yh x y : Int) (hx : xl ≤ x ∧ x ≤ xh)
    (hy : yl ≤ y ∧ y ≤ yh) :
    x*y ≤ max (max (xl*yl) (xl*yh)) (max (xh*yl) (xh*yh)) := by
  have h1 := int_mul_le_max y xl xh x hx
  have h2 := int_mul_le_max xl yl yh y hy
  have h3 := int_mul_le_max xh yl yh y hy
  rw [Int.mul_comm y x, Int.mul_comm y xl, Int.mul_comm y xh] at h1
  omega

private theorem int_mul_div_corner_bounds (xl xh yl yh x y : Int) (hx : xl ≤ x ∧ x ≤ xh)
    (hy : yl ≤ y ∧ y ≤ yh) :
    min (min (xl*yl/(2 : Int)^32) (xl*yh/(2 : Int)^32))
        (min (xh*yl/(2 : Int)^32) (xh*yh/(2 : Int)^32)) ≤ x*y/(2 : Int)^32 ∧
      x*y/(2 : Int)^32 ≤ max (max (xl*yl/(2 : Int)^32) (xl*yh/(2 : Int)^32))
        (max (xh*yl/(2 : Int)^32) (xh*yh/(2 : Int)^32)) := by
  have hu := int_mul_le_corner xl xh yl yh x y hx hy
  have hl := int_mul_le_corner (-xh) (-xl) yl yh (-x) y (by omega) hy
  simp only [Int.neg_mul] at hl
  omega

/-- Signed enclosure with the guard bit: `w ∈ [iv.lo, iv.hi] ⊂ (-2^62, 2^62)`. -/
@[expose, reducible] def q32Encloses (iv : Q32Interval) (w : Word) : Prop :=
  -((2 : Int)^62) < iv.lo ∧ iv.lo ≤ w.toInt ∧ w.toInt ≤ iv.hi ∧ iv.hi < (2 : Int)^62

/-- Unbounded-integer meaning of one SSA node over the words already evaluated. -/
def q32NodeIntSem (inputs : Nat → Word) (params : Nat → Rat) (vals : Array Word) :
    FluxSsaNode → Int
  | .const q => ratToQ32Scaled q
  | .var i => (inputs i).toInt
  | .param p => ratToQ32Scaled (params p)
  | .neg a => -(vals.getD a 0#64).toInt
  | .add a b => (vals.getD a 0#64).toInt + (vals.getD b 0#64).toInt
  | .sub a b => (vals.getD a 0#64).toInt - (vals.getD b 0#64).toInt
  | .mul a b => (vals.getD a 0#64).toInt * (vals.getD b 0#64).toInt / (2 : Int)^32
  | .invSafe a => (evalQ32Reciprocal (vals.getD a 0#64)).toInt

/-- One accepted propagation step: the evaluated word lies in the inferred interval and equals
the unbounded-integer node meaning, so no signed 64-bit wrap occurred. -/
theorem propagateSsaInterval_encloses (numVars : Nat) (box : Nat → Q32Interval)
    (params : Nat → Rat) (inputs : Nat → Word)
    (hin : ∀ i, i < numVars → (box i).lo ≤ (inputs i).toInt ∧ (inputs i).toInt ≤ (box i).hi)
    (acc : Array Q32Interval) (vals : Array Word)
    (hacc : ∀ j iv, acc[j]? = some iv → q32Encloses iv (vals.getD j 0#64))
    (n : FluxSsaNode) (iv : Q32Interval)
    (h : propagateSsaInterval numVars box params acc n = some iv) :
    q32Encloses iv (evalFluxSsaNodeQ32 inputs params vals n) ∧
      (evalFluxSsaNodeQ32 inputs params vals n).toInt = q32NodeIntSem inputs params vals n := by
  have hwrap : ∀ (lo hi z : Int) (w : Word), checkedQ32Interval lo hi = some iv →
      (w.toInt = z ∨ w.toInt = z.bmod (2^64)) → lo ≤ z → z ≤ hi →
      q32Encloses iv w ∧ w.toInt = z := by
    intro lo hi z w hh hw h1 h2
    obtain ⟨e1, e2, b1, b2⟩ := checkedQ32Interval_bounds lo hi iv hh
    have e : w.toInt = z :=
      hw.elim id fun hw => hw.trans (Int.bmod_eq_of_le (by omega) (by omega))
    exact ⟨⟨b1, by omega, by omega, b2⟩, e⟩
  cases n with
  | const q | param q =>
    obtain ⟨w, hw, hiv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hs, _, _⟩ := ratToQ32Checked_sound _ w hw
    exact hwrap _ _ (ratToQ32Scaled _) (ratToQ32Word _) hiv (.inr (BitVec.toInt_ofInt ..))
      (by omega) (by omega)
  | var i =>
    simp only [propagateSsaInterval] at h
    split at h
    · exact hwrap _ _ _ (inputs i) h (.inl rfl) (hin i ‹_›).1 (hin i ‹_›).2
    · contradiction
  | neg a =>
    obtain ⟨x, hx, hiv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, xl, xh, _⟩ := hacc a x hx
    exact hwrap _ _ (-(vals.getD a 0#64).toInt) (-vals.getD a 0#64) hiv
      (.inr (BitVec.toInt_neg ..)) (by omega) (by omega)
  | add a b =>
    obtain ⟨x, hx, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, hiv⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨_, xl, xh, _⟩ := hacc a x hx
    obtain ⟨_, yl, yh, _⟩ := hacc b y hy
    exact hwrap _ _ ((vals.getD a 0#64).toInt + (vals.getD b 0#64).toInt)
      (vals.getD a 0#64 + vals.getD b 0#64) hiv (.inr (BitVec.toInt_add ..)) (by omega) (by omega)
  | sub a b =>
    obtain ⟨x, hx, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, hiv⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨_, xl, xh, _⟩ := hacc a x hx
    obtain ⟨_, yl, yh, _⟩ := hacc b y hy
    exact hwrap _ _ ((vals.getD a 0#64).toInt - (vals.getD b 0#64).toInt)
      (vals.getD a 0#64 - vals.getD b 0#64) hiv (.inr (BitVec.toInt_sub ..)) (by omega) (by omega)
  | mul a b =>
    obtain ⟨x, hx, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, hiv⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨xb1, xl, xh, xb2⟩ := hacc a x hx
    obtain ⟨yb1, yl, yh, yb2⟩ := hacc b y hy
    obtain ⟨hlo, hhi⟩ := int_mul_div_corner_bounds x.lo x.hi y.lo y.hi
      (vals.getD a 0#64).toInt (vals.getD b 0#64).toInt ⟨xl, xh⟩ ⟨yl, yh⟩
    obtain ⟨e1, e2, b1, b2⟩ := checkedQ32Interval_bounds _ _ iv hiv
    rw [← e1] at hlo; rw [← e2] at hhi
    have e := qmul32_toInt (vals.getD a 0#64) (vals.getD b 0#64) (by omega)
    rw [← e] at hlo hhi
    exact ⟨⟨b1, hlo, hhi, b2⟩, e⟩
  | invSafe a =>
    obtain ⟨x, hx, hiv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xb1, xl, xh, xb2⟩ := hacc a x hx
    unfold reciprocalQ32Interval at hiv
    split at hiv
    · rename_i hp
      have hr := evalQ32Reciprocal_residual_bound (vals.getD a 0#64) (by omega)
      obtain ⟨r1, r2⟩ := q32_interval_of_residual x.lo x.hi (vals.getD a 0#64).toInt
        (evalQ32Reciprocal (vals.getD a 0#64)).toInt hp.1 ⟨xl, xh⟩ (by omega)
      exact hwrap _ _ _ (evalQ32Reciprocal (vals.getD a 0#64)) hiv (.inl rfl) r1 r2
    · split at hiv
      · rename_i hn
        have hr := evalQ32Reciprocal_residual_bound (vals.getD a 0#64) (by omega)
        obtain ⟨r1, r2⟩ := q32_interval_of_residual (-x.hi) (-x.lo) (-(vals.getD a 0#64).toInt)
          (-(evalQ32Reciprocal (vals.getD a 0#64)).toInt) (by omega) (by omega)
          (by rw [Int.neg_mul_neg]; omega)
        exact hwrap _ _ _ (evalQ32Reciprocal (vals.getD a 0#64)) hiv (.inl rfl)
          (Int.neg_le_of_neg_le r2) (Int.le_neg_of_le_neg r1)
      · contradiction

/-- **Signed Q32 interval soundness (`inferSsaDagQ32Intervals_encloses_eval`)**: when inference
accepts a DAG and every input word lies in its declared box, every evaluated SSA word lies in its
inferred guard-bit interval, so every DAG output stays strictly inside `(-2^62, 2^62)`. -/
theorem inferSsaDagQ32Intervals_encloses_eval (numVars : Nat) (box : Nat → Q32Interval)
    (params : Nat → Rat) (dag : FluxSsaDag) (ivs : Array Q32Interval)
    (h : inferSsaDagQ32Intervals numVars box params dag = some ivs) (inputs : Nat → Word)
    (hin : ∀ i, i < numVars → (box i).lo ≤ (inputs i).toInt ∧ (inputs i).toInt ≤ (box i).hi) :
    (∀ j iv, ivs[j]? = some iv → q32Encloses iv ((dag.nodes.foldl
      (fun a n => a.push (evalFluxSsaNodeQ32 inputs params a n)) #[]).getD j 0#64)) ∧
    ∀ w ∈ evalFluxSsaDagQ32 inputs params dag,
      -((2 : Int)^62) < w.toInt ∧ w.toInt < (2 : Int)^62 := by
  have key : ∀ (ns : List FluxSsaNode) (acc : Array Q32Interval) (vals : Array Word),
      vals.size = acc.size →
      (∀ j iv, acc[j]? = some iv → q32Encloses iv (vals.getD j 0#64)) →
      inferNodesQ32Intervals numVars box params ns acc = some ivs →
      (ns.foldl (fun a n => a.push (evalFluxSsaNodeQ32 inputs params a n)) vals).size = ivs.size ∧
      ∀ j iv, ivs[j]? = some iv → q32Encloses iv
        ((ns.foldl (fun a n => a.push (evalFluxSsaNodeQ32 inputs params a n)) vals).getD j 0#64) := by
    intro ns
    induction ns with
    | nil => intro acc vals hs ha h; cases Option.some.inj h; exact ⟨hs, ha⟩
    | cons n ns ih =>
      intro acc vals hs ha h
      obtain ⟨iv, hn, ht⟩ := Option.bind_eq_some_iff.mp h
      refine ih (acc.push iv) (vals.push _) (by simp [hs]) ?_ ht
      intro j iv' hj
      rw [Array.getElem?_push] at hj
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
      split at hj
      · cases Option.some.inj hj
        rw [ite_eq_left (by omega)]
        exact (propagateSsaInterval_encloses numVars box params inputs hin acc vals ha n _ hn).1
      · rw [ite_eq_right (by omega), ← Array.getD_eq_getD_getElem?]; exact ha j iv' hj
  obtain ⟨hs, he⟩ := key dag.nodes #[] #[] rfl (by simp) h
  refine ⟨he, ?_⟩
  intro w hw
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hw
  by_cases hr : r < ivs.size
  · obtain ⟨b1, l, u, b2⟩ := he r ivs[r] (Array.getElem?_eq_getElem hr)
    omega
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    decide

/-- Declared `stateBox` entry when both ends encode, else positive variables in [0.5,4], rest [-4,4]. -/
def pdeQ32StateBox (spec : ConservationLawSpec) (i : Nat) : Q32Interval :=
  let dflt : Q32Interval := if PosTarget.stateVar i ∈ spec.domain then
    ⟨(2 : Int)^31, 4 * (2 : Int)^32, by decide⟩ else ⟨-4 * (2 : Int)^32, 4 * (2 : Int)^32, by decide⟩
  match spec.stateBox[i]? with
  | none => dflt
  | some b => match ratToQ32Checked b.1, ratToQ32Checked b.2 with
    | some wLo, some wHi => if h : wLo.toInt ≤ wHi.toInt then ⟨wLo.toInt, wHi.toInt, h⟩ else dflt
    | _, _ => dflt

def checkPdeQ32Intervals (spec : ConservationLawSpec) : Bool :=
  (specializeFluxSweep spec).axisFluxDags.all fun dag =>
    (inferSsaDagQ32Intervals spec.numVars (pdeQ32StateBox spec) spec.paramEnv dag).isSome

/-- Every accepted solver keeps each directional flux output word inside the guard-bit range
for all inputs in the canonical state box. -/
theorem checkPdeQ32Intervals_sound (spec : ConservationLawSpec)
    (h : checkPdeQ32Intervals spec = true) (inputs : Nat → Word)
    (hin : ∀ i, i < spec.numVars → (pdeQ32StateBox spec i).lo ≤ (inputs i).toInt ∧
      (inputs i).toInt ≤ (pdeQ32StateBox spec i).hi) :
    ∀ dag ∈ (specializeFluxSweep spec).axisFluxDags,
      ∀ w ∈ evalFluxSsaDagQ32 inputs spec.paramEnv dag,
        -((2 : Int)^62) < w.toInt ∧ w.toInt < (2 : Int)^62 := by
  intro dag hm
  unfold checkPdeQ32Intervals at h
  rw [List.all_eq_true] at h
  obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.mp (h dag hm)
  exact (inferSsaDagQ32Intervals_encloses_eval _ _ _ _ ivs hivs inputs hin).2

/-- Check fixed-point constants before any modular encoding, including specialized flux constants. -/
def checkPdeQ32Constants (spec : ConservationLawSpec) : Bool :=
  (ratToQ32Checked spec.cfl).isSome && (ratToQ32Checked (spec.aMax / 2)).isSome &&
  (specializeFluxSweep spec).axisFluxDags.all fun dag => dag.nodes.all fun n =>
    match n with
    | .const q => (ratToQ32Checked q).isSome
    | .param p => (ratToQ32Checked (spec.paramEnv p)).isSome
    | _ => true

/-- Synthesize the pipelined Q32.32 systolic `RtlModule` for directional flux `axis` of `spec`. -/
def buildSpecSystolicRtl (spec : ConservationLawSpec) (axis : Nat) : RtlModule :=
  let plan := specializeFluxSweep spec
  let dag := getOr plan.axisFluxDags axis ⟨[], []⟩
  emitSystolicFluxCellRtlModule s!"{spec.name}_flux_axis{axis}" spec.vars dag

theorem spec_systolicRtl_ok (spec : ConservationLawSpec) (axis : Nat) :
    checkRtlModule (buildSpecSystolicRtl spec axis) = true := by
  unfold buildSpecSystolicRtl
  exact emitSystolicFluxCellRtlModule_ok _ _ _

theorem domainValid_nil (env : FluxEnv) : DomainValid [] env := fun _ h => nomatch h

/-! ## 3. Meta `Lean.Expr` Quoters & Proof-Producing Tactics (`flux_eq_by_canon`, `sym_jacobian_frechet`) -/

meta def quoteRatExpr (q : Rat) : Lean.Expr :=
  let numExpr : Lean.Expr := ToExpr.toExpr q.num
  let denExpr : Lean.Expr := ToExpr.toExpr q.den
  mkApp2 (mkConst ``Rat.divInt) numExpr (mkApp (mkConst ``Int.ofNat) denExpr)

meta def quoteListExpr {α : Type} (elemTy : Lean.Expr) (quoteElem : α → Lean.Expr) : List α → Lean.Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) elemTy
  | x :: xs =>
    mkApp3 (mkConst ``List.cons [Level.zero]) elemTy (quoteElem x) (quoteListExpr elemTy quoteElem xs)

meta def quoteFluxExpr : FluxExpr → Lean.Expr
  | .const q => mkApp (mkConst ``FluxExpr.const) (quoteRatExpr q)
  | .var i => mkApp (mkConst ``FluxExpr.var) (ToExpr.toExpr i)
  | .param p => mkApp (mkConst ``FluxExpr.param) (ToExpr.toExpr p)
  | .neg a => mkApp (mkConst ``FluxExpr.neg) (quoteFluxExpr a)
  | .add a b => mkApp2 (mkConst ``FluxExpr.add) (quoteFluxExpr a) (quoteFluxExpr b)
  | .sub a b => mkApp2 (mkConst ``FluxExpr.sub) (quoteFluxExpr a) (quoteFluxExpr b)
  | .mul a b => mkApp2 (mkConst ``FluxExpr.mul) (quoteFluxExpr a) (quoteFluxExpr b)
  | .invSafe d => mkApp (mkConst ``FluxExpr.invSafe) (quoteFluxExpr d)

meta def quotePosTarget : PosTarget → Lean.Expr
  | .stateVar idx => mkApp (mkConst ``PosTarget.stateVar) (ToExpr.toExpr idx)
  | .paramVar idx => mkApp (mkConst ``PosTarget.paramVar) (ToExpr.toExpr idx)
meta def quoteSlopeLimiter (k : SlopeLimiterKind) : Lean.Expr :=
  if k = .minmod then mkConst ``SlopeLimiterKind.minmod else mkConst ``SlopeLimiterKind.firstOrder

meta def quoteParamPair (p : String × Rat) : Lean.Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
    (mkConst ``String) (mkConst ``Rat) (ToExpr.toExpr p.1) (quoteRatExpr p.2)

meta def quoteConservationLawSpec (s : ConservationLawSpec) : Lean.Expr :=
  let strTy := mkConst ``String
  let fluxExprTy := mkConst ``FluxExpr
  let fluxRowTy := mkApp (mkConst ``List [Level.zero]) fluxExprTy
  let paramPairTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) strTy (mkConst ``Rat)
  let posTargetTy := mkConst ``PosTarget
  let ratTy := mkConst ``Rat
  let quotePair := fun (b : Rat × Rat) => mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
    ratTy ratTy (quoteRatExpr b.1) (quoteRatExpr b.2)
  mkAppN (mkConst ``ConservationLawSpec.mk) #[
    ToExpr.toExpr s.name, quoteListExpr strTy ToExpr.toExpr s.coords,
    quoteListExpr strTy ToExpr.toExpr s.vars, quoteListExpr paramPairTy quoteParamPair s.params,
    quoteListExpr posTargetTy quotePosTarget s.domain,
    quoteListExpr fluxRowTy (quoteListExpr fluxExprTy quoteFluxExpr) s.fluxes,
    quoteRatExpr s.aMax, quoteRatExpr s.cfl, quoteSlopeLimiter s.limiter,
    quoteListExpr fluxExprTy quoteFluxExpr s.sources,
    quoteListExpr (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) ratTy ratTy) quotePair s.stateBox,
    quoteListExpr ratTy quoteRatExpr s.wavespeedWeights]

theorem flux_eq_of_canon {dom : List PosTarget} {e1 e2 : FluxExpr} {env : FluxEnv}
    (hDom : DomainValid dom env) (hOk : checkFluxEqReflective dom e1 e2 = true) :
    evalFlux e1 env = evalFlux e2 env :=
  checkFluxEqReflective_sound dom e1 e2 hOk env hDom

/-- `by flux_eq_by_canon`: Discharges goals of the form `evalFlux e₁ env = evalFlux e₂ env` using
local hypothesis `hDom : DomainValid dom env` and reflective `CanonPoly` (`checkFluxEqReflective_sound`). -/
macro "flux_eq_by_canon" : tactic =>
  `(tactic| (
    try dsimp only
    first
      | refine flux_eq_of_canon (by assumption) (by decide +kernel)
      | refine flux_eq_of_canon (domainValid_nil _) (by decide +kernel)))

/-- `by sym_jacobian_frechet`: Discharges multivariable Fréchet Taylor remainder goals via
`symJacobian_frechet_taylor` or `symExpr_frechet_taylor` and `decide +kernel` domain-safety verification. -/
macro "sym_jacobian_frechet" : tactic =>
  `(tactic| (
    try dsimp only
    first
      | apply symJacobian_frechet_taylor <;> first | assumption | decide +kernel
      | apply symExpr_frechet_taylor <;>
          first
            | assumption
            | exact checkExprDomainSafe_implies_denomNonzero [] _ _ (by decide +kernel) (domainValid_nil _)))

private theorem checkSymmetrizerReflective_inhabited :
    ∃ (dom : List PosTarget) (m : Nat) (H jac : List (List FluxExpr)),
      0 < m ∧ 0 < dom.length ∧ checkSymmetrizerReflective dom m H jac = true :=
  ⟨[.stateVar 0], 2,
    [[.const 2, .const 0], [.const 0, .const 3]],
    [[.const 0, .mul (.const 3) (.var 0)], [.mul (.const 2) (.var 0), .const 0]],
    by decide, by decide, by decide +kernel⟩

private theorem checkPdeQ32Intervals_inhabited :
    ∃ spec : ConservationLawSpec,
      0 < (specializeFluxSweep spec).axisFluxDags.length ∧ checkPdeQ32Intervals spec = true := by
  let spec : ConservationLawSpec :=
    { name := "toy_2var", coords := ["x"], vars := ["u", "v"], params := [], domain := []
    , fluxes := [[.add (.var 0) (.var 1), .mul (.var 0) (.var 1)]]
    , aMax := 4, cfl := 1 / 2, limiter := .firstOrder, sources := []
    , stateBox := [(1, 2), (1, 2)], wavespeedWeights := [1, 1] }
  exact ⟨spec, by decide +kernel, by decide +kernel⟩

end Obend.Tactic.SymDiffAndFlux
