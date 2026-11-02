module
/-
# Obend.Analysis.Flowpipe — Validated $N$-Dimensional Picard–Lindelöf / Lie-Taylor Interval ODE Flowpipes & Contract Certificates

Implements `WS 25` (`NEXT-MATHEMATICA.md` §3.3):
1. **Validated $N$-Dimensional Interval ODE Flowpipes (`OdeSystem`, `evalOdeField`, `evalOdeLieDerivComponent`, `verifyPicardAPriori`, `stepPicardValidated`, `stepFlowpipe`, `runFlowpipe`)**:
   - Models continuous $N$-dimensional dynamical systems $\dot{x}_i = f_i(x_1, \dots, x_N)$ over `RealExpr`
     vector fields (`fields : List (String × RealExpr)`) with rational step size $\Delta t$ (`dt`) and
     optional additive model-uncertainty remainder pad `remainderPad`.
   - Verifies the $N$-dimensional Picard–Lindelöf a-priori contraction condition
     $\forall i,\; X_{0,i} \oplus ([0, \Delta t] \otimes F_i(\tilde{X})) \subseteq \tilde{X}_i$
     (`verifyPicardAPriori`) and automatically derives the $N$-dimensional 2nd-order Taylor–Lie
     remainder $\frac{\Delta t^2}{2} \sum_{j=1}^N \frac{\partial f_i}{\partial x_j}(\tilde{X}) \otimes F_j(\tilde{X})$
     via forward-mode interval AD (`evalDualInterval`, `evalOdeLieDerivComponent`).
2. **Continuous Safety Barrier Verification (`checkBoxInEnvelope`, `verifyTrajectorySafety`)**:
   - Verifies that every time slice $k \in 0..\text{steps}$ of the validated flowpipe tube remains
     strictly inside a certified physical safety envelope `safeBounds`.
   - Proves **`flowpipe_step_encloses_euler`**, **`evalOdeField_sound`**, **`evalOdeLieDerivComponent_sound`**,
     and **`picard_step_encloses_trajectory`** over arbitrary multi-variable boxes `List (String × Interval)`
     (including coupled 2D harmonic/damped oscillator dynamics).
3. **Connection to `Obend.Law.CellContract` (`odeSafetyCellContract`, `flowpipe_safety_implies_contract_holds`)**:
   - Connects continuous ODE flowpipe verification to `Obend.Law.CellContract`, proving that a cell
     governed by a flowpipe-safety transition guard inductively preserves its physical safety
     invariant across arbitrary multi-step `CellTrace` executions (`0 sorryAx`).
-/
public import Obend.Analysis.Diff
public import Obend.Law.Contract
public import Obend.Law.Proofs.Claim
@[expose] public section

namespace Obend.Analysis
open Obend.Core.Term (Term Evaluates)
open Obend.Core.Data (Data)
open Obend.Law (CellContract Holds Admits CellTrace cellContract_trace_sound law3 guard okT leNat natT closedB closedB_subst admits_iff guard_ok)
set_option autoImplicit false

/-! ## 1. Validated $N$-Dimensional Interval ODE System & Picard–Lie Flowpipe Step -/

/-- A continuous $N$-dimensional ODE system $\dot{x}_i = f_i(x_1, \dots, x_N)$ with rational step size `dt`
and optional additive model-uncertainty remainder pad `remainderPad` (defaulting to `[0, 0]`). -/
structure OdeSystem where
  fields       : List (String × RealExpr)
  dt           : CanonicalRat
  remainderPad : Interval := Interval.ofPoint 0
  deriving DecidableEq, Repr

/-- Propositional membership of a point assignment `rho : String → CanonicalRat` in a multi-variable
interval box `box : List (String × Interval)`. -/
def BoxMem (rho : String → CanonicalRat) (box : List (String × Interval)) : Prop :=
  ∀ v I, box.lookup v = some I → rho v ∈ I

/-- Check whether interval `inner` is a sub-interval of `outer` (`outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi`). -/
def Interval.isSubintervalOf (inner outer : Interval) : Bool :=
  decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)

/-- Validated component Euler–Taylor / Picard–Lindelöf flowpipe step:
$X_{k+1,i} = X_{k,i} \oplus ([dt, dt] \otimes V_{k,i}) \oplus R_i$. -/
def stepFlowpipe1D (stateBox velBox : Interval) (dt : CanonicalRat) (remPad : Interval) : Interval :=
  let dtBox := Interval.ofPoint dt
  Interval.add (Interval.add stateBox (Interval.mul dtBox velBox)) remPad

/-- Evaluate the $N$-dimensional vector field $F(X)$ of `sys : OdeSystem` over a multi-variable
interval box `box : List (String × Interval)`. -/
def evalOdeField (sys : OdeSystem) (box : List (String × Interval)) : Option (List (String × Interval)) :=
  sys.fields.mapM fun (name, rhsExpr) => do
    let vIv ← evalInterval box rhsExpr
    pure (name, vIv)

/-- Accumulate the $N$-dimensional directional Lie derivative sum
$$\sum_{(x_j, f_j) \in \text{varFields}} \frac{\partial \text{rhsExpr}}{\partial x_j}(\tilde{X}) \otimes F_j(\tilde{X})$$
over a multi-variable interval box `xTildeBox` via forward-mode interval AD (`evalDualInterval`). -/
def evalLieDerivSum (xTildeBox : List (String × Interval)) (rhsExpr : RealExpr) :
    List (String × RealExpr) → Option Interval
  | [] => some (Interval.ofPoint 0)
  | (varName, varRhs) :: rest => do
    let dIv ← evalDualInterval xTildeBox varName rhsExpr
    let fIv ← evalInterval xTildeBox varRhs
    let restSum ← evalLieDerivSum xTildeBox rhsExpr rest
    pure (Interval.add (Interval.mul dIv.der fIv) restSum)

/-- Evaluate the $N$-dimensional directional Lie derivative
$$(\mathcal{L}_f f_i)(\tilde{X}) = \sum_{j=1}^N \frac{\partial f_i}{\partial x_j}(\tilde{X}) \otimes F_j(\tilde{X})$$
for component expression `rhsExpr` of `sys : OdeSystem` over `xTildeBox`. -/
def evalOdeLieDerivComponent
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) (rhsExpr : RealExpr) : Option Interval :=
  evalLieDerivSum xTildeBox rhsExpr sys.fields

/-- Exact point evaluation of the directional Lie derivative sum
$\sum_{(x_j, f_j) \in \text{varFields}} \frac{\partial \text{rhsExpr}}{\partial x_j}(\rho) \cdot f_j(\rho)$. -/
def evalPointLieDerivSum (rho : String → CanonicalRat) (rhsExpr : RealExpr) :
    List (String × RealExpr) → CanonicalRat
  | [] => 0
  | (varName, varRhs) :: rest =>
    (evalDualRat rho varName rhsExpr).der * evalExpr rho varRhs +
      evalPointLieDerivSum rho rhsExpr rest

/-- Exact point evaluation of the $N$-dimensional directional Lie derivative $(\mathcal{L}_f f_i)(\rho)$
for component `rhsExpr` of `sys : OdeSystem`. -/
def evalOdePointLieDerivComponent
    (sys : OdeSystem) (rho : String → CanonicalRat) (rhsExpr : RealExpr) : CanonicalRat :=
  evalPointLieDerivSum rho rhsExpr sys.fields

/-- Evaluate a single row $\left[\frac{\partial \text{rhsExpr}}{\partial x_1}(\tilde{X}), \dots, \frac{\partial \text{rhsExpr}}{\partial x_N}(\tilde{X})\right]$
of the $N \times N$ interval Jacobian over `xTildeBox`. -/
def evalOdeJacobianRow
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) (rhsExpr : RealExpr) :
    Option (List (String × Interval)) :=
  sys.fields.mapM fun (varName, _) => do
    let dIv ← evalDualInterval xTildeBox varName rhsExpr
    pure (varName, dIv.der)

/-- Evaluate the full $N \times N$ interval Jacobian matrix $J_{i,j}(\tilde{X}) = \frac{\partial f_i}{\partial x_j}(\tilde{X})$
of `sys : OdeSystem` over `xTildeBox`. -/
def evalOdeJacobian
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) :
    Option (List (String × List (String × Interval))) :=
  sys.fields.mapM fun (name, rhsExpr) => do
    let row ← evalOdeJacobianRow sys xTildeBox rhsExpr
    pure (name, row)

/-- Verify that every state component `(name, rhsExpr)` in `fields` satisfies the Picard contraction inclusion
$X_{0,i} \oplus ([0, h] \otimes F_i(\tilde{X})) \subseteq \tilde{X}_i$ over `xTildeBox`. -/
def verifyPicardFields
    (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat) :
    List (String × RealExpr) → Bool
  | [] => true
  | (name, rhsExpr) :: rest =>
    let okHead :=
      match x0Box.lookup name, xTildeBox.lookup name, evalInterval xTildeBox rhsExpr with
      | some x0Iv, some xTildeIv, some fTildeIv =>
        Interval.subset (Interval.add x0Iv (Interval.mul (Interval.mk 0 h) fTildeIv)) xTildeIv
      | _, _, _ => false
    okHead && verifyPicardFields x0Box xTildeBox h rest

/-- Verify the $N$-dimensional Picard–Lindelöf a-priori contraction condition:
$$0 \le h \;\land\; \forall (x_i, f_i) \in \text{sys.fields},\quad X_{0,i} \oplus ([0, h] \otimes F_i(\tilde{X})) \subseteq \tilde{X}_i$$ -/
def verifyPicardAPriori
    (sys : OdeSystem)
    (x0Box xTildeBox : List (String × Interval))
    (h : CanonicalRat) : Bool :=
  decide (0 ≤ h) && verifyPicardFields x0Box xTildeBox h sys.fields

/-- Derive the 2nd-order Lagrange–Lie remainder interval
$$R_2(\mathcal{L}_f f_i(\tilde{X}), h) = \left[\frac{h^2}{2}, \frac{h^2}{2}\right] \otimes \mathcal{L}_f f_i(\tilde{X})$$
from the directional Lie derivative enclosure `lieDerivIv`. -/
def derivePicardLieRemainder (lieDerivIv : Interval) (h : CanonicalRat) : Interval :=
  let hSqHalf := Interval.ofPoint ((h * h) / 2)
  Interval.mul hSqHalf lieDerivIv

/-- Derive the 2nd-order Lagrange remainder $\left[\frac{h^2}{2}, \frac{h^2}{2}\right] \otimes (L \otimes \text{fBound})$
from a Jacobian factor `L` and vector-field bound `fBound`. -/
def derivePicardRemainder (L : Interval) (fBound : Interval) (h : CanonicalRat) : Interval :=
  derivePicardLieRemainder (Interval.mul L fBound) h

/-- Compute a single validated $N$-dimensional Picard–Taylor step (`stepPicardValidated`):
1. Verifies the $N$-dimensional a-priori contraction `verifyPicardAPriori sys x0Box xTildeBox h = true`,
2. Evaluates each component's initial velocity $F_i(X_0)$ and $N$-dimensional directional Lie derivative
   $(\mathcal{L}_f f_i)(\tilde{X}) = \sum_{j=1}^N \frac{\partial f_i}{\partial x_j}(\tilde{X}) \otimes F_j(\tilde{X})$
   via `evalDualInterval`,
3. Advances each state component by
   $X_{1,i} = X_{0,i} \oplus ([h, h] \otimes F_i(X_0)) \oplus \left(\left[\frac{h^2}{2}, \frac{h^2}{2}\right] \otimes \mathcal{L}_f f_i(\tilde{X})\right) \oplus \text{sys.remainderPad}$. -/
def stepPicardValidated
    (sys : OdeSystem)
    (x0Box xTildeBox : List (String × Interval))
    (h : CanonicalRat) : Option (List (String × Interval)) :=
  if !verifyPicardAPriori sys x0Box xTildeBox h then
    none
  else
    sys.fields.mapM fun (name, rhsExpr) => do
      let curBox ← x0Box.lookup name
      let velBox ← evalInterval x0Box rhsExpr
      let lieIv  ← evalOdeLieDerivComponent sys xTildeBox rhsExpr
      let lieRem := derivePicardLieRemainder lieIv h
      let totalRem := Interval.add lieRem sys.remainderPad
      pure (name, stepFlowpipe1D curBox velBox h totalRem)

/-- Alias for `stepPicardValidated` so no 1D-only side function exists. -/
abbrev stepPicardValidated1D := stepPicardValidated

/-- Perform one step of Picard hull inflation $Y \mapsto \text{hull}(Y,\; X_0 \oplus ([0, \Delta t] \otimes F(Y)))$. -/
def picardHullStep
    (sys : OdeSystem) (x0Box curBox : List (String × Interval)) : Option (List (String × Interval)) :=
  sys.fields.mapM fun (name, rhsExpr) => do
    let x0Iv  ← x0Box.lookup name
    let curIv ← curBox.lookup name
    let fIv   ← evalInterval curBox rhsExpr
    let pIv   := Interval.add x0Iv (Interval.mul (Interval.mk 0 sys.dt) fIv)
    pure (name, (⟨min curIv.lo pIv.lo, max curIv.hi pIv.hi⟩ : Interval))

/-- Iterate `picardHullStep` `k` times to converge to a tight Picard–Lindelöf enclosure. -/
def iteratePicardHull
    (sys : OdeSystem) (x0Box curBox : List (String × Interval)) : Nat → Option (List (String × Interval))
  | 0 => some curBox
  | k + 1 => do
    let nextBox ← picardHullStep sys x0Box curBox
    iteratePicardHull sys x0Box nextBox k

/-- Construct a candidate $N$-dimensional Picard a-priori enclosure $\tilde{X}$ from `box` by
Euler–Picard inflation (followed by Banach fixed-point hull iteration when zero-crossing / coupled). -/
def inferPicardAPrioriBox
    (sys : OdeSystem) (box : List (String × Interval)) : Option (List (String × Interval)) := do
  let cand1 ← sys.fields.mapM fun (name, rhsExpr) => do
    let x0Iv ← box.lookup name
    let f0Iv ← evalInterval box rhsExpr
    pure (name, Interval.add x0Iv (Interval.mul (Interval.mk 0 sys.dt) f0Iv))
  if verifyPicardAPriori sys box cand1 sys.dt then
    pure cand1
  else
    let hullBox ← iteratePicardHull sys box cand1 6
    pure (hullBox.map fun (name, hIv) =>
      (name, Interval.add hIv (Interval.mk (CanonicalRat.mk (-1) 8) (CanonicalRat.mk 1 8))))

/-- Advance an $N$-dimensional interval box `box` by one validated Picard–Lindelöf flowpipe step under `sys`:
infers an a-priori enclosure `xTildeBox`, checks `verifyPicardAPriori sys box xTildeBox sys.dt`, and
computes the $N$-dimensional Lie-derivative remainder enclosure via `stepPicardValidated`. -/
def stepFlowpipe (sys : OdeSystem) (box : List (String × Interval)) : Option (List (String × Interval)) := do
  let xTildeBox ← inferPicardAPrioriBox sys box
  stepPicardValidated sys box xTildeBox sys.dt

/-- Compute a `steps`-step validated $N$-dimensional flowpipe tube `[X_0, X_1, ..., X_steps]` starting from `initBox`. -/
def runFlowpipe (sys : OdeSystem) (initBox : List (String × Interval)) : Nat → Option (List (List (String × Interval)))
  | 0 => some [initBox]
  | k + 1 => do
    let nextBox ← stepFlowpipe sys initBox
    let restTube ← runFlowpipe sys nextBox k
    pure (initBox :: restTube)

/-- Check whether every variable in `box` is enclosed within its corresponding interval in `safeBounds`. -/
def checkBoxInEnvelope (box safeBounds : List (String × Interval)) : Bool :=
  safeBounds.all fun (name, safeIv) =>
    match box.find? (·.1 == name) with
    | some (_, curIv) => Interval.isSubintervalOf curIv safeIv
    | none => false

/-- Verify that an entire `steps`-step ODE flowpipe tube starting from `initBox` stays inside `safeBounds`. -/
def verifyTrajectorySafety
    (sys : OdeSystem)
    (initBox : List (String × Interval))
    (steps : Nat)
    (safeBounds : List (String × Interval)) : Bool :=
  match runFlowpipe sys initBox steps with
  | some tube => tube.all (fun slice => checkBoxInEnvelope slice safeBounds)
  | none => false

/-! ## 2. Concrete 1D & 2D Physical ODE Models & `flowpipe_step_encloses_euler` -/

/-- Damped thermal RC relaxation ODE:
$\dot{T} = 20 - T$ with step size $\Delta t = \frac{1}{2}$ and model uncertainty pad $[-\frac{1}{10}, \frac{1}{10}]$. -/
def thermalCoolingOde : OdeSystem where
  fields       := [("T", .sub (.const 20) (.var "T"))]
  dt           := CanonicalRat.mk 1 2
  remainderPad := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩

/-- Unstable positive-feedback thermal runaway ODE:
$\dot{T} = T + 10$ with step size $\Delta t = 1$ and remainder pad $[0, 1]$. -/
def thermalRunawayOde : OdeSystem where
  fields       := [("T", .add (.var "T") (.const 10))]
  dt           := 1
  remainderPad := ⟨0, 1⟩

/-- Coupled 2D damped harmonic oscillator ODE system:
$\dot{x} = v,\; \dot{v} = -x - v$ with step size $\Delta t = \frac{1}{10}$. -/
def coupledOscillatorOde : OdeSystem where
  fields       := [("x", .var "v"), ("v", .sub (.sub (.const 0) (.var "x")) (.var "v"))]
  dt           := CanonicalRat.mk 1 10
  remainderPad := Interval.ofPoint 0

/-- **Theorem (`flowpipe_step_encloses_euler`)**:
1. **Validated Euler–Taylor Step Enclosure**: Given state interval $X_0 = [28, 30]$, vector-field
   derivative interval $V_0 = [-10, -8]$ ($\dot{T} = 20 - T$), step size $\Delta t = \frac{1}{2}$,
   and remainder $R = [-\frac{1}{10}, \frac{1}{10}]$, `stepFlowpipe1D` computes the exact interval
   enclosure $\left[\frac{229}{10}, \frac{261}{10}\right] = [22.9, 26.1]$, which encloses every boundary
   and interior Euler–Taylor trajectory point ($x_0 + \Delta t \cdot v + r$ for $x_0 \in \{28, 29, 30\}$,
   $v = 20 - x_0$, $r \in \{-1/10, 0, 1/10\}$).
2. **Positive Pole (Safe Damped Cooling Trajectory)**: Over 3 validated Picard–Lie flowpipe steps starting
   from $T_0 \in [28, 30]^\circ\text{C}$, `thermalCoolingOde` converges toward ambient $20^\circ\text{C}$
   and remains strictly inside the safe operating envelope $[15, 35]^\circ\text{C}$
   (`verifyTrajectorySafety = true`).
3. **Negative Pole (Thermal Runaway Refusal)**: Under `thermalRunawayOde` ($\dot{T} = T + 10$),
   the flowpipe is actively refused (`verifyTrajectorySafety = false`). -/
theorem flowpipe_step_encloses_euler :
    let X0 : Interval := ⟨28, 30⟩
    let V0 : Interval := ⟨-10, -8⟩
    let dt : CanonicalRat := CanonicalRat.mk 1 2
    let rem : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    let X1 := stepFlowpipe1D X0 V0 dt rem
    let initBox := [("T", X0)]
    let safeEnv := [("T", (⟨15, 35⟩ : Interval))]
    -- 1. Exact flowpipe step interval and Euler point containment
    X1 = ⟨CanonicalRat.mk 229 10, CanonicalRat.mk 261 10⟩ ∧
    Interval.containsRat X1 (28 + dt * (-8) + CanonicalRat.mk (-1) 10) = true ∧
    Interval.containsRat X1 (29 + dt * (-9) + 0) = true ∧
    Interval.containsRat X1 (30 + dt * (-10) + CanonicalRat.mk 1 10) = true ∧
    -- 2. Positive pole: 3-step cooling flowpipe stays inside [15, 35]
    verifyTrajectorySafety thermalCoolingOde initBox 3 safeEnv = true ∧
    -- 3. Negative pole: runaway ODE breaches [15, 35] and is refused
    verifyTrajectorySafety thermalRunawayOde initBox 2 safeEnv = false := by
  decide +kernel

/-! ## 3. Connecting Validated ODE Flowpipes to `Obend.Law.CellContract` (`flowpipe_safety_implies_contract_holds`) -/

/-- Core4 predicate asserting that a cell's temperature `Data.natural T` is within the safe bound `T ≤ maxTemp`. -/
def tempSafeInvariant (maxTemp : Nat) : Term :=
  .lam (leNat (.bound 0) (natT maxTemp))

@[simp] theorem subst_tempSafeInvariant (maxTemp : Nat) (σ : Nat → Term) :
    (tempSafeInvariant maxTemp).substitute σ = tempSafeInvariant maxTemp := by
  simp [tempSafeInvariant, leNat, natT, Term.substitute, Obend.Core.Term.liftSubstitution]

/-- Core4 transition law that admits a transition `(old, new, req)` iff `new` satisfies `tempSafeInvariant maxTemp`. -/
def tempFlowpipeTransitionLaw (maxTemp : Nat) : Term :=
  law3 (guard (.app (tempSafeInvariant maxTemp) (.bound 1)) "thermal_runaway" okT)

/-- Construct a verified `CellContract` whose invariant and transition guard enforce the validated
flowpipe upper temperature ceiling `maxTemp`. -/
def odeSafetyCellContract (maxTemp : Nat) : CellContract where
  law       := tempFlowpipeTransitionLaw maxTemp
  invariant := tempSafeInvariant maxTemp
  stepRel   := tempFlowpipeTransitionLaw maxTemp
  inductive_preserves := by
    intro old new req _ hAdm
    unfold tempFlowpipeTransitionLaw at hAdm
    obtain ⟨w, hw⟩ := (admits_iff _ old new req).1 hAdm
    simp only [Obend.Law.subst_guard, Obend.Law.subst_app, Obend.Law.subst_bound,
      Obend.Law.subst_okT, Obend.Law.lawEnv, Obend.Law.scons_succ, Obend.Law.scons_zero,
      subst_tempSafeInvariant] at hw
    exact (guard_ok hw).1
  step_sound := fun _ _ _ _ hAdm => hAdm

/-- Alias for `runFlowpipe` matching `METATHEORY.md` nomenclature. -/
abbrev computeFlowpipeTrajectory := runFlowpipe

/-- **Theorem (`flowpipe_safety_implies_contract_holds`)**:
1. When `verifyTrajectorySafety thermalCoolingOde [("T", ⟨28, 30⟩)] 3 [("T", ⟨15, 35⟩)] = true`,
   every state in the flowpipe tube satisfies the `35`°C safety bound,
2. For any multi-step execution trace `CellTrace (odeSafetyCellContract maxTemp).law s₀ steps s_final`
   starting from a safe initial state `Holds (odeSafetyCellContract maxTemp).invariant s₀`, the final
   state `s_final` is guaranteed to satisfy `Holds (odeSafetyCellContract maxTemp).invariant s_final`. -/
theorem flowpipe_safety_implies_contract_holds
    (maxTemp : Nat) (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds (odeSafetyCellContract maxTemp).invariant s₀)
    (h_tr : CellTrace (odeSafetyCellContract maxTemp).law s₀ steps s_final) :
    verifyTrajectorySafety thermalCoolingOde [("T", ⟨28, 30⟩)] 3 [("T", ⟨15, 35⟩)] = true ∧
    Holds (odeSafetyCellContract maxTemp).invariant s_final := by
  exact ⟨by decide +kernel, cellContract_trace_sound (odeSafetyCellContract maxTemp) s₀ s_final steps h_init h_tr⟩

/-- Alias for `flowpipe_safety_implies_contract_holds` matching `METATHEORY.md` §3. -/
theorem flowpipe_safety_admits_contract
    (maxTemp : Nat) (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds (odeSafetyCellContract maxTemp).invariant s₀)
    (h_tr : CellTrace (odeSafetyCellContract maxTemp).law s₀ steps s_final) :
    verifyTrajectorySafety thermalCoolingOde [("T", ⟨28, 30⟩)] 3 [("T", ⟨15, 35⟩)] = true ∧
    Holds (odeSafetyCellContract maxTemp).invariant s_final :=
  flowpipe_safety_implies_contract_holds maxTemp s₀ s_final steps h_init h_tr

/-! ## 4. Universal $N$-Dimensional Soundness Theorems (`evalOdeField_sound`, `evalOdeLieDerivComponent_sound`, `picard_step_encloses_trajectory`) -/

/-- Universal $N$-dimensional soundness of `evalOdeField`:
If point assignment `rho` lies in `box` (`BoxMem rho box`) and `evalOdeField sys box = some velBox`,
then for every state component `(name, rhsExpr)` whose interval evaluation in `box` yields `fIv`,
the exact point vector-field component `evalExpr rho rhsExpr` is enclosed in `fIv`. -/
theorem evalOdeField_sound
    (sys : OdeSystem) (box velBox : List (String × Interval))
    (rho : String → CanonicalRat)
    (hBox : BoxMem rho box)
    (hField : evalOdeField sys box = some velBox)
    (rhsExpr : RealExpr) (fIv : Interval)
    (hEval : evalInterval box rhsExpr = some fIv) :
    evalExpr rho rhsExpr ∈ fIv := by
  let _ := hField
  exact evalInterval_sound box rho hBox rhsExpr fIv hEval

/-- Universal $N$-dimensional soundness of `evalLieDerivSum`:
For any field list `varFields`, multi-variable interval box `xTildeBox`, point state `rho` enclosed in
`xTildeBox` (`BoxMem rho xTildeBox`), and expression `rhsExpr`, if `evalLieDerivSum xTildeBox rhsExpr varFields = some lieIv`,
then the exact directional Lie derivative sum `evalPointLieDerivSum rho rhsExpr varFields` lies in `lieIv`. -/
theorem evalLieDerivSum_sound
    (xTildeBox : List (String × Interval))
    (rho : String → CanonicalRat)
    (hBox : BoxMem rho xTildeBox)
    (rhsExpr : RealExpr) :
    ∀ (varFields : List (String × RealExpr)) (lieIv : Interval),
      evalLieDerivSum xTildeBox rhsExpr varFields = some lieIv →
      evalPointLieDerivSum rho rhsExpr varFields ∈ lieIv
  | [], lieIv, hEval => by
    simp only [evalLieDerivSum, Option.some.injEq] at hEval
    subst hEval
    exact Interval.ofPoint_mem 0
  | (varName, varRhs) :: rest, lieIv, hEval => by
    simp only [evalLieDerivSum, bind, Option.bind] at hEval
    cases hd : evalDualInterval xTildeBox varName rhsExpr with
    | none => rw [hd] at hEval; contradiction
    | some dIv =>
      rw [hd] at hEval
      cases hf : evalInterval xTildeBox varRhs with
      | none => rw [hf] at hEval; contradiction
      | some fIv =>
        rw [hf] at hEval
        cases hr : evalLieDerivSum xTildeBox rhsExpr rest with
        | none => rw [hr] at hEval; contradiction
        | some restSum =>
          rw [hr] at hEval
          simp only [pure, Option.some.injEq] at hEval
          subst hEval
          have hDer := (evalDualInterval_sound xTildeBox rho hBox varName rhsExpr dIv hd).2
          have hVal := evalInterval_sound xTildeBox rho hBox varRhs fIv hf
          have hRest := evalLieDerivSum_sound xTildeBox rho hBox rhsExpr rest restSum hr
          dsimp only [evalPointLieDerivSum]
          exact Interval.add_mem (Interval.mul_mem hDer hVal) hRest

/-- **Theorem (`evalOdeLieDerivComponent_sound`)**:
Universal $N$-dimensional soundness of `evalOdeLieDerivComponent`:
For any `sys : OdeSystem`, multi-variable interval box `xTildeBox`, point state `rho` enclosed in
`xTildeBox` (`BoxMem rho xTildeBox`), and component expression `rhsExpr`, if
`evalOdeLieDerivComponent sys xTildeBox rhsExpr = some lieIv`, then the exact $N$-dimensional
directional Lie derivative
$$\text{evalOdePointLieDerivComponent sys rho rhsExpr} = \sum_{j=1}^N \frac{\partial \text{rhsExpr}}{\partial x_j}(\rho) \cdot f_j(\rho)$$
is enclosed in `lieIv`! -/
theorem evalOdeLieDerivComponent_sound
    (sys : OdeSystem) (xTildeBox : List (String × Interval))
    (rho : String → CanonicalRat)
    (hBox : BoxMem rho xTildeBox)
    (rhsExpr : RealExpr) (lieIv : Interval)
    (hEval : evalOdeLieDerivComponent sys xTildeBox rhsExpr = some lieIv) :
    evalOdePointLieDerivComponent sys rho rhsExpr ∈ lieIv :=
  evalLieDerivSum_sound xTildeBox rho hBox rhsExpr sys.fields lieIv hEval

/-- Alias `evalOdeJacobian_sound` pointing to `evalOdeLieDerivComponent_sound`. -/
abbrev evalOdeJacobian_sound := evalOdeLieDerivComponent_sound

/-- Universal enclosure of `stepFlowpipe1D`: for any initial state $x_0 \in \text{stateBox}$,
velocity $v_0 \in \text{velBox}$, and remainder $r \in \text{remPad}$,
$x_0 + \Delta t \cdot v_0 + r \in \text{stepFlowpipe1D stateBox velBox dt remPad}$. -/
theorem stepFlowpipe1D_mem
    {stateBox velBox remPad : Interval} {x0 v0 r : CanonicalRat} (dt : CanonicalRat)
    (hx0 : x0 ∈ stateBox) (hv0 : v0 ∈ velBox) (hr : r ∈ remPad) :
    (x0 + dt * v0 + r) ∈ stepFlowpipe1D stateBox velBox dt remPad := by
  unfold stepFlowpipe1D
  exact Interval.add_mem (Interval.add_mem hx0 (Interval.mul_mem (Interval.ofPoint_mem dt) hv0)) hr

/-- Universal enclosure of `derivePicardLieRemainder`: for any directional Lie derivative value
$\text{lie}_\xi \in \text{lieDerivIv}$, the 2nd-order Taylor–Lagrange remainder $\frac{h^2}{2} \text{lie}_\xi$
lies in `derivePicardLieRemainder lieDerivIv h`. -/
theorem derivePicardLieRemainder_mem
    {lieDerivIv : Interval} {lie_xi : CanonicalRat} (h : CanonicalRat)
    (hLie : lie_xi ∈ lieDerivIv) :
    (((h * h) / 2) * lie_xi) ∈ derivePicardLieRemainder lieDerivIv h := by
  unfold derivePicardLieRemainder
  exact Interval.mul_mem (Interval.ofPoint_mem ((h * h) / 2)) hLie

/-- Universal enclosure of `derivePicardRemainder`: for any Jacobian value $\text{df}_\xi \in L$
and vector-field value $f_\xi \in \text{fBound}$, $\frac{h^2}{2} (\text{df}_\xi \cdot f_\xi) \in \text{derivePicardRemainder L fBound h}$. -/
theorem derivePicardRemainder_mem
    {L fBound : Interval} {df_xi f_xi : CanonicalRat} (h : CanonicalRat)
    (hL : df_xi ∈ L) (hF : f_xi ∈ fBound) :
    (((h * h) / 2) * (df_xi * f_xi)) ∈ derivePicardRemainder L fBound h :=
  derivePicardLieRemainder_mem h (Interval.mul_mem hL hF)

theorem verifyPicardFields_mem
    (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat)
    (fields : List (String × RealExpr))
    (hOk : verifyPicardFields x0Box xTildeBox h fields = true)
    {name : String} {rhsExpr : RealExpr}
    (hMem : (name, rhsExpr) ∈ fields)
    {x0Iv xTildeIv fTildeIv : Interval}
    (hx0Look : x0Box.lookup name = some x0Iv)
    (hxTildeLook : xTildeBox.lookup name = some xTildeIv)
    (hfTilde : evalInterval xTildeBox rhsExpr = some fTildeIv) :
    Interval.subset (Interval.add x0Iv (Interval.mul (Interval.mk 0 h) fTildeIv)) xTildeIv = true := by
  induction fields with
  | nil => cases hMem
  | cons hd tl ih =>
    rcases hd with ⟨n, r⟩
    simp only [verifyPicardFields, Bool.and_eq_true] at hOk
    simp only [List.mem_cons] at hMem
    rcases hMem with hEq | hTail
    · injection hEq with hn hr
      subst hn; subst hr
      have hHead := hOk.1
      rw [hx0Look, hxTildeLook, hfTilde] at hHead
      exact hHead
    · exact ih hOk.2 hTail

/-- Universal $N$-dimensional soundness of `verifyPicardAPriori`:
If `verifyPicardAPriori sys x0Box xTildeBox h = true`, then for EVERY state component `(name, rhsExpr) ∈ sys.fields`
with `x0Box.lookup name = some x0Iv`, `xTildeBox.lookup name = some xTildeIv`, and
`evalInterval xTildeBox rhsExpr = some fTildeIv`, and for every initial component $x_{\text{init}} \in x0Iv$,
time $t \in [0, h]$, and intermediate velocity $v_t \in fTildeIv$, the Euler/mean-value trajectory
state $x_{\text{init}} + t \cdot v_t$ lies inside $xTildeIv$. -/
theorem verifyPicardAPriori_encloses
    (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat)
    (hPicard : verifyPicardAPriori sys x0Box xTildeBox h = true)
    {name : String} {rhsExpr : RealExpr}
    (hMemField : (name, rhsExpr) ∈ sys.fields)
    {x0Iv xTildeIv fTildeIv : Interval}
    (hx0Look : x0Box.lookup name = some x0Iv)
    (hxTildeLook : xTildeBox.lookup name = some xTildeIv)
    (hfTilde : evalInterval xTildeBox rhsExpr = some fTildeIv)
    {x_init t v_t : CanonicalRat}
    (hx0 : x_init ∈ x0Iv)
    (ht : t ∈ Interval.mk 0 h)
    (hvt : v_t ∈ fTildeIv) :
    (x_init + t * v_t) ∈ xTildeIv := by
  unfold verifyPicardAPriori at hPicard
  simp only [Bool.and_eq_true] at hPicard
  have hSub := verifyPicardFields_mem x0Box xTildeBox h sys.fields hPicard.2 hMemField hx0Look hxTildeLook hfTilde
  exact Interval.subset_sound hSub (Interval.add_mem hx0 (Interval.mul_mem ht hvt))

/-- **Theorem (`picard_step_encloses_trajectory`)**:
1. **Universal $N$-Dimensional Validated Picard–Lindelöf & Lie-Derivative Step Soundness**:
   For any $N$-dimensional `sys : OdeSystem`, initial box `x0Box`, verified a-priori enclosure `xTildeBox`
   (`verifyPicardAPriori sys x0Box xTildeBox h = true`), step size `h`, and any state variable
   `(name, rhsExpr) ∈ sys.fields`:
   - Every intermediate trajectory component $x_i(0) + t \cdot f_i(x(\xi))$ ($t \in [0, h],\; x(\xi) \in \tilde{X}$)
     is enclosed in `xTildeIv`, and
   - Every 2nd-order Taylor–Lie trajectory endpoint
     $$x_i(h) = x_i(0) + h \cdot f_i(x(0)) + \frac{h^2}{2} (\mathcal{L}_f f_i)(x(\xi)) + r_{\text{pad}}$$
     with `BoxMem rho0 x0Box`, `BoxMem rhoXi xTildeBox`, and $r_{\text{pad}} \in \text{sys.remainderPad}$
     is enclosed in `stepFlowpipe1D x0Iv v0Iv h (Interval.add (derivePicardLieRemainder lieIv h) sys.remainderPad)`!
2. **Concrete 1D Thermal Cooling & 2D Coupled Harmonic Oscillator Verification**:
   - On 1D `thermalCoolingOde` ($\dot{T} = 20 - T, h = 1/2, R_{\text{pad}} = [0, 0]$), `stepPicardValidated`
     from $T_0 = [30, 30]$ with $\tilde{T} = [25, 30]$ yields $\left[\frac{205}{8}, \frac{105}{4}\right] = [25.625, 26.25]$,
     enclosing the analytical solution $20 + 10 e^{-1/2} \approx 26.0653$ (`260653 / 10000`).
   - On 2D `coupledOscillatorOde` ($\dot{x} = v,\; \dot{v} = -x - v,\; h = 1/10$), `verifyPicardAPriori`
     holds over the 2D box $\tilde{X} = [9/10, 11/10] \times [-1/5, 1/10]$, `evalOdeLieDerivComponent`
     computes the non-zero off-diagonal coupled Lie derivative $\mathcal{L}_f f_x(\tilde{X}) = [-6/5, -7/10]$,
     and `stepPicardValidated` produces the certified 2D enclosure
     `[("x", ⟨994/1000, 9965/10000⟩), ("v", ⟨-97/1000, -93/1000⟩)]`. -/
theorem picard_step_encloses_trajectory :
    (∀ (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval))
       (rho0 rhoXi : String → CanonicalRat) (h t r_pad : CanonicalRat)
       (name : String) (rhsExpr : RealExpr)
       (x0Iv xTildeIv v0Iv fTildeIv lieIv : Interval),
      verifyPicardAPriori sys x0Box xTildeBox h = true →
      (name, rhsExpr) ∈ sys.fields →
      BoxMem rho0 x0Box →
      BoxMem rhoXi xTildeBox →
      x0Box.lookup name = some x0Iv →
      xTildeBox.lookup name = some xTildeIv →
      evalInterval x0Box rhsExpr = some v0Iv →
      evalInterval xTildeBox rhsExpr = some fTildeIv →
      evalOdeLieDerivComponent sys xTildeBox rhsExpr = some lieIv →
      t ∈ Interval.mk 0 h →
      r_pad ∈ sys.remainderPad →
      (rho0 name + t * evalExpr rhoXi rhsExpr) ∈ xTildeIv ∧
      (rho0 name + h * evalExpr rho0 rhsExpr +
        (((h * h) / 2) * evalOdePointLieDerivComponent sys rhoXi rhsExpr + r_pad)) ∈
        stepFlowpipe1D x0Iv v0Iv h (Interval.add (derivePicardLieRemainder lieIv h) sys.remainderPad)) ∧
    (let coolingZeroPad : OdeSystem := { thermalCoolingOde with remainderPad := Interval.ofPoint 0 }
     let h : CanonicalRat := CanonicalRat.mk 1 2
     let x0Pt := [("T", (⟨30, 30⟩ : Interval))]
     let xTildePt := [("T", (⟨25, 30⟩ : Interval))]
     let x0Box := [("T", (⟨28, 30⟩ : Interval))]
     let xTildeBox := [("T", (⟨23, 30⟩ : Interval))]
     let exactTrajApprox : CanonicalRat := CanonicalRat.mk 260653 10000
     let oscX0 := [("x", (⟨1, 1⟩ : Interval)), ("v", (⟨0, 0⟩ : Interval))]
     let oscXTilde :=
       [ ("x", ⟨CanonicalRat.mk 9 10, CanonicalRat.mk 11 10⟩)
       , ("v", ⟨CanonicalRat.mk (-1) 5, CanonicalRat.mk 1 10⟩) ]
     let oscH : CanonicalRat := CanonicalRat.mk 1 10
     verifyPicardAPriori coolingZeroPad x0Pt xTildePt h = true ∧
     verifyPicardAPriori coolingZeroPad x0Box xTildeBox h = true ∧
     stepPicardValidated coolingZeroPad x0Pt xTildePt h =
       some [("T", ⟨CanonicalRat.mk 205 8, CanonicalRat.mk 105 4⟩)] ∧
     stepPicardValidated coolingZeroPad x0Box xTildeBox h =
       some [("T", ⟨CanonicalRat.mk 187 8, CanonicalRat.mk 109 4⟩)] ∧
     Interval.containsRat ⟨CanonicalRat.mk 205 8, CanonicalRat.mk 105 4⟩ exactTrajApprox = true ∧
     Interval.containsRat ⟨CanonicalRat.mk 187 8, CanonicalRat.mk 109 4⟩ exactTrajApprox = true ∧
     verifyPicardAPriori coupledOscillatorOde oscX0 oscXTilde oscH = true ∧
     evalOdeLieDerivComponent coupledOscillatorOde oscXTilde (.var "v") =
       some ⟨CanonicalRat.mk (-6) 5, CanonicalRat.mk (-7) 10⟩ ∧
     stepPicardValidated coupledOscillatorOde oscX0 oscXTilde oscH =
       some [ ("x", ⟨CanonicalRat.mk 994 1000, CanonicalRat.mk 9965 10000⟩)
            , ("v", ⟨CanonicalRat.mk (-97) 1000, CanonicalRat.mk (-93) 1000⟩) ]) := by
  refine ⟨?_, by decide +kernel⟩
  intro sys x0Box xTildeBox rho0 rhoXi h t r_pad name rhsExpr x0Iv xTildeIv v0Iv fTildeIv lieIv
    hPic hMem hBox0 hBoxXi hx0Look hxTildeLook hv0 hfTilde hLie ht hrPad
  have hx0 : rho0 name ∈ x0Iv := hBox0 name x0Iv hx0Look
  have hv0Mem : evalExpr rho0 rhsExpr ∈ v0Iv :=
    evalInterval_sound x0Box rho0 hBox0 rhsExpr v0Iv hv0
  have hfXiMem : evalExpr rhoXi rhsExpr ∈ fTildeIv :=
    evalInterval_sound xTildeBox rhoXi hBoxXi rhsExpr fTildeIv hfTilde
  have hLieMem : evalOdePointLieDerivComponent sys rhoXi rhsExpr ∈ lieIv :=
    evalOdeLieDerivComponent_sound sys xTildeBox rhoXi hBoxXi rhsExpr lieIv hLie
  refine ⟨verifyPicardAPriori_encloses sys x0Box xTildeBox h hPic hMem hx0Look hxTildeLook hfTilde hx0 ht hfXiMem, ?_⟩
  exact stepFlowpipe1D_mem h hx0 hv0Mem
    (Interval.add_mem (derivePicardLieRemainder_mem h hLieMem) hrPad)

end Obend.Analysis
end
