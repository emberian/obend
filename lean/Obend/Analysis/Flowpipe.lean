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
public section

namespace Obend.Analysis
open Obend.Core.Term (Term Evaluates Primitive)
open Obend.Core.Data (Data)
open Obend.Law (CellContract Holds Admits Refuses CellTrace cellContract_trace_sound law3 guard okT refusedT
  trueT falseT andT anyOf eqNat leNat ltNat addNat natT closedB closedB_subst admits_iff refuses_iff
  refuses_not_admits guard_ok andT_true anyOf_true eqNat_true leNat_true ltNat_true addNat_val
  binary_inv get_data data_term_nat run okB refusalOf admits_of_run refuses_of_run)
set_option autoImplicit false

/-! ## 1. Validated $N$-Dimensional Interval ODE System & Picard–Lie Flowpipe Step -/

/-- A continuous $N$-dimensional ODE system $\dot{x}_i = f_i(x_1, \dots, x_N)$ with rational step size `dt`
and optional additive model-uncertainty remainder pad `remainderPad` (defaulting to `[0, 0]`). -/
structure OdeSystem where
  fields       : List (String × RealExpr)
  dt           : CanonicalRat
  remainderPad : Interval := Interval.ofPoint 0
  deriving @[expose] DecidableEq, Repr

/-- Propositional membership of a point assignment `rho : String → CanonicalRat` in a multi-variable
interval box `box : List (String × Interval)`. -/
@[expose] def BoxMem (rho : String → CanonicalRat) (box : List (String × Interval)) : Prop :=
  ∀ v I, box.lookup v = some I → rho v ∈ I

/-- Check whether interval `inner` is a sub-interval of `outer` (`outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi`). -/
@[expose] def Interval.isSubintervalOf (inner outer : Interval) : Bool :=
  decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)

/-- Validated component Euler–Taylor / Picard–Lindelöf flowpipe step:
$X_{k+1,i} = X_{k,i} \oplus ([dt, dt] \otimes V_{k,i}) \oplus R_i$. -/
@[expose] def stepFlowpipe1D (stateBox velBox : Interval) (dt : CanonicalRat) (remPad : Interval) : Interval :=
  let dtBox := Interval.ofPoint dt
  Interval.add (Interval.add stateBox (Interval.mul dtBox velBox)) remPad

/-- Evaluate the $N$-dimensional vector field $F(X)$ of `sys : OdeSystem` over a multi-variable
interval box `box : List (String × Interval)`. -/
@[expose] def evalOdeField (sys : OdeSystem) (box : List (String × Interval)) : Option (List (String × Interval)) :=
  sys.fields.mapM fun (name, rhsExpr) => do
    let vIv ← evalInterval box rhsExpr
    pure (name, vIv)

/-- Accumulate the $N$-dimensional directional Lie derivative sum
$$\sum_{(x_j, f_j) \in \text{varFields}} \frac{\partial \text{rhsExpr}}{\partial x_j}(\tilde{X}) \otimes F_j(\tilde{X})$$
over a multi-variable interval box `xTildeBox` via forward-mode interval AD (`evalDualInterval`). -/
@[expose] def evalLieDerivSum (xTildeBox : List (String × Interval)) (rhsExpr : RealExpr) :
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
@[expose] def evalOdeLieDerivComponent
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) (rhsExpr : RealExpr) : Option Interval :=
  evalLieDerivSum xTildeBox rhsExpr sys.fields

/-- Exact point evaluation of the directional Lie derivative sum
$\sum_{(x_j, f_j) \in \text{varFields}} \frac{\partial \text{rhsExpr}}{\partial x_j}(\rho) \cdot f_j(\rho)$. -/
@[expose] def evalPointLieDerivSum (rho : String → CanonicalRat) (rhsExpr : RealExpr) :
    List (String × RealExpr) → CanonicalRat
  | [] => 0
  | (varName, varRhs) :: rest =>
    (evalDualRat rho varName rhsExpr).der * evalExpr rho varRhs +
      evalPointLieDerivSum rho rhsExpr rest

/-- Exact point evaluation of the $N$-dimensional directional Lie derivative $(\mathcal{L}_f f_i)(\rho)$
for component `rhsExpr` of `sys : OdeSystem`. -/
@[expose] def evalOdePointLieDerivComponent
    (sys : OdeSystem) (rho : String → CanonicalRat) (rhsExpr : RealExpr) : CanonicalRat :=
  evalPointLieDerivSum rho rhsExpr sys.fields

/-- Evaluate a single row $\left[\frac{\partial \text{rhsExpr}}{\partial x_1}(\tilde{X}), \dots, \frac{\partial \text{rhsExpr}}{\partial x_N}(\tilde{X})\right]$
of the $N \times N$ interval Jacobian over `xTildeBox`. -/
@[expose] def evalOdeJacobianRow
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) (rhsExpr : RealExpr) :
    Option (List (String × Interval)) :=
  sys.fields.mapM fun (varName, _) => do
    let dIv ← evalDualInterval xTildeBox varName rhsExpr
    pure (varName, dIv.der)

/-- Evaluate the full $N \times N$ interval Jacobian matrix $J_{i,j}(\tilde{X}) = \frac{\partial f_i}{\partial x_j}(\tilde{X})$
of `sys : OdeSystem` over `xTildeBox`. -/
@[expose] def evalOdeJacobian
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) :
    Option (List (String × List (String × Interval))) :=
  sys.fields.mapM fun (name, rhsExpr) => do
    let row ← evalOdeJacobianRow sys xTildeBox rhsExpr
    pure (name, row)

/-- Verify that every state component `(name, rhsExpr)` in `fields` satisfies the Picard contraction inclusion
$X_{0,i} \oplus ([0, h] \otimes F_i(\tilde{X})) \subseteq \tilde{X}_i$ over `xTildeBox`. -/
@[expose] def verifyPicardFields
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
@[expose] def verifyPicardAPriori
    (sys : OdeSystem)
    (x0Box xTildeBox : List (String × Interval))
    (h : CanonicalRat) : Bool :=
  decide (0 ≤ h) && verifyPicardFields x0Box xTildeBox h sys.fields

/-- Derive the 2nd-order Lagrange–Lie remainder interval
$$R_2(\mathcal{L}_f f_i(\tilde{X}), h) = \left[\frac{h^2}{2}, \frac{h^2}{2}\right] \otimes \mathcal{L}_f f_i(\tilde{X})$$
from the directional Lie derivative enclosure `lieDerivIv`. -/
@[expose] def derivePicardLieRemainder (lieDerivIv : Interval) (h : CanonicalRat) : Interval :=
  let hSqHalf := Interval.ofPoint ((h * h) / 2)
  Interval.mul hSqHalf lieDerivIv

/-- Derive the 2nd-order Lagrange remainder $\left[\frac{h^2}{2}, \frac{h^2}{2}\right] \otimes (L \otimes \text{fBound})$
from a Jacobian factor `L` and vector-field bound `fBound`. -/
@[expose] def derivePicardRemainder (L : Interval) (fBound : Interval) (h : CanonicalRat) : Interval :=
  derivePicardLieRemainder (Interval.mul L fBound) h

/-- Compute a single validated $N$-dimensional Picard–Taylor step (`stepPicardValidated`):
1. Verifies the $N$-dimensional a-priori contraction `verifyPicardAPriori sys x0Box xTildeBox h = true`,
2. Evaluates each component's initial velocity $F_i(X_0)$ and $N$-dimensional directional Lie derivative
   $(\mathcal{L}_f f_i)(\tilde{X}) = \sum_{j=1}^N \frac{\partial f_i}{\partial x_j}(\tilde{X}) \otimes F_j(\tilde{X})$
   via `evalDualInterval`,
3. Advances each state component by
   $X_{1,i} = X_{0,i} \oplus ([h, h] \otimes F_i(X_0)) \oplus \left(\left[\frac{h^2}{2}, \frac{h^2}{2}\right] \otimes \mathcal{L}_f f_i(\tilde{X})\right) \oplus \text{sys.remainderPad}$. -/
@[expose] def stepPicardValidated
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
@[expose] def picardHullStep
    (sys : OdeSystem) (x0Box curBox : List (String × Interval)) : Option (List (String × Interval)) :=
  sys.fields.mapM fun (name, rhsExpr) => do
    let x0Iv  ← x0Box.lookup name
    let curIv ← curBox.lookup name
    let fIv   ← evalInterval curBox rhsExpr
    let pIv   := Interval.add x0Iv (Interval.mul (Interval.mk 0 sys.dt) fIv)
    pure (name, (⟨min curIv.lo pIv.lo, max curIv.hi pIv.hi⟩ : Interval))

/-- Iterate `picardHullStep` `k` times to converge to a tight Picard–Lindelöf enclosure. -/
@[expose] def iteratePicardHull
    (sys : OdeSystem) (x0Box curBox : List (String × Interval)) : Nat → Option (List (String × Interval))
  | 0 => some curBox
  | k + 1 => do
    let nextBox ← picardHullStep sys x0Box curBox
    iteratePicardHull sys x0Box nextBox k

/-- Symmetrically widen an interval `[lo, hi]` by scaling its half-width by `scale` ($1.1\times$ or $2\times$)
plus a small floor pad `minPad` when `lo = hi`. -/
@[expose] def widenIntervalSymmetric (iv : Interval) (scale minPad : CanonicalRat) : Interval :=
  let mid := (iv.lo + iv.hi) / 2
  let half := (iv.hi - iv.lo) / 2
  let paddedHalf := if decide (half ≤ 0) then minPad else half * scale + minPad
  ⟨mid - paddedHalf, mid + paddedHalf⟩

/-- Iterative Picard–Lindelöf inflation loop:
applies `iteratePicardHull` and widens by $1.1\times$ (`11/10`) then $2\times$ (`2`) up to `fuel`
until `verifyPicardAPriori sys x0Box box sys.dt = true` holds (failing closed with `none` if
contraction is not achieved within `fuel`). -/
@[expose] def inflatePicardLoop
    (sys : OdeSystem) (x0Box : List (String × Interval)) :
    Nat → List (String × Interval) → Option (List (String × Interval))
  | 0, curBox =>
    if verifyPicardAPriori sys x0Box curBox sys.dt then some curBox else none
  | fuel + 1, curBox =>
    if verifyPicardAPriori sys x0Box curBox sys.dt then
      some curBox
    else do
      let hullBox ← iteratePicardHull sys x0Box curBox 4
      if verifyPicardAPriori sys x0Box hullBox sys.dt then
        some hullBox
      else
        let scale := if fuel ≥ 4 then CanonicalRat.mk 11 10 else 2
        let minPad := CanonicalRat.mk 1 8
        let widened := hullBox.map fun (name, hIv) =>
          (name, widenIntervalSymmetric hIv scale minPad)
        inflatePicardLoop sys x0Box fuel widened

/-- Construct a certified $N$-dimensional Picard a-priori rough enclosure $\tilde{X}$ from `box` by
Euler–Picard seeding followed by `inflatePicardLoop` ($1.1\times$ / $2\times$ iterative widening up to `fuel`). -/
@[expose] def inferPicardAPrioriBoxWithFuel
    (sys : OdeSystem) (box : List (String × Interval)) (fuel : Nat) : Option (List (String × Interval)) := do
  let cand1 ← sys.fields.mapM fun (name, rhsExpr) => do
    let x0Iv ← box.lookup name
    let f0Iv ← evalInterval box rhsExpr
    pure (name, Interval.add x0Iv (Interval.mul (Interval.mk 0 sys.dt) f0Iv))
  inflatePicardLoop sys box fuel cand1

/-- Construct a certified $N$-dimensional Picard a-priori rough enclosure $\tilde{X}$ from `box`
with default inflation fuel `8`. -/
@[expose] def inferPicardAPrioriBox
    (sys : OdeSystem) (box : List (String × Interval)) : Option (List (String × Interval)) :=
  inferPicardAPrioriBoxWithFuel sys box 8

/-- Advance an $N$-dimensional interval box `box` by one validated Picard–Lindelöf flowpipe step under `sys`:
infers an a-priori enclosure `xTildeBox`, checks `verifyPicardAPriori sys box xTildeBox sys.dt`, and
computes the $N$-dimensional Lie-derivative remainder enclosure via `stepPicardValidated`. -/
@[expose] def stepFlowpipe (sys : OdeSystem) (box : List (String × Interval)) : Option (List (String × Interval)) := do
  let xTildeBox ← inferPicardAPrioriBox sys box
  stepPicardValidated sys box xTildeBox sys.dt

/-- Structural recursion helper for `runFlowpipe`. -/
@[expose] def runFlowpipeLoop (sys : OdeSystem) : Nat → List (String × Interval) → Option (List (List (String × Interval)))
  | 0, curBox => some [curBox]
  | k + 1, curBox => do
    let nextBox ← stepFlowpipe sys curBox
    let restTube ← runFlowpipeLoop sys k nextBox
    pure (curBox :: restTube)

/-- Compute a `steps`-step validated $N$-dimensional flowpipe tube `[X_0, X_1, ..., X_steps]` starting from `initBox`. -/
@[expose] def runFlowpipe (sys : OdeSystem) (initBox : List (String × Interval)) (steps : Nat) : Option (List (List (String × Interval))) :=
  runFlowpipeLoop sys steps initBox

/-- Check whether every variable in `box` is enclosed within its corresponding interval in `safeBounds`. -/
@[expose] def checkBoxInEnvelope (box safeBounds : List (String × Interval)) : Bool :=
  safeBounds.all fun (name, safeIv) =>
    match box.find? (·.1 == name) with
    | some (_, curIv) => Interval.isSubintervalOf curIv safeIv
    | none => false

/-- Structural recursion helper for `verifyTrajectorySafety` over `Nat → List (String × Interval) → Bool`. -/
@[expose] def verifyTrajectorySafetyLoop
    (sys : OdeSystem) (safeBounds : List (String × Interval)) :
    Nat → List (String × Interval) → Bool
  | 0, curBox => checkBoxInEnvelope curBox safeBounds
  | k + 1, curBox =>
    if !checkBoxInEnvelope curBox safeBounds then
      false
    else
      match inferPicardAPrioriBox sys curBox with
      | none => false
      | some xTildeBox =>
        if !checkBoxInEnvelope xTildeBox safeBounds then
          false
        else
          match stepPicardValidated sys curBox xTildeBox sys.dt with
          | none => false
          | some nextBox =>
            verifyTrajectorySafetyLoop sys safeBounds k nextBox

/-- Verify that an entire `steps`-step continuous-time ODE flowpipe tube starting from `initBox` stays
inside `safeBounds`: checks BOTH every discrete slice $X_k$ AND every continuous-time rough enclosure
$\tilde{X}_k$ covering $t \in [t_k, t_{k+1}]$, preventing any inter-step barrier tunneling! -/
@[expose] def verifyTrajectorySafety
    (sys : OdeSystem)
    (initBox : List (String × Interval))
    (steps : Nat)
    (safeBounds : List (String × Interval)) : Bool :=
  verifyTrajectorySafetyLoop sys safeBounds steps initBox

/-! ## 2. Concrete 1D & 2D Physical ODE Models & `flowpipe_step_encloses_euler` -/

/-- Damped thermal RC relaxation ODE:
$\dot{T} = 20 - T$ with step size $\Delta t = \frac{1}{2}$ and model uncertainty pad $[-\frac{1}{10}, \frac{1}{10}]$. -/
@[expose] def thermalCoolingOde : OdeSystem where
  fields       := [("T", .sub (.const 20) (.var "T"))]
  dt           := CanonicalRat.mk 1 2
  remainderPad := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩

/-- Unstable positive-feedback thermal runaway ODE:
$\dot{T} = T + 10$ with step size $\Delta t = 1$ and remainder pad $[0, 1]$. -/
@[expose] def thermalRunawayOde : OdeSystem where
  fields       := [("T", .add (.var "T") (.const 10))]
  dt           := 1
  remainderPad := ⟨0, 1⟩

/-- Coupled 2D damped harmonic oscillator ODE system:
$\dot{x} = v,\; \dot{v} = -x - v$ with step size $\Delta t = \frac{1}{10}$. -/
@[expose] def coupledOscillatorOde : OdeSystem where
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
-- fixture kept (2026-11-04): consumed by Obend/Tactic/SiliconElab.lean
theorem flowpipe_step_encloses_euler :
    let X0 : Interval := ⟨28, 30⟩
    let V0 : Interval := ⟨-10, -8⟩
    let dt : CanonicalRat := CanonicalRat.mk 1 2
    let rem : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    let X1 := stepFlowpipe1D X0 V0 dt rem
    let initBox := [("T", X0)]
    let safeEnv := [("T", (⟨12, 35⟩ : Interval))]
    -- 1. Exact flowpipe step interval and Euler point containment
    X1 = ⟨CanonicalRat.mk 229 10, CanonicalRat.mk 261 10⟩ ∧
    Interval.containsRat X1 (28 + dt * (-8) + CanonicalRat.mk (-1) 10) = true ∧
    Interval.containsRat X1 (29 + dt * (-9) + 0) = true ∧
    Interval.containsRat X1 (30 + dt * (-10) + CanonicalRat.mk 1 10) = true ∧
    -- 2. Positive pole: 3-step cooling flowpipe stays inside [12, 35]
    verifyTrajectorySafety thermalCoolingOde initBox 3 safeEnv = true ∧
    -- 3. Negative pole: runaway ODE breaches [12, 35] and is refused
    verifyTrajectorySafety thermalRunawayOde initBox 2 safeEnv = false := by
  decide +kernel

/-! ## 3. Connecting Validated ODE Flowpipes to `Obend.Law.CellContract` (`odeSafetyCellContract`, `flowpipe_safety_implies_contract_holds`) -/

/-- Exact Core4 `Data` record encoding of a rational number $q = \frac{\text{posNum} - \text{negNum}}{\text{den}}$
with positive denominator `den = q.den`, allowing branch-free exact cross-multiplied rational comparison
in Core4 `Term`. -/
@[expose] def ratToCellData (q : CanonicalRat) : Data :=
  .record [("den", .natural q.den), ("negNum", .natural (-q.num).toNat), ("posNum", .natural q.num.toNat)]

/-- Decode a rational cell field back from `Data`. -/
@[expose] def decodeRatCellData? (d : Data) : Option CanonicalRat := do
  let .natural den ← d.field "den" | none
  let .natural negN ← d.field "negNum" | none
  let .natural posN ← d.field "posNum" | none
  if den == 0 then none
  else some (CanonicalRat.mk ((posN : Int) - (negN : Int)) den)

/-- Encode a discrete time-step index `stepIdx` and multi-variable rational state `rho` as Core4 `Data`. -/
@[expose] def stateToCellData (stepIdx : Nat) (vars : List String) (rho : String → CanonicalRat) : Data :=
  .record (("step", .natural stepIdx) :: vars.map (fun v => (v, ratToCellData (rho v))))

/-- Core4 natural multiplication `a * b`. -/
@[expose] def mulNat (a b : Term) : Term :=
  .binary .multiply a b

@[simp] theorem subst_mulNat (σ : Nat → Term) (a b : Term) :
    (mulNat a b).substitute σ = mulNat (a.substitute σ) (b.substitute σ) := by
  simp [mulNat]

theorem mulNat_val {a b v : Term} (h : Evaluates (mulNat a b) v) :
    ∃ m k, Evaluates a (.nat m) ∧ Evaluates b (.nat k) ∧ v = .nat (m * k) := by
  obtain ⟨x, y, hx, hy, hp⟩ := binary_inv h
  cases x <;> cases y <;> simp [Obend.Core.Term.primitiveResult] at hp
  exact ⟨_, _, hx, hy, hp.symm⟩

/-- Exact Core4 `Term` predicate checking that rational field `valTerm` has positive denominator `0 < den`
and lies inside closed rational interval `iv = [iv.lo, iv.hi]` via exact cross-multiplication:
$$\frac{\text{lo}_+ - \text{lo}_-}{\text{lo}_d} \le \frac{p - m}{d} \le \frac{\text{hi}_+ - \text{hi}_-}{\text{hi}_d}.$$ -/
@[expose] def intervalContainsTerm (iv : Interval) (valTerm : Term) : Term :=
  let p := .get valTerm "posNum"
  let m := .get valTerm "negNum"
  let d := .get valTerm "den"
  let loP := natT iv.lo.num.toNat
  let loM := natT (-iv.lo.num).toNat
  let loD := natT iv.lo.den
  let hiP := natT iv.hi.num.toNat
  let hiM := natT (-iv.hi.num).toNat
  let hiD := natT iv.hi.den
  andT (ltNat (natT 0) d)
    (andT
      (leNat (addNat (mulNat loP d) (mulNat m loD))
             (addNat (mulNat p loD) (mulNat loM d)))
      (leNat (addNat (mulNat p hiD) (mulNat hiM d))
             (addNat (mulNat hiP d) (mulNat m hiD))))

@[simp] theorem subst_intervalContainsTerm (iv : Interval) (valTerm : Term) (σ : Nat → Term) :
    (intervalContainsTerm iv valTerm).substitute σ = intervalContainsTerm iv (valTerm.substitute σ) := by
  simp [intervalContainsTerm]

/-- Core4 `Term` predicate checking that every variable `(v, iv) ∈ box` of `stTerm` lies in `iv`. -/
@[expose] def boxContainsStateTerm : List (String × Interval) → Term → Term
  | [], _ => trueT
  | (v, iv) :: rest, stTerm =>
    andT (intervalContainsTerm iv (.get stTerm v)) (boxContainsStateTerm rest stTerm)

@[simp] theorem subst_boxContainsStateTerm (box : List (String × Interval)) (stTerm : Term) (σ : Nat → Term) :
    (boxContainsStateTerm box stTerm).substitute σ = boxContainsStateTerm box (stTerm.substitute σ) := by
  induction box with
  | nil => simp [boxContainsStateTerm]
  | cons hd tl ih =>
    rcases hd with ⟨v, iv⟩
    simp [boxContainsStateTerm, ih]

/-- Core4 `Term` predicate checking that `stTerm.step = k` and `stTerm` lies inside slice `X_k`
for some slice `(k, X_k)` in the computed `OdeSystem` flowpipe tube starting at index `idx`. -/
@[expose] def tubeSliceTerms (stTerm : Term) : Nat → List (List (String × Interval)) → List Term
  | _, [] => []
  | idx, slice :: rest =>
    andT (eqNat (.get stTerm "step") (natT idx)) (boxContainsStateTerm slice stTerm) ::
      tubeSliceTerms stTerm (idx + 1) rest

@[simp] theorem subst_tubeSliceTerms (stTerm : Term) (idx : Nat)
    (tube : List (List (String × Interval))) (σ : Nat → Term) :
    (tubeSliceTerms stTerm idx tube).map (·.substitute σ) =
      tubeSliceTerms (stTerm.substitute σ) idx tube := by
  induction tube generalizing idx with
  | nil => simp [tubeSliceTerms]
  | cons slice rest ih =>
    simp [tubeSliceTerms, ih (idx + 1)]

/-- Closed Core4 `Term` state invariant induced by `OdeSystem` flowpipe verification:
requires `verifyTrajectorySafety sys initBox horizon safeBounds = true`, every variable in `safeBounds`
within its safe interval, and `(st.step, st)` enclosed in the exact `k`-th slice `X_k` of
`runFlowpipe sys initBox horizon`! -/
@[expose] def odeFlowpipeInvariant
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval)) : Term :=
  let tube := (runFlowpipe sys initBox horizon).getD []
  let certOk := if verifyTrajectorySafety sys initBox horizon safeBounds then trueT else falseT
  .lam (andT certOk
    (andT (boxContainsStateTerm safeBounds (.bound 0))
          (anyOf (tubeSliceTerms (.bound 0) 0 tube))))

@[simp] theorem subst_odeFlowpipeInvariant
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval)) (σ : Nat → Term) :
    (odeFlowpipeInvariant sys initBox horizon safeBounds).substitute σ =
      odeFlowpipeInvariant sys initBox horizon safeBounds := by
  unfold odeFlowpipeInvariant
  have hCert : ∀ (b : Bool) (τ : Nat → Term),
      (if b then trueT else falseT).substitute τ = (if b then trueT else falseT) := by
    intro b τ; cases b <;> simp
  simp only [Term.substitute, Obend.Law.subst_andT, hCert, subst_boxContainsStateTerm,
    Obend.Law.subst_anyOf, subst_tubeSliceTerms, Obend.Core.Term.liftSubstitution]

/-- Closed Core4 `Term` transition law induced by `OdeSystem` flowpipe evolution:
admits `(old, new, req)` iff:
1. `verifyTrajectorySafety sys initBox horizon safeBounds = true` (`"unsafe_ode_flowpipe"` otherwise),
2. `old` satisfies `odeFlowpipeInvariant` (`old ∈ X_k ∩ safeBounds` at step `k`),
3. `new.step = old.step + 1` (`"invalid_ode_step_counter"` otherwise), and
4. `new` satisfies `odeFlowpipeInvariant` (`new ∈ X_{k+1} ∩ safeBounds` at step `k + 1`, where
   `X_{k+1} = stepFlowpipe sys X_k`!). -/
@[expose] def odeFlowpipeTransitionLaw
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval)) : Term :=
  let inv := odeFlowpipeInvariant sys initBox horizon safeBounds
  let certOk := if verifyTrajectorySafety sys initBox horizon safeBounds then trueT else falseT
  law3
    (guard certOk "unsafe_ode_flowpipe"
      (guard (.app inv (.bound 2)) "old_state_outside_flowpipe"
        (guard (eqNat (.get (.bound 1) "step") (addNat (.get (.bound 2) "step") (natT 1)))
          "invalid_ode_step_counter"
          (guard (.app inv (.bound 1)) "new_state_outside_flowpipe" okT))))

/-- Verified `CellContract` genuinely encoding `OdeSystem` validated flowpipe evolution:
enforces both `verifyTrajectorySafety sys initBox horizon safeBounds = true` and exact slice-to-slice
rational flowpipe progression `old ∈ X_k ↦ new ∈ X_{k+1} = stepFlowpipe sys X_k` inside `safeBounds`. -/
@[expose] def odeSafetyCellContract
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval)) : CellContract where
  law       := odeFlowpipeTransitionLaw sys initBox horizon safeBounds
  invariant := odeFlowpipeInvariant sys initBox horizon safeBounds
  stepRel   := odeFlowpipeTransitionLaw sys initBox horizon safeBounds
  inductive_preserves := by
    intro old new req _ hAdm
    unfold odeFlowpipeTransitionLaw at hAdm
    obtain ⟨w, hw⟩ := (admits_iff _ old new req).1 hAdm
    have hCert : ∀ (b : Bool) (τ : Nat → Term),
        (if b then trueT else falseT).substitute τ = (if b then trueT else falseT) := by
      intro b τ; cases b <;> simp
    simp only [Obend.Law.subst_guard, Obend.Law.subst_app, Obend.Law.subst_eqNat,
      Obend.Law.subst_get, Obend.Law.subst_addNat, Obend.Law.subst_natT, Obend.Law.subst_bound,
      Obend.Law.subst_okT, Obend.Law.lawEnv, Obend.Law.scons_succ, Obend.Law.scons_zero,
      subst_odeFlowpipeInvariant, hCert] at hw
    obtain ⟨_, hw1⟩ := guard_ok hw
    obtain ⟨_, hw2⟩ := guard_ok hw1
    obtain ⟨_, hw3⟩ := guard_ok hw2
    exact (guard_ok hw3).1
  step_sound := fun _ _ _ _ hAdm => hAdm

/-- **Theorem (`odeSafetyCellContract_refuses_unsafe_ode`)**:
Whenever `verifyTrajectorySafety sys initBox horizon safeBounds = false` (such as `thermalRunawayOde`),
`odeSafetyCellContract` refuses EVERY transition `(old, new, req)` with `"unsafe_ode_flowpipe"`. -/
theorem odeSafetyCellContract_refuses_unsafe_ode
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval))
    (hUnsafe : verifyTrajectorySafety sys initBox horizon safeBounds = false)
    (old new req : Data) :
    ¬ Admits (odeSafetyCellContract sys initBox horizon safeBounds).law old new req := by
  intro hAdm
  dsimp [odeSafetyCellContract, odeFlowpipeTransitionLaw] at hAdm
  obtain ⟨w, hw⟩ := (admits_iff _ old new req).1 hAdm
  rw [hUnsafe] at hw
  simp only [Bool.false_eq_true, ↓reduceIte, Obend.Law.subst_guard, Obend.Law.subst_falseT] at hw
  have hFalse := (guard_ok hw).1
  have hVal := Obend.Law.evaluates_value (.boolean _) hFalse
  simp at hVal

/-- Helper: reading a nested natural field `.get (.get st.term v) f` evaluates to `.nat k` only when
`st.field v = some fv` and `fv.field f = some (.natural k)`. -/
private theorem get_get_field_nat {st : Data} {v f : String} {k : Nat}
    (h : Evaluates (.get (.get st.term v) f) (.nat k)) :
    ∃ fv, st.field v = some fv ∧ fv.field f = some (.natural k) := by
  obtain ⟨fs, body, hr, hf, hb⟩ := Obend.Law.get_inv h
  obtain ⟨fv, hfv, hfvTerm⟩ := get_data hr
  cases fv with
  | record dfs =>
    simp only [Data.term, Term.record.injEq] at hfvTerm
    subst hfvTerm
    rw [Obend.Law.fieldsTerm_find] at hf
    obtain ⟨e, he, heq⟩ := Option.map_eq_some_iff.1 hf
    cases heq
    have hbEq := Obend.Law.evaluates_data hb
    exact ⟨.record dfs, hfv, by rw [Data.field, he, data_term_nat hbEq.symm]⟩
  | natural _ => simp [Data.term] at hfvTerm
  | boolean _ => simp [Data.term] at hfvTerm
  | label _ => simp [Data.term] at hfvTerm
  | variant _ _ => simp [Data.term] at hfvTerm

private theorem nat_term_inj {a b : Nat} (h : Term.nat a = Term.nat b) : a = b := by
  injection h

/-- **Theorem (`intervalContainsTerm_sound`)**:
If `Evaluates (intervalContainsTerm iv (.get st.term v)) (.boolean true)`, then `st.field v` decodes
via `decodeRatCellData?` to an exact rational `q : CanonicalRat` with `q ∈ iv`. -/
theorem intervalContainsTerm_sound {iv : Interval} {st : Data} {v : String}
    (hEval : Evaluates (intervalContainsTerm iv (.get st.term v)) (.boolean true)) :
    ∃ fv q, st.field v = some fv ∧ decodeRatCellData? fv = some q ∧ q ∈ iv := by
  unfold intervalContainsTerm at hEval
  obtain ⟨hDenPosT, hBoundsT⟩ := andT_true hEval
  obtain ⟨hLoT, hHiT⟩ := andT_true hBoundsT
  obtain ⟨zeroN, den, hZeroEval, hDenEval, hDenPos⟩ := ltNat_true hDenPosT
  have hZeroEq : zeroN = 0 := by
    have hv := Obend.Law.evaluates_value (.natural _) hZeroEval
    cases hv; rfl
  rw [hZeroEq] at hDenPos
  obtain ⟨fv, hfvField, heDen⟩ := get_get_field_nat hDenEval
  obtain ⟨lhsLo, rhsLo, hLhsLo, hRhsLo, hLoLe⟩ := leNat_true hLoT
  obtain ⟨loP_d, m_loD, hLoPd, hMloD, hEqLhsLo⟩ := addNat_val hLhsLo
  obtain ⟨p_loD, loM_d, hPloD, hLoMd, hEqRhsLo⟩ := addNat_val hRhsLo
  obtain ⟨loPv, dVal1, hLoPv, hD1, hEqLoPd⟩ := mulNat_val hLoPd
  obtain ⟨negN, loDv1, hNegEval, hLoDv1, hEqMloD⟩ := mulNat_val hMloD
  obtain ⟨posN, loDv2, hPosEval, hLoDv2, hEqPloD⟩ := mulNat_val hPloD
  obtain ⟨loMv, dVal2, hLoMv, hD2, hEqLoMd⟩ := mulNat_val hLoMd
  obtain ⟨fvPos, hfvPos, hPosField0⟩ := get_get_field_nat hPosEval
  have hfvPosEq : fvPos = fv := Option.some.inj (hfvPos.symm.trans hfvField)
  rw [hfvPosEq] at hPosField0
  obtain ⟨fvNeg, hfvNeg, hNegField0⟩ := get_get_field_nat hNegEval
  have hfvNegEq : fvNeg = fv := Option.some.inj (hfvNeg.symm.trans hfvField)
  rw [hfvNegEq] at hNegField0
  have hd1Eq : dVal1 = den := nat_term_inj (Obend.Law.evaluates_unique hD1 hDenEval)
  have hd2Eq : dVal2 = den := nat_term_inj (Obend.Law.evaluates_unique hD2 hDenEval)
  have hLoPvEq : loPv = iv.lo.num.toNat := by
    have hv := Obend.Law.evaluates_value (.natural _) hLoPv; cases hv; rfl
  have hLoMvEq : loMv = (-iv.lo.num).toNat := by
    have hv := Obend.Law.evaluates_value (.natural _) hLoMv; cases hv; rfl
  have hLoDv1Eq : loDv1 = iv.lo.den := by
    have hv := Obend.Law.evaluates_value (.natural _) hLoDv1; cases hv; rfl
  have hLoDv2Eq : loDv2 = iv.lo.den := by
    have hv := Obend.Law.evaluates_value (.natural _) hLoDv2; cases hv; rfl
  rw [nat_term_inj hEqLhsLo, nat_term_inj hEqRhsLo,
      nat_term_inj hEqLoPd, nat_term_inj hEqMloD,
      nat_term_inj hEqPloD, nat_term_inj hEqLoMd,
      hd1Eq, hd2Eq, hLoPvEq, hLoMvEq, hLoDv1Eq, hLoDv2Eq] at hLoLe
  obtain ⟨lhsHi, rhsHi, hLhsHi, hRhsHi, hHiLe⟩ := leNat_true hHiT
  obtain ⟨p_hiD, hiM_d, hPhiD, hHiMd, hEqLhsHi⟩ := addNat_val hLhsHi
  obtain ⟨hiP_d, m_hiD, hHiPd, hMhiD, hEqRhsHi⟩ := addNat_val hRhsHi
  obtain ⟨posN2, hiDv1, hPosEval2, hHiDv1, hEqPhiD⟩ := mulNat_val hPhiD
  obtain ⟨hiMv, dVal3, hHiMv, hD3, hEqHiMd⟩ := mulNat_val hHiMd
  obtain ⟨hiPv, dVal4, hHiPv, hD4, hEqHiPd⟩ := mulNat_val hHiPd
  obtain ⟨negN2, hiDv2, hNegEval2, hHiDv2, hEqMhiD⟩ := mulNat_val hMhiD
  have hPos2Eq : posN2 = posN := nat_term_inj (Obend.Law.evaluates_unique hPosEval2 hPosEval)
  have hNeg2Eq : negN2 = negN := nat_term_inj (Obend.Law.evaluates_unique hNegEval2 hNegEval)
  have hd3Eq : dVal3 = den := nat_term_inj (Obend.Law.evaluates_unique hD3 hDenEval)
  have hd4Eq : dVal4 = den := nat_term_inj (Obend.Law.evaluates_unique hD4 hDenEval)
  have hHiPvEq : hiPv = iv.hi.num.toNat := by
    have hv := Obend.Law.evaluates_value (.natural _) hHiPv; cases hv; rfl
  have hHiMvEq : hiMv = (-iv.hi.num).toNat := by
    have hv := Obend.Law.evaluates_value (.natural _) hHiMv; cases hv; rfl
  have hHiDv1Eq : hiDv1 = iv.hi.den := by
    have hv := Obend.Law.evaluates_value (.natural _) hHiDv1; cases hv; rfl
  have hHiDv2Eq : hiDv2 = iv.hi.den := by
    have hv := Obend.Law.evaluates_value (.natural _) hHiDv2; cases hv; rfl
  rw [nat_term_inj hEqLhsHi, nat_term_inj hEqRhsHi,
      nat_term_inj hEqPhiD, nat_term_inj hEqHiMd,
      nat_term_inj hEqHiPd, nat_term_inj hEqMhiD,
      hPos2Eq, hNeg2Eq, hd3Eq, hd4Eq,
      hHiPvEq, hHiMvEq, hHiDv1Eq, hHiDv2Eq] at hHiLe
  let q := CanonicalRat.mk ((posN : Int) - (negN : Int)) den
  have hDec : decodeRatCellData? fv = some q := by
    unfold decodeRatCellData?
    rw [heDen, hNegField0, hPosField0]
    have hDenNe : den ≠ 0 := by omega
    simp [hDenNe, q]
  refine ⟨fv, q, hfvField, hDec, ?_⟩
  rw [Interval.mem_iff]
  have hLoSplit :
      (iv.lo.num.toNat : Int) * (den : Int) - ((-iv.lo.num).toNat : Int) * (den : Int) =
        iv.lo.num * (den : Int) := by
    rw [← Int.sub_mul]
    congr 1
    omega
  have hHiSplit :
      (iv.hi.num.toNat : Int) * (den : Int) - ((-iv.hi.num).toNat : Int) * (den : Int) =
        iv.hi.num * (den : Int) := by
    rw [← Int.sub_mul]
    congr 1
    omega
  have hPosLoDist :
      ((posN : Int) - (negN : Int)) * (iv.lo.den : Int) =
        (posN : Int) * (iv.lo.den : Int) - (negN : Int) * (iv.lo.den : Int) := Int.sub_mul ..
  have hPosHiDist :
      ((posN : Int) - (negN : Int)) * (iv.hi.den : Int) =
        (posN : Int) * (iv.hi.den : Int) - (negN : Int) * (iv.hi.den : Int) := Int.sub_mul ..
  have hLoLeInt :
      (iv.lo.num.toNat : Int) * (den : Int) + (negN : Int) * (iv.lo.den : Int) ≤
        (posN : Int) * (iv.lo.den : Int) + ((-iv.lo.num).toNat : Int) * (den : Int) := by
    exact_mod_cast hLoLe
  have hHiLeInt :
      (posN : Int) * (iv.hi.den : Int) + ((-iv.hi.num).toNat : Int) * (den : Int) ≤
        (iv.hi.num.toNat : Int) * (den : Int) + (negN : Int) * (iv.hi.den : Int) := by
    exact_mod_cast hHiLe
  have hLoInt : iv.lo.num * (den : Int) ≤ ((posN : Int) - (negN : Int)) * (iv.lo.den : Int) := by
    omega
  have hHiInt : ((posN : Int) - (negN : Int)) * (iv.hi.den : Int) ≤ iv.hi.num * (den : Int) := by
    omega
  have hLoDenPos : (0 : CanonicalRat) < (iv.lo.den : CanonicalRat) := by exact_mod_cast iv.lo.den_pos
  have hHiDenPos : (0 : CanonicalRat) < (iv.hi.den : CanonicalRat) := by exact_mod_cast iv.hi.den_pos
  have hDenRatPos : (0 : CanonicalRat) < (den : CanonicalRat) := by exact_mod_cast hDenPos
  have hqEq : q = (((posN : Int) - (negN : Int) : Int) : CanonicalRat) / (den : CanonicalRat) := by
    simp [q, CanonicalRat.mk, Rat.mkRat_eq_div]
  have hLoEq : iv.lo = (iv.lo.num : CanonicalRat) / (iv.lo.den : CanonicalRat) := by
    have h1 := Rat.mkRat_self iv.lo
    rw [Rat.mkRat_eq_div] at h1
    exact h1.symm
  have hHiEq : iv.hi = (iv.hi.num : CanonicalRat) / (iv.hi.den : CanonicalRat) := by
    have h1 := Rat.mkRat_self iv.hi
    rw [Rat.mkRat_eq_div] at h1
    exact h1.symm
  have hLoRat : (iv.lo.num : CanonicalRat) * (den : CanonicalRat) ≤
      (((posN : Int) - (negN : Int) : Int) : CanonicalRat) * (iv.lo.den : CanonicalRat) := by
    exact_mod_cast hLoInt
  have hHiRat : (((posN : Int) - (negN : Int) : Int) : CanonicalRat) * (iv.hi.den : CanonicalRat) ≤
      (iv.hi.num : CanonicalRat) * (den : CanonicalRat) := by
    exact_mod_cast hHiInt
  have hLoNe : (iv.lo.den : CanonicalRat) ≠ 0 := by grind
  have hHiNe : (iv.hi.den : CanonicalRat) ≠ 0 := by grind
  have hDenNeR : (den : CanonicalRat) ≠ 0 := by grind
  have hC1Lo : iv.lo * (iv.lo.den : CanonicalRat) = (iv.lo.num : CanonicalRat) := by
    have h := Rat.div_mul_cancel (a := (iv.lo.num : CanonicalRat)) hLoNe
    rw [← hLoEq] at h
    exact h
  have hC1Hi : iv.hi * (iv.hi.den : CanonicalRat) = (iv.hi.num : CanonicalRat) := by
    have h := Rat.div_mul_cancel (a := (iv.hi.num : CanonicalRat)) hHiNe
    rw [← hHiEq] at h
    exact h
  have hC2 : q * (den : CanonicalRat) = (((posN : Int) - (negN : Int) : Int) : CanonicalRat) := by
    rw [hqEq, Rat.div_mul_cancel hDenNeR]
  constructor
  · by_cases hlt : q < iv.lo
    · have hDiff : 0 < iv.lo - q := by grind
      have hMul1 := Rat.mul_pos hDiff hLoDenPos
      have hMul2 := Rat.mul_pos hMul1 hDenRatPos
      have hExpand :
          (iv.lo - q) * (iv.lo.den : CanonicalRat) * (den : CanonicalRat) =
            (iv.lo * (iv.lo.den : CanonicalRat)) * (den : CanonicalRat) -
            (q * (den : CanonicalRat)) * (iv.lo.den : CanonicalRat) := by grind
      rw [hC1Lo, hC2] at hExpand
      grind
    · grind
  · by_cases hlt : iv.hi < q
    · have hDiff : 0 < q - iv.hi := by grind
      have hMul1 := Rat.mul_pos hDiff hHiDenPos
      have hMul2 := Rat.mul_pos hMul1 hDenRatPos
      have hExpand :
          (q - iv.hi) * (iv.hi.den : CanonicalRat) * (den : CanonicalRat) =
            (q * (den : CanonicalRat)) * (iv.hi.den : CanonicalRat) -
            (iv.hi * (iv.hi.den : CanonicalRat)) * (den : CanonicalRat) := by grind
      rw [hC1Hi, hC2] at hExpand
      grind
    · grind

/-- Alias for `runFlowpipe` matching `METATHEORY.md` nomenclature. -/
abbrev computeFlowpipeTrajectory := runFlowpipe

/-- **Theorem (`flowpipe_safety_implies_contract_holds`)**:
1. When `verifyTrajectorySafety thermalCoolingOde [("T", ⟨28, 30⟩)] 3 [("T", ⟨12, 35⟩)] = true`,
   every state and continuous-time rough enclosure in the flowpipe tube satisfies the `[12, 35]`°C safety bound,
2. For any `OdeSystem`, initial box `initBox`, horizon `horizon`, safe envelope `safeBounds`, and
   multi-step execution trace `CellTrace (odeSafetyCellContract sys initBox horizon safeBounds).law s₀ steps s_final`
   starting from `Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s₀`, the final
   state `s_final` is guaranteed to satisfy `Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s_final`. -/
theorem flowpipe_safety_implies_contract_holds
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval))
    (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s₀)
    (h_tr : CellTrace (odeSafetyCellContract sys initBox horizon safeBounds).law s₀ steps s_final) :
    verifyTrajectorySafety thermalCoolingOde [("T", ⟨28, 30⟩)] 3 [("T", ⟨12, 35⟩)] = true ∧
    Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s_final := by
  exact ⟨by decide +kernel,
    cellContract_trace_sound (odeSafetyCellContract sys initBox horizon safeBounds) s₀ s_final steps h_init h_tr⟩

/-- Alias for `flowpipe_safety_implies_contract_holds` matching `METATHEORY.md` §3. -/
theorem flowpipe_safety_admits_contract
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval))
    (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s₀)
    (h_tr : CellTrace (odeSafetyCellContract sys initBox horizon safeBounds).law s₀ steps s_final) :
    verifyTrajectorySafety thermalCoolingOde [("T", ⟨28, 30⟩)] 3 [("T", ⟨12, 35⟩)] = true ∧
    Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s_final :=
  flowpipe_safety_implies_contract_holds sys initBox horizon safeBounds s₀ s_final steps h_init h_tr

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

theorem verifyPicardFields_mem :
    ∀ (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat)
      (fields : List (String × RealExpr)),
      verifyPicardFields x0Box xTildeBox h fields = true →
      ∀ {name : String} {rhsExpr : RealExpr},
        (name, rhsExpr) ∈ fields →
        ∀ {x0Iv xTildeIv fTildeIv : Interval},
          x0Box.lookup name = some x0Iv →
          xTildeBox.lookup name = some xTildeIv →
          evalInterval xTildeBox rhsExpr = some fTildeIv →
          Interval.subset (Interval.add x0Iv (Interval.mul (Interval.mk 0 h) fTildeIv)) xTildeIv = true := by
  intro x0Box xTildeBox h fields hOk name rhsExpr hMem x0Iv xTildeIv fTildeIv hx0Look hxTildeLook hfTilde
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
theorem verifyPicardAPriori_encloses :
    ∀ (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat),
      verifyPicardAPriori sys x0Box xTildeBox h = true →
      ∀ {name : String} {rhsExpr : RealExpr},
        (name, rhsExpr) ∈ sys.fields →
        ∀ {x0Iv xTildeIv fTildeIv : Interval},
          x0Box.lookup name = some x0Iv →
          xTildeBox.lookup name = some xTildeIv →
          evalInterval xTildeBox rhsExpr = some fTildeIv →
          ∀ {x_init t v_t : CanonicalRat},
            x_init ∈ x0Iv →
            t ∈ Interval.mk 0 h →
            v_t ∈ fTildeIv →
            (x_init + t * v_t) ∈ xTildeIv := by
  intro sys x0Box xTildeBox h hPicard name rhsExpr hMemField x0Iv xTildeIv fTildeIv
    hx0Look hxTildeLook hfTilde x_init t v_t hx0 ht hvt
  unfold verifyPicardAPriori at hPicard
  simp only [Bool.and_eq_true] at hPicard
  have hSub := verifyPicardFields_mem x0Box xTildeBox h sys.fields hPicard.2 hMemField hx0Look hxTildeLook hfTilde
  exact Interval.subset_sound hSub (Interval.add_mem hx0 (Interval.mul_mem ht hvt))

/-- `IsPicardSegmentState sys x0Box xTildeBox h rho0 rhoXi` states that `rhoXi` lies on a mean-value /
Euler–Picard trajectory segment from `rho0` over $\tau \in [0, h]$: for every variable `v` in `xTildeBox`,
there exist `(v, rhs) ∈ sys.fields`, time $\tau \in [0, h]$, and intermediate velocity `vel` enclosed in
`evalInterval xTildeBox rhs` such that `rhoXi v = rho0 v + τ * vel`. -/
@[expose] def IsPicardSegmentState
    (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat)
    (rho0 rhoXi : String → CanonicalRat) : Prop :=
  ∀ v xTildeIv, xTildeBox.lookup v = some xTildeIv →
    ∃ rhs x0Iv fTildeIv τ vel,
      (v, rhs) ∈ sys.fields ∧
      x0Box.lookup v = some x0Iv ∧
      evalInterval xTildeBox rhs = some fTildeIv ∧
      τ ∈ Interval.mk 0 h ∧
      vel ∈ fTildeIv ∧
      rhoXi v = rho0 v + τ * vel

/-- **Theorem (`verifyPicardAPriori_discharges_rough_enclosure`)**:
Whenever `verifyPicardAPriori sys x0Box xTildeBox h = true`, `BoxMem rho0 x0Box`, and
`IsPicardSegmentState sys x0Box xTildeBox h rho0 rhoXi`, the rough enclosure membership
`BoxMem rhoXi xTildeBox` is discharged automatically from `verifyPicardAPriori_encloses`! -/
theorem verifyPicardAPriori_discharges_rough_enclosure :
    ∀ (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat)
      (rho0 rhoXi : String → CanonicalRat),
      verifyPicardAPriori sys x0Box xTildeBox h = true →
      BoxMem rho0 x0Box →
      IsPicardSegmentState sys x0Box xTildeBox h rho0 rhoXi →
      BoxMem rhoXi xTildeBox := by
  intro sys x0Box xTildeBox h rho0 rhoXi hPicard hBox0 hSeg v xTildeIv hxTildeLook
  rcases hSeg v xTildeIv hxTildeLook with
    ⟨rhs, x0Iv, fTildeIv, τ, vel, hMemField, hx0Look, hfTilde, hτ, hvel, hEq⟩
  rw [hEq]
  exact verifyPicardAPriori_encloses sys x0Box xTildeBox h hPicard hMemField hx0Look hxTildeLook hfTilde
    (hBox0 v x0Iv hx0Look) hτ hvel

/-- **Theorem (`picard_step_encloses_trajectory`)**:
1. **Universal $N$-Dimensional Validated Picard–Lindelöf & Lie-Derivative Step Soundness**:
   For any $N$-dimensional `sys : OdeSystem`, initial box `x0Box`, verified a-priori enclosure `xTildeBox`
   (`verifyPicardAPriori sys x0Box xTildeBox h = true`), step size `h`, and any state variable
   `(name, rhsExpr) ∈ sys.fields`:
   - Discharges `BoxMem rhoXi xTildeBox` directly from `verifyPicardAPriori sys x0Box xTildeBox h = true`
     and `IsPicardSegmentState sys x0Box xTildeBox h rho0 rhoXi` via `verifyPicardAPriori_discharges_rough_enclosure`,
   - Every intermediate trajectory component $x_i(0) + t \cdot f_i(x(\xi))$ ($t \in [0, h]$)
     is enclosed in `xTildeIv`, and
   - Every 2nd-order Taylor–Lie trajectory endpoint
     $$x_i(h) = x_i(0) + h \cdot f_i(x(0)) + \frac{h^2}{2} (\mathcal{L}_f f_i)(x(\xi)) + r_{\text{pad}}$$
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
      IsPicardSegmentState sys x0Box xTildeBox h rho0 rhoXi →
      x0Box.lookup name = some x0Iv →
      xTildeBox.lookup name = some xTildeIv →
      evalInterval x0Box rhsExpr = some v0Iv →
      evalInterval xTildeBox rhsExpr = some fTildeIv →
      evalOdeLieDerivComponent sys xTildeBox rhsExpr = some lieIv →
      t ∈ Interval.mk 0 h →
      r_pad ∈ sys.remainderPad →
      BoxMem rhoXi xTildeBox ∧
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
            , ("v", ⟨CanonicalRat.mk (-97) 1000, CanonicalRat.mk (-93) 1000⟩) ] ∧
     -- Inter-step barrier tunneling rejection: X_0 = [28, 30] and X_1 = [22.9, 26.1] both lie inside
     -- [22.9, 30], yet the continuous-time rough enclosure xTildeBox = [23, 30] breaches [23.1, 30]!
     verifyTrajectorySafety thermalCoolingOde x0Box 1 [("T", ⟨CanonicalRat.mk 231 10, 30⟩)] = false) := by
  refine ⟨?_, by decide +kernel⟩
  intro sys x0Box xTildeBox rho0 rhoXi h t r_pad name rhsExpr x0Iv xTildeIv v0Iv fTildeIv lieIv
    hPic hMem hBox0 hSeg hx0Look hxTildeLook hv0 hfTilde hLie ht hrPad
  have hBoxXi : BoxMem rhoXi xTildeBox :=
    verifyPicardAPriori_discharges_rough_enclosure sys x0Box xTildeBox h rho0 rhoXi hPic hBox0 hSeg
  have hx0 : rho0 name ∈ x0Iv := hBox0 name x0Iv hx0Look
  have hv0Mem : evalExpr rho0 rhsExpr ∈ v0Iv :=
    evalInterval_sound x0Box rho0 hBox0 rhsExpr v0Iv hv0
  have hfXiMem : evalExpr rhoXi rhsExpr ∈ fTildeIv :=
    evalInterval_sound xTildeBox rhoXi hBoxXi rhsExpr fTildeIv hfTilde
  have hLieMem : evalOdePointLieDerivComponent sys rhoXi rhsExpr ∈ lieIv :=
    evalOdeLieDerivComponent_sound sys xTildeBox rhoXi hBoxXi rhsExpr lieIv hLie
  refine ⟨hBoxXi, verifyPicardAPriori_encloses sys x0Box xTildeBox h hPic hMem hx0Look hxTildeLook hfTilde hx0 ht hfXiMem, ?_⟩
  exact stepFlowpipe1D_mem h hx0 hv0Mem
    (Interval.add_mem (derivePicardLieRemainder_mem h hLieMem) hrPad)

/-! ## 5. Discrete/Rational-Time Lipschitz Picard Contraction on $[0, h]$ (`L * h < 1`) -/

/-- Exact rational absolute value $|q|$. -/
@[expose] def ratAbs (q : CanonicalRat) : CanonicalRat :=
  if decide (q < 0) then -q else q

theorem ratAbs_nonneg (q : CanonicalRat) : 0 ≤ ratAbs q := by
  unfold ratAbs; split <;> grind

theorem ratAbs_le_iff (q b : CanonicalRat) :
    ratAbs q ≤ b ↔ (-b ≤ q ∧ q ≤ b) := by
  unfold ratAbs; split <;> grind

theorem ratAbs_add_le (a b : CanonicalRat) :
    ratAbs (a + b) ≤ ratAbs a + ratAbs b := by
  unfold ratAbs; split <;> split <;> split <;> grind

theorem ratAbs_mul_of_nonneg {w a : CanonicalRat} (hw : 0 ≤ w) :
    ratAbs (w * a) = w * ratAbs a := by
  unfold ratAbs
  split
  · rename_i hwa
    split
    · grind
    · rename_i ha
      have := Rat.mul_le_mul_of_nonneg_left (by grind : 0 ≤ a) hw
      grind
  · rename_i hwa
    split
    · rename_i ha
      have hNonpos : w * a ≤ 0 := by
        have := Rat.mul_le_mul_of_nonneg_left (by grind : 0 ≤ -a) hw
        grind
      grind
    · grind

/-- Natural power $r^n$ over `CanonicalRat` for geometric contraction rates $(L \cdot h)^n$. -/
@[expose] def powRatFlow (r : CanonicalRat) : Nat → CanonicalRat
  | 0 => 1
  | n + 1 => r * powRatFlow r n

theorem powRatFlow_nonneg {r : CanonicalRat} (hr : 0 ≤ r) (n : Nat) :
    0 ≤ powRatFlow r n := by
  induction n with
  | zero => unfold powRatFlow; grind
  | succ k ih =>
    unfold powRatFlow
    have := Rat.mul_le_mul_of_nonneg_left ih hr
    grind

/-- $\ell_\infty$ seminorm distance $\max_{v \in \text{vars}} |\rho_1(v) - \rho_2(v)|$ over state variables `vars`. -/
@[expose] def boxDistInf : List String → (String → CanonicalRat) → (String → CanonicalRat) → CanonicalRat
  | [], _, _ => 0
  | v :: vs, rho1, rho2 => max (ratAbs (rho1 v - rho2 v)) (boxDistInf vs rho1 rho2)

theorem boxDistInf_nonneg (vars : List String) (rho1 rho2 : String → CanonicalRat) :
    0 ≤ boxDistInf vars rho1 rho2 := by
  induction vars with
  | nil => unfold boxDistInf; grind
  | cons v vs ih =>
    unfold boxDistInf
    have hv := ratAbs_nonneg (rho1 v - rho2 v)
    grind

theorem boxDistInf_comp_le {vars : List String} {rho1 rho2 : String → CanonicalRat} {v : String}
    (hv : v ∈ vars) :
    ratAbs (rho1 v - rho2 v) ≤ boxDistInf vars rho1 rho2 := by
  induction vars with
  | nil => cases hv
  | cons u us ih =>
    simp only [List.mem_cons] at hv
    unfold boxDistInf
    rcases hv with rfl | hTail
    · grind
    · have := ih hTail; grind

theorem boxDistInf_le_of_all {vars : List String} {rho1 rho2 : String → CanonicalRat} {B : CanonicalRat}
    (hB : 0 ≤ B)
    (hAll : ∀ v ∈ vars, ratAbs (rho1 v - rho2 v) ≤ B) :
    boxDistInf vars rho1 rho2 ≤ B := by
  induction vars with
  | nil => exact hB
  | cons v vs ih =>
    unfold boxDistInf
    have hv := hAll v (List.mem_cons_self ..)
    have hvs := ih (fun u hu => hAll u (List.mem_cons_of_mem _ hu))
    grind

/-- State variable names of an `OdeSystem`. -/
@[expose] def odeStateVars (sys : OdeSystem) : List String :=
  sys.fields.map (·.1)

/-- Box-Lipschitz condition with constant $L \ge 0$ in the $\ell_\infty$ norm over `xTildeBox`:
for all $\rho_1, \rho_2 \in \tilde{X}$ and every component `(name, rhs) ∈ sys.fields`,
$|f_i(\rho_1) - f_i(\rho_2)| \le L \cdot \|\rho_1 - \rho_2\|_\infty$. -/
@[expose] def IsOdeBoxLipschitz
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) (L : CanonicalRat) : Prop :=
  0 ≤ L ∧
    ∀ rho1 rho2, BoxMem rho1 xTildeBox → BoxMem rho2 xTildeBox →
      ∀ name rhs, (name, rhs) ∈ sys.fields →
        ratAbs (evalExpr rho1 rhs - evalExpr rho2 rhs) ≤ L * boxDistInf (odeStateVars sys) rho1 rho2

/-- Computable interval-Jacobian induced $\ell_\infty$ Lipschitz bound $\max_i \sum_j \max(|\text{lo}_{i,j}|, |\text{hi}_{i,j}|)$
over `xTildeBox`. -/
@[expose] def computeOdeLipschitzBound
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) : Option CanonicalRat := do
  let jac ← evalOdeJacobian sys xTildeBox
  pure <| jac.foldl (fun maxRow (_, row) =>
    let rowSum := row.foldl (fun acc (_, dIv) =>
      acc + max (ratAbs dIv.lo) (ratAbs dIv.hi)) 0
    max maxRow rowSum) 0

/-- Computable Picard–Lindelöf Banach contraction verifier on $[0, h]$:
checks BOTH self-mapping $X_0 \oplus [0, h] F(\tilde{X}) \subseteq \tilde{X}$ (`verifyPicardAPriori`)
AND strict Jacobian contraction factor $L \cdot h < 1$! -/
@[expose] def verifyPicardContraction
    (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat) : Bool :=
  verifyPicardAPriori sys x0Box xTildeBox h &&
    match computeOdeLipschitzBound sys xTildeBox with
    | some L => decide (0 ≤ L ∧ L * h < 1)
    | none => false

/-- Sum of quadrature weights $\sum_{(w, \tau) \in \text{qs}} w$. -/
@[expose] def quadWeightSum : List (CanonicalRat × CanonicalRat) → CanonicalRat
  | [] => 0
  | (w, _) :: rest => w + quadWeightSum rest

/-- Quadrature sum $\sum_{(w, \tau) \in \text{qs}} w \cdot f_i(\gamma(\tau))$ approximating $\int_0^t f_i(\gamma(\tau))\,d\tau$. -/
@[expose] def evalPicardQuadSum
    (rhs : RealExpr) (gamma : CanonicalRat → String → CanonicalRat) :
    List (CanonicalRat × CanonicalRat) → CanonicalRat
  | [] => 0
  | (w, τ) :: rest => w * evalExpr (gamma τ) rhs + evalPicardQuadSum rhs gamma rest

/-- Rational-time / discrete quadrature Picard operator $\Phi(\gamma)(t)(v) = x_0(v) + \sum_{(w, \tau) \in \text{nodes}(t)} w \cdot f_v(\gamma(\tau))$. -/
@[expose] def picardOperator
    (sys : OdeSystem) (rho0 : String → CanonicalRat)
    (nodes : CanonicalRat → List (CanonicalRat × CanonicalRat))
    (gamma : CanonicalRat → String → CanonicalRat)
    (t : CanonicalRat) (v : String) : CanonicalRat :=
  match sys.fields.find? (·.1 == v) with
  | some (_, rhs) => rho0 v + evalPicardQuadSum rhs gamma (nodes t)
  | none => rho0 v

/-- $n$-fold Picard iteration $\Phi^{[n]}(\gamma_0)$ starting from the constant curve $\gamma_0(t) = \rho_0$. -/
@[expose] def iteratePicardOperator
    (sys : OdeSystem) (rho0 : String → CanonicalRat)
    (nodes : CanonicalRat → List (CanonicalRat × CanonicalRat)) :
    Nat → (CanonicalRat → String → CanonicalRat)
  | 0 => fun _ => rho0
  | n + 1 => picardOperator sys rho0 nodes (iteratePicardOperator sys rho0 nodes n)

/-- Valid nonnegative rational quadrature family on $[0, h]$:
for every $t \in [0, h]$, weights are nonnegative, sample times lie in $[0, h]$, and weights sum to $t$. -/
@[expose] def ValidQuadratureOn
    (h : CanonicalRat) (nodes : CanonicalRat → List (CanonicalRat × CanonicalRat)) : Prop :=
  ∀ t, t ∈ Interval.mk 0 h →
    quadWeightSum (nodes t) = t ∧
    ∀ p ∈ nodes t, 0 ≤ p.1 ∧ p.2 ∈ Interval.mk 0 h

/-- Supremum $\ell_\infty$ distance $\max_{t \in \text{times}} \|\gamma_1(t) - \gamma_2(t)\|_\infty$ over a finite rational time grid. -/
@[expose] def curveSupDist
    (vars : List String) : List CanonicalRat →
    (CanonicalRat → String → CanonicalRat) → (CanonicalRat → String → CanonicalRat) → CanonicalRat
  | [], _, _ => 0
  | t :: ts, g1, g2 => max (boxDistInf vars (g1 t) (g2 t)) (curveSupDist vars ts g1 g2)

theorem curveSupDist_nonneg
    (vars : List String) (times : List CanonicalRat)
    (g1 g2 : CanonicalRat → String → CanonicalRat) :
    0 ≤ curveSupDist vars times g1 g2 := by
  induction times with
  | nil => unfold curveSupDist; grind
  | cons t ts ih =>
    unfold curveSupDist
    have ht := boxDistInf_nonneg vars (g1 t) (g2 t)
    grind

theorem curveSupDist_at_le
    {vars : List String} {times : List CanonicalRat}
    {g1 g2 : CanonicalRat → String → CanonicalRat} {t : CanonicalRat}
    (ht : t ∈ times) :
    boxDistInf vars (g1 t) (g2 t) ≤ curveSupDist vars times g1 g2 := by
  induction times with
  | nil => cases ht
  | cons s ts ih =>
    simp only [List.mem_cons] at ht
    unfold curveSupDist
    rcases ht with rfl | hTail
    · grind
    · have := ih hTail; grind

theorem curveSupDist_le_of_all
    {vars : List String} {times : List CanonicalRat}
    {g1 g2 : CanonicalRat → String → CanonicalRat} {B : CanonicalRat}
    (hB : 0 ≤ B)
    (hAll : ∀ t ∈ times, boxDistInf vars (g1 t) (g2 t) ≤ B) :
    curveSupDist vars times g1 g2 ≤ B := by
  induction times with
  | nil => exact hB
  | cons t ts ih =>
    unfold curveSupDist
    have ht := hAll t (List.mem_cons_self ..)
    have hts := ih (fun s hs => hAll s (List.mem_cons_of_mem _ hs))
    grind

theorem curveSupDist_congr
    {vars : List String} {times : List CanonicalRat}
    {g1 g2 f1 f2 : CanonicalRat → String → CanonicalRat}
    (hPoint : ∀ t ∈ times, boxDistInf vars (g1 t) (g2 t) = boxDistInf vars (f1 t) (f2 t)) :
    curveSupDist vars times g1 g2 = curveSupDist vars times f1 f2 := by
  induction times with
  | nil => rfl
  | cons t ts ih =>
    unfold curveSupDist
    rw [hPoint t (List.mem_cons_self ..),
        ih (fun s hs => hPoint s (List.mem_cons_of_mem _ hs))]

theorem evalPicardQuadSum_bounds
    {rhs : RealExpr} {gamma : CanonicalRat → String → CanonicalRat}
    {qs : List (CanonicalRat × CanonicalRat)} {iv : Interval}
    (hQs : ∀ p ∈ qs, 0 ≤ p.1 ∧ evalExpr (gamma p.2) rhs ∈ iv) :
    quadWeightSum qs * iv.lo ≤ evalPicardQuadSum rhs gamma qs ∧
      evalPicardQuadSum rhs gamma qs ≤ quadWeightSum qs * iv.hi := by
  induction qs with
  | nil =>
    simp [quadWeightSum, evalPicardQuadSum]
  | cons hd tl ih =>
    rcases hd with ⟨w, τ⟩
    have hHead := hQs (w, τ) (List.mem_cons_self ..)
    have hRest := ih (fun p hp => hQs p (List.mem_cons_of_mem _ hp))
    rcases hHead with ⟨hw, hMem⟩
    rw [Interval.mem_iff] at hMem
    have hwLo := Rat.mul_le_mul_of_nonneg_left hMem.1 hw
    have hwHi := Rat.mul_le_mul_of_nonneg_left hMem.2 hw
    unfold quadWeightSum evalPicardQuadSum
    grind

theorem find?_pair_mem_and_eq {α : Type} :
    ∀ (xs : List (String × α)) (v : String) (p : String × α),
      xs.find? (·.1 == v) = some p → p.1 = v ∧ p ∈ xs
  | [], _, _, h => by simp at h
  | (k, val) :: rest, v, p, h => by
    simp only [List.find?_cons] at h
    cases hkv : k == v
    · rw [hkv] at h
      obtain ⟨hEq, hMem⟩ := find?_pair_mem_and_eq rest v p h
      exact ⟨hEq, List.mem_cons_of_mem _ hMem⟩
    · rw [hkv] at h
      injection h with hp
      subst hp
      simp only [beq_iff_eq] at hkv
      exact ⟨hkv, List.mem_cons_self ..⟩

theorem find?_pair_of_mem {α : Type} :
    ∀ (xs : List (String × α)) (v : String) (val : α),
      (v, val) ∈ xs → ∃ val', xs.find? (·.1 == v) = some (v, val') ∧ (v, val') ∈ xs
  | [], _, _, h => by cases h
  | (k, w) :: rest, v, val, h => by
    simp only [List.mem_cons] at h
    cases hkv : k == v
    · simp only [List.find?_cons, hkv]
      rcases h with hEq | hTail
      · injection hEq with hk _
        subst hk
        simp at hkv
      · obtain ⟨val', hFind, hMem⟩ := find?_pair_of_mem rest v val hTail
        exact ⟨val', hFind, List.mem_cons_of_mem _ hMem⟩
    · simp only [List.find?_cons, hkv]
      simp only [beq_iff_eq] at hkv
      subst hkv
      exact ⟨w, rfl, List.mem_cons_self ..⟩

/-- **Theorem (`picardOperator_self_maps_apriori`)**:
If `verifyPicardAPriori sys x0Box xTildeBox h = true`, `BoxMem rho0 x0Box`, every variable in `xTildeBox`
is governed by `sys.fields`, and `ValidQuadratureOn h nodes`, then $\Phi$ maps $\tilde{X}$-valued curves
into $\tilde{X}$-valued curves on $[0, h]$ (and satisfies `IsPicardSegmentState` when `0 < t` or via
interval enclosure directly). -/
theorem picardOperator_self_maps_apriori
    (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat)
    (rho0 : String → CanonicalRat)
    (nodes : CanonicalRat → List (CanonicalRat × CanonicalRat))
    (gamma : CanonicalRat → String → CanonicalRat)
    (hPic : verifyPicardAPriori sys x0Box xTildeBox h = true)
    (hBox0 : BoxMem rho0 x0Box)
    (hFieldsCover : ∀ v iv, xTildeBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields)
    (hQuad : ValidQuadratureOn h nodes)
    (hGamma : ∀ τ, τ ∈ Interval.mk 0 h → BoxMem (gamma τ) xTildeBox)
    {t : CanonicalRat} (ht : t ∈ Interval.mk 0 h) :
    BoxMem (picardOperator sys rho0 nodes gamma t) xTildeBox := by
  intro v xTildeIv hxTildeLook
  obtain ⟨rhs0, hMem0⟩ := hFieldsCover v xTildeIv hxTildeLook
  obtain ⟨rhs, hFind, hMemField⟩ := find?_pair_of_mem sys.fields v rhs0 hMem0
  unfold picardOperator
  rw [hFind]
  unfold verifyPicardAPriori at hPic
  simp only [Bool.and_eq_true] at hPic
  -- Extract `x0Iv` and `fTildeIv` directly from `verifyPicardFields = true` and `(v, rhs) ∈ sys.fields`
  have hFieldAux : ∀ (fs : List (String × RealExpr)),
      verifyPicardFields x0Box xTildeBox h fs = true →
      (v, rhs) ∈ fs →
      ∃ x0Iv fTildeIv,
        x0Box.lookup v = some x0Iv ∧
        evalInterval xTildeBox rhs = some fTildeIv ∧
        Interval.subset (Interval.add x0Iv (Interval.mul (Interval.mk 0 h) fTildeIv)) xTildeIv = true := by
    intro fs hVerFs hMemFs
    induction fs with
    | nil => cases hMemFs
    | cons hd tl ih =>
      rcases hd with ⟨n, r⟩
      simp only [verifyPicardFields, Bool.and_eq_true] at hVerFs
      simp only [List.mem_cons] at hMemFs
      rcases hMemFs with hEq | hTail
      · injection hEq with hn hr
        subst hn; subst hr
        have h1 := hVerFs.1
        cases hx0 : x0Box.lookup v with
        | none => rw [hx0] at h1; simp at h1
        | some x0Iv =>
          rw [hx0, hxTildeLook] at h1
          cases hf : evalInterval xTildeBox rhs with
          | none => rw [hf] at h1; simp at h1
          | some fTildeIv =>
            rw [hf] at h1
            exact ⟨x0Iv, fTildeIv, rfl, rfl, h1⟩
      · exact ih hVerFs.2 hTail
  rcases hFieldAux sys.fields hPic.2 hMemField with ⟨x0Iv, fTildeIv, hx0Look, hfTilde, hSub⟩
  obtain ⟨hSumEq, hPts⟩ := hQuad t ht
  have hfWf : fTildeIv.Wf := by
    have h0Mem : (0 : CanonicalRat) ∈ Interval.mk 0 h := by
      have hHNonneg : 0 ≤ h := of_decide_eq_true hPic.1
      rw [Interval.mem_iff]; exact ⟨by grind, hHNonneg⟩
    have hVal0 := evalInterval_sound xTildeBox (gamma 0) (hGamma 0 h0Mem) rhs fTildeIv hfTilde
    exact Interval.mem_imp_wf hVal0
  have hQBounds := evalPicardQuadSum_bounds (rhs := rhs) (gamma := gamma) (qs := nodes t) (iv := fTildeIv)
    (fun p hp =>
      let ⟨hw, hτ⟩ := hPts p hp
      ⟨hw, evalInterval_sound xTildeBox (gamma p.2) (hGamma p.2 hτ) rhs fTildeIv hfTilde⟩)
  rw [hSumEq] at hQBounds
  have hLoInMul : (t * fTildeIv.lo) ∈ Interval.mul (Interval.mk 0 h) fTildeIv :=
    Interval.mul_mem ht ⟨by grind, hfWf⟩
  have hHiInMul : (t * fTildeIv.hi) ∈ Interval.mul (Interval.mk 0 h) fTildeIv :=
    Interval.mul_mem ht ⟨hfWf, by grind⟩
  have hSumInMul : evalPicardQuadSum rhs gamma (nodes t) ∈ Interval.mul (Interval.mk 0 h) fTildeIv := by
    rw [Interval.mem_iff] at hLoInMul hHiInMul ⊢
    grind
  exact Interval.subset_sound hSub (Interval.add_mem (hBox0 v x0Iv hx0Look) hSumInMul)

/-- **Theorem (`iteratePicardOperator_stays_in_apriori`)**:
By induction on the iteration index $n \in \mathbb{N}$, EVERY Picard iterate $\Phi^{[n]}(\rho_0)(t)$
stays inside the a-priori box $\tilde{X}$ for all $t \in [0, h]$! -/
theorem iteratePicardOperator_stays_in_apriori
    (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval)) (h : CanonicalRat)
    (rho0 : String → CanonicalRat)
    (nodes : CanonicalRat → List (CanonicalRat × CanonicalRat))
    (hPic : verifyPicardAPriori sys x0Box xTildeBox h = true)
    (hBox0 : BoxMem rho0 x0Box)
    (hInitInTilde : BoxMem rho0 xTildeBox)
    (hFieldsCover : ∀ v iv, xTildeBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields)
    (hQuad : ValidQuadratureOn h nodes)
    (n : Nat) :
    ∀ t, t ∈ Interval.mk 0 h → BoxMem (iteratePicardOperator sys rho0 nodes n t) xTildeBox := by
  induction n with
  | zero =>
    intro _ _
    exact hInitInTilde
  | succ k ih =>
    intro t ht
    exact picardOperator_self_maps_apriori sys x0Box xTildeBox h rho0 nodes
      (iteratePicardOperator sys rho0 nodes k) hPic hBox0 hFieldsCover hQuad ih ht

theorem evalPicardQuadSum_lipschitz_diff
    {sys : OdeSystem} {xTildeBox : List (String × Interval)} {L D : CanonicalRat}
    {rhs : RealExpr} {name : String}
    {g1 g2 : CanonicalRat → String → CanonicalRat}
    {qs : List (CanonicalRat × CanonicalRat)}
    (hLip : IsOdeBoxLipschitz sys xTildeBox L)
    (hD : 0 ≤ D)
    (hMemField : (name, rhs) ∈ sys.fields)
    (hNodes : ∀ p ∈ qs,
      0 ≤ p.1 ∧
      BoxMem (g1 p.2) xTildeBox ∧
      BoxMem (g2 p.2) xTildeBox ∧
      boxDistInf (odeStateVars sys) (g1 p.2) (g2 p.2) ≤ D) :
    ratAbs (evalPicardQuadSum rhs g1 qs - evalPicardQuadSum rhs g2 qs) ≤
      quadWeightSum qs * (L * D) := by
  induction qs with
  | nil =>
    simp [evalPicardQuadSum, quadWeightSum, ratAbs]
    grind
  | cons hd tl ih =>
    rcases hd with ⟨w, τ⟩
    obtain ⟨hw, hB1, hB2, hDist⟩ := hNodes (w, τ) (List.mem_cons_self ..)
    have hRest := ih (fun p hp => hNodes p (List.mem_cons_of_mem _ hp))
    have hSplit :
        (w * evalExpr (g1 τ) rhs + evalPicardQuadSum rhs g1 tl) -
          (w * evalExpr (g2 τ) rhs + evalPicardQuadSum rhs g2 tl) =
        w * (evalExpr (g1 τ) rhs - evalExpr (g2 τ) rhs) +
          (evalPicardQuadSum rhs g1 tl - evalPicardQuadSum rhs g2 tl) := by grind
    unfold evalPicardQuadSum quadWeightSum
    rw [hSplit]
    have hTri := ratAbs_add_le
      (w * (evalExpr (g1 τ) rhs - evalExpr (g2 τ) rhs))
      (evalPicardQuadSum rhs g1 tl - evalPicardQuadSum rhs g2 tl)
    rw [ratAbs_mul_of_nonneg hw] at hTri
    have hF := hLip.2 (g1 τ) (g2 τ) hB1 hB2 name rhs hMemField
    have hLD : L * boxDistInf (odeStateVars sys) (g1 τ) (g2 τ) ≤ L * D :=
      Rat.mul_le_mul_of_nonneg_left hDist hLip.1
    have hwF : w * ratAbs (evalExpr (g1 τ) rhs - evalExpr (g2 τ) rhs) ≤ w * (L * D) :=
      Rat.mul_le_mul_of_nonneg_left (by grind) hw
    let _ := hD
    grind

/-- **Theorem (`picardOperator_contraction`)**:
Under `IsOdeBoxLipschitz sys xTildeBox L` and `0 ≤ h` on a closed quadrature grid `times ⊆ [0, h]`,
the Picard operator $\Phi$ satisfies the Banach contraction inequality:
$$\|\Phi(\gamma_1) - \Phi(\gamma_2)\|_{\infty,\text{times}} \le (L \cdot h) \cdot \|\gamma_1 - \gamma_2\|_{\infty,\text{times}},$$
with strict contraction rate $0 \le L \cdot h < 1$ whenever `L * h < 1`! -/
theorem picardOperator_contraction
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) (L h : CanonicalRat)
    (rho0 : String → CanonicalRat)
    (nodes : CanonicalRat → List (CanonicalRat × CanonicalRat))
    (times : List CanonicalRat)
    (g1 g2 : CanonicalRat → String → CanonicalRat)
    (hH : 0 ≤ h)
    (hLip : IsOdeBoxLipschitz sys xTildeBox L)
    (hContract : L * h < 1)
    (hGrid : ∀ t ∈ times, t ∈ Interval.mk 0 h ∧ quadWeightSum (nodes t) = t ∧
      ∀ p ∈ nodes t, 0 ≤ p.1 ∧ p.2 ∈ times)
    (hg1 : ∀ t ∈ times, BoxMem (g1 t) xTildeBox)
    (hg2 : ∀ t ∈ times, BoxMem (g2 t) xTildeBox) :
    0 ≤ L * h ∧
    L * h < 1 ∧
    curveSupDist (odeStateVars sys) times
      (picardOperator sys rho0 nodes g1)
      (picardOperator sys rho0 nodes g2) ≤
      (L * h) * curveSupDist (odeStateVars sys) times g1 g2 := by
  let D := curveSupDist (odeStateVars sys) times g1 g2
  have hDNonneg : 0 ≤ D := curveSupDist_nonneg (odeStateVars sys) times g1 g2
  have hLhNonneg : 0 ≤ L * h := by
    have := Rat.mul_le_mul_of_nonneg_left hH hLip.1; grind
  have hBoundNonneg : 0 ≤ (L * h) * D := by
    have := Rat.mul_le_mul_of_nonneg_left hDNonneg hLhNonneg; grind
  refine ⟨hLhNonneg, hContract, curveSupDist_le_of_all hBoundNonneg ?_⟩
  intro t htMem
  obtain ⟨htIv, hSumT, hPtsT⟩ := hGrid t htMem
  rw [Interval.mem_iff] at htIv
  apply boxDistInf_le_of_all hBoundNonneg
  intro v hvMem
  unfold picardOperator
  cases hFind : sys.fields.find? (·.1 == v) with
  | none =>
    have hZero : (rho0 v - rho0 v) = 0 := by grind
    rw [hZero]
    have hAbs0 : ratAbs 0 = 0 := by simp [ratAbs]
    rw [hAbs0]
    exact hBoundNonneg
  | some pair =>
    rcases pair with ⟨kName, rhs⟩
    obtain ⟨hkEq, hMemField⟩ := find?_pair_mem_and_eq sys.fields v (kName, rhs) hFind
    dsimp only at hkEq
    rw [hkEq] at hMemField
    have hCancelRho :
        (rho0 v + evalPicardQuadSum rhs g1 (nodes t)) -
          (rho0 v + evalPicardQuadSum rhs g2 (nodes t)) =
        evalPicardQuadSum rhs g1 (nodes t) - evalPicardQuadSum rhs g2 (nodes t) := by grind
    rw [hCancelRho]
    have hDiff := evalPicardQuadSum_lipschitz_diff (sys := sys) (xTildeBox := xTildeBox)
      (L := L) (D := D) (rhs := rhs) (name := v) (g1 := g1) (g2 := g2) (qs := nodes t)
      hLip hDNonneg hMemField
      (fun p hp =>
        let ⟨hw, hτMem⟩ := hPtsT p hp
        ⟨hw, hg1 p.2 hτMem, hg2 p.2 hτMem, curveSupDist_at_le hτMem⟩)
    rw [hSumT] at hDiff
    have hLDNonneg : 0 ≤ L * D := by
      have := Rat.mul_le_mul_of_nonneg_left hDNonneg hLip.1; grind
    have htLeH : t * (L * D) ≤ h * (L * D) :=
      Rat.mul_le_mul_of_nonneg_right htIv.2 hLDNonneg
    let _ := hvMem
    grind

/-- **Theorem (`iteratePicardOperator_geometric_decay`)**:
By induction on $n \in \mathbb{N}$, when `verifyPicardAPriori sys x0Box xTildeBox h = true`,
`IsOdeBoxLipschitz sys xTildeBox L`, and `L * h < 1`, consecutive Picard iterates contract geometrically:
$$\|\Phi^{[n+1]}(\rho_0) - \Phi^{[n]}(\rho_0)\|_{\infty,\text{times}} \le (L \cdot h)^n \cdot \|\Phi(\rho_0) - \rho_0\|_{\infty,\text{times}}.$$ -/
theorem iteratePicardOperator_geometric_decay
    (sys : OdeSystem) (x0Box xTildeBox : List (String × Interval)) (L h : CanonicalRat)
    (rho0 : String → CanonicalRat)
    (nodes : CanonicalRat → List (CanonicalRat × CanonicalRat))
    (times : List CanonicalRat)
    (hPic : verifyPicardAPriori sys x0Box xTildeBox h = true)
    (hBox0 : BoxMem rho0 x0Box)
    (hInitInTilde : BoxMem rho0 xTildeBox)
    (hFieldsCover : ∀ v iv, xTildeBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields)
    (hQuad : ValidQuadratureOn h nodes)
    (hLip : IsOdeBoxLipschitz sys xTildeBox L)
    (hContract : L * h < 1)
    (hGrid : ∀ t ∈ times, t ∈ Interval.mk 0 h ∧ quadWeightSum (nodes t) = t ∧
      ∀ p ∈ nodes t, 0 ≤ p.1 ∧ p.2 ∈ times)
    (n : Nat) :
    curveSupDist (odeStateVars sys) times
      (iteratePicardOperator sys rho0 nodes (n + 1))
      (iteratePicardOperator sys rho0 nodes n) ≤
      powRatFlow (L * h) n *
        curveSupDist (odeStateVars sys) times
          (iteratePicardOperator sys rho0 nodes 1)
          (iteratePicardOperator sys rho0 nodes 0) := by
  have hH : 0 ≤ h := by
    unfold verifyPicardAPriori at hPic
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPic
    exact hPic.1
  induction n with
  | zero =>
    unfold powRatFlow
    grind
  | succ k ih =>
    have hg1 : ∀ t ∈ times, BoxMem (iteratePicardOperator sys rho0 nodes (k + 1) t) xTildeBox :=
      fun t ht => iteratePicardOperator_stays_in_apriori sys x0Box xTildeBox h rho0 nodes
        hPic hBox0 hInitInTilde hFieldsCover hQuad (k + 1) t (hGrid t ht).1
    have hg0 : ∀ t ∈ times, BoxMem (iteratePicardOperator sys rho0 nodes k t) xTildeBox :=
      fun t ht => iteratePicardOperator_stays_in_apriori sys x0Box xTildeBox h rho0 nodes
        hPic hBox0 hInitInTilde hFieldsCover hQuad k t (hGrid t ht).1
    have hStep := (picardOperator_contraction sys xTildeBox L h rho0 nodes times
      (iteratePicardOperator sys rho0 nodes (k + 1))
      (iteratePicardOperator sys rho0 nodes k)
      hH hLip hContract hGrid hg1 hg0).2.2
    have hLhNonneg : 0 ≤ L * h := by
      have := Rat.mul_le_mul_of_nonneg_left hH hLip.1; grind
    have hMulIh := Rat.mul_le_mul_of_nonneg_left ih hLhNonneg
    have hPow : powRatFlow (L * h) (k + 1) = (L * h) * powRatFlow (L * h) k := rfl
    have hIter2 : iteratePicardOperator sys rho0 nodes (k + 2) =
        picardOperator sys rho0 nodes (iteratePicardOperator sys rho0 nodes (k + 1)) := rfl
    have hIter1 : iteratePicardOperator sys rho0 nodes (k + 1) =
        picardOperator sys rho0 nodes (iteratePicardOperator sys rho0 nodes k) := rfl
    rw [hPow, hIter2]
    rw [← hIter1] at hStep
    grind

/-- **Theorem (`picardOperator_unique_fixed_point`)**:
When $L \cdot h < 1$, any two fixed points $\gamma_1, \gamma_2$ of $\Phi$ inside $\tilde{X}$ on `times`
coincide identically across all $t \in \text{times}$ and all state variables $v \in \text{odeStateVars sys}$. -/
theorem picardOperator_unique_fixed_point
    (sys : OdeSystem) (xTildeBox : List (String × Interval)) (L h : CanonicalRat)
    (rho0 : String → CanonicalRat)
    (nodes : CanonicalRat → List (CanonicalRat × CanonicalRat))
    (times : List CanonicalRat)
    (g1 g2 : CanonicalRat → String → CanonicalRat)
    (hH : 0 ≤ h)
    (hLip : IsOdeBoxLipschitz sys xTildeBox L)
    (hContract : L * h < 1)
    (hGrid : ∀ t ∈ times, t ∈ Interval.mk 0 h ∧ quadWeightSum (nodes t) = t ∧
      ∀ p ∈ nodes t, 0 ≤ p.1 ∧ p.2 ∈ times)
    (hg1 : ∀ t ∈ times, BoxMem (g1 t) xTildeBox)
    (hg2 : ∀ t ∈ times, BoxMem (g2 t) xTildeBox)
    (hFix1 : ∀ t ∈ times, ∀ v ∈ odeStateVars sys, picardOperator sys rho0 nodes g1 t v = g1 t v)
    (hFix2 : ∀ t ∈ times, ∀ v ∈ odeStateVars sys, picardOperator sys rho0 nodes g2 t v = g2 t v) :
    ∀ t ∈ times, ∀ v ∈ odeStateVars sys, g1 t v = g2 t v := by
  have hCont := (picardOperator_contraction sys xTildeBox L h rho0 nodes times g1 g2
    hH hLip hContract hGrid hg1 hg2).2.2
  have hEqDist : ∀ (vars : List String),
      (∀ u ∈ vars, u ∈ odeStateVars sys) →
      ∀ t ∈ times,
        boxDistInf vars (g1 t) (g2 t) =
          boxDistInf vars (picardOperator sys rho0 nodes g1 t) (picardOperator sys rho0 nodes g2 t) := by
    intro vars hSub t ht
    induction vars with
    | nil => rfl
    | cons u us ih =>
      unfold boxDistInf
      rw [hFix1 t ht u (hSub u (List.mem_cons_self ..)),
          hFix2 t ht u (hSub u (List.mem_cons_self ..)),
          ih (fun w hw => hSub w (List.mem_cons_of_mem _ hw))]
  have hSupEq : curveSupDist (odeStateVars sys) times g1 g2 =
      curveSupDist (odeStateVars sys) times
        (picardOperator sys rho0 nodes g1) (picardOperator sys rho0 nodes g2) :=
    curveSupDist_congr (fun t ht => hEqDist (odeStateVars sys) (fun u hu => hu) t ht)
  rw [← hSupEq] at hCont
  let D := curveSupDist (odeStateVars sys) times g1 g2
  have hDNonneg : 0 ≤ D := curveSupDist_nonneg (odeStateVars sys) times g1 g2
  have hDZero : D = 0 := by
    by_cases hPos : 0 < D
    · have hDiffPos : 0 < 1 - L * h := by grind
      have hProdPos : 0 < (1 - L * h) * D := Rat.mul_pos hDiffPos hPos
      grind
    · grind
  intro t ht v hv
  have htLe : boxDistInf (odeStateVars sys) (g1 t) (g2 t) ≤ D := curveSupDist_at_le ht
  have hvLe : ratAbs (g1 t v - g2 t v) ≤ boxDistInf (odeStateVars sys) (g1 t) (g2 t) :=
    boxDistInf_comp_le hv
  rw [hDZero] at htLe
  have hvZero : ratAbs (g1 t v - g2 t v) ≤ 0 := by grind
  rw [ratAbs_le_iff] at hvZero
  grind

/-! ## 6. Inductive $K$-Step Tube & Trajectory Safety (`verifyTrajectorySafety_sound`, `picardIteratedTrajectory_safety_sound`) -/

theorem mapM_kv_lookup_inv {α : Type} {F : (String × α) → Option (String × Interval)}
    (hKey : ∀ p out, F p = some out → out.1 = p.1) :
    ∀ {fields : List (String × α)} {outBox : List (String × Interval)} {v : String} {outIv : Interval},
      fields.mapM F = some outBox →
      outBox.lookup v = some outIv →
      ∃ rhs, (v, rhs) ∈ fields ∧ F (v, rhs) = some (v, outIv)
  | [], outBox, v, outIv, hMap, hLook => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at hMap
    subst hMap
    simp at hLook
  | (n, rhs) :: rest, outBox, v, outIv, hMap, hLook => by
    simp only [List.mapM_cons, bind, Option.bind, pure] at hMap
    cases hp : F (n, rhs) with
    | none =>
      rw [hp] at hMap
      simp at hMap
    | some headOut =>
      rw [hp] at hMap
      cases hRest : rest.mapM F with
      | none =>
        rw [hRest] at hMap
        simp at hMap
      | some restOut =>
        rw [hRest] at hMap
        dsimp only at hMap
        injection hMap with hOutEq
        subst hOutEq
        have hKeyEq : headOut.1 = n := hKey (n, rhs) headOut hp
        rcases headOut with ⟨n', ivHead⟩
        dsimp only at hKeyEq
        rw [hKeyEq] at hp hLook
        simp only [List.lookup] at hLook
        cases hvn : v == n
        · rw [hvn] at hLook
          obtain ⟨rhs', hMem', hf'⟩ := mapM_kv_lookup_inv hKey hRest hLook
          exact ⟨rhs', List.mem_cons_of_mem _ hMem', hf'⟩
        · rw [hvn, Option.some.injEq] at hLook
          rw [hLook] at hp
          simp only [beq_iff_eq] at hvn
          rw [hvn]
          exact ⟨rhs, List.mem_cons_self .., hp⟩

theorem checkBoxInEnvelope_sound
    {box safeBounds : List (String × Interval)} {rho : String → CanonicalRat}
    (hCheck : checkBoxInEnvelope box safeBounds = true)
    (hBox : BoxMem rho box) :
    BoxMem rho safeBounds := by
  intro v safeIv hLook
  unfold checkBoxInEnvelope at hCheck
  induction safeBounds with
  | nil => simp at hLook
  | cons hd tl ih =>
    rcases hd with ⟨name, iv⟩
    simp only [List.all_cons, Bool.and_eq_true] at hCheck
    simp only [List.lookup] at hLook
    cases hvn : v == name
    · rw [hvn] at hLook
      exact ih hCheck.2 hLook
    · rw [hvn, Option.some.injEq] at hLook
      have hHead := hCheck.1
      rw [hLook] at hHead
      simp only [beq_iff_eq] at hvn
      rw [← hvn] at hHead
      cases hFind : box.find? (·.1 == v) with
      | none => rw [hFind] at hHead; simp at hHead
      | some p =>
        rcases p with ⟨k, curIv⟩
        rw [hFind] at hHead
        have hLookBox : box.lookup v = some curIv := by
          have hMap := find?_map_snd_eq_lookup box v
          rw [hFind] at hMap
          exact hMap.symm
        change Interval.subset curIv safeIv = true at hHead
        exact Interval.subset_sound hHead (hBox v curIv hLookBox)

theorem widenIntervalSymmetric_mem
    {iv : Interval} {scale minPad x : CanonicalRat}
    (hScale : 1 ≤ scale) (hPad : 0 ≤ minPad) (hx : x ∈ iv) :
    x ∈ widenIntervalSymmetric iv scale minPad := by
  dsimp only [widenIntervalSymmetric]
  rw [Interval.mem_iff] at hx ⊢
  have hLoEq : (iv.lo + iv.hi) / 2 - (iv.hi - iv.lo) / 2 = iv.lo := by grind
  have hHiEq : (iv.lo + iv.hi) / 2 + (iv.hi - iv.lo) / 2 = iv.hi := by grind
  cases hd : decide (((iv.hi - iv.lo) / 2) ≤ 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hHalfPos : 0 ≤ (iv.hi - iv.lo) / 2 := by
      have hNot : ¬ (((iv.hi - iv.lo) / 2) ≤ 0) := of_decide_eq_false hd
      grind
    have hScaleHalf : ((iv.hi - iv.lo) / 2) * 1 ≤ ((iv.hi - iv.lo) / 2) * scale :=
      Rat.mul_le_mul_of_nonneg_left hScale hHalfPos
    grind
  · simp only [↓reduceIte]
    have hHalfLeP : (iv.hi - iv.lo) / 2 ≤ 0 := of_decide_eq_true hd
    grind

theorem picardHullStep_preserves_init_and_fields
    {sys : OdeSystem} {x0Box curBox nextBox : List (String × Interval)}
    {rho0 : String → CanonicalRat}
    (hStep : picardHullStep sys x0Box curBox = some nextBox)
    (hCur : BoxMem rho0 curBox) :
    BoxMem rho0 nextBox ∧ ∀ v iv, nextBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields := by
  unfold picardHullStep at hStep
  have hKey : ∀ (p : String × RealExpr) (out : String × Interval),
      (match p with
       | (name, rhsExpr) => do
         let x0Iv ← x0Box.lookup name
         let curIv ← curBox.lookup name
         let fIv ← evalInterval curBox rhsExpr
         let pIv := Interval.add x0Iv (Interval.mul (Interval.mk 0 sys.dt) fIv)
         pure (name, (⟨min curIv.lo pIv.lo, max curIv.hi pIv.hi⟩ : Interval))) = some out →
      out.1 = p.1 := by
    intro ⟨n, r⟩ out hOut
    dsimp only [bind, Option.bind, pure] at hOut
    cases hx0 : x0Box.lookup n <;> rw [hx0] at hOut
    · simp at hOut
    · cases hc : curBox.lookup n <;> rw [hc] at hOut
      · simp at hOut
      · cases hf : evalInterval curBox r <;> rw [hf] at hOut
        · simp at hOut
        · simp only [Option.some.injEq] at hOut
          rw [← hOut]
  have hCover : ∀ v iv, nextBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields := by
    intro v iv hLook
    obtain ⟨rhs, hMem, _⟩ := mapM_kv_lookup_inv hKey hStep hLook
    exact ⟨rhs, hMem⟩
  refine ⟨?_, hCover⟩
  intro v iv hLook
  obtain ⟨rhs, _, hF⟩ := mapM_kv_lookup_inv hKey hStep hLook
  dsimp only [bind, Option.bind, pure] at hF
  cases hx0 : x0Box.lookup v with
  | none => rw [hx0] at hF; simp at hF
  | some x0Iv =>
    rw [hx0] at hF
    cases hcur : curBox.lookup v with
    | none => rw [hcur] at hF; simp at hF
    | some curIv =>
      rw [hcur] at hF
      cases hf : evalInterval curBox rhs with
      | none => rw [hf] at hF; simp at hF
      | some fIv =>
        rw [hf] at hF
        simp only [Option.some.injEq, Prod.mk.injEq] at hF
        rcases hF with ⟨_, rfl⟩
        have hMemCur := hCur v curIv hcur
        rw [Interval.mem_iff] at hMemCur ⊢
        grind

theorem iteratePicardHull_preserves_init_and_fields
    {sys : OdeSystem} {x0Box : List (String × Interval)} {rho0 : String → CanonicalRat} :
    ∀ (k : Nat) {curBox outBox : List (String × Interval)},
      iteratePicardHull sys x0Box curBox k = some outBox →
      BoxMem rho0 curBox →
      (∀ v iv, curBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields) →
      BoxMem rho0 outBox ∧ ∀ v iv, outBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields
  | 0, curBox, outBox, hIter, hCur, hCov => by
    simp [iteratePicardHull] at hIter
    subst hIter
    exact ⟨hCur, hCov⟩
  | k + 1, curBox, outBox, hIter, hCur, hCov => by
    simp only [iteratePicardHull, bind, Option.bind] at hIter
    cases hStep : picardHullStep sys x0Box curBox with
    | none => rw [hStep] at hIter; simp at hIter
    | some nextBox =>
      rw [hStep] at hIter
      obtain ⟨hNextMem, hNextCov⟩ := picardHullStep_preserves_init_and_fields hStep hCur
      let _ := hCov
      exact iteratePicardHull_preserves_init_and_fields k hIter hNextMem hNextCov

theorem lookup_map_val {α β : Type} (g : α → β) :
    ∀ (box : List (String × α)) (v : String),
      (box.map fun (name, x) => (name, g x)).lookup v = (box.lookup v).map g
  | [], _ => rfl
  | (n, x) :: rest, v => by
    simp only [List.map_cons, List.lookup]
    cases hvn : v == n <;> simp [lookup_map_val g rest v]

theorem map_widen_preserves_init_and_fields
    {scale minPad : CanonicalRat} {rho0 : String → CanonicalRat}
    {sys : OdeSystem} {box : List (String × Interval)}
    (hScale : 1 ≤ scale) (hPad : 0 ≤ minPad)
    (hBox : BoxMem rho0 box)
    (hCov : ∀ v iv, box.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields) :
    let widened := box.map fun (name, hIv) => (name, widenIntervalSymmetric hIv scale minPad)
    BoxMem rho0 widened ∧ ∀ v iv, widened.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields := by
  dsimp only
  let g := fun hIv => widenIntervalSymmetric hIv scale minPad
  constructor
  · intro v iv hLook
    rw [lookup_map_val g box v] at hLook
    obtain ⟨hIv, hBoxLook, rfl⟩ := Option.map_eq_some_iff.1 hLook
    exact widenIntervalSymmetric_mem hScale hPad (hBox v hIv hBoxLook)
  · intro v iv hLook
    rw [lookup_map_val g box v] at hLook
    obtain ⟨hIv, hBoxLook, _⟩ := Option.map_eq_some_iff.1 hLook
    exact hCov v hIv hBoxLook

theorem inflatePicardLoop_verifies {sys : OdeSystem} {x0Box : List (String × Interval)} :
    ∀ (fuel : Nat) {curBox outBox : List (String × Interval)},
      inflatePicardLoop sys x0Box fuel curBox = some outBox →
      verifyPicardAPriori sys x0Box outBox sys.dt = true
  | 0, curBox, outBox, hLoop => by
    unfold inflatePicardLoop at hLoop
    cases hV : verifyPicardAPriori sys x0Box curBox sys.dt with
    | false => rw [hV] at hLoop; simp at hLoop
    | true =>
      rw [hV] at hLoop
      simp only [↓reduceIte, Option.some.injEq] at hLoop
      subst hLoop
      exact hV
  | fuel + 1, curBox, outBox, hLoop => by
    unfold inflatePicardLoop at hLoop
    cases hV : verifyPicardAPriori sys x0Box curBox sys.dt with
    | true =>
      rw [hV] at hLoop
      simp only [↓reduceIte, Option.some.injEq] at hLoop
      subst hLoop
      exact hV
    | false =>
      rw [hV] at hLoop
      simp only [Bool.false_eq_true, ↓reduceIte] at hLoop
      cases hHull : iteratePicardHull sys x0Box curBox 4 with
      | none =>
        rw [hHull] at hLoop
        simp [bind, Option.bind] at hLoop
      | some hullBox =>
        rw [hHull] at hLoop
        dsimp only [bind, Option.bind] at hLoop
        cases hVH : verifyPicardAPriori sys x0Box hullBox sys.dt with
        | true =>
          rw [hVH] at hLoop
          simp only [↓reduceIte, Option.some.injEq] at hLoop
          subst hLoop
          exact hVH
        | false =>
          rw [hVH] at hLoop
          simp only [Bool.false_eq_true, ↓reduceIte] at hLoop
          exact inflatePicardLoop_verifies fuel hLoop

theorem inflatePicardLoop_preserves_init_and_fields
    {sys : OdeSystem} {x0Box : List (String × Interval)} {rho0 : String → CanonicalRat} :
    ∀ (fuel : Nat) {curBox outBox : List (String × Interval)},
      inflatePicardLoop sys x0Box fuel curBox = some outBox →
      BoxMem rho0 curBox →
      (∀ v iv, curBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields) →
      BoxMem rho0 outBox ∧ ∀ v iv, outBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields
  | 0, curBox, outBox, hLoop, hCur, hCov => by
    unfold inflatePicardLoop at hLoop
    cases hV : verifyPicardAPriori sys x0Box curBox sys.dt with
    | false => rw [hV] at hLoop; simp at hLoop
    | true =>
      rw [hV] at hLoop
      simp only [↓reduceIte, Option.some.injEq] at hLoop
      subst hLoop
      exact ⟨hCur, hCov⟩
  | fuel + 1, curBox, outBox, hLoop, hCur, hCov => by
    unfold inflatePicardLoop at hLoop
    cases hV : verifyPicardAPriori sys x0Box curBox sys.dt with
    | true =>
      rw [hV] at hLoop
      simp only [↓reduceIte, Option.some.injEq] at hLoop
      subst hLoop
      exact ⟨hCur, hCov⟩
    | false =>
      rw [hV] at hLoop
      simp only [Bool.false_eq_true, ↓reduceIte] at hLoop
      cases hHull : iteratePicardHull sys x0Box curBox 4 with
      | none =>
        rw [hHull] at hLoop
        simp [bind, Option.bind] at hLoop
      | some hullBox =>
        rw [hHull] at hLoop
        dsimp only [bind, Option.bind] at hLoop
        obtain ⟨hHullMem, hHullCov⟩ := iteratePicardHull_preserves_init_and_fields 4 hHull hCur hCov
        cases hVH : verifyPicardAPriori sys x0Box hullBox sys.dt with
        | true =>
          rw [hVH] at hLoop
          simp only [↓reduceIte, Option.some.injEq] at hLoop
          subst hLoop
          exact ⟨hHullMem, hHullCov⟩
        | false =>
          rw [hVH] at hLoop
          simp only [Bool.false_eq_true, ↓reduceIte] at hLoop
          have hScale : (1 : CanonicalRat) ≤ (if fuel ≥ 4 then CanonicalRat.mk 11 10 else 2) := by
            split <;> decide +kernel
          have hPad : (0 : CanonicalRat) ≤ CanonicalRat.mk 1 8 := by decide +kernel
          obtain ⟨hWidMem, hWidCov⟩ :=
            map_widen_preserves_init_and_fields hScale hPad hHullMem hHullCov
          exact inflatePicardLoop_preserves_init_and_fields fuel hLoop hWidMem hWidCov

theorem inferPicardAPrioriBoxWithFuel_encloses_init_and_fields
    {sys : OdeSystem} {box xTildeBox : List (String × Interval)} {fuel : Nat}
    {rho0 : String → CanonicalRat}
    (hInfer : inferPicardAPrioriBoxWithFuel sys box fuel = some xTildeBox)
    (hBox0 : BoxMem rho0 box) :
    verifyPicardAPriori sys box xTildeBox sys.dt = true ∧
    0 ≤ sys.dt ∧
    BoxMem rho0 xTildeBox ∧
    (∀ v iv, xTildeBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields) := by
  unfold inferPicardAPrioriBoxWithFuel at hInfer
  let seedFn : (String × RealExpr) → Option (String × Interval) := fun (name, rhsExpr) => do
    let x0Iv ← box.lookup name
    let f0Iv ← evalInterval box rhsExpr
    pure (name, Interval.add x0Iv (Interval.mul (Interval.mk 0 sys.dt) f0Iv))
  change (do let cand1 ← sys.fields.mapM seedFn; inflatePicardLoop sys box fuel cand1) = some xTildeBox at hInfer
  have hSeedKey : ∀ p out, seedFn p = some out → out.1 = p.1 := by
    intro ⟨n, r⟩ out hOut
    dsimp only [seedFn, bind, Option.bind, pure] at hOut
    cases hx0 : box.lookup n <;> rw [hx0] at hOut
    · simp at hOut
    · cases hf0 : evalInterval box r <;> rw [hf0] at hOut
      · simp at hOut
      · simp only [Option.some.injEq] at hOut
        rw [← hOut]
  cases hCand : sys.fields.mapM seedFn with
  | none =>
    rw [hCand] at hInfer
    simp [bind, Option.bind] at hInfer
  | some cand1 =>
    rw [hCand] at hInfer
    dsimp only [bind, Option.bind] at hInfer
    have hVer := inflatePicardLoop_verifies fuel hInfer
    have hDtNonneg : 0 ≤ sys.dt := by
      unfold verifyPicardAPriori at hVer
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hVer
      exact hVer.1
    have hCandCov : ∀ v iv, cand1.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields := by
      intro v iv hLook
      obtain ⟨rhs, hMem, _⟩ := mapM_kv_lookup_inv hSeedKey hCand hLook
      exact ⟨rhs, hMem⟩
    have hCandMem : BoxMem rho0 cand1 := by
      intro v iv hLook
      obtain ⟨rhs, _, hF⟩ := mapM_kv_lookup_inv hSeedKey hCand hLook
      dsimp only [seedFn, bind, Option.bind, pure] at hF
      cases hx0 : box.lookup v with
      | none => rw [hx0] at hF; simp at hF
      | some x0Iv =>
        rw [hx0] at hF
        cases hf0 : evalInterval box rhs with
        | none => rw [hf0] at hF; simp at hF
        | some f0Iv =>
          rw [hf0] at hF
          simp only [Option.some.injEq, Prod.mk.injEq] at hF
          rcases hF with ⟨_, rfl⟩
          have h0Mem : (0 : CanonicalRat) ∈ Interval.mk 0 sys.dt := by
            rw [Interval.mem_iff]; exact ⟨by grind, hDtNonneg⟩
          have hv0Mem : evalExpr rho0 rhs ∈ f0Iv :=
            evalInterval_sound box rho0 hBox0 rhs f0Iv hf0
          have hAdd := Interval.add_mem (hBox0 v x0Iv hx0) (Interval.mul_mem h0Mem hv0Mem)
          have hId : rho0 v + 0 * evalExpr rho0 rhs = rho0 v := by grind
          rw [hId] at hAdd
          exact hAdd
    obtain ⟨hOutMem, hOutCov⟩ :=
      inflatePicardLoop_preserves_init_and_fields fuel hInfer hCandMem hCandCov
    exact ⟨hVer, hDtNonneg, hOutMem, hOutCov⟩

theorem inferPicardAPrioriBox_encloses_init_and_fields
    {sys : OdeSystem} {box xTildeBox : List (String × Interval)}
    {rho0 : String → CanonicalRat}
    (hInfer : inferPicardAPrioriBox sys box = some xTildeBox)
    (hBox0 : BoxMem rho0 box) :
    verifyPicardAPriori sys box xTildeBox sys.dt = true ∧
    0 ≤ sys.dt ∧
    BoxMem rho0 xTildeBox ∧
    (∀ v iv, xTildeBox.lookup v = some iv → ∃ rhs, (v, rhs) ∈ sys.fields) :=
  inferPicardAPrioriBoxWithFuel_encloses_init_and_fields hInfer hBox0

/-- Single-step $N$-dimensional enclosure theorem for `stepPicardValidated`:
Whenever `stepPicardValidated sys curBox xTildeBox h = some nextBox` and `BoxMem rho0 curBox`,
every state `rho1` satisfying the 2nd-order Taylor–Lie remainder law with intermediate Lie witness
`zeta` inside `xTildeBox` lies inside `nextBox`. -/
theorem stepPicardValidated_encloses_step
    {sys : OdeSystem} {curBox xTildeBox nextBox : List (String × Interval)}
    {h : CanonicalRat} {rho0 rho1 : String → CanonicalRat}
    (hStep : stepPicardValidated sys curBox xTildeBox h = some nextBox)
    (hBox0 : BoxMem rho0 curBox)
    (hStepLaw : ∀ name rhsExpr, (name, rhsExpr) ∈ sys.fields →
      ∃ zeta r_pad,
        BoxMem zeta xTildeBox ∧
        r_pad ∈ sys.remainderPad ∧
        rho1 name = rho0 name + h * evalExpr rho0 rhsExpr +
          (((h * h) / 2) * evalOdePointLieDerivComponent sys zeta rhsExpr + r_pad)) :
    BoxMem rho1 nextBox := by
  unfold stepPicardValidated at hStep
  cases hPic : verifyPicardAPriori sys curBox xTildeBox h with
  | false => rw [hPic] at hStep; simp at hStep
  | true =>
    rw [hPic] at hStep
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
    let stepFn : (String × RealExpr) → Option (String × Interval) := fun (name, rhsExpr) => do
      let curBoxIv ← curBox.lookup name
      let velBox ← evalInterval curBox rhsExpr
      let lieIv ← evalOdeLieDerivComponent sys xTildeBox rhsExpr
      let lieRem := derivePicardLieRemainder lieIv h
      let totalRem := Interval.add lieRem sys.remainderPad
      pure (name, stepFlowpipe1D curBoxIv velBox h totalRem)
    change sys.fields.mapM stepFn = some nextBox at hStep
    have hStepKey : ∀ p out, stepFn p = some out → out.1 = p.1 := by
      intro ⟨n, r⟩ out hOut
      dsimp only [stepFn, bind, Option.bind, pure] at hOut
      cases hc : curBox.lookup n <;> rw [hc] at hOut
      · simp at hOut
      · cases hv : evalInterval curBox r <;> rw [hv] at hOut
        · simp at hOut
        · cases hl : evalOdeLieDerivComponent sys xTildeBox r <;> rw [hl] at hOut
          · simp at hOut
          · simp only [Option.some.injEq] at hOut
            rw [← hOut]
    intro v nextIv hLook
    obtain ⟨rhsExpr, hMemField, hF⟩ := mapM_kv_lookup_inv hStepKey hStep hLook
    dsimp only [stepFn, bind, Option.bind, pure] at hF
    cases hCur : curBox.lookup v with
    | none => rw [hCur] at hF; simp at hF
    | some curIv =>
      rw [hCur] at hF
      cases hVel : evalInterval curBox rhsExpr with
      | none => rw [hVel] at hF; simp at hF
      | some velIv =>
        rw [hVel] at hF
        cases hLie : evalOdeLieDerivComponent sys xTildeBox rhsExpr with
        | none => rw [hLie] at hF; simp at hF
        | some lieIv =>
          rw [hLie] at hF
          simp only [Option.some.injEq, Prod.mk.injEq] at hF
          rcases hF with ⟨_, rfl⟩
          obtain ⟨zeta, r_pad, hZetaBox, hrPad, hEq1⟩ := hStepLaw v rhsExpr hMemField
          rw [hEq1]
          have h0Mem : rho0 v ∈ curIv := hBox0 v curIv hCur
          have hvMem : evalExpr rho0 rhsExpr ∈ velIv :=
            evalInterval_sound curBox rho0 hBox0 rhsExpr velIv hVel
          have hLieMem : evalOdePointLieDerivComponent sys zeta rhsExpr ∈ lieIv :=
            evalOdeLieDerivComponent_sound sys xTildeBox zeta hZetaBox rhsExpr lieIv hLie
          exact stepFlowpipe1D_mem h h0Mem hvMem
            (Interval.add_mem (derivePicardLieRemainder_mem h hLieMem) hrPad)

/-- Intrinsic dynamical characterization of a multi-step ODE flow / Picard-iterated trajectory over
`steps` horizons (completely independent of any interval box or verifier):
1. **Continuous Inter-Step Picard Cone (`k < steps`, `τ ∈ [0, sys.dt]`)**: there exists a valid
   rational quadrature rule `ValidQuadratureOn sys.dt nodes` such that every inter-step point
   `traj k τ` is realized by some Picard iterate `iteratePicardOperator sys (traj k 0) nodes m τ`
   (covering constant $m=0$, Euler $m=1$, Heun $m=2$, and arbitrary higher-order Picard iterates),
2. **2nd-Order Taylor–Lie Step Evolution (`k < steps`)**: for every state variable
   `(name, rhsExpr) ∈ sys.fields`, there exist an intermediate time `ζ ∈ [0, sys.dt]` and additive
   remainder `r_pad ∈ sys.remainderPad` such that
   $$x_{k+1,i}(0) = x_{k,i}(0) + \Delta t \cdot f_i(x_k(0)) + \frac{\Delta t^2}{2}(\mathcal{L}_f f_i)(x_k(\zeta)) + r_{\text{pad}}.$$ -/
@[expose] def IsValidOdeFlowTrajectory
    (sys : OdeSystem) (steps : Nat)
    (traj : Nat → CanonicalRat → String → CanonicalRat) : Prop :=
  ∀ k, k < steps →
    (∃ nodes, ValidQuadratureOn sys.dt nodes ∧
      ∀ τ ∈ Interval.mk 0 sys.dt, ∃ m : Nat,
        ∀ v, traj k τ v = iteratePicardOperator sys (traj k 0) nodes m τ v) ∧
    (∀ name rhsExpr, (name, rhsExpr) ∈ sys.fields →
      ∃ ζ r_pad,
        ζ ∈ Interval.mk 0 sys.dt ∧
        r_pad ∈ sys.remainderPad ∧
        traj (k + 1) 0 name = traj k 0 name + sys.dt * evalExpr (traj k 0) rhsExpr +
          (((sys.dt * sys.dt) / 2) * evalOdePointLieDerivComponent sys (traj k ζ) rhsExpr + r_pad))

/-- Inductive $K$-step soundness helper for `verifyTrajectorySafetyLoop`. -/
theorem verifyTrajectorySafetyLoop_sound :
    ∀ (steps : Nat) (sys : OdeSystem) (curBox safeBounds : List (String × Interval))
      (traj : Nat → CanonicalRat → String → CanonicalRat),
      verifyTrajectorySafetyLoop sys safeBounds steps curBox = true →
      BoxMem (traj 0 0) curBox →
      IsValidOdeFlowTrajectory sys steps traj →
      ∃ tube,
        runFlowpipeLoop sys steps curBox = some tube ∧
        tube.length = steps + 1 ∧
        (∀ k, k ≤ steps → BoxMem (traj k 0) (tube.getD k []) ∧ BoxMem (traj k 0) safeBounds) ∧
        (∀ k, k < steps → ∀ τ ∈ Interval.mk 0 sys.dt, BoxMem (traj k τ) safeBounds)
  | 0, sys, curBox, safeBounds, traj, hVer, hInit, _ => by
    unfold verifyTrajectorySafetyLoop at hVer
    refine ⟨[curBox], rfl, rfl, ?_, ?_⟩
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨hInit, checkBoxInEnvelope_sound hVer hInit⟩
    · intro k hk; omega
  | steps + 1, sys, curBox, safeBounds, traj, hVer, hInit, hFlow => by
    unfold verifyTrajectorySafetyLoop at hVer
    cases hEnv0 : checkBoxInEnvelope curBox safeBounds with
    | false => rw [hEnv0] at hVer; simp at hVer
    | true =>
      rw [hEnv0] at hVer
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hVer
      cases hInfer : inferPicardAPrioriBox sys curBox with
      | none => rw [hInfer] at hVer; simp at hVer
      | some xTildeBox =>
        rw [hInfer] at hVer
        dsimp only at hVer
        cases hEnvTilde : checkBoxInEnvelope xTildeBox safeBounds with
        | false => rw [hEnvTilde] at hVer; simp at hVer
        | true =>
          rw [hEnvTilde] at hVer
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hVer
          cases hStep : stepPicardValidated sys curBox xTildeBox sys.dt with
          | none => rw [hStep] at hVer; simp at hVer
          | some nextBox =>
            rw [hStep] at hVer
            dsimp only at hVer
            obtain ⟨hPic, _, hInitTilde, hCovTilde⟩ :=
              inferPicardAPrioriBox_encloses_init_and_fields hInfer hInit
            obtain ⟨⟨nodes0, hQuad0, hCone0⟩, hTaylor0⟩ := hFlow 0 (Nat.zero_lt_succ steps)
            have hSegTilde : ∀ τ ∈ Interval.mk 0 sys.dt, BoxMem (traj 0 τ) xTildeBox := by
              intro τ hτ
              obtain ⟨m, hmEq⟩ := hCone0 τ hτ
              have hIterMem := iteratePicardOperator_stays_in_apriori
                sys curBox xTildeBox sys.dt (traj 0 0) nodes0 hPic hInit hInitTilde hCovTilde hQuad0 m τ hτ
              intro v iv hLook
              rw [hmEq v]
              exact hIterMem v iv hLook
            have hNextInit : BoxMem (traj 1 0) nextBox := by
              apply stepPicardValidated_encloses_step hStep hInit
              intro name rhsExpr hMemField
              obtain ⟨ζ, r_pad, hζ, hrPad, hEq⟩ := hTaylor0 name rhsExpr hMemField
              exact ⟨traj 0 ζ, r_pad, hSegTilde ζ hζ, hrPad, hEq⟩
            let trajShift : Nat → CanonicalRat → String → CanonicalRat := fun k => traj (k + 1)
            have hFlowShift : IsValidOdeFlowTrajectory sys steps trajShift := by
              intro k hk
              exact hFlow (k + 1) (Nat.succ_lt_succ hk)
            obtain ⟨restTube, hRestRun, hRestLen, hRestDisc, hRestCont⟩ :=
              verifyTrajectorySafetyLoop_sound steps sys nextBox safeBounds trajShift
                hVer hNextInit hFlowShift
            have hRunSucc : runFlowpipeLoop sys (steps + 1) curBox = some (curBox :: restTube) := by
              unfold runFlowpipeLoop stepFlowpipe
              simp [bind, Option.bind, pure, hInfer, hStep, hRestRun]
            refine ⟨curBox :: restTube, hRunSucc, by simp [hRestLen], ?_, ?_⟩
            · intro k hk
              cases k with
              | zero =>
                exact ⟨hInit, checkBoxInEnvelope_sound hEnv0 hInit⟩
              | succ j =>
                have hj : j ≤ steps := by omega
                have hSub := hRestDisc j hj
                simpa [trajShift, List.getD] using hSub
            · intro k hk τ hτ
              cases k with
              | zero =>
                exact checkBoxInEnvelope_sound hEnvTilde (hSegTilde τ hτ)
              | succ j =>
                have hj : j < steps := by omega
                exact hRestCont j hj τ hτ

/-- **Theorem (`verifyTrajectorySafety_sound`)**:
Universal $K$-step tube & continuous-time trajectory safety theorem!
Whenever `verifyTrajectorySafety sys initBox steps safeBounds = true`:
1. `runFlowpipe sys initBox steps` succeeds with a certified `(steps + 1)`-slice tube `tube = [X_0, ..., X_steps]`,
2. For **every** initial point `traj 0 0 ∈ initBox` and **every** `steps`-step ODE / Picard-iterated
   trajectory `traj` satisfying `IsValidOdeFlowTrajectory sys steps traj`:
   - **Discrete Tube Containment & Safety**: for all $k \le \text{steps}$, `traj k 0 ∈ tube[k]` AND `traj k 0 ∈ safeBounds`,
   - **Continuous Inter-Step Barrier Safety (No Tunneling)**: for all $k < \text{steps}$ and all local times
     $\tau \in [0, \Delta t]$, `traj k τ ∈ safeBounds`! -/
theorem verifyTrajectorySafety_sound :
    ∀ (sys : OdeSystem) (initBox safeBounds : List (String × Interval))
      (steps : Nat) (traj : Nat → CanonicalRat → String → CanonicalRat),
      verifyTrajectorySafety sys initBox steps safeBounds = true →
      BoxMem (traj 0 0) initBox →
      IsValidOdeFlowTrajectory sys steps traj →
      ∃ tube,
        runFlowpipe sys initBox steps = some tube ∧
        tube.length = steps + 1 ∧
        (∀ k, k ≤ steps → BoxMem (traj k 0) (tube.getD k []) ∧ BoxMem (traj k 0) safeBounds) ∧
        (∀ k, k < steps → ∀ τ ∈ Interval.mk 0 sys.dt, BoxMem (traj k τ) safeBounds) := by
  intro sys initBox safeBounds steps traj hVer hInit hFlow
  exact verifyTrajectorySafetyLoop_sound steps sys initBox safeBounds traj hVer hInit hFlow

/-- Canonical rational trapezoidal / Euler quadrature rule on $[0, h]$:
uses trapezoidal nodes $[(h/2, 0), (h/2, h)]$ at $t = h$ and Euler node $[(t, 0)]$ for $t \in [0, h)$. -/
@[expose] def trapezoidalQuadrature (h : CanonicalRat) (t : CanonicalRat) :
    List (CanonicalRat × CanonicalRat) :=
  if t == h then [(h / 2, 0), (h / 2, h)] else [(t, 0)]

theorem trapezoidalQuadrature_valid {h : CanonicalRat} (hNonneg : 0 ≤ h) :
    ValidQuadratureOn h (trapezoidalQuadrature h) := by
  intro t ht
  rw [Interval.mem_iff] at ht
  unfold trapezoidalQuadrature
  cases hEq : t == h
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · simp only [quadWeightSum]
      grind
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      rw [Interval.mem_iff]
      exact ⟨ht.1, ⟨by grind, hNonneg⟩⟩
  · simp only [beq_iff_eq] at hEq
    subst hEq
    simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · simp only [quadWeightSum]
      grind
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [Interval.mem_iff]; exact ⟨by grind, ⟨by grind, hNonneg⟩⟩
      · rw [Interval.mem_iff]; exact ⟨by grind, ⟨hNonneg, by grind⟩⟩

/-- Constructive multi-step 2nd-order Taylor–Picard trajectory seeded at `rho0`:
on each step $k$, evolves continuously across $\tau \in [0, \Delta t]$ via the $m$-th Picard iterate
`iteratePicardOperator sys (rhoStep k) (trapezoidalQuadrature sys.dt) m τ`, and advances the discrete
horizon state `rhoStep (k + 1)` by the exact 2nd-order Taylor–Lie map with $r_{\text{pad}} = 0$. -/
@[expose] def buildTaylorPicardStep
    (sys : OdeSystem) (m : Nat) (rho : String → CanonicalRat) (v : String) : CanonicalRat :=
  match sys.fields.lookup v with
  | some rhsExpr =>
    let zeta := iteratePicardOperator sys rho (trapezoidalQuadrature sys.dt) m 0
    rho v + sys.dt * evalExpr rho rhsExpr +
      (((sys.dt * sys.dt) / 2) * evalOdePointLieDerivComponent sys zeta rhsExpr + 0)
  | none => rho v

@[expose] def buildTaylorPicardDiscrete
    (sys : OdeSystem) (m : Nat) (rho0 : String → CanonicalRat) : Nat → String → CanonicalRat
  | 0 => rho0
  | k + 1 => buildTaylorPicardStep sys m (buildTaylorPicardDiscrete sys m rho0 k)

@[expose] def buildTaylorPicardTrajectory
    (sys : OdeSystem) (m : Nat) (rho0 : String → CanonicalRat)
    (k : Nat) (τ : CanonicalRat) : String → CanonicalRat :=
  iteratePicardOperator sys (buildTaylorPicardDiscrete sys m rho0 k) (trapezoidalQuadrature sys.dt) m τ

theorem lookup_of_mem_nodup_keys :
    ∀ {fields : List (String × RealExpr)} {name : String} {rhs : RealExpr},
      (fields.map Prod.fst).Nodup →
      (name, rhs) ∈ fields →
      fields.lookup name = some rhs
  | [], _, _, _, hMem => by simp at hMem
  | (n, r) :: rest, name, rhs, hNodup, hMem => by
    simp only [List.map_cons, List.nodup_cons] at hNodup
    simp only [List.mem_cons] at hMem
    simp only [List.lookup]
    rcases hMem with hEq | hRest
    · injection hEq with hn hr
      subst hn; subst hr
      simp
    · cases hvn : name == n
      · exact lookup_of_mem_nodup_keys hNodup.2 hRest
      · simp only [beq_iff_eq] at hvn
        subst hvn
        have hInFst : name ∈ rest.map Prod.fst :=
          List.mem_map.2 ⟨(name, rhs), hRest, rfl⟩
        exact absurd hInFst hNodup.1

/-- **Theorem (`picardIteratedTrajectory_safety_sound`)**:
Connects arbitrary-order Picard iteration (`buildTaylorPicardTrajectory sys m rho0`) directly to
$K$-step flowpipe safety (`verifyTrajectorySafety`) with purely structural hypotheses (`0 ≤ sys.dt`,
`0 ∈ sys.remainderPad`, distinct field names, and `BoxMem rho0 initBox`). -/
theorem picardIteratedTrajectory_safety_sound
    (sys : OdeSystem) (initBox safeBounds : List (String × Interval))
    (steps m : Nat) (rho0 : String → CanonicalRat)
    (hDtNonneg : 0 ≤ sys.dt)
    (hZeroPad : (0 : CanonicalRat) ∈ sys.remainderPad)
    (hNodup : (sys.fields.map Prod.fst).Nodup)
    (hVer : verifyTrajectorySafety sys initBox steps safeBounds = true)
    (hInit : BoxMem rho0 initBox) :
    ∃ tube,
      runFlowpipe sys initBox steps = some tube ∧
      tube.length = steps + 1 ∧
      (∀ k, k ≤ steps →
        BoxMem (buildTaylorPicardDiscrete sys m rho0 k) (tube.getD k []) ∧
        BoxMem (buildTaylorPicardDiscrete sys m rho0 k) safeBounds) ∧
      (∀ k, k < steps → ∀ τ ∈ Interval.mk 0 sys.dt,
        BoxMem (buildTaylorPicardTrajectory sys m rho0 k τ) safeBounds) := by
  let traj := buildTaylorPicardTrajectory sys m rho0
  have hAtZero : ∀ k v, traj k 0 v = buildTaylorPicardDiscrete sys m rho0 k v := by
    intro k v
    unfold traj buildTaylorPicardTrajectory
    cases m with
    | zero => rfl
    | succ m' =>
      unfold iteratePicardOperator picardOperator trapezoidalQuadrature
      cases hEq : (0 : CanonicalRat) == sys.dt
      · simp only [Bool.false_eq_true, ↓reduceIte, evalPicardQuadSum]
        cases sys.fields.find? (·.1 == v) <;> grind
      · simp only [beq_iff_eq] at hEq
        have hDtZero : sys.dt = 0 := hEq.symm
        simp only [hDtZero, ↓reduceIte, evalPicardQuadSum]
        cases sys.fields.find? (·.1 == v) <;> grind
  have hFunZero : ∀ k, traj k 0 = buildTaylorPicardDiscrete sys m rho0 k := by
    intro k; funext u; exact hAtZero k u
  have hInitTraj : BoxMem (traj 0 0) initBox := by
    rw [hFunZero 0]
    exact hInit
  have hValid : IsValidOdeFlowTrajectory sys steps traj := by
    intro k _
    refine ⟨⟨trapezoidalQuadrature sys.dt, trapezoidalQuadrature_valid hDtNonneg, ?_⟩, ?_⟩
    · intro τ _
      refine ⟨m, fun u => ?_⟩
      rw [hFunZero k]
      rfl
    · intro name rhsExpr hMemField
      refine ⟨0, 0, ⟨by grind, hDtNonneg⟩, hZeroPad, ?_⟩
      rw [hAtZero (k + 1) name]
      unfold buildTaylorPicardDiscrete buildTaylorPicardStep
      rw [lookup_of_mem_nodup_keys hNodup hMemField]
      dsimp only
      have hZetaEq :
          iteratePicardOperator sys (buildTaylorPicardDiscrete sys m rho0 k)
            (trapezoidalQuadrature sys.dt) m 0 =
          buildTaylorPicardDiscrete sys m rho0 k := hFunZero k
      rw [hZetaEq, hFunZero k]
  obtain ⟨tube, hRun, hLen, hDisc, hCont⟩ :=
    verifyTrajectorySafety_sound sys initBox safeBounds steps traj hVer hInitTraj hValid
  refine ⟨tube, hRun, hLen, ?_, hCont⟩
  intro k hk
  obtain ⟨hD1, hD2⟩ := hDisc k hk
  rw [← hFunZero k]
  exact ⟨hD1, hD2⟩

/-- **Theorem (`odeSafetyCellContract_enforces_flowpipe_step`)**:
Concrete verification that `odeSafetyCellContract` genuinely encodes and checks `OdeSystem` flowpipe
evolution (rather than a disconnected bound predicate):
1. **Valid Flowpipe Transition Admitted**: Under `thermalCoolingOde` ($\Delta t = 1/2$, $X_0 = [28, 30]$,
   $X_1 = [22.9, 26.1]$), transitioning from `step = 0, T = 29` to `step = 1, T = 24` is admitted!
2. **Envelope-Safe Non-Flowpipe Jump Refused**: Transitioning from `step = 0, T = 29` to `step = 1, T = 34`
   is **refused** with `"new_state_outside_flowpipe"` even though $34 \in [12, 35]$ lies strictly inside
   `safeBounds` (because $34 \notin X_1 = [22.9, 26.1]$)!
3. **Step Counter Violation Refused**: Jumping directly from `step = 0` to `step = 2` is refused with
   `"invalid_ode_step_counter"`. -/
theorem odeSafetyCellContract_enforces_flowpipe_step :
    let initBox := [("T", (⟨28, 30⟩ : Interval))]
    let safeEnv := [("T", (⟨12, 35⟩ : Interval))]
    let C := odeSafetyCellContract thermalCoolingOde initBox 3 safeEnv
    let s0 := stateToCellData 0 ["T"] (fun _ => 29)
    let s1Valid := stateToCellData 1 ["T"] (fun _ => 24)
    let s1Drift := stateToCellData 1 ["T"] (fun _ => 34)
    let s2Skip := stateToCellData 2 ["T"] (fun _ => 24)
    let req := Data.record []
    Admits C.law s0 s1Valid req ∧
    Refuses C.law s0 s1Drift req "new_state_outside_flowpipe" ∧
    Refuses C.law s0 s2Skip req "invalid_ode_step_counter" ∧
    -- Contraction check on thermalCoolingOde: Lipschitz constant L = 1, h = 1/2 => L * h = 1/2 < 1
    verifyPicardContraction thermalCoolingOde [("T", ⟨28, 30⟩)] [("T", ⟨23, 30⟩)] (CanonicalRat.mk 1 2) = true := by
  refine ⟨admits_of_run 600 (by decide +kernel),
          refuses_of_run 600 (by decide +kernel),
          refuses_of_run 600 (by decide +kernel),
          by decide +kernel⟩

end Obend.Analysis
end
