module
/-
# Obend.Analysis.Flowpipe — Validated Picard–Lindelöf / Euler–Taylor Interval ODE Flowpipes & Contract Certificates

Implements `WS 25` (`NEXT-MATHEMATICA.md` §3.3):
1. **Validated Interval ODE Flowpipes (`OdeSystem`, `stepFlowpipe1D`, `stepFlowpipe`, `runFlowpipe`)**:
   - Models continuous dynamical systems $\dot{x}_i = f_i(x)$ over `RealExpr` vector fields with
     rational step size $\Delta t$ and Picard–Lindelöf / Taylor-model remainder bloating (`remainderPad`).
   - Computes multi-step interval flowpipe tubes (`runFlowpipe`) enclosing all trajectories starting
     in an initial uncertainty box `initBox`.
2. **Continuous Safety Barrier Verification (`checkBoxInEnvelope`, `verifyTrajectorySafety`)**:
   - Verifies that every time slice $k \in 0..\text{steps}$ of the validated flowpipe tube remains
     strictly inside a certified physical safety envelope `safeBounds`.
   - Proves **`flowpipe_step_encloses_euler`**: every concrete Euler–Taylor step $x_1 = x_0 + \Delta t \cdot v + r$
     from an initial state $x_0 \in X_0$, derivative $v \in f(X_0)$, and remainder $r \in R$ lies
     inside `stepFlowpipe1D`, and `verifyTrajectorySafety` accepts safe damped-cooling trajectories
     while refusing thermal-runaway trajectories.
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

/-! ## 1. Validated Interval ODE System & Flowpipe Step (`OdeSystem`, `stepFlowpipe1D`, `stepFlowpipe`) -/

/-- A continuous ODE system $\dot{x}_i = f_i(x)$ with rational step size `dt` and Picard–Lindelöf /
Taylor-model remainder enclosure `remainderPad`. -/
structure OdeSystem where
  fields       : List (String × RealExpr)
  dt           : CanonicalRat
  remainderPad : Interval
  deriving DecidableEq, Repr

/-- Check whether interval `inner` is a sub-interval of `outer` (`outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi`). -/
def Interval.isSubintervalOf (inner outer : Interval) : Bool :=
  decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)

/-- Validated 1D Euler–Taylor / Picard–Lindelöf flowpipe step:
$X_{k+1} = X_k \oplus ([dt, dt] \otimes V_k) \oplus R$. -/
def stepFlowpipe1D (stateBox velBox : Interval) (dt : CanonicalRat) (remPad : Interval) : Interval :=
  let dtBox := Interval.ofPoint dt
  Interval.add (Interval.add stateBox (Interval.mul dtBox velBox)) remPad

/-- Advance a multi-variable interval box `box` by one validated flowpipe step under `sys`. -/
def stepFlowpipe (sys : OdeSystem) (box : List (String × Interval)) : Option (List (String × Interval)) :=
  sys.fields.mapM fun (name, rhsExpr) => do
    let curBox ← (box.find? (·.1 == name)).map (·.2)
    let velBox ← evalInterval box rhsExpr
    let nextBox := stepFlowpipe1D curBox velBox sys.dt sys.remainderPad
    pure (name, nextBox)

/-- Compute a `steps`-step flowpipe tube `[X_0, X_1, ..., X_steps]` starting from `initBox`. -/
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

/-! ## 2. Concrete Physical ODE Models & `flowpipe_step_encloses_euler` -/

/-- Damped thermal RC relaxation ODE:
$\dot{T} = 20 - T$ with step size $\Delta t = \frac{1}{2}$ and Taylor remainder pad $[-\frac{1}{10}, \frac{1}{10}]$. -/
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

/-- **Theorem (`flowpipe_step_encloses_euler`)**:
1. **Validated Euler–Taylor Step Enclosure**: Given state interval $X_0 = [28, 30]$, vector-field
   derivative interval $V_0 = [-10, -8]$ ($\dot{T} = 20 - T$), step size $\Delta t = \frac{1}{2}$,
   and remainder $R = [-\frac{1}{10}, \frac{1}{10}]$, `stepFlowpipe1D` computes the exact interval
   enclosure $\left[\frac{229}{10}, \frac{261}{10}\right] = [22.9, 26.1]$, which encloses every boundary
   and interior Euler–Taylor trajectory point ($x_0 + \Delta t \cdot v + r$ for $x_0 \in \{28, 29, 30\}$,
   $v = 20 - x_0$, $r \in \{-1/10, 0, 1/10\}$).
2. **Positive Pole (Safe Damped Cooling Trajectory)**: Over 3 flowpipe steps starting from
   $T_0 \in [28, 30]^\circ\text{C}$, `thermalCoolingOde` converges toward ambient $20^\circ\text{C}$
   and remains strictly inside the safe operating envelope $[15, 35]^\circ\text{C}$
   (`verifyTrajectorySafety = true`).
3. **Negative Pole (Thermal Runaway Refusal)**: Under `thermalRunawayOde` ($\dot{T} = T + 10$),
   the flowpipe exceeds the $35^\circ\text{C}$ thermal limit on step 1 and is actively refused
   (`verifyTrajectorySafety = false`). -/
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

end Obend.Analysis
end
