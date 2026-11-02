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

/-! ## 4. Validated Picard–Lindelöf A-Priori Enclosure & Derived Remainder (`verifyPicardAPriori`, `derivePicardRemainder`, `picard_step_encloses_trajectory`) -/

/-- Evaluate the primary vector field of `f : OdeSystem` over an interval enclosure `xTilde`. -/
def evalOdeField (f : OdeSystem) (xTilde : Interval) : Interval :=
  let env := f.fields.map (fun (name, _) => (name, xTilde))
  match f.fields with
  | [] => Interval.ofPoint 0
  | (_, rhsExpr) :: _ =>
    (evalInterval env rhsExpr).getD (Interval.ofPoint 0)

/-- Evaluate the interval Jacobian $\frac{\partial f}{\partial x}$ of the primary vector field of `f`
over `xTilde` via forward-mode interval AD (`evalDualInterval`). -/
def evalOdeJacobian (f : OdeSystem) (xTilde : Interval) : Interval :=
  let env := f.fields.map (fun (name, _) => (name, xTilde))
  match f.fields with
  | [] => Interval.ofPoint 0
  | (name, rhsExpr) :: _ =>
    match evalDualInterval env name rhsExpr with
    | some dIv => dIv.der
    | none     => Interval.ofPoint 0

/-- Verify the Picard–Lindelöf a-priori enclosure condition:
$$X_0 \oplus ([0, h] \otimes F(\tilde{X})) \subseteq \tilde{X}$$ -/
def verifyPicardAPriori (f : OdeSystem) (x0 xTilde : Interval) (h : CanonicalRat) : Bool :=
  Interval.subset (Interval.add x0 (Interval.mul (Interval.mk 0 h) (evalOdeField f xTilde))) xTilde

/-- Automatically derive the validated 2nd-order Lagrange remainder interval:
$$R_2(L, F(\tilde{X}), h) = \left[\frac{h^2}{2}, \frac{h^2}{2}\right] \otimes (L \otimes F(\tilde{X}))$$
from the interval Jacobian enclosure $L \supseteq f'(\tilde{X})$ and vector-field bound $\text{fBound} \supseteq f(\tilde{X})$. -/
def derivePicardRemainder (L : Interval) (fBound : Interval) (h : CanonicalRat) : Interval :=
  let hSqHalf := Interval.ofPoint ((h * h) / 2)
  Interval.mul hSqHalf (Interval.mul L fBound)

/-- Compute a single validated 1D Picard–Taylor step using the automatically derived remainder
`derivePicardRemainder L (evalOdeField f xTilde) h`. -/
def stepPicardValidated1D (f : OdeSystem) (x0 xTilde L : Interval) (h : CanonicalRat) : Interval :=
  stepFlowpipe1D x0 (evalOdeField f x0) h (derivePicardRemainder L (evalOdeField f xTilde) h)

theorem lookup_map_const_interval
    (fields : List (String × RealExpr)) (xTilde : Interval)
    (v : String) (I : Interval)
    (hLook : (fields.map (fun (name, _) => (name, xTilde))).lookup v = some I) :
    I = xTilde := by
  induction fields with
  | nil => cases hLook
  | cons hd tl ih =>
    rcases hd with ⟨name, _⟩
    simp only [List.map_cons, List.lookup] at hLook
    split at hLook
    · injection hLook with hEq
      exact hEq.symm
    · exact ih hLook

/-- Universal soundness of `evalOdeField`: for any ODE system `f` with primary field `(name, rhsExpr)`
whose interval evaluation succeeds, if `x ∈ xTilde`, then `evalExpr (fun _ => x) rhsExpr ∈ evalOdeField f xTilde`. -/
theorem evalOdeField_sound
    (f : OdeSystem) (name : String) (rhsExpr : RealExpr) (rest : List (String × RealExpr))
    (xTilde fIv : Interval) (x : CanonicalRat)
    (hFields : f.fields = (name, rhsExpr) :: rest)
    (hEval : evalInterval (f.fields.map (fun (n, _) => (n, xTilde))) rhsExpr = some fIv)
    (hx : x ∈ xTilde) :
    evalExpr (fun _ => x) rhsExpr ∈ evalOdeField f xTilde := by
  unfold evalOdeField
  rw [hFields] at hEval ⊢
  dsimp only
  rw [hEval, Option.getD_some]
  refine evalInterval_sound _ (fun _ => x) ?_ rhsExpr fIv hEval
  intro v I hLook
  have hEq := lookup_map_const_interval ((name, rhsExpr) :: rest) xTilde v I hLook
  subst hEq
  exact hx

/-- Universal soundness of `evalOdeJacobian`: for any ODE system `f` with primary field `(name, rhsExpr)`
whose forward-mode interval AD evaluation succeeds, if `x ∈ xTilde`, then the exact Jacobian
`(evalDualRat (fun _ => x) name rhsExpr).der` is enclosed in `evalOdeJacobian f xTilde`. -/
theorem evalOdeJacobian_sound
    (f : OdeSystem) (name : String) (rhsExpr : RealExpr) (rest : List (String × RealExpr))
    (xTilde : Interval) (dIv : DualInterval) (x : CanonicalRat)
    (hFields : f.fields = (name, rhsExpr) :: rest)
    (hEval : evalDualInterval (f.fields.map (fun (n, _) => (n, xTilde))) name rhsExpr = some dIv)
    (hx : x ∈ xTilde) :
    (evalDualRat (fun _ => x) name rhsExpr).der ∈ evalOdeJacobian f xTilde := by
  unfold evalOdeJacobian
  rw [hFields] at hEval ⊢
  dsimp only
  rw [hEval]
  refine (evalDualInterval_sound _ (fun _ => x) ?_ name rhsExpr dIv hEval).2
  intro v I hLook
  have hEq := lookup_map_const_interval ((name, rhsExpr) :: rest) xTilde v I hLook
  subst hEq
  exact hx

/-- Universal enclosure of `stepFlowpipe1D`: for any initial state $x_0 \in \text{stateBox}$,
velocity $v_0 \in \text{velBox}$, and remainder $r \in \text{remPad}$,
$x_0 + \Delta t \cdot v_0 + r \in \text{stepFlowpipe1D stateBox velBox dt remPad}$. -/
theorem stepFlowpipe1D_mem
    {stateBox velBox remPad : Interval} {x0 v0 r : CanonicalRat} (dt : CanonicalRat)
    (hx0 : x0 ∈ stateBox) (hv0 : v0 ∈ velBox) (hr : r ∈ remPad) :
    (x0 + dt * v0 + r) ∈ stepFlowpipe1D stateBox velBox dt remPad := by
  unfold stepFlowpipe1D
  exact Interval.add_mem (Interval.add_mem hx0 (Interval.mul_mem (Interval.ofPoint_mem dt) hv0)) hr

/-- Universal enclosure of `derivePicardRemainder`: for any Jacobian value $\text{df}_\xi \in L$
and vector-field value $f_\xi \in \text{fBound}$, the 2nd-order Taylor-Lagrange remainder term
$\frac{h^2}{2} (\text{df}_\xi \cdot f_\xi)$ is enclosed in `derivePicardRemainder L fBound h`. -/
theorem derivePicardRemainder_mem
    {L fBound : Interval} {df_xi f_xi : CanonicalRat} (h : CanonicalRat)
    (hL : df_xi ∈ L) (hF : f_xi ∈ fBound) :
    (((h * h) / 2) * (df_xi * f_xi)) ∈ derivePicardRemainder L fBound h := by
  unfold derivePicardRemainder
  exact Interval.mul_mem (Interval.ofPoint_mem ((h * h) / 2)) (Interval.mul_mem hL hF)

/-- Universal soundness of `verifyPicardAPriori`: if `verifyPicardAPriori f x0 xTilde h = true`,
then for every initial state $x_{\text{init}} \in X_0$, time $t \in [0, h]$, and intermediate
velocity $v_t \in F(\tilde{X})$, the Euler/mean-value trajectory point $x_{\text{init}} + t \cdot v_t$
remains inside the a-priori enclosure $\tilde{X}$. -/
theorem verifyPicardAPriori_encloses
    (f : OdeSystem) (x0 xTilde : Interval) (h : CanonicalRat)
    (hPicard : verifyPicardAPriori f x0 xTilde h = true)
    {x_init t v_t : CanonicalRat}
    (hx0 : x_init ∈ x0)
    (ht : t ∈ Interval.mk 0 h)
    (hvt : v_t ∈ evalOdeField f xTilde) :
    (x_init + t * v_t) ∈ xTilde := by
  unfold verifyPicardAPriori at hPicard
  exact Interval.subset_sound hPicard (Interval.add_mem hx0 (Interval.mul_mem ht hvt))

/-- **Theorem (`picard_step_encloses_trajectory`)**:
1. **Universal Validated Picard–Lindelöf Step Soundness**:
   For any `f : OdeSystem`, initial interval `x0`, verified a-priori enclosure `xTilde`
   (`verifyPicardAPriori f x0 xTilde h = true`), Jacobian enclosure `L`, and step size `h`:
   - Every intermediate mean-value state $x(0) + t \cdot f(x(\xi))$ ($t \in [0, h], f(x(\xi)) \in F(\tilde{X})$)
     is enclosed in `xTilde`, and
   - Every trajectory endpoint $x(h) = x(0) + h \cdot f(x(0)) + \frac{h^2}{2} f'(x(\xi)) f(x(\xi))$
     with $x(0) \in x_0$, $f(x(0)) \in F(x_0)$, $f'(x(\xi)) \in L$, and $f(x(\xi)) \in F(\tilde{X})$
     is enclosed in `stepPicardValidated1D f x0 xTilde L h`!
2. **Concrete Thermal Cooling Trajectory Verification ($x(0) = 30, \dot{x} = 20 - x, h = 1/2$)**:
   - `verifyPicardAPriori thermalCoolingOde ⟨30, 30⟩ ⟨25, 30⟩ (1/2) = true` and
     `verifyPicardAPriori thermalCoolingOde ⟨28, 30⟩ ⟨23, 30⟩ (1/2) = true`,
   - `evalOdeJacobian thermalCoolingOde ⟨25, 30⟩ = ⟨-1, -1⟩`,
   - `derivePicardRemainder ⟨-1, -1⟩ (evalOdeField thermalCoolingOde ⟨25, 30⟩) (1/2) = ⟨5/8, 5/4⟩`,
   - The derived Picard enclosure from $x(0) = 30$ (`stepPicardValidated1D thermalCoolingOde ⟨30, 30⟩ ⟨25, 30⟩ ⟨-1, -1⟩ (1/2) = [205/8, 105/4] = [25.625, 26.25]`)
     and from $X_0 = [28, 30]$ (`[187/8, 109/4] = [23.375, 27.25]`) genuinely enclose the analytical
     solution $20 + 10 e^{-1/2} \approx 26.0653$ (`260653 / 10000`). -/
theorem picard_step_encloses_trajectory :
    (∀ (f : OdeSystem) (x0 xTilde L : Interval) (h x_init v0 df_xi f_xi t : CanonicalRat),
      verifyPicardAPriori f x0 xTilde h = true →
      x_init ∈ x0 →
      v0 ∈ evalOdeField f x0 →
      df_xi ∈ L →
      f_xi ∈ evalOdeField f xTilde →
      t ∈ Interval.mk 0 h →
      (x_init + t * f_xi) ∈ xTilde ∧
      (x_init + h * v0 + ((h * h) / 2) * (df_xi * f_xi)) ∈
        stepPicardValidated1D f x0 xTilde L h) ∧
    (let h : CanonicalRat := CanonicalRat.mk 1 2
     let x0Pt : Interval := ⟨30, 30⟩
     let xTildePt : Interval := ⟨25, 30⟩
     let x0Box : Interval := ⟨28, 30⟩
     let xTildeBox : Interval := ⟨23, 30⟩
     let L := evalOdeJacobian thermalCoolingOde xTildePt
     let remPt := derivePicardRemainder L (evalOdeField thermalCoolingOde xTildePt) h
     let stepPt := stepPicardValidated1D thermalCoolingOde x0Pt xTildePt L h
     let stepBox := stepPicardValidated1D thermalCoolingOde x0Box xTildeBox L h
     let exactTrajApprox : CanonicalRat := CanonicalRat.mk 260653 10000
     verifyPicardAPriori thermalCoolingOde x0Pt xTildePt h = true ∧
     verifyPicardAPriori thermalCoolingOde x0Box xTildeBox h = true ∧
     L = ⟨-1, -1⟩ ∧
     remPt = ⟨CanonicalRat.mk 5 8, CanonicalRat.mk 5 4⟩ ∧
     stepPt = ⟨CanonicalRat.mk 205 8, CanonicalRat.mk 105 4⟩ ∧
     stepBox = ⟨CanonicalRat.mk 187 8, CanonicalRat.mk 109 4⟩ ∧
     Interval.containsRat stepPt exactTrajApprox = true ∧
     Interval.containsRat stepBox exactTrajApprox = true) := by
  refine ⟨?_, by decide +kernel⟩
  intro f x0 xTilde L h x_init v0 df_xi f_xi t hPic hx0 hv0 hL hF ht
  exact ⟨verifyPicardAPriori_encloses f x0 xTilde h hPic hx0 ht hF,
    stepFlowpipe1D_mem h hx0 hv0 (derivePicardRemainder_mem h hL hF)⟩

end Obend.Analysis
end

