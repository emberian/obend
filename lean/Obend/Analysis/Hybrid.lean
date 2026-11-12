module
/-
# Obend.Analysis.Hybrid — Hybrid Automata Coupling Continuous ODE Flowpipes with Discrete Guard Transitions & `CellContract`

Implements `WS 29.3` (`NEXT-MATHEMATICA.md` §3.3 & §5):
1. **Hybrid Automata (`HybridMode`, `AffineResetMap`, `HybridJump`, `HybridAutomaton`, `HybridState`)**:
   - Couples continuous interval/Taylor ODE flowpipes (`OdeSystem`) inside discrete operating modes
     with guarded mode transitions (`guardBounds`), affine state reset maps
     ($X' := \alpha X \oplus \beta$), mode invariants (`invariantBounds`), and a global physical
     safety envelope (`safeEnvelope`).
2. **Certified Hybrid Trajectory Verification (`stepHybridFlow`, `stepHybridJump?`, `runHybridSchedule`, `verifyHybridScheduleSafety`)**:
   - Executes arbitrary schedules of continuous flow steps (`.flowStep`) and discrete mode switches
     (`.jumpTo targetMode`), enforcing mode invariants, guard enablement, reset enclosure, and global
     safety bounds at every continuous slice and discrete jump.
3. **Inductive `CellContract` Soundness (`hybrid_flowpipe_safety_admits_contract`)**:
   - Proves that a verified hybrid automaton schedule (`heating` $\to$ `cooling` with hysteresis
     guard and reset map) remains strictly inside the certified safety envelope, refuses out-of-guard
     or thermal-runaway transitions, and preserves the `Obend.Law.CellContract` invariant across
     arbitrary multi-step `CellTrace` executions (`0 sorryAx`).
-/
public import Obend.Analysis.TaylorModel
public import Obend.Judge.Class
public import Obend.Tactic.Tooth
public section

namespace Obend.Analysis
open Obend.Core.Data (Data)
open Obend.Law (CellContract Holds CellTrace cellContract_trace_sound)
set_option autoImplicit false

/-! ## 1. Hybrid Automaton Syntax & Semantics (`HybridMode`, `HybridJump`, `HybridAutomaton`) -/

/-- Discrete operating mode of a hybrid dynamical system:
* `modeId`: discrete mode identifier (e.g., `"heating"`, `"cooling"`),
* `ode`: continuous vector field $\dot{x} = f_{\text{mode}}(x)$ with step size `dt` and remainder pad,
* `invariantBounds`: domain invariant $X \subseteq \text{Inv}(\text{mode})$ that must hold throughout the mode. -/
structure HybridMode where
  modeId          : String
  ode             : OdeSystem
  invariantBounds : List (String × Interval)
  deriving @[expose] DecidableEq, Repr

/-- Affine discrete reset map $x'_i := \alpha_i x_i + \beta_i$ applied across a discrete mode switch. -/
structure AffineResetMap where
  resets : List (String × CanonicalRat × CanonicalRat)
  deriving @[expose] DecidableEq, Repr

/-- Guarded discrete transition between two `HybridMode`s:
* `fromMode`, `toMode`: source and target discrete mode identifiers,
* `guardBounds`: guard region $G \subseteq \mathbb{R}^n$ that must enclose the pre-jump continuous box,
* `resetMap`: affine reset map applied upon taking the discrete transition. -/
structure HybridJump where
  fromMode    : String
  toMode      : String
  guardBounds : List (String × Interval)
  resetMap    : AffineResetMap
  deriving @[expose] DecidableEq, Repr

/-- Complete hybrid automaton coupling continuous `OdeSystem` modes with discrete guarded jumps. -/
structure HybridAutomaton where
  modes        : List HybridMode
  jumps        : List HybridJump
  safeEnvelope : List (String × Interval)
  deriving @[expose] DecidableEq, Repr

/-- Hybrid state pairing a discrete `modeId` with a continuous interval enclosure `box`. -/
structure HybridState where
  modeId : String
  box    : List (String × Interval)
  deriving @[expose] DecidableEq, Repr

/-- Discrete or continuous action in a hybrid execution schedule. -/
inductive HybridAction where
  | flowStep
  | jumpTo (targetMode : String)
  deriving @[expose] DecidableEq, Repr

/-- Look up a `HybridMode` by `modeId` via direct structural recursion. -/
@[expose] def findHybridMode? (targetId : String) : List HybridMode → Option HybridMode
  | [] => none
  | m :: ms => if m.modeId == targetId then some m else findHybridMode? targetId ms

/-- Look up a `HybridJump` from `srcMode` to `dstMode` via direct structural recursion. -/
@[expose] def findHybridJump? (srcMode dstMode : String) : List HybridJump → Option HybridJump
  | [] => none
  | j :: js =>
    if j.fromMode == srcMode && j.toMode == dstMode then some j
    else findHybridJump? srcMode dstMode js

/-- Apply an `AffineResetMap` ($X'_i = \alpha_i X_i \oplus [\beta_i, \beta_i]$) to a continuous box. -/
@[expose] def applyAffineReset (rm : AffineResetMap) : List (String × Interval) → List (String × Interval)
  | [] => []
  | (name, iv) :: rest =>
    let iv' :=
      match rm.resets.find? (fun (n, _, _) => n == name) with
      | some (_, scale, offset) =>
        Interval.add (Interval.mul (Interval.ofPoint scale) iv) (Interval.ofPoint offset)
      | none => iv
    (name, iv') :: applyAffineReset rm rest

/-- Check that every interval in `box` is non-inverted (`iv.lo ≤ iv.hi`). -/
@[expose] def checkBoxNonInverted (box : List (String × Interval)) : Bool :=
  box.all (fun (_, iv) => decide (iv.lo ≤ iv.hi))

/-- Execute one continuous flowpipe step inside the active mode `st.modeId`, verifying that the
pre-state `st.box`, the continuous-time rough enclosure `xTildeBox` (covering all $t \in [0, \Delta t]$),
and the post-state `nextBox` all satisfy the mode invariant and global `safeEnvelope`. -/
@[expose] def stepHybridFlow (aut : HybridAutomaton) (st : HybridState) : Option HybridState := do
  let mode ← findHybridMode? st.modeId aut.modes
  if !checkBoxNonInverted st.box ||
     !checkBoxInEnvelope st.box mode.invariantBounds ||
     !checkBoxInEnvelope st.box aut.safeEnvelope then
    none
  else
    let xTildeBox ← inferPicardAPrioriBox mode.ode st.box
    if !checkBoxInEnvelope xTildeBox mode.invariantBounds ||
       !checkBoxInEnvelope xTildeBox aut.safeEnvelope then
      none
    else
      let nextBox ← stepPicardValidated mode.ode st.box xTildeBox mode.ode.dt
      if checkBoxInEnvelope nextBox mode.invariantBounds && checkBoxInEnvelope nextBox aut.safeEnvelope then
        some { modeId := st.modeId, box := nextBox }
      else
        none

/-- Execute a guarded discrete mode switch from `st.modeId` to `targetMode`, verifying that:
1. `st.box` is non-inverted and lies inside `jump.guardBounds`,
2. the post-reset box `applyAffineReset jump.resetMap st.box` lies inside the target mode's
   `invariantBounds` and `aut.safeEnvelope`. -/
@[expose] def stepHybridJump? (aut : HybridAutomaton) (st : HybridState) (targetMode : String) : Option HybridState := do
  let jump ← findHybridJump? st.modeId targetMode aut.jumps
  let dstMode ← findHybridMode? targetMode aut.modes
  if !checkBoxNonInverted st.box || !checkBoxInEnvelope st.box jump.guardBounds then
    none
  else
    let resetBox := applyAffineReset jump.resetMap st.box
    if checkBoxInEnvelope resetBox dstMode.invariantBounds && checkBoxInEnvelope resetBox aut.safeEnvelope then
      some { modeId := targetMode, box := resetBox }
    else
      none

/-- Execute a single `HybridAction` (`.flowStep` or `.jumpTo targetMode`). -/
@[expose] def stepHybridAction (aut : HybridAutomaton) (st : HybridState) : HybridAction → Option HybridState
  | .flowStep          => stepHybridFlow aut st
  | .jumpTo targetMode => stepHybridJump? aut st targetMode

/-- Structural recursion helper for `runHybridSchedule`. -/
@[expose] def runHybridScheduleLoop (aut : HybridAutomaton) : List HybridAction → HybridState → Option (List HybridState)
  | [], st =>
    match findHybridMode? st.modeId aut.modes with
    | some mode =>
      if checkBoxNonInverted st.box &&
         checkBoxInEnvelope st.box mode.invariantBounds &&
         checkBoxInEnvelope st.box aut.safeEnvelope then
        some [st]
      else none
    | none => none
  | act :: rest, st => do
    let nextState ← stepHybridAction aut st act
    let restTube ← runHybridScheduleLoop aut rest nextState
    pure (st :: restTube)

/-- Run a sequence of `HybridAction`s from `initState`, returning the full hybrid state tube
if every continuous flow step and discrete jump is safe and guard-enabled. -/
@[expose] def runHybridSchedule (aut : HybridAutomaton) (initState : HybridState) (schedule : List HybridAction) : Option (List HybridState) :=
  runHybridScheduleLoop aut schedule initState

/-- Verify that a hybrid execution schedule from `initState` is valid and stays within `aut.safeEnvelope`. -/
@[expose] def verifyHybridScheduleSafety
    (aut : HybridAutomaton)
    (initState : HybridState)
    (schedule : List HybridAction) : Bool :=
  match runHybridSchedule aut initState schedule with
  | some tube => tube.all (fun st => checkBoxInEnvelope st.box aut.safeEnvelope)
  | none      => false

/-! ## 2. Concrete Thermostat Hybrid Automata & `hybrid_flowpipe_safety_admits_contract` -/

/-- Dual-mode thermostat / power-stage thermal hybrid automaton (damped RC cooling):
* Mode `"heating"`: $\dot{T} = 4$ with $\Delta t = 1$, remainder $[-1/10, 1/10]$, invariant $T \in [15, 32]^\circ\text{C}$.
* Mode `"cooling"`: damped cooling `thermalCoolingOde` ($\dot{T} = 20 - T$, $\Delta t = 1/2$), invariant $T \in [15, 35]^\circ\text{C}$.
* Guarded jump `"heating" → "cooling"`: enabled when $T \in [27, 32]^\circ\text{C}$, with reset map $T' := T - 1$ (active coolant valve purge).
* Global safety envelope: $T \in [15, 35]^\circ\text{C}$. -/
@[expose] def thermostatHybridAutomaton : HybridAutomaton where
  modes :=
    [ { modeId := "heating"
      , ode :=
          { fields       := [("T", .const 4)]
          , dt           := 1
          , remainderPad := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩ }
      , invariantBounds := [("T", ⟨15, 32⟩)] }
    , { modeId := "cooling"
      , ode := thermalCoolingOde
      , invariantBounds := [("T", ⟨15, 35⟩)] } ]
  jumps :=
    [ { fromMode    := "heating"
      , toMode      := "cooling"
      , guardBounds := [("T", ⟨27, 32⟩)]
      , resetMap    := { resets := [("T", (1, -1))] } } ]
  safeEnvelope := [("T", ⟨15, 35⟩)]

/-- Dual-mode constant-rate thermostat hybrid automaton (`"thermostat"`):
* Mode `"heating"`: $\dot{T} = 4$ with $\Delta t = 1$, invariant $T \in [15, 32]^\circ\text{C}$.
* Mode `"cooling"`: $\dot{T} = -2$ with $\Delta t = 1$, invariant $T \in [15, 35]^\circ\text{C}$.
* Guarded jump `"heating" → "cooling"`: guard $T \in [27, 32]^\circ\text{C}$, affine reset $T' := T - 1$.
* Global safety envelope: $T \in [15, 35]^\circ\text{C}$. -/
@[expose] def thermostatLinearAutomaton : HybridAutomaton where
  modes :=
    [ { modeId := "heating"
      , ode :=
          { fields       := [("T", .const 4)]
          , dt           := 1
          , remainderPad := Interval.ofPoint 0 }
      , invariantBounds := [("T", ⟨15, 32⟩)] }
    , { modeId := "cooling"
      , ode :=
          { fields       := [("T", .const (-2))]
          , dt           := 1
          , remainderPad := Interval.ofPoint 0 }
      , invariantBounds := [("T", ⟨15, 35⟩)] } ]
  jumps :=
    [ { fromMode    := "heating"
      , toMode      := "cooling"
      , guardBounds := [("T", ⟨27, 32⟩)]
      , resetMap    := { resets := [("T", (1, -1))] } } ]
  safeEnvelope := [("T", ⟨15, 35⟩)]

/-- **Theorem (`hybrid_flowpipe_safety_admits_contract`)**:
1. **Certified Hybrid Flow + Discrete Switch (Positive Pole)**:
   Starting in mode `"heating"` with $T_0 \in [24, 26]^\circ\text{C}$, executing:
   - `.flowStep` (heats to $[27.9, 30.1]^\circ\text{C} \subseteq [27, 32]^\circ\text{C}$ guard),
   - `.jumpTo "cooling"` (guard satisfied; reset map cools to $[26.9, 29.1]^\circ\text{C}$),
   - `.flowStep` and `.flowStep` (damped cooling toward $20^\circ\text{C}$)
   is accepted (`verifyHybridScheduleSafety = true`) and remains strictly inside $[15, 35]^\circ\text{C}$.
2. **Premature / Out-of-Guard Switch & Runaway Refusal (Negative Poles)**:
   - Attempting `.jumpTo "cooling"` immediately at $T_0 \in [24, 26]^\circ\text{C}$ (below the
     $[27, 32]^\circ\text{C}$ guard threshold) is refused (`verifyHybridScheduleSafety = false`).
   - Staying in `"heating"` for 3 consecutive steps without switching to `"cooling"` breaches the
     `"heating"` mode invariant ceiling $32^\circ\text{C}$ and is refused (`verifyHybridScheduleSafety = false`).
3. **Inductive `CellContract` Trace Soundness**:
   For any multi-step `CellTrace` governed by `odeSafetyCellContract sys initBox horizon safeBounds`
   from an initial state satisfying `Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s₀`,
   the final state `s_final` satisfies `Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s_final`. -/
theorem hybrid_flowpipe_safety_admits_contract
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval))
    (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s₀)
    (h_tr : CellTrace (odeSafetyCellContract sys initBox horizon safeBounds).law s₀ steps s_final) :
    let initSt : HybridState := { modeId := "heating", box := [("T", ⟨24, 26⟩)] }
    let validSchedule : List HybridAction :=
      [.flowStep, .jumpTo "cooling", .flowStep, .flowStep]
    let prematureJumpSchedule : List HybridAction :=
      [.jumpTo "cooling", .flowStep]
    let unswitchedOverheatSchedule : List HybridAction :=
      [.flowStep, .flowStep, .flowStep]
    verifyHybridScheduleSafety thermostatHybridAutomaton initSt validSchedule = true ∧
    verifyHybridScheduleSafety thermostatHybridAutomaton initSt prematureJumpSchedule = false ∧
    verifyHybridScheduleSafety thermostatHybridAutomaton initSt unswitchedOverheatSchedule = false ∧
    Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s_final := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact cellContract_trace_sound
    (odeSafetyCellContract sys initBox horizon safeBounds) s₀ s_final steps h_init h_tr

/-! ## 3. Inner-System Seam Weld: `HybridProblem` / `HybridCert` `Core.Data` Codecs & `hybridFlowpipeFormat` (`"hybrid-flowpipe@1"`) -/

/-- Encode an `Int` deterministically as `Obend.Core.Data`. -/
@[expose] def intToData : Int → Data
  | .ofNat n   => .variant "pos" (.natural n)
  | .negSucc n => .variant "neg" (.natural n)

/-- Decode an `Int` deterministically from `Obend.Core.Data`. -/
@[expose] def intOfData? : Data → Option Int
  | .variant "pos" (.natural n) => some (.ofNat n)
  | .variant "neg" (.natural n) => some (.negSucc n)
  | _                           => none

theorem intOfData_toData (i : Int) : intOfData? (intToData i) = some i := by
  cases i <;> rfl

/-- Encode a `CanonicalRat` deterministically as `Obend.Core.Data`. -/
@[expose] def ratToData (q : CanonicalRat) : Data :=
  .record [("num", intToData q.num), ("den", .natural q.den)]

/-- Decode a `CanonicalRat` deterministically from `Obend.Core.Data` (requiring reduced positive `den`). -/
@[expose] def ratOfData? : Data → Option CanonicalRat
  | .record [("num", numData), ("den", .natural den)] => do
    let num ← intOfData? numData
    if den == 0 then none
    else
      let q := CanonicalRat.mk num den
      if decide (q.num = num ∧ q.den = den) then some q else none
  | _ => none

theorem ratOfData_toData (q : CanonicalRat) : ratOfData? (ratToData q) = some q := by
  unfold ratToData ratOfData?
  simp only [intOfData_toData, bind, Option.bind]
  have hDenNe : (q.den == 0) = false := by
    cases h : q.den == 0
    · rfl
    · simp only [beq_iff_eq] at h
      exact absurd h (Nat.ne_of_gt q.den_pos)
  have hMk : CanonicalRat.mk q.num q.den = q := Rat.mkRat_self q
  simp [hDenNe, hMk]

/-- Deterministic `Obend.Core.Data` encoding of `Interval`. -/
@[expose] def Interval.toData (iv : Interval) : Data :=
  .record [("lo", ratToData iv.lo), ("hi", ratToData iv.hi)]

/-- Deterministic `Obend.Core.Data` decoding of `Interval`. -/
@[expose] def Interval.ofData? : Data → Option Interval
  | .record [("lo", loD), ("hi", hiD)] => do
    let lo ← ratOfData? loD
    let hi ← ratOfData? hiD
    pure ⟨lo, hi⟩
  | _ => none

theorem Interval.ofData_toData (iv : Interval) :
    Interval.ofData? iv.toData = some iv := by
  cases iv
  simp [Interval.toData, Interval.ofData?, ratOfData_toData]

/-- Deterministic `Obend.Core.Data` encoding of `RealExpr`. -/
@[expose] def RealExpr.toData : RealExpr → Data
  | .const c => .variant "const" (ratToData c)
  | .var v   => .variant "var" (.label v)
  | .add l r => .variant "add" (.record [("lhs", l.toData), ("rhs", r.toData)])
  | .sub l r => .variant "sub" (.record [("lhs", l.toData), ("rhs", r.toData)])
  | .mul l r => .variant "mul" (.record [("lhs", l.toData), ("rhs", r.toData)])
  | .sqr a   => .variant "sqr" a.toData

/-- Deterministic `Obend.Core.Data` decoding of `RealExpr`. -/
@[expose] def RealExpr.ofData? : Data → Option RealExpr
  | .variant "const" cD => do
    let c ← ratOfData? cD
    pure (.const c)
  | .variant "var" (.label v) => some (.var v)
  | .variant "add" (.record [("lhs", lD), ("rhs", rD)]) => do
    let l ← RealExpr.ofData? lD
    let r ← RealExpr.ofData? rD
    pure (.add l r)
  | .variant "sub" (.record [("lhs", lD), ("rhs", rD)]) => do
    let l ← RealExpr.ofData? lD
    let r ← RealExpr.ofData? rD
    pure (.sub l r)
  | .variant "mul" (.record [("lhs", lD), ("rhs", rD)]) => do
    let l ← RealExpr.ofData? lD
    let r ← RealExpr.ofData? rD
    pure (.mul l r)
  | .variant "sqr" aD => do
    let a ← RealExpr.ofData? aD
    pure (.sqr a)
  | _ => none

theorem RealExpr.ofData_toData (e : RealExpr) :
    RealExpr.ofData? e.toData = some e := by
  induction e with
  | const c => simp [RealExpr.toData, RealExpr.ofData?, ratOfData_toData]
  | var v => rfl
  | add l r ihl ihr => simp [RealExpr.toData, RealExpr.ofData?, ihl, ihr]
  | sub l r ihl ihr => simp [RealExpr.toData, RealExpr.ofData?, ihl, ihr]
  | mul l r ihl ihr => simp [RealExpr.toData, RealExpr.ofData?, ihl, ihr]
  | sqr a iha => simp [RealExpr.toData, RealExpr.ofData?, iha]

@[expose] def fieldExprListToData : List (String × RealExpr) → Data
  | [] => .variant "nil" (.record [])
  | (name, rhs) :: rest =>
    .variant "cons" (.record [("name", .label name), ("rhs", rhs.toData), ("tail", fieldExprListToData rest)])

@[expose] def fieldExprListOfData? : Data → Option (List (String × RealExpr))
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("name", .label name), ("rhs", rhsD), ("tail", tailD)]) => do
    let rhs ← RealExpr.ofData? rhsD
    let rest ← fieldExprListOfData? tailD
    pure ((name, rhs) :: rest)
  | _ => none

theorem fieldExprListOfData_toData (fs : List (String × RealExpr)) :
    fieldExprListOfData? (fieldExprListToData fs) = some fs := by
  induction fs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, rhs⟩
    simp [fieldExprListToData, fieldExprListOfData?, RealExpr.ofData_toData, ih]

@[expose] def boxListToData : List (String × Interval) → Data
  | [] => .variant "nil" (.record [])
  | (name, iv) :: rest =>
    .variant "cons" (.record [("name", .label name), ("iv", iv.toData), ("tail", boxListToData rest)])

@[expose] def boxListOfData? : Data → Option (List (String × Interval))
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("name", .label name), ("iv", ivD), ("tail", tailD)]) => do
    let iv ← Interval.ofData? ivD
    let rest ← boxListOfData? tailD
    pure ((name, iv) :: rest)
  | _ => none

theorem boxListOfData_toData (bx : List (String × Interval)) :
    boxListOfData? (boxListToData bx) = some bx := by
  induction bx with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, iv⟩
    simp [boxListToData, boxListOfData?, Interval.ofData_toData, ih]

@[expose] def resetListToData : List (String × CanonicalRat × CanonicalRat) → Data
  | [] => .variant "nil" (.record [])
  | (name, scale, offset) :: rest =>
    .variant "cons"
      (.record
        [ ("name", .label name)
        , ("scale", ratToData scale)
        , ("offset", ratToData offset)
        , ("tail", resetListToData rest) ])

@[expose] def resetListOfData? : Data → Option (List (String × CanonicalRat × CanonicalRat))
  | .variant "nil" (.record []) => some []
  | .variant "cons"
      (.record
        [ ("name", .label name)
        , ("scale", scaleD)
        , ("offset", offsetD)
        , ("tail", tailD) ]) => do
    let scale ← ratOfData? scaleD
    let offset ← ratOfData? offsetD
    let rest ← resetListOfData? tailD
    pure ((name, scale, offset) :: rest)
  | _ => none

theorem resetListOfData_toData (rs : List (String × CanonicalRat × CanonicalRat)) :
    resetListOfData? (resetListToData rs) = some rs := by
  induction rs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, scale, offset⟩
    simp [resetListToData, resetListOfData?, ratOfData_toData, ih]

/-- Deterministic `Obend.Core.Data` encoding of `OdeSystem`. -/
@[expose] def OdeSystem.toData (sys : OdeSystem) : Data :=
  .record
    [ ("fields", fieldExprListToData sys.fields)
    , ("dt", ratToData sys.dt)
    , ("remainderPad", sys.remainderPad.toData) ]

/-- Deterministic `Obend.Core.Data` decoding of `OdeSystem`. -/
@[expose] def OdeSystem.ofData? : Data → Option OdeSystem
  | .record [("fields", fsD), ("dt", dtD), ("remainderPad", padD)] => do
    let fields ← fieldExprListOfData? fsD
    let dt ← ratOfData? dtD
    let remainderPad ← Interval.ofData? padD
    pure { fields, dt, remainderPad }
  | _ => none

theorem OdeSystem.ofData_toData (sys : OdeSystem) :
    OdeSystem.ofData? sys.toData = some sys := by
  cases sys
  simp [OdeSystem.toData, OdeSystem.ofData?, fieldExprListOfData_toData,
    ratOfData_toData, Interval.ofData_toData]

/-- Deterministic `Obend.Core.Data` encoding of `HybridMode`. -/
@[expose] def HybridMode.toData (m : HybridMode) : Data :=
  .record
    [ ("modeId", .label m.modeId)
    , ("ode", m.ode.toData)
    , ("invariantBounds", boxListToData m.invariantBounds) ]

/-- Deterministic `Obend.Core.Data` decoding of `HybridMode`. -/
@[expose] def HybridMode.ofData? : Data → Option HybridMode
  | .record [("modeId", .label modeId), ("ode", odeD), ("invariantBounds", invD)] => do
    let ode ← OdeSystem.ofData? odeD
    let invariantBounds ← boxListOfData? invD
    pure { modeId, ode, invariantBounds }
  | _ => none

theorem HybridMode.ofData_toData (m : HybridMode) :
    HybridMode.ofData? m.toData = some m := by
  cases m
  simp [HybridMode.toData, HybridMode.ofData?, OdeSystem.ofData_toData, boxListOfData_toData]

/-- Deterministic `Obend.Core.Data` encoding of `AffineResetMap`. -/
@[expose] def AffineResetMap.toData (rm : AffineResetMap) : Data :=
  resetListToData rm.resets

/-- Deterministic `Obend.Core.Data` decoding of `AffineResetMap`. -/
@[expose] def AffineResetMap.ofData? (d : Data) : Option AffineResetMap := do
  let resets ← resetListOfData? d
  pure { resets }

theorem AffineResetMap.ofData_toData (rm : AffineResetMap) :
    AffineResetMap.ofData? rm.toData = some rm := by
  cases rm
  simp [AffineResetMap.toData, AffineResetMap.ofData?, resetListOfData_toData]

/-- Deterministic `Obend.Core.Data` encoding of `HybridJump`. -/
@[expose] def HybridJump.toData (j : HybridJump) : Data :=
  .record
    [ ("fromMode", .label j.fromMode)
    , ("toMode", .label j.toMode)
    , ("guardBounds", boxListToData j.guardBounds)
    , ("resetMap", j.resetMap.toData) ]

/-- Deterministic `Obend.Core.Data` decoding of `HybridJump`. -/
@[expose] def HybridJump.ofData? : Data → Option HybridJump
  | .record
      [ ("fromMode", .label fromMode)
      , ("toMode", .label toMode)
      , ("guardBounds", guardD)
      , ("resetMap", resetD) ] => do
    let guardBounds ← boxListOfData? guardD
    let resetMap ← AffineResetMap.ofData? resetD
    pure { fromMode, toMode, guardBounds, resetMap }
  | _ => none

theorem HybridJump.ofData_toData (j : HybridJump) :
    HybridJump.ofData? j.toData = some j := by
  cases j
  simp [HybridJump.toData, HybridJump.ofData?, boxListOfData_toData, AffineResetMap.ofData_toData]

@[expose] def modeListToData : List HybridMode → Data
  | [] => .variant "nil" (.record [])
  | m :: rest => .variant "cons" (.record [("head", m.toData), ("tail", modeListToData rest)])

@[expose] def modeListOfData? : Data → Option (List HybridMode)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", hD), ("tail", tD)]) => do
    let m ← HybridMode.ofData? hD
    let rest ← modeListOfData? tD
    pure (m :: rest)
  | _ => none

theorem modeListOfData_toData (ms : List HybridMode) :
    modeListOfData? (modeListToData ms) = some ms := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    simp [modeListToData, modeListOfData?, HybridMode.ofData_toData, ih]

@[expose] def jumpListToData : List HybridJump → Data
  | [] => .variant "nil" (.record [])
  | j :: rest => .variant "cons" (.record [("head", j.toData), ("tail", jumpListToData rest)])

@[expose] def jumpListOfData? : Data → Option (List HybridJump)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", hD), ("tail", tD)]) => do
    let j ← HybridJump.ofData? hD
    let rest ← jumpListOfData? tD
    pure (j :: rest)
  | _ => none

theorem jumpListOfData_toData (js : List HybridJump) :
    jumpListOfData? (jumpListToData js) = some js := by
  induction js with
  | nil => rfl
  | cons j rest ih =>
    simp [jumpListToData, jumpListOfData?, HybridJump.ofData_toData, ih]

/-- Deterministic `Obend.Core.Data` encoding of `HybridAutomaton`. -/
@[expose] def HybridAutomaton.toData (aut : HybridAutomaton) : Data :=
  .record
    [ ("modes", modeListToData aut.modes)
    , ("jumps", jumpListToData aut.jumps)
    , ("safeEnvelope", boxListToData aut.safeEnvelope) ]

/-- Deterministic `Obend.Core.Data` decoding of `HybridAutomaton`. -/
@[expose] def HybridAutomaton.ofData? : Data → Option HybridAutomaton
  | .record [("modes", msD), ("jumps", jsD), ("safeEnvelope", safeD)] => do
    let modes ← modeListOfData? msD
    let jumps ← jumpListOfData? jsD
    let safeEnvelope ← boxListOfData? safeD
    pure { modes, jumps, safeEnvelope }
  | _ => none

theorem HybridAutomaton.ofData_toData (aut : HybridAutomaton) :
    HybridAutomaton.ofData? aut.toData = some aut := by
  cases aut
  simp [HybridAutomaton.toData, HybridAutomaton.ofData?, modeListOfData_toData,
    jumpListOfData_toData, boxListOfData_toData]

/-- Deterministic `Obend.Core.Data` encoding of `HybridAction`. -/
@[expose] def HybridAction.toData : HybridAction → Data
  | .flowStep          => .variant "flowStep" (.record [])
  | .jumpTo targetMode => .variant "jumpTo" (.label targetMode)

/-- Deterministic `Obend.Core.Data` decoding of `HybridAction`. -/
@[expose] def HybridAction.ofData? : Data → Option HybridAction
  | .variant "flowStep" (.record [])     => some .flowStep
  | .variant "jumpTo" (.label targetMode) => some (.jumpTo targetMode)
  | _                                    => none

theorem HybridAction.ofData_toData (act : HybridAction) :
    HybridAction.ofData? act.toData = some act := by
  cases act <;> rfl

/-- Encode a schedule `List HybridAction` as `Obend.Core.Data`. -/
@[expose] def actionListToData : List HybridAction → Data
  | [] => .variant "nil" (.record [])
  | a :: rest => .variant "cons" (.record [("head", a.toData), ("tail", actionListToData rest)])

/-- Decode a schedule `List HybridAction` from `Obend.Core.Data`. -/
@[expose] def actionListOfData? : Data → Option (List HybridAction)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", h), ("tail", t)]) => do
    let a ← HybridAction.ofData? h
    let rest ← actionListOfData? t
    pure (a :: rest)
  | _ => none

theorem actionListOfData_toData (xs : List HybridAction) :
    actionListOfData? (actionListToData xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp [actionListToData, actionListOfData?, HybridAction.ofData_toData, ih]

/-- Hybrid flowpipe verification problem carrying an explicit `HybridAutomaton` AST,
monitored variable `varName`, initial mode/box bounds, and unsafe zone bounds. -/
structure HybridProblem where
  automaton : HybridAutomaton := thermostatLinearAutomaton
  varName   : String
  initMode  : String
  initLo    : Int
  initHi    : Int
  unsafeLo  : Int
  unsafeHi  : Int
  deriving @[expose] DecidableEq, Repr

/-- Deterministic `Obend.Core.Data` encoding of `HybridProblem`. -/
@[expose] def HybridProblem.toData (p : HybridProblem) : Data :=
  .record
    [ ("automaton", p.automaton.toData)
    , ("varName", .label p.varName)
    , ("initMode", .label p.initMode)
    , ("initLo", intToData p.initLo)
    , ("initHi", intToData p.initHi)
    , ("unsafeLo", intToData p.unsafeLo)
    , ("unsafeHi", intToData p.unsafeHi) ]

/-- Deterministic `Obend.Core.Data` decoding of `HybridProblem`. -/
@[expose] def HybridProblem.ofData? : Data → Option HybridProblem
  | .record
      [ ("automaton", automatonData)
      , ("varName", .label varName)
      , ("initMode", .label initMode)
      , ("initLo", initLoData)
      , ("initHi", initHiData)
      , ("unsafeLo", unsafeLoData)
      , ("unsafeHi", unsafeHiData) ] => do
    let automaton ← HybridAutomaton.ofData? automatonData
    let initLo ← intOfData? initLoData
    let initHi ← intOfData? initHiData
    let unsafeLo ← intOfData? unsafeLoData
    let unsafeHi ← intOfData? unsafeHiData
    pure { automaton, varName, initMode, initLo, initHi, unsafeLo, unsafeHi }
  | _ => none

/-- Exact roundtrip theorem for `HybridProblem.toData` / `HybridProblem.ofData?`. -/
theorem HybridProblem.ofData_toData (p : HybridProblem) :
    HybridProblem.ofData? p.toData = some p := by
  cases p
  simp [HybridProblem.toData, HybridProblem.ofData?, HybridAutomaton.ofData_toData, intOfData_toData]

/-- Hybrid flowpipe certificate carrying the execution schedule, expected terminal mode, and step count. -/
structure HybridCert where
  schedule          : List HybridAction
  expectedFinalMode : String
  claimedSteps      : Nat
  deriving @[expose] DecidableEq, Repr

/-- Deterministic `Obend.Core.Data` encoding of `HybridCert`. -/
@[expose] def HybridCert.toData (c : HybridCert) : Data :=
  .record
    [ ("schedule", actionListToData c.schedule)
    , ("expectedFinalMode", .label c.expectedFinalMode)
    , ("claimedSteps", .natural c.claimedSteps) ]

/-- Deterministic `Obend.Core.Data` decoding of `HybridCert`. -/
@[expose] def HybridCert.ofData? : Data → Option HybridCert
  | .record
      [ ("schedule", scheduleData)
      , ("expectedFinalMode", .label expectedFinalMode)
      , ("claimedSteps", .natural claimedSteps) ] => do
    let schedule ← actionListOfData? scheduleData
    pure { schedule, expectedFinalMode, claimedSteps }
  | _ => none

/-- Exact roundtrip theorem for `HybridCert.toData` / `HybridCert.ofData?`. -/
theorem HybridCert.ofData_toData (c : HybridCert) :
    HybridCert.ofData? c.toData = some c := by
  cases c
  simp [HybridCert.toData, HybridCert.ofData?, actionListOfData_toData]

/-- Construct the initial `HybridState` from a `HybridProblem`. -/
@[expose] def HybridProblem.initState (p : HybridProblem) : HybridState :=
  { modeId := p.initMode
  , box    := [(p.varName, ⟨Rat.ofInt p.initLo, Rat.ofInt p.initHi⟩)] }

/-- Construct the unsafe `Interval` from a `HybridProblem`. -/
@[expose] def HybridProblem.unsafeInterval (p : HybridProblem) : Interval :=
  ⟨Rat.ofInt p.unsafeLo, Rat.ofInt p.unsafeHi⟩

/-- Check whether two rational intervals `iv₁` and `iv₂` are valid (`lo ≤ hi`) and strictly disjoint. -/
@[expose] def intervalStrictlyDisjoint (iv₁ iv₂ : Interval) : Bool :=
  decide (iv₁.lo ≤ iv₁.hi) && decide (iv₂.lo ≤ iv₂.hi) &&
  (decide (iv₁.hi < iv₂.lo) || decide (iv₂.hi < iv₁.lo))

/-- Check whether two integer interval bounds `[lo₁, hi₁]` and `[lo₂, hi₂]` are valid and strictly disjoint. -/
@[expose] def intIntervalDisjoint (lo₁ hi₁ lo₂ hi₂ : Int) : Bool :=
  intervalStrictlyDisjoint ⟨Rat.ofInt lo₁, Rat.ofInt hi₁⟩ ⟨Rat.ofInt lo₂, Rat.ofInt hi₂⟩

/-- Check whether `[lo, hi]` is a non-inverted interval (`lo ≤ hi`) lying inside `[envLo, envHi]`. -/
@[expose] def intIntervalInBounds (lo hi envLo envHi : Int) : Bool :=
  decide (lo ≤ hi) && decide (envLo ≤ lo) && decide (hi ≤ envHi)

/-- Check that a continuous box `box` satisfies its `HybridMode` invariant, the global `safeEnvelope`,
and is strictly disjoint from `unsafeIv` on `varName`. -/
@[expose] def checkBoxModeAndDisjoint
    (aut : HybridAutomaton) (modeId varName : String)
    (box : List (String × Interval)) (unsafeIv : Interval) : Bool :=
  match findHybridMode? modeId aut.modes, box.lookup varName with
  | some mode, some curIv =>
    checkBoxNonInverted box &&
    checkBoxInEnvelope box mode.invariantBounds &&
    checkBoxInEnvelope box aut.safeEnvelope &&
    intervalStrictlyDisjoint curIv unsafeIv
  | _, _ => false

/-- Mode invariant check for `modeId` over `[lo, hi]` against `thermostatLinearAutomaton`. -/
@[expose] def modeInvariantHolds (modeId : String) (lo hi : Int) : Bool :=
  match findHybridMode? modeId thermostatLinearAutomaton.modes with
  | some mode =>
    decide (lo ≤ hi) &&
    checkBoxInEnvelope [("T", ⟨Rat.ofInt lo, Rat.ofInt hi⟩)] mode.invariantBounds
  | none => false

/-- Execute a single hybrid transition on `thermostatLinearAutomaton` via `stepHybridAction`. -/
@[expose] def stepHybrid (modeId : String) (lo hi : Int) (act : HybridAction) : Option (String × Int × Int) := do
  let st : HybridState := { modeId := modeId, box := [("T", ⟨Rat.ofInt lo, Rat.ofInt hi⟩)] }
  let nextSt ← stepHybridAction thermostatLinearAutomaton st act
  let nextIv ← nextSt.box.lookup "T"
  pure (nextSt.modeId, nextIv.lo.num, nextIv.hi.num)

/-- Execute a hybrid schedule on `aut : HybridAutomaton` from `st : HybridState`, checking at every
continuous `.flowStep` and discrete `.jumpTo`:
1. `st.box` satisfies the active `HybridMode.invariantBounds`, `aut.safeEnvelope`, and is strictly
   disjoint from `unsafeIv`,
2. For `.flowStep`, the continuous-time rough flowpipe enclosure `xTildeBox` (from `inferPicardAPrioriBox`)
   is ALSO strictly disjoint from `unsafeIv` and stays inside `mode.invariantBounds` and `aut.safeEnvelope`,
3. Advances `st` via `stepHybridFlow aut st` / `stepHybridJump? aut st targetMode`, returning the terminal mode. -/
@[expose] def runHybridAutomatonTube
    (aut : HybridAutomaton) (varName : String) (unsafeIv : Interval) :
    List HybridAction → HybridState → Option String
  | [], st =>
    if checkBoxModeAndDisjoint aut st.modeId varName st.box unsafeIv then
      some st.modeId
    else none
  | act :: rest, st =>
    if !checkBoxModeAndDisjoint aut st.modeId varName st.box unsafeIv then
      none
    else
      match act with
      | .flowStep => do
        let mode ← findHybridMode? st.modeId aut.modes
        let xTildeBox ← inferPicardAPrioriBox mode.ode st.box
        if !checkBoxModeAndDisjoint aut st.modeId varName xTildeBox unsafeIv then
          none
        else
          let nextSt ← stepHybridFlow aut st
          runHybridAutomatonTube aut varName unsafeIv rest nextSt
      | .jumpTo targetMode => do
        let nextSt ← stepHybridJump? aut st targetMode
        runHybridAutomatonTube aut varName unsafeIv rest nextSt

/-- Execute a hybrid schedule from `(modeId, lo, hi)` on `thermostatLinearAutomaton`. -/
@[expose] def runFlowpipeTube (modeId : String) (lo hi unsafeLo unsafeHi : Int)
    (schedule : List HybridAction) : Option String :=
  let st : HybridState := { modeId := modeId, box := [("T", ⟨Rat.ofInt lo, Rat.ofInt hi⟩)] }
  let unsafeIv : Interval := ⟨Rat.ofInt unsafeLo, Rat.ofInt unsafeHi⟩
  runHybridAutomatonTube thermostatLinearAutomaton "T" unsafeIv schedule st

/-- Verify a hybrid flowpipe certificate `c` against problem `p`:
1. `p.initLo ≤ p.initHi` and `p.unsafeLo ≤ p.unsafeHi`,
2. `c.claimedSteps = c.schedule.length`,
3. `runHybridAutomatonTube p.automaton p.varName p.unsafeInterval c.schedule p.initState` succeeds
   across all continuous `stepHybridFlow` and discrete `stepHybridJump?` transitions (checking both
   discrete slices AND continuous-time rough enclosures `xTildeBox` against mode invariants,
   `safeEnvelope`, and `p.unsafeInterval`),
4. The terminal hybrid state reaches `c.expectedFinalMode`. -/
@[expose] def verifyFlowpipe (p : HybridProblem) (c : HybridCert) : Bool :=
  decide (p.initLo ≤ p.initHi) &&
  decide (p.unsafeLo ≤ p.unsafeHi) &&
  decide (c.claimedSteps = c.schedule.length) &&
  match runHybridAutomatonTube p.automaton p.varName p.unsafeInterval c.schedule p.initState with
  | some finalMode => decide (finalMode = c.expectedFinalMode)
  | none           => false

/-! ## 4. Semantic Multi-Hop Hybrid Trajectory Safety (`HybridTrajectorySafe` & `verifyFlowpipe_sound`) -/

/-- Exact pointwise affine reset map $x'_v := \alpha_v x_v + \beta_v$ corresponding to `applyAffineReset`. -/
@[expose] def evalAffineResetPoint
    (rm : AffineResetMap) (rho : String → CanonicalRat) (v : String) : CanonicalRat :=
  match rm.resets.find? (fun (n, _, _) => n == v) with
  | some (_, scale, offset) => scale * rho v + offset
  | none                    => rho v

theorem applyAffineReset_lookup_inv (rm : AffineResetMap) (v : String) :
    ∀ (box : List (String × Interval)) (targetIv : Interval),
      (applyAffineReset rm box).lookup v = some targetIv →
      ∃ srcIv, box.lookup v = some srcIv ∧
        targetIv =
          match rm.resets.find? (fun (n, _, _) => n == v) with
          | some (_, scale, offset) =>
            Interval.add (Interval.mul (Interval.ofPoint scale) srcIv) (Interval.ofPoint offset)
          | none => srcIv
  | [], _, hLook => by simp [applyAffineReset] at hLook
  | (name, iv) :: rest, targetIv, hLook => by
    simp only [applyAffineReset, List.lookup] at hLook ⊢
    cases hvn : v == name
    · rw [hvn] at hLook
      exact applyAffineReset_lookup_inv rm v rest targetIv hLook
    · rw [hvn, Option.some.injEq] at hLook
      simp only [beq_iff_eq] at hvn
      subst hvn
      exact ⟨iv, rfl, hLook.symm⟩

/-- **Theorem (`applyAffineReset_sound`)**:
Interval affine reset `applyAffineReset rm box` encloses the pointwise affine reset
`evalAffineResetPoint rm rho` for every `rho` enclosed by `box`. -/
theorem applyAffineReset_sound
    {rm : AffineResetMap} {box : List (String × Interval)} {rho : String → CanonicalRat}
    (hBox : BoxMem rho box) :
    BoxMem (evalAffineResetPoint rm rho) (applyAffineReset rm box) := by
  intro v targetIv hLook
  obtain ⟨srcIv, hSrcLook, hTargetEq⟩ := applyAffineReset_lookup_inv rm v box targetIv hLook
  have hSrcMem : rho v ∈ srcIv := hBox v srcIv hSrcLook
  unfold evalAffineResetPoint
  rw [hTargetEq]
  cases rm.resets.find? (fun (n, _, _) => n == v) with
  | none => exact hSrcMem
  | some triple =>
    rcases triple with ⟨_, scale, offset⟩
    exact Interval.add_mem
      (Interval.mul_mem (Interval.ofPoint_mem scale) hSrcMem)
      (Interval.ofPoint_mem offset)

/-- **Theorem (`intervalStrictlyDisjoint_sound`)**:
If `intervalStrictlyDisjoint iv₁ iv₂ = true`, no rational point `x ∈ iv₁` lies in `iv₂`. -/
theorem intervalStrictlyDisjoint_sound
    {iv₁ iv₂ : Interval} (hDisj : intervalStrictlyDisjoint iv₁ iv₂ = true)
    {x : CanonicalRat} (hx : x ∈ iv₁) :
    x ∉ iv₂ := by
  unfold intervalStrictlyDisjoint at hDisj
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hDisj
  rw [Interval.mem_iff] at hx ⊢
  grind

/-- **Theorem (`checkBoxModeAndDisjoint_sound`)**:
If `checkBoxModeAndDisjoint aut modeId varName box unsafeIv = true`, then for every state `rho`
enclosed in `box`:
1. `modeId` resolves to an active `HybridMode` whose `invariantBounds` enclose `rho`,
2. `rho` stays inside `aut.safeEnvelope`, and
3. `rho varName ∉ unsafeIv`. -/
theorem checkBoxModeAndDisjoint_sound
    {aut : HybridAutomaton} {modeId varName : String}
    {box : List (String × Interval)} {unsafeIv : Interval}
    {rho : String → CanonicalRat}
    (hChk : checkBoxModeAndDisjoint aut modeId varName box unsafeIv = true)
    (hBox : BoxMem rho box) :
    (∃ mode, findHybridMode? modeId aut.modes = some mode ∧ BoxMem rho mode.invariantBounds) ∧
    BoxMem rho aut.safeEnvelope ∧
    rho varName ∉ unsafeIv := by
  unfold checkBoxModeAndDisjoint at hChk
  cases hMode : findHybridMode? modeId aut.modes with
  | none => rw [hMode] at hChk; simp at hChk
  | some mode =>
    rw [hMode] at hChk
    cases hLookVar : box.lookup varName with
    | none => rw [hLookVar] at hChk; simp at hChk
    | some curIv =>
      rw [hLookVar] at hChk
      simp only [Bool.and_eq_true] at hChk
      obtain ⟨⟨⟨_, hInv⟩, hSafe⟩, hDisj⟩ := hChk
      refine ⟨⟨mode, rfl, checkBoxInEnvelope_sound hInv hBox⟩,
              checkBoxInEnvelope_sound hSafe hBox,
              intervalStrictlyDisjoint_sound hDisj (hBox varName curIv hLookVar)⟩

private theorem stepHybridFlow_unpack
    {aut : HybridAutomaton} {st nextSt : HybridState}
    {mode : HybridMode} {xTildeBox : List (String × Interval)}
    (hMode : findHybridMode? st.modeId aut.modes = some mode)
    (hInfer : inferPicardAPrioriBox mode.ode st.box = some xTildeBox)
    (hStep : stepHybridFlow aut st = some nextSt) :
    ∃ nextBox,
      stepPicardValidated mode.ode st.box xTildeBox mode.ode.dt = some nextBox ∧
      nextSt = { modeId := st.modeId, box := nextBox } := by
  unfold stepHybridFlow at hStep
  simp only [bind, Option.bind] at hStep
  rw [hMode] at hStep
  dsimp only at hStep
  split at hStep
  · simp at hStep
  · rw [hInfer] at hStep
    dsimp only at hStep
    split at hStep
    · simp at hStep
    · cases hPic : stepPicardValidated mode.ode st.box xTildeBox mode.ode.dt with
      | none => rw [hPic] at hStep; simp at hStep
      | some nextBox =>
        rw [hPic] at hStep
        dsimp only at hStep
        split at hStep
        · simp only [Option.some.injEq] at hStep
          exact ⟨nextBox, rfl, hStep.symm⟩
        · simp at hStep

private theorem stepHybridJump_unpack
    {aut : HybridAutomaton} {st nextSt : HybridState} {targetMode : String}
    (hStep : stepHybridJump? aut st targetMode = some nextSt) :
    ∃ jump dstMode,
      findHybridJump? st.modeId targetMode aut.jumps = some jump ∧
      findHybridMode? targetMode aut.modes = some dstMode ∧
      checkBoxInEnvelope st.box jump.guardBounds = true ∧
      nextSt = { modeId := targetMode, box := applyAffineReset jump.resetMap st.box } := by
  unfold stepHybridJump? at hStep
  simp only [bind, Option.bind] at hStep
  cases hJump : findHybridJump? st.modeId targetMode aut.jumps with
  | none => rw [hJump] at hStep; simp at hStep
  | some jump =>
    rw [hJump] at hStep
    dsimp only at hStep
    cases hDst : findHybridMode? targetMode aut.modes with
    | none => rw [hDst] at hStep; simp at hStep
    | some dstMode =>
      rw [hDst] at hStep
      dsimp only at hStep
      cases hGuard : (!checkBoxNonInverted st.box || !checkBoxInEnvelope st.box jump.guardBounds) with
      | true => rw [hGuard] at hStep; simp at hStep
      | false =>
        rw [hGuard] at hStep
        simp only [Bool.false_eq_true, ↓reduceIte] at hStep
        have hGuardEnv : checkBoxInEnvelope st.box jump.guardBounds = true := by
          cases hE : checkBoxInEnvelope st.box jump.guardBounds
          · rw [hE] at hGuard; simp at hGuard
          · rfl
        split at hStep
        · simp only [Option.some.injEq] at hStep
          exact ⟨jump, dstMode, rfl, rfl, hGuardEnv, hStep.symm⟩
        · simp at hStep

/-- Single-step semantic relation for a hybrid execution transition `(srcMode, seg) ↦ (dstMode, nextRho)`:
* On `.flowStep`: discrete mode stays `dstMode = srcMode`, `seg : [0, Δt] → (String → ℚ)` is a valid
  Picard/quadrature flow curve of `mode.ode` starting from `seg 0` (`IsPicardStepCurve`), and `nextRho`
  obeys the 2nd-order Taylor–Lie ODE evolution bound over `[0, mode.ode.dt]`.
* On `.jumpTo targetMode`: discrete mode switches to `dstMode = targetMode` and `nextRho` is obtained
  by applying the active jump's affine reset map `evalAffineResetPoint jump.resetMap (seg 0)`. -/
@[expose] def IsValidHybridStep
    (aut : HybridAutomaton) (act : HybridAction)
    (srcMode dstMode : String)
    (seg : CanonicalRat → String → CanonicalRat)
    (nextRho : String → CanonicalRat) : Prop :=
  match act with
  | .flowStep =>
    dstMode = srcMode ∧
    ∀ mode, findHybridMode? srcMode aut.modes = some mode →
      (∃ nodes, ValidQuadratureOn mode.ode.dt nodes ∧
        ∀ τ ∈ Interval.mk 0 mode.ode.dt, ∃ m : Nat,
          ∀ v, seg τ v = iteratePicardOperator mode.ode (seg 0) nodes m τ v) ∧
      (∀ name rhsExpr, (name, rhsExpr) ∈ mode.ode.fields →
        ∃ τ_mid ∈ Interval.mk 0 mode.ode.dt,
        ∃ r_pad ∈ mode.ode.remainderPad,
          nextRho name =
            seg 0 name + mode.ode.dt * evalExpr (seg 0) rhsExpr +
              (((mode.ode.dt * mode.ode.dt) / 2) *
                evalOdePointLieDerivComponent mode.ode (seg τ_mid) rhsExpr + r_pad))
  | .jumpTo targetMode =>
    dstMode = targetMode ∧
    ∀ jump, findHybridJump? srcMode targetMode aut.jumps = some jump →
      ∀ v, nextRho v = evalAffineResetPoint jump.resetMap (seg 0) v

/-- Multi-hop semantic hybrid execution of `aut` along `schedule : List HybridAction` over discrete
mode trace `modes : Nat → String` and continuous segments `segs : Nat → CanonicalRat → String → CanonicalRat`. -/
@[expose] def IsValidHybridExecution
    (aut : HybridAutomaton) (schedule : List HybridAction)
    (modes : Nat → String) (segs : Nat → CanonicalRat → String → CanonicalRat) : Prop :=
  ∀ k (hk : k < schedule.length),
    IsValidHybridStep aut schedule[k] (modes k) (modes (k + 1)) (segs k) (segs (k + 1) 0)

/-- Genuine semantic multi-hop hybrid trajectory safety proposition (`hybridFlowpipeJudge.Meaning`):
asserts that initial and unsafe intervals are well-formed, `claimedSteps` matches `schedule.length`,
and **every** multi-hop hybrid trajectory `(modes, segs)` starting from `p.initMode` and any initial
continuous point `segs 0 0 ∈ p.initState.box` and evolving according to `IsValidHybridExecution`:
1. Reaches `modes c.schedule.length = c.expectedFinalMode`,
2. Satisfies the active mode invariant, global `safeEnvelope`, and strict avoidance of `p.unsafeInterval`
   at **every** discrete boundary slice `0 ≤ k ≤ c.schedule.length`,
3. Satisfies the active mode invariant, global `safeEnvelope`, and strict avoidance of `p.unsafeInterval`
   at **every** continuous intermediate time `τ ∈ [0, mode.ode.dt]` during every `.flowStep`, and
4. Satisfies `jump.guardBounds` prior to **every** discrete `.jumpTo targetMode` switch! -/
@[expose] def HybridTrajectorySafe (p : HybridProblem) (c : HybridCert) : Prop :=
  p.initLo ≤ p.initHi ∧
  p.unsafeLo ≤ p.unsafeHi ∧
  c.claimedSteps = c.schedule.length ∧
  ∀ (modes : Nat → String) (segs : Nat → CanonicalRat → String → CanonicalRat),
    modes 0 = p.initMode →
    BoxMem (segs 0 0) p.initState.box →
    IsValidHybridExecution p.automaton c.schedule modes segs →
    modes c.schedule.length = c.expectedFinalMode ∧
    (∀ k, k ≤ c.schedule.length →
      (∃ mode, findHybridMode? (modes k) p.automaton.modes = some mode ∧
        BoxMem (segs k 0) mode.invariantBounds) ∧
      BoxMem (segs k 0) p.automaton.safeEnvelope ∧
      segs k 0 p.varName ∉ p.unsafeInterval) ∧
    (∀ k (hk : k < c.schedule.length),
      match c.schedule[k] with
      | .flowStep =>
        ∃ mode, findHybridMode? (modes k) p.automaton.modes = some mode ∧
          ∀ τ ∈ Interval.mk 0 mode.ode.dt,
            BoxMem (segs k τ) mode.invariantBounds ∧
            BoxMem (segs k τ) p.automaton.safeEnvelope ∧
            segs k τ p.varName ∉ p.unsafeInterval
      | .jumpTo targetMode =>
        ∃ jump, findHybridJump? (modes k) targetMode p.automaton.jumps = some jump ∧
          BoxMem (segs k 0) jump.guardBounds)

/-- Inductive multi-hop tube soundness theorem for `runHybridAutomatonTube`. -/
theorem runHybridAutomatonTube_sound
    (aut : HybridAutomaton) (varName : String) (unsafeIv : Interval)
    (schedule : List HybridAction) :
    ∀ (st : HybridState) (finalMode : String)
      (modes : Nat → String) (segs : Nat → CanonicalRat → String → CanonicalRat),
      runHybridAutomatonTube aut varName unsafeIv schedule st = some finalMode →
      modes 0 = st.modeId →
      BoxMem (segs 0 0) st.box →
      IsValidHybridExecution aut schedule modes segs →
      modes schedule.length = finalMode ∧
      (∀ k, k ≤ schedule.length →
        (∃ mode, findHybridMode? (modes k) aut.modes = some mode ∧
          BoxMem (segs k 0) mode.invariantBounds) ∧
        BoxMem (segs k 0) aut.safeEnvelope ∧
        segs k 0 varName ∉ unsafeIv) ∧
      (∀ k (hk : k < schedule.length),
        match schedule[k] with
        | .flowStep =>
          ∃ mode, findHybridMode? (modes k) aut.modes = some mode ∧
            ∀ τ ∈ Interval.mk 0 mode.ode.dt,
              BoxMem (segs k τ) mode.invariantBounds ∧
              BoxMem (segs k τ) aut.safeEnvelope ∧
              segs k τ varName ∉ unsafeIv
        | .jumpTo targetMode =>
          ∃ jump, findHybridJump? (modes k) targetMode aut.jumps = some jump ∧
            BoxMem (segs k 0) jump.guardBounds) := by
  induction schedule with
  | nil =>
    intro st finalMode modes segs hRun hMode0 hBox0 _
    unfold runHybridAutomatonTube at hRun
    cases hChk : checkBoxModeAndDisjoint aut st.modeId varName st.box unsafeIv with
    | false => rw [hChk] at hRun; simp at hRun
    | true =>
      rw [hChk] at hRun
      simp only [↓reduceIte, Option.some.injEq] at hRun
      have hSafe0 := checkBoxModeAndDisjoint_sound hChk hBox0
      refine ⟨by simp [hMode0, hRun], ?_, ?_⟩
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        rw [hMode0]
        exact hSafe0
      · intro k hk
        simp at hk
  | cons act rest ih =>
    intro st finalMode modes segs hRun hMode0 hBox0 hExec
    unfold runHybridAutomatonTube at hRun
    cases hChk0 : checkBoxModeAndDisjoint aut st.modeId varName st.box unsafeIv with
    | false => rw [hChk0] at hRun; simp at hRun
    | true =>
      rw [hChk0] at hRun
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRun
      have hSafe0 := checkBoxModeAndDisjoint_sound hChk0 hBox0
      have hStep0 : IsValidHybridStep aut act (modes 0) (modes 1) (segs 0) (segs 1 0) :=
        hExec 0 (Nat.zero_lt_succ _)
      let modes' : Nat → String := fun j => modes (j + 1)
      let segs' : Nat → CanonicalRat → String → CanonicalRat := fun j => segs (j + 1)
      have hExecRest : IsValidHybridExecution aut rest modes' segs' := by
        intro j hj
        exact hExec (j + 1) (Nat.succ_lt_succ hj)
      cases act with
      | flowStep =>
        simp only [bind, Option.bind] at hRun
        cases hMode : findHybridMode? st.modeId aut.modes with
        | none => rw [hMode] at hRun; simp at hRun
        | some mode =>
          rw [hMode] at hRun
          dsimp only at hRun
          cases hInfer : inferPicardAPrioriBox mode.ode st.box with
          | none => rw [hInfer] at hRun; simp at hRun
          | some xTildeBox =>
            rw [hInfer] at hRun
            dsimp only at hRun
            cases hChkTilde : checkBoxModeAndDisjoint aut st.modeId varName xTildeBox unsafeIv with
            | false => rw [hChkTilde] at hRun; simp at hRun
            | true =>
              rw [hChkTilde] at hRun
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRun
              cases hStepFlow : stepHybridFlow aut st with
              | none => rw [hStepFlow] at hRun; simp at hRun
              | some nextSt =>
                rw [hStepFlow] at hRun
                dsimp only at hRun
                obtain ⟨nextBox, hPicVal, hNextStEq⟩ := stepHybridFlow_unpack hMode hInfer hStepFlow
                obtain ⟨hPicVer, _, hInitTilde, hFieldsCover⟩ :=
                  inferPicardAPrioriBox_encloses_init_and_fields hInfer hBox0
                unfold IsValidHybridStep at hStep0
                obtain ⟨hMode1Eq, hFlowSpec⟩ := hStep0
                have hMode0Find : findHybridMode? (modes 0) aut.modes = some mode := by
                  rw [hMode0]; exact hMode
                obtain ⟨hPicCurve, hLieStep⟩ := hFlowSpec mode hMode0Find
                rcases hPicCurve with ⟨nodes, hValidQuad, hIterEq⟩
                have hSegTilde : ∀ τ ∈ Interval.mk 0 mode.ode.dt, BoxMem (segs 0 τ) xTildeBox := by
                  intro τ hτ
                  obtain ⟨m, hmEq⟩ := hIterEq τ hτ
                  have hIterMem := iteratePicardOperator_stays_in_apriori
                    mode.ode st.box xTildeBox mode.ode.dt (segs 0 0) nodes
                    hPicVer hBox0 hInitTilde hFieldsCover hValidQuad m τ hτ
                  intro u uIv huLook
                  rw [hmEq u]
                  exact hIterMem u uIv huLook
                have hBox1 : BoxMem (segs 1 0) nextSt.box := by
                  rw [hNextStEq]
                  dsimp only
                  exact stepPicardValidated_encloses_step hPicVal hBox0 (fun name rhsExpr hMemF => by
                    obtain ⟨τ_mid, hτMid, r_pad, hrPad, hEq1⟩ := hLieStep name rhsExpr hMemF
                    exact ⟨segs 0 τ_mid, r_pad, hSegTilde τ_mid hτMid, hrPad, hEq1⟩)
                have hMode1Next : modes' 0 = nextSt.modeId := by
                  dsimp only [modes']
                  rw [hMode1Eq, hMode0, hNextStEq]
                obtain ⟨hTerm, hDiscRest, hContRest⟩ :=
                  ih nextSt finalMode modes' segs' hRun hMode1Next hBox1 hExecRest
                refine ⟨hTerm, ?_, ?_⟩
                · intro k hk
                  cases k with
                  | zero =>
                    rw [hMode0]
                    exact hSafe0
                  | succ j =>
                    exact hDiscRest j (Nat.le_of_succ_le_succ hk)
                · intro k hk
                  cases k with
                  | zero =>
                    simp only [List.getElem_cons_zero]
                    refine ⟨mode, hMode0Find, ?_⟩
                    intro τ hτ
                    obtain ⟨_, hSafeτ, hDisjτ⟩ :=
                      checkBoxModeAndDisjoint_sound hChkTilde (hSegTilde τ hτ)
                    have hInvτ : BoxMem (segs 0 τ) mode.invariantBounds := by
                      unfold checkBoxModeAndDisjoint at hChkTilde
                      rw [hMode] at hChkTilde
                      cases hLv : xTildeBox.lookup varName with
                      | none => rw [hLv] at hChkTilde; simp at hChkTilde
                      | some cIv =>
                        rw [hLv] at hChkTilde
                        simp only [Bool.and_eq_true] at hChkTilde
                        exact checkBoxInEnvelope_sound hChkTilde.1.1.2 (hSegTilde τ hτ)
                    exact ⟨hInvτ, hSafeτ, hDisjτ⟩
                  | succ j =>
                    simp only [List.getElem_cons_succ]
                    exact hContRest j (Nat.lt_of_succ_lt_succ hk)
      | jumpTo targetMode =>
        simp only [bind, Option.bind] at hRun
        cases hStepJump : stepHybridJump? aut st targetMode with
        | none => rw [hStepJump] at hRun; simp at hRun
        | some nextSt =>
          rw [hStepJump] at hRun
          dsimp only at hRun
          obtain ⟨jump, _, hJumpFind, _, hGuardEnv, hNextStEq⟩ := stepHybridJump_unpack hStepJump
          unfold IsValidHybridStep at hStep0
          obtain ⟨hMode1Eq, hResetSpec⟩ := hStep0
          have hJump0Find : findHybridJump? (modes 0) targetMode aut.jumps = some jump := by
            rw [hMode0]; exact hJumpFind
          have hResetFun : segs 1 0 = evalAffineResetPoint jump.resetMap (segs 0 0) := by
            funext u
            exact hResetSpec jump hJump0Find u
          have hBox1 : BoxMem (segs 1 0) nextSt.box := by
            rw [hNextStEq, hResetFun]
            exact applyAffineReset_sound hBox0
          have hMode1Next : modes' 0 = nextSt.modeId := by
            dsimp only [modes']
            rw [hMode1Eq, hNextStEq]
          obtain ⟨hTerm, hDiscRest, hContRest⟩ :=
            ih nextSt finalMode modes' segs' hRun hMode1Next hBox1 hExecRest
          refine ⟨hTerm, ?_, ?_⟩
          · intro k hk
            cases k with
            | zero =>
              rw [hMode0]
              exact hSafe0
            | succ j =>
              exact hDiscRest j (Nat.le_of_succ_le_succ hk)
          · intro k hk
            cases k with
            | zero =>
              simp only [List.getElem_cons_zero]
              exact ⟨jump, hJump0Find, checkBoxInEnvelope_sound hGuardEnv hBox0⟩
            | succ j =>
              simp only [List.getElem_cons_succ]
              exact hContRest j (Nat.lt_of_succ_lt_succ hk)

/-- **Theorem (`verifyFlowpipe_sound`)**:
Whenever `verifyFlowpipe p c = true`, the genuine semantic multi-hop hybrid trajectory safety
proposition `HybridTrajectorySafe p c` holds across all discrete mode switches and continuous
ODE segments! -/
theorem verifyFlowpipe_sound :
    ∀ (p : HybridProblem) (c : HybridCert),
      verifyFlowpipe p c = true →
      HybridTrajectorySafe p c := by
  intro p c hVer
  unfold verifyFlowpipe at hVer
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hVer
  obtain ⟨⟨⟨hInitLe, hUnsafeLe⟩, hStepsEq⟩, hTubeOk⟩ := hVer
  cases hRun : runHybridAutomatonTube p.automaton p.varName p.unsafeInterval c.schedule p.initState with
  | none => rw [hRun] at hTubeOk; simp at hTubeOk
  | some finalMode =>
    rw [hRun] at hTubeOk
    simp only [decide_eq_true_eq] at hTubeOk
    subst hTubeOk
    refine ⟨hInitLe, hUnsafeLe, hStepsEq, ?_⟩
    intro modes segs hMode0 hBox0 hExec
    exact runHybridAutomatonTube_sound
      p.automaton p.varName p.unsafeInterval c.schedule
      p.initState c.expectedFinalMode modes segs hRun hMode0 hBox0 hExec

#tooth verifyFlowpipe_sound by mutation
  verifyFlowpipe := fun _ _ => true

/-- Concrete valid and invalid hybrid flowpipe problem/certificate fixtures. -/
@[expose] def demoHybridProblem : HybridProblem :=
  { automaton := thermostatLinearAutomaton
  , varName   := "T"
  , initMode  := "heating"
  , initLo    := 24
  , initHi    := 26
  , unsafeLo  := 36
  , unsafeHi  := 50 }

@[expose] def validHybridCert : HybridCert :=
  { schedule          := [.flowStep, .jumpTo "cooling", .flowStep, .flowStep]
  , expectedFinalMode := "cooling"
  , claimedSteps      := 4 }

@[expose] def badHybridCert : HybridCert :=
  { schedule          := [.flowStep, .flowStep, .flowStep]
  , expectedFinalMode := "heating"
  , claimedSteps      := 3 }

@[expose] def badStepCountHybridCert : HybridCert :=
  { schedule          := [.flowStep, .jumpTo "cooling"]
  , expectedFinalMode := "cooling"
  , claimedSteps      := 99 }

-- fixture kept (2026-11-04): target of #tooth at Obend/Analysis/Hybrid.lean
theorem badHybridCert_rejected :
    verifyFlowpipe demoHybridProblem badHybridCert = false := by decide +kernel

/-- Inverted initial interval (`initLo > initHi`) is rejected even if endpoints lie in `[15, 32]`. -/
-- fixture kept (2026-11-04): refusal witness: `verifyFlowpipe` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
example :
    verifyFlowpipe { demoHybridProblem with initLo := 26, initHi := 24 } validHybridCert = false := by decide +kernel

/-- Nonexistent mode is rejected even on an empty schedule (`schedule = []`). -/
-- fixture kept (2026-11-04): refusal witness: `verifyFlowpipe` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
example :
    verifyFlowpipe
      { demoHybridProblem with initMode := "bogus", initLo := 20, initHi := 22 }
      { schedule := [], expectedFinalMode := "bogus", claimedSteps := 0 } = false := by decide +kernel

#tooth badHybridCert_rejected by mutation
  verifyFlowpipe := fun _ _ => true

/-- Decision procedure returning `Obend.Judge.Verdict String` for `(HybridProblem, HybridCert)`. -/
@[expose] def checkHybridFlowpipe (_grade : Nat) (p : HybridProblem) (c : HybridCert) : Obend.Judge.Verdict String :=
  if verifyFlowpipe p c then .ok
  else .refused "flowpipe_invariant_or_unsafe_zone_violation" []

/-- `Obend.Judge` instance for `(HybridProblem, HybridCert)` with genuine semantic multi-hop
hybrid trajectory safety `HybridTrajectorySafe` as `Meaning`. -/
instance hybridFlowpipeJudge : Obend.Judge HybridProblem HybridCert where
  Clause := String
  Meaning := HybridTrajectorySafe
  check := checkHybridFlowpipe
  sound := by
    intro _r o c h_ok
    unfold checkHybridFlowpipe at h_ok
    cases h : verifyFlowpipe o c
    · rw [h] at h_ok
      contradiction
    · exact verifyFlowpipe_sound o c h
  refutes _ := false
  refuted := by
    intro _r _o _c _k _p _h_ref h_false
    contradiction
  Fragment p := ∃ c, verifyFlowpipe p c = true
  complete := by
    intro o ⟨c, hc⟩ _
    refine ⟨c, 0, ?_⟩
    simp [checkHybridFlowpipe, hc]
  mono := by
    intro _r _r' _o _c _hle _hunc
    rfl

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem hybridFlowpipe_bad_refused :
    checkHybridFlowpipe 0 demoHybridProblem badHybridCert =
      .refused "flowpipe_invariant_or_unsafe_zone_violation" [] := by decide +kernel

/-! ## 5. General `Lean.Json` AST Encoders & Decoders for `HybridProblem` and `HybridCert` -/

/-- Decode a `HybridProblem` from `Obend.Core.Data` via `HybridProblem.ofData?`. -/
@[expose] def decodeHybridProblemData (d : Data) : Except String HybridProblem :=
  match HybridProblem.ofData? d with
  | some p => .ok p
  | none   => .error "malformed HybridProblem Core.Data payload"

/-- Decode a `HybridCert` from `Obend.Core.Data` via `HybridCert.ofData?`. -/
@[expose] def decodeHybridCertData (d : Data) : Except String HybridCert :=
  match HybridCert.ofData? d with
  | some c => .ok c
  | none   => .error "malformed HybridCert Core.Data payload"

/-- Encode a `CanonicalRat` as a `Lean.Json` object `{"num": ..., "den": ...}`. -/
@[expose] def encodeHybridRatJson (q : CanonicalRat) : Lean.Json :=
  Lean.Json.mkObj [("num", Lean.toJson q.num), ("den", Lean.toJson q.den)]

/-- Decode a `CanonicalRat` from `Lean.Json` (accepts integer `n` or `{"num": n, "den": d}`). -/
@[expose] def decodeHybridRatJson (j : Lean.Json) : Except String CanonicalRat :=
  match j.getInt? with
  | .ok n => .ok (Rat.ofInt n)
  | .error _ =>
    match j.getObjValAs? Int "num", j.getObjValAs? Nat "den" with
    | .ok num, .ok den =>
      if den == 0 then .error "zero denominator in rational JSON"
      else .ok (CanonicalRat.mk num den)
    | _, _ => .error "invalid rational JSON"

/-- Encode an `Interval` as `Lean.Json`. -/
@[expose] def encodeIntervalJson (iv : Interval) : Lean.Json :=
  Lean.Json.mkObj [("lo", encodeHybridRatJson iv.lo), ("hi", encodeHybridRatJson iv.hi)]

/-- Decode an `Interval` from `Lean.Json` (`{"lo": ..., "hi": ...}`). -/
@[expose] def decodeIntervalJson (j : Lean.Json) : Except String Interval := do
  let loJ ← j.getObjVal? "lo"
  let hiJ ← j.getObjVal? "hi"
  let lo ← decodeHybridRatJson loJ
  let hi ← decodeHybridRatJson hiJ
  pure ⟨lo, hi⟩

/-- Encode a `RealExpr` AST as `Lean.Json`. -/
@[expose] def encodeRealExprJson : RealExpr → Lean.Json
  | .const c => Lean.Json.mkObj [("op", Lean.toJson "const"), ("val", encodeHybridRatJson c)]
  | .var v   => Lean.Json.mkObj [("op", Lean.toJson "var"), ("name", Lean.toJson v)]
  | .add l r => Lean.Json.mkObj [("op", Lean.toJson "add"), ("lhs", encodeRealExprJson l), ("rhs", encodeRealExprJson r)]
  | .sub l r => Lean.Json.mkObj [("op", Lean.toJson "sub"), ("lhs", encodeRealExprJson l), ("rhs", encodeRealExprJson r)]
  | .mul l r => Lean.Json.mkObj [("op", Lean.toJson "mul"), ("lhs", encodeRealExprJson l), ("rhs", encodeRealExprJson r)]
  | .sqr a   => Lean.Json.mkObj [("op", Lean.toJson "sqr"), ("arg", encodeRealExprJson a)]

/-- Structural fuel-bounded JSON AST decoder for `RealExpr`. -/
@[expose] def decodeRealExprJsonAux : Nat → Lean.Json → Except String RealExpr
  | 0, _ => .error "RealExpr JSON nesting depth exceeded"
  | fuel + 1, j =>
    match j.getInt? with
    | .ok n => .ok (.const (Rat.ofInt n))
    | .error _ =>
      match j.getStr? with
      | .ok v => .ok (.var v)
      | .error _ => do
        let op ← j.getObjValAs? String "op"
        if op == "const" then
          let valJ ← j.getObjVal? "val"
          let q ← decodeHybridRatJson valJ
          pure (.const q)
        else if op == "var" then
          let name ← j.getObjValAs? String "name"
          pure (.var name)
        else if op == "add" then
          let lJ ← j.getObjVal? "lhs"
          let rJ ← j.getObjVal? "rhs"
          let l ← decodeRealExprJsonAux fuel lJ
          let r ← decodeRealExprJsonAux fuel rJ
          pure (.add l r)
        else if op == "sub" then
          let lJ ← j.getObjVal? "lhs"
          let rJ ← j.getObjVal? "rhs"
          let l ← decodeRealExprJsonAux fuel lJ
          let r ← decodeRealExprJsonAux fuel rJ
          pure (.sub l r)
        else if op == "mul" then
          let lJ ← j.getObjVal? "lhs"
          let rJ ← j.getObjVal? "rhs"
          let l ← decodeRealExprJsonAux fuel lJ
          let r ← decodeRealExprJsonAux fuel rJ
          pure (.mul l r)
        else if op == "sqr" then
          let aJ ← j.getObjVal? "arg"
          let a ← decodeRealExprJsonAux fuel aJ
          pure (.sqr a)
        else
          .error s!"unknown RealExpr op: {op}"

/-- Decode an arbitrary `RealExpr` AST from `Lean.Json` (supports integer literals, variable strings,
and structured operator nodes `const`, `var`, `add`, `sub`, `mul`, `sqr`). -/
@[expose] def decodeRealExprJson (j : Lean.Json) : Except String RealExpr :=
  decodeRealExprJsonAux 64 j

@[expose] def encodeNamedBoxJson (box : List (String × Interval)) : Lean.Json :=
  Lean.Json.arr <| box.toArray.map fun (v, iv) =>
    Lean.Json.mkObj [("var", Lean.toJson v), ("lo", encodeHybridRatJson iv.lo), ("hi", encodeHybridRatJson iv.hi)]

@[expose] def decodeNamedIntervalEntryJson (j : Lean.Json) : Except String (String × Interval) := do
  let v ← j.getObjValAs? String "var"
  match j.getObjVal? "interval" with
  | .ok ivJ =>
    let iv ← decodeIntervalJson ivJ
    pure (v, iv)
  | .error _ =>
    let iv ← decodeIntervalJson j
    pure (v, iv)

@[expose] def decodeNamedBoxJson (j : Lean.Json) : Except String (List (String × Interval)) := do
  let arr ← j.getArr?
  arr.toList.mapM decodeNamedIntervalEntryJson

@[expose] def encodeOdeSystemJson (sys : OdeSystem) : Lean.Json :=
  Lean.Json.mkObj
    [ ("fields", Lean.Json.arr <| sys.fields.toArray.map fun (v, e) =>
        Lean.Json.mkObj [("var", Lean.toJson v), ("rhs", encodeRealExprJson e)])
    , ("dt", encodeHybridRatJson sys.dt)
    , ("remainderPad", encodeIntervalJson sys.remainderPad) ]

@[expose] def decodeOdeFieldEntryJson (j : Lean.Json) : Except String (String × RealExpr) := do
  let v ← j.getObjValAs? String "var"
  let rhsJ ← j.getObjVal? "rhs"
  let rhs ← decodeRealExprJson rhsJ
  pure (v, rhs)

@[expose] def decodeOdeSystemJson (j : Lean.Json) : Except String OdeSystem := do
  let fsJ ← j.getObjVal? "fields"
  let fsArr ← fsJ.getArr?
  let fields ← fsArr.toList.mapM decodeOdeFieldEntryJson
  let dtJ ← j.getObjVal? "dt"
  let dt ← decodeHybridRatJson dtJ
  let padJ ← j.getObjVal? "remainderPad"
  let remainderPad ← decodeIntervalJson padJ
  pure { fields, dt, remainderPad }

@[expose] def encodeHybridModeJson (m : HybridMode) : Lean.Json :=
  Lean.Json.mkObj
    [ ("modeId", Lean.toJson m.modeId)
    , ("ode", encodeOdeSystemJson m.ode)
    , ("invariantBounds", encodeNamedBoxJson m.invariantBounds) ]

@[expose] def decodeHybridModeJson (j : Lean.Json) : Except String HybridMode := do
  let modeId ← j.getObjValAs? String "modeId"
  let odeJ ← j.getObjVal? "ode"
  let ode ← decodeOdeSystemJson odeJ
  let invJ ← j.getObjVal? "invariantBounds"
  let invariantBounds ← decodeNamedBoxJson invJ
  pure { modeId, ode, invariantBounds }

@[expose] def encodeAffineResetMapJson (rm : AffineResetMap) : Lean.Json :=
  Lean.Json.arr <| rm.resets.toArray.map fun (v, scale, offset) =>
    Lean.Json.mkObj
      [ ("var", Lean.toJson v)
      , ("scale", encodeHybridRatJson scale)
      , ("offset", encodeHybridRatJson offset) ]

@[expose] def decodeAffineResetEntryJson (j : Lean.Json) : Except String (String × CanonicalRat × CanonicalRat) := do
  let v ← j.getObjValAs? String "var"
  let sJ ← j.getObjVal? "scale"
  let oJ ← j.getObjVal? "offset"
  let scale ← decodeHybridRatJson sJ
  let offset ← decodeHybridRatJson oJ
  pure (v, scale, offset)

@[expose] def decodeAffineResetMapJson (j : Lean.Json) : Except String AffineResetMap := do
  let arr ← j.getArr?
  let resets ← arr.toList.mapM decodeAffineResetEntryJson
  pure { resets }

@[expose] def encodeHybridJumpJson (jmp : HybridJump) : Lean.Json :=
  Lean.Json.mkObj
    [ ("fromMode", Lean.toJson jmp.fromMode)
    , ("toMode", Lean.toJson jmp.toMode)
    , ("guardBounds", encodeNamedBoxJson jmp.guardBounds)
    , ("resetMap", encodeAffineResetMapJson jmp.resetMap) ]

@[expose] def decodeHybridJumpJson (j : Lean.Json) : Except String HybridJump := do
  let fromMode ← j.getObjValAs? String "fromMode"
  let toMode ← j.getObjValAs? String "toMode"
  let guardJ ← j.getObjVal? "guardBounds"
  let guardBounds ← decodeNamedBoxJson guardJ
  let resetJ ← j.getObjVal? "resetMap"
  let resetMap ← decodeAffineResetMapJson resetJ
  pure { fromMode, toMode, guardBounds, resetMap }

@[expose] def encodeHybridAutomatonJson (aut : HybridAutomaton) : Lean.Json :=
  Lean.Json.mkObj
    [ ("modes", Lean.Json.arr <| aut.modes.toArray.map encodeHybridModeJson)
    , ("jumps", Lean.Json.arr <| aut.jumps.toArray.map encodeHybridJumpJson)
    , ("safeEnvelope", encodeNamedBoxJson aut.safeEnvelope) ]

@[expose] def decodeHybridAutomatonJson (j : Lean.Json) : Except String HybridAutomaton := do
  let modesJ ← j.getObjVal? "modes"
  let modesArr ← modesJ.getArr?
  let modes ← modesArr.toList.mapM decodeHybridModeJson
  let jumpsJ ← j.getObjVal? "jumps"
  let jumpsArr ← jumpsJ.getArr?
  let jumps ← jumpsArr.toList.mapM decodeHybridJumpJson
  let safeJ ← j.getObjVal? "safeEnvelope"
  let safeEnvelope ← decodeNamedBoxJson safeJ
  pure { modes, jumps, safeEnvelope }

@[expose] def hybridJsonNatToChars : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    let d := Char.ofNat (48 + (n % 10))
    let q := n / 10
    if q == 0 then d :: acc
    else hybridJsonNatToChars fuel q (d :: acc)

@[expose] def hybridJsonIntToStr : Int → String
  | .ofNat n   => String.ofList (hybridJsonNatToChars 32 n [])
  | .negSucc n => "-" ++ String.ofList (hybridJsonNatToChars 32 (n + 1) [])

@[expose] def hybridJsonJoinSep (sep : String) : List String → String
  | []      => ""
  | [x]     => x
  | x :: xs => x ++ sep ++ hybridJsonJoinSep sep xs

@[expose] def hybridJsonEscapeChars : List Char → List Char
  | [] => []
  | '"' :: cs  => '\\' :: '"' :: hybridJsonEscapeChars cs
  | '\\' :: cs => '\\' :: '\\' :: hybridJsonEscapeChars cs
  | '\n' :: cs => '\\' :: 'n' :: hybridJsonEscapeChars cs
  | '\r' :: cs => '\\' :: 'r' :: hybridJsonEscapeChars cs
  | '\t' :: cs => '\\' :: 't' :: hybridJsonEscapeChars cs
  | c :: cs    => c :: hybridJsonEscapeChars cs

@[expose] def hybridJsonQuoteStr (s : String) : String :=
  String.ofList ('"' :: (hybridJsonEscapeChars s.toList ++ ['"']))

/-- Kernel-reducible structural serializer for `Lean.Json` (zero `partial def`). -/
@[expose] def hybridJsonCompressAux : Nat → Lean.Json → String
  | 0, _ => "null"
  | _ + 1, .null => "null"
  | _ + 1, .bool true => "true"
  | _ + 1, .bool false => "false"
  | _ + 1, .num n =>
    if n.exponent == 0 then hybridJsonIntToStr n.mantissa else n.toString
  | _ + 1, .str s => hybridJsonQuoteStr s
  | fuel + 1, .arr elems =>
    "[" ++ hybridJsonJoinSep "," (elems.toList.map (hybridJsonCompressAux fuel)) ++ "]"
  | fuel + 1, .obj kvs =>
    let pairs := kvs.foldl (fun acc k v => (hybridJsonQuoteStr k ++ ":" ++ hybridJsonCompressAux fuel v) :: acc) []
    "{" ++ hybridJsonJoinSep "," pairs.reverse ++ "}"

@[expose] def hybridJsonCompress (j : Lean.Json) : String :=
  hybridJsonCompressAux 32 j

@[expose] def hybridJsonSkipWs : List Char → List Char
  | [] => []
  | c :: cs =>
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then hybridJsonSkipWs cs else c :: cs

@[expose] def hybridJsonParseStrBody : List Char → List Char → Option (String × List Char)
  | [], _ => none
  | '"' :: rest, rev => some (String.ofList rev.reverse, rest)
  | '\\' :: '"' :: rest, rev => hybridJsonParseStrBody rest ('"' :: rev)
  | '\\' :: '\\' :: rest, rev => hybridJsonParseStrBody rest ('\\' :: rev)
  | '\\' :: '/' :: rest, rev => hybridJsonParseStrBody rest ('/' :: rev)
  | '\\' :: 'n' :: rest, rev => hybridJsonParseStrBody rest ('\n' :: rev)
  | '\\' :: 'r' :: rest, rev => hybridJsonParseStrBody rest ('\r' :: rev)
  | '\\' :: 't' :: rest, rev => hybridJsonParseStrBody rest ('\t' :: rev)
  | '\\' :: _, _ => none
  | c :: rest, rev => hybridJsonParseStrBody rest (c :: rev)

@[expose] def hybridJsonParseDigits : List Char → Nat → Bool → Nat × Bool × List Char
  | [], acc, has => (acc, has, [])
  | c :: rest, acc, has =>
    if '0' ≤ c && c ≤ '9' then
      hybridJsonParseDigits rest (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      (acc, has, c :: rest)

@[expose] def hybridJsonParseFracDigits : List Char → Nat → Nat → Nat × Nat × List Char
  | [], acc, exp => (acc, exp, [])
  | c :: rest, acc, exp =>
    if '0' ≤ c && c ≤ '9' then
      hybridJsonParseFracDigits rest (acc * 10 + (c.toNat - '0'.toNat)) (exp + 1)
    else
      (acc, exp, c :: rest)

@[expose] def hybridJsonParseNum (cs : List Char) : Option (Lean.JsonNumber × List Char) :=
  let (neg, cs1) :=
    match cs with
    | '-' :: r => (true, r)
    | _ => (false, cs)
  let (intPart, hasInt, cs2) := hybridJsonParseDigits cs1 0 false
  if !hasInt then none
  else
    match cs2 with
    | '.' :: fracCs =>
      let (fracAcc, fracExp, cs3) := hybridJsonParseFracDigits fracCs intPart 0
      if fracExp == 0 then none
      else
        let m : Int := if neg then -(Int.ofNat fracAcc) else Int.ofNat fracAcc
        some (⟨m, fracExp⟩, cs3)
    | _ =>
      let m : Int := if neg then -(Int.ofNat intPart) else Int.ofNat intPart
      some (⟨m, 0⟩, cs2)

@[expose] def hybridJsonParseArrAux (parseElem : List Char → Option (Lean.Json × List Char)) :
    Nat → List Char → List Lean.Json → Option (List Lean.Json × List Char)
  | 0, _, _ => none
  | itemFuel + 1, cs, rev => do
    let (v, cs1) ← parseElem cs
    match hybridJsonSkipWs cs1 with
    | ']' :: rest => some ((v :: rev).reverse, rest)
    | ',' :: rest => hybridJsonParseArrAux parseElem itemFuel (hybridJsonSkipWs rest) (v :: rev)
    | _ => none

@[expose] def hybridJsonParseObjAux (parseElem : List Char → Option (Lean.Json × List Char)) :
    Nat → List Char → List (String × Lean.Json) → Option (List (String × Lean.Json) × List Char)
  | 0, _, _ => none
  | itemFuel + 1, cs, rev =>
    match hybridJsonSkipWs cs with
    | '"' :: keyCs => do
      let (k, cs1) ← hybridJsonParseStrBody keyCs []
      match hybridJsonSkipWs cs1 with
      | ':' :: valCs => do
        let (v, cs2) ← parseElem (hybridJsonSkipWs valCs)
        match hybridJsonSkipWs cs2 with
        | '}' :: rest => some (((k, v) :: rev).reverse, rest)
        | ',' :: rest => hybridJsonParseObjAux parseElem itemFuel rest ((k, v) :: rev)
        | _ => none
      | _ => none
    | _ => none

/-- Kernel-reducible structural recursive-descent `Lean.Json` parser (zero `partial def`). -/
@[expose] def hybridJsonParseAux : Nat → List Char → Option (Lean.Json × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match hybridJsonSkipWs cs with
    | [] => none
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
    | '"' :: strCs => do
      let (s, rest) ← hybridJsonParseStrBody strCs []
      some (.str s, rest)
    | '[' :: arrCs =>
      match hybridJsonSkipWs arrCs with
      | ']' :: rest => some (.arr #[], rest)
      | arrCs' => do
        let (items, rest) ← hybridJsonParseArrAux (hybridJsonParseAux fuel) (arrCs'.length + 1) arrCs' []
        some (.arr items.toArray, rest)
    | '{' :: objCs =>
      match hybridJsonSkipWs objCs with
      | '}' :: rest => some (Lean.Json.mkObj [], rest)
      | objCs' => do
        let (fields, rest) ← hybridJsonParseObjAux (hybridJsonParseAux fuel) (objCs'.length + 1) objCs' []
        some (Lean.Json.mkObj fields, rest)
    | numCs => do
      let (n, rest) ← hybridJsonParseNum numCs
      some (.num n, rest)

@[expose] def hybridJsonParse (s : String) : Except String Lean.Json :=
  match hybridJsonParseAux 32 s.toList with
  | some (j, rest) =>
    if (hybridJsonSkipWs rest).isEmpty then .ok j
    else .error "trailing characters in JSON"
  | none => .error "malformed JSON"

/-- Render a `HybridProblem` deterministically as a general AST JSON string. -/
@[expose] def renderHybridProblemJson (p : HybridProblem) : String :=
  hybridJsonCompress <| Lean.Json.mkObj
    [ ("automaton", encodeHybridAutomatonJson p.automaton)
    , ("varName", Lean.toJson p.varName)
    , ("initMode", Lean.toJson p.initMode)
    , ("initLo", Lean.toJson p.initLo)
    , ("initHi", Lean.toJson p.initHi)
    , ("unsafeLo", Lean.toJson p.unsafeLo)
    , ("unsafeHi", Lean.toJson p.unsafeHi) ]

/-- Decode a `HybridProblem` from a general JSON AST string representation
(`{"automaton":{...},"varName":...,"initMode":...,"initLo":...,"initHi":...,"unsafeLo":...,"unsafeHi":...}`). -/
@[expose] def decodeHybridProblem (s : String) : Except String HybridProblem :=
  match hybridJsonParse s with
  | .error _ => .error "invalid HybridProblem JSON"
  | .ok j =>
    match j.getObjVal? "automaton",
          j.getObjValAs? String "varName",
          j.getObjValAs? String "initMode",
          j.getObjValAs? Int "initLo",
          j.getObjValAs? Int "initHi",
          j.getObjValAs? Int "unsafeLo",
          j.getObjValAs? Int "unsafeHi" with
    | .ok autJ, .ok varName, .ok initMode, .ok initLo, .ok initHi, .ok unsafeLo, .ok unsafeHi => do
      let automaton ← decodeHybridAutomatonJson autJ
      decodeHybridProblemData
        ({ automaton, varName, initMode, initLo, initHi, unsafeLo, unsafeHi } : HybridProblem).toData
    | _, _, _, _, _, _, _ => .error "invalid HybridProblem JSON: missing required fields"

/-- Encode a `HybridAction` as `Lean.Json`. -/
@[expose] def encodeHybridActionJson : HybridAction → Lean.Json
  | .flowStep          => Lean.Json.mkObj [("action", Lean.toJson "flowStep")]
  | .jumpTo targetMode => Lean.Json.mkObj [("action", Lean.toJson "jumpTo"), ("targetMode", Lean.toJson targetMode)]

/-- Decode an arbitrary `HybridAction` from `Lean.Json` (supports structured objects
`{"action": "flowStep"}` / `{"action": "jumpTo", "targetMode": mode}` / `{"jumpTo": mode}` as well
as string shorthand `"flowStep"` or `"jumpTo:<mode>"` for any mode identifier). -/
@[expose] def decodeHybridActionJson (j : Lean.Json) : Except String HybridAction :=
  match j.getStr? with
  | .ok str =>
    if str == "flowStep" then
      .ok .flowStep
    else if str.startsWith "jumpTo:" then
      let target := (str.drop 7).toString
      if target.isEmpty then .error "empty targetMode in HybridAction JSON"
      else .ok (.jumpTo target)
    else
      .error "invalid HybridAction JSON"
  | .error _ =>
    match j.getObjValAs? String "jumpTo" with
    | .ok targetMode =>
      if targetMode.isEmpty then .error "empty targetMode in HybridAction JSON"
      else .ok (.jumpTo targetMode)
    | .error _ =>
      match j.getObjValAs? String "action" with
      | .ok "flowStep" => .ok .flowStep
      | .ok "jumpTo" => do
        let targetMode ← j.getObjValAs? String "targetMode"
        if targetMode.isEmpty then .error "empty targetMode in HybridAction JSON"
        else .ok (.jumpTo targetMode)
      | _ => .error "invalid HybridAction JSON"

/-- Render a `HybridCert` deterministically as a general AST JSON string. -/
@[expose] def renderHybridCertJson (c : HybridCert) : String :=
  hybridJsonCompress <| Lean.Json.mkObj
    [ ("schedule", Lean.Json.arr <| c.schedule.toArray.map encodeHybridActionJson)
    , ("expectedFinalMode", Lean.toJson c.expectedFinalMode)
    , ("claimedSteps", Lean.toJson c.claimedSteps) ]

/-- Decode a `HybridCert` from a general JSON AST string representation
(`{"schedule":[...],"expectedFinalMode":...,"claimedSteps":...}`). -/
@[expose] def decodeHybridCert (s : String) : Except String HybridCert :=
  match hybridJsonParse s with
  | .error _ => .error "invalid HybridCert JSON"
  | .ok j =>
    match j.getObjValAs? String "expectedFinalMode",
          j.getObjValAs? Nat "claimedSteps",
          j.getObjValAs? (Array Lean.Json) "schedule" with
    | .ok finalMode, .ok steps, .ok schedArr => do
      let sched ← schedArr.toList.mapM decodeHybridActionJson
      decodeHybridCertData
        ({ schedule := sched, expectedFinalMode := finalMode, claimedSteps := steps } : HybridCert).toData
    | _, _, _ => .error "invalid HybridCert JSON: missing required fields"

/-- Registered `Obend.Judge.Format` for `"hybrid-flowpipe@1"`. -/
@[expose] def hybridFlowpipeFormat : Obend.Judge.Format where
  name := "hybrid-flowpipe@1"
  version := "1"
  Obj := HybridProblem
  Cert := HybridCert
  decodeObj := decodeHybridProblem
  decodeCert := decodeHybridCert
  trust := .kernel
  regime := .decidable
  bad := (demoHybridProblem, badHybridCert)
  badGrade := 0
  bad_refused :=
    ⟨"flowpipe_invariant_or_unsafe_zone_violation", [], hybridFlowpipe_bad_refused⟩

end Obend.Analysis
end
