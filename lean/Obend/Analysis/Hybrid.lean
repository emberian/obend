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

/-- Resolve a registered `HybridAutomaton` by `automatonId`. -/
@[expose] def resolveHybridAutomaton? (automatonId : String) : Option HybridAutomaton :=
  if decide (automatonId = "thermostat") then
    some thermostatLinearAutomaton
  else if decide (automatonId = "thermostat-damped") then
    some thermostatHybridAutomaton
  else
    none

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
   For any multi-step `CellTrace` governed by `odeSafetyCellContract maxTemp` from an initial state
   satisfying `Holds (odeSafetyCellContract maxTemp).invariant s₀`, the final state `s_final`
   satisfies `Holds (odeSafetyCellContract maxTemp).invariant s_final`. -/
theorem hybrid_flowpipe_safety_admits_contract
    (maxTemp : Nat) (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds (odeSafetyCellContract maxTemp).invariant s₀)
    (h_tr : CellTrace (odeSafetyCellContract maxTemp).law s₀ steps s_final) :
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
    Holds (odeSafetyCellContract maxTemp).invariant s_final := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact cellContract_trace_sound (odeSafetyCellContract maxTemp) s₀ s_final steps h_init h_tr

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

/-- Hybrid flowpipe verification problem specifying initial mode/box and unsafe zone bounds. -/
structure HybridProblem where
  automatonId : String
  varName     : String
  initMode    : String
  initLo      : Int
  initHi      : Int
  unsafeLo    : Int
  unsafeHi    : Int
  deriving @[expose] DecidableEq, Repr

/-- Deterministic `Obend.Core.Data` encoding of `HybridProblem`. -/
@[expose] def HybridProblem.toData (p : HybridProblem) : Data :=
  .record
    [ ("automatonId", .label p.automatonId)
    , ("varName", .label p.varName)
    , ("initMode", .label p.initMode)
    , ("initLo", intToData p.initLo)
    , ("initHi", intToData p.initHi)
    , ("unsafeLo", intToData p.unsafeLo)
    , ("unsafeHi", intToData p.unsafeHi) ]

/-- Deterministic `Obend.Core.Data` decoding of `HybridProblem`. -/
@[expose] def HybridProblem.ofData? : Data → Option HybridProblem
  | .record
      [ ("automatonId", .label automatonId)
      , ("varName", .label varName)
      , ("initMode", .label initMode)
      , ("initLo", initLoData)
      , ("initHi", initHiData)
      , ("unsafeLo", unsafeLoData)
      , ("unsafeHi", unsafeHiData) ] => do
    let initLo ← intOfData? initLoData
    let initHi ← intOfData? initHiData
    let unsafeLo ← intOfData? unsafeLoData
    let unsafeHi ← intOfData? unsafeHiData
    pure { automatonId, varName, initMode, initLo, initHi, unsafeLo, unsafeHi }
  | _ => none

/-- Exact roundtrip theorem for `HybridProblem.toData` / `HybridProblem.ofData?`. -/
theorem HybridProblem.ofData_toData (p : HybridProblem) :
    HybridProblem.ofData? p.toData = some p := by
  cases p
  simp [HybridProblem.toData, HybridProblem.ofData?, intOfData_toData]

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
1. Resolves `aut ← resolveHybridAutomaton? p.automatonId` and checks `p.varName = "T"`,
2. `p.initLo ≤ p.initHi` and `p.unsafeLo ≤ p.unsafeHi`,
3. `c.claimedSteps = c.schedule.length`,
4. `runHybridAutomatonTube aut p.varName p.unsafeInterval c.schedule p.initState` succeeds across
   all continuous `stepHybridFlow` and discrete `stepHybridJump?` transitions (checking both discrete
   slices AND continuous-time rough enclosures `xTildeBox` against mode invariants, `safeEnvelope`,
   and `p.unsafeInterval`),
5. The terminal hybrid state reaches `c.expectedFinalMode`. -/
@[expose] def verifyFlowpipe (p : HybridProblem) (c : HybridCert) : Bool :=
  decide (p.varName = "T") &&
  decide (p.initLo ≤ p.initHi) &&
  decide (p.unsafeLo ≤ p.unsafeHi) &&
  decide (c.claimedSteps = c.schedule.length) &&
  match resolveHybridAutomaton? p.automatonId with
  | none => false
  | some aut =>
    match runHybridAutomatonTube aut p.varName p.unsafeInterval c.schedule p.initState with
    | some finalMode => decide (finalMode = c.expectedFinalMode)
    | none           => false

/-- Concrete valid and invalid hybrid flowpipe problem/certificate fixtures. -/
@[expose] def demoHybridProblem : HybridProblem :=
  { automatonId := "thermostat"
  , varName     := "T"
  , initMode    := "heating"
  , initLo      := 24
  , initHi      := 26
  , unsafeLo    := 36
  , unsafeHi    := 50 }

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

-- fixture kept (2026-11-04): target of #tooth at Obend/Analysis/Hybrid.lean:548
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

/-- `Obend.Judge` instance for `(HybridProblem, HybridCert)`. -/
@[expose] instance hybridFlowpipeJudge : Obend.Judge HybridProblem HybridCert where
  Clause := String
  Meaning p c := verifyFlowpipe p c = true
  check := checkHybridFlowpipe
  sound := by
    intro _r o c h_ok
    unfold checkHybridFlowpipe at h_ok
    cases h : verifyFlowpipe o c
    · rw [h] at h_ok
      contradiction
    · rfl
  refutes _ := false
  refuted := by
    intro _r _o _c _k _p _h_ref h_false
    contradiction
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    refine ⟨c, 0, ?_⟩
    simp [checkHybridFlowpipe, hc]
  mono := by
    intro _r _r' _o _c _hle _hunc
    rfl

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem hybridFlowpipe_bad_refused :
    checkHybridFlowpipe 0 demoHybridProblem badHybridCert =
      .refused "flowpipe_invariant_or_unsafe_zone_violation" [] := by decide +kernel

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

/-- Decode a `HybridProblem` from a string wire representation:
supports `"thermostat-default"`, `"thermostat-damped"`, and structured JSON payloads
`{"automatonId":...,"varName":...,"initMode":...,"initLo":...,"initHi":...,"unsafeLo":...,"unsafeHi":...}`. -/
@[expose] def decodeHybridProblem (s : String) : Except String HybridProblem :=
  if decide (s = "thermostat-default") then
    decodeHybridProblemData demoHybridProblem.toData
  else if decide (s = "thermostat-damped") then
    decodeHybridProblemData { demoHybridProblem with automatonId := "thermostat-damped" }.toData
  else
    match Lean.Json.parse s with
    | .error _ => .error "unknown HybridProblem wire payload"
    | .ok j =>
      match j.getObjValAs? String "automatonId",
            j.getObjValAs? String "varName",
            j.getObjValAs? String "initMode",
            j.getObjValAs? Int "initLo",
            j.getObjValAs? Int "initHi",
            j.getObjValAs? Int "unsafeLo",
            j.getObjValAs? Int "unsafeHi" with
      | .ok autId, .ok varName, .ok initMode, .ok initLo, .ok initHi, .ok unsafeLo, .ok unsafeHi =>
        decodeHybridProblemData
          ({ automatonId := autId
           , varName     := varName
           , initMode    := initMode
           , initLo      := initLo
           , initHi      := initHi
           , unsafeLo    := unsafeLo
           , unsafeHi    := unsafeHi } : HybridProblem).toData
      | _, _, _, _, _, _, _ => .error "unknown HybridProblem wire payload"

/-- Decode a `HybridAction` from a JSON string (`"flowStep"` or `"jumpTo:<mode>"`). -/
@[expose] def decodeHybridActionJson (j : Lean.Json) : Except String HybridAction :=
  match j.getStr? with
  | .ok "flowStep" => .ok .flowStep
  | .ok "jumpTo:cooling" => .ok (.jumpTo "cooling")
  | .ok "jumpTo:heating" => .ok (.jumpTo "heating")
  | _ => .error "invalid HybridAction JSON"

/-- Decode a `HybridCert` from a string wire representation:
supports `"valid-cooling-switch"`, `"bad-overheat-runaway"`, `"bad-step-count"`, and structured JSON payloads. -/
@[expose] def decodeHybridCert (s : String) : Except String HybridCert :=
  if decide (s = "valid-cooling-switch") then
    decodeHybridCertData validHybridCert.toData
  else if decide (s = "bad-overheat-runaway") then
    decodeHybridCertData badHybridCert.toData
  else if decide (s = "bad-step-count") then
    decodeHybridCertData badStepCountHybridCert.toData
  else
    match Lean.Json.parse s with
    | .error _ => .error "unknown HybridCert wire payload"
    | .ok j =>
      match j.getObjValAs? String "expectedFinalMode",
            j.getObjValAs? Nat "claimedSteps",
            j.getObjValAs? (Array Lean.Json) "schedule" with
      | .ok finalMode, .ok steps, .ok schedArr => do
        let sched ← schedArr.toList.mapM decodeHybridActionJson
        decodeHybridCertData
          ({ schedule := sched, expectedFinalMode := finalMode, claimedSteps := steps } : HybridCert).toData
      | _, _, _ => .error "unknown HybridCert wire payload"

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
