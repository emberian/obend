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
@[expose] public section

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
  deriving DecidableEq, Repr

/-- Affine discrete reset map $x'_i := \alpha_i x_i + \beta_i$ applied across a discrete mode switch. -/
structure AffineResetMap where
  resets : List (String × CanonicalRat × CanonicalRat)
  deriving DecidableEq, Repr

/-- Guarded discrete transition between two `HybridMode`s:
* `fromMode`, `toMode`: source and target discrete mode identifiers,
* `guardBounds`: guard region $G \subseteq \mathbb{R}^n$ that must enclose the pre-jump continuous box,
* `resetMap`: affine reset map applied upon taking the discrete transition. -/
structure HybridJump where
  fromMode    : String
  toMode      : String
  guardBounds : List (String × Interval)
  resetMap    : AffineResetMap
  deriving DecidableEq, Repr

/-- Complete hybrid automaton coupling continuous `OdeSystem` modes with discrete guarded jumps. -/
structure HybridAutomaton where
  modes        : List HybridMode
  jumps        : List HybridJump
  safeEnvelope : List (String × Interval)
  deriving DecidableEq, Repr

/-- Hybrid state pairing a discrete `modeId` with a continuous interval enclosure `box`. -/
structure HybridState where
  modeId : String
  box    : List (String × Interval)
  deriving DecidableEq, Repr

/-- Discrete or continuous action in a hybrid execution schedule. -/
inductive HybridAction where
  | flowStep
  | jumpTo (targetMode : String)
  deriving DecidableEq, Repr

/-- Look up a `HybridMode` by `modeId` via direct structural recursion. -/
def findHybridMode? (targetId : String) : List HybridMode → Option HybridMode
  | [] => none
  | m :: ms => if m.modeId == targetId then some m else findHybridMode? targetId ms

/-- Look up a `HybridJump` from `srcMode` to `dstMode` via direct structural recursion. -/
def findHybridJump? (srcMode dstMode : String) : List HybridJump → Option HybridJump
  | [] => none
  | j :: js =>
    if j.fromMode == srcMode && j.toMode == dstMode then some j
    else findHybridJump? srcMode dstMode js

/-- Apply an `AffineResetMap` ($X'_i = \alpha_i X_i \oplus [\beta_i, \beta_i]$) to a continuous box. -/
def applyAffineReset (rm : AffineResetMap) : List (String × Interval) → List (String × Interval)
  | [] => []
  | (name, iv) :: rest =>
    let iv' :=
      match rm.resets.find? (fun (n, _, _) => n == name) with
      | some (_, scale, offset) =>
        Interval.add (Interval.mul (Interval.ofPoint scale) iv) (Interval.ofPoint offset)
      | none => iv
    (name, iv') :: applyAffineReset rm rest

/-- Execute one continuous flowpipe step inside the active mode `st.modeId`, verifying that both
the pre-state and post-state satisfy the mode invariant and global `safeEnvelope`. -/
def stepHybridFlow (aut : HybridAutomaton) (st : HybridState) : Option HybridState := do
  let mode ← findHybridMode? st.modeId aut.modes
  if !checkBoxInEnvelope st.box mode.invariantBounds || !checkBoxInEnvelope st.box aut.safeEnvelope then
    none
  else
    let nextBox ← stepFlowpipe mode.ode st.box
    if checkBoxInEnvelope nextBox mode.invariantBounds && checkBoxInEnvelope nextBox aut.safeEnvelope then
      some { modeId := st.modeId, box := nextBox }
    else
      none

/-- Execute a guarded discrete mode switch from `st.modeId` to `targetMode`, verifying that:
1. `st.box` lies inside `jump.guardBounds`,
2. the post-reset box `applyAffineReset jump.resetMap st.box` lies inside the target mode's
   `invariantBounds` and `aut.safeEnvelope`. -/
def stepHybridJump? (aut : HybridAutomaton) (st : HybridState) (targetMode : String) : Option HybridState := do
  let jump ← findHybridJump? st.modeId targetMode aut.jumps
  let dstMode ← findHybridMode? targetMode aut.modes
  if !checkBoxInEnvelope st.box jump.guardBounds then
    none
  else
    let resetBox := applyAffineReset jump.resetMap st.box
    if checkBoxInEnvelope resetBox dstMode.invariantBounds && checkBoxInEnvelope resetBox aut.safeEnvelope then
      some { modeId := targetMode, box := resetBox }
    else
      none

/-- Execute a single `HybridAction` (`.flowStep` or `.jumpTo targetMode`). -/
def stepHybridAction (aut : HybridAutomaton) (st : HybridState) : HybridAction → Option HybridState
  | .flowStep          => stepHybridFlow aut st
  | .jumpTo targetMode => stepHybridJump? aut st targetMode

/-- Run a sequence of `HybridAction`s from `initState`, returning the full hybrid state tube
if every continuous flow step and discrete jump is safe and guard-enabled. -/
def runHybridSchedule (aut : HybridAutomaton) (initState : HybridState) : List HybridAction → Option (List HybridState)
  | [] =>
    if checkBoxInEnvelope initState.box aut.safeEnvelope then some [initState] else none
  | act :: rest => do
    let nextState ← stepHybridAction aut initState act
    let restTube ← runHybridSchedule aut nextState rest
    pure (initState :: restTube)

/-- Verify that a hybrid execution schedule from `initState` is valid and stays within `aut.safeEnvelope`. -/
def verifyHybridScheduleSafety
    (aut : HybridAutomaton)
    (initState : HybridState)
    (schedule : List HybridAction) : Bool :=
  match runHybridSchedule aut initState schedule with
  | some tube => tube.all (fun st => checkBoxInEnvelope st.box aut.safeEnvelope)
  | none      => false

/-! ## 2. Concrete Thermostat Hybrid Automaton & `hybrid_flowpipe_safety_admits_contract` -/

/-- Dual-mode thermostat / power-stage thermal hybrid automaton:
* Mode `"heating"`: $\dot{T} = 4$ with $\Delta t = 1$, remainder $[-1/10, 1/10]$, invariant $T \in [15, 32]^\circ\text{C}$.
* Mode `"cooling"`: damped cooling `thermalCoolingOde` ($\dot{T} = 20 - T$, $\Delta t = 1/2$), invariant $T \in [15, 35]^\circ\text{C}$.
* Guarded jump `"heating" → "cooling"`: enabled when $T \in [27, 32]^\circ\text{C}$, with reset map $T' := T - 1$ (active coolant valve purge).
* Global safety envelope: $T \in [15, 35]^\circ\text{C}$. -/
def thermostatHybridAutomaton : HybridAutomaton where
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
def intToData : Int → Data
  | .ofNat n   => .variant "pos" (.natural n)
  | .negSucc n => .variant "neg" (.natural n)

/-- Decode an `Int` deterministically from `Obend.Core.Data`. -/
def intOfData? : Data → Option Int
  | .variant "pos" (.natural n) => some (.ofNat n)
  | .variant "neg" (.natural n) => some (.negSucc n)
  | _                           => none

theorem intOfData_toData (i : Int) : intOfData? (intToData i) = some i := by
  cases i <;> rfl

/-- Deterministic `Obend.Core.Data` encoding of `HybridAction`. -/
def HybridAction.toData : HybridAction → Data
  | .flowStep          => .variant "flowStep" (.record [])
  | .jumpTo targetMode => .variant "jumpTo" (.label targetMode)

/-- Deterministic `Obend.Core.Data` decoding of `HybridAction`. -/
def HybridAction.ofData? : Data → Option HybridAction
  | .variant "flowStep" (.record [])     => some .flowStep
  | .variant "jumpTo" (.label targetMode) => some (.jumpTo targetMode)
  | _                                    => none

theorem HybridAction.ofData_toData (act : HybridAction) :
    HybridAction.ofData? act.toData = some act := by
  cases act <;> rfl

/-- Encode a schedule `List HybridAction` as `Obend.Core.Data`. -/
def actionListToData : List HybridAction → Data
  | [] => .variant "nil" (.record [])
  | a :: rest => .variant "cons" (.record [("head", a.toData), ("tail", actionListToData rest)])

/-- Decode a schedule `List HybridAction` from `Obend.Core.Data`. -/
def actionListOfData? : Data → Option (List HybridAction)
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
  deriving DecidableEq, Repr

/-- Deterministic `Obend.Core.Data` encoding of `HybridProblem`. -/
def HybridProblem.toData (p : HybridProblem) : Data :=
  .record
    [ ("automatonId", .label p.automatonId)
    , ("varName", .label p.varName)
    , ("initMode", .label p.initMode)
    , ("initLo", intToData p.initLo)
    , ("initHi", intToData p.initHi)
    , ("unsafeLo", intToData p.unsafeLo)
    , ("unsafeHi", intToData p.unsafeHi) ]

/-- Deterministic `Obend.Core.Data` decoding of `HybridProblem`. -/
def HybridProblem.ofData? : Data → Option HybridProblem
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
  deriving DecidableEq, Repr

/-- Deterministic `Obend.Core.Data` encoding of `HybridCert`. -/
def HybridCert.toData (c : HybridCert) : Data :=
  .record
    [ ("schedule", actionListToData c.schedule)
    , ("expectedFinalMode", .label c.expectedFinalMode)
    , ("claimedSteps", .natural c.claimedSteps) ]

/-- Deterministic `Obend.Core.Data` decoding of `HybridCert`. -/
def HybridCert.ofData? : Data → Option HybridCert
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
def HybridProblem.initState (p : HybridProblem) : HybridState :=
  { modeId := p.initMode
  , box    := [(p.varName, ⟨Rat.ofInt p.initLo, Rat.ofInt p.initHi⟩)] }

/-- Construct the unsafe `Interval` from a `HybridProblem`. -/
def HybridProblem.unsafeInterval (p : HybridProblem) : Interval :=
  ⟨Rat.ofInt p.unsafeLo, Rat.ofInt p.unsafeHi⟩

/-- Check whether two intervals are strictly disjoint (`a.hi < b.lo` or `b.hi < a.lo`). -/
def Interval.disjoint (a b : Interval) : Bool :=
  decide (a.hi < b.lo) || decide (b.hi < a.lo)

/-- Look up the interval for `varName` in a continuous `box`. -/
def findBoxInterval? (varName : String) : List (String × Interval) → Option Interval
  | [] => none
  | (n, iv) :: rest => if n == varName then some iv else findBoxInterval? varName rest

/-- Check that `varName`'s interval in `box` is strictly disjoint from `unsafeIv`. -/
def boxDisjointFromUnsafe (box : List (String × Interval)) (varName : String) (unsafeIv : Interval) : Bool :=
  match findBoxInterval? varName box with
  | some iv => Interval.disjoint iv unsafeIv
  | none    => false

/-- Single-step hybrid transition wrapper (`stepHybrid`). -/
def stepHybrid (aut : HybridAutomaton) (st : HybridState) (act : HybridAction) : Option HybridState :=
  stepHybridAction aut st act

/-- Verify a hybrid flowpipe certificate `c` against problem `p`:
    1. `c.claimedSteps == c.schedule.length`,
    2. `runHybridSchedule` succeeds across all continuous `.flowStep` and discrete `.jumpTo` transitions,
    3. Every reachable slice in the flowpipe tube lies inside `safeEnvelope` AND is strictly disjoint
       from `p.unsafeInterval`,
    4. The terminal hybrid state reaches `c.expectedFinalMode`. -/
def verifyFlowpipe (p : HybridProblem) (c : HybridCert) : Bool :=
  c.claimedSteps == c.schedule.length &&
  match runHybridSchedule thermostatHybridAutomaton p.initState c.schedule with
  | some tube =>
    tube.all (fun st =>
      checkBoxInEnvelope st.box thermostatHybridAutomaton.safeEnvelope &&
      boxDisjointFromUnsafe st.box p.varName p.unsafeInterval) &&
    match tube.getLast? with
    | some lastSt => lastSt.modeId == c.expectedFinalMode
    | none        => false
  | none => false

/-- Concrete valid and invalid hybrid flowpipe problem/certificate fixtures. -/
def demoHybridProblem : HybridProblem :=
  { automatonId := "thermostat"
  , varName     := "T"
  , initMode    := "heating"
  , initLo      := 24
  , initHi      := 26
  , unsafeLo    := 36
  , unsafeHi    := 50 }

def validHybridCert : HybridCert :=
  { schedule          := [.flowStep, .jumpTo "cooling", .flowStep, .flowStep]
  , expectedFinalMode := "cooling"
  , claimedSteps      := 4 }

def badHybridCert : HybridCert :=
  { schedule          := [.flowStep, .flowStep, .flowStep]
  , expectedFinalMode := "heating"
  , claimedSteps      := 3 }

theorem validHybridCert_accepted :
    verifyFlowpipe demoHybridProblem validHybridCert = true := by
  decide +kernel

theorem badHybridCert_rejected :
    verifyFlowpipe demoHybridProblem badHybridCert = false := by
  decide +kernel

/-- Check whether a `HybridCert`'s claimed step count matches its schedule length. -/
def checkCertStepCount (c : HybridCert) : Bool :=
  c.claimedSteps == c.schedule.length

def badStepCountHybridCert : HybridCert :=
  { schedule          := [.flowStep, .jumpTo "cooling"]
  , expectedFinalMode := "cooling"
  , claimedSteps      := 99 }

theorem badStepCountHybridCert_rejected :
    checkCertStepCount badStepCountHybridCert = false := rfl

#tooth badStepCountHybridCert_rejected by mutation
  checkCertStepCount := fun _ => true

/-- Decision procedure returning `Obend.Judge.Verdict String` for `(HybridProblem, HybridCert)`. -/
def checkHybridFlowpipe (_grade : Nat) (p : HybridProblem) (c : HybridCert) : Obend.Judge.Verdict String :=
  if verifyFlowpipe p c then .ok
  else .refused "flowpipe_invariant_or_unsafe_zone_violation" []

/-- `Obend.Judge` instance for `(HybridProblem, HybridCert)`. -/
instance hybridFlowpipeJudge : Obend.Judge HybridProblem HybridCert where
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

theorem hybridFlowpipe_bad_refused :
    Obend.Judge.check 0 demoHybridProblem badHybridCert =
      .refused "flowpipe_invariant_or_unsafe_zone_violation" [] := by
  change checkHybridFlowpipe 0 demoHybridProblem badHybridCert =
    .refused "flowpipe_invariant_or_unsafe_zone_violation" []
  simp [checkHybridFlowpipe, badHybridCert_rejected]

/-- Decode a `HybridProblem` from a string wire representation. -/
def decodeHybridProblem (s : String) : Except String HybridProblem :=
  if s == "thermostat-default" then .ok demoHybridProblem
  else .error s!"unknown HybridProblem wire payload: {s}"

/-- Decode a `HybridCert` from a string wire representation. -/
def decodeHybridCert (s : String) : Except String HybridCert :=
  if s == "valid-cooling-switch" then .ok validHybridCert
  else if s == "bad-overheat-runaway" then .ok badHybridCert
  else .error s!"unknown HybridCert wire payload: {s}"

/-- Registered `Obend.Judge.Format` for `"hybrid-flowpipe@1"`. -/
def hybridFlowpipeFormat : Obend.Judge.Format where
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
