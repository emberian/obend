module
/-
# Obend.Hardware.FSM — Multi-Cycle Valid/Ready FSMs, Fuel-Bounded `fix` Loops & `perform`/`resume` Handshakes

Compiles iterative/tail-recursive computations (`Term.fix`) and interactive activity suspensions
(`Term.perform` / `Machine.resume`) into cycle-accurate **Valid/Ready Finite State Machines (FSMs)**
over `Obend.Hardware.HDL`:

1. **4-Phase Valid/Ready Hardware Handshake (`FsmPhase`: `.idle`, `.busy`, `.yielded`, `.done`)**:
   - `.idle`: asserts `inReady = true`; latches `inArg` and `initFuel` when `inValid = true`,
   - `.busy`: executes one loop iteration per clock cycle (`inReady = false`), decrementing `fuel`,
     checking early convergence (`doneCondExpr`) or suspension (`yieldCondExpr`),
   - `.yielded`: asserts `yieldValid = true` and drives `yieldPlan` to the host/kernel; holds all
     live loop registers (`accReg`, `fuel`, `yieldPlan`) invariant across arbitrary host response
     latency until `resumeValid = true`,
   - `.done`: asserts `outValid = true` and holds `outData = accReg` until `outReady = true`.
2. **Formal Hardware FSM Theorems (`0 sorry`)**:
   - `fsm_no_overwrite_while_busy`: when `st.phase ≠ .idle`, `inReady = false` and mutating external
     input signals (`inValid`, `inArg`) cannot corrupt in-flight state,
   - `fsm_fuel_monotone_termination` & `fsm_refines_tailrec`: for any pure loop config, running
     `k + 1` cycles from `.busy` with `fuel = k` terminates in `.done` with `accReg = evalTailRec cfg k acc`,
   - `fsm_yield_resume_sound`: in `.yielded`, state is invariant across arbitrary host stall cycles
     $L \in \mathbb{N}$ while `resumeValid = false`, and resumes into `.busy` with the host response
     upon `resumeValid = true`.
-/
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware.FSM
open Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. FSM Phases, Configuration, State & Handshake I/O Bundles -/

/-- Control phase of a hardware Valid/Ready + Yield/Resume finite state machine. -/
inductive FsmPhase where
  | idle
  | busy
  | yielded
  | done
  deriving DecidableEq, Repr

/-- Hardware FSM configuration synthesized from a bounded `fix` loop or interactive `perform` term.
* `stepExpr`: computes next accumulator state from `.regRead 0` (`accReg`) and `.inputPort 0` (`resumeVal`),
* `doneCondExpr`: evaluates to non-zero when the loop has converged early,
* `yieldCondExpr`: evaluates to non-zero when the loop suspends via `perform`,
* `yieldPlanExpr`: computes the 64-bit plan word emitted on `yieldPlan` when suspending. -/
structure FsmConfig where
  name          : String
  initFuel      : Nat
  stepExpr      : RtlExpr
  doneCondExpr  : RtlExpr
  yieldCondExpr : RtlExpr
  yieldPlanExpr : RtlExpr
  deriving DecidableEq, Repr

/-- Sequential register state of the hardware FSM. -/
structure FsmState where
  phase     : FsmPhase
  accReg    : BitVec 64
  fuel      : Nat
  yieldPlan : BitVec 64
  deriving DecidableEq, Repr

/-- Initial reset state of the hardware FSM. -/
def initFsmState : FsmState :=
  { phase := .idle, accReg := 0#64, fuel := 0, yieldPlan := 0#64 }

/-- Cycle-by-cycle external input signals to the hardware FSM. -/
structure FsmInputs where
  inValid     : Bool
  inArg       : BitVec 64
  outReady    : Bool
  resumeValid : Bool
  resumeVal   : BitVec 64
  deriving DecidableEq, Repr

/-- Default idle input bundle (all valid/ready strobes deasserted). -/
def idleFsmInputs : FsmInputs :=
  { inValid := false, inArg := 0#64, outReady := false, resumeValid := false, resumeVal := 0#64 }

/-- Cycle-by-cycle external output signals driven by the hardware FSM. -/
structure FsmOutputs where
  inReady    : Bool
  outValid   : Bool
  outData    : BitVec 64
  yieldValid : Bool
  yieldPlan  : BitVec 64
  deriving DecidableEq, Repr

/-! ## 2. Datapath Evaluation & Cycle-Accurate FSM Transition Function (`stepFsm`) -/

/-- Evaluate a combinational `RtlExpr` inside the FSM datapath with register `0` bound to `accReg`
and input port `0` bound to `resumeVal`. -/
def evalFsmExpr (accReg resumeVal : BitVec 64) (e : RtlExpr) : BitVec 64 :=
  evalRtlExpr (fun _ => resumeVal) (fun _ => 0#64) (fun _ => accReg) e

/-- Moore output decoder for the hardware FSM (depends only on current `FsmState`, preventing
combinational Valid/Ready loops). -/
def decodeFsmOutputs (st : FsmState) : FsmOutputs :=
  { inReady    := st.phase == .idle
  , outValid   := st.phase == .done
  , outData    := st.accReg
  , yieldValid := st.phase == .yielded
  , yieldPlan  := st.yieldPlan }

/-- Compute the next sequential `FsmState` after one clock edge. -/
def stepFsmNextState (cfg : FsmConfig) (st : FsmState) (inp : FsmInputs) : FsmState :=
  match st.phase with
  | .idle =>
    if inp.inValid then
      { phase := .busy, accReg := inp.inArg, fuel := cfg.initFuel, yieldPlan := 0#64 }
    else
      st
  | .busy =>
    match st.fuel with
    | 0 => { st with phase := .done, fuel := 0 }
    | k + 1 =>
      if evalFsmExpr st.accReg 0#64 cfg.doneCondExpr != 0#64 then
        { st with phase := .done, fuel := 0 }
      else if evalFsmExpr st.accReg 0#64 cfg.yieldCondExpr != 0#64 then
        let plan := evalFsmExpr st.accReg 0#64 cfg.yieldPlanExpr
        { st with phase := .yielded, yieldPlan := plan }
      else
        let nextAcc := evalFsmExpr st.accReg 0#64 cfg.stepExpr
        { st with phase := .busy, accReg := nextAcc, fuel := k }
  | .yielded =>
    if inp.resumeValid then
      let resumedAcc := evalFsmExpr st.accReg inp.resumeVal cfg.stepExpr
      { st with phase := .busy, accReg := resumedAcc }
    else
      st
  | .done =>
    if inp.outReady then
      { st with phase := .idle }
    else
      st

/-- Combined cycle-accurate step function returning `(nextState, currentOutputs)`. -/
def stepFsm (cfg : FsmConfig) (st : FsmState) (inp : FsmInputs) : FsmState × FsmOutputs :=
  (stepFsmNextState cfg st inp, decodeFsmOutputs st)

/-! ## 3. Non-Interference & Input Isolation Theorem (`fsm_no_overwrite_while_busy`) -/

/-- Theorem (`fsm_no_overwrite_while_busy`):
Whenever the FSM is not in `.idle` (`st.phase ≠ .idle`):
1. `inReady` is strictly `false`, and
2. Arbitrary noise on `inValid` and `inArg` has zero effect on the next FSM state or outputs! -/
theorem fsm_no_overwrite_while_busy
    (cfg : FsmConfig) (st : FsmState) (inp : FsmInputs)
    (noisyValid : Bool) (noisyArg : BitVec 64)
    (hNotIdle : st.phase ≠ .idle) :
    (stepFsm cfg st inp).2.inReady = false ∧
    stepFsm cfg st { inp with inValid := noisyValid, inArg := noisyArg } =
      stepFsm cfg st inp := by
  refine ⟨beq_eq_false_iff_ne.mpr hNotIdle, ?_⟩
  dsimp only [stepFsm, stepFsmNextState]
  cases hPhase : st.phase with
  | idle => exact False.elim (hNotIdle hPhase)
  | busy => rfl
  | yielded => rfl
  | done => rfl

/-! ## 4. Tail-Recursive Loop Specification & Fuel-Bounded Refinement (`fsm_refines_tailrec`) -/

/-- Pure mathematical tail-recursive specification with fuel `k`:
At each step, if `doneCondExpr` is non-zero, returns `acc` immediately; otherwise updates `acc` via
`stepExpr` and recurses with `k - 1`. -/
def evalTailRec (cfg : FsmConfig) : Nat → BitVec 64 → BitVec 64
  | 0, acc => acc
  | k + 1, acc =>
    if evalFsmExpr acc 0#64 cfg.doneCondExpr != 0#64 then
      acc
    else
      evalTailRec cfg k (evalFsmExpr acc 0#64 cfg.stepExpr)

/-- Run the FSM for `n` clock cycles under a fixed input bundle `inp`. -/
def runFsmCycles (cfg : FsmConfig) : Nat → FsmState → FsmInputs → FsmState
  | 0, st, _ => st
  | n + 1, st, inp => runFsmCycles cfg n (stepFsmNextState cfg st inp) inp

/-- Lemma: Once the FSM reaches `.done`, if `inp.outReady = false`, it stays in `.done` with the
exact same `accReg`, `fuel`, and `yieldPlan` for any remaining number of cycles `n`. -/
theorem done_holds_until_outReady
    (cfg : FsmConfig) (n : Nat) (acc yp : BitVec 64) (fuel : Nat) (inp : FsmInputs)
    (hNotReady : inp.outReady = false) :
    runFsmCycles cfg n { phase := .done, accReg := acc, fuel := fuel, yieldPlan := yp } inp =
      { phase := .done, accReg := acc, fuel := fuel, yieldPlan := yp } := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [runFsmCycles, stepFsmNextState, hNotReady, Bool.false_eq_true, ↓reduceIte]
    exact ih

/-- Helper predicate stating that `cfg` is a pure iterative loop (`yieldCondExpr = .const 0#64`). -/
def isPureLoopConfig (cfg : FsmConfig) : Prop :=
  cfg.yieldCondExpr = .const 0#64

/-- Theorem (`fsm_refines_tailrec` & `fsm_fuel_monotone_termination`):
For any pure loop configuration (`cfg.yieldCondExpr = .const 0#64`) and any fuel `k : Nat`,
running the hardware FSM for `k + 1` clock cycles from `.busy` (with `inp.outReady = false`)
terminates in `.done` with `fuel = 0` and `accReg = evalTailRec cfg k acc`! -/
theorem fsm_refines_tailrec
    (cfg : FsmConfig) (k : Nat) (acc yp : BitVec 64) (inp : FsmInputs)
    (hPure : cfg.yieldCondExpr = .const 0#64)
    (hHold : inp.outReady = false) :
    runFsmCycles cfg (k + 1) { phase := .busy, accReg := acc, fuel := k, yieldPlan := yp } inp =
      { phase := .done, accReg := evalTailRec cfg k acc, fuel := 0, yieldPlan := yp } := by
  induction k generalizing acc with
  | zero =>
    rfl
  | succ m ih =>
    simp only [runFsmCycles, stepFsmNextState, evalTailRec]
    by_cases hDone : (evalFsmExpr acc 0#64 cfg.doneCondExpr != 0#64) = true
    · simp only [hDone, ↓reduceIte]
      exact done_holds_until_outReady cfg (m + 1) acc yp 0 inp hHold
    · simp only [hDone, ↓reduceIte]
      have hNoYield : (evalFsmExpr acc 0#64 cfg.yieldCondExpr != 0#64) = false := by
        rw [hPure]
        rfl
      simp only [hNoYield, Bool.false_eq_true, ↓reduceIte]
      exact ih (evalFsmExpr acc 0#64 cfg.stepExpr)

/-- Corollary (`fsm_fuel_monotone_termination`):
For any pure loop configuration, starting from `.busy` with `fuel = k`, the FSM is guaranteed to
reach `phase = .done` and `outValid = true` after `k + 1` cycles. -/
theorem fsm_fuel_monotone_termination
    (cfg : FsmConfig) (k : Nat) (acc yp : BitVec 64) (inp : FsmInputs)
    (hPure : cfg.yieldCondExpr = .const 0#64)
    (hHold : inp.outReady = false) :
    let finalSt := runFsmCycles cfg (k + 1) { phase := .busy, accReg := acc, fuel := k, yieldPlan := yp } inp
    finalSt.phase = .done ∧ (decodeFsmOutputs finalSt).outValid = true := by
  dsimp only
  simp only [fsm_refines_tailrec cfg k acc yp inp hPure hHold, decodeFsmOutputs, beq_self_eq_true, and_self]

/-! ## 5. Interactive `perform` / `resume` Yield Handshake Soundness (`fsm_yield_resume_sound`) -/

/-- Theorem (`fsm_yield_resume_sound`):
1. **Arbitrary Host Latency Stability**: While in `.yielded` and `inp.resumeValid = false`, the FSM
   asserts `yieldValid = true` with `yieldPlan = yp` and preserves `accReg`, `fuel`, and `yieldPlan`
   unchanged across any number of host stall cycles `latency : Nat`.
2. **Exact Resume Continuation**: On the clock edge when `inp.resumeValid = true` with response
   `inp.resumeVal = resp`, the FSM transitions back to `.busy` with `accReg = evalFsmExpr acc resp cfg.stepExpr`
   and intact `fuel`. -/
theorem fsm_yield_resume_sound
    (cfg : FsmConfig) (latency : Nat) (acc yp resp : BitVec 64) (fuel : Nat)
    (stallInp : FsmInputs)
    (hWait : stallInp.resumeValid = false) :
    let ySt : FsmState := { phase := .yielded, accReg := acc, fuel := fuel, yieldPlan := yp }
    runFsmCycles cfg latency ySt stallInp = ySt ∧
    (decodeFsmOutputs (runFsmCycles cfg latency ySt stallInp)).yieldValid = true ∧
    (decodeFsmOutputs (runFsmCycles cfg latency ySt stallInp)).yieldPlan = yp ∧
    stepFsmNextState cfg (runFsmCycles cfg latency ySt stallInp)
      { stallInp with resumeValid := true, resumeVal := resp } =
      { phase := .busy, accReg := evalFsmExpr acc resp cfg.stepExpr, fuel := fuel, yieldPlan := yp } := by
  dsimp only
  have hStable :
      runFsmCycles cfg latency { phase := .yielded, accReg := acc, fuel := fuel, yieldPlan := yp } stallInp =
        { phase := .yielded, accReg := acc, fuel := fuel, yieldPlan := yp } := by
    induction latency with
    | zero => rfl
    | succ n ih =>
      simp only [runFsmCycles, stepFsmNextState, hWait, Bool.false_eq_true, ↓reduceIte]
      exact ih
  simp only [hStable, decodeFsmOutputs, beq_self_eq_true, stepFsmNextState, ↓reduceIte, and_self]

/-! ## 6. Compiler from High-Level `LoopSpec` to `FsmConfig` (`compileLoopToFsm`) -/

/-- High-level specification of a hardware loop with optional `perform` suspension. -/
structure LoopSpec where
  name          : String
  maxIterations : Nat
  bodyStep      : RtlExpr
  stopWhen      : RtlExpr
  yieldWhen     : Option (RtlExpr × RtlExpr)
  deriving DecidableEq, Repr

/-- Lower a `LoopSpec` into a concrete `FsmConfig`. -/
def compileLoopToFsm (spec : LoopSpec) : FsmConfig :=
  match spec.yieldWhen with
  | none =>
    { name          := spec.name
    , initFuel      := spec.maxIterations
    , stepExpr      := spec.bodyStep
    , doneCondExpr  := spec.stopWhen
    , yieldCondExpr := .const 0#64
    , yieldPlanExpr := .const 0#64 }
  | some (yCond, yPlan) =>
    { name          := spec.name
    , initFuel      := spec.maxIterations
    , stepExpr      := spec.bodyStep
    , doneCondExpr  := spec.stopWhen
    , yieldCondExpr := yCond
    , yieldPlanExpr := yPlan }

/-- Theorem: Any `LoopSpec` with `yieldWhen = none` compiles to a pure loop config whose hardware
FSM refines `evalTailRec`. -/
theorem compileLoopToFsm_pure_refines
    (spec : LoopSpec) (acc : BitVec 64) (inp : FsmInputs)
    (hNoYield : spec.yieldWhen = none)
    (hHold : inp.outReady = false) :
    let cfg := compileLoopToFsm spec
    runFsmCycles cfg (cfg.initFuel + 1)
      { phase := .busy, accReg := acc, fuel := cfg.initFuel, yieldPlan := 0#64 } inp =
      { phase := .done, accReg := evalTailRec cfg cfg.initFuel acc, fuel := 0, yieldPlan := 0#64 } := by
  dsimp only
  have hPure : (compileLoopToFsm spec).yieldCondExpr = .const 0#64 := by
    simp [compileLoopToFsm, hNoYield]
  exact fsm_refines_tailrec (compileLoopToFsm spec) (compileLoopToFsm spec).initFuel acc 0#64 inp hPure hHold

end Obend.Hardware.FSM
