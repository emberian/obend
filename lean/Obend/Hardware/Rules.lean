module
/-
# Obend.Hardware.Rules — Guarded Atomic Hardware Rules (Kôika / Kami Style) & ORAAT Refinement

Formalizes rule-based hardware design (in the tradition of Bluespec, MIT's Kami, and Kôika,
Bourgeat et al. PLDI 2020) on top of `Obend.Hardware.HDL`:

1. **Dynamic Action Logs & Multi-Port Register causality (`PortPhase`, `ActionKind`, `ActionLog`)**:
   - Models 2-port EHR (Ephemeral History Register) ordering `read0 < write0 < read1 < write1`
     within a single clock cycle,
   - Rejects causal hazards (`write0` before `read0`, double `write0`, `write1` before `read1`,
     double `write1`) while admitting intra-cycle bypass forwarding (`write0` followed by `read1`).
2. **Guarded Atomic Hardware Rules (`HwRule`, `evalRuleAtomic`, `evalScheduleORAAT`, `evalScheduleSync`)**:
   - Each rule has a combinational `guardExpr : RtlExpr`, a `targetReg : Nat`, and a `valueExpr : RtlExpr`,
   - `evalScheduleORAAT` defines sequential One-Rule-At-A-Time (ORAAT) atomic execution,
   - `evalScheduleSync` defines simultaneous single-cycle synchronous hardware execution (where all
     enabled rules sample the pre-cycle register state `regs` in parallel).
3. **Static Footprint Analysis & Conflict-Free Schedule Checker (`disjointFootprint`, `checkConflictFreeSchedule`)**:
   - Proves `evalRtlExpr_update_irrelevant`: updating a register `rIdx` when `exprAvoidsReg rIdx e = true`
     leaves `evalRtlExpr` invariant,
   - Proves `conflictFree_two_rules_commute`: when `disjointFootprint r1 r2 = true`, executing `r1`
     then `r2` atomically commutes with executing `r2` then `r1` and equals simultaneous single-cycle
     parallel execution at every register index,
   - Proves `schedule_oraat_refinement`: for any rule schedule `rs`, if `checkConflictFreeSchedule rs = true`,
     single-cycle synchronous hardware execution `evalScheduleSync` is bit-identical to sequential
     atomic execution `evalScheduleORAAT` across all registers.
-/
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware.Rules
open Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. Dynamic Action Logs & Intra-Cycle EHR Port Ordering (`read0 < write0 < read1 < write1`) -/

/-- Port phase of an Ephemeral History Register (EHR) within a single clock cycle. -/
inductive PortPhase where
  | port0
  | port1
  deriving DecidableEq, Repr

/-- Register access action kind logged during rule execution. -/
inductive ActionKind where
  | read  (phase : PortPhase) (regIdx : Nat)
  | write (phase : PortPhase) (regIdx : Nat) (val : BitVec 64)
  deriving DecidableEq, Repr

/-- Per-cycle dynamic action log recording all register reads and writes on `port0` and `port1`. -/
structure ActionLog where
  reads0  : List Nat
  writes0 : List Nat
  reads1  : List Nat
  writes1 : List Nat
  deriving DecidableEq, Repr

/-- Empty action log at the start of a clock cycle. -/
def emptyActionLog : ActionLog :=
  { reads0 := [], writes0 := [], reads1 := [], writes1 := [] }

/-- Causality & port-collision violations caught by the Kôika-style dynamic action log checker. -/
inductive LogConflict where
  | read0AfterWrite (regIdx : Nat)
  | doubleWrite0    (regIdx : Nat)
  | write0AfterPort1 (regIdx : Nat)
  | read1AfterWrite1 (regIdx : Nat)
  | doubleWrite1    (regIdx : Nat)
  deriving DecidableEq, Repr

/-- Check whether appending `act` to `log` respects the intra-cycle causal order
`read0 < write0 < read1 < write1` and at-most-once write discipline per port. -/
def checkActionStep (log : ActionLog) (act : ActionKind) : Except LogConflict ActionLog :=
  match act with
  | .read .port0 r =>
    if log.writes0.contains r || log.writes1.contains r then
      .error (.read0AfterWrite r)
    else
      .ok { log with reads0 := r :: log.reads0 }
  | .write .port0 r _ =>
    if log.writes0.contains r then
      .error (.doubleWrite0 r)
    else if log.reads1.contains r || log.writes1.contains r then
      .error (.write0AfterPort1 r)
    else
      .ok { log with writes0 := r :: log.writes0 }
  | .read .port1 r =>
    if log.writes1.contains r then
      .error (.read1AfterWrite1 r)
    else
      .ok { log with reads1 := r :: log.reads1 }
  | .write .port1 r _ =>
    if log.writes1.contains r then
      .error (.doubleWrite1 r)
    else
      .ok { log with writes1 := r :: log.writes1 }

/-- Execute a sequence of register actions against an `ActionLog`, halting on the first conflict. -/
def runActionTrace (log : ActionLog) : List ActionKind → Except LogConflict ActionLog
  | [] => .ok log
  | a :: rest =>
    match checkActionStep log a with
    | .error err => .error err
    | .ok log'   => runActionTrace log' rest

/-- Theorem: A `read0` after a `write0` to the same register `r` is refused as a causal hazard
(`read0AfterWrite r`). -/
theorem write0_before_read0_refused (r : Nat) (v : BitVec 64) :
    runActionTrace emptyActionLog [.write .port0 r v, .read .port0 r] =
      .error (.read0AfterWrite r) := by
  simp [runActionTrace, checkActionStep, emptyActionLog]

/-- Theorem: Two `write0` actions to the same register `r` in the same cycle are refused
(`doubleWrite0 r`). -/
theorem double_write0_refused (r : Nat) (v1 v2 : BitVec 64) :
    runActionTrace emptyActionLog [.write .port0 r v1, .write .port0 r v2] =
      .error (.doubleWrite0 r) := by
  simp [runActionTrace, checkActionStep, emptyActionLog]

/-- Theorem: Writing on `port0` and reading on `port1` (`write0 r` -> `read1 r`) is admitted by the
EHR causal order (`read0 < write0 < read1 < write1`), enabling intra-cycle bypass forwarding. -/
theorem write0_then_read1_forwarding_allowed (r : Nat) (v : BitVec 64) :
    runActionTrace emptyActionLog [.write .port0 r v, .read .port1 r] =
      .ok { reads0 := [], writes0 := [r], reads1 := [r], writes1 := [] } :=
  rfl

/-! ## 2. Guarded Atomic Hardware Rules (`HwRule`) & Register-Avoidance Locality -/

/-- A guarded atomic hardware rule: when `guardExpr` evaluates to non-zero, `targetReg` is updated
to `valueExpr`. -/
structure HwRule where
  name      : String
  guardExpr : RtlExpr
  targetReg : Nat
  valueExpr : RtlExpr
  deriving DecidableEq, Repr

/-- Check statically that an `RtlExpr` never reads register `rIdx`. -/
def exprAvoidsReg (rIdx : Nat) : RtlExpr → Bool
  | .const _       => true
  | .inputPort _   => true
  | .wireRef _     => true
  | .regRead idx   => idx != rIdx
  | .alu _ a b     => exprAvoidsReg rIdx a && exprAvoidsReg rIdx b
  | .mux c t f     => exprAvoidsReg rIdx c && exprAvoidsReg rIdx t && exprAvoidsReg rIdx f
  | .bitNot a      => exprAvoidsReg rIdx a

/-- Check statically that neither the guard nor the value expression of `rule` reads `rIdx`. -/
def ruleAvoidsReg (rIdx : Nat) (rule : HwRule) : Bool :=
  exprAvoidsReg rIdx rule.guardExpr && exprAvoidsReg rIdx rule.valueExpr

/-- Update a single register `rIdx` in a register environment `regs : Nat → BitVec 64`. -/
def updateRegEnv (regs : Nat → BitVec 64) (rIdx : Nat) (newVal : BitVec 64) : Nat → BitVec 64 :=
  fun i => if i == rIdx then newVal else regs i

/-- Frame Locality Theorem (`evalRtlExpr_update_irrelevant`):
If `exprAvoidsReg rIdx e = true`, then mutating register `rIdx` in `regs` does not change the
evaluation of `e` under `evalRtlExpr`. -/
theorem evalRtlExpr_update_irrelevant
    (inputs wires regs : Nat → BitVec 64)
    (rIdx : Nat) (newVal : BitVec 64) (e : RtlExpr)
    (hAvoid : exprAvoidsReg rIdx e = true) :
    evalRtlExpr inputs wires (updateRegEnv regs rIdx newVal) e =
      evalRtlExpr inputs wires regs e := by
  induction e with
  | const _ => rfl
  | inputPort _ => rfl
  | wireRef _ => rfl
  | regRead idx =>
    simp only [exprAvoidsReg, bne_iff_ne, ne_eq] at hAvoid
    have hBeq : (idx == rIdx) = false := beq_eq_false_iff_ne.mpr hAvoid
    simp [evalRtlExpr, updateRegEnv, hBeq]
  | alu op a b iha ihb =>
    simp only [exprAvoidsReg, Bool.and_eq_true] at hAvoid
    simp only [evalRtlExpr, iha hAvoid.1, ihb hAvoid.2]
  | mux c t f ihc iht ihf =>
    simp only [exprAvoidsReg, Bool.and_eq_true] at hAvoid
    simp only [evalRtlExpr, ihc hAvoid.1.1, iht hAvoid.1.2, ihf hAvoid.2]
  | bitNot a iha =>
    simp only [exprAvoidsReg] at hAvoid
    simp only [evalRtlExpr, iha hAvoid]

/-! ## 3. Atomic Rule Execution (`evalRuleAtomic`), ORAAT vs Synchronous Semantics & Commutativity -/

/-- Evaluate a single guarded rule `r` atomically on register state `regs`. -/
def evalRuleAtomic
    (inputs wires regs : Nat → BitVec 64)
    (r : HwRule) : Nat → BitVec 64 :=
  if evalRtlExpr inputs wires regs r.guardExpr != 0#64 then
    updateRegEnv regs r.targetReg (evalRtlExpr inputs wires regs r.valueExpr)
  else
    regs

/-- Compute the next value that rule `r` wants to write to `r.targetReg` when sampling pre-cycle
register state `preRegs` (or `preRegs r.targetReg` if `r`'s guard is false). -/
def evalRuleTargetNext
    (inputs wires preRegs : Nat → BitVec 64)
    (r : HwRule) : BitVec 64 :=
  if evalRtlExpr inputs wires preRegs r.guardExpr != 0#64 then
    evalRtlExpr inputs wires preRegs r.valueExpr
  else
    preRegs r.targetReg

/-- Lemma: `evalRuleAtomic` is equivalent to `updateRegEnv regs r.targetReg (evalRuleTargetNext ... r)`. -/
theorem evalRuleAtomic_eq_updateTarget
    (inputs wires regs : Nat → BitVec 64)
    (r : HwRule) (regIdx : Nat) :
    evalRuleAtomic inputs wires regs r regIdx =
      updateRegEnv regs r.targetReg (evalRuleTargetNext inputs wires regs r) regIdx := by
  simp only [evalRuleAtomic, evalRuleTargetNext, updateRegEnv]
  by_cases hGuard : (evalRtlExpr inputs wires regs r.guardExpr != 0#64) = true
  · rw [if_pos hGuard, if_pos hGuard]
    rfl
  · rw [if_neg hGuard, if_neg hGuard]
    by_cases hIdx : (regIdx == r.targetReg) = true
    · have hEq : regIdx = r.targetReg := beq_iff_eq.mp hIdx
      rw [if_pos hIdx, hEq]
    · rw [if_neg hIdx]

/-- Frame lemma for `evalRuleTargetNext` when `r.targetReg ≠ rIdx` and `ruleAvoidsReg rIdx r = true`. -/
theorem evalRuleTargetNext_frame
    (inputs wires regs : Nat → BitVec 64)
    (rIdx : Nat) (v : BitVec 64) (r : HwRule)
    (hNe : r.targetReg ≠ rIdx)
    (hAvoid : ruleAvoidsReg rIdx r = true) :
    evalRuleTargetNext inputs wires (updateRegEnv regs rIdx v) r =
      evalRuleTargetNext inputs wires regs r := by
  simp only [ruleAvoidsReg, Bool.and_eq_true] at hAvoid
  have hBeq : (r.targetReg == rIdx) = false := beq_eq_false_iff_ne.mpr hNe
  simp [evalRuleTargetNext,
    evalRtlExpr_update_irrelevant inputs wires regs rIdx v r.guardExpr hAvoid.1,
    evalRtlExpr_update_irrelevant inputs wires regs rIdx v r.valueExpr hAvoid.2,
    updateRegEnv, hBeq]

/-- Pairwise static conflict-freedom check between two rules `r1` and `r2`:
1. They write to distinct target registers (`r1.targetReg != r2.targetReg`),
2. `r2` does not read `r1.targetReg`,
3. `r1` does not read `r2.targetReg`. -/
def disjointFootprint (r1 r2 : HwRule) : Bool :=
  (r1.targetReg != r2.targetReg) &&
  ruleAvoidsReg r1.targetReg r2 &&
  ruleAvoidsReg r2.targetReg r1

/-- Simultaneous single-cycle execution of two rules `r1` and `r2` sampling the same pre-cycle `regs`. -/
def evalTwoRulesSync
    (inputs wires regs : Nat → BitVec 64)
    (r1 r2 : HwRule) : Nat → BitVec 64 :=
  let v1 := evalRuleTargetNext inputs wires regs r1
  let v2 := evalRuleTargetNext inputs wires regs r2
  updateRegEnv (updateRegEnv regs r1.targetReg v1) r2.targetReg v2

/-- Theorem (`conflictFree_two_rules_commute`):
If `disjointFootprint r1 r2 = true`, then for every register `regIdx`:
1. Sequential ORAAT execution (`r1` then `r2`) equals simultaneous single-cycle execution `evalTwoRulesSync`, and
2. Sequential ORAAT execution (`r1` then `r2`) commutes with (`r2` then `r1`)! -/
theorem conflictFree_two_rules_commute
    (inputs wires regs : Nat → BitVec 64)
    (r1 r2 : HwRule)
    (hDisj : disjointFootprint r1 r2 = true)
    (regIdx : Nat) :
    evalRuleAtomic inputs wires (evalRuleAtomic inputs wires regs r1) r2 regIdx =
      evalTwoRulesSync inputs wires regs r1 r2 regIdx ∧
    evalRuleAtomic inputs wires (evalRuleAtomic inputs wires regs r1) r2 regIdx =
      evalRuleAtomic inputs wires (evalRuleAtomic inputs wires regs r2) r1 regIdx := by
  simp only [disjointFootprint, Bool.and_eq_true, bne_iff_ne, ne_eq] at hDisj
  rcases hDisj with ⟨⟨hNe12, hAvoid12⟩, hAvoid21⟩
  have hNe21 : r2.targetReg ≠ r1.targetReg := Ne.symm hNe12
  have hStep1 : evalRuleAtomic inputs wires regs r1 =
      updateRegEnv regs r1.targetReg (evalRuleTargetNext inputs wires regs r1) := by
    funext i
    exact evalRuleAtomic_eq_updateTarget inputs wires regs r1 i
  have hStep2 : evalRuleAtomic inputs wires regs r2 =
      updateRegEnv regs r2.targetReg (evalRuleTargetNext inputs wires regs r2) := by
    funext i
    exact evalRuleAtomic_eq_updateTarget inputs wires regs r2 i
  constructor
  · simp only [hStep1, evalRuleAtomic_eq_updateTarget,
      evalRuleTargetNext_frame inputs wires regs r1.targetReg
        (evalRuleTargetNext inputs wires regs r1) r2 hNe21 hAvoid12,
      evalTwoRulesSync]
  · simp only [hStep1, hStep2, evalRuleAtomic_eq_updateTarget,
      evalRuleTargetNext_frame inputs wires regs r1.targetReg
        (evalRuleTargetNext inputs wires regs r1) r2 hNe21 hAvoid12,
      evalRuleTargetNext_frame inputs wires regs r2.targetReg
        (evalRuleTargetNext inputs wires regs r2) r1 hNe12 hAvoid21,
      updateRegEnv]
    by_cases h1 : (regIdx == r2.targetReg) = true
    · have hEq2 : regIdx = r2.targetReg := beq_iff_eq.mp h1
      have hNot1 : (regIdx == r1.targetReg) = false := by
        rw [hEq2]
        exact beq_eq_false_iff_ne.mpr hNe21
      simp [h1, hNot1]
    · simp [h1]

/-! ## 4. General Multi-Rule Schedule ORAAT Refinement (`schedule_oraat_refinement`) -/

/-- One-Rule-At-A-Time (ORAAT) sequential execution of a rule schedule `rs : List HwRule`. -/
def evalScheduleORAAT
    (inputs wires regs : Nat → BitVec 64) : List HwRule → (Nat → BitVec 64)
  | [] => regs
  | r :: rest => evalScheduleORAAT inputs wires (evalRuleAtomic inputs wires regs r) rest

/-- Synchronous single-cycle parallel execution of a rule schedule `rs : List HwRule`:
Every rule in `rs` evaluates its guard and value expression against the SAME pre-cycle register
snapshot `preRegs`, and updates its target register. -/
def evalScheduleSyncFrom
    (inputs wires preRegs curRegs : Nat → BitVec 64) : List HwRule → (Nat → BitVec 64)
  | [] => curRegs
  | r :: rest =>
    let nextCur := updateRegEnv curRegs r.targetReg (evalRuleTargetNext inputs wires preRegs r)
    evalScheduleSyncFrom inputs wires preRegs nextCur rest

/-- Top-level single-cycle synchronous transition for schedule `rs` starting from `regs`. -/
def evalScheduleSync
    (inputs wires regs : Nat → BitVec 64) (rs : List HwRule) : Nat → BitVec 64 :=
  evalScheduleSyncFrom inputs wires regs regs rs

/-- Check that every rule in `rest` has `targetReg ≠ rIdx` and avoids reading `rIdx`. -/
def scheduleAvoidsReg (rIdx : Nat) : List HwRule → Bool
  | [] => true
  | r :: rest =>
    (r.targetReg != rIdx) && ruleAvoidsReg rIdx r && scheduleAvoidsReg rIdx rest

/-- Static conflict-free schedule checker (`checkConflictFreeSchedule`):
Verifies that for every rule `r` in the schedule, no subsequent rule in the schedule reads or
writes `r.targetReg`. -/
def checkConflictFreeSchedule : List HwRule → Bool
  | [] => true
  | r :: rest =>
    scheduleAvoidsReg r.targetReg rest && checkConflictFreeSchedule rest

/-- Lemma: If `scheduleAvoidsReg rIdx rs = true`, then changing `preRegs` to
`updateRegEnv preRegs rIdx v` does not change `evalScheduleSyncFrom`. -/
theorem evalScheduleSyncFrom_preRegs_frame
    (inputs wires preRegs curRegs : Nat → BitVec 64)
    (rIdx : Nat) (v : BitVec 64) (rs : List HwRule)
    (hAvoid : scheduleAvoidsReg rIdx rs = true) :
    evalScheduleSyncFrom inputs wires (updateRegEnv preRegs rIdx v) curRegs rs =
      evalScheduleSyncFrom inputs wires preRegs curRegs rs := by
  induction rs generalizing curRegs with
  | nil => rfl
  | cons r rest ih =>
    simp only [scheduleAvoidsReg, Bool.and_eq_true, bne_iff_ne, ne_eq] at hAvoid
    rcases hAvoid with ⟨⟨hNe, hRuleAvoid⟩, hRestAvoid⟩
    simp only [evalScheduleSyncFrom,
      evalRuleTargetNext_frame inputs wires preRegs rIdx v r hNe hRuleAvoid]
    exact ih (updateRegEnv curRegs r.targetReg (evalRuleTargetNext inputs wires preRegs r)) hRestAvoid

/-- Main Theorem (`schedule_oraat_refinement`):
For ANY list of guarded atomic rules `rs : List HwRule`, if `checkConflictFreeSchedule rs = true`,
then single-cycle synchronous hardware execution `evalScheduleSync` is bit-identical to sequential
One-Rule-At-A-Time atomic execution `evalScheduleORAAT` across all register states! -/
theorem schedule_oraat_refinement
    (inputs wires regs : Nat → BitVec 64)
    (rs : List HwRule)
    (hCF : checkConflictFreeSchedule rs = true) :
    evalScheduleSync inputs wires regs rs = evalScheduleORAAT inputs wires regs rs := by
  unfold evalScheduleSync
  induction rs generalizing regs with
  | nil => rfl
  | cons r rest ih =>
    simp only [checkConflictFreeSchedule, Bool.and_eq_true] at hCF
    rcases hCF with ⟨hAvoidRest, hCFRest⟩
    simp only [evalScheduleSyncFrom, evalScheduleORAAT]
    have hAtomicEq : evalRuleAtomic inputs wires regs r =
        updateRegEnv regs r.targetReg (evalRuleTargetNext inputs wires regs r) := by
      funext i
      exact evalRuleAtomic_eq_updateTarget inputs wires regs r i
    rw [hAtomicEq]
    have hFrame := evalScheduleSyncFrom_preRegs_frame inputs wires regs
      (updateRegEnv regs r.targetReg (evalRuleTargetNext inputs wires regs r))
      r.targetReg (evalRuleTargetNext inputs wires regs r) rest hAvoidRest
    rw [← hFrame]
    exact ih (updateRegEnv regs r.targetReg (evalRuleTargetNext inputs wires regs r)) hCFRest

/-! ## 5. Synthesis of Conflict-Free Rule Schedules to `Obend.Hardware.HDL.RegSpec` -/

/-- Lower a guarded rule `r` into the combinational `nextExpr` of its target register `r.targetReg`:
`mux r.guardExpr r.valueExpr (.regRead r.targetReg)`. -/
def compileRuleToRegNext (r : HwRule) : RtlExpr :=
  .mux r.guardExpr r.valueExpr (.regRead r.targetReg)

/-- Soundness of `compileRuleToRegNext`: evaluating the synthesized `RtlExpr` equals `evalRuleTargetNext`. -/
theorem compileRuleToRegNext_sound
    (inputs wires regs : Nat → BitVec 64) (r : HwRule) :
    evalRtlExpr inputs wires regs (compileRuleToRegNext r) =
      evalRuleTargetNext inputs wires regs r := by
  rfl

end Obend.Hardware.Rules
