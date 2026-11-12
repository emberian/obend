module
/-
# PipelinedRiscBurchDillTest — End-to-End Hazard Corner Cases, RTL Co-Simulation & `#tooth` Kills

Verifies `Obend.Hardware.PipelinedRisc`:
1. `#assert_axioms_tree` whole-cone axiom hygiene (`0 sorryAx`, `0` custom axioms, `0 native_decide`).
2. Concrete `#guard` programs exercising every 5-stage pipeline hazard corner case and matching
   `stepIsaN` bit-for-bit (`==` on `IsaState`) after `flushPipeline`:
   - Back-to-back `EX/MEM → EX` double bypass (`ADD r2, r1, r1`) + simultaneous `EX/MEM` & `MEM/WB`
     bypass with **0 stall cycles**,
   - Double-writer `ADD`/`ADDI` (`EX/MEM` priority over stale `MEM/WB` targeting the same `rd`),
   - `r0` write-ignore attack (`ADDI r0, r0, 99; ADD r2, r0, ...` across both `EX/MEM` and `MEM/WB`),
   - Load-use hazard interlock (`LD r1, [0]; ADD r2, r1, ...` — 1 stall bubble + `MEM/WB → EX` forward),
   - Taken branch loops computing both **Fibonacci (`F(10) = 55`)** and **sum-of-array (`150`)** in `DataMem`.
3. Cycle-accurate co-simulation of synthesizable `pipelinedRiscCoreRtlModule` (`stepModuleRegs` &
   `evalModuleOutputs`) across 45 clock cycles of the sum-of-array loop.
4. **7 `#tooth` kernel mutation kills** (reversing `EX/MEM` vs `MEM/WB` priority, dropping `rd != r0`
   bypass guard, breaking `regNonZero`, disabling `detectLoadUseStall`, disabling `branchTakenFlush`,
   corrupting `exAluResult`, and dropping `applyWb`).
-/
public import Obend.Hardware.PipelinedRisc
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Hardware.HDL
import all Obend.Hardware.PipelinedRiscCore
import all Obend.Hardware.PipelinedRisc
meta import all Obend.Hardware.HDL
meta import all Obend.Hardware.PipelinedRiscCore
meta import all Obend.Hardware.PipelinedRisc
import all Obend.Tactic.Tooth
import all Obend.AssertAxioms

public section
namespace Obend.Tests.SiliconElab.PipelinedRiscBurchDill

open Obend.Hardware.HDL
open Obend.Hardware.PipelinedRisc

set_option autoImplicit false

/-! ## 0. Whole-Cone Axiom Purity Audit (`0 sorryAx`, `0` Custom Axioms, `0` Compiler Trust) -/

#assert_axioms_tree

/-! ## 1. Universal Sanity Bundle Across ISA, Burch–Dill Commutator, Liveness & `RtlModule` -/

theorem pipelinedRisc_master_verification_bundle
    (imem : InstrMem) (p : PipeState) (hWf : PipeWf p) (n : Nat) :
    (∃ k, (k = 0 ∨ k = 1) ∧
      flushPipeline (stepPipeline imem p) = stepIsaN imem k (flushPipeline p)) ∧
    (∃ k, k ≤ n ∧ PipeWf (stepPipelineN imem n p) ∧
      flushPipeline (stepPipelineN imem n p) = stepIsaN imem k (flushPipeline p)) ∧
    ((stepPipelineN imem 2 p).retiredCount + 1 ≤
      (stepPipelineN imem 3 (stepPipelineN imem 2 p)).retiredCount) ∧
    (1 ≤ burchDillStepsN imem 4 p) ∧
    (checkRtlModule pipelinedRiscCoreRtlModule = true ∧
     checkRtlModuleW pipelinedRiscCoreRtlModule = true) := by
  exact ⟨burchDill_step_commutes imem p hWf,
   pipelinedRisc_multiCycle_refines_isa imem n p hWf,
   pipelinedRisc_retires_every_3_cycles imem p,
   (burchDill_no_starvation_progress imem p hWf).2,
   ⟨(pipelinedRiscCoreRtlModule_faithful (fun _ => 0#64) (fun _ => 0#64)).1,
    (pipelinedRiscCoreRtlModule_faithful (fun _ => 0#64) (fun _ => 0#64)).2.1⟩⟩

/-! ## 2. Concrete `#guard` Hazard Corner-Case Programs Matching `stepIsaN` Bit-for-Bit -/

/-- Helper checking that `n` hardware clock cycles from `initPipeState s0` drain to the exact
    `IsaState` produced by `burchDillStepsN` architectural `stepIsa` steps. -/
def runMatchesIsa (prog : Array IsaInstr) (s0 : IsaState) (cycles : Nat) : Bool :=
  let imem := progToImem prog
  let p0   := initPipeState s0
  let pEnd := stepPipelineN imem cycles p0
  let k    := burchDillStepsN imem cycles p0
  flushPipeline pEnd == stepIsaN imem k s0

/-- **Corner Case 1: Back-to-Back ALU RAW Double Bypass (`EX/MEM → EX`, 0 Stall Cycles).**
    `ADD r1, r0, r5; ADD r2, r1, r1; SUB r3, r2, r1; XOR r4, r2, r3` with `r5 = 21`:
    - `ADD r2, r1, r1` forwards `r1 = 21` onto BOTH `rs1` and `rs2` via `EX/MEM → EX` (`0` stalls),
    - `SUB r3, r2, r1` simultaneously forwards `r2 = 42` from `EX/MEM` and `r1 = 21` from `MEM/WB`! -/
def backToBackDoubleBypassProg : Array IsaInstr :=
  #[ .ADD r1 r0 r5,
     .ADD r2 r1 r1,
     .SUB r3 r2 r1,
     .XOR r4 r2 r3 ]

def backToBackInit : IsaState :=
  { pc := 0#64, regs := RegFile.empty.write r5 21#64, dmem := DataMem.empty }

#guard
  let imem := progToImem backToBackDoubleBypassProg
  let p0   := initPipeState backToBackInit
  let k    := burchDillStepsN imem 4 p0
  let sFin := flushPipeline (stepPipelineN imem 4 p0)
  k == 4 &&
  sFin == stepIsaN imem 4 backToBackInit &&
  sFin.regs.read r1 == 21#64 &&
  sFin.regs.read r2 == 42#64 &&
  sFin.regs.read r3 == 21#64 &&
  sFin.regs.read r4 == 63#64

/-- **Corner Case 2: Double-Writer Priority (`EX/MEM` Must Override Stale `MEM/WB`!).**
    `ADD r1, r0, r5; ADD r1, r1, r6; ADD r2, r1, r7` (`r5 = 5, r6 = 10, r7 = 1`) and immediate
    variant `ADDI r1, r0, 5; ADDI r1, r1, 10; ADDI r2, r1, 1`:
    When instruction 3 enters `EX`, `MEM/WB` holds stale `r1 = 5` while `EX/MEM` holds fresh `r1 = 15`.
    `forwardOperand` selects `EX/MEM` (`15`), yielding `r2 = 16` (NOT stale `6`!) in 0 stall cycles. -/
def doubleWriterAddProg : Array IsaInstr :=
  #[ .ADD r1 r0 r5,
     .ADD r1 r1 r6,
     .ADD r2 r1 r7 ]

def doubleWriterAddInit : IsaState :=
  { pc   := 0#64
    regs := ((RegFile.empty.write r5 5#64).write r6 10#64).write r7 1#64
    dmem := DataMem.empty }

def doubleWriterAddiProg : Array IsaInstr :=
  #[ .ADDI r1 r0 5#64,
     .ADDI r1 r1 10#64,
     .ADDI r2 r1 1#64 ]

#guard
  let imemA := progToImem doubleWriterAddProg
  let p0A   := initPipeState doubleWriterAddInit
  let sFinA := flushPipeline (stepPipelineN imemA 3 p0A)
  let imemI := progToImem doubleWriterAddiProg
  let p0I   := initPipeState default
  let sFinI := flushPipeline (stepPipelineN imemI 3 p0I)
  burchDillStepsN imemA 3 p0A == 3 &&
  sFinA == stepIsaN imemA 3 doubleWriterAddInit &&
  sFinA.regs.read r1 == 15#64 &&
  sFinA.regs.read r2 == 16#64 &&
  burchDillStepsN imemI 3 p0I == 3 &&
  sFinI == stepIsaN imemI 3 default &&
  sFinI.regs.read r1 == 15#64 &&
  sFinI.regs.read r2 == 16#64

/-- **Corner Case 3: `r0` Write-Ignore Attack (`ADDI r0, r0, 99; ADD r2, r0, r1`).**
    Tests BOTH `EX/MEM → EX` (1-cycle distance) and `MEM/WB → EX` (2-cycle distance) after writing
    non-zero values `99` and `77` to `r0`. Both bypass paths suppress `rd == r0`, preserving `0#64`. -/
def r0AttackProg : Array IsaInstr :=
  #[ .ADDI r0 r0 99#64,
     .ADD  r2 r0 r1,
     .ADDI r0 r0 77#64,
     .NOP,
     .ADDI r3 r0 1#64 ]

def r0AttackInit : IsaState :=
  { pc := 0#64, regs := RegFile.empty.write r1 1#64, dmem := DataMem.empty }

#guard
  let imem := progToImem r0AttackProg
  let p0   := initPipeState r0AttackInit
  let sFin := flushPipeline (stepPipelineN imem 5 p0)
  burchDillStepsN imem 5 p0 == 5 &&
  sFin == stepIsaN imem 5 r0AttackInit &&
  sFin.regs.read r0 == 0#64 &&
  sFin.regs.read r2 == 1#64 &&
  sFin.regs.read r3 == 1#64

/-- **Corner Case 4: Load-Use Hazard Interlock (`LD r1, [0]; ADD r2, r1, r5` — 1 Bubble + `MEM/WB` Forward).**
    Verifies cycle-accurate stall detection on cycle 2 (`detectLoadUseStall = true`), bubble injection
    into `ID/EX` and frozen `PC`/`IF/ID` on cycle 3, clean `MEM/WB → EX` forwarding of `100#64` on
    cycle 4, and bit-exact `IsaState` agreement with `stepIsaN`! -/
def loadUseStallProg : Array IsaInstr :=
  #[ .LD   r1 r0 0#64,
     .ADD  r2 r1 r5,
     .ADDI r3 r2 10#64,
     .ST   r0 r2 8#64 ]

def loadUseInit : IsaState :=
  { pc   := 0#64
    regs := RegFile.empty.write r5 7#64
    dmem := DataMem.empty.write 0#64 100#64 }

#guard
  let imem := progToImem loadUseStallProg
  let p0   := initPipeState loadUseInit
  let p2   := stepPipelineN imem 2 p0
  let p3   := stepPipelineN imem 3 p0
  let p5   := stepPipelineN imem 5 p0
  let sFin := flushPipeline p5
  detectLoadUseStall p2.idEx p2.ifId == true &&
  burchDillStepCount p2 == 0 &&
  p3.idEx.valid == false &&
  p3.fetchPc == p2.fetchPc &&
  p3.ifId == p2.ifId &&
  burchDillStepsN imem 5 p0 == 4 &&
  sFin == stepIsaN imem 4 loadUseInit &&
  sFin.regs.read r1 == 100#64 &&
  sFin.regs.read r2 == 107#64 &&
  sFin.regs.read r3 == 117#64 &&
  sFin.dmem.read 8#64 == 107#64

/-- **Corner Case 5A: Taken Branch Loop Computing `Fibonacci(10) = 55`!**
    Executes 10 loop iterations with `EX/MEM → EX` forwarding directly into `BNE` in `EX`, flushing
    wrong-path `IF/ID` and `ID/EX` latches on each of the 9 taken back-edges, then stores `55` to
    `dmem[64]` and matches `stepIsaN` bit-for-bit after pipeline drain! -/
def fibonacciLoopProg : Array IsaInstr :=
  #[ .ADDI r1 r0 0#64,                       -- pc 0:  a = 0
     .ADDI r2 r0 1#64,                       -- pc 4:  b = 1
     .ADDI r3 r0 10#64,                      -- pc 8:  n = 10
     .ADD  r4 r1 r2,                         -- pc 12: next = a + b
     .ADD  r1 r0 r2,                         -- pc 16: a = b
     .ADD  r2 r0 r4,                         -- pc 20: b = next
     .ADDI r3 r3 (BitVec.ofInt 64 (-1)),     -- pc 24: n = n - 1
     .BNE  r3 r0 (BitVec.ofInt 64 (-16)),    -- pc 28: if n != 0 goto 12
     .ST   r0 r1 64#64 ]                     -- pc 32: dmem[64] = a = F(10) = 55

#guard
  let imem := progToImem fibonacciLoopProg
  let p0   := initPipeState default
  let k    := burchDillStepsN imem 75 p0
  let sFin := flushPipeline (stepPipelineN imem 75 p0)
  runMatchesIsa fibonacciLoopProg default 75 &&
  sFin == stepIsaN imem k default &&
  sFin.regs.read r1 == 55#64 &&
  sFin.regs.read r2 == 89#64 &&
  sFin.regs.read r3 == 0#64 &&
  sFin.dmem.read 64#64 == 55#64

/-- **Corner Case 5B: Taken Branch Loop + Load-Use Stall Computing Sum-of-Array (`[10,20,30,40,50] = 150`)!**
    Every iteration executes `LD r4, [r1]` immediately followed by `ADD r3, r3, r4` (triggering a
    1-cycle load-use interlock + `MEM/WB → EX` forward) AND `ADDI r1, r1, 8` into `BNE r1, r2, -12`
    (triggering `EX/MEM → EX` forward into a taken branch flush!), then stores `150` to `dmem[64]`. -/
def sumArrayLoopProg : Array IsaInstr :=
  #[ .ADDI r1 r0 0#64,                       -- pc 0:  ptr = 0
     .ADDI r2 r0 40#64,                      -- pc 4:  end = 40
     .ADDI r3 r0 0#64,                       -- pc 8:  sum = 0
     .LD   r4 r1 0#64,                       -- pc 12: val = dmem[ptr]
     .ADD  r3 r3 r4,                         -- pc 16: sum += val (1-cycle load-use stall!)
     .ADDI r1 r1 8#64,                       -- pc 20: ptr += 8
     .BNE  r1 r2 (BitVec.ofInt 64 (-12)),    -- pc 24: if ptr != 40 goto 12 (taken branch squash!)
     .ST   r0 r3 64#64 ]                     -- pc 28: dmem[64] = sum = 150

def sumArrayInit : IsaState :=
  { pc   := 0#64
    regs := RegFile.empty
    dmem := (((((DataMem.empty.write 0#64 10#64).write 8#64 20#64).write 16#64 30#64).write
              24#64 40#64).write 32#64 50#64) }

#guard
  let imem := progToImem sumArrayLoopProg
  let p0   := initPipeState sumArrayInit
  let k    := burchDillStepsN imem 45 p0
  let sFin := flushPipeline (stepPipelineN imem 45 p0)
  runMatchesIsa sumArrayLoopProg sumArrayInit 45 &&
  sFin == stepIsaN imem k sumArrayInit &&
  sFin.regs.read r3 == 150#64 &&
  sFin.dmem.read 64#64 == 150#64

/-! ## 3. Cycle-Accurate Co-Simulation of Synthesizable `pipelinedRiscCoreRtlModule` -/

def checkRtlRegsMatch (rtlRegs : Nat → BitVec 64) (p : PipeState) : Bool :=
  (List.range 24).all (fun idx => rtlRegs idx == encodePipeRegs p idx)

def coSimRtlCycles (imem : InstrMem) : Nat → PipeState → (Nat → BitVec 64) → Bool
  | 0, p, rtlRegs => checkRtlRegsMatch rtlRegs p
  | n + 1, p, rtlRegs =>
    let ins := mkPipeRtlInputs imem p
    let outsOk := evalModuleOutputs pipelinedRiscCoreRtlModule ins rtlRegs ==
                  evalModuleOutputs pipelinedRiscCoreRtlModule ins (encodePipeRegs p)
    let nextRaw := stepModuleRegs pipelinedRiscCoreRtlModule false ins rtlRegs
    let nextArr : Array (BitVec 64) := (Array.range 24).map nextRaw
    checkRtlRegsMatch rtlRegs p && outsOk &&
      coSimRtlCycles imem n (stepPipeline imem p) (fun i => nextArr.getD i 0#64)

#guard
  let imem := progToImem sumArrayLoopProg
  let p0   := initPipeState sumArrayInit
  checkRtlModule pipelinedRiscCoreRtlModule &&
  checkRtlModuleW pipelinedRiscCoreRtlModule &&
  (widthErrors pipelinedRiscCoreRtlModule).isEmpty &&
  coSimRtlCycles imem 45 p0 (encodePipeRegs p0)

/-! ## 4. `#tooth` Kernel Mutation Kills (`7` Microarchitectural & Hazard Bugs Rejected) -/

/-- 1. **Reversed Bypass Priority (`MEM/WB` checked before `EX/MEM`):** corrupts double-writer
    sequences `ADD r1, ...; ADD r1, ...; ADD r2, r1, ...` with stale `MEM/WB` operands. -/
def forwardOperandMemWbFirst
    (rs : RegIdx) (idVal : BitVec 64) (exMem : ExMemLatch) (memWb : MemWbLatch) : BitVec 64 :=
  if memWb.valid && memWb.regWrite && regNonZero memWb.rd && (memWb.rd == rs) then
    memWb.wbVal
  else if exMem.valid && exMem.regWrite && !exMem.isLoad && regNonZero exMem.rd && (exMem.rd == rs) then
    exMem.aluVal
  else idVal

#tooth Obend.Hardware.PipelinedRisc.burchDill_step_commutes
  by mutation Obend.Hardware.PipelinedRisc.forwardOperand := forwardOperandMemWbFirst

/-- 2. **Missing `rd != r0` Guard in `forwardOperand`:** allows `ADDI r0, r0, 99` in `EX/MEM` or
    `MEM/WB` to forward `99` onto reads of hardwired-zero `r0`. -/
def forwardOperandMissingR0Guard
    (rs : RegIdx) (idVal : BitVec 64) (exMem : ExMemLatch) (memWb : MemWbLatch) : BitVec 64 :=
  if exMem.valid && exMem.regWrite && !exMem.isLoad && (exMem.rd == rs) then
    exMem.aluVal
  else if memWb.valid && memWb.regWrite && (memWb.rd == rs) then
    memWb.wbVal
  else idVal

#tooth Obend.Hardware.PipelinedRisc.burchDill_step_commutes
  by mutation Obend.Hardware.PipelinedRisc.forwardOperand := forwardOperandMissingR0Guard

/-- 3. **Broken `regNonZero` Guard (`fun _ => true`):** treats `r0` as a writable/forwardable
    general-purpose register. -/
def regNonZeroBroken (_ : RegIdx) : Bool := true

#tooth Obend.Hardware.PipelinedRisc.pipelinedRiscRtl_step_refines
  by mutation Obend.Hardware.PipelinedRisc.regNonZero := regNonZeroBroken

/-- 4. **Disabled Load-Use Hazard Interlock (`detectLoadUseStall := false`):** lets `ADD r2, r1, ...`
    enter `EX` 1 cycle early behind `LD r1, [0]` with an unforwarded stale register value. -/
def detectLoadUseStallDisabled (_ : IdExLatch) (_ : IfIdLatch) : Bool := false

#tooth Obend.Hardware.PipelinedRisc.burchDill_step_commutes
  by mutation Obend.Hardware.PipelinedRisc.detectLoadUseStall := detectLoadUseStallDisabled

/-- 5. **Disabled Control-Hazard Squash (`branchTakenFlush := false`):** fails to squash wrong-path
    `IF/ID` and `ID/EX` instructions and fails to redirect `fetchPc` when a branch/jump is taken in `EX`. -/
def branchTakenFlushDisabled (_ : Bool) (_ : IsaInstr) (_ _ : BitVec 64) : Bool := false

#tooth Obend.Hardware.PipelinedRisc.burchDill_step_commutes
  by mutation Obend.Hardware.PipelinedRisc.branchTakenFlush := branchTakenFlushDisabled

/-- 6. **Corrupted Execute ALU (`SUB` adds instead of subtracting):** breaks RTL-to-pipeline
    register-transfer refinement on `ex_mem_alu`. -/
def exAluResultBrokenSub (pc : BitVec 64) (instr : IsaInstr) (v1 v2 : BitVec 64) : BitVec 64 :=
  match instr with
  | .ADD .. => v1 + v2 | .SUB .. => v1 + v2 | .AND .. => v1 &&& v2
  | .OR  .. => v1 ||| v2 | .XOR .. => v1 ^^^ v2
  | .SLT .. => if BitVec.slt v1 v2 then 1#64 else 0#64
  | .ADDI _ _ imm => v1 + imm | .LD _ _ off => v1 + off | .ST _ _ off => v1 + off
  | .JAL _ _ => pc + 4#64 | .BEQ .. | .BNE .. | .NOP => 0#64

#tooth Obend.Hardware.PipelinedRisc.pipelinedRiscRtl_step_refines
  by mutation Obend.Hardware.PipelinedRisc.exAluResult := exAluResultBrokenSub

/-- 7. **Dropped Writeback Commit (`applyWb` ignores `MEM/WB`):** loses retired architectural
    register writes once instructions leave `MEM/WB`. -/
def applyWbDropped (regs : RegFile) (_ : MemWbLatch) : RegFile := regs

#tooth Obend.Hardware.PipelinedRisc.burchDill_step_commutes
  by mutation Obend.Hardware.PipelinedRisc.applyWb := applyWbDropped

end Obend.Tests.SiliconElab.PipelinedRiscBurchDill
end
