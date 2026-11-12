module
/-
# Obend.Hardware.PipelinedRisc — Synthesizable 5-Stage RISC `RtlModule` & Burch–Dill Umbrella

Re-exports the 64-bit RISC ISA, 5-stage `IF/ID/EX/MEM/WB` hazard-forwarding/interlocked pipeline,
Burch–Dill flushing equivalence proof (`burchDill_step_commutes`,
`pipelinedRisc_multiCycle_refines_isa`), and bounded no-starvation liveness theorems from
`Obend.Hardware.PipelinedRiscCore`, and synthesizes the word-level hardware datapath
`pipelinedRiscCoreRtlModule : RtlModule` with proved combinational output and sequential
register-transfer refinement (`pipelinedRiscRtl_outputs_refine`, `pipelinedRiscRtl_step_refines`).
-/
public import Obend.Hardware.HDL
public import Obend.Hardware.PipelinedRiscCore
import all Obend.Hardware.HDL
import all Obend.Hardware.PipelinedRiscCore

public section
namespace Obend.Hardware.PipelinedRisc

open Obend.Hardware.HDL

set_option autoImplicit false

/-! ## 1. Synthesizable 5-Stage `RtlModule` Datapath (`pipelinedRiscCoreRtlModule`) -/

def boolToBv (b : Bool) : BitVec 64 := if b then 1#64 else 0#64

/-- Combinational wires (`w_0 .. w_24`) of the synthesizable 5-stage `pipelinedRiscCoreRtlModule`. -/
def pipelinedRiscWires : List WireAssign :=
  [ { wireIdx := 0,  name := "id_op",    expr := .alu .bitAnd (.regRead 3) (.const 15#64) },
    { wireIdx := 1,  name := "id_rd",    expr := .alu .bitAnd (.alu .lshr (.regRead 3) (.const 4#64)) (.const 31#64) },
    { wireIdx := 2,  name := "id_rs1",   expr := .alu .bitAnd (.alu .lshr (.regRead 3) (.const 9#64)) (.const 31#64) },
    { wireIdx := 3,  name := "id_rs2",   expr := .alu .bitAnd (.alu .lshr (.regRead 3) (.const 14#64)) (.const 31#64) },
    { wireIdx := 4,  name := "id_imm",   expr := .alu .ashr (.regRead 3) (.const 20#64) },
    { wireIdx := 5,  name := "ex_is_load",  expr := .alu .eq (.regRead 6) (.const 8#64) },
    { wireIdx := 6,  name := "ex_is_store", expr := .alu .eq (.regRead 6) (.const 9#64) },
    { wireIdx := 7,  name := "ex_reg_write",
      expr := .alu .bitOr (.alu .bitAnd (.alu .ult (.const 0#64) (.regRead 6))
                                        (.alu .ult (.regRead 6) (.const 9#64)))
                          (.alu .eq (.regRead 6) (.const 12#64)) },
    { wireIdx := 8,  name := "ex_mem_can_fwd",
      expr := .alu .bitAnd (.alu .bitAnd (.regRead 13) (.regRead 15))
                           (.alu .bitAnd (.mux (.regRead 16) (.const 0#64) (.const 1#64))
                                         (.alu .ult (.const 0#64) (.regRead 14))) },
    { wireIdx := 9,  name := "mem_wb_can_fwd",
      expr := .alu .bitAnd (.alu .bitAnd (.regRead 20) (.regRead 22))
                           (.alu .ult (.const 0#64) (.regRead 21)) },
    { wireIdx := 10, name := "ex_fwd1",
      expr := .mux (.alu .bitAnd (.wireRef 8) (.alu .eq (.regRead 14) (.regRead 8))) (.regRead 18)
                (.mux (.alu .bitAnd (.wireRef 9) (.alu .eq (.regRead 21) (.regRead 8))) (.regRead 23) (.regRead 11)) },
    { wireIdx := 11, name := "ex_fwd2",
      expr := .mux (.alu .bitAnd (.wireRef 8) (.alu .eq (.regRead 14) (.regRead 9))) (.regRead 18)
                (.mux (.alu .bitAnd (.wireRef 9) (.alu .eq (.regRead 21) (.regRead 9))) (.regRead 23) (.regRead 12)) },
    { wireIdx := 12, name := "ex_alu_out",
      expr := .mux (.alu .eq (.regRead 6) (.const 1#64)) (.alu .add (.wireRef 10) (.wireRef 11))
              (.mux (.alu .eq (.regRead 6) (.const 2#64)) (.alu .sub (.wireRef 10) (.wireRef 11))
              (.mux (.alu .eq (.regRead 6) (.const 3#64)) (.alu .bitAnd (.wireRef 10) (.wireRef 11))
              (.mux (.alu .eq (.regRead 6) (.const 4#64)) (.alu .bitOr (.wireRef 10) (.wireRef 11))
              (.mux (.alu .eq (.regRead 6) (.const 5#64)) (.alu .bitXor (.wireRef 10) (.wireRef 11))
              (.mux (.alu .eq (.regRead 6) (.const 6#64)) (.alu .slt (.wireRef 10) (.wireRef 11))
              (.mux (.alu .bitOr (.alu .eq (.regRead 6) (.const 7#64)) (.alu .bitOr (.wireRef 5) (.wireRef 6)))
                    (.alu .add (.wireRef 10) (.regRead 10))
              (.mux (.alu .eq (.regRead 6) (.const 12#64)) (.alu .add (.regRead 5) (.const 4#64)) (.const 0#64)))))))) },
    { wireIdx := 13, name := "ex_raw_take",
      expr := .mux (.alu .eq (.regRead 6) (.const 10#64)) (.alu .eq (.wireRef 10) (.wireRef 11))
                (.mux (.alu .eq (.regRead 6) (.const 11#64))
                  (.mux (.alu .eq (.wireRef 10) (.wireRef 11)) (.const 0#64) (.const 1#64))
                  (.mux (.alu .eq (.regRead 6) (.const 12#64)) (.const 1#64) (.const 0#64))) },
    { wireIdx := 14, name := "branch_taken_flush", expr := .mux (.regRead 4) (.wireRef 13) (.const 0#64) },
    { wireIdx := 15, name := "ex_branch_target",   expr := .alu .add (.regRead 5) (.regRead 10) },
    { wireIdx := 16, name := "load_use_stall",
      expr := .alu .bitAnd (.alu .bitAnd (.regRead 4) (.regRead 1))
                (.alu .bitAnd (.alu .bitAnd (.wireRef 5) (.alu .ult (.const 0#64) (.regRead 7)))
                  (.alu .bitOr (.alu .eq (.regRead 7) (.wireRef 2)) (.alu .eq (.regRead 7) (.wireRef 3)))) },
    { wireIdx := 17, name := "id_ex_issue",      expr := .mux (.wireRef 14) (.const 0#64) (.mux (.wireRef 16) (.const 0#64) (.regRead 1)) },
    { wireIdx := 18, name := "next_fetch_pc",    expr := .mux (.wireRef 14) (.wireRef 15) (.mux (.wireRef 16) (.regRead 0) (.alu .add (.regRead 0) (.const 4#64))) },
    { wireIdx := 19, name := "next_if_id_valid", expr := .mux (.wireRef 14) (.const 0#64) (.mux (.wireRef 16) (.regRead 1) (.const 1#64)) },
    { wireIdx := 20, name := "next_if_id_pc",    expr := .mux (.wireRef 14) (.const 0#64) (.mux (.wireRef 16) (.regRead 2) (.regRead 0)) },
    { wireIdx := 21, name := "next_if_id_inst",  expr := .mux (.wireRef 14) (.const 0#64) (.mux (.wireRef 16) (.regRead 3) (.inputPort 0)) },
    { wireIdx := 22, name := "mem_wb_data_mux",  expr := .mux (.regRead 16) (.inputPort 1) (.regRead 18) },
    { wireIdx := 23, name := "dmem_we_w",        expr := .alu .bitAnd (.regRead 13) (.regRead 17) },
    { wireIdx := 24, name := "wb_en_w",          expr := .alu .bitAnd (.regRead 20) (.regRead 22) } ]

private def mkPipeReg (idx : Nat) (nm : String) (nxt : RtlExpr) : RegSpec :=
  { regIdx := idx, name := nm, domain := .coreClk, resetKind := .syncReset 0#64,
    isSynchronizer := false, nextExpr := nxt }

def pipelinedRiscRegs : List RegSpec :=
  [ mkPipeReg 0  "fetch_pc"         (.wireRef 18),
    mkPipeReg 1  "if_id_valid"      (.wireRef 19),
    mkPipeReg 2  "if_id_pc"         (.wireRef 20),
    mkPipeReg 3  "if_id_inst"       (.wireRef 21),
    mkPipeReg 4  "id_ex_valid"      (.wireRef 17),
    mkPipeReg 5  "id_ex_pc"         (.mux (.wireRef 17) (.regRead 2) (.const 0#64)),
    mkPipeReg 6  "id_ex_op"         (.mux (.wireRef 17) (.wireRef 0) (.const 0#64)),
    mkPipeReg 7  "id_ex_rd"         (.mux (.wireRef 17) (.wireRef 1) (.const 0#64)),
    mkPipeReg 8  "id_ex_rs1"        (.mux (.wireRef 17) (.wireRef 2) (.const 0#64)),
    mkPipeReg 9  "id_ex_rs2"        (.mux (.wireRef 17) (.wireRef 3) (.const 0#64)),
    mkPipeReg 10 "id_ex_imm"        (.mux (.wireRef 17) (.wireRef 4) (.const 0#64)),
    mkPipeReg 11 "id_ex_v1"         (.mux (.wireRef 17) (.inputPort 2) (.const 0#64)),
    mkPipeReg 12 "id_ex_v2"         (.mux (.wireRef 17) (.inputPort 3) (.const 0#64)),
    mkPipeReg 13 "ex_mem_valid"     (.regRead 4),
    mkPipeReg 14 "ex_mem_rd"        (.mux (.regRead 4) (.regRead 7) (.const 0#64)),
    mkPipeReg 15 "ex_mem_reg_write" (.mux (.regRead 4) (.wireRef 7) (.const 0#64)),
    mkPipeReg 16 "ex_mem_is_load"   (.mux (.regRead 4) (.wireRef 5) (.const 0#64)),
    mkPipeReg 17 "ex_mem_is_store"  (.mux (.regRead 4) (.wireRef 6) (.const 0#64)),
    mkPipeReg 18 "ex_mem_alu"       (.mux (.regRead 4) (.wireRef 12) (.const 0#64)),
    mkPipeReg 19 "ex_mem_store"     (.mux (.regRead 4) (.wireRef 11) (.const 0#64)),
    mkPipeReg 20 "mem_wb_valid"     (.regRead 13),
    mkPipeReg 21 "mem_wb_rd"        (.mux (.regRead 13) (.regRead 14) (.const 0#64)),
    mkPipeReg 22 "mem_wb_reg_write" (.mux (.regRead 13) (.regRead 15) (.const 0#64)),
    mkPipeReg 23 "mem_wb_val"       (.mux (.regRead 13) (.wireRef 22) (.const 0#64)) ]

def pipelinedRiscOutputs : List OutputPort :=
  [ { name := "imem_addr",  expr := .regRead 0 },  { name := "rf_raddr1",  expr := .wireRef 2 },
    { name := "rf_raddr2",  expr := .wireRef 3 },  { name := "ex_fwd1",    expr := .wireRef 10 },
    { name := "ex_fwd2",    expr := .wireRef 11 }, { name := "ex_alu_out", expr := .wireRef 12 },
    { name := "stall_out",  expr := .wireRef 16 }, { name := "flush_out",  expr := .wireRef 14 },
    { name := "dmem_addr",  expr := .regRead 18 }, { name := "dmem_wdata", expr := .regRead 19 },
    { name := "dmem_we",    expr := .wireRef 23 }, { name := "wb_valid",   expr := .regRead 20 },
    { name := "wb_en",      expr := .wireRef 24 }, { name := "wb_rd",      expr := .regRead 21 },
    { name := "wb_data",    expr := .regRead 23 } ]

/-- Synthesizable 5-stage `IF/ID/EX/MEM/WB` hazard-forwarding & interlocked RISC core `RtlModule`. -/
def pipelinedRiscCoreRtlModule : RtlModule :=
  { name       := "pipelined_risc_core_5stage"
    inputNames := ["imem_rdata", "dmem_rdata", "rf_rdata1", "rf_rdata2"]
    wires      := pipelinedRiscWires
    regs       := pipelinedRiscRegs
    outputs    := pipelinedRiscOutputs }

example : checkRtlModule pipelinedRiscCoreRtlModule = true := by decide +kernel
example : checkRtlModuleW pipelinedRiscCoreRtlModule = true := by decide +kernel
example : widthErrors pipelinedRiscCoreRtlModule = [] := by decide +kernel

theorem pipelinedRiscCoreRtlModule_faithful (inputs regs : Nat → BitVec 64) :
    checkRtlModule pipelinedRiscCoreRtlModule = true ∧
    checkRtlModuleW pipelinedRiscCoreRtlModule = true ∧
    evalModuleOutputsW pipelinedRiscCoreRtlModule inputs regs =
      evalModuleOutputs pipelinedRiscCoreRtlModule inputs regs := by
  exact ⟨by decide +kernel, by decide +kernel,
   evalModuleOutputsW_eq_of_all64 pipelinedRiscCoreRtlModule inputs regs (by decide +kernel)⟩

/-! ## 2. Pipeline-to-RTL State Projection & Combinational / Sequential Refinement Proofs -/

def encodePipeRegs (p : PipeState) : Nat → BitVec 64
  | 0  => p.fetchPc
  | 1  => boolToBv p.ifId.valid
  | 2  => if p.ifId.valid then p.ifId.pc else 0#64
  | 3  => if p.ifId.valid then encodeInstr p.ifId.instr else 0#64
  | 4  => boolToBv p.idEx.valid
  | 5  => if p.idEx.valid then p.idEx.pc else 0#64
  | 6  => if p.idEx.valid then BitVec.ofNat 64 (instrOpcode p.idEx.instr) else 0#64
  | 7  => if p.idEx.valid then BitVec.ofNat 64 (instrRd p.idEx.instr).val else 0#64
  | 8  => if p.idEx.valid then BitVec.ofNat 64 p.idEx.rs1.val else 0#64
  | 9  => if p.idEx.valid then BitVec.ofNat 64 p.idEx.rs2.val else 0#64
  | 10 => if p.idEx.valid then instrImm p.idEx.instr else 0#64
  | 11 => if p.idEx.valid then p.idEx.v1 else 0#64
  | 12 => if p.idEx.valid then p.idEx.v2 else 0#64
  | 13 => boolToBv p.exMem.valid
  | 14 => if p.exMem.valid then BitVec.ofNat 64 p.exMem.rd.val else 0#64
  | 15 => if p.exMem.valid then boolToBv p.exMem.regWrite else 0#64
  | 16 => if p.exMem.valid then boolToBv p.exMem.isLoad else 0#64
  | 17 => if p.exMem.valid then boolToBv p.exMem.isStore else 0#64
  | 18 => if p.exMem.valid then p.exMem.aluVal else 0#64
  | 19 => if p.exMem.valid then p.exMem.storeVal else 0#64
  | 20 => boolToBv p.memWb.valid
  | 21 => if p.memWb.valid then BitVec.ofNat 64 p.memWb.rd.val else 0#64
  | 22 => if p.memWb.valid then boolToBv p.memWb.regWrite else 0#64
  | 23 => if p.memWb.valid then p.memWb.wbVal else 0#64
  | _  => 0#64

def mkPipeRtlInputs (imem : InstrMem) (p : PipeState) : Nat → BitVec 64
  | 0 => encodeInstr (imem p.fetchPc)
  | 1 => p.dmem.read (if p.exMem.valid then p.exMem.aluVal else 0#64)
  | 2 => (applyWb p.regs p.memWb).read (if p.ifId.valid then instrRs1 p.ifId.instr else r0)
  | 3 => (applyWb p.regs p.memWb).read (if p.ifId.valid then instrRs2 p.ifId.instr else r0)
  | _ => 0#64

/-- Closed-form wire specification matching `pipelinedRiscWires` (`w_0..w_24`) without nested closures. -/
def specPipeWires (imem : InstrMem) (p : PipeState) : Nat → BitVec 64
  | 0  => if p.ifId.valid then BitVec.ofNat 64 (instrOpcode p.ifId.instr) else 0#64
  | 1  => if p.ifId.valid then BitVec.ofNat 64 (instrRd p.ifId.instr).val else 0#64
  | 2  => if p.ifId.valid then BitVec.ofNat 64 (instrRs1 p.ifId.instr).val else 0#64
  | 3  => if p.ifId.valid then BitVec.ofNat 64 (instrRs2 p.ifId.instr).val else 0#64
  | 4  => if p.ifId.valid then instrImm p.ifId.instr else 0#64
  | 5  => boolToBv (p.idEx.valid && instrIsLoad p.idEx.instr)
  | 6  => boolToBv (p.idEx.valid && instrIsStore p.idEx.instr)
  | 7  => boolToBv (p.idEx.valid && instrWritesReg p.idEx.instr)
  | 8  => boolToBv (p.exMem.valid && p.exMem.regWrite && !p.exMem.isLoad && regNonZero p.exMem.rd)
  | 9  => boolToBv (p.memWb.valid && p.memWb.regWrite && regNonZero p.memWb.rd)
  | 10 => if p.idEx.valid then forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb else 0#64
  | 11 => if p.idEx.valid then forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb else 0#64
  | 12 => if p.idEx.valid then exAluResult p.idEx.pc p.idEx.instr
            (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
            (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) else 0#64
  | 13 => boolToBv (branchTakenFlush p.idEx.valid p.idEx.instr
            (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
            (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb))
  | 14 => boolToBv (branchTakenFlush p.idEx.valid p.idEx.instr
            (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
            (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb))
  | 15 => if p.idEx.valid then exBranchTarget p.idEx.pc p.idEx.instr else 0#64
  | 16 => boolToBv (detectLoadUseStall p.idEx p.ifId)
  | 17 => boolToBv (!branchTakenFlush p.idEx.valid p.idEx.instr
            (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
            (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) &&
            !detectLoadUseStall p.idEx p.ifId && p.ifId.valid)
  | 18 => (stepPipeline imem p).fetchPc
  | 19 => boolToBv (stepPipeline imem p).ifId.valid
  | 20 => if (stepPipeline imem p).ifId.valid then (stepPipeline imem p).ifId.pc else 0#64
  | 21 => if (stepPipeline imem p).ifId.valid then encodeInstr (stepPipeline imem p).ifId.instr else 0#64
  | 22 => if p.exMem.valid then (if p.exMem.isLoad then p.dmem.read p.exMem.aluVal else p.exMem.aluVal) else 0#64
  | 23 => boolToBv (p.exMem.valid && p.exMem.isStore)
  | 24 => boolToBv (p.memWb.valid && p.memWb.regWrite)
  | _  => 0#64

private theorem evalWireTable_eq_of_spec
    (nIn nReg : Nat) (inputs regs specWires : Nat → BitVec 64) (assigns : List WireAssign)
    (hDag : checkWireTableDAG nIn nReg assigns = true)
    (hZero : ∀ i, assigns.length ≤ i → specWires i = 0#64)
    (hStep : ∀ a ∈ assigns, evalRtlExpr inputs specWires regs a.expr = specWires a.wireIdx) :
    evalWireTable inputs regs assigns = specWires := by
  unfold evalWireTable; unfold checkWireTableDAG at hDag
  suffices ∀ (ws : List WireAssign) (k : Nat) (env : Nat → BitVec 64),
      checkWireTableDAG.go nIn nReg k ws = true →
      (∀ i, i < k → env i = specWires i) →
      (∀ i, k + ws.length ≤ i → env i = specWires i) →
      (∀ a ∈ ws, evalRtlExpr inputs specWires regs a.expr = specWires a.wireIdx) →
      ws.foldl (fun (env : Nat → BitVec 64) a =>
        let v := evalRtlExpr inputs env regs a.expr
        fun i => if i == a.wireIdx then v else env i) env = specWires from
    this assigns 0 (fun _ => 0#64) hDag (fun _ h => nomatch h)
      (fun i hi => (hZero i (by omega)).symm) hStep
  intro ws; induction ws with
  | nil =>
    intro k env _ hLo hHi _; funext i
    by_cases hi : i < k
    · exact hLo i hi
    · exact hHi i (by simp only [List.length_nil]; omega)
  | cons a rest ih =>
    intro k env hGo hLo hHi hSt
    simp only [checkWireTableDAG.go, Bool.and_eq_true, beq_iff_eq] at hGo
    obtain ⟨⟨hIdx, hExprDag⟩, hGoRest⟩ := hGo
    have hVal : evalRtlExpr inputs env regs a.expr = specWires k := by
      rw [evalRtlExpr_dag_locality nIn nReg k inputs regs env specWires a.expr hExprDag hLo,
          hSt a List.mem_cons_self, hIdx]
    simp only [List.foldl_cons, hVal, hIdx]
    apply ih (k + 1) _ hGoRest
    · intro i hi
      by_cases hEq : i = k
      · simp [hEq]
      · simp [beq_false_of_ne hEq, hLo i (by omega)]
    · intro i hi
      have hNe : (i == k) = false := beq_false_of_ne (by omega)
      simp only [hNe, Bool.false_eq_true, ↓reduceIte]
      exact hHi i (by simp only [List.length_cons]; omega)
    · exact fun x hx => hSt x (List.mem_cons_of_mem _ hx)

private theorem boolToBv_ne_zero (b : Bool) : (boolToBv b != 0#64) = b := by cases b <;> decide
private theorem bv_zero_bne_zero : (0#64 != 0#64) = false := rfl
private theorem bv_one_bne_zero : (1#64 != 0#64) = true := rfl
private theorem boolToBv_bitAnd (a b : Bool) : (boolToBv a &&& boolToBv b) = boolToBv (a && b) := by
  cases a <;> cases b <;> decide
private theorem boolToBv_bitOr (a b : Bool) : (boolToBv a ||| boolToBv b) = boolToBv (a || b) := by
  cases a <;> cases b <;> decide
private theorem boolToBv_false_and (x : BitVec 64) : (boolToBv false &&& x) = 0#64 := BitVec.zero_and

private theorem regIdx_ult_zero (r : RegIdx) :
    (if BitVec.ult 0#64 (BitVec.ofNat 64 r.val) then 1#64 else 0#64) = boolToBv (regNonZero r) := by
  revert r; decide

private theorem regIdx_ofNat_eq (a b : RegIdx) :
    (if BitVec.ofNat 64 a.val == BitVec.ofNat 64 b.val then 1#64 else 0#64) = boolToBv (a == b) := by
  have ha := a.isLt; have hb := b.isLt
  by_cases hEq : a = b
  · subst hEq; simp [boolToBv]
  · have hValNe : a.val ≠ b.val := fun h => hEq (Fin.ext h)
    have hBvNe : BitVec.ofNat 64 a.val ≠ BitVec.ofNat 64 b.val := fun h => by
      have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
    simp [boolToBv, beq_false_of_ne hEq, beq_false_of_ne hBvNe]

/-- Shared RTL priority-forwarding mux lemma covering both `w_10` (`ex_fwd1`) and `w_11` (`ex_fwd2`). -/
private theorem rtlFwdMux_eq
    (idExValid : Bool) (rs : RegIdx) (idVal : BitVec 64) (exMem : ExMemLatch) (memWb : MemWbLatch) :
    let w8  := boolToBv (exMem.valid && exMem.regWrite && !exMem.isLoad && regNonZero exMem.rd)
    let w9  := boolToBv (memWb.valid && memWb.regWrite && regNonZero memWb.rd)
    let rRs := if idExValid then BitVec.ofNat 64 rs.val else 0#64
    let rId := if idExValid then idVal else 0#64
    let r14 := if exMem.valid then BitVec.ofNat 64 exMem.rd.val else 0#64
    let r18 := if exMem.valid then exMem.aluVal else 0#64
    let r21 := if memWb.valid then BitVec.ofNat 64 memWb.rd.val else 0#64
    let r23 := if memWb.valid then memWb.wbVal else 0#64
    (if (w8 &&& (if r14 == rRs then 1#64 else 0#64)) != 0#64 then r18
     else if (w9 &&& (if r21 == rRs then 1#64 else 0#64)) != 0#64 then r23
     else rId) =
      if idExValid then forwardOperand rs idVal exMem memWb else 0#64 := by
  have hZ : ∀ rd : RegIdx, (if BitVec.ofNat 64 rd.val == 0#64 then 1#64 else 0#64) =
      boolToBv (!regNonZero rd) := by decide
  have hAndNot : ∀ (a b : Bool), (a && b && !b) = false := by decide
  dsimp only
  cases idExValid
  · cases exMem.valid <;> cases memWb.valid
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, boolToBv_false_and, bne_self_eq_false]
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, Bool.true_and,
        boolToBv_false_and, bne_self_eq_false, hZ, boolToBv_bitAnd, hAndNot, boolToBv_ne_zero]
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, Bool.true_and, Bool.and_false,
        boolToBv_false_and, bne_self_eq_false, hZ, boolToBv_bitAnd, Bool.and_assoc, hAndNot, boolToBv_ne_zero]
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_and, Bool.and_false,
        hZ, boolToBv_bitAnd, Bool.and_assoc, hAndNot, boolToBv_ne_zero]
  · unfold forwardOperand
    cases exMem.valid <;> cases memWb.valid
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, boolToBv_false_and, bne_self_eq_false]
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, Bool.true_and,
        boolToBv_false_and, bne_self_eq_false, regIdx_ofNat_eq, boolToBv_bitAnd, boolToBv_ne_zero, Bool.and_assoc]
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, Bool.true_and,
        boolToBv_false_and, bne_self_eq_false, regIdx_ofNat_eq, boolToBv_bitAnd, boolToBv_ne_zero, Bool.and_assoc]
    · simp only [↓reduceIte, Bool.true_and, regIdx_ofNat_eq, boolToBv_bitAnd, boolToBv_ne_zero, Bool.and_assoc]

set_option linter.unusedSimpArgs false in
private theorem pipeWire_step_ok (imem : InstrMem) (p : PipeState)
    (hIfImm : p.ifId.valid = true → FitsSigned44 (instrImm p.ifId.instr) = true)
    (a : WireAssign) (ha : a ∈ pipelinedRiscWires) :
    evalRtlExpr (mkPipeRtlInputs imem p) (specPipeWires imem p) (encodePipeRegs p) a.expr =
      specPipeWires imem p a.wireIdx := by
  simp only [pipelinedRiscWires, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hIf : p.ifId.valid
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, Bool.false_eq_true, ↓reduceIte]; decide
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, ↓reduceIte]
      exact (encodeInstr_bit_slices _ (hIfImm hIf)).1
  · cases hIf : p.ifId.valid
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, Bool.false_eq_true, ↓reduceIte]; decide
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, ↓reduceIte]
      exact (encodeInstr_bit_slices _ (hIfImm hIf)).2.1
  · cases hIf : p.ifId.valid
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, Bool.false_eq_true, ↓reduceIte]; decide
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, ↓reduceIte]
      exact (encodeInstr_bit_slices _ (hIfImm hIf)).2.2.1
  · cases hIf : p.ifId.valid
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, Bool.false_eq_true, ↓reduceIte]; decide
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, ↓reduceIte]
      exact (encodeInstr_bit_slices _ (hIfImm hIf)).2.2.2.1
  · cases hIf : p.ifId.valid
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, Bool.false_eq_true, ↓reduceIte]; decide
    · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hIf, ↓reduceIte]
      exact (encodeInstr_bit_slices _ (hIfImm hIf)).2.2.2.2
  · cases hV : p.idEx.valid <;> cases hI : p.idEx.instr <;>
      (simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hV, hI,
        instrOpcode, instrIsLoad, boolToBv, ↓reduceIte, Bool.true_and, Bool.false_and]; decide)
  · cases hV : p.idEx.valid <;> cases hI : p.idEx.instr <;>
      (simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hV, hI,
        instrOpcode, instrIsStore, boolToBv, ↓reduceIte, Bool.true_and, Bool.false_and]; decide)
  · cases hV : p.idEx.valid <;> cases hI : p.idEx.instr <;>
      (simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, hV, hI,
        instrOpcode, instrWritesReg, boolToBv, ↓reduceIte, Bool.true_and, Bool.false_and]; decide)
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    cases p.exMem.valid <;> cases p.exMem.regWrite <;> cases p.exMem.isLoad <;>
      simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, Bool.true_and, Bool.not_true,
        Bool.not_false, regIdx_ult_zero, boolToBv_ne_zero, boolToBv_bitAnd, boolToBv_false_and] <;>
      cases regNonZero p.exMem.rd <;> decide
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    cases p.memWb.valid <;> cases p.memWb.regWrite <;>
      simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, Bool.true_and,
        regIdx_ult_zero, boolToBv_bitAnd, boolToBv_false_and] <;>
      cases regNonZero p.memWb.rd <;> decide
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    exact rtlFwdMux_eq p.idEx.valid p.idEx.rs1 p.idEx.v1 p.exMem p.memWb
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    exact rtlFwdMux_eq p.idEx.valid p.idEx.rs2 p.idEx.v2 p.exMem p.memWb
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    cases p.idEx.valid
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, boolToBv_bitOr]; decide
    · cases p.idEx.instr <;>
        simp only [↓reduceIte, Bool.true_and, instrOpcode, instrIsLoad, instrIsStore, instrImm,
          exAluResult, boolToBv_bitOr]
      all_goals rfl
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    cases p.idEx.valid
    · simp only [↓reduceIte, Bool.false_eq_true, branchTakenFlush, Bool.false_and]; decide
    · by_cases hEq : (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb ==
          forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = true
      · cases p.idEx.instr <;>
          (simp only [↓reduceIte, instrOpcode, branchTakenFlush, Bool.true_and,
            evalBranchCond, bne, hEq, Bool.not_true, boolToBv, bv_zero_bne_zero, bv_one_bne_zero]; decide)
      · simp only [Bool.not_eq_true] at hEq
        cases p.idEx.instr <;>
          (simp only [↓reduceIte, instrOpcode, branchTakenFlush, Bool.true_and,
            evalBranchCond, bne, hEq, Bool.false_eq_true, Bool.not_false,
            boolToBv, bv_zero_bne_zero, bv_one_bne_zero]; decide)
  · simp only [evalRtlExpr, encodePipeRegs, specPipeWires]
    cases p.idEx.valid <;> simp only [↓reduceIte, Bool.false_eq_true, branchTakenFlush,
      Bool.true_and, Bool.false_and, boolToBv, bv_zero_bne_zero, bv_one_bne_zero]
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    cases p.idEx.valid <;> simp only [↓reduceIte, Bool.false_eq_true, exBranchTarget, BitVec.add_zero]
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires, detectLoadUseStall]
    cases p.idEx.valid <;> cases p.ifId.valid <;>
      simp only [↓reduceIte, Bool.false_eq_true, Bool.false_and, Bool.true_and,
        regIdx_ult_zero, regIdx_ofNat_eq, boolToBv_false_and, boolToBv_bitAnd, boolToBv_bitOr, Bool.and_assoc]
    all_goals (try decide)
  · simp only [evalRtlExpr, encodePipeRegs, specPipeWires]
    cases branchTakenFlush p.idEx.valid p.idEx.instr
      (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
      (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) <;>
    cases detectLoadUseStall p.idEx p.ifId <;>
    cases p.ifId.valid <;> decide
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    dsimp only [stepPipeline, stepCore]
    by_cases hSq : branchTakenFlush p.idEx.valid p.idEx.instr
        (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
        (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = true
    · have hExV := (branchTaken_not_load _ _ _ _ hSq).1
      simp only [hSq, hExV, ↓reduceIte, boolToBv_ne_zero]
    · simp only [Bool.not_eq_true] at hSq
      cases detectLoadUseStall p.idEx p.ifId <;>
        simp only [hSq, ↓reduceIte, Bool.false_eq_true, boolToBv_ne_zero]
  · simp only [evalRtlExpr, encodePipeRegs, specPipeWires]
    dsimp only [stepPipeline, stepCore]
    by_cases hSq : branchTakenFlush p.idEx.valid p.idEx.instr
        (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
        (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = true <;>
    by_cases hSt : detectLoadUseStall p.idEx p.ifId = true <;>
    by_cases hIf : p.ifId.valid = true <;>
      (try simp only [Bool.not_eq_true] at hSq hSt hIf) <;>
      simp only [hSq, hSt, hIf, ↓reduceIte, Bool.false_eq_true,
        IfIdLatch.bubble, boolToBv, bv_zero_bne_zero, bv_one_bne_zero]
  · simp only [evalRtlExpr, encodePipeRegs, specPipeWires]
    dsimp only [stepPipeline, stepCore]
    by_cases hSq : branchTakenFlush p.idEx.valid p.idEx.instr
        (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
        (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = true <;>
    by_cases hSt : detectLoadUseStall p.idEx p.ifId = true <;>
    by_cases hIf : p.ifId.valid = true <;>
      (try simp only [Bool.not_eq_true] at hSq hSt hIf) <;>
      simp only [hSq, hSt, hIf, ↓reduceIte, Bool.false_eq_true,
        IfIdLatch.bubble, boolToBv, bv_zero_bne_zero, bv_one_bne_zero]
  · simp only [evalRtlExpr, encodePipeRegs, mkPipeRtlInputs, specPipeWires]
    dsimp only [stepPipeline, stepCore]
    by_cases hSq : branchTakenFlush p.idEx.valid p.idEx.instr
        (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
        (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = true <;>
    by_cases hSt : detectLoadUseStall p.idEx p.ifId = true <;>
    by_cases hIf : p.ifId.valid = true <;>
      (try simp only [Bool.not_eq_true] at hSq hSt hIf) <;>
      simp only [hSq, hSt, hIf, ↓reduceIte, Bool.false_eq_true,
        IfIdLatch.bubble, boolToBv, bv_zero_bne_zero, bv_one_bne_zero]
  · simp only [evalRtlExpr, encodePipeRegs, mkPipeRtlInputs, specPipeWires]
    cases p.exMem.valid <;> cases p.exMem.isLoad <;>
      simp only [↓reduceIte, Bool.false_eq_true, boolToBv_ne_zero, bne_self_eq_false]
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    cases p.exMem.valid <;> cases p.exMem.isStore <;> decide
  · simp only [evalRtlExpr, evalAluOp, encodePipeRegs, specPipeWires]
    cases p.memWb.valid <;> cases p.memWb.regWrite <;> decide

/-- Single-pass wire-table evaluation of `pipelinedRiscCoreRtlModule` agrees identically with `specPipeWires`. -/
theorem evalWireTable_pipelinedRisc (imem : InstrMem) (p : PipeState)
    (hIfImm : p.ifId.valid = true → FitsSigned44 (instrImm p.ifId.instr) = true) :
    evalWireTable (mkPipeRtlInputs imem p) (encodePipeRegs p) pipelinedRiscWires =
      specPipeWires imem p := by
  apply evalWireTable_eq_of_spec 4 24 _ _ _ pipelinedRiscWires (by decide +kernel)
  · intro i hi
    simp only [pipelinedRiscWires, List.length] at hi
    dsimp only [specPipeWires]; split; all_goals first | rfl | omega
  · exact pipeWire_step_ok imem p hIfImm

/-- **Combinational Output Refinement Theorem (`pipelinedRiscRtl_outputs_refine`).** -/
theorem pipelinedRiscRtl_outputs_refine (imem : InstrMem) (p : PipeState)
    (hIfImm : p.ifId.valid = true → FitsSigned44 (instrImm p.ifId.instr) = true) :
    let fwd1 := forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb
    let fwd2 := forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb
    evalModuleOutputs pipelinedRiscCoreRtlModule (mkPipeRtlInputs imem p) (encodePipeRegs p) =
      [ ("imem_addr",  p.fetchPc),
        ("rf_raddr1",  if p.ifId.valid then BitVec.ofNat 64 (instrRs1 p.ifId.instr).val else 0#64),
        ("rf_raddr2",  if p.ifId.valid then BitVec.ofNat 64 (instrRs2 p.ifId.instr).val else 0#64),
        ("ex_fwd1",    if p.idEx.valid then fwd1 else 0#64),
        ("ex_fwd2",    if p.idEx.valid then fwd2 else 0#64),
        ("ex_alu_out", if p.idEx.valid then exAluResult p.idEx.pc p.idEx.instr fwd1 fwd2 else 0#64),
        ("stall_out",  boolToBv (detectLoadUseStall p.idEx p.ifId)),
        ("flush_out",  boolToBv (branchTakenFlush p.idEx.valid p.idEx.instr fwd1 fwd2)),
        ("dmem_addr",  if p.exMem.valid then p.exMem.aluVal else 0#64),
        ("dmem_wdata", if p.exMem.valid then p.exMem.storeVal else 0#64),
        ("dmem_we",    boolToBv (p.exMem.valid && p.exMem.isStore)),
        ("wb_valid",   boolToBv p.memWb.valid),
        ("wb_en",      boolToBv (p.memWb.valid && p.memWb.regWrite)),
        ("wb_rd",      if p.memWb.valid then BitVec.ofNat 64 p.memWb.rd.val else 0#64),
        ("wb_data",    if p.memWb.valid then p.memWb.wbVal else 0#64) ] := by
  unfold evalModuleOutputs pipelinedRiscCoreRtlModule
  simp only [evalWireTable_pipelinedRisc imem p hIfImm, pipelinedRiscOutputs, List.map,
    evalRtlExpr, encodePipeRegs, specPipeWires]

private def checkRegIdxSeq : Nat → List RegSpec → Bool
  | _, [] => true
  | k, r :: rest => (r.regIdx == k) && (r.resetKind == .syncReset 0#64) && checkRegIdxSeq (k + 1) rest

private theorem stepModuleRegs_eq_of_spec
    (m : RtlModule) (inputs wireEnv regState targetRegs : Nat → BitVec 64)
    (hWires : evalWireTable inputs regState m.wires = wireEnv)
    (hSeq : checkRegIdxSeq 0 m.regs = true)
    (hHi : ∀ i, m.regs.length ≤ i → targetRegs i = regState i)
    (hStep : ∀ r ∈ m.regs, evalRtlExpr inputs wireEnv regState r.nextExpr = targetRegs r.regIdx) :
    stepModuleRegs m false inputs regState = targetRegs := by
  unfold stepModuleRegs; rw [hWires]
  suffices ∀ (rs : List RegSpec) (k : Nat) (st : Nat → BitVec 64),
      checkRegIdxSeq k rs = true →
      (∀ i, i < k → st i = targetRegs i) →
      (∀ i, k + rs.length ≤ i → st i = targetRegs i) →
      (∀ r ∈ rs, evalRtlExpr inputs wireEnv regState r.nextExpr = targetRegs r.regIdx) →
      rs.foldl (fun (nextSt : Nat → BitVec 64) r =>
        let v := match r.resetKind with
          | .resetFree => evalRtlExpr inputs wireEnv regState r.nextExpr
          | .syncReset initVal => if false then initVal else evalRtlExpr inputs wireEnv regState r.nextExpr
        fun i => if i == r.regIdx then v else nextSt i) st = targetRegs from
    this m.regs 0 regState hSeq (fun _ h => nomatch h) (fun i hi => (hHi i (by omega)).symm) hStep
  intro rs; induction rs with
  | nil =>
    intro k st _ hLo hHi' _; funext i
    by_cases hi : i < k
    · exact hLo i hi
    · exact hHi' i (by simp only [List.length_nil]; omega)
  | cons r rest ih =>
    intro k st hS hLo hHi' hSt
    simp only [checkRegIdxSeq, Bool.and_eq_true, beq_iff_eq] at hS
    obtain ⟨⟨hIdx, hRst⟩, hSRest⟩ := hS
    have hVal : evalRtlExpr inputs wireEnv regState r.nextExpr = targetRegs k := by
      rw [hSt r List.mem_cons_self, hIdx]
    simp only [List.foldl_cons, hRst, Bool.false_eq_true, ↓reduceIte, hVal, hIdx]
    apply ih (k + 1) _ hSRest
    · intro i hi
      by_cases hEq : i = k
      · simp [hEq]
      · simp [beq_false_of_ne hEq, hLo i (by omega)]
    · intro i hi
      have hNe : (i == k) = false := beq_false_of_ne (by omega)
      simp only [hNe, Bool.false_eq_true, ↓reduceIte]
      exact hHi' i (by simp only [List.length_cons]; omega)
    · exact fun x hx => hSt x (List.mem_cons_of_mem _ hx)

set_option linter.unusedSimpArgs false in
/-- **Sequential Register-Transfer Refinement Theorem (`pipelinedRiscRtl_step_refines`).**
    Stepping `pipelinedRiscCoreRtlModule` by one clock edge (`rst = false`) commutes identically
    with `stepPipeline imem p` under `encodePipeRegs` across all 24 pipeline latch registers! -/
theorem pipelinedRiscRtl_step_refines (imem : InstrMem) (p : PipeState)
    (hIfImm : p.ifId.valid = true → FitsSigned44 (instrImm p.ifId.instr) = true) :
    stepModuleRegs pipelinedRiscCoreRtlModule false (mkPipeRtlInputs imem p) (encodePipeRegs p) =
      encodePipeRegs (stepPipeline imem p) := by
  apply stepModuleRegs_eq_of_spec pipelinedRiscCoreRtlModule
    (mkPipeRtlInputs imem p) (specPipeWires imem p) (encodePipeRegs p)
    (encodePipeRegs (stepPipeline imem p))
    (evalWireTable_pipelinedRisc imem p hIfImm)
    (by decide +kernel)
  · intro i hi
    simp only [pipelinedRiscCoreRtlModule, pipelinedRiscRegs, List.length] at hi
    dsimp only [encodePipeRegs]; split; all_goals first | rfl | omega
  · intro r hr
    simp only [pipelinedRiscCoreRtlModule, pipelinedRiscRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [mkPipeReg, evalRtlExpr, encodePipeRegs, mkPipeRtlInputs, specPipeWires]
    all_goals first
      | rfl
      | (dsimp only [stepPipeline, stepCore]
         by_cases hSq : branchTakenFlush p.idEx.valid p.idEx.instr
           (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
           (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = true <;>
         by_cases hSt : detectLoadUseStall p.idEx p.ifId = true <;>
         by_cases hIf : p.ifId.valid = true <;>
           (try simp only [Bool.not_eq_true] at hSq hSt hIf) <;>
           simp only [hSq, hSt, hIf, ↓reduceIte, Bool.false_eq_true, Bool.true_or, Bool.false_or,
             Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
             IdExLatch.bubble, boolToBv, bv_zero_bne_zero, bv_one_bne_zero]
         done)
      | (dsimp only [stepPipeline, stepCore]
         by_cases hEx : p.idEx.valid = true <;>
           (try simp only [Bool.not_eq_true] at hEx) <;>
           simp only [hEx, ↓reduceIte, Bool.false_eq_true, Bool.true_and, Bool.false_and,
             ExMemLatch.bubble, boolToBv, bv_zero_bne_zero, bv_one_bne_zero]
         done)
      | (dsimp only [stepPipeline, stepCore, memStepWb]
         by_cases hEm : p.exMem.valid = true <;>
           (try simp only [Bool.not_eq_true] at hEm) <;>
           simp only [hEm, ↓reduceIte, Bool.false_eq_true, Bool.true_and, Bool.false_and,
             MemWbLatch.bubble, boolToBv, bv_zero_bne_zero, bv_one_bne_zero]
         done)

end Obend.Hardware.PipelinedRisc
end
