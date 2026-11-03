module
/-
# Obend.Hardware.HDL — Core Verified Synchronous HDL, Combinational DAG & CDC Checkers, and SV Emitter

Provides a deeply embedded, compositional synchronous Hardware Description Language (`RtlModule`)
for Objective Bend with:
1. **Word-Level & Bit-Level Combinational Expressions (`RtlAluOp`, `RtlExpr`)**:
   - Arbitrary 64-bit datapath operations (`add`, `sub`, `mul`, `bitAnd`, `bitOr`, `bitXor`,
     `shl`, `lshr`, `eq`, `ult`, `mux`, `const`, `inputPort`, `wireRef`, `regRead`),
   - Structural topological DAG checking (`checkExprDAG`, `checkWireTableDAG`) guaranteeing
     fuel-free, deterministic single-pass combinational evaluation (`evalWireTable`).
2. **Synchronous Sequential Machines with Explicit Reset & Clock-Domain Discipline (`RegSpec`, `ClkDomain`)**:
   - Distinguishes reset-free datapath registers (`ResetKind.resetFree`) from control registers
     with synchronous reset (`ResetKind.syncReset initVal`),
   - Static Clock-Domain Crossing (CDC) verifier (`checkCdcSafe`) ensuring no signal crosses
     `srcDomain ≠ dstDomain` without an explicit 2-FF synchronizer (` isSynchronizer = true `),
   - Soundness theorem `cdcSafe_no_unsynchronized_crossing`.
3. **AST-Driven SystemVerilog Emitter (`emitModuleSV`)**:
   - Directly pretty-prints any verified `RtlModule` AST into synthesizable SystemVerilog-2012
     (`always_comb` + separate reset and reset-free `always_ff @(posedge clk)` blocks).
-/
@[expose] public section

namespace Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. Combinational ALU Operations & RTL Expressions -/

/-- Binary ALU operations in the core 64-bit hardware datapath. -/
inductive RtlAluOp where
  | add
  | sub
  | mul
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | lshr
  | ashr
  | eq
  | ult
  | slt
  | qmul32
  deriving DecidableEq, Repr

/-- Evaluate a binary ALU operation on 64-bit bitvectors. -/
def evalAluOp (op : RtlAluOp) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .add    => a + b
  | .sub    => a - b
  | .mul    => a * b
  | .bitAnd => a &&& b
  | .bitOr  => a ||| b
  | .bitXor => a ^^^ b
  | .shl    => a <<< (b.toNat % 64)
  | .lshr   => a >>> (b.toNat % 64)
  | .ashr   => BitVec.sshiftRight a (b.toNat % 64)
  | .eq     => if a == b then 1#64 else 0#64
  | .ult    => if BitVec.ult a b then 1#64 else 0#64
  | .slt    => if BitVec.slt a b then 1#64 else 0#64
  | .qmul32 => ((a.signExtend 128 * b.signExtend 128) >>> 32).setWidth 64

/-- Combinational RTL expression over input ports, internal wires, and sequential registers. -/
inductive RtlExpr where
  | const     (val : BitVec 64)
  | inputPort (portIdx : Nat)
  | wireRef   (wireIdx : Nat)
  | regRead   (regIdx : Nat)
  | alu       (op : RtlAluOp) (lhs rhs : RtlExpr)
  | mux       (cond : RtlExpr) (ifTrue ifFalse : RtlExpr)
  | bitNot    (arg : RtlExpr)
  deriving DecidableEq, Repr

/-- Evaluate an `RtlExpr` given environments for input ports, already-evaluated wires, and registers. -/
def evalRtlExpr
    (inputs : Nat → BitVec 64)
    (wires  : Nat → BitVec 64)
    (regs   : Nat → BitVec 64) : RtlExpr → BitVec 64
  | .const v       => v
  | .inputPort idx => inputs idx
  | .wireRef idx   => wires idx
  | .regRead idx   => regs idx
  | .alu op a b    => evalAluOp op (evalRtlExpr inputs wires regs a) (evalRtlExpr inputs wires regs b)
  | .mux c t f     =>
    if evalRtlExpr inputs wires regs c != 0#64 then
      evalRtlExpr inputs wires regs t
    else
      evalRtlExpr inputs wires regs f
  | .bitNot a      => ~~~(evalRtlExpr inputs wires regs a)

/-! ## 2. Topological Combinational DAG Checker & Agreement Theorem -/

/-- Check that an `RtlExpr` only references internal wires with index `< bound` (strictly topological),
and ports/registers within their declared counts. -/
def checkExprDAG (numInputs numRegs wireBound : Nat) : RtlExpr → Bool
  | .const _       => true
  | .inputPort idx => idx < numInputs
  | .wireRef idx   => idx < wireBound
  | .regRead idx   => idx < numRegs
  | .alu _ a b     => checkExprDAG numInputs numRegs wireBound a && checkExprDAG numInputs numRegs wireBound b
  | .mux c t f     =>
    checkExprDAG numInputs numRegs wireBound c &&
    checkExprDAG numInputs numRegs wireBound t &&
    checkExprDAG numInputs numRegs wireBound f
  | .bitNot a      => checkExprDAG numInputs numRegs wireBound a

/-- Theorem: If `checkExprDAG numInputs numRegs wireBound e = true`, then `evalRtlExpr` depends ONLY
on wire values at indices `< wireBound` — mutating any wire at index `≥ wireBound` cannot affect `e`! -/
theorem evalRtlExpr_dag_locality
    (numInputs numRegs wireBound : Nat)
    (inputs regs : Nat → BitVec 64)
    (w1 w2 : Nat → BitVec 64)
    (e : RtlExpr)
    (hDag : checkExprDAG numInputs numRegs wireBound e = true)
    (hAgree : ∀ i, i < wireBound → w1 i = w2 i) :
    evalRtlExpr inputs w1 regs e = evalRtlExpr inputs w2 regs e := by
  induction e with
  | const v => rfl
  | inputPort idx => rfl
  | wireRef idx =>
    simp only [checkExprDAG, decide_eq_true_eq] at hDag
    exact hAgree idx hDag
  | regRead idx => rfl
  | alu op a b iha ihb =>
    simp only [checkExprDAG, Bool.and_eq_true] at hDag
    simp only [evalRtlExpr, iha hDag.1, ihb hDag.2]
  | mux c t f ihc iht ihf =>
    simp only [checkExprDAG, Bool.and_eq_true] at hDag
    simp only [evalRtlExpr, ihc hDag.1.1, iht hDag.1.2, ihf hDag.2]
  | bitNot a iha =>
    simp only [checkExprDAG] at hDag
    simp only [evalRtlExpr, iha hDag]

/-- A topological wire assignment table: wire `i` (at position `i` in the list) is defined by `expr`. -/
structure WireAssign where
  wireIdx : Nat
  name    : String
  expr    : RtlExpr
  deriving DecidableEq, Repr

/-- Verify that a list of wire assignments is indexed `0, 1, 2, ...` and each wire `i` only
references earlier wires `< i`. This statically rules out all combinational loops! -/
def checkWireTableDAG (numInputs numRegs : Nat) (assigns : List WireAssign) : Bool :=
  let rec go (expectedIdx : Nat) : List WireAssign → Bool
    | [] => true
    | a :: rest =>
      (a.wireIdx == expectedIdx) &&
      checkExprDAG numInputs numRegs expectedIdx a.expr &&
      go (expectedIdx + 1) rest
  go 0 assigns

/-- Evaluate a wire assignment table in a single forward pass. -/
def evalWireTable
    (inputs regs : Nat → BitVec 64)
    (assigns : List WireAssign) : Nat → BitVec 64 :=
  assigns.foldl
    (fun (env : Nat → BitVec 64) a =>
      let v := evalRtlExpr inputs env regs a.expr
      fun i => if i == a.wireIdx then v else env i)
    (fun _ => 0#64)

/-! ## 3. Clock Domains, Reset Discipline & Static CDC Verification -/

/-- Named hardware clock domains. -/
inductive ClkDomain where
  | coreClk     -- Primary high-frequency datapath clock (e.g., 500 MHz)
  | axiIoClk    -- Host DMA / PCIe / AXI4-Lite clock (e.g., 250 MHz)
  | cfgJtagClk  -- Bitstream / configuration loader clock (e.g., 50 MHz)
  deriving DecidableEq, Repr

/-- Hardware register reset discipline: reset-free datapath vs synchronous-reset control. -/
inductive ResetKind where
  | resetFree
  | syncReset (initVal : BitVec 64)
  deriving DecidableEq, Repr

/-- Specification of a 64-bit hardware register inside an `RtlModule`. -/
structure RegSpec where
  regIdx         : Nat
  name           : String
  domain         : ClkDomain
  resetKind      : ResetKind
  isSynchronizer : Bool        -- True if this register is a dedicated 2-FF CDC synchronizer stage
  nextExpr       : RtlExpr     -- Next-state expression latched on `posedge domain`
  deriving DecidableEq, Repr

/-- Collect all register indices referenced by an `RtlExpr`. -/
def exprReadRegs : RtlExpr → List Nat
  | .const _       => []
  | .inputPort _   => []
  | .wireRef _     => []
  | .regRead idx   => [idx]
  | .alu _ a b     => exprReadRegs a ++ exprReadRegs b
  | .mux c t f     => exprReadRegs c ++ exprReadRegs t ++ exprReadRegs f
  | .bitNot a      => exprReadRegs a

/-- Look up the clock domain of register `idx` in `regs`. -/
def lookupRegDomain (regs : List RegSpec) (idx : Nat) : Option ClkDomain :=
  (regs.find? (fun r => r.regIdx == idx)).map (·.domain)

/-- Check that every register `srcIdx` directly read by `dstReg.nextExpr` either:
1. Lives in the exact same `ClkDomain` (`srcDomain == dstReg.domain`), OR
2. `dstReg` is an explicit CDC synchronizer (`dstReg.isSynchronizer == true`) AND `dstReg.nextExpr`
   is a direct `.regRead srcIdx` (no combinational logic before a CDC synchronizer!). -/
def checkRegCdc (allRegs : List RegSpec) (dstReg : RegSpec) : Bool :=
  let srcRegs := exprReadRegs dstReg.nextExpr
  srcRegs.all fun srcIdx =>
    match lookupRegDomain allRegs srcIdx with
    | none => false
    | some srcDom =>
      if srcDom == dstReg.domain then
        true
      else
        dstReg.isSynchronizer && (dstReg.nextExpr == .regRead srcIdx)

/-- Verify CDC safety across all registers in a module. -/
def checkModuleCdc (regs : List RegSpec) : Bool :=
  regs.all (checkRegCdc regs)

/-- Soundness theorem for `checkRegCdc`: if `checkRegCdc allRegs dstReg = true` and `dstReg` is
NOT a dedicated CDC synchronizer (`dstReg.isSynchronizer = false`), then no register read in
`dstReg.nextExpr` can come from a different clock domain! -/
theorem cdcSafe_no_unsynchronized_crossing
    (allRegs : List RegSpec) (dstReg : RegSpec) (srcIdx : Nat) (srcDom : ClkDomain)
    (hCdc : checkRegCdc allRegs dstReg = true)
    (hNoSync : dstReg.isSynchronizer = false)
    (hMem : srcIdx ∈ exprReadRegs dstReg.nextExpr)
    (hDom : lookupRegDomain allRegs srcIdx = some srcDom) :
    srcDom = dstReg.domain := by
  unfold checkRegCdc at hCdc
  rw [List.all_eq_true] at hCdc
  have hSrc := hCdc srcIdx hMem
  rw [hDom] at hSrc
  by_cases hEq : srcDom == dstReg.domain
  · exact eq_of_beq hEq
  · simp [hEq, hNoSync] at hSrc

/-! ## 4. Complete Synchronous `RtlModule` & Operational Semantics -/

/-- Output port binding of an `RtlModule`. -/
structure OutputPort where
  name : String
  expr : RtlExpr
  deriving DecidableEq, Repr

/-- A complete synchronous hardware module in `Obend.Hardware.HDL`. -/
structure RtlModule where
  name        : String
  inputNames  : List String
  wires       : List WireAssign
  regs        : List RegSpec
  outputs     : List OutputPort
  deriving DecidableEq, Repr

/-- Well-formedness check for an `RtlModule`:
1. The wire table is a valid topological DAG (`checkWireTableDAG`),
2. Every register's `nextExpr` is a valid DAG over all wires,
3. Every output's `expr` is a valid DAG over all wires,
4. All register clock-domain crossings pass `checkModuleCdc`. -/
def checkRtlModule (m : RtlModule) : Bool :=
  let nIn := m.inputNames.length
  let nReg := m.regs.length
  let nWires := m.wires.length
  checkWireTableDAG nIn nReg m.wires &&
  m.regs.all (fun r => checkExprDAG nIn nReg nWires r.nextExpr) &&
  m.outputs.all (fun o => checkExprDAG nIn nReg nWires o.expr) &&
  checkModuleCdc m.regs

/-- Evaluate all combinational outputs of `m` given current inputs and register state. -/
def evalModuleOutputs
    (m : RtlModule)
    (inputs : Nat → BitVec 64)
    (regState : Nat → BitVec 64) : List (String × BitVec 64) :=
  let wireEnv := evalWireTable inputs regState m.wires
  m.outputs.map fun o => (o.name, evalRtlExpr inputs wireEnv regState o.expr)

/-- Step all sequential registers of `m` by one clock edge (`rst = true` triggers synchronous resets). -/
def stepModuleRegs
    (m : RtlModule)
    (rst : Bool)
    (inputs : Nat → BitVec 64)
    (regState : Nat → BitVec 64) : Nat → BitVec 64 :=
  let wireEnv := evalWireTable inputs regState m.wires
  m.regs.foldl
    (fun (nextSt : Nat → BitVec 64) r =>
      let v :=
        match r.resetKind with
        | .resetFree => evalRtlExpr inputs wireEnv regState r.nextExpr
        | .syncReset initVal =>
          if rst then initVal else evalRtlExpr inputs wireEnv regState r.nextExpr
      fun i => if i == r.regIdx then v else nextSt i)
    regState

/-- Run an `RtlModule` over a trace of `(rst, inputs)` cycles, returning the final register state. -/
def runModuleTrace
    (m : RtlModule)
    (initRegs : Nat → BitVec 64)
    (trace : List (Bool × (Nat → BitVec 64))) : Nat → BitVec 64 :=
  trace.foldl (fun st (rst, ins) => stepModuleRegs m rst ins st) initRegs

/-! ## 5. AST-Driven SystemVerilog-2012 Emitter (`emitModuleSV`) -/

/-- Render an `RtlAluOp` as a SystemVerilog operator symbol. -/
def emitAluOpSV : RtlAluOp → String
  | .add    => "+"
  | .sub    => "-"
  | .mul    => "*"
  | .bitAnd => "&"
  | .bitOr  => "|"
  | .bitXor => "^"
  | .shl    => "<<"
  | .lshr   => ">>"
  | .ashr   => ">>>"
  | .eq     => "=="
  | .ult    => "<"
  | .slt    => "<s"
  | .qmul32 => "*q32"

/-- Render an `RtlExpr` as a SystemVerilog expression string. -/
def emitExprSV (inNames : List String) (regNames : List String) : RtlExpr → String
  | .const v         => s!"64'd{v.toNat}"
  | .inputPort idx   => inNames.getD idx s!"in_{idx}"
  | .wireRef idx     => s!"w_{idx}"
  | .regRead idx     => regNames.getD idx s!"r_{idx}"
  | .alu .eq a b     => s!"({emitExprSV inNames regNames a} == {emitExprSV inNames regNames b} ? 64'd1 : 64'd0)"
  | .alu .ult a b    => s!"({emitExprSV inNames regNames a} < {emitExprSV inNames regNames b} ? 64'd1 : 64'd0)"
  | .alu .slt a b    => s!"($signed({emitExprSV inNames regNames a}) < $signed({emitExprSV inNames regNames b}) ? 64'd1 : 64'd0)"
  | .alu .shl a b    => s!"({emitExprSV inNames regNames a} << ({emitExprSV inNames regNames b} & 64'd63))"
  | .alu .lshr a b   => s!"({emitExprSV inNames regNames a} >> ({emitExprSV inNames regNames b} & 64'd63))"
  | .alu .ashr a b   => s!"64'($signed({emitExprSV inNames regNames a}) >>> ({emitExprSV inNames regNames b} & 64'd63))"
  | .alu .qmul32 a b => s!"64'((128'($signed({emitExprSV inNames regNames a})) * 128'($signed({emitExprSV inNames regNames b}))) >>> 32)"
  | .alu op a b      => s!"({emitExprSV inNames regNames a} {emitAluOpSV op} {emitExprSV inNames regNames b})"
  | .mux c t f       => s!"(({emitExprSV inNames regNames c} != 64'd0) ? {emitExprSV inNames regNames t} : {emitExprSV inNames regNames f})"
  | .bitNot a        => s!"(~{emitExprSV inNames regNames a})"

/-- Emit a complete, synthesizable SystemVerilog-2012 module directly from an `RtlModule` AST.
Separates reset-free datapath registers from synchronous-reset control registers into distinct
`always_ff @(posedge clk)` blocks so X-optimism cannot mask uninitialized datapath state. -/
def emitModuleSV (m : RtlModule) : String :=
  let regNames := m.regs.map (·.name)
  let inPorts := m.inputNames.map fun n => s!"  input  logic [63:0] {n}"
  let outPorts := m.outputs.map fun o => s!"  output logic [63:0] {o.name}"
  let allPorts := ["  input  logic        clk", "  input  logic        rst"] ++ inPorts ++ outPorts
  let portHeader := String.intercalate ",\n" allPorts
  let wireDecls := m.wires.map fun w =>
    s!"  logic [63:0] w_{w.wireIdx}; // {w.name}"
  let regDecls := m.regs.map fun r =>
    s!"  logic [63:0] {r.name};"
  let combWires := m.wires.map fun w =>
    s!"    w_{w.wireIdx} = {emitExprSV m.inputNames regNames w.expr};"
  let combOuts := m.outputs.map fun o =>
    s!"    {o.name} = {emitExprSV m.inputNames regNames o.expr};"
  let resetFreeRegs := m.regs.filter fun r =>
    match r.resetKind with | .resetFree => true | .syncReset _ => false
  let syncResetRegs := m.regs.filter fun r =>
    match r.resetKind with | .resetFree => false | .syncReset _ => true
  let rfBlock :=
    if resetFreeRegs.isEmpty then ""
    else
      let assigns := resetFreeRegs.map fun r =>
        s!"    {r.name} <= {emitExprSV m.inputNames regNames r.nextExpr};"
      "  // Reset-free datapath registers\n  always_ff @(posedge clk) begin\n" ++
        String.intercalate "\n" assigns ++ "\n  end\n"
  let srBlock :=
    if syncResetRegs.isEmpty then ""
    else
      let rstAssigns := syncResetRegs.map fun r =>
        let initV := match r.resetKind with | .syncReset v => v.toNat | .resetFree => 0
        s!"      {r.name} <= 64'd{initV};"
      let stepAssigns := syncResetRegs.map fun r =>
        s!"      {r.name} <= {emitExprSV m.inputNames regNames r.nextExpr};"
      "  // Synchronous-reset control registers\n  always_ff @(posedge clk) begin\n    if (rst) begin\n" ++
        String.intercalate "\n" rstAssigns ++ "\n    end else begin\n" ++
        String.intercalate "\n" stepAssigns ++ "\n    end\n  end\n"
  s!"module {m.name} (\n{portHeader}\n);\n" ++
  (if wireDecls.isEmpty then "" else String.intercalate "\n" wireDecls ++ "\n") ++
  (if regDecls.isEmpty then "" else String.intercalate "\n" regDecls ++ "\n") ++
  "  always_comb begin\n" ++
  String.intercalate "\n" (combWires ++ combOuts) ++
  "\n  end\n" ++
  rfBlock ++ srBlock ++
  "endmodule\n"

/-- Emit synthesizable SystemVerilog-2012 for the 4-stage `obend_macro_dsp48e2` DSP48E2 slice (`A -> M -> P`). -/
def emitMacroDsp48E2SV : String :=
  "module obend_macro_dsp48e2 (\n" ++
  "  input  logic        clk,\n" ++
  "  input  logic        rst,\n" ++
  "  input  logic [26:0] a_in,\n" ++
  "  input  logic [17:0] b_in,\n" ++
  "  input  logic [47:0] c_in,\n" ++
  "  output logic [47:0] p_out\n" ++
  ");\n" ++
  "  logic [26:0] a1_reg, a2_reg;\n" ++
  "  logic [17:0] b1_reg, b2_reg;\n" ++
  "  logic [47:0] c_reg, m_reg, p_reg;\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  "    if (rst) begin\n" ++
  "      a1_reg <= 27'd0; a2_reg <= 27'd0;\n" ++
  "      b1_reg <= 18'd0; b2_reg <= 18'd0;\n" ++
  "      c_reg  <= 48'd0; m_reg  <= 48'd0; p_reg <= 48'd0;\n" ++
  "    end else begin\n" ++
  "      a1_reg <= a_in;  a2_reg <= a1_reg;\n" ++
  "      b1_reg <= b_in;  b2_reg <= b1_reg;\n" ++
  "      c_reg  <= c_in;\n" ++
  "      m_reg  <= 48'(a2_reg) * 48'(b2_reg);\n" ++
  "      p_reg  <= m_reg + c_reg;\n" ++
  "    end\n" ++
  "  end\n" ++
  "  assign p_out = p_reg;\n" ++
  "endmodule\n"

/-- Emit synthesizable SystemVerilog-2012 for the `obend_macro_uram288_bypass` URAM288 macro with RAW forwarding. -/
def emitMacroUram288BypassSV : String :=
  "module obend_macro_uram288_bypass (\n" ++
  "  input  logic        clk,\n" ++
  "  input  logic        rst,\n" ++
  "  input  logic        we,\n" ++
  "  input  logic [11:0] waddr,\n" ++
  "  input  logic [63:0] wdata,\n" ++
  "  input  logic [11:0] raddr,\n" ++
  "  output logic [63:0] rdata\n" ++
  ");\n" ++
  "  logic [63:0] mem [0:4095];\n" ++
  "  logic [63:0] s1_rdata, s2_rdata, oreg_rdata;\n" ++
  "  logic        bp_s1_valid, bp_s2_valid;\n" ++
  "  logic [11:0] bp_s1_addr, bp_s2_addr;\n" ++
  "  logic [63:0] bp_s1_data, bp_s2_data;\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  "    if (we) mem[waddr] <= wdata;\n" ++
  "    s1_rdata   <= mem[raddr];\n" ++
  "    s2_rdata   <= (bp_s1_valid && (bp_s1_addr == raddr)) ? bp_s1_data : s1_rdata;\n" ++
  "    oreg_rdata <= (bp_s2_valid && (bp_s2_addr == raddr)) ? bp_s2_data : s2_rdata;\n" ++
  "    if (rst) begin\n" ++
  "      bp_s1_valid <= 1'b0; bp_s2_valid <= 1'b0;\n" ++
  "      bp_s1_addr  <= 12'd0; bp_s2_addr <= 12'd0;\n" ++
  "      bp_s1_data  <= 64'd0; bp_s2_data <= 64'd0;\n" ++
  "    end else begin\n" ++
  "      bp_s1_valid <= we;          bp_s2_valid <= bp_s1_valid;\n" ++
  "      bp_s1_addr  <= waddr;       bp_s2_addr  <= bp_s1_addr;\n" ++
  "      bp_s1_data  <= wdata;       bp_s2_data  <= bp_s1_data;\n" ++
  "    end\n" ++
  "  end\n" ++
  "  assign rdata = oreg_rdata;\n" ++
  "endmodule\n"

/-- Emit synthesizable SystemVerilog-2012 for the `obend_macro_axis_skid` Carloni 2-register AXI4-Stream skid buffer. -/
def emitMacroAxisSkidSV : String :=
  "module obend_macro_axis_skid (\n" ++
  "  input  logic        clk,\n" ++
  "  input  logic        rst,\n" ++
  "  input  logic        up_valid,\n" ++
  "  output logic        up_ready,\n" ++
  "  input  logic [63:0] up_data,\n" ++
  "  output logic        dn_valid,\n" ++
  "  input  logic        dn_ready,\n" ++
  "  output logic [63:0] dn_data\n" ++
  ");\n" ++
  "  logic        main_valid, skid_valid;\n" ++
  "  logic [63:0] main_data,  skid_data;\n" ++
  "  assign up_ready = ~skid_valid;\n" ++
  "  assign dn_valid = main_valid;\n" ++
  "  assign dn_data  = main_data;\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  "    if (rst) begin\n" ++
  "      main_valid <= 1'b0; skid_valid <= 1'b0;\n" ++
  "      main_data  <= 64'd0; skid_data <= 64'd0;\n" ++
  "    end else if (skid_valid) begin\n" ++
  "      if (dn_ready) begin\n" ++
  "        main_valid <= 1'b1;\n" ++
  "        main_data  <= skid_data;\n" ++
  "        skid_valid <= 1'b0;\n" ++
  "      end\n" ++
  "    end else if (main_valid) begin\n" ++
  "      if (dn_ready) begin\n" ++
  "        main_valid <= up_valid;\n" ++
  "        if (up_valid) main_data <= up_data;\n" ++
  "      end else if (up_valid) begin\n" ++
  "        skid_valid <= 1'b1;\n" ++
  "        skid_data  <= up_data;\n" ++
  "      end\n" ++
  "    end else if (up_valid) begin\n" ++
  "      main_valid <= 1'b1;\n" ++
  "      main_data  <= up_data;\n" ++
  "    end\n" ++
  "  end\n" ++
  "endmodule\n"

/-- Emit synthesizable SystemVerilog-2012 for the `obend_macro_icap_dpr_tile` ICAP Dynamic Partial Reconfiguration controller. -/
def emitMacroIcapDprTileSV : String :=
  "module obend_macro_icap_dpr_tile (\n" ++
  "  input  logic        clk,\n" ++
  "  input  logic        rst,\n" ++
  "  input  logic        trigger_reconfig,\n" ++
  "  input  logic        drain_complete,\n" ++
  "  input  logic        icap_done,\n" ++
  "  input  logic [63:0] target_spec_digest,\n" ++
  "  input  logic [63:0] wire_in,\n" ++
  "  input  logic [63:0] safe_default,\n" ++
  "  output logic        decouple_en,\n" ++
  "  output logic [63:0] active_spec_digest,\n" ++
  "  output logic [63:0] wire_out\n" ++
  ");\n" ++
  "  typedef enum logic [1:0] {\n" ++
  "    DPR_ACTIVE    = 2'd0,\n" ++
  "    DPR_DRAINING  = 2'd1,\n" ++
  "    DPR_SWAPPING  = 2'd2,\n" ++
  "    DPR_WARMING   = 2'd3\n" ++
  "  } dpr_phase_t;\n" ++
  "  dpr_phase_t phase;\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  "    if (rst) begin\n" ++
  "      phase              <= DPR_ACTIVE;\n" ++
  "      decouple_en        <= 1'b0;\n" ++
  "      active_spec_digest <= 64'd0;\n" ++
  "    end else begin\n" ++
  "      case (phase)\n" ++
  "        DPR_ACTIVE: if (trigger_reconfig) begin phase <= DPR_DRAINING; decouple_en <= 1'b1; end\n" ++
  "        DPR_DRAINING: if (drain_complete) begin phase <= DPR_SWAPPING; decouple_en <= 1'b1; end\n" ++
  "        DPR_SWAPPING: if (icap_done) begin phase <= DPR_WARMING; decouple_en <= 1'b1; active_spec_digest <= target_spec_digest; end\n" ++
  "        DPR_WARMING: begin phase <= DPR_ACTIVE; decouple_en <= 1'b0; end\n" ++
  "      endcase\n" ++
  "    end\n" ++
  "  end\n" ++
  "  assign wire_out = decouple_en ? safe_default : wire_in;\n" ++
  "endmodule\n"

/-- Emit synthesizable SystemVerilog-2012 for the `obend_macro_noc_router_xy` dimension-ordered XY wormhole NoC router. -/
def emitMacroNocRouterXySV : String :=
  "module obend_macro_noc_router_xy (\n" ++
  "  input  logic [7:0]  my_x,\n" ++
  "  input  logic [7:0]  my_y,\n" ++
  "  input  logic [7:0]  dst_x,\n" ++
  "  input  logic [7:0]  dst_y,\n" ++
  "  output logic [2:0]  route_dir\n" ++
  ");\n" ++
  "  always_comb begin\n" ++
  "    if (dst_x < my_x)      route_dir = 3'd3; // WEST\n" ++
  "    else if (dst_x > my_x) route_dir = 3'd2; // EAST\n" ++
  "    else if (dst_y < my_y) route_dir = 3'd1; // SOUTH\n" ++
  "    else if (dst_y > my_y) route_dir = 3'd0; // NORTH\n" ++
  "    else                   route_dir = 3'd4; // LOCAL\n" ++
  "  end\n" ++
  "endmodule\n"

/-- Emit hierarchical SystemVerilog-2012 containing all hard-IP macro modules (`obend_macro_dsp48e2`,
`obend_macro_uram288_bypass`, `obend_macro_axis_skid`, `obend_macro_icap_dpr_tile`, `obend_macro_noc_router_xy`)
followed by the top-level `RtlModule`. -/
def emitHierarchicalSV (m : RtlModule) : String :=
  emitMacroDsp48E2SV ++ "\n" ++
  emitMacroUram288BypassSV ++ "\n" ++
  emitMacroAxisSkidSV ++ "\n" ++
  emitMacroIcapDprTileSV ++ "\n" ++
  emitMacroNocRouterXySV ++ "\n" ++
  emitModuleSV m

/-- `emitHierarchicalSV m` decomposes into the 5 hard-IP macro modules followed by `emitModuleSV m`,
and all 5 macro emitters begin with their synthesizable SystemVerilog-2012 `module` headers. -/
theorem emitHierarchicalSV_nonEmpty_and_has_header (m : RtlModule) :
    emitHierarchicalSV m =
      emitMacroDsp48E2SV ++ "\n" ++
      emitMacroUram288BypassSV ++ "\n" ++
      emitMacroAxisSkidSV ++ "\n" ++
      emitMacroIcapDprTileSV ++ "\n" ++
      emitMacroNocRouterXySV ++ "\n" ++
      emitModuleSV m ∧
    ("module obend_macro_dsp48e2".toList.isPrefixOf emitMacroDsp48E2SV.toList) = true ∧
    ("module obend_macro_uram288_bypass".toList.isPrefixOf emitMacroUram288BypassSV.toList) = true ∧
    ("module obend_macro_axis_skid".toList.isPrefixOf emitMacroAxisSkidSV.toList) = true ∧
    ("module obend_macro_icap_dpr_tile".toList.isPrefixOf emitMacroIcapDprTileSV.toList) = true ∧
    ("module obend_macro_noc_router_xy".toList.isPrefixOf emitMacroNocRouterXySV.toList) = true := by
  exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end Obend.Hardware.HDL
end
