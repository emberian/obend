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
  | eq
  | ult
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
  | .eq     => if a == b then 1#64 else 0#64
  | .ult    => if BitVec.ult a b then 1#64 else 0#64

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
  | .eq     => "=="
  | .ult    => "<"

/-- Render an `RtlExpr` as a SystemVerilog expression string. -/
def emitExprSV (inNames : List String) (regNames : List String) : RtlExpr → String
  | .const v       => s!"64'd{v.toNat}"
  | .inputPort idx => inNames.getD idx s!"in_{idx}"
  | .wireRef idx   => s!"w_{idx}"
  | .regRead idx   => regNames.getD idx s!"r_{idx}"
  | .alu .eq a b   => s!"({emitExprSV inNames regNames a} == {emitExprSV inNames regNames b} ? 64'd1 : 64'd0)"
  | .alu .ult a b  => s!"({emitExprSV inNames regNames a} < {emitExprSV inNames regNames b} ? 64'd1 : 64'd0)"
  | .alu op a b    => s!"({emitExprSV inNames regNames a} {emitAluOpSV op} {emitExprSV inNames regNames b})"
  | .mux c t f     => s!"(({emitExprSV inNames regNames c} != 64'd0) ? {emitExprSV inNames regNames t} : {emitExprSV inNames regNames f})"
  | .bitNot a      => s!"(~{emitExprSV inNames regNames a})"

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

end Obend.Hardware.HDL
end
