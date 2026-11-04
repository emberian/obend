module
/-
# Obend.Hardware.HDL — Core Verified Synchronous HDL, Combinational DAG & CDC Checkers, and SV Emitter

A small word-level synchronous RTL for Objective Bend. What it is, exactly:
1. **64-bit word expressions (`RtlAluOp`, `RtlExpr`)**. Every wire, register and expression is a
   `BitVec 64`; there are no bit-selects, concatenations or memories. Port widths (1..64) are an
   emission annotation (`RtlModule.inputWidths`, `OutputPort.width`): inputs are zero-extended on
   entry, outputs truncated on exit (`truncToWidth`, `evalModuleOutputsW`).
   `checkExprDAG`/`checkWireTableDAG` rule out combinational loops; `evalRtlExpr_dag_locality`
   is the theorem that makes the single-pass evaluation (`evalWireTable`) sound.
2. **Registers, resets, clock domains (`RegSpec`, `ResetKind`, `ClkDomain`)**. Resets are
   synchronous only (`syncReset initVal`) or absent (`resetFree`). `checkModuleCdc` refuses a
   register that reads another domain's register unless it is flagged `isSynchronizer` and latches
   that register directly (`cdcSafe_no_unsynchronized_crossing`, also through wires). The emission
   gate `checkRtlModuleW` additionally requires a two-flop chain (`checkCdcTwoFlop`,
   `checkCdcTwoFlop_second_stage`) and port widths in range (`checkPortWidths`).
3. **SystemVerilog-2012 emitter (`emitModuleSV`)**. One `clk`/`rst` pair for a single-domain module,
   one `clk_<d>`/`rst_<d>` pair per domain otherwise; reset-free and synchronous-reset registers in
   separate `always_ff` blocks per domain; `(* ASYNC_REG = "TRUE" *)` on synchronizers.
   `stepModuleRegs` is the cycle semantics the emitted text is meant to realise; the differential
   check against Verilator lives in `Obend.Hardware.VerilateRunner`.
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

/-- Port-name suffix of a clock domain when a module has more than one domain
(`clk_core`/`rst_core`, `clk_axi`/`rst_axi`, `clk_cfg`/`rst_cfg`). A single-domain module keeps
the plain `clk`/`rst` ports. -/
def ClkDomain.portSuffix : ClkDomain → String
  | .coreClk    => "core"
  | .axiIoClk   => "axi"
  | .cfgJtagClk => "cfg"

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

/-- Collect all register indices and wire indices directly referenced by an `RtlExpr`
(pure structural recursion on `RtlExpr` for kernel reduction). -/
def exprReadRegsAndWires : RtlExpr → List Nat × List Nat
  | .const _       => ([], [])
  | .inputPort _   => ([], [])
  | .wireRef idx   => ([], [idx])
  | .regRead idx   => ([idx], [])
  | .alu _ a b     =>
    let (ra, wa) := exprReadRegsAndWires a
    let (rb, wb) := exprReadRegsAndWires b
    (ra ++ rb, wa ++ wb)
  | .mux c t f     =>
    let (rc, wc) := exprReadRegsAndWires c
    let (rt, wt) := exprReadRegsAndWires t
    let (rf, wf) := exprReadRegsAndWires f
    (rc ++ rt ++ rf, wc ++ wt ++ wf)
  | .bitNot a      =>
    exprReadRegsAndWires a

/-- Expand `.wireRef` indices transitively through `wires` up to `fuel` hops
(pure structural recursion on `Nat` for kernel reduction). -/
def expandWiresToRegs : Nat → List WireAssign → List Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, wires, wireIdxs =>
    wireIdxs.foldl
      (fun acc idx =>
        match wires.find? (fun w => w.wireIdx == idx) with
        | none   => acc
        | some w =>
          let (rDirect, wNext) := exprReadRegsAndWires w.expr
          acc ++ rDirect ++ expandWiresToRegs fuel wires wNext)
      []

/-- Collect all register indices referenced by an `RtlExpr` (expanding `.wireRef` transitively
through `wires` bounded by `wires.length` fuel). -/
def exprReadRegs (e : RtlExpr) (wires : List WireAssign := []) : List Nat :=
  let (rDirect, wDirect) := exprReadRegsAndWires e
  match wires with
  | [] => rDirect
  | _  => rDirect ++ expandWiresToRegs wires.length wires wDirect

/-- Look up the clock domain of register `idx` in `regs`. -/
def lookupRegDomain (regs : List RegSpec) (idx : Nat) : Option ClkDomain :=
  (regs.find? (fun r => r.regIdx == idx)).map (·.domain)

/-- Check that every register `srcIdx` transitively read by `dstReg.nextExpr` through `wires` either:
1. Lives in the exact same `ClkDomain` (`srcDomain == dstReg.domain`), OR
2. `dstReg` is an explicit CDC synchronizer (`dstReg.isSynchronizer == true`) AND `dstReg.nextExpr`
   is a direct `.regRead srcIdx` (no combinational logic or intermediate wire before a CDC synchronizer!). -/
def checkRegCdcWithWires (wires : List WireAssign) (allRegs : List RegSpec) (dstReg : RegSpec) : Bool :=
  let srcRegs := exprReadRegs dstReg.nextExpr wires
  srcRegs.all fun srcIdx =>
    match lookupRegDomain allRegs srcIdx with
    | none => false
    | some srcDom =>
      if srcDom == dstReg.domain then
        true
      else
        dstReg.isSynchronizer && (dstReg.nextExpr == .regRead srcIdx)

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

/-- Verify CDC safety across all registers in a module (expanding intermediate `.wireRef`s
transitively through `wires` when present). -/
def checkModuleCdc (regs : List RegSpec) (wires : List WireAssign := []) : Bool :=
  match wires with
  | [] => regs.all (checkRegCdc regs)
  | _  => regs.all (checkRegCdcWithWires wires regs) && regs.all (checkRegCdc regs)

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

/-- Transitive wire CDC soundness theorem: if `checkRegCdcWithWires wires allRegs dstReg = true` and
`dstReg.isSynchronizer = false`, then no register transitively read through `wires` in `dstReg.nextExpr`
can come from a different clock domain! -/
theorem cdcSafe_no_unsynchronized_crossing_withWires
    (wires : List WireAssign) (allRegs : List RegSpec) (dstReg : RegSpec) (srcIdx : Nat) (srcDom : ClkDomain)
    (hCdc : checkRegCdcWithWires wires allRegs dstReg = true)
    (hNoSync : dstReg.isSynchronizer = false)
    (hMem : srcIdx ∈ exprReadRegs dstReg.nextExpr wires)
    (hDom : lookupRegDomain allRegs srcIdx = some srcDom) :
    srcDom = dstReg.domain := by
  unfold checkRegCdcWithWires at hCdc
  rw [List.all_eq_true] at hCdc
  have hSrc := hCdc srcIdx hMem
  rw [hDom] at hSrc
  by_cases hEq : srcDom == dstReg.domain
  · exact eq_of_beq hEq
  · simp [hEq, hNoSync] at hSrc

/-! ## 4. Complete Synchronous `RtlModule` & Operational Semantics -/

/-- Output port binding of an `RtlModule`. `width` (1..64, default 64) is the emitted port width:
the 64-bit value of `expr` is truncated to its low `width` bits at the port (`truncToWidth`). -/
structure OutputPort where
  name  : String
  expr  : RtlExpr
  width : Nat := 64
  deriving DecidableEq, Repr

/-- A complete synchronous hardware module in `Obend.Hardware.HDL`.

Every wire and register is a 64-bit word. Port widths are an emission-time annotation:
`inputWidths` (empty = all 64, otherwise one entry per input, each in 1..64) gives the emitted
width of each input; the module sees the input zero-extended to 64 bits, so the semantics
(`evalRtlExpr`) is unchanged for input values below `2^width`. Output widths live on
`OutputPort.width`. -/
structure RtlModule where
  name        : String
  inputNames  : List String
  wires       : List WireAssign
  regs        : List RegSpec
  outputs     : List OutputPort
  inputWidths : List Nat := []
  deriving DecidableEq, Repr

/-- Well-formedness check for an `RtlModule`:
1. The wire table is a valid topological DAG (`checkWireTableDAG`),
2. Every register's `nextExpr` is a valid DAG over all wires,
3. Every output's `expr` is a valid DAG over all wires,
4. Every register's directly read registers pass `checkModuleCdc` (direct `.regRead` sources only;
   the wire-transitive variant is part of the emission gate `checkRtlModuleW`). -/
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

/-! ## 4b. Port Widths, Two-Flop Synchronizer Chains & the Emission Gate (`checkRtlModuleW`)

`checkRtlModule` is the structural gate every compiled module satisfies by construction and the
one the compiler soundness proofs quantify over; it is not changed here. `checkRtlModuleW` adds
the two conditions the SystemVerilog emitter needs and the compiler does not guarantee:
port widths are in range, and every clock-domain crossing lands on a two-flop synchronizer chain
whose first stage feeds nothing but the second stage. The CLI refuses to emit a module that fails
`checkRtlModuleW`. -/

/-- Emitted width of input `idx` (64 when `inputWidths` is empty). -/
def inputWidth (m : RtlModule) (idx : Nat) : Nat :=
  m.inputWidths.getD idx 64

/-- A port width is 1..64. -/
def validWidth (w : Nat) : Bool :=
  0 < w && w ≤ 64

/-- Port widths are in range and `inputWidths` is either empty or one entry per input. -/
def checkPortWidths (m : RtlModule) : Bool :=
  (m.inputWidths.isEmpty || m.inputWidths.length == m.inputNames.length) &&
  m.inputWidths.all validWidth &&
  m.outputs.all (fun o => validWidth o.width)

/-- Truncate a 64-bit word to its low `w` bits (zero above). -/
def truncToWidth (w : Nat) (v : BitVec 64) : BitVec 64 :=
  v &&& (BitVec.allOnes 64 >>> (64 - w))

theorem truncToWidth_width64 (v : BitVec 64) : truncToWidth 64 v = v := by
  have h : BitVec.allOnes 64 >>> (64 - 64) = BitVec.allOnes 64 := by decide
  rw [truncToWidth, h, BitVec.and_allOnes]

/-- Combinational outputs as seen at the emitted ports: each output truncated to its width. -/
def evalModuleOutputsW
    (m : RtlModule)
    (inputs : Nat → BitVec 64)
    (regState : Nat → BitVec 64) : List (String × BitVec 64) :=
  let wireEnv := evalWireTable inputs regState m.wires
  m.outputs.map fun o => (o.name, truncToWidth o.width (evalRtlExpr inputs wireEnv regState o.expr))

/-- With all outputs 64 bits wide, the port view is the word-level view. -/
theorem evalModuleOutputsW_eq_of_all64
    (m : RtlModule) (inputs regState : Nat → BitVec 64)
    (h : m.outputs.all (fun o => o.width == 64) = true) :
    evalModuleOutputsW m inputs regState = evalModuleOutputs m inputs regState := by
  simp only [evalModuleOutputsW, evalModuleOutputs]
  rw [List.all_eq_true] at h
  apply List.map_congr_left
  intro o ho
  have hw : o.width = 64 := by simpa using h o ho
  simp [hw, truncToWidth_width64]

/-- Registers read by `r.nextExpr` (through `wires`) that live in a different clock domain. -/
def crossDomainSources (regs : List RegSpec) (wires : List WireAssign) (r : RegSpec) : List Nat :=
  (exprReadRegs r.nextExpr wires).filter fun src =>
    match lookupRegDomain regs src with
    | some d => d != r.domain
    | none   => true

/-- A synchronizer `s1` with a cross-domain source must be the first stage of a two-flop chain:
some other synchronizer `s2` in `s1`'s domain latches `.regRead s1.regIdx` directly, and nothing
else (no non-synchronizer register, no wire, no output) reads `s1`. Synchronizers without a
cross-domain source are unconstrained. -/
def checkSyncChain (regs : List RegSpec) (wires : List WireAssign) (outputs : List OutputPort)
    (s1 : RegSpec) : Bool :=
  (crossDomainSources regs wires s1).isEmpty ||
  (regs.any (fun s2 =>
      s2.isSynchronizer && s2.domain == s1.domain && s2.regIdx != s1.regIdx &&
      s2.nextExpr == .regRead s1.regIdx) &&
   regs.all (fun r => r.isSynchronizer || !(exprReadRegs r.nextExpr wires).contains s1.regIdx) &&
   wires.all (fun w => !(exprReadRegsAndWires w.expr).1.contains s1.regIdx) &&
   outputs.all (fun o => !(exprReadRegs o.expr wires).contains s1.regIdx))

/-- Every synchronizer register of `m` heads a well-formed two-flop chain. -/
def checkCdcTwoFlop (m : RtlModule) : Bool :=
  m.regs.all fun r => !r.isSynchronizer || checkSyncChain m.regs m.wires m.outputs r

/-- The emission gate: `checkRtlModule`, CDC through wires as well as direct reads, port widths in
range, two-flop synchronizer chains. -/
def checkRtlModuleW (m : RtlModule) : Bool :=
  checkRtlModule m && checkModuleCdc m.regs m.wires && checkPortWidths m && checkCdcTwoFlop m

/-- If `checkCdcTwoFlop m` holds and `s1` is a synchronizer with a cross-domain source, a second
synchronizer stage `s2` in the same domain latches `s1` directly. -/
theorem checkCdcTwoFlop_second_stage (m : RtlModule) (s1 : RegSpec)
    (hOk : checkCdcTwoFlop m = true) (hMem : s1 ∈ m.regs) (hSync : s1.isSynchronizer = true)
    (hCross : (crossDomainSources m.regs m.wires s1).isEmpty = false) :
    ∃ s2 ∈ m.regs, s2.isSynchronizer = true ∧ s2.domain = s1.domain ∧
      s2.nextExpr = .regRead s1.regIdx := by
  unfold checkCdcTwoFlop at hOk
  rw [List.all_eq_true] at hOk
  have h := hOk s1 hMem
  rw [hSync] at h
  simp only [Bool.not_true, Bool.false_or] at h
  unfold checkSyncChain at h
  rw [hCross] at h
  simp only [Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hAny, _⟩, _⟩, _⟩ := h
  rw [List.any_eq_true] at hAny
  obtain ⟨s2, hs2, hp⟩ := hAny
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  exact ⟨s2, hs2, hp.1.1.1, hp.1.1.2, hp.2⟩

/-- Clock domains of `m`, in order of first appearance among its registers. -/
def moduleDomains (m : RtlModule) : List ClkDomain :=
  m.regs.foldl (fun acc r => if acc.contains r.domain then acc else acc ++ [r.domain]) []

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

/-- The SystemVerilog expression standing for input `idx` inside the module body: the port name
when it is 64 bits wide, otherwise the port zero-extended to 64 bits (`64'(name)`). -/
def inputExprsSV (m : RtlModule) : List String :=
  (List.range m.inputNames.length).map fun i =>
    let n := m.inputNames.getD i s!"in_{i}"
    if inputWidth m i == 64 then n else s!"64'({n})"

/-- The `always_ff` blocks of one clock domain: reset-free datapath registers in one block and
synchronous-reset control registers in another, clocked by `clkName` and reset by `rstName`. -/
def emitDomainBlocksSV (inExprs regNames : List String) (regsD : List RegSpec)
    (clkName rstName : String) : String :=
  let resetFreeRegs := regsD.filter fun r =>
    match r.resetKind with | .resetFree => true | .syncReset _ => false
  let syncResetRegs := regsD.filter fun r =>
    match r.resetKind with | .resetFree => false | .syncReset _ => true
  let rfBlock :=
    if resetFreeRegs.isEmpty then ""
    else
      let assigns := resetFreeRegs.map fun r =>
        s!"    {r.name} <= {emitExprSV inExprs regNames r.nextExpr};"
      s!"  // Reset-free datapath registers\n  always_ff @(posedge {clkName}) begin\n" ++
        String.intercalate "\n" assigns ++ "\n  end\n"
  let srBlock :=
    if syncResetRegs.isEmpty then ""
    else
      let rstAssigns := syncResetRegs.map fun r =>
        let initV := match r.resetKind with | .syncReset v => v.toNat | .resetFree => 0
        s!"      {r.name} <= 64'd{initV};"
      let stepAssigns := syncResetRegs.map fun r =>
        s!"      {r.name} <= {emitExprSV inExprs regNames r.nextExpr};"
      s!"  // Synchronous-reset control registers\n  always_ff @(posedge {clkName}) begin\n    if ({rstName}) begin\n" ++
        String.intercalate "\n" rstAssigns ++ "\n    end else begin\n" ++
        String.intercalate "\n" stepAssigns ++ "\n    end\n  end\n"
  rfBlock ++ srBlock

/-- Emit a complete, synthesizable SystemVerilog-2012 module directly from an `RtlModule` AST.

* One clock domain (or no registers): ports `clk`, `rst`; two `always_ff @(posedge clk)` blocks,
  reset-free datapath registers apart from synchronous-reset control registers.
* Several clock domains: one `clk_<d>`/`rst_<d>` pair per domain (`ClkDomain.portSuffix`), each
  domain's registers in their own blocks; each `rst_<d>` is a synchronous reset that the
  surrounding design must already have synchronized into domain `d`.
* Synchronizer registers (`isSynchronizer`) are declared with `(* ASYNC_REG = "TRUE" *)`.
* Input ports narrower than 64 bits are zero-extended inside the module; output ports narrower
  than 64 bits are the low bits of an internal 64-bit `o_<name>`.

Callers should check `checkRtlModuleW` first; the emitter itself does not refuse. -/
def emitModuleSV (m : RtlModule) : String :=
  let regNames := m.regs.map (·.name)
  let inExprs := inputExprsSV m
  let domains := moduleDomains m
  let multi := decide (domains.length > 1)
  let clkName (d : ClkDomain) : String := if multi then s!"clk_{d.portSuffix}" else "clk"
  let rstName (d : ClkDomain) : String := if multi then s!"rst_{d.portSuffix}" else "rst"
  let clkPorts :=
    if multi then
      domains.flatMap fun d =>
        [s!"  input  logic        {clkName d}", s!"  input  logic        {rstName d}"]
    else ["  input  logic        clk", "  input  logic        rst"]
  let inPorts := (List.range m.inputNames.length).map fun i =>
    let n := m.inputNames.getD i s!"in_{i}"
    let w := inputWidth m i
    if w == 64 then s!"  input  logic [63:0] {n}" else s!"  input  logic [{w - 1}:0] {n}"
  let outPorts := m.outputs.map fun o =>
    if o.width == 64 then s!"  output logic [63:0] {o.name}"
    else s!"  output logic [{o.width - 1}:0] {o.name}"
  let allPorts := clkPorts ++ inPorts ++ outPorts
  let portHeader := String.intercalate ",\n" allPorts
  let wireDecls := m.wires.map fun w =>
    s!"  logic [63:0] w_{w.wireIdx}; // {w.name}"
  let regDecls := m.regs.map fun r =>
    if r.isSynchronizer then s!"  (* ASYNC_REG = \"TRUE\" *) logic [63:0] {r.name};"
    else s!"  logic [63:0] {r.name};"
  let narrowOuts := m.outputs.filter fun o => o.width != 64
  let narrowDecls := narrowOuts.map fun o => s!"  logic [63:0] o_{o.name};"
  let combWires := m.wires.map fun w =>
    s!"    w_{w.wireIdx} = {emitExprSV inExprs regNames w.expr};"
  let combOuts := m.outputs.map fun o =>
    if o.width == 64 then s!"    {o.name} = {emitExprSV inExprs regNames o.expr};"
    else s!"    o_{o.name} = {emitExprSV inExprs regNames o.expr};"
  let narrowAssigns := narrowOuts.map fun o =>
    s!"  assign {o.name} = o_{o.name}[{o.width - 1}:0];"
  let ffBlocks := String.join (domains.map fun d =>
    emitDomainBlocksSV inExprs regNames (m.regs.filter (·.domain == d)) (clkName d) (rstName d))
  s!"module {m.name} (\n{portHeader}\n);\n" ++
  (if wireDecls.isEmpty then "" else String.intercalate "\n" wireDecls ++ "\n") ++
  (if regDecls.isEmpty then "" else String.intercalate "\n" regDecls ++ "\n") ++
  (if narrowDecls.isEmpty then "" else String.intercalate "\n" narrowDecls ++ "\n") ++
  "  always_comb begin\n" ++
  String.intercalate "\n" (combWires ++ combOuts) ++
  "\n  end\n" ++
  (if narrowAssigns.isEmpty then "" else String.intercalate "\n" narrowAssigns ++ "\n") ++
  ffBlocks ++
  "endmodule\n"

/-- Emit synthesizable SystemVerilog-2012 for the 4-stage `obend_macro_dsp48e2` DSP48E2 slice
(`A -> A1 -> A2 -> M -> P` and `C -> C1 -> C2 -> C3 -> P`, zero C-port skew). -/
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
  "  logic [47:0] c1_reg, c2_reg, c3_reg, m_reg, p_reg;\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  "    if (rst) begin\n" ++
  "      a1_reg <= 27'd0; a2_reg <= 27'd0;\n" ++
  "      b1_reg <= 18'd0; b2_reg <= 18'd0;\n" ++
  "      c1_reg <= 48'd0; c2_reg <= 48'd0; c3_reg <= 48'd0;\n" ++
  "      m_reg  <= 48'd0; p_reg  <= 48'd0;\n" ++
  "    end else begin\n" ++
  "      a1_reg <= a_in;  a2_reg <= a1_reg;\n" ++
  "      b1_reg <= b_in;  b2_reg <= b1_reg;\n" ++
  "      c1_reg <= c_in;  c2_reg <= c1_reg; c3_reg <= c2_reg;\n" ++
  "      m_reg  <= 48'(a2_reg) * 48'(b2_reg);\n" ++
  "      p_reg  <= m_reg + c3_reg;\n" ++
  "    end\n" ++
  "  end\n" ++
  "  assign p_out = p_reg;\n" ++
  "endmodule\n"

/-- Emit synthesizable SystemVerilog-2012 for the `obend_macro_uram288_bypass` URAM288 macro with
pipelined `raddr_s1`/`raddr_s2` RAW forwarding and stage-3 registered bypass output (`oreg_rdata`). -/
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
  "  logic [11:0] raddr_s1, raddr_s2;\n" ++
  "  logic        bp_s1_valid, bp_s2_valid;\n" ++
  "  logic [11:0] bp_s1_addr, bp_s2_addr;\n" ++
  "  logic [63:0] bp_s1_data, bp_s2_data;\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  "    if (we) mem[waddr] <= wdata;\n" ++
  "    s1_rdata   <= mem[raddr];\n" ++
  "    s2_rdata   <= (bp_s1_valid && (bp_s1_addr == raddr_s1)) ? bp_s1_data : s1_rdata;\n" ++
  "    oreg_rdata <= (bp_s2_valid && (bp_s2_addr == raddr_s2)) ? bp_s2_data : s2_rdata;\n" ++
  "    if (rst) begin\n" ++
  "      raddr_s1    <= 12'd0; raddr_s2    <= 12'd0;\n" ++
  "      bp_s1_valid <= 1'b0;  bp_s2_valid <= 1'b0;\n" ++
  "      bp_s1_addr  <= 12'd0; bp_s2_addr  <= 12'd0;\n" ++
  "      bp_s1_data  <= 64'd0; bp_s2_data  <= 64'd0;\n" ++
  "    end else begin\n" ++
  "      raddr_s1    <= raddr;       raddr_s2    <= raddr_s1;\n" ++
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

/-- Emit synthesizable SystemVerilog-2012 for the `obend_macro_icap_dpr_tile` ICAP Dynamic Partial
Reconfiguration controller with internal rolling FNV-1a/CRC64 payload digest verification. -/
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
  "  dpr_phase_t  phase;\n" ++
  "  logic [63:0] rolling_crc_q;\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  "    if (rst) begin\n" ++
  "      phase              <= DPR_ACTIVE;\n" ++
  "      decouple_en        <= 1'b0;\n" ++
  "      active_spec_digest <= 64'd0;\n" ++
  "      rolling_crc_q      <= 64'hCBF2_9CE4_8422_2325;\n" ++
  "    end else begin\n" ++
  "      case (phase)\n" ++
  "        DPR_ACTIVE: if (trigger_reconfig) begin\n" ++
  "          phase         <= DPR_DRAINING;\n" ++
  "          decouple_en   <= 1'b1;\n" ++
  "          rolling_crc_q <= 64'hCBF2_9CE4_8422_2325;\n" ++
  "        end\n" ++
  "        DPR_DRAINING: if (drain_complete) begin\n" ++
  "          phase       <= DPR_SWAPPING;\n" ++
  "          decouple_en <= 1'b1;\n" ++
  "        end\n" ++
  "        DPR_SWAPPING: begin\n" ++
  "          rolling_crc_q <= (rolling_crc_q ^ wire_in) * 64'h0000_0100_0000_01B3;\n" ++
  "          if (icap_done) begin\n" ++
  "            if (rolling_crc_q == target_spec_digest) begin\n" ++
  "              phase              <= DPR_WARMING;\n" ++
  "              decouple_en        <= 1'b1;\n" ++
  "              active_spec_digest <= rolling_crc_q;\n" ++
  "            end else begin\n" ++
  "              decouple_en <= 1'b1;\n" ++
  "            end\n" ++
  "          end\n" ++
  "        end\n" ++
  "        DPR_WARMING: begin phase <= DPR_ACTIVE; decouple_en <= 1'b0; end\n" ++
  "      endcase\n" ++
  "    end\n" ++
  "  end\n" ++
  "  assign wire_out = decouple_en ? safe_default : wire_in;\n" ++
  "endmodule\n"

/-- Emit synthesizable SystemVerilog-2012 for the `obend_macro_noc_router_xy` dimension-ordered XY
wormhole NoC router with downstream credit/ready backpressure propagation (`in_ready = credit_avail`). -/
def emitMacroNocRouterXySV : String :=
  "module obend_macro_noc_router_xy (\n" ++
  "  input  logic [7:0]  my_x,\n" ++
  "  input  logic [7:0]  my_y,\n" ++
  "  input  logic [7:0]  dst_x,\n" ++
  "  input  logic [7:0]  dst_y,\n" ++
  "  input  logic        in_valid,\n" ++
  "  input  logic        credit_avail,\n" ++
  "  output logic        in_ready,\n" ++
  "  output logic [2:0]  route_dir\n" ++
  ");\n" ++
  "  assign in_ready = credit_avail;\n" ++
  "  always_comb begin\n" ++
  "    if (!in_valid || !credit_avail) route_dir = 3'd4; // HOLD/LOCAL\n" ++
  "    else if (dst_x < my_x)          route_dir = 3'd3; // WEST\n" ++
  "    else if (dst_x > my_x)          route_dir = 3'd2; // EAST\n" ++
  "    else if (dst_y < my_y)          route_dir = 3'd1; // SOUTH\n" ++
  "    else if (dst_y > my_y)          route_dir = 3'd0; // NORTH\n" ++
  "    else                            route_dir = 3'd4; // LOCAL\n" ++
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

/-- `emitHierarchicalSV m` decomposes into the 5 non-empty hard-IP SystemVerilog-2012 macro modules
followed by `emitModuleSV m`. -/
theorem emitHierarchicalSV_nonEmpty_and_has_header (m : RtlModule) :
    emitHierarchicalSV m =
      emitMacroDsp48E2SV ++ "\n" ++
      emitMacroUram288BypassSV ++ "\n" ++
      emitMacroAxisSkidSV ++ "\n" ++
      emitMacroIcapDprTileSV ++ "\n" ++
      emitMacroNocRouterXySV ++ "\n" ++
      emitModuleSV m ∧
    (emitMacroDsp48E2SV != "") = true ∧
    (emitMacroUram288BypassSV != "") = true ∧
    (emitMacroAxisSkidSV != "") = true ∧
    (emitMacroIcapDprTileSV != "") = true ∧
    (emitMacroNocRouterXySV != "") = true ∧
    (emitMacroDsp48E2SV.utf8ByteSize > 100) = true := by
  exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

end Obend.Hardware.HDL
end
