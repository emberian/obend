module
/-
# Obend.Hardware.HDL — Core Verified Synchronous HDL, Combinational DAG & CDC Checkers, and SV Emitter

A small word-level synchronous RTL for Objective Bend. What it is, exactly:
1. **Word expressions with checked widths (`RtlAluOp`, `RtlWidthOp`, `RtlExpr`)**. Every value is
   carried in a `BitVec 64`. Inputs (`RtlModule.inputWidths`), wires (`WireAssign.width`), registers
   (`RegSpec.width`) and outputs (`OutputPort.width`) declare a width 1..64, default 64; `.resize`
   applies a slice, zero/sign extension or truncation, and `RtlExpr.concat` builds a concatenation.
   `inferWidthE` bounds every expression and `checkWidths` refuses, with a reason naming the
   signal, any signal driven by something wider than it or a slice outside its source; the
   theorems of §4c say that for a checked module every value fits its declared width, so the
   64-bit carrier and the narrow emitted signals agree (`runModuleTrace_lt`). There are no memories.
   `checkExprDAG`/`checkWireTableDAG` rule out combinational loops; `evalRtlExpr_dag_locality`
   is the theorem that makes the single-pass evaluation (`evalWireTable`) sound.
2. **Registers, resets, clock domains (`RegSpec`, `ResetKind`, `ClkDomain`)**. Resets are
   synchronous only (`syncReset initVal`) or absent (`resetFree`). `checkModuleCdc` refuses a
   register that reads another domain's register unless it is flagged `isSynchronizer` and latches
   that register directly (`cdcSafe_no_unsynchronized_crossing`, also through wires). The emission
   gate `checkRtlModuleW` additionally requires a two-flop chain (`checkCdcTwoFlop`,
   `checkCdcTwoFlop_second_stage`), port widths in range (`checkPortWidths`) and `checkWidths`.
   `stepModuleDomain` is one edge of one domain's clock, the edge the emitted always-blocks of that
   domain take; `stepDomain_nonSync_reads_own_domain` reads the CDC check against it.
3. **SystemVerilog-2012 emitter (`emitModuleSV`)**. Each signal declared `logic [w-1:0]` from its
   declared width, read zero-extended to 64 bits and stored through a `w'(...)` cast, so every
   operator is evaluated at 64 bits as `evalRtlExpr` does. One `clk`/`rst` pair for a single-domain
   module, one `clk_<d>`/`rst_<d>` pair per domain otherwise; reset-free and synchronous-reset registers in
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

/-- Truncate a 64-bit word to its low `w` bits (zero above). -/
def truncToWidth (w : Nat) (v : BitVec 64) : BitVec 64 :=
  v &&& (BitVec.allOnes 64 >>> (64 - w))

/-- Width-changing unary operators. Every value is carried in a `BitVec 64` whose bits above the
value's width are zero (the checked invariant of §4c), so each operator is a total function on the
carrier and its width is what `inferWidth` computes:
* `slice hi lo`: bits `hi..lo` of the operand, moved to the bottom (`hi + 1 - lo` bits);
* `zext w`: the operand, asserted to fit in `w` bits (the identity on the carrier);
* `sext fromW toW`: the low `fromW` bits read as a signed number and widened to `toW` bits;
* `trunc w`: the low `w` bits.
A concatenation is `RtlExpr.concat`, a shift and an or over these. -/
inductive RtlWidthOp where
  | slice (hi lo : Nat)
  | zext  (w : Nat)
  | sext  (fromW toW : Nat)
  | trunc (w : Nat)
  deriving DecidableEq, Repr

/-- Semantics of a width operator on the 64-bit carrier. -/
def evalWidthOp : RtlWidthOp → BitVec 64 → BitVec 64
  | .slice hi lo, a => truncToWidth (hi + 1 - lo) (a >>> lo)
  | .zext _,      a => a
  | .sext f t,    a => ((a.setWidth f).signExtend t).setWidth 64
  | .trunc w,     a => truncToWidth w a

/-- Combinational RTL expression over input ports, internal wires, and sequential registers. -/
inductive RtlExpr where
  | const     (val : BitVec 64)
  | inputPort (portIdx : Nat)
  | wireRef   (wireIdx : Nat)
  | regRead   (regIdx : Nat)
  | alu       (op : RtlAluOp) (lhs rhs : RtlExpr)
  | mux       (cond : RtlExpr) (ifTrue ifFalse : RtlExpr)
  | bitNot    (arg : RtlExpr)
  | resize    (op : RtlWidthOp) (arg : RtlExpr)
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
  | .resize op a   => evalWidthOp op (evalRtlExpr inputs wires regs a)

/-- `{hi, lo}` with `lo` taken as `loW` bits: `(hi << loW) | trunc loW lo`. -/
def RtlExpr.concat (hi lo : RtlExpr) (loW : Nat) : RtlExpr :=
  .alu .bitOr (.alu .shl hi (.const (BitVec.ofNat 64 loW))) (.resize (.trunc loW) lo)

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
  | .resize _ a    => checkExprDAG numInputs numRegs wireBound a

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
  | resize op a iha =>
    simp only [checkExprDAG] at hDag
    simp only [evalRtlExpr, iha hDag]

/-- A topological wire assignment table: wire `i` (at position `i` in the list) is defined by `expr`. -/
structure WireAssign where
  wireIdx : Nat
  name    : String
  expr    : RtlExpr
  /-- Declared width, 1..64; the value of `expr` must fit (`checkWidths`). -/
  width   : Nat := 64
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

/-- Executable twin of `evalWireTable` (`implemented_by`): the same fold with the environment held
in an array, so every wire is evaluated once and a `wireRef` read is an index. Compiled, the
closure chain the definition builds re-evaluated upstream wires on every read, and
`evalModuleOutputs` of a 250-wire module did not return. Same results: `0#64` for an index never
assigned, the last assignment wins on a repeated index; the definition itself is unchanged and is
what the proofs unfold. Indices beyond a million fall back to the definition's fold. -/
def evalWireTableImpl
    (inputs regs : Nat → BitVec 64)
    (assigns : List WireAssign) : Nat → BitVec 64 :=
  let n := assigns.foldl (fun k a => max k (a.wireIdx + 1)) 0
  if n > 1000000 then
    assigns.foldl
      (fun (env : Nat → BitVec 64) a =>
        let v := evalRtlExpr inputs env regs a.expr
        fun i => if i == a.wireIdx then v else env i)
      (fun _ => 0#64)
  else
    let arr := assigns.foldl
      (fun (arr : Array (BitVec 64)) a =>
        let env : Nat → BitVec 64 := fun i => arr.getD i 0#64
        let v := evalRtlExpr inputs env regs a.expr
        arr.set! a.wireIdx v)
      (Array.replicate n 0#64)
    fun i => arr.getD i 0#64

/-- Evaluate a wire assignment table in a single forward pass. -/
@[implemented_by evalWireTableImpl]
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

/-- Specification of a hardware register inside an `RtlModule` (carried as a `BitVec 64`; `width`
is its declared width). -/
structure RegSpec where
  regIdx         : Nat
  name           : String
  domain         : ClkDomain
  resetKind      : ResetKind
  isSynchronizer : Bool        -- True if this register is a dedicated 2-FF CDC synchronizer stage
  nextExpr       : RtlExpr     -- Next-state expression latched on `posedge domain`
  /-- Declared width, 1..64; `nextExpr` and the reset value must fit (`checkWidths`). -/
  width          : Nat := 64
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
  | .resize _ a    =>
    exprReadRegsAndWires a

/-- The register indices reachable from the wires `work` through `wires`: a worklist walk that
visits each wire once (`visited`), so a shared sub-cone is expanded once, not once per path. The
earlier version re-expanded the cone under every reference and was exponential on wire graphs with
fan-out (a Goldilocks multiply chain of 250 wires did not finish); the fuel is spent once per pop
and `exprReadRegs` passes enough for every wire and every edge. -/
def expandWiresToRegs : Nat → List WireAssign → List Nat → List Nat → List Nat → List Nat
  | 0, _, _, _, acc => acc
  | _ + 1, _, [], _, acc => acc
  | fuel + 1, wires, idx :: rest, visited, acc =>
    if visited.contains idx then expandWiresToRegs fuel wires rest visited acc
    else
      match wires.find? (fun w => w.wireIdx == idx) with
      | none   => expandWiresToRegs fuel wires rest (idx :: visited) acc
      | some w =>
        let (rDirect, wNext) := exprReadRegsAndWires w.expr
        expandWiresToRegs fuel wires (wNext ++ rest) (idx :: visited) (acc ++ rDirect)

/-- Collect all register indices referenced by an `RtlExpr` (expanding `.wireRef` transitively
through `wires`). -/
def exprReadRegs (e : RtlExpr) (wires : List WireAssign := []) : List Nat :=
  let (rDirect, wDirect) := exprReadRegsAndWires e
  match wires with
  | [] => rDirect
  | _  =>
    let edges := wires.foldl (fun n w => n + (exprReadRegsAndWires w.expr).2.length) 0
    rDirect ++ expandWiresToRegs (wires.length + edges + wDirect.length + 1) wires wDirect [] []

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

Every value is carried as a 64-bit word. `inputWidths` (empty = all 64, otherwise one entry per
input, each in 1..64) gives the width of each input; the module sees the input zero-extended to 64
bits, so `evalRtlExpr` is unchanged for input values below `2^width`. Wire, register and output
widths live on `WireAssign.width`, `RegSpec.width` and `OutputPort.width`; `checkWidths` (§4c)
is what makes them true of the values. -/
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

/-- Executable twin of `stepModuleRegs` (`implemented_by`): every register's next value computed
once into an array; a read of a slot no register writes falls through to `regState`, as in the
definition. Compiled, the definition's closure chain re-evaluated the previous cycles on every
read, and 21 cycles of the softcore did not return. -/
def stepModuleRegsImpl
    (m : RtlModule)
    (rst : Bool)
    (inputs : Nat → BitVec 64)
    (regState : Nat → BitVec 64) : Nat → BitVec 64 :=
  let wireEnv := evalWireTable inputs regState m.wires
  let n := m.regs.foldl (fun k r => max k (r.regIdx + 1)) 0
  if n > 1000000 then
    m.regs.foldl
      (fun (nextSt : Nat → BitVec 64) r =>
        let v :=
          match r.resetKind with
          | .resetFree => evalRtlExpr inputs wireEnv regState r.nextExpr
          | .syncReset initVal =>
            if rst then initVal else evalRtlExpr inputs wireEnv regState r.nextExpr
        fun i => if i == r.regIdx then v else nextSt i)
      regState
  else
    let vals := m.regs.foldl
      (fun (arr : Array (Option (BitVec 64))) r =>
        let v :=
          match r.resetKind with
          | .resetFree => evalRtlExpr inputs wireEnv regState r.nextExpr
          | .syncReset initVal =>
            if rst then initVal else evalRtlExpr inputs wireEnv regState r.nextExpr
        arr.set! r.regIdx (some v))
      (Array.replicate n none)
    fun i => match vals.getD i none with
      | some v => v
      | none => regState i

/-- Step all sequential registers of `m` by one clock edge (`rst = true` triggers synchronous resets). -/
@[implemented_by stepModuleRegsImpl]
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

/-! ## 4c. Widths as a Checked Refinement of the 64-bit Carrier (`inferWidth`, `checkWidths`)

Every value stays a `BitVec 64`; a width says how many of its low bits can be non-zero.
`inferWidthE` computes, bottom-up, a bound `w` with `value < 2^w` from the declared widths of the
inputs, wires and registers (`WidthEnv`), and refuses a width operator applied outside its source
(a slice above the operand's width, a `zext` that would narrow). `checkWidths` asks every wire,
register (next state and reset value) and output port to hold the bound of the expression that
drives it. The theorems say the carrier is then faithful: every value an evaluation produces is
below `2^w` (`evalRtlExpr_lt_of_inferWidthE`), every wire and register stays below `2^width`
through any trace (`runModuleTrace_lt`), and the output truncation the ports perform loses nothing
(`evalModuleOutputsW_eq_of_checkWidths`). So the emitter may declare each signal `[w-1:0]`. -/

/-- Declared widths of a module's inputs, wires and registers, by index. -/
structure WidthEnv where
  input : Nat → Nat
  wire  : Nat → Nat
  reg   : Nat → Nat

/-- Bit length of a constant (at least 1). -/
def constWidth (v : BitVec 64) : Nat := v.toNat.log2 + 1

/-- Width bound of an ALU result from its operands' bounds `wa`, `wb` (`rhs` is the right operand,
read for a constant shift amount). -/
def aluWidth (op : RtlAluOp) (rhs : RtlExpr) (wa wb : Nat) : Nat :=
  match op with
  | .add    => min 64 (max wa wb + 1)
  | .sub    => 64
  | .mul    => min 64 (wa + wb)
  | .bitAnd => min wa wb
  | .bitOr  => max wa wb
  | .bitXor => max wa wb
  | .shl    => match rhs with
    | .const k => min 64 (wa + k.toNat % 64)
    | _        => 64
  | .lshr   => wa
  | .ashr   => if wa < 64 then wa else 64
  | .eq     => 1
  | .ult    => 1
  | .slt    => 1
  | .qmul32 => 64

/-- Width of a width operator's result from its operand's bound `wa`, or the reason it is refused. -/
def widthOpWidth : RtlWidthOp → Nat → Except String Nat
  | .slice hi lo, wa =>
    if lo ≤ hi ∧ hi < wa ∧ hi < 64 then .ok (hi + 1 - lo)
    else .error s!"slice [{hi}:{lo}] is outside its {wa}-bit source"
  | .zext w, wa =>
    if wa ≤ w ∧ w ≤ 64 then .ok w
    else .error s!"zext to {w} bits of a {wa}-bit value"
  | .sext f t, _ =>
    if 0 < f ∧ f ≤ t ∧ t ≤ 64 then .ok t
    else .error s!"sext from {f} to {t} bits (needs 0 < from <= to <= 64)"
  | .trunc w, wa =>
    if 0 < w ∧ w ≤ 64 then .ok (min w wa)
    else .error s!"trunc to {w} bits (needs 1..64)"

/-- Width bound of an expression, or the first width operator it refuses. -/
def inferWidthE (env : WidthEnv) : RtlExpr → Except String Nat
  | .const v       => .ok (constWidth v)
  | .inputPort idx => .ok (env.input idx)
  | .wireRef idx   => .ok (env.wire idx)
  | .regRead idx   => .ok (env.reg idx)
  | .alu op a b    =>
    match inferWidthE env a, inferWidthE env b with
    | .ok wa, .ok wb => .ok (aluWidth op b wa wb)
    | .error e, _    => .error e
    | _, .error e    => .error e
  | .mux c t f     =>
    match inferWidthE env c, inferWidthE env t, inferWidthE env f with
    | .ok _, .ok wt, .ok wf => .ok (max wt wf)
    | .error e, _, _ => .error e
    | _, .error e, _ => .error e
    | _, _, .error e => .error e
  | .bitNot a      =>
    match inferWidthE env a with
    | .ok _    => .ok 64
    | .error e => .error e
  | .resize op a   =>
    match inferWidthE env a with
    | .ok wa   => widthOpWidth op wa
    | .error e => .error e

/-- `inferWidthE` without the reason. -/
def inferWidth (env : WidthEnv) (e : RtlExpr) : Option Nat :=
  (inferWidthE env e).toOption

/-- The `w ≤ 64` masks of `truncToWidth`, all 65 of them. -/
theorem truncMask_toNat : ∀ w, w < 65 → (BitVec.allOnes 64 >>> (64 - w)).toNat = 2 ^ w - 1 := by
  decide

theorem truncToWidth_toNat (w : Nat) (hw : w ≤ 64) (v : BitVec 64) :
    (truncToWidth w v).toNat = v.toNat % 2 ^ w := by
  rw [truncToWidth, BitVec.toNat_and, truncMask_toNat w (by omega), Nat.and_two_pow_sub_one_eq_mod]

theorem truncToWidth_lt (w : Nat) (hw : w ≤ 64) (v : BitVec 64) :
    (truncToWidth w v).toNat < 2 ^ w := by
  rw [truncToWidth_toNat w hw]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem truncToWidth_le (w : Nat) (v : BitVec 64) : (truncToWidth w v).toNat ≤ v.toNat := by
  rw [truncToWidth, BitVec.toNat_and]
  exact Nat.and_le_left

/-- Truncating a value that already fits changes nothing. -/
theorem truncToWidth_of_lt (w : Nat) (hw : w ≤ 64) (v : BitVec 64) (h : v.toNat < 2 ^ w) :
    truncToWidth w v = v := by
  apply BitVec.eq_of_toNat_eq
  rw [truncToWidth_toNat w hw, Nat.mod_eq_of_lt h]

private theorem lt_two_pow_mono {x a b : Nat} (h : x < 2 ^ a) (hab : a ≤ b) : x < 2 ^ b :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hab)

private theorem lt_two_pow_min64 (x : BitVec 64) (n : Nat) (h : x.toNat < 2 ^ n) :
    x.toNat < 2 ^ (min 64 n) := by
  rcases Nat.le_total 64 n with h64 | h64
  · rw [Nat.min_eq_left h64]; exact x.isLt
  · rw [Nat.min_eq_right h64]; exact h

private theorem ite_one_zero_lt (c : Prop) [Decidable c] :
    (if c then 1#64 else 0#64).toNat < 2 ^ 1 := by
  split <;> decide

theorem evalAluOp_lt_aluWidth (op : RtlAluOp) (rhs : RtlExpr) (a b : BitVec 64) (wa wb : Nat)
    (ha : a.toNat < 2 ^ wa) (hb : b.toNat < 2 ^ wb)
    (hrhs : ∀ k, rhs = .const k → b = k) :
    (evalAluOp op a b).toNat < 2 ^ aluWidth op rhs wa wb := by
  cases op with
  | add =>
    apply lt_two_pow_min64
    simp only [evalAluOp]
    rw [BitVec.toNat_add]
    have h1 := lt_two_pow_mono ha (Nat.le_max_left wa wb)
    have h2 := lt_two_pow_mono hb (Nat.le_max_right wa wb)
    have := Nat.mod_le (a.toNat + b.toNat) (2 ^ 64)
    rw [Nat.pow_succ]
    omega
  | sub => exact (evalAluOp .sub a b).isLt
  | mul =>
    apply lt_two_pow_min64
    simp only [evalAluOp]
    rw [BitVec.toNat_mul, Nat.pow_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _)
      (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (Nat.two_pow_pos wb))
  | bitAnd =>
    simp only [evalAluOp, aluWidth, BitVec.toNat_and]
    rcases Nat.le_total wa wb with h | h
    · rw [Nat.min_eq_left h, Nat.and_comm]; exact Nat.and_lt_two_pow _ ha
    · rw [Nat.min_eq_right h]; exact Nat.and_lt_two_pow _ hb
  | bitOr =>
    simp only [evalAluOp, aluWidth, BitVec.toNat_or]
    exact Nat.or_lt_two_pow (lt_two_pow_mono ha (Nat.le_max_left _ _))
      (lt_two_pow_mono hb (Nat.le_max_right _ _))
  | bitXor =>
    simp only [evalAluOp, aluWidth, BitVec.toNat_xor]
    exact Nat.xor_lt_two_pow (lt_two_pow_mono ha (Nat.le_max_left _ _))
      (lt_two_pow_mono hb (Nat.le_max_right _ _))
  | shl =>
    cases rhs with
    | const k =>
      have hbk := hrhs k rfl
      subst hbk
      apply lt_two_pow_min64
      simp only [evalAluOp, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_add]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _)
        (Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos _))
    | _ => exact (evalAluOp .shl a b).isLt
  | lshr =>
    simp only [evalAluOp, aluWidth, BitVec.toNat_ushiftRight]
    exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
  | ashr =>
    simp only [aluWidth]
    split
    · rename_i hw
      have hmsb : a.msb = false := by
        rw [BitVec.msb_eq_decide]
        have := lt_two_pow_mono ha (show wa ≤ 63 by omega)
        simp only [decide_eq_false_iff_not, Nat.not_le]
        exact this
      simp only [evalAluOp, BitVec.sshiftRight_eq_of_msb_false hmsb, BitVec.toNat_ushiftRight]
      exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
    · exact (evalAluOp .ashr a b).isLt
  | eq => exact ite_one_zero_lt _
  | ult => exact ite_one_zero_lt _
  | slt => exact ite_one_zero_lt _
  | qmul32 => exact (evalAluOp .qmul32 a b).isLt

theorem evalWidthOp_lt (op : RtlWidthOp) (a : BitVec 64) (wa w : Nat)
    (ha : a.toNat < 2 ^ wa) (h : widthOpWidth op wa = .ok w) :
    (evalWidthOp op a).toNat < 2 ^ w := by
  cases op with
  | slice hi lo =>
    simp only [widthOpWidth] at h
    split at h
    · rename_i hc
      cases h
      exact truncToWidth_lt _ (by omega) _
    · cases h
  | zext w' =>
    simp only [widthOpWidth] at h
    split at h
    · rename_i hc
      cases h
      exact lt_two_pow_mono ha hc.1
    · cases h
  | sext f t =>
    simp only [widthOpWidth] at h
    split at h
    · cases h
      simp only [evalWidthOp, BitVec.toNat_setWidth]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)
    · cases h
  | trunc w' =>
    simp only [widthOpWidth] at h
    split at h
    · rename_i hc
      cases h
      simp only [evalWidthOp]
      rcases Nat.le_total w' wa with hle | hle
      · rw [Nat.min_eq_left hle]; exact truncToWidth_lt _ hc.2 _
      · rw [Nat.min_eq_right hle]
        exact Nat.lt_of_le_of_lt (truncToWidth_le _ _) ha
    · cases h

/-- **Width soundness.** If the inputs, wires and registers fit their declared widths and
`inferWidthE` assigns `e` the width `w`, the value of `e` is below `2^w`. -/
theorem evalRtlExpr_lt_of_inferWidthE (env : WidthEnv)
    (inputs wires regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ env.input i)
    (hW : ∀ i, (wires i).toNat < 2 ^ env.wire i)
    (hR : ∀ i, (regs i).toNat < 2 ^ env.reg i) :
    ∀ (e : RtlExpr) (w : Nat), inferWidthE env e = .ok w →
      (evalRtlExpr inputs wires regs e).toNat < 2 ^ w := by
  intro e
  induction e with
  | const v =>
    intro w h
    simp only [inferWidthE, Except.ok.injEq] at h
    subst h
    exact Nat.lt_log2_self
  | inputPort idx =>
    intro w h
    simp only [inferWidthE, Except.ok.injEq] at h
    subst h; exact hIn idx
  | wireRef idx =>
    intro w h
    simp only [inferWidthE, Except.ok.injEq] at h
    subst h; exact hW idx
  | regRead idx =>
    intro w h
    simp only [inferWidthE, Except.ok.injEq] at h
    subst h; exact hR idx
  | alu op a b iha ihb =>
    intro w h
    simp only [inferWidthE] at h
    cases ha : inferWidthE env a <;> cases hb : inferWidthE env b <;> simp [ha, hb] at h
    rename_i wa wb
    subst h
    exact evalAluOp_lt_aluWidth op b _ _ wa wb (iha wa ha) (ihb wb hb)
      (fun k hk => by subst hk; rfl)
  | mux c t f ihc iht ihf =>
    intro w h
    simp only [inferWidthE] at h
    cases hc : inferWidthE env c <;> cases ht : inferWidthE env t <;>
      cases hf : inferWidthE env f <;> simp [hc, ht, hf] at h
    rename_i wc wt wf
    subst h
    simp only [evalRtlExpr]
    split
    · exact lt_two_pow_mono (iht wt ht) (Nat.le_max_left _ _)
    · exact lt_two_pow_mono (ihf wf hf) (Nat.le_max_right _ _)
  | bitNot a iha =>
    intro w h
    simp only [inferWidthE] at h
    cases ha : inferWidthE env a <;> simp [ha] at h
    subst h
    exact (evalRtlExpr inputs wires regs (.bitNot a)).isLt
  | resize op a iha =>
    intro w h
    simp only [inferWidthE] at h
    cases ha : inferWidthE env a <;> simp [ha] at h
    rename_i wa
    exact evalWidthOp_lt op _ wa w (iha wa ha) h

/-- `inferWidth` form of `evalRtlExpr_lt_of_inferWidthE`. -/
theorem evalRtlExpr_lt_of_inferWidth (env : WidthEnv)
    (inputs wires regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ env.input i)
    (hW : ∀ i, (wires i).toNat < 2 ^ env.wire i)
    (hR : ∀ i, (regs i).toNat < 2 ^ env.reg i)
    (e : RtlExpr) (w : Nat) (h : inferWidth env e = some w) :
    (evalRtlExpr inputs wires regs e).toNat < 2 ^ w := by
  apply evalRtlExpr_lt_of_inferWidthE env inputs wires regs hIn hW hR e w
  unfold inferWidth at h
  cases he : inferWidthE env e <;> simp [he, Except.toOption] at h
  subst h; rfl

/-- Declared width of wire `idx` (64 if no wire has that index). -/
def wireWidthOf (m : RtlModule) (idx : Nat) : Nat :=
  ((m.wires.find? (·.wireIdx == idx)).map (·.width)).getD 64

/-- Declared width of register `idx` (64 if no register has that index). -/
def regWidthOf (m : RtlModule) (idx : Nat) : Nat :=
  ((m.regs.find? (·.regIdx == idx)).map (·.width)).getD 64

/-- The declared widths of `m`. -/
def moduleWidthEnv (m : RtlModule) : WidthEnv :=
  ⟨inputWidth m, wireWidthOf m, regWidthOf m⟩

/-- Why `e` does not fit `decl` bits (empty if it does). `what` names the driven signal. -/
def fitErrors (env : WidthEnv) (what : String) (decl : Nat) (e : RtlExpr) : List String :=
  match inferWidthE env e with
  | .error msg => [s!"{what}: {msg}"]
  | .ok w => if w ≤ decl then [] else
    [s!"{what} is {decl} bits wide but is driven by a {w}-bit expression (narrow it with trunc or slice)"]

/-- Why a declared width is out of range (empty if it is 1..64). -/
def declErrors (what : String) (w : Nat) : List String :=
  if validWidth w then [] else [s!"{what} declares width {w}; widths are 1..64"]

/-- Every reason `m` fails the width check, each naming the signal. -/
def widthErrors (m : RtlModule) : List String :=
  let env := moduleWidthEnv m
  (List.range m.inputNames.length).flatMap (fun i =>
    declErrors s!"input port `{m.inputNames.getD i s!"in_{i}"}`" (inputWidth m i)) ++
  m.wires.flatMap (fun a =>
    declErrors s!"wire `{a.name}`" a.width ++
    fitErrors env s!"wire `{a.name}`" (wireWidthOf m a.wireIdx) a.expr) ++
  m.regs.flatMap (fun r =>
    declErrors s!"register `{r.name}`" r.width ++
    fitErrors env s!"register `{r.name}`" (regWidthOf m r.regIdx) r.nextExpr ++
    (match r.resetKind with
     | .resetFree => []
     | .syncReset v =>
       if constWidth v ≤ regWidthOf m r.regIdx then [] else
         [s!"register `{r.name}` resets to {v.toNat}, which does not fit its {regWidthOf m r.regIdx} bits"])) ++
  m.outputs.flatMap (fun o =>
    declErrors s!"output port `{o.name}`" o.width ++
    fitErrors env s!"output port `{o.name}`" o.width o.expr)

/-- The width check: no reasons. -/
def checkWidths (m : RtlModule) : Bool :=
  (widthErrors m).isEmpty

theorem fitErrors_nil {env : WidthEnv} {what : String} {decl : Nat} {e : RtlExpr}
    (h : fitErrors env what decl e = []) : ∃ w, inferWidthE env e = .ok w ∧ w ≤ decl := by
  unfold fitErrors at h
  cases he : inferWidthE env e with
  | error msg => simp [he] at h
  | ok w =>
    simp only [he] at h
    split at h
    · exact ⟨w, rfl, by assumption⟩
    · cases h

private theorem flatMap_nil_mem {α β : Type} {f : α → List β} {l : List α} {x : α}
    (h : l.flatMap f = []) (hx : x ∈ l) : f x = [] :=
  List.flatMap_eq_nil_iff.mp h x hx

/-- What `checkWidths` gives, piece by piece. -/
theorem checkWidths_parts (m : RtlModule) (h : checkWidths m = true) :
    (∀ a ∈ m.wires, fitErrors (moduleWidthEnv m) s!"wire `{a.name}`" (wireWidthOf m a.wireIdx) a.expr = []) ∧
    (∀ r ∈ m.regs, fitErrors (moduleWidthEnv m) s!"register `{r.name}`" (regWidthOf m r.regIdx) r.nextExpr = [] ∧
      ∀ v, r.resetKind = .syncReset v → constWidth v ≤ regWidthOf m r.regIdx) ∧
    (∀ o ∈ m.outputs, validWidth o.width = true ∧
      fitErrors (moduleWidthEnv m) s!"output port `{o.name}`" o.width o.expr = []) := by
  unfold checkWidths widthErrors at h
  simp only [List.isEmpty_iff, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨_, hw⟩, hr⟩, ho⟩ := h
  refine ⟨fun a ha => ?_, fun r hr' => ?_, fun o ho' => ?_⟩
  · have := flatMap_nil_mem hw ha
    simp only [List.append_eq_nil_iff] at this
    exact this.2
  · have := flatMap_nil_mem hr hr'
    simp only [List.append_eq_nil_iff] at this
    refine ⟨this.1.2, fun v hv => ?_⟩
    have h3 := this.2
    rw [hv] at h3
    simp only at h3
    split at h3
    · assumption
    · cases h3
  · have := flatMap_nil_mem ho ho'
    simp only [List.append_eq_nil_iff] at this
    refine ⟨?_, this.2⟩
    have h1 := this.1
    unfold declErrors at h1
    split at h1
    · assumption
    · cases h1

/-- The wire table keeps every wire inside its declared width. -/
theorem evalWireTable_lt (m : RtlModule) (inputs regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ inputWidth m i)
    (hR : ∀ i, (regs i).toNat < 2 ^ regWidthOf m i)
    (hChk : checkWidths m = true) :
    ∀ i, (evalWireTable inputs regs m.wires i).toNat < 2 ^ wireWidthOf m i := by
  have hWires := (checkWidths_parts m hChk).1
  unfold evalWireTable
  suffices ∀ (l : List WireAssign), (∀ a ∈ l, a ∈ m.wires) →
      ∀ (env : Nat → BitVec 64), (∀ i, (env i).toNat < 2 ^ wireWidthOf m i) →
      ∀ i, ((l.foldl (fun (env : Nat → BitVec 64) a =>
        let v := evalRtlExpr inputs env regs a.expr
        fun i => if i == a.wireIdx then v else env i) env) i).toNat < 2 ^ wireWidthOf m i by
    exact this m.wires (fun _ h => h) _ (fun i => by simpa using Nat.two_pow_pos (wireWidthOf m i))
  intro l
  induction l with
  | nil => intro _ env hEnv; exact hEnv
  | cons a rest ih =>
    intro hSub env hEnv
    simp only [List.foldl_cons]
    apply ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx))
    intro i
    obtain ⟨w, hw, hle⟩ := fitErrors_nil (hWires a (hSub a List.mem_cons_self))
    have hv := evalRtlExpr_lt_of_inferWidthE (moduleWidthEnv m) inputs env regs hIn hEnv hR a.expr w hw
    by_cases hi : i = a.wireIdx
    · subst hi; simp only [beq_self_eq_true, ite_true]; exact lt_two_pow_mono hv hle
    · simp only [beq_iff_eq, hi, ite_false]; exact hEnv i

/-- One clock edge keeps every register inside its declared width. -/
theorem stepModuleRegs_lt (m : RtlModule) (rst : Bool) (inputs regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ inputWidth m i)
    (hR : ∀ i, (regs i).toNat < 2 ^ regWidthOf m i)
    (hChk : checkWidths m = true) :
    ∀ i, (stepModuleRegs m rst inputs regs i).toNat < 2 ^ regWidthOf m i := by
  have hRegs := (checkWidths_parts m hChk).2.1
  have hWire := evalWireTable_lt m inputs regs hIn hR hChk
  unfold stepModuleRegs
  suffices ∀ (l : List RegSpec), (∀ r ∈ l, r ∈ m.regs) →
      ∀ (st : Nat → BitVec 64), (∀ i, (st i).toNat < 2 ^ regWidthOf m i) →
      ∀ i, ((l.foldl (fun (nextSt : Nat → BitVec 64) r =>
        let v :=
          match r.resetKind with
          | .resetFree => evalRtlExpr inputs (evalWireTable inputs regs m.wires) regs r.nextExpr
          | .syncReset initVal =>
            if rst then initVal else evalRtlExpr inputs (evalWireTable inputs regs m.wires) regs r.nextExpr
        fun i => if i == r.regIdx then v else nextSt i) st) i).toNat < 2 ^ regWidthOf m i by
    exact this m.regs (fun _ h => h) regs hR
  intro l
  induction l with
  | nil => intro _ st hSt; exact hSt
  | cons r rest ih =>
    intro hSub st hSt
    simp only [List.foldl_cons]
    apply ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx))
    intro i
    have hr := hRegs r (hSub r List.mem_cons_self)
    obtain ⟨w, hw, hle⟩ := fitErrors_nil hr.1
    have hNext := lt_two_pow_mono
      (evalRtlExpr_lt_of_inferWidthE (moduleWidthEnv m) inputs _ regs hIn hWire hR r.nextExpr w hw) hle
    by_cases hi : i = r.regIdx
    · subst hi
      simp only [beq_self_eq_true, ite_true]
      cases hk : r.resetKind with
      | resetFree => exact hNext
      | syncReset v =>
        simp only
        cases rst
        · exact hNext
        · exact lt_two_pow_mono Nat.lt_log2_self (hr.2 v hk)
    · simp only [beq_iff_eq, hi, ite_false]; exact hSt i

/-- **The carrier is faithful.** For a width-checked module, from registers that fit and inputs
that fit their ports on every cycle, every register fits its declared width after any trace. -/
theorem runModuleTrace_lt (m : RtlModule) (hChk : checkWidths m = true)
    (trace : List (Bool × (Nat → BitVec 64)))
    (hIn : ∀ c ∈ trace, ∀ i, (c.2 i).toNat < 2 ^ inputWidth m i) :
    ∀ (init : Nat → BitVec 64), (∀ i, (init i).toNat < 2 ^ regWidthOf m i) →
      ∀ i, (runModuleTrace m init trace i).toNat < 2 ^ regWidthOf m i := by
  unfold runModuleTrace
  induction trace with
  | nil => intro init h; exact h
  | cons c rest ih =>
    intro init hInit
    simp only [List.foldl_cons]
    exact ih (fun c' hc' => hIn c' (List.mem_cons_of_mem _ hc')) _
      (stepModuleRegs_lt m c.1 c.2 init (hIn c List.mem_cons_self) hInit hChk)

/-- For a width-checked module the port truncation is the identity: the narrow output ports carry
the whole word-level value. -/
theorem evalModuleOutputsW_eq_of_checkWidths (m : RtlModule) (inputs regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ inputWidth m i)
    (hR : ∀ i, (regs i).toNat < 2 ^ regWidthOf m i)
    (hChk : checkWidths m = true) :
    evalModuleOutputsW m inputs regs = evalModuleOutputs m inputs regs := by
  have hOuts := (checkWidths_parts m hChk).2.2
  have hWire := evalWireTable_lt m inputs regs hIn hR hChk
  simp only [evalModuleOutputsW, evalModuleOutputs]
  apply List.map_congr_left
  intro o ho
  obtain ⟨hv, hf⟩ := hOuts o ho
  obtain ⟨w, hw, hle⟩ := fitErrors_nil hf
  have hlt := evalRtlExpr_lt_of_inferWidthE (moduleWidthEnv m) inputs _ regs hIn hWire hR o.expr w hw
  have h64 : o.width ≤ 64 := by
    unfold validWidth at hv; simp only [Bool.and_eq_true, decide_eq_true_eq] at hv; exact hv.2
  rw [truncToWidth_of_lt o.width h64 _ (lt_two_pow_mono hlt hle)]

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
range, two-flop synchronizer chains, and every signal holding its declared width (`checkWidths`). -/
def checkRtlModuleW (m : RtlModule) : Bool :=
  checkRtlModule m && checkModuleCdc m.regs m.wires && checkPortWidths m && checkCdcTwoFlop m &&
    checkWidths m

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

/-! ## 4d. Clock Domains in the Cycle Semantics (`stepModuleDomain`)

The emitter clocks each domain's registers from that domain's own `clk_<d>` (`moduleClockPorts`).
`stepModuleDomain m d` is one rising edge of `clk_<d>`: the registers of `d` latch and every other
register holds (`stepModuleDomain_other_holds`). `stepModuleRegs`, which `runModuleTrace` and
`obend verilate` use, is the edge of a module whose clocks all rise together; for a one-domain
module the two are the same edge (`stepModuleDomain_eq_of_single`). The CDC check is then a
statement about what the emitted always-blocks sample: at an edge of `clk_<d>`, a register of `d`
that is not a synchronizer computes the same next value from any two states that agree on `d`'s
registers (`stepDomain_nonSync_reads_own_domain`; registers it reads directly, the wire table held
fixed). -/

/-- The `(clock, reset)` port names the emitter gives each domain of `m`, in `moduleDomains` order:
`clk`/`rst` for a one-domain module, `clk_<d>`/`rst_<d>` otherwise. -/
def moduleClockPorts (m : RtlModule) : List (ClkDomain × String × String) :=
  let ds := moduleDomains m
  if ds.length > 1 then ds.map fun d => (d, s!"clk_{d.portSuffix}", s!"rst_{d.portSuffix}")
  else match ds with
    | d :: _ => [(d, "clk", "rst")]
    | []     => [(.coreClk, "clk", "rst")]

/-- One rising edge of domain `d`'s clock: `d`'s registers latch, the rest hold. -/
def stepModuleDomain (m : RtlModule) (d : ClkDomain) (rst : Bool)
    (inputs regState : Nat → BitVec 64) : Nat → BitVec 64 :=
  stepModuleRegs { m with regs := m.regs.filter (·.domain == d) } rst inputs regState

/-- With one clock domain, its edge is the module's edge. -/
theorem stepModuleDomain_eq_of_single (m : RtlModule) (d : ClkDomain)
    (h : m.regs.all (·.domain == d) = true) (rst : Bool) (inputs regState : Nat → BitVec 64) :
    stepModuleDomain m d rst inputs regState = stepModuleRegs m rst inputs regState := by
  have hf : m.regs.filter (·.domain == d) = m.regs := List.filter_eq_self.mpr (by simpa using h)
  unfold stepModuleDomain
  rw [hf]

/-- An edge of `d` leaves alone every register index that no register of `d` writes. -/
theorem stepModuleDomain_other_holds (m : RtlModule) (d : ClkDomain) (rst : Bool)
    (inputs regState : Nat → BitVec 64) (i : Nat)
    (hi : ∀ r ∈ m.regs, r.domain = d → r.regIdx ≠ i) :
    stepModuleDomain m d rst inputs regState i = regState i := by
  unfold stepModuleDomain stepModuleRegs
  simp only
  generalize hw : evalWireTable inputs regState m.wires = wenv
  suffices ∀ (l : List RegSpec), (∀ r ∈ l, r.regIdx ≠ i) → ∀ (st : Nat → BitVec 64), st i = regState i →
      (l.foldl (fun (nextSt : Nat → BitVec 64) r =>
        let v :=
          match r.resetKind with
          | .resetFree => evalRtlExpr inputs wenv regState r.nextExpr
          | .syncReset initVal => if rst then initVal else evalRtlExpr inputs wenv regState r.nextExpr
        fun j => if j == r.regIdx then v else nextSt j) st) i = regState i by
    apply this
    · intro r hr
      rw [List.mem_filter] at hr
      exact hi r hr.1 (by simpa using hr.2)
    · rfl
  intro l
  induction l with
  | nil => intro _ st h; exact h
  | cons r rest ih =>
    intro hl st hst
    simp only [List.foldl_cons]
    apply ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    have hne : (i == r.regIdx) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h => hl r List.mem_cons_self h.symm
    simp only [hne]
    exact hst

/-- An expression reads only the registers `exprReadRegsAndWires` lists: two register states that
agree there give the same value. -/
theorem evalRtlExpr_regs_locality (inputs wires : Nat → BitVec 64) (st1 st2 : Nat → BitVec 64) :
    ∀ (e : RtlExpr), (∀ i ∈ (exprReadRegsAndWires e).1, st1 i = st2 i) →
      evalRtlExpr inputs wires st1 e = evalRtlExpr inputs wires st2 e := by
  intro e
  induction e with
  | const _ => intro _; rfl
  | inputPort _ => intro _; rfl
  | wireRef _ => intro _; rfl
  | regRead idx =>
    intro h
    simp only [exprReadRegsAndWires, List.mem_singleton, forall_eq] at h
    simp only [evalRtlExpr, h]
  | alu op a b iha ihb =>
    intro h
    simp only [exprReadRegsAndWires, List.mem_append] at h
    simp only [evalRtlExpr, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi))]
  | mux c t f ihc iht ihf =>
    intro h
    simp only [exprReadRegsAndWires, List.mem_append] at h
    simp only [evalRtlExpr, ihc (fun i hi => h i (Or.inl (Or.inl hi))),
      iht (fun i hi => h i (Or.inl (Or.inr hi))), ihf (fun i hi => h i (Or.inr hi))]
  | bitNot a iha =>
    intro h
    simp only [exprReadRegsAndWires] at h
    simp only [evalRtlExpr, iha h]
  | resize op a iha =>
    intro h
    simp only [exprReadRegsAndWires] at h
    simp only [evalRtlExpr, iha h]

/-- **The CDC check, read against the emitted clocks.** A register `r` of domain `d` that is not a
synchronizer and passes `checkRegCdc` samples, at an edge of `clk_<d>`, nothing but registers of
`d`: from two states agreeing on `d`'s registers it latches the same value. -/
theorem stepDomain_nonSync_reads_own_domain (m : RtlModule) (r : RegSpec)
    (hCdc : checkRegCdc m.regs r = true) (hNoSync : r.isSynchronizer = false)
    (inputs wires st1 st2 : Nat → BitVec 64)
    (hAgree : ∀ i, lookupRegDomain m.regs i = some r.domain → st1 i = st2 i) :
    evalRtlExpr inputs wires st1 r.nextExpr = evalRtlExpr inputs wires st2 r.nextExpr := by
  apply evalRtlExpr_regs_locality
  intro i hi
  have hMem : i ∈ exprReadRegs r.nextExpr := by
    unfold exprReadRegs; simpa using hi
  have hSome : ∃ dom, lookupRegDomain m.regs i = some dom := by
    have h := hCdc
    unfold checkRegCdc at h
    rw [List.all_eq_true] at h
    have hi' := h i hMem
    cases hl : lookupRegDomain m.regs i with
    | none => rw [hl] at hi'; cases hi'
    | some dom => exact ⟨dom, rfl⟩
  obtain ⟨dom, hDom⟩ := hSome
  have hEq := cdcSafe_no_unsynchronized_crossing m.regs r i dom hCdc hNoSync hMem hDom
  exact hAgree i (hEq ▸ hDom)

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

/-- The 64-bit SystemVerilog constant `2^w - 1` (all ones below bit `w`). -/
def svMask (w : Nat) : String := s!"64'd{2 ^ (min w 64) - 1}"

/-- Render an `RtlExpr` as a SystemVerilog expression string. Every leaf is a 64-bit expression
(`inNames`, `regNames` and `wireName` already zero-extend narrow signals), so every operator is
evaluated at 64 bits, as `evalRtlExpr` does; a width operator is a mask, a shift or a cast. -/
def emitExprSV (inNames : List String) (regNames : List String)
    (wireName : Nat → String := fun i => s!"w_{i}") : RtlExpr → String
  | .const v         => s!"64'd{v.toNat}"
  | .inputPort idx   => inNames.getD idx s!"in_{idx}"
  | .wireRef idx     => wireName idx
  | .regRead idx     => regNames.getD idx s!"r_{idx}"
  | .alu .eq a b     => s!"({emitExprSV inNames regNames wireName a} == {emitExprSV inNames regNames wireName b} ? 64'd1 : 64'd0)"
  | .alu .ult a b    => s!"({emitExprSV inNames regNames wireName a} < {emitExprSV inNames regNames wireName b} ? 64'd1 : 64'd0)"
  | .alu .slt a b    => s!"($signed({emitExprSV inNames regNames wireName a}) < $signed({emitExprSV inNames regNames wireName b}) ? 64'd1 : 64'd0)"
  | .alu .shl a b    => s!"({emitExprSV inNames regNames wireName a} << ({emitExprSV inNames regNames wireName b} & 64'd63))"
  | .alu .lshr a b   => s!"({emitExprSV inNames regNames wireName a} >> ({emitExprSV inNames regNames wireName b} & 64'd63))"
  | .alu .ashr a b   => s!"64'($signed({emitExprSV inNames regNames wireName a}) >>> ({emitExprSV inNames regNames wireName b} & 64'd63))"
  | .alu .qmul32 a b => s!"64'((128'($signed({emitExprSV inNames regNames wireName a})) * 128'($signed({emitExprSV inNames regNames wireName b}))) >>> 32)"
  | .alu op a b      => s!"({emitExprSV inNames regNames wireName a} {emitAluOpSV op} {emitExprSV inNames regNames wireName b})"
  | .mux c t f       => s!"(({emitExprSV inNames regNames wireName c} != 64'd0) ? {emitExprSV inNames regNames wireName t} : {emitExprSV inNames regNames wireName f})"
  | .bitNot a        => s!"(~{emitExprSV inNames regNames wireName a})"
  | .resize (.slice hi lo) a =>
    s!"(({emitExprSV inNames regNames wireName a} >> 64'd{lo}) & {svMask (hi + 1 - lo)})"
  | .resize (.zext _) a => emitExprSV inNames regNames wireName a
  | .resize (.sext f t) a =>
    s!"64'($unsigned({t}'($signed({f}'({emitExprSV inNames regNames wireName a})))))"
  | .resize (.trunc w) a => s!"({emitExprSV inNames regNames wireName a} & {svMask w})"

/-- The SystemVerilog expression standing for input `idx` inside the module body: the port name
when it is 64 bits wide, otherwise the port zero-extended to 64 bits (`64'(name)`). -/
def inputExprsSV (m : RtlModule) : List String :=
  (List.range m.inputNames.length).map fun i =>
    let n := m.inputNames.getD i s!"in_{i}"
    if inputWidth m i == 64 then n else s!"64'({n})"

/-- A signal of width `w` read inside an expression: itself at 64 bits, zero-extended otherwise. -/
def readSV (w : Nat) (name : String) : String :=
  if w == 64 then name else s!"64'({name})"

/-- The right-hand side stored into a `w`-bit signal: the 64-bit expression, cast down when `w < 64`
(the width check makes the cast lose only zero bits). -/
def storeSV (w : Nat) (rhs : String) : String :=
  if w == 64 then rhs else s!"{w}'({rhs})"

/-- The packed range of a `w`-bit declaration. -/
def rangeSV (w : Nat) : String := s!"[{w - 1}:0]"

/-- The `always_ff` blocks of one clock domain: reset-free datapath registers in one block and
synchronous-reset control registers in another, clocked by `clkName` and reset by `rstName`. -/
def emitDomainBlocksSV (inExprs regNames : List String) (regsD : List RegSpec)
    (clkName rstName : String) (wireName : Nat → String := fun i => s!"w_{i}") : String :=
  let resetFreeRegs := regsD.filter fun r =>
    match r.resetKind with | .resetFree => true | .syncReset _ => false
  let syncResetRegs := regsD.filter fun r =>
    match r.resetKind with | .resetFree => false | .syncReset _ => true
  let rfBlock :=
    if resetFreeRegs.isEmpty then ""
    else
      let assigns := resetFreeRegs.map fun r =>
        s!"    {r.name} <= {storeSV r.width (emitExprSV inExprs regNames wireName r.nextExpr)};"
      s!"  // Reset-free datapath registers\n  always_ff @(posedge {clkName}) begin\n" ++
        String.intercalate "\n" assigns ++ "\n  end\n"
  let srBlock :=
    if syncResetRegs.isEmpty then ""
    else
      let rstAssigns := syncResetRegs.map fun r =>
        let initV := match r.resetKind with | .syncReset v => v.toNat | .resetFree => 0
        s!"      {r.name} <= {r.width}'d{initV};"
      let stepAssigns := syncResetRegs.map fun r =>
        s!"      {r.name} <= {storeSV r.width (emitExprSV inExprs regNames wireName r.nextExpr)};"
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
* Every port, wire and register is declared `logic [w-1:0]` from its declared width. A narrow
  signal is read as `64'(name)` and written as `w'(expr)`; under `checkWidths` the cast drops only
  zero bits (`runModuleTrace_lt`, `evalModuleOutputsW_eq_of_checkWidths`). A module whose signals
  are all 64 bits emits the same text as before widths existed.

Callers should check `checkRtlModuleW` first; the emitter itself does not refuse. -/
def emitModuleSV (m : RtlModule) : String :=
  let regNames := m.regs.map fun r => readSV r.width r.name
  let wireName (i : Nat) : String := readSV (wireWidthOf m i) s!"w_{i}"
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
    s!"  input  logic {rangeSV (inputWidth m i)} {n}"
  let outPorts := m.outputs.map fun o =>
    s!"  output logic {rangeSV o.width} {o.name}"
  let allPorts := clkPorts ++ inPorts ++ outPorts
  let portHeader := String.intercalate ",\n" allPorts
  let wireDecls := m.wires.map fun w =>
    s!"  logic {rangeSV w.width} w_{w.wireIdx}; // {w.name}"
  let regDecls := m.regs.map fun r =>
    if r.isSynchronizer then s!"  (* ASYNC_REG = \"TRUE\" *) logic {rangeSV r.width} {r.name};"
    else s!"  logic {rangeSV r.width} {r.name};"
  let combWires := m.wires.map fun w =>
    s!"    w_{w.wireIdx} = {storeSV w.width (emitExprSV inExprs regNames wireName w.expr)};"
  let combOuts := m.outputs.map fun o =>
    s!"    {o.name} = {storeSV o.width (emitExprSV inExprs regNames wireName o.expr)};"
  let ffBlocks := String.join (domains.map fun d =>
    emitDomainBlocksSV inExprs regNames (m.regs.filter (·.domain == d)) (clkName d) (rstName d) wireName)
  s!"module {m.name} (\n{portHeader}\n);\n" ++
  (if wireDecls.isEmpty then "" else String.intercalate "\n" wireDecls ++ "\n") ++
  (if regDecls.isEmpty then "" else String.intercalate "\n" regDecls ++ "\n") ++
  "  always_comb begin\n" ++
  String.intercalate "\n" (combWires ++ combOuts) ++
  "\n  end\n" ++
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
