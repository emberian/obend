module
/-
# Obend.Hardware.HDL — Verified Synchronous HDL, `SyncRamSpec`, Combinational DAG/CDC Checkers & SV Emitter

Word-level synchronous RTL over `BitVec 64` with checked signal widths (`1..64`), topological wire DAGs
(`checkWireTableDAG`), clock-domain crossing gates (`checkModuleCdc`, `checkCdcTwoFlop`), synchronous
clocked RAM banks (`SyncRamSpec`, `RtlMemModule`, `stepMemModule`), and SystemVerilog-2012 emission
(`emitModuleSV`, `emitMemModuleSV`).
-/
public section

namespace Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. Combinational ALU Operations & RTL Expressions -/

/-- Binary ALU operations in the core 64-bit hardware datapath. -/
inductive RtlAluOp where
  | add | sub | mul | bitAnd | bitOr | bitXor | shl | lshr | ashr | eq | ult | slt | qmul32
  deriving @[expose] DecidableEq, Repr

/-- Evaluate a binary ALU operation on 64-bit bitvectors. -/
@[expose] def evalAluOp (op : RtlAluOp) (a b : BitVec 64) : BitVec 64 :=
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
abbrev truncToWidth (w : Nat) (v : BitVec 64) : BitVec 64 :=
  v &&& (BitVec.allOnes 64 >>> (64 - w))

/-- Width-changing unary operators (`slice`, `zext`, `sext`, `trunc`) on the 64-bit carrier. -/
inductive RtlWidthOp where
  | slice (hi lo : Nat) | zext (w : Nat) | sext (fromW toW : Nat) | trunc (w : Nat)
  deriving @[expose] DecidableEq, Repr

/-- Semantics of a width operator on the 64-bit carrier. -/
abbrev evalWidthOp : RtlWidthOp → BitVec 64 → BitVec 64
  | .slice hi lo, a => truncToWidth (hi + 1 - lo) (a >>> lo)
  | .zext _,      a => a
  | .sext f t,    a => ((a.setWidth f).signExtend t).setWidth 64
  | .trunc w,     a => truncToWidth w a

/-- Combinational RTL expression over input ports, internal wires, and sequential registers. -/
inductive RtlExpr where
  | const (val : BitVec 64) | inputPort (portIdx : Nat) | wireRef (wireIdx : Nat) | regRead (regIdx : Nat)
  | alu (op : RtlAluOp) (lhs rhs : RtlExpr) | mux (cond ifTrue ifFalse : RtlExpr)
  | bitNot (arg : RtlExpr) | resize (op : RtlWidthOp) (arg : RtlExpr)
  deriving @[expose] DecidableEq, Repr

/-- Evaluate an `RtlExpr` given environments for input ports, already-evaluated wires, and registers. -/
@[expose] def evalRtlExpr (inputs wires regs : Nat → BitVec 64) : RtlExpr → BitVec 64
  | .const v       => v
  | .inputPort idx => inputs idx
  | .wireRef idx   => wires idx
  | .regRead idx   => regs idx
  | .alu op a b    => evalAluOp op (evalRtlExpr inputs wires regs a) (evalRtlExpr inputs wires regs b)
  | .mux c t f     => if evalRtlExpr inputs wires regs c != 0#64 then evalRtlExpr inputs wires regs t else evalRtlExpr inputs wires regs f
  | .bitNot a      => ~~~(evalRtlExpr inputs wires regs a)
  | .resize op a   => evalWidthOp op (evalRtlExpr inputs wires regs a)

/-- `{hi, lo}` with `lo` taken as `loW` bits: `(hi << loW) | trunc loW lo`. -/
abbrev RtlExpr.concat (hi lo : RtlExpr) (loW : Nat) : RtlExpr :=
  .alu .bitOr (.alu .shl hi (.const (BitVec.ofNat 64 loW))) (.resize (.trunc loW) lo)

/-! ## 2. Topological Combinational DAG Checker & Agreement Theorem -/

/-- Check that `RtlExpr` only references internal wires `< bound` and valid inputs/registers. -/
@[expose] def checkExprDAG (numInputs numRegs wireBound : Nat) : RtlExpr → Bool
  | .const _       => true
  | .inputPort idx => idx < numInputs
  | .wireRef idx   => idx < wireBound
  | .regRead idx   => idx < numRegs
  | .alu _ a b     => checkExprDAG numInputs numRegs wireBound a && checkExprDAG numInputs numRegs wireBound b
  | .mux c t f     => checkExprDAG numInputs numRegs wireBound c && checkExprDAG numInputs numRegs wireBound t && checkExprDAG numInputs numRegs wireBound f
  | .bitNot a      => checkExprDAG numInputs numRegs wireBound a
  | .resize _ a    => checkExprDAG numInputs numRegs wireBound a

/-- If `checkExprDAG` holds, `evalRtlExpr` depends only on wire values at indices `< wireBound`. -/
theorem evalRtlExpr_dag_locality (numInputs numRegs wireBound : Nat)
    (inputs regs w1 w2 : Nat → BitVec 64) (e : RtlExpr)
    (hDag : checkExprDAG numInputs numRegs wireBound e = true)
    (hAgree : ∀ i, i < wireBound → w1 i = w2 i) :
    evalRtlExpr inputs w1 regs e = evalRtlExpr inputs w2 regs e := by
  induction e with
  | const _ | inputPort _ | regRead _ => rfl
  | wireRef idx => simp only [checkExprDAG, decide_eq_true_eq] at hDag; exact hAgree idx hDag
  | alu _ _ _ iha ihb => simp only [checkExprDAG, Bool.and_eq_true] at hDag; simp only [evalRtlExpr, iha hDag.1, ihb hDag.2]
  | mux _ _ _ ihc iht ihf => simp only [checkExprDAG, Bool.and_eq_true] at hDag; simp only [evalRtlExpr, ihc hDag.1.1, iht hDag.1.2, ihf hDag.2]
  | bitNot _ iha => simp only [checkExprDAG] at hDag; simp only [evalRtlExpr, iha hDag]
  | resize _ _ iha => simp only [checkExprDAG] at hDag; simp only [evalRtlExpr, iha hDag]

/-- Topological wire assignment: wire `wireIdx` is defined by `expr` at declared `width` (1..64). -/
structure WireAssign where
  wireIdx : Nat
  name    : String
  expr    : RtlExpr
  width   : Nat := 64
  deriving @[expose] DecidableEq, Repr

/-- Verify wires are indexed `0, 1, ...` and wire `i` only references earlier wires `< i`. -/
@[expose] def checkWireTableDAG (numInputs numRegs : Nat) (assigns : List WireAssign) : Bool :=
  let rec go (expectedIdx : Nat) : List WireAssign → Bool
    | [] => true
    | a :: rest => (a.wireIdx == expectedIdx) && checkExprDAG numInputs numRegs expectedIdx a.expr && go (expectedIdx + 1) rest
  go 0 assigns

/-- Evaluate a wire assignment table in a single forward pass. -/
@[expose] def evalWireTable (inputs regs : Nat → BitVec 64) (assigns : List WireAssign) : Nat → BitVec 64 :=
  assigns.foldl (fun env a => let v := evalRtlExpr inputs env regs a.expr; fun i => if i == a.wireIdx then v else env i) (fun _ => 0#64)

/-- Array-backed wire table evaluation (`evalWireTableArr_getD`). -/
abbrev evalWireTableArr (inputs regs : Nat → BitVec 64) (assigns : List WireAssign) : Array (BitVec 64) :=
  let n := assigns.foldl (fun k a => max k (a.wireIdx + 1)) 0
  assigns.foldl (fun arr a => arr.set! a.wireIdx (evalRtlExpr inputs (fun i => arr.getD i 0#64) regs a.expr)) (Array.replicate n 0#64)

/-- Compiled array-backed form of `evalWireTable` (`evalWireTable_eq_impl`, `@[csimp]`). -/
def evalWireTableImpl (inputs regs : Nat → BitVec 64) (assigns : List WireAssign) : Nat → BitVec 64 :=
  let n := assigns.foldl (fun k a => max k (a.wireIdx + 1)) 0
  if n > 1000000 then evalWireTable inputs regs assigns else let arr := evalWireTableArr inputs regs assigns; fun i => arr.getD i 0#64

theorem le_foldl_max {α : Type} (g : α → Nat) :
    ∀ (l : List α) (k : Nat), k ≤ l.foldl (fun k a => max k (g a)) k
  | [], _ => Nat.le_refl _
  | a :: rest, k => Nat.le_trans (Nat.le_max_left k (g a)) (le_foldl_max g rest _)

theorem mem_le_foldl_max {α : Type} (g : α → Nat) :
    ∀ (l : List α) (k : Nat), ∀ a ∈ l, g a ≤ l.foldl (fun k a => max k (g a)) k
  | [], _, _, h => nomatch h
  | b :: rest, k, a, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_trans (Nat.le_max_right k (g a)) (le_foldl_max g rest _)
    · exact mem_le_foldl_max g rest _ a h'

theorem array_getD_set! {α : Type} (a : Array α) (j i : Nat) (v d : α) (hj : j < a.size) :
    (a.set! j v).getD i d = if i = j then v else a.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; simp [hj]
  · simp [h, Ne.symm h]

theorem array_getD_replicate {α : Type} (n i : Nat) (d : α) : (Array.replicate n d).getD i d = d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl

/-- The array wire table agrees with `evalWireTable` at every index. -/
theorem evalWireTableArr_getD (inputs regs : Nat → BitVec 64) (assigns : List WireAssign) (i : Nat) :
    (evalWireTableArr inputs regs assigns).getD i 0#64 = evalWireTable inputs regs assigns i := by
  unfold evalWireTableArr evalWireTable
  generalize hn : assigns.foldl (fun k a => max k (a.wireIdx + 1)) 0 = n
  have hBound : ∀ a ∈ assigns, a.wireIdx < n := fun a ha => by
    have := mem_le_foldl_max (fun a : WireAssign => a.wireIdx + 1) assigns 0 a ha
    omega
  suffices ∀ (l : List WireAssign), (∀ a ∈ l, a.wireIdx < n) →
      ∀ (arr : Array (BitVec 64)) (env : Nat → BitVec 64),
        arr.size = n → (∀ i, arr.getD i 0#64 = env i) →
        ∀ i, (l.foldl (fun (arr : Array (BitVec 64)) a =>
            arr.set! a.wireIdx (evalRtlExpr inputs (fun i => arr.getD i 0#64) regs a.expr)) arr).getD i 0#64 =
          (l.foldl (fun (env : Nat → BitVec 64) a =>
            fun i => if i == a.wireIdx then evalRtlExpr inputs env regs a.expr else env i) env) i from
    this assigns hBound _ _ (by simp) (fun i => array_getD_replicate n i 0#64) i
  intro l
  induction l with
  | nil => intro _ arr env _ h; exact h
  | cons a rest ih =>
    intro hB arr env hSize hEq
    simp only [List.foldl_cons]
    have hEnv : (fun i => arr.getD i 0#64) = env := funext hEq
    apply ih (fun x hx => hB x (List.mem_cons_of_mem _ hx))
    · simp [hSize]
    · intro i
      rw [array_getD_set! _ _ _ _ _ (by rw [hSize]; exact hB a List.mem_cons_self), hEnv]
      by_cases h : i = a.wireIdx
      · simp [h]
      · simp [h, hEq]

/-- **The compiled wire table is the definition.** -/
@[csimp] theorem evalWireTable_eq_impl : @evalWireTable = @evalWireTableImpl := by
  funext inputs regs assigns i
  unfold evalWireTableImpl
  split
  · rfl
  · exact (evalWireTableArr_getD inputs regs assigns i).symm

/-! ## 3. Clock Domains, Reset Discipline & Static CDC Verification -/

/-- Named hardware clock domains. -/
inductive ClkDomain where
  | coreClk | axiIoClk | cfgJtagClk
  deriving @[expose] DecidableEq, Repr

/-- Port-name suffix of a clock domain when a module has more than one domain. -/
abbrev ClkDomain.portSuffix : ClkDomain → String
  | .coreClk    => "core"
  | .axiIoClk   => "axi"
  | .cfgJtagClk => "cfg"

/-- Hardware register reset discipline: reset-free datapath vs synchronous-reset control. -/
inductive ResetKind where
  | resetFree | syncReset (initVal : BitVec 64)
  deriving @[expose] DecidableEq, Repr

/-- Hardware register specification inside an `RtlModule` (`width` in 1..64). -/
structure RegSpec where
  regIdx         : Nat
  name           : String
  domain         : ClkDomain
  resetKind      : ResetKind
  isSynchronizer : Bool
  nextExpr       : RtlExpr
  width          : Nat := 64
  deriving @[expose] DecidableEq, Repr

/-- Collect all register and wire indices directly referenced by an `RtlExpr`. -/
@[expose] def exprReadRegsAndWires : RtlExpr → List Nat × List Nat
  | .const _ | .inputPort _ => ([], [])
  | .wireRef idx => ([], [idx])
  | .regRead idx => ([idx], [])
  | .alu _ a b => let (ra, wa) := exprReadRegsAndWires a; let (rb, wb) := exprReadRegsAndWires b; (ra ++ rb, wa ++ wb)
  | .mux c t f =>
    let (rc, wc) := exprReadRegsAndWires c; let (rt, wt) := exprReadRegsAndWires t; let (rf, wf) := exprReadRegsAndWires f
    (rc ++ rt ++ rf, wc ++ wt ++ wf)
  | .bitNot a | .resize _ a => exprReadRegsAndWires a

/-- Worklist walk collecting register indices reachable from `work` through `wires`. -/
@[expose] def expandWiresToRegs : Nat → List WireAssign → List Nat → List Nat → List Nat → List Nat
  | 0, _, _, _, acc => acc
  | _ + 1, _, [], _, acc => acc
  | fuel + 1, wires, idx :: rest, visited, acc =>
    if visited.contains idx then expandWiresToRegs fuel wires rest visited acc
    else match wires.find? (fun w => w.wireIdx == idx) with
      | none   => expandWiresToRegs fuel wires rest (idx :: visited) acc
      | some w =>
        let (rDirect, wNext) := exprReadRegsAndWires w.expr
        expandWiresToRegs fuel wires (wNext ++ rest) (idx :: visited) (acc ++ rDirect)

/-- Collect all register indices referenced by `e` (expanding `.wireRef` transitively when `wires ≠ []`). -/
abbrev exprReadRegs (e : RtlExpr) (wires : List WireAssign := []) : List Nat :=
  let (rDirect, wDirect) := exprReadRegsAndWires e
  match wires with
  | [] => rDirect
  | _  =>
    let edges := wires.foldl (fun n w => n + (exprReadRegsAndWires w.expr).2.length) 0
    rDirect ++ expandWiresToRegs (wires.length + edges + wDirect.length + 1) wires wDirect [] []

/-- Look up the clock domain of register `idx` in `regs`. -/
abbrev lookupRegDomain (regs : List RegSpec) (idx : Nat) : Option ClkDomain :=
  (regs.find? (fun r => r.regIdx == idx)).map (·.domain)

/-- Transitive wire-aware CDC safety check for `dstReg`. -/
abbrev checkRegCdcWithWires (wires : List WireAssign) (allRegs : List RegSpec) (dstReg : RegSpec) : Bool :=
  (exprReadRegs dstReg.nextExpr wires).all fun srcIdx =>
    match lookupRegDomain allRegs srcIdx with
    | none => false
    | some srcDom => if srcDom == dstReg.domain then true else dstReg.isSynchronizer && (dstReg.nextExpr == .regRead srcIdx)

/-- Direct-read CDC safety check for `dstReg`. -/
abbrev checkRegCdc (allRegs : List RegSpec) (dstReg : RegSpec) : Bool :=
  (exprReadRegs dstReg.nextExpr).all fun srcIdx =>
    match lookupRegDomain allRegs srcIdx with
    | none => false
    | some srcDom => if srcDom == dstReg.domain then true else dstReg.isSynchronizer && (dstReg.nextExpr == .regRead srcIdx)

/-- Verify CDC safety across all registers in a module. -/
abbrev checkModuleCdc (regs : List RegSpec) (wires : List WireAssign := []) : Bool :=
  match wires with
  | [] => regs.all (checkRegCdc regs)
  | _  => regs.all (checkRegCdcWithWires wires regs) && regs.all (checkRegCdc regs)

/-- If `checkRegCdc` holds and `dstReg.isSynchronizer = false`, no directly read register crosses domains. -/
theorem cdcSafe_no_unsynchronized_crossing (allRegs : List RegSpec) (dstReg : RegSpec) (srcIdx : Nat) (srcDom : ClkDomain)
    (hCdc : checkRegCdc allRegs dstReg = true) (hNoSync : dstReg.isSynchronizer = false)
    (hMem : srcIdx ∈ exprReadRegs dstReg.nextExpr) (hDom : lookupRegDomain allRegs srcIdx = some srcDom) :
    srcDom = dstReg.domain := by
  unfold checkRegCdc at hCdc; rw [List.all_eq_true] at hCdc
  have hSrc := hCdc srcIdx hMem; rw [hDom] at hSrc
  by_cases hEq : srcDom == dstReg.domain
  · exact eq_of_beq hEq
  · simp [hEq, hNoSync] at hSrc

/-- Transitive wire CDC soundness theorem when `dstReg.isSynchronizer = false`. -/
theorem cdcSafe_no_unsynchronized_crossing_withWires (wires : List WireAssign) (allRegs : List RegSpec) (dstReg : RegSpec)
    (srcIdx : Nat) (srcDom : ClkDomain) (hCdc : checkRegCdcWithWires wires allRegs dstReg = true)
    (hNoSync : dstReg.isSynchronizer = false) (hMem : srcIdx ∈ exprReadRegs dstReg.nextExpr wires)
    (hDom : lookupRegDomain allRegs srcIdx = some srcDom) : srcDom = dstReg.domain := by
  unfold checkRegCdcWithWires at hCdc; rw [List.all_eq_true] at hCdc
  have hSrc := hCdc srcIdx hMem; rw [hDom] at hSrc
  by_cases hEq : srcDom == dstReg.domain
  · exact eq_of_beq hEq
  · simp [hEq, hNoSync] at hSrc

/-! ## 4. Complete Synchronous `RtlModule` & Operational Semantics -/

/-- Output port binding of an `RtlModule` (`width` in 1..64). -/
structure OutputPort where
  name  : String
  expr  : RtlExpr
  width : Nat := 64
  deriving @[expose] DecidableEq, Repr

/-- Complete synchronous hardware module in `Obend.Hardware.HDL`. -/
structure RtlModule where
  name        : String
  inputNames  : List String
  wires       : List WireAssign
  regs        : List RegSpec
  outputs     : List OutputPort
  inputWidths : List Nat := []
  deriving @[expose] DecidableEq, Repr

/-- Structural DAG + direct CDC gate for an `RtlModule`. -/
@[expose] def checkRtlModule (m : RtlModule) : Bool :=
  let nIn := m.inputNames.length; let nReg := m.regs.length; let nWires := m.wires.length
  checkWireTableDAG nIn nReg m.wires && m.regs.all (fun r => checkExprDAG nIn nReg nWires r.nextExpr) &&
  m.outputs.all (fun o => checkExprDAG nIn nReg nWires o.expr) && checkModuleCdc m.regs

/-- Evaluate all combinational outputs of `m` given current inputs and register state. -/
abbrev evalModuleOutputs (m : RtlModule) (inputs regState : Nat → BitVec 64) : List (String × BitVec 64) :=
  let wireEnv := evalWireTable inputs regState m.wires
  m.outputs.map fun o => (o.name, evalRtlExpr inputs wireEnv regState o.expr)

/-- Step all sequential registers of `m` by one clock edge (`rst = true` triggers synchronous resets). -/
@[expose] def stepModuleRegs (m : RtlModule) (rst : Bool) (inputs regState : Nat → BitVec 64) : Nat → BitVec 64 :=
  let wireEnv := evalWireTable inputs regState m.wires
  m.regs.foldl (fun nextSt r =>
    let v := match r.resetKind with
      | .resetFree => evalRtlExpr inputs wireEnv regState r.nextExpr
      | .syncReset initVal => if rst then initVal else evalRtlExpr inputs wireEnv regState r.nextExpr
    fun i => if i == r.regIdx then v else nextSt i) regState

/-- Next value register `r` latches on a clock edge. -/
abbrev regNextValue (rst : Bool) (inputs wireEnv regState : Nat → BitVec 64) (r : RegSpec) : BitVec 64 :=
  match r.resetKind with
  | .resetFree => evalRtlExpr inputs wireEnv regState r.nextExpr
  | .syncReset initVal => if rst then initVal else evalRtlExpr inputs wireEnv regState r.nextExpr

/-- Compiled array-backed form of `stepModuleRegs` (`stepModuleRegs_eq_impl`, `@[csimp]`). -/
def stepModuleRegsImpl (m : RtlModule) (rst : Bool) (inputs regState : Nat → BitVec 64) : Nat → BitVec 64 :=
  let n := m.regs.foldl (fun k r => max k (r.regIdx + 1)) 0
  if n > 1000000 then stepModuleRegs m rst inputs regState
  else
    let wireEnv := evalWireTable inputs regState m.wires
    let vals := m.regs.foldl (fun (arr : Array (Option (BitVec 64))) r =>
      arr.set! r.regIdx (some (regNextValue rst inputs wireEnv regState r))) (Array.replicate n none)
    fun i => match vals.getD i none with | some v => v | none => regState i

theorem stepModuleRegs_eq_foldl_next (m : RtlModule) (rst : Bool) (inputs regState : Nat → BitVec 64) :
    stepModuleRegs m rst inputs regState =
      m.regs.foldl (fun nextSt r => fun i =>
        if i == r.regIdx then regNextValue rst inputs (evalWireTable inputs regState m.wires) regState r else nextSt i) regState := by
  unfold stepModuleRegs regNextValue; rfl

@[csimp] theorem stepModuleRegs_eq_impl : @stepModuleRegs = @stepModuleRegsImpl := by
  funext m rst inputs regState i; unfold stepModuleRegsImpl; split
  · rfl
  · rw [stepModuleRegs_eq_foldl_next]
    generalize evalWireTable inputs regState m.wires = wireEnv
    generalize hn : m.regs.foldl (fun k r => max k (r.regIdx + 1)) 0 = n
    have hBound : ∀ r ∈ m.regs, r.regIdx < n := fun r hr => by
      have := mem_le_foldl_max (fun r : RegSpec => r.regIdx + 1) m.regs 0 r hr; omega
    suffices ∀ (l : List RegSpec), (∀ r ∈ l, r.regIdx < n) →
        ∀ (arr : Array (Option (BitVec 64))) (st : Nat → BitVec 64), arr.size = n →
          (∀ i, (match arr.getD i none with | some v => v | none => regState i) = st i) →
          ∀ i, (l.foldl (fun nextSt r => fun i => if i == r.regIdx then regNextValue rst inputs wireEnv regState r else nextSt i) st) i =
            (match (l.foldl (fun (arr : Array (Option (BitVec 64))) r =>
              arr.set! r.regIdx (some (regNextValue rst inputs wireEnv regState r))) arr).getD i none with
              | some v => v | none => regState i) from
      this m.regs hBound _ _ (by simp) (fun i => by rw [array_getD_replicate]) i
    intro l; induction l with
    | nil => intro _ _ _ _ h i; exact (h i).symm
    | cons r rest ih =>
      intro hB arr st hSize hEq i; simp only [List.foldl_cons]
      apply ih (fun x hx => hB x (List.mem_cons_of_mem _ hx)) _ _ (by simp [hSize])
      intro j; rw [array_getD_set! _ _ _ _ _ (by rw [hSize]; exact hB r List.mem_cons_self)]
      by_cases h : j = r.regIdx
      · simp [h]
      · simp only [beq_iff_eq, h, ite_false]; exact hEq j

/-- Run an `RtlModule` over a trace of `(rst, inputs)` cycles, returning the final register state. -/
@[expose] def runModuleTrace (m : RtlModule) (initRegs : Nat → BitVec 64) (trace : List (Bool × (Nat → BitVec 64))) : Nat → BitVec 64 :=
  trace.foldl (fun st (rst, ins) => stepModuleRegs m rst ins st) initRegs

/-- Array-backed single clock edge (`stepRegsArr_getD`). -/
def stepRegsArr (m : RtlModule) (rst : Bool) (inputs init : Nat → BitVec 64) (st : Array (BitVec 64)) : Array (BitVec 64) :=
  let regState : Nat → BitVec 64 := fun i => st.getD i (init i)
  let wArr := evalWireTableArr inputs regState m.wires
  let wireEnv : Nat → BitVec 64 := fun i => wArr.getD i 0#64
  m.regs.foldl (fun arr r => arr.set! r.regIdx (regNextValue rst inputs wireEnv regState r)) st

/-- Compiled array-backed form of `runModuleTrace` (`runModuleTrace_eq_impl`, `@[csimp]`). -/
abbrev runModuleTraceImpl (m : RtlModule) (initRegs : Nat → BitVec 64) (trace : List (Bool × (Nat → BitVec 64))) : Nat → BitVec 64 :=
  let n := m.regs.foldl (fun k r => max k (r.regIdx + 1)) 0
  if n > 1000000 then runModuleTrace m initRegs trace
  else let fin := trace.foldl (fun st c => stepRegsArr m c.1 c.2 initRegs st) ((List.range n).toArray.map initRegs); fun i => fin.getD i (initRegs i)

theorem stepRegsArr_getD (m : RtlModule) (rst : Bool) (inputs init F : Nat → BitVec 64)
    (st : Array (BitVec 64)) (n : Nat) (hBound : ∀ r ∈ m.regs, r.regIdx < n)
    (hSize : st.size = n) (hEq : ∀ i, st.getD i (init i) = F i) :
    (stepRegsArr m rst inputs init st).size = n ∧
    ∀ i, (stepRegsArr m rst inputs init st).getD i (init i) = stepModuleRegs m rst inputs F i := by
  have hF : (fun i => st.getD i (init i)) = F := funext hEq
  have hW : (fun i => (evalWireTableArr inputs F m.wires).getD i 0#64) = evalWireTable inputs F m.wires :=
    funext (evalWireTableArr_getD inputs F m.wires)
  unfold stepRegsArr; simp only [hF, hW]; rw [stepModuleRegs_eq_foldl_next]
  generalize evalWireTable inputs F m.wires = wireEnv
  suffices ∀ (l : List RegSpec), (∀ r ∈ l, r.regIdx < n) →
      ∀ (arr : Array (BitVec 64)) (G : Nat → BitVec 64), arr.size = n → (∀ i, arr.getD i (init i) = G i) →
        (l.foldl (fun arr r => arr.set! r.regIdx (regNextValue rst inputs wireEnv F r)) arr).size = n ∧
        ∀ i, (l.foldl (fun arr r => arr.set! r.regIdx (regNextValue rst inputs wireEnv F r)) arr).getD i (init i) =
          (l.foldl (fun nextSt r => fun i => if i == r.regIdx then regNextValue rst inputs wireEnv F r else nextSt i) G) i from
    this m.regs hBound st F hSize hEq
  intro l; induction l with
  | nil => intro _ arr _ hS h; exact ⟨hS, h⟩
  | cons r rest ih =>
    intro hB arr G hS hE; simp only [List.foldl_cons]
    apply ih (fun x hx => hB x (List.mem_cons_of_mem _ hx)) _ _ (by simp [hS])
    intro j; rw [array_getD_set! _ _ _ _ _ (by rw [hS]; exact hB r List.mem_cons_self)]
    by_cases h : j = r.regIdx <;> simp [h, hE]

@[csimp] theorem runModuleTrace_eq_impl : @runModuleTrace = @runModuleTraceImpl := by
  funext m initRegs trace i; unfold runModuleTraceImpl; split
  · rfl
  · generalize hn : m.regs.foldl (fun k r => max k (r.regIdx + 1)) 0 = n
    have hBound : ∀ r ∈ m.regs, r.regIdx < n := fun r hr => by
      have := mem_le_foldl_max (fun r : RegSpec => r.regIdx + 1) m.regs 0 r hr; omega
    unfold runModuleTrace
    suffices ∀ (tr : List (Bool × (Nat → BitVec 64))) (arr : Array (BitVec 64)) (F : Nat → BitVec 64),
        arr.size = n → (∀ i, arr.getD i (initRegs i) = F i) →
        (tr.foldl (fun st c => stepRegsArr m c.1 c.2 initRegs st) arr).getD i (initRegs i) =
          tr.foldl (fun st (rst, ins) => stepModuleRegs m rst ins st) F i from
      (this trace _ initRegs (by simp) (fun j => by by_cases h : j < n <;> simp [Array.getD_eq_getD_getElem?, h])).symm
    intro tr; induction tr with
    | nil => intro _ _ _ h; exact h i
    | cons c rest ih =>
      intro arr F hS hE; simp only [List.foldl_cons]
      obtain ⟨hS', hE'⟩ := stepRegsArr_getD m c.1 c.2 initRegs F arr n hBound hS hE
      exact ih _ _ hS' hE'

/-! ## 4b. Port Widths, Two-Flop Synchronizer Chains & the Emission Gate (`checkRtlModuleW`) -/

/-- Emitted width of input `idx` (64 when `inputWidths` is empty). -/
abbrev inputWidth (m : RtlModule) (idx : Nat) : Nat := m.inputWidths.getD idx 64

/-- A port width is 1..64. -/
abbrev validWidth (w : Nat) : Bool := 0 < w && w ≤ 64

/-- Port widths are in range and `inputWidths` is either empty or one entry per input. -/
abbrev checkPortWidths (m : RtlModule) : Bool :=
  (m.inputWidths.isEmpty || m.inputWidths.length == m.inputNames.length) &&
  m.inputWidths.all validWidth && m.outputs.all (fun o => validWidth o.width)

theorem truncToWidth_width64 (v : BitVec 64) : truncToWidth 64 v = v := by
  have h : BitVec.allOnes 64 >>> (64 - 64) = BitVec.allOnes 64 := by decide
  rw [truncToWidth, h, BitVec.and_allOnes]

/-- Combinational outputs as seen at the emitted ports: each output truncated to its width. -/
abbrev evalModuleOutputsW (m : RtlModule) (inputs regState : Nat → BitVec 64) : List (String × BitVec 64) :=
  let wireEnv := evalWireTable inputs regState m.wires
  m.outputs.map fun o => (o.name, truncToWidth o.width (evalRtlExpr inputs wireEnv regState o.expr))

theorem evalModuleOutputsW_eq_of_all64 (m : RtlModule) (inputs regState : Nat → BitVec 64)
    (h : m.outputs.all (fun o => o.width == 64) = true) :
    evalModuleOutputsW m inputs regState = evalModuleOutputs m inputs regState := by
  simp only [evalModuleOutputsW, evalModuleOutputs]; rw [List.all_eq_true] at h
  apply List.map_congr_left; intro o ho
  have hw : o.width = 64 := by simpa using h o ho
  simp [hw, truncToWidth_width64]

/-! ## 4c. Widths as a Checked Refinement of the 64-bit Carrier (`inferWidth`, `checkWidths`) -/

/-- Declared widths of a module's inputs, wires and registers, by index. -/
structure WidthEnv where
  input : Nat → Nat
  wire  : Nat → Nat
  reg   : Nat → Nat

/-- Bit length of a constant (at least 1). -/
abbrev constWidth (v : BitVec 64) : Nat := v.toNat.log2 + 1

/-- Width bound of an ALU result from its operands' bounds `wa`, `wb`. -/
abbrev aluWidth (op : RtlAluOp) (rhs : RtlExpr) (wa wb : Nat) : Nat :=
  match op with
  | .add => min 64 (max wa wb + 1) | .sub => 64 | .mul => min 64 (wa + wb)
  | .bitAnd => min wa wb | .bitOr => max wa wb | .bitXor => max wa wb
  | .shl => match rhs with | .const k => min 64 (wa + k.toNat % 64) | _ => 64
  | .lshr => wa | .ashr => if wa < 64 then wa else 64
  | .eq | .ult | .slt => 1 | .qmul32 => 64

/-- Width of a width operator's result from its operand's bound `wa`, or the refusal reason. -/
abbrev widthOpWidth : RtlWidthOp → Nat → Except String Nat
  | .slice hi lo, wa => if lo ≤ hi ∧ hi < wa ∧ hi < 64 then .ok (hi + 1 - lo) else .error s!"slice [{hi}:{lo}] is outside its {wa}-bit source"
  | .zext w, wa => if wa ≤ w ∧ w ≤ 64 then .ok w else .error s!"zext to {w} bits of a {wa}-bit value"
  | .sext f t, _ => if 0 < f ∧ f ≤ t ∧ t ≤ 64 then .ok t else .error s!"sext from {f} to {t} bits (needs 0 < from <= to <= 64)"
  | .trunc w, wa => if 0 < w ∧ w ≤ 64 then .ok (min w wa) else .error s!"trunc to {w} bits (needs 1..64)"

/-- Width bound of an expression, or the first width operator it refuses. -/
@[expose] def inferWidthE (env : WidthEnv) : RtlExpr → Except String Nat
  | .const v => .ok (constWidth v) | .inputPort idx => .ok (env.input idx)
  | .wireRef idx => .ok (env.wire idx) | .regRead idx => .ok (env.reg idx)
  | .alu op a b =>
    match inferWidthE env a, inferWidthE env b with
    | .ok wa, .ok wb => .ok (aluWidth op b wa wb) | .error e, _ => .error e | _, .error e => .error e
  | .mux c t f =>
    match inferWidthE env c, inferWidthE env t, inferWidthE env f with
    | .ok _, .ok wt, .ok wf => .ok (max wt wf) | .error e, _, _ => .error e | _, .error e, _ => .error e | _, _, .error e => .error e
  | .bitNot a => match inferWidthE env a with | .ok _ => .ok 64 | .error e => .error e
  | .resize op a => match inferWidthE env a with | .ok wa => widthOpWidth op wa | .error e => .error e

/-- `inferWidthE` without the reason. -/
abbrev inferWidth (env : WidthEnv) (e : RtlExpr) : Option Nat := (inferWidthE env e).toOption

theorem truncMask_toNat : ∀ w, w < 65 → (BitVec.allOnes 64 >>> (64 - w)).toNat = 2 ^ w - 1 := by decide

theorem truncToWidth_toNat (w : Nat) (hw : w ≤ 64) (v : BitVec 64) :
    (truncToWidth w v).toNat = v.toNat % 2 ^ w := by
  rw [truncToWidth, BitVec.toNat_and, truncMask_toNat w (by omega), Nat.and_two_pow_sub_one_eq_mod]

theorem truncToWidth_lt (w : Nat) (hw : w ≤ 64) (v : BitVec 64) : (truncToWidth w v).toNat < 2 ^ w := by
  rw [truncToWidth_toNat w hw]; exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem truncToWidth_le (w : Nat) (v : BitVec 64) : (truncToWidth w v).toNat ≤ v.toNat := by
  rw [truncToWidth, BitVec.toNat_and]; exact Nat.and_le_left

theorem truncToWidth_of_lt (w : Nat) (hw : w ≤ 64) (v : BitVec 64) (h : v.toNat < 2 ^ w) :
    truncToWidth w v = v := by
  apply BitVec.eq_of_toNat_eq; rw [truncToWidth_toNat w hw, Nat.mod_eq_of_lt h]

private theorem lt_two_pow_mono {x a b : Nat} (h : x < 2 ^ a) (hab : a ≤ b) : x < 2 ^ b :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hab)

private theorem lt_two_pow_min64 (x : BitVec 64) (n : Nat) (h : x.toNat < 2 ^ n) : x.toNat < 2 ^ (min 64 n) := by
  rcases Nat.le_total 64 n with h64 | h64
  · rw [Nat.min_eq_left h64]; exact x.isLt
  · rw [Nat.min_eq_right h64]; exact h

private theorem ite_one_zero_lt (c : Prop) [Decidable c] : (if c then 1#64 else 0#64).toNat < 2 ^ 1 := by split <;> decide

theorem evalAluOp_lt_aluWidth (op : RtlAluOp) (rhs : RtlExpr) (a b : BitVec 64) (wa wb : Nat)
    (ha : a.toNat < 2 ^ wa) (hb : b.toNat < 2 ^ wb) (hrhs : ∀ k, rhs = .const k → b = k) :
    (evalAluOp op a b).toNat < 2 ^ aluWidth op rhs wa wb := by
  cases op with
  | add =>
    apply lt_two_pow_min64; simp only [evalAluOp]; rw [BitVec.toNat_add]
    have h1 := lt_two_pow_mono ha (Nat.le_max_left wa wb); have h2 := lt_two_pow_mono hb (Nat.le_max_right wa wb)
    have := Nat.mod_le (a.toNat + b.toNat) (2 ^ 64); rw [Nat.pow_succ]; omega
  | sub => exact (evalAluOp .sub a b).isLt
  | mul =>
    apply lt_two_pow_min64; simp only [evalAluOp]; rw [BitVec.toNat_mul, Nat.pow_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (Nat.two_pow_pos wb))
  | bitAnd =>
    simp only [evalAluOp, aluWidth, BitVec.toNat_and]
    rcases Nat.le_total wa wb with h | h
    · rw [Nat.min_eq_left h, Nat.and_comm]; exact Nat.and_lt_two_pow _ ha
    · rw [Nat.min_eq_right h]; exact Nat.and_lt_two_pow _ hb
  | bitOr =>
    simp only [evalAluOp, aluWidth, BitVec.toNat_or]
    exact Nat.or_lt_two_pow (lt_two_pow_mono ha (Nat.le_max_left _ _)) (lt_two_pow_mono hb (Nat.le_max_right _ _))
  | bitXor =>
    simp only [evalAluOp, aluWidth, BitVec.toNat_xor]
    exact Nat.xor_lt_two_pow (lt_two_pow_mono ha (Nat.le_max_left _ _)) (lt_two_pow_mono hb (Nat.le_max_right _ _))
  | shl =>
    cases rhs with
    | const k =>
      have hk := hrhs k rfl; subst hk
      apply lt_two_pow_min64; simp only [evalAluOp, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_add]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos _))
    | _ => exact (evalAluOp .shl a b).isLt
  | lshr => simp only [evalAluOp, aluWidth, BitVec.toNat_ushiftRight]; exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
  | ashr =>
    simp only [aluWidth]; split
    · rename_i hw
      have hmsb : a.msb = false := by
        rw [BitVec.msb_eq_decide]; have := lt_two_pow_mono ha (show wa ≤ 63 by omega)
        simp only [decide_eq_false_iff_not, Nat.not_le]; exact this
      simp only [evalAluOp, BitVec.sshiftRight_eq_of_msb_false hmsb, BitVec.toNat_ushiftRight]
      exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
    · exact (evalAluOp .ashr a b).isLt
  | eq | ult | slt => exact ite_one_zero_lt _
  | qmul32 => exact (evalAluOp .qmul32 a b).isLt

theorem evalWidthOp_lt (op : RtlWidthOp) (a : BitVec 64) (wa w : Nat)
    (ha : a.toNat < 2 ^ wa) (h : widthOpWidth op wa = .ok w) : (evalWidthOp op a).toNat < 2 ^ w := by
  cases op with
  | slice hi lo =>
    simp only [widthOpWidth] at h; split at h
    · rename_i hc; cases h; exact truncToWidth_lt _ (by omega) _
    · cases h
  | zext w' =>
    simp only [widthOpWidth] at h; split at h
    · rename_i hc; cases h; exact lt_two_pow_mono ha hc.1
    · cases h
  | sext f t =>
    simp only [widthOpWidth] at h; split at h
    · cases h; simp only [evalWidthOp, BitVec.toNat_setWidth]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)
    · cases h
  | trunc w' =>
    simp only [widthOpWidth] at h; split at h
    · rename_i hc; cases h; simp only [evalWidthOp]
      rcases Nat.le_total w' wa with hle | hle
      · rw [Nat.min_eq_left hle]; exact truncToWidth_lt _ hc.2 _
      · rw [Nat.min_eq_right hle]; exact Nat.lt_of_le_of_lt (truncToWidth_le _ _) ha
    · cases h

/-- **Width soundness:** if inputs, wires, and registers fit declared widths, `evalRtlExpr < 2^w`. -/
theorem evalRtlExpr_lt_of_inferWidthE (env : WidthEnv) (inputs wires regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ env.input i) (hW : ∀ i, (wires i).toNat < 2 ^ env.wire i)
    (hR : ∀ i, (regs i).toNat < 2 ^ env.reg i) :
    ∀ (e : RtlExpr) (w : Nat), inferWidthE env e = .ok w → (evalRtlExpr inputs wires regs e).toNat < 2 ^ w := by
  intro e; induction e with
  | const _ => intro w h; simp only [inferWidthE, Except.ok.injEq] at h; subst h; exact Nat.lt_log2_self
  | inputPort idx => intro w h; simp only [inferWidthE, Except.ok.injEq] at h; subst h; exact hIn idx
  | wireRef idx => intro w h; simp only [inferWidthE, Except.ok.injEq] at h; subst h; exact hW idx
  | regRead idx => intro w h; simp only [inferWidthE, Except.ok.injEq] at h; subst h; exact hR idx
  | alu op a b iha ihb =>
    intro w h; simp only [inferWidthE] at h
    cases ha : inferWidthE env a <;> cases hb : inferWidthE env b <;> simp [ha, hb] at h
    rename_i wa wb; subst h; exact evalAluOp_lt_aluWidth op b _ _ wa wb (iha wa ha) (ihb wb hb) (fun k hk => by subst hk; rfl)
  | mux c t f _ iht ihf =>
    intro w h; simp only [inferWidthE] at h
    cases hc : inferWidthE env c <;> cases ht : inferWidthE env t <;> cases hf : inferWidthE env f <;> simp [hc, ht, hf] at h
    rename_i _ wt wf; subst h; simp only [evalRtlExpr]; split
    · exact lt_two_pow_mono (iht wt ht) (Nat.le_max_left _ _)
    · exact lt_two_pow_mono (ihf wf hf) (Nat.le_max_right _ _)
  | bitNot a _ =>
    intro w h; simp only [inferWidthE] at h; cases ha : inferWidthE env a <;> simp [ha] at h
    subst h; exact (evalRtlExpr inputs wires regs (.bitNot a)).isLt
  | resize op a iha =>
    intro w h; simp only [inferWidthE] at h; cases ha : inferWidthE env a <;> simp [ha] at h
    rename_i wa; exact evalWidthOp_lt op _ wa w (iha wa ha) h

theorem evalRtlExpr_lt_of_inferWidth (env : WidthEnv) (inputs wires regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ env.input i) (hW : ∀ i, (wires i).toNat < 2 ^ env.wire i)
    (hR : ∀ i, (regs i).toNat < 2 ^ env.reg i) (e : RtlExpr) (w : Nat) (h : inferWidth env e = some w) :
    (evalRtlExpr inputs wires regs e).toNat < 2 ^ w := by
  apply evalRtlExpr_lt_of_inferWidthE env inputs wires regs hIn hW hR e w
  unfold inferWidth at h; cases he : inferWidthE env e <;> simp [he, Except.toOption] at h; subst h; rfl

abbrev wireWidthOf (m : RtlModule) (idx : Nat) : Nat := ((m.wires.find? (·.wireIdx == idx)).map (·.width)).getD 64
abbrev regWidthOf (m : RtlModule) (idx : Nat) : Nat := ((m.regs.find? (·.regIdx == idx)).map (·.width)).getD 64
abbrev moduleWidthEnv (m : RtlModule) : WidthEnv := ⟨inputWidth m, wireWidthOf m, regWidthOf m⟩

abbrev fitErrors (env : WidthEnv) (what : String) (decl : Nat) (e : RtlExpr) : List String :=
  match inferWidthE env e with
  | .error msg => [s!"{what}: {msg}"]
  | .ok w => if w ≤ decl then [] else [s!"{what} is {decl} bits wide but is driven by a {w}-bit expression (narrow it with trunc or slice)"]

abbrev declErrors (what : String) (w : Nat) : List String :=
  if validWidth w then [] else [s!"{what} declares width {w}; widths are 1..64"]

abbrev widthErrors (m : RtlModule) : List String :=
  let env := moduleWidthEnv m
  (List.range m.inputNames.length).flatMap (fun i => declErrors s!"input port `{m.inputNames.getD i s!"in_{i}"}`" (inputWidth m i)) ++
  m.wires.flatMap (fun a => declErrors s!"wire `{a.name}`" a.width ++ fitErrors env s!"wire `{a.name}`" (wireWidthOf m a.wireIdx) a.expr) ++
  m.regs.flatMap (fun r => declErrors s!"register `{r.name}`" r.width ++ fitErrors env s!"register `{r.name}`" (regWidthOf m r.regIdx) r.nextExpr ++
    match r.resetKind with
    | .resetFree => []
    | .syncReset v => if constWidth v ≤ regWidthOf m r.regIdx then [] else [s!"register `{r.name}` resets to {v.toNat}, which does not fit its {regWidthOf m r.regIdx} bits"]) ++
  m.outputs.flatMap (fun o => declErrors s!"output port `{o.name}`" o.width ++ fitErrors env s!"output port `{o.name}`" o.width o.expr)

abbrev checkWidths (m : RtlModule) : Bool := (widthErrors m).isEmpty

theorem fitErrors_nil {env : WidthEnv} {what : String} {decl : Nat} {e : RtlExpr}
    (h : fitErrors env what decl e = []) : ∃ w, inferWidthE env e = .ok w ∧ w ≤ decl := by
  unfold fitErrors at h; cases he : inferWidthE env e with
  | error msg => simp [he] at h
  | ok w =>
    simp only [he] at h; split at h
    · exact ⟨w, rfl, by assumption⟩
    · simp at h

private theorem flatMap_nil_mem {α β : Type} {f : α → List β} {l : List α} {x : α}
    (h : l.flatMap f = []) (hx : x ∈ l) : f x = [] := List.flatMap_eq_nil_iff.mp h x hx

theorem checkWidths_parts (m : RtlModule) (h : checkWidths m = true) :
    (∀ a ∈ m.wires, fitErrors (moduleWidthEnv m) s!"wire `{a.name}`" (wireWidthOf m a.wireIdx) a.expr = []) ∧
    (∀ r ∈ m.regs, fitErrors (moduleWidthEnv m) s!"register `{r.name}`" (regWidthOf m r.regIdx) r.nextExpr = [] ∧
      ∀ v, r.resetKind = .syncReset v → constWidth v ≤ regWidthOf m r.regIdx) ∧
    (∀ o ∈ m.outputs, validWidth o.width = true ∧
      fitErrors (moduleWidthEnv m) s!"output port `{o.name}`" o.width o.expr = []) := by
  unfold checkWidths widthErrors at h; simp only [List.isEmpty_iff, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨_, hw⟩, hr⟩, ho⟩ := h; refine ⟨fun a ha => ?_, fun r hr' => ?_, fun o ho' => ?_⟩
  · have := flatMap_nil_mem hw ha; simp only [List.append_eq_nil_iff] at this; exact this.2
  · have := flatMap_nil_mem hr hr'; simp only [List.append_eq_nil_iff] at this
    refine ⟨this.1.2, fun v hv => ?_⟩; have h3 := this.2; rw [hv] at h3; simp only at h3
    split at h3
    · assumption
    · simp at h3
  · have := flatMap_nil_mem ho ho'; simp only [List.append_eq_nil_iff] at this
    refine ⟨?_, this.2⟩; have h1 := this.1; unfold declErrors at h1
    split at h1
    · assumption
    · simp at h1

theorem evalWireTable_lt (m : RtlModule) (inputs regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ inputWidth m i) (hR : ∀ i, (regs i).toNat < 2 ^ regWidthOf m i)
    (hChk : checkWidths m = true) : ∀ i, (evalWireTable inputs regs m.wires i).toNat < 2 ^ wireWidthOf m i := by
  have hWires := (checkWidths_parts m hChk).1; unfold evalWireTable
  suffices ∀ (l : List WireAssign), (∀ a ∈ l, a ∈ m.wires) →
      ∀ (env : Nat → BitVec 64), (∀ i, (env i).toNat < 2 ^ wireWidthOf m i) →
      ∀ i, ((l.foldl (fun env a => let v := evalRtlExpr inputs env regs a.expr; fun i => if i == a.wireIdx then v else env i) env) i).toNat < 2 ^ wireWidthOf m i by
    exact this m.wires (fun _ h => h) _ (fun i => by simpa using Nat.two_pow_pos (wireWidthOf m i))
  intro l; induction l with
  | nil => intro _ env hEnv; exact hEnv
  | cons a rest ih =>
    intro hSub env hEnv; simp only [List.foldl_cons]
    apply ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx)); intro i
    obtain ⟨w, hw, hle⟩ := fitErrors_nil (hWires a (hSub a List.mem_cons_self))
    have hv := evalRtlExpr_lt_of_inferWidthE (moduleWidthEnv m) inputs env regs hIn hEnv hR a.expr w hw
    by_cases hi : i = a.wireIdx
    · subst hi; simp only [beq_self_eq_true, ite_true]; exact lt_two_pow_mono hv hle
    · simp only [beq_iff_eq, hi, ite_false]; exact hEnv i

theorem stepModuleRegs_lt (m : RtlModule) (rst : Bool) (inputs regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ inputWidth m i) (hR : ∀ i, (regs i).toNat < 2 ^ regWidthOf m i)
    (hChk : checkWidths m = true) : ∀ i, (stepModuleRegs m rst inputs regs i).toNat < 2 ^ regWidthOf m i := by
  have hRegs := (checkWidths_parts m hChk).2.1; have hWire := evalWireTable_lt m inputs regs hIn hR hChk
  unfold stepModuleRegs
  suffices ∀ (l : List RegSpec), (∀ r ∈ l, r ∈ m.regs) →
      ∀ (st : Nat → BitVec 64), (∀ i, (st i).toNat < 2 ^ regWidthOf m i) →
      ∀ i, ((l.foldl (fun nextSt r =>
        let v := match r.resetKind with
          | .resetFree => evalRtlExpr inputs (evalWireTable inputs regs m.wires) regs r.nextExpr
          | .syncReset initVal => if rst then initVal else evalRtlExpr inputs (evalWireTable inputs regs m.wires) regs r.nextExpr
        fun i => if i == r.regIdx then v else nextSt i) st) i).toNat < 2 ^ regWidthOf m i by
    exact this m.regs (fun _ h => h) regs hR
  intro l; induction l with
  | nil => intro _ st hSt; exact hSt
  | cons r rest ih =>
    intro hSub st hSt; simp only [List.foldl_cons]
    apply ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx)); intro i
    have hr := hRegs r (hSub r List.mem_cons_self)
    obtain ⟨w, hw, hle⟩ := fitErrors_nil hr.1
    have hNext := lt_two_pow_mono (evalRtlExpr_lt_of_inferWidthE (moduleWidthEnv m) inputs _ regs hIn hWire hR r.nextExpr w hw) hle
    by_cases hi : i = r.regIdx
    · subst hi; simp only [beq_self_eq_true, ite_true]
      cases hk : r.resetKind with
      | resetFree => exact hNext
      | syncReset v =>
        cases rst
        · exact hNext
        · simp only [ite_true]; exact lt_two_pow_mono Nat.lt_log2_self (hr.2 v hk)
    · simp only [beq_iff_eq, hi, ite_false]; exact hSt i

theorem runModuleTrace_lt (m : RtlModule) (hChk : checkWidths m = true)
    (trace : List (Bool × (Nat → BitVec 64))) (hIn : ∀ c ∈ trace, ∀ i, (c.2 i).toNat < 2 ^ inputWidth m i) :
    ∀ (init : Nat → BitVec 64), (∀ i, (init i).toNat < 2 ^ regWidthOf m i) →
      ∀ i, (runModuleTrace m init trace i).toNat < 2 ^ regWidthOf m i := by
  unfold runModuleTrace; induction trace with
  | nil => intro _ h; exact h
  | cons c rest ih =>
    intro init hInit; simp only [List.foldl_cons]
    exact ih (fun c' hc' => hIn c' (List.mem_cons_of_mem _ hc')) _
      (stepModuleRegs_lt m c.1 c.2 init (hIn c List.mem_cons_self) hInit hChk)

theorem evalModuleOutputsW_eq_of_checkWidths (m : RtlModule) (inputs regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ inputWidth m i) (hR : ∀ i, (regs i).toNat < 2 ^ regWidthOf m i)
    (hChk : checkWidths m = true) : evalModuleOutputsW m inputs regs = evalModuleOutputs m inputs regs := by
  have hOuts := (checkWidths_parts m hChk).2.2; have hWire := evalWireTable_lt m inputs regs hIn hR hChk
  simp only [evalModuleOutputsW, evalModuleOutputs]; apply List.map_congr_left; intro o ho
  obtain ⟨hv, hf⟩ := hOuts o ho; obtain ⟨w, hw, hle⟩ := fitErrors_nil hf
  have hlt := evalRtlExpr_lt_of_inferWidthE (moduleWidthEnv m) inputs _ regs hIn hWire hR o.expr w hw
  have h64 : o.width ≤ 64 := by unfold validWidth at hv; simp only [Bool.and_eq_true, decide_eq_true_eq] at hv; exact hv.2
  rw [truncToWidth_of_lt o.width h64 _ (lt_two_pow_mono hlt hle)]

/-- Registers read by `r.nextExpr` (through `wires`) that live in a different clock domain. -/
abbrev crossDomainSources (regs : List RegSpec) (wires : List WireAssign) (r : RegSpec) : List Nat :=
  (exprReadRegs r.nextExpr wires).filter fun src =>
    match lookupRegDomain regs src with | some d => d != r.domain | none => true

/-- First-stage synchronizer two-flop chain check. -/
abbrev checkSyncChain (regs : List RegSpec) (wires : List WireAssign) (outputs : List OutputPort) (s1 : RegSpec) : Bool :=
  (crossDomainSources regs wires s1).isEmpty ||
  (regs.any (fun s2 => s2.isSynchronizer && s2.domain == s1.domain && s2.regIdx != s1.regIdx && s2.nextExpr == .regRead s1.regIdx) &&
   regs.all (fun r => r.isSynchronizer || !(exprReadRegs r.nextExpr wires).contains s1.regIdx) &&
   wires.all (fun w => !(exprReadRegsAndWires w.expr).1.contains s1.regIdx) &&
   outputs.all (fun o => !(exprReadRegs o.expr wires).contains s1.regIdx))

abbrev checkCdcTwoFlop (m : RtlModule) : Bool :=
  m.regs.all fun r => !r.isSynchronizer || checkSyncChain m.regs m.wires m.outputs r

/-- Emission gate: `checkRtlModule`, transitive CDC, port widths, 2-FF chains, and `checkWidths`. -/
abbrev checkRtlModuleW (m : RtlModule) : Bool :=
  checkRtlModule m && checkModuleCdc m.regs m.wires && checkPortWidths m && checkCdcTwoFlop m && checkWidths m

theorem checkCdcTwoFlop_second_stage (m : RtlModule) (s1 : RegSpec)
    (hOk : checkCdcTwoFlop m = true) (hMem : s1 ∈ m.regs) (hSync : s1.isSynchronizer = true)
    (hCross : (crossDomainSources m.regs m.wires s1).isEmpty = false) :
    ∃ s2 ∈ m.regs, s2.isSynchronizer = true ∧ s2.domain = s1.domain ∧ s2.nextExpr = .regRead s1.regIdx := by
  unfold checkCdcTwoFlop at hOk; rw [List.all_eq_true] at hOk
  have h := hOk s1 hMem; rw [hSync] at h; simp only [Bool.not_true, Bool.false_or] at h
  unfold checkSyncChain at h; rw [hCross] at h; simp only [Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hAny, _⟩, _⟩, _⟩ := h; rw [List.any_eq_true] at hAny; obtain ⟨s2, hs2, hp⟩ := hAny
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  exact ⟨s2, hs2, hp.1.1.1, hp.1.1.2, hp.2⟩

abbrev moduleDomains (m : RtlModule) : List ClkDomain :=
  m.regs.foldl (fun acc r => if acc.contains r.domain then acc else acc ++ [r.domain]) []

/-! ## 4d. Clock Domains in the Cycle Semantics (`stepModuleDomain`) -/

abbrev moduleClockPorts (m : RtlModule) : List (ClkDomain × String × String) :=
  let ds := moduleDomains m
  if ds.length > 1 then ds.map fun d => (d, s!"clk_{d.portSuffix}", s!"rst_{d.portSuffix}")
  else match ds with | d :: _ => [(d, "clk", "rst")] | [] => [(.coreClk, "clk", "rst")]

abbrev stepModuleDomain (m : RtlModule) (d : ClkDomain) (rst : Bool) (inputs regState : Nat → BitVec 64) : Nat → BitVec 64 :=
  stepModuleRegs { m with regs := m.regs.filter (·.domain == d) } rst inputs regState

theorem stepModuleDomain_eq_of_single (m : RtlModule) (d : ClkDomain)
    (h : m.regs.all (·.domain == d) = true) (rst : Bool) (inputs regState : Nat → BitVec 64) :
    stepModuleDomain m d rst inputs regState = stepModuleRegs m rst inputs regState := by
  have hf : m.regs.filter (·.domain == d) = m.regs := List.filter_eq_self.mpr (by simpa using h)
  unfold stepModuleDomain; rw [hf]

theorem stepModuleDomain_other_holds (m : RtlModule) (d : ClkDomain) (rst : Bool)
    (inputs regState : Nat → BitVec 64) (i : Nat) (hi : ∀ r ∈ m.regs, r.domain = d → r.regIdx ≠ i) :
    stepModuleDomain m d rst inputs regState i = regState i := by
  unfold stepModuleDomain stepModuleRegs; simp only
  generalize evalWireTable inputs regState m.wires = wenv
  suffices ∀ (l : List RegSpec), (∀ r ∈ l, r.regIdx ≠ i) → ∀ (st : Nat → BitVec 64), st i = regState i →
      (l.foldl (fun nextSt r =>
        let v := match r.resetKind with
          | .resetFree => evalRtlExpr inputs wenv regState r.nextExpr
          | .syncReset initVal => if rst then initVal else evalRtlExpr inputs wenv regState r.nextExpr
        fun j => if j == r.regIdx then v else nextSt j) st) i = regState i by
    apply this _ (fun r hr => by rw [List.mem_filter] at hr; exact hi r hr.1 (by simpa using hr.2)) _ rfl
  intro l; induction l with
  | nil => intro _ _ h; exact h
  | cons r rest ih =>
    intro hl st hst; simp only [List.foldl_cons]
    apply ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    have hne : (i == r.regIdx) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hl r List.mem_cons_self h.symm
    simp only [hne]; exact hst

theorem evalRtlExpr_regs_locality (inputs wires st1 st2 : Nat → BitVec 64) :
    ∀ (e : RtlExpr), (∀ i ∈ (exprReadRegsAndWires e).1, st1 i = st2 i) →
      evalRtlExpr inputs wires st1 e = evalRtlExpr inputs wires st2 e := by
  intro e; induction e with
  | const _ | inputPort _ | wireRef _ => intro _; rfl
  | regRead idx => intro h; simp only [exprReadRegsAndWires, List.mem_singleton, forall_eq] at h; simp only [evalRtlExpr, h]
  | alu _ _ _ iha ihb =>
    intro h; simp only [exprReadRegsAndWires, List.mem_append] at h
    simp only [evalRtlExpr, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi))]
  | mux _ _ _ ihc iht ihf =>
    intro h; simp only [exprReadRegsAndWires, List.mem_append] at h
    simp only [evalRtlExpr, ihc (fun i hi => h i (Or.inl (Or.inl hi))), iht (fun i hi => h i (Or.inl (Or.inr hi))), ihf (fun i hi => h i (Or.inr hi))]
  | bitNot _ iha => intro h; simp only [exprReadRegsAndWires] at h; simp only [evalRtlExpr, iha h]
  | resize _ _ iha => intro h; simp only [exprReadRegsAndWires] at h; simp only [evalRtlExpr, iha h]

theorem stepDomain_nonSync_reads_own_domain (m : RtlModule) (r : RegSpec)
    (hCdc : checkRegCdc m.regs r = true) (hNoSync : r.isSynchronizer = false)
    (inputs wires st1 st2 : Nat → BitVec 64) (hAgree : ∀ i, lookupRegDomain m.regs i = some r.domain → st1 i = st2 i) :
    evalRtlExpr inputs wires st1 r.nextExpr = evalRtlExpr inputs wires st2 r.nextExpr := by
  apply evalRtlExpr_regs_locality; intro i hi
  have hMem : i ∈ exprReadRegs r.nextExpr := by unfold exprReadRegs; simpa using hi
  have hSome : ∃ dom, lookupRegDomain m.regs i = some dom := by
    have h := hCdc; unfold checkRegCdc at h; rw [List.all_eq_true] at h
    have hi' := h i hMem
    cases hl : lookupRegDomain m.regs i with | none => rw [hl] at hi'; cases hi' | some dom => exact ⟨dom, rfl⟩
  obtain ⟨dom, hDom⟩ := hSome
  exact hAgree i (cdcSafe_no_unsynchronized_crossing m.regs r i dom hCdc hNoSync hMem hDom ▸ hDom)

/-! ## 5. AST-Driven SystemVerilog-2012 Emitter (`emitModuleSV`) -/

abbrev emitAluOpSV : RtlAluOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .shl => "<<" | .lshr => ">>" | .ashr => ">>>" | .eq => "==" | .ult => "<" | .slt => "<s" | .qmul32 => "*q32"

abbrev svMask (w : Nat) : String := s!"64'd{2 ^ (min w 64) - 1}"

@[expose] def emitExprSV (inNames regNames : List String) (wireName : Nat → String := fun i => s!"w_{i}") : RtlExpr → String
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
  | .resize (.slice hi lo) a => s!"(({emitExprSV inNames regNames wireName a} >> 64'd{lo}) & {svMask (hi + 1 - lo)})"
  | .resize (.zext _) a => emitExprSV inNames regNames wireName a
  | .resize (.sext f t) a => s!"64'($unsigned({t}'($signed({f}'({emitExprSV inNames regNames wireName a})))))"
  | .resize (.trunc w) a => s!"({emitExprSV inNames regNames wireName a} & {svMask w})"

abbrev inputExprsSV (m : RtlModule) : List String :=
  (List.range m.inputNames.length).map fun i =>
    let n := m.inputNames.getD i s!"in_{i}"; if inputWidth m i == 64 then n else s!"64'({n})"

abbrev readSV (w : Nat) (name : String) : String := if w == 64 then name else s!"64'({name})"
abbrev storeSV (w : Nat) (rhs : String) : String := if w == 64 then rhs else s!"{w}'({rhs})"
abbrev rangeSV (w : Nat) : String := s!"[{w - 1}:0]"

abbrev emitDomainBlocksSV (inExprs regNames : List String) (regsD : List RegSpec)
    (clkName rstName : String) (wireName : Nat → String := fun i => s!"w_{i}") : String :=
  let resetFreeRegs := regsD.filter fun r => match r.resetKind with | .resetFree => true | .syncReset _ => false
  let syncResetRegs := regsD.filter fun r => match r.resetKind with | .resetFree => false | .syncReset _ => true
  let rfBlock := if resetFreeRegs.isEmpty then "" else
    let assigns := resetFreeRegs.map fun r => s!"    {r.name} <= {storeSV r.width (emitExprSV inExprs regNames wireName r.nextExpr)};"
    s!"  // Reset-free datapath registers\n  always_ff @(posedge {clkName}) begin\n" ++ String.intercalate "\n" assigns ++ "\n  end\n"
  let srBlock := if syncResetRegs.isEmpty then "" else
    let rstAssigns := syncResetRegs.map fun r =>
      let initV := match r.resetKind with | .syncReset v => v.toNat | .resetFree => 0
      s!"      {r.name} <= {r.width}'d{initV};"
    let stepAssigns := syncResetRegs.map fun r => s!"      {r.name} <= {storeSV r.width (emitExprSV inExprs regNames wireName r.nextExpr)};"
    s!"  // Synchronous-reset control registers\n  always_ff @(posedge {clkName}) begin\n    if ({rstName}) begin\n" ++
      String.intercalate "\n" rstAssigns ++ "\n    end else begin\n" ++ String.intercalate "\n" stepAssigns ++ "\n    end\n  end\n"
  rfBlock ++ srBlock

/-- Emit a complete, synthesizable SystemVerilog-2012 module directly from an `RtlModule` AST. -/
abbrev emitModuleSV (m : RtlModule) : String :=
  let regNames := m.regs.map fun r => readSV r.width r.name
  let wireName (i : Nat) : String := readSV (wireWidthOf m i) s!"w_{i}"
  let inExprs := inputExprsSV m
  let domains := moduleDomains m
  let multi := decide (domains.length > 1)
  let clkName (d : ClkDomain) : String := if multi then s!"clk_{d.portSuffix}" else "clk"
  let rstName (d : ClkDomain) : String := if multi then s!"rst_{d.portSuffix}" else "rst"
  let clkPorts := if multi then domains.flatMap fun d => [s!"  input  logic        {clkName d}", s!"  input  logic        {rstName d}"]
    else ["  input  logic        clk", "  input  logic        rst"]
  let inPorts := (List.range m.inputNames.length).map fun i => s!"  input  logic {rangeSV (inputWidth m i)} {m.inputNames.getD i s!"in_{i}"}"
  let outPorts := m.outputs.map fun o => s!"  output logic {rangeSV o.width} {o.name}"
  let portHeader := String.intercalate ",\n" (clkPorts ++ inPorts ++ outPorts)
  let wireDecls := m.wires.map fun w => s!"  logic {rangeSV w.width} w_{w.wireIdx}; // {w.name}"
  let regDecls := m.regs.map fun r =>
    if r.isSynchronizer then s!"  (* ASYNC_REG = \"TRUE\" *) logic {rangeSV r.width} {r.name};" else s!"  logic {rangeSV r.width} {r.name};"
  let combWires := m.wires.map fun w => s!"    w_{w.wireIdx} = {storeSV w.width (emitExprSV inExprs regNames wireName w.expr)};"
  let combOuts := m.outputs.map fun o => s!"    {o.name} = {storeSV o.width (emitExprSV inExprs regNames wireName o.expr)};"
  let ffBlocks := String.join (domains.map fun d => emitDomainBlocksSV inExprs regNames (m.regs.filter (·.domain == d)) (clkName d) (rstName d) wireName)
  s!"module {m.name} (\n{portHeader}\n);\n" ++
  (if wireDecls.isEmpty then "" else String.intercalate "\n" wireDecls ++ "\n") ++
  (if regDecls.isEmpty then "" else String.intercalate "\n" regDecls ++ "\n") ++
  "  always_comb begin\n" ++ String.intercalate "\n" (combWires ++ combOuts) ++ "\n  end\n" ++ ffBlocks ++ "endmodule\n"

abbrev emitMacroDsp48E2SV : String :=
  "module obend_macro_dsp48e2 (\n  input  logic        clk,\n  input  logic        rst,\n" ++
  "  input  logic [26:0] a_in,\n  input  logic [17:0] b_in,\n  input  logic [47:0] c_in,\n  output logic [47:0] p_out\n);\n" ++
  "  logic [26:0] a1_reg, a2_reg;\n  logic [17:0] b1_reg, b2_reg;\n  logic [47:0] c1_reg, c2_reg, c3_reg, m_reg, p_reg;\n" ++
  "  always_ff @(posedge clk) begin\n    if (rst) begin\n      a1_reg <= 27'd0; a2_reg <= 27'd0;\n" ++
  "      b1_reg <= 18'd0; b2_reg <= 18'd0;\n      c1_reg <= 48'd0; c2_reg <= 48'd0; c3_reg <= 48'd0;\n" ++
  "      m_reg  <= 48'd0; p_reg  <= 48'd0;\n    end else begin\n      a1_reg <= a_in;  a2_reg <= a1_reg;\n" ++
  "      b1_reg <= b_in;  b2_reg <= b1_reg;\n      c1_reg <= c_in;  c2_reg <= c1_reg; c3_reg <= c2_reg;\n" ++
  "      m_reg  <= 48'(a2_reg) * 48'(b2_reg);\n      p_reg  <= m_reg + c3_reg;\n    end\n  end\n  assign p_out = p_reg;\nendmodule\n"

abbrev emitMacroUram288BypassSV : String :=
  "module obend_macro_uram288_bypass (\n  input  logic        clk,\n  input  logic        rst,\n  input  logic        we,\n" ++
  "  input  logic [11:0] waddr,\n  input  logic [63:0] wdata,\n  input  logic [11:0] raddr,\n  output logic [63:0] rdata\n);\n" ++
  "  logic [63:0] mem [0:4095];\n  logic [63:0] s1_rdata, s2_rdata, oreg_rdata;\n  logic [11:0] raddr_s1, raddr_s2;\n" ++
  "  logic        bp_s1_valid, bp_s2_valid;\n  logic [11:0] bp_s1_addr, bp_s2_addr;\n  logic [63:0] bp_s1_data, bp_s2_data;\n" ++
  "  always_ff @(posedge clk) begin\n    if (we) mem[waddr] <= wdata;\n    s1_rdata   <= mem[raddr];\n" ++
  "    s2_rdata   <= (bp_s1_valid && (bp_s1_addr == raddr_s1)) ? bp_s1_data : s1_rdata;\n" ++
  "    oreg_rdata <= (bp_s2_valid && (bp_s2_addr == raddr_s2)) ? bp_s2_data : s2_rdata;\n    if (rst) begin\n" ++
  "      raddr_s1    <= 12'd0; raddr_s2    <= 12'd0;\n      bp_s1_valid <= 1'b0;  bp_s2_valid <= 1'b0;\n" ++
  "      bp_s1_addr  <= 12'd0; bp_s2_addr  <= 12'd0;\n      bp_s1_data  <= 64'd0; bp_s2_data  <= 64'd0;\n    end else begin\n" ++
  "      raddr_s1    <= raddr;       raddr_s2    <= raddr_s1;\n      bp_s1_valid <= we;          bp_s2_valid <= bp_s1_valid;\n" ++
  "      bp_s1_addr  <= waddr;       bp_s2_addr  <= bp_s1_addr;\n      bp_s1_data  <= wdata;       bp_s2_data  <= bp_s1_data;\n" ++
  "    end\n  end\n  assign rdata = oreg_rdata;\nendmodule\n"

abbrev emitMacroAxisSkidSV : String :=
  "module obend_macro_axis_skid (\n  input  logic        clk,\n  input  logic        rst,\n  input  logic        up_valid,\n" ++
  "  output logic        up_ready,\n  input  logic [63:0] up_data,\n  output logic        dn_valid,\n" ++
  "  input  logic        dn_ready,\n  output logic [63:0] dn_data\n);\n" ++
  "  logic        main_valid, skid_valid;\n  logic [63:0] main_data,  skid_data;\n" ++
  "  assign up_ready = ~skid_valid;\n  assign dn_valid = main_valid;\n  assign dn_data  = main_data;\n" ++
  "  always_ff @(posedge clk) begin\n    if (rst) begin\n      main_valid <= 1'b0; skid_valid <= 1'b0;\n" ++
  "      main_data  <= 64'd0; skid_data <= 64'd0;\n    end else if (skid_valid) begin\n      if (dn_ready) begin\n" ++
  "        main_valid <= 1'b1;\n        main_data  <= skid_data;\n        skid_valid <= 1'b0;\n      end\n" ++
  "    end else if (main_valid) begin\n      if (dn_ready) begin\n        main_valid <= up_valid;\n" ++
  "        if (up_valid) main_data <= up_data;\n      end else if (up_valid) begin\n        skid_valid <= 1'b1;\n" ++
  "        skid_data  <= up_data;\n      end\n    end else if (up_valid) begin\n      main_valid <= 1'b1;\n" ++
  "      main_data  <= up_data;\n    end\n  end\nendmodule\n"

abbrev emitMacroIcapDprTileSV : String :=
  "module obend_macro_icap_dpr_tile (\n  input  logic        clk,\n  input  logic        rst,\n  input  logic        trigger_reconfig,\n" ++
  "  input  logic        drain_complete,\n  input  logic        icap_done,\n  input  logic [63:0] target_spec_digest,\n" ++
  "  input  logic [63:0] wire_in,\n  input  logic [63:0] safe_default,\n  output logic        decouple_en,\n" ++
  "  output logic [63:0] active_spec_digest,\n  output logic [63:0] wire_out\n);\n" ++
  "  typedef enum logic [1:0] {\n    DPR_ACTIVE    = 2'd0,\n    DPR_DRAINING  = 2'd1,\n    DPR_SWAPPING  = 2'd2,\n    DPR_WARMING   = 2'd3\n  } dpr_phase_t;\n" ++
  "  dpr_phase_t  phase;\n  logic [63:0] rolling_crc_q;\n  always_ff @(posedge clk) begin\n    if (rst) begin\n" ++
  "      phase              <= DPR_ACTIVE;\n      decouple_en        <= 1'b0;\n      active_spec_digest <= 64'd0;\n" ++
  "      rolling_crc_q      <= 64'hCBF2_9CE4_8422_2325;\n    end else begin\n      case (phase)\n" ++
  "        DPR_ACTIVE: if (trigger_reconfig) begin\n          phase         <= DPR_DRAINING;\n          decouple_en   <= 1'b1;\n          rolling_crc_q <= 64'hCBF2_9CE4_8422_2325;\n        end\n" ++
  "        DPR_DRAINING: if (drain_complete) begin\n          phase       <= DPR_SWAPPING;\n          decouple_en <= 1'b1;\n        end\n" ++
  "        DPR_SWAPPING: begin\n          rolling_crc_q <= (rolling_crc_q ^ wire_in) * 64'h0000_0100_0000_01B3;\n          if (icap_done) begin\n" ++
  "            if (rolling_crc_q == target_spec_digest) begin\n              phase              <= DPR_WARMING;\n              decouple_en        <= 1'b1;\n" ++
  "              active_spec_digest <= rolling_crc_q;\n            end else begin\n              decouple_en <= 1'b1;\n            end\n          end\n        end\n" ++
  "        DPR_WARMING: begin phase <= DPR_ACTIVE; decouple_en <= 1'b0; end\n      endcase\n    end\n  end\n  assign wire_out = decouple_en ? safe_default : wire_in;\nendmodule\n"

abbrev emitMacroNocRouterXySV : String :=
  "module obend_macro_noc_router_xy (\n  input  logic [7:0]  my_x,\n  input  logic [7:0]  my_y,\n  input  logic [7:0]  dst_x,\n  input  logic [7:0]  dst_y,\n" ++
  "  input  logic        in_valid,\n  input  logic        credit_avail,\n  output logic        in_ready,\n  output logic [2:0]  route_dir\n);\n" ++
  "  assign in_ready = credit_avail;\n  always_comb begin\n" ++
  "    if (!in_valid || !credit_avail) route_dir = 3'd4; // HOLD/LOCAL\n    else if (dst_x < my_x)          route_dir = 3'd3; // WEST\n" ++
  "    else if (dst_x > my_x)          route_dir = 3'd2; // EAST\n    else if (dst_y < my_y)          route_dir = 3'd1; // SOUTH\n" ++
  "    else if (dst_y > my_y)          route_dir = 3'd0; // NORTH\n    else                            route_dir = 3'd4; // LOCAL\n  end\nendmodule\n"

abbrev emitHierarchicalSV (m : RtlModule) : String :=
  emitMacroDsp48E2SV ++ "\n" ++ emitMacroUram288BypassSV ++ "\n" ++ emitMacroAxisSkidSV ++ "\n" ++
  emitMacroIcapDprTileSV ++ "\n" ++ emitMacroNocRouterXySV ++ "\n" ++ emitModuleSV m

theorem emitHierarchicalSV_nonEmpty_and_has_header (m : RtlModule) :
    emitHierarchicalSV m =
      emitMacroDsp48E2SV ++ "\n" ++ emitMacroUram288BypassSV ++ "\n" ++ emitMacroAxisSkidSV ++ "\n" ++
      emitMacroIcapDprTileSV ++ "\n" ++ emitMacroNocRouterXySV ++ "\n" ++ emitModuleSV m ∧
    (emitMacroDsp48E2SV != "") = true ∧ (emitMacroUram288BypassSV != "") = true ∧
    (emitMacroAxisSkidSV != "") = true ∧ (emitMacroIcapDprTileSV != "") = true ∧
    (emitMacroNocRouterXySV != "") = true ∧ (emitMacroDsp48E2SV.utf8ByteSize > 100) = true := by
  exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 6. Synchronous Clocked RAM Primitives (`SyncRamSpec`, `RtlMemModule`, `stepMemModule`, `emitMemModuleSV`) -/

/-- Same-cycle read/write collision discipline on a synchronous clocked RAM port. -/
inductive SyncRamMode where
  | readFirst   -- `rdata_q <= mem[raddr]` (latches pre-write word when `we && waddr == raddr`)
  | writeFirst  -- `rdata_q <= (we && waddr == raddr) ? wdata : mem[raddr]`
  deriving @[expose] DecidableEq, Repr

/-- Physical FPGA/ASIC synthesis target attribute for a synchronous RAM bank. -/
inductive SyncRamStyle where
  | bram | uram | sram
  deriving @[expose] DecidableEq, Repr

def SyncRamStyle.svAttr : SyncRamStyle → String
  | .bram => "block"
  | .uram => "ultra"
  | .sram => "distributed"

/-- Synchronous clocked RAM bank (`1 ≤ addrWidth ≤ 24`, `1 ≤ dataWidth ≤ 64`).
Its synchronous registered read-data output `rdataName` is visible to `core` at register slot
`core.regs.length + ramIdx` (`RtlExpr.regRead (core.regs.length + ramIdx)`). -/
structure SyncRamSpec where
  ramIdx        : Nat
  name          : String
  rdataName     : String
  domain        : ClkDomain := .coreClk
  style         : SyncRamStyle := .bram
  mode          : SyncRamMode := .readFirst
  addrWidth     : Nat
  dataWidth     : Nat := 64
  readAddrExpr  : RtlExpr
  writeEnExpr   : RtlExpr
  writeAddrExpr : RtlExpr
  writeDataExpr : RtlExpr
  deriving @[expose] DecidableEq, Repr

/-- Synchronous RTL module paired with zero or more clocked `SyncRamSpec` banks. -/
structure RtlMemModule where
  core : RtlModule
  rams : List SyncRamSpec := []
  deriving @[expose] DecidableEq, Repr

/-- Complete architectural state of an `RtlMemModule`:
`regs` (`0 .. core.regs.length - 1` for flip-flops, `core.regs.length + k` for RAM `k`'s registered
read-data output `rdataName`) and `mems` (`ramIdx → addr → word`). -/
structure MemState where
  regs : Nat → BitVec 64
  mems : Nat → BitVec 64 → BitVec 64

/-- Evaluate the registered read-data value latched by `ram` on `posedge clk`. -/
abbrev evalSyncRamReadNext (inputs wireEnv regState : Nat → BitVec 64)
    (memArr : BitVec 64 → BitVec 64) (ram : SyncRamSpec) : BitVec 64 :=
  let raddr := truncToWidth ram.addrWidth (evalRtlExpr inputs wireEnv regState ram.readAddrExpr)
  let raw := truncToWidth ram.dataWidth (memArr raddr)
  match ram.mode with
  | .readFirst => raw
  | .writeFirst =>
    let we := truncToWidth 1 (evalRtlExpr inputs wireEnv regState ram.writeEnExpr) != 0#64
    let waddr := truncToWidth ram.addrWidth (evalRtlExpr inputs wireEnv regState ram.writeAddrExpr)
    let wdata := truncToWidth ram.dataWidth (evalRtlExpr inputs wireEnv regState ram.writeDataExpr)
    if we && waddr == raddr then wdata else raw

/-- Evaluate the next-cycle memory array of `ram` on `posedge clk`. -/
abbrev stepSyncRamArray (inputs wireEnv regState : Nat → BitVec 64)
    (memArr : BitVec 64 → BitVec 64) (ram : SyncRamSpec) : BitVec 64 → BitVec 64 :=
  let we := truncToWidth 1 (evalRtlExpr inputs wireEnv regState ram.writeEnExpr) != 0#64
  let waddr := truncToWidth ram.addrWidth (evalRtlExpr inputs wireEnv regState ram.writeAddrExpr)
  let wdata := truncToWidth ram.dataWidth (evalRtlExpr inputs wireEnv regState ram.writeDataExpr)
  if we then fun a => if a == waddr then wdata else memArr a else memArr

/-- Advance `m : RtlMemModule` by one synchronous clock edge. -/
abbrev stepMemModule (m : RtlMemModule) (rst : Bool) (inputs : Nat → BitVec 64) (st : MemState) : MemState :=
  let wireEnv := evalWireTable inputs st.regs m.core.wires
  let baseRegs := stepModuleRegs m.core rst inputs st.regs
  let nCore := m.core.regs.length
  let nextRegs := m.rams.foldl (fun regAcc ram =>
    let v := evalSyncRamReadNext inputs wireEnv st.regs (st.mems ram.ramIdx) ram
    fun i => if i == nCore + ram.ramIdx then v else regAcc i) baseRegs
  let nextMems := m.rams.foldl (fun memAcc ram =>
    let arr' := stepSyncRamArray inputs wireEnv st.regs (st.mems ram.ramIdx) ram
    fun k => if k == ram.ramIdx then arr' else memAcc k) st.mems
  { regs := nextRegs, mems := nextMems }

/-- Run `m : RtlMemModule` over a multi-cycle `(rst, inputs)` trace. -/
abbrev runMemModuleTrace (m : RtlMemModule) (init : MemState) (trace : List (Bool × (Nat → BitVec 64))) : MemState :=
  trace.foldl (fun st (rst, ins) => stepMemModule m rst ins st) init

/-- Evaluate combinational outputs of `m : RtlMemModule` in current `MemState`. -/
abbrev evalMemModuleOutputs (m : RtlMemModule) (inputs : Nat → BitVec 64) (st : MemState) : List (String × BitVec 64) :=
  evalModuleOutputs m.core inputs st.regs

/-- Valid address width range `1..24` for synthesizable BRAM/URAM/SRAM banks. -/
abbrev validRamAddrWidth (aw : Nat) : Bool := 0 < aw && aw ≤ 24

/-- Augmented register list treating each `SyncRamSpec`'s registered readout slot as a domain-local register. -/
abbrev augmentedMemRegs (m : RtlMemModule) : List RegSpec :=
  let nCore := m.core.regs.length
  m.core.regs ++ m.rams.map fun ram =>
    { regIdx := nCore + ram.ramIdx
    , name := ram.rdataName
    , domain := ram.domain
    , resetKind := .resetFree
    , isSynchronizer := false
    , nextExpr := .const 0#64
    , width := ram.dataWidth }

/-- Check indexing (`0, 1, ...`), non-empty distinct names, width bounds, DAG bounds, and domain CDC across `rams`. -/
def checkSyncRamTable (nIn nTotalRegs nWires : Nat) (allRegs : List RegSpec)
    (wires : List WireAssign) (rams : List SyncRamSpec) : Bool :=
  let rec go (expectedIdx : Nat) (seenNames : List String) : List SyncRamSpec → Bool
    | [] => true
    | ram :: rest =>
      let sameDom (e : RtlExpr) : Bool :=
        (exprReadRegs e wires).all fun src => lookupRegDomain allRegs src == some ram.domain
      (ram.ramIdx == expectedIdx) &&
      (ram.name != "") && (ram.rdataName != "") && (ram.name != ram.rdataName) &&
      !seenNames.contains ram.name && !seenNames.contains ram.rdataName &&
      validRamAddrWidth ram.addrWidth && validWidth ram.dataWidth &&
      checkExprDAG nIn nTotalRegs nWires ram.readAddrExpr &&
      checkExprDAG nIn nTotalRegs nWires ram.writeEnExpr &&
      checkExprDAG nIn nTotalRegs nWires ram.writeAddrExpr &&
      checkExprDAG nIn nTotalRegs nWires ram.writeDataExpr &&
      sameDom ram.readAddrExpr && sameDom ram.writeEnExpr &&
      sameDom ram.writeAddrExpr && sameDom ram.writeDataExpr &&
      go (expectedIdx + 1) (ram.name :: ram.rdataName :: seenNames) rest
  go 0 (allRegs.take (nTotalRegs - rams.length) |>.map (·.name)) rams

/-- Structural DAG + CDC gate for `RtlMemModule`. -/
abbrev checkRtlMemModule (m : RtlMemModule) : Bool :=
  let nIn := m.core.inputNames.length
  let nTotalRegs := m.core.regs.length + m.rams.length
  let nWires := m.core.wires.length
  let allRegs := augmentedMemRegs m
  checkWireTableDAG nIn nTotalRegs m.core.wires &&
  m.core.regs.all (fun r => checkExprDAG nIn nTotalRegs nWires r.nextExpr) &&
  m.core.outputs.all (fun o => checkExprDAG nIn nTotalRegs nWires o.expr) &&
  checkModuleCdc allRegs m.core.wires &&
  checkSyncRamTable nIn nTotalRegs nWires allRegs m.core.wires m.rams

/-- Declared width of register or RAM readout slot `idx` in `m : RtlMemModule`. -/
abbrev memRegWidthOf (m : RtlMemModule) (idx : Nat) : Nat :=
  let nCore := m.core.regs.length
  if idx < nCore then regWidthOf m.core idx
  else ((m.rams.find? (fun r => nCore + r.ramIdx == idx)).map (·.dataWidth)).getD 64

/-- Declared data width of RAM bank `k` (64 if absent). -/
abbrev ramDataWidthOf (m : RtlMemModule) (k : Nat) : Nat :=
  ((m.rams.find? (·.ramIdx == k)).map (·.dataWidth)).getD 64

/-- Width environment of `m : RtlMemModule` covering inputs, wires, core registers, and RAM readout registers. -/
abbrev memModuleWidthEnv (m : RtlMemModule) : WidthEnv :=
  ⟨inputWidth m.core, wireWidthOf m.core, memRegWidthOf m⟩

/-- Every width error in `m : RtlMemModule`, naming the offending port, wire, register, or RAM port. -/
abbrev memWidthErrors (m : RtlMemModule) : List String :=
  let env := memModuleWidthEnv m
  (List.range m.core.inputNames.length).flatMap (fun i =>
    declErrors s!"input port `{m.core.inputNames.getD i s!"in_{i}"}`" (inputWidth m.core i)) ++
  m.core.wires.flatMap (fun a =>
    declErrors s!"wire `{a.name}`" a.width ++ fitErrors env s!"wire `{a.name}`" (wireWidthOf m.core a.wireIdx) a.expr) ++
  m.core.regs.flatMap (fun r =>
    declErrors s!"register `{r.name}`" r.width ++ fitErrors env s!"register `{r.name}`" (regWidthOf m.core r.regIdx) r.nextExpr ++
    match r.resetKind with
    | .resetFree => []
    | .syncReset v => if constWidth v ≤ regWidthOf m.core r.regIdx then [] else
        [s!"register `{r.name}` resets to {v.toNat}, which does not fit its {regWidthOf m.core r.regIdx} bits"]) ++
  m.core.outputs.flatMap (fun o =>
    declErrors s!"output port `{o.name}`" o.width ++ fitErrors env s!"output port `{o.name}`" o.width o.expr) ++
  m.rams.flatMap (fun ram =>
    (if validRamAddrWidth ram.addrWidth then [] else [s!"ram `{ram.name}` addrWidth {ram.addrWidth} outside 1..24"]) ++
    declErrors s!"ram `{ram.name}` data" ram.dataWidth ++
    fitErrors env s!"ram `{ram.name}` raddr" ram.addrWidth ram.readAddrExpr ++
    fitErrors env s!"ram `{ram.name}` we" 1 ram.writeEnExpr ++
    fitErrors env s!"ram `{ram.name}` waddr" ram.addrWidth ram.writeAddrExpr ++
    fitErrors env s!"ram `{ram.name}` wdata" ram.dataWidth ram.writeDataExpr)

abbrev checkMemWidths (m : RtlMemModule) : Bool := (memWidthErrors m).isEmpty

/-- Complete emission & LEC gate for `RtlMemModule`. -/
abbrev checkRtlMemModuleW (m : RtlMemModule) : Bool :=
  let allRegs := augmentedMemRegs m
  checkRtlMemModule m && checkPortWidths m.core &&
  (allRegs.all fun r => !r.isSynchronizer || checkSyncChain allRegs m.core.wires m.core.outputs r) &&
  checkMemWidths m

/-- Clock domains of `m : RtlMemModule`, across both `core.regs` and `rams`. -/
def memModuleDomains (m : RtlMemModule) : List ClkDomain :=
  let d0 := moduleDomains m.core
  m.rams.foldl (fun acc r => if acc.contains r.domain then acc else acc ++ [r.domain]) d0

/-- Emit `always_ff` synchronous RAM blocks for domain `d` (`(* ram_style = ... *)` inferred by Yosys/Vivado). -/
def emitRamDomainBlockSV (inExprs regNames : List String) (ramsD : List SyncRamSpec)
    (clkName : String) (wireName : Nat → String) : String :=
  if ramsD.isEmpty then ""
  else
    let stmts := ramsD.flatMap fun ram =>
      let raddr := storeSV ram.addrWidth (emitExprSV inExprs regNames wireName ram.readAddrExpr)
      let weBit := s!"(({emitExprSV inExprs regNames wireName ram.writeEnExpr} & 64'd1) != 64'd0)"
      let waddr := storeSV ram.addrWidth (emitExprSV inExprs regNames wireName ram.writeAddrExpr)
      let wdata := storeSV ram.dataWidth (emitExprSV inExprs regNames wireName ram.writeDataExpr)
      let wrLine := s!"    if ({weBit}) {ram.name}[{waddr}] <= {wdata};"
      let rdLine := match ram.mode with
        | .readFirst  => s!"    {ram.rdataName} <= {ram.name}[{raddr}];"
        | .writeFirst => s!"    {ram.rdataName} <= ({weBit} && ({waddr} == {raddr})) ? {wdata} : {ram.name}[{raddr}];"
      [wrLine, rdLine]
    s!"  // Synchronous RAM banks\n  always_ff @(posedge {clkName}) begin\n" ++
      String.intercalate "\n" stmts ++ "\n  end\n"

/-- Emit synthesizable SystemVerilog-2012 for `m : RtlMemModule`.
When `m.rams = []`, emits the exact byte-identical string `emitModuleSV m.core`. -/
def emitMemModuleSV (m : RtlMemModule) : String :=
  if m.rams.isEmpty then emitModuleSV m.core
  else
    let regNames := (m.core.regs.map fun r => readSV r.width r.name) ++
      (m.rams.map fun ram => readSV ram.dataWidth ram.rdataName)
    let wireName (i : Nat) : String := readSV (wireWidthOf m.core i) s!"w_{i}"
    let inExprs := inputExprsSV m.core
    let domains := memModuleDomains m
    let multi := decide (domains.length > 1)
    let clkName (d : ClkDomain) : String := if multi then s!"clk_{d.portSuffix}" else "clk"
    let rstName (d : ClkDomain) : String := if multi then s!"rst_{d.portSuffix}" else "rst"
    let clkPorts := if multi then domains.flatMap fun d => [s!"  input  logic        {clkName d}", s!"  input  logic        {rstName d}"]
      else ["  input  logic        clk", "  input  logic        rst"]
    let inPorts := (List.range m.core.inputNames.length).map fun i =>
      s!"  input  logic {rangeSV (inputWidth m.core i)} {m.core.inputNames.getD i s!"in_{i}"}"
    let outPorts := m.core.outputs.map fun o => s!"  output logic {rangeSV o.width} {o.name}"
    let portHeader := String.intercalate ",\n" (clkPorts ++ inPorts ++ outPorts)
    let wireDecls := m.core.wires.map fun w => s!"  logic {rangeSV w.width} w_{w.wireIdx}; // {w.name}"
    let regDecls := m.core.regs.map fun r =>
      if r.isSynchronizer then s!"  (* ASYNC_REG = \"TRUE\" *) logic {rangeSV r.width} {r.name};"
      else s!"  logic {rangeSV r.width} {r.name};"
    let ramDecls := m.rams.flatMap fun ram =>
      [ s!"  (* ram_style = \"{ram.style.svAttr}\" *) logic {rangeSV ram.dataWidth} {ram.name} [0:{(1 <<< ram.addrWidth) - 1}];"
      , s!"  logic {rangeSV ram.dataWidth} {ram.rdataName};" ]
    let combWires := m.core.wires.map fun w => s!"    w_{w.wireIdx} = {storeSV w.width (emitExprSV inExprs regNames wireName w.expr)};"
    let combOuts := m.core.outputs.map fun o => s!"    {o.name} = {storeSV o.width (emitExprSV inExprs regNames wireName o.expr)};"
    let ffBlocks := String.join (domains.map fun d =>
      emitDomainBlocksSV inExprs regNames (m.core.regs.filter (·.domain == d)) (clkName d) (rstName d) wireName ++
      emitRamDomainBlockSV inExprs regNames (m.rams.filter (·.domain == d)) (clkName d) wireName)
    s!"module {m.core.name} (\n{portHeader}\n);\n" ++
    (if wireDecls.isEmpty then "" else String.intercalate "\n" wireDecls ++ "\n") ++
    (if regDecls.isEmpty then "" else String.intercalate "\n" regDecls ++ "\n") ++
    String.intercalate "\n" ramDecls ++ "\n" ++
    "  always_comb begin\n" ++ String.intercalate "\n" (combWires ++ combOuts) ++ "\n  end\n" ++
    ffBlocks ++ "endmodule\n"

/-- Backwards-compatibility identity: with zero RAM banks, `emitMemModuleSV` is `emitModuleSV`. -/
theorem emitMemModuleSV_empty (m : RtlModule) :
    emitMemModuleSV { core := m, rams := [] } = emitModuleSV m := by rfl

/-- With zero RAM banks, `stepMemModule` steps `core.regs` identically to `stepModuleRegs` and preserves `mems`. -/
theorem stepMemModule_empty (m : RtlModule) (rst : Bool) (inputs : Nat → BitVec 64) (st : MemState) :
    (stepMemModule { core := m, rams := [] } rst inputs st).regs = stepModuleRegs m rst inputs st.regs ∧
    (stepMemModule { core := m, rams := [] } rst inputs st).mems = st.mems := by exact ⟨rfl, rfl⟩

/-- Exact same-cycle read/write collision law distinguishing `.readFirst` from `.writeFirst` on a `SyncRamSpec`:
1. Away from an active same-address write (`¬(we ∧ waddr = raddr)`), `.readFirst` and `.writeFirst` latch identical read data;
2. Under an active same-address write (`we = true` and `waddr = raddr`), `.readFirst` latches the pre-write word
   `truncToWidth D (memArr raddr)` while `.writeFirst` forwards the newly written word `truncToWidth D wdata`. -/
theorem stepSyncRam_readFirst_vs_writeFirst
    (inputs wireEnv regState : Nat → BitVec 64) (memArr : BitVec 64 → BitVec 64) (ram : SyncRamSpec) :
    let raddr := truncToWidth ram.addrWidth (evalRtlExpr inputs wireEnv regState ram.readAddrExpr)
    let we    := truncToWidth 1 (evalRtlExpr inputs wireEnv regState ram.writeEnExpr) != 0#64
    let waddr := truncToWidth ram.addrWidth (evalRtlExpr inputs wireEnv regState ram.writeAddrExpr)
    let wdata := truncToWidth ram.dataWidth (evalRtlExpr inputs wireEnv regState ram.writeDataExpr)
    evalSyncRamReadNext inputs wireEnv regState memArr { ram with mode := .readFirst } =
      truncToWidth ram.dataWidth (memArr raddr) ∧
    evalSyncRamReadNext inputs wireEnv regState memArr { ram with mode := .writeFirst } =
      (if we && waddr == raddr then wdata else truncToWidth ram.dataWidth (memArr raddr)) := by exact ⟨rfl, rfl⟩

/-- Every RAM readout latch and updated RAM word stays strictly below `2 ^ dataWidth` when `dataWidth ≤ 64`. -/
theorem evalSyncRamReadNext_lt (inputs wireEnv regState : Nat → BitVec 64)
    (memArr : BitVec 64 → BitVec 64) (ram : SyncRamSpec) (hw : ram.dataWidth ≤ 64) :
    (evalSyncRamReadNext inputs wireEnv regState memArr ram).toNat < 2 ^ ram.dataWidth := by
  unfold evalSyncRamReadNext
  cases ram.mode with
  | readFirst => exact truncToWidth_lt ram.dataWidth hw _
  | writeFirst =>
    dsimp only; split
    · exact truncToWidth_lt ram.dataWidth hw _
    · exact truncToWidth_lt ram.dataWidth hw _

theorem stepSyncRamArray_lt (inputs wireEnv regState : Nat → BitVec 64)
    (memArr : BitVec 64 → BitVec 64) (ram : SyncRamSpec) (hw : ram.dataWidth ≤ 64)
    (hMem : ∀ a, (memArr a).toNat < 2 ^ ram.dataWidth) (a : BitVec 64) :
    (stepSyncRamArray inputs wireEnv regState memArr ram a).toNat < 2 ^ ram.dataWidth := by
  unfold stepSyncRamArray
  split
  · dsimp only; split
    · exact truncToWidth_lt ram.dataWidth hw _
    · exact hMem a
  · exact hMem a

theorem checkMemWidths_parts (m : RtlMemModule) (h : checkMemWidths m = true) :
    (∀ a ∈ m.core.wires, fitErrors (memModuleWidthEnv m) s!"wire `{a.name}`" (wireWidthOf m.core a.wireIdx) a.expr = []) ∧
    (∀ r ∈ m.core.regs, validWidth r.width = true ∧
      fitErrors (memModuleWidthEnv m) s!"register `{r.name}`" (regWidthOf m.core r.regIdx) r.nextExpr = [] ∧
      ∀ v, r.resetKind = .syncReset v → constWidth v ≤ regWidthOf m.core r.regIdx) ∧
    (∀ o ∈ m.core.outputs, validWidth o.width = true ∧
      fitErrors (memModuleWidthEnv m) s!"output port `{o.name}`" o.width o.expr = []) ∧
    (∀ ram ∈ m.rams, validRamAddrWidth ram.addrWidth = true ∧ validWidth ram.dataWidth = true ∧
      fitErrors (memModuleWidthEnv m) s!"ram `{ram.name}` raddr" ram.addrWidth ram.readAddrExpr = [] ∧
      fitErrors (memModuleWidthEnv m) s!"ram `{ram.name}` we" 1 ram.writeEnExpr = [] ∧
      fitErrors (memModuleWidthEnv m) s!"ram `{ram.name}` waddr" ram.addrWidth ram.writeAddrExpr = [] ∧
      fitErrors (memModuleWidthEnv m) s!"ram `{ram.name}` wdata" ram.dataWidth ram.writeDataExpr = []) := by
  unfold checkMemWidths memWidthErrors at h; simp only [List.isEmpty_iff, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨_, hw⟩, hr⟩, ho⟩, hram⟩ := h
  refine ⟨fun a ha => ?_, fun r hr' => ?_, fun o ho' => ?_, fun ram hram' => ?_⟩
  · have := flatMap_nil_mem hw ha; simp only [List.append_eq_nil_iff] at this; exact this.2
  · have := flatMap_nil_mem hr hr'; simp only [List.append_eq_nil_iff] at this
    refine ⟨?_, this.1.2, fun v hv => ?_⟩
    · have h1 := this.1.1; unfold declErrors at h1
      split at h1
      · assumption
      · simp at h1
    · have h3 := this.2; rw [hv] at h3; simp only at h3
      split at h3
      · assumption
      · simp at h3
  · have := flatMap_nil_mem ho ho'; simp only [List.append_eq_nil_iff] at this
    refine ⟨?_, this.2⟩; have h1 := this.1; unfold declErrors at h1
    split at h1
    · assumption
    · simp at h1
  · have := flatMap_nil_mem hram hram'; simp only [List.append_eq_nil_iff] at this
    obtain ⟨⟨⟨⟨⟨ha, hd⟩, hra⟩, hwe⟩, hwa⟩, hwd⟩ := this
    refine ⟨?_, ?_, hra, hwe, hwa, hwd⟩
    · split at ha
      · assumption
      · simp at ha
    · unfold declErrors at hd
      split at hd
      · assumption
      · simp at hd

theorem evalMemWireTable_lt (m : RtlMemModule) (inputs regs : Nat → BitVec 64)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ inputWidth m.core i)
    (hR : ∀ i, (regs i).toNat < 2 ^ memRegWidthOf m i)
    (hChk : checkMemWidths m = true) :
    ∀ i, (evalWireTable inputs regs m.core.wires i).toNat < 2 ^ wireWidthOf m.core i := by
  have hWires := (checkMemWidths_parts m hChk).1; unfold evalWireTable
  suffices ∀ (l : List WireAssign), (∀ a ∈ l, a ∈ m.core.wires) →
      ∀ (env : Nat → BitVec 64), (∀ i, (env i).toNat < 2 ^ wireWidthOf m.core i) →
      ∀ i, ((l.foldl (fun env a => let v := evalRtlExpr inputs env regs a.expr; fun i => if i == a.wireIdx then v else env i) env) i).toNat < 2 ^ wireWidthOf m.core i by
    exact this m.core.wires (fun _ h => h) _ (fun i => by simpa using Nat.two_pow_pos (wireWidthOf m.core i))
  intro l; induction l with
  | nil => intro _ env hEnv; exact hEnv
  | cons a rest ih =>
    intro hSub env hEnv; simp only [List.foldl_cons]
    apply ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx)); intro i
    obtain ⟨w, hw, hle⟩ := fitErrors_nil (hWires a (hSub a List.mem_cons_self))
    have hv := evalRtlExpr_lt_of_inferWidthE (memModuleWidthEnv m) inputs env regs hIn hEnv hR a.expr w hw
    by_cases hi : i = a.wireIdx
    · subst hi; simp only [beq_self_eq_true, ite_true]; exact lt_two_pow_mono hv hle
    · simp only [beq_iff_eq, hi, ite_false]; exact hEnv i

/-- Constructive inhabitedness witness: a non-empty synchronous BRAM module passing `checkRtlMemModuleW`. -/
theorem checkRtlMemModuleW_inhabited :
    ∃ m : RtlMemModule, m.rams ≠ [] ∧ checkRtlMemModuleW m = true := by
  refine ⟨{ core := { name := "bram_probe"
                    , inputNames := ["we", "addr", "wdata"]
                    , inputWidths := [1, 4, 64]
                    , wires := []
                    , regs := []
                    , outputs := [{ name := "rdata", expr := .regRead 0, width := 64 }] }
          , rams := [{ ramIdx := 0
                     , name := "bank0"
                     , rdataName := "bank0_q"
                     , addrWidth := 4
                     , dataWidth := 64
                     , readAddrExpr := .inputPort 1
                     , writeEnExpr := .inputPort 0
                     , writeAddrExpr := .inputPort 1
                     , writeDataExpr := .inputPort 2 }] }, ?_, ?_⟩
  · decide
  · decide +kernel

end Obend.Hardware.HDL
end
