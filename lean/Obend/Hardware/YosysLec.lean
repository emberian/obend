module
/-
# Obend.Hardware.YosysLec — logic equivalence of an emitted `.sv` against Lean's model of its `RtlModule`

`emitYosysLecSmt2 m` writes the second half of an SMT-LIB2 query whose first half is Yosys's reading of
`emitModuleSV m`:

    yosys -p "read_verilog -sv X.sv; prep -top X; write_smt2 X.yosys.smt2"
    cat X.yosys.smt2 X_lec.smt2 | z3 -in        # unsat = equivalent

Yosys's half declares a state sort `|X_s|`, an accessor `|X_n p|` for every port and register `p`, and
the transition relation `|X_t|`. This half takes two states `s`, `s1` with `(|X_t| s s1)`, reads the
inputs, resets and register values of `s` through the port and register names `emitModuleSV` gives
them, and builds Lean's model of `m` over those values with `emitExprSmt2` (the `QF_BV` rendering of
`evalRtlExpr`): every wire, every output truncated to its port width (`evalModuleOutputsW`), and every
register's next value with its synchronous reset (`stepModuleRegs`). It then asserts that some output
of `s` or some register of `s1` differs from the model.

`unsat` says: for every register state and every input, the module Yosys read from the `.sv` and
Lean's model of `m` agree on every output and on every next register value. With registers matched by
name, that is sequential equivalence from any common state. Nothing between the two halves is
hand-written; both come from a program. What the query trusts: Yosys's SystemVerilog frontend and
`write_smt2`, z3, and `emitAluOpSmt2`'s table of thirteen operators against `evalAluOp`.

Two conventions of `RtlModule` are read into the model rather than proved: a narrow input port is the
low bits of a 64-bit `inputPort` (the module sees it zero-extended), and with several clock domains
each register's synchronous reset is its own domain's `rst_<d>` (`stepModuleRegs` has one `rst`; the
query covers every combination of the domain resets, which includes all of them equal). All registers
step together, as in `stepModuleRegs`; Yosys's `write_smt2` treats every flip-flop as clocked by one
global clock in the same way.
-/
public import Obend.Hardware.HDL
public import Obend.Hardware.VerilateRunner
@[expose] public section

namespace Obend.Hardware.YosysLec
open Obend.Hardware.HDL Obend.Hardware.VerilateRunner
set_option autoImplicit false

/-- Yosys's accessor for port or register `p` of module `mod` at state `st`: `(|mod_n p| st)`. -/
def yosysSig (mod p st : String) : String :=
  s!"(|{mod}_n {p}| {st})"

/-- A Yosys signal of width `w` as an `(_ BitVec w)` term: Yosys gives 1-bit signals sort `Bool`. -/
def yosysBv (w : Nat) (sig : String) : String :=
  if w == 1 then s!"(ite {sig} #b1 #b0)" else sig

/-- Input `i` of `m` as the 64-bit word the module sees: the port, zero-extended when narrower. -/
def inputWord (m : RtlModule) (i : Nat) : String :=
  let w := inputWidth m i
  let sig := yosysBv w (yosysSig m.name (m.inputNames.getD i s!"in_{i}") "s")
  if w == 64 then sig else s!"((_ zero_extend {64 - w}) {sig})"

/-- The reset port that governs register `r` in `emitModuleSV m`. -/
def resetPortOf (m : RtlModule) (r : RegSpec) : String :=
  if (moduleDomains m).length > 1 then s!"rst_{r.domain.portSuffix}" else "rst"

/-- The register that writes state slot `k` (the last one in `m.regs`, as in `stepModuleRegs`). -/
def regOfSlot (m : RtlModule) (k : Nat) : Option RegSpec :=
  m.regs.foldl (fun acc r => if r.regIdx == k then some r else acc) none

/-- Lean's next value of register `r`: `nextExpr`, or its reset value while its domain's reset is high. -/
def regNextSmt2 (m : RtlModule) (r : RegSpec) : String :=
  let next := emitExprSmt2 "spec_" r.nextExpr
  match r.resetKind with
  | .resetFree => next
  | .syncReset v => s!"(ite {yosysSig m.name (resetPortOf m r) "s"} {bitVec64ToSmtHex v} {next})"

/-- The low `w` bits of a 64-bit term (`truncToWidth`, as seen at a `w`-bit port). -/
def lowBits (w : Nat) (t : String) : String :=
  if w == 64 then t else s!"((_ extract {w - 1} 0) {t})"

/-- The Lean half of the LEC query for `m` (see the module docstring). Appended to Yosys's
`write_smt2` of `emitModuleSV m`, `z3` answers `unsat` exactly when the two agree. After
`(check-sat)` comes a `get-value` block for the counterexample, which a caller sends only on `sat`. -/
def emitYosysLecSmt2 (m : RtlModule) : String :=
  let mod := m.name
  let nSlots := m.regs.foldl (fun acc r => max acc (r.regIdx + 1)) m.regs.length
  let states :=
    [ s!"(declare-const s |{mod}_s|)"
    , s!"(declare-const s1 |{mod}_s|)"
    , s!"(assert (|{mod}_h| s))"
    , s!"(assert (|{mod}_t| s s1))" ]
  let inDefs := (List.range m.inputNames.length).map fun i =>
    s!"(define-fun in_{i} () (_ BitVec 64) {inputWord m i})"
  let regDefs := (List.range nSlots).map fun k =>
    match regOfSlot m k with
    | some r => s!"(define-fun r_{k} () (_ BitVec 64) {yosysSig mod r.name "s"})"
    | none => s!"(declare-const r_{k} (_ BitVec 64))"
  let wireDefs := m.wires.map fun w =>
    s!"(define-fun spec_w_{w.wireIdx} () (_ BitVec 64) {emitExprSmt2 "spec_" w.expr})"
  let outDefs := m.outputs.flatMap fun o =>
    [ s!"(define-fun |rtl_out_{o.name}| () (_ BitVec {o.width}) {yosysBv o.width (yosysSig mod o.name "s")})"
    , s!"(define-fun |spec_out_{o.name}| () (_ BitVec {o.width}) {lowBits o.width (emitExprSmt2 "spec_" o.expr)})"
    , s!"(define-fun |lec_out_{o.name}| () Bool (= |rtl_out_{o.name}| |spec_out_{o.name}|))" ]
  let regObls := m.regs.flatMap fun r =>
    [ s!"(define-fun |rtl_next_{r.name}| () (_ BitVec 64) {yosysSig mod r.name "s1"})"
    , s!"(define-fun |spec_next_{r.name}| () (_ BitVec 64) {regNextSmt2 m r})"
    , s!"(define-fun |lec_next_{r.name}| () Bool (= |rtl_next_{r.name}| |spec_next_{r.name}|))" ]
  let obls := m.outputs.map (fun o => s!"|lec_out_{o.name}|") ++ m.regs.map (fun r => s!"|lec_next_{r.name}|")
  let miter :=
    if obls.isEmpty then "(assert false)"
    else s!"(assert (not (and true {String.intercalate " " obls})))"
  let domains := moduleDomains m
  let resets :=
    if domains.length > 1 then domains.map fun d => s!"rst_{d.portSuffix}" else ["rst"]
  let resetVals := if m.regs.isEmpty then [] else resets.map fun p => yosysSig mod p "s"
  let cexTerms :=
    (List.range m.inputNames.length).map (fun i => s!"in_{i}") ++ resetVals ++
    (List.range nSlots).map (fun k => s!"r_{k}") ++
    m.outputs.flatMap (fun o => [s!"|lec_out_{o.name}|", s!"|rtl_out_{o.name}|", s!"|spec_out_{o.name}|"]) ++
    m.regs.flatMap (fun r => [s!"|lec_next_{r.name}|", s!"|rtl_next_{r.name}|", s!"|spec_next_{r.name}|"])
  s!"; Lean half of the LEC of {mod}: Obend.Hardware.YosysLec.emitYosysLecSmt2 over the RtlModule that emitModuleSV printed.\n" ++
  s!"; Append to Yosys `write_smt2` of the emitted .sv; unsat = every output and next register agrees with Lean's model.\n" ++
  s!"; Module: {mod} (inputs={m.inputNames.length}, wires={m.wires.length}, regs={m.regs.length}, outputs={m.outputs.length})\n" ++
  "\n; 1. Two states of Yosys's model, one transition apart\n" ++
  String.intercalate "\n" states ++ "\n" ++
  "\n; 2. Inputs and registers of state s, read through the emitted port and register names\n" ++
  String.intercalate "\n" (inDefs ++ regDefs) ++ "\n" ++
  "\n; 3. Lean's model of the RtlModule (emitExprSmt2 of evalRtlExpr) over those values\n" ++
  String.intercalate "\n" wireDefs ++ (if wireDefs.isEmpty then "" else "\n") ++
  "\n; 4. Obligations: each output at s, each register at s1\n" ++
  String.intercalate "\n" (outDefs ++ regObls) ++ (if outDefs.isEmpty && regObls.isEmpty then "" else "\n") ++
  "\n; 5. Miter\n" ++ miter ++ "\n(check-sat)\n" ++
  "; --- counterexample (sent only after sat) ---\n" ++
  s!"(get-value ({String.intercalate " " cexTerms}))\n"

end Obend.Hardware.YosysLec
end
