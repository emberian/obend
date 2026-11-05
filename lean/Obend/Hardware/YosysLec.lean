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
them, and builds Lean's model of `m` over those values with `smtOf` (the `QF_BV` term of an
`RtlExpr`, proved equal to `evalRtlExpr` by `smtOf_sound`): every wire, every output truncated to its port width (`evalModuleOutputsW`), and every
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
public meta import Obend.Hardware.HDL
public meta import Obend.Hardware.VerilateRunner
@[expose] public section

namespace Obend.Hardware.YosysLec
open Obend.Hardware.HDL Obend.Hardware.VerilateRunner
set_option autoImplicit false


/-! ## The SMT-LIB terms the LEC file contains, as a Lean model

The Lean half of the LEC is not trusted text. `SmtBV w` is the fragment of `QF_BV` the file uses,
`SmtBV.eval` is its SMT-LIB semantics on Lean's `BitVec w` (`bvudiv` by zero is all-ones and `bvurem`
by zero the dividend, as SMT-LIB defines them; `RtlAluOp` has neither), `smtOf` maps an `RtlExpr`
to a term, and `emitExprSmt2_sound` (from `smtOf_sound` and `inferWidthE_faithful`) proves the
term means `evalRtlExpr` for every expression `inferWidthE` accepts. `emitYosysLecSmt2` prints `smtOf`, so the file is the model's
print. What remains trusted is that `SmtBV.print` writes the SMT-LIB syntax of the constructor it
prints, Yosys's frontend, and z3. The `#guard`s at the end compare the print of `smtOf e` with
`VerilateRunner.emitExprSmt2` (the BEL miter's printer) on every constructor and operator. -/

inductive SmtVar where
  | inp | wire | reg
  deriving DecidableEq, Repr

inductive SmtBinOp where
  | add | sub | mul | and | or | xor | shl | lshr | ashr | udiv | urem
  deriving DecidableEq, Repr

mutual
inductive SmtBV : Nat → Type where
  | lit (v : BitVec 64) : SmtBV 64
  | var (k : SmtVar) (i : Nat) : SmtBV 64
  | bin {w : Nat} (op : SmtBinOp) (a b : SmtBV w) : SmtBV w
  | not {w : Nat} (a : SmtBV w) : SmtBV w
  | ite {w : Nat} (c : SmtBool) (t f : SmtBV w) : SmtBV w
  | extract {w : Nat} (hi lo : Nat) (a : SmtBV w) : SmtBV (hi - lo + 1)
  | zeroExtend {w : Nat} (k : Nat) (a : SmtBV w) : SmtBV (w + k)
  | signExtend {w : Nat} (k : Nat) (a : SmtBV w) : SmtBV (w + k)
  | cast {w w' : Nat} (h : w = w') (a : SmtBV w) : SmtBV w'
inductive SmtBool : Type where
  | eq {w : Nat} (a b : SmtBV w) : SmtBool
  | distinct {w : Nat} (a b : SmtBV w) : SmtBool
  | ult {w : Nat} (a b : SmtBV w) : SmtBool
  | slt {w : Nat} (a b : SmtBV w) : SmtBool
end

structure SmtEnv where
  inp  : Nat → BitVec 64
  wire : Nat → BitVec 64
  reg  : Nat → BitVec 64

def SmtEnv.get (env : SmtEnv) : SmtVar → Nat → BitVec 64
  | .inp => env.inp | .wire => env.wire | .reg => env.reg

def SmtBinOp.eval {w : Nat} : SmtBinOp → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< b
  | .lshr, a, b => a >>> b
  | .ashr, a, b => a.sshiftRight' b
  | .udiv, a, b => a.smtUDiv b
  | .urem, a, b => a % b

mutual
def SmtBV.eval (env : SmtEnv) : {w : Nat} → SmtBV w → BitVec w
  | _, .lit v => v
  | _, .var k i => env.get k i
  | _, .bin op a b => op.eval (a.eval env) (b.eval env)
  | _, .not a => ~~~(a.eval env)
  | _, .ite c t f => if c.eval env then t.eval env else f.eval env
  | _, .extract hi lo a => (a.eval env).extractLsb hi lo
  | _, .zeroExtend k a => (a.eval env).setWidth _
  | _, .signExtend k a => (a.eval env).signExtend _
  | _, .cast h a => (a.eval env).cast h
def SmtBool.eval (env : SmtEnv) : SmtBool → Bool
  | .eq a b => a.eval env == b.eval env
  | .distinct a b => a.eval env != b.eval env
  | .ult a b => (a.eval env).ult (b.eval env)
  | .slt a b => (a.eval env).slt (b.eval env)
end


def mask64 (w : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ (min w 64) - 1)

def smtAlu (op : RtlAluOp) (a b : SmtBV 64) : SmtBV 64 :=
  match op with
  | .add    => .bin .add a b
  | .sub    => .bin .sub a b
  | .mul    => .bin .mul a b
  | .bitAnd => .bin .and a b
  | .bitOr  => .bin .or a b
  | .bitXor => .bin .xor a b
  | .shl    => .bin .shl a (.bin .and b (.lit 63#64))
  | .lshr   => .bin .lshr a (.bin .and b (.lit 63#64))
  | .ashr   => .bin .ashr a (.bin .and b (.lit 63#64))
  | .eq     => .ite (.eq a b) (.lit 1#64) (.lit 0#64)
  | .ult    => .ite (.ult a b) (.lit 1#64) (.lit 0#64)
  | .slt    => .ite (.slt a b) (.lit 1#64) (.lit 0#64)
  | .qmul32 => .cast (by decide) (.extract 95 32 (.bin .mul (.signExtend 64 a) (.signExtend 64 b)))

def smtWidth (op : RtlWidthOp) (x : SmtBV 64) : SmtBV 64 :=
  match op with
  | .slice hi lo => .bin .and (.bin .lshr x (.lit (BitVec.ofNat 64 lo))) (.lit (mask64 (hi + 1 - lo)))
  | .zext _ => x
  | .sext f t =>
    if h : 0 < f ∧ f ≤ t ∧ t ≤ 64 then
      .cast (by omega) (.zeroExtend (64 - t) (.signExtend (t - f) (.extract (f - 1) 0 x)))
    else x
  | .trunc w => .bin .and x (.lit (mask64 w))

def smtOf : RtlExpr → SmtBV 64
  | .const v       => .lit v
  | .inputPort idx => .var .inp idx
  | .wireRef idx   => .var .wire idx
  | .regRead idx   => .var .reg idx
  | .alu op a b    => smtAlu op (smtOf a) (smtOf b)
  | .mux c t f     => .ite (.distinct (smtOf c) (.lit 0#64)) (smtOf t) (smtOf f)
  | .bitNot a      => .not (smtOf a)
  | .resize op a   => smtWidth op (smtOf a)

/-- The width-operator parameters for which the emitted SMT term means `evalWidthOp` (what
`widthOpWidth` accepts implies it). -/
def widthFaithful : RtlWidthOp → Bool
  | .slice _ lo => decide (lo < 64)
  | .sext f t => decide (0 < f ∧ f ≤ t ∧ t ≤ 64)
  | _ => true

def smtFaithful : RtlExpr → Bool
  | .const _ | .inputPort _ | .wireRef _ | .regRead _ => true
  | .alu _ a b => smtFaithful a && smtFaithful b
  | .mux c t f => smtFaithful c && smtFaithful t && smtFaithful f
  | .bitNot a => smtFaithful a
  | .resize op a => widthFaithful op && smtFaithful a

theorem and63 (b : BitVec 64) : (b &&& 63#64).toNat = b.toNat % 64 := by
  have := Nat.and_two_pow_sub_one_eq_mod b.toNat 6
  simp only [BitVec.toNat_and]; simpa using this

theorem smtAlu_sound (env : SmtEnv) (op : RtlAluOp) (a b : SmtBV 64) :
    (smtAlu op a b).eval env = evalAluOp op (a.eval env) (b.eval env) := by
  cases op <;> simp only [smtAlu, SmtBV.eval, SmtBool.eval, SmtBinOp.eval, evalAluOp]
  · rw [BitVec.shiftLeft_eq', and63]
  · rw [BitVec.ushiftRight_eq', and63]
  · simp only [BitVec.sshiftRight', and63]
  · simp
  · rfl
  · rfl
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb_toNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]

theorem mask64_eq (w : Nat) (v : BitVec 64) : v &&& mask64 w = truncToWidth w v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [truncToWidth, mask64, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, Nat.testBit_two_pow_sub_one]
  simp only [hi, decide_true, Bool.true_and]
  congr 1
  simp only [decide_eq_decide]
  omega

theorem sext_sound (f t : Nat) (h : 0 < f ∧ f ≤ t ∧ t ≤ 64) (x : BitVec 64) :
    BitVec.cast (by omega : (f - 1 - 0 + 1) + (t - f) + (64 - t) = 64)
      (((x.extractLsb (f - 1) 0).signExtend ((f - 1 - 0 + 1) + (t - f))).setWidth
        ((f - 1 - 0 + 1) + (t - f) + (64 - t)))
      = ((x.setWidth f).signExtend t).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_extractLsb, BitVec.msb_eq_getLsbD_last]
  have e1 : f - 1 - 0 + 1 = f := by omega
  have e2 : f + (t - f) = t := by omega
  have e3 : t + (64 - t) = 64 := by omega
  simp only [e1, e2, e3, Nat.zero_add]

theorem smtWidth_sound (env : SmtEnv) (op : RtlWidthOp) (x : SmtBV 64) (h : widthFaithful op = true) :
    (smtWidth op x).eval env = evalWidthOp op (x.eval env) := by
  cases op with
  | slice hi lo =>
    simp only [widthFaithful, decide_eq_true_eq] at h
    simp only [smtWidth, SmtBV.eval, SmtBinOp.eval, evalWidthOp, mask64_eq]
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  | zext w => rfl
  | sext f t =>
    simp only [widthFaithful, decide_eq_true_eq] at h
    simp only [smtWidth, h, and_self, dite_true, SmtBV.eval, evalWidthOp]
    exact sext_sound f t h _
  | trunc w => simp only [smtWidth, SmtBV.eval, SmtBinOp.eval, evalWidthOp, mask64_eq]

theorem smtOf_sound (env : SmtEnv) (e : RtlExpr) (h : smtFaithful e = true) :
    (smtOf e).eval env = evalRtlExpr env.inp env.wire env.reg e := by
  induction e with
  | const v => rfl
  | inputPort i => rfl
  | wireRef i => rfl
  | regRead i => rfl
  | alu op a b iha ihb =>
    simp only [smtFaithful, Bool.and_eq_true] at h
    simp only [smtOf, evalRtlExpr, smtAlu_sound, iha h.1, ihb h.2]
  | mux c t f ihc iht ihf =>
    simp only [smtFaithful, Bool.and_eq_true] at h
    simp only [smtOf, evalRtlExpr, SmtBV.eval, SmtBool.eval, ihc h.1.1, iht h.1.2, ihf h.2]
  | bitNot a iha =>
    simp only [smtFaithful] at h
    simp only [smtOf, evalRtlExpr, SmtBV.eval, iha h]
  | resize op a iha =>
    simp only [smtFaithful, Bool.and_eq_true] at h
    simp only [smtOf, evalRtlExpr, smtWidth_sound env op _ h.1, iha h.2]

theorem widthOpWidth_faithful (op : RtlWidthOp) (wa w : Nat) (h : widthOpWidth op wa = .ok w) :
    widthFaithful op = true := by
  cases op <;> simp only [widthOpWidth] at h <;> simp only [widthFaithful, decide_eq_true_eq]
  all_goals first | trivial | (split at h <;> first | omega | (simp at h))

theorem inferWidthE_faithful (env : WidthEnv) (e : RtlExpr) (w : Nat) (h : inferWidthE env e = .ok w) :
    smtFaithful e = true := by
  induction e generalizing w with
  | const v => rfl
  | inputPort i => rfl
  | wireRef i => rfl
  | regRead i => rfl
  | alu op a b iha ihb =>
    simp only [inferWidthE] at h
    split at h <;> simp_all [smtFaithful]
  | mux c t f ihc iht ihf =>
    simp only [inferWidthE] at h
    split at h <;> simp_all [smtFaithful]
  | bitNot a iha =>
    simp only [inferWidthE] at h
    split at h <;> simp_all [smtFaithful]
  | resize op a iha =>
    simp only [inferWidthE] at h
    split at h
    · simp only [smtFaithful, Bool.and_eq_true]
      exact ⟨widthOpWidth_faithful op _ w h, iha _ (by assumption)⟩
    · simp at h

/-- The LEC's Lean half means the `RtlModule`: for every expression the width check accepts, the
SMT-LIB semantics of the term the file contains is `evalRtlExpr` (with `in_i`, `spec_w_i`, `r_i`
read as `inputs i`, `wires i`, `regs i`). -/
theorem emitExprSmt2_sound (inputs wires regs : Nat → BitVec 64) (wenv : WidthEnv) (e : RtlExpr)
    (w : Nat) (h : inferWidthE wenv e = .ok w) :
    (smtOf e).eval ⟨inputs, wires, regs⟩ = evalRtlExpr inputs wires regs e :=
  smtOf_sound ⟨inputs, wires, regs⟩ e (inferWidthE_faithful wenv e w h)

/-! ### Printing: the SMT-LIB2 text of a term, which the LEC file is -/

def SmtBinOp.name : SmtBinOp → String
  | .add => "bvadd" | .sub => "bvsub" | .mul => "bvmul" | .and => "bvand" | .or => "bvor"
  | .xor => "bvxor" | .shl => "bvshl" | .lshr => "bvlshr" | .ashr => "bvashr"
  | .udiv => "bvudiv" | .urem => "bvurem"

mutual
/-- SMT-LIB2 text of a term; `pfx` is the prefix of wire names (`spec_` in the LEC file). -/
def SmtBV.print (pfx : String) : {w : Nat} → SmtBV w → String
  | _, .lit v => bitVec64ToSmtHex v
  | _, .var .inp i => s!"in_{i}"
  | _, .var .wire i => s!"{pfx}w_{i}"
  | _, .var .reg i => s!"r_{i}"
  | _, .bin op a b => s!"({op.name} {a.print pfx} {b.print pfx})"
  | _, .not a => s!"(bvnot {a.print pfx})"
  | _, .ite c t f => s!"(ite {c.print pfx} {t.print pfx} {f.print pfx})"
  | _, .extract hi lo a => s!"((_ extract {hi} {lo}) {a.print pfx})"
  | _, .zeroExtend k a => s!"((_ zero_extend {k}) {a.print pfx})"
  | _, .signExtend k a => s!"((_ sign_extend {k}) {a.print pfx})"
  | _, .cast _ a => a.print pfx
def SmtBool.print (pfx : String) : SmtBool → String
  | .eq a b => s!"(= {a.print pfx} {b.print pfx})"
  | .distinct a b => s!"(distinct {a.print pfx} {b.print pfx})"
  | .ult a b => s!"(bvult {a.print pfx} {b.print pfx})"
  | .slt a b => s!"(bvslt {a.print pfx} {b.print pfx})"
end

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
  let next := (smtOf r.nextExpr).print "spec_"
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
    s!"(define-fun spec_w_{w.wireIdx} () (_ BitVec 64) {(smtOf w.expr).print "spec_"})"
  let outDefs := m.outputs.flatMap fun o =>
    [ s!"(define-fun |rtl_out_{o.name}| () (_ BitVec {o.width}) {yosysBv o.width (yosysSig mod o.name "s")})"
    , s!"(define-fun |spec_out_{o.name}| () (_ BitVec {o.width}) {lowBits o.width ((smtOf o.expr).print "spec_")})"
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
  "\n; 3. Lean's model of the RtlModule over those values (smtOf; smtOf_sound proves it is evalRtlExpr)\n" ++
  String.intercalate "\n" wireDefs ++ (if wireDefs.isEmpty then "" else "\n") ++
  "\n; 4. Obligations: each output at s, each register at s1\n" ++
  String.intercalate "\n" (outDefs ++ regObls) ++ (if outDefs.isEmpty && regObls.isEmpty then "" else "\n") ++
  "\n; 5. Miter\n" ++ miter ++ "\n(check-sat)\n" ++
  "; --- counterexample (sent only after sat) ---\n" ++
  s!"(get-value ({String.intercalate " " cexTerms}))\n"


/-! ### Tests: the model's print against `emitExprSmt2`, constructor by constructor -/

/-- One expression per `RtlExpr` constructor, `RtlAluOp` and `RtlWidthOp` (and the out-of-range
`sext` the emitter prints as its operand). -/
def printProbes : List RtlExpr :=
  let a : RtlExpr := .inputPort 0
  let b : RtlExpr := .regRead 2
  let ops : List RtlAluOp :=
    [.add, .sub, .mul, .bitAnd, .bitOr, .bitXor, .shl, .lshr, .ashr, .eq, .ult, .slt, .qmul32]
  ops.map (fun op => .alu op a b) ++
  [ .const 0xdeadbeef#64, .wireRef 7, .mux (.wireRef 1) a b, .bitNot (.alu .add a (.const 1#64)),
    .resize (.slice 15 4) a, .resize (.zext 32) b, .resize (.sext 8 32) a, .resize (.sext 0 9) a,
    .resize (.trunc 12) (.alu .mul a b),
    .mux (.alu .ult a b) (.resize (.sext 16 64) (.alu .qmul32 a b)) (.bitNot (.resize (.slice 63 32) b)) ]

#guard printProbes.all fun e => (smtOf e).print "spec_" == emitExprSmt2 "spec_" e
#guard (smtOf (.alu .shl (.inputPort 0) (.regRead 1))).print "spec_" ==
  "(bvshl in_0 (bvand r_1 #x000000000000003f))"
#guard (smtOf (.resize (.sext 8 32) (.wireRef 3))).print "spec_" ==
  "((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) spec_w_3)))"

/-- SMT-LIB's division by zero, which the model follows: all-ones quotient, dividend remainder. -/
example : (SmtBV.bin .udiv (.lit 5#64) (.lit 0#64)).eval ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ =
    BitVec.allOnes 64 := by decide
example : (SmtBV.bin .urem (.lit 5#64) (.lit 0#64)).eval ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ = 5#64 := by
  decide

end Obend.Hardware.YosysLec
end
