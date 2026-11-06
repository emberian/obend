module
/-
# Obend.Hardware.YosysLec — logic equivalence of an emitted `.sv` against Lean's model of its `RtlModule`

`emitYosysLecSmt2 m = (lecScript m).print` is the second half of an SMT-LIB2 query whose first half
is Yosys's reading of `emitModuleSV m` (`hardware/lec/lec.sh`):

    yosys -p "read_verilog -sv X.sv; hierarchy -check -top X; proc; flatten; ...; write_smt2 X.yosys.smt2"
    cat X.yosys.smt2 X_lec.smt2 | z3 -in        # unsat = equivalent

Yosys's half declares a state sort `|X_s|`, an accessor `|X_n p|` for every port and register `p`,
and the transition relation `|X_t|`. The Lean half is one value, `lecScript m : LecScript`: two
states `s`, `s1` with `(|X_t| s s1)`, the inputs and registers of `s` read through the names
`emitModuleSV` gives them (zero-extended from their widths), Lean's model of every wire, output and
next register value as `QF_BV` terms (`smtOf`, equal to `evalRtlExpr` by `emitExprSmt2_sound`), and
a miter asserting that some output in `s` or some register in `s1` differs.

What is proved:
* `lecScript_holds_iff`: for every assignment z3 may choose, the script holds exactly when both Yosys
  assertions hold and some output Yosys reads in `s`, or register it reads in `s1`, differs at its
  width from Lean's step (`regNextValue` per register, each reset by its own domain's `rst_<d>`) on
  the inputs and registers read in `s`. So `unsat` is agreement and `sat` is a real disagreement.
* `lecScript_unsat_of_step`: for a one-domain module with distinct register indices, the same
  statement against `evalModuleOutputsW` and `stepModuleRegs` (and so `stepModuleDomain`, by
  `stepModuleDomain_eq_of_single`).
* `moduleFaithful_of_checkWidths`: the emission gate (`checkRtlModuleW`, which includes
  `checkWidths`) implies the theorems' hypothesis, so `obend-emit-sv --lec` has one check.

Which clocking it checks: Yosys's `write_smt2` has one global clock (every flip-flop latches on
every transition) and the Lean half resets each register by its domain's `rst_<d>`. For several
clock domains that is all clocks rising together, with the resets free; the edge-by-edge semantics
`stepModuleDomain` gives (one domain latches, the others hold) is not what the LEC checks.

What it trusts: Yosys's SystemVerilog frontend and `write_smt2`, z3, and that `LecScript.print` and
`SmtBV.print` write the SMT-LIB syntax of what they print (pinned, not proved, by
`lean/tests/silicon_elab/YosysLecTest.lean`). Read into the model, not proved: narrow ports and
registers are zero-extended into the 64-bit carrier.
-/
public import Obend.Hardware.HDL
public import Obend.Hardware.VerilateRunner
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
print. The whole file is one value, `lecScript m`, whose meaning `lecScript_holds_iff` states.
What remains trusted is that `LecScript.print` and `SmtBV.print` write the SMT-LIB syntax of what
they print, Yosys's frontend, and z3; `lean/tests/silicon_elab/YosysLecTest.lean` pins the print
against `VerilateRunner.emitExprSmt2` and against committed files. -/

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
  /-- A literal of a width other than 64 (`#b...`); the file uses `#b1` and `#b0`. -/
  | bits {w : Nat} (v : BitVec w) : SmtBV w
  /-- Yosys's accessor `(|mod_n port| s)` (`next = false`) or `... s1)` (`next = true`) of a
  `w`-bit signal, `w > 1` (Yosys gives 1-bit signals sort `Bool`: `SmtBool.yosys`). -/
  | yosys (mod port : String) (next : Bool) (w : Nat) : SmtBV w
inductive SmtBool : Type where
  | eq {w : Nat} (a b : SmtBV w) : SmtBool
  | distinct {w : Nat} (a b : SmtBV w) : SmtBool
  | ult {w : Nat} (a b : SmtBV w) : SmtBool
  | slt {w : Nat} (a b : SmtBV w) : SmtBool
  /-- Yosys's accessor of a 1-bit signal, which has sort `Bool`. -/
  | yosys (mod port : String) (next : Bool) : SmtBool
end

/-- What the terms read: the `in_i`, `spec_w_i` and `r_i` the file defines, and Yosys's signals in
the two states (`sig next port` as a number, read at the signal's width; `bit` for 1-bit signals). -/
structure SmtEnv where
  inp  : Nat → BitVec 64
  wire : Nat → BitVec 64
  reg  : Nat → BitVec 64
  sig  : Bool → String → Nat := fun _ _ => 0
  bit  : Bool → String → Bool := fun _ _ => false

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
  | _, .bits v => v
  | _, .yosys _ port next w => BitVec.ofNat w (env.sig next port)
def SmtBool.eval (env : SmtEnv) : SmtBool → Bool
  | .eq a b => a.eval env == b.eval env
  | .distinct a b => a.eval env != b.eval env
  | .ult a b => (a.eval env).ult (b.eval env)
  | .slt a b => (a.eval env).slt (b.eval env)
  | .yosys _ port next => env.bit next port
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
    (smtOf e).eval { inp := inputs, wire := wires, reg := regs } = evalRtlExpr inputs wires regs e :=
  smtOf_sound { inp := inputs, wire := wires, reg := regs } e (inferWidthE_faithful wenv e w h)

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
  | w, .bits v => "#b" ++ String.ofList ((List.range w).reverse.map fun i => if v.getLsbD i then '1' else '0')
  | _, .yosys mod port next _ => s!"(|{mod}_n {port}| {if next then "s1" else "s"})"
def SmtBool.print (pfx : String) : SmtBool → String
  | .eq a b => s!"(= {a.print pfx} {b.print pfx})"
  | .distinct a b => s!"(distinct {a.print pfx} {b.print pfx})"
  | .ult a b => s!"(bvult {a.print pfx} {b.print pfx})"
  | .slt a b => s!"(bvslt {a.print pfx} {b.print pfx})"
  | .yosys mod port next => s!"(|{mod}_n {port}| {if next then "s1" else "s"})"
end

/-! ## The whole Lean half as one Lean value

`LecScript` is the file: every definition and assertion is a field holding a term, `print` writes
the file, and `holds` is what z3 is asked to satisfy. `lecScript m` builds it from the `RtlModule`;
`emitYosysLecSmt2 m = (lecScript m).print`. The `get-value` block after `(check-sat)` and the
comment lines are printed but carry no meaning. -/

/-- One output obligation: `rtl` is Yosys's port, `spec` Lean's value at the port's width. -/
structure OutObl where
  name : String
  w    : Nat
  rtl  : SmtBV w
  spec : SmtBV w

/-- One register obligation: Yosys's value in `s1` against Lean's next value, at the register's
declared width. -/
structure RegObl where
  name : String
  w    : Nat
  rtl  : SmtBV w
  spec : SmtBV w

structure LecScript where
  mod     : String
  header  : String
  /-- `(define-fun in_i () (_ BitVec 64) t)`, over Yosys's accessors in `s`. -/
  inputs  : List (Nat × SmtBV 64)
  /-- `r_k`: `some t` is `(define-fun r_k () (_ BitVec 64) t)`, `none` a free `declare-const`. -/
  slots   : List (Nat × Option (SmtBV 64))
  /-- `(define-fun spec_w_i () (_ BitVec 64) t)`, in order. -/
  wires   : List (Nat × SmtBV 64)
  outputs : List OutObl
  regs    : List RegObl
  /-- The reset accessors listed in the counterexample query. -/
  resets  : List SmtBool

/-- An assignment z3 may choose: Yosys's signals in `s` and `s1`, the truth of `|mod_h| s` and
`|mod_t| s s1`, and the free `r_k`. -/
structure LecAssign where
  sig  : Bool → String → Nat
  bit  : Bool → String → Bool
  h    : Bool
  t    : Bool
  free : Nat → BitVec 64

/-- Yosys's signals alone, the environment of the `in_i` and `r_k` definitions. -/
def LecAssign.base (Y : LecAssign) : SmtEnv :=
  { inp := fun _ => 0, wire := fun _ => 0, reg := fun _ => 0, sig := Y.sig, bit := Y.bit }

def LecScript.inpVal (S : LecScript) (Y : LecAssign) (i : Nat) : BitVec 64 :=
  match S.inputs.find? (·.1 == i) with
  | some (_, t) => t.eval Y.base
  | none => 0

def LecScript.regVal (S : LecScript) (Y : LecAssign) (k : Nat) : BitVec 64 :=
  match S.slots.find? (·.1 == k) with
  | some (_, some t) => t.eval Y.base
  | some (_, none) => Y.free k
  | none => 0

/-- The `spec_w_i` definitions in order, each over the ones before it (a later or missing wire is
a name z3 rejects; here it reads `0#64`, as `evalWireTable` does). -/
def wireFold (inp reg : Nat → BitVec 64) (sig : Bool → String → Nat) (bit : Bool → String → Bool)
    (ws : List (Nat × SmtBV 64)) : Nat → BitVec 64 :=
  ws.foldl (fun env (i, t) =>
      let v := t.eval { inp := inp, wire := env, reg := reg, sig := sig, bit := bit }
      fun j => if j == i then v else env j)
    (fun _ => 0#64)

/-- The environment every obligation term is evaluated in. -/
def LecScript.env (S : LecScript) (Y : LecAssign) : SmtEnv :=
  { inp := S.inpVal Y, reg := S.regVal Y,
    wire := wireFold (S.inpVal Y) (S.regVal Y) Y.sig Y.bit S.wires, sig := Y.sig, bit := Y.bit }

/-- What z3 is asked: both Yosys assertions hold and the miter `(not (and true lec_...))` holds,
i.e. some obligation's two sides differ. -/
def LecScript.holds (S : LecScript) (Y : LecAssign) : Prop :=
  Y.h = true ∧ Y.t = true ∧
  ¬ ((∀ o ∈ S.outputs, o.rtl.eval (S.env Y) = o.spec.eval (S.env Y)) ∧
     (∀ r ∈ S.regs, r.rtl.eval (S.env Y) = r.spec.eval (S.env Y)))

def LecScript.print (S : LecScript) : String :=
  let mod := S.mod
  let states :=
    [ s!"(declare-const s |{mod}_s|)"
    , s!"(declare-const s1 |{mod}_s|)"
    , s!"(assert (|{mod}_h| s))"
    , s!"(assert (|{mod}_t| s s1))" ]
  let inDefs := S.inputs.map fun (i, t) => s!"(define-fun in_{i} () (_ BitVec 64) {t.print "spec_"})"
  let regDefs := S.slots.map fun (k, t?) =>
    match t? with
    | some t => s!"(define-fun r_{k} () (_ BitVec 64) {t.print "spec_"})"
    | none => s!"(declare-const r_{k} (_ BitVec 64))"
  let wireDefs := S.wires.map fun (i, t) => s!"(define-fun spec_w_{i} () (_ BitVec 64) {t.print "spec_"})"
  let outDefs := S.outputs.flatMap fun o =>
    [ s!"(define-fun |rtl_out_{o.name}| () (_ BitVec {o.w}) {o.rtl.print "spec_"})"
    , s!"(define-fun |spec_out_{o.name}| () (_ BitVec {o.w}) {o.spec.print "spec_"})"
    , s!"(define-fun |lec_out_{o.name}| () Bool (= |rtl_out_{o.name}| |spec_out_{o.name}|))" ]
  let regObls := S.regs.flatMap fun r =>
    [ s!"(define-fun |rtl_next_{r.name}| () (_ BitVec {r.w}) {r.rtl.print "spec_"})"
    , s!"(define-fun |spec_next_{r.name}| () (_ BitVec {r.w}) {r.spec.print "spec_"})"
    , s!"(define-fun |lec_next_{r.name}| () Bool (= |rtl_next_{r.name}| |spec_next_{r.name}|))" ]
  let obls := S.outputs.map (fun o => s!"|lec_out_{o.name}|") ++ S.regs.map (fun r => s!"|lec_next_{r.name}|")
  let miter :=
    if obls.isEmpty then "(assert false)"
    else s!"(assert (not (and true {String.intercalate " " obls})))"
  let cexTerms :=
    S.inputs.map (fun (i, _) => s!"in_{i}") ++ S.resets.map (·.print "spec_") ++
    S.slots.map (fun (k, _) => s!"r_{k}") ++
    S.outputs.flatMap (fun o => [s!"|lec_out_{o.name}|", s!"|rtl_out_{o.name}|", s!"|spec_out_{o.name}|"]) ++
    S.regs.flatMap (fun r => [s!"|lec_next_{r.name}|", s!"|rtl_next_{r.name}|", s!"|spec_next_{r.name}|"])
  S.header ++
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

/-! ### The script of an `RtlModule` -/

/-- A `w`-bit Yosys signal as an `(_ BitVec w)` term (1-bit signals are `Bool` in Yosys). -/
def yosysBV (mod port : String) (next : Bool) (w : Nat) : SmtBV w :=
  if h : w = 1 then .cast h.symm (SmtBV.ite (.yosys mod port next) (.bits 1#1) (.bits 0#1))
  else .yosys mod port next w

/-- A `w`-bit Yosys signal in `s` as the 64-bit word the module sees: zero-extended when narrower. -/
def wordTerm (mod port : String) (w : Nat) : SmtBV 64 :=
  if h : w = 64 then .cast h (yosysBV mod port false w)
  else if h' : w < 64 then .cast (by omega) (.zeroExtend (64 - w) (yosysBV mod port false w))
  else .yosys mod port false 64

/-- Input `i` as the 64-bit word the module sees: the port, zero-extended when narrower. -/
def inputTerm (m : RtlModule) (i : Nat) : SmtBV 64 :=
  wordTerm m.name (m.inputNames.getD i s!"in_{i}") (inputWidth m i)

/-- The reset port that governs register `r` in `emitModuleSV m`. -/
def resetPortOf (m : RtlModule) (r : RegSpec) : String :=
  if (moduleDomains m).length > 1 then s!"rst_{r.domain.portSuffix}" else "rst"

/-- The register that writes state slot `k` (the last one in `m.regs`, as in `stepModuleRegs`). -/
def regOfSlot (m : RtlModule) (k : Nat) : Option RegSpec :=
  m.regs.foldl (fun acc r => if r.regIdx == k then some r else acc) none

/-- Lean's next value of `r`: `nextExpr`, or its reset value while its domain's reset is high. -/
def regNextTerm (m : RtlModule) (r : RegSpec) : SmtBV 64 :=
  match r.resetKind with
  | .resetFree => smtOf r.nextExpr
  | .syncReset v => .ite (.yosys m.name (resetPortOf m r) false) (.lit v) (smtOf r.nextExpr)

/-- The low `w` bits of a 64-bit term, as an `(_ BitVec w)` term (`w` in 1..64). -/
def lowBitsTerm (w : Nat) (t : SmtBV 64) : SmtBV w :=
  if h : w = 64 then .cast h.symm t
  else if h' : 0 < w then .cast (by omega) (.extract (w - 1) 0 t)
  else .bits 0#w

def lecScript (m : RtlModule) : LecScript :=
  let mod := m.name
  let nSlots := m.regs.foldl (fun acc r => max acc (r.regIdx + 1)) m.regs.length
  let domains := moduleDomains m
  let resets := if domains.length > 1 then domains.map fun d => s!"rst_{d.portSuffix}" else ["rst"]
  { mod := mod
    header :=
      s!"; Lean half of the LEC of {mod}: Obend.Hardware.YosysLec.emitYosysLecSmt2 over the RtlModule that emitModuleSV printed.\n" ++
      s!"; Append to Yosys `write_smt2` of the emitted .sv; unsat = every output and next register agrees with Lean's model.\n" ++
      s!"; Module: {mod} (inputs={m.inputNames.length}, wires={m.wires.length}, regs={m.regs.length}, outputs={m.outputs.length})\n"
    inputs := (List.range m.inputNames.length).map fun i => (i, inputTerm m i)
    slots := (List.range nSlots).map fun k => (k, (regOfSlot m k).map fun r => wordTerm mod r.name r.width)
    wires := m.wires.map fun w => (w.wireIdx, smtOf w.expr)
    outputs := m.outputs.map fun o =>
      { name := o.name, w := o.width, rtl := yosysBV mod o.name false o.width,
        spec := lowBitsTerm o.width (smtOf o.expr) }
    regs := m.regs.map fun r =>
      { name := r.name, w := r.width, rtl := yosysBV mod r.name true r.width,
        spec := lowBitsTerm r.width (regNextTerm m r) }
    resets := if m.regs.isEmpty then [] else resets.map fun p => SmtBool.yosys mod p false }

/-- The Lean half of the LEC query for `m`: the print of `lecScript m`. Appended to Yosys's
`write_smt2` of `emitModuleSV m`, z3 answers `unsat` exactly when no assignment makes
`(lecScript m).holds` true. -/
def emitYosysLecSmt2 (m : RtlModule) : String :=
  (lecScript m).print

/-! ### What the script means -/

/-- Every expression of `m` has width parameters the SMT terms are faithful to (`inferWidthE`
acceptance implies it; `obend-emit-sv --lec` refuses a module without it). -/
def moduleFaithful (m : RtlModule) : Bool :=
  m.wires.all (fun w => smtFaithful w.expr) && m.outputs.all (fun o => smtFaithful o.expr) &&
    m.regs.all (fun r => smtFaithful r.nextExpr)

theorem wireFold_sound (ins regs : Nat → BitVec 64) (sig : Bool → String → Nat)
    (bit : Bool → String → Bool) (ws : List WireAssign) (h : ws.all (fun w => smtFaithful w.expr) = true) :
    wireFold ins regs sig bit (ws.map fun w => (w.wireIdx, smtOf w.expr)) = evalWireTable ins regs ws := by
  unfold wireFold evalWireTable
  generalize (fun _ => 0#64 : Nat → BitVec 64) = acc
  induction ws generalizing acc with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, List.foldl_cons]
    rw [smtOf_sound _ a.expr h.1]
    exact ih h.2 _

theorem lowBitsTerm_eval (env : SmtEnv) (w : Nat) (t : SmtBV 64) :
    (lowBitsTerm w t).eval env = (t.eval env).setWidth w := by
  unfold lowBitsTerm
  split
  · next h => subst h; simp [SmtBV.eval]
  · split
    · next h h' =>
      apply BitVec.eq_of_toNat_eq
      simp only [SmtBV.eval, BitVec.toNat_cast, BitVec.extractLsb_toNat, BitVec.toNat_setWidth,
        Nat.shiftRight_zero]
      congr 2; omega
    · next h h' =>
      have : w = 0 := by omega
      subst this; exact Subsingleton.elim _ _

/-- **The LEC file means the LEC.** For every assignment z3 may choose, the script holds exactly
when both Yosys assertions hold and some output Yosys reads in `s`, or some register it reads in
`s1`, differs from Lean's step of the `RtlModule` on the inputs and registers it reads in `s`
(each register reset by its domain's reset port). So if every one-step reading of the emitted
module agrees with Lean's step, the query is unsat; and a `sat` answer is a real disagreement. -/
theorem lecScript_holds_iff (m : RtlModule) (hf : moduleFaithful m = true) (Y : LecAssign) :
    (lecScript m).holds Y ↔
      Y.h = true ∧ Y.t = true ∧
      ¬ ((∀ o ∈ m.outputs,
            (yosysBV m.name o.name false o.width).eval ((lecScript m).env Y) =
              (evalRtlExpr ((lecScript m).inpVal Y)
                (evalWireTable ((lecScript m).inpVal Y) ((lecScript m).regVal Y) m.wires)
                ((lecScript m).regVal Y) o.expr).setWidth o.width) ∧
         (∀ r ∈ m.regs,
            (yosysBV m.name r.name true r.width).eval ((lecScript m).env Y) =
              (regNextValue (Y.bit false (resetPortOf m r)) ((lecScript m).inpVal Y)
                (evalWireTable ((lecScript m).inpVal Y) ((lecScript m).regVal Y) m.wires)
                ((lecScript m).regVal Y) r).setWidth r.width)) := by
  simp only [moduleFaithful, Bool.and_eq_true, List.all_eq_true] at hf
  obtain ⟨⟨hw, ho⟩, hr⟩ := hf
  have hwires : ((lecScript m).env Y).wire =
      evalWireTable ((lecScript m).inpVal Y) ((lecScript m).regVal Y) m.wires := by
    show wireFold _ _ _ _ (m.wires.map fun w => (w.wireIdx, smtOf w.expr)) = _
    exact wireFold_sound _ _ _ _ m.wires (List.all_eq_true.mpr hw)
  have hsound : ∀ e, smtFaithful e = true → (smtOf e).eval ((lecScript m).env Y) =
      evalRtlExpr ((lecScript m).inpVal Y)
        (evalWireTable ((lecScript m).inpVal Y) ((lecScript m).regVal Y) m.wires)
        ((lecScript m).regVal Y) e := by
    intro e he; rw [smtOf_sound _ e he, hwires]; rfl
  have hbit : ((lecScript m).env Y).bit = Y.bit := rfl
  unfold LecScript.holds
  generalize (lecScript m).env Y = E at hsound hbit ⊢
  generalize (lecScript m).inpVal Y = I at hsound ⊢
  generalize (lecScript m).regVal Y = R at hsound ⊢
  apply and_congr Iff.rfl; apply and_congr Iff.rfl; apply not_congr
  apply and_congr
  · simp only [lecScript, List.forall_mem_map]
    apply forall_congr'; intro o; apply imp_congr_right; intro hmem
    rw [lowBitsTerm_eval, hsound o.expr (ho o hmem)]
  · simp only [lecScript, List.forall_mem_map]
    apply forall_congr'; intro r; apply imp_congr_right; intro hmem
    have hn := hsound r.nextExpr (hr r hmem)
    rw [lowBitsTerm_eval]
    unfold regNextTerm regNextValue
    cases r.resetKind with
    | resetFree => rw [hn]
    | syncReset v => simp only [SmtBV.eval, SmtBool.eval, hbit]; rw [hn]

/-- The direction the LEC uses: if Lean's step and Yosys's reading agree on every assignment, no
assignment satisfies the script (z3 must answer unsat). -/
theorem lecScript_unsat_of_agree (m : RtlModule) (hf : moduleFaithful m = true)
    (hagree : ∀ Y : LecAssign, Y.h = true → Y.t = true →
      (∀ o ∈ m.outputs,
          (yosysBV m.name o.name false o.width).eval ((lecScript m).env Y) =
            (evalRtlExpr ((lecScript m).inpVal Y)
              (evalWireTable ((lecScript m).inpVal Y) ((lecScript m).regVal Y) m.wires)
              ((lecScript m).regVal Y) o.expr).setWidth o.width) ∧
      (∀ r ∈ m.regs,
          (yosysBV m.name r.name true r.width).eval ((lecScript m).env Y) =
            (regNextValue (Y.bit false (resetPortOf m r)) ((lecScript m).inpVal Y)
              (evalWireTable ((lecScript m).inpVal Y) ((lecScript m).regVal Y) m.wires)
              ((lecScript m).regVal Y) r).setWidth r.width)) :
    ∀ Y, ¬ (lecScript m).holds Y := by
  intro Y hY
  rw [lecScript_holds_iff m hf Y] at hY
  exact hY.2.2 (hagree Y hY.1 hY.2.1)

/-! ### The emission gate is the theorem's hypothesis -/

/-- The width check `checkRtlModuleW` runs at emission implies `moduleFaithful`. -/
theorem moduleFaithful_of_checkWidths (m : RtlModule) (h : checkWidths m = true) :
    moduleFaithful m = true := by
  unfold checkWidths at h
  have he : widthErrors m = [] := List.isEmpty_iff.mp h
  unfold widthErrors at he
  simp only [List.append_eq_nil_iff] at he
  obtain ⟨⟨⟨_, hw⟩, hr⟩, ho⟩ := he
  simp only [moduleFaithful, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun a ha => ?_, fun o ho' => ?_⟩, fun r hr' => ?_⟩
  · have := List.flatMap_eq_nil_iff.mp hw a ha
    simp only [List.append_eq_nil_iff] at this
    obtain ⟨w, hw', _⟩ := fitErrors_nil this.2
    exact inferWidthE_faithful _ _ w hw'
  · have := List.flatMap_eq_nil_iff.mp ho o ho'
    simp only [List.append_eq_nil_iff] at this
    obtain ⟨w, hw', _⟩ := fitErrors_nil this.2
    exact inferWidthE_faithful _ _ w hw'
  · have := List.flatMap_eq_nil_iff.mp hr r hr'
    simp only [List.append_eq_nil_iff] at this
    obtain ⟨w, hw', _⟩ := fitErrors_nil this.1.2
    exact inferWidthE_faithful _ _ w hw'

/-! ### Against the module's own step

Which clocking the LEC checks: Yosys's `write_smt2` has one global clock, every flip-flop
latching on every transition, and the Lean half resets each register by its own domain's
`rst_<d>`. For a module with one clock domain that is exactly `stepModuleRegs` (and
`stepModuleDomain`, by `stepModuleDomain_eq_of_single`), and `lecScript_unsat_of_step` below is
the LEC stated against it. For several domains the LEC checks every register's next value as if
all clocks rose together; it does not check the edge-by-edge semantics `stepModuleDomain` gives,
in which one domain latches while the others hold. -/

/-- A fold of register updates over registers none of which writes slot `i` leaves slot `i`. -/
theorem foldRegs_other (inputs wenv regState : Nat → BitVec 64) (rst : Bool) (i : Nat) :
    ∀ (l : List RegSpec) (st : Nat → BitVec 64), (∀ r ∈ l, r.regIdx ≠ i) →
      l.foldl (fun (nextSt : Nat → BitVec 64) r =>
          let v := match r.resetKind with
            | .resetFree => evalRtlExpr inputs wenv regState r.nextExpr
            | .syncReset initVal => if rst then initVal else evalRtlExpr inputs wenv regState r.nextExpr
          fun j => if j == r.regIdx then v else nextSt j) st i = st i := by
  intro l
  induction l with
  | nil => intro st _; rfl
  | cons a rest ih =>
    intro st h
    simp only [List.foldl_cons]
    rw [ih _ (fun r hr => h r (List.mem_cons_of_mem _ hr))]
    have : (i == a.regIdx) = false := by
      have := h a List.mem_cons_self; simp [Ne.symm this]
    simp [this]

/-- With distinct register indices, `stepModuleRegs` at a register's slot is that register's
`regNextValue`. -/
theorem stepModuleRegs_at (m : RtlModule) (rst : Bool) (inputs regState : Nat → BitVec 64)
    (hnd : (m.regs.map (·.regIdx)).Nodup) (r : RegSpec) (hr : r ∈ m.regs) :
    stepModuleRegs m rst inputs regState r.regIdx =
      regNextValue rst inputs (evalWireTable inputs regState m.wires) regState r := by
  unfold stepModuleRegs
  simp only
  generalize evalWireTable inputs regState m.wires = wenv
  generalize regState = st0 at *
  revert hnd hr
  generalize m.regs = l
  intro hnd hr
  suffices ∀ (st : Nat → BitVec 64), l.foldl (fun (nextSt : Nat → BitVec 64) r =>
          let v := match r.resetKind with
            | .resetFree => evalRtlExpr inputs wenv st0 r.nextExpr
            | .syncReset initVal => if rst then initVal else evalRtlExpr inputs wenv st0 r.nextExpr
          fun j => if j == r.regIdx then v else nextSt j) st r.regIdx =
        regNextValue rst inputs wenv st0 r from this st0
  induction l with
  | nil => simp at hr
  | cons a rest ih =>
    intro st
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with h | h
    · subst h
      rw [foldRegs_other inputs wenv st0 rst r.regIdx rest _ (fun x hx he => hnd.1 ⟨x, hx, he⟩)]
      simp only [beq_self_eq_true, ite_true, regNextValue]
      cases r.resetKind <;> rfl
    · exact ih hnd.2 h _

/-- A `w`-bit port value, zero-extended, is the port view `truncToWidth w` of a 64-bit value
exactly when it is that value's low `w` bits. -/
theorem setWidth64_eq_truncToWidth {w : Nat} (hw : w ≤ 64) (x : BitVec w) (v : BitVec 64) :
    x.setWidth 64 = truncToWidth w v ↔ x = v.setWidth w := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, truncToWidth_toNat w hw] at this
    rw [BitVec.toNat_setWidth, ← this]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hw))).symm
  · intro h
    subst h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, truncToWidth_toNat w hw]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w))
      (Nat.pow_le_pow_right (by decide) hw))

/-- **The LEC against the module's step (one clock domain).** If, in every pair of Yosys states
one transition apart, the outputs Yosys reads in `s` (zero-extended) are `evalModuleOutputsW`
and the registers it reads in `s1` are `stepModuleRegs` at their widths (with `rst` read in `s`),
all on the inputs and registers it reads in `s`, then no assignment satisfies the LEC script. -/
theorem lecScript_unsat_of_step (m : RtlModule) (hw : checkWidths m = true)
    (hp : checkPortWidths m = true) (hnd : (m.regs.map (·.regIdx)).Nodup)
    (h1 : (moduleDomains m).length ≤ 1)
    (hagree : ∀ Y : LecAssign, Y.h = true → Y.t = true →
      m.outputs.map (fun o =>
          (o.name, ((yosysBV m.name o.name false o.width).eval ((lecScript m).env Y)).setWidth 64)) =
        evalModuleOutputsW m ((lecScript m).inpVal Y) ((lecScript m).regVal Y) ∧
      ∀ r ∈ m.regs, (yosysBV m.name r.name true r.width).eval ((lecScript m).env Y) =
          (stepModuleRegs m (Y.bit false "rst") ((lecScript m).inpVal Y) ((lecScript m).regVal Y)
            r.regIdx).setWidth r.width) :
    ∀ Y, ¬ (lecScript m).holds Y := by
  apply lecScript_unsat_of_agree m (moduleFaithful_of_checkWidths m hw)
  intro Y hh ht
  obtain ⟨hout, hreg⟩ := hagree Y hh ht
  refine ⟨fun o ho => ?_, fun r hr => ?_⟩
  · unfold evalModuleOutputsW at hout
    simp only at hout
    have hwo : o.width ≤ 64 := by
      unfold checkPortWidths at hp
      simp only [Bool.and_eq_true, List.all_eq_true] at hp
      have := hp.2 o ho
      simp only [validWidth, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    have := (List.map_inj_left.mp hout) o ho
    simp only [Prod.mk.injEq, true_and] at this
    exact (setWidth64_eq_truncToWidth hwo _ _).mp this
  · have hrst : resetPortOf m r = "rst" := by
      unfold resetPortOf; simp [show ¬ (moduleDomains m).length > 1 by omega]
    rw [hreg r hr, stepModuleRegs_at m _ _ _ hnd r hr, hrst]

end Obend.Hardware.YosysLec
end
