module
/-
# Obend.Hardware.Compiler — General Compiler from `Obend.Core.Term` & `Obend.Leaf.Book` to `RtlModule`

Compiles Objective Bend `Term`s and `Obend.Leaf.Book` method/cell vtables directly
into the verified synchronous HDL (`Obend.Hardware.HDL.RtlModule`):
1. **Hardware Port Substitution (`substInputPort0`, `substInputPort0_sound`)**:
   - Inlines/specializes a compiled slot expression parameterized by `.inputPort 0` at any call-site
     argument expression `argExpr`, with universal soundness theorem `substInputPort0_sound`.
2. **De Bruijn, Inline-`let` (`(λx. body) arg`), and `self.m(arg)` Slot-Call Compiler (`compileTerm`)**:
   - Handles arbitrary nesting of:
     * `.app (.lam subBody) arg` (flattened `super` / `let` β-redexes),
     * `.app (.get (.bound selfDepth) member) arg` (method calls through `self`),
     * `.get (.bound selfDepth) member` (cell reads through `self`),
     * `.ifZero` successor binders (`predExpr :: varEnv` with `selfDepth + 1` shifting),
     * `.ifBool`, `.binary` (`add`, `multiply`, `subtract`, `equal`, `conjunction`, `less`, `lessEqual`),
     * `.bound idx`, `.nat`, and `.boolean`.
3. **Universal Structural Soundness Theorem (`compileTerm_sound`)**:
   - Proves by structural recursion on `t : Term` that for ANY `Term` in the compilable fragment,
     evaluating the compiled `RtlExpr` equals `evalTermHw`.
4. **Whole-Book Compiler (`compileBookToRtl`)**:
   - Compiles an entire `Obend.Leaf.Book` (such as `emit (comp 1)` from `ReviewMember.obend`) into a
     verified `RtlModule` and emits synthesizable SystemVerilog-2012 via `emitModuleSV`.
-/
public import Obend.Core.Term
public import Obend.Leaf.Emit
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware.Compiler
open Obend.Core.Term Obend.Leaf Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. Hardware Input-Port Substitution & Soundness (`substInputPort0`) -/

/-- Substitute `argExpr` for `.inputPort 0` throughout an `RtlExpr` (used when inlining a call
`self.m(arg)` to an earlier slot's compiled hardware body). -/
def substInputPort0 (argExpr : RtlExpr) : RtlExpr → RtlExpr
  | .const v       => .const v
  | .inputPort idx => if idx == 0 then argExpr else .inputPort idx
  | .wireRef idx   => .wireRef idx
  | .regRead idx   => .regRead idx
  | .alu op a b    => .alu op (substInputPort0 argExpr a) (substInputPort0 argExpr b)
  | .mux c t f     =>
    .mux (substInputPort0 argExpr c) (substInputPort0 argExpr t) (substInputPort0 argExpr f)
  | .bitNot a      => .bitNot (substInputPort0 argExpr a)

/-- Soundness of `substInputPort0`: evaluating `substInputPort0 argExpr e` is identical to evaluating
`e` with input port `0` bound to `evalRtlExpr inputs wires regs argExpr`. -/
theorem substInputPort0_sound
    (inputs wires regs : Nat → BitVec 64)
    (argExpr e : RtlExpr) :
    evalRtlExpr inputs wires regs (substInputPort0 argExpr e) =
      evalRtlExpr
        (fun i => if i == 0 then evalRtlExpr inputs wires regs argExpr else inputs i)
        wires regs e := by
  induction e with
  | const v => rfl
  | inputPort idx =>
    simp only [substInputPort0, evalRtlExpr]
    by_cases h : idx == 0 <;> simp [h, evalRtlExpr]
  | wireRef idx => rfl
  | regRead idx => rfl
  | alu op a b iha ihb =>
    simp only [substInputPort0, evalRtlExpr, iha, ihb]
  | mux c t f ihc iht ihf =>
    simp only [substInputPort0, evalRtlExpr, ihc, iht, ihf]
  | bitNot a iha =>
    simp only [substInputPort0, evalRtlExpr, iha]

/-! ## 2. Primitive Operations Compilation & Soundness -/

/-- Reference 64-bit hardware semantics for `Obend.Core.Term.Primitive`. -/
def evalPrimHw (op : Primitive) (a b : BitVec 64) : Option (BitVec 64) :=
  match op with
  | .add         => some (a + b)
  | .multiply    => some (a * b)
  | .subtract    => some (a - b)
  | .equal       => some (if a == b then 1#64 else 0#64)
  | .conjunction => some (a &&& b)
  | .less        => some (if BitVec.ult a b then 1#64 else 0#64)
  | .lessEqual   => some (if BitVec.ult b a then 0#64 else 1#64)
  | _            => none

/-- Compile an `Obend.Core.Term.Primitive` applied to two compiled `RtlExpr` operands. -/
def compilePrim (op : Primitive) (l r : RtlExpr) : Option RtlExpr :=
  match op with
  | .add         => some (.alu .add l r)
  | .multiply    => some (.alu .mul l r)
  | .subtract    => some (.alu .sub l r)
  | .equal       => some (.alu .eq l r)
  | .conjunction => some (.alu .bitAnd l r)
  | .less        => some (.alu .ult l r)
  | .lessEqual   => some (.mux (.alu .ult r l) (.const 0#64) (.const 1#64))
  | _            => none

/-- Soundness of `compilePrim`: evaluating the compiled `RtlExpr` matches `evalPrimHw`. -/
theorem compilePrim_sound
    (inputs wires regs : Nat → BitVec 64)
    (op : Primitive) (l r e : RtlExpr)
    (h : compilePrim op l r = some e) :
    evalPrimHw op (evalRtlExpr inputs wires regs l) (evalRtlExpr inputs wires regs r) =
      some (evalRtlExpr inputs wires regs e) := by
  cases op <;> simp [compilePrim, evalPrimHw] at h ⊢
  all_goals
    subst h
    simp [evalRtlExpr, evalAluOp]

/-! ## 3. General `Term` → `RtlExpr` Compiler & Structural Soundness Theorem -/

/-- Reference 64-bit hardware semantics for `Obend.Core.Term` under:
* `slots`: the book's slot member table (`Book.slots`),
* `slotBodies`: already-compiled slot expressions for `self.m(arg)` method calls,
* `inputs`, `slotWires`, `regs`: hardware port, wire, and register environments,
* `selfDepth`: current de Bruijn index of `self`,
* `varVals`: current 64-bit values of bound variables `0, 1, ...` inside the method body. -/
def evalTermHw
    (slots : List String)
    (slotBodies : List RtlExpr)
    (inputs slotWires regs : Nat → BitVec 64)
    (selfDepth : Nat)
    (varVals : List (BitVec 64)) : Term → Option (BitVec 64)
  | .nat n => some (BitVec.ofNat 64 n)
  | .boolean b => some (if b then 1#64 else 0#64)
  | .bound idx => varVals[idx]?
  | .get (.bound idx) member =>
    if idx == selfDepth then
      match slots.idxOf? member with
      | some slotIdx => some (slotWires slotIdx)
      | none => none
    else none
  | .app fn arg =>
    match fn with
    | .lam subBody =>
      match evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg with
      | some vArg =>
        evalTermHw slots slotBodies inputs slotWires regs (selfDepth + 1) (vArg :: varVals) subBody
      | none => none
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg with
        | some slotIdx, some vArg =>
          match slotBodies[slotIdx]? with
          | some slotExpr =>
            some (evalRtlExpr (fun i => if i == 0 then vArg else inputs i) slotWires regs slotExpr)
          | none => none
        | _, _ => none
      else none
    | _ => none
  | .binary op l r =>
    match evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals l,
          evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals r with
    | some vl, some vr => evalPrimHw op vl vr
    | _, _ => none
  | .ifBool c t f =>
    match evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals c,
          evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals t,
          evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals f with
    | some vc, some vt, some vf => some (if vc != 0#64 then vt else vf)
    | _, _, _ => none
  | .ifZero v z s =>
    match evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals v,
          evalTermHw slots slotBodies inputs slotWires regs selfDepth varVals z with
    | some vv, some vz =>
      match evalTermHw slots slotBodies inputs slotWires regs (selfDepth + 1) ((vv - 1#64) :: varVals) s with
      | some vs => some (if (if vv == 0#64 then 1#64 else 0#64) != 0#64 then vz else vs)
      | none => none
    | _, _ => none
  | _ => none

/-- Compile an `Obend.Core.Term` into a combinational `RtlExpr` under:
* `slots`: the book's slot member table (`Book.slots`),
* `slotBodies`: already-compiled slot expressions for `self.m(arg)` method calls,
* `selfDepth`: current de Bruijn index of `self`,
* `varEnv`: `RtlExpr` bound to each de Bruijn variable `0, 1, ...` in scope. -/
def compileTerm
    (slots : List String)
    (slotBodies : List RtlExpr)
    (selfDepth : Nat)
    (varEnv : List RtlExpr) : Term → Option RtlExpr
  | .nat n => some (.const (BitVec.ofNat 64 n))
  | .boolean b => some (.const (if b then 1#64 else 0#64))
  | .bound idx => varEnv[idx]?
  | .get (.bound idx) member =>
    if idx == selfDepth then
      match slots.idxOf? member with
      | some slotIdx => some (.wireRef slotIdx)
      | none => none
    else none
  | .app fn arg =>
    match fn with
    | .lam subBody =>
      match compileTerm slots slotBodies selfDepth varEnv arg with
      | some eArg =>
        compileTerm slots slotBodies (selfDepth + 1) (eArg :: varEnv) subBody
      | none => none
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              compileTerm slots slotBodies selfDepth varEnv arg with
        | some slotIdx, some eArg =>
          match slotBodies[slotIdx]? with
          | some slotExpr => some (substInputPort0 eArg slotExpr)
          | none => none
        | _, _ => none
      else none
    | _ => none
  | .binary op l r =>
    match compileTerm slots slotBodies selfDepth varEnv l,
          compileTerm slots slotBodies selfDepth varEnv r with
    | some el, some er => compilePrim op el er
    | _, _ => none
  | .ifBool c t f =>
    match compileTerm slots slotBodies selfDepth varEnv c,
          compileTerm slots slotBodies selfDepth varEnv t,
          compileTerm slots slotBodies selfDepth varEnv f with
    | some ec, some et, some ef => some (.mux ec et ef)
    | _, _, _ => none
  | .ifZero v z s =>
    match compileTerm slots slotBodies selfDepth varEnv v,
          compileTerm slots slotBodies selfDepth varEnv z with
    | some ev, some ez =>
      let predExpr := RtlExpr.alu .sub ev (.const 1#64)
      match compileTerm slots slotBodies (selfDepth + 1) (predExpr :: varEnv) s with
      | some es => some (.mux (.alu .eq ev (.const 0#64)) ez es)
      | none => none
    | _, _ => none
  | _ => none

/-- Universal Structural Soundness of `compileTerm`:
For EVERY `t : Term`, if `compileTerm slots slotBodies selfDepth varEnv t = some e`, then evaluating
`e` in the hardware semantics `evalRtlExpr` produces the EXACT same result as `evalTermHw` under the
evaluated variable environment `varEnv.map (evalRtlExpr inputs wires regs)`! -/
theorem compileTerm_sound
    (inputs wires regs : Nat → BitVec 64)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (t : Term)
    (selfDepth : Nat) (varEnv : List RtlExpr) (e : RtlExpr)
    (h : compileTerm slots slotBodies selfDepth varEnv t = some e) :
    evalTermHw slots slotBodies inputs wires regs selfDepth (varEnv.map (evalRtlExpr inputs wires regs)) t =
      some (evalRtlExpr inputs wires regs e) := by
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .record _ | .inject _ _ | .case _ _ | .perform _ | .done _ | .split _ _ _ =>
    simp [compileTerm] at h
  | .nat n =>
    simp only [compileTerm, Option.some.injEq] at h
    subst h
    rfl
  | .boolean b =>
    simp only [compileTerm, Option.some.injEq] at h
    subst h
    rfl
  | .bound idx =>
    simp only [compileTerm] at h
    simp only [evalTermHw, List.getElem?_map, h, Option.map_some]
  | .get target member =>
    cases target with
    | bound idx =>
      simp only [compileTerm] at h
      simp only [evalTermHw]
      by_cases hEq : idx == selfDepth
      · simp only [hEq, ↓reduceIte] at h ⊢
        cases hSlot : slots.idxOf? member with
        | none => simp [hSlot] at h
        | some slotIdx =>
          simp only [hSlot, Option.some.injEq] at h
          subst h
          rfl
      · simp [hEq] at h
    | _ =>
      simp [compileTerm] at h
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [compileTerm] at h
      cases hArg : compileTerm slots slotBodies selfDepth varEnv arg with
      | none => simp [hArg] at h
      | some eArg =>
        simp only [hArg] at h
        have ihArg := compileTerm_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg hArg
        have ihBody := compileTerm_sound inputs wires regs slots slotBodies subBody
          (selfDepth + 1) (eArg :: varEnv) e h
        simp only [List.map_cons] at ihBody
        simp only [evalTermHw, ihArg, ihBody]
    | get target member =>
      cases target with
      | bound idx =>
        simp only [compileTerm] at h
        simp only [evalTermHw]
        by_cases hEq : idx == selfDepth
        · simp only [hEq, ↓reduceIte] at h ⊢
          cases hSlot : slots.idxOf? member with
          | none => simp [hSlot] at h
          | some slotIdx =>
            cases hArg : compileTerm slots slotBodies selfDepth varEnv arg with
            | none => simp [hSlot, hArg] at h
            | some eArg =>
              simp only [hSlot, hArg] at h
              cases hBody : slotBodies[slotIdx]? with
              | none => simp [hBody] at h
              | some slotExpr =>
                simp only [hBody, Option.some.injEq] at h
                subst h
                have ihArg := compileTerm_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg hArg
                simp only [ihArg, hBody, substInputPort0_sound]
        · simp [hEq] at h
      | _ =>
        simp [compileTerm] at h
    | _ =>
      simp [compileTerm] at h
  | .binary op l r =>
    simp only [compileTerm] at h
    cases hl : compileTerm slots slotBodies selfDepth varEnv l with
    | none => simp [hl] at h
    | some el =>
      cases hr : compileTerm slots slotBodies selfDepth varEnv r with
      | none => simp [hl, hr] at h
      | some er =>
        simp only [hl, hr] at h
        have ihl := compileTerm_sound inputs wires regs slots slotBodies l selfDepth varEnv el hl
        have ihr := compileTerm_sound inputs wires regs slots slotBodies r selfDepth varEnv er hr
        simp only [evalTermHw, ihl, ihr]
        exact compilePrim_sound inputs wires regs op el er e h
  | .ifBool c t f =>
    simp only [compileTerm] at h
    cases hc : compileTerm slots slotBodies selfDepth varEnv c with
    | none => simp [hc] at h
    | some ec =>
      cases ht : compileTerm slots slotBodies selfDepth varEnv t with
      | none => simp [hc, ht] at h
      | some et =>
        cases hf : compileTerm slots slotBodies selfDepth varEnv f with
        | none => simp [hc, ht, hf] at h
        | some ef =>
          simp only [hc, ht, hf, Option.some.injEq] at h
          subst h
          have ihc := compileTerm_sound inputs wires regs slots slotBodies c selfDepth varEnv ec hc
          have iht := compileTerm_sound inputs wires regs slots slotBodies t selfDepth varEnv et ht
          have ihf := compileTerm_sound inputs wires regs slots slotBodies f selfDepth varEnv ef hf
          simp only [evalTermHw, ihc, iht, ihf, evalRtlExpr]
  | .ifZero v z s =>
    simp only [compileTerm] at h
    cases hv : compileTerm slots slotBodies selfDepth varEnv v with
    | none => simp [hv] at h
    | some ev =>
      cases hz : compileTerm slots slotBodies selfDepth varEnv z with
      | none => simp [hv, hz] at h
      | some ez =>
        cases hs : compileTerm slots slotBodies (selfDepth + 1)
            (RtlExpr.alu .sub ev (.const 1#64) :: varEnv) s with
        | none => simp [hv, hz, hs] at h
        | some es =>
          simp only [hv, hz, hs, Option.some.injEq] at h
          subst h
          have hv' := compileTerm_sound inputs wires regs slots slotBodies v selfDepth varEnv ev hv
          have hz' := compileTerm_sound inputs wires regs slots slotBodies z selfDepth varEnv ez hz
          have hs' := compileTerm_sound inputs wires regs slots slotBodies s (selfDepth + 1)
            (RtlExpr.alu .sub ev (.const 1#64) :: varEnv) es hs
          simp only [List.map_cons, evalRtlExpr, evalAluOp] at hs'
          simp only [evalTermHw, hv', hz', hs', evalRtlExpr, evalAluOp]
          rfl

/-! ## 4. Whole-Book Compiler (`compileLeafDef`, `compileBookToRtl`) -/

/-- Extract the inner body of a `LeafDef`'s `code` (`λself. λarg. body`) and compile it to `RtlExpr`. -/
def compileLeafDef (slots : List String) (slotBodies : List RtlExpr) (d : LeafDef) : Option RtlExpr :=
  match d.code with
  | .lam (.lam body) => compileTerm slots slotBodies 1 [.inputPort 0] body
  | _ => none

/-- Structurally recursive slot-list compiler (avoids `ForIn` monad overhead in kernel reduction). -/
def compileBookDefs
    (slots : List String)
    (slotBodies : List RtlExpr)
    (wires : List WireAssign)
    (regs : List RegSpec)
    (outs : List OutputPort) :
    List LeafDef → Option (List WireAssign × List RegSpec × List OutputPort)
  | [] => some (wires, regs, outs)
  | d :: rest =>
    match compileLeafDef slots slotBodies d with
    | none => none
    | some expr =>
      let w : WireAssign := { wireIdx := d.slot, name := d.member, expr := expr }
      let r : RegSpec :=
        { regIdx         := d.slot
        , name           := s!"reg_{d.member}"
        , domain         := .coreClk
        , resetKind      := .resetFree
        , isSynchronizer := false
        , nextExpr       := .wireRef d.slot }
      let o : OutputPort := { name := s!"out_{d.member}", expr := .wireRef d.slot }
      compileBookDefs slots (slotBodies ++ [expr]) (wires ++ [w]) (regs ++ [r]) (outs ++ [o]) rest

/-- Compile an entire `Obend.Leaf.Book` into a synchronous `RtlModule`:
* Input port 0 is `"arg"` (the 64-bit method parameter),
* Each slot `d` in `B.defs` becomes wire `w_{d.slot}` (`d.member`),
* Each slot `d` also produces a combinational output port `out_{d.member}` and a registered
  pipeline output `reg_{d.member}` clocked on `coreClk` (`ResetKind.resetFree`). -/
def compileBookToRtl (modName : String) (B : Book) : Option RtlModule :=
  match compileBookDefs B.slots [] [] [] [] B.defs with
  | none => none
  | some (wires, regs, outs) =>
    some {
      name       := modName
      inputNames := ["arg"]
      wires      := wires
      regs       := regs
      outputs    := outs
    }

/-! ## 5. Saturating `Nat`-Compatible Mode (`compilePrimSat`, `compileTermSat`) for `Obend.Lower` -/

/-- Saturating 64-bit hardware semantics for `Obend.Core.Term.Primitive`:
`.subtract` saturates at `0#64` when `a < b` (`BitVec.ult a b`), matching `Lean` and `Core4`
truncated `Nat` subtraction (`0 - 1 = 0`). -/
def evalPrimHwSat (op : Primitive) (a b : BitVec 64) : Option (BitVec 64) :=
  match op with
  | .add         => some (a + b)
  | .multiply    => some (a * b)
  | .subtract    => some (if BitVec.ult a b then 0#64 else a - b)
  | .equal       => some (if a == b then 1#64 else 0#64)
  | .conjunction => some (a &&& b)
  | .less        => some (if BitVec.ult a b then 1#64 else 0#64)
  | .lessEqual   => some (if BitVec.ult b a then 0#64 else 1#64)
  | _            => none

/-- Compile `Primitive` with saturating subtraction `(l < r) ? 64'd0 : (l - r)`. -/
def compilePrimSat (op : Primitive) (l r : RtlExpr) : Option RtlExpr :=
  match op with
  | .add         => some (.alu .add l r)
  | .multiply    => some (.alu .mul l r)
  | .subtract    => some (.mux (.alu .ult l r) (.const 0#64) (.alu .sub l r))
  | .equal       => some (.alu .eq l r)
  | .conjunction => some (.alu .bitAnd l r)
  | .less        => some (.alu .ult l r)
  | .lessEqual   => some (.mux (.alu .ult r l) (.const 0#64) (.const 1#64))
  | _            => none

/-- Soundness of `compilePrimSat`: evaluating the compiled `RtlExpr` matches `evalPrimHwSat`. -/
theorem compilePrimSat_sound
    (inputs wires regs : Nat → BitVec 64)
    (op : Primitive) (l r e : RtlExpr)
    (h : compilePrimSat op l r = some e) :
    evalPrimHwSat op (evalRtlExpr inputs wires regs l) (evalRtlExpr inputs wires regs r) =
      some (evalRtlExpr inputs wires regs e) := by
  cases op <;> simp [compilePrimSat, evalPrimHwSat] at h ⊢
  all_goals
    subst h
    simp [evalRtlExpr, evalAluOp]

/-- **Exact `Nat` Subtraction Correspondence (`evalPrimHwSat_subtract_eq_ofNat_sub`)**:
For all `a, b < 2^64`, saturating 64-bit hardware subtraction `evalPrimHwSat .subtract` agrees
with Lean/Core4 truncated `Nat` subtraction `a - b`. -/
theorem evalPrimHwSat_subtract_eq_ofNat_sub {a b : Nat}
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    evalPrimHwSat .subtract (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      some (BitVec.ofNat 64 (a - b)) := by
  simp only [evalPrimHwSat, Option.some.injEq]
  by_cases hlt : BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true
  · simp only [hlt, ite_true]
    have hab : a < b := by
      simpa [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hlt
    have hsub : a - b = 0 := by omega
    rw [hsub]
  · simp only [hlt, Bool.false_eq_true, ite_false]
    have hle : b ≤ a := by
      simpa [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hlt
    apply BitVec.eq_of_toNat_eq
    have hsub_lt : a - b < 2 ^ 64 := by omega
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt hsub_lt]
    omega

/-- Reference 64-bit saturating hardware semantics for `Obend.Core.Term`:
matches `evalTermHw`, except `.record []` (`box` for `LExpr.erased`) evaluates to `0#64` and
binary primitives use `evalPrimHwSat`. -/
def evalTermHwSat
    (slots : List String)
    (slotBodies : List RtlExpr)
    (inputs slotWires regs : Nat → BitVec 64)
    (selfDepth : Nat)
    (varVals : List (BitVec 64)) : Term → Option (BitVec 64)
  | .nat n => some (BitVec.ofNat 64 n)
  | .boolean b => some (if b then 1#64 else 0#64)
  | .record [] => some 0#64
  | .bound idx => varVals[idx]?
  | .get (.bound idx) member =>
    if idx == selfDepth then
      match slots.idxOf? member with
      | some slotIdx => some (slotWires slotIdx)
      | none => none
    else none
  | .app fn arg =>
    match fn with
    | .lam subBody =>
      match evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals arg with
      | some vArg =>
        evalTermHwSat slots slotBodies inputs slotWires regs (selfDepth + 1) (vArg :: varVals) subBody
      | none => none
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals arg with
        | some slotIdx, some vArg =>
          match slotBodies[slotIdx]? with
          | some slotExpr =>
            some (evalRtlExpr (fun i => if i == 0 then vArg else inputs i) slotWires regs slotExpr)
          | none => none
        | _, _ => none
      else none
    | _ => none
  | .binary op l r =>
    match evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals l,
          evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals r with
    | some vl, some vr => evalPrimHwSat op vl vr
    | _, _ => none
  | .ifBool c t f =>
    match evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals c,
          evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals t,
          evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals f with
    | some vc, some vt, some vf => some (if vc != 0#64 then vt else vf)
    | _, _, _ => none
  | .ifZero v z s =>
    match evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals v,
          evalTermHwSat slots slotBodies inputs slotWires regs selfDepth varVals z with
    | some vv, some vz =>
      match evalTermHwSat slots slotBodies inputs slotWires regs (selfDepth + 1) ((vv - 1#64) :: varVals) s with
      | some vs => some (if (if vv == 0#64 then 1#64 else 0#64) != 0#64 then vz else vs)
      | none => none
    | _, _ => none
  | _ => none

/-- Compile `Term` in saturating `Nat`-compatible mode, also accepting `box = .record []` (the
lowered representation of `LExpr.erased` from `Obend.Lower`) as `0#64`. -/
def compileTermSat
    (slots : List String)
    (slotBodies : List RtlExpr)
    (selfDepth : Nat)
    (varEnv : List RtlExpr) : Term → Option RtlExpr
  | .nat n => some (.const (BitVec.ofNat 64 n))
  | .boolean b => some (.const (if b then 1#64 else 0#64))
  | .record [] => some (.const 0#64)
  | .bound idx => varEnv[idx]?
  | .get (.bound idx) member =>
    if idx == selfDepth then
      match slots.idxOf? member with
      | some slotIdx => some (.wireRef slotIdx)
      | none => none
    else none
  | .app fn arg =>
    match fn with
    | .lam subBody =>
      match compileTermSat slots slotBodies selfDepth varEnv arg with
      | some eArg =>
        compileTermSat slots slotBodies (selfDepth + 1) (eArg :: varEnv) subBody
      | none => none
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              compileTermSat slots slotBodies selfDepth varEnv arg with
        | some slotIdx, some eArg =>
          match slotBodies[slotIdx]? with
          | some slotExpr => some (substInputPort0 eArg slotExpr)
          | none => none
        | _, _ => none
      else none
    | _ => none
  | .binary op l r =>
    match compileTermSat slots slotBodies selfDepth varEnv l,
          compileTermSat slots slotBodies selfDepth varEnv r with
    | some el, some er => compilePrimSat op el er
    | _, _ => none
  | .ifBool c t f =>
    match compileTermSat slots slotBodies selfDepth varEnv c,
          compileTermSat slots slotBodies selfDepth varEnv t,
          compileTermSat slots slotBodies selfDepth varEnv f with
    | some ec, some et, some ef => some (.mux ec et ef)
    | _, _, _ => none
  | .ifZero v z s =>
    match compileTermSat slots slotBodies selfDepth varEnv v,
          compileTermSat slots slotBodies selfDepth varEnv z with
    | some ev, some ez =>
      let predExpr := RtlExpr.alu .sub ev (.const 1#64)
      match compileTermSat slots slotBodies (selfDepth + 1) (predExpr :: varEnv) s with
      | some es => some (.mux (.alu .eq ev (.const 0#64)) ez es)
      | none => none
    | _, _ => none
  | _ => none

/-- **Universal Structural Soundness of `compileTermSat` (`compileTermSat_sound`)**:
For EVERY `t : Term`, if `compileTermSat slots slotBodies selfDepth varEnv t = some e`, then
evaluating `e` in `evalRtlExpr` produces the exact same 64-bit value as `evalTermHwSat` under
`varEnv.map (evalRtlExpr inputs wires regs)`. -/
theorem compileTermSat_sound
    (inputs wires regs : Nat → BitVec 64)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (t : Term)
    (selfDepth : Nat) (varEnv : List RtlExpr) (e : RtlExpr)
    (h : compileTermSat slots slotBodies selfDepth varEnv t = some e) :
    evalTermHwSat slots slotBodies inputs wires regs selfDepth (varEnv.map (evalRtlExpr inputs wires regs)) t =
      some (evalRtlExpr inputs wires regs e) := by
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .inject _ _ | .case _ _ | .perform _ | .done _ | .split _ _ _ =>
    simp [compileTermSat] at h
  | .record fs =>
    cases fs with
    | nil =>
      simp only [compileTermSat, Option.some.injEq] at h
      subst h
      rfl
    | cons _ _ =>
      simp [compileTermSat] at h
  | .nat n =>
    simp only [compileTermSat, Option.some.injEq] at h
    subst h
    rfl
  | .boolean b =>
    simp only [compileTermSat, Option.some.injEq] at h
    subst h
    rfl
  | .bound idx =>
    simp only [compileTermSat] at h
    simp only [evalTermHwSat, List.getElem?_map, h, Option.map_some]
  | .get target member =>
    cases target with
    | bound idx =>
      simp only [compileTermSat] at h
      simp only [evalTermHwSat]
      by_cases hEq : idx == selfDepth
      · simp only [hEq, ↓reduceIte] at h ⊢
        cases hSlot : slots.idxOf? member with
        | none => simp [hSlot] at h
        | some slotIdx =>
          simp only [hSlot, Option.some.injEq] at h
          subst h
          rfl
      · simp [hEq] at h
    | _ =>
      simp [compileTermSat] at h
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [compileTermSat] at h
      cases hArg : compileTermSat slots slotBodies selfDepth varEnv arg with
      | none => simp [hArg] at h
      | some eArg =>
        simp only [hArg] at h
        have ihArg := compileTermSat_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg hArg
        have ihBody := compileTermSat_sound inputs wires regs slots slotBodies subBody
          (selfDepth + 1) (eArg :: varEnv) e h
        simp only [List.map_cons] at ihBody
        simp only [evalTermHwSat, ihArg, ihBody]
    | get target member =>
      cases target with
      | bound idx =>
        simp only [compileTermSat] at h
        simp only [evalTermHwSat]
        by_cases hEq : idx == selfDepth
        · simp only [hEq, ↓reduceIte] at h ⊢
          cases hSlot : slots.idxOf? member with
          | none => simp [hSlot] at h
          | some slotIdx =>
            cases hArg : compileTermSat slots slotBodies selfDepth varEnv arg with
            | none => simp [hSlot, hArg] at h
            | some eArg =>
              simp only [hSlot, hArg] at h
              cases hBody : slotBodies[slotIdx]? with
              | none => simp [hBody] at h
              | some slotExpr =>
                simp only [hBody, Option.some.injEq] at h
                subst h
                have ihArg := compileTermSat_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg hArg
                simp only [ihArg, hBody, substInputPort0_sound]
        · simp [hEq] at h
      | _ =>
        simp [compileTermSat] at h
    | _ =>
      simp [compileTermSat] at h
  | .binary op l r =>
    simp only [compileTermSat] at h
    cases hl : compileTermSat slots slotBodies selfDepth varEnv l with
    | none => simp [hl] at h
    | some el =>
      cases hr : compileTermSat slots slotBodies selfDepth varEnv r with
      | none => simp [hl, hr] at h
      | some er =>
        simp only [hl, hr] at h
        have ihl := compileTermSat_sound inputs wires regs slots slotBodies l selfDepth varEnv el hl
        have ihr := compileTermSat_sound inputs wires regs slots slotBodies r selfDepth varEnv er hr
        simp only [evalTermHwSat, ihl, ihr]
        exact compilePrimSat_sound inputs wires regs op el er e h
  | .ifBool c t f =>
    simp only [compileTermSat] at h
    cases hc : compileTermSat slots slotBodies selfDepth varEnv c with
    | none => simp [hc] at h
    | some ec =>
      cases ht : compileTermSat slots slotBodies selfDepth varEnv t with
      | none => simp [hc, ht] at h
      | some et =>
        cases hf : compileTermSat slots slotBodies selfDepth varEnv f with
        | none => simp [hc, ht, hf] at h
        | some ef =>
          simp only [hc, ht, hf, Option.some.injEq] at h
          subst h
          have ihc := compileTermSat_sound inputs wires regs slots slotBodies c selfDepth varEnv ec hc
          have iht := compileTermSat_sound inputs wires regs slots slotBodies t selfDepth varEnv et ht
          have ihf := compileTermSat_sound inputs wires regs slots slotBodies f selfDepth varEnv ef hf
          simp only [evalTermHwSat, ihc, iht, ihf, evalRtlExpr]
  | .ifZero v z s =>
    simp only [compileTermSat] at h
    cases hv : compileTermSat slots slotBodies selfDepth varEnv v with
    | none => simp [hv] at h
    | some ev =>
      cases hz : compileTermSat slots slotBodies selfDepth varEnv z with
      | none => simp [hv, hz] at h
      | some ez =>
        cases hs : compileTermSat slots slotBodies (selfDepth + 1)
            (RtlExpr.alu .sub ev (.const 1#64) :: varEnv) s with
        | none => simp [hv, hz, hs] at h
        | some es =>
          simp only [hv, hz, hs, Option.some.injEq] at h
          subst h
          have hv' := compileTermSat_sound inputs wires regs slots slotBodies v selfDepth varEnv ev hv
          have hz' := compileTermSat_sound inputs wires regs slots slotBodies z selfDepth varEnv ez hz
          have hs' := compileTermSat_sound inputs wires regs slots slotBodies s (selfDepth + 1)
            (RtlExpr.alu .sub ev (.const 1#64) :: varEnv) es hs
          simp only [List.map_cons, evalRtlExpr, evalAluOp] at hs'
          simp only [evalTermHwSat, hv', hz', hs', evalRtlExpr, evalAluOp]
          rfl

/-- Extract the inner body of a `LeafDef`'s `code` (`λself. λarg. body`) and compile it via
`compileTermSat`. -/
def compileLeafDefSat (slots : List String) (slotBodies : List RtlExpr) (d : LeafDef) : Option RtlExpr :=
  match d.code with
  | .lam (.lam body) => compileTermSat slots slotBodies 1 [.inputPort 0] body
  | _ => none

/-- Structurally recursive slot-list compiler using `compileLeafDefSat`. -/
def compileBookDefsSat
    (slots : List String)
    (slotBodies : List RtlExpr)
    (wires : List WireAssign)
    (regs : List RegSpec)
    (outs : List OutputPort) :
    List LeafDef → Option (List WireAssign × List RegSpec × List OutputPort)
  | [] => some (wires, regs, outs)
  | d :: rest =>
    match compileLeafDefSat slots slotBodies d with
    | none => none
    | some expr =>
      let w : WireAssign := { wireIdx := d.slot, name := d.member, expr := expr }
      let r : RegSpec :=
        { regIdx         := d.slot
        , name           := s!"reg_{d.member}"
        , domain         := .coreClk
        , resetKind      := .resetFree
        , isSynchronizer := false
        , nextExpr       := .wireRef d.slot }
      let o : OutputPort := { name := s!"out_{d.member}", expr := .wireRef d.slot }
      compileBookDefsSat slots (slotBodies ++ [expr]) (wires ++ [w]) (regs ++ [r]) (outs ++ [o]) rest

/-- Compile an entire `Obend.Leaf.Book` into a synchronous `RtlModule` using saturating `Nat`-compatible
arithmetic (`compileBookDefsSat`). -/
def compileBookToRtlSat (modName : String) (B : Book) : Option RtlModule :=
  match compileBookDefsSat B.slots [] [] [] [] B.defs with
  | none => none
  | some (wires, regs, outs) =>
    some {
      name       := modName
      inputNames := ["arg"]
      wires      := wires
      regs       := regs
      outputs    := outs
    }

end Obend.Hardware.Compiler
end
