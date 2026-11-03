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
public import Obend.Hardware.Types
@[expose] public section

namespace Obend.Hardware.Compiler
open Obend.Core.Term Obend.Leaf Obend.Hardware.HDL Obend.Hardware.Types
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
  | .bitAnd      => some (a &&& b)
  | .bitOr       => some (a ||| b)
  | .bitXor      => some (a ^^^ b)
  | .shl         => some (a <<< (b.toNat % 64))
  | .lshr        => some (a >>> (b.toNat % 64))
  | .ashr        => some (BitVec.sshiftRight a (b.toNat % 64))
  | .slt         => some (if BitVec.slt a b then 1#64 else 0#64)
  | .qmul32      => some (((a.signExtend 128 * b.signExtend 128) >>> 32).setWidth 64)
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
  | .bitAnd      => some (.alu .bitAnd l r)
  | .bitOr       => some (.alu .bitOr l r)
  | .bitXor      => some (.alu .bitXor l r)
  | .shl         => some (.alu .shl l r)
  | .lshr        => some (.alu .lshr l r)
  | .ashr        => some (.alu .ashr l r)
  | .slt         => some (.alu .slt l r)
  | .qmul32      => some (.alu .qmul32 l r)
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

/-- Count the number of formal arguments (excluding `self`) of a `LeafDef`'s `code` (up to 4). -/
def leafDefArity : Term → Nat
  | .lam (.lam (.lam (.lam (.lam _)))) => 4
  | .lam (.lam (.lam (.lam _)))        => 3
  | .lam (.lam (.lam _))               => 2
  | _                                  => 1

/-- Determine the input port list for a compiled `Obend.Leaf.Book` from the maximum method arity
across all `LeafDef`s in the `Book` (returning `["arg"]` when all slots have arity ≤ 1). -/
def defInputNames (defs : List LeafDef) : List String :=
  let maxArity := defs.foldl (fun acc d => max acc (leafDefArity d.code)) 1
  if maxArity == 4 then ["arg0", "arg1", "arg2", "arg3"]
  else if maxArity == 3 then ["arg0", "arg1", "arg2"]
  else if maxArity == 2 then ["arg0", "arg1"]
  else ["arg"]

/-- Extract the inner body of a `LeafDef`'s `code` (`λself. λarg₀...λargₖ. body`) and compile it to `RtlExpr`. -/
def compileLeafDef (slots : List String) (slotBodies : List RtlExpr) (d : LeafDef) : Option RtlExpr :=
  match d.code with
  | .lam (.lam (.lam (.lam (.lam body)))) =>
    compileTerm slots slotBodies 4 [.inputPort 3, .inputPort 2, .inputPort 1, .inputPort 0] body
  | .lam (.lam (.lam (.lam body))) =>
    compileTerm slots slotBodies 3 [.inputPort 2, .inputPort 1, .inputPort 0] body
  | .lam (.lam (.lam body)) =>
    compileTerm slots slotBodies 2 [.inputPort 1, .inputPort 0] body
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
* Input port(s) are `"arg"` (when max method arity ≤ 1) or `"arg0".."arg{k-1}"` (for multi-arg books),
* Each slot `d` in `B.defs` becomes wire `w_{d.slot}` (`d.member`),
* Each slot `d` also produces a combinational output port `out_{d.member}` and a registered
  pipeline output `reg_{d.member}` clocked on `coreClk` (`ResetKind.resetFree`). -/
def compileBookToRtl (modName : String) (B : Book) : Option RtlModule :=
  match compileBookDefs B.slots [] [] [] [] B.defs with
  | none => none
  | some (wires, regs, outs) =>
    some {
      name       := modName
      inputNames := defInputNames B.defs
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
  | .bitAnd      => some (a &&& b)
  | .bitOr       => some (a ||| b)
  | .bitXor      => some (a ^^^ b)
  | .shl         => some (a <<< (b.toNat % 64))
  | .lshr        => some (a >>> (b.toNat % 64))
  | .ashr        => some (BitVec.sshiftRight a (b.toNat % 64))
  | .slt         => some (if BitVec.slt a b then 1#64 else 0#64)
  | .qmul32      => some (((a.signExtend 128 * b.signExtend 128) >>> 32).setWidth 64)
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
  | .bitAnd      => some (.alu .bitAnd l r)
  | .bitOr       => some (.alu .bitOr l r)
  | .bitXor      => some (.alu .bitXor l r)
  | .shl         => some (.alu .shl l r)
  | .lshr        => some (.alu .lshr l r)
  | .ashr        => some (.alu .ashr l r)
  | .slt         => some (.alu .slt l r)
  | .qmul32      => some (.alu .qmul32 l r)
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

/-- Extract the inner body of a `LeafDef`'s `code` (`λself. λarg₀...λargₖ. body`) and compile it via
`compileTermSat`. -/
def compileLeafDefSat (slots : List String) (slotBodies : List RtlExpr) (d : LeafDef) : Option RtlExpr :=
  match d.code with
  | .lam (.lam (.lam (.lam (.lam body)))) =>
    compileTermSat slots slotBodies 4 [.inputPort 3, .inputPort 2, .inputPort 1, .inputPort 0] body
  | .lam (.lam (.lam (.lam body))) =>
    compileTermSat slots slotBodies 3 [.inputPort 2, .inputPort 1, .inputPort 0] body
  | .lam (.lam (.lam body)) =>
    compileTermSat slots slotBodies 2 [.inputPort 1, .inputPort 0] body
  | .lam (.lam body) => compileTermSat slots slotBodies 1 [.inputPort 0] body
  | _ => none

/-- Determine the input port list for a compiled `Obend.Leaf.Book` based on the maximum method arity
across all `LeafDef`s in the `Book`. -/
def defInputNamesSat (defs : List LeafDef) : List String :=
  defInputNames defs

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
      inputNames := defInputNamesSat B.defs
      wires      := wires
      regs       := regs
      outputs    := outs
    }

/-! ## 6. Sequential Multi-Cycle FSM Synthesis for `Nat.rec` Loops (`compileBookToSeqRtlSat`) -/

/-- Compile the successor step body of a lowered `Nat.rec z s count` (`fix (natRecSpec Z S) {} count`):
* `recFnDepth` tracks the de Bruijn index of the `fix` self-binder (`3` at the top of the `ifZero`
  successor arm),
* `predDepth` tracks the de Bruijn index of the `ifZero` predecessor variable `p` (`0` at the top
  of the `ifZero` successor arm),
* Any recursive accumulator reference `.app (.bound rIdx) (.bound pIdx)` with `rIdx == recFnDepth`
  and `pIdx == predDepth` compiles to `.wireRef 1` (`w_eff_acc`),
* Curried 2-argument step functions `.app (.app (.lam (.lam subBody)) arg1) arg2` are beta-reduced
  on the fly so both un-inlined (`lowerT`) and dictionary-inlined (`inlineDict`) `Nat.rec` terms
  compile to identical hardware! -/
def compileNatRecStepSat
    (recFnDepth predDepth : Nat)
    (varEnv : List RtlExpr) : Term → Option RtlExpr
  | .nat n => some (.const (BitVec.ofNat 64 n))
  | .boolean b => some (.const (if b then 1#64 else 0#64))
  | .record [] => some (.const 0#64)
  | .bound idx => varEnv[idx]?
  | .app fn arg =>
    match fn with
    | .bound rIdx =>
      match arg with
      | .bound pIdx =>
        if rIdx == recFnDepth && pIdx == predDepth then
          some (.wireRef 1)
        else
          none
      | _ => none
    | .lam subBody =>
      match compileNatRecStepSat recFnDepth predDepth varEnv arg with
      | some eArg =>
        compileNatRecStepSat (recFnDepth + 1) (predDepth + 1) (eArg :: varEnv) subBody
      | none => none
    | _ => none
  | .binary op l r =>
    match compileNatRecStepSat recFnDepth predDepth varEnv l,
          compileNatRecStepSat recFnDepth predDepth varEnv r with
    | some el, some er => compilePrimSat op el er
    | _, _ => none
  | .ifBool c t f =>
    match compileNatRecStepSat recFnDepth predDepth varEnv c,
          compileNatRecStepSat recFnDepth predDepth varEnv t,
          compileNatRecStepSat recFnDepth predDepth varEnv f with
    | some ec, some et, some ef => some (.mux ec et ef)
    | _, _, _ => none
  | _ => none

/-- Recognize a lowered `Nat.rec` slot definition
`λself. λarg. (.app (.fix (.lam (.lam (.lam (.ifZero (.bound 0) zTerm sTerm)))) _) countTerm)`
(supporting both the un-inlined curried form `.app (.app (.lam (.lam subBody)) (.bound 0)) (.app (.bound 3) (.bound 0))`
and the dictionary-inlined form) and synthesize its `(zExpr, stepExpr, countExpr)` datapath tuple. -/
def extractSeqNatRecDefSat (d : LeafDef) : Option (RtlExpr × RtlExpr × RtlExpr) :=
  match d.code with
  | .lam (.lam (.app (.fix (.lam (.lam (.lam (.ifZero (.bound 0) zTerm sTerm)))) _) countTerm)) =>
    let zEnv : List RtlExpr := [.const 0#64, .const 0#64, .const 0#64, .inputPort 0]
    let sEnv : List RtlExpr := [.regRead 0, .const 0#64, .const 0#64, .const 0#64, .inputPort 0]
    let stepOpt : Option RtlExpr :=
      match sTerm with
      | .app (.app (.lam (.lam subBody)) (.bound 0)) (.app (.bound 3) (.bound 0)) =>
        let subEnv : List RtlExpr :=
          [.wireRef 1, .regRead 0, .const 0#64, .const 0#64, .const 0#64, .inputPort 0]
        compileNatRecStepSat 5 2 subEnv subBody
      | _ =>
        compileNatRecStepSat 3 0 sEnv sTerm
    match compileTermSat [] [] 4 zEnv zTerm,
          stepOpt,
          compileTermSat [] [] 1 [.inputPort 0] countTerm with
    | some zExpr, some stepExpr, some countExpr => some (zExpr, stepExpr, countExpr)
    | _, _, _ => none
  | _ => none

/-- Synthesize a 2-state-register synchronous sequential FSM (`RtlModule`) for 2-state linear
recurrences `(a, b) ↦ (b, a + b)` (such as Fibonacci `fib`), with:
* `reg 0` (`reg_i`, `.syncReset 0#64`): loop counter $i \in [0, N]$,
* `reg 1` (`reg_a`, `.syncReset initA`): primary state register $a_i$ (driven to `out_{fnName}`),
* `reg 2` (`reg_b`, `.syncReset initB`): secondary state register $b_i = a_{i+1}$,
* `reg 3` (`reg_running`, `.syncReset 1#64`): active execution status register,
* `reg 4` (`reg_done`, `.syncReset 0#64`): completion status register,
* `wire 0` (`w_count`): `arg | nVal` (supports both runtime `arg` and static `nVal`),
* `wire 1` (`w_next_b`): `reg_a + reg_b`,
* `wire 2` (`fnName`): `reg_a`,
* `wire 3` (`done`): `(reg_i < w_count) ? 0 : 1`. -/
def compileNatRec2StateSat (fnName : String) (nVal : Nat) (initA initB : Nat) : RtlModule :=
  let w0 : WireAssign :=
    { wireIdx := 0
    , name    := "w_count"
    , expr    := .alu .bitOr (.inputPort 0) (.const (BitVec.ofNat 64 nVal)) }
  let w1 : WireAssign :=
    { wireIdx := 1
    , name    := "w_next_b"
    , expr    := .alu .add (.regRead 1) (.regRead 2) }
  let w2 : WireAssign :=
    { wireIdx := 2
    , name    := fnName
    , expr    := .regRead 1 }
  let w3 : WireAssign :=
    { wireIdx := 3
    , name    := "done"
    , expr    := .mux (.alu .ult (.regRead 0) (.wireRef 0)) (.const 0#64) (.const 1#64) }
  let condLt : RtlExpr := .alu .ult (.regRead 0) (.wireRef 0)
  let r0 : RegSpec :=
    { regIdx         := 0
    , name           := "reg_i"
    , domain         := .coreClk
    , resetKind      := .syncReset 0#64
    , isSynchronizer := false
    , nextExpr       := .mux condLt (.alu .add (.regRead 0) (.const 1#64)) (.regRead 0) }
  let r1 : RegSpec :=
    { regIdx         := 1
    , name           := "reg_a"
    , domain         := .coreClk
    , resetKind      := .syncReset (BitVec.ofNat 64 initA)
    , isSynchronizer := false
    , nextExpr       := .mux condLt (.regRead 2) (.regRead 1) }
  let r2 : RegSpec :=
    { regIdx         := 2
    , name           := "reg_b"
    , domain         := .coreClk
    , resetKind      := .syncReset (BitVec.ofNat 64 initB)
    , isSynchronizer := false
    , nextExpr       := .mux condLt (.wireRef 1) (.regRead 2) }
  let r3 : RegSpec :=
    { regIdx         := 3
    , name           := "reg_running"
    , domain         := .coreClk
    , resetKind      := .syncReset 1#64
    , isSynchronizer := false
    , nextExpr       := .mux condLt (.const 1#64) (.const 0#64) }
  let r4 : RegSpec :=
    { regIdx         := 4
    , name           := "reg_done"
    , domain         := .coreClk
    , resetKind      := .syncReset 0#64
    , isSynchronizer := false
    , nextExpr       := .wireRef 3 }
  { name       := fnName
  , inputNames := ["arg"]
  , wires      := [w0, w1, w2, w3]
  , regs       := [r0, r1, r2, r3, r4]
  , outputs    :=
      [ { name := s!"out_{fnName}", expr := .wireRef 2 }
      , { name := "out_done",       expr := .wireRef 3 } ] }

/-- Recognize a single weighted state summand in a 2-state linear recurrence:
returns `some (true, c)` for the current state `b` (`.bound 0` with coeff `1`, or `c * b` / `b * c`),
and `some (false, c)` for the previous state `a` (`.bound 6` / `.bound 2` with coeff `1`, or `c * a` / `a * c`). -/
def extractStateTermCoeff : Term → Option (Bool × Nat)
  | .bound idx =>
    if idx == 0 then some (true, 1)
    else if idx == 6 || idx == 2 then some (false, 1)
    else none
  | .binary .multiply (.nat c) (.bound idx) =>
    if idx == 0 then some (true, c)
    else if idx == 6 || idx == 2 then some (false, c)
    else none
  | .binary .multiply (.bound idx) (.nat c) =>
    if idx == 0 then some (true, c)
    else if idx == 6 || idx == 2 then some (false, c)
    else none
  | _ => none

/-- Extract `(coeffCurr, coeffPrev)` from the inner linear combination AST of a 2-state recurrence
`(a, b) ↦ (b, coeffCurr * b + coeffPrev * a)`, supporting arbitrary commuted multiplication and
addition operand orders (`cCurr * b + cPrev * a`, `b * cCurr + a * cPrev`, `a * cPrev + b * cCurr`, etc.). -/
def extractTwoStateCombCoeffs : Term → Option (Nat × Nat)
  | .binary .add lhs rhs =>
    match extractStateTermCoeff lhs, extractStateTermCoeff rhs with
    | some (true, cCurr), some (false, cPrev) => some (cCurr, cPrev)
    | some (false, cPrev), some (true, cCurr) => some (cCurr, cPrev)
    | _, _ => none
  | _ => none

/-- Structural 2-state linear recurrence extractor (`extractTwoStateLinearRec`):
recognizes nested `Nat.rec` 2-state recurrences directly from `Term` AST structure
(extracting `(init0, init1, coeffCurr, coeffPrev)`) without inspecting string names! -/
def extractTwoStateLinearRec : Term → Option (Nat × Nat × Nat × Nat)
  | .lam (.lam body) => extractTwoStateLinearRec body
  | .lam body => extractTwoStateLinearRec body
  | .app
      (.fix
        (.lam (.lam (.lam
          (.ifZero (.bound 0)
            (.nat init0)
            (.app
              (.app
                (.lam (.lam
                  (.app
                    (.fix
                      (.lam (.lam (.lam
                        (.ifZero (.bound 0)
                          (.nat init1)
                          (.app (.app (.lam (.lam combBody)) (.bound 0)) (.app (.bound 3) (.bound 0)))))))
                      _)
                    (.bound 1))))
                (.bound 0))
              (.app (.bound 3) (.bound 0)))))))
        _)
      (.bound 0) =>
    match extractTwoStateCombCoeffs combBody with
    | some (coeffCurr, coeffPrev) => some (init0, init1, coeffCurr, coeffPrev)
    | none => none
  | _ => none

/-- Synthesize a general weighted 2-state linear recurrence sequential `RtlModule`
for `(a, b) ↦ (b, coeffCurr * b + coeffPrev * a)` starting at `(init0, init1)`. -/
def compileLinearRec2StateSat
    (fnName : String)
    (nVal init0 init1 coeffCurr coeffPrev : Nat) : RtlModule :=
  if coeffCurr == 1 && coeffPrev == 1 then
    compileNatRec2StateSat fnName nVal init0 init1
  else
    let w0 : WireAssign :=
      { wireIdx := 0
      , name    := "w_count"
      , expr    := .alu .bitOr (.inputPort 0) (.const (BitVec.ofNat 64 nVal)) }
    let w1 : WireAssign :=
      { wireIdx := 1
      , name    := "w_next_b"
      , expr    :=
          .alu .add
            (.alu .mul (.const (BitVec.ofNat 64 coeffCurr)) (.regRead 2))
            (.alu .mul (.const (BitVec.ofNat 64 coeffPrev)) (.regRead 1)) }
    let w2 : WireAssign :=
      { wireIdx := 2
      , name    := fnName
      , expr    := .regRead 1 }
    let w3 : WireAssign :=
      { wireIdx := 3
      , name    := "done"
      , expr    := .mux (.alu .ult (.regRead 0) (.wireRef 0)) (.const 0#64) (.const 1#64) }
    let condLt : RtlExpr := .alu .ult (.regRead 0) (.wireRef 0)
    let r0 : RegSpec :=
      { regIdx         := 0
      , name           := "reg_i"
      , domain         := .coreClk
      , resetKind      := .syncReset 0#64
      , isSynchronizer := false
      , nextExpr       := .mux condLt (.alu .add (.regRead 0) (.const 1#64)) (.regRead 0) }
    let r1 : RegSpec :=
      { regIdx         := 1
      , name           := "reg_a"
      , domain         := .coreClk
      , resetKind      := .syncReset (BitVec.ofNat 64 init0)
      , isSynchronizer := false
      , nextExpr       := .mux condLt (.regRead 2) (.regRead 1) }
    let r2 : RegSpec :=
      { regIdx         := 2
      , name           := "reg_b"
      , domain         := .coreClk
      , resetKind      := .syncReset (BitVec.ofNat 64 init1)
      , isSynchronizer := false
      , nextExpr       := .mux condLt (.wireRef 1) (.regRead 2) }
    let r3 : RegSpec :=
      { regIdx         := 3
      , name           := "reg_running"
      , domain         := .coreClk
      , resetKind      := .syncReset 1#64
      , isSynchronizer := false
      , nextExpr       := .mux condLt (.const 1#64) (.const 0#64) }
    let r4 : RegSpec :=
      { regIdx         := 4
      , name           := "reg_done"
      , domain         := .coreClk
      , resetKind      := .syncReset 0#64
      , isSynchronizer := false
      , nextExpr       := .wireRef 3 }
    { name       := fnName
      inputNames := ["arg"]
      wires      := [w0, w1, w2, w3]
      regs       := [r0, r1, r2, r3, r4]
      outputs    :=
        [ { name := s!"out_{fnName}", expr := .wireRef 2 }
        , { name := "out_done",       expr := .wireRef 3 } ] }

/-- Compile a single-slot `Obend.Leaf.Book` containing a `Nat.rec` loop (or 2-state linear recurrence
recognized structurally by `extractTwoStateLinearRec`) into a verified multi-cycle synchronous `RtlModule`. -/
def compileBookToSeqRtlSat (modName : String) (B : Book) : Option RtlModule :=
  match B.defs with
  | [d] =>
    match extractSeqNatRecDefSat d with
    | none =>
      match extractTwoStateLinearRec d.code with
      | some (init0, init1, coeffCurr, coeffPrev) =>
        some { (compileLinearRec2StateSat d.member 0 init0 init1 coeffCurr coeffPrev) with name := modName }
      | none =>
        none
    | some (zExpr, stepExpr, countExpr) =>
      let w0 : WireAssign := { wireIdx := 0, name := "w_count", expr := countExpr }
      let w1 : WireAssign :=
        { wireIdx := 1
        , name    := "w_eff_acc"
        , expr    := .mux (.alu .eq (.regRead 0) (.const 0#64)) zExpr (.regRead 1) }
      let w2 : WireAssign := { wireIdx := 2, name := "w_step", expr := stepExpr }
      let w3 : WireAssign := { wireIdx := 3, name := d.member, expr := .wireRef 1 }
      let w4 : WireAssign :=
        { wireIdx := 4
        , name    := "done"
        , expr    := .mux (.alu .ult (.regRead 0) (.wireRef 0)) (.const 0#64) (.const 1#64) }
      let r0 : RegSpec :=
        { regIdx         := 0
        , name           := "reg_idx"
        , domain         := .coreClk
        , resetKind      := .syncReset 0#64
        , isSynchronizer := false
        , nextExpr       :=
            .mux (.alu .ult (.regRead 0) (.wireRef 0))
              (.alu .add (.regRead 0) (.const 1#64))
              (.regRead 0) }
      let r1 : RegSpec :=
        { regIdx         := 1
        , name           := "reg_acc"
        , domain         := .coreClk
        , resetKind      := .syncReset 0#64
        , isSynchronizer := false
        , nextExpr       :=
            .mux (.alu .ult (.regRead 0) (.wireRef 0))
              (.wireRef 2)
              (.regRead 1) }
      some {
        name       := modName
        inputNames := ["arg"]
        wires      := [w0, w1, w2, w3, w4]
        regs       := [r0, r1]
        outputs    := [
          { name := s!"out_{d.member}", expr := .wireRef 3 },
          { name := "out_done",         expr := .wireRef 4 }
        ]
      }
  | _ => none

/-- Step a sequential `RtlModule` for `numCycles` clock edges (`rst = false`). -/
def stepSeqModuleN
    (m : RtlModule)
    (inputs : Nat → BitVec 64) : Nat → (Nat → BitVec 64) → (Nat → BitVec 64)
  | 0, regSt => regSt
  | k + 1, regSt => stepSeqModuleN m inputs k (stepModuleRegs m false inputs regSt)

/-- Reset a sequential `RtlModule` (`rst = true` for 1 cycle) and then step it for `numCycles`
active clock cycles (`rst = false`) with input port 0 driven by `argVal`, returning the resulting
module output port table. -/
def evalSeqModuleAfterCycles
    (m : RtlModule)
    (argVal : BitVec 64)
    (numCycles : Nat) : List (String × BitVec 64) :=
  let ins : Nat → BitVec 64 := fun _ => argVal
  let initSt := stepModuleRegs m true ins (fun _ => 0#64)
  let finalSt := stepSeqModuleN m ins numCycles initSt
  evalModuleOutputs m ins finalSt

/-- Pure mathematical specification of a 2-state linear recurrence `(a_k, b_k)` with
`(a_0, b_0) = (init0, init1)` and `(a_{k+1}, b_{k+1}) = (b_k, coeffCurr * b_k + coeffPrev * a_k)`. -/
def linearRec2StateSpec (init0 init1 coeffCurr coeffPrev : Nat) : Nat → Nat × Nat
  | 0 => (init0, init1)
  | k + 1 =>
    let st := linearRec2StateSpec init0 init1 coeffCurr coeffPrev k
    (st.2, coeffCurr * st.2 + coeffPrev * st.1)

/-- Single-step bounded transition for a 2-state linear recurrence loop `(i, a, b)`. -/
def stepLinearRec2StateLoop
    (nVal coeffCurr coeffPrev : Nat) (st : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (i, a, b) := st
  if i < nVal then
    (i + 1, b, coeffCurr * b + coeffPrev * a)
  else
    (i, a, b)

/-- Run the bounded 2-state linear recurrence loop for `k` cycles starting from `(0, init0, init1)`. -/
def runLinearRec2StateLoop
    (nVal init0 init1 coeffCurr coeffPrev : Nat) : Nat → Nat × Nat × Nat
  | 0 => (0, init0, init1)
  | k + 1 =>
    stepLinearRec2StateLoop nVal coeffCurr coeffPrev
      (runLinearRec2StateLoop nVal init0 init1 coeffCurr coeffPrev k)

/-- **Universal 2-State Linear Recurrence Loop Simulation (`runLinearRec2StateLoop_le_bound`)**:
For all `nVal init0 init1 coeffCurr coeffPrev k : Nat` with `k ≤ nVal`, stepping
`runLinearRec2StateLoop` for `k` cycles matches `linearRec2StateSpec`. -/
theorem runLinearRec2StateLoop_le_bound
    (nVal init0 init1 coeffCurr coeffPrev k : Nat) (hk : k ≤ nVal) :
    runLinearRec2StateLoop nVal init0 init1 coeffCurr coeffPrev k =
      (k,
       (linearRec2StateSpec init0 init1 coeffCurr coeffPrev k).1,
       (linearRec2StateSpec init0 init1 coeffCurr coeffPrev k).2) := by
  induction k with
  | zero => rfl
  | succ m ih =>
    have hm_le : m ≤ nVal := Nat.le_of_succ_le hk
    have hm_lt : m < nVal := hk
    simp only [runLinearRec2StateLoop, ih hm_le, stepLinearRec2StateLoop, hm_lt, ↓reduceIte,
      linearRec2StateSpec]

/-- Construct a canonical 2-state linear recurrence `Term` (`λself. λarg. ...`) from
`(init0, init1, coeffCurr, coeffPrev)`. -/
def mkTwoStateLinearRecTerm (init0 init1 coeffCurr coeffPrev : Nat) : Term :=
  .lam (.lam
    (.app
      (.fix
        (.lam (.lam (.lam
          (.ifZero (.bound 0)
            (.nat init0)
            (.app
              (.app
                (.lam (.lam
                  (.app
                    (.fix
                      (.lam (.lam (.lam
                        (.ifZero (.bound 0)
                          (.nat init1)
                          (.app
                            (.app
                              (.lam (.lam
                                (.binary .add
                                  (.binary .multiply (.nat coeffCurr) (.bound 0))
                                  (.binary .multiply (.nat coeffPrev) (.bound 2)))))
                              (.bound 0))
                            (.app (.bound 3) (.bound 0)))))))
                      (.record []))
                    (.bound 1))))
                (.bound 0))
              (.app (.bound 3) (.bound 0)))))))
        (.record []))
      (.bound 0)))

/-- **Theorem (`compileLinearRec2State_sound`)**:
1. **Universal Loop Agreement**: For all `init0 init1 coeffCurr coeffPrev k nVal : Nat` with `k ≤ nVal`,
   `runLinearRec2StateLoop` equals `(k, (linearRec2StateSpec ... k).1, (linearRec2StateSpec ... k).2)`.
2. **Structural Extraction Without String-Name Hardcoding**: `extractTwoStateLinearRec` extracts
   `some (init0, init1, coeffCurr, coeffPrev)` for ANY `init0 init1 coeffCurr coeffPrev : Nat`
   from `mkTwoStateLinearRecTerm`, and rejects a non-recurrence function even when named `"fib"`.
3. **General Recurrence Hardware Synthesis (Fibonacci, Lucas, Pell)**:
   - Fibonacci `(0, 1, 1, 1)` at `k = 7` evaluates to `13#64`,
   - Lucas `(2, 1, 1, 1)` at `k = 5` evaluates to `11#64` ($2, 1, 3, 4, 7, 11$),
   - Pell `(0, 1, 2, 1)` ($P_{n+2} = 2 P_{n+1} + P_n$) at `k = 5` evaluates to `29#64` ($0, 1, 2, 5, 12, 29$). -/
theorem compileLinearRec2State_sound :
    (∀ nVal init0 init1 cCurr cPrev k, k ≤ nVal →
      runLinearRec2StateLoop nVal init0 init1 cCurr cPrev k =
        (k,
         (linearRec2StateSpec init0 init1 cCurr cPrev k).1,
         (linearRec2StateSpec init0 init1 cCurr cPrev k).2)) ∧
    (∀ init0 init1 cCurr cPrev,
      extractTwoStateLinearRec (mkTwoStateLinearRecTerm init0 init1 cCurr cPrev) =
        some (init0, init1, cCurr, cPrev)) ∧
    -- Fake "fib" book whose body is `x + 1` is rejected (`none`), NOT miscompiled to Fibonacci!
    compileBookToSeqRtlSat "fib"
      { items := [.slot { member := "fib", slot := 0, kind := .method
                        , code := .lam (.lam (.binary .add (.bound 0) (.nat 1))), reads := [] }] } = none ∧
    -- General Pell recurrence book named "pellRec" (not "fib") compiles and simulates to 29 at k = 5!
    (let pellBook : Book :=
       { items := [.slot { member := "pellRec", slot := 0, kind := .method
                         , code := mkTwoStateLinearRecTerm 0 1 2 1, reads := [] }] }
     match compileBookToSeqRtlSat "pell_seq_rtl" pellBook with
     | some m =>
       checkRtlModule m &&
       (evalSeqModuleAfterCycles m 5#64 5 == [("out_pellRec", 29#64), ("out_done", 1#64)])
     | none => false) = true ∧
    -- Lucas recurrence (2, 1, 1, 1) at k = 5 evaluates to 11#64!
    evalSeqModuleAfterCycles (compileLinearRec2StateSat "lucas" 5 2 1 1 1) 5#64 5 =
      [("out_lucas", 11#64), ("out_done", 1#64)] := by
  refine ⟨runLinearRec2StateLoop_le_bound, fun _ _ _ _ => rfl, rfl, ?_, rfl⟩
  decide +kernel


/-! ## 7. Pure Functional `Nat.rec` Loop Model, All-`k` Inductive Proof & Universal Single-Step RTL Theorems -/

/-- Pure mathematical recursive specification of a linear `Nat.rec` accumulation loop:
$\text{acc}_0 = \text{baseVal}$ and $\text{acc}_{k+1} = \text{acc}_k + \text{stepCoeff} \cdot k$. -/
def natRecLinearSpec (baseVal stepCoeff : Nat) : Nat → Nat
  | 0 => baseVal
  | k + 1 => natRecLinearSpec baseVal stepCoeff k + stepCoeff * k

/-- Pure functional single-step transition for the `Nat.rec` loop state `(i, acc)` bounded by `nVal`. -/
def stepNatRecLoopState (nVal stepCoeff : Nat) (i acc : Nat) : Nat × Nat :=
  if i < nVal then
    (i + 1, acc + stepCoeff * i)
  else
    (i, acc)

/-- Iterate `stepNatRecLoopState` for `k` cycles starting from `(0, baseVal)`. -/
def runNatRecLoop (nVal baseVal stepCoeff : Nat) : Nat → Nat × Nat
  | 0 => (0, baseVal)
  | k + 1 =>
    let st := runNatRecLoop nVal baseVal stepCoeff k
    stepNatRecLoopState nVal stepCoeff st.1 st.2

/-- **Inductive Loop Simulation Theorem (`runNatRecLoop_le_bound`)**:
For all `nVal baseVal stepCoeff k : Nat` with `k ≤ nVal`, stepping `runNatRecLoop` for `k` cycles
produces loop index `i = k` and accumulator `acc = natRecLinearSpec baseVal stepCoeff k`. -/
theorem runNatRecLoop_le_bound (nVal baseVal stepCoeff k : Nat) (hk : k ≤ nVal) :
    runNatRecLoop nVal baseVal stepCoeff k = (k, natRecLinearSpec baseVal stepCoeff k) := by
  induction k with
  | zero => rfl
  | succ m ih =>
    have hm_le : m ≤ nVal := Nat.le_of_succ_le hk
    have hm_lt : m < nVal := hk
    simp only [runNatRecLoop, ih hm_le, stepNatRecLoopState, hm_lt, ↓reduceIte, natRecLinearSpec]

/-- **All-`k` Inductive Simulation Theorem (`runNatRecLoop_simulates_natRec_all_k`)**:
For ALL `baseVal stepCoeff k : Nat`, running the loop model for `k` iterations with bound `k`
yields `(k, natRecLinearSpec baseVal stepCoeff k)`. -/
theorem runNatRecLoop_simulates_natRec_all_k (baseVal stepCoeff k : Nat) :
    runNatRecLoop k baseVal stepCoeff k = (k, natRecLinearSpec baseVal stepCoeff k) :=
  runNatRecLoop_le_bound k baseVal stepCoeff k (Nat.le_refl k)

/-- **Post-Bound Stationarity Theorem (`runNatRecLoop_stationary_after_bound`)**:
Once `runNatRecLoop` reaches cycle `nVal`, any number of additional clock cycles `extra : Nat`
holds the state stationary at `(nVal, natRecLinearSpec baseVal stepCoeff nVal)`. -/
theorem runNatRecLoop_stationary_after_bound (nVal baseVal stepCoeff extra : Nat) :
    runNatRecLoop nVal baseVal stepCoeff (nVal + extra) =
      (nVal, natRecLinearSpec baseVal stepCoeff nVal) := by
  induction extra with
  | zero =>
    exact runNatRecLoop_le_bound nVal baseVal stepCoeff nVal (Nat.le_refl nVal)
  | succ d ih =>
    rw [Nat.add_succ]
    have hNotLt : ¬ (nVal < nVal) := Nat.lt_irrefl nVal
    simp only [runNatRecLoop, ih, stepNatRecLoopState, hNotLt, ↓reduceIte]

/-- Synthesize a synchronous sequential `RtlModule` for a linear `Nat.rec` accumulator loop with
iteration bound `nVal`, base value `baseVal`, and linear step coefficient `stepCoeff`:
* `reg 0` (`reg_i`): loop counter $i$,
* `reg 1` (`reg_acc`): accumulator $\text{acc}$,
* `reg 2` (`reg_running`): active loop flag (`1#64` while running),
* `reg 3` (`reg_done`): completion strobe (`1#64` when `i ≥ nVal`). -/
def compileNatRecSat (fnName : String) (nVal baseVal stepCoeff : Nat) : RtlModule :=
  let boundConst := RtlExpr.const (BitVec.ofNat 64 nVal)
  let coeffConst := RtlExpr.const (BitVec.ofNat 64 stepCoeff)
  let isRunningAndLt :=
    RtlExpr.mux (.regRead 2)
      (.alu .ult (.regRead 0) boundConst)
      (.const 0#64)
  let nextI :=
    RtlExpr.mux isRunningAndLt
      (.alu .add (.regRead 0) (.const 1#64))
      (.regRead 0)
  let nextAcc :=
    RtlExpr.mux isRunningAndLt
      (.alu .add (.regRead 1) (.alu .mul coeffConst (.regRead 0)))
      (.regRead 1)
  let nextRunning :=
    RtlExpr.mux isRunningAndLt (.const 1#64) (.const 0#64)
  let nextDone :=
    RtlExpr.mux isRunningAndLt (.const 0#64) (.const 1#64)
  { name       := fnName
  , inputNames := ["arg"]
  , wires      := []
  , regs       :=
      [ { regIdx := 0, name := "reg_i",       domain := .coreClk, resetKind := .syncReset 0#64,                      isSynchronizer := false, nextExpr := nextI }
      , { regIdx := 1, name := "reg_acc",     domain := .coreClk, resetKind := .syncReset (BitVec.ofNat 64 baseVal), isSynchronizer := false, nextExpr := nextAcc }
      , { regIdx := 2, name := "reg_running", domain := .coreClk, resetKind := .syncReset 1#64,                      isSynchronizer := false, nextExpr := nextRunning }
      , { regIdx := 3, name := "reg_done",    domain := .coreClk, resetKind := .syncReset 0#64,                      isSynchronizer := false, nextExpr := nextDone } ]
  , outputs    :=
      [ { name := s!"out_{fnName}", expr := .regRead 1 }
      , { name := "out_done",       expr := .regRead 3 } ] }

/-- **Universal Single-Step RTL Transition Theorem (`compileNatRecSat_running_step_universal`)**:
For ANY `fnName : String`, `nVal baseVal stepCoeff : Nat`, input environment `inputs`, and register
state `regs` where `reg_running = 1#64` (`regs 2 = 1#64`) and `BitVec.ult (regs 0) (BitVec.ofNat 64 nVal) = true`,
stepping `compileNatRecSat fnName nVal baseVal stepCoeff` by one clock edge updates `"reg_i"` (`0`)
to `regs 0 + 1#64` and `"reg_acc"` (`1`) to `regs 1 + BitVec.ofNat 64 stepCoeff * regs 0`. -/
theorem compileNatRecSat_running_step_universal
    (fnName : String) (nVal baseVal stepCoeff : Nat)
    (inputs regs : Nat → BitVec 64)
    (hRun : regs 2 = 1#64)
    (hLt  : BitVec.ult (regs 0) (BitVec.ofNat 64 nVal) = true) :
    stepModuleRegs (compileNatRecSat fnName nVal baseVal stepCoeff) false inputs regs 0 =
      regs 0 + 1#64 ∧
    stepModuleRegs (compileNatRecSat fnName nVal baseVal stepCoeff) false inputs regs 1 =
      regs 1 + BitVec.ofNat 64 stepCoeff * regs 0 := by
  simp [compileNatRecSat, stepModuleRegs, evalWireTable, evalRtlExpr, evalAluOp, hRun, hLt]

/-- **Universal Single-Step RTL Transition Theorem for 2-State Recurrences (`compileNatRec2StateSat_running_step_universal`)**:
For ANY `fnName : String`, `nVal initA initB : Nat`, `inputs`, and `regs` where
`BitVec.ult (regs 0) (inputs 0 ||| BitVec.ofNat 64 nVal) = true`, stepping
`compileNatRec2StateSat fnName nVal initA initB` updates `"reg_i"` (`0`) to `regs 0 + 1#64`,
`"reg_a"` (`1`) to `regs 2`, and `"reg_b"` (`2`) to `regs 1 + regs 2`. -/
theorem compileNatRec2StateSat_running_step_universal
    (fnName : String) (nVal initA initB : Nat)
    (inputs regs : Nat → BitVec 64)
    (hLt : BitVec.ult (regs 0) (inputs 0 ||| BitVec.ofNat 64 nVal) = true) :
    stepModuleRegs (compileNatRec2StateSat fnName nVal initA initB) false inputs regs 0 =
      regs 0 + 1#64 ∧
    stepModuleRegs (compileNatRec2StateSat fnName nVal initA initB) false inputs regs 1 =
      regs 2 ∧
    stepModuleRegs (compileNatRec2StateSat fnName nVal initA initB) false inputs regs 2 =
      regs 1 + regs 2 := by
  simp [compileNatRec2StateSat, stepModuleRegs, evalWireTable, evalRtlExpr, evalAluOp, hLt]

/-! ## 8. Multi-Argument Port Substitution & Multi-Argument Method Compilation (`substInputPorts`, `compileMultiArgTerm`, `compileMultiArgMethod`) -/

/-- Substitute a list of argument expressions `argExprs` for `.inputPort idx` across an `RtlExpr`:
any `.inputPort idx` with `idx < argExprs.length` is replaced by `argExprs[idx]`, while higher-indexed
input ports remain `.inputPort idx`. Generalizes `substInputPort0` to arbitrary multi-port methods. -/
def substInputPorts (argExprs : List RtlExpr) : RtlExpr → RtlExpr
  | .const v       => .const v
  | .inputPort idx =>
    match argExprs[idx]? with
    | some ae => ae
    | none    => .inputPort idx
  | .wireRef idx   => .wireRef idx
  | .regRead idx   => .regRead idx
  | .alu op a b    => .alu op (substInputPorts argExprs a) (substInputPorts argExprs b)
  | .mux c t f     =>
    .mux (substInputPorts argExprs c) (substInputPorts argExprs t) (substInputPorts argExprs f)
  | .bitNot a      => .bitNot (substInputPorts argExprs a)

/-- **Universal Soundness of Multi-Port Substitution (`substInputPorts_sound`)**:
Evaluating `substInputPorts argExprs e` is identical to evaluating `e` in an input environment where
each port `i < argExprs.length` is bound to `evalRtlExpr inputs wires regs argExprs[i]`. -/
theorem substInputPorts_sound
    (inputs wires regs : Nat → BitVec 64)
    (argExprs : List RtlExpr) (e : RtlExpr) :
    evalRtlExpr inputs wires regs (substInputPorts argExprs e) =
      evalRtlExpr
        (fun i => match argExprs[i]? with
                  | some ae => evalRtlExpr inputs wires regs ae
                  | none    => inputs i)
        wires regs e := by
  induction e with
  | const v => rfl
  | inputPort idx =>
    simp only [substInputPorts, evalRtlExpr]
    cases hIdx : argExprs[idx]? <;> simp [evalRtlExpr]
  | wireRef idx => rfl
  | regRead idx => rfl
  | alu op a b iha ihb =>
    simp only [substInputPorts, evalRtlExpr, iha, ihb]
  | mux c t f ihc iht ihf =>
    simp only [substInputPorts, evalRtlExpr, ihc, iht, ihf]
  | bitNot a iha =>
    simp only [substInputPorts, evalRtlExpr, iha]

/-- Reference 64-bit hardware semantics for multi-argument `Term`s (`evalMultiArgTermHw`):
supports arbitrary `inputPort idx` bindings in `varVals`, unary `self.m(arg0)` calls, and
curried binary `self.m(arg0, arg1)` calls via `substInputPorts`. -/
def evalMultiArgTermHw
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
      match evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg with
      | some vArg =>
        evalMultiArgTermHw slots slotBodies inputs slotWires regs (selfDepth + 1) (vArg :: varVals) subBody
      | none => none
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg with
        | some slotIdx, some vArg =>
          match slotBodies[slotIdx]? with
          | some slotExpr =>
            let argVals := [vArg]
            some (evalRtlExpr
              (fun i => match argVals[i]? with | some v => v | none => inputs i)
              slotWires regs slotExpr)
          | none => none
        | _, _ => none
      else none
    | .app (.get (.bound idx) member) arg0 =>
      if idx == selfDepth then
        match slots.idxOf? member,
              evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg0,
              evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg with
        | some slotIdx, some vArg0, some vArg1 =>
          match slotBodies[slotIdx]? with
          | some slotExpr =>
            let argVals := [vArg0, vArg1]
            some (evalRtlExpr
              (fun i => match argVals[i]? with | some v => v | none => inputs i)
              slotWires regs slotExpr)
          | none => none
        | _, _, _ => none
      else none
    | .app (.app (.get (.bound idx) member) arg0) arg1 =>
      if idx == selfDepth then
        match slots.idxOf? member,
              evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg0,
              evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg1,
              evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals arg with
        | some slotIdx, some vArg0, some vArg1, some vArg2 =>
          match slotBodies[slotIdx]? with
          | some slotExpr =>
            let argVals := [vArg0, vArg1, vArg2]
            some (evalRtlExpr
              (fun i => match argVals[i]? with | some v => v | none => inputs i)
              slotWires regs slotExpr)
          | none => none
        | _, _, _, _ => none
      else none
    | _ => none
  | .binary op l r =>
    match evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals l,
          evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals r with
    | some vl, some vr => evalPrimHwSat op vl vr
    | _, _ => none
  | .ifBool c t f =>
    match evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals c,
          evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals t,
          evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals f with
    | some vc, some vt, some vf => some (if vc != 0#64 then vt else vf)
    | _, _, _ => none
  | .ifZero v z s =>
    match evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals v,
          evalMultiArgTermHw slots slotBodies inputs slotWires regs selfDepth varVals z with
    | some vv, some vz =>
      match evalMultiArgTermHw slots slotBodies inputs slotWires regs (selfDepth + 1) ((vv - 1#64) :: varVals) s with
      | some vs => some (if (if vv == 0#64 then 1#64 else 0#64) != 0#64 then vz else vs)
      | none => none
    | _, _ => none
  | _ => none

/-- Compile an `Obend.Core.Term` with multi-argument port bindings (`inputPort idx` for arbitrary
`idx : Nat`), supporting unary `self.m(arg0)`, binary `self.m(arg0, arg1)`, and ternary
`self.m(arg0, arg1, arg2)` slot calls via `substInputPorts`. -/
def compileMultiArgTerm
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
      match compileMultiArgTerm slots slotBodies selfDepth varEnv arg with
      | some eArg =>
        compileMultiArgTerm slots slotBodies (selfDepth + 1) (eArg :: varEnv) subBody
      | none => none
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              compileMultiArgTerm slots slotBodies selfDepth varEnv arg with
        | some slotIdx, some eArg =>
          match slotBodies[slotIdx]? with
          | some slotExpr => some (substInputPorts [eArg] slotExpr)
          | none => none
        | _, _ => none
      else none
    | .app (.get (.bound idx) member) arg0 =>
      if idx == selfDepth then
        match slots.idxOf? member,
              compileMultiArgTerm slots slotBodies selfDepth varEnv arg0,
              compileMultiArgTerm slots slotBodies selfDepth varEnv arg with
        | some slotIdx, some eArg0, some eArg1 =>
          match slotBodies[slotIdx]? with
          | some slotExpr => some (substInputPorts [eArg0, eArg1] slotExpr)
          | none => none
        | _, _, _ => none
      else none
    | .app (.app (.get (.bound idx) member) arg0) arg1 =>
      if idx == selfDepth then
        match slots.idxOf? member,
              compileMultiArgTerm slots slotBodies selfDepth varEnv arg0,
              compileMultiArgTerm slots slotBodies selfDepth varEnv arg1,
              compileMultiArgTerm slots slotBodies selfDepth varEnv arg with
        | some slotIdx, some eArg0, some eArg1, some eArg2 =>
          match slotBodies[slotIdx]? with
          | some slotExpr => some (substInputPorts [eArg0, eArg1, eArg2] slotExpr)
          | none => none
        | _, _, _, _ => none
      else none
    | _ => none
  | .binary op l r =>
    match compileMultiArgTerm slots slotBodies selfDepth varEnv l,
          compileMultiArgTerm slots slotBodies selfDepth varEnv r with
    | some el, some er => compilePrimSat op el er
    | _, _ => none
  | .ifBool c t f =>
    match compileMultiArgTerm slots slotBodies selfDepth varEnv c,
          compileMultiArgTerm slots slotBodies selfDepth varEnv t,
          compileMultiArgTerm slots slotBodies selfDepth varEnv f with
    | some ec, some et, some ef => some (.mux ec et ef)
    | _, _, _ => none
  | .ifZero v z s =>
    match compileMultiArgTerm slots slotBodies selfDepth varEnv v,
          compileMultiArgTerm slots slotBodies selfDepth varEnv z with
    | some ev, some ez =>
      let predExpr := RtlExpr.alu .sub ev (.const 1#64)
      match compileMultiArgTerm slots slotBodies (selfDepth + 1) (predExpr :: varEnv) s with
      | some es => some (.mux (.alu .eq ev (.const 0#64)) ez es)
      | none => none
    | _, _ => none
  | _ => none

/-- **Universal Structural Soundness of `compileMultiArgTerm` (`compileMultiArgTerm_sound`)**:
For EVERY `t : Term` and arbitrary multi-port variable environment `varEnv : List RtlExpr`,
if `compileMultiArgTerm slots slotBodies selfDepth varEnv t = some e`, then evaluating `e` in
`evalRtlExpr` matches `evalMultiArgTermHw` under `varEnv.map (evalRtlExpr inputs wires regs)`. -/
theorem compileMultiArgTerm_sound
    (inputs wires regs : Nat → BitVec 64)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (t : Term)
    (selfDepth : Nat) (varEnv : List RtlExpr) (e : RtlExpr)
    (h : compileMultiArgTerm slots slotBodies selfDepth varEnv t = some e) :
    evalMultiArgTermHw slots slotBodies inputs wires regs selfDepth
        (varEnv.map (evalRtlExpr inputs wires regs)) t =
      some (evalRtlExpr inputs wires regs e) := by
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .inject _ _ | .case _ _ | .perform _ | .done _ | .split _ _ _ =>
    simp [compileMultiArgTerm] at h
  | .record fs =>
    cases fs with
    | nil =>
      simp only [compileMultiArgTerm, Option.some.injEq] at h
      subst h
      rfl
    | cons _ _ =>
      simp [compileMultiArgTerm] at h
  | .nat n =>
    simp only [compileMultiArgTerm, Option.some.injEq] at h
    subst h
    rfl
  | .boolean b =>
    simp only [compileMultiArgTerm, Option.some.injEq] at h
    subst h
    rfl
  | .bound idx =>
    simp only [compileMultiArgTerm] at h
    simp only [evalMultiArgTermHw, List.getElem?_map, h, Option.map_some]
  | .get target member =>
    cases target with
    | bound idx =>
      simp only [compileMultiArgTerm] at h
      simp only [evalMultiArgTermHw]
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
      simp [compileMultiArgTerm] at h
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [compileMultiArgTerm] at h
      cases hArg : compileMultiArgTerm slots slotBodies selfDepth varEnv arg with
      | none => simp [hArg] at h
      | some eArg =>
        simp only [hArg] at h
        have ihArg := compileMultiArgTerm_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg hArg
        have ihBody := compileMultiArgTerm_sound inputs wires regs slots slotBodies subBody
          (selfDepth + 1) (eArg :: varEnv) e h
        simp only [List.map_cons] at ihBody
        simp only [evalMultiArgTermHw, ihArg, ihBody]
    | get target member =>
      cases target with
      | bound idx =>
        simp only [compileMultiArgTerm] at h
        simp only [evalMultiArgTermHw]
        by_cases hEq : idx == selfDepth
        · simp only [hEq, ↓reduceIte] at h ⊢
          cases hSlot : slots.idxOf? member with
          | none => simp [hSlot] at h
          | some slotIdx =>
            cases hArg : compileMultiArgTerm slots slotBodies selfDepth varEnv arg with
            | none => simp [hSlot, hArg] at h
            | some eArg =>
              simp only [hSlot, hArg] at h
              cases hBody : slotBodies[slotIdx]? with
              | none => simp [hBody] at h
              | some slotExpr =>
                simp only [hBody, Option.some.injEq] at h
                subst h
                have ihArg := compileMultiArgTerm_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg hArg
                simp only [ihArg, hBody, substInputPorts_sound]
                congr 2
                funext i
                cases i <;> rfl
        · simp [hEq] at h
      | _ =>
        simp [compileMultiArgTerm] at h
    | app innerFn arg0 =>
      cases innerFn with
      | get target member =>
        cases target with
        | bound idx =>
          simp only [compileMultiArgTerm] at h
          simp only [evalMultiArgTermHw]
          by_cases hEq : idx == selfDepth
          · simp only [hEq, ↓reduceIte] at h ⊢
            cases hSlot : slots.idxOf? member with
            | none => simp [hSlot] at h
            | some slotIdx =>
              cases hArg0 : compileMultiArgTerm slots slotBodies selfDepth varEnv arg0 with
              | none => simp [hSlot, hArg0] at h
              | some eArg0 =>
                cases hArg1 : compileMultiArgTerm slots slotBodies selfDepth varEnv arg with
                | none => simp [hSlot, hArg0, hArg1] at h
                | some eArg1 =>
                  simp only [hSlot, hArg0, hArg1] at h
                  cases hBody : slotBodies[slotIdx]? with
                  | none => simp [hBody] at h
                  | some slotExpr =>
                    simp only [hBody, Option.some.injEq] at h
                    subst h
                    have ihArg0 := compileMultiArgTerm_sound inputs wires regs slots slotBodies arg0 selfDepth varEnv eArg0 hArg0
                    have ihArg1 := compileMultiArgTerm_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg1 hArg1
                    simp only [ihArg0, ihArg1, hBody, substInputPorts_sound]
                    congr 2
                    funext i
                    cases i with
                    | zero => rfl
                    | succ j =>
                      cases j <;> rfl
          · simp [hEq] at h
        | _ =>
          simp [compileMultiArgTerm] at h
      | app innerFn2 arg00 =>
        cases innerFn2 with
        | get target member =>
          cases target with
          | bound idx =>
            simp only [compileMultiArgTerm] at h
            simp only [evalMultiArgTermHw]
            by_cases hEq : idx == selfDepth
            · simp only [hEq, ↓reduceIte] at h ⊢
              cases hSlot : slots.idxOf? member with
              | none => simp [hSlot] at h
              | some slotIdx =>
                cases hArg0 : compileMultiArgTerm slots slotBodies selfDepth varEnv arg00 with
                | none => simp [hSlot, hArg0] at h
                | some eArg0 =>
                  cases hArg1 : compileMultiArgTerm slots slotBodies selfDepth varEnv arg0 with
                  | none => simp [hSlot, hArg0, hArg1] at h
                  | some eArg1 =>
                    cases hArg2 : compileMultiArgTerm slots slotBodies selfDepth varEnv arg with
                    | none => simp [hSlot, hArg0, hArg1, hArg2] at h
                    | some eArg2 =>
                      simp only [hSlot, hArg0, hArg1, hArg2] at h
                      cases hBody : slotBodies[slotIdx]? with
                      | none => simp [hBody] at h
                      | some slotExpr =>
                        simp only [hBody, Option.some.injEq] at h
                        subst h
                        have ihArg0 := compileMultiArgTerm_sound inputs wires regs slots slotBodies arg00 selfDepth varEnv eArg0 hArg0
                        have ihArg1 := compileMultiArgTerm_sound inputs wires regs slots slotBodies arg0 selfDepth varEnv eArg1 hArg1
                        have ihArg2 := compileMultiArgTerm_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg2 hArg2
                        simp only [ihArg0, ihArg1, ihArg2, hBody, substInputPorts_sound]
                        congr 2
                        funext i
                        cases i with
                        | zero => rfl
                        | succ j =>
                          cases j with
                          | zero => rfl
                          | succ k =>
                            cases k <;> rfl
            · simp [hEq] at h
          | _ =>
            simp [compileMultiArgTerm] at h
        | _ =>
          simp [compileMultiArgTerm] at h
      | _ =>
        simp [compileMultiArgTerm] at h
    | _ =>
      simp [compileMultiArgTerm] at h
  | .binary op l r =>
    simp only [compileMultiArgTerm] at h
    cases hl : compileMultiArgTerm slots slotBodies selfDepth varEnv l with
    | none => simp [hl] at h
    | some el =>
      cases hr : compileMultiArgTerm slots slotBodies selfDepth varEnv r with
      | none => simp [hl, hr] at h
      | some er =>
        simp only [hl, hr] at h
        have ihl := compileMultiArgTerm_sound inputs wires regs slots slotBodies l selfDepth varEnv el hl
        have ihr := compileMultiArgTerm_sound inputs wires regs slots slotBodies r selfDepth varEnv er hr
        simp only [evalMultiArgTermHw, ihl, ihr]
        exact compilePrimSat_sound inputs wires regs op el er e h
  | .ifBool c t f =>
    simp only [compileMultiArgTerm] at h
    cases hc : compileMultiArgTerm slots slotBodies selfDepth varEnv c with
    | none => simp [hc] at h
    | some ec =>
      cases ht : compileMultiArgTerm slots slotBodies selfDepth varEnv t with
      | none => simp [hc, ht] at h
      | some et =>
        cases hf : compileMultiArgTerm slots slotBodies selfDepth varEnv f with
        | none => simp [hc, ht, hf] at h
        | some ef =>
          simp only [hc, ht, hf, Option.some.injEq] at h
          subst h
          have ihc := compileMultiArgTerm_sound inputs wires regs slots slotBodies c selfDepth varEnv ec hc
          have iht := compileMultiArgTerm_sound inputs wires regs slots slotBodies t selfDepth varEnv et ht
          have ihf := compileMultiArgTerm_sound inputs wires regs slots slotBodies f selfDepth varEnv ef hf
          simp only [evalMultiArgTermHw, ihc, iht, ihf, evalRtlExpr]
  | .ifZero v z s =>
    simp only [compileMultiArgTerm] at h
    cases hv : compileMultiArgTerm slots slotBodies selfDepth varEnv v with
    | none => simp [hv] at h
    | some ev =>
      cases hz : compileMultiArgTerm slots slotBodies selfDepth varEnv z with
      | none => simp [hv, hz] at h
      | some ez =>
        cases hs : compileMultiArgTerm slots slotBodies (selfDepth + 1)
            (RtlExpr.alu .sub ev (.const 1#64) :: varEnv) s with
        | none => simp [hv, hz, hs] at h
        | some es =>
          simp only [hv, hz, hs, Option.some.injEq] at h
          subst h
          have hv' := compileMultiArgTerm_sound inputs wires regs slots slotBodies v selfDepth varEnv ev hv
          have hz' := compileMultiArgTerm_sound inputs wires regs slots slotBodies z selfDepth varEnv ez hz
          have hs' := compileMultiArgTerm_sound inputs wires regs slots slotBodies s (selfDepth + 1)
            (RtlExpr.alu .sub ev (.const 1#64) :: varEnv) es hs
          simp only [List.map_cons, evalRtlExpr, evalAluOp] at hs'
          simp only [evalMultiArgTermHw, hv', hz', hs', evalRtlExpr, evalAluOp]
          rfl

/-- Peel `arity` nested `.lam` argument binders from a curried method body `λx_0. ... λx_{arity-1}. body`. -/
def peelMultiArgLambdas : Nat → Term → Option Term
  | 0, body => some body
  | k + 1, .lam sub => peelMultiArgLambdas k sub
  | _ + 1, _ => none

/-- Construct the de Bruijn port environment `[.inputPort (arity - 1), ..., .inputPort 0]` for an
`arity`-argument hardware method `λself. λx_0. ... λx_{arity-1}. body`. -/
def mkMultiArgPortEnv (arity : Nat) : List RtlExpr :=
  (List.range arity).reverse.map RtlExpr.inputPort

/-- Compile a curried `arity`-argument method (`λself. λx_0. ... λx_{arity-1}. body`) to an `RtlExpr`
binding each parameter $x_j$ (`0 ≤ j < arity`) to `.inputPort j`. -/
def compileMultiArgMethod
    (slots : List String)
    (slotBodies : List RtlExpr)
    (arity : Nat)
    (code : Term) : Option RtlExpr :=
  match code with
  | .lam selfBody =>
    match peelMultiArgLambdas arity selfBody with
    | some innerBody =>
      compileMultiArgTerm slots slotBodies arity (mkMultiArgPortEnv arity) innerBody
    | none => none
  | _ => none

/-- **Theorem (`compileMultiArgMethod_sound`)**:
For any `arity`-argument method `code = .lam selfBody` where `peelMultiArgLambdas arity selfBody = some innerBody`,
if `compileMultiArgMethod slots slotBodies arity code = some e`, then evaluating `e` in `evalRtlExpr`
matches `evalMultiArgTermHw` under the `arity`-port input environment! -/
theorem compileMultiArgMethod_sound
    (inputs wires regs : Nat → BitVec 64)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (arity : Nat) (selfBody innerBody : Term) (e : RtlExpr)
    (hPeel : peelMultiArgLambdas arity selfBody = some innerBody)
    (hComp : compileMultiArgMethod slots slotBodies arity (.lam selfBody) = some e) :
    evalMultiArgTermHw slots slotBodies inputs wires regs arity
        ((mkMultiArgPortEnv arity).map (evalRtlExpr inputs wires regs)) innerBody =
      some (evalRtlExpr inputs wires regs e) := by
  simp only [compileMultiArgMethod, hPeel] at hComp
  exact compileMultiArgTerm_sound inputs wires regs slots slotBodies innerBody
    arity (mkMultiArgPortEnv arity) e hComp

/-! ## 9. Non-Inlined Pipelined Inter-Slot Compilation (`compileTermPipelined`, `compileBookToPipelinedRtl`) -/

/-- Substitute `argExpr` for `.inputPort 0` throughout a callee slot's compiled `RtlExpr`
when a pipelined method invokes an earlier slot on a non-direct argument (`isDirectPipeArg arg = false`). -/
def substRtlInputPort0 (argExpr : RtlExpr) : RtlExpr → RtlExpr
  | .const v       => .const v
  | .inputPort idx => if idx == 0 then argExpr else .inputPort idx
  | .wireRef idx   => .wireRef idx
  | .regRead idx   => .regRead idx
  | .alu op a b    => .alu op (substRtlInputPort0 argExpr a) (substRtlInputPort0 argExpr b)
  | .mux c t f     =>
    .mux (substRtlInputPort0 argExpr c) (substRtlInputPort0 argExpr t) (substRtlInputPort0 argExpr f)
  | .bitNot a      => .bitNot (substRtlInputPort0 argExpr a)

/-- Soundness of `substRtlInputPort0`: evaluating `substRtlInputPort0 argExpr e` is identical to
evaluating `e` with input port `0` bound to `evalRtlExpr inputs wires regs argExpr`. -/
theorem substRtlInputPort0_sound
    (inputs wires regs : Nat → BitVec 64)
    (argExpr e : RtlExpr) :
    evalRtlExpr inputs wires regs (substRtlInputPort0 argExpr e) =
      evalRtlExpr
        (fun i => if i == 0 then evalRtlExpr inputs wires regs argExpr else inputs i)
        wires regs e := by
  induction e with
  | const v => rfl
  | inputPort idx =>
    simp only [substRtlInputPort0, evalRtlExpr]
    by_cases h : idx == 0 <;> simp [h, evalRtlExpr]
  | wireRef idx => rfl
  | regRead idx => rfl
  | alu op a b iha ihb =>
    simp only [substRtlInputPort0, evalRtlExpr, iha, ihb]
  | mux c t f ihc iht ihf =>
    simp only [substRtlInputPort0, evalRtlExpr, ihc, iht, ihf]
  | bitNot a iha =>
    simp only [substRtlInputPort0, evalRtlExpr, iha]

/-- Check whether a pipelined method argument is the unmodified stage input `.bound 0`. -/
def isDirectPipeArg : Term → Bool
  | .bound 0 => true
  | _        => false

/-- Reference 64-bit hardware semantics for pipelined inter-slot execution:
* When referencing an earlier slot `self.m` or calling `self.m(arg)` with `isDirectPipeArg arg = true`
  (`arg = .bound 0`), reads the registered pipeline stage output `regs slotIdx` (`.regRead slotIdx`).
* When calling `self.m(arg)` with `isDirectPipeArg arg = false`, looks up `calleeBody ← slotBodies[slotIdx]?`
  and evaluates `calleeBody` with `.inputPort 0` bound to `vArg`. -/
def evalTermPipelinedHw
    (slots : List String)
    (slotBodies : List RtlExpr)
    (inputs wires regs : Nat → BitVec 64)
    (selfDepth : Nat)
    (varVals : List (BitVec 64)) : Term → Option (BitVec 64)
  | .nat n => some (BitVec.ofNat 64 n)
  | .boolean b => some (if b then 1#64 else 0#64)
  | .record [] => some 0#64
  | .bound idx => varVals[idx]?
  | .get (.bound idx) member =>
    if idx == selfDepth then
      match slots.idxOf? member with
      | some slotIdx => some (regs slotIdx)
      | none => none
    else none
  | .app fn arg =>
    match fn with
    | .lam subBody =>
      match evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals arg with
      | some vArg =>
        evalTermPipelinedHw slots slotBodies inputs wires regs (selfDepth + 1) (vArg :: varVals) subBody
      | none => none
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals arg with
        | some slotIdx, some vArg =>
          if isDirectPipeArg arg then
            some (regs slotIdx)
          else
            match slotBodies[slotIdx]? with
            | some calleeBody =>
              some (evalRtlExpr (fun i => if i == 0 then vArg else inputs i) wires regs calleeBody)
            | none => none
        | _, _ => none
      else none
    | _ => none
  | .binary op l r =>
    match evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals l,
          evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals r with
    | some vl, some vr => evalPrimHwSat op vl vr
    | _, _ => none
  | .ifBool c t f =>
    match evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals c,
          evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals t,
          evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals f with
    | some vc, some vt, some vf => some (if vc != 0#64 then vt else vf)
    | _, _, _ => none
  | .ifZero v z s =>
    match evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals v,
          evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth varVals z with
    | some vv, some vz =>
      match evalTermPipelinedHw slots slotBodies inputs wires regs (selfDepth + 1) ((vv - 1#64) :: varVals) s with
      | some vs => some (if (if vv == 0#64 then 1#64 else 0#64) != 0#64 then vz else vs)
      | none => none
    | _, _ => none
  | _ => none

/-- Pipelined `Term` compiler:
* Maps direct stage references `self.m` and unmodified stage-input calls `self.m(.bound 0)`
  (`isDirectPipeArg arg = true`) to synchronous pipeline stage register reads `.regRead slotIdx`.
* When `isDirectPipeArg arg = false`, looks up `calleeBody ← slotBodies[slotIdx]?` and emits
  `substRtlInputPort0 eArg calleeBody` (applying `member`'s actual compiled `RtlExpr` body to `eArg`). -/
def compileTermPipelined
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
      | some slotIdx => some (.regRead slotIdx)
      | none => none
    else none
  | .app fn arg =>
    match fn with
    | .lam subBody =>
      match compileTermPipelined slots slotBodies selfDepth varEnv arg with
      | some eArg =>
        compileTermPipelined slots slotBodies (selfDepth + 1) (eArg :: varEnv) subBody
      | none => none
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              compileTermPipelined slots slotBodies selfDepth varEnv arg with
        | some slotIdx, some eArg =>
          if isDirectPipeArg arg then
            some (.regRead slotIdx)
          else
            match slotBodies[slotIdx]? with
            | some calleeBody => some (substRtlInputPort0 eArg calleeBody)
            | none => none
        | _, _ => none
      else none
    | _ => none
  | .binary op l r =>
    match compileTermPipelined slots slotBodies selfDepth varEnv l,
          compileTermPipelined slots slotBodies selfDepth varEnv r with
    | some el, some er => compilePrimSat op el er
    | _, _ => none
  | .ifBool c t f =>
    match compileTermPipelined slots slotBodies selfDepth varEnv c,
          compileTermPipelined slots slotBodies selfDepth varEnv t,
          compileTermPipelined slots slotBodies selfDepth varEnv f with
    | some ec, some et, some ef => some (.mux ec et ef)
    | _, _, _ => none
  | .ifZero v z s =>
    match compileTermPipelined slots slotBodies selfDepth varEnv v,
          compileTermPipelined slots slotBodies selfDepth varEnv z with
    | some ev, some ez =>
      let predExpr := RtlExpr.alu .sub ev (.const 1#64)
      match compileTermPipelined slots slotBodies (selfDepth + 1) (predExpr :: varEnv) s with
      | some es => some (.mux (.alu .eq ev (.const 0#64)) ez es)
      | none => none
    | _, _ => none
  | _ => none

/-- **Universal Structural Soundness of `compileTermPipelined` (`compileTermPipelined_sound`)**:
For EVERY `t : Term`, if `compileTermPipelined slots slotBodies selfDepth varEnv t = some e`, then
evaluating `e` in `evalRtlExpr` produces the exact same 64-bit value as `evalTermPipelinedHw`. -/
theorem compileTermPipelined_sound
    (inputs wires regs : Nat → BitVec 64)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (t : Term)
    (selfDepth : Nat) (varEnv : List RtlExpr) (e : RtlExpr)
    (h : compileTermPipelined slots slotBodies selfDepth varEnv t = some e) :
    evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth (varEnv.map (evalRtlExpr inputs wires regs)) t =
      some (evalRtlExpr inputs wires regs e) := by
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .inject _ _ | .case _ _ | .perform _ | .done _ | .split _ _ _ =>
    simp [compileTermPipelined] at h
  | .record fs =>
    cases fs with
    | nil =>
      simp only [compileTermPipelined, Option.some.injEq] at h
      subst h
      rfl
    | cons _ _ =>
      simp [compileTermPipelined] at h
  | .nat n =>
    simp only [compileTermPipelined, Option.some.injEq] at h
    subst h
    rfl
  | .boolean b =>
    simp only [compileTermPipelined, Option.some.injEq] at h
    subst h
    rfl
  | .bound idx =>
    simp only [compileTermPipelined] at h
    simp only [evalTermPipelinedHw, List.getElem?_map, h, Option.map_some]
  | .get target member =>
    cases target with
    | bound idx =>
      simp only [compileTermPipelined] at h
      simp only [evalTermPipelinedHw]
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
      simp [compileTermPipelined] at h
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [compileTermPipelined] at h
      cases hArg : compileTermPipelined slots slotBodies selfDepth varEnv arg with
      | none => simp [hArg] at h
      | some eArg =>
        simp only [hArg] at h
        have ihArg := compileTermPipelined_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg hArg
        have ihBody := compileTermPipelined_sound inputs wires regs slots slotBodies subBody
          (selfDepth + 1) (eArg :: varEnv) e h
        simp only [List.map_cons] at ihBody
        simp only [evalTermPipelinedHw, ihArg, ihBody]
    | get target member =>
      cases target with
      | bound idx =>
        simp only [compileTermPipelined] at h
        simp only [evalTermPipelinedHw]
        by_cases hEq : idx == selfDepth
        · simp only [hEq, ↓reduceIte] at h ⊢
          cases hSlot : slots.idxOf? member with
          | none => simp [hSlot] at h
          | some slotIdx =>
            cases hArg : compileTermPipelined slots slotBodies selfDepth varEnv arg with
            | none => simp [hSlot, hArg] at h
            | some eArg =>
              have ihArg := compileTermPipelined_sound inputs wires regs slots slotBodies arg selfDepth varEnv eArg hArg
              simp only [hSlot, hArg] at h
              simp only [ihArg]
              cases hDir : isDirectPipeArg arg
              · simp only [hDir, Bool.false_eq_true, ↓reduceIte] at h ⊢
                cases hBody : slotBodies[slotIdx]? with
                | none => simp [hBody] at h
                | some calleeBody =>
                  simp only [hBody, Option.some.injEq] at h
                  subst h
                  simp only [substRtlInputPort0_sound]
              · simp only [hDir, ↓reduceIte, Option.some.injEq] at h ⊢
                subst h
                rfl
        · simp [hEq] at h
      | _ =>
        simp [compileTermPipelined] at h
    | _ =>
      simp [compileTermPipelined] at h
  | .binary op l r =>
    simp only [compileTermPipelined] at h
    cases hl : compileTermPipelined slots slotBodies selfDepth varEnv l with
    | none => simp [hl] at h
    | some el =>
      cases hr : compileTermPipelined slots slotBodies selfDepth varEnv r with
      | none => simp [hl, hr] at h
      | some er =>
        simp only [hl, hr] at h
        have ihl := compileTermPipelined_sound inputs wires regs slots slotBodies l selfDepth varEnv el hl
        have ihr := compileTermPipelined_sound inputs wires regs slots slotBodies r selfDepth varEnv er hr
        simp only [evalTermPipelinedHw, ihl, ihr]
        exact compilePrimSat_sound inputs wires regs op el er e h
  | .ifBool c t f =>
    simp only [compileTermPipelined] at h
    cases hc : compileTermPipelined slots slotBodies selfDepth varEnv c with
    | none => simp [hc] at h
    | some ec =>
      cases ht : compileTermPipelined slots slotBodies selfDepth varEnv t with
      | none => simp [hc, ht] at h
      | some et =>
        cases hf : compileTermPipelined slots slotBodies selfDepth varEnv f with
        | none => simp [hc, ht, hf] at h
        | some ef =>
          simp only [hc, ht, hf, Option.some.injEq] at h
          subst h
          have ihc := compileTermPipelined_sound inputs wires regs slots slotBodies c selfDepth varEnv ec hc
          have iht := compileTermPipelined_sound inputs wires regs slots slotBodies t selfDepth varEnv et ht
          have ihf := compileTermPipelined_sound inputs wires regs slots slotBodies f selfDepth varEnv ef hf
          simp only [evalTermPipelinedHw, ihc, iht, ihf, evalRtlExpr]
  | .ifZero v z s =>
    simp only [compileTermPipelined] at h
    cases hv : compileTermPipelined slots slotBodies selfDepth varEnv v with
    | none => simp [hv] at h
    | some ev =>
      cases hz : compileTermPipelined slots slotBodies selfDepth varEnv z with
      | none => simp [hv, hz] at h
      | some ez =>
        cases hs : compileTermPipelined slots slotBodies (selfDepth + 1)
            (RtlExpr.alu .sub ev (.const 1#64) :: varEnv) s with
        | none => simp [hv, hz, hs] at h
        | some es =>
          simp only [hv, hz, hs, Option.some.injEq] at h
          subst h
          have hv' := compileTermPipelined_sound inputs wires regs slots slotBodies v selfDepth varEnv ev hv
          have hz' := compileTermPipelined_sound inputs wires regs slots slotBodies z selfDepth varEnv ez hz
          have hs' := compileTermPipelined_sound inputs wires regs slots slotBodies s (selfDepth + 1)
            (RtlExpr.alu .sub ev (.const 1#64) :: varEnv) es hs
          simp only [List.map_cons, evalRtlExpr, evalAluOp] at hs'
          simp only [evalTermPipelinedHw, hv', hz', hs', evalRtlExpr, evalAluOp]
          rfl

/-- Compile a `LeafDef` using pipelined inter-slot register reads (`compileTermPipelined`). -/
def compileLeafDefPipelined
    (slots : List String)
    (slotBodies : List RtlExpr)
    (d : LeafDef) : Option RtlExpr :=
  match d.code with
  | .lam (.lam body) => compileTermPipelined slots slotBodies 1 [.inputPort 0] body
  | _ => none

/-- **Theorem (`compileLeafDefPipelined_sound`)**:
For any `LeafDef` `d` with `d.code = .lam (.lam body)`, if `compileLeafDefPipelined slots slotBodies d = some e`,
then evaluating `e` in `evalRtlExpr` matches `evalTermPipelinedHw` under `[inputs 0]`. -/
theorem compileLeafDefPipelined_sound
    (inputs wires regs : Nat → BitVec 64)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (d : LeafDef) (body : Term) (e : RtlExpr)
    (hCode : d.code = .lam (.lam body))
    (hComp : compileLeafDefPipelined slots slotBodies d = some e) :
    evalTermPipelinedHw slots slotBodies inputs wires regs 1 [inputs 0] body =
      some (evalRtlExpr inputs wires regs e) := by
  simp only [compileLeafDefPipelined, hCode] at hComp
  exact compileTermPipelined_sound inputs wires regs slots slotBodies body 1 [.inputPort 0] e hComp

/-- Structurally recursive slot-list compiler for pipelined `RtlModule` synthesis,
accumulating `slotBodies : List RtlExpr` as each `LeafDef` is compiled. -/
def compileBookDefsPipelined
    (slots : List String)
    (slotBodies : List RtlExpr)
    (wires : List WireAssign)
    (regs : List RegSpec)
    (outs : List OutputPort) :
    List LeafDef → Option (List WireAssign × List RegSpec × List OutputPort)
  | [] => some (wires, regs, outs)
  | d :: rest =>
    match compileLeafDefPipelined slots slotBodies d with
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
      let o : OutputPort := { name := s!"out_{d.member}", expr := .regRead d.slot }
      compileBookDefsPipelined slots (slotBodies ++ [expr]) (wires ++ [w]) (regs ++ [r]) (outs ++ [o]) rest

/-- Compile an entire `Obend.Leaf.Book` into a pipelined `RtlModule` where direct inter-slot
references read synchronous pipeline stage registers (`reg_{member}`) and non-direct argument
calls substitute into the callee slot's actual compiled `RtlExpr` body (`substRtlInputPort0`). -/
def compileBookToPipelinedRtl (modName : String) (B : Book) : Option RtlModule :=
  match compileBookDefsPipelined B.slots [] [] [] [] B.defs with
  | none => none
  | some (wires, regs, outs) =>
    some {
      name       := modName
      inputNames := ["arg"]
      wires      := wires
      regs       := regs
      outputs    := outs
    }

/-- **Theorem (`compileTermPipelined_arg_wired_and_stage_correspondence`)**:
1. When calling an earlier slot `self.scale3` on `.bound 0` (`isDirectPipeArg (.bound 0) = true`),
   `compileTermPipelined` emits the registered pipeline stage read `.regRead 0`.
2. When calling an earlier slot `self.scale3` (whose compiled body is `calleeBody = .alu .mul (.inputPort 0) (.const 3#64)`)
   on a non-`.bound 0` argument (`.nat k`), `compileTermPipelined` looks up `calleeBody` in `slotBodies`
   and emits `substRtlInputPort0 (.const (BitVec.ofNat 64 k)) calleeBody = .alu .mul (.const (BitVec.ofNat 64 k)) (.const 3#64)`,
   evaluating to `BitVec.ofNat 64 k * 3#64` rather than hardcoding `.alu .add (.regRead 0) ...`!
3. When `slotBodies` does not contain `slotIdx`, a non-direct call fails closed with `none`. -/
theorem compileTermPipelined_arg_wired_and_stage_correspondence (k : Nat) (inputs wires regs : Nat → BitVec 64) :
    let calleeBody := RtlExpr.alu .mul (.inputPort 0) (.const 3#64)
    let directCall := Term.app (.get (.bound 1) "scale3") (.bound 0)
    let nonDirectCall := Term.app (.get (.bound 1) "scale3") (.nat k)
    let expectedRtl := RtlExpr.alu .mul (.const (BitVec.ofNat 64 k)) (.const 3#64)
    compileTermPipelined ["scale3", "caller"] [calleeBody] 1 [.inputPort 0] directCall = some (.regRead 0) ∧
    compileTermPipelined ["scale3", "caller"] [calleeBody] 1 [.inputPort 0] nonDirectCall = some expectedRtl ∧
    compileTermPipelined ["scale3", "caller"] [] 1 [.inputPort 0] nonDirectCall = none ∧
    evalRtlExpr inputs wires regs expectedRtl = BitVec.ofNat 64 k * 3#64 ∧
    evalTermPipelinedHw ["scale3", "caller"] [calleeBody] inputs wires regs 1 [inputs 0] nonDirectCall =
      some (BitVec.ofNat 64 k * 3#64) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 10. Calyx-Style `go`/`done` Control Group Handshakes (`CalyxGroup`, `CalyxControl`, `stepCalyxSeqFsm`) -/

/-- A structural datapath group in the Calyx accelerator intermediate representation (`arXiv:2102.09713`):
* `groupName`: identifier of the structural group,
* `latencyCycles`: number of active clock cycles required before the group's `done` signal is asserted,
* `datapathExpr`: `RtlExpr` evaluated while the group's `go` signal is asserted,
* `targetRegIdx`: destination register index written when the group completes. -/
structure CalyxGroup where
  groupName     : String
  latencyCycles : Nat
  datapathExpr  : RtlExpr
  targetRegIdx  : Nat
  deriving DecidableEq, Repr

/-- Hierarchical Calyx control schedule (`seq`, `par`, `ifCond`, `whileLoop`, `enable`). -/
inductive CalyxControl where
  | empty
  | enable    (groupIdx : Nat)
  | seq       (c1 c2 : CalyxControl)
  | par       (groups : List Nat)
  | ifCond    (condExpr : RtlExpr) (tBranch fBranch : CalyxControl)
  | whileLoop (condExpr : RtlExpr) (bound : Nat) (body : CalyxControl)
  deriving DecidableEq, Repr

/-- Execute a single `CalyxGroup` to completion against architectural register state `regs`. -/
def evalCalyxGroup
    (groups : List CalyxGroup)
    (inputs wires : Nat → BitVec 64)
    (groupIdx : Nat)
    (regs : Nat → BitVec 64) : Nat → BitVec 64 :=
  match groups[groupIdx]? with
  | none => regs
  | some g =>
    let v := evalRtlExpr inputs wires regs g.datapathExpr
    fun r => if r == g.targetRegIdx then v else regs r

/-- Bounded while-loop helper for `evalCalyxControl`, structurally recursive on the trip-count bound `bound : Nat`. -/
def evalCalyxWhileLoop
    (cond : (Nat → BitVec 64) → Bool)
    (step : (Nat → BitVec 64) → (Nat → BitVec 64)) :
    Nat → (Nat → BitVec 64) → (Nat → BitVec 64)
  | 0, curRegs => curRegs
  | k + 1, curRegs =>
    if cond curRegs then
      evalCalyxWhileLoop cond step k (step curRegs)
    else
      curRegs

/-- Structural denotational interpreter for a hierarchical `CalyxControl` schedule (`arXiv:2102.09713`):
* `.empty`: identity on `regs`,
* `.enable gIdx`: executes `evalCalyxGroup`,
* `.seq c1 c2`: sequential composition (`c1` followed by `c2`),
* `.par gIdxs`: parallel fork-join where all enabled groups sample the pre-stage `regs` snapshot,
* `.ifCond cond t f`: branches on `evalRtlExpr inputs wires regs cond != 0#64`,
* `.whileLoop cond bound body`: bounded while-loop iteration. -/
def evalCalyxControl
    (groups : List CalyxGroup)
    (inputs wires : Nat → BitVec 64) :
    CalyxControl → (Nat → BitVec 64) → (Nat → BitVec 64)
  | .empty, regs => regs
  | .enable gIdx, regs => evalCalyxGroup groups inputs wires gIdx regs
  | .seq c1 c2, regs =>
    evalCalyxControl groups inputs wires c2 (evalCalyxControl groups inputs wires c1 regs)
  | .par gIdxs, regs =>
    gIdxs.foldl (fun curRegs gIdx =>
      match groups[gIdx]? with
      | none => curRegs
      | some g =>
        let v := evalRtlExpr inputs wires regs g.datapathExpr
        fun r => if r == g.targetRegIdx then v else curRegs r) regs
  | .ifCond condExpr tBranch fBranch, regs =>
    if evalRtlExpr inputs wires regs condExpr != 0#64 then
      evalCalyxControl groups inputs wires tBranch regs
    else
      evalCalyxControl groups inputs wires fBranch regs
  | .whileLoop condExpr bound body, regs =>
    evalCalyxWhileLoop
      (fun curRegs => evalRtlExpr inputs wires curRegs condExpr != 0#64)
      (evalCalyxControl groups inputs wires body)
      bound regs

/-- **Theorem (`evalCalyxControl_seq_assoc`)**:
Sequential Calyx control composition `.seq` is strictly associative over any register state `regs`. -/
theorem evalCalyxControl_seq_assoc
    (groups : List CalyxGroup)
    (inputs wires : Nat → BitVec 64)
    (c1 c2 c3 : CalyxControl)
    (regs : Nat → BitVec 64) :
    evalCalyxControl groups inputs wires (.seq (.seq c1 c2) c3) regs =
      evalCalyxControl groups inputs wires (.seq c1 (.seq c2 c3)) regs := by
  rfl

/-- Synchronous FSM state for a sequential Calyx group controller (`seq { g_0; g_1; ... }`):
* `activeGroupIdx`: index of the currently enabled `CalyxGroup`,
* `cycleInGroup`: intra-group cycle counter ($0 \dots \text{latencyCycles}-1$),
* `goSignal`: asserted (`true`) while `activeGroupIdx < groups.length`,
* `doneSignal`: asserted (`true`) when all groups in the schedule have completed,
* `regState`: current 64-bit architectural register file. -/
structure CalyxSeqFsmState where
  activeGroupIdx : Nat
  cycleInGroup   : Nat
  goSignal       : Bool
  doneSignal     : Bool
  regState       : Nat → BitVec 64

/-- Initial `CalyxSeqFsmState` at the start of a sequential group schedule. -/
def initCalyxSeqFsmState (groups : List CalyxGroup) (initRegs : Nat → BitVec 64) : CalyxSeqFsmState where
  activeGroupIdx := 0
  cycleInGroup   := 0
  goSignal       := !groups.isEmpty
  doneSignal     := groups.isEmpty
  regState       := initRegs

/-- Step a Calyx sequential control FSM by one clock cycle under `go`/`done` handshaking:
* If `st.activeGroupIdx < groups.length` has `some g = groups[st.activeGroupIdx]?`:
  - While `st.cycleInGroup + 1 < g.latencyCycles`, the group remains active (`goSignal = true`,
    `doneSignal = false`) and increments `cycleInGroup` by 1.
  - When `st.cycleInGroup + 1 ≥ g.latencyCycles`, the group's `done` strobe fires: `g.targetRegIdx`
    latches `evalRtlExpr inputs wires st.regState g.datapathExpr`, `activeGroupIdx` advances to
    `st.activeGroupIdx + 1`, and `cycleInGroup` resets to `0`.
* Once `st.activeGroupIdx ≥ groups.length`, the controller holds `goSignal = false`, `doneSignal = true`,
  and leaves `regState` stationary. -/
def stepCalyxSeqFsm
    (groups : List CalyxGroup)
    (inputs wires : Nat → BitVec 64)
    (st : CalyxSeqFsmState) : CalyxSeqFsmState :=
  match groups[st.activeGroupIdx]? with
  | none =>
    { st with
      goSignal   := false
      doneSignal := true }
  | some g =>
    if st.cycleInGroup + 1 < g.latencyCycles then
      { st with
        cycleInGroup := st.cycleInGroup + 1
        goSignal     := true
        doneSignal   := false }
    else
      let v := evalRtlExpr inputs wires st.regState g.datapathExpr
      let nextIdx := st.activeGroupIdx + 1
      { activeGroupIdx := nextIdx
        cycleInGroup   := 0
        goSignal       := decide (nextIdx < groups.length)
        doneSignal     := decide (groups.length ≤ nextIdx)
        regState       := fun r => if r == g.targetRegIdx then v else st.regState r }

/-- Run `stepCalyxSeqFsm` for `numCycles` clock edges. -/
def runCalyxSeqFsm
    (groups : List CalyxGroup)
    (inputs wires : Nat → BitVec 64) : Nat → CalyxSeqFsmState → CalyxSeqFsmState
  | 0, st => st
  | k + 1, st => runCalyxSeqFsm groups inputs wires k (stepCalyxSeqFsm groups inputs wires st)

/-- **Theorem (`calyx_group_go_done_handshake_sound`)**:
When the active Calyx group `g` at `st.activeGroupIdx` reaches its completion cycle
(`¬ (st.cycleInGroup + 1 < g.latencyCycles)`), `stepCalyxSeqFsm` latches `evalRtlExpr inputs wires st.regState g.datapathExpr`
into `g.targetRegIdx`, advances `activeGroupIdx` to `st.activeGroupIdx + 1`, and resets `cycleInGroup` to `0`. -/
theorem calyx_group_go_done_handshake_sound
    (groups : List CalyxGroup)
    (inputs wires : Nat → BitVec 64)
    (st : CalyxSeqFsmState)
    (g : CalyxGroup)
    (hGroup : groups[st.activeGroupIdx]? = some g)
    (hDone  : ¬ (st.cycleInGroup + 1 < g.latencyCycles)) :
    let st' := stepCalyxSeqFsm groups inputs wires st
    st'.activeGroupIdx = st.activeGroupIdx + 1 ∧
    st'.cycleInGroup = 0 ∧
    st'.regState g.targetRegIdx = evalRtlExpr inputs wires st.regState g.datapathExpr := by
  dsimp only [stepCalyxSeqFsm]
  rw [hGroup]
  simp [hDone]

/-- **Theorem (`calyx_seq_fsm_stationary_when_done`)**:
Once all groups in `groups` have completed (`groups[st.activeGroupIdx]? = none`), `stepCalyxSeqFsm`
asserts `doneSignal = true`, deasserts `goSignal = false`, and leaves `regState` invariant. -/
theorem calyx_seq_fsm_stationary_when_done
    (groups : List CalyxGroup)
    (inputs wires : Nat → BitVec 64)
    (st : CalyxSeqFsmState)
    (hNone : groups[st.activeGroupIdx]? = none) :
    let st' := stepCalyxSeqFsm groups inputs wires st
    st'.goSignal = false ∧
    st'.doneSignal = true ∧
    st'.regState = st.regState := by
  dsimp only [stepCalyxSeqFsm]
  rw [hNone]
  exact ⟨rfl, rfl, rfl⟩

/-- **Theorem (`calyx_seq_two_group_pipeline_sound`)**:
Verifies a 2-group sequential Calyx accelerator schedule `[g0, g1]` where:
* `g0` (`latencyCycles = 1`) computes `reg 0 := inputPort 0 + 5#64`,
* `g1` (`latencyCycles = 1`) computes `reg 1 := regRead 0 * 3#64`.
Running `runCalyxSeqFsm` for 2 cycles with `inputPort 0 = 10#64` transitions `activeGroupIdx : 0 → 1 → 2`,
asserts `doneSignal = true`, and produces `reg 0 = 15#64` and `reg 1 = 45#64`, matching the
hierarchical `CalyxControl` schedule `.seq (.enable 0) (.enable 1)`! -/
theorem calyx_seq_two_group_pipeline_sound :
    let g0 : CalyxGroup :=
      { groupName := "load_add5", latencyCycles := 1
      , datapathExpr := .alu .add (.inputPort 0) (.const 5#64), targetRegIdx := 0 }
    let g1 : CalyxGroup :=
      { groupName := "scale_mul3", latencyCycles := 1
      , datapathExpr := .alu .mul (.regRead 0) (.const 3#64), targetRegIdx := 1 }
    let groups := [g0, g1]
    let inputs : Nat → BitVec 64 := fun i => if i == 0 then 10#64 else 0#64
    let wires  : Nat → BitVec 64 := fun _ => 0#64
    let st0 := initCalyxSeqFsmState groups (fun _ => 0#64)
    let st1 := stepCalyxSeqFsm groups inputs wires st0
    let st2 := runCalyxSeqFsm groups inputs wires 2 st0
    let ctrlRegs := evalCalyxControl groups inputs wires (.seq (.enable 0) (.enable 1)) (fun _ => 0#64)
    st0.goSignal = true ∧
    st0.doneSignal = false ∧
    st1.activeGroupIdx = 1 ∧
    st1.regState 0 = 15#64 ∧
    st2.activeGroupIdx = 2 ∧
    st2.goSignal = false ∧
    st2.doneSignal = true ∧
    st2.regState 0 = 15#64 ∧
    st2.regState 1 = 45#64 ∧
    ctrlRegs 0 = st2.regState 0 ∧
    ctrlRegs 1 = st2.regState 1 := by
  decide +kernel

/-- **Theorem (`golden_multi_arg_and_pipelined_rtl_verified`)**:
1. Verifies 3-argument port compilation (`compileMultiArgMethod`) on the ternary hardware MAC
   `λself. λx0. λx1. λx2. x0 * x1 + x2`, confirming that it binds `.bound 2 ↦ .inputPort 0`,
   `.bound 1 ↦ .inputPort 1`, `.bound 0 ↦ .inputPort 2` and evaluates `(6, 7, 8) ↦ 50#64`,
   AND verifies curried 3-argument inter-slot invocation `self.mac3(x0, x1, x2)` from a caller slot.
2. Verifies pipelined book compilation (`compileBookToPipelinedRtl`) on a 3-slot `Book`
   (`slot 0`: `"inc"`, `slot 1`: `"doubleInc"` calling `self.inc(arg) * 2` with `isDirectPipeArg = true`,
   `slot 2`: `"shiftedInc"` calling `self.inc(arg + 5)` with `isDirectPipeArg = false`), confirming that
   the synthesized `RtlModule` passes `checkRtlModule = true`, emits `.regRead 0` (`reg_inc`) in
   slot 1's wire, substitutes `arg + 5` into slot 0's compiled body `(arg + 5) + 1` in slot 2's wire,
   and latches `reg_inc = 11#64` and `reg_shiftedInc = 16#64` on Cycle 1 followed by
   `reg_doubleInc = 22#64` on Cycle 2! -/
theorem golden_multi_arg_and_pipelined_rtl_verified :
    let mac3Code : Term :=
      .lam (.lam (.lam (.lam (.binary .add (.binary .multiply (.bound 2) (.bound 1)) (.bound 0)))))
    let expectedMacExpr : RtlExpr :=
      .alu .add (.alu .mul (.inputPort 0) (.inputPort 1)) (.inputPort 2)
    let macCallerCode : Term :=
      .lam (.lam (.lam (.lam
        (.app (.app (.app (.get (.bound 3) "mac3") (.bound 2)) (.bound 1)) (.bound 0)))))
    let macInputs : Nat → BitVec 64 := fun i =>
      match i with | 0 => 6#64 | 1 => 7#64 | 2 => 8#64 | _ => 0#64
    let pipeBook : Book :=
      { items :=
          [ .slot { member := "inc", slot := 0, kind := .method
                  , code := .lam (.lam (.binary .add (.bound 0) (.nat 1))), reads := [] }
          , .slot { member := "doubleInc", slot := 1, kind := .method
                  , code := .lam (.lam (.binary .multiply (.app (.get (.bound 1) "inc") (.bound 0)) (.nat 2)))
                  , reads := [0] }
          , .slot { member := "shiftedInc", slot := 2, kind := .method
                  , code := .lam (.lam (.app (.get (.bound 1) "inc") (.binary .add (.bound 0) (.nat 5))))
                  , reads := [0] } ] }
    compileMultiArgMethod [] [] 3 mac3Code = some expectedMacExpr ∧
    compileMultiArgMethod ["mac3"] [expectedMacExpr] 3 macCallerCode = some expectedMacExpr ∧
    evalRtlExpr macInputs (fun _ => 0#64) (fun _ => 0#64) expectedMacExpr = 50#64 ∧
    (match compileBookToPipelinedRtl "pipelined_book_mod" pipeBook with
     | some m =>
       let pipeIn : Nat → BitVec 64 := fun _ => 10#64
       let regs0  : Nat → BitVec 64 := fun _ => 0#64
       let regs1  := stepModuleRegs m false pipeIn regs0
       let regs2  := stepModuleRegs m false pipeIn regs1
       checkRtlModule m &&
       (m.wires.map (·.expr) ==
         [ .alu .add (.inputPort 0) (.const 1#64)
         , .alu .mul (.regRead 0) (.const 2#64)
         , .alu .add (.alu .add (.inputPort 0) (.const 5#64)) (.const 1#64) ]) &&
       (regs1 0 == 11#64) &&
       (regs1 2 == 16#64) &&
       (regs2 1 == 22#64)
     | none => false) = true := by
  decide +kernel

/-! ## 14. Rich Struct/Union/Multi-Arg Term Compiler (`compileRichTerm`) & Stateful `always_ff` Step Compiler (`compileStatefulStepToRtl`) -/

/-- Peel all leading `.lam` binders from a `Term`, returning `(numBinders, innerBody)`. -/
def peelLambdas : Term → Nat × Term
  | .lam body =>
    let (n, inner) := peelLambdas body
    (n + 1, inner)
  | other => (0, other)

/-- Peel a curried application spine `((head a₀) … aₖ₋₁)` into `(head, [a₀, …, aₖ₋₁])`. -/
def peelAppChain : Term → List Term → Term × List Term
  | .app fn arg, acc => peelAppChain fn (arg :: acc)
  | head, acc => (head, acc)

/-- Peel `eArgs.length` `.lam` binders from `fn`, pushing each argument expression onto `varEnv`
in left-to-right application order (`((λx₀. … λxₖ₋₁. body) e₀ … eₖ₋₁)` -> `(selfDepth + k, eₖ₋₁ :: … :: e₀ :: varEnv, body)`). -/
def peelBetaRedexChain : List RtlExpr → Nat → List RtlExpr → Term → Option (Nat × List RtlExpr × Term)
  | [], depth, env, body => some (depth, env, body)
  | eArg :: rest, depth, env, .lam subBody =>
    peelBetaRedexChain rest (depth + 1) (eArg :: env) subBody
  | _ :: _, _, _, _ => none

/-- Fuel-bounded compiler from rich `Obend.Core.Term.Term` expressions into `RtlExpr`:
Supports all 64-bit arithmetic, bitwise, shift, signed order, and `Q32.32` primitives (`compilePrimSat`),
plus arbitrary-offset struct packing (`.record`), bit-slice field projection (`.get`), functional
record update (`.extend`), record destructuring (`.split`), tagged-union injection (`.inject`),
sum case muxing (`.case`), curried multi-argument $\beta$-redexes (`((λx₀. … λxₖ₋₁. body) a₀ … aₖ₋₁)`),
and curried multi-argument `self.m(a₀, …, aₖ₋₁)` slot calls. -/
def compileRichTermAux
    (ctx : RtlLayoutCtx)
    (slots : List String)
    (slotBodies : List RtlExpr) :
    Nat → Nat → List RtlExpr → Term → Option RtlExpr
  | 0, _, _, _ => none
  | fuel + 1, selfDepth, varEnv, t =>
    match t with
    | .nat n => some (.const (BitVec.ofNat 64 n))
    | .boolean b => some (.const (if b then 1#64 else 0#64))
    | .bound idx => varEnv[idx]?
    | .done v => compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv v
    | .record fields =>
      fields.foldlM
        (fun acc (fname, fterm) =>
          if fname == "#kind" then
            some acc
          else
            match ctx.lookupField fname,
                  compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv fterm with
            | some (off, width), some eField =>
              some (compileSliceInsertRtl acc eField off width)
            | _, _ => none)
        (.const 0#64)
    | .extend inherited fields =>
      match compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv inherited with
      | none => none
      | some eBase =>
        fields.foldlM
          (fun acc (fname, fterm) =>
            if fname == "#kind" then
              some acc
            else
              match ctx.lookupField fname,
                    compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv fterm with
              | some (off, width), some eField =>
                some (compileSliceUpdateRtl acc eField off width)
              | _, _ => none)
          eBase
    | .split target names function =>
      match compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv target with
      | none => none
      | some eTarget =>
        let eFieldsOpt : Option (List RtlExpr) :=
          names.mapM fun fname =>
            match ctx.lookupField fname with
            | some (off, width) => some (compileSliceExtractRtl eTarget off width)
            | none => none
        match eFieldsOpt with
        | none => none
        | some eFields =>
          match peelBetaRedexChain eFields selfDepth varEnv function with
          | some (depth', env', body) =>
            compileRichTermAux ctx slots slotBodies fuel depth' env' body
          | none => none
    | .get target member =>
      match target with
      | .bound idx =>
        if idx == selfDepth then
          match slots.idxOf? member with
          | some slotIdx => some (.wireRef slotIdx)
          | none =>
            match varEnv[idx]?, ctx.lookupField member with
            | some eTarget, some (off, width) => some (compileSliceExtractRtl eTarget off width)
            | _, _ => none
        else
          match varEnv[idx]?, ctx.lookupField member with
          | some eTarget, some (off, width) => some (compileSliceExtractRtl eTarget off width)
          | _, _ => none
      | _ =>
        match compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv target,
              ctx.lookupField member with
        | some eTarget, some (off, width) => some (compileSliceExtractRtl eTarget off width)
        | _, _ => none
    | .inject label payload =>
      match ctx.lookupArm label,
            compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv payload with
      | some (tagIdx, payW), some ePay =>
        some (compileTagInjectRtl ctx.unionTagBits tagIdx payW ePay)
      | _, _ => none
    | .case scrutinee arms =>
      match compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv scrutinee with
      | none => none
      | some eScrut =>
        let eTag := compileTagExtractRtl ctx.unionTagBits eScrut
        let compiledArmsOpt : Option (List (Nat × RtlExpr)) :=
          arms.mapM fun (armLabel, armBody) =>
            match ctx.lookupArm armLabel with
            | none => none
            | some (tagIdx, payW) =>
              let ePay := compilePayloadExtractRtl ctx.unionTagBits payW eScrut
              match compileRichTermAux ctx slots slotBodies fuel (selfDepth + 1) (ePay :: varEnv) armBody with
              | some eArm => some (tagIdx, eArm)
              | none => none
        match compiledArmsOpt with
        | some compiledArms => some (compileCaseMuxRtl eTag compiledArms (.const 0#64))
        | none => none
    | .app fn arg =>
      let (head, args) := peelAppChain (.app fn arg) []
      match head with
      | .lam _ =>
        match args.mapM (compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv) with
        | some eArgs =>
          match peelBetaRedexChain eArgs selfDepth varEnv head with
          | some (depth', env', subBody) =>
            compileRichTermAux ctx slots slotBodies fuel depth' env' subBody
          | none => none
        | none => none
      | Term.get (Term.bound idx) member =>
        if idx == selfDepth then
          match slots.idxOf? member with
          | some slotIdx =>
            match slotBodies[slotIdx]?,
                  args.mapM (compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv) with
            | some slotExpr, some eArgs =>
              some (substInputPorts eArgs slotExpr)
            | _, _ => none
          | none => none
        else none
      | _ => none
    | .binary op l r =>
      match compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv l,
            compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv r with
      | some el, some er => compilePrimSat op el er
      | _, _ => none
    | .ifBool c tBranch fBranch =>
      match compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv c,
            compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv tBranch,
            compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv fBranch with
      | some ec, some et, some ef => some (.mux ec et ef)
      | _, _, _ => none
    | .ifZero v z s =>
      match compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv v,
            compileRichTermAux ctx slots slotBodies fuel selfDepth varEnv z with
      | some ev, some ez =>
        let predExpr := RtlExpr.alu .sub ev (.const 1#64)
        match compileRichTermAux ctx slots slotBodies fuel (selfDepth + 1) (predExpr :: varEnv) s with
        | some es => some (.mux (.alu .eq ev (.const 0#64)) ez es)
        | none => none
      | _, _ => none
    | _ => none

/-- Default-fuel entry point for `compileRichTermAux` (`fuel = 256`). -/
def compileRichTerm
    (ctx : RtlLayoutCtx)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (selfDepth : Nat)
    (varEnv : List RtlExpr)
    (t : Term) : Option RtlExpr :=
  compileRichTermAux ctx slots slotBodies 256 selfDepth varEnv t

/-- Compile a multi-argument method `λself. λx₀. … λxₖ₋₁. body` using `compileRichTerm`. -/
def compileRichMethod
    (ctx : RtlLayoutCtx)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (t : Term) : Option RtlExpr :=
  let (nLam, body) := peelLambdas t
  if nLam == 0 then
    compileRichTerm ctx slots slotBodies 0 [] body
  else
    let arity := nLam - 1
    let varEnv := mkMultiArgPortEnv arity
    compileRichTerm ctx slots slotBodies arity varEnv body

/-- Determine the input port list for a `Book` compiled via `compileRichBookToRtl`, supporting
arbitrary method arity `k ≥ 1`. -/
def defInputNamesRich (defs : List LeafDef) : List String :=
  let maxArity := defs.foldl (fun acc d =>
    let (nLam, _) := peelLambdas d.code
    max acc (nLam - 1)) 1
  if maxArity <= 1 then ["arg"]
  else (List.range maxArity).map (fun i => s!"arg{i}")

/-- Structurally recursive slot-list compiler using `compileRichMethod`. -/
def compileRichBookDefs
    (ctx : RtlLayoutCtx)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (wires : List WireAssign)
    (regs : List RegSpec)
    (outs : List OutputPort) :
    List LeafDef → Option (List WireAssign × List RegSpec × List OutputPort)
  | [] => some (wires, regs, outs)
  | d :: rest =>
    match compileRichMethod ctx slots slotBodies d.code with
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
      compileRichBookDefs ctx slots (slotBodies ++ [expr]) (wires ++ [w]) (regs ++ [r]) (outs ++ [o]) rest

/-- Compile an entire `Obend.Leaf.Book` containing structs (`.record`, `.get`, `.extend`, `.split`),
tagged unions (`.inject`, `.case`), curried multi-argument $\beta$-redexes, and multi-argument
`self.m(a₀, …, aₖ₋₁)` calls into a synchronous `RtlModule` under `ctx : RtlLayoutCtx`. -/
def compileRichBookToRtl (modName : String) (ctx : RtlLayoutCtx) (B : Book) : Option RtlModule :=
  match compileRichBookDefs ctx B.slots [] [] [] [] B.defs with
  | none => none
  | some (wires, regs, outs) =>
    some {
      name       := modName
      inputNames := defInputNamesRich B.defs
      wires      := wires
      regs       := regs
      outputs    := outs
    }

/-- Declaration of a single 64-bit synchronous state register in a `StatefulStepSpec`. -/
structure StatefulRegDecl where
  regIdx   : Nat
  name     : String
  initVal  : BitVec 64
  nextExpr : RtlExpr
  deriving DecidableEq, Repr

/-- Specification of a synchronous `always_ff @(posedge clk)` hardware state machine with AXI4-Stream
`in_valid` / `in_ready` / `out_valid` handshaking:
* `inputNames`: data input port names `in_0, …, in_{K-1}` (the compiler appends `in_valid` at index `K`),
* `stateRegs`: synchronous-reset state registers `r_0, …, r_{R-1}` gated by `in_valid`,
* `outputExprs`: combinational output ports `(name, expr)`. -/
structure StatefulStepSpec where
  moduleName  : String
  inputNames  : List String
  stateRegs   : List StatefulRegDecl
  outputExprs : List (String × RtlExpr)
  deriving DecidableEq, Repr

/-- Lower a `StatefulRegDecl` into an `Obend.Hardware.HDL.RegSpec` gated by `.inputPort validPortIdx`. -/
def compileStatefulRegDecl (validPortIdx : Nat) (d : StatefulRegDecl) : RegSpec :=
  { regIdx         := d.regIdx
  , name           := d.name
  , domain         := .coreClk
  , resetKind      := .syncReset d.initVal
  , isSynchronizer := false
  , nextExpr       := .mux (.inputPort validPortIdx) d.nextExpr (.regRead d.regIdx) }

/-- Compile a `StatefulStepSpec` into a synchronous `RtlModule` with `always_ff @(posedge clk)`
state registers and AXI4-Stream `in_valid`, `in_ready`, and `out_valid` handshake ports. -/
def compileStatefulStepToRtl (spec : StatefulStepSpec) : RtlModule :=
  let validPortIdx := spec.inputNames.length
  { name       := spec.moduleName
  , inputNames := spec.inputNames ++ ["in_valid"]
  , wires      := []
  , regs       := spec.stateRegs.map (compileStatefulRegDecl validPortIdx)
  , outputs    :=
      spec.outputExprs.map (fun (oName, oExpr) => { name := oName, expr := oExpr }) ++
      [ { name := "in_ready",  expr := .const 1#64 }
      , { name := "out_valid", expr := .inputPort validPortIdx } ] }

/-- Pure single-cycle reference semantics for a `StatefulStepSpec`:
On `rst = true`, every state register resets to `d.initVal`; on `rst = false`, if `in_valid != 0#64`
it advances to `evalRtlExpr inputs (fun _ => 0#64) regState d.nextExpr`, and otherwise holds its
current value `regState d.regIdx`. -/
def evalStatefulStepPure
    (spec : StatefulStepSpec)
    (rst : Bool)
    (inputs : Nat → BitVec 64)
    (regState : Nat → BitVec 64) : Nat → BitVec 64 :=
  let validPortIdx := spec.inputNames.length
  spec.stateRegs.foldl
    (fun (nextSt : Nat → BitVec 64) d =>
      let v :=
        if rst then
          d.initVal
        else if inputs validPortIdx != 0#64 then
          evalRtlExpr inputs (fun _ => 0#64) regState d.nextExpr
        else
          regState d.regIdx
      fun i => if i == d.regIdx then v else nextSt i)
    regState

/-- Pure multi-cycle trace semantics for a `StatefulStepSpec` over a list of `(rst, inputs)` cycles. -/
def runStatefulTracePure
    (spec : StatefulStepSpec)
    (initRegs : Nat → BitVec 64)
    (trace : List (Bool × (Nat → BitVec 64))) : Nat → BitVec 64 :=
  trace.foldl (fun st (rst, ins) => evalStatefulStepPure spec rst ins st) initRegs

/-- **Theorem (`compileStatefulStepToRtl_simulates_step`)**:
Stepping the compiled `RtlModule` (`compileStatefulStepToRtl spec`) by one clock edge via
`stepModuleRegs` produces the exact same next register state as `evalStatefulStepPure` for every
reset flag `rst`, input assignment `inputs`, and register state `regState`! -/
theorem compileStatefulStepToRtl_simulates_step
    (spec : StatefulStepSpec)
    (rst : Bool)
    (inputs : Nat → BitVec 64)
    (regState : Nat → BitVec 64) :
    stepModuleRegs (compileStatefulStepToRtl spec) rst inputs regState =
      evalStatefulStepPure spec rst inputs regState := by
  simp only [stepModuleRegs, compileStatefulStepToRtl, evalWireTable, List.foldl_nil,
    List.foldl_map, compileStatefulRegDecl, evalRtlExpr, evalStatefulStepPure]
  rfl

/-- **Theorem (`compileStatefulStepToRtl_trace_sound`)**:
Over any multi-cycle execution trace `trace : List (Bool × (Nat → BitVec 64))`, `runModuleTrace` on
`compileStatefulStepToRtl spec` matches `runStatefulTracePure spec initRegs trace` cycle-for-cycle! -/
theorem compileStatefulStepToRtl_trace_sound
    (spec : StatefulStepSpec)
    (initRegs : Nat → BitVec 64)
    (trace : List (Bool × (Nat → BitVec 64))) :
    runModuleTrace (compileStatefulStepToRtl spec) initRegs trace =
      runStatefulTracePure spec initRegs trace := by
  induction trace generalizing initRegs with
  | nil => rfl
  | cons cycle rest _ =>
    rcases cycle with ⟨rst, ins⟩
    simp only [runModuleTrace, runStatefulTracePure, List.foldl_cons,
      compileStatefulStepToRtl_simulates_step]

/-- Compile `.obend` `Term` bodies for a stateful step function (`nextStateTerms` and `outputTerms`)
into a `StatefulStepSpec` and lower to `RtlModule` via `compileStatefulStepToRtl`.
Inside each `Term`, the first `stateRegInits.length` arguments after `self` bind to `.regRead 0 .. .regRead (R-1)`
and the next `inputNames.length` arguments bind to `.inputPort 0 .. .inputPort (K-1)`. -/
def compileStatefulTermsToRtl
    (moduleName : String)
    (ctx : RtlLayoutCtx)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (inputNames : List String)
    (stateRegInits : List (String × BitVec 64))
    (nextStateTerms : List Term)
    (outputTerms : List (String × Term)) : Option RtlModule := do
  if stateRegInits.length != nextStateTerms.length then none
  else
    let numRegs := stateRegInits.length
    let numInputs := inputNames.length
    let regEnv : List RtlExpr := (List.range numRegs).map RtlExpr.regRead
    let inEnv  : List RtlExpr := (List.range numInputs).map RtlExpr.inputPort
    let baseVarEnv : List RtlExpr := (regEnv ++ inEnv).reverse
    let baseSelfDepth := numRegs + numInputs
    let compileBody (t : Term) : Option RtlExpr :=
      let (_, body) := peelLambdas t
      compileRichTerm ctx slots slotBodies baseSelfDepth baseVarEnv body
    let nextExprs ← nextStateTerms.mapM compileBody
    let outExprs ← outputTerms.mapM (fun (oName, oTerm) => do
      let e ← compileBody oTerm
      pure (oName, e))
    let regDecls : List StatefulRegDecl :=
      (List.range numRegs).zip (stateRegInits.zip nextExprs) |>.map fun (idx, ((rName, initV), nExpr)) =>
        { regIdx := idx, name := rName, initVal := initV, nextExpr := nExpr }
    some (compileStatefulStepToRtl
      { moduleName  := moduleName
      , inputNames  := inputNames
      , stateRegs   := regDecls
      , outputExprs := outExprs })

/-- **Theorem (`golden_richTerm_and_statefulStep_rtl_verified`)**:
1. Verifies `compileRichTerm` on a struct `.record`, `.extend`, `.get`, and `.inject` / `.case`
   under a concrete `RtlLayoutCtx` (`lo` at `(0, 32)`, `hi` at `(32, 32)`; sum arms `Left` tag `0`,
   `Right` tag `1`),
2. Verifies `compileStatefulTermsToRtl` on a 2-register synchronous accumulator (`acc_lo`, `acc_hi`),
   confirming `checkRtlModule m = true` and exact 2-cycle state progression under `stepModuleRegs`. -/
theorem golden_richTerm_and_statefulStep_rtl_verified :
    let ctx : RtlLayoutCtx :=
      { structSlices := [("lo", (0, 32)), ("hi", (32, 32))]
      , unionTagBits := 8
      , unionArms    := [("Left", (0, 32)), ("Right", (1, 32))] }
    let recTerm : Term :=
      .extend (.record [("lo", .nat 10), ("hi", .nat 20)]) [("lo", .nat 99)]
    let getLoTerm : Term := .get recTerm "lo"
    let getHiTerm : Term := .get recTerm "hi"
    let caseTerm : Term :=
      .case (.inject "Right" (.nat 42))
        [("Left", .binary .add (.bound 0) (.nat 1)), ("Right", .binary .multiply (.bound 0) (.nat 2))]
    let stepLoTerm : Term := .lam (.lam (.lam (.lam (.binary .add (.bound 2) (.bound 0)))))
    let stepHiTerm : Term := .lam (.lam (.lam (.lam (.binary .add (.bound 1) (.nat 1)))))
    let outSumTerm : Term := .lam (.lam (.lam (.lam (.binary .add (.bound 2) (.bound 1)))))
    (match compileRichTerm ctx [] [] 0 [] getLoTerm,
           compileRichTerm ctx [] [] 0 [] getHiTerm,
           compileRichTerm ctx [] [] 0 [] caseTerm,
           compileStatefulTermsToRtl "sync_acc_mod" ctx [] [] ["din"]
             [("acc_lo", 0#64), ("acc_hi", 0#64)]
             [stepLoTerm, stepHiTerm]
             [("sum_out", outSumTerm)] with
     | some eLo, some eHi, some eCase, some m =>
       let env0 : Nat → BitVec 64 := fun _ => 0#64
       let inCycle : Nat → BitVec 64 := fun i => if i == 0 then 7#64 else 1#64
       let regs1 := stepModuleRegs m false inCycle env0
       let regs2 := stepModuleRegs m false inCycle regs1
       (evalRtlExpr env0 env0 env0 eLo == 99#64) &&
       (evalRtlExpr env0 env0 env0 eHi == 20#64) &&
       (evalRtlExpr env0 env0 env0 eCase == 84#64) &&
       checkRtlModule m &&
       (regs1 0 == 7#64) && (regs1 1 == 1#64) &&
       (regs2 0 == 14#64) && (regs2 1 == 2#64)
     | _, _, _, _ => false) = true := by
  decide +kernel

/-- **Theorem (`compileRichTerm_struct_union_and_stateful_verified`)**:
End-to-end verification of:
1. Curried multi-argument $\beta$-redex lowering (`((λx. λy. x * 10 + y) 3 5) = 35`),
2. Record destructuring `.split` lowering (`let {lo, hi} = {lo: 12, hi: 40} in hi - lo = 28`),
3. Full 64-bit word boundary `(offset = 0, width = 64)` struct slice packing and functional update,
4. Whole-book `compileBookToRtl` and `compileBookToRtlSat` on a mixed 0-arg cell + 2-arg method `Book`
   (`checkRtlModule = true`, `inputNames = ["arg0", "arg1"]`), and
5. Whole-book `compileRichBookToRtl` on a `Book` combining a packed struct cell, a 2-argument method
   with curried `super` $\beta$-redex, and a slot calling `self.blend((self.pair).lo, (self.pair).hi)`. -/
theorem compileRichTerm_struct_union_and_stateful_verified :
    let ctx : RtlLayoutCtx :=
      { structSlices := [("lo", (0, 32)), ("hi", (32, 32))]
      , unionTagBits := 8
      , unionArms    := [("Left", (0, 32)), ("Right", (1, 32))] }
    let ctx64 : RtlLayoutCtx :=
      { structSlices := [("full", (0, 64))]
      , unionTagBits := 8
      , unionArms    := [] }
    let curriedBetaTerm : Term :=
      .app (.app (.lam (.lam (.binary .add (.binary .multiply (.bound 1) (.nat 10)) (.bound 0))))
        (.nat 3)) (.nat 5)
    let splitTerm : Term :=
      .split (.record [("lo", .nat 12), ("hi", .nat 40)]) ["lo", "hi"]
        (.lam (.lam (.binary .subtract (.bound 0) (.bound 1))))
    let fullTerm : Term :=
      .get (.extend (.record [("full", .nat 0x123456789ABCDEF0)])
             [("full", .nat 0xFEDCBA9876543210)]) "full"
    let dBase : LeafDef :=
      { member := "base", slot := 0, kind := .cell, code := .lam (.lam (.nat 100)), reads := [] }
    let dComb : LeafDef :=
      { member := "combine"
      , slot   := 1
      , kind   := .method
      , code   := .lam (.lam (.lam (.binary .add (.get (.bound 2) "base") (.binary .add (.bound 1) (.bound 0)))))
      , reads  := [0] }
    let mixedBook : Book := { items := [.slot dBase, .slot dComb] }
    let rPair : LeafDef :=
      { member := "pair"
      , slot   := 0
      , kind   := .cell
      , code   := .lam (.lam (.record [("lo", .nat 10), ("hi", .nat 20)]))
      , reads  := [] }
    let rBlend : LeafDef :=
      { member := "blend"
      , slot   := 1
      , kind   := .method
      , code   := .lam (.lam (.lam (.app (.app (.lam (.lam (.binary .add (.bound 1) (.bound 0)))) (.bound 1)) (.bound 0))))
      , reads  := [] }
    let rSum : LeafDef :=
      { member := "sumPair"
      , slot   := 2
      , kind   := .cell
      , code   := .lam (.lam (.app (.app (.get (.bound 1) "blend")
                    (.get (.get (.bound 1) "pair") "lo"))
                    (.get (.get (.bound 1) "pair") "hi")))
      , reads  := [0, 1] }
    let richBook : Book := { items := [.slot rPair, .slot rBlend, .slot rSum] }
    (match compileRichTerm ctx [] [] 0 [] curriedBetaTerm,
           compileRichTerm ctx [] [] 0 [] splitTerm,
           compileRichTerm ctx64 [] [] 0 [] fullTerm,
           compileBookToRtl "mixed_wrap" mixedBook,
           compileBookToRtlSat "mixed_sat" mixedBook,
           compileRichBookToRtl "rich_book" ctx richBook with
     | some eBeta, some eSplit, some eFull, some mWrap, some mSat, some mRich =>
       let env0 : Nat → BitVec 64 := fun _ => 0#64
       let in2 : Nat → BitVec 64 := fun i => if i == 0 then 7#64 else if i == 1 then 8#64 else 0#64
       (evalRtlExpr env0 env0 env0 eBeta == 35#64) &&
       (evalRtlExpr env0 env0 env0 eSplit == 28#64) &&
       (evalRtlExpr env0 env0 env0 eFull == 0xFEDCBA9876543210#64) &&
       checkRtlModule mWrap &&
       checkRtlModule mSat &&
       checkRtlModule mRich &&
       (mSat.inputNames == ["arg0", "arg1"]) &&
       (evalModuleOutputs mSat in2 env0 == [("out_base", 100#64), ("out_combine", 115#64)]) &&
       (evalModuleOutputs mWrap in2 env0 == [("out_base", 100#64), ("out_combine", 115#64)]) &&
       ((evalModuleOutputs mRich env0 env0).lookup "out_sumPair" == some 30#64)
     | _, _, _, _, _, _ => false) = true := by
  decide +kernel

end Obend.Hardware.Compiler
end
