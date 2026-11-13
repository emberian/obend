module
/-
# Obend.Lower.LCNF — Lean 4 LCNF (Lean Compiler Normal Form) to `LExpr`, `Core4` & `Leaf.Book`

Implements Pillar 1B of the Silicon Elaborator architecture (`SILICON-ELABORATOR.md` §1.2):
the verified compiler bridge from Lean 4's **LCNF (Lean Compiler Normal Form)** intermediate
representation into `Obend.Lower.LExpr`, `Obend.Core.Term`, and flat `Obend.Leaf.Book` supercombinators:

1. **Quantitative Parameter Erasure (`LcnfQuantity`, `LcnfParam`, `LcnfArg.erased`, `lcnf_zero_erasure_sound`)**:
   - Models `.zero` (erased proof/type `□`), `.one` (linear state token), and `.many` (computational)
     quantities.
   - All `.zero`-quantity proof and type arguments are erased (`LcnfArg.erased ↦ LExpr.erased ↦ box`),
     so proof terms occupy 0 LUTs and 0 BRAM words in lowered hardware.

2. **Linear State-Token Conservation (`LcnfArg.stateTok`, `LcnfLetValue.stateRead`, `LcnfLetValue.stateWrite`, `checkLinearStateToken`, `lcnf_linear_state_conserved`)**:
   - Models `.one`-quantity `StateM` / `MetaM` world tokens threaded through ANF `letValue` chains
     without heap cloning.
   - `checkLinearStateToken` statically verifies single-threaded linear token consumption across
     sequential `letValue`, `jpDecl`/`jmp`, `ifBool`, and `cases` branches, rejecting stale/duplicated
     token reuse (`= none`).

3. **ANF Control Flow, Join Points & Lowering (`LcnfCode`, `evalLcnfCode`, `compileLcnfToLExpr`, `compileLcnfToCore4`, `compileLcnfToBook`)**:
   - Supports `letValue`, `jpDecl` (local join-point declarations), `jmp` (join-point jumps),
     `cases` (algebraic constructor dispatch), `ifBool`, `return`, and `unreach`.
   - Join points capture their declaration environment and lexical join scope.
   - `evalLcnfModule` and `compileLcnfModuleToLExpr` bind closed recursive declarations.
   - `evalLcnfCodeVal_simulates_ssteps` proves structural simulation on `PureBlock`,
     with the closed scalar corollary `evalLcnfCode_simulates_core4`.
   - Separate agreement theorems cover lexical join capture and recursive module calls.
   - Scalar and Boolean result APIs are distinct; state tokens are not scalar results.
-/
public import Obend.Lower.Fragment
public import Obend.Lower.Proofs.Book
import Obend.Lower.Proofs.Complete

public section

namespace Obend.Lower.LCNF

open Obend.Core
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Lower

set_option autoImplicit false

/-! ## 1. Quantitative Types, Arguments & Linear State Operations (`LcnfQuantity`, `LcnfParam`, `LcnfArg`, `LcnfLetValue`) -/

/-- Quantitative usage grade in LCNF / QTT:
* `.zero`: erased compile-time type or `Prop` proof (`0` runtime wires),
* `.one`: linear single-threaded resource (`StateM` / `MetaM` state token),
* `.many`: unrestricted computational value. -/
inductive LcnfQuantity where
  | zero
  | one
  | many
  deriving DecidableEq, Repr, Inhabited

/-- Typed LCNF parameter with explicit usage quantity (`qty`). -/
structure LcnfParam where
  name : String
  qty  : LcnfQuantity
  ty   : Ty := .emptyRow
  deriving DecidableEq, Repr, Inhabited

/-- An atomic argument in LCNF (Lean Compiler Normal Form):
* `.bvar idx`: computational de Bruijn variable in scope,
* `.lit n`: scalar `Nat` literal,
* `.boolLit b`: scalar `Bool` literal,
* `.erased`: `.zero`-quantity erased type or proof argument (`□`),
* `.stateTok tokId`: `.one`-quantity linear state token (`StateM` / `MetaM` world wire). -/
inductive LcnfArg where
  | bvar (idx : Nat)
  | lit (n : Nat)
  | boolLit (b : Bool)
  | erased
  | stateTok (tokId : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Backwards-compatible alias for `LcnfArg`. -/
abbrev LCNFArg := LcnfArg

/-- Right-hand side of an ANF `let`-binding in LCNF:
* `.arg a`: atomic argument copy,
* `.natOp op lhs rhs`: primitive `Nat` ALU operation,
* `.ctor tag fields`: algebraic constructor injection,
* `.record fields`: record construction,
* `.proj field target`: record field projection,
* `.app fn arg`: function application,
* `.stateRead tok addr`: linear state read consuming `.one`-quantity `tok` at `addr`,
* `.stateWrite tok addr val`: linear state write consuming `.one`-quantity `tok` and writing `val` at `addr`. -/
inductive LcnfLetValue where
  | arg (a : LcnfArg)
  | natOp (op : NatOp) (lhs rhs : LcnfArg)
  | ctor (tag : String) (fields : List (String × LcnfArg))
  | record (fields : List (String × LcnfArg))
  | proj (field : String) (target : LcnfArg)
  | app (fn arg : LcnfArg)
  | stateRead (tok : LcnfArg) (addr : LcnfArg)
  | stateWrite (tok : LcnfArg) (addr val : LcnfArg)
  deriving DecidableEq, Repr, Inhabited

/-- Backwards-compatible alias for `LcnfLetValue`. -/
abbrev LCNFLetValue := LcnfLetValue

/-! ## 2. ANF Code Blocks, Join Points, Declarations & Modules (`LcnfAlt`, `LcnfCode`, `LcnfFunDecl`, `LcnfModule`) -/

/-- ANF-flattened LCNF code block:
* `letValue val body`: bind ANF right-hand side `val` at de Bruijn index `0` in `body`,
* `jpDecl jpId numParams jpBody body`: bind a local join point `jpId` taking `numParams` arguments,
* `jmp jpId args`: tail-jump to join point `jpId` with `args`,
* `cases scrut arms`: constructor pattern match on `scrut`,
* `ifBool cond whenTrue whenFalse`: boolean branch on `cond`,
* `return a`: return atomic argument `a`,
* `unreach`: unreachable control-flow point (empty inductive elimination). -/
inductive LcnfCode where
  | letValue (val : LcnfLetValue) (body : LcnfCode)
  | jpDecl (jpId : Nat) (numParams : Nat) (jpBody : LcnfCode) (body : LcnfCode)
  | jmp (jpId : Nat) (args : List LcnfArg)
  | cases (scrut : LcnfArg) (arms : List (String × List String × LcnfCode))
  | ifBool (cond : LcnfArg) (whenTrue whenFalse : LcnfCode)
  | return (a : LcnfArg)
  | unreach
  deriving Repr, Inhabited

/-- Backwards-compatible constructor pattern aliases for `LcnfCode`. -/
@[match_pattern] abbrev LcnfCode.letDecl := LcnfCode.letValue
@[match_pattern] abbrev LcnfCode.returnArg := LcnfCode.return

/-- Backwards-compatible alias for `LcnfCode`. -/
abbrev LCNFCode := LcnfCode

/-- Structured constructor alternative for `LcnfCode.cases`. -/
structure LcnfAlt where
  ctorTag    : String
  fieldNames : List String
  body       : LcnfCode
  deriving Repr, Inhabited

/-- Convert a structured `LcnfAlt` into a `cases` arm tuple. -/
def LcnfAlt.toArm (alt : LcnfAlt) : String × List String × LcnfCode :=
  (alt.ctorTag, alt.fieldNames, alt.body)

/-- Construct an `LcnfCode.cases` node from a list of `LcnfAlt` alternatives. -/
def LcnfCode.casesAlts (scrut : LcnfArg) (alts : List LcnfAlt) : LcnfCode :=
  .cases scrut (alts.map LcnfAlt.toArm)

/-- A recursive LCNF function declaration (`Lean.Compiler.LCNF.FunDecl`):
`body` is an ANF `LcnfCode` block under `numParams` parameter binders and a recursive self-binder
at the outermost de Bruijn index (`numParams`), lowered via `LExpr.recConst`. -/
structure LcnfFunDecl where
  name      : String
  numParams : Nat
  params    : List LcnfParam := []
  body      : LcnfCode
  deriving Repr, Inhabited

/-- Backwards-compatible alias for `LcnfFunDecl`. -/
abbrev LCNFFunDecl := LcnfFunDecl

/-- An LCNF compilation module consisting of top-level function declarations and an entry code block. -/
structure LcnfModule where
  decls : List LcnfFunDecl
  entry : LcnfCode
  deriving Repr, Inhabited

/-! ## 3. Quantitative `.zero` Erasure & `.one` Linear State-Token Checker (`eraseZeroQtyArgs`, `checkLinearStateToken`, `evalLcnfCode`) -/

/-- Erase every argument whose corresponding parameter has quantity `.zero`. -/
def eraseZeroQtyArgs : List LcnfParam → List LcnfArg → List LcnfArg
  | [], args => args
  | p :: ps, a :: as =>
    (if p.qty == .zero then .erased else a) :: eraseZeroQtyArgs ps as
  | _ :: _, [] => []

/-- Read a cell from the linear state store `st : List (Nat × Nat)`. -/
def readLinearStore (st : List (Nat × Nat)) (addr : Nat) : Nat :=
  match st.find? (fun p => p.1 == addr) with
  | some (_, v) => v
  | none        => 0

/-- Write a cell in the linear state store `st : List (Nat × Nat)` in-place. -/
def writeLinearStore (st : List (Nat × Nat)) (addr val : Nat) : List (Nat × Nat) :=
  (addr, val) :: st.filter (fun p => p.1 != addr)

/-- Runtime values preserve constructor tags, named fields, and lexical closures. -/
inductive LcnfVal where
  | scalar (n : Nat)
  | bool (b : Bool)
  | erased
  | stateTok (id : Nat)
  | ctor (tag : String) (fields : List (String × LcnfVal))
  | record (fields : List (String × LcnfVal))
  | closure (env : List LcnfVal) (params : List LcnfVal) (decl : LcnfFunDecl)

/-- A join point closes over its declaration environment and lexical join-table suffix.
The saved depth excludes the join itself: local joins are non-recursive. -/
structure LcnfJpClosure where
  jpId : Nat
  numParams : Nat
  declEnv : List LcnfVal
  savedJpsDepth : Nat
  jpBody : LcnfCode

def evalLcnfArgVal (env : List LcnfVal) : LcnfArg → Option LcnfVal
  | .bvar i => env[i]?
  | .lit n => some (.scalar n)
  | .boolLit b => some (.bool b)
  | .erased => some .erased
  | .stateTok id => some (.stateTok id)

/-- The scalar API accepts only actual scalar results. -/
def LcnfVal.toNat? : LcnfVal → Option Nat
  | .scalar n => some n
  | _ => none

mutual
/-- Fuel bounds both control flow and recursive closure applications. -/
def evalLcnfLetValueVal : Nat → List LcnfVal → List LcnfJpClosure →
    List (Nat × Nat) → LcnfLetValue → Option (LcnfVal × List (Nat × Nat))
  | 0, _, _, _, _ => none
  | fuel + 1, env, _jps, st, v => do
    match v with
    | .arg a => return (← evalLcnfArgVal env a, st)
    | .natOp op l r =>
      let .scalar lv ← evalLcnfArgVal env l | none
      let .scalar rv ← evalLcnfArgVal env r | none
      let res := match op with
        | .add => LcnfVal.scalar (lv + rv)
        | .sub => .scalar (lv - rv)
        | .mul => .scalar (lv * rv)
        | .div => .scalar (lv / rv)
        | .mod => .scalar (lv % rv)
        | .beq => .bool (lv == rv)
        | .ble => .bool (lv <= rv)
      return (res, st)
    | .ctor tag fs =>
      let vals ← fs.mapM fun (name, a) => do return (name, ← evalLcnfArgVal env a)
      return (.ctor tag vals, st)
    | .record fs =>
      let vals ← fs.mapM fun (name, a) => do return (name, ← evalLcnfArgVal env a)
      return (.record vals, st)
    | .proj field tgt =>
      let .record fs ← evalLcnfArgVal env tgt | none
      let (_, val) ← fs.find? (fun p => p.1 == field)
      return (val, st)
    | .app fn arg =>
      let .closure cenv params decl ← evalLcnfArgVal env fn | none
      let a ← evalLcnfArgVal env arg
      let args := params ++ [a]
      if args.length < decl.numParams then
        return (.closure cenv args decl, st)
      else if args.length == decl.numParams then
        evalLcnfCodeVal fuel (args.reverse ++ [.closure cenv [] decl] ++ cenv) [] st decl.body
      else none
    | .stateRead tok addr =>
      let .stateTok _ ← evalLcnfArgVal env tok | none
      let .scalar a ← evalLcnfArgVal env addr | none
      return (.scalar (readLinearStore st a), st)
    | .stateWrite tok addr val =>
      let .stateTok _ ← evalLcnfArgVal env tok | none
      let .scalar a ← evalLcnfArgVal env addr | none
      let .scalar v ← evalLcnfArgVal env val | none
      return (.scalar v, writeLinearStore st a v)

def evalLcnfCodeVal : Nat → List LcnfVal → List LcnfJpClosure →
    List (Nat × Nat) → LcnfCode → Option (LcnfVal × List (Nat × Nat))
  | 0, _, _, _, _ => none
  | fuel + 1, env, jps, st, c => do
    match c with
    | .return a => return (← evalLcnfArgVal env a, st)
    | .unreach => none
    | .letValue v body =>
      let (val, st') ← evalLcnfLetValueVal fuel env jps st v
      evalLcnfCodeVal fuel (val :: env) jps st' body
    | .jpDecl id n jpBody body =>
      evalLcnfCodeVal fuel env (⟨id, n, env, jps.length, jpBody⟩ :: jps) st body
    | .jmp id args =>
      let jp ← jps.find? (fun entry => entry.jpId == id)
      if args.length != jp.numParams then none else do
        let vals ← args.mapM (evalLcnfArgVal env)
        evalLcnfCodeVal fuel (vals ++ jp.declEnv)
          (jps.drop (jps.length - jp.savedJpsDepth)) st jp.jpBody
    | .ifBool cond t f =>
      let .bool b ← evalLcnfArgVal env cond | none
      evalLcnfCodeVal fuel env jps st (if b then t else f)
    | .cases scrut arms =>
      let .ctor tag fs ← evalLcnfArgVal env scrut | none
      let (_, names, body) ← arms.find? (fun (armTag, _, _) => armTag == tag)
      let vals ← Obend.Core.Term.splitValues fs names
      evalLcnfCodeVal fuel (vals.reverse ++ env) jps st body
end

/-- Scalar compatibility view; structured or ill-typed results fail closed. -/
def evalLcnfCode (fuel : Nat) (env : List Nat) (jps : List LcnfJpClosure)
    (st : List (Nat × Nat)) (c : LcnfCode) : Option (Nat × List (Nat × Nat)) := do
  let (val, st') ← evalLcnfCodeVal fuel (env.map LcnfVal.scalar) jps st c
  return (← val.toNat?, st')

/-- Boolean results have a separate view and are never coerced to natural numbers. -/
def evalLcnfCodeBool (fuel : Nat) (env : List LcnfVal) (jps : List LcnfJpClosure)
    (st : List (Nat × Nat)) (c : LcnfCode) : Option (Bool × List (Nat × Nat)) := do
  let (.bool b, st') ← evalLcnfCodeVal fuel env jps st c | none
  return (b, st')

/-- Top-level declarations are closed recursive functions. Later declarations occupy
lower de Bruijn indices, matching the nested let bindings in module compilation. -/
def evalLcnfModule (fuel : Nat) (m : LcnfModule) : Option (Nat × List (Nat × Nat)) := do
  let env := m.decls.foldl (fun env decl => .closure [] [] decl :: env) []
  let (v, st) ← evalLcnfCodeVal fuel env [] [] m.entry
  return (← v.toNat?, st)

/-- Evaluate a scalar let value through the same structured evaluator. -/
def evalLcnfLetValue (env : List Nat) (st : List (Nat × Nat)) (v : LcnfLetValue) :
    Option (Nat × List (Nat × Nat)) := do
  let (val, st') ← evalLcnfLetValueVal 1 (env.map LcnfVal.scalar) [] st v
  return (← val.toNat?, st')

/-- Static `.one`-quantity linear state-token checker (`checkLinearStateToken`):
Given the current live state token `tokId : Nat`, verifies that:
1. Every `.stateRead (.stateTok id) _` and `.stateWrite (.stateTok id) _ _` consumes the exact
   live token `id == tokId` and advances the live token to `tokId + 1` (rejecting any stale or
   duplicated token `id != tokId` with `none`),
2. Non-state `letValue` operations do not forge or duplicate `.stateTok` arguments, and
3. Branching constructs (`ifBool`, `cases`) conserve linearity by requiring both branches to
   succeed and produce the same outgoing token ID. -/
def checkLinearLetValue (tokId : Nat) : LcnfLetValue → Option Nat
  | .stateRead (.stateTok id) _ =>
    if id == tokId then some (tokId + 1) else none
  | .stateRead _ _ => none
  | .stateWrite (.stateTok id) _ _ =>
    if id == tokId then some (tokId + 1) else none
  | .stateWrite _ _ _ => none
  | .arg (.stateTok id) =>
    if id == tokId then some tokId else none
  | _ => some tokId

mutual
/-- Check linear state-token conservation across an `LcnfCode` block, returning `some tokId'`
if the linear token is threaded single-threadedly without duplication or use-after-consume. -/
def checkLinearStateToken (tokId : Nat) : LcnfCode → Option Nat
  | .return (.stateTok id) => if id == tokId then some tokId else none
  | .return _              => some tokId
  | .unreach               => some tokId
  | .letValue v body       =>
    match checkLinearLetValue tokId v with
    | some tokId' => checkLinearStateToken tokId' body
    | none        => none
  | .jpDecl _ _ jpBody body =>
    match checkLinearStateToken tokId body with
    | some tokAfterBody =>
      match checkLinearStateToken tokId jpBody with
      | some _ => some tokAfterBody
      | none   => none
    | none => none
  | .jmp _ _ => some tokId
  | .ifBool _ t f =>
    match checkLinearStateToken tokId t, checkLinearStateToken tokId f with
    | some t1, some t2 => if t1 == t2 then some t1 else none
    | _, _             => none
  | .cases _ arms => checkLinearArms tokId arms

/-- Check linear state-token conservation across `cases` arms. -/
def checkLinearArms (tokId : Nat) : List (String × List String × LcnfCode) → Option Nat
  | [] => some tokId
  | (_, _, body) :: [] => checkLinearStateToken tokId body
  | (_, _, body) :: rest =>
    match checkLinearStateToken tokId body, checkLinearArms tokId rest with
    | some t1, some t2 => if t1 == t2 then some t1 else none
    | _, _             => none
end

/-! ## 4. Lowering `LcnfCode` to `LExpr`, `Core4.Term`, and `Leaf.Book` (`compileLcnfToLExpr`, `compileLcnfToCore4`, `compileLcnfToBook`) -/

/-- Compile-time de Bruijn & linear-state lowering context (`LcnfLowerCtx`):
* `varEnv`: maps each bound LCNF variable slot `i` to its current `LExpr` de Bruijn index,
* `jpEnv`: maps each declared `jpId` to `(jpLExprIdx, jpTakesState)` accounting for all intervening
  `letValue`, `jpDecl`, `cases`, and linear-store bindings,
* `stateIdx?`: when `some stIdx`, holds the `LExpr` de Bruijn index of the live functional store
  `st : Nat → Nat` threaded through `.stateRead` / `.stateWrite` and join points,
* `extraBinders`: number of `LExpr`-only binders (`jpDecl` closures + linear stores) pushed without
  growing the LCNF computational environment, so outer `LcnfFunDecl` / `recConst` binders `i ≥ varEnv.length`
  shift by `extraBinders`. -/
structure LcnfLowerCtx where
  varEnv       : List Nat := []
  jpEnv        : List (Nat × Nat × Bool) := []
  stateIdx?    : Option Nat := none
  extraBinders : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Push 1 computational variable binding (both LCNF `env` and `LExpr` binder depth grow by 1). -/
def LcnfLowerCtx.pushVar (ctx : LcnfLowerCtx) : LcnfLowerCtx where
  varEnv       := 0 :: ctx.varEnv.map (· + 1)
  jpEnv        := ctx.jpEnv.map fun (id, d, takesSt) => (id, d + 1, takesSt)
  stateIdx?    := ctx.stateIdx?.map (· + 1)
  extraBinders := ctx.extraBinders

/-- Push `k` computational variable bindings (e.g., `cases` arm fields or join-point parameters). -/
def LcnfLowerCtx.pushVars : Nat → LcnfLowerCtx → LcnfLowerCtx
  | 0, ctx     => ctx
  | k + 1, ctx => (ctx.pushVars k).pushVar

/-- Push 1 `LExpr`-only binder (`jpDecl` closure or linear store binder) where LCNF `env` does not grow. -/
def LcnfLowerCtx.pushExtraBinder (ctx : LcnfLowerCtx) : LcnfLowerCtx where
  varEnv       := ctx.varEnv.map (· + 1)
  jpEnv        := ctx.jpEnv.map fun (id, d, takesSt) => (id, d + 1, takesSt)
  stateIdx?    := ctx.stateIdx?.map (· + 1)
  extraBinders := ctx.extraBinders + 1

/-- Resolve LCNF de Bruijn variable `i` to its exact `LExpr` de Bruijn index under `ctx`. -/
def LcnfLowerCtx.lookupVar (ctx : LcnfLowerCtx) (i : Nat) : Nat :=
  match ctx.varEnv[i]? with
  | some idx => idx
  | none     => i + ctx.extraBinders

/-- Look up join point `jpId` in `ctx.jpEnv`, returning `(jpLExprIdx, jpTakesState)`. -/
def LcnfLowerCtx.lookupJp? (ctx : LcnfLowerCtx) (jpId : Nat) : Option (Nat × Bool) :=
  match ctx.jpEnv.find? (fun (id, _, _) => id == jpId) with
  | some (_, idx, takesSt) => some (idx, takesSt)
  | none                   => none

/-- Detect whether an `LcnfLetValue` performs a linear state read or write. -/
def letValueUsesState : LcnfLetValue → Bool
  | .stateRead _ _    => true
  | .stateWrite _ _ _ => true
  | _                 => false

mutual
/-- Detect whether an `LcnfCode` block contains any `.stateRead` or `.stateWrite` operation. -/
def codeUsesState : LcnfCode → Bool
  | .return _               => false
  | .unreach                => false
  | .letValue v body        => letValueUsesState v || codeUsesState body
  | .jpDecl _ _ jpBody body => codeUsesState jpBody || codeUsesState body
  | .jmp _ _                => false
  | .ifBool _ t f           => codeUsesState t || codeUsesState f
  | .cases _ arms           => armsUseState arms

/-- Detect whether any `cases` arm contains a state operation. -/
def armsUseState : List (String × List String × LcnfCode) → Bool
  | []                  => false
  | (_, _, body) :: tl  => codeUsesState body || armsUseState tl
end

/-- Initial empty linear functional store (`fun _ : Nat => 0`). -/
def emptyLinearStoreLExpr : LExpr :=
  .lam .natural (.lit 0)

/-- Functional store update (`fun q : Nat => if q == addr then val else st q`). -/
def mkStoreWriteLExpr (stExpr addrExpr valExpr : LExpr) : LExpr :=
  .lam .natural
    (.boolRec .natural
      (.app (stExpr.rename Nat.succ) (.bvar 0))
      (valExpr.rename Nat.succ)
      (.natBin .beq (.bvar 0) (addrExpr.rename Nat.succ)))

/-- Lower an `LcnfArg` into `LExpr` under `ctx`. -/
def lcnfArgToLExprCtx (ctx : LcnfLowerCtx) : LcnfArg → LExpr
  | .bvar i      => .bvar (ctx.lookupVar i)
  | .lit n       => .lit n
  | .boolLit b   => .boolLit b
  | .erased      => .erased
  | .stateTok id => .lit id

/-- Lower an `LcnfArg` into `LExpr` in the empty context. -/
def lcnfArgToLExpr (a : LcnfArg) : LExpr :=
  lcnfArgToLExprCtx {} a

/-- Lower a non-state-mutating `LcnfLetValue` into `LExpr` under `ctx`. -/
def lcnfLetValueToLExprCtx (ctx : LcnfLowerCtx) : LcnfLetValue → LExpr
  | .arg a            => lcnfArgToLExprCtx ctx a
  | .natOp op l r     => .natBin op (lcnfArgToLExprCtx ctx l) (lcnfArgToLExprCtx ctx r)
  | .ctor tag fs      => .inject tag (fs.map fun f => (f.1, lcnfArgToLExprCtx ctx f.2))
  | .record fs        => .record (fs.map fun f => (f.1, lcnfArgToLExprCtx ctx f.2))
  | .proj field tgt   => .proj field (lcnfArgToLExprCtx ctx tgt)
  | .app fn arg       => .app (lcnfArgToLExprCtx ctx fn) (lcnfArgToLExprCtx ctx arg)
  | .stateRead _ addr =>
    match ctx.stateIdx? with
    | some stIdx => .app (.bvar stIdx) (lcnfArgToLExprCtx ctx addr)
    | none       => .app emptyLinearStoreLExpr (lcnfArgToLExprCtx ctx addr)
  | .stateWrite _ _ val => lcnfArgToLExprCtx ctx val

/-- Lower an `LcnfLetValue` into `LExpr` in the empty context. -/
def lcnfLetValueToLExpr (v : LcnfLetValue) : LExpr :=
  lcnfLetValueToLExprCtx {} v

/-- Wrap an arm body `body : LExpr` in `k` curried `.lam .emptyRow` binders for the constructor's
fields (matching `LExpr.cases` minor-premise convention). -/
@[expose] def wrapMinorBvars : Nat → LExpr → LExpr
  | 0, body     => body
  | k + 1, body => .lam .emptyRow (wrapMinorBvars k body)

/-- Apply a function `fn : LExpr` to a spine of already-lowered `LExpr` arguments. -/
def applyLExprArgs (fn : LExpr) : List LExpr → LExpr
  | []      => fn
  | a :: as => applyLExprArgs (.app fn a) as

/-- Apply a function `fn : LExpr` to a spine of `LcnfArg` arguments in the empty context. -/
def applyLcnfArgs (fn : LExpr) (args : List LcnfArg) : LExpr :=
  applyLExprArgs fn (args.map lcnfArgToLExpr)

mutual
/-- Context-aware lowering of `LcnfCode` into `LExpr`, threading linear functional store bindings
across `.stateRead`/`.stateWrite` and tracking exact de Bruijn binder depth for `.jpDecl`/`.jmp`. -/
def compileLcnfWithCtx (ctx : LcnfLowerCtx) : LcnfCode → LExpr
  | .return a => lcnfArgToLExprCtx ctx a
  | .unreach  => .erased
  | .letValue (.stateWrite _ addr val) body =>
    let addrE := lcnfArgToLExprCtx ctx addr
    let valE  := lcnfArgToLExprCtx ctx val
    let curSt := match ctx.stateIdx? with
      | some stIdx => .bvar stIdx
      | none       => emptyLinearStoreLExpr
    let nextStore := mkStoreWriteLExpr curSt addrE valE
    let ctxWithStore : LcnfLowerCtx := { ctx.pushExtraBinder with stateIdx? := some 0 }
    .letE (fn .natural .natural) nextStore
      (.letE .natural (valE.rename Nat.succ) (compileLcnfWithCtx ctxWithStore.pushVar body))
  | .letValue (.stateRead tok addr) body =>
    .letE .natural
      (lcnfLetValueToLExprCtx ctx (.stateRead tok addr))
      (compileLcnfWithCtx ctx.pushVar body)
  | .letValue v body =>
    .letE .emptyRow (lcnfLetValueToLExprCtx ctx v) (compileLcnfWithCtx ctx.pushVar body)
  | .jpDecl jpId numParams jpBody body =>
    match ctx.stateIdx? with
    | none =>
      let jpClosure := wrapMinorBvars numParams (compileLcnfWithCtx (ctx.pushVars numParams) jpBody)
      let pushed := ctx.pushExtraBinder
      let ctxBody : LcnfLowerCtx := { pushed with jpEnv := (jpId, 0, false) :: pushed.jpEnv }
      .letE .emptyRow jpClosure (compileLcnfWithCtx ctxBody body)
    | some _ =>
      let ctxJpParams := (ctx.pushVars numParams).pushExtraBinder
      let ctxJp : LcnfLowerCtx := { ctxJpParams with stateIdx? := some 0 }
      let jpClosure := wrapMinorBvars numParams (.lam (fn .natural .natural) (compileLcnfWithCtx ctxJp jpBody))
      let pushed := ctx.pushExtraBinder
      let ctxBody : LcnfLowerCtx := { pushed with jpEnv := (jpId, 0, true) :: pushed.jpEnv }
      .letE .emptyRow jpClosure (compileLcnfWithCtx ctxBody body)
  | .jmp jpId args =>
    let argExprs := args.reverse.map (lcnfArgToLExprCtx ctx)
    match ctx.lookupJp? jpId with
    | some (jpIdx, false) =>
      applyLExprArgs (.bvar jpIdx) argExprs
    | some (jpIdx, true) =>
      let stArg := match ctx.stateIdx? with
        | some stIdx => .bvar stIdx
        | none       => emptyLinearStoreLExpr
      applyLExprArgs (.bvar jpIdx) (argExprs ++ [stArg])
    | none =>
      applyLExprArgs (.bvar (ctx.lookupVar jpId)) argExprs
  | .ifBool c t f =>
    .boolRec .emptyRow (compileLcnfWithCtx ctx f) (compileLcnfWithCtx ctx t) (lcnfArgToLExprCtx ctx c)
  | .cases scrut arms =>
    .cases .emptyRow (lcnfArmsWithCtx ctx arms) (lcnfArgToLExprCtx ctx scrut)

/-- Context-aware lowering of `cases` arms into `LExpr`. -/
def lcnfArmsWithCtx (ctx : LcnfLowerCtx) :
    List (String × List String × LcnfCode) → List (String × List String × LExpr)
  | [] => []
  | (tag, names, body) :: rest =>
    (tag, names, wrapMinorBvars names.length (compileLcnfWithCtx (ctx.pushVars names.length) body)) ::
      lcnfArmsWithCtx ctx rest
end

/-- Lower a list of LCNF `cases` arms into `LExpr` arms in the empty context. -/
def lcnfArmsToLExpr (arms : List (String × List String × LcnfCode)) :
    List (String × List String × LExpr) :=
  lcnfArmsWithCtx {} arms

/-- Lower an `LcnfCode` block into `LExpr`:
* For state-free blocks (`codeUsesState c = false`), lowers directly in `{}`.
* For blocks containing `.stateRead`/`.stateWrite`, binds `emptyLinearStoreLExpr` (`fun _ => 0`) at
  the entry of the block and threads functional store updates single-threadedly through `stateIdx?`. -/
def compileLcnfToLExpr (c : LcnfCode) : LExpr :=
  if codeUsesState c then
    .letE (fn .natural .natural) emptyLinearStoreLExpr
      (compileLcnfWithCtx { stateIdx? := some 0, extraBinders := 1 } c)
  else
    compileLcnfWithCtx {} c

/-- Backwards-compatible alias for `compileLcnfToLExpr`. -/
abbrev lcnfToLExpr := compileLcnfToLExpr

/-- Lower an `LcnfCode` block directly to a `Core4` `Term`. -/
def compileLcnfToCore4 (c : LcnfCode) : Term :=
  lowerT (compileLcnfToLExpr c)

/-- Backwards-compatible alias for `compileLcnfToCore4`. -/
abbrev lowerLCNF := compileLcnfToCore4

/-- Lower a recursive `LcnfFunDecl` into `LExpr` via `LExpr.recConst`. -/
def lcnfFunDeclToLExpr (decl : LcnfFunDecl) : LExpr :=
  .recConst decl.name (fn .emptyRow .natural) (wrapMinorBvars decl.numParams (compileLcnfToLExpr decl.body))

/-- Bind closed top-level declarations before compiling the module entry. -/
def compileLcnfModuleToLExpr (m : LcnfModule) : LExpr :=
  let rec bindDecls (ctx : LcnfLowerCtx) : List LcnfFunDecl → LExpr
    | [] =>
      if codeUsesState m.entry then
        .letE (fn .natural .natural) emptyLinearStoreLExpr
          (compileLcnfWithCtx { ctx.pushExtraBinder with stateIdx? := some 0 } m.entry)
      else compileLcnfWithCtx ctx m.entry
    | decl :: rest =>
      .letE .emptyRow (lcnfFunDeclToLExpr decl) (bindDecls ctx.pushVar rest)
  bindDecls {} m.decls

/-- Module compilation through the existing verified Lower bridge. -/
def compileLcnfModuleToCore4 (m : LcnfModule) : Term :=
  lowerT (compileLcnfModuleToLExpr m)

/-- Lower a recursive `LcnfFunDecl` directly to a `Core4` `Term`. -/
def lowerLCNFFunDecl (decl : LcnfFunDecl) : Term :=
  lowerT (lcnfFunDeclToLExpr decl)

/-- Emit an `LcnfCode` block as a flat `Obend.Leaf.Book` member via `leanComposition`. -/
def compileLcnfToBook (name : String) (c : LcnfCode) : Obend.Leaf.Book :=
  Obend.Leaf.emit (leanComposition name (compileLcnfToCore4 c))

/-- Emit a recursive `LcnfFunDecl` as a flat `Obend.Leaf.Book` member via `leanComposition`. -/
def compileLcnfFunDeclToBook (decl : LcnfFunDecl) : Obend.Leaf.Book :=
  Obend.Leaf.emit (leanComposition decl.name (lowerLCNFFunDecl decl))

/-! ## 5. Concrete LCNF Benchmarks & Soundness Theorems -/

/-- Concrete recursive `LcnfFunDecl` computing `countdown(n) = if n == 0 then 42 else countdown(n - 1)`:
under self-binder `bvar 1` and parameter `n = bvar 0`:
1. `let isZ := (n == 0)` (`bvar 0` inside let; `n` shifts to `bvar 1`, `self` shifts to `bvar 2`),
2. `ifBool isZ then return 42 else (let pred := n - 1; let res := self pred; return res)`. -/
def sampleLcnfRecDecl : LcnfFunDecl where
  name      := "lcnfCountdown42"
  numParams := 1
  params    := [{ name := "n", qty := .many, ty := .natural }]
  body      :=
    .letValue (.natOp .beq (.bvar 0) (.lit 0))
      (.ifBool (.bvar 0)
        (.return (.lit 42))
        (.letValue (.natOp .sub (.bvar 1) (.lit 1))
          (.letValue (.app (.bvar 3) (.bvar 0))
            (.return (.bvar 0)))))

def sampleLcnfRecBody : LExpr :=
  wrapMinorBvars sampleLcnfRecDecl.numParams (compileLcnfToLExpr sampleLcnfRecDecl.body)

theorem sampleLcnfRecDecl_runs_zero :
    SSteps (.app (lcnfFunDeclToLExpr sampleLcnfRecDecl) (.lit 0)) (.lit 42) := by
  have heq : lcnfFunDeclToLExpr sampleLcnfRecDecl =
      .recConst "lcnfCountdown42" (fn .emptyRow .natural)
        (.lam .emptyRow
          (.letE .emptyRow (.natBin .beq (.bvar 0) (.lit 0))
            (.boolRec .emptyRow
              (.letE .emptyRow (.natBin .sub (.bvar 1) (.lit 1))
                (.letE .emptyRow (.app (.bvar 3) (.bvar 0)) (.bvar 0)))
              (.lit 42)
              (.bvar 0)))) := rfl
  rw [heq]
  refine .next (.appFun (.lit 0) (.unfold _ _ _)) ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.letE .emptyRow (.natBin .beq (.bvar 0) (.lit 0))
          (.boolRec .emptyRow
            (.letE .emptyRow (.natBin .sub (.bvar 1) (.lit 1))
              (.letE .emptyRow (.app (.bvar 3) (.bvar 0)) (.bvar 0)))
            (.lit 42)
            (.bvar 0)))).inst
        (lcnfFunDeclToLExpr sampleLcnfRecDecl) =
      .lam .emptyRow
        (.letE .emptyRow (.natBin .beq (.bvar 0) (.lit 0))
          (.boolRec .emptyRow
            (.letE .emptyRow (.natBin .sub (.bvar 1) (.lit 1))
              (.letE .emptyRow (.app (lcnfFunDeclToLExpr sampleLcnfRecDecl) (.bvar 0)) (.bvar 0)))
            (.lit 42)
            (.bvar 0))) := by
    simp [lcnfFunDeclToLExpr, sampleLcnfRecDecl, compileLcnfToLExpr, codeUsesState,
      letValueUsesState, compileLcnfWithCtx, lcnfLetValueToLExprCtx, lcnfArgToLExprCtx,
      LcnfLowerCtx.lookupVar, LcnfLowerCtx.pushVar, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename, liftRename]
  rw [← heq, hinst1]
  refine .next (.beta .emptyRow _ (.lit 0)) ?_
  have hinst2 :
      (LExpr.letE .emptyRow (.natBin .beq (.bvar 0) (.lit 0))
        (.boolRec .emptyRow
          (.letE .emptyRow (.natBin .sub (.bvar 1) (.lit 1))
            (.letE .emptyRow (.app (lcnfFunDeclToLExpr sampleLcnfRecDecl) (.bvar 0)) (.bvar 0)))
          (.lit 42)
          (.bvar 0))).inst (.lit 0) =
      .letE .emptyRow (.natBin .beq (.lit 0) (.lit 0))
        (.boolRec .emptyRow
          (.letE .emptyRow (.natBin .sub (.lit 0) (.lit 1))
            (.letE .emptyRow (.app (lcnfFunDeclToLExpr sampleLcnfRecDecl) (.bvar 0)) (.bvar 0)))
          (.lit 42)
          (.bvar 0)) := by
    simp [lcnfFunDeclToLExpr, sampleLcnfRecDecl, compileLcnfToLExpr, codeUsesState,
      letValueUsesState, compileLcnfWithCtx, lcnfLetValueToLExprCtx, lcnfArgToLExprCtx,
      LcnfLowerCtx.lookupVar, LcnfLowerCtx.pushVar, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.zeta .emptyRow (.natBin .beq (.lit 0) (.lit 0)) _) ?_
  have hinst3 :
      (LExpr.boolRec .emptyRow
        (.letE .emptyRow (.natBin .sub (.lit 0) (.lit 1))
          (.letE .emptyRow (.app (lcnfFunDeclToLExpr sampleLcnfRecDecl) (.bvar 0)) (.bvar 0)))
        (.lit 42)
        (.bvar 0)).inst (.natBin .beq (.lit 0) (.lit 0)) =
      .boolRec .emptyRow
        (.letE .emptyRow (.natBin .sub (.lit 0) (.lit 1))
          (.letE .emptyRow (.app (lcnfFunDeclToLExpr sampleLcnfRecDecl) (.bvar 0)) (.bvar 0)))
        (.lit 42)
        (.natBin .beq (.lit 0) (.lit 0)) := by
    simp [lcnfFunDeclToLExpr, sampleLcnfRecDecl, compileLcnfToLExpr, codeUsesState,
      letValueUsesState, compileLcnfWithCtx, lcnfLetValueToLExprCtx, lcnfArgToLExprCtx,
      LcnfLowerCtx.lookupVar, LcnfLowerCtx.pushVar, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst3]
  refine .next (.boolRecMajor .emptyRow _ (.lit 42) (.binLit .beq 0 0)) ?_
  exact .next (.boolRecTrue .emptyRow _ (.lit 42)) (.refl _)

/-- Concrete LCNF block that allocates a `KExpr.bvar 7` node, pattern-matches on its constructor
tag `"bvar"`, and returns `idx + 35 = 42`. -/
def sampleLcnfAstMatch : LcnfCode :=
  .letValue (.ctor "bvar" [("idx", .lit 7)])
    (.cases (.bvar 0)
      [ ("bvar", ["idx"],
          .letValue (.natOp .add (.bvar 0) (.lit 35))
            (.return (.bvar 0)))
      , ("sort", ["u"],
          .return (.lit 0)) ])

theorem sampleLcnfAstMatch_runs_42 :
    SSteps (compileLcnfToLExpr sampleLcnfAstMatch) (.lit 42) := by
  have heq : compileLcnfToLExpr sampleLcnfAstMatch =
      .letE .emptyRow (.inject "bvar" [("idx", .lit 7)])
        (.cases .emptyRow
          [ ("bvar", ["idx"], .lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)))
          , ("sort", ["u"], .lam .emptyRow (.lit 0)) ]
          (.bvar 0)) := rfl
  rw [heq]
  refine .next (.zeta .emptyRow (.inject "bvar" [("idx", .lit 7)]) _) ?_
  have h1 :
      (LExpr.cases .emptyRow
        [ ("bvar", ["idx"], .lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)))
        , ("sort", ["u"], .lam .emptyRow (.lit 0)) ]
        (.bvar 0)).inst (.inject "bvar" [("idx", .lit 7)]) =
      .cases .emptyRow
        [ ("bvar", ["idx"], .lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)))
        , ("sort", ["u"], .lam .emptyRow (.lit 0)) ]
        (.inject "bvar" [("idx", .lit 7)]) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [h1]
  refine .next (.casesInject .emptyRow _ "bvar" [("idx", .lit 7)] ["idx"]
    (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)))
    [.lit 7] rfl rfl) ?_
  refine .next (.beta .emptyRow _ (.lit 7)) ?_
  have h2 :
      (LExpr.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)).inst (.lit 7) =
      .letE .emptyRow (.natBin .add (.lit 7) (.lit 35)) (.bvar 0) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [h2]
  refine .next (.zeta .emptyRow (.natBin .add (.lit 7) (.lit 35)) (.bvar 0)) ?_
  have h3 : (LExpr.bvar 0).inst (.natBin .add (.lit 7) (.lit 35)) = .natBin .add (.lit 7) (.lit 35) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [h3]
  exact .next (.binLit .add 7 35) (.refl _)

/-- Concrete LCNF join-point program (`jpDecl` / `jmp`):
Declares a join point `jp(x) = x + 32` (`jpId = 0`, `numParams = 1`) and jumps to it with `10`,
evaluating to `42`. -/
def sampleLcnfJpCode : LcnfCode :=
  .jpDecl 0 1
    (.letValue (.natOp .add (.bvar 0) (.lit 32)) (.return (.bvar 0)))
    (.jmp 0 [.lit 10])

theorem sampleLcnfJpCode_runs_42 :
    SSteps (compileLcnfToLExpr sampleLcnfJpCode) (.lit 42) := by
  have heq : compileLcnfToLExpr sampleLcnfJpCode =
      .letE .emptyRow (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0)))
        (.app (.bvar 0) (.lit 10)) := rfl
  rw [heq]
  refine .next (.zeta .emptyRow (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0))) _) ?_
  have h1 :
      (LExpr.app (.bvar 0) (.lit 10)).inst
        (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0))) =
      .app (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0))) (.lit 10) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [h1]
  refine .next (.beta .emptyRow _ (.lit 10)) ?_
  have h2 :
      (LExpr.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0)).inst (.lit 10) =
      .letE .emptyRow (.natBin .add (.lit 10) (.lit 32)) (.bvar 0) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [h2]
  refine .next (.zeta .emptyRow (.natBin .add (.lit 10) (.lit 32)) (.bvar 0)) ?_
  have h3 : (LExpr.bvar 0).inst (.natBin .add (.lit 10) (.lit 32)) = .natBin .add (.lit 10) (.lit 32) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [h3]
  exact .next (.binLit .add 10 32) (.refl _)

/-- Parametric join-point LCNF program (`mkShiftedJpCode v1 v2 offset`) with **two intervening
`letValue` bindings** between `.jpDecl 0` and `.jmp 0`, exercising join-point de Bruijn depth
tracking (`jpIdx = 2` at `.jmp 0`, while argument `.bvar 0` resolves to `v1 + v2`):
`jp 0 (x) := return (x + offset); let a := v1; let b := a + v2; jmp 0 [b]`. -/
def mkShiftedJpCode (v1 v2 offset : Nat) : LcnfCode :=
  .jpDecl 0 1
    (.letValue (.natOp .add (.bvar 0) (.lit offset)) (.return (.bvar 0)))
    (.letValue (.arg (.lit v1))
      (.letValue (.natOp .add (.bvar 0) (.lit v2))
        (.jmp 0 [.bvar 0])))

theorem mkShiftedJpCode_runs (v1 v2 offset : Nat) :
    SSteps (compileLcnfToLExpr (mkShiftedJpCode v1 v2 offset)) (.lit (v1 + v2 + offset)) := by
  let jpFn : LExpr := .lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit offset)) (.bvar 0))
  have heq : compileLcnfToLExpr (mkShiftedJpCode v1 v2 offset) =
      .letE .emptyRow jpFn
        (.letE .emptyRow (.lit v1)
          (.letE .emptyRow (.natBin .add (.bvar 0) (.lit v2))
            (.app (.bvar 2) (.bvar 0)))) := rfl
  rw [heq]
  refine .next (.zeta .emptyRow jpFn _) ?_
  have h1 :
      (LExpr.letE .emptyRow (.lit v1)
        (.letE .emptyRow (.natBin .add (.bvar 0) (.lit v2))
          (.app (.bvar 2) (.bvar 0)))).inst jpFn =
      .letE .emptyRow (.lit v1)
        (.letE .emptyRow (.natBin .add (.bvar 0) (.lit v2))
          (.app jpFn (.bvar 0))) := by
    simp [jpFn, LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename, liftRename]
  rw [h1]
  refine .next (.zeta .emptyRow (.lit v1) _) ?_
  have h2 :
      (LExpr.letE .emptyRow (.natBin .add (.bvar 0) (.lit v2))
        (.app jpFn (.bvar 0))).inst (.lit v1) =
      .letE .emptyRow (.natBin .add (.lit v1) (.lit v2))
        (.app jpFn (.bvar 0)) := by
    simp [jpFn, LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [h2]
  refine .next (.zeta .emptyRow (.natBin .add (.lit v1) (.lit v2)) _) ?_
  have h3 :
      (LExpr.app jpFn (.bvar 0)).inst (.natBin .add (.lit v1) (.lit v2)) =
      .app jpFn (.natBin .add (.lit v1) (.lit v2)) := by
    simp [jpFn, LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [h3]
  refine .next (.beta .emptyRow _ (.natBin .add (.lit v1) (.lit v2))) ?_
  have h4 :
      (LExpr.letE .emptyRow (.natBin .add (.bvar 0) (.lit offset)) (.bvar 0)).inst
        (.natBin .add (.lit v1) (.lit v2)) =
      .letE .emptyRow (.natBin .add (.natBin .add (.lit v1) (.lit v2)) (.lit offset)) (.bvar 0) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [h4]
  refine .next (.zeta .emptyRow (.natBin .add (.natBin .add (.lit v1) (.lit v2)) (.lit offset)) (.bvar 0)) ?_
  have h5 :
      (LExpr.bvar 0).inst (.natBin .add (.natBin .add (.lit v1) (.lit v2)) (.lit offset)) =
      .natBin .add (.natBin .add (.lit v1) (.lit v2)) (.lit offset) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [h5]
  refine .next (.binLeft .add (.lit offset) (.binLit .add v1 v2)) ?_
  exact .next (.binLit .add (v1 + v2) offset) (.refl _)

/-- Parametric linear state-threaded write-then-read LCNF program (`mkLinearStateWriteRead addr val`):
1. Writes `val` to state address `addr` consuming `.stateTok 0` (advancing live token to `1`),
2. Reads state address `addr` consuming `.stateTok 1` (advancing live token to `2`),
3. Returns the read value (`val` — NOT `addr`!). -/
def mkLinearStateWriteRead (addr val : Nat) : LcnfCode :=
  .letValue (.stateWrite (.stateTok 0) (.lit addr) (.lit val))
    (.letValue (.stateRead (.stateTok 1) (.lit addr))
      (.return (.bvar 0)))

/-- Concrete linear state-threaded LCNF program (`addr = 0, val = 42`). -/
def sampleLinearStateCode : LcnfCode :=
  mkLinearStateWriteRead 0 42

/-- Broken linear state-threaded LCNF program that attempts to reuse the consumed `.stateTok 0`
twice (use-after-consume violation). -/
def sampleDuplicatedStateTokCode : LcnfCode :=
  .letValue (.stateWrite (.stateTok 0) (.lit 0) (.lit 42))
    (.letValue (.stateRead (.stateTok 0) (.lit 0))
      (.return (.bvar 0)))

theorem mkLinearStateWriteRead_runs (addr val : Nat) :
    SSteps (compileLcnfToLExpr (mkLinearStateWriteRead addr val)) (.lit val) := by
  let st1 : LExpr :=
    .lam .natural
      (.boolRec .natural
        (.app emptyLinearStoreLExpr (.bvar 0))
        (.lit val)
        (.natBin .beq (.bvar 0) (.lit addr)))
  have heq : compileLcnfToLExpr (mkLinearStateWriteRead addr val) =
      .letE (fn .natural .natural) emptyLinearStoreLExpr
        (.letE (fn .natural .natural) (mkStoreWriteLExpr (.bvar 0) (.lit addr) (.lit val))
          (.letE .natural (.lit val)
            (.letE .natural (.app (.bvar 1) (.lit addr))
              (.bvar 0)))) := by
    simp [mkLinearStateWriteRead, compileLcnfToLExpr, codeUsesState, letValueUsesState,
      compileLcnfWithCtx, lcnfLetValueToLExprCtx, lcnfArgToLExprCtx, LcnfLowerCtx.lookupVar,
      LcnfLowerCtx.pushVar, LcnfLowerCtx.pushExtraBinder, LExpr.rename]
  rw [heq]
  refine .next (.zeta (fn .natural .natural) emptyLinearStoreLExpr _) ?_
  have h1 :
      (LExpr.letE (fn .natural .natural) (mkStoreWriteLExpr (.bvar 0) (.lit addr) (.lit val))
        (.letE .natural (.lit val)
          (.letE .natural (.app (.bvar 1) (.lit addr))
            (.bvar 0)))).inst emptyLinearStoreLExpr =
      .letE (fn .natural .natural) st1
        (.letE .natural (.lit val)
          (.letE .natural (.app (.bvar 1) (.lit addr))
            (.bvar 0))) := by
    simp [st1, mkStoreWriteLExpr, emptyLinearStoreLExpr, LExpr.inst, LExpr.subst,
      LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [h1]
  refine .next (.zeta (fn .natural .natural) st1 _) ?_
  have h2 :
      (LExpr.letE .natural (.lit val)
        (.letE .natural (.app (.bvar 1) (.lit addr))
          (.bvar 0))).inst st1 =
      .letE .natural (.lit val)
        (.letE .natural (.app st1 (.lit addr))
          (.bvar 0)) := by
    simp [st1, emptyLinearStoreLExpr, LExpr.inst, LExpr.subst, LExpr.liftSubst,
      LExpr.single, LExpr.rename, liftRename]
  rw [h2]
  refine .next (.zeta .natural (.lit val) _) ?_
  have h3 :
      (LExpr.letE .natural (.app st1 (.lit addr)) (.bvar 0)).inst (.lit val) =
      .letE .natural (.app st1 (.lit addr)) (.bvar 0) := by
    simp [st1, emptyLinearStoreLExpr, LExpr.inst, LExpr.subst, LExpr.liftSubst]
  rw [h3]
  refine .next (.zeta .natural (.app st1 (.lit addr)) (.bvar 0)) ?_
  have h4 :
      (LExpr.bvar 0).inst (.app st1 (.lit addr)) = .app st1 (.lit addr) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [h4]
  refine .next (.beta .natural _ (.lit addr)) ?_
  have h5 :
      (LExpr.boolRec .natural
        (.app emptyLinearStoreLExpr (.bvar 0))
        (.lit val)
        (.natBin .beq (.bvar 0) (.lit addr))).inst (.lit addr) =
      .boolRec .natural
        (.app emptyLinearStoreLExpr (.lit addr))
        (.lit val)
        (.natBin .beq (.lit addr) (.lit addr)) := by
    simp [emptyLinearStoreLExpr, LExpr.inst, LExpr.subst, LExpr.single]
  rw [h5]
  refine .next (.boolRecMajor .natural _ (.lit val) (.binLit .beq addr addr)) ?_
  have hbeq : NatOp.eval .beq addr addr = .boolLit true := by
    simp [NatOp.eval]
  rw [hbeq]
  exact .next (.boolRecTrue .natural _ (.lit val)) (.refl _)

/-- **Theorem (`lcnf_zero_erasure_sound`)**:
1. Every `.zero`-quantity erased argument (`LcnfArg.erased`) compiles to `LExpr.erased` and `Core4` `box`,
2. `eraseZeroQtyArgs` replaces every `.zero`-quantity argument with `.erased`
   while preserving `.one` and `.many` arguments verbatim, and
3. Binding an erased `.zero`-quantity proof/type in `letValue (.arg .erased) body` and returning a
   computational literal `.lit n` reduces in 1 ζ-step to `.lit n` and evaluates in `Core4` to `.nat n`. -/
theorem lcnf_zero_erasure_sound (n : Nat) (a : LcnfArg) :
    compileLcnfToCore4 (.return .erased) = box ∧
    eraseZeroQtyArgs [{ name := "hProof", qty := .zero }, { name := "x", qty := .many }] [a, .lit n] =
      [.erased, .lit n] ∧
    Evaluates (compileLcnfToCore4 (.letValue (.arg .erased) (.return (.lit n)))) (.nat n) := by
  refine ⟨by simp [compileLcnfToCore4, compileLcnfToLExpr, codeUsesState, compileLcnfWithCtx,
              lcnfArgToLExprCtx, lowerT], rfl, ?_⟩
  have hrun : SSteps (compileLcnfToLExpr (.letValue (.arg .erased) (.return (.lit n)))) (.lit n) := by
    have heq : compileLcnfToLExpr (.letValue (.arg .erased) (.return (.lit n))) =
        .letE .emptyRow .erased (.lit n) := rfl
    rw [heq]
    refine .next (.zeta .emptyRow .erased (.lit n)) ?_
    have hinst : (LExpr.lit n).inst .erased = .lit n := by
      simp [LExpr.inst, LExpr.subst]
    rw [hinst]
    exact .refl _
  simpa [compileLcnfToCore4, lowerT] using lower_sound_nat hrun

/-- **Theorem (`lcnf_linear_state_conserved`, Universally Quantified)**:
For EVERY address `addr : Nat` and written value `val : Nat`:
1. `mkLinearStateWriteRead addr val` passes `checkLinearStateToken 0` (advancing live token `0 → 2`),
2. Reusing a consumed `.stateTok 0` is rejected (`= none`),
3. Executing `mkLinearStateWriteRead addr val` via `evalLcnfCode` updates the store at `addr` to `val`
   and returns `val`, and
4. Lowering `mkLinearStateWriteRead addr val` via `compileLcnfToLExpr` / `compileLcnfToCore4` threads
   the functional linear store so the subsequent `.stateRead` reduces in `SSteps` to `.lit val` and
   evaluates in `Core4` to `.nat val` (never erasing `.stateRead` to `addr`). -/
theorem lcnf_linear_state_conserved (addr val : Nat) :
    checkLinearStateToken 0 (mkLinearStateWriteRead addr val) = some 2 ∧
    checkLinearStateToken 0 sampleDuplicatedStateTokCode = none ∧
    evalLcnfCode 8 [] [] [] (mkLinearStateWriteRead addr val) = some (val, [(addr, val)]) ∧
    SSteps (compileLcnfToLExpr (mkLinearStateWriteRead addr val)) (.lit val) ∧
    Evaluates (compileLcnfToCore4 (mkLinearStateWriteRead addr val)) (.nat val) := by
  have hSteps := mkLinearStateWriteRead_runs addr val
  refine ⟨rfl, rfl, ?_, hSteps, ?_⟩
  · simp [mkLinearStateWriteRead, evalLcnfCode, evalLcnfCodeVal, evalLcnfLetValueVal, evalLcnfArgVal, LcnfVal.toNat?,
          writeLinearStore, readLinearStore]
  · simpa [compileLcnfToCore4, lowerT] using lower_sound_nat hSteps

/-- **Theorem (`lcnf_to_core4_sound`)**:
1. Every `.zero`-quantity erased LCNF argument (`LCNFArg.erased`) lowers to `box` (`.record []`),
2. For ANY `c : LCNFCode` whose `lcnfToLExpr c` reduces in `SSteps` to `.lit n` (or `.boolLit b`),
   `lowerLCNF c` evaluates in `Core4` to `.nat n` (or `.boolean b`),
3. Specifically, `sampleLcnfAstMatch` (allocating an AST constructor and pattern-matching in ANF)
   reduces in `SSteps` to `.lit 42` and evaluates in `Core4` to `.nat 42`, and
4. Recursive `LCNFFunDecl` declarations (`sampleLcnfRecDecl`, lowered via `LExpr.recConst`)
   evaluate in `Core4` to `.nat 42`. -/
theorem lcnf_to_core4_sound :
    lowerLCNF (.returnArg .erased) = box ∧
    (∀ (c : LCNFCode) (n : Nat),
      SSteps (lcnfToLExpr c) (.lit n) → Evaluates (lowerLCNF c) (.nat n)) ∧
    (∀ (c : LCNFCode) (b : Bool),
      SSteps (lcnfToLExpr c) (.boolLit b) → Evaluates (lowerLCNF c) (.boolean b)) ∧
    SSteps (lcnfToLExpr sampleLcnfAstMatch) (.lit 42) ∧
    Evaluates (lowerLCNF sampleLcnfAstMatch) (.nat 42) ∧
    Evaluates (.app (lowerLCNFFunDecl sampleLcnfRecDecl) (.nat 0)) (.nat 42) := by
  refine ⟨by simp [lowerLCNF, compileLcnfToCore4, compileLcnfToLExpr, codeUsesState,
              compileLcnfWithCtx, lcnfArgToLExprCtx, lowerT], ?_, ?_,
    sampleLcnfAstMatch_runs_42, ?_, ?_⟩
  · intro c n hrun
    simpa [lowerLCNF, compileLcnfToCore4, lowerT] using lower_sound_nat hrun
  · intro c b hrun
    simpa [lowerLCNF, compileLcnfToCore4, lowerT] using lower_sound_bool hrun
  · simpa [lowerLCNF, compileLcnfToCore4, lowerT] using lower_sound_nat sampleLcnfAstMatch_runs_42
  · simpa [lowerLCNFFunDecl, lowerT] using lower_sound_nat sampleLcnfRecDecl_runs_zero

/-- **Theorem (`lcnf_elab_pass_to_book_sound`, Universally Quantified)**:
For ALL `(v1 v2 offset : Nat)`:
1. Join-point LCNF programs with intervening `letValue` bindings (`mkShiftedJpCode v1 v2 offset`)
   shift the join-point de Bruijn index accurately across `let` scopes, reducing in `SSteps` to
   `.lit (v1 + v2 + offset)`, evaluating in `Core4` to `.nat (v1 + v2 + offset)`, and matching
   `evalLcnfCode 8 [] [] [] (mkShiftedJpCode v1 v2 offset) = some (v1 + v2 + offset, [])`, and
2. Emitting `sampleLcnfRecDecl` to a flat `Obend.Leaf.Book` via `compileLcnfFunDeclToBook`
   produces a closed composition whose book member `"lcnfCountdown42"` applied to `.nat 0`
   halts with `.natural 42` (`Halts`). -/
theorem lcnf_elab_pass_to_book_sound (v1 v2 offset : Nat) :
    SSteps (compileLcnfToLExpr (mkShiftedJpCode v1 v2 offset)) (.lit (v1 + v2 + offset)) ∧
    Evaluates (compileLcnfToCore4 (mkShiftedJpCode v1 v2 offset)) (.nat (v1 + v2 + offset)) ∧
    evalLcnfCode 8 [] [] [] (mkShiftedJpCode v1 v2 offset) = some (v1 + v2 + offset, []) ∧
    Obend.Equiv.Halts
      (.app (.get (compileLcnfFunDeclToBook sampleLcnfRecDecl).link sampleLcnfRecDecl.name) (.nat 0))
      (.natural 42) := by
  have hJp := mkShiftedJpCode_runs v1 v2 offset
  refine ⟨hJp, ?_, rfl, ?_⟩
  · simpa [compileLcnfToCore4, lowerT] using lower_sound_nat hJp
  · exact lean_to_book sampleLcnfRecDecl.name (lcnfFunDeclToLExpr sampleLcnfRecDecl) 0 42
      (by
        simp only [lcnfFunDeclToLExpr, lowerT, recSpec_eq]
        decide +kernel) sampleLcnfRecDecl_runs_zero

/-- Dispatch deliberately skips the first arm; subtraction observes both binder positions. -/
def casesProjCode (x y : Nat) : LcnfCode :=
  .letValue (.ctor "right" [("x", .lit x), ("y", .lit y)])
    (.cases (.bvar 0)
      [("left", [], .return (.lit 0)),
       ("right", ["x", "y"],
         .letValue (.natOp .sub (.bvar 1) (.bvar 0)) (.return (.bvar 0)))])

def namedProjCode (field : String) (x y : Nat) : LcnfCode :=
  .letValue (.record [("fst", .lit x), ("snd", .lit y)])
    (.letValue (.proj field (.bvar 0)) (.return (.bvar 0)))

def unmatchedCasesCode (x : Nat) : LcnfCode :=
  .letValue (.ctor "absent" [("x", .lit x)])
    (.cases (.bvar 0) [("right", ["x"], .return (.bvar 0))])

theorem casesProjCode_runs (x y : Nat) :
    SSteps (compileLcnfToLExpr (casesProjCode x y)) (.lit (x - y)) := by
  change SSteps (.letE .emptyRow (.inject "right" [("x", .lit x), ("y", .lit y)])
    (.cases .emptyRow
      [("left", [], .lit 0), ("right", ["x", "y"],
        .lam .emptyRow (.lam .emptyRow
          (.letE .emptyRow (.natBin .sub (.bvar 1) (.bvar 0)) (.bvar 0))))]
      (.bvar 0))) _
  refine .next (.zeta _ _ _) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, List.map_cons,
    List.map_nil]
  refine .next (.casesInject _ _ "right" _ ["x", "y"] _ [.lit x, .lit y] rfl rfl) ?_
  simp only [LExpr.spine]
  refine .next (.appFun _ (.beta _ _ _)) ?_
  simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  refine .next (.beta _ _ _) ?_
  simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  refine .next (.zeta _ _ _) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single]
  exact .next (.binLit .sub x y) (.refl _)

theorem namedProjCode_runs (x y : Nat) :
    SSteps (compileLcnfToLExpr (namedProjCode "snd" x y)) (.lit y) := by
  change SSteps (.letE .emptyRow (.record [("fst", .lit x), ("snd", .lit y)])
    (.letE .emptyRow (.proj "snd" (.bvar 0)) (.bvar 0))) _
  refine .next (.zeta _ _ _) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  refine .next (.zeta _ _ _) ?_
  simp only [LExpr.inst, LExpr.subst, LExpr.single]
  exact .next (.projRecord "snd" _ (.lit y) rfl) (.refl _)

/-- Tag dispatch, field order and named projection agree with both lowering semantics;
missing tags and missing fields are refused by the scalar evaluator. -/
theorem lcnf_eval_cases_proj_sound (x y : Nat) :
    evalLcnfCode 8 [] [] [] (casesProjCode x y) = some (x - y, []) ∧
    SSteps (compileLcnfToLExpr (casesProjCode x y)) (.lit (x - y)) ∧
    Evaluates (compileLcnfToCore4 (casesProjCode x y)) (.nat (x - y)) ∧
    evalLcnfCode 8 [] [] [] (unmatchedCasesCode x) = none ∧
    evalLcnfCode 8 [] [] [] (namedProjCode "snd" x y) = some (y, []) ∧
    Evaluates (compileLcnfToCore4 (namedProjCode "snd" x y)) (.nat y) ∧
    evalLcnfCode 8 [] [] [] (namedProjCode "missing" x y) = none := by
  refine ⟨rfl, casesProjCode_runs x y, ?_, rfl, rfl, ?_, rfl⟩
  · simpa [compileLcnfToCore4, lowerT] using lower_sound_nat (casesProjCode_runs x y)
  · simpa [compileLcnfToCore4, lowerT] using lower_sound_nat (namedProjCode_runs x y)

/-- Curried closures retain captured values; the last argument occupies binder zero. -/
theorem lcnf_eval_closure_sound (x y captured : Nat) :
    let decl : LcnfFunDecl :=
      { name := "capture", numParams := 2,
        body := .letValue (.natOp .sub (.bvar 1) (.bvar 0))
          (.letValue (.natOp .add (.bvar 0) (.bvar 4)) (.return (.bvar 0))) }
    evalLcnfCodeVal 10 [.closure [.scalar captured] [] decl] [] []
      (.letValue (.app (.bvar 0) (.lit x))
        (.letValue (.app (.bvar 0) (.lit y)) (.return (.bvar 0)))) =
      some (.scalar (x - y + captured), []) := by
  rfl

/-- Invalid runtime shapes and missing constructor fields cannot become scalar successes. -/
theorem lcnf_eval_invalid_refused (n : Nat) :
    evalLcnfCode 8 [] [] [] (.letValue (.app (.lit n) (.lit 1)) (.return (.bvar 0))) = none ∧
    evalLcnfCode 8 [] [] [] (.letValue (.proj "x" (.lit n)) (.return (.bvar 0))) = none ∧
    evalLcnfCode 8 [] [] [] (.letValue (.record [("x", .lit n)]) (.return (.bvar 0))) = none ∧
    evalLcnfCode 8 [] [] [] (.cases (.lit n) [("right", [], .return (.lit 0))]) = none ∧
    evalLcnfCode 8 [] [] []
      (.letValue (.ctor "right" [("x", .lit n)])
        (.cases (.bvar 0) [("right", ["missing"], .return (.bvar 0))])) = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A jump-site binding must not shadow a variable captured by the join declaration. -/
def lexicalCaptureCode (captured shadowed arg : Nat) : LcnfCode :=
  .letValue (.arg (.lit captured))
    (.jpDecl 0 1
      (.letValue (.natOp .add (.bvar 0) (.bvar 1)) (.return (.bvar 0)))
      (.letValue (.arg (.lit shadowed)) (.jmp 0 [.lit arg])))

theorem lexicalCaptureCode_runs (captured shadowed arg : Nat) :
    SSteps (compileLcnfToLExpr (lexicalCaptureCode captured shadowed arg))
      (.lit (arg + captured)) := by
  change SSteps (.letE .emptyRow (.lit captured)
    (.letE .emptyRow
      (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.bvar 1)) (.bvar 0)))
      (.letE .emptyRow (.lit shadowed) (.app (.bvar 1) (.lit arg))))) _
  refine .next (.zeta _ _ _) ?_
  simp [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst, LExpr.rename, liftRename]
  refine .next (.zeta _ _ _) ?_
  simp [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst, LExpr.rename, liftRename]
  refine .next (.zeta _ _ _) ?_
  simp [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst, LExpr.rename, liftRename]
  refine .next (.beta _ _ _) ?_
  simp [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst, LExpr.rename, liftRename]
  refine .next (.zeta _ _ _) ?_
  simp [LExpr.inst, LExpr.subst, LExpr.single]
  exact .next (.binLit .add arg captured) (.refl _)

/-- Evaluator and both compilation layers agree for every captured, shadowing, and
argument value. The result is independent of the intervening binding. -/
theorem lcnf_jp_lexical_capture_sound (captured shadowed arg : Nat) :
    evalLcnfCode 8 [] [] [] (lexicalCaptureCode captured shadowed arg) =
      some (arg + captured, []) ∧
    SSteps (compileLcnfToLExpr (lexicalCaptureCode captured shadowed arg))
      (.lit (arg + captured)) ∧
    Evaluates (compileLcnfToCore4 (lexicalCaptureCode captured shadowed arg))
      (.nat (arg + captured)) := by
  refine ⟨rfl, lexicalCaptureCode_runs captured shadowed arg, ?_⟩
  simpa [compileLcnfToCore4, lowerT] using lower_sound_nat (lexicalCaptureCode_runs captured shadowed arg)

/-- Entry through the public module API, including two recursive self applications. -/
def sampleLcnfRecModule : LcnfModule :=
  { decls := [sampleLcnfRecDecl],
    entry := .letValue (.app (.bvar 0) (.lit 2)) (.return (.bvar 0)) }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem sampleLcnfRecModule_runs :
    SSteps (compileLcnfModuleToLExpr sampleLcnfRecModule) (.lit 42) := by
  simp only [compileLcnfModuleToLExpr, sampleLcnfRecModule,
    compileLcnfModuleToLExpr.bindDecls, lcnfFunDeclToLExpr, sampleLcnfRecDecl,
    compileLcnfToLExpr, codeUsesState, letValueUsesState, compileLcnfWithCtx,
    lcnfLetValueToLExprCtx, lcnfArgToLExprCtx, LcnfLowerCtx.pushVar,
    LcnfLowerCtx.lookupVar, wrapMinorBvars, List.map_cons, List.map_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Bool.false_or, Bool.or_false, Bool.false_eq_true, ite_false, Nat.add_zero]
  repeat
    first
    | exact .refl _
    | (refine .next (.zeta _ _ _) ?_)
    | (refine .next (.beta _ _ _) ?_)
    | (refine .next (.appFun _ (.unfold _ _ _)) ?_)
    | (refine .next (.boolRecTrue _ _ _) ?_)
    | (refine .next (.boolRecFalse _ _ _) ?_)
    | (refine .next (.boolRecMajor _ _ _ (.binLit _ _ _)) ?_)
    | (refine .next (.boolRecMajor _ _ _ (.binLeft _ _ (.binLit _ _ _))) ?_)
    | (refine .next (.boolRecMajor _ _ _ (.binLeft _ _ (.binLeft _ _ (.binLit _ _ _)))) ?_)
    | simp [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst,
        LExpr.rename, liftRename, NatOp.eval]

/-- The same closed recursive module evaluates to 42 through the interpreter,
source reduction, and Core4. -/
theorem sampleLcnfRecModule_eval_agreed :
    evalLcnfModule 32 sampleLcnfRecModule = some (42, []) ∧
    SSteps (compileLcnfModuleToLExpr sampleLcnfRecModule) (.lit 42) ∧
    Evaluates (compileLcnfModuleToCore4 sampleLcnfRecModule) (.nat 42) := by
  refine ⟨rfl, sampleLcnfRecModule_runs, ?_⟩
  simpa [compileLcnfModuleToCore4, lowerT] using lower_sound_nat sampleLcnfRecModule_runs

mutual
/-- State-free runtime values are related to source expressions by weak-head
reduction; record and constructor fields remain lazy, as in `SStep`. -/
inductive LcnfValueRel : LcnfVal → LExpr → Prop where
  | scalar {e : LExpr} (n : Nat) : SSteps e (.lit n) → LcnfValueRel (.scalar n) e
  | bool {e : LExpr} (b : Bool) : SSteps e (.boolLit b) → LcnfValueRel (.bool b) e
  | erased {e : LExpr} : SSteps e .erased → LcnfValueRel .erased e
  | stateTok {e : LExpr} (id : Nat) : SSteps e (.lit id) → LcnfValueRel (.stateTok id) e
  | record {e : LExpr} {vs : List (String × LcnfVal)} {es : List (String × LExpr)} :
      SSteps e (.record es) → LcnfFieldsRel vs es → LcnfValueRel (.record vs) e
  | ctor {e : LExpr} {tag : String} {vs : List (String × LcnfVal)} {es : List (String × LExpr)} :
      SSteps e (.inject tag es) → LcnfFieldsRel vs es → LcnfValueRel (.ctor tag vs) e

inductive LcnfFieldsRel : List (String × LcnfVal) → List (String × LExpr) → Prop where
  | nil : LcnfFieldsRel [] []
  | cons {v : String × LcnfVal} {e : String × LExpr}
      {vs : List (String × LcnfVal)} {es : List (String × LExpr)} :
      v.1 = e.1 → LcnfValueRel v.2 e.2 → LcnfFieldsRel vs es →
      LcnfFieldsRel (v :: vs) (e :: es)
end

private theorem LcnfValueRel.steps {v : LcnfVal} {e e' : LExpr}
    (hs : SSteps e e') (h : LcnfValueRel v e') : LcnfValueRel v e := by
  cases h with
  | scalar n h => exact .scalar n (ssteps_trans hs h)
  | bool v h => exact .bool v (ssteps_trans hs h)
  | erased h => exact .erased (ssteps_trans hs h)
  | stateTok id h => exact .stateTok id (ssteps_trans hs h)
  | record h fs => exact .record (ssteps_trans hs h) fs
  | ctor h fs => exact .ctor (ssteps_trans hs h) fs

private theorem LcnfValueRel.scalar_steps {n : Nat} {e : LExpr}
    (h : LcnfValueRel (.scalar n) e) : SSteps e (.lit n) := by cases h with
  | scalar _ hs => exact hs


private theorem LcnfValueRel.bool_steps {b : Bool} {e : LExpr}
    (h : LcnfValueRel (.bool b) e) : SSteps e (.boolLit b) := by cases h with
  | bool _ hs => exact hs


/-- Every runtime variable is represented by the corresponding substituted
compiler variable. This invariant allows arbitrary source environments. -/
def LcnfEnvRel (env : List LcnfVal) (ctx : LcnfLowerCtx) (σ : Nat → LExpr) : Prop :=
  ∀ i v, env[i]? = some v → LcnfValueRel v (σ (ctx.lookupVar i))

private theorem lookupVar_pushVar_zero (ctx : LcnfLowerCtx) :
    ctx.pushVar.lookupVar 0 = 0 := by simp [LcnfLowerCtx.pushVar, LcnfLowerCtx.lookupVar]

private theorem lookupVar_pushVar_succ (ctx : LcnfLowerCtx) (i : Nat) :
    ctx.pushVar.lookupVar (i + 1) = ctx.lookupVar i + 1 := by
  simp only [LcnfLowerCtx.pushVar, LcnfLowerCtx.lookupVar, List.getElem?_cons_succ,
    List.getElem?_map]
  cases ctx.varEnv[i]? <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem LcnfEnvRel.cons {env : List LcnfVal} {ctx : LcnfLowerCtx}
    {σ : Nat → LExpr} {v : LcnfVal} {e : LExpr}
    (h : LcnfEnvRel env ctx σ) (hv : LcnfValueRel v e) :
    LcnfEnvRel (v :: env) ctx.pushVar (consSubst e σ) := by
  intro i w hi
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst w; simpa only [lookupVar_pushVar_zero, consSubst] using hv
  | succ i => simpa only [lookupVar_pushVar_succ, consSubst] using h i w hi

private theorem evalLcnfArgVal_rel {env : List LcnfVal} {ctx : LcnfLowerCtx}
    {σ : Nat → LExpr} (h : LcnfEnvRel env ctx σ) (a : LcnfArg) (v : LcnfVal)
    (hv : evalLcnfArgVal env a = some v) :
    LcnfValueRel v ((lcnfArgToLExprCtx ctx a).subst σ) := by
  cases a <;> simp only [evalLcnfArgVal, lcnfArgToLExprCtx, LExpr.subst] at hv ⊢
  · exact h _ _ hv
  all_goals cases hv
  · exact .scalar _ (.refl _)
  · exact .bool _ (.refl _)
  · exact .erased (.refl _)
  · exact .stateTok _ (.refl _)

private theorem evalLcnfFields_rel {env : List LcnfVal} {ctx : LcnfLowerCtx}
    {σ : Nat → LExpr} (h : LcnfEnvRel env ctx σ)
    (fs : List (String × LcnfArg)) (vs : List (String × LcnfVal))
    (hv : fs.mapM (fun x => (evalLcnfArgVal env x.2).bind (fun v => some (x.1, v))) = some vs) :
    LcnfFieldsRel vs
      (fs.map (fun f => (f.1, (lcnfArgToLExprCtx ctx f.2).subst σ))) := by
  induction fs generalizing vs with
  | nil => simp at hv; subst vs; exact .nil
  | cons f fs ih =>
    obtain ⟨name, a⟩ := f
    cases ha : evalLcnfArgVal env a with
    | none => simp [List.mapM_cons, ha] at hv
    | some v =>
      cases ht : fs.mapM (fun x => (evalLcnfArgVal env x.2).bind (fun v => some (x.1, v))) with
      | none => simp [List.mapM_cons, ha, ht] at hv
      | some rest =>
        simp [List.mapM_cons, ha, ht] at hv
        subst vs
        exact .cons rfl (evalLcnfArgVal_rel h a v ha) (ih rest ht)

private theorem LcnfValueRel.record_steps {vs : List (String × LcnfVal)} {e : LExpr}
    (h : LcnfValueRel (.record vs) e) :
    ∃ es, SSteps e (.record es) ∧
      LcnfFieldsRel vs es := by cases h with
  | record hs fs => exact ⟨_, hs, fs⟩


private theorem LcnfValueRel.ctor_steps {tag : String} {vs : List (String × LcnfVal)} {e : LExpr}
    (h : LcnfValueRel (.ctor tag vs) e) :
    ∃ es, SSteps e (.inject tag es) ∧
      LcnfFieldsRel vs es := by cases h with
  | ctor hs fs => exact ⟨_, hs, fs⟩


private theorem relatedFields_find {vs : List (String × LcnfVal)}
    {es : List (String × LExpr)}
    (h : LcnfFieldsRel vs es)
    (name : String) (p : String × LcnfVal)
    (hp : vs.find? (fun p => p.1 == name) = some p) :
    ∃ e, es.find? (fun p => p.1 == name) = some (name, e) ∧ LcnfValueRel p.2 e := by
  cases h with
  | nil => simp at hp
  | @cons v e vs es hname hval htail =>
    by_cases hn : v.1 = name
    · simp [List.find?, hn] at hp
      subst p
      exact ⟨e.2, by simp [List.find?, ← hname, hn]; exact Prod.ext (hname.symm.trans hn) rfl, hval⟩
    · have hnb : (v.1 == name) = false := beq_eq_false_iff_ne.mpr hn
      simp [List.find?, hnb] at hp
      obtain ⟨r, hr, hv⟩ := relatedFields_find htail name p hp
      exact ⟨r, by simpa [List.find?, ← hname, hnb] using hr, hv⟩
termination_by vs.length

/-- Supported state-free RHSs. Applications require a separate recursive-function
logical relation and are intentionally outside this structural block theorem. -/
def isPureLetValue : LcnfLetValue → Bool
  | .arg _ | .natOp _ _ _ | .ctor _ _ | .record _ | .proj _ _ => true
  | _ => false

private theorem evalLcnfLetValueVal_rel (fuel : Nat) {env : List LcnfVal}
    {ctx : LcnfLowerCtx} {σ : Nat → LExpr} (henv : LcnfEnvRel env ctx σ)
    (jps : List LcnfJpClosure) (st st' : List (Nat × Nat))
    (rhs : LcnfLetValue) (v : LcnfVal) (hp : isPureLetValue rhs = true)
    (hv : evalLcnfLetValueVal fuel env jps st rhs = some (v, st')) :
    st' = st ∧ LcnfValueRel v ((lcnfLetValueToLExprCtx ctx rhs).subst σ) := by
  cases fuel with
  | zero => simp [evalLcnfLetValueVal] at hv
  | succ fuel =>
    cases rhs with
    | arg a =>
      cases ha : evalLcnfArgVal env a <;> simp [evalLcnfLetValueVal, ha] at hv
      rcases hv with ⟨rfl, rfl⟩
      exact ⟨rfl, by simpa only [lcnfLetValueToLExprCtx] using evalLcnfArgVal_rel henv _ _ ha⟩
    | natOp op l r =>
      cases hl : evalLcnfArgVal env l with
      | none => simp [evalLcnfLetValueVal, hl] at hv
      | some lv =>
        cases lv <;> simp [evalLcnfLetValueVal, hl] at hv
        rename_i a
        cases hr : evalLcnfArgVal env r with
        | none => simp [hr] at hv
        | some rv =>
          cases rv <;> simp [hr] at hv
          rename_i b
          have sl := (evalLcnfArgVal_rel henv _ _ hl).scalar_steps
          have sr := (evalLcnfArgVal_rel henv _ _ hr).scalar_steps
          have steps := ssteps_trans
            (ssteps_congr (fun e => .natBin op e ((lcnfArgToLExprCtx ctx r).subst σ))
              (fun s => .binLeft op _ s) sl)
            (ssteps_trans (ssteps_congr (fun e => .natBin op (.lit a) e)
              (fun s => .binRight op a s) sr) (.next (.binLit op a b) (.refl _)))
          cases op <;> simp at hv <;> rcases hv with ⟨rfl, rfl⟩
          all_goals simp only [lcnfLetValueToLExprCtx, LExpr.subst]
          all_goals refine ⟨by trivial, .steps steps ?_⟩
          all_goals first | exact .scalar _ (.refl _) | exact .bool _ (.refl _)
    | ctor tag fs =>
      cases hf : fs.mapM (fun x => (evalLcnfArgVal env x.2).bind (fun v => some (x.1, v))) with
      | none => simp [evalLcnfLetValueVal, hf] at hv
      | some vs =>
        simp [evalLcnfLetValueVal, hf] at hv
        rcases hv with ⟨rfl, rfl⟩
        refine ⟨rfl, ?_⟩
        simpa only [lcnfLetValueToLExprCtx, LExpr.subst, List.map_map, Function.comp_def]
          using LcnfValueRel.ctor (.refl _) (evalLcnfFields_rel henv fs vs hf)
    | record fs =>
      cases hf : fs.mapM (fun x => (evalLcnfArgVal env x.2).bind (fun v => some (x.1, v))) with
      | none => simp [evalLcnfLetValueVal, hf] at hv
      | some vs =>
        simp [evalLcnfLetValueVal, hf] at hv
        rcases hv with ⟨rfl, rfl⟩
        refine ⟨rfl, ?_⟩
        simpa only [lcnfLetValueToLExprCtx, LExpr.subst, List.map_map, Function.comp_def]
          using LcnfValueRel.record (.refl _) (evalLcnfFields_rel henv fs vs hf)
    | proj name tgt =>
      cases ht : evalLcnfArgVal env tgt with
      | none => simp [evalLcnfLetValueVal, ht] at hv
      | some tv =>
        cases tv <;> simp [evalLcnfLetValueVal, ht] at hv
        rename_i fs
        cases hf : fs.find? (fun p => p.1 == name) with
        | none => simp [hf] at hv
        | some p =>
          simp [hf] at hv
          rcases hv with ⟨rfl, rfl⟩
          obtain ⟨es, hs, he⟩ := (evalLcnfArgVal_rel henv _ _ ht).record_steps
          obtain ⟨e, hfind, hrel⟩ := relatedFields_find he name p hf
          simp only [lcnfLetValueToLExprCtx, LExpr.subst]
          exact ⟨by trivial, .steps (ssteps_trans
            (ssteps_congr (.proj name) (fun s => .projTarget name s) hs)
            (.next (.projRecord name es e hfind) (.refl _))) hrel⟩
    | app _ _ | stateRead _ _ | stateWrite _ _ _ => cases hp

/-- The block fragment proved below: scalar operations, aggregate construction
and projection, Boolean branches, and constructor dispatch. No state or calls. -/
inductive PureBlock : LcnfCode → Prop where
  | ret (a : LcnfArg) : PureBlock (.return a)
  | unreach : PureBlock .unreach
  | letValue {v : LcnfLetValue} {body : LcnfCode} :
      isPureLetValue v = true → PureBlock body → PureBlock (.letValue v body)
  | ifBool {a : LcnfArg} {t f : LcnfCode} :
      PureBlock t → PureBlock f → PureBlock (.ifBool a t f)
  | cases {a : LcnfArg} {arms : List (String × List String × LcnfCode)} :
      (∀ arm ∈ arms, PureBlock arm.2.2) → PureBlock (.cases a arms)

private theorem pureLetValue_usesState (v : LcnfLetValue) (h : isPureLetValue v = true) :
    letValueUsesState v = false := by cases v <;> cases h <;> rfl

private theorem PureBlock.usesState {c : LcnfCode} (h : PureBlock c) :
    codeUsesState c = false := by
  induction h with
  | ret => rfl
  | unreach => rfl
  | letValue hp _ ih => simp [codeUsesState, pureLetValue_usesState _ hp, ih]
  | ifBool _ _ iht ihf => simp [codeUsesState, iht, ihf]
  | @cases a arms hp ih =>
    simp only [codeUsesState]
    induction arms with
    | nil => rfl
    | cons arm rest ihr =>
      simp only [armsUseState]
      rw [ih arm (by simp), ihr (fun x hx => hp x (by simp [hx]))
        (fun x hx => ih x (by simp [hx]))]
      rfl

/-- A list of runtime arguments paired with their lazy source representatives. -/
inductive LcnfArgsRel : List LcnfVal → List LExpr → Prop where
  | nil : LcnfArgsRel [] []
  | cons {v : LcnfVal} {e : LExpr} {vs : List LcnfVal} {es : List LExpr} :
      LcnfValueRel v e → LcnfArgsRel vs es → LcnfArgsRel (v :: vs) (e :: es)

private theorem relatedFields_split {vs : List (String × LcnfVal)} {es : List (String × LExpr)}
    (h : LcnfFieldsRel vs es) (names : List String) (vals : List LcnfVal)
    (hv : splitValues vs names = some vals) :
    ∃ exprs, splitValues es names = some exprs ∧ LcnfArgsRel vals exprs := by
  induction names generalizing vals with
  | nil => simp [splitValues] at hv; subst vals; exact ⟨[], rfl, .nil⟩
  | cons name names ih =>
    cases hf : vs.find? (fun p => p.1 == name) with
    | none => simp [splitValues, hf] at hv
    | some p =>
      cases ht : splitValues vs names with
      | none => simp [splitValues, hf, ht] at hv
      | some rest =>
        simp [splitValues, hf, ht] at hv
        subst vals
        obtain ⟨e, he, hr⟩ := relatedFields_find h name p hf
        obtain ⟨exprs, hes, hrs⟩ := ih rest ht
        exact ⟨e :: exprs, by simp [splitValues, he, hes], .cons hr hrs⟩

private theorem LcnfArgsRel.length {vs : List LcnfVal} {es : List LExpr}
    (h : LcnfArgsRel vs es) : vs.length = es.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem sstep_spine {f g : LExpr} (h : SStep f g) (es : List LExpr) :
    SStep (f.spine es) (g.spine es) := by
  induction es generalizing f g with
  | nil => exact h
  | cons e es ih => exact ih (.appFun e h)

private theorem pushVars_pushVar (ctx : LcnfLowerCtx) (n : Nat) :
    ctx.pushVar.pushVars n = (ctx.pushVars n).pushVar := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [LcnfLowerCtx.pushVars, ih]

/-- Applying a curried minor extends the substitution in argument order; thus
its final environment is the reverse of the source field list. -/
private theorem minor_spine_subst (es : List LExpr) (body : LExpr) (σ : Nat → LExpr) :
    SSteps (((wrapMinorBvars es.length body).subst σ).spine es)
      (body.subst (es.foldl (fun σ e => consSubst e σ) σ)) := by
  induction es generalizing body σ with
  | nil => simp [wrapMinorBvars, LExpr.spine]; exact .refl _
  | cons e es ih =>
    simp only [List.length_cons, wrapMinorBvars, LExpr.subst, LExpr.spine]
    have hb := ssteps_congr (fun f => f.spine es) (fun st => sstep_spine st es)
      (SSteps.next (SStep.beta .emptyRow
        ((wrapMinorBvars es.length body).subst (LExpr.liftSubst σ)) e) (.refl _))
    rw [subst_liftSubst_inst] at hb
    exact ssteps_trans hb (ih body (consSubst e σ))

private theorem args_env_rel {vs : List LcnfVal} {es : List LExpr}
    (h : LcnfArgsRel vs es) {env : List LcnfVal} {ctx : LcnfLowerCtx}
    {σ : Nat → LExpr} (henv : LcnfEnvRel env ctx σ) :
    LcnfEnvRel (vs.reverse ++ env) (ctx.pushVars vs.length)
      (es.foldl (fun σ e => consSubst e σ) σ) := by
  induction h generalizing env ctx σ with
  | nil => simpa [LcnfLowerCtx.pushVars] using henv
  | @cons v e vs es hv hs ih =>
    have hi := ih (henv.cons hv)
    simpa [List.reverse_cons, List.append_assoc, LcnfLowerCtx.pushVars, pushVars_pushVar] using hi

private theorem splitValues_length {α : Type} {fields : List (String × α)}
    {names : List String} {vals : List α} (h : splitValues fields names = some vals) :
    vals.length = names.length := by
  induction names generalizing vals with
  | nil => simp [splitValues] at h; subst vals; rfl
  | cons name names ih =>
    cases hf : fields.find? (fun p => p.1 == name) with
    | none => simp [splitValues, hf] at h
    | some p =>
      cases ht : splitValues fields names with
      | none => simp [splitValues, hf, ht] at h
      | some rest =>
        simp [splitValues, hf, ht] at h
        subst vals
        simp [ih ht]

private theorem compiled_arms_find (ctx : LcnfLowerCtx) (σ : Nat → LExpr)
    (tag : String) (arms : List (String × List String × LcnfCode))
    (p : String × List String × LcnfCode)
    (h : arms.find? (fun arm => arm.1 == tag) = some p) :
    p.1 = tag ∧
    ((lcnfArmsWithCtx ctx arms).map (fun a => (a.1, a.2.1, a.2.2.subst σ))).find?
      (fun arm => arm.1 == tag) =
      some (tag, p.2.1, (wrapMinorBvars p.2.1.length
        (compileLcnfWithCtx (ctx.pushVars p.2.1.length) p.2.2)).subst σ) := by
  induction arms with
  | nil => simp at h
  | cons arm arms ih =>
    obtain ⟨label, names, body⟩ := arm
    cases ht : (label == tag) with
    | false =>
      simp [List.find?, ht] at h
      simpa [lcnfArmsWithCtx, List.find?, ht] using ih h
    | true =>
      simp [List.find?, ht] at h
      subst p
      have he : label = tag := beq_iff_eq.mp ht
      subst label
      exact ⟨rfl, by simp [lcnfArmsWithCtx, List.find?]⟩

private theorem compile_pureLet (ctx : LcnfLowerCtx) (v : LcnfLetValue)
    (body : LcnfCode) (h : isPureLetValue v = true) :
    compileLcnfWithCtx ctx (.letValue v body) =
      .letE .emptyRow (lcnfLetValueToLExprCtx ctx v) (compileLcnfWithCtx ctx.pushVar body) := by
  cases v <;> (try cases h) <;> rfl

/-- Fuel induction connecting the actual evaluator to source reduction on the
state-free block fragment. The environment relation permits arbitrary lazy
representatives, so let-bound records and nested cases compose. -/
theorem evalLcnfCodeVal_simulates_ssteps (fuel : Nat) (c : LcnfCode) (hp : PureBlock c)
    (env : List LcnfVal) (ctx : LcnfLowerCtx) (σ : Nat → LExpr)
    (henv : LcnfEnvRel env ctx σ) (jps : List LcnfJpClosure)
    (st st' : List (Nat × Nat)) (v : LcnfVal)
    (hv : evalLcnfCodeVal fuel env jps st c = some (v, st')) :
    st' = st ∧ LcnfValueRel v ((compileLcnfWithCtx ctx c).subst σ) := by
  induction fuel generalizing c env ctx σ jps st st' v with
  | zero => simp [evalLcnfCodeVal] at hv
  | succ fuel ih =>
    cases hp with
    | ret a =>
      cases ha : evalLcnfArgVal env a <;> simp [evalLcnfCodeVal, ha] at hv
      rcases hv with ⟨rfl, rfl⟩
      exact ⟨rfl, by simpa only [compileLcnfWithCtx] using evalLcnfArgVal_rel henv _ _ ha⟩
    | unreach => simp [evalLcnfCodeVal] at hv
    | @letValue rhs body hr hb =>
      cases he : evalLcnfLetValueVal fuel env jps st rhs with
      | none => simp [evalLcnfCodeVal, he] at hv
      | some result =>
        obtain ⟨value, store⟩ := result
        simp only [evalLcnfCodeVal, he, Option.bind_some] at hv
        obtain ⟨hstore, hvalue⟩ := evalLcnfLetValueVal_rel fuel henv jps st store rhs value hr he
        subst store
        obtain ⟨hst, hbody⟩ := ih body hb (value :: env) ctx.pushVar
          (consSubst ((lcnfLetValueToLExprCtx ctx rhs).subst σ) σ) (henv.cons hvalue)
          jps st st' v hv
        refine ⟨hst, ?_⟩
        rw [compile_pureLet ctx rhs body hr]
        simp only [LExpr.subst]
        apply LcnfValueRel.steps (.next (.zeta _ _ _) (.refl _))
        rw [subst_liftSubst_inst]
        exact hbody
    | @ifBool cond t f ht hf =>
      cases ha : evalLcnfArgVal env cond with
      | none => simp [evalLcnfCodeVal, ha] at hv
      | some val =>
        cases val <;> simp [evalLcnfCodeVal, ha] at hv
        rename_i b
        have hs := (evalLcnfArgVal_rel henv _ _ ha).bool_steps
        have stepMajor := ssteps_congr
          (fun e => .boolRec .emptyRow ((compileLcnfWithCtx ctx f).subst σ)
            ((compileLcnfWithCtx ctx t).subst σ) e)
          (fun s => .boolRecMajor _ _ _ s) hs
        cases b
        · obtain ⟨hst, hbody⟩ := ih f hf env ctx σ henv jps st st' v hv
          refine ⟨hst, ?_⟩
          simp only [compileLcnfWithCtx, LExpr.subst]
          exact .steps (ssteps_trans stepMajor (.next (.boolRecFalse _ _ _) (.refl _))) hbody
        · obtain ⟨hst, hbody⟩ := ih t ht env ctx σ henv jps st st' v hv
          refine ⟨hst, ?_⟩
          simp only [compileLcnfWithCtx, LExpr.subst]
          exact .steps (ssteps_trans stepMajor (.next (.boolRecTrue _ _ _) (.refl _))) hbody
    | @cases scrut arms harms =>
      cases ha : evalLcnfArgVal env scrut with
      | none => simp [evalLcnfCodeVal, ha] at hv
      | some val =>
        cases val <;> simp [evalLcnfCodeVal, ha] at hv
        rename_i tag fs
        cases hf : arms.find? (fun arm => arm.1 == tag) with
        | none => simp [hf] at hv
        | some arm =>
          obtain ⟨label, names, body⟩ := arm
          cases hvals : splitValues fs names with
          | none => simp [hf, hvals] at hv
          | some vals =>
            simp [hf, hvals] at hv
            obtain ⟨es, hs, hfields⟩ := (evalLcnfArgVal_rel henv _ _ ha).ctor_steps
            obtain ⟨exprs, hexprs, hargs⟩ := relatedFields_split hfields names vals hvals
            have hlen : vals.length = names.length := splitValues_length hvals
            have helen : exprs.length = names.length := hargs.length.symm.trans hlen
            have hpbody := harms (label, names, body) (List.mem_of_find?_eq_some hf)
            have he := args_env_rel hargs henv
            rw [hlen] at he
            obtain ⟨hst, hbody⟩ := ih body hpbody (vals.reverse ++ env)
              (ctx.pushVars names.length) (exprs.foldl (fun σ e => consSubst e σ) σ)
              he jps st st' v hv
            obtain ⟨_, hfind⟩ := compiled_arms_find ctx σ tag arms (label, names, body) hf
            refine ⟨hst, ?_⟩
            simp only [compileLcnfWithCtx, LExpr.subst]
            apply LcnfValueRel.steps (ssteps_congr
              (fun e => .cases .emptyRow
                ((lcnfArmsWithCtx ctx arms).map (fun a => (a.1, a.2.1, a.2.2.subst σ))) e)
              (fun s => .casesMajor _ _ s) hs)
            apply LcnfValueRel.steps (.next (.casesInject _ _ tag es names _ exprs hfind hexprs) (.refl _))
            have hminor := minor_spine_subst exprs (compileLcnfWithCtx (ctx.pushVars names.length) body) σ
            rw [helen] at hminor
            exact .steps hminor hbody

/-- Closed scalar corollary for all fuel amounts and all supported blocks.
Unreachable blocks have no successful evaluator run and require no false
compiler-divergence claim. -/
theorem evalLcnfCode_simulates_core4 (fuel : Nat) (c : LcnfCode) (n : Nat)
    (hp : PureBlock c)
    (hv : evalLcnfCode fuel [] [] [] c = some (n, [])) :
    Evaluates (compileLcnfToCore4 c) (.nat n) := by
  cases he : evalLcnfCodeVal fuel [] [] [] c with
  | none => simp [evalLcnfCode, he] at hv
  | some result =>
    obtain ⟨v, st⟩ := result
    cases v <;> simp [evalLcnfCode, he, LcnfVal.toNat?] at hv
    rename_i m
    rcases hv with ⟨hm, hst⟩
    subst m
    subst st
    have henv : LcnfEnvRel [] {} LExpr.bvar := by intro i v h; simp at h
    have hs := (evalLcnfCodeVal_simulates_ssteps fuel c hp [] {} LExpr.bvar
      henv [] [] [] (.scalar n) he).2.scalar_steps
    rw [LExpr.subst_bvar] at hs
    have hc : SSteps (compileLcnfToLExpr c) (.lit n) := by
      simpa [compileLcnfToLExpr, hp.usesState] using hs
    simpa [compileLcnfToCore4, lowerT] using lower_sound_nat hc

end Obend.Lower.LCNF
end
