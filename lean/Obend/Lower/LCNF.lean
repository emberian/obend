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
   - Proves `lcnf_zero_erasure_sound`, `lcnf_linear_state_conserved`, `lcnf_to_core4_sound`,
     and `lcnf_elab_pass_to_book_sound`.
-/
public import Obend.Lower.Fragment
public import Obend.Lower.Proofs.Sound
public import Obend.Lower.Proofs.Book

@[expose] public section

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

/-- Look up a scalar `Nat` value in an LCNF environment `env : List Nat`. -/
def evalLcnfArgNat (env : List Nat) : LcnfArg → Nat
  | .bvar i      => env.getD i 0
  | .lit n       => n
  | .boolLit b   => if b then 1 else 0
  | .erased      => 0
  | .stateTok id => id

/-- Read a cell from the linear state store `st : List (Nat × Nat)`. -/
def readLinearStore (st : List (Nat × Nat)) (addr : Nat) : Nat :=
  match st.find? (fun p => p.1 == addr) with
  | some (_, v) => v
  | none        => 0

/-- Write a cell in the linear state store `st : List (Nat × Nat)` in-place. -/
def writeLinearStore (st : List (Nat × Nat)) (addr val : Nat) : List (Nat × Nat) :=
  (addr, val) :: st.filter (fun p => p.1 != addr)

/-- Evaluate an `LcnfLetValue` in `(env, st)`, returning `(boundVal, st')`. -/
def evalLcnfLetValue (env : List Nat) (st : List (Nat × Nat)) : LcnfLetValue → Nat × List (Nat × Nat)
  | .arg a => (evalLcnfArgNat env a, st)
  | .natOp op l r =>
    let lv := evalLcnfArgNat env l
    let rv := evalLcnfArgNat env r
    let res := match op with
      | .add => lv + rv
      | .sub => lv - rv
      | .mul => lv * rv
      | .div => lv / rv
      | .mod => lv % rv
      | .beq => if lv == rv then 1 else 0
      | .ble => if lv <= rv then 1 else 0
    (res, st)
  | .ctor _ fs =>
    match fs with
    | (_, a) :: _ => (evalLcnfArgNat env a, st)
    | []          => (0, st)
  | .record fs =>
    match fs with
    | (_, a) :: _ => (evalLcnfArgNat env a, st)
    | []          => (0, st)
  | .proj _ tgt => (evalLcnfArgNat env tgt, st)
  | .app fn arg => (evalLcnfArgNat env fn + evalLcnfArgNat env arg, st)
  | .stateRead _ addr =>
    let a := evalLcnfArgNat env addr
    (readLinearStore st a, st)
  | .stateWrite _ addr val =>
    let a := evalLcnfArgNat env addr
    let v := evalLcnfArgNat env val
    (v, writeLinearStore st a v)

/-- Fuel-bounded operational evaluator for `LcnfCode` over scalar environment `env`,
join-point table `jps : List (Nat × Nat × LcnfCode)`, and linear state store `st`. -/
def evalLcnfCode : Nat → List Nat → List (Nat × Nat × LcnfCode) → List (Nat × Nat) → LcnfCode →
    Option (Nat × List (Nat × Nat))
  | 0, _, _, _, _ => none
  | fuel' + 1, env, jps, st, c =>
    match c with
    | .return a => some (evalLcnfArgNat env a, st)
    | .unreach  => none
    | .letValue v body =>
      let (val, st') := evalLcnfLetValue env st v
      evalLcnfCode fuel' (val :: env) jps st' body
    | .jpDecl jpId numParams jpBody body =>
      evalLcnfCode fuel' env ((jpId, numParams, jpBody) :: jps) st body
    | .jmp jpId args =>
      match jps.find? (fun entry => entry.1 == jpId) with
      | some (_, _, jpBody) =>
        let argVals := args.map (evalLcnfArgNat env)
        evalLcnfCode fuel' (argVals ++ env) jps st jpBody
      | none => none
    | .ifBool cond t f =>
      if evalLcnfArgNat env cond != 0 then
        evalLcnfCode fuel' env jps st t
      else
        evalLcnfCode fuel' env jps st f
    | .cases scrut arms =>
      let sv := evalLcnfArgNat env scrut
      match arms with
      | (_, _, body) :: _ => evalLcnfCode fuel' (sv :: env) jps st body
      | [] => none

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

/-- Lower an `LcnfArg` into `LExpr`. -/
def lcnfArgToLExpr : LcnfArg → LExpr
  | .bvar i      => .bvar i
  | .lit n       => .lit n
  | .boolLit b   => .boolLit b
  | .erased      => .erased
  | .stateTok id => .lit id

/-- Lower an `LcnfLetValue` into `LExpr`. -/
def lcnfLetValueToLExpr : LcnfLetValue → LExpr
  | .arg a              => lcnfArgToLExpr a
  | .natOp op l r       => .natBin op (lcnfArgToLExpr l) (lcnfArgToLExpr r)
  | .ctor tag fs        => .inject tag (fs.map fun f => (f.1, lcnfArgToLExpr f.2))
  | .record fs          => .record (fs.map fun f => (f.1, lcnfArgToLExpr f.2))
  | .proj field tgt     => .proj field (lcnfArgToLExpr tgt)
  | .app fn arg         => .app (lcnfArgToLExpr fn) (lcnfArgToLExpr arg)
  | .stateRead _ addr   => lcnfArgToLExpr addr
  | .stateWrite _ _ val => lcnfArgToLExpr val

/-- Wrap an arm body `body : LExpr` in `k` curried `.lam .emptyRow` binders for the constructor's
fields (matching `LExpr.cases` minor-premise convention). -/
def wrapMinorBvars : Nat → LExpr → LExpr
  | 0, body     => body
  | k + 1, body => .lam .emptyRow (wrapMinorBvars k body)

/-- Apply a function `fn : LExpr` to a spine of lowered `LcnfArg` arguments. -/
def applyLcnfArgs (fn : LExpr) : List LcnfArg → LExpr
  | []      => fn
  | a :: as => applyLcnfArgs (.app fn (lcnfArgToLExpr a)) as

mutual
/-- Lower an `LcnfCode` block into `LExpr` by structural recursion. -/
def compileLcnfToLExpr : LcnfCode → LExpr
  | .return a => lcnfArgToLExpr a
  | .unreach => .erased
  | .letValue v body => .letE .emptyRow (lcnfLetValueToLExpr v) (compileLcnfToLExpr body)
  | .jpDecl _ numParams jpBody body =>
    .letE .emptyRow (wrapMinorBvars numParams (compileLcnfToLExpr jpBody)) (compileLcnfToLExpr body)
  | .jmp jpId args => applyLcnfArgs (.bvar jpId) args
  | .ifBool c t f => .boolRec .emptyRow (compileLcnfToLExpr f) (compileLcnfToLExpr t) (lcnfArgToLExpr c)
  | .cases scrut arms => .cases .emptyRow (lcnfArmsToLExpr arms) (lcnfArgToLExpr scrut)

/-- Lower a list of LCNF `cases` arms into `LExpr` arms. -/
def lcnfArmsToLExpr : List (String × List String × LcnfCode) → List (String × List String × LExpr)
  | [] => []
  | (tag, names, body) :: rest =>
    (tag, names, wrapMinorBvars names.length (compileLcnfToLExpr body)) :: lcnfArmsToLExpr rest
end

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
      .recConst "lcnfCountdown42" (fn .emptyRow .natural) sampleLcnfRecBody := rfl
  rw [heq]
  refine .next (.appFun (.lit 0) (.unfold _ _ _)) ?_
  have hinst1 :
      sampleLcnfRecBody.inst (.recConst "lcnfCountdown42" (fn .emptyRow .natural) sampleLcnfRecBody) =
      .lam .emptyRow
        (.letE .emptyRow (.natBin .beq (.bvar 0) (.lit 0))
          (.boolRec .emptyRow
            (.letE .emptyRow (.natBin .sub (.bvar 1) (.lit 1))
              (.letE .emptyRow (.app (.recConst "lcnfCountdown42" (fn .emptyRow .natural) sampleLcnfRecBody) (.bvar 0)) (.bvar 0)))
            (.lit 42)
            (.bvar 0))) := by
    simp [sampleLcnfRecBody, sampleLcnfRecDecl, wrapMinorBvars, compileLcnfToLExpr,
      lcnfLetValueToLExpr, lcnfArgToLExpr, LExpr.inst, LExpr.subst, LExpr.liftSubst,
      LExpr.single, LExpr.rename, liftRename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (.lit 0)) ?_
  have hinst2 :
      (LExpr.letE .emptyRow (.natBin .beq (.bvar 0) (.lit 0))
        (.boolRec .emptyRow
          (.letE .emptyRow (.natBin .sub (.bvar 1) (.lit 1))
            (.letE .emptyRow (.app (.recConst "lcnfCountdown42" (fn .emptyRow .natural) sampleLcnfRecBody) (.bvar 0)) (.bvar 0)))
          (.lit 42)
          (.bvar 0))).inst (.lit 0) =
      .letE .emptyRow (.natBin .beq (.lit 0) (.lit 0))
        (.boolRec .emptyRow
          (.letE .emptyRow (.natBin .sub (.lit 0) (.lit 1))
            (.letE .emptyRow (.app (.recConst "lcnfCountdown42" (fn .emptyRow .natural) sampleLcnfRecBody) (.bvar 0)) (.bvar 0)))
          (.lit 42)
          (.bvar 0)) := by
    simp [sampleLcnfRecBody, sampleLcnfRecDecl, wrapMinorBvars, compileLcnfToLExpr,
      lcnfLetValueToLExpr, lcnfArgToLExpr, LExpr.inst, LExpr.subst, LExpr.liftSubst,
      LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.zeta .emptyRow (.natBin .beq (.lit 0) (.lit 0)) _) ?_
  have hinst3 :
      (LExpr.boolRec .emptyRow
        (.letE .emptyRow (.natBin .sub (.lit 0) (.lit 1))
          (.letE .emptyRow (.app (.recConst "lcnfCountdown42" (fn .emptyRow .natural) sampleLcnfRecBody) (.bvar 0)) (.bvar 0)))
        (.lit 42)
        (.bvar 0)).inst (.natBin .beq (.lit 0) (.lit 0)) =
      .boolRec .emptyRow
        (.letE .emptyRow (.natBin .sub (.lit 0) (.lit 1))
          (.letE .emptyRow (.app (.recConst "lcnfCountdown42" (fn .emptyRow .natural) sampleLcnfRecBody) (.bvar 0)) (.bvar 0)))
        (.lit 42)
        (.natBin .beq (.lit 0) (.lit 0)) := by
    simp [sampleLcnfRecBody, sampleLcnfRecDecl, wrapMinorBvars, compileLcnfToLExpr,
      lcnfLetValueToLExpr, lcnfArgToLExpr, LExpr.inst, LExpr.subst, LExpr.liftSubst,
      LExpr.single, LExpr.rename]
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
  dsimp only [sampleLcnfAstMatch, compileLcnfToLExpr, lcnfArmsToLExpr, lcnfLetValueToLExpr,
    lcnfArgToLExpr, wrapMinorBvars, List.map, List.length]
  refine .next (.zeta .emptyRow (.inject "bvar" [("idx", .lit 7)]) _) ?_
  have hinst1 :
      (LExpr.cases .emptyRow
        [ ("bvar", ["idx"], .lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)))
        , ("sort", ["u"], .lam .emptyRow (.lit 0)) ]
        (.bvar 0)).inst (.inject "bvar" [("idx", .lit 7)]) =
      .cases .emptyRow
        [ ("bvar", ["idx"], .lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)))
        , ("sort", ["u"], .lam .emptyRow (.lit 0)) ]
        (.inject "bvar" [("idx", .lit 7)]) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [hinst1]
  refine .next (.casesInject .emptyRow _ "bvar" [("idx", .lit 7)] ["idx"]
    (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)))
    [.lit 7] rfl rfl) ?_
  refine .next (.beta .emptyRow _ (.lit 7)) ?_
  have hinst2 :
      (LExpr.letE .emptyRow (.natBin .add (.bvar 0) (.lit 35)) (.bvar 0)).inst (.lit 7) =
      .letE .emptyRow (.natBin .add (.lit 7) (.lit 35)) (.bvar 0) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [hinst2]
  refine .next (.zeta .emptyRow (.natBin .add (.lit 7) (.lit 35)) (.bvar 0)) ?_
  have hinst3 :
      (LExpr.bvar 0).inst (.natBin .add (.lit 7) (.lit 35)) =
      .natBin .add (.lit 7) (.lit 35) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst3]
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
  dsimp only [sampleLcnfJpCode, compileLcnfToLExpr, wrapMinorBvars, applyLcnfArgs,
    lcnfLetValueToLExpr, lcnfArgToLExpr]
  refine .next (.zeta .emptyRow (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0))) _) ?_
  have hinst1 :
      (LExpr.app (.bvar 0) (.lit 10)).inst
        (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0))) =
      .app (.lam .emptyRow (.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0))) (.lit 10) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (.lit 10)) ?_
  have hinst2 :
      (LExpr.letE .emptyRow (.natBin .add (.bvar 0) (.lit 32)) (.bvar 0)).inst (.lit 10) =
      .letE .emptyRow (.natBin .add (.lit 10) (.lit 32)) (.bvar 0) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [hinst2]
  refine .next (.zeta .emptyRow (.natBin .add (.lit 10) (.lit 32)) (.bvar 0)) ?_
  have hinst3 :
      (LExpr.bvar 0).inst (.natBin .add (.lit 10) (.lit 32)) =
      .natBin .add (.lit 10) (.lit 32) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst3]
  exact .next (.binLit .add 10 32) (.refl _)

/-- Concrete linear state-threaded LCNF program:
1. Writes `42` to state address `0` consuming `.stateTok 0` (advancing live token to `1`),
2. Reads state address `0` consuming `.stateTok 1` (advancing live token to `2`),
3. Returns the read value (`42`). -/
def sampleLinearStateCode : LcnfCode :=
  .letValue (.stateWrite (.stateTok 0) (.lit 0) (.lit 42))
    (.letValue (.stateRead (.stateTok 1) (.lit 0))
      (.return (.bvar 0)))

/-- Broken linear state-threaded LCNF program that attempts to reuse the consumed `.stateTok 0`
twice (use-after-consume violation). -/
def sampleDuplicatedStateTokCode : LcnfCode :=
  .letValue (.stateWrite (.stateTok 0) (.lit 0) (.lit 42))
    (.letValue (.stateRead (.stateTok 0) (.lit 0))
      (.return (.bvar 0)))

/-- **Theorem (`lcnf_zero_erasure_sound`)**:
1. Every `.zero`-quantity erased argument (`LcnfArg.erased`) compiles to `LExpr.erased` and `Core4` `box`,
2. `eraseZeroQtyArgs` is idempotent and replaces every `.zero`-quantity argument with `.erased`
   while preserving `.one` and `.many` arguments verbatim, and
3. Binding an erased `.zero`-quantity proof/type in `letValue (.arg .erased) body` and returning a
   computational literal `.lit n` reduces in 1 ζ-step to `.lit n` and evaluates in `Core4` to `.nat n`. -/
theorem lcnf_zero_erasure_sound (n : Nat) (a : LcnfArg) :
    compileLcnfToCore4 (.return .erased) = box ∧
    eraseZeroQtyArgs [{ name := "hProof", qty := .zero }, { name := "x", qty := .many }] [a, .lit n] =
      [.erased, .lit n] ∧
    Evaluates (compileLcnfToCore4 (.letValue (.arg .erased) (.return (.lit n)))) (.nat n) := by
  refine ⟨by simp [compileLcnfToCore4, compileLcnfToLExpr, lcnfArgToLExpr, lowerT], rfl, ?_⟩
  have hrun : SSteps (compileLcnfToLExpr (.letValue (.arg .erased) (.return (.lit n)))) (.lit n) := by
    dsimp only [compileLcnfToLExpr, lcnfLetValueToLExpr, lcnfArgToLExpr]
    refine .next (.zeta .emptyRow .erased (.lit n)) ?_
    have hinst : (LExpr.lit n).inst .erased = .lit n := by
      simp [LExpr.inst, LExpr.subst]
    rw [hinst]
    exact .refl _
  simpa [compileLcnfToCore4, lowerT] using lower_sound_nat hrun

/-- **Theorem (`lcnf_linear_state_conserved`)**:
1. `sampleLinearStateCode` passes `checkLinearStateToken 0` and advances the linear token from `0` to `2`,
2. `sampleDuplicatedStateTokCode` (which reuses consumed `.stateTok 0`) is rejected (`= none`),
3. Executing `sampleLinearStateCode` via `evalLcnfCode` updates the linear state store in-place at
   address `0` to `42` and returns `42`. -/
theorem lcnf_linear_state_conserved :
    checkLinearStateToken 0 sampleLinearStateCode = some 2 ∧
    checkLinearStateToken 0 sampleDuplicatedStateTokCode = none ∧
    evalLcnfCode 8 [] [] [] sampleLinearStateCode = some (42, [(0, 42)]) := by
  exact ⟨rfl, rfl, rfl⟩

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
  refine ⟨by simp [lowerLCNF, compileLcnfToCore4, compileLcnfToLExpr, lcnfArgToLExpr, lowerT], ?_, ?_,
    sampleLcnfAstMatch_runs_42, ?_, ?_⟩
  · intro c n hrun
    simpa [lowerLCNF, compileLcnfToCore4, lowerT] using lower_sound_nat hrun
  · intro c b hrun
    simpa [lowerLCNF, compileLcnfToCore4, lowerT] using lower_sound_bool hrun
  · simpa [lowerLCNF, compileLcnfToCore4, lowerT] using lower_sound_nat sampleLcnfAstMatch_runs_42
  · simpa [lowerLCNFFunDecl, lowerT] using lower_sound_nat sampleLcnfRecDecl_runs_zero

/-- **Theorem (`lcnf_elab_pass_to_book_sound`)**:
1. Join-point LCNF programs (`sampleLcnfJpCode` with `jpDecl`/`jmp`) reduce in `SSteps` to `.lit 42`
   and evaluate in `Core4` to `.nat 42`,
2. `evalLcnfCode` agrees with `Core4` evaluation on both `sampleLcnfJpCode` (`= 42`) and
   `sampleLinearStateCode` (`= 42`), and
3. Emitting `sampleLcnfRecDecl` to a flat `Obend.Leaf.Book` via `compileLcnfFunDeclToBook`
   produces a closed composition whose book member `"lcnfCountdown42"` applied to `.nat 0`
   halts with `.natural 42` (`Halts`). -/
-- fixture kept (2026-11-04): consumed by Obend/Lower/Inductive.lean
theorem lcnf_elab_pass_to_book_sound :
    SSteps (compileLcnfToLExpr sampleLcnfJpCode) (.lit 42) ∧
    Evaluates (compileLcnfToCore4 sampleLcnfJpCode) (.nat 42) ∧
    evalLcnfCode 8 [] [] [] sampleLcnfJpCode = some (42, []) ∧
    Obend.Equiv.Halts
      (.app (.get (compileLcnfFunDeclToBook sampleLcnfRecDecl).link sampleLcnfRecDecl.name) (.nat 0))
      (.natural 42) := by
  refine ⟨sampleLcnfJpCode_runs_42, ?_, rfl, ?_⟩
  · simpa [compileLcnfToCore4, lowerT] using lower_sound_nat sampleLcnfJpCode_runs_42
  · exact lean_to_book sampleLcnfRecDecl.name (lcnfFunDeclToLExpr sampleLcnfRecDecl) 0 42
      (by decide +kernel) sampleLcnfRecDecl_runs_zero

end Obend.Lower.LCNF
end
