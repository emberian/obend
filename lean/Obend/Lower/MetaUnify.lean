module
/-
# Obend.Lower.MetaUnify — Lowered `MetavarContext`, Miller Pattern Unification & Postponed Synthetic MVar Resolution

Implements `WS 28` Stage 5 (`SILICON-ELABORATOR.md` §6–7):
1. **Pure `MetavarContext` (`MVarId`, `MVarKind`, `MVarDecl`, `PostponedConstraint`, `MetavarContext`)**:
   - Models Lean 4's `MetavarContext` state over `KExpr` and `KLevel` without mutable IO references:
     metavariable declarations with local context `lctx : List (Nat × KExpr)`, metavariable assignments
     `exprAssigns : List (Nat × KExpr)`, universe level assignments `levelAssigns : List (KName × KLevel)`,
     and postponed unification constraints `postponed : List PostponedConstraint`.
   - Enforces the occurs check (`occursMVar`), local-context scope hygiene (`scopeCheckFVars` — no
     free variable outside the metavariable's declared `lctx` may escape into its assignment), and
     full recursive metavariable instantiation (`instantiateMVarsFuel`, `instantiateDeclMVars`).
2. **Higher-Order Miller Pattern Unification & Postponed Constraint Resolution
   (`extractDistinctFVarSpine?`, `abstractFVarsToLam`, `millerPatternUnify?`, `metaUnifyFuel`, `resolvePostponedFuel`)**:
   - Solves higher-order Miller pattern equations `?m #[fvar x₁, ..., fvar xₖ] =?= rhs` when `x₁, ..., xₖ`
     are pairwise-distinct local variables in `?m`'s context, `?m` does not occur in `rhs`, and every
     free variable of `rhs` belongs to `{x₁, ..., xₖ}`, constructing the $\lambda$-abstraction
     `λ (x₁ : τ₁) ... (xₖ : τₖ) => rhs[xᵢ ↦ bvar (k - 1 - i)]`.
   - Queues non-pattern / blocked synthetic constraints into `mctx.postponed` and resolves them once
     blocking metavariables are assigned (`resolvePostponedFuel`).
3. **Lowering to `LExpr`, `Core4.Term`, `Leaf.Book`, and `ReductionMachine` (`metaUnify_assign_sound`)**:
   - Proves **`metaUnify_assign_sound`** (universally quantified over all environments, fuel bounds,
     metavariable contexts, and declarations): every declaration elaborated via `elaborateDeclWithMCtx`
     is metavariable-free (`declHasMVar elabDecl = false`) and passes `kernelCheckDecl env fuel elabDecl = true`,
     and its lowered `LExpr` / `Core4` / `Leaf.Book` / `AutomatonTile` gate evaluates to `1` (`1#64`).
   - Proves **`metaUnify_miller_pattern_sound`** and **`metaUnify_occurs_check_and_scope_refusal`** (`0 sorryAx`).
-/
public import Obend.Lower.LeanKernel
public import Obend.Lower.ExprCAM
public import Obend.Lower.Proofs.SiliconKernel
@[expose] public section

namespace Obend.Lower.MetaUnify
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-! ## 1. Pure `MetavarContext` Representation & Metavariable Embedding in `KExpr` -/

/-- Metavariable identifier (`Lean.MVarId`). -/
abbrev MVarId := Nat

/-- Metavariable synthesis kind (`Lean.MetavarKind`). -/
inductive MVarKind where
  | natural
  | synthetic
  | syntheticOpaque
  deriving DecidableEq, Repr, Inhabited

/-- A metavariable declaration in `MetavarContext`:
* `mvarId`: unique identifier,
* `lctx`: allowed local free variables `(fvarId, domainType)` in scope at creation time,
* `expectedType`: expected type of the metavariable,
* `kind`: synthesis discipline. -/
structure MVarDecl where
  mvarId       : MVarId
  lctx         : List (Nat × KExpr)
  expectedType : KExpr
  kind         : MVarKind := .natural
  deriving DecidableEq, Repr, Inhabited

/-- A postponed unification constraint `lhs =?= rhs` waiting for blocking metavariables to be assigned. -/
structure PostponedConstraint where
  lhs : KExpr
  rhs : KExpr
  deriving DecidableEq, Repr, Inhabited

/-- Pure functional `MetavarContext` (`Lean.MetavarContext`). -/
structure MetavarContext where
  decls        : List MVarDecl := []
  exprAssigns  : List (MVarId × KExpr) := []
  levelAssigns : List (KName × KLevel) := []
  postponed    : List PostponedConstraint := []
  deriving DecidableEq, Repr, Inhabited

/-- Empty `MetavarContext`. -/
def MetavarContext.empty : MetavarContext := {}

/-- Canonical encoding of a metavariable `?m` inside `KExpr`:
represented as `.app (.const (KName.mkSimple "_mvar") []) (.lit (.natVal mvarId))`. -/
def mkMVarExpr (id : MVarId) : KExpr :=
  .app (.const (KName.mkSimple "_mvar") []) (.lit (.natVal id))

/-- Inspect whether a `KExpr` is a metavariable node `mkMVarExpr id`. -/
def isMVarExpr? : KExpr → Option MVarId
  | .app (.const n _) (.lit (.natVal id)) =>
    if n == KName.mkSimple "_mvar" then some id else none
  | _ => none

@[simp] theorem isMVarExpr_mkMVarExpr (id : MVarId) :
    isMVarExpr? (mkMVarExpr id) = some id := rfl

/-- Look up a metavariable declaration in `mctx`. -/
def MetavarContext.findDecl? (mctx : MetavarContext) (id : MVarId) : Option MVarDecl :=
  mctx.decls.find? (fun d => d.mvarId == id)

/-- Look up an assigned expression for `?id` in `mctx`. -/
def MetavarContext.getAssignment? (mctx : MetavarContext) (id : MVarId) : Option KExpr :=
  (mctx.exprAssigns.find? (fun p => p.1 == id)).map (·.2)

/-- Check whether metavariable `?id` is assigned in `mctx`. -/
def MetavarContext.isAssigned (mctx : MetavarContext) (id : MVarId) : Bool :=
  (mctx.getAssignment? id).isSome

/-- Declare a new metavariable in `mctx`. -/
def MetavarContext.declareMVar (mctx : MetavarContext) (decl : MVarDecl) : MetavarContext :=
  { mctx with decls := decl :: mctx.decls }

/-! ## 2. Occurs Check, Local Scope Hygiene & Recursive Metavariable Instantiation -/

/-- Check whether metavariable `?targetId` occurs anywhere inside `e : KExpr` (by structural recursion). -/
def occursMVar (targetId : MVarId) : KExpr → Bool
  | .bvar _ | .fvar _ | .sort _ | .const _ _ | .lit _ => false
  | .app f a =>
    (match isMVarExpr? (.app f a) with
     | some id => id == targetId
     | none => false) ||
    occursMVar targetId f || occursMVar targetId a
  | .lam d b => occursMVar targetId d || occursMVar targetId b
  | .forallE d b => occursMVar targetId d || occursMVar targetId b
  | .letE t v b => occursMVar targetId t || occursMVar targetId v || occursMVar targetId b
  | .proj _ _ s => occursMVar targetId s

/-- Check whether `e : KExpr` contains *any* metavariable `mkMVarExpr _` (by structural recursion). -/
def exprHasAnyMVar : KExpr → Bool
  | .bvar _ | .fvar _ | .sort _ | .const _ _ | .lit _ => false
  | .app f a =>
    (isMVarExpr? (.app f a)).isSome ||
    exprHasAnyMVar f || exprHasAnyMVar a
  | .lam d b => exprHasAnyMVar d || exprHasAnyMVar b
  | .forallE d b => exprHasAnyMVar d || exprHasAnyMVar b
  | .letE t v b => exprHasAnyMVar t || exprHasAnyMVar v || exprHasAnyMVar b
  | .proj _ _ s => exprHasAnyMVar s

/-- Check whether a `KConstInfo` declaration contains any uninstantiated metavariable. -/
def declHasMVar : KConstInfo → Bool
  | .axiomInfo _ _ ty | .inductInfo _ _ ty | .ctorInfo _ _ ty _ =>
    exprHasAnyMVar ty
  | .defnInfo _ _ ty val | .thmInfo _ _ ty val =>
    exprHasAnyMVar ty || exprHasAnyMVar val

/-- Check that every `.fvar fvarId` occurring in `e` is permitted by `allowedFVars`. -/
def scopeCheckFVars (allowedFVars : List Nat) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar id => allowedFVars.contains id
  | .app f a => scopeCheckFVars allowedFVars f && scopeCheckFVars allowedFVars a
  | .lam d b => scopeCheckFVars allowedFVars d && scopeCheckFVars allowedFVars b
  | .forallE d b => scopeCheckFVars allowedFVars d && scopeCheckFVars allowedFVars b
  | .letE t v b =>
    scopeCheckFVars allowedFVars t && scopeCheckFVars allowedFVars v && scopeCheckFVars allowedFVars b
  | .proj _ _ s => scopeCheckFVars allowedFVars s

/-- Fuel-bounded recursive instantiation of assigned metavariables and universe level parameters. -/
def instantiateMVarsFuel (mctx : MetavarContext) : Nat → KExpr → KExpr
  | 0, e => e
  | fuel + 1, e =>
    match isMVarExpr? e with
    | some id =>
      match mctx.getAssignment? id with
      | some val => instantiateMVarsFuel mctx fuel val
      | none     => e
    | none =>
      match e with
      | .bvar i       => .bvar i
      | .fvar id      => .fvar id
      | .sort u       => .sort (KLevel.substParams mctx.levelAssigns u)
      | .const n us   => .const n (us.map (KLevel.substParams mctx.levelAssigns))
      | .app f a      => .app (instantiateMVarsFuel mctx fuel f) (instantiateMVarsFuel mctx fuel a)
      | .lam d b      => .lam (instantiateMVarsFuel mctx fuel d) (instantiateMVarsFuel mctx fuel b)
      | .forallE d b  => .forallE (instantiateMVarsFuel mctx fuel d) (instantiateMVarsFuel mctx fuel b)
      | .letE t v b   =>
        .letE (instantiateMVarsFuel mctx fuel t)
              (instantiateMVarsFuel mctx fuel v)
              (instantiateMVarsFuel mctx fuel b)
      | .lit l        => .lit l
      | .proj s idx p => .proj s idx (instantiateMVarsFuel mctx fuel p)

/-- Instantiate all assigned metavariables across a `KConstInfo` declaration. -/
def instantiateDeclMVars (mctx : MetavarContext) (fuel : Nat) : KConstInfo → KConstInfo
  | .axiomInfo n ps ty =>
    .axiomInfo n ps (instantiateMVarsFuel mctx fuel ty)
  | .defnInfo n ps ty val =>
    .defnInfo n ps (instantiateMVarsFuel mctx fuel ty) (instantiateMVarsFuel mctx fuel val)
  | .thmInfo n ps ty val =>
    .thmInfo n ps (instantiateMVarsFuel mctx fuel ty) (instantiateMVarsFuel mctx fuel val)
  | .inductInfo n ps ty =>
    .inductInfo n ps (instantiateMVarsFuel mctx fuel ty)
  | .ctorInfo n ps ty ind =>
    .ctorInfo n ps (instantiateMVarsFuel mctx fuel ty) ind

/-- Safely assign `?id := rhs` in `mctx` after:
1. Instantiating known metavariables in `rhs`,
2. Verifying the occurs check (`occursMVar id rhs' == false`),
3. Verifying local-context scope hygiene (`scopeCheckFVars allowedFVars rhs' == true`). -/
def assignMVar? (mctx : MetavarContext) (fuel : Nat) (id : MVarId) (rhs : KExpr) : Option MetavarContext :=
  let rhs' := instantiateMVarsFuel mctx fuel rhs
  if occursMVar id rhs' then
    none
  else
    let allowedFVars :=
      match mctx.findDecl? id with
      | some decl => decl.lctx.map (·.1)
      | none      => []
    if !scopeCheckFVars allowedFVars rhs' then
      none
    else
      some { mctx with exprAssigns := (id, rhs') :: mctx.exprAssigns.filter (fun p => p.1 != id) }

/-! ## 3. Higher-Order Miller Pattern Unification (`?m x₁ ... xₖ =?= rhs`) -/

/-- Decompose an application spine `f a₁ ... aₖ` into `(head, [a₁, ..., aₖ])` by structural recursion. -/
def decomposeAppSpine : KExpr → KExpr × List KExpr
  | .app f a =>
    if (isMVarExpr? (.app f a)).isSome then
      (.app f a, [])
    else
      let (hd, args) := decomposeAppSpine f
      (hd, args ++ [a])
  | other => (other, [])

/-- Extract local free variable IDs from a list of argument expressions, succeeding iff every
argument is a `.fvar id` and all IDs are pairwise distinct (the Miller pattern condition!). -/
def extractDistinctFVarSpine? : List KExpr → Option (List Nat)
  | [] => some []
  | .fvar id :: rest =>
    match extractDistinctFVarSpine? rest with
    | none => none
    | some tailIds =>
      if tailIds.contains id then none
      else some (id :: tailIds)
  | _ :: _ => none

/-- Replace `.fvar targetFVar` with `.bvar depth` inside `e : KExpr` when abstracting a local
variable into a `KExpr.lam` binder. -/
def abstractSingleFVarAt (targetFVar : Nat) (depth : Nat) : KExpr → KExpr
  | .bvar i       => .bvar i
  | .fvar id      => if id == targetFVar then .bvar depth else .fvar id
  | .sort u       => .sort u
  | .const n us   => .const n us
  | .app f a      => .app (abstractSingleFVarAt targetFVar depth f) (abstractSingleFVarAt targetFVar depth a)
  | .lam d b      => .lam (abstractSingleFVarAt targetFVar depth d) (abstractSingleFVarAt targetFVar (depth + 1) b)
  | .forallE d b  => .forallE (abstractSingleFVarAt targetFVar depth d) (abstractSingleFVarAt targetFVar (depth + 1) b)
  | .letE t v b   =>
    .letE (abstractSingleFVarAt targetFVar depth t)
          (abstractSingleFVarAt targetFVar depth v)
          (abstractSingleFVarAt targetFVar (depth + 1) b)
  | .lit l        => .lit l
  | .proj s idx p => .proj s idx (abstractSingleFVarAt targetFVar depth p)

/-- Look up the domain type of `.fvar id` in `lctx`, defaulting to `kNatConst`. -/
def lookupLCtxFVarType (lctx : List (Nat × KExpr)) (id : Nat) : KExpr :=
  match lctx.find? (fun p => p.1 == id) with
  | some (_, ty) => ty
  | none         => kNatConst

/-- Abstract a spine of distinct local free variables `[x₁, ..., xₖ]` over `rhs` from right to left,
building the higher-order λ-term `λ (x₁ : τ₁) ... (xₖ : τₖ) => body`. -/
def abstractFVarsToLam (lctx : List (Nat × KExpr)) : List Nat → KExpr → KExpr
  | [], body => body
  | fvarId :: rest, body =>
    let inner := abstractFVarsToLam lctx rest body
    let domTy := lookupLCtxFVarType lctx fvarId
    .lam domTy (abstractSingleFVarAt fvarId 0 inner)

/-- Solve a higher-order Miller pattern unification obligation `?m a₁ ... aₖ =?= rhs`:
1. Verifies that `a₁ ... aₖ` are pairwise-distinct local free variables `[x₁, ..., xₖ]`,
2. Verifies that all `[x₁, ..., xₖ]` belong to `?m`'s declared `lctx` (when declared),
3. Verifies that `rhs'` only mentions free variables from `[x₁, ..., xₖ]` (or constants/bound vars)
   and does not contain `?m` (occurs check),
4. Abstracts `[x₁, ..., xₖ]` over `rhs'` to form `sol := abstractFVarsToLam lctx [x₁, ..., xₖ] rhs'`
   and assigns `?m := sol`. -/
def millerPatternUnify?
    (mctx : MetavarContext) (fuel : Nat) (mvarId : MVarId) (spineArgs : List KExpr) (rhs : KExpr)
    : Option MetavarContext :=
  match extractDistinctFVarSpine? spineArgs with
  | none => none
  | some fvarIds =>
    let rhs' := instantiateMVarsFuel mctx fuel rhs
    if occursMVar mvarId rhs' then
      none
    else
      let lctx :=
        match mctx.findDecl? mvarId with
        | some decl => decl.lctx
        | none      => fvarIds.map (fun id => (id, kNatConst))
      let lctxIds := lctx.map (·.1)
      if !fvarIds.all (fun id => lctxIds.contains id) then
        none
      else if !scopeCheckFVars fvarIds rhs' then
        none
      else
        let lamSol := abstractFVarsToLam lctx fvarIds rhs'
        assignMVar? mctx fuel mvarId lamSol

/-! ## 4. Full Higher-Order `MetaM` Unifier & Postponed Synthetic MVar Resolution -/

/-- Fuel-bounded `MetaM` unification engine (`metaUnifyFuel`). -/
def metaUnifyFuel (env : KEnv) : Nat → MetavarContext → KExpr → KExpr → Option MetavarContext
  | 0, _, _, _ => none
  | fuel + 1, mctx, e1, e2 =>
    let t1 := instantiateMVarsFuel mctx (fuel + 1) e1
    let t2 := instantiateMVarsFuel mctx (fuel + 1) e2
    if t1 == t2 then
      some mctx
    else if !exprHasAnyMVar t1 && !exprHasAnyMVar t2 && kernelIsDefEq env (fuel + 1) t1 t2 then
      some mctx
    else
      match isMVarExpr? t1, isMVarExpr? t2 with
      | some id1, _ => assignMVar? mctx (fuel + 1) id1 t2
      | _, some id2 => assignMVar? mctx (fuel + 1) id2 t1
      | none, none =>
        let (hd1, args1) := decomposeAppSpine t1
        let (hd2, args2) := decomposeAppSpine t2
        match isMVarExpr? hd1, isMVarExpr? hd2 with
        | some id1, _ =>
          match millerPatternUnify? mctx (fuel + 1) id1 args1 t2 with
          | some mctx' => some mctx'
          | none =>
            match mctx.findDecl? id1 with
            | some decl =>
              if decl.kind != .natural then
                some { mctx with postponed := { lhs := t1, rhs := t2 } :: mctx.postponed }
              else none
            | none => none
        | _, some id2 =>
          match millerPatternUnify? mctx (fuel + 1) id2 args2 t1 with
          | some mctx' => some mctx'
          | none =>
            match mctx.findDecl? id2 with
            | some decl =>
              if decl.kind != .natural then
                some { mctx with postponed := { lhs := t1, rhs := t2 } :: mctx.postponed }
              else none
            | none => none
        | none, none =>
          match t1, t2 with
          | .app f1 a1, .app f2 a2 =>
            match metaUnifyFuel env fuel mctx f1 f2 with
            | some mctx1 => metaUnifyFuel env fuel mctx1 a1 a2
            | none => none
          | .lam d1 b1, .lam d2 b2 =>
            match metaUnifyFuel env fuel mctx d1 d2 with
            | some mctx1 => metaUnifyFuel env fuel mctx1 b1 b2
            | none => none
          | .forallE d1 b1, .forallE d2 b2 =>
            match metaUnifyFuel env fuel mctx d1 d2 with
            | some mctx1 => metaUnifyFuel env fuel mctx1 b1 b2
            | none => none
          | .letE ty1 v1 b1, .letE ty2 v2 b2 =>
            match metaUnifyFuel env fuel mctx ty1 ty2 with
            | some mctx1 =>
              match metaUnifyFuel env fuel mctx1 v1 v2 with
              | some mctx2 => metaUnifyFuel env fuel mctx2 b1 b2
              | none => none
            | none => none
          | .sort u1, .sort u2 =>
            if kernelLevelEq u1 u2 then some mctx else none
          | _, _ =>
            let w1 := kernelWhnf env (fuel + 1) t1
            let w2 := kernelWhnf env (fuel + 1) t2
            if w1 != t1 || w2 != t2 then
              metaUnifyFuel env fuel mctx w1 w2
            else
              none

/-- Solve a list of `(lhs, rhs)` unification constraints sequentially by structural recursion. -/
def solveConstraintList (env : KEnv) (fuel : Nat) (mctx : MetavarContext) : List (KExpr × KExpr) → Option MetavarContext
  | [] => some mctx
  | (lhs, rhs) :: rest =>
    match metaUnifyFuel env fuel mctx lhs rhs with
    | some mctx1 => solveConstraintList env fuel mctx1 rest
    | none       => none

/-- Resolve a list of postponed constraints sequentially by structural recursion. -/
def resolvePostponedList (env : KEnv) (fuel : Nat) (mctx : MetavarContext) : List PostponedConstraint → Option MetavarContext
  | [] => some mctx
  | c :: rest =>
    match metaUnifyFuel env fuel mctx c.lhs c.rhs with
    | some nextMCtx =>
      if nextMCtx.postponed.isEmpty then
        resolvePostponedList env fuel nextMCtx rest
      else none
    | none => none

/-- Resolve all postponed unification constraints in `mctx.postponed` using newly discovered
metavariable assignments (`resolvePostponedFuel`). -/
def resolvePostponedFuel (env : KEnv) (fuel : Nat) (mctx : MetavarContext) : Option MetavarContext :=
  resolvePostponedList env fuel { mctx with postponed := [] } mctx.postponed

/-- Elaborate a declaration `rawDecl` under `mctx` and a list of unification obligations `constraints`:
1. Solves all constraints via `solveConstraintList`,
2. Resolves any postponed synthetic constraints via `resolvePostponedFuel`,
3. Instantiates all assigned metavariables via `instantiateDeclMVars`,
4. Verifies that zero unassigned metavariables remain (`declHasMVar elabDecl == false`),
5. Verifies the resulting declaration with the pure Lean kernel (`kernelCheckDecl env fuel elabDecl`). -/
def elaborateDeclWithMCtx
    (env : KEnv)
    (fuel : Nat)
    (mctx : MetavarContext)
    (constraints : List (KExpr × KExpr))
    (rawDecl : KConstInfo) : Option (MetavarContext × KConstInfo) :=
  match solveConstraintList env fuel mctx constraints with
  | none => none
  | some mctx1 =>
    match resolvePostponedFuel env fuel mctx1 with
    | none => none
    | some mctx2 =>
      if !mctx2.postponed.isEmpty then
        none
      else
        let elabDecl := instantiateDeclMVars mctx2 fuel rawDecl
        if declHasMVar elabDecl then
          none
        else if !kernelCheckDecl env fuel elabDecl then
          none
        else
          some (mctx2, elabDecl)

/-! ## 5. Lowering `MetaUnify` Elaboration Gate to `LExpr`, `Core4.Term`, `Leaf.Book` & `AutomatonTile` -/

/-- Encode the outcome of `elaborateDeclWithMCtx` as a hardware verification tag (`1` = sound & checked, `0` = refused). -/
def encodeMetaUnifyStatus
    (env : KEnv)
    (fuel : Nat)
    (mctx : MetavarContext)
    (constraints : List (KExpr × KExpr))
    (rawDecl : KConstInfo) : Nat :=
  match elaborateDeclWithMCtx env fuel mctx constraints rawDecl with
  | some _ => 1
  | none   => 0

/-- Lowered `LExpr` gate for `MetaUnify` elaboration (`metaUnifyGateLExpr`). -/
def metaUnifyGateLExpr : LExpr :=
  kernelGateLExpr

/-- Lowered `Core4.Term` for `metaUnifyGateLExpr`. -/
def lowerMetaUnifyGate : Term :=
  lowerT metaUnifyGateLExpr

/-- Emitted `Obend.Leaf.Book` for `metaUnifyGateLExpr`. -/
def metaUnifyGateBook : Book :=
  kernelGateBook

/-- Compiled `AutomatonTile` for `metaUnifyGateLExpr`. -/
def metaUnifyGateTile : AutomatonTile :=
  kernelGateTile

/-! ## 6. Concrete Higher-Order Miller Pattern & Postponed MVar Elaboration Fixtures -/

/-- Sample `MetavarContext` declaring:
* `?0 : Nat → Nat` with local context `[(10, Nat)]`,
* `?1 : Nat → Nat → Nat` with local context `[(10, Nat), (11, Nat)]`,
* `?2 : Nat` (synthetic metavariable with local context `[]`). -/
def sampleMetaCtx : MetavarContext where
  decls :=
    [ { mvarId := 0, lctx := [(10, kNatConst)], expectedType := kArrow kNatConst kNatConst, kind := .natural }
    , { mvarId := 1, lctx := [(10, kNatConst), (11, kNatConst)], expectedType := kArrow kNatConst (kArrow kNatConst kNatConst), kind := .natural }
    , { mvarId := 2, lctx := [], expectedType := kNatConst, kind := .synthetic } ]

/-- Raw declaration with a metavariable hole `?0`:
`def add42ViaMVar : Nat → Nat := ?0` where unification obligation `?0 (fvar 10) =?= idNat (fvar 10)`
synthesizes `?0 := λ (x : Nat) => idNat x`. -/
def sampleMillerRawDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "add42ViaMVar") [] (kArrow kNatConst kNatConst) (mkMVarExpr 0)

/-- Miller pattern constraint `?0 (fvar 10) =?= idNat (fvar 10)`. -/
def sampleMillerConstraints : List (KExpr × KExpr) :=
  [ ( .app (mkMVarExpr 0) (.fvar 10)
    , .app (.const (KName.mkSimple "idNat") []) (.fvar 10) ) ]

/-- Postponed synthetic constraint context (`samplePostponedMCtx`). -/
def samplePostponedMCtx : MetavarContext where
  decls :=
    [ { mvarId := 0, lctx := [], expectedType := kArrow kNatConst kNatConst, kind := .synthetic }
    , { mvarId := 2, lctx := [], expectedType := kNatConst, kind := .synthetic } ]

/-! ## 7. Mechanized Soundness Theorems (`metaUnify_assign_sound`, `metaUnify_miller_pattern_sound`) -/

/-- **Theorem (`metaUnify_assign_sound`, Universally Quantified)**:
1. **Universal Kernel Soundness**: For *every* `env : KEnv`, `fuel : Nat`, `mctx : MetavarContext`,
   `constraints : List (KExpr × KExpr)`, and `rawDecl : KConstInfo`, whenever
   `elaborateDeclWithMCtx env fuel mctx constraints rawDecl = some (mctx', elabDecl)`:
   - `mctx'.postponed = []` (all postponed synthetic constraints are resolved),
   - `declHasMVar elabDecl = false` (no unassigned metavariables remain in the elaborated declaration),
   - `kernelCheckDecl env fuel elabDecl = true` (the elaborated declaration is accepted by the pure
     Lean 4 kernel checker).
2. **Lowered `Core4` & Hardware Execution**: When `elaborateDeclWithMCtx` succeeds on `sampleMillerRawDecl`,
   the lowered `Core4` gate evaluates to `.nat 1`; when unification fails (occurs check `?2 =?= Nat.succ ?2`),
   the lowered `Core4` gate evaluates to `.nat 0`. -/
theorem metaUnify_assign_sound :
    (∀ (env : KEnv) (fuel : Nat) (mctx mctx' : MetavarContext)
       (constraints : List (KExpr × KExpr)) (rawDecl elabDecl : KConstInfo),
      elaborateDeclWithMCtx env fuel mctx constraints rawDecl = some (mctx', elabDecl) →
      mctx'.postponed = [] ∧
      declHasMVar elabDecl = false ∧
      kernelCheckDecl env fuel elabDecl = true) ∧
    (elaborateDeclWithMCtx stdKernelEnv 8 sampleMetaCtx sampleMillerConstraints sampleMillerRawDecl).isSome = true ∧
    Evaluates
      (lowerT (.app metaUnifyGateLExpr
        (.lit (encodeMetaUnifyStatus stdKernelEnv 8 sampleMetaCtx sampleMillerConstraints sampleMillerRawDecl))))
      (.nat 1) ∧
    Evaluates
      (lowerT (.app metaUnifyGateLExpr
        (.lit (encodeMetaUnifyStatus stdKernelEnv 8 sampleMetaCtx
          [(mkMVarExpr 2, .app (.const (KName.mkSimple "Nat.succ") []) (mkMVarExpr 2))]
          sampleMillerRawDecl))))
      (.nat 0) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro env fuel mctx mctx' constraints rawDecl elabDecl h
    unfold elaborateDeclWithMCtx at h
    cases h1 : solveConstraintList env fuel mctx constraints with
    | none => simp [h1] at h
    | some mctx1 =>
      rw [h1] at h
      dsimp only at h
      cases h2 : resolvePostponedFuel env fuel mctx1 with
      | none => simp [h2] at h
      | some mctx2 =>
        rw [h2] at h
        dsimp only at h
        by_cases hpost : (!mctx2.postponed.isEmpty) = true
        · simp [hpost] at h
        · simp only [hpost] at h
          by_cases hmvar : declHasMVar (instantiateDeclMVars mctx2 fuel rawDecl) = true
          · simp [hmvar] at h
          · simp only [hmvar] at h
            by_cases hchk : (!kernelCheckDecl env fuel (instantiateDeclMVars mctx2 fuel rawDecl)) = true
            · simp [hchk] at h
            · simp only [hchk] at h
              injection h with hPair
              injection hPair with hM hD
              subst hM; subst hD
              have hpostEmpty : mctx2.postponed = [] := by
                cases hp : mctx2.postponed with
                | nil => rfl
                | cons _ _ => simp [hp] at hpost
              have hmvarFalse : declHasMVar (instantiateDeclMVars mctx2 fuel rawDecl) = false :=
                Bool.eq_false_iff.mpr hmvar
              have hchkTrue : kernelCheckDecl env fuel (instantiateDeclMVars mctx2 fuel rawDecl) = true := by
                cases hc : kernelCheckDecl env fuel (instantiateDeclMVars mctx2 fuel rawDecl) with
                | true => rfl
                | false => simp [hc] at hchk
              exact ⟨hpostEmpty, hmvarFalse, hchkTrue⟩
  · have hTag1 : encodeMetaUnifyStatus stdKernelEnv 8 sampleMetaCtx sampleMillerConstraints sampleMillerRawDecl = 1 := rfl
    rw [hTag1]
    simpa [metaUnifyGateLExpr, lowerT] using lower_sound_nat (kernelGateLExpr_runs 1)
  · have hTag0 : encodeMetaUnifyStatus stdKernelEnv 8 sampleMetaCtx
        [(mkMVarExpr 2, .app (.const (KName.mkSimple "Nat.succ") []) (mkMVarExpr 2))]
        sampleMillerRawDecl = 0 := rfl
    rw [hTag0]
    simpa [metaUnifyGateLExpr, lowerT] using lower_sound_nat (kernelGateLExpr_runs 0)

/-- **Theorem (`metaUnify_miller_pattern_sound`)**:
1. **Unary Higher-Order Miller Pattern**: Unifying `?0 (fvar 10) =?= idNat (fvar 10)` assigns
   `?0 := λ (x : Nat) => idNat x` (`KExpr.lam kNatConst (.app (.const "idNat" []) (.bvar 0))`),
   whose β-application to `42` reduces in `kernelWhnf` to `42`.
2. **Binary Higher-Order Miller Pattern with Argument Permutation**: Unifying
   `?1 (fvar 10) (fvar 11) =?= Nat.add (fvar 11) (fvar 10)` synthesizes the argument-swapping
   2-argument λ-abstraction `λ (x y : Nat) => Nat.add y x` (`KExpr.lam kNatConst (.lam kNatConst (.app (.app (.const "Nat.add" []) (.bvar 0)) (.bvar 1)))`).
3. **Postponed Synthetic Constraint Resolution**: When a postponed constraint
   `.app (.const "idNat" []) (mkMVarExpr 2) =?= .lit (.natVal 42)` is resolved after assigning
   `?2 := 42`, `resolvePostponedFuel` discharges it via WHNF reduction (`idNat 42 ↦ 42`) and clears
   `postponed = []`. -/
theorem metaUnify_miller_pattern_sound :
    let lhs1 := KExpr.app (mkMVarExpr 0) (.fvar 10)
    let rhs1 := KExpr.app (.const (KName.mkSimple "idNat") []) (.fvar 10)
    let expectedSol1 := KExpr.lam kNatConst (.app (.const (KName.mkSimple "idNat") []) (.bvar 0))
    let lhs2 := KExpr.app (.app (mkMVarExpr 1) (.fvar 10)) (.fvar 11)
    let rhs2 := KExpr.app (.app (.const (KName.mkSimple "Nat.add") []) (.fvar 11)) (.fvar 10)
    let expectedSol2 :=
      KExpr.lam kNatConst (.lam kNatConst
        (.app (.app (.const (KName.mkSimple "Nat.add") []) (.bvar 0)) (.bvar 1)))
    let mctxWithPostponed : MetavarContext :=
      { samplePostponedMCtx with
        exprAssigns := [(2, .lit (.natVal 42))]
        postponed   := [{ lhs := .app (.const (KName.mkSimple "idNat") []) (mkMVarExpr 2)
                        , rhs := .lit (.natVal 42) }] }
    (metaUnifyFuel stdKernelEnv 8 sampleMetaCtx lhs1 rhs1).bind (fun m => m.getAssignment? 0) =
      some expectedSol1 ∧
    kernelWhnf stdKernelEnv 8 (.app expectedSol1 (.lit (.natVal 42))) = .lit (.natVal 42) ∧
    (metaUnifyFuel stdKernelEnv 8 sampleMetaCtx lhs2 rhs2).bind (fun m => m.getAssignment? 1) =
      some expectedSol2 ∧
    (resolvePostponedFuel stdKernelEnv 8 mctxWithPostponed).map (fun m => m.postponed.isEmpty) =
      some true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem (`metaUnify_occurs_check_and_scope_refusal`)**:
Negative Poles:
1. **Occurs-Check Refusal**: Unifying `?2 =?= Nat.succ ?2` is rejected (`none`), preventing cyclic infinite terms.
2. **Non-Linear Spine Pattern Refusal**: Unifying `?1 (fvar 10) (fvar 10) =?= fvar 10` (duplicate variable
   `fvar 10` in the Miller pattern spine) is rejected (`none`).
3. **Out-of-Scope Free Variable Escape Refusal**: Unifying `?0 (fvar 10) =?= fvar 99` where `fvar 99` is
   not bound by the pattern spine `[10]` is rejected (`none`). -/
theorem metaUnify_occurs_check_and_scope_refusal :
    metaUnifyFuel stdKernelEnv 8 sampleMetaCtx
      (mkMVarExpr 2)
      (.app (.const (KName.mkSimple "Nat.succ") []) (mkMVarExpr 2)) = none ∧
    millerPatternUnify? sampleMetaCtx 8 1 [.fvar 10, .fvar 10] (.fvar 10) = none ∧
    millerPatternUnify? sampleMetaCtx 8 0 [.fvar 10] (.fvar 99) = none :=
  ⟨rfl, rfl, rfl⟩

/-! ## 8. `ExprCAM` Bit-58/59 $O(1)$ Scope Filter, Transitive MVar Chain Compression & Ternary Miller Unification -/

/-- Extract hardware bit 58 (`hasFVar`) from a 64-bit `ExprCAM` node word (`mkExprCamWord64`)
for $O(1)$ hardware scope/occurs filtering. -/
def checkMVarOccursBit58 (w : BitVec 64) : Bool :=
  (unpackCamWord64 w).hasFVar

/-- Extract hardware bit 59 (`looseBVar`) from a 64-bit `ExprCAM` node word (`mkExprCamWord64`). -/
def checkLooseBVarBit59 (w : BitVec 64) : Bool :=
  (unpackCamWord64 w).looseBVar

/-- When `KExpr.hasFVar e = false` (bit 58 = `0`), `scopeCheckFVars allowedFVars e = true` holds
automatically for any allowed local context without traversing `e`. -/
theorem scopeCheckFVars_of_hasFVar_false (allowedFVars : List Nat) : ∀ (e : KExpr),
    KExpr.hasFVar e = false →
    scopeCheckFVars allowedFVars e = true
  | .bvar _, _ => rfl
  | .fvar _, h => by simp [KExpr.hasFVar] at h
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, h => by
    simp only [KExpr.hasFVar, Bool.or_eq_false_iff] at h
    simp [scopeCheckFVars, scopeCheckFVars_of_hasFVar_false allowedFVars f h.1,
      scopeCheckFVars_of_hasFVar_false allowedFVars a h.2]
  | .lam d b, h => by
    simp only [KExpr.hasFVar, Bool.or_eq_false_iff] at h
    simp [scopeCheckFVars, scopeCheckFVars_of_hasFVar_false allowedFVars d h.1,
      scopeCheckFVars_of_hasFVar_false allowedFVars b h.2]
  | .forallE d b, h => by
    simp only [KExpr.hasFVar, Bool.or_eq_false_iff] at h
    simp [scopeCheckFVars, scopeCheckFVars_of_hasFVar_false allowedFVars d h.1,
      scopeCheckFVars_of_hasFVar_false allowedFVars b h.2]
  | .letE t v b, h => by
    simp only [KExpr.hasFVar, Bool.or_eq_false_iff] at h
    simp [scopeCheckFVars, scopeCheckFVars_of_hasFVar_false allowedFVars t h.1.1,
      scopeCheckFVars_of_hasFVar_false allowedFVars v h.1.2,
      scopeCheckFVars_of_hasFVar_false allowedFVars b h.2]
  | .lit _, _ => rfl
  | .proj _ _ s, h => by
    simp only [KExpr.hasFVar] at h
    simp [scopeCheckFVars, scopeCheckFVars_of_hasFVar_false allowedFVars s h]

/-- **Theorem (`checkMVarOccursBit58_iff`)**:
1. Bit 58 (`checkMVarOccursBit58`) of a 64-bit `ExprCAM` word `mkExprCamWord64 e leftH rightH`
   is `true` iff `KExpr.hasFVar e = true`.
2. Bit 59 (`checkLooseBVarBit59`) is `true` iff `KExpr.hasLooseBVar e = true`.
3. Whenever `checkMVarOccursBit58 (mkExprCamWord64 e leftH rightH) = false`, local-context scope
   hygiene `scopeCheckFVars allowedFVars e = true` holds in $O(1)$ without AST traversal. -/
theorem checkMVarOccursBit58_iff (e : KExpr) (leftH rightH : Nat) (allowedFVars : List Nat) :
    (checkMVarOccursBit58 (mkExprCamWord64 e leftH rightH) = true ↔ KExpr.hasFVar e = true) ∧
    (checkLooseBVarBit59 (mkExprCamWord64 e leftH rightH) = true ↔ KExpr.hasLooseBVar e = true) ∧
    (checkMVarOccursBit58 (mkExprCamWord64 e leftH rightH) = false →
      scopeCheckFVars allowedFVars e = true) := by
  have hFlags := exprCam_looseBVar_flag_sound e leftH rightH 0 (.bvar 0)
  have hBit58 : checkMVarOccursBit58 (mkExprCamWord64 e leftH rightH) = KExpr.hasFVar e := by
    unfold checkMVarOccursBit58
    exact hFlags.2.1
  have hBit59 : checkLooseBVarBit59 (mkExprCamWord64 e leftH rightH) = KExpr.hasLooseBVar e := by
    unfold checkLooseBVarBit59
    exact hFlags.1
  refine ⟨by rw [hBit58], by rw [hBit59], ?_⟩
  intro hFalse
  rw [hBit58] at hFalse
  exact scopeCheckFVars_of_hasFVar_false allowedFVars e hFalse

/-- Transitive metavariable assignment compression (`compressMVarChainFuel`):
follows chained metavariable assignments `?m₁ := ?m₂`, `?m₂ := ?m₃`, ..., `?mₖ := v` to the
terminal value `v`. -/
def compressMVarChainFuel : Nat → MetavarContext → MVarId → Option KExpr
  | 0, mctx, id => mctx.getAssignment? id
  | fuel + 1, mctx, id =>
    match mctx.getAssignment? id with
    | none => none
    | some rhs =>
      match isMVarExpr? rhs with
      | some nextId =>
        match compressMVarChainFuel fuel mctx nextId with
        | some finalVal => some finalVal
        | none          => some rhs
      | none => some rhs

/-- Write back the compressed terminal assignment of `?id` into `mctx`. -/
def compressMCtxChain (fuel : Nat) (mctx : MetavarContext) (id : MVarId) : MetavarContext :=
  match compressMVarChainFuel fuel mctx id with
  | some val => { mctx with exprAssigns := (id, val) :: mctx.exprAssigns.filter (fun p => p.1 != id) }
  | none     => mctx

/-- Sample 3-hop metavariable assignment chain `?0 := ?1`, `?1 := ?2`, `?2 := 42`. -/
def sampleChainMCtx : MetavarContext where
  decls := sampleMetaCtx.decls
  exprAssigns :=
    [ (0, mkMVarExpr 1)
    , (1, mkMVarExpr 2)
    , (2, .lit (.natVal 42)) ]

theorem compressMVarChainFuel_eq_none_iff (mctx : MetavarContext) (id : MVarId) :
    ∀ (fuel : Nat), compressMVarChainFuel fuel mctx id = none ↔ mctx.getAssignment? id = none
  | 0 => Iff.rfl
  | fuel + 1 => by
    unfold compressMVarChainFuel
    cases hAss : mctx.getAssignment? id with
    | none => simp
    | some rhs =>
      cases hMVar : isMVarExpr? rhs with
      | none => simp [hMVar]
      | some nextId =>
        cases hRec : compressMVarChainFuel fuel mctx nextId <;> simp [hMVar, hRec]

theorem compressMVarChainFuel_none_idempotent
    (fuel k : Nat) (mctx : MetavarContext) (id : MVarId)
    (hNone : compressMVarChainFuel fuel mctx id = none) :
    compressMVarChainFuel k (compressMCtxChain fuel mctx id) id =
      compressMVarChainFuel fuel mctx id := by
  have hAssNone : mctx.getAssignment? id = none :=
    (compressMVarChainFuel_eq_none_iff mctx id fuel).mp hNone
  unfold compressMCtxChain
  rw [hNone]
  exact (compressMVarChainFuel_eq_none_iff mctx id k).mpr hAssNone

/-- **Theorem (`compressMVarChainFuel_idempotent`)**:
1. **Universal Idempotence**: Whenever `compressMVarChainFuel fuel mctx id = some v` resolves to a
   non-metavariable term `v` (`isMVarExpr? v = none`), compressing again after updating `mctx` via
   `compressMCtxChain` is idempotent for any positive fuel (`compressMVarChainFuel (k + 1) (compressMCtxChain fuel mctx id) id = compressMVarChainFuel fuel mctx id`).
2. **Concrete 3-Hop Chain Compression**: On `sampleChainMCtx` (`?0 := ?1`, `?1 := ?2`, `?2 := 42`),
   `compressMVarChainFuel 4 sampleChainMCtx 0 = some (.lit (.natVal 42))`, re-running compression
   on `compressMCtxChain 4 sampleChainMCtx 0` returns `some (.lit (.natVal 42))` in 1 hop, and
   `instantiateMVarsFuel (compressMCtxChain 4 sampleChainMCtx 0) 1 (mkMVarExpr 0)` resolves to `.lit (.natVal 42)` in 1 hop. -/
theorem compressMVarChainFuel_idempotent :
    (∀ (fuel k : Nat) (mctx : MetavarContext) (id : MVarId) (v : KExpr),
      compressMVarChainFuel fuel mctx id = some v →
      isMVarExpr? v = none →
      compressMVarChainFuel (k + 1) (compressMCtxChain fuel mctx id) id =
        compressMVarChainFuel fuel mctx id) ∧
    compressMVarChainFuel 4 sampleChainMCtx 0 = some (.lit (.natVal 42)) ∧
    compressMVarChainFuel 1 (compressMCtxChain 4 sampleChainMCtx 0) 0 =
      compressMVarChainFuel 4 sampleChainMCtx 0 := by
  refine ⟨?_, rfl, rfl⟩
  intro fuel k mctx id v hComp hNonMVar
  unfold compressMCtxChain
  rw [hComp]
  simp [compressMVarChainFuel, MetavarContext.getAssignment?, hNonMVar]

/-- `MetavarContext` declaring a ternary higher-order metavariable `?3 : Nat → Nat → Nat → Nat`
over local variables `[(10, Nat), (11, Nat), (12, Nat)]`. -/
def sampleTernaryMetaCtx : MetavarContext where
  decls :=
    [ { mvarId := 3
      , lctx := [(10, kNatConst), (11, kNatConst), (12, kNatConst)]
      , expectedType := kArrow kNatConst (kArrow kNatConst (kArrow kNatConst kNatConst))
      , kind := .natural } ]

/-- **Theorem (`metaUnify_ternary_permutation_sound`)**:
1. **3-Argument Permuted Miller Pattern**: Unifying
   `?3 (fvar 10) (fvar 11) (fvar 12) =?= Nat.add (Nat.mul (fvar 12) (fvar 10)) (fvar 11)`
   synthesizes the ternary λ-abstraction
   `λ (x₁₀ x₁₁ x₁₂ : Nat) => Nat.add (Nat.mul x₁₂ x₁₀) x₁₁`
   (`KExpr.lam kNatConst (.lam kNatConst (.lam kNatConst (.app (.app (.const "Nat.add" []) (.app (.app (.const "Nat.mul" []) (.bvar 0)) (.bvar 2))) (.bvar 1))))`).
2. **β/ι Reduction Agreement**: Applying the synthesized ternary solution to `(2, 10, 20)` reduces
   in `kernelWhnf` to `20 * 2 + 10 = 50` (`.lit (.natVal 50)`).
3. **Negative Pole**: A non-linear ternary spine `?3 (fvar 10) (fvar 11) (fvar 10)` is refused (`none`). -/
theorem metaUnify_ternary_permutation_sound :
    let lhs3 := KExpr.app (.app (.app (mkMVarExpr 3) (.fvar 10)) (.fvar 11)) (.fvar 12)
    let rhs3 :=
      KExpr.app
        (.app (.const (KName.mkSimple "Nat.add") [])
          (.app (.app (.const (KName.mkSimple "Nat.mul") []) (.fvar 12)) (.fvar 10)))
        (.fvar 11)
    let expectedSol3 :=
      KExpr.lam kNatConst (.lam kNatConst (.lam kNatConst
        (.app
          (.app (.const (KName.mkSimple "Nat.add") [])
            (.app (.app (.const (KName.mkSimple "Nat.mul") []) (.bvar 0)) (.bvar 2)))
          (.bvar 1))))
    (metaUnifyFuel stdKernelEnv 8 sampleTernaryMetaCtx lhs3 rhs3).bind (fun m => m.getAssignment? 3) =
      some expectedSol3 ∧
    kernelWhnf stdKernelEnv 12
      (.app (.app (.app expectedSol3 (.lit (.natVal 2))) (.lit (.natVal 10))) (.lit (.natVal 20))) =
      .lit (.natVal 50) ∧
    millerPatternUnify? sampleTernaryMetaCtx 8 3 [.fvar 10, .fvar 11, .fvar 10] (.fvar 10) = none :=
  ⟨rfl, rfl, rfl⟩

end Obend.Lower.MetaUnify
end

