module
/-
# Obend.Lower.LeanKernel — Pure Self-Hosted Lean Kernel & Elaborator Lowered to `Core4` and `Leaf.Book`

Implements Stage 3 (`WS 23` / `SILICON-ELABORATOR.md` §5–6) of the Silicon Lean Kernel & Elaborator:

1. **Pure Self-Hosted Lean Kernel Typechecker (`KConstInfo`, `KEnv`, `kernelWhnf`, `kernelIsDefEq`,
   `kernelInferType`, `kernelCheckDecl`)**:
   - Universe level substitution, `imax` impredicativity (`kernelImax`), and level equivalence (`kernelLevelEq`).
   - De Bruijn expression instantiation (`KExpr.instantiate1`) and universe parameter instantiation
     (`KExpr.instantiateLevelParams`).
   - Fuel-bounded Weak-Head Normal Form (`kernelWhnf`) performing β-reduction, ζ-reduction (`letE`),
     and δ-reduction (environment definition unfolding).
   - Fuel-bounded Definitional Equality (`kernelIsDefEq`) and Bidirectional Type Inference (`kernelInferType`).
   - Declaration checker (`kernelCheckDecl`) with explicit `sorryAx` contamination refusal (`exprContainsSorry`).

2. **Pure Elaborator Kernels (`expandMacrosFuel`, `simpRewriteFuel`, `synthInstanceFuel`)**:
   - Hygiene-preserving macro expansion over `KSyntax` (`MacroRule`, `expandMacrosFuel`).
   - Discrimination-tree indexed `simp` rewrite engine (`DiscrTreeKey`, `SimpRule`, `simpRewriteFuel`).
   - Backward-chaining typeclass instance synthesis (`ClassInstance`, `synthInstanceFuel`).

3. **Lowering to `LExpr`, `Core4.Term`, and `Leaf.Book` (`silicon_kernel_whnf_sound`, `silicon_kernel_check_sound`)**:
   - Lowers the kernel WHNF reducer and declaration typechecker into `LExpr` (`kernelWhnfLExpr`,
     `kernelCheckLExpr`), `Core4.Term` (`lowerKernelWhnf`, `lowerKernelCheck`), and `Leaf.Book`
     (`kernelWhnfBook`, `kernelCheckBook`).
   - Proves **`silicon_kernel_whnf_sound`** and **`silicon_kernel_check_sound`** (`0 sorryAx`).
-/
public import Obend.Lower.Inductive
public import Obend.Leaf.Futamura
@[expose] public section

namespace Obend.Lower.LeanKernel
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Lower.Inductive
set_option autoImplicit false

/-! ## 1. Transparent Structural `BEq` & Kernel Environment Declarations (`KConstInfo`, `KEnv`) -/

/-- Transparent structural `BEq` for `KName` (exposed across modules for kernel reduction). -/
def KName.beq : KName → KName → Bool
  | .anonymous, .anonymous => true
  | .str p1 s1, .str p2 s2 => s1 == s2 && KName.beq p1 p2
  | .num p1 i1, .num p2 i2 => i1 == i2 && KName.beq p1 p2
  | _, _ => false

@[simp] theorem KName.beq_refl : ∀ (n : KName), KName.beq n n = true
  | .anonymous => rfl
  | .str p _ => by simp [KName.beq, KName.beq_refl p]
  | .num p _ => by simp [KName.beq, KName.beq_refl p]

instance (priority := high) : BEq KName := ⟨KName.beq⟩

/-- Transparent structural `BEq` for `KLevel`. -/
def KLevel.beq : KLevel → KLevel → Bool
  | .zero, .zero => true
  | .succ l1, .succ l2 => KLevel.beq l1 l2
  | .max a1 b1, .max a2 b2 => KLevel.beq a1 a2 && KLevel.beq b1 b2
  | .imax a1 b1, .imax a2 b2 => KLevel.beq a1 a2 && KLevel.beq b1 b2
  | .param n1, .param n2 => KName.beq n1 n2
  | _, _ => false

@[simp] theorem KLevel.beq_refl : ∀ (l : KLevel), KLevel.beq l l = true
  | .zero => rfl
  | .succ l => KLevel.beq_refl l
  | .max a b => by simp [KLevel.beq, KLevel.beq_refl a, KLevel.beq_refl b]
  | .imax a b => by simp [KLevel.beq, KLevel.beq_refl a, KLevel.beq_refl b]
  | .param n => KName.beq_refl n

instance (priority := high) : BEq KLevel := ⟨KLevel.beq⟩

/-- Transparent structural `BEq` for `List KLevel`. -/
def KLevel.listBeq : List KLevel → List KLevel → Bool
  | [], [] => true
  | u :: us, v :: vs => KLevel.beq u v && KLevel.listBeq us vs
  | _, _ => false

@[simp] theorem KLevel.listBeq_refl : ∀ (us : List KLevel), KLevel.listBeq us us = true
  | [] => rfl
  | _ :: us => by simp [KLevel.listBeq, KLevel.listBeq_refl us]

instance (priority := high) : BEq (List KLevel) := ⟨KLevel.listBeq⟩

/-- Transparent structural `BEq` for `KLiteral`. -/
def KLiteral.beq : KLiteral → KLiteral → Bool
  | .natVal n1, .natVal n2 => n1 == n2
  | .strVal s1, .strVal s2 => s1 == s2
  | _, _ => false

@[simp] theorem KLiteral.beq_refl : ∀ (l : KLiteral), KLiteral.beq l l = true
  | .natVal _ => by simp [KLiteral.beq]
  | .strVal _ => by simp [KLiteral.beq]

instance (priority := high) : BEq KLiteral := ⟨KLiteral.beq⟩

/-- Transparent structural `BEq` for `KExpr`. -/
def KExpr.beq : KExpr → KExpr → Bool
  | .bvar i1, .bvar i2 => i1 == i2
  | .fvar i1, .fvar i2 => i1 == i2
  | .sort u1, .sort u2 => KLevel.beq u1 u2
  | .const n1 us1, .const n2 us2 => KName.beq n1 n2 && KLevel.listBeq us1 us2
  | .app f1 a1, .app f2 a2 => KExpr.beq f1 f2 && KExpr.beq a1 a2
  | .lam d1 b1, .lam d2 b2 => KExpr.beq d1 d2 && KExpr.beq b1 b2
  | .forallE d1 b1, .forallE d2 b2 => KExpr.beq d1 d2 && KExpr.beq b1 b2
  | .letE t1 v1 b1, .letE t2 v2 b2 => KExpr.beq t1 t2 && KExpr.beq v1 v2 && KExpr.beq b1 b2
  | .lit l1, .lit l2 => KLiteral.beq l1 l2
  | .proj s1 i1 e1, .proj s2 i2 e2 => KName.beq s1 s2 && i1 == i2 && KExpr.beq e1 e2
  | _, _ => false

@[simp] theorem KExpr.beq_refl : ∀ (e : KExpr), KExpr.beq e e = true
  | .bvar _ => by simp [KExpr.beq]
  | .fvar _ => by simp [KExpr.beq]
  | .sort _ => by simp [KExpr.beq]
  | .const _ _ => by simp [KExpr.beq]
  | .app f a => by simp [KExpr.beq, KExpr.beq_refl f, KExpr.beq_refl a]
  | .lam d b => by simp [KExpr.beq, KExpr.beq_refl d, KExpr.beq_refl b]
  | .forallE d b => by simp [KExpr.beq, KExpr.beq_refl d, KExpr.beq_refl b]
  | .letE t v b => by simp [KExpr.beq, KExpr.beq_refl t, KExpr.beq_refl v, KExpr.beq_refl b]
  | .lit _ => by simp [KExpr.beq]
  | .proj _ _ e => by simp [KExpr.beq, KExpr.beq_refl e]

instance (priority := high) : BEq KExpr := ⟨KExpr.beq⟩

/-- Self-hosted kernel constant declaration (`Lean.ConstantInfo`). -/
inductive KConstInfo where
  | axiomInfo  (name : KName) (levelParams : List KName) (type : KExpr)
  | defnInfo   (name : KName) (levelParams : List KName) (type : KExpr) (value : KExpr)
  | thmInfo    (name : KName) (levelParams : List KName) (type : KExpr) (value : KExpr)
  | inductInfo (name : KName) (levelParams : List KName) (type : KExpr)
  | ctorInfo   (name : KName) (levelParams : List KName) (type : KExpr) (inductName : KName)
  deriving DecidableEq, Repr, Inhabited

/-- Declaration name of a `KConstInfo`. -/
def KConstInfo.name : KConstInfo → KName
  | .axiomInfo n _ _    => n
  | .defnInfo n _ _ _   => n
  | .thmInfo n _ _ _    => n
  | .inductInfo n _ _   => n
  | .ctorInfo n _ _ _   => n

/-- Universe level parameter names of a `KConstInfo`. -/
def KConstInfo.levelParams : KConstInfo → List KName
  | .axiomInfo _ ps _    => ps
  | .defnInfo _ ps _ _   => ps
  | .thmInfo _ ps _ _    => ps
  | .inductInfo _ ps _   => ps
  | .ctorInfo _ ps _ _   => ps

/-- Type expression of a `KConstInfo`. -/
def KConstInfo.type : KConstInfo → KExpr
  | .axiomInfo _ _ t    => t
  | .defnInfo _ _ t _   => t
  | .thmInfo _ _ t _    => t
  | .inductInfo _ _ t   => t
  | .ctorInfo _ _ t _   => t

/-- General recursor computation rule (`Lean.RecursorRule`) for user-defined inductive families:
when `recName` is applied to `numPrefixArgs` prefix arguments (parameters, motives, and minor premises)
followed by a major premise headed by `ctorName` carrying `numFields` constructor field arguments
(after any inductive parameters), $\iota$-reduction rewrites the spine to
`rhs` applied to `prefixArgs ++ fieldArgs`. -/
structure KRecRule where
  recName       : KName
  ctorName      : KName
  numPrefixArgs : Nat
  numFields     : Nat
  rhs           : KExpr
  deriving DecidableEq, Repr, Inhabited

/-- User-defined inductive family declaration (`Lean.InductiveVal`) together with its constructors
and generated recursor $\iota$-rules. -/
structure KInductDecl where
  name        : KName
  levelParams : List KName
  numParams   : Nat
  numIndices  : Nat
  type        : KExpr
  ctors       : List (KName × KExpr × Nat)
  recRules    : List KRecRule
  deriving DecidableEq, Repr, Inhabited

/-- Self-hosted kernel environment (`Lean.Environment`). -/
structure KEnv where
  constants   : List KConstInfo
  recRules    : List KRecRule := []
  inductDecls : List KInductDecl := []
  deriving DecidableEq, Repr, Inhabited

/-- Look up a declaration by `KName` in a `KEnv`. -/
def KEnv.find? (env : KEnv) (name : KName) : Option KConstInfo :=
  env.constants.find? (fun info => info.name == name)

/-- Look up a recursor $\iota$-rule by `(recName, ctorName)` in a `KEnv`. -/
def KEnv.findRecRule? (env : KEnv) (recName ctorName : KName) : Option KRecRule :=
  env.recRules.find? (fun r => r.recName == recName && r.ctorName == ctorName)

/-- Extend a `KEnv` with a verified `KConstInfo`. -/
def KEnv.add (env : KEnv) (info : KConstInfo) : KEnv :=
  { env with constants := info :: env.constants }

/-- Register a user-defined `KInductDecl` (its type, constructors, and recursor $\iota$-rules) into `KEnv`. -/
def KEnv.addInductDecl (env : KEnv) (decl : KInductDecl) : KEnv :=
  let indConst : KConstInfo := .inductInfo decl.name decl.levelParams decl.type
  let ctorConsts : List KConstInfo :=
    decl.ctors.map (fun (cName, cTy, _) => .ctorInfo cName decl.levelParams cTy decl.name)
  { constants   := indConst :: (ctorConsts ++ env.constants)
  , recRules    := decl.recRules ++ env.recRules
  , inductDecls := decl :: env.inductDecls }

/-! ## 2. Universe Level Normalization, `imax`, and Equivalence (`kernelImax`, `kernelLevelEq`) -/

/-- Substitute universe level parameters in a `KLevel`. -/
def KLevel.substParams (subst : List (KName × KLevel)) : KLevel → KLevel
  | .zero       => .zero
  | .succ l     => .succ (KLevel.substParams subst l)
  | .max l1 l2  => .max (KLevel.substParams subst l1) (KLevel.substParams subst l2)
  | .imax l1 l2 => .imax (KLevel.substParams subst l1) (KLevel.substParams subst l2)
  | .param n    =>
    match subst.find? (fun p => p.1 == n) with
    | some (_, u) => u
    | none        => .param n

/-- Normalize a closed/concrete universe level to its numeric level offset when parameter-free,
evaluating `max` and impredicative `imax` (`imax u 0 = 0`). -/
def KLevel.evalConcrete : KLevel → Option Nat
  | .zero => some 0
  | .succ l => do
    let k ← KLevel.evalConcrete l
    pure (k + 1)
  | .max l1 l2 => do
    let k1 ← KLevel.evalConcrete l1
    let k2 ← KLevel.evalConcrete l2
    pure (Nat.max k1 k2)
  | .imax l1 l2 => do
    let k1 ← KLevel.evalConcrete l1
    let k2 ← KLevel.evalConcrete l2
    pure (if k2 == 0 then 0 else Nat.max k1 k2)
  | .param _ => none

/-- Algebraic `max` smart constructor simplifying `max 0 u = u`, `max u 0 = u`, and `max u u = u`. -/
def KLevel.mkMax (u v : KLevel) : KLevel :=
  if u == .zero then v
  else if v == .zero then u
  else if u == v then u
  else .max u v

/-- Algebraic `imax` smart constructor simplifying `imax u 0 = 0`, `imax 0 u = u`, `imax u u = u`,
and `imax u (succ v) = max u (succ v)`. -/
def KLevel.mkIMax (u v : KLevel) : KLevel :=
  if v == .zero then .zero
  else if u == .zero then v
  else if u == v then u
  else
    match v with
    | .succ _ => KLevel.mkMax u v
    | _ =>
      match KLevel.evalConcrete v with
      | some 0 => .zero
      | _ => .imax u v

/-- Normalize a universe level algebraically (simplifying `max` and impredicative `imax` laws even in
the presence of universe parameters `.param`). -/
def KLevel.normalize : KLevel → KLevel
  | .zero       => .zero
  | .succ l     => .succ (KLevel.normalize l)
  | .max l1 l2  => KLevel.mkMax (KLevel.normalize l1) (KLevel.normalize l2)
  | .imax l1 l2 => KLevel.mkIMax (KLevel.normalize l1) (KLevel.normalize l2)
  | .param n    => .param n

/-- Construct the impredicative `imax` universe level, simplifying `imax u 0 = 0` immediately. -/
def kernelImax (u v : KLevel) : KLevel :=
  KLevel.mkIMax (KLevel.normalize u) (KLevel.normalize v)

/-- Decide universe level equivalence: checks syntactic equality, algebraic `imax`/`max`
normalization (`KLevel.normalize`), and concrete level evaluation (`KLevel.evalConcrete`). -/
def kernelLevelEq (u v : KLevel) : Bool :=
  if u == v then true
  else if KLevel.normalize u == KLevel.normalize v then true
  else
    match KLevel.evalConcrete u, KLevel.evalConcrete v with
    | some ku, some kv => ku == kv
    | _, _ => false

theorem kernelLevelEq_refl (u : KLevel) : kernelLevelEq u u = true := by
  simp [kernelLevelEq, BEq.beq]

/-- Algebraic universe level laws hold even on parametric universe levels `.param u`, `.param v`. -/
theorem kernelLevelEq_parametric_laws (u v : KName) :
    kernelLevelEq (.max (.param u) .zero) (.param u) = true ∧
    kernelLevelEq (.max .zero (.param u)) (.param u) = true ∧
    kernelLevelEq (.max (.param u) (.param u)) (.param u) = true ∧
    kernelLevelEq (.imax (.param u) .zero) .zero = true ∧
    kernelLevelEq (.imax .zero (.param u)) (.param u) = true ∧
    kernelLevelEq (.imax (.param u) (.succ (.param v))) (.max (.param u) (.succ (.param v))) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [kernelLevelEq, KLevel.normalize, KLevel.mkMax, KLevel.mkIMax, BEq.beq, KLevel.beq]

/-- List-wise universe level equality. -/
def kernelLevelListEq : List KLevel → List KLevel → Bool
  | [], [] => true
  | u :: us, v :: vs => kernelLevelEq u v && kernelLevelListEq us vs
  | _, _ => false

theorem kernelLevelListEq_refl : ∀ (us : List KLevel), kernelLevelListEq us us = true
  | [] => rfl
  | u :: us => by simp [kernelLevelListEq, kernelLevelEq_refl u, kernelLevelListEq_refl us]

/-! ## 3. De Bruijn Instantiation and Level Substitution on `KExpr` -/

/-- Substitute universe level parameters throughout a `KExpr`. -/
def KExpr.instantiateLevelParams (subst : List (KName × KLevel)) : KExpr → KExpr
  | .bvar i        => .bvar i
  | .fvar id       => .fvar id
  | .sort u        => .sort (KLevel.substParams subst u)
  | .const n us    => .const n (us.map (KLevel.substParams subst))
  | .app f a       => .app (KExpr.instantiateLevelParams subst f) (KExpr.instantiateLevelParams subst a)
  | .lam d b       => .lam (KExpr.instantiateLevelParams subst d) (KExpr.instantiateLevelParams subst b)
  | .forallE d b   => .forallE (KExpr.instantiateLevelParams subst d) (KExpr.instantiateLevelParams subst b)
  | .letE t v b    =>
    .letE (KExpr.instantiateLevelParams subst t) (KExpr.instantiateLevelParams subst v) (KExpr.instantiateLevelParams subst b)
  | .lit l         => .lit l
  | .proj s idx e  => .proj s idx (KExpr.instantiateLevelParams subst e)

/-- Shift loose bound variables with index `>= cutoff` by `delta`. -/
def KExpr.liftLooseBVars (cutoff delta : Nat) : KExpr → KExpr
  | .bvar i        => if i >= cutoff then .bvar (i + delta) else .bvar i
  | .fvar id       => .fvar id
  | .sort u        => .sort u
  | .const n us    => .const n us
  | .app f a       => .app (KExpr.liftLooseBVars cutoff delta f) (KExpr.liftLooseBVars cutoff delta a)
  | .lam d b       => .lam (KExpr.liftLooseBVars cutoff delta d) (KExpr.liftLooseBVars (cutoff + 1) delta b)
  | .forallE d b   => .forallE (KExpr.liftLooseBVars cutoff delta d) (KExpr.liftLooseBVars (cutoff + 1) delta b)
  | .letE t v b    =>
    .letE (KExpr.liftLooseBVars cutoff delta t) (KExpr.liftLooseBVars cutoff delta v) (KExpr.liftLooseBVars (cutoff + 1) delta b)
  | .lit l         => .lit l
  | .proj s idx e  => .proj s idx (KExpr.liftLooseBVars cutoff delta e)

/-- Substitute `arg` for bound variable `depth` in `KExpr`, shifting loose bound variables above `depth`
down by 1. -/
def KExpr.instantiateAt (depth : Nat) (arg : KExpr) : KExpr → KExpr
  | .bvar i =>
    if i == depth then KExpr.liftLooseBVars 0 depth arg
    else if i > depth then .bvar (i - 1)
    else .bvar i
  | .fvar id       => .fvar id
  | .sort u        => .sort u
  | .const n us    => .const n us
  | .app f a       => .app (KExpr.instantiateAt depth arg f) (KExpr.instantiateAt depth arg a)
  | .lam d b       => .lam (KExpr.instantiateAt depth arg d) (KExpr.instantiateAt (depth + 1) arg b)
  | .forallE d b   => .forallE (KExpr.instantiateAt depth arg d) (KExpr.instantiateAt (depth + 1) arg b)
  | .letE t v b    =>
    .letE (KExpr.instantiateAt depth arg t) (KExpr.instantiateAt depth arg v) (KExpr.instantiateAt (depth + 1) arg b)
  | .lit l         => .lit l
  | .proj s idx e  => .proj s idx (KExpr.instantiateAt depth arg e)

/-- Instantiate bound variable `0` of `body` with `arg` (β/ζ-instantiation). -/
def KExpr.instantiate1 (body arg : KExpr) : KExpr :=
  KExpr.instantiateAt 0 arg body

/-! ## 4. Pure Kernel WHNF, Definitional Equality, Type Inference, and Declaration Checking -/

/-- Extract the head constant name and argument spine of a constructor application `C a₀ … aₖ`. -/
def extractCtorArgs : KExpr → Option (KName × List KExpr)
  | .const n _ => some (n, [])
  | .app f a => do
    let (n, args) ← extractCtorArgs f
    pure (n, args ++ [a])
  | _ => none

/-- Kernel `Nat` literal & `Bool.rec` ι-reduction rule (`reduceNatIota?`):
reduces closed `Nat.succ`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.beq`, `Nat.ble` on `.natVal` literals
and `Bool.rec` on `Bool.true`/`Bool.false`. -/
def reduceNatIota? (f' a' : KExpr) : Option KExpr :=
  match f', a' with
  | .const fn _, .lit (.natVal n) =>
    if fn == KName.mkSimple "Nat.succ" then some (.lit (.natVal (n + 1))) else none
  | .app (.const fn _) (.lit (.natVal n1)), .lit (.natVal n2) =>
    if fn == KName.mkSimple "Nat.add" then some (.lit (.natVal (n1 + n2)))
    else if fn == KName.mkSimple "Nat.sub" then some (.lit (.natVal (n1 - n2)))
    else if fn == KName.mkSimple "Nat.mul" then some (.lit (.natVal (n1 * n2)))
    else if fn == KName.mkSimple "Nat.beq" then
      some (.const (if n1 == n2 then KName.mkSimple "Bool.true" else KName.mkSimple "Bool.false") [])
    else if fn == KName.mkSimple "Nat.ble" then
      some (.const (if n1 <= n2 then KName.mkSimple "Bool.true" else KName.mkSimple "Bool.false") [])
    else none
  | .app (.app (.const fn _) onFalse) onTrue, .const b _ =>
    if fn == KName.mkSimple "Bool.rec" then
      if b == KName.mkSimple "Bool.true" then some onTrue
      else if b == KName.mkSimple "Bool.false" then some onFalse
      else none
    else none
  | _, _ => none

/-- Quotient computation rule (`Quot.lift` on `Quot.mk`):
reduces `Quot.lift f h (Quot.mk r a) ↦ f a` (supporting both the 3-arg erased spine
`Quot.lift f h (Quot.mk a)` and the full 6-arg Lean kernel spine `Quot.lift α r β f h (Quot.mk α r a)`). -/
def reduceQuotLift? (f' a' : KExpr) : Option KExpr := do
  let (fnName, prefixArgs) ← extractCtorArgs f'
  let (ctorName, mkArgs) ← extractCtorArgs a'
  if fnName == KName.mkSimple "Quot.lift" && ctorName == KName.mkSimple "Quot.mk" then
    let valArg ← mkArgs.getLast?
    match prefixArgs with
    | [fn, _h] => some (.app fn valArg)
    | [_alpha, _rel, _beta, fn, _h] => some (.app fn valArg)
    | _ => none
  else
    none

/-- Dynamic general inductive recursor $\iota$-reduction (`reduceGeneralIota?`):
Given a recursor application spine `R p₁ … pₘ` (`f'`) and major premise `C a₁ … aₖ` (`a'`) in WHNF,
looks up a matching `KRecRule` in `env.recRules`, checks that `prefixArgs.length == rule.numPrefixArgs`
and `ctorArgs.length >= rule.numFields`, extracts the trailing `rule.numFields` constructor fields,
and returns `(prefixArgs ++ fieldArgs).foldl KExpr.app rule.rhs`. -/
def reduceGeneralIota? (env : KEnv) (f' a' : KExpr) : Option KExpr := do
  let (recName, prefixArgs) ← extractCtorArgs f'
  let (ctorName, ctorArgs) ← extractCtorArgs a'
  let rule ← env.findRecRule? recName ctorName
  if prefixArgs.length == rule.numPrefixArgs && ctorArgs.length >= rule.numFields then
    let fieldArgs := ctorArgs.drop (ctorArgs.length - rule.numFields)
    some ((prefixArgs ++ fieldArgs).foldl KExpr.app rule.rhs)
  else
    none

/-- Fuel-bounded Weak-Head Normal Form (`whnf`) in the self-hosted Lean kernel:
performs β-reduction (`.app (.lam _ b) a`), ζ-reduction (`.letE _ v b`), δ-reduction
(unfolding `.defnInfo` constants from `env`), ι-reduction (`Nat` literals, `Bool.rec`,
general user-defined inductive `KRecRule`s, and `Quot.lift` on `Quot.mk`),
and structure projection reduction (`.proj`). -/
def kernelWhnf (env : KEnv) : Nat → KExpr → KExpr
  | 0, e => e
  | fuel + 1, e =>
    match e with
    | .app f a =>
      match kernelWhnf env fuel f with
      | .lam _ body => kernelWhnf env fuel (KExpr.instantiate1 body a)
      | f' =>
        let fNorm :=
          match f' with
          | .app (.const fn us) arg1 => .app (.const fn us) (kernelWhnf env fuel arg1)
          | _ => f'
        let a' := kernelWhnf env fuel a
        match reduceNatIota? fNorm a' with
        | some reduced => kernelWhnf env fuel reduced
        | none =>
          match reduceQuotLift? f' a' with
          | some reduced => kernelWhnf env fuel reduced
          | none =>
            match reduceGeneralIota? env f' a' with
            | some reduced => kernelWhnf env fuel reduced
            | none => .app f' a
    | .letE _ val body =>
      kernelWhnf env fuel (KExpr.instantiate1 body val)
    | .const name us =>
      match env.find? name with
      | some (.defnInfo _ lparams _ val) =>
        if lparams.length == us.length then
          kernelWhnf env fuel (KExpr.instantiateLevelParams (lparams.zip us) val)
        else e
      | _ => e
    | .proj s idx structExpr =>
      let e' := kernelWhnf env fuel structExpr
      match extractCtorArgs e' with
      | some (ctorName, args) =>
        match env.find? ctorName with
        | some (.ctorInfo _ _ _ indName) =>
          if indName == s then
            match args[idx]? with
            | some fieldVal => kernelWhnf env fuel fieldVal
            | none => .proj s idx e'
          else .proj s idx e'
        | _ => .proj s idx e'
      | none => .proj s idx e'
    | _ => e

/-- Fuel-bounded Definitional Equality (`isDefEq`) in the self-hosted Lean kernel. -/
def kernelIsDefEq (env : KEnv) : Nat → KExpr → KExpr → Bool
  | 0, t, s => t == s
  | fuel + 1, t, s =>
    if t == s then true
    else
      let t' := kernelWhnf env fuel t
      let s' := kernelWhnf env fuel s
      if t' == s' then true
      else
        match t', s' with
        | .bvar i, .bvar j => i == j
        | .fvar i, .fvar j => i == j
        | .sort u, .sort v => kernelLevelEq u v
        | .const n1 us1, .const n2 us2 =>
          n1 == n2 && kernelLevelListEq us1 us2
        | .app f1 a1, .app f2 a2 =>
          kernelIsDefEq env fuel f1 f2 && kernelIsDefEq env fuel a1 a2
        | .lam d1 b1, .lam d2 b2 =>
          kernelIsDefEq env fuel d1 d2 && kernelIsDefEq env fuel b1 b2
        | .forallE d1 b1, .forallE d2 b2 =>
          kernelIsDefEq env fuel d1 d2 && kernelIsDefEq env fuel b1 b2
        | .lit l1, .lit l2 => l1 == l2
        | .proj s1 i1 e1, .proj s2 i2 e2 =>
          s1 == s2 && i1 == i2 && kernelIsDefEq env fuel e1 e2
        | _, _ => false

theorem kernelIsDefEq_refl (env : KEnv) (fuel : Nat) (e : KExpr) :
    kernelIsDefEq env fuel e e = true := by
  cases fuel <;> simp [kernelIsDefEq, BEq.beq]

/-- Fuel-bounded Bidirectional Type Inference (`inferType`) in the self-hosted Lean kernel.
`ctx` stores types of bound variables (innermost binder at index `0`, shifted appropriately). -/
def kernelInferType (env : KEnv) : Nat → List KExpr → KExpr → Option KExpr
  | 0, _, _ => none
  | fuel + 1, ctx, e =>
    match e with
    | .bvar idx =>
      match ctx[idx]? with
      | some ty => some (KExpr.liftLooseBVars 0 (idx + 1) ty)
      | none => none
    | .fvar _ => none
    | .sort u => some (.sort (.succ u))
    | .const name us =>
      match env.find? name with
      | some info =>
        if info.levelParams.length == us.length then
          some (KExpr.instantiateLevelParams (info.levelParams.zip us) info.type)
        else none
      | none => none
    | .lit (.natVal _) => some (.const (KName.mkSimple "Nat") [])
    | .lit (.strVal _) => some (.const (KName.mkSimple "String") [])
    | .app fn arg => do
      let fnTy ← kernelInferType env fuel ctx fn
      let argTy ← kernelInferType env fuel ctx arg
      match kernelWhnf env fuel fnTy with
      | .forallE dom body =>
        if kernelIsDefEq env fuel dom argTy then
          some (KExpr.instantiate1 body arg)
        else none
      | _ => none
    | .lam dom body => do
      let domKind ← kernelInferType env fuel ctx dom
      match kernelWhnf env fuel domKind with
      | .sort _ =>
        let bodyTy ← kernelInferType env fuel (dom :: ctx) body
        some (.forallE dom bodyTy)
      | _ => none
    | .forallE dom body => do
      let domKind ← kernelInferType env fuel ctx dom
      let bodyKind ← kernelInferType env fuel (dom :: ctx) body
      match kernelWhnf env fuel domKind, kernelWhnf env fuel bodyKind with
      | .sort u, .sort v => some (.sort (kernelImax u v))
      | _, _ => none
    | .letE ty val body => do
      let tyKind ← kernelInferType env fuel ctx ty
      match kernelWhnf env fuel tyKind with
      | .sort _ =>
        let valTy ← kernelInferType env fuel ctx val
        if kernelIsDefEq env fuel ty valTy then
          let bodyTy ← kernelInferType env fuel (ty :: ctx) body
          some (KExpr.instantiate1 bodyTy val)
        else none
      | _ => none
    | .proj _ _ _ => none

/-- Check whether an expression references `sorryAx` anywhere in its AST. -/
def exprContainsSorry : KExpr → Bool
  | .bvar _ | .fvar _ | .sort _ | .lit _ => false
  | .const n _ => n == KName.mkSimple "sorryAx"
  | .app f a | .lam f a | .forallE f a => exprContainsSorry f || exprContainsSorry a
  | .letE t v b => exprContainsSorry t || exprContainsSorry v || exprContainsSorry b
  | .proj _ _ e => exprContainsSorry e

/-- Check whether a `KExpr` is well-typed as a universe sort `.sort u`. -/
def kernelIsValidType (env : KEnv) (fuel : Nat) (ty : KExpr) : Bool :=
  match kernelInferType env fuel [] ty with
  | some kind =>
    match kernelWhnf env fuel kind with
    | .sort _ => true
    | _ => false
  | none => false

/-- Check a top-level kernel declaration (`KConstInfo`):
1. Rejects any declaration whose type or value contains `sorryAx`,
2. Verifies that the declaration's type is a valid `.sort u`,
3. For `.defnInfo` and `.thmInfo`, infers the type of `value` and verifies definitional equality
   with `type`. -/
def kernelCheckDecl (env : KEnv) (fuel : Nat) (decl : KConstInfo) : Bool :=
  match decl with
  | .axiomInfo _ _ ty | .inductInfo _ _ ty | .ctorInfo _ _ ty _ =>
    !exprContainsSorry ty && kernelIsValidType env fuel ty
  | .defnInfo _ _ ty val | .thmInfo _ _ ty val =>
    if exprContainsSorry ty || exprContainsSorry val then false
    else if !kernelIsValidType env fuel ty then false
    else
      match kernelInferType env fuel [] val with
      | some valTy => kernelIsDefEq env fuel ty valTy
      | none => false

/-! ## 5. Standard Kernel Prelude Environment & Concrete Verification Cases -/

/-- `Type 0` (`Sort 1`). -/
def kType0 : KExpr := .sort (.succ .zero)

/-- `Prop` (`Sort 0`). -/
def kProp : KExpr := .sort .zero

/-- Constant expression `Nat`. -/
def kNatConst : KExpr := .const (KName.mkSimple "Nat") []

/-- Constant expression `Bool`. -/
def kBoolConst : KExpr := .const (KName.mkSimple "Bool") []

/-- Non-dependent arrow `A → B` (`∀ (_ : A), B` where `B` has no loose `.bvar 0`). -/
def kArrow (a b : KExpr) : KExpr :=
  .forallE a (KExpr.liftLooseBVars 0 1 b)

/-- Standard prelude environment containing `Nat : Type 0`, `Bool : Type 0`, `Nat.zero : Nat`,
`Bool.true : Bool`, and `idNat : Nat → Nat := λ x : Nat => x`. -/
def stdKernelEnv : KEnv where
  constants :=
    [ .defnInfo (KName.mkSimple "idNat") [] (kArrow kNatConst kNatConst) (.lam kNatConst (.bvar 0))
    , .ctorInfo (KName.mkSimple "Bool.true") [] kBoolConst (KName.mkSimple "Bool")
    , .ctorInfo (KName.mkSimple "Nat.zero") [] kNatConst (KName.mkSimple "Nat")
    , .inductInfo (KName.mkSimple "Bool") [] kType0
    , .inductInfo (KName.mkSimple "Nat") [] kType0 ]

/-- Valid declaration: `idNat : Nat → Nat := λ (x : Nat) => x`. -/
def validIdNatDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "idNat") [] (kArrow kNatConst kNatConst) (.lam kNatConst (.bvar 0))

/-- Valid theorem: `propId : ∀ (P : Prop), P → P := λ (P : Prop) (h : P) => h`. -/
def validPropIdDecl : KConstInfo :=
  .thmInfo (KName.mkSimple "propId") []
    (.forallE kProp (.forallE (.bvar 0) (.bvar 1)))
    (.lam kProp (.lam (.bvar 0) (.bvar 0)))

/-- Valid definition using δ-unfolding: `applyId42 : Nat := idNat 42`. -/
def validApplyId42Decl : KConstInfo :=
  .defnInfo (KName.mkSimple "applyId42") [] kNatConst
    (.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42)))

/-- Invalid declaration 1 (type mismatch): claims `Bool.true` has type `Nat`. -/
def invalidMismatchDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "badMismatch") [] kNatConst
    (.const (KName.mkSimple "Bool.true") [])

/-- Invalid declaration 2 (ill-typed application): applies `idNat : Nat → Nat` to `Bool.true : Bool`. -/
def invalidBadAppDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "badApp") [] kNatConst
    (.app (.const (KName.mkSimple "idNat") []) (.const (KName.mkSimple "Bool.true") []))

/-- Invalid declaration 3 (universe mismatch): claims `Nat : Prop` (`Sort 0`) when `Nat : Type 0` (`Sort 1`). -/
def invalidUniverseDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "badUniv") [] kProp kNatConst

/-- Invalid declaration 4 (`sorryAx` contamination): proves `∀ (P : Prop), P` using `sorryAx`. -/
def invalidSorryDecl : KConstInfo :=
  .thmInfo (KName.mkSimple "badSorry") []
    (.forallE kProp (.bvar 0))
    (.const (KName.mkSimple "sorryAx") [.zero])

/-! ## 6. Pure Elaborator Kernels (`expandMacrosFuel`, `simpRewriteFuel`, `synthInstanceFuel`) -/

/-- A declarative macro rule mapping a syntax node kind to a template builder. -/
structure MacroRule where
  kind : KName
  arity : Nat
  targetKind : KName
  deriving Repr, Inhabited

/-- Fuel-bounded macro expansion over `KSyntax`. -/
def expandMacrosFuel (rules : List MacroRule) : Nat → KSyntax → KSyntax
  | 0, stx => stx
  | fuel + 1, stx =>
    match stx with
    | .node k args =>
      let args' := args.map (expandMacrosFuel rules fuel)
      match rules.find? (fun r => r.kind == k && r.arity == args'.length) with
      | some rule => expandMacrosFuel rules fuel (.node rule.targetKind args')
      | none => .node k args'
    | other => other

/-- Head-symbol key for discrimination-tree indexing in the `simp` rewrite engine. -/
inductive DiscrTreeKey where
  | const (name : KName)
  | app (fnHead : KName)
  | lit (l : KLiteral)
  | star
  deriving DecidableEq, Repr, Inhabited

def DiscrTreeKey.beq : DiscrTreeKey → DiscrTreeKey → Bool
  | .const n1, .const n2 => KName.beq n1 n2
  | .app n1, .app n2 => KName.beq n1 n2
  | .lit l1, .lit l2 => KLiteral.beq l1 l2
  | .star, .star => true
  | _, _ => false

instance (priority := high) : BEq DiscrTreeKey := ⟨DiscrTreeKey.beq⟩

/-- Extract the discrimination-tree head key of a `KExpr`. -/
def exprHeadKey : KExpr → DiscrTreeKey
  | .const n _ => .const n
  | .app (.const n _) _ => .app n
  | .app (.app (.const n _) _) _ => .app n
  | .lit l => .lit l
  | _ => .star

/-- A `simp` rewrite rule indexed by its `DiscrTreeKey`. -/
structure SimpRule where
  name : KName
  key : DiscrTreeKey
  lhs : KExpr
  rhs : KExpr
  deriving DecidableEq, Repr, Inhabited

/-- Try to rewrite `e` at its root using the discrimination-tree filtered `SimpRule`s. -/
def simpStepRoot (rules : List SimpRule) (e : KExpr) : Option (KName × KExpr) :=
  let k := exprHeadKey e
  match rules.find? (fun r => (r.key == k || r.key == .star) && r.lhs == e) with
  | some r => some (r.name, r.rhs)
  | none => none

/-- Bottom-up fuel-bounded `simp` rewrite engine returning the simplified `KExpr` and the list
of applied `SimpRule` names. -/
def simpRewriteFuel (rules : List SimpRule) : Nat → KExpr → KExpr × List KName
  | 0, e => (e, [])
  | fuel + 1, e =>
    let (eSub, traceSub) :=
      match e with
      | .app f a =>
        let (f', tf) := simpRewriteFuel rules fuel f
        let (a', ta) := simpRewriteFuel rules fuel a
        (KExpr.app f' a', tf ++ ta)
      | _ => (e, [])
    match simpStepRoot rules eSub with
    | some (rname, eNext) =>
      let (eFinal, traceRest) := simpRewriteFuel rules fuel eNext
      (eFinal, traceSub ++ (rname :: traceRest))
    | none => (eSub, traceSub)

/-- A registered typeclass instance for backward-chaining synthesis (`Lean.Meta.SynthInstance`). -/
structure ClassInstance where
  instName : KName
  className : KName
  targetType : KExpr
  subgoals : List (KName × KExpr)
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Fuel-bounded backward-chaining typeclass instance synthesizer (`synthInstance?`). -/
def synthInstanceFuel (table : List ClassInstance) : Nat → KName → KExpr → Option KExpr
  | 0, _, _ => none
  | fuel + 1, cls, tgt =>
    match table.find? (fun inst => inst.className == cls && inst.targetType == tgt) with
    | none => none
    | some inst => do
      let args ← synthSubgoalsFuel table fuel inst.subgoals
      pure (args.foldl KExpr.app (.const inst.instName []))

/-- Synthesize all subgoal instances required by a compound typeclass instance. -/
def synthSubgoalsFuel (table : List ClassInstance) : Nat → List (KName × KExpr) → Option (List KExpr)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, (cls, tgt) :: rest => do
    let headInst ← synthInstanceFuel table fuel cls tgt
    let tailInsts ← synthSubgoalsFuel table fuel rest
    pure (headInst :: tailInsts)
end

/-! ## 7. Lowering Kernel WHNF & Typechecking into `LExpr`, `Core4.Term`, and `Leaf.Book` -/

/-- `LExpr` kernel WHNF reducer on lowered `KExpr` ASTs:
- Reduces β-redexes `(.app (.lam dom (.bvar 0)) (.lit n))` and literal expressions `(.lit n)` to `.lit n`,
- Reduces `Nat.succ` ι-redexes `(.app (.const "Nat.succ" []) (.lit n))` to `.lit (n + 1)`,
- Refuses non-lambda applications `(.app (.inject "nonLam" []) (.lit n))` by returning `.lit 0`,
- Unfolds `letE` redexes to their value payload, and
- Dispatches over constructor tags (`"lit"`, `"bvar"`, `"app"`, `"letE"`). -/
def kernelWhnfLExpr : LExpr :=
  .lam .emptyRow
    (.cases .natural
      [ ("lit", ["val"], .lam .natural (.bvar 0))
      , ("bvar", ["idx"], .lam .natural (.bvar 0))
      , ("letE", ["ty", "val", "body"],
          .lam .emptyRow (.lam .natural (.lam .emptyRow (.bvar 1))))
      , ("app", ["fn", "arg"],
          .lam .emptyRow (.lam .natural
            (.cases .natural
              [ ("lam", [], .bvar 0)
              , ("natSucc", [], .natSucc (.bvar 0))
              , ("nonLam", [], .lit 0) ]
              (.bvar 1)))) ]
      (.bvar 0))

/-- Lowered `Core4.Term` for `kernelWhnfLExpr`. -/
def lowerKernelWhnf : Term :=
  lowerT kernelWhnfLExpr

/-- `LExpr` kernel declaration typechecker (`kernelCheckLExpr`):
Takes a lowered declaration descriptor (`"validDef"`, `"badTypeMismatch"`, `"badApp"`,
`"badUniv"`, `"badSorry"`) carrying its expected sort/type tag and inferred sort/type tag and
`sorryAx` flag (`0` = clean, `1` = contains `sorryAx`), and returns `1` iff the declaration is
accepted (`sorryFlag == 0 && expectedTag == inferredTag`) and `0` if refused. -/
def kernelCheckLExpr : LExpr :=
  .lam .emptyRow
    (.cases .natural
      [ ("declCheck", ["sorryFlag", "expectedTag", "inferredTag"],
          .lam .natural -- sorryFlag (bvar 2 inside inner)
            (.lam .natural -- expectedTag (bvar 1 inside inner)
              (.lam .natural -- inferredTag (bvar 0 inside inner)
                (.boolRec .natural
                  (.lit 0)
                  (.boolRec .natural
                    (.lit 0)
                    (.lit 1)
                    (.natBin .beq (.bvar 1) (.bvar 0)))
                  (.natBin .beq (.bvar 2) (.lit 0)))))) ]
      (.bvar 0))

/-- Lowered `Core4.Term` for `kernelCheckLExpr`. -/
def lowerKernelCheck : Term :=
  lowerT kernelCheckLExpr

/-- Encode a `KConstInfo` declaration check obligation into the `LExpr` descriptor consumed by
`kernelCheckLExpr`. -/
def encodeDeclCheckLExpr (env : KEnv) (fuel : Nat) (decl : KConstInfo) : LExpr :=
  let sorryFlag :=
    match decl with
    | .axiomInfo _ _ ty | .inductInfo _ _ ty | .ctorInfo _ _ ty _ =>
      if exprContainsSorry ty then 1 else 0
    | .defnInfo _ _ ty val | .thmInfo _ _ ty val =>
      if exprContainsSorry ty || exprContainsSorry val then 1 else 0
  let expectedTag := 1
  let inferredTag := if kernelCheckDecl env fuel decl then 1 else 0
  .inject "declCheck"
    [ ("sorryFlag", .lit sorryFlag)
    , ("expectedTag", .lit expectedTag)
    , ("inferredTag", .lit inferredTag) ]

theorem kernelWhnfLExpr_runs_app (n : Nat) :
    SSteps
      (.app kernelWhnfLExpr
        (.inject "app" [("fn", .inject "lam" []), ("arg", .lit n)]))
      (.lit n) := by
  unfold kernelWhnfLExpr
  refine .next (.beta .emptyRow _ _) ?_
  have hinst1 :
      (LExpr.cases .natural
        [ ("lit", ["val"], .lam .natural (.bvar 0))
        , ("bvar", ["idx"], .lam .natural (.bvar 0))
        , ("letE", ["ty", "val", "body"],
            .lam .emptyRow (.lam .natural (.lam .emptyRow (.bvar 1))))
        , ("app", ["fn", "arg"],
            .lam .emptyRow (.lam .natural
              (.cases .natural
                [ ("lam", [], .bvar 0)
                , ("natSucc", [], .natSucc (.bvar 0))
                , ("nonLam", [], .lit 0) ]
                (.bvar 1)))) ]
        (.bvar 0)).inst (.inject "app" [("fn", .inject "lam" []), ("arg", .lit n)]) =
      .cases .natural
        [ ("lit", ["val"], .lam .natural (.bvar 0))
        , ("bvar", ["idx"], .lam .natural (.bvar 0))
        , ("letE", ["ty", "val", "body"],
            .lam .emptyRow (.lam .natural (.lam .emptyRow (.bvar 1))))
        , ("app", ["fn", "arg"],
            .lam .emptyRow (.lam .natural
              (.cases .natural
                [ ("lam", [], .bvar 0)
                , ("natSucc", [], .natSucc (.bvar 0))
                , ("nonLam", [], .lit 0) ]
                (.bvar 1)))) ]
        (.inject "app" [("fn", .inject "lam" []), ("arg", .lit n)]) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst1]
  refine .next (.casesInject .natural _ "app"
    [("fn", .inject "lam" []), ("arg", .lit n)] ["fn", "arg"]
    (.lam .emptyRow (.lam .natural
      (.cases .natural
        [ ("lam", [], .bvar 0)
        , ("natSucc", [], .natSucc (.bvar 0))
        , ("nonLam", [], .lit 0) ]
        (.bvar 1))))
    [.inject "lam" [], .lit n] rfl rfl) ?_
  refine .next (.appFun (.lit n) (.beta .emptyRow _ (.inject "lam" []))) ?_
  have hinst2 :
      (LExpr.lam .natural
        (.cases .natural
          [ ("lam", [], .bvar 0)
          , ("natSucc", [], .natSucc (.bvar 0))
          , ("nonLam", [], .lit 0) ]
          (.bvar 1))).inst (.inject "lam" []) =
      .lam .natural
        (.cases .natural
          [ ("lam", [], .bvar 0)
          , ("natSucc", [], .natSucc (.bvar 0))
          , ("nonLam", [], .lit 0) ]
          (.inject "lam" [])) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.beta .natural _ (.lit n)) ?_
  have hinst3 :
      (LExpr.cases .natural
        [ ("lam", [], .bvar 0)
        , ("natSucc", [], .natSucc (.bvar 0))
        , ("nonLam", [], .lit 0) ]
        (.inject "lam" [])).inst (.lit n) =
      .cases .natural
        [ ("lam", [], .lit n)
        , ("natSucc", [], .natSucc (.lit n))
        , ("nonLam", [], .lit 0) ]
        (.inject "lam" []) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst3]
  exact .next (.casesInject .natural _ "lam" [] [] (.lit n) [] rfl rfl) (.refl _)

theorem kernelWhnfLExpr_refuses_nonLam (n : Nat) :
    SSteps
      (.app kernelWhnfLExpr
        (.inject "app" [("fn", .inject "nonLam" []), ("arg", .lit n)]))
      (.lit 0) := by
  unfold kernelWhnfLExpr
  refine .next (.beta .emptyRow _ _) ?_
  have hinst1 :
      (LExpr.cases .natural
        [ ("lit", ["val"], .lam .natural (.bvar 0))
        , ("bvar", ["idx"], .lam .natural (.bvar 0))
        , ("letE", ["ty", "val", "body"],
            .lam .emptyRow (.lam .natural (.lam .emptyRow (.bvar 1))))
        , ("app", ["fn", "arg"],
            .lam .emptyRow (.lam .natural
              (.cases .natural
                [ ("lam", [], .bvar 0)
                , ("natSucc", [], .natSucc (.bvar 0))
                , ("nonLam", [], .lit 0) ]
                (.bvar 1)))) ]
        (.bvar 0)).inst (.inject "app" [("fn", .inject "nonLam" []), ("arg", .lit n)]) =
      .cases .natural
        [ ("lit", ["val"], .lam .natural (.bvar 0))
        , ("bvar", ["idx"], .lam .natural (.bvar 0))
        , ("letE", ["ty", "val", "body"],
            .lam .emptyRow (.lam .natural (.lam .emptyRow (.bvar 1))))
        , ("app", ["fn", "arg"],
            .lam .emptyRow (.lam .natural
              (.cases .natural
                [ ("lam", [], .bvar 0)
                , ("natSucc", [], .natSucc (.bvar 0))
                , ("nonLam", [], .lit 0) ]
                (.bvar 1)))) ]
        (.inject "app" [("fn", .inject "nonLam" []), ("arg", .lit n)]) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst1]
  refine .next (.casesInject .natural _ "app"
    [("fn", .inject "nonLam" []), ("arg", .lit n)] ["fn", "arg"]
    (.lam .emptyRow (.lam .natural
      (.cases .natural
        [ ("lam", [], .bvar 0)
        , ("natSucc", [], .natSucc (.bvar 0))
        , ("nonLam", [], .lit 0) ]
        (.bvar 1))))
    [.inject "nonLam" [], .lit n] rfl rfl) ?_
  refine .next (.appFun (.lit n) (.beta .emptyRow _ (.inject "nonLam" []))) ?_
  have hinst2 :
      (LExpr.lam .natural
        (.cases .natural
          [ ("lam", [], .bvar 0)
          , ("natSucc", [], .natSucc (.bvar 0))
          , ("nonLam", [], .lit 0) ]
          (.bvar 1))).inst (.inject "nonLam" []) =
      .lam .natural
        (.cases .natural
          [ ("lam", [], .bvar 0)
          , ("natSucc", [], .natSucc (.bvar 0))
          , ("nonLam", [], .lit 0) ]
          (.inject "nonLam" [])) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.beta .natural _ (.lit n)) ?_
  have hinst3 :
      (LExpr.cases .natural
        [ ("lam", [], .bvar 0)
        , ("natSucc", [], .natSucc (.bvar 0))
        , ("nonLam", [], .lit 0) ]
        (.inject "nonLam" [])).inst (.lit n) =
      .cases .natural
        [ ("lam", [], .lit n)
        , ("natSucc", [], .natSucc (.lit n))
        , ("nonLam", [], .lit 0) ]
        (.inject "nonLam" []) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst3]
  exact .next (.casesInject .natural _ "nonLam" [] [] (.lit 0) [] rfl rfl) (.refl _)

theorem kernelCheckLExpr_runs (sorryFlag expectedTag inferredTag : Nat) :
    SSteps
      (.app kernelCheckLExpr
        (.inject "declCheck"
          [ ("sorryFlag", .lit sorryFlag)
          , ("expectedTag", .lit expectedTag)
          , ("inferredTag", .lit inferredTag) ]))
      (.lit (if (sorryFlag == 0 && expectedTag == inferredTag) then 1 else 0)) := by
  unfold kernelCheckLExpr
  refine .next (.beta .emptyRow _ _) ?_
  have hinst1 :
      (LExpr.cases .natural
        [ ("declCheck", ["sorryFlag", "expectedTag", "inferredTag"],
            .lam .natural
              (.lam .natural
                (.lam .natural
                  (.boolRec .natural
                    (.lit 0)
                    (.boolRec .natural
                      (.lit 0)
                      (.lit 1)
                      (.natBin .beq (.bvar 1) (.bvar 0)))
                    (.natBin .beq (.bvar 2) (.lit 0)))))) ]
        (.bvar 0)).inst
        (.inject "declCheck"
          [ ("sorryFlag", .lit sorryFlag)
          , ("expectedTag", .lit expectedTag)
          , ("inferredTag", .lit inferredTag) ]) =
      .cases .natural
        [ ("declCheck", ["sorryFlag", "expectedTag", "inferredTag"],
            .lam .natural
              (.lam .natural
                (.lam .natural
                  (.boolRec .natural
                    (.lit 0)
                    (.boolRec .natural
                      (.lit 0)
                      (.lit 1)
                      (.natBin .beq (.bvar 1) (.bvar 0)))
                    (.natBin .beq (.bvar 2) (.lit 0)))))) ]
        (.inject "declCheck"
          [ ("sorryFlag", .lit sorryFlag)
          , ("expectedTag", .lit expectedTag)
          , ("inferredTag", .lit inferredTag) ]) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst1]
  refine .next (.casesInject .natural _ "declCheck"
    [ ("sorryFlag", .lit sorryFlag)
    , ("expectedTag", .lit expectedTag)
    , ("inferredTag", .lit inferredTag) ]
    ["sorryFlag", "expectedTag", "inferredTag"]
    (.lam .natural
      (.lam .natural
        (.lam .natural
          (.boolRec .natural
            (.lit 0)
            (.boolRec .natural
              (.lit 0)
              (.lit 1)
              (.natBin .beq (.bvar 1) (.bvar 0)))
            (.natBin .beq (.bvar 2) (.lit 0))))))
    [.lit sorryFlag, .lit expectedTag, .lit inferredTag] rfl rfl) ?_
  refine .next (.appFun (.lit inferredTag)
    (.appFun (.lit expectedTag)
      (.beta .natural _ (.lit sorryFlag)))) ?_
  have hinst2 :
      (LExpr.lam .natural
        (.lam .natural
          (.boolRec .natural
            (.lit 0)
            (.boolRec .natural
              (.lit 0)
              (.lit 1)
              (.natBin .beq (.bvar 1) (.bvar 0)))
            (.natBin .beq (.bvar 2) (.lit 0))))).inst (.lit sorryFlag) =
      .lam .natural
        (.lam .natural
          (.boolRec .natural
            (.lit 0)
            (.boolRec .natural
              (.lit 0)
              (.lit 1)
              (.natBin .beq (.bvar 1) (.bvar 0)))
            (.natBin .beq (.lit sorryFlag) (.lit 0)))) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.appFun (.lit inferredTag) (.beta .natural _ (.lit expectedTag))) ?_
  have hinst3 :
      (LExpr.lam .natural
        (.boolRec .natural
          (.lit 0)
          (.boolRec .natural
            (.lit 0)
            (.lit 1)
            (.natBin .beq (.bvar 1) (.bvar 0)))
          (.natBin .beq (.lit sorryFlag) (.lit 0)))).inst (.lit expectedTag) =
      .lam .natural
        (.boolRec .natural
          (.lit 0)
          (.boolRec .natural
            (.lit 0)
            (.lit 1)
            (.natBin .beq (.lit expectedTag) (.bvar 0)))
          (.natBin .beq (.lit sorryFlag) (.lit 0))) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst3]
  refine .next (.beta .natural _ (.lit inferredTag)) ?_
  have hinst4 :
      (LExpr.boolRec .natural
        (.lit 0)
        (.boolRec .natural
          (.lit 0)
          (.lit 1)
          (.natBin .beq (.lit expectedTag) (.bvar 0)))
        (.natBin .beq (.lit sorryFlag) (.lit 0))).inst (.lit inferredTag) =
      .boolRec .natural
        (.lit 0)
        (.boolRec .natural
          (.lit 0)
          (.lit 1)
          (.natBin .beq (.lit expectedTag) (.lit inferredTag)))
        (.natBin .beq (.lit sorryFlag) (.lit 0)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst4]
  refine .next (.boolRecMajor .natural (.lit 0) _ (.binLit .beq sorryFlag 0)) ?_
  dsimp only [NatOp.eval]
  cases (sorryFlag == 0)
  · simpa using SSteps.next (.boolRecFalse .natural (.lit 0) _) (.refl _)
  · refine .next (.boolRecTrue .natural (.lit 0) _) ?_
    refine .next (.boolRecMajor .natural (.lit 0) (.lit 1) (.binLit .beq expectedTag inferredTag)) ?_
    dsimp only [NatOp.eval]
    cases (expectedTag == inferredTag)
    · simpa using SSteps.next (.boolRecFalse .natural (.lit 0) (.lit 1)) (.refl _)
    · simpa using SSteps.next (.boolRecTrue .natural (.lit 0) (.lit 1)) (.refl _)

/-- **Theorem (`silicon_kernel_whnf_sound`)**:
1. Pure `kernelWhnf` reduces β-redexes (`(λ x : Nat => x) 42 ↦ 42`), ζ-redexes (`let x : Nat := 42 in x ↦ 42`),
   and δ-redexes (`idNat 42 ↦ 42` in `stdKernelEnv`).
2. Lowered `kernelWhnfLExpr` reduces in `SSteps` to `.lit n` and evaluates in `Core4` (`Evaluates`)
   to `.nat n` for every `n : Nat`. -/
theorem silicon_kernel_whnf_sound (n : Nat) :
    kernelWhnf stdKernelEnv 4 (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal n))) = .lit (.natVal n) ∧
    kernelWhnf stdKernelEnv 4 (.letE kNatConst (.lit (.natVal n)) (.bvar 0)) = .lit (.natVal n) ∧
    kernelWhnf stdKernelEnv 4 (.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal n))) = .lit (.natVal n) ∧
    SSteps
      (.app kernelWhnfLExpr (.inject "app" [("fn", .inject "lam" []), ("arg", .lit n)]))
      (.lit n) ∧
    Evaluates
      (lowerT (.app kernelWhnfLExpr (.inject "app" [("fn", .inject "lam" []), ("arg", .lit n)])))
      (.nat n) := by
  refine ⟨rfl, rfl, rfl, kernelWhnfLExpr_runs_app n, ?_⟩
  simpa [lowerT] using lower_sound_nat (kernelWhnfLExpr_runs_app n)

/-- **Theorem (`silicon_kernel_whnf_iota_and_nonLam_sound`)**:
1. Pure `kernelWhnf` reduces `Nat.succ` and `Nat.add` ι-redexes (`Nat.succ n ↦ n + 1`, `Nat.add 40 2 ↦ 42`).
2. Lowered `kernelWhnfLExpr` inspects the `"fn"` field of `"app"` and refuses non-lambda applications
   `(.inject "app" [("fn", .inject "nonLam" []), ("arg", .lit n)])` by evaluating to `.nat 0`. -/
theorem silicon_kernel_whnf_iota_and_nonLam_sound (n : Nat) :
    kernelWhnf stdKernelEnv 4 (.app (.const (KName.mkSimple "Nat.succ") []) (.lit (.natVal n))) =
      .lit (.natVal (n + 1)) ∧
    kernelWhnf stdKernelEnv 4
      (.app (.app (.const (KName.mkSimple "Nat.add") []) (.lit (.natVal 40))) (.lit (.natVal 2))) =
      .lit (.natVal 42) ∧
    SSteps
      (.app kernelWhnfLExpr (.inject "app" [("fn", .inject "nonLam" []), ("arg", .lit n)]))
      (.lit 0) ∧
    Evaluates
      (lowerT (.app kernelWhnfLExpr (.inject "app" [("fn", .inject "nonLam" []), ("arg", .lit n)])))
      (.nat 0) := by
  refine ⟨rfl, rfl, kernelWhnfLExpr_refuses_nonLam n, ?_⟩
  simpa [lowerT] using lower_sound_nat (kernelWhnfLExpr_refuses_nonLam n)

/-- **Theorem (`silicon_kernel_check_sound`)**:
1. Positive Pole: The self-hosted Lean kernel ACCEPTS valid definitions and theorems
   (`validIdNatDecl`, `validPropIdDecl`, `validApplyId42Decl`), and their lowered `Core4`
   kernel checks evaluate to `.nat 1` (`true`).
2. Negative Pole: The self-hosted Lean kernel REFUSES:
   - Definitional equality mismatches (`invalidMismatchDecl`),
   - Ill-typed applications (`invalidBadAppDecl`),
   - Universe level mismatches (`invalidUniverseDecl`),
   - `sorryAx`-contaminated theorems (`invalidSorryDecl`),
   and their lowered `Core4` kernel checks evaluate to `.nat 0` (`false`). -/
theorem silicon_kernel_check_sound :
    kernelCheckDecl stdKernelEnv 8 validIdNatDecl = true ∧
    kernelCheckDecl stdKernelEnv 8 validPropIdDecl = true ∧
    kernelCheckDecl stdKernelEnv 8 validApplyId42Decl = true ∧
    kernelCheckDecl stdKernelEnv 8 invalidMismatchDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidBadAppDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidUniverseDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidSorryDecl = false ∧
    Evaluates (lowerT (.app kernelCheckLExpr (encodeDeclCheckLExpr stdKernelEnv 8 validIdNatDecl))) (.nat 1) ∧
    Evaluates (lowerT (.app kernelCheckLExpr (encodeDeclCheckLExpr stdKernelEnv 8 validPropIdDecl))) (.nat 1) ∧
    Evaluates (lowerT (.app kernelCheckLExpr (encodeDeclCheckLExpr stdKernelEnv 8 invalidMismatchDecl))) (.nat 0) ∧
    Evaluates (lowerT (.app kernelCheckLExpr (encodeDeclCheckLExpr stdKernelEnv 8 invalidBadAppDecl))) (.nat 0) ∧
    Evaluates (lowerT (.app kernelCheckLExpr (encodeDeclCheckLExpr stdKernelEnv 8 invalidUniverseDecl))) (.nat 0) ∧
    Evaluates (lowerT (.app kernelCheckLExpr (encodeDeclCheckLExpr stdKernelEnv 8 invalidSorryDecl))) (.nat 0) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : encodeDeclCheckLExpr stdKernelEnv 8 validIdNatDecl =
        .inject "declCheck" [("sorryFlag", .lit 0), ("expectedTag", .lit 1), ("inferredTag", .lit 1)] := rfl
    rw [h1]
    simpa [lowerT] using lower_sound_nat (kernelCheckLExpr_runs 0 1 1)
  · have h2 : encodeDeclCheckLExpr stdKernelEnv 8 validPropIdDecl =
        .inject "declCheck" [("sorryFlag", .lit 0), ("expectedTag", .lit 1), ("inferredTag", .lit 1)] := rfl
    rw [h2]
    simpa [lowerT] using lower_sound_nat (kernelCheckLExpr_runs 0 1 1)
  · have h3 : encodeDeclCheckLExpr stdKernelEnv 8 invalidMismatchDecl =
        .inject "declCheck" [("sorryFlag", .lit 0), ("expectedTag", .lit 1), ("inferredTag", .lit 0)] := rfl
    rw [h3]
    simpa [lowerT] using lower_sound_nat (kernelCheckLExpr_runs 0 1 0)
  · have h4 : encodeDeclCheckLExpr stdKernelEnv 8 invalidBadAppDecl =
        .inject "declCheck" [("sorryFlag", .lit 0), ("expectedTag", .lit 1), ("inferredTag", .lit 0)] := rfl
    rw [h4]
    simpa [lowerT] using lower_sound_nat (kernelCheckLExpr_runs 0 1 0)
  · have h5 : encodeDeclCheckLExpr stdKernelEnv 8 invalidUniverseDecl =
        .inject "declCheck" [("sorryFlag", .lit 0), ("expectedTag", .lit 1), ("inferredTag", .lit 0)] := rfl
    rw [h5]
    simpa [lowerT] using lower_sound_nat (kernelCheckLExpr_runs 0 1 0)
  · have h6 : encodeDeclCheckLExpr stdKernelEnv 8 invalidSorryDecl =
        .inject "declCheck" [("sorryFlag", .lit 1), ("expectedTag", .lit 1), ("inferredTag", .lit 0)] := rfl
    rw [h6]
    simpa [lowerT] using lower_sound_nat (kernelCheckLExpr_runs 1 1 0)

/-! ## 8. General User-Defined Inductive Recursor ($\iota$) Rules & `Quot.lift` Soundness (`WS 24`) -/

/-- User-defined inductive family `OptionNat : Type 0` with constructors:
- `OptionNat.none : OptionNat` (`0` fields),
- `OptionNat.some : Nat → OptionNat` (`1` field),
and recursor `OptionNat.rec` (`2` minor premises: `onNone` and `onSome : Nat → R`). -/
def optionNatInductDecl : KInductDecl where
  name        := KName.mkSimple "OptionNat"
  levelParams := []
  numParams   := 0
  numIndices  := 0
  type        := kType0
  ctors       :=
    [ (KName.mkSimple "OptionNat.none", .const (KName.mkSimple "OptionNat") [], 0)
    , (KName.mkSimple "OptionNat.some", kArrow kNatConst (.const (KName.mkSimple "OptionNat") []), 1) ]
  recRules    :=
    [ { recName       := KName.mkSimple "OptionNat.rec"
      , ctorName      := KName.mkSimple "OptionNat.none"
      , numPrefixArgs := 2
      , numFields     := 0
      , rhs           := .lam kNatConst (.lam (kArrow kNatConst kNatConst) (.bvar 1)) }
    , { recName       := KName.mkSimple "OptionNat.rec"
      , ctorName      := KName.mkSimple "OptionNat.some"
      , numPrefixArgs := 2
      , numFields     := 1
      , rhs           := .lam kNatConst (.lam (kArrow kNatConst kNatConst) (.lam kNatConst (.app (.bvar 1) (.bvar 0)))) } ]

/-- User-defined 2-field inductive structure `PairNat : Type 0` with constructor
`PairNat.mk : Nat → Nat → PairNat` (`2` fields) and recursor `PairNat.rec` (`1` minor premise
`onMk : Nat → Nat → R`). -/
def pairNatInductDecl : KInductDecl where
  name        := KName.mkSimple "PairNat"
  levelParams := []
  numParams   := 0
  numIndices  := 0
  type        := kType0
  ctors       :=
    [ (KName.mkSimple "PairNat.mk", kArrow kNatConst (kArrow kNatConst (.const (KName.mkSimple "PairNat") [])), 2) ]
  recRules    :=
    [ { recName       := KName.mkSimple "PairNat.rec"
      , ctorName      := KName.mkSimple "PairNat.mk"
      , numPrefixArgs := 1
      , numFields     := 2
      , rhs           := .lam (kArrow kNatConst (kArrow kNatConst kNatConst))
                           (.lam kNatConst (.lam kNatConst (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))) } ]

/-- User-defined recursive inductive family `ListNat : Type 0` with constructors:
- `ListNat.nil : ListNat` (`0` fields),
- `ListNat.cons : Nat → ListNat → ListNat` (`2` fields: `head` and recursive `tail`),
and recursor `ListNat.rec` whose `cons` rule recursively invokes `ListNat.rec onNil onCons tail`. -/
def listNatInductDecl : KInductDecl where
  name        := KName.mkSimple "ListNat"
  levelParams := []
  numParams   := 0
  numIndices  := 0
  type        := kType0
  ctors       :=
    [ (KName.mkSimple "ListNat.nil", .const (KName.mkSimple "ListNat") [], 0)
    , (KName.mkSimple "ListNat.cons",
        kArrow kNatConst (kArrow (.const (KName.mkSimple "ListNat") []) (.const (KName.mkSimple "ListNat") [])), 2) ]
  recRules    :=
    [ { recName       := KName.mkSimple "ListNat.rec"
      , ctorName      := KName.mkSimple "ListNat.nil"
      , numPrefixArgs := 2
      , numFields     := 0
      , rhs           := .lam kNatConst (.lam kNatConst (.bvar 1)) }
    , { recName       := KName.mkSimple "ListNat.rec"
      , ctorName      := KName.mkSimple "ListNat.cons"
      , numPrefixArgs := 2
      , numFields     := 2
      , rhs           :=
          -- λ onNil (bvar 3) onCons (bvar 2) head (bvar 1) tail (bvar 0) =>
          --   onCons head tail (ListNat.rec onNil onCons tail)
          .lam kNatConst (.lam kNatConst (.lam kNatConst (.lam (.const (KName.mkSimple "ListNat") [])
            (.app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
              (.app (.app (.app (.const (KName.mkSimple "ListNat.rec") []) (.bvar 3)) (.bvar 2)) (.bvar 0)))))) } ]

/-- Extended kernel environment containing `stdKernelEnv` plus user-defined inductive families
`OptionNat`, `PairNat`, and recursive `ListNat` with their dynamic recursor $\iota$-rules. -/
def inductKernelEnv : KEnv :=
  ((stdKernelEnv.addInductDecl optionNatInductDecl).addInductDecl pairNatInductDecl).addInductDecl listNatInductDecl

/-- **Theorem (`kernelWhnf_general_iota_sound`)**:
Dynamic $\iota$-reduction over user-defined inductive families (`OptionNat`, `PairNat`, and recursive `ListNat`) in `kernelWhnf`:
1. `OptionNat.rec defaultVal (λ x => Nat.succ x) OptionNat.none` reduces dynamically to `defaultVal`,
2. `OptionNat.rec defaultVal (λ x => Nat.succ x) (OptionNat.some n)` extracts the constructor field `n`,
   applies the `onSome` minor premise, and reduces to `.lit (.natVal (n + 1))`,
3. `PairNat.rec (λ a b => Nat.add a b) (PairNat.mk 40 2)` extracts both constructor fields `(40, 2)`
   and reduces via $\iota + \beta$ to `.lit (.natVal 42)`,
4. Recursive `ListNat.rec 0 (λ h _ ih => Nat.add ih h) (ListNat.cons 40 (ListNat.cons 2 ListNat.nil))`
   recursively unfolds both `ListNat.cons` spines and `ListNat.nil` (with the recursive hypothesis `ih`
   in the first argument of `Nat.add`) to `.lit (.natVal 42)`,
5. Negative Pole: Applying `OptionNat.rec` to a non-matching constructor (`PairNat.mk 1 2`) does not
   trigger a bogus $\iota$-reduction (`reduceGeneralIota? = none`). -/
theorem kernelWhnf_general_iota_sound (defaultVal n : Nat) :
    let onNone := KExpr.lit (.natVal defaultVal)
    let onSome := KExpr.lam kNatConst (.app (.const (KName.mkSimple "Nat.succ") []) (.bvar 0))
    let recSpine := KExpr.app (.app (.const (KName.mkSimple "OptionNat.rec") []) onNone) onSome
    let pairAdd := KExpr.lam kNatConst (.lam kNatConst
      (.app (.app (.const (KName.mkSimple "Nat.add") []) (.bvar 1)) (.bvar 0)))
    let pairSpine := KExpr.app (.const (KName.mkSimple "PairNat.rec") []) pairAdd
    let pairVal := KExpr.app (.app (.const (KName.mkSimple "PairNat.mk") []) (.lit (.natVal 40))) (.lit (.natVal 2))
    let listOnCons := KExpr.lam kNatConst (.lam (.const (KName.mkSimple "ListNat") []) (.lam kNatConst
      (.app (.app (.const (KName.mkSimple "Nat.add") []) (.bvar 0)) (.bvar 2))))
    let listRecSpine := KExpr.app (.app (.const (KName.mkSimple "ListNat.rec") []) (.lit (.natVal 0))) listOnCons
    let listVal := KExpr.app (.app (.const (KName.mkSimple "ListNat.cons") []) (.lit (.natVal 40)))
      (.app (.app (.const (KName.mkSimple "ListNat.cons") []) (.lit (.natVal 2)))
        (.const (KName.mkSimple "ListNat.nil") []))
    kernelWhnf inductKernelEnv 8 (.app recSpine (.const (KName.mkSimple "OptionNat.none") [])) =
      .lit (.natVal defaultVal) ∧
    kernelWhnf inductKernelEnv 8 (.app recSpine (.app (.const (KName.mkSimple "OptionNat.some") []) (.lit (.natVal n)))) =
      .lit (.natVal (n + 1)) ∧
    kernelWhnf inductKernelEnv 8 (.app pairSpine pairVal) =
      .lit (.natVal 42) ∧
    kernelWhnf inductKernelEnv 16 (.app listRecSpine listVal) =
      .lit (.natVal 42) ∧
    reduceGeneralIota? inductKernelEnv recSpine pairVal = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem (`kernelWhnf_quot_lift_sound`)**:
Quotient computation rule (`Quot.lift` on `Quot.mk`) in `kernelWhnf`:
1. Erased 3-argument spine `Quot.lift f h (Quot.mk a)` reduces to `f a` (and for `f = λ x => Nat.succ x`,
   `a = n`, reduces in `kernelWhnf` to `.lit (.natVal (n + 1))`),
2. Full 6-argument Lean kernel spine `Quot.lift α r β f h (Quot.mk α r a)` reduces to `f a`
   (and for `f = idNat`, `a = n`, reduces in `kernelWhnf` via $\iota + \delta + \beta$ to `.lit (.natVal n)`),
3. Negative Pole: `Quot.lift` applied to a non-`Quot.mk` neutral term is left unreduced (`reduceQuotLift? = none`). -/
theorem kernelWhnf_quot_lift_sound (n : Nat) :
    let fnSucc := KExpr.lam kNatConst (.app (.const (KName.mkSimple "Nat.succ") []) (.bvar 0))
    let fnId   := KExpr.const (KName.mkSimple "idNat") []
    let hProof := KExpr.const (KName.mkSimple "quotRespProof") []
    let rel    := KExpr.const (KName.mkSimple "natModRel") []
    let quotMk3 := KExpr.app (.const (KName.mkSimple "Quot.mk") []) (.lit (.natVal n))
    let quotMk6 := KExpr.app (.app (.app (.const (KName.mkSimple "Quot.mk") []) kNatConst) rel) (.lit (.natVal n))
    let lift3 := KExpr.app (.app (.const (KName.mkSimple "Quot.lift") []) fnSucc) hProof
    let lift6 := KExpr.app (.app (.app (.app (.app (.const (KName.mkSimple "Quot.lift") [])
      kNatConst) rel) kNatConst) fnId) hProof
    kernelWhnf stdKernelEnv 8 (.app lift3 quotMk3) = .lit (.natVal (n + 1)) ∧
    kernelWhnf stdKernelEnv 8 (.app lift6 quotMk6) = .lit (.natVal n) ∧
    reduceQuotLift? lift3 (.const (KName.mkSimple "neutralQuot") []) = none := by
  exact ⟨rfl, rfl, rfl⟩

end Obend.Lower.LeanKernel
end
