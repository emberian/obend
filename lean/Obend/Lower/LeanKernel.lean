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
public import Obend.Tactic.Tooth
public import Obend.Lower.Inductive
public import Obend.Leaf.Specialize
public section

namespace Obend.Lower.LeanKernel
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Leaf
open Obend.Lower
open Obend.Lower.Inductive
set_option autoImplicit false

/-! ## 1. Transparent Structural `BEq` & Kernel Environment Declarations (`KConstInfo`, `KEnv`) -/

/-- Transparent structural `BEq` for `KName` (exposed across modules for kernel reduction). -/
@[expose] def KName.beq : KName → KName → Bool
  | .anonymous, .anonymous => true
  | .str p1 s1, .str p2 s2 => s1 == s2 && KName.beq p1 p2
  | .num p1 i1, .num p2 i2 => i1 == i2 && KName.beq p1 p2
  | _, _ => false

@[simp] theorem KName.beq_refl : ∀ (n : KName), KName.beq n n = true
  | .anonymous => rfl
  | .str p _ => by simp [KName.beq, KName.beq_refl p]
  | .num p _ => by simp [KName.beq, KName.beq_refl p]

@[expose] instance (priority := high) : BEq KName := ⟨KName.beq⟩

/-- Transparent structural `BEq` for `KLevel`. -/
@[expose] def KLevel.beq : KLevel → KLevel → Bool
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

@[expose] instance (priority := high) : BEq KLevel := ⟨KLevel.beq⟩

/-- Transparent structural `BEq` for `List KLevel`. -/
@[expose] def KLevel.listBeq : List KLevel → List KLevel → Bool
  | [], [] => true
  | u :: us, v :: vs => KLevel.beq u v && KLevel.listBeq us vs
  | _, _ => false

@[simp] theorem KLevel.listBeq_refl : ∀ (us : List KLevel), KLevel.listBeq us us = true
  | [] => rfl
  | _ :: us => by simp [KLevel.listBeq, KLevel.listBeq_refl us]

@[expose] instance (priority := high) : BEq (List KLevel) := ⟨KLevel.listBeq⟩

/-- Transparent structural `BEq` for `KLiteral`. -/
@[expose] def KLiteral.beq : KLiteral → KLiteral → Bool
  | .natVal n1, .natVal n2 => n1 == n2
  | .strVal s1, .strVal s2 => s1 == s2
  | _, _ => false

@[simp] theorem KLiteral.beq_refl : ∀ (l : KLiteral), KLiteral.beq l l = true
  | .natVal _ => by simp [KLiteral.beq]
  | .strVal _ => by simp [KLiteral.beq]

@[expose] instance (priority := high) : BEq KLiteral := ⟨KLiteral.beq⟩

/-- Transparent structural `BEq` for `KExpr`. -/
@[expose] def KExpr.beq : KExpr → KExpr → Bool
  | .bvar i1, .bvar i2 => i1 == i2
  | .fvar i1, .fvar i2 => i1 == i2
  | .mvar i1, .mvar i2 => i1 == i2
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
  | .mvar _ => by simp [KExpr.beq]
  | .sort _ => by simp [KExpr.beq]
  | .const _ _ => by simp [KExpr.beq]
  | .app f a => by simp [KExpr.beq, KExpr.beq_refl f, KExpr.beq_refl a]
  | .lam d b => by simp [KExpr.beq, KExpr.beq_refl d, KExpr.beq_refl b]
  | .forallE d b => by simp [KExpr.beq, KExpr.beq_refl d, KExpr.beq_refl b]
  | .letE t v b => by simp [KExpr.beq, KExpr.beq_refl t, KExpr.beq_refl v, KExpr.beq_refl b]
  | .lit _ => by simp [KExpr.beq]
  | .proj _ _ e => by simp [KExpr.beq, KExpr.beq_refl e]

@[expose] instance (priority := high) : BEq KExpr := ⟨KExpr.beq⟩

/-- Self-hosted kernel constant declaration (`Lean.ConstantInfo`). -/
inductive KConstInfo where
  | axiomInfo  (name : KName) (levelParams : List KName) (type : KExpr)
  | defnInfo   (name : KName) (levelParams : List KName) (type : KExpr) (value : KExpr)
  | thmInfo    (name : KName) (levelParams : List KName) (type : KExpr) (value : KExpr)
  | inductInfo (name : KName) (levelParams : List KName) (type : KExpr)
  | ctorInfo   (name : KName) (levelParams : List KName) (type : KExpr) (inductName : KName)
  deriving @[expose] DecidableEq, Repr, Inhabited

/-- Declaration name of a `KConstInfo`. -/
@[expose] def KConstInfo.name : KConstInfo → KName
  | .axiomInfo n _ _    => n
  | .defnInfo n _ _ _   => n
  | .thmInfo n _ _ _    => n
  | .inductInfo n _ _   => n
  | .ctorInfo n _ _ _   => n

/-- Universe level parameter names of a `KConstInfo`. -/
@[expose] def KConstInfo.levelParams : KConstInfo → List KName
  | .axiomInfo _ ps _    => ps
  | .defnInfo _ ps _ _   => ps
  | .thmInfo _ ps _ _    => ps
  | .inductInfo _ ps _   => ps
  | .ctorInfo _ ps _ _   => ps

/-- Type expression of a `KConstInfo`. -/
@[expose] def KConstInfo.type : KConstInfo → KExpr
  | .axiomInfo _ _ t    => t
  | .defnInfo _ _ t _   => t
  | .thmInfo _ _ t _    => t
  | .inductInfo _ _ t   => t
  | .ctorInfo _ _ t _   => t

/-- General recursor computation rule (`Lean.RecursorRule`) for user-defined inductive families:
when `recName.{recLevels}` is applied to `numPrefixArgs` prefix arguments (parameters, motives, and
minor premises) followed by a major premise headed by `ctorName` carrying `numFields` constructor
field arguments (after any inductive parameters), $\iota$-reduction instantiates `levelParams` in
`rhs` with `recLevels` and rewrites the spine to `rhsInst` applied to `prefixArgs ++ fieldArgs`. -/
structure KRecRule where
  recName       : KName
  ctorName      : KName
  levelParams   : List KName := []
  numPrefixArgs : Nat
  numFields     : Nat
  rhs           : KExpr
  deriving @[expose] DecidableEq, Repr, Inhabited

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
  deriving @[expose] DecidableEq, Repr, Inhabited

/-- Self-hosted kernel environment (`Lean.Environment`). -/
structure KEnv where
  constants   : List KConstInfo
  recRules    : List KRecRule := []
  inductDecls : List KInductDecl := []
  deriving @[expose] DecidableEq, Repr, Inhabited

/-- Look up a declaration by `KName` in a `KEnv`. -/
@[expose] def KEnv.find? (env : KEnv) (name : KName) : Option KConstInfo :=
  env.constants.find? (fun info => info.name == name)

/-- Look up a recursor $\iota$-rule by `(recName, ctorName)` in a `KEnv`. -/
@[expose] def KEnv.findRecRule? (env : KEnv) (recName ctorName : KName) : Option KRecRule :=
  env.recRules.find? (fun r => r.recName == recName && r.ctorName == ctorName)

/-- Extend a `KEnv` with a verified `KConstInfo`. -/
@[expose] def KEnv.add (env : KEnv) (info : KConstInfo) : KEnv :=
  { env with constants := info :: env.constants }

/-- Register a user-defined `KInductDecl` (its type, constructors, and recursor $\iota$-rules) into `KEnv`. -/
@[expose] def KEnv.addInductDecl (env : KEnv) (decl : KInductDecl) : KEnv :=
  let indConst : KConstInfo := .inductInfo decl.name decl.levelParams decl.type
  let ctorConsts : List KConstInfo :=
    decl.ctors.map (fun (cName, cTy, _) => .ctorInfo cName decl.levelParams cTy decl.name)
  { constants   := indConst :: (ctorConsts ++ env.constants)
  , recRules    := decl.recRules ++ env.recRules
  , inductDecls := decl :: env.inductDecls }

/-! ## 2. Universe Level Normalization, `imax`, and Equivalence (`kernelImax`, `kernelLevelEq`) -/

/-- Substitute universe level parameters in a `KLevel`. -/
@[expose] def KLevel.substParams (subst : List (KName × KLevel)) : KLevel → KLevel
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
@[expose] def KLevel.evalConcrete : KLevel → Option Nat
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
@[expose] def KLevel.mkMax (u v : KLevel) : KLevel :=
  if u == .zero then v
  else if v == .zero then u
  else if u == v then u
  else .max u v

/-- Algebraic `imax` smart constructor simplifying `imax u 0 = 0`, `imax 0 u = u`, `imax u u = u`,
`imax u (succ v) = max u (succ v)`, and `imax w (max u v) = max (imax w u) (imax w v)`. -/
@[expose] def KLevel.mkIMax (u : KLevel) : KLevel → KLevel
  | .zero => .zero
  | .succ v' =>
    if u == .zero then .succ v'
    else if u == .succ v' then u
    else KLevel.mkMax u (.succ v')
  | .max v1 v2 =>
    if u == .zero then KLevel.mkMax v1 v2
    else if u == .max v1 v2 then u
    else KLevel.mkMax (KLevel.mkIMax u v1) (KLevel.mkIMax u v2)
  | v =>
    if u == .zero then v
    else if u == v then u
    else
      match KLevel.evalConcrete v with
      | some 0 => .zero
      | _ => .imax u v

/-- Normalize a universe level algebraically (simplifying `max` and impredicative `imax` laws,
including `imax w (max u v) = max (imax w u) (imax w v)`, even in the presence of universe parameters `.param`). -/
@[expose] def KLevel.normalize : KLevel → KLevel
  | .zero       => .zero
  | .succ l     => .succ (KLevel.normalize l)
  | .max l1 l2  => KLevel.mkMax (KLevel.normalize l1) (KLevel.normalize l2)
  | .imax l1 l2 => KLevel.mkIMax (KLevel.normalize l1) (KLevel.normalize l2)
  | .param n    => .param n

/-- Alias `KLevel.norm` to `KLevel.normalize`. -/
@[expose] abbrev KLevel.norm : KLevel → KLevel := KLevel.normalize

/-- Construct the impredicative `imax` universe level, simplifying `imax u 0 = 0` immediately. -/
@[expose] def kernelImax (u v : KLevel) : KLevel :=
  KLevel.mkIMax (KLevel.normalize u) (KLevel.normalize v)

/-- Symmetric/commutative equivalence on normalized `KLevel`s (`max u v ≡ max v u`). -/
@[expose] def KLevel.equivComm : KLevel → KLevel → Bool
  | u, v =>
    if u == v then true
    else
      match u, v with
      | .succ u1, .succ v1 => KLevel.equivComm u1 v1
      | .max a1 b1, .max a2 b2 =>
        (KLevel.equivComm a1 a2 && KLevel.equivComm b1 b2) ||
        (KLevel.equivComm a1 b2 && KLevel.equivComm b1 a2)
      | .imax a1 b1, .imax a2 b2 =>
        KLevel.equivComm a1 a2 && KLevel.equivComm b1 b2
      | _, _ => false

/-- Decide universe level equivalence: checks syntactic equality, algebraic `imax`/`max`
normalization (`KLevel.normalize`) with symmetric `max u v == max v u` (`KLevel.equivComm`),
and concrete level evaluation (`KLevel.evalConcrete`). -/
@[expose] def kernelLevelEq (u v : KLevel) : Bool :=
  if u == v then true
  else
    let nu := KLevel.normalize u
    let nv := KLevel.normalize v
    if KLevel.equivComm nu nv then true
    else
      match KLevel.evalConcrete u, KLevel.evalConcrete v with
      | some ku, some kv => ku == kv
      | _, _ => false

/-- Alias `klevelEquivB` to `kernelLevelEq`. -/
@[expose] abbrev klevelEquivB : KLevel → KLevel → Bool := kernelLevelEq

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
    simp [kernelLevelEq, KLevel.normalize, KLevel.mkMax, KLevel.mkIMax, KLevel.equivComm, BEq.beq, KLevel.beq]

/-- List-wise universe level equality. -/
@[expose] def kernelLevelListEq : List KLevel → List KLevel → Bool
  | [], [] => true
  | u :: us, v :: vs => kernelLevelEq u v && kernelLevelListEq us vs
  | _, _ => false

theorem kernelLevelListEq_refl : ∀ (us : List KLevel), kernelLevelListEq us us = true
  | [] => rfl
  | u :: us => by simp [kernelLevelListEq, kernelLevelEq_refl u, kernelLevelListEq_refl us]

/-! ## 3. De Bruijn Instantiation and Level Substitution on `KExpr` -/

/-- Substitute universe level parameters throughout a `KExpr`. -/
@[expose] def KExpr.instantiateLevelParams (subst : List (KName × KLevel)) : KExpr → KExpr
  | .bvar i        => .bvar i
  | .fvar id       => .fvar id
  | .mvar id       => .mvar id
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
@[expose] def KExpr.liftLooseBVars (cutoff delta : Nat) : KExpr → KExpr
  | .bvar i        => if i >= cutoff then .bvar (i + delta) else .bvar i
  | .fvar id       => .fvar id
  | .mvar id       => .mvar id
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
@[expose] def KExpr.instantiateAt (depth : Nat) (arg : KExpr) : KExpr → KExpr
  | .bvar i =>
    if i == depth then KExpr.liftLooseBVars 0 depth arg
    else if i > depth then .bvar (i - 1)
    else .bvar i
  | .fvar id       => .fvar id
  | .mvar id       => .mvar id
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
@[expose] def KExpr.instantiate1 (body arg : KExpr) : KExpr :=
  KExpr.instantiateAt 0 arg body

/-! ## 4. Pure Kernel WHNF, Definitional Equality, Type Inference, and Declaration Checking -/

/-- Extract the head constant name and argument spine of a constructor application `C a₀ … aₖ`. -/
@[expose] def extractCtorArgs : KExpr → Option (KName × List KExpr)
  | .const n _ => some (n, [])
  | .app f a => do
    let (n, args) ← extractCtorArgs f
    pure (n, args ++ [a])
  | _ => none

/-- Extract the head constant name, universe levels, and argument spine of `C.{us} a₀ … aₖ`. -/
@[expose] def extractCtorArgsWithLevels : KExpr → Option (KName × List KLevel × List KExpr)
  | .const n us => some (n, us, [])
  | .app f a => do
    let (n, us, args) ← extractCtorArgsWithLevels f
    pure (n, us, args ++ [a])
  | _ => none

/-- Kernel `Nat` literal & `Bool.rec` ι-reduction rule (`reduceNatIota?`):
reduces closed `Nat.succ`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.beq`, `Nat.ble` on `.natVal` literals
and `Bool.rec` on `Bool.true`/`Bool.false`. -/
@[expose] def reduceNatIota? (f' a' : KExpr) : Option KExpr :=
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
reduces `Quot.lift f h (Quot.mk α r a) ↦ f a` and `Quot.lift α r β f h (Quot.mk α r a) ↦ f a`,
requiring `mkArgs.length == 3` (`[α, r, a]`) on `Quot.mk`. -/
@[expose] def reduceQuotLift? (f' a' : KExpr) : Option KExpr := do
  let (fnName, prefixArgs) ← extractCtorArgs f'
  let (ctorName, mkArgs) ← extractCtorArgs a'
  if fnName == KName.mkSimple "Quot.lift" && ctorName == KName.mkSimple "Quot.mk" && mkArgs.length == 3 then
    let valArg ← mkArgs.getLast?
    match prefixArgs with
    | [fn, _h] => some (.app fn valArg)
    | [_alpha, _rel, _beta, fn, _h] => some (.app fn valArg)
    | _ => none
  else
    none

/-- Dynamic general inductive recursor $\iota$-reduction (`reduceGeneralIota?`):
Given a recursor application spine `R.{recLevels} p₁ … pₘ` (`f'`) and major premise `C a₁ … aₖ` (`a'`)
in WHNF, looks up a matching `KRecRule` in `env.recRules`, resolves the recursor universe parameters
(`rule.levelParams`, falling back to `env.find? recName` if unspecified), checks universe arity,
`prefixArgs.length == rule.numPrefixArgs`, and `ctorArgs.length >= rule.numFields`, instantiates
universe level parameters in `rule.rhs` with `recLevels`, and returns
`(prefixArgs ++ fieldArgs).foldl KExpr.app rhsInst`. -/
@[expose] def reduceGeneralIota? (env : KEnv) (f' a' : KExpr) : Option KExpr := do
  let (recName, recLevels, prefixArgs) ← extractCtorArgsWithLevels f'
  let (ctorName, ctorArgs) ← extractCtorArgs a'
  let rule ← env.findRecRule? recName ctorName
  let lparams :=
    if !rule.levelParams.isEmpty then rule.levelParams
    else
      match env.find? recName with
      | some ci => ci.levelParams
      | none => []
  if (lparams.isEmpty || lparams.length == recLevels.length) &&
     prefixArgs.length == rule.numPrefixArgs &&
     ctorArgs.length >= rule.numFields then
    let fieldArgs := ctorArgs.drop (ctorArgs.length - rule.numFields)
    let rhsInst :=
      if lparams.isEmpty then rule.rhs
      else KExpr.instantiateLevelParams (lparams.zip recLevels) rule.rhs
    some ((prefixArgs ++ fieldArgs).foldl KExpr.app rhsInst)
  else
    none

/-- Fuel-bounded Weak-Head Normal Form (`whnf`) in the self-hosted Lean kernel:
performs β-reduction (`.app (.lam _ b) a`), ζ-reduction (`.letE _ v b`), δ-reduction
(unfolding `.defnInfo` constants from `env`), ι-reduction (`Nat` literals, `Bool.rec`,
general user-defined inductive `KRecRule`s, and `Quot.lift` on `Quot.mk`),
and structure projection reduction (`.proj`, applying `numParams` offset `args[numParams + idx]?`). -/
@[expose] def kernelWhnf (env : KEnv) : Nat → KExpr → KExpr
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
            let numParams :=
              match env.inductDecls.find? (fun d => d.name == s) with
              | some d => d.numParams
              | none => 0
            match args[numParams + idx]? with
            | some fieldVal => kernelWhnf env fuel fieldVal
            | none => .proj s idx e'
          else .proj s idx e'
        | _ => .proj s idx e'
      | none => .proj s idx e'
    | _ => e

/-- Expand a `Nat` literal one constructor layer (`0 ↦ Nat.zero`, `n + 1 ↦ Nat.succ (.lit n)`). -/
@[expose] def natLitToKExpr : Nat → KExpr
  | 0     => .const (KName.mkSimple "Nat.zero") []
  | n + 1 => .app (.const (KName.mkSimple "Nat.succ") []) (.lit (.natVal n))

/-- Single-step `Nat`-literal ↔ `Nat.zero` / `Nat.succ` bridge for definitional equality. -/
@[expose] def stepNatLitBridge : KExpr → KExpr → Option (KExpr × KExpr)
  | .lit (.natVal 0), .const n [] =>
    if n == KName.mkSimple "Nat.zero" then some (.lit (.natVal 0), .lit (.natVal 0)) else none
  | .const n [], .lit (.natVal 0) =>
    if n == KName.mkSimple "Nat.zero" then some (.lit (.natVal 0), .lit (.natVal 0)) else none
  | .lit (.natVal (k + 1)), .app (.const n []) arg =>
    if n == KName.mkSimple "Nat.succ" then some (.lit (.natVal k), arg) else none
  | .app (.const n []) arg, .lit (.natVal (k + 1)) =>
    if n == KName.mkSimple "Nat.succ" then some (arg, .lit (.natVal k)) else none
  | _, _ => none

/-- Single-step $\lambda$-$\eta$ expansion candidate `(dom, lhsBody, rhsBody)`. -/
@[expose] def stepLamEta : KExpr → KExpr → Option (KExpr × KExpr × KExpr)
  | .lam dom body, other =>
    some (dom, body, .app (KExpr.liftLooseBVars 0 1 other) (.bvar 0))
  | other, .lam dom body =>
    some (dom, .app (KExpr.liftLooseBVars 0 1 other) (.bvar 0), body)
  | _, _ => none

/-- Check domain compatibility (`etaDomCompat`) during one-sided $\lambda$-$\eta$ expansion:
fails closed (`false`) whenever `inferPrev ctx other` returns `none` or its WHNF is not `.forallE`! -/
@[expose] def etaDomCompat (env : KEnv) (fuel : Nat)
    (inferPrev : List KExpr → KExpr → Option KExpr)
    (defEqPrev : List KExpr → KExpr → KExpr → Bool)
    (ctx : List KExpr) (dom other : KExpr) : Bool :=
  match inferPrev ctx other with
  | some otherTy =>
    match kernelWhnf env fuel otherTy with
    | .forallE otherDom _ => defEqPrev ctx dom otherDom
    | _ => false
  | none => false

/-- Single-step proposition check (`ty : Sort 0` / `Prop`) given the previous fuel's `inferPrev`. -/
@[expose] def isPropTypeStep (env : KEnv) (fuel : Nat)
    (inferPrev : List KExpr → KExpr → Option KExpr)
    (ctx : List KExpr) (ty : KExpr) : Bool :=
  match inferPrev ctx ty with
  | some kind =>
    match kernelWhnf env fuel kind with
    | .sort u => kernelLevelEq u .zero
    | _ => false
  | none => false

/-- Instantiate leading `.forallE` binders of a constructor telescope with `paramArgs`. -/
@[expose] def instantiateParamsTele : List KExpr → KExpr → Option KExpr
  | [], tele => some tele
  | p :: ps, .forallE _ body => instantiateParamsTele ps (KExpr.instantiate1 body p)
  | _ :: _, _ => none

/-- Walk a constructor's field telescope to extract the type of field `targetIdx`, instantiating
earlier fields `j < targetIdx` with `.proj s j structExpr`. -/
@[expose] def inferFieldFromTele? (s : KName) (structExpr : KExpr) (curIdx : Nat) :
    Nat → KExpr → Option KExpr
  | 0, .forallE dom _ => some dom
  | k + 1, .forallE _ body =>
    inferFieldFromTele? s structExpr (curIdx + 1) k (KExpr.instantiate1 body (.proj s curIdx structExpr))
  | _, _ => none

/-- Infer the type of a structure projection `.proj s idx structExpr` from `structExpr`'s inferred
type `structTy` and the structure constructor's `.forallE` field telescope in `env`. -/
@[expose] def inferProjFieldType? (env : KEnv) (fuel : Nat) (s : KName) (idx : Nat)
    (structExpr structTy : KExpr) : Option KExpr := do
  let structTyWhnf := kernelWhnf env fuel structTy
  let (indName, indLevels, indArgs) ← extractCtorArgsWithLevels structTyWhnf
  if indName != s then none
  else
    let ctorInfo ← env.constants.find? fun info =>
      match info with
      | .ctorInfo _ _ _ cInd => cInd == s
      | _ => false
    if ctorInfo.levelParams.length != indLevels.length then none
    else
      let ctorTyInst := KExpr.instantiateLevelParams (ctorInfo.levelParams.zip indLevels) ctorInfo.type
      let numParams :=
        match env.inductDecls.find? (fun d => d.name == s) with
        | some d => d.numParams
        | none => indArgs.length
      let paramArgs := indArgs.take numParams
      let fieldTele ← instantiateParamsTele paramArgs ctorTyInst
      inferFieldFromTele? s structExpr 0 idx fieldTele

/-- Single fuel step of Bidirectional Type Inference (`inferType`) given `(inferPrev, defEqPrev)`. -/
@[expose] def kernelInferTypeStep (env : KEnv) (fuel : Nat)
    (inferPrev : List KExpr → KExpr → Option KExpr)
    (defEqPrev : List KExpr → KExpr → KExpr → Bool)
    (ctx : List KExpr) (e : KExpr) : Option KExpr :=
  match e with
  | .bvar idx =>
    match ctx[idx]? with
    | some ty => some (KExpr.liftLooseBVars 0 (idx + 1) ty)
    | none => none
  | .fvar _ | .mvar _ => none
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
    let fnTy ← inferPrev ctx fn
    let argTy ← inferPrev ctx arg
    match kernelWhnf env fuel fnTy with
    | .forallE dom body =>
      if defEqPrev ctx dom argTy then
        some (KExpr.instantiate1 body arg)
      else none
    | _ => none
  | .lam dom body => do
    let domKind ← inferPrev ctx dom
    match kernelWhnf env fuel domKind with
    | .sort _ =>
      let bodyTy ← inferPrev (dom :: ctx) body
      some (.forallE dom bodyTy)
    | _ => none
  | .forallE dom body => do
    let domKind ← inferPrev ctx dom
    let bodyKind ← inferPrev (dom :: ctx) body
    match kernelWhnf env fuel domKind, kernelWhnf env fuel bodyKind with
    | .sort u, .sort v => some (.sort (kernelImax u v))
    | _, _ => none
  | .letE ty val body => do
    let tyKind ← inferPrev ctx ty
    match kernelWhnf env fuel tyKind with
    | .sort _ =>
      let valTy ← inferPrev ctx val
      if defEqPrev ctx ty valTy then
        let bodyTy ← inferPrev (ty :: ctx) body
        some (KExpr.instantiate1 bodyTy val)
      else none
    | _ => none
  | .proj s idx structExpr => do
    let structTy ← inferPrev ctx structExpr
    inferProjFieldType? env fuel s idx structExpr structTy

/-- Single fuel step of Context-Aware Definitional Equality (`isDefEq`) given `(inferPrev, defEqPrev)`,
natively executing full $\beta\delta\iota\zeta\eta$ + `Nat`-literal bridging (`stepNatLitBridge`)
+ $\lambda$-$\eta$ (`stepLamEta`) + `Sort 0` (`Prop`) proof-irrelevant conversion (`isPropTypeStep`). -/
@[expose] def kernelIsDefEqStep (env : KEnv) (fuel : Nat)
    (inferPrev : List KExpr → KExpr → Option KExpr)
    (defEqPrev : List KExpr → KExpr → KExpr → Bool)
    (ctx : List KExpr) (t s : KExpr) : Bool :=
  if t == s then true
  else
    let bridgeDirect : Bool :=
      match stepNatLitBridge t s with
      | some (tSub, sSub) => defEqPrev ctx tSub sSub
      | none => false
    if bridgeDirect == true then true
    else
      let proofIrrel : Bool :=
        match inferPrev ctx t, inferPrev ctx s with
        | some tyT, some tyS =>
          isPropTypeStep env fuel inferPrev ctx tyT && defEqPrev ctx tyT tyS
        | _, _ => false
      if proofIrrel == true then true
      else
        let t' := kernelWhnf env fuel t
        let s' := kernelWhnf env fuel s
        if t' == s' then true
        else
          let proofIrrelWhnf : Bool :=
            match inferPrev ctx t', inferPrev ctx s' with
            | some tyT, some tyS =>
              isPropTypeStep env fuel inferPrev ctx tyT && defEqPrev ctx tyT tyS
            | _, _ => false
          if proofIrrelWhnf == true then true
          else
            match stepNatLitBridge t' s' with
            | some (tSub, sSub) => defEqPrev ctx tSub sSub
            | none =>
              match t', s' with
              | .bvar i, .bvar j => i == j
              | .fvar i, .fvar j => i == j
              | .mvar i, .mvar j => i == j
              | .sort u, .sort v => kernelLevelEq u v
              | .const n1 us1, .const n2 us2 =>
                n1 == n2 && kernelLevelListEq us1 us2
              | .app f1 a1, .app f2 a2 =>
                defEqPrev ctx f1 f2 && defEqPrev ctx a1 a2
              | .lam d1 b1, .lam d2 b2 =>
                defEqPrev ctx d1 d2 && defEqPrev (d1 :: ctx) b1 b2
              | .forallE d1 b1, .forallE d2 b2 =>
                defEqPrev ctx d1 d2 && defEqPrev (d1 :: ctx) b1 b2
              | .lit l1, .lit l2 => l1 == l2
              | .proj s1 i1 e1, .proj s2 i2 e2 =>
                s1 == s2 && i1 == i2 && defEqPrev ctx e1 e2
              | _, _ =>
                match stepLamEta t' s' with
                | some (dom, lhsBody, rhsBody) =>
                  let other := match t' with | .lam _ _ => s' | _ => t'
                  let domCompat : Bool :=
                    etaDomCompat env fuel inferPrev defEqPrev ctx dom other
                  domCompat && defEqPrev (dom :: ctx) lhsBody rhsBody
                | none => false

/-- Structurally recursive coupled `(inferType, isDefEq)` engine on `fuel : Nat` (zero `WellFounded.fix`). -/
@[expose] def kernelEngineFuel (env : KEnv) :
    Nat → (List KExpr → KExpr → Option KExpr) × (List KExpr → KExpr → KExpr → Bool)
  | 0 => (fun _ _ => none, fun _ t s => t == s)
  | fuel + 1 =>
    let prev := kernelEngineFuel env fuel
    (kernelInferTypeStep env fuel prev.1 prev.2,
     kernelIsDefEqStep env fuel prev.1 prev.2)

/-- Check whether `ty : KExpr` is a proposition (`ty : Sort 0` / `Prop`) in context `ctx`. -/
@[expose] def isPropType? (env : KEnv) (fuel : Nat) (ctx : List KExpr) (ty : KExpr) : Bool :=
  isPropTypeStep env fuel (kernelEngineFuel env fuel).1 ctx ty

/-- Alias `isPropType` to `isPropType?`. -/
@[expose] abbrev isPropType := isPropType?

/-- Fuel-bounded Bidirectional Type Inference (`inferType`) in the self-hosted Lean kernel.
`ctx` stores types of bound variables (innermost binder at index `0`, shifted appropriately). -/
@[expose] def kernelInferType (env : KEnv) (fuel : Nat) (ctx : List KExpr) (e : KExpr) : Option KExpr :=
  (kernelEngineFuel env fuel).1 ctx e

/-- Context-aware fuel-bounded Definitional Equality (`isDefEq`) in the self-hosted Lean kernel. -/
@[expose] def kernelIsDefEqAux (env : KEnv) (fuel : Nat) (ctx : List KExpr) (t s : KExpr) : Bool :=
  (kernelEngineFuel env fuel).2 ctx t s

/-- Canonical Fuel-bounded Definitional Equality (`isDefEq`) in the self-hosted Lean kernel,
executing full $\beta\delta\iota\zeta\eta$ + `Nat`-literal bridging + `Prop` proof-irrelevant conversion. -/
@[expose, reducible] def kernelIsDefEq (env : KEnv) (fuel : Nat) (t s : KExpr) (ctx : List KExpr := []) : Bool :=
  kernelIsDefEqAux env fuel ctx t s

/-- Alias `kernelIsDefEqFull` to the single canonical `kernelIsDefEq`. -/
@[expose, reducible] def kernelIsDefEqFull (env : KEnv) (fuel : Nat) (t s : KExpr) (ctx : List KExpr := []) : Bool :=
  kernelIsDefEq env fuel t s ctx

theorem kernelIsDefEqAux_refl (env : KEnv) (fuel : Nat) (ctx : List KExpr) (e : KExpr) :
    kernelIsDefEqAux env fuel ctx e e = true := by
  cases fuel <;> simp [kernelIsDefEqAux, kernelEngineFuel, kernelIsDefEqStep, BEq.beq]

theorem kernelIsDefEq_refl (env : KEnv) (fuel : Nat) (e : KExpr) (ctx : List KExpr := []) :
    kernelIsDefEq env fuel e e ctx = true :=
  kernelIsDefEqAux_refl env fuel ctx e

/-- Check whether an expression references `sorryAx` anywhere in its AST. -/
@[expose] def exprContainsSorry : KExpr → Bool
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false
  | .const n _ => n == KName.mkSimple "sorryAx"
  | .app f a | .lam f a | .forallE f a => exprContainsSorry f || exprContainsSorry a
  | .letE t v b => exprContainsSorry t || exprContainsSorry v || exprContainsSorry b
  | .proj _ _ e => exprContainsSorry e

/-- Check whether an expression mentions constant `target` anywhere in its AST. -/
@[expose] def exprMentionsConst (target : KName) : KExpr → Bool
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false
  | .const n _ => n == target
  | .app f a | .lam f a | .forallE f a => exprMentionsConst target f || exprMentionsConst target a
  | .letE t v b => exprMentionsConst target t || exprMentionsConst target v || exprMentionsConst target b
  | .proj _ _ e => exprMentionsConst target e

/-- Check that a constructor parameter domain `dom` is strictly positive in `indName`
(`indName` never appears to the left of an arrow or inside an argument to another type former). -/
@[expose] def isStrictlyPositiveArg (indName : KName) : KExpr → Bool
  | .forallE argDom argCod =>
    !exprMentionsConst indName argDom && isStrictlyPositiveArg indName argCod
  | dom =>
    if !exprMentionsConst indName dom then true
    else
      match extractCtorArgs dom with
      | some (headName, args) =>
        headName == indName && args.all (fun a => !exprMentionsConst indName a)
      | none => false

/-- Check that a constructor type telescope `ctorTy` is strictly positive in `indName`
and returns an application headed by `indName`. -/
@[expose] def checkCtorStrictPositivity (indName : KName) : KExpr → Bool
  | .forallE dom body =>
    isStrictlyPositiveArg indName dom && checkCtorStrictPositivity indName body
  | retTy =>
    match extractCtorArgs retTy with
    | some (headName, args) =>
      headName == indName && args.all (fun a => !exprMentionsConst indName a)
    | none => false

/-- Check strict positivity (`checkInductiveStrictPositivity`) for an inductive type `indName`
across its own type signature and all constructors of `indName` registered in `env`. -/
@[expose] def checkInductiveStrictPositivity (env : KEnv) (indName : KName) (indType : KExpr) : Bool :=
  if exprMentionsConst indName indType then false
  else
    let ctorsInConsts := env.constants.filterMap fun info =>
      match info with
      | .ctorInfo _ _ cTy cInd => if cInd == indName then some cTy else none
      | _ => none
    let ctorsInDecls := (env.inductDecls.filter (fun d => d.name == indName)).flatMap
      (fun d => d.ctors.map (fun (_, cTy, _) => cTy))
    (ctorsInConsts ++ ctorsInDecls).all (checkCtorStrictPositivity indName)

/-- Check whether a `KExpr` is well-typed as a universe sort `.sort u`. -/
@[expose] def kernelIsValidType (env : KEnv) (fuel : Nat) (ty : KExpr) : Bool :=
  match kernelInferType env fuel [] ty with
  | some kind =>
    match kernelWhnf env fuel kind with
    | .sort _ => true
    | _ => false
  | none => false

/-- Check a top-level kernel declaration (`KConstInfo`):
1. Rejects any declaration whose type or value contains `sorryAx`,
2. Verifies that the declaration's type is a valid `.sort u`,
3. For `.inductInfo` and `.ctorInfo`, verifies strict positivity (`checkInductiveStrictPositivity` /
   `checkCtorStrictPositivity`),
4. For `.defnInfo` and `.thmInfo`, infers the type of `value` and verifies definitional equality
   with `type`. -/
@[expose] def kernelCheckDecl (env : KEnv) (fuel : Nat) (decl : KConstInfo) : Bool :=
  match decl with
  | .axiomInfo _ _ ty =>
    !exprContainsSorry ty && kernelIsValidType env fuel ty
  | .inductInfo indName _ ty =>
    !exprContainsSorry ty && kernelIsValidType env fuel ty &&
      checkInductiveStrictPositivity env indName ty
  | .ctorInfo _ _ ty indName =>
    !exprContainsSorry ty && kernelIsValidType env fuel ty &&
      checkCtorStrictPositivity indName ty
  | .defnInfo _ _ ty val | .thmInfo _ _ ty val =>
    if exprContainsSorry ty || exprContainsSorry val then false
    else if !kernelIsValidType env fuel ty then false
    else
      match kernelInferType env fuel [] val with
      | some valTy => kernelIsDefEq env fuel ty valTy
      | none => false

/-! ## 5. Standard Kernel Prelude Environment & Concrete Verification Cases -/

/-- `Type 0` (`Sort 1`). -/
@[expose] def kType0 : KExpr := .sort (.succ .zero)

/-- `Prop` (`Sort 0`). -/
@[expose] def kProp : KExpr := .sort .zero

/-- Constant expression `Nat`. -/
@[expose] def kNatConst : KExpr := .const (KName.mkSimple "Nat") []

/-- Constant expression `Bool`. -/
@[expose] def kBoolConst : KExpr := .const (KName.mkSimple "Bool") []

/-- Non-dependent arrow `A → B` (`∀ (_ : A), B` where `B` has no loose `.bvar 0`). -/
@[expose] def kArrow (a b : KExpr) : KExpr :=
  .forallE a (KExpr.liftLooseBVars 0 1 b)

/-- Standard prelude environment containing `Nat : Type 0`, `Bool : Type 0`, `Nat.zero : Nat`,
`Bool.true : Bool`, and `idNat : Nat → Nat := λ x : Nat => x`. -/
@[expose] def stdKernelEnv : KEnv where
  constants :=
    [ .defnInfo (KName.mkSimple "idNat") [] (kArrow kNatConst kNatConst) (.lam kNatConst (.bvar 0))
    , .ctorInfo (KName.mkSimple "Bool.true") [] kBoolConst (KName.mkSimple "Bool")
    , .ctorInfo (KName.mkSimple "Nat.zero") [] kNatConst (KName.mkSimple "Nat")
    , .inductInfo (KName.mkSimple "Bool") [] kType0
    , .inductInfo (KName.mkSimple "Nat") [] kType0 ]

/-- Valid declaration: `idNat : Nat → Nat := λ (x : Nat) => x`. -/
@[expose] def validIdNatDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "idNat") [] (kArrow kNatConst kNatConst) (.lam kNatConst (.bvar 0))

/-- Valid theorem: `propId : ∀ (P : Prop), P → P := λ (P : Prop) (h : P) => h`. -/
@[expose] def validPropIdDecl : KConstInfo :=
  .thmInfo (KName.mkSimple "propId") []
    (.forallE kProp (.forallE (.bvar 0) (.bvar 1)))
    (.lam kProp (.lam (.bvar 0) (.bvar 0)))

/-- Valid definition using δ-unfolding: `applyId42 : Nat := idNat 42`. -/
@[expose] def validApplyId42Decl : KConstInfo :=
  .defnInfo (KName.mkSimple "applyId42") [] kNatConst
    (.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42)))

/-- Invalid declaration 1 (type mismatch): claims `Bool.true` has type `Nat`. -/
@[expose] def invalidMismatchDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "badMismatch") [] kNatConst
    (.const (KName.mkSimple "Bool.true") [])

/-- Invalid declaration 2 (ill-typed application): applies `idNat : Nat → Nat` to `Bool.true : Bool`. -/
@[expose] def invalidBadAppDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "badApp") [] kNatConst
    (.app (.const (KName.mkSimple "idNat") []) (.const (KName.mkSimple "Bool.true") []))

/-- Invalid declaration 3 (universe mismatch): claims `Nat : Prop` (`Sort 0`) when `Nat : Type 0` (`Sort 1`). -/
@[expose] def invalidUniverseDecl : KConstInfo :=
  .defnInfo (KName.mkSimple "badUniv") [] kProp kNatConst

/-- Invalid declaration 4 (`sorryAx` contamination): proves `∀ (P : Prop), P` using `sorryAx`. -/
@[expose] def invalidSorryDecl : KConstInfo :=
  .thmInfo (KName.mkSimple "badSorry") []
    (.forallE kProp (.bvar 0))
    (.const (KName.mkSimple "sorryAx") [.zero])

/-- Check whether any expression in a `KConstInfo` declaration references `sorryAx`. -/
@[expose] def declContainsSorry : KConstInfo → Bool
  | .axiomInfo _ _ ty | .inductInfo _ _ ty | .ctorInfo _ _ ty _ =>
    exprContainsSorry ty
  | .defnInfo _ _ ty val | .thmInfo _ _ ty val =>
    exprContainsSorry ty || exprContainsSorry val

/-- **Universal `sorryAx` Refusal Theorem (`kernelCheckDecl_refuses_sorry`)**:
For every kernel environment `env`, fuel budget `fuel`, and declaration `decl`, if `declContainsSorry decl = true`
then `kernelCheckDecl env fuel decl = false`. -/
theorem kernelCheckDecl_refuses_sorry (env : KEnv) (fuel : Nat) (decl : KConstInfo)
    (hSorry : declContainsSorry decl = true) :
    kernelCheckDecl env fuel decl = false := by
  cases decl <;> simp_all [declContainsSorry, kernelCheckDecl]

/-- **Universal Kernel WHNF $\beta/\zeta/\delta/\iota$ Reduction (`kernelWhnf_nat_iota_sound`)**:
For all `n1 n2 : Nat`:
1. $\beta$-reduction: `(λ x : Nat => x) n1 ↦ n1`,
2. $\zeta$-reduction: `let x : Nat := n1 in x ↦ n1`,
3. $\delta+\beta$-reduction: `idNat n1 ↦ n1`,
4. `Nat` $\iota$-reduction: `Nat.succ n1 ↦ n1 + 1` and `Nat.add n1 n2 ↦ n1 + n2`. -/
theorem kernelWhnf_nat_iota_sound (n1 n2 : Nat) :
    kernelWhnf stdKernelEnv 4 (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal n1))) = .lit (.natVal n1) ∧
    kernelWhnf stdKernelEnv 4 (.letE kNatConst (.lit (.natVal n1)) (.bvar 0)) = .lit (.natVal n1) ∧
    kernelWhnf stdKernelEnv 4 (.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal n1))) = .lit (.natVal n1) ∧
    kernelWhnf stdKernelEnv 4 (.app (.const (KName.mkSimple "Nat.succ") []) (.lit (.natVal n1))) =
      .lit (.natVal (n1 + 1)) ∧
    kernelWhnf stdKernelEnv 4
      (.app (.app (.const (KName.mkSimple "Nat.add") []) (.lit (.natVal n1))) (.lit (.natVal n2))) =
      .lit (.natVal (n1 + n2)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 6. General User-Defined Inductive Recursor ($\iota$) Rules & `Quot.lift` Soundness (`WS 24`) -/

/-- User-defined inductive family `OptionNat : Type 0` with constructors:
- `OptionNat.none : OptionNat` (`0` fields),
- `OptionNat.some : Nat → OptionNat` (`1` field),
and recursor `OptionNat.rec` (`2` minor premises: `onNone` and `onSome : Nat → R`). -/
@[expose] def optionNatInductDecl : KInductDecl where
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
@[expose] def pairNatInductDecl : KInductDecl where
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
@[expose] def listNatInductDecl : KInductDecl where
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

/-- Universe-polymorphic inductive family `PolyBox.{u} : Sort (u + 2)` with constructor
`PolyBox.mk.{u} : Sort u → PolyBox.{u}` (`1` field) and universe-polymorphic recursor
`PolyBox.rec.{v, u}` (`levelParams := ["v", "u"]`) whose `rhs` instantiates `.sort (.param "v")`
and `.sort (.param "u")`. -/
@[expose] def polyBoxInductDecl : KInductDecl where
  name        := KName.mkSimple "PolyBox"
  levelParams := [KName.mkSimple "u"]
  numParams   := 0
  numIndices  := 0
  type        := .sort (.succ (.succ (.param (KName.mkSimple "u"))))
  ctors       :=
    [ (KName.mkSimple "PolyBox.mk",
        kArrow (.sort (.param (KName.mkSimple "u")))
          (.const (KName.mkSimple "PolyBox") [.param (KName.mkSimple "u")]),
        1) ]
  recRules    :=
    [ { recName       := KName.mkSimple "PolyBox.rec"
      , ctorName      := KName.mkSimple "PolyBox.mk"
      , levelParams   := [KName.mkSimple "v", KName.mkSimple "u"]
      , numPrefixArgs := 1
      , numFields     := 1
      , rhs           :=
          .lam (kArrow (.sort (.param (KName.mkSimple "u"))) (.sort (.param (KName.mkSimple "v"))))
            (.lam (.sort (.param (KName.mkSimple "u")))
              (.app (.bvar 1) (.sort (.param (KName.mkSimple "v"))))) } ]

/-- Extended kernel environment containing `stdKernelEnv` plus user-defined inductive families
`OptionNat`, `PairNat`, recursive `ListNat`, and universe-polymorphic `PolyBox.{u}` with their
dynamic recursor $\iota$-rules. -/
@[expose] def inductKernelEnv : KEnv :=
  (((stdKernelEnv.addInductDecl optionNatInductDecl).addInductDecl pairNatInductDecl).addInductDecl
    listNatInductDecl).addInductDecl polyBoxInductDecl

/-- **Universal Universe-Polymorphic Recursor $\iota$-Reduction (`reduceGeneralIota?_univ_poly_sound`)**:
For all universe levels `v u : KLevel`:
1. `PolyBox.rec.{v, u} (λ _ => .bvar 0) (PolyBox.mk.{u} payload)` instantiates `rule.levelParams = ["v", "u"]`
   inside `rule.rhs` with `[v, u]` and reduces in `kernelWhnf` to `.sort v`,
2. Negative Pole: Supplying a mismatched universe level list (`[v]` instead of `[v, u]`) is rejected
   (`reduceGeneralIota? = none`). -/
theorem reduceGeneralIota?_univ_poly_sound (v u payload : KLevel) :
    let onMk := KExpr.lam (.sort u) (.bvar 0)
    let goodSpine := KExpr.app (.const (KName.mkSimple "PolyBox.rec") [v, u]) onMk
    let badSpine  := KExpr.app (.const (KName.mkSimple "PolyBox.rec") [v]) onMk
    let major     := KExpr.app (.const (KName.mkSimple "PolyBox.mk") [u]) (.sort payload)
    kernelWhnf inductKernelEnv 8 (.app goodSpine major) = .sort v ∧
    reduceGeneralIota? inductKernelEnv badSpine major = none :=
  ⟨rfl, rfl⟩

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
1. Negative Pole: the erased spine `Quot.lift f h (Quot.mk a)` is not a redex (`reduceQuotLift? = none`);
   the kernel's `Quot.mk` takes `α r a`, and a spine without them is left alone,
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
    reduceQuotLift? lift3 quotMk3 = none ∧
    kernelWhnf stdKernelEnv 8 (.app lift6 quotMk6) = .lit (.natVal n) ∧
    reduceQuotLift? lift3 (.const (KName.mkSimple "neutralQuot") []) = none := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## 11. Upgraded Definitional Equality (`kernelIsDefEqFull := kernelIsDefEq`) & Genuine Term-Level Lowered Kernel (`WS-A`) -/

/-- Check `Sort 0` (`Prop`) proof irrelevance for `t` and `s` in context `ctx`:
returns `true` when `t` and `s` infer definitionally equal types `tyT ≡ tyS` and `tyT : Prop` (`Sort 0`). -/
@[expose] def isProofIrrelDefEq (env : KEnv) (fuel : Nat) (ctx : List KExpr) (t s : KExpr) : Bool :=
  match kernelInferType env fuel ctx t, kernelInferType env fuel ctx s with
  | some tyT, some tyS =>
    isPropType? env fuel ctx tyT && kernelIsDefEq env fuel tyT tyS ctx
  | _, _ => false

/-- **Reflexivity of `kernelIsDefEqFull` (`kernelIsDefEqFull_refl`)**:
For every environment `env`, fuel `fuel`, expression `e`, and context `ctx`,
`kernelIsDefEqFull env fuel e e ctx = true`. -/
theorem kernelIsDefEqFull_refl (env : KEnv) (fuel : Nat) (e : KExpr) (ctx : List KExpr := []) :
    kernelIsDefEqFull env fuel e e ctx = true :=
  kernelIsDefEq_refl env fuel e ctx

/-- **Universal `Nat` Literal ↔ `Nat.succ` Bridging (`kernelIsDefEqFull_nat_succ_bridge`)**:
For all `n : Nat`, `fuel : Nat`, `env : KEnv`, and `ctx : List KExpr`,
`kernelIsDefEqFull env (fuel + 2) (.lit (.natVal (n + 1))) (.app (.const (KName.mkSimple "Nat.succ") []) (.lit (.natVal n))) ctx = true`. -/
theorem kernelIsDefEqFull_nat_succ_bridge (env : KEnv) (fuel : Nat) (n : Nat) (ctx : List KExpr := []) :
    kernelIsDefEqFull env (fuel + 2)
      (.lit (.natVal (n + 1)))
      (.app (.const (KName.mkSimple "Nat.succ") []) (.lit (.natVal n)))
      ctx = true := by
  simp [kernelIsDefEqFull, kernelIsDefEq, kernelIsDefEqAux, kernelEngineFuel,
    kernelIsDefEqStep, stepNatLitBridge, BEq.beq, KExpr.beq]

/-- Alias `kernelIsDefEqFull_natLit_bridge` to `kernelIsDefEqFull_nat_succ_bridge`. -/
theorem kernelIsDefEqFull_natLit_bridge (env : KEnv) (fuel : Nat) (n : Nat) (ctx : List KExpr := []) :
    kernelIsDefEqFull env (fuel + 2)
      (.lit (.natVal (n + 1)))
      (natLitToKExpr (n + 1))
      ctx = true :=
  kernelIsDefEqFull_nat_succ_bridge env fuel n ctx

/-- Extended kernel environment with proposition `P : Prop` and two distinct proofs `proof1, proof2 : P`,
plus a neutral function `extFn : Nat → Nat` and indexed family `Vec : Nat → Type 0` for testing
$\eta$-equivalence, `Nat`-literal bridging, and proof irrelevance inside `kernelIsDefEq`,
`kernelInferType`, and `kernelCheckDecl`. -/
@[expose] def defEqFullTestEnv : KEnv :=
  (((((stdKernelEnv.add
    (.axiomInfo (KName.mkSimple "P") [] kProp)).add
    (.axiomInfo (KName.mkSimple "proof1") [] (.const (KName.mkSimple "P") []))).add
    (.axiomInfo (KName.mkSimple "proof2") [] (.const (KName.mkSimple "P") []))).add
    (.axiomInfo (KName.mkSimple "extFn") [] (kArrow kNatConst kNatConst))).add
    (.axiomInfo (KName.mkSimple "Vec") [] (kArrow kNatConst kType0))).add
    (.axiomInfo (KName.mkSimple "vecTwo") []
      (.app (.const (KName.mkSimple "Vec") [])
        (.app (.const (KName.mkSimple "Nat.succ") [])
          (.app (.const (KName.mkSimple "Nat.succ") []) (.const (KName.mkSimple "Nat.zero") [])))))

/-- **Lambda $\eta$-Equivalence Theorem (`kernelIsDefEqFull_eta_lam`)**:
`(.lam Nat (.app extFn (.bvar 0))) ≡ extFn` in both directions, while non-$\eta$ or domain-mismatched
lambdas are rejected (`false`). -/
theorem kernelIsDefEqFull_eta_lam :
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lam kNatConst (.app (.const (KName.mkSimple "extFn") []) (.bvar 0)))
      (.const (KName.mkSimple "extFn") []) = true ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.const (KName.mkSimple "extFn") [])
      (.lam kNatConst (.app (.const (KName.mkSimple "extFn") []) (.bvar 0))) = true ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lam kBoolConst (.app (.const (KName.mkSimple "extFn") []) (.bvar 0)))
      (.const (KName.mkSimple "extFn") []) = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- **`Sort 0` (`Prop`) Proof Irrelevance (`kernelIsDefEqFull_prop_proofIrrel`)**:
Distinct proofs `proof1, proof2 : P` (where `P : Prop`) are definitionally equal (`true`),
whereas distinct computational terms `0, 1 : Nat` are NOT (`false`). -/
theorem kernelIsDefEqFull_prop_proofIrrel :
    kernelIsDefEqFull defEqFullTestEnv 8
      (.const (KName.mkSimple "proof1") [])
      (.const (KName.mkSimple "proof2") []) = true ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lit (.natVal 0))
      (.lit (.natVal 1)) = false := by
  exact ⟨rfl, rfl⟩

/-- Predicate for the scalar/control `LExpr` fragment (including 0-field `Unit.unit` `.record []`),
on which substitution and renaming are purely structural (`LExpr.rec`) and reduce by `rfl` in the kernel. -/
@[expose] def isScalarLExpr : LExpr → Bool
  | .bvar _ | .erased | .lit _ | .boolLit _ | .record [] => true
  | .const _ b | .lam _ b | .natSucc b | .proj _ b | .recConst _ _ b => isScalarLExpr b
  | .app a b | .letE _ a b | .natBin _ a b | .split _ a b => isScalarLExpr a && isScalarLExpr b
  | .natRec _ x y z | .boolRec _ x y z => isScalarLExpr x && isScalarLExpr y && isScalarLExpr z
  | .record (_ :: _) | .inject _ _ | .cases _ _ _ => false

/-- Structurally recursive renaming on the scalar/control `LExpr` fragment. -/
@[expose] def renameScalar (f : Nat → Nat) : LExpr → LExpr
  | .bvar i => .bvar (f i)
  | .erased => .erased
  | .const n b => .const n (renameScalar f b)
  | .app a b => .app (renameScalar f a) (renameScalar f b)
  | .lam T b => .lam T (renameScalar (Obend.Core.Term.liftRename f) b)
  | .letE T v b => .letE T (renameScalar f v) (renameScalar (Obend.Core.Term.liftRename f) b)
  | .lit n => .lit n
  | .natSucc a => .natSucc (renameScalar f a)
  | .natBin op a b => .natBin op (renameScalar f a) (renameScalar f b)
  | .boolLit b => .boolLit b
  | .natRec T z s m => .natRec T (renameScalar f z) (renameScalar f s) (renameScalar f m)
  | .boolRec T x y m => .boolRec T (renameScalar f x) (renameScalar f y) (renameScalar f m)
  | .split ns F m => .split ns (renameScalar f F) (renameScalar f m)
  | .proj n t => .proj n (renameScalar f t)
  | .recConst n T b => .recConst n T (renameScalar (Obend.Core.Term.liftRename f) b)
  | e => e

theorem renameScalar_isScalar : ∀ (e : LExpr) (f : Nat → Nat),
    isScalarLExpr e = true → isScalarLExpr (renameScalar f e) = true
  | .bvar _, _, _ | .erased, _, _ | .lit _, _, _ | .boolLit _, _, _ | .record [], _, _ => rfl
  | .const _ b, f, h | .natSucc b, f, h | .proj _ b, f, h => by
    simp only [renameScalar, isScalarLExpr] at h ⊢
    exact renameScalar_isScalar b f h
  | .lam _ b, f, h | .recConst _ _ b, f, h => by
    simp only [renameScalar, isScalarLExpr] at h ⊢
    exact renameScalar_isScalar b (Obend.Core.Term.liftRename f) h
  | .app a b, f, h | .natBin _ a b, f, h | .split _ a b, f, h => by
    simp only [renameScalar, isScalarLExpr, Bool.and_eq_true] at h ⊢
    exact ⟨renameScalar_isScalar a f h.1, renameScalar_isScalar b f h.2⟩
  | .letE _ a b, f, h => by
    simp only [renameScalar, isScalarLExpr, Bool.and_eq_true] at h ⊢
    exact ⟨renameScalar_isScalar a f h.1, renameScalar_isScalar b (Obend.Core.Term.liftRename f) h.2⟩
  | .natRec _ x y z, f, h | .boolRec _ x y z, f, h => by
    simp only [renameScalar, isScalarLExpr, Bool.and_eq_true] at h ⊢
    exact ⟨⟨renameScalar_isScalar x f h.1.1, renameScalar_isScalar y f h.1.2⟩, renameScalar_isScalar z f h.2⟩
  | .record (_ :: _), _, h | .inject _ _, _, h | .cases _ _ _, _, h => by cases h

theorem renameScalar_eq_rename : ∀ (e : LExpr) (f : Nat → Nat),
    isScalarLExpr e = true → renameScalar f e = e.rename f
  | .bvar _, _, _ | .erased, _, _ | .lit _, _, _ | .boolLit _, _, _ | .record [], _, _ => by
    simp [renameScalar, LExpr.rename]
  | .const _ b, f, h | .natSucc b, f, h | .proj _ b, f, h => by
    simp only [isScalarLExpr] at h
    simp [renameScalar, LExpr.rename, renameScalar_eq_rename b f h]
  | .lam _ b, f, h | .recConst _ _ b, f, h => by
    simp only [isScalarLExpr] at h
    simp [renameScalar, LExpr.rename, renameScalar_eq_rename b (Obend.Core.Term.liftRename f) h]
  | .app a b, f, h | .natBin _ a b, f, h | .split _ a b, f, h => by
    simp only [isScalarLExpr, Bool.and_eq_true] at h
    simp [renameScalar, LExpr.rename, renameScalar_eq_rename a f h.1, renameScalar_eq_rename b f h.2]
  | .letE _ a b, f, h => by
    simp only [isScalarLExpr, Bool.and_eq_true] at h
    simp [renameScalar, LExpr.rename, renameScalar_eq_rename a f h.1,
      renameScalar_eq_rename b (Obend.Core.Term.liftRename f) h.2]
  | .natRec _ x y z, f, h | .boolRec _ x y z, f, h => by
    simp only [isScalarLExpr, Bool.and_eq_true] at h
    simp [renameScalar, LExpr.rename, renameScalar_eq_rename x f h.1.1,
      renameScalar_eq_rename y f h.1.2, renameScalar_eq_rename z f h.2]
  | .record (_ :: _), _, h | .inject _ _, _, h | .cases _ _ _, _, h => by cases h

@[expose] def liftSubstScalar (σ : Nat → LExpr) : Nat → LExpr
  | 0 => .bvar 0
  | n + 1 => renameScalar Nat.succ (σ n)

theorem liftSubstScalar_isScalar {σ : Nat → LExpr} (hσ : ∀ i, isScalarLExpr (σ i) = true) :
    ∀ i, isScalarLExpr (liftSubstScalar σ i) = true
  | 0 => rfl
  | n + 1 => renameScalar_isScalar (σ n) Nat.succ (hσ n)

theorem liftSubstScalar_eq_liftSubst {σ : Nat → LExpr} (hσ : ∀ i, isScalarLExpr (σ i) = true) :
    liftSubstScalar σ = LExpr.liftSubst σ := by
  funext i
  cases i with
  | zero => rfl
  | succ n =>
    simp [liftSubstScalar, LExpr.liftSubst, renameScalar_eq_rename (σ n) Nat.succ (hσ n)]

/-- Structurally recursive substitution on the scalar/control `LExpr` fragment. -/
@[expose] def substScalar (σ : Nat → LExpr) : LExpr → LExpr
  | .bvar i => σ i
  | .erased => .erased
  | .const n b => .const n (substScalar σ b)
  | .app a b => .app (substScalar σ a) (substScalar σ b)
  | .lam T b => .lam T (substScalar (liftSubstScalar σ) b)
  | .letE T v b => .letE T (substScalar σ v) (substScalar (liftSubstScalar σ) b)
  | .lit n => .lit n
  | .natSucc a => .natSucc (substScalar σ a)
  | .natBin op a b => .natBin op (substScalar σ a) (substScalar σ b)
  | .boolLit b => .boolLit b
  | .natRec T z s m => .natRec T (substScalar σ z) (substScalar σ s) (substScalar σ m)
  | .boolRec T x y m => .boolRec T (substScalar σ x) (substScalar σ y) (substScalar σ m)
  | .split ns F m => .split ns (substScalar σ F) (substScalar σ m)
  | .proj n t => .proj n (substScalar σ t)
  | .recConst n T b => .recConst n T (substScalar (liftSubstScalar σ) b)
  | e => e

theorem substScalar_eq_subst : ∀ (e : LExpr) (σ : Nat → LExpr),
    isScalarLExpr e = true →
    (∀ i, isScalarLExpr (σ i) = true) →
    substScalar σ e = e.subst σ
  | .bvar _, _, _, _ | .erased, _, _, _ | .lit _, _, _, _ | .boolLit _, _, _, _ | .record [], _, _, _ => by
    simp [substScalar, LExpr.subst]
  | .const _ b, σ, h, hσ | .natSucc b, σ, h, hσ | .proj _ b, σ, h, hσ => by
    simp only [isScalarLExpr] at h
    simp [substScalar, LExpr.subst, substScalar_eq_subst b σ h hσ]
  | .lam _ b, σ, h, hσ | .recConst _ _ b, σ, h, hσ => by
    simp only [isScalarLExpr] at h
    rw [substScalar, LExpr.subst,
        substScalar_eq_subst b (liftSubstScalar σ) h (liftSubstScalar_isScalar hσ),
        liftSubstScalar_eq_liftSubst hσ]
  | .app a b, σ, h, hσ | .natBin _ a b, σ, h, hσ | .split _ a b, σ, h, hσ => by
    simp only [isScalarLExpr, Bool.and_eq_true] at h
    simp [substScalar, LExpr.subst, substScalar_eq_subst a σ h.1 hσ, substScalar_eq_subst b σ h.2 hσ]
  | .letE _ a b, σ, h, hσ => by
    simp only [isScalarLExpr, Bool.and_eq_true] at h
    rw [substScalar, LExpr.subst,
        substScalar_eq_subst a σ h.1 hσ,
        substScalar_eq_subst b (liftSubstScalar σ) h.2 (liftSubstScalar_isScalar hσ),
        liftSubstScalar_eq_liftSubst hσ]
  | .natRec _ x y z, σ, h, hσ | .boolRec _ x y z, σ, h, hσ => by
    simp only [isScalarLExpr, Bool.and_eq_true] at h
    simp [substScalar, LExpr.subst, substScalar_eq_subst x σ h.1.1 hσ,
      substScalar_eq_subst y σ h.1.2 hσ, substScalar_eq_subst z σ h.2 hσ]
  | .record (_ :: _), _, h, _ | .inject _ _, _, h, _ | .cases _ _ _, _, h, _ => by cases h

/-- Kernel-reducible single-binder instantiation on the scalar/control `LExpr` fragment. -/
@[expose] def instScalar (body a : LExpr) : LExpr :=
  substScalar (LExpr.single a) body

theorem single_isScalar {a : LExpr} (ha : isScalarLExpr a = true) :
    ∀ i, isScalarLExpr (LExpr.single a i) = true
  | 0 => ha
  | _ + 1 => rfl

theorem instScalar_eq_inst (body a : LExpr)
    (hb : isScalarLExpr body = true) (ha : isScalarLExpr a = true) :
    instScalar body a = body.inst a :=
  substScalar_eq_subst body (LExpr.single a) hb (single_isScalar ha)

/-- Deterministic single-step small-step reducer (`stepLExpr?`) for the scalar/control `LExpr` fragment,
used to drive verified multi-step `SSteps` reductions of lowered multi-argument kernel programs. -/
@[expose] def stepLExpr? : LExpr → Option LExpr
  | .const _ b => some b
  | .app (.lam _ body) arg =>
    if isScalarLExpr body && isScalarLExpr arg then
      some (instScalar body arg)
    else
      none
  | .app f a => (stepLExpr? f).map (fun f' => .app f' a)
  | .letE _ val body =>
    if isScalarLExpr body && isScalarLExpr val then
      some (instScalar body val)
    else
      none
  | .natSucc (.lit n) => some (.lit (n + 1))
  | .natSucc a => (stepLExpr? a).map .natSucc
  | .natBin op (.lit a) (.lit b) => some (op.eval a b)
  | .natBin op (.lit a) r => (stepLExpr? r).map (fun r' => .natBin op (.lit a) r')
  | .natBin op l r => (stepLExpr? l).map (fun l' => .natBin op l' r)
  | .boolRec _ x _ (.boolLit false) => some x
  | .boolRec _ _ y (.boolLit true) => some y
  | .boolRec T x y m => (stepLExpr? m).map (fun m' => .boolRec T x y m')
  | _ => none

/-- Soundness of `stepLExpr?` with respect to `Obend.Lower.SStep`. -/
theorem stepLExpr?_sound : ∀ (e e' : LExpr), stepLExpr? e = some e' → SStep e e'
  | .const n b, _, h => by
    simp only [stepLExpr?, Option.some.injEq] at h
    subst h
    exact .delta n b
  | .app (.lam T body) arg, e', h => by
    simp only [stepLExpr?] at h
    split at h
    · rename_i hsc
      simp only [Bool.and_eq_true] at hsc
      simp only [Option.some.injEq] at h
      subst h
      rw [instScalar_eq_inst body arg hsc.1 hsc.2]
      exact .beta T body arg
    · cases h
  | .app (.bvar i) a, e', h
  | .app .erased a, e', h
  | .app (.const _ _) a, e', h
  | .app (.app _ _) a, e', h
  | .app (.letE _ _ _) a, e', h
  | .app (.lit _) a, e', h
  | .app (.natSucc _) a, e', h
  | .app (.natBin _ _ _) a, e', h
  | .app (.boolLit _) a, e', h
  | .app (.natRec _ _ _ _) a, e', h
  | .app (.boolRec _ _ _ _) a, e', h
  | .app (.record _) a, e', h
  | .app (.split _ _ _) a, e', h
  | .app (.proj _ _) a, e', h
  | .app (.inject _ _) a, e', h
  | .app (.cases _ _ _) a, e', h
  | .app (.recConst _ _ _) a, e', h => by
    simp only [stepLExpr?, Option.map_eq_some_iff] at h
    obtain ⟨f', hf, rfl⟩ := h
    exact .appFun a (stepLExpr?_sound _ f' hf)
  | .letE T val body, e', h => by
    simp only [stepLExpr?] at h
    split at h
    · rename_i hsc
      simp only [Bool.and_eq_true] at hsc
      simp only [Option.some.injEq] at h
      subst h
      rw [instScalar_eq_inst body val hsc.1 hsc.2]
      exact .zeta T val body
    · cases h
  | .natSucc (.lit n), _, h => by
    simp only [stepLExpr?, Option.some.injEq] at h
    subst h
    exact .succFold n
  | .natSucc (.bvar _), _, h
  | .natSucc .erased, _, h
  | .natSucc (.const _ _), _, h
  | .natSucc (.app _ _), _, h
  | .natSucc (.lam _ _), _, h
  | .natSucc (.letE _ _ _), _, h
  | .natSucc (.natSucc _), _, h
  | .natSucc (.natBin _ _ _), _, h
  | .natSucc (.boolLit _), _, h
  | .natSucc (.natRec _ _ _ _), _, h
  | .natSucc (.boolRec _ _ _ _), _, h
  | .natSucc (.record _), _, h
  | .natSucc (.split _ _ _), _, h
  | .natSucc (.proj _ _), _, h
  | .natSucc (.inject _ _), _, h
  | .natSucc (.cases _ _ _), _, h
  | .natSucc (.recConst _ _ _), _, h => by
    simp only [stepLExpr?, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    exact .succArg (stepLExpr?_sound _ a' ha)
  | .natBin op (.lit a) (.lit b), _, h => by
    simp only [stepLExpr?, Option.some.injEq] at h
    subst h
    exact .binLit op a b
  | .natBin op (.lit a) (.bvar _), _, h
  | .natBin op (.lit a) .erased, _, h
  | .natBin op (.lit a) (.const _ _), _, h
  | .natBin op (.lit a) (.app _ _), _, h
  | .natBin op (.lit a) (.lam _ _), _, h
  | .natBin op (.lit a) (.letE _ _ _), _, h
  | .natBin op (.lit a) (.natSucc _), _, h
  | .natBin op (.lit a) (.natBin _ _ _), _, h
  | .natBin op (.lit a) (.boolLit _), _, h
  | .natBin op (.lit a) (.natRec _ _ _ _), _, h
  | .natBin op (.lit a) (.boolRec _ _ _ _), _, h
  | .natBin op (.lit a) (.record _), _, h
  | .natBin op (.lit a) (.split _ _ _), _, h
  | .natBin op (.lit a) (.proj _ _), _, h
  | .natBin op (.lit a) (.inject _ _), _, h
  | .natBin op (.lit a) (.cases _ _ _), _, h
  | .natBin op (.lit a) (.recConst _ _ _), _, h => by
    simp only [stepLExpr?, Option.map_eq_some_iff] at h
    obtain ⟨r', hr, rfl⟩ := h
    exact .binRight op a (stepLExpr?_sound _ r' hr)
  | .natBin op (.bvar _) r, _, h
  | .natBin op .erased r, _, h
  | .natBin op (.const _ _) r, _, h
  | .natBin op (.app _ _) r, _, h
  | .natBin op (.lam _ _) r, _, h
  | .natBin op (.letE _ _ _) r, _, h
  | .natBin op (.natSucc _) r, _, h
  | .natBin op (.natBin _ _ _) r, _, h
  | .natBin op (.boolLit _) r, _, h
  | .natBin op (.natRec _ _ _ _) r, _, h
  | .natBin op (.boolRec _ _ _ _) r, _, h
  | .natBin op (.record _) r, _, h
  | .natBin op (.split _ _ _) r, _, h
  | .natBin op (.proj _ _) r, _, h
  | .natBin op (.inject _ _) r, _, h
  | .natBin op (.cases _ _ _) r, _, h
  | .natBin op (.recConst _ _ _) r, _, h => by
    simp only [stepLExpr?, Option.map_eq_some_iff] at h
    obtain ⟨l', hl, rfl⟩ := h
    exact .binLeft op r (stepLExpr?_sound _ l' hl)
  | .boolRec T x y (.boolLit false), _, h => by
    simp only [stepLExpr?, Option.some.injEq] at h
    subst h
    exact .boolRecFalse T x y
  | .boolRec T x y (.boolLit true), _, h => by
    simp only [stepLExpr?, Option.some.injEq] at h
    subst h
    exact .boolRecTrue T x y
  | .boolRec T x y (.bvar _), _, h
  | .boolRec T x y .erased, _, h
  | .boolRec T x y (.const _ _), _, h
  | .boolRec T x y (.app _ _), _, h
  | .boolRec T x y (.lam _ _), _, h
  | .boolRec T x y (.letE _ _ _), _, h
  | .boolRec T x y (.lit _), _, h
  | .boolRec T x y (.natSucc _), _, h
  | .boolRec T x y (.natBin _ _ _), _, h
  | .boolRec T x y (.natRec _ _ _ _), _, h
  | .boolRec T x y (.boolRec _ _ _ _), _, h
  | .boolRec T x y (.record _), _, h
  | .boolRec T x y (.split _ _ _), _, h
  | .boolRec T x y (.proj _ _), _, h
  | .boolRec T x y (.inject _ _), _, h
  | .boolRec T x y (.cases _ _ _), _, h
  | .boolRec T x y (.recConst _ _ _), _, h => by
    simp only [stepLExpr?, Option.map_eq_some_iff] at h
    obtain ⟨m', hm, rfl⟩ := h
    exact .boolRecMajor T x y (stepLExpr?_sound _ m' hm)
  | .bvar _, _, h | .erased, _, h | .lam _ _, _, h | .lit _, _, h
  | .boolLit _, _, h | .natRec _ _ _ _, _, h | .record _, _, h | .split _ _ _, _, h
  | .proj _ _, _, h | .inject _ _, _, h | .cases _ _ _, _, h | .recConst _ _ _, _, h => by
    cases h

/-- Run `stepLExpr?` for up to `k` steps. -/
@[expose] def runLExprSteps : Nat → LExpr → LExpr
  | 0, e => e
  | k + 1, e =>
    match stepLExpr? e with
    | some e' => runLExprSteps k e'
    | none => e

/-- **Verified Multi-Step `SSteps` Reflection (`runLExprSteps_sound`)**:
If `runLExprSteps k e = v`, then `SSteps e v`. -/
theorem runLExprSteps_sound : ∀ (k : Nat) (e v : LExpr),
    runLExprSteps k e = v → SSteps e v
  | 0, e, _, rfl => .refl e
  | k + 1, e, v, h => by
    unfold runLExprSteps at h
    cases hs : stepLExpr? e with
    | none =>
      rw [hs] at h
      subst h
      exact .refl e
    | some e' =>
      rw [hs] at h
      exact .next (stepLExpr?_sound e e' hs) (runLExprSteps_sound k e' v h)

/-- **Theorem (`etaDomCompat_fail_closed_sound`)**:
Proves universally that `etaDomCompat` and `kernelIsDefEqFull` fail closed (`false`) during one-sided
$\lambda$-$\eta$ expansion whenever `other` fails type inference (`inferPrev ctx other = none`,
such as an untyped free variable `.fvar id` or unknown constant) or infers a non-`.forallE` type,
while preserving valid $\eta$-expansion when `other` infers a matching `.forallE` arrow type. -/
theorem etaDomCompat_fail_closed_sound
    (env : KEnv) (fuel : Nat)
    (inferPrev : List KExpr → KExpr → Option KExpr)
    (defEqPrev : List KExpr → KExpr → KExpr → Bool)
    (ctx : List KExpr) (dom other : KExpr)
    (hNone : inferPrev ctx other = none) :
    etaDomCompat env fuel inferPrev defEqPrev ctx dom other = false ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lam kNatConst (.app (.fvar 0) (.bvar 0)))
      (.fvar 0) = false ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.fvar 0)
      (.lam kNatConst (.app (.fvar 0) (.bvar 0))) = false ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lam kNatConst (.app (.const (KName.mkSimple "Nat.zero") []) (.bvar 0)))
      (.const (KName.mkSimple "Nat.zero") []) = false ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lam kNatConst (.app (.const (KName.mkSimple "extFn") []) (.bvar 0)))
      (.const (KName.mkSimple "extFn") []) = true := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  unfold etaDomCompat
  rw [hNone]

/-- Broken `etaDomCompat` that defaults `none ↦ true` (unsoundly permitting $\eta$-expansion
against untyped free variables or ill-typed terms). -/
@[expose] def etaDomCompatFailOpen (env : KEnv) (fuel : Nat)
    (inferPrev : List KExpr → KExpr → Option KExpr)
    (defEqPrev : List KExpr → KExpr → KExpr → Bool)
    (ctx : List KExpr) (dom other : KExpr) : Bool :=
  match inferPrev ctx other with
  | some otherTy =>
    match kernelWhnf env fuel otherTy with
    | .forallE otherDom _ => defEqPrev ctx dom otherDom
    | _ => false
  | none => true

#tooth etaDomCompat_fail_closed_sound by mutation etaDomCompat := etaDomCompatFailOpen

end Obend.Lower.LeanKernel
end
