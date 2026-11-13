module
/-
# Obend.Lower.Syntax — Lean-lite, the erased kernel terms of the lowered fragment

The fragment's terms are Lean kernel `Expr`s read by `Obend.Lower.Fragment` into `LExpr`, the way
Lean4Lean reads `Expr` into its own `VExpr` and MetaCoq's erasure reads Coq terms into λ□: a term
the kernel would reduce is kept rule for rule; what the kernel never reduces in a closed computation
of a fragment type (a type, a proof, a universe level, a binder's type) is erased to `erased` (MetaCoq's
`□`), and the reader records each binder's type as the Core4 type it lowers to (`Ty`), the annotation
the checker needs. Every node of `LExpr` is one kernel form:

* `bvar`, `app`, `lam`, `letE`, `lit`: `Expr.bvar`, `Expr.app`, `Expr.lam`, `Expr.letE`, `Expr.lit (.natVal _)`;
* `const name body`: `Expr.const name _`, a definition, carried with its value (read at its use, with
  its type arguments known; its universe levels erased), so δ is `const name body ↦ body`;
* `natSucc`, `natBin`: `Nat.succ` and the literal operations the kernel computes on literals
  (`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`), fully applied;
* `boolLit`: `Bool.false`, `Bool.true`;
* `natRec`, `boolRec`: `Nat.rec` and `Bool.rec` fully applied (the motive erased, `result` the Core4
  type of the motive's body, which the fragment requires not to depend on the major premise);
* `record`, `split`, `proj`: a structure's constructor applied to its fields, its recursor
  (`S.rec F major ↦ F field₀ … fieldₖ₋₁`), and `Expr.proj` (by field name);
* `inject`, `cases`: a non-recursive inductive's constructor applied to its fields, and its recursor
  over the arms in constructor order (each arm's minor premise takes the constructor's fields);
* `recConst name T body`: a recursive definition read from its unfolding equation (`f.eq_def`), the
  body binding the definition itself, so recursive δ is `recConst ↦ body[recConst]`.

Parameters of a constructor or recursor are types and are erased with the motive.
-/

/-
# Obend.Lower.Semantics — the source semantics: Lean's kernel reductions on the fragment

A small-step, weak-head reduction on `LExpr`, rule for rule the reductions Lean's kernel performs in
`whnf` (and Lean4Lean models: `Lean4Lean/TypeChecker.lean` `whnfCore`/`whnf`, `Lean4Lean/Inductive/Reduce.lean`
`inductiveReduceRec`, `Lean4Lean/Theory/Typing/Basic.lean` the `IsDefEq` β/δ/ι rules) restricted to the
fragment. Each constructor says which kernel rule it is:

| rule | kernel | Lean4Lean |
|---|---|---|
| `beta`, `appFun` | `whnfCore`: `Expr.app` with a `lam` head is `instantiate`d; otherwise the head is reduced | `whnfCore` `.app` case, `IsDefEq.beta` |
| `zeta` | `whnfCore`: `letE` is `instantiate1`d | `whnfCore` `.letE` case, `IsDefEq.zeta` (Lean4Lean's VExpr has no `let`; `TrExpr` unfolds it) |
| `delta` | `whnf`: `unfoldDefinition?` of a definition | `whnf` `unfoldDefinition`, `IsDefEq.delta` |
| `unfold` | a recursive definition replaced by the right-hand side of its unfolding equation `f.eq_def` (Meta's smart unfolding; the compiler's `_unsafe_rec` view) | `unfoldDefinition` followed by the ι steps through `brecOn` that make `f.eq_def` hold by `rfl` (structural recursion); for well-founded recursion `f.eq_def` is a propositional equation (`WellFounded.fix_eq`), not a kernel reduction |
| `succFold`, `succArg` | `whnf`/`reduceNat`: `Nat.succ` of an argument whose `whnf` is a literal folds to a literal | `reduceNat` (`Nat.succ` case) |
| `binLit`, `binLeft`, `binRight` | `reduceNat`/`reduceBinNatOp`: both arguments are `whnf`ed, left first, and computed when literals | `reduceBinNatOp` |
| `natRecZero`, `natRecSucc`, `natRecMajor` | `inductiveReduceRec` for `Nat.rec`: the major premise is `whnf`ed; a literal is turned into `Nat.zero`/`Nat.succ (lit n)` (`natLitExt`, `toCtorIfLit`) and the rule applied | `inductiveReduceRec`, `toCtorIfLit`, `IsDefEq.iota` |
| `boolRecFalse`, `boolRecTrue`, `boolRecMajor` | `inductiveReduceRec` for `Bool.rec` | the same |
| `splitRecord`, `splitMajor` | `inductiveReduceRec` for a structure's `rec` on its constructor | the same (structure eta, `toCtorWhenStructure`, is not needed: a closed major reduces to the constructor) |
| `projRecord`, `projTarget` | `whnfCore`: `Expr.proj` of a constructor application selects the field | `whnfCore` `.proj` case, `projReduce` |
| `casesInject`, `casesMajor` | `inductiveReduceRec` for a non-recursive inductive's `rec` | the same |

The strategy is the kernel's: only the head is reduced (an argument is never reduced before it is
substituted), and a literal operation's arguments left to right. `Nat.zero` is read as `lit 0`
(the kernel treats `Nat.zero` and `lit 0` alike, `isNatZero`). What is not here: universe-level
instantiation (levels are erased), η and proof irrelevance (definitional-equality rules, not
reductions), `Nat.pow` as a primitive (its structural `Nat.rec` definition δ-unfolds instead),
`Nat.gcd`/`Nat.log2`/bitwise operations (defined via `WellFounded.fix`/`Acc.rec` in `Init`, outside
the fragment), quotients, well-founded recursion (`WellFounded.fix`, `Acc.rec`), and `Prop`-to-`Type`
recursors.
-/

/-
# Obend.Lower.Lower — the erased fragment to Core4

`lowerT` maps Lean-lite to a Core4 `Term`; `Obend.Lower.Fragment.lower` composes it with the reader of
Lean's `Expr` (`lower : Environment → Expr → Option Term`, in `MetaM`):

* proofs and types (`erased`) to the empty record `{}` (the λ□ box); every λ is kept, so an erased
  argument is passed as `{}` and its binder is never read;
* a definition to its lowered value (the δ step is a stutter);
* a structure's constructor to a record with its field names, its recursor to the destructor
  `split`, `Expr.proj` to `get`;
* a non-recursive inductive's constructor to `inject label {fields}`, its recursor to `case` whose
  arm for each constructor destructs the payload with `split` and passes the fields to the minor
  premise;
* `Nat` literals to `nat`, `Nat.succ` to `+ 1`, the literal operations to `binary`;
* `Bool.rec` to `ifBool`;
* `Nat.rec` to `fix`: `Nat.rec z s m` is `(fix (λself. λ_. λk. ifZero k z (s (k-1) (self (k-1)))) {}) m`;
* `let` to `(λx. body) value`;
* a recursive definition to `fix (λself. λ_. body) {}`.
-/

/-
# Obend.Lower.Typing — the simply typed fragment the lowering is type-correct on

`LTyped Γ e T`: a fragment term has the Core4 type `T` its Lean type lowers to (`Fragment.lowerTy`),
in the context `Γ` of its binders' lowered types. The relation is the erased fragment's simple type
discipline: every type is `good` (built from `Nat`, `Bool`, `{}`, closed field rows, closed sums and
reusable unrestricted arrows), so every binding is shareable and a lowered program uses no linear or
affine resource. It is what Lean's own typing gives a fragment term after erasure when the motive of
every recursor does not depend on the major premise; a large elimination (a motive computing a type
by recursion, as `Nat.below` does inside `Nat.brecOn`) has no simple type and is outside it.
-/

/-
# Obend.Lower.Proofs.Sound — the lowering preserves what a fragment term computes

**The simulation** (`lower_step`): every source step `s → s'` is matched by Core4 on the lowered
terms in one of two ways.

* A *stutter*: `lowerT s' = lowerT s`. Only δ is a stutter (the lowering inlines definitions), and it
  strictly decreases the source term's size (`sizeOf`): this is the measure that bounds a run of
  stutters, so a source run of `k` steps from `s` has at most `sizeOf s` stutters before each
  non-stuttering step.
* A *positive* run: `lowerT s` takes one or more Core4 steps to a term `m` that is `lowerT s'` with
  some of its subterms run ahead (`Ahead (lowerT s') m`, `Obend.Equiv.Ahead`). β, ζ, the literal
  operations, the eliminators on constructors are matched exactly (`m = lowerT s'`); a step inside the
  major premise of `Nat.rec` is matched after the lowered `fix` has unrolled once (`natRec_unfold`),
  which `Ahead` absorbs: the unrolled `ifZero` is `lowerT s'` run ahead.

**The theorem** (`lower_sound`): a fragment term the source semantics reduces to a canonical form `v`
has a lowered term that evaluates in Core4 to a value related to `lowerT v` by a chain of `Ahead` links
(`AheadChain`), so with the same completed runs (`Obend.Equiv.sameRuns_of_ahead`); for a literal and a
Boolean the value is exactly the lowered one: `Evaluates (lowerT e) (lowerT v)` (`lower_sound_nat`,
`lower_sound_bool`). `lower_value`: canonical forms lower to values.

**Teeth**: a lowering that drops `Nat.rec`'s minor premise (`lowerDropMinor`) and one that maps
`Nat.sub` to `add` (`lowerSubAdd`) each fail the theorem on a two-line program
(`dropMinor_refuted`, `subAdd_refuted`).
-/
public import Lean
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Equiv.Reduction
public import Obend.Equiv.Behaviour

public section

namespace Obend.Lower
open Obend.Core.Term (Primitive)
open Obend.Core.Ty (Ty)
set_option autoImplicit false

/-- The kernel's literal operations on `Nat` that Core4 has a primitive for. -/
inductive NatOp where
  | add | sub | mul | div | mod | beq | ble
  deriving Repr, DecidableEq

/-- The Core4 primitive of a literal operation. -/
@[expose] def NatOp.prim : NatOp → Primitive
  | .add => .add | .sub => .subtract | .mul => .multiply | .div => .divide | .mod => .modulo
  | .beq => .equal | .ble => .lessEqual

/-- The kernel constant a literal operation is. -/
def NatOp.constName : NatOp → String
  | .add => "Nat.add" | .sub => "Nat.sub" | .mul => "Nat.mul" | .div => "Nat.div" | .mod => "Nat.mod"
  | .beq => "Nat.beq" | .ble => "Nat.ble"

inductive LExpr where
  | bvar (index : Nat)
  /-- A type, a proof, or anything else that is never reduced in a computation (MetaCoq's `□`). -/
  | erased
  /-- A definition, with its value: δ unfolds it. -/
  | const (name : String) (body : LExpr)
  | app (function argument : LExpr)
  | lam (domain : Ty) (body : LExpr)
  | letE (domain : Ty) (value body : LExpr)
  | lit (value : Nat)
  | natSucc (argument : LExpr)
  | natBin (op : NatOp) (left right : LExpr)
  | boolLit (value : Bool)
  | natRec (result : Ty) (zero succ major : LExpr)
  | boolRec (result : Ty) (whenFalse whenTrue major : LExpr)
  | record (fields : List (String × LExpr))
  | split (names : List String) (minor major : LExpr)
  | proj (name : String) (target : LExpr)
  | inject (label : String) (fields : List (String × LExpr))
  /-- Arms in constructor order: the label, the constructor's field names, the minor premise. -/
  | cases (result : Ty) (arms : List (String × List String × LExpr)) (major : LExpr)
  /-- A recursive definition, read from its unfolding equation `f.eq_def : f = fun xs => rhs[f]`: the
  body binds the definition itself at index 0 (recursive δ unfolds it into its body). -/
  | recConst (name : String) (type : Ty) (body : LExpr)
  deriving Repr, Inhabited

namespace LExpr

theorem sizeOf_snd_lt {α : Type} [SizeOf α] {l : List (String × α)} {x : String × α} (h : x ∈ l) :
    sizeOf x.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  cases x; simp at this ⊢; omega

theorem sizeOf_arm_lt {l : List (String × List String × LExpr)} {x : String × List String × LExpr}
    (h : x ∈ l) : sizeOf x.2.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨a, b, c⟩ := x; simp at this ⊢; omega

/-- Renaming. A definition's value is renamed too (it is closed, so this changes nothing, and no
closedness premise is needed anywhere). -/
@[expose] def rename (f : Nat → Nat) : LExpr → LExpr
  | .bvar i => .bvar (f i)
  | .erased => .erased
  | .const n b => .const n (b.rename f)
  | .app a b => .app (a.rename f) (b.rename f)
  | .lam T b => .lam T (b.rename (Obend.Core.Term.liftRename f))
  | .letE T v b => .letE T (v.rename f) (b.rename (Obend.Core.Term.liftRename f))
  | .lit n => .lit n
  | .natSucc a => .natSucc (a.rename f)
  | .natBin op a b => .natBin op (a.rename f) (b.rename f)
  | .boolLit b => .boolLit b
  | .natRec T z s m => .natRec T (z.rename f) (s.rename f) (m.rename f)
  | .boolRec T x y m => .boolRec T (x.rename f) (y.rename f) (m.rename f)
  | .record fs => .record (fs.map fun x => (x.1, x.2.rename f))
  | .split ns F m => .split ns (F.rename f) (m.rename f)
  | .proj n t => .proj n (t.rename f)
  | .inject l fs => .inject l (fs.map fun x => (x.1, x.2.rename f))
  | .cases T arms m => .cases T (arms.map fun x => (x.1, x.2.1, x.2.2.rename f)) (m.rename f)
  | .recConst n T b => .recConst n T (b.rename (Obend.Core.Term.liftRename f))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := sizeOf_snd_lt h; omega)
    | (rename_i h; have := sizeOf_arm_lt h; omega)

@[expose] def liftSubst (σ : Nat → LExpr) : Nat → LExpr
  | 0 => .bvar 0
  | n + 1 => (σ n).rename Nat.succ

@[expose] def subst (σ : Nat → LExpr) : LExpr → LExpr
  | .bvar i => σ i
  | .erased => .erased
  | .const n b => .const n (b.subst σ)
  | .app a b => .app (a.subst σ) (b.subst σ)
  | .lam T b => .lam T (b.subst (liftSubst σ))
  | .letE T v b => .letE T (v.subst σ) (b.subst (liftSubst σ))
  | .lit n => .lit n
  | .natSucc a => .natSucc (a.subst σ)
  | .natBin op a b => .natBin op (a.subst σ) (b.subst σ)
  | .boolLit b => .boolLit b
  | .natRec T z s m => .natRec T (z.subst σ) (s.subst σ) (m.subst σ)
  | .boolRec T x y m => .boolRec T (x.subst σ) (y.subst σ) (m.subst σ)
  | .record fs => .record (fs.map fun x => (x.1, x.2.subst σ))
  | .split ns F m => .split ns (F.subst σ) (m.subst σ)
  | .proj n t => .proj n (t.subst σ)
  | .inject l fs => .inject l (fs.map fun x => (x.1, x.2.subst σ))
  | .cases T arms m => .cases T (arms.map fun x => (x.1, x.2.1, x.2.2.subst σ)) (m.subst σ)
  | .recConst n T b => .recConst n T (b.subst (liftSubst σ))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := sizeOf_snd_lt h; omega)
    | (rename_i h; have := sizeOf_arm_lt h; omega)

/-- The substitution one β (or ζ) step performs. -/
@[expose] def single (a : LExpr) : Nat → LExpr
  | 0 => a
  | n + 1 => .bvar n

@[expose] def inst (body a : LExpr) : LExpr := body.subst (single a)

/-- `F a₀ … aₖ₋₁`. -/
@[expose] def spine (F : LExpr) : List LExpr → LExpr
  | [] => F
  | a :: as => spine (.app F a) as

end LExpr

/-- The evaluation of a literal operation on two literals, as the kernel computes it (`Nat.sub`
truncated, `x / 0 = 0`, `x % 0 = x`, `Nat.beq` and `Nat.ble` to `Bool`). -/
@[expose] def NatOp.eval : NatOp → Nat → Nat → LExpr
  | .add, a, b => .lit (a + b)
  | .sub, a, b => .lit (a - b)
  | .mul, a, b => .lit (a * b)
  | .div, a, b => .lit (a / b)
  | .mod, a, b => .lit (a % b)
  | .beq, a, b => .boolLit (a == b)
  | .ble, a, b => .boolLit (decide (a ≤ b))

end Obend.Lower

namespace Obend.Lower
open Obend.Core.Term (splitValues)
open Obend.Core.Ty (Ty)
set_option autoImplicit false

open LExpr in
inductive SStep : LExpr → LExpr → Prop where
  | beta (T : Ty) (body argument : LExpr) : SStep (.app (.lam T body) argument) (body.inst argument)
  | appFun {f f' : LExpr} (a : LExpr) : SStep f f' → SStep (.app f a) (.app f' a)
  | zeta (T : Ty) (value body : LExpr) : SStep (.letE T value body) (body.inst value)
  | delta (name : String) (body : LExpr) : SStep (.const name body) body
  | succFold (n : Nat) : SStep (.natSucc (.lit n)) (.lit (n + 1))
  | succArg {a a' : LExpr} : SStep a a' → SStep (.natSucc a) (.natSucc a')
  | binLit (op : NatOp) (a b : Nat) : SStep (.natBin op (.lit a) (.lit b)) (op.eval a b)
  | binLeft {l l' : LExpr} (op : NatOp) (r : LExpr) : SStep l l' → SStep (.natBin op l r) (.natBin op l' r)
  | binRight {r r' : LExpr} (op : NatOp) (a : Nat) : SStep r r' → SStep (.natBin op (.lit a) r) (.natBin op (.lit a) r')
  | natRecZero (T : Ty) (z s : LExpr) : SStep (.natRec T z s (.lit 0)) z
  | natRecSucc (T : Ty) (z s : LExpr) (n : Nat) :
      SStep (.natRec T z s (.lit (n + 1))) (.app (.app s (.lit n)) (.natRec T z s (.lit n)))
  | natRecMajor {m m' : LExpr} (T : Ty) (z s : LExpr) : SStep m m' → SStep (.natRec T z s m) (.natRec T z s m')
  | boolRecFalse (T : Ty) (x y : LExpr) : SStep (.boolRec T x y (.boolLit false)) x
  | boolRecTrue (T : Ty) (x y : LExpr) : SStep (.boolRec T x y (.boolLit true)) y
  | boolRecMajor {m m' : LExpr} (T : Ty) (x y : LExpr) : SStep m m' → SStep (.boolRec T x y m) (.boolRec T x y m')
  | splitRecord (names : List String) (F : LExpr) (fields : List (String × LExpr)) (values : List LExpr) :
      splitValues fields names = some values → SStep (.split names F (.record fields)) (F.spine values)
  | splitMajor {m m' : LExpr} (names : List String) (F : LExpr) : SStep m m' → SStep (.split names F m) (.split names F m')
  | projRecord (name : String) (fields : List (String × LExpr)) (value : LExpr) :
      fields.find? (fun field => field.1 == name) = some (name, value) → SStep (.proj name (.record fields)) value
  | projTarget {t t' : LExpr} (name : String) : SStep t t' → SStep (.proj name t) (.proj name t')
  | casesInject (T : Ty) (arms : List (String × List String × LExpr)) (label : String)
      (fields : List (String × LExpr)) (names : List String) (minor : LExpr) (values : List LExpr) :
      arms.find? (fun arm => arm.1 == label) = some (label, names, minor) →
      splitValues fields names = some values →
      SStep (.cases T arms (.inject label fields)) (minor.spine values)
  | casesMajor {m m' : LExpr} (T : Ty) (arms : List (String × List String × LExpr)) :
      SStep m m' → SStep (.cases T arms m) (.cases T arms m')
  /-- Recursive δ: a recursive definition unfolds by its unfolding equation (`f.eq_def`). -/
  | unfold (name : String) (T : Ty) (body : LExpr) :
      SStep (.recConst name T body) (body.inst (.recConst name T body))

inductive SSteps : LExpr → LExpr → Prop where
  | refl (e : LExpr) : SSteps e e
  | next {a b c : LExpr} : SStep a b → SSteps b c → SSteps a c

/-- The canonical forms of the fragment's types: a literal, a Boolean, a structure's constructor, an
inductive's constructor (fields unevaluated, as the kernel's `whnf` leaves them), a function. -/
inductive Canonical : LExpr → Prop where
  | lit (n : Nat) : Canonical (.lit n)
  | boolLit (b : Bool) : Canonical (.boolLit b)
  | record (fields : List (String × LExpr)) : Canonical (.record fields)
  | inject (label : String) (fields : List (String × LExpr)) : Canonical (.inject label fields)
  | lam (T : Ty) (body : LExpr) : Canonical (.lam T body)

theorem canonical_no_step {v w : LExpr} (h : Canonical v) : ¬ SStep v w := by
  intro s; cases h <;> cases s

end Obend.Lower

namespace Obend.Lower
open Obend.Core.Term
set_option autoImplicit false

/-- The box an erased term lowers to. -/
@[expose] def box : Term := .record []

/-- The `fix` specification of `Nat.rec z s`: `λself. λ_. λk. ifZero k z (s p (self p))` with `p`
the predecessor `ifZero` binds; `z` and `s` are moved under the binders. -/
def natRecSpec (Z S : Term) : Term :=
  .lam (.lam (.lam (.ifZero (.bound 0) (Z.rename (· + 3))
    (.app (.app (S.rename (· + 4)) (.bound 0)) (.app (.bound 3) (.bound 0))))))

/-- The arm of a lowered `cases`: the payload (bound at 0) destructed, its fields passed to the
minor premise. -/
def caseArm (names : List String) (M : Term) : Term := .split (.bound 0) names (M.rename Nat.succ)

/-- The `fix` specification of a recursive definition: `λself. λ_. body` (the body binds `self` at 0). -/
def recSpec (B : Term) : Term := .lam (.lam (B.rename Nat.succ))

@[expose] def lowerT : LExpr → Term
  | .bvar i => .bound i
  | .erased => box
  | .const _ b => lowerT b
  | .app f a => .app (lowerT f) (lowerT a)
  | .lam _ b => .lam (lowerT b)
  | .letE _ v b => .app (.lam (lowerT b)) (lowerT v)
  | .lit n => .nat n
  | .natSucc a => .binary .add (lowerT a) (.nat 1)
  | .natBin op l r => .binary op.prim (lowerT l) (lowerT r)
  | .boolLit b => .boolean b
  | .natRec _ z s m => .app (.fix (natRecSpec (lowerT z) (lowerT s)) box) (lowerT m)
  | .boolRec _ x y m => .ifBool (lowerT m) (lowerT y) (lowerT x)
  | .record fs => .record (fs.map fun x => (x.1, lowerT x.2))
  | .split ns F m => .split (lowerT m) ns (lowerT F)
  | .proj n t => .get (lowerT t) n
  | .inject l fs => .inject l (.record (fs.map fun x => (x.1, lowerT x.2)))
  | .cases _ arms m => .case (lowerT m) (arms.map fun x => (x.1, caseArm x.2.1 (lowerT x.2.2)))
  | .recConst _ _ b => .fix (recSpec (lowerT b)) box
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := LExpr.sizeOf_snd_lt h; omega)
    | (rename_i h; have := LExpr.sizeOf_arm_lt h; omega)

/-- Lowered fields. -/
def lowerFields (fs : List (String × LExpr)) : List (String × Term) := fs.map fun x => (x.1, lowerT x.2)

end Obend.Lower

namespace Obend.Lower
open Obend.Core.Ty
set_option autoImplicit false

/-- The fragment's Core4 types. -/
def good : Ty → Bool
  | .natural | .boolean | .emptyRow => true
  | .arrow .reusable .unrestricted A B => good A && good B
  | .field _ m t => good m && good t
  | .variant r => good r
  | _ => false

/-- A reusable unrestricted arrow, the fragment's only function type. -/
abbrev fn (A B : Ty) : Ty := .arrow .reusable .unrestricted A B

/-- `T₀ → … → Tₖ₋₁ → R`. -/
@[expose] def curry : List Ty → Ty → Ty
  | [], R => R
  | T :: Ts, R => fn T (curry Ts R)

/-- The closed field row of named members, in order. -/
@[expose] def fieldRow : List (String × Ty) → Ty
  | [] => .emptyRow
  | (n, T) :: rest => .field n T (fieldRow rest)

/-- The closed sum of a non-recursive inductive: each constructor's label to the field row of its fields. -/
def armsRow : List (String × List String × LExpr) → List (List Ty) → Ty
  | (label, names, _) :: arms, Ts :: sig => .field label (fieldRow (names.zip Ts)) (armsRow arms sig)
  | _, _ => .emptyRow

@[simp] theorem armsRow_nil (sig : List (List Ty)) : armsRow [] sig = .emptyRow := by
  cases sig <;> rfl
@[simp] theorem armsRow_cons (label : String) (names : List String) (body : LExpr)
    (rest : List (String × List String × LExpr)) (Ts : List Ty) (tail : List (List Ty)) :
    armsRow ((label, names, body) :: rest) (Ts :: tail) =
      .field label (fieldRow (names.zip Ts)) (armsRow rest tail) := by rfl

/-- The type of a literal operation's result. -/
def NatOp.resultTy : NatOp → Ty
  | .beq | .ble => .boolean
  | _ => .natural

@[simp] theorem NatOp.resultTy_eq (op : NatOp) :
    op.resultTy = (match op with | .beq | .ble => .boolean | _ => .natural) := by
  cases op <;> rfl

inductive LTyped : List Ty → LExpr → Ty → Prop where
  | bvar {Γ : List Ty} {i : Nat} {T : Ty} : Γ[i]? = some T → LTyped Γ (.bvar i) T
  | erased (Γ : List Ty) : LTyped Γ .erased .emptyRow
  | const {Γ : List Ty} {name : String} {body : LExpr} {T : Ty} : LTyped Γ body T → LTyped Γ (.const name body) T
  | app {Γ : List Ty} {f a : LExpr} {A B : Ty} : LTyped Γ f (fn A B) → LTyped Γ a A → good A = true →
      LTyped Γ (.app f a) B
  | lam {Γ : List Ty} {A B : Ty} {body : LExpr} : good A = true → LTyped (A :: Γ) body B → LTyped Γ (.lam A body) (fn A B)
  | letE {Γ : List Ty} {A B : Ty} {v body : LExpr} : good A = true → LTyped Γ v A → LTyped (A :: Γ) body B →
      LTyped Γ (.letE A v body) B
  | lit (Γ : List Ty) (n : Nat) : LTyped Γ (.lit n) .natural
  | natSucc {Γ : List Ty} {a : LExpr} : LTyped Γ a .natural → LTyped Γ (.natSucc a) .natural
  | natBin {Γ : List Ty} {l r : LExpr} (op : NatOp) : LTyped Γ l .natural → LTyped Γ r .natural →
      LTyped Γ (.natBin op l r) op.resultTy
  | boolLit (Γ : List Ty) (b : Bool) : LTyped Γ (.boolLit b) .boolean
  | natRec {Γ : List Ty} {T : Ty} {z s m : LExpr} : good T = true → LTyped Γ z T →
      LTyped Γ s (fn .natural (fn T T)) → LTyped Γ m .natural → LTyped Γ (.natRec T z s m) T
  | boolRec {Γ : List Ty} {T : Ty} {x y m : LExpr} : LTyped Γ x T → LTyped Γ y T → LTyped Γ m .boolean →
      LTyped Γ (.boolRec T x y m) T
  | record {Γ : List Ty} {fs : List (String × LExpr)} {Ts : List Ty} : fs.length = Ts.length →
      (fs.map Prod.fst).Nodup → (∀ T ∈ Ts, good T = true) → (∀ p ∈ fs.zip Ts, LTyped Γ p.1.2 p.2) →
      LTyped Γ (.record fs) (fieldRow ((fs.map Prod.fst).zip Ts))
  | split {Γ : List Ty} {names : List String} {F m : LExpr} {Ts : List Ty} {R : Ty} :
      names.length = Ts.length → names.Nodup → (∀ T ∈ Ts, good T = true) →
      LTyped Γ m (fieldRow (names.zip Ts)) → LTyped Γ F (curry Ts R) → LTyped Γ (.split names F m) R
  | proj {Γ : List Ty} {t : LExpr} {row T : Ty} {name : String} {fuel : Nat} :
      LTyped Γ t row → row.lookup [] fuel name = some T → LTyped Γ (.proj name t) T
  | inject {Γ : List Ty} {label : String} {fs : List (String × LExpr)} {Ts : List Ty} {row : Ty} {fuel : Nat} :
      fs.length = Ts.length → (fs.map Prod.fst).Nodup → (∀ T ∈ Ts, good T = true) →
      (∀ p ∈ fs.zip Ts, LTyped Γ p.1.2 p.2) →
      row.lookup [] fuel label = some (fieldRow ((fs.map Prod.fst).zip Ts)) →
      LTyped Γ (.inject label fs) (.variant row)
  | cases {Γ : List Ty} {R : Ty} {arms : List (String × List String × LExpr)} {sig : List (List Ty)} {m : LExpr} :
      arms.length = sig.length → (arms.map Prod.fst).Nodup →
      LTyped Γ m (.variant (armsRow arms sig)) →
      (∀ p ∈ arms.zip sig, p.1.2.1.length = p.2.length) → (∀ p ∈ arms.zip sig, p.1.2.1.Nodup) →
      (∀ p ∈ arms.zip sig, ∀ T ∈ p.2, good T = true) → good R = true →
      (∀ p ∈ arms.zip sig, LTyped Γ p.1.2.2 (curry p.2 R)) →
      LTyped Γ (.cases R arms m) R
  | recConst {Γ : List Ty} {name : String} {T : Ty} {body : LExpr} : good T = true → LTyped (T :: Γ) body T →
      LTyped Γ (.recConst name T body) T


end Obend.Lower

namespace Obend.Lower
open Obend.Core.Term
open Obend.Core.TermTraverse (rename_comp rename_substitute substitute_rename substitute_comp)
open Obend.Equiv (instantiate_eq single)
set_option autoImplicit false

theorem rename_shift1 (t : Term) (f : Nat → Nat) :
    (t.rename Nat.succ).rename (liftRename f) = (t.rename f).rename Nat.succ := by
  rw [rename_comp, rename_comp]; rfl

theorem rename_shift3 (t : Term) (f : Nat → Nat) :
    (t.rename (· + 3)).rename (liftRename (liftRename (liftRename f))) = (t.rename f).rename (· + 3) := by
  rw [rename_comp, rename_comp]; rfl

theorem rename_shift4 (t : Term) (f : Nat → Nat) :
    (t.rename (· + 4)).rename (liftRename (liftRename (liftRename (liftRename f)))) =
      (t.rename f).rename (· + 4) := by
  rw [rename_comp, rename_comp]; rfl

theorem subst_shift1 (t : Term) (τ : Nat → Term) :
    (t.rename Nat.succ).substitute (liftSubstitution τ) = (t.substitute τ).rename Nat.succ := by
  rw [rename_substitute, substitute_rename]; rfl

theorem subst_shift3 (t : Term) (τ : Nat → Term) :
    (t.rename (· + 3)).substitute (liftSubstitution (liftSubstitution (liftSubstitution τ))) =
      (t.substitute τ).rename (· + 3) := by
  rw [rename_substitute, substitute_rename]
  congr 1; funext i
  simp only [liftSubstitution, rename_comp]

theorem subst_shift4 (t : Term) (τ : Nat → Term) :
    (t.rename (· + 4)).substitute
        (liftSubstitution (liftSubstitution (liftSubstitution (liftSubstitution τ)))) =
      (t.substitute τ).rename (· + 4) := by
  rw [rename_substitute, substitute_rename]
  congr 1; funext i
  simp only [liftSubstitution, rename_comp]

theorem natRecSpec_rename (Z S : Term) (f : Nat → Nat) :
    (natRecSpec Z S).rename f = natRecSpec (Z.rename f) (S.rename f) := by
  simp only [natRecSpec, Term.rename, rename_shift3, rename_shift4]
  rfl

theorem natRecSpec_substitute (Z S : Term) (τ : Nat → Term) :
    (natRecSpec Z S).substitute τ = natRecSpec (Z.substitute τ) (S.substitute τ) := by
  simp only [natRecSpec, Term.substitute, subst_shift3, subst_shift4]
  simp [liftSubstitution, Term.rename]

theorem caseArm_rename (names : List String) (M : Term) (f : Nat → Nat) :
    (caseArm names M).rename (liftRename f) = caseArm names (M.rename f) := by
  simp only [caseArm, Term.rename, rename_shift1]; rfl

theorem caseArm_substitute (names : List String) (M : Term) (τ : Nat → Term) :
    (caseArm names M).substitute (liftSubstitution τ) = caseArm names (M.substitute τ) := by
  simp only [caseArm, Term.substitute, subst_shift1]; rfl

theorem lowerT_rename : ∀ (e : LExpr) (f : Nat → Nat), lowerT (e.rename f) = (lowerT e).rename f
  | .bvar i, f => by simp [LExpr.rename, lowerT, Term.rename]
  | .erased, f => by simp [LExpr.rename, lowerT, Term.rename, box]
  | .const n b, f => by simp only [LExpr.rename, lowerT]; exact lowerT_rename b f
  | .app a b, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename a f, lowerT_rename b f]
  | .lam T b, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename b]
  | .letE T v b, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename b, lowerT_rename v]
  | .lit n, f => by simp [LExpr.rename, lowerT, Term.rename]
  | .natSucc a, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename a f]
  | .natBin op a b, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename a f, lowerT_rename b f]
  | .boolLit b, f => by simp [LExpr.rename, lowerT, Term.rename]
  | .natRec T z s m, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename z f, lowerT_rename s f, lowerT_rename m f,
      natRecSpec_rename, box]
    rfl
  | .boolRec T x y m, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename x f, lowerT_rename y f, lowerT_rename m f]
  | .record fs, f => by
    simp only [LExpr.rename, lowerT, Term.rename, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_rename x.2 f]
  | .split ns F m, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename F f, lowerT_rename m f]
  | .proj n t, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename t f]
  | .inject l fs, f => by
    simp only [LExpr.rename, lowerT, Term.rename, List.map_map]
    congr 2; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_rename x.2 f]
  | .cases T arms m, f => by
    simp only [LExpr.rename, lowerT, Term.rename, List.map_map, lowerT_rename m f]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_rename x.2.2 f, caseArm_rename]
  | .recConst n T b, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename b, recSpec, box, rename_shift1]
    rfl
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

theorem lowerT_liftSubst (σ : Nat → LExpr) :
    (fun i => lowerT (LExpr.liftSubst σ i)) = liftSubstitution (fun i => lowerT (σ i)) := by
  funext i; cases i with
  | zero => simp [LExpr.liftSubst, lowerT, liftSubstitution]
  | succ n => simp [LExpr.liftSubst, liftSubstitution, lowerT_rename]

theorem lowerT_subst : ∀ (e : LExpr) (σ : Nat → LExpr),
    lowerT (e.subst σ) = (lowerT e).substitute (fun i => lowerT (σ i))
  | .bvar i, σ => by simp [LExpr.subst, lowerT, Term.substitute]
  | .erased, σ => by simp [LExpr.subst, lowerT, Term.substitute, box]
  | .const n b, σ => by simp only [LExpr.subst, lowerT]; exact lowerT_subst b σ
  | .app a b, σ => by simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst a σ, lowerT_subst b σ]
  | .lam T b, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst b, lowerT_liftSubst]
  | .letE T v b, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst b, lowerT_subst v, lowerT_liftSubst]
  | .lit n, σ => by simp [LExpr.subst, lowerT, Term.substitute]
  | .natSucc a, σ => by simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst a σ]
  | .natBin op a b, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst a σ, lowerT_subst b σ]
  | .boolLit b, σ => by simp [LExpr.subst, lowerT, Term.substitute]
  | .natRec T z s m, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst z σ, lowerT_subst s σ, lowerT_subst m σ,
      natRecSpec_substitute, box]
    rfl
  | .boolRec T x y m, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst x σ, lowerT_subst y σ, lowerT_subst m σ]
  | .record fs, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_subst x.2 σ]
  | .split ns F m, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst F σ, lowerT_subst m σ]
  | .proj n t, σ => by simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst t σ]
  | .inject l fs, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, List.map_map]
    congr 2; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_subst x.2 σ]
  | .cases T arms m, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, List.map_map, lowerT_subst m σ]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_subst x.2.2 σ, caseArm_substitute]
  | .recConst n T b, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst b, lowerT_liftSubst, recSpec, box,
      subst_shift1]
    rfl
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

/-- **A source β step is a Core4 β step**: lowering commutes with instantiation. -/
theorem lowerT_inst (b a : LExpr) : lowerT (b.inst a) = instantiate (lowerT b) (lowerT a) := by
  rw [LExpr.inst, lowerT_subst, instantiate_eq]
  congr 1; funext i; cases i <;> simp [LExpr.single, single, lowerT]

theorem lowerT_spine : ∀ (F : LExpr) (vs : List LExpr), lowerT (F.spine vs) = applyAll (lowerT F) (vs.map lowerT)
  | F, [] => rfl
  | F, v :: vs => by
    simp only [LExpr.spine, List.map_cons, applyAll]
    rw [lowerT_spine]; simp only [lowerT]

end Obend.Lower

namespace Obend.Lower
open Obend.Core.Term
open Obend.Core.TermTraverse (rename_comp rename_substitute substitute_rename substitute_comp)
open Obend.Equiv
set_option autoImplicit false

/-! ## Core4 facts -/

theorem positive_steps {a b : Term} (h : PositiveSteps a b) : Steps a b := by
  cases h with | begin s r => exact .next s r

theorem positive_trans {a b c : Term} (h : PositiveSteps a b) (r : Steps b c) : PositiveSteps a c := by
  cases h with | begin s r' => exact .begin s (steps_trans r' r)

theorem positive_of_steps_trans {a b c : Term} (r : Steps a b) (h : PositiveSteps b c) : PositiveSteps a c := by
  cases r with
  | refl => exact h
  | next s r' => exact .begin s (steps_trans r' (positive_steps h))

theorem positive_one {a b : Term} (s : Step a b) : PositiveSteps a b := .begin s (.refl _)

theorem positive_congr {a b : Term} (frame : Term → Term)
    (lift : ∀ {x y : Term}, Step x y → Step (frame x) (frame y)) (h : PositiveSteps a b) :
    PositiveSteps (frame a) (frame b) := by
  cases h with | begin s r => exact .begin (lift s) (steps_congr frame lift r)

/-- An applied lowered `Nat.rec` unrolls in four steps to its `ifZero`. -/
theorem natRec_unfold (Z S K : Term) :
    Steps (.app (.fix (natRecSpec Z S) box) K)
      (.ifZero K Z (.app (.app (S.rename Nat.succ) (.bound 0))
        (.app ((Term.fix (natRecSpec Z S) box).rename Nat.succ) (.bound 0)))) := by
  refine .next (.application _ (.fix _ _)) ?_
  refine .next (.application _ (.application _ (.beta _ _))) ?_
  rw [instantiate_eq]; simp only [Term.substitute]
  refine .next (.application _ (.beta _ _)) ?_
  rw [instantiate_eq]; simp only [Term.substitute]
  refine .next (.beta _ _) ?_
  rw [instantiate_eq]; simp only [Term.substitute]
  simp only [rename_substitute, substitute_comp]
  simp [liftSubstitution, single, Term.rename, Term.substitute, substitute_bound, rename_substitute]
  rw [rename_eq_substitute S, rename_eq_substitute (natRecSpec Z S), rename_eq_substitute box]
  exact .refl _

theorem natRec_unfold_positive (Z S K : Term) :
    PositiveSteps (.app (.fix (natRecSpec Z S) box) K)
      (.ifZero K Z (.app (.app (S.rename Nat.succ) (.bound 0))
        (.app ((Term.fix (natRecSpec Z S) box).rename Nat.succ) (.bound 0)))) := by
  have h := natRec_unfold Z S K
  cases h with
  | next s r => exact .begin s r

/-- A lowered recursive definition unfolds in three steps to its body with itself for `self`. -/
theorem recConst_unfold (B : Term) :
    PositiveSteps (.fix (recSpec B) box) (instantiate B (.fix (recSpec B) box)) := by
  refine .begin (Step.fix _ _) ?_
  generalize Term.fix (recSpec B) box = X
  have hs : recSpec B = .lam (.lam (B.rename Nat.succ)) := rfl
  rw [hs]
  refine .next (.application _ (.beta _ _)) ?_
  rw [instantiate_eq]; simp only [Term.substitute]
  refine .next (.beta _ _) ?_
  rw [instantiate_eq, instantiate_eq, rename_substitute, substitute_comp]
  have : (fun i => ((liftSubstitution (single X)) (Nat.succ i)).substitute (single box)) = single X := by
    funext i; cases i with
    | zero => simp only [liftSubstitution, single]; exact shift_one_cancel _ _
    | succ n => simp [liftSubstitution, single, Term.substitute, Term.rename]
  rw [this]; exact .refl _

theorem natOp_result (op : NatOp) (a b : Nat) :
    primitiveResult op.prim (.nat a) (.nat b) = some (lowerT (op.eval a b)) := by
  cases op <;> simp [NatOp.prim, NatOp.eval, primitiveResult, lowerT]

theorem lowerFields_splitValues (fs : List (String × LExpr)) (names : List String) (values : List LExpr)
    (h : splitValues fs names = some values) :
    splitValues (fs.map fun x => (x.1, lowerT x.2)) names = some (values.map lowerT) := by
  rw [splitValues_map lowerT fs names, h]; rfl

theorem find_lowered {α : Type} (g : α → Term) (fs : List (String × α)) (name : String) (value : α)
    (h : fs.find? (fun field => field.1 == name) = some (name, value)) :
    (fs.map fun x => (x.1, g x.2)).find? (fun field => field.1 == name) = some (name, g value) := by
  rw [find?_map_snd g name fs, h]; rfl

theorem caseArm_open (names : List String) (M P : Term) :
    instantiate (caseArm names M) P = .split P names M := by
  simp only [caseArm, instantiate_eq, Term.substitute, single]
  rw [rename_substitute]
  have : (fun i => single P (Nat.succ i)) = Term.bound := by funext i; rfl
  rw [this, substitute_bound]

/-! ## The simulation -/

theorem ahead_case_target {sc sc' : Term} (arms : List (String × Term)) (h : Ahead sc sc') :
    Ahead (.case sc arms) (.case sc' arms) :=
  .case h rfl (zip_refl (fun a b => Ahead a.2 b.2) arms (fun x _ => Ahead.refl x.2))

/-- **One source step, matched**: a stutter that shrinks the source, or a positive Core4 run to a
term the step's lowering is behind. -/
theorem lower_step {s s' : LExpr} (h : SStep s s') :
    (lowerT s' = lowerT s ∧ sizeOf s' < sizeOf s) ∨
      ∃ m, PositiveSteps (lowerT s) m ∧ Ahead (lowerT s') m := by
  induction h with
  | beta T body argument =>
    simp only [lowerT]
    right; refine ⟨_, positive_one (.beta _ _), ?_⟩
    rw [lowerT_inst]; exact Ahead.refl _
  | appFun a _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right; refine ⟨_, positive_congr (fun x => .app x (lowerT a)) (fun s => .application _ s) pos, ?_⟩
      exact .app ah (Ahead.refl _)
  | zeta T value body =>
    simp only [lowerT]
    right; refine ⟨_, positive_one (.beta _ _), ?_⟩
    rw [lowerT_inst]; exact Ahead.refl _
  | delta name body =>
    simp only [lowerT]
    left; exact ⟨by simp, by simp; omega⟩
  | succFold n =>
    simp only [lowerT]
    right; refine ⟨_, positive_one (.primitive _ _ _ _ (.natural _) (.natural _) rfl), ?_⟩
    exact Ahead.refl _
  | succArg _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .binary .add x (.nat 1)) (fun s => .binaryLeft _ _ s) pos, ?_⟩
      exact .binary _ ah (Ahead.refl _)
  | binLit op a b =>
    simp only [lowerT]
    right; refine ⟨_, positive_one (.primitive _ _ _ _ (.natural _) (.natural _) (natOp_result op a b)), ?_⟩
    exact Ahead.refl _
  | binLeft op r _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .binary op.prim x (lowerT r)) (fun s => .binaryLeft _ _ s) pos, ?_⟩
      exact .binary _ ah (Ahead.refl _)
  | binRight op a _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .binary op.prim (.nat a) x)
        (fun s => .binaryRight _ _ (.natural a) s) pos, ?_⟩
      exact .binary _ (Ahead.refl _) ah
  | natRecZero T z s =>
    simp only [lowerT]
    right
    refine ⟨_, positive_trans (natRec_unfold_positive _ _ _) (.next (.zero _ _) (.refl _)), ?_⟩
    exact Ahead.refl _
  | natRecSucc T z s n =>
    simp only [lowerT]
    right
    refine ⟨_, positive_trans (natRec_unfold_positive _ _ _) (.next (.successor _ _ _) (.refl _)), ?_⟩
    simp only [instantiate_eq, Term.substitute, single]
    rw [rename_substitute, rename_substitute]
    have : (fun i => single (Term.nat n) (Nat.succ i)) = Term.bound := by funext i; rfl
    rw [this, substitute_bound, substitute_bound]
    exact Ahead.refl _
  | natRecMajor T z s _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_trans (natRec_unfold_positive _ _ _) (steps_ifZero _ _ (positive_steps pos)), ?_⟩
      exact .run (natRec_unfold _ _ _) (.ifZero ah (Ahead.refl _) (Ahead.refl _))
  | boolRecFalse T x y =>
    simp only [lowerT]
    right; exact ⟨_, positive_one (.ifFalse _ _), Ahead.refl _⟩
  | boolRecTrue T x y =>
    simp only [lowerT]
    right; exact ⟨_, positive_one (.ifTrue _ _), Ahead.refl _⟩
  | boolRecMajor T x y _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun c => .ifBool c (lowerT y) (lowerT x)) (fun s => .ifCondition _ _ s) pos, ?_⟩
      exact .ifBool ah (Ahead.refl _) (Ahead.refl _)
  | splitRecord names F fields values hit =>
    simp only [lowerT]
    right
    refine ⟨_, positive_one (.splitRecord _ _ _ _ (lowerFields_splitValues fields names values hit)), ?_⟩
    rw [lowerT_spine]; exact Ahead.refl _
  | splitMajor names F _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .split x names (lowerT F)) (fun s => .splitTarget _ _ s) pos, ?_⟩
      exact .split names ah (Ahead.refl _)
  | projRecord name fields value hit =>
    simp only [lowerT]
    right
    exact ⟨_, positive_one (.field _ _ _ (find_lowered lowerT fields name value hit)), Ahead.refl _⟩
  | projTarget name _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .get x name) (fun s => .target _ s) pos, ?_⟩
      exact .get name ah
  | casesInject T arms label fields names minor values armHit hit =>
    simp only [lowerT]
    right
    have found := find_lowered (fun p => caseArm p.1 (lowerT p.2)) arms label (names, minor) armHit
    refine ⟨applyAll (lowerT minor) (values.map lowerT), .begin (.caseInject _ _ _ _ found) ?_, ?_⟩
    · rw [caseArm_open]
      exact .next (.splitRecord _ _ _ _ (lowerFields_splitValues fields names values hit)) (.refl _)
    · rw [lowerT_spine]; exact Ahead.refl _
  | unfold name T body =>
    simp only [lowerT]
    right; refine ⟨_, recConst_unfold _, ?_⟩
    rw [lowerT_inst]; simp only [lowerT]; exact Ahead.refl _
  | casesMajor T arms _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .case x _) (fun s => .caseTarget _ s) pos, ?_⟩
      exact ahead_case_target _ ah

/-! ## The theorem -/

/-- `lowerT v` and a value reached by a chain of `Ahead` links. -/
inductive AheadChain : Term → Term → Prop where
  | refl (t : Term) : AheadChain t t
  | snoc {t m u : Term} : AheadChain t m → Ahead m u → AheadChain t u

theorem AheadChain.literal {v w : Term} (lit : Literal v) (h : AheadChain v w) : w = v := by
  induction h with
  | refl => rfl
  | snoc _ a ih => subst ih; exact inv_literal_behind lit a

theorem AheadChain.sameRuns {t u : Term} (h : AheadChain t u) : SameRuns t u := by
  induction h with
  | refl => exact ⟨fun _ => Iff.rfl, Iff.rfl⟩
  | snoc _ a ih =>
    have s := sameRuns_of_ahead a
    exact ⟨fun o => (ih.halts o).trans (s.halts o), ih.converges.trans s.converges⟩

/-- **`lower_value`**: canonical forms lower to Core4 values. -/
theorem lower_value {v : LExpr} (h : Canonical v) : Value (lowerT v) := by
  cases h <;> simp only [lowerT] <;> constructor

/-- **`lower_sound`, general form**: a source run to a canonical form is matched by a Core4 evaluation
of the lowered term, to a value that is the lowered canonical form up to a chain of `Ahead` links. -/
theorem lower_sound {e v : LExpr} (run : SSteps e v) (canonical : Canonical v) :
    ∃ w, Evaluates (lowerT e) w ∧ AheadChain (lowerT v) w := by
  induction run with
  | refl => exact ⟨_, ⟨.refl _, lower_value canonical⟩, .refl _⟩
  | next st _ ih =>
    obtain ⟨w, ⟨steps, value⟩, chain⟩ := ih canonical
    rcases lower_step st with ⟨e, _⟩ | ⟨m, pos, ah⟩
    · rw [e] at steps; exact ⟨w, ⟨steps, value⟩, chain⟩
    · obtain ⟨w', ev, a⟩ := evaluates_behind ah ⟨steps, value⟩
      exact ⟨w', ⟨steps_trans (positive_steps pos) ev.1, ev.2⟩, chain.snoc a⟩

/-- **`lower_sound` at `Nat`**: `Evaluates (lowerT e) (lowerT (lit n))`. -/
theorem lower_sound_nat {e : LExpr} {n : Nat} (run : SSteps e (.lit n)) :
    Evaluates (lowerT e) (lowerT (.lit n)) := by
  obtain ⟨w, ev, chain⟩ := lower_sound run (.lit n)
  simp only [lowerT] at chain ⊢
  rw [chain.literal (.nat n)] at ev; exact ev

/-- **`lower_sound` at `Bool`**. -/
theorem lower_sound_bool {e : LExpr} {b : Bool} (run : SSteps e (.boolLit b)) :
    Evaluates (lowerT e) (lowerT (.boolLit b)) := by
  obtain ⟨w, ev, chain⟩ := lower_sound run (.boolLit b)
  simp only [lowerT] at chain ⊢
  rw [chain.literal (.boolean b)] at ev; exact ev

/-- **`lower_sound` at a fragment inductive**: the lowered term evaluates to the same constructor,
whose payload has the completed runs of the lowered fields. -/
theorem lower_sound_inject {e : LExpr} {label : String} {fields : List (String × LExpr)}
    (run : SSteps e (.inject label fields)) :
    ∃ P, Evaluates (lowerT e) (.inject label P) ∧ AheadChain (.record (lowerFields fields)) P := by
  obtain ⟨w, ev, chain⟩ := lower_sound run (.inject label fields)
  simp only [lowerT] at chain
  suffices ∀ {t u : Term}, AheadChain t u → ∀ R, t = .inject label R →
      ∃ P, u = .inject label P ∧ AheadChain R P by
    obtain ⟨P, rfl, c⟩ := this chain _ rfl; exact ⟨P, ev, c⟩
  intro t u c
  induction c with
  | refl => intro R h; exact ⟨R, h, .refl _⟩
  | snoc _ a ih =>
    intro R h
    obtain ⟨P, rfl, c⟩ := ih R h
    obtain ⟨P', rfl, a'⟩ := inv_inject_behind a
    exact ⟨P', rfl, c.snoc a'⟩

/-! ## Teeth -/

theorem evaluates_unique {t v v' : Term} (h : Evaluates t v) (h' : Evaluates t v') : v = v' := by
  obtain ⟨s, val⟩ := h
  obtain ⟨s', val'⟩ := h'
  induction s with
  | refl => exact (value_steps_eq val s').symm
  | next st _ ih =>
    cases s' with
    | refl => exact absurd st (value_no_step val')
    | next st' r' => cases step_deterministic st st'; exact ih val r'

/-- A lowering that drops `Nat.rec`'s minor premise (its successor case keeps only the recursive result). -/
def lowerDropMinor : LExpr → Term
  | .natRec T z _ m => lowerT (.natRec T z (.lam .natural (.lam .natural (.bvar 0))) m)
  | e => lowerT e

/-- A lowering that maps `Nat.sub` to `add`. -/
def lowerSubAdd : LExpr → Term
  | .natBin .sub l r => lowerT (.natBin .add l r)
  | e => lowerT e

/-- `Nat.rec 7 (fun _ ih => ih + 1) 1`. -/
def succOnce : LExpr :=
  .natRec .natural (.lit 7) (.lam .natural (.lam .natural (.natSucc (.bvar 0)))) (.lit 1)

theorem succOnce_runs : SSteps succOnce (.lit 8) := by
  have e1 : (LExpr.lam .natural (.natSucc (.bvar 0))).inst (.lit 0) = .lam .natural (.natSucc (.bvar 0)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst]
  have e2 : ∀ R : LExpr, (LExpr.natSucc (.bvar 0)).inst R = .natSucc R := fun R => by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  refine .next (.natRecSucc _ _ _ 0) ?_
  refine .next (.appFun _ (.beta _ _ _)) ?_
  rw [e1]
  refine .next (.beta _ _ _) ?_
  rw [e2]
  refine .next (.succArg (.natRecZero _ _ _)) ?_
  exact .next (.succFold 7) (.refl _)

theorem dropped_runs :
    SSteps (.natRec .natural (.lit 7) (.lam .natural (.lam .natural (.bvar 0))) (.lit 1)) (.lit 7) := by
  have e1 : (LExpr.lam .natural (.bvar 0)).inst (.lit 0) = .lam .natural (.bvar 0) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst]
  have e2 : ∀ R : LExpr, (LExpr.bvar 0).inst R = R := fun R => by simp [LExpr.inst, LExpr.subst, LExpr.single]
  refine .next (.natRecSucc _ _ _ 0) ?_
  refine .next (.appFun _ (.beta _ _ _)) ?_
  rw [e1]
  refine .next (.beta _ _ _) ?_
  rw [e2]
  exact .next (.natRecZero _ _ _) (.refl _)

/-- **Tooth**: dropping the minor premise is refused by `lower_sound`: `Nat.rec 7 (fun _ ih => ih + 1) 1`
reduces to `8`, its mis-lowering evaluates to `7`. -/
theorem dropMinor_refuted :
    ¬ ∀ (e : LExpr) (n : Nat), SSteps e (.lit n) → Evaluates (lowerDropMinor e) (.nat n) := by
  intro claim
  have bad := claim succOnce 8 succOnce_runs
  have good := lower_sound_nat dropped_runs
  simp only [lowerDropMinor, succOnce] at bad
  simp only [lowerT] at bad good
  have := evaluates_unique bad good
  simp at this

/-- **Tooth**: `Nat.sub` lowered to `add` is refused: `5 - 3` reduces to `2`, its mis-lowering to `8`. -/
theorem subAdd_refuted :
    ¬ ∀ (e : LExpr) (n : Nat), SSteps e (.lit n) → Evaluates (lowerSubAdd e) (.nat n) := by
  intro claim
  have bad := claim (.natBin .sub (.lit 5) (.lit 3)) 2 (.next (.binLit .sub 5 3) (.refl _))
  have good := lower_sound_nat (e := .natBin .add (.lit 5) (.lit 3)) (n := 8) (.next (.binLit .add 5 3) (.refl _))
  simp only [lowerSubAdd] at bad
  simp only [lowerT] at bad good
  have := evaluates_unique bad good
  simp at this

end Obend.Lower

namespace Obend.Lower.Fragment
open Lean Meta
open Obend.Core.Ty (Ty)
open Obend.Lower
set_option autoImplicit false

/-- The annotation of a binder whose type has no Core4 type in the fragment. -/
def untyped : Ty := .variable 0

/-- The read's context: the binders in scope (outermost first) and the recursive definitions being
read, each bound to the variable that stands for it in its own body. -/
structure Ctx where
  locals : Array Expr := #[]
  recs : List (Name × Expr) := []
  /-- read recursive definitions from their unfolding equations (else through the kernel's value) -/
  equations : Bool := true

/-- The read's state: the unfolding budget, and what the read reports (each recursive definition read
through its unfolding equation, or through the kernel's value when it has none). -/
structure St where
  fuel : Nat
  notes : Array String := #[]

abbrev ReadM := ReaderT Ctx (StateRefT St MetaM)

def tick : ReadM Unit := do
  let st ← get
  if st.fuel == 0 then throwError "the fragment's unfolding budget is exhausted"
  set { st with fuel := st.fuel - 1 }

def note (s : String) : ReadM Unit := modify fun st => if st.notes.contains s then st else { st with notes := st.notes.push s }

/-- A recursive definition's unfolding equation `c = fun xs => rhs[c]` (`c.eq_def`), as the
λ-abstraction of its right-hand side; `none` for a definition that is not recursive or has none. -/
def unfoldingBody? (c : Name) (us : List Level) : MetaM (Option Expr) := do
  let some eqn ← (try getUnfoldEqnFor? c (nonRec := false) catch _ => pure none) | return none
  let info ← getConstInfo eqn
  let ty := info.type.instantiateLevelParams info.levelParams us
  forallTelescopeReducing ty fun xs eq => do
    let some (_, _, rhs) := eq.eq? | return none
    unless rhs.find? (·.isConstOf c) |>.isSome do return none
    return some (← mkLambdaFVars xs rhs)

def literalOp? : Name → Option NatOp
  | ``Nat.add => some .add | ``Nat.sub => some .sub | ``Nat.mul => some .mul | ``Nat.div => some .div
  | ``Nat.mod => some .mod | ``Nat.beq => some .beq | ``Nat.ble => some .ble
  | _ => none

/-- A type, a proof, or a type former. -/
def erasable (e : Expr) : MetaM Bool := do
  if ← isProof e then return true
  if ← isType e then return true
  isTypeFormer e

def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => toString n

/-- The constructor's fields (after its parameters) as `(name, type)` under fresh variables. -/
def ctorFields {α : Type} (ctor : Name) (us : List Level) (params : Array Expr) (k : Array (String × Expr) → MetaM α)
    : MetaM α := do
  let info ← getConstInfoCtor ctor
  let ty ← instantiateForall (info.type.instantiateLevelParams info.levelParams us) params
  forallTelescopeReducing ty fun xs _ => do
    let fields ← xs.mapM fun x => do return (shortName (← x.fvarId!.getUserName), ← inferType x)
    k fields

/-- An inductive of the fragment: computational (not in `Prop`), or a field-less `Prop` structure
(whose K-like recursor `toCtorWhenK` reduces on erased `{}`), not recursive, no indices, one inductive
in its block. -/
def fragmentInductive? (n : Name) : MetaM (Option InductiveVal) := do
  match (← getEnv).find? n with
  | some (.inductInfo v) =>
    let isPropInd ← forallTelescopeReducing v.type fun _ s => pure s.isProp
    let kLikePropStruct ← if isPropInd && isStructure (← getEnv) n then
      pure (getStructureFields (← getEnv) n).isEmpty
    else pure false
    if (!isPropInd || kLikePropStruct) && v.numIndices == 0 && !v.isRec && v.all.length == 1 && !v.isNested then return some v else return none
  | _ => return none

mutual
/-- The Core4 type of a binder of type `T`. -/
partial def binderTy (T : Expr) : MetaM Ty := do
  if ← isProp T then return .emptyRow
  if ← isTypeFormerType T then return .emptyRow
  return (← lowerTy T).getD untyped

/-- **`lowerTy`**: the Core4 type of a fragment type (proofs and types erased to `{}`). -/
partial def lowerTy (T : Expr) : MetaM (Option Ty) := do
  let T ← whnf T
  if ← isProp T then return some .emptyRow
  if ← isTypeFormerType T then return some .emptyRow
  match T with
  | .forallE n A B bi =>
    withLocalDecl n bi A fun x => do
      let a ← binderTy A
      if a == untyped then return none
      let some b ← lowerTy (B.instantiate1 x) | return none
      return some (fn a b)
  | _ =>
    let .const c us := T.getAppFn | return none
    if c == ``Nat then return some .natural
    if c == ``Bool then return some .boolean
    let some v ← fragmentInductive? c | return none
    let params := T.getAppArgs.extract 0 v.numParams
    if params.size != v.numParams then return none
    let row ← v.ctors.mapM fun ctor => ctorFields ctor us params fun fields => do
      let mut out : List (String × Ty) := []
      for (n, t) in fields.toList.reverse do
        let some ty ← binderTy' t | return none
        out := (n, ty) :: out
      return some (shortName ctor, fieldRow out)
    if row.any Option.isNone then return none
    let row := row.filterMap id
    if isStructure (← getEnv) c then
      match row with
      | [(_, r)] => return some r
      | _ => return none
    else return some (.variant (fieldRow row))

partial def binderTy' (T : Expr) : MetaM (Option Ty) := do
  let t ← binderTy T
  return if t == untyped then none else some t
end

def localIndex (x : Expr) : ReadM LExpr := do
  let locals := (← read).locals
  match locals.findIdx? (· == x) with
  | some i => return .bvar (locals.size - 1 - i)
  | none => throwError "the term is open: {x}"

def withBinder {α : Type} (n : Name) (T : Expr) (value? : Option Expr) (k : Expr → ReadM α) : ReadM α := do
  match value? with
  | none => withLocalDeclD n T fun x => withReader (fun c => { c with locals := c.locals.push x }) (k x)
  | some v => withLetDecl n T v fun x => withReader (fun c => { c with locals := c.locals.push x }) (k x)

mutual
/-- Read a fragment term. -/
partial def readExpr (e : Expr) : ReadM LExpr := do
  tick
  if ← erasable e then return .erased
  match e with
  | .mdata _ b => readExpr b
  | .fvar _ => localIndex e
  | .lit (.natVal n) => return .lit n
  | .lit (.strVal _) => throwError "out of the fragment: a string literal"
  | .lam n T b _ =>
    let A ← binderTy T
    withBinder n T none fun x => return .lam A (← readExpr (b.instantiate1 x))
  | .letE n T v b _ =>
    let A ← binderTy T
    let v' ← readExpr v
    withBinder n T (some v) fun x => return .letE A v' (← readExpr (b.instantiate1 x))
  | .proj S i t =>
    let some _ ← fragmentInductive? S | throwError "out of the fragment: projection of {S}"
    let fields := getStructureFields (← getEnv) S
    let some f := fields[i]? | throwError "a projection out of range"
    return .proj (shortName f) (← readExpr t)
  | .app .. | .const .. => readApp e
  | _ => throwError "out of the fragment: {e}"

partial def readSpine (head : LExpr) (args : Array Expr) : ReadM LExpr := do
  let mut acc := head
  for a in args do acc := .app acc (← readExpr a)
  return acc

partial def resultTy (e : Expr) : ReadM Ty := do
  return (← lowerTy (← inferType e)).getD untyped

/-- An application, by its head. -/
partial def readApp (e : Expr) : ReadM LExpr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const c us := f | do
    readSpine (← readExpr f) args
  let env ← getEnv
  let etaThen (arity : Nat) (k : Array Expr → Array Expr → ReadM LExpr) : ReadM LExpr := do
    if args.size < arity then readExpr (← etaExpand e)
    else k (args.extract 0 arity) (args.extract arity args.size)
  if c == ``Nat.zero then return (← readSpine (.lit 0) args)
  if c == ``Nat.succ then
    return (← etaThen 1 fun a rest => do readSpine (.natSucc (← readExpr a[0]!)) rest)
  if let some op := literalOp? c then
    return (← etaThen 2 fun a rest => do readSpine (.natBin op (← readExpr a[0]!) (← readExpr a[1]!)) rest)
  if c == ``Bool.true then return (← readSpine (.boolLit true) args)
  if c == ``Bool.false then return (← readSpine (.boolLit false) args)
  match env.find? c with
  | some (.recInfo r) =>
    let arity := r.numParams + r.numMotives + r.numMinors + r.numIndices + 1
    etaThen arity fun a rest => do
      let T ← resultTy (mkAppN f a)
      let minors := a.extract (r.numParams + r.numMotives) (r.numParams + r.numMotives + r.numMinors)
      let major ← readExpr a[arity - 1]!
      let ind := r.getMajorInduct
      if ind == ``Nat then
        return (← readSpine (.natRec T (← readExpr minors[0]!) (← readExpr minors[1]!) major) rest)
      if ind == ``Bool then
        return (← readSpine (.boolRec T (← readExpr minors[0]!) (← readExpr minors[1]!) major) rest)
      let some v ← fragmentInductive? ind | throwError "out of the fragment: the recursor {c}"
      let params := a.extract 0 r.numParams
      let arms ← v.ctors.toArray.mapIdxM fun i ctor => do
        let names ← ctorFields ctor us params fun fs => return fs.toList.map (·.1)
        return (shortName ctor, names, ← readExpr minors[i]!)
      if isStructure env ind then
        let some (_, names, minor) := arms[0]? | throwError "a structure without a constructor"
        return (← readSpine (.split names minor major) rest)
      readSpine (.cases T arms.toList major) rest
  | some (.ctorInfo k) =>
    let some v ← fragmentInductive? k.induct | throwError "out of the fragment: the constructor {c}"
    etaThen (k.numParams + k.numFields) fun a rest => do
      let params := a.extract 0 k.numParams
      let names ← ctorFields c us params fun fs => return fs.toList.map (·.1)
      let values ← (a.extract k.numParams a.size).toList.mapM readExpr
      let fields := names.zip values
      if isStructure env v.name then return (← readSpine (.record fields) rest)
      readSpine (.inject (shortName c) fields) rest
  | some (.defnInfo d) =>
    if let some self := (← read).recs.lookup c then
      return (← readSpine (← localIndex self) args)
    if let some rhs ← (if (← read).equations then unfoldingBody? c us else pure none) then
      note s!"{c}: recursive, read from {c}.eq_def"
      let T ← binderTy (← inferType f)
      let body ← withBinder `self (← inferType f) none fun x =>
        withReader (fun ctx => { ctx with recs := (c, x) :: ctx.recs }) do
          readExpr (rhs.replace fun e => if e.isConstOf c then some x else none)
      return (← readSpine (.recConst (toString c) T body) args)
    if (d.value.find? fun e => e.isConstOf ``Nat.brecOn || e.isConstOf ``WellFounded.Nat.fix).isSome then
      note s!"{c}: read through its kernel value (no unfolding equation): untyped"
    let body := d.value.instantiateLevelParams d.levelParams us
    let b ← readSpecialized body args.toList
    readSpine (.const (toString c) b) args
  | some _ => throwError "out of the fragment: {c} has no kernel value the fragment reduces"
  | none => throwError "unknown constant {c}"

/-- A definition's value read at a use: each leading λ whose argument is a type is let-bound to it,
so the binder types under it are concrete. -/
partial def readSpecialized (v : Expr) (args : List Expr) : ReadM LExpr := do
  match v, args with
  | .lam n T b _, a :: rest =>
    let A ← binderTy T
    let isTy ← (do return (← isType a) || (← isTypeFormer a) : MetaM Bool)
    withBinder n T (if isTy then some a else none) fun x =>
      return .lam A (← readSpecialized (b.instantiate1 x) rest)
  | .mdata _ b, _ => readSpecialized b args
  | _, _ => readExpr v
end

/-- The fuel for one read: the number of nodes read, definitions unfolded included. -/
def budget : Nat := 2000000

/-- The reader with its notes. -/
def readNoted (e : Expr) (equations : Bool := true) : MetaM (Except String (LExpr × Array String)) := do
  try
    let (r, st) ← (readExpr e).run { equations } |>.run { fuel := budget }
    return .ok (r, st.notes)
  catch ex => return .error (← ex.toMessageData.toString)

/-- **The fragment's reader**: `e` read into Lean-lite, or the reason it is out. -/
def read (e : Expr) : MetaM (Except String LExpr) := do
  return (← readNoted e).map (·.1)

/-- **The fragment** (decidable: `read` is a total computation): `e` is in when it reads. -/
def inFragment (e : Expr) : MetaM Bool := do
  match ← read e with
  | .ok _ => return true
  | .error _ => return false

/-- **`lower`**: the fragment term `e` (relative to the environment of the `MetaM` context), lowered
to Core4, or `none` outside the fragment. -/
def lower (e : Expr) : MetaM (Option Obend.Core.Term.Term) := do
  match ← read e with
  | .ok l => return some (lowerT l)
  | .error _ => return none

/-! ## Reading Theorem Decision Procedures (`readTheoremDecider`) -/

/-- Standard axioms permitted in a source theorem prior to `transport`. `sorryAx` and custom axioms
are rejected. -/
def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Quot.sound || n == ``Classical.choice

/-- Synthesize the `Bool`-valued decision expression for proposition `p` in the fragment
(supporting `Eq` and `Ne` on `Nat` and `Bool`, `<`, `≤`, `>`, and `≥` on `Nat`, `And`, `Or`, `Not`,
`Iff`, `True`, `False`, and propositional implication `P → Q`), working even in standalone
`importModules` environments where typeclass extensions are not initialized. -/
partial def synthFragmentDeciderBool (p : Expr) : MetaM Expr := do
  let boolTy := mkConst ``Bool
  let motive := mkLambda `_ .default boolTy boolTy
  let bTrue := mkConst ``Bool.true
  let bFalse := mkConst ``Bool.false
  if let .forallE _ P Q _ := p then
    if (← isProp P) && !Q.hasLooseBVars then
      let dp ← synthFragmentDeciderBool P
      let dq ← synthFragmentDeciderBool Q
      return mkApp4 (mkConst ``Bool.rec [Level.one]) motive bTrue dq dp
  let fn := p.getAppFn
  let args := p.getAppArgs
  if fn.isConstOf ``True && args.size == 0 then
    return bTrue
  if fn.isConstOf ``False && args.size == 0 then
    return bFalse
  if fn.isConstOf ``Eq && args.size == 3 then
    let ty ← whnf args[0]!
    let lhs := args[1]!
    let rhs := args[2]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decEq) lhs rhs
      return mkApp2 (mkConst ``Decidable.decide) p inst
    if ty.isConstOf ``Bool then
      let inst := mkApp2 (mkConst ``Bool.decEq) lhs rhs
      return mkApp2 (mkConst ``Decidable.decide) p inst
  if fn.isConstOf ``Ne && args.size == 3 then
    let eqProp := mkApp3 (mkConst ``Eq fn.constLevels!) args[0]! args[1]! args[2]!
    let dp ← synthFragmentDeciderBool eqProp
    return mkApp4 (mkConst ``Bool.rec [Level.one]) motive bTrue bFalse dp
  if (fn.isConstOf ``LT.lt && args.size == 4) then
    let ty ← whnf args[0]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decLt) args[2]! args[3]!
      return mkApp2 (mkConst ``Decidable.decide) p inst
  if (fn.isConstOf ``LE.le && args.size == 4) then
    let ty ← whnf args[0]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decLe) args[2]! args[3]!
      return mkApp2 (mkConst ``Decidable.decide) p inst
  if (fn.isConstOf ``GT.gt && args.size == 4) then
    let ty ← whnf args[0]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decLt) args[3]! args[2]!
      return mkApp2 (mkConst ``Decidable.decide) (mkApp2 (mkConst ``Nat.lt) args[3]! args[2]!) inst
  if (fn.isConstOf ``GE.ge && args.size == 4) then
    let ty ← whnf args[0]!
    if ty.isConstOf ``Nat then
      let inst := mkApp2 (mkConst ``Nat.decLe) args[3]! args[2]!
      return mkApp2 (mkConst ``Decidable.decide) (mkApp2 (mkConst ``Nat.le) args[3]! args[2]!) inst
  if fn.isConstOf ``Nat.lt && args.size == 2 then
    let inst := mkApp2 (mkConst ``Nat.decLt) args[0]! args[1]!
    return mkApp2 (mkConst ``Decidable.decide) p inst
  if fn.isConstOf ``Nat.le && args.size == 2 then
    let inst := mkApp2 (mkConst ``Nat.decLe) args[0]! args[1]!
    return mkApp2 (mkConst ``Decidable.decide) p inst
  if fn.isConstOf ``And && args.size == 2 then
    let dp ← synthFragmentDeciderBool args[0]!
    let dq ← synthFragmentDeciderBool args[1]!
    return mkApp4 (mkConst ``Bool.rec [Level.one]) motive bFalse dq dp
  if fn.isConstOf ``Or && args.size == 2 then
    let dp ← synthFragmentDeciderBool args[0]!
    let dq ← synthFragmentDeciderBool args[1]!
    return mkApp4 (mkConst ``Bool.rec [Level.one]) motive dq bTrue dp
  if fn.isConstOf ``Iff && args.size == 2 then
    let dp ← synthFragmentDeciderBool args[0]!
    let dq ← synthFragmentDeciderBool args[1]!
    let eqProp := mkApp3 (mkConst ``Eq [Level.one]) boolTy dp dq
    let inst := mkApp2 (mkConst ``Bool.decEq) dp dq
    return mkApp2 (mkConst ``Decidable.decide) eqProp inst
  if fn.isConstOf ``Not && args.size == 1 then
    let dp ← synthFragmentDeciderBool args[0]!
    return mkApp4 (mkConst ``Bool.rec [Level.one]) motive bTrue bFalse dp
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  return mkApp2 (mkConst ``Decidable.decide) p inst

/-- Peel leading computational universal quantifiers `∀ (x₁ : A₁) ... (xₖ : Aₖ), P` and synthesize
`Decidable.decide P` at the propositional body `P`. -/
partial def buildDeciderExpr (ty : Expr) : MetaM (Expr × List Ty) := do
  match ty with
  | .forallE n A B bi =>
    let aIsProp ← isProp A
    let aIsType ← isTypeFormerType A
    if !aIsProp && !aIsType then
      let some argTy ← lowerTy A
        | throwError "quantifier domain {A} has no Core4 type in the fragment"
      withLocalDecl n bi A fun x => do
        let (bodyDec, restTys) ← buildDeciderExpr (B.instantiate1 x)
        let lamExpr ← mkLambdaFVars #[x] bodyDec
        return (lamExpr, argTy :: restTys)
    else
      return (← synthFragmentDeciderBool ty, [])
  | _ =>
    return (← synthFragmentDeciderBool ty, [])

/-- **`readTheoremDecider`**: given a theorem or proposition declaration `declName` in the
environment:
1. verifies `declName` has a kernel proof term, is not `unsafe`, and does not depend on `sorryAx` or
   non-standard axioms (`Lean.collectAxioms`),
2. verifies its type is a `Prop`,
3. strips leading computational universal quantifiers and synthesizes `Decidable` for the body, and
4. reads the resulting decision procedure `fun x₁ ... xₖ => decide P` into `LExpr` along with the
   lowered argument types `argTys : List Ty`. -/
def readTheoremDecider (declName : Name) : MetaM (Except String (LExpr × List Ty)) := do
  let env ← getEnv
  let some info := env.find? declName
    | return .error s!"unknown declaration {declName}"
  if info.isUnsafe then
    return .error s!"declaration {declName} is unsafe"
  match info with
  | .thmInfo _ | .defnInfo _ => pure ()
  | .axiomInfo _ => return .error s!"declaration {declName} is an unproved axiom"
  | .opaqueInfo _ => return .error s!"declaration {declName} is opaque"
  | _ => return .error s!"declaration {declName} has no proof term"
  let axioms ← Lean.collectAxioms declName
  for ax in axioms do
    unless allowedAxiom ax do
      return .error s!"declaration {declName} depends on disallowed axiom {ax}"
  let ty := info.type.instantiateLevelParams info.levelParams (info.levelParams.map fun _ => Level.zero)
  unless (← isProp ty) do
    return .error s!"declaration {declName} is not a proposition"
  try
    let (decExpr, argTys) ← buildDeciderExpr ty
    match ← read decExpr with
    | .ok lexpr => return .ok (lexpr, argTys)
    | .error msg => return .error msg
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Obend.Lower.Fragment

namespace Obend.Lower
open Obend.Core.Ty (Ty)
@[simp] theorem curry_nil (R : Ty) : curry [] R = R := by
  simp only [curry]
@[simp] theorem curry_cons (T : Ty) (Ts : List Ty) (R : Ty) :
    curry (T :: Ts) R = fn T (curry Ts R) := by
  simp only [curry]
@[simp] theorem fieldRow_nil : fieldRow [] = .emptyRow := by
  simp only [fieldRow]
@[simp] theorem fieldRow_cons (n : String) (T : Ty) (fs : List (String × Ty)) :
    fieldRow ((n, T) :: fs) = .field n T (fieldRow fs) := by
  simp only [fieldRow]
@[simp] theorem natRecSpec_eq (Z S : Obend.Core.Term.Term) :
    natRecSpec Z S = .lam (.lam (.lam (.ifZero (.bound 0) (Z.rename (· + 3))
      (.app (.app (S.rename (· + 4)) (.bound 0)) (.app (.bound 3) (.bound 0)))))) := by
  simp only [natRecSpec]
@[simp] theorem caseArm_eq (names : List String) (M : Obend.Core.Term.Term) :
    caseArm names M = .split (.bound 0) names (M.rename Nat.succ) := by
  simp only [caseArm]
@[simp] theorem recSpec_eq (B : Obend.Core.Term.Term) :
    recSpec B = .lam (.lam (B.rename Nat.succ)) := by
  simp only [recSpec]

end Obend.Lower
end
