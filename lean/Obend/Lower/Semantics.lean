module
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
reductions), `Nat.pow`/`Nat.gcd`/`Nat.log2`/the bitwise operations (no Core4 primitive; their
definitions δ-unfold instead), quotients, well-founded recursion (`WellFounded.fix`, `Acc.rec`).
-/
public import Obend.Lower.Syntax
@[expose] public section
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
end
