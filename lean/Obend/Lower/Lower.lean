module
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
* `let` to `(λx. body) value`.
-/
public import Obend.Lower.Semantics
public import Obend.Lower.Fragment
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term
set_option autoImplicit false

/-- The box an erased term lowers to. -/
def box : Term := .record []

/-- The `fix` specification of `Nat.rec z s`: `λself. λ_. λk. ifZero k z (s p (self p))` with `p`
the predecessor `ifZero` binds; `z` and `s` are moved under the binders. -/
def natRecSpec (Z S : Term) : Term :=
  .lam (.lam (.lam (.ifZero (.bound 0) (Z.rename (· + 3))
    (.app (.app (S.rename (· + 4)) (.bound 0)) (.app (.bound 3) (.bound 0))))))

/-- The arm of a lowered `cases`: the payload (bound at 0) destructed, its fields passed to the
minor premise. -/
def caseArm (names : List String) (M : Term) : Term := .split (.bound 0) names (M.rename Nat.succ)

def lowerT : LExpr → Term
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
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := LExpr.sizeOf_snd_lt h; omega)
    | (rename_i h; have := LExpr.sizeOf_arm_lt h; omega)

/-- Lowered fields. -/
def lowerFields (fs : List (String × LExpr)) : List (String × Term) := fs.map fun x => (x.1, lowerT x.2)

/-- **`lower`**: a Lean kernel term, relative to the environment of the `MetaM` context, read into the
fragment (`Fragment.read`) and lowered; `none` outside the fragment. -/
def lower (e : Lean.Expr) : Lean.Meta.MetaM (Option Term) := do
  match ← Fragment.read e with
  | .ok l => return some (lowerT l)
  | .error _ => return none

end Obend.Lower
end
