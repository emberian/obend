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
  over the arms in constructor order (each arm's minor premise takes the constructor's fields).

Parameters of a constructor or recursor are types and are erased with the motive.
-/
public import Obend.Core.Term
public import Obend.Core.Ty
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term (Primitive)
open Obend.Core.Ty (Ty)
set_option autoImplicit false

/-- The kernel's literal operations on `Nat` that Core4 has a primitive for. -/
inductive NatOp where
  | add | sub | mul | div | mod | beq | ble
  deriving Repr, DecidableEq

/-- The Core4 primitive of a literal operation. -/
def NatOp.prim : NatOp → Primitive
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
def rename (f : Nat → Nat) : LExpr → LExpr
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
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := sizeOf_snd_lt h; omega)
    | (rename_i h; have := sizeOf_arm_lt h; omega)

def liftSubst (σ : Nat → LExpr) : Nat → LExpr
  | 0 => .bvar 0
  | n + 1 => (σ n).rename Nat.succ

def subst (σ : Nat → LExpr) : LExpr → LExpr
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
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := sizeOf_snd_lt h; omega)
    | (rename_i h; have := sizeOf_arm_lt h; omega)

/-- The substitution one β (or ζ) step performs. -/
def single (a : LExpr) : Nat → LExpr
  | 0 => a
  | n + 1 => .bvar n

def inst (body a : LExpr) : LExpr := body.subst (single a)

/-- `F a₀ … aₖ₋₁`. -/
def spine (F : LExpr) : List LExpr → LExpr
  | [] => F
  | a :: as => spine (.app F a) as

end LExpr

/-- The evaluation of a literal operation on two literals, as the kernel computes it (`Nat.sub`
truncated, `x / 0 = 0`, `x % 0 = x`, `Nat.beq` and `Nat.ble` to `Bool`). -/
def NatOp.eval : NatOp → Nat → Nat → LExpr
  | .add, a, b => .lit (a + b)
  | .sub, a, b => .lit (a - b)
  | .mul, a, b => .lit (a * b)
  | .div, a, b => .lit (a / b)
  | .mod, a, b => .lit (a % b)
  | .beq, a, b => .boolLit (a == b)
  | .ble, a, b => .boolLit (decide (a ≤ b))

end Obend.Lower
end
