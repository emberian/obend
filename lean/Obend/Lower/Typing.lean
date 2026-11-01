module
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
public import Obend.Lower.Syntax
@[expose] public section
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

/-- `T₀ → … → Tₖ₋₁ → R`. -/
def curry : List Ty → Ty → Ty
  | [], R => R
  | T :: Ts, R => fn T (curry Ts R)

/-- The closed sum of a non-recursive inductive: each constructor's label to the field row of its fields. -/
def armsRow : List (String × List String × LExpr) → List (List Ty) → Ty
  | (label, names, _) :: arms, Ts :: sig => .field label (fieldRow (names.zip Ts)) (armsRow arms sig)
  | _, _ => .emptyRow

/-- The type of a literal operation's result. -/
def NatOp.resultTy : NatOp → Ty
  | .beq | .ble => .boolean
  | _ => .natural

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
end
