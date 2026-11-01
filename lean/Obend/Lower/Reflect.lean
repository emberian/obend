module
/-
# Obend.Lower.Reflect — prototype lowering bridge connecting Leaf.Flatten to Lower.Transport

Provides:
- `LayoutEnv`: Layout environment mapping member names and record positions.
- `lowerTerm` & `lowerLeafDef`: Lowers acyclic first-order method definitions into `LExpr`.
- `ReflectedObject`: Reflected object bundling lowered definitions with `specSlot` pin witnesses.
- `reflectComposition`: Compiles flattened prototype compositions into reflected objects.
- `reflect_override_blocks`: Proves that modifying any ancestor layer immediately transitions `specSlot` to `.blocked`.
-/
public import Obend.Logic.Obligation
public import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Slot.World
public import Obend.Lower.Syntax
public import Obend.Lower.Lower
public import Obend.Lower.Transport

@[expose] public section
namespace Obend.Lower.Reflect

open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty)
open Obend.Logic (Composition)
open Obend.Leaf (LeafDef LeafPin LeafView specSlot Candidate moved_pin_blocks)
open Obend.Slot.World (holdsAt)
open Obend.Lower (LExpr lowerT)

set_option autoImplicit false

/-- Layout Environment mapping record field names and method slots to de Bruijn indices. -/
structure LayoutEnv where
  fields : List (String × Nat)
  selfIndex : Nat
  arity : Nat
  deriving DecidableEq, Repr

/-- Lower a first-order Core4 term into an `LExpr` under fuel. -/
def lowerTermFuel (env : LayoutEnv) : Nat → Term → Option LExpr
  | 0, _ => none
  | _fuel + 1, .bound i => some (.bvar i)
  | _fuel + 1, .nat n => some (.lit n)
  | _fuel + 1, .boolean b => some (.boolLit b)
  | fuel + 1, .binary .add l r => do return .natBin .add (← lowerTermFuel env fuel l) (← lowerTermFuel env fuel r)
  | fuel + 1, .binary .subtract l r => do return .natBin .sub (← lowerTermFuel env fuel l) (← lowerTermFuel env fuel r)
  | fuel + 1, .binary .multiply l r => do return .natBin .mul (← lowerTermFuel env fuel l) (← lowerTermFuel env fuel r)
  | fuel + 1, .binary .divide l r => do return .natBin .div (← lowerTermFuel env fuel l) (← lowerTermFuel env fuel r)
  | fuel + 1, .binary .modulo l r => do return .natBin .mod (← lowerTermFuel env fuel l) (← lowerTermFuel env fuel r)
  | fuel + 1, .binary .equal l r => do return .natBin .beq (← lowerTermFuel env fuel l) (← lowerTermFuel env fuel r)
  | fuel + 1, .binary .lessEqual l r => do return .natBin .ble (← lowerTermFuel env fuel l) (← lowerTermFuel env fuel r)
  | fuel + 1, .app f a => do return .app (← lowerTermFuel env fuel f) (← lowerTermFuel env fuel a)
  | fuel + 1, .lam b => do return .lam .emptyRow (← lowerTermFuel env fuel b)
  | fuel + 1, .get t m => do return .proj m (← lowerTermFuel env fuel t)
  | fuel + 1, .record fs => do
      let fields ← fs.mapM fun (m, t) => do return (m, ← lowerTermFuel env fuel t)
      return .record fields
  | fuel + 1, .ifBool c x y => do
      return .boolRec .emptyRow (← lowerTermFuel env fuel y) (← lowerTermFuel env fuel x) (← lowerTermFuel env fuel c)
  | _, _ => none

/-- Lower a first-order Core4 term into an `LExpr`. -/
def lowerTerm (env : LayoutEnv) (t : Term) : Option LExpr :=
  lowerTermFuel env 1024 t

/-- Lower a first-order flattened Book definition into Lean-lite `LExpr`.
    Because `Flatten` statically substitutes `super` lookups into provider records,
    `def.code` contains no dynamic mix or open prototypes. -/
def lowerLeafDef (env : LayoutEnv) (d : LeafDef) : Option LExpr :=
  lowerTerm env d.code

/-- The reflected object: a table of lowered expressions paired with the specialization pins
    that guard their contextual validity. -/
structure ReflectedObject where
  name : String
  composition : Composition
  defs : List (String × LExpr)
  pins : List LeafPin
  pins_eq : pins = (Candidate.book name composition).supports := by rfl

/-- Compile a prototype composition into a reflected object guarded by specSlot pins. -/
def reflectComposition (name : String) (C : Composition) (env : LayoutEnv) :
    Option ReflectedObject := do
  guard (C.closedB == true)
  let book := Obend.Leaf.emit C
  let defs ← book.defs.mapM fun d => do
    let e ← lowerLeafDef env d
    pure (d.member, e)
  let pins := (Candidate.book name C).supports
  pure ⟨name, C, defs, pins, rfl⟩

/-- **Dynamic Override Invalidation Theorem**:
    If any ancestor layer in `C` is modified or overridden with different code,
    `specSlot` immediately transitions to `.blocked`, invalidating the reflected `LExpr`
    and preventing stale proofs from being admitted. -/
theorem reflect_override_blocks (v : LeafView) (ref : ReflectedObject)
    (hj : ref.composition.closedB = true)
    {p : LeafPin} (hp : p ∈ ref.pins) (hd : holdsAt v p = false) :
    ∃ dead, specSlot.read (holdsAt v) (some (.book ref.name ref.composition)) =
      .blocked (.book ref.name ref.composition) dead ∧ p ∈ dead := by
  have hp' : p ∈ (Candidate.book ref.name ref.composition).supports := by
    rw [← ref.pins_eq]; exact hp
  obtain ⟨d, hr, hp_in_d, _⟩ := moved_pin_blocks hj hp' hd
  exact ⟨d, hr, hp_in_d⟩

end Obend.Lower.Reflect
end
