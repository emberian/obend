module
/-
# Obend.Logic.Program — claims and objects read off an elaborated program, and the producers

What `obend check --obligations`, `obend prove` and `obend ground` run on the elaborator's own
output (the erased term of a package, `Spec.FrontEnd`): nothing here is trusted. The checkers of
`Obend.Logic` re-check what these functions produce.

* The package is a knot `fix (specification … (λ$globals. λ$seed. extend $seed {fields})) {}`;
  its fields include every spec's hidden claims `KEY#claim#NAME` (`claimFields`). A claim's code is
  that field read off the knot (`knotValue`): the `$globals` knot is substituted by the reduction,
  so the code is closed.
* The object a claim is judged of is reached by reducing an entry of the program until a
  `fix (compose …) {seed}` stands at the head (`findObject`); its operands, knot references, are
  reduced to their layers (`decodeProgram`), and `object_bequiv_of_operands` is what makes a fact
  about the decoded composition a fact about the program's own object.
* Producers: `derive`, a rewriter that alternates weak-head runs with late binding at the head of
  the left side; `groundAt` instances for the ground judge.
-/
public import Obend.Logic.Obligation
@[expose] public section
namespace Obend.Logic.Program
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Logic
set_option autoImplicit false

/-- The reduction budget of every read off the program. -/
def readFuel : Nat := 200000

/-- The knot of a lowered selection `get knot entry`. -/
def knotOf : Term → Option Term
  | .get root _ => some root
  | _ => none

/-- The knot's fields: `fix (specification _ (λ. λ. extend _ fields)) _`. -/
def knotFields : Term → List (String × Term)
  | .fix (.specification _ (.lam (.lam (.extend _ fields)))) _ => fields
  | _ => []

/-- A field of the knot, reduced to a value. -/
def knotValue (root : Term) (key : String) : Option Term := Obend.Law.run readFuel (.get root key)

/-- The claims a package declares: `(spec key, claim name)`. -/
def claimFields (root : Term) : List (String × String) :=
  (knotFields root).filterMap fun (key, _) =>
    match key.splitOn "#claim#" with
    | [spec, name] => some (spec, name)
    | _ => none

/-- The number of leading binders. -/
def binders : Term → Nat
  | .lam b => binders b + 1
  | _ => 0

/-- Read a composition off a compose term whose operands are reduced on the way. -/
def decodeOperands : Nat → Term → Option (Layer × List Layer)
  | 0, _ => none
  | fuel + 1, .specification md (.mix x y) => do
    let (top, below) ← decodeOperands fuel x
    let L ← (Obend.Law.run readFuel y).bind decodeLayer
    pure ({ L with composeMeta := md }, top :: below)
  | _ + 1, t => ((Obend.Law.run readFuel t).bind decodeLayer).map fun L => (L, [])

/-- The program's object as a composition: `fix (compose …) {seed}`, operands reduced. -/
def decodeProgram : Term → Option Composition
  | .fix S (.record seed) => (decodeOperands 64 S).map fun (top, below) => ⟨top, below, seed⟩
  | _ => none

/-- The `fix` at the head of a term that `want` accepts, if one stands there. -/
def headFix (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match (decodeProgram t).filter want with
    | some C => some C
    | none => match t with
      | .app f _ => headFix want fuel f
      | .get x _ => headFix want fuel x
      | .extend x _ => headFix want fuel x
      | .binary _ x _ => headFix want fuel x
      | _ => none

/-- Reduce `t` until a composition `want` accepts stands at its head. -/
def findObject (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match headFix want 64 t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findObject want fuel)

/-- The index of the layer a spec key names. -/
def layerIndex (C : Composition) (key : String) : Option Nat := C.layers.findIdx? (·.name == key)

/-- The object of a claim of spec `key`, reached from the selection `t`. -/
def objectFor (key : String) (t : Term) : Option Composition :=
  findObject (fun C => (layerIndex C key).isSome) 100000 t

/-- A claim of the program at the object. -/
def claimObj (root : Term) (C : Composition) (spec name : String) : Except String ClaimObj := do
  let some code := knotValue root (spec ++ "#claim#" ++ name) | throw s!"{spec}.{name}: no such claim"
  let some j := layerIndex C spec | throw s!"{spec} is not a layer of this object"
  let n := binders code
  unless n ≥ 2 do throw s!"{spec}.{name}: the claim's code is not λself. λsuper. …"
  return ⟨C, j, code, n - 2⟩

/-! ## The rewriter -/

/-- `apps (get X m) args` at the head: the member and the arguments. -/
def headGet : Term → Option (Term × String × List Term)
  | .get X m => some (X, m, [])
  | .app f a => (headGet f).map fun (X, m, args) => (X, m, args ++ [a])
  | _ => none

/-- Merge consecutive `run` steps. -/
def pushRun : List RStep → List RStep
  | .run n :: rest => .run (n + 1) :: rest
  | acc => .run 1 :: acc

/-- **The rewriter.** From the left side: a weak-head step when there is one; else, when `self.m`
stands at the head, late binding through its provider (in the context of the arguments); stop
when the right side is reached. A proposal only: the claim checker decides. -/
def derive (o : ClaimObj) (r : Term) : Nat → Term → List RStep → Option (List RStep)
  | 0, _, _ => none
  | fuel + 1, t, acc =>
    if Obend.Law.termEq t r then some acc.reverse
    else match Obend.Law.step? t with
    | some t' => derive o r fuel t' (pushRun acc)
    | none =>
      match headGet t with
      | some (.bound i, m, args) =>
        if i == o.self then
          match symUnfold o.comp o.self m with
          | some (L, _) =>
            let step : RStep := if args.isEmpty then .lateBinding m L
              else .congr (apps (.bound 0) (args.map (·.rename Nat.succ))) (.get (.bound i) m) [.lateBinding m L]
            match apply (claimResolver o.comp o.self) step t with
            | .ok t' => derive o r fuel t' (step :: acc)
            | .error _ => none
          | none => none
        else none
      | _ => none

/-- Propose a derivation for a claim. -/
def proposeDerivation (o : ClaimObj) : Option (List RStep) :=
  match o.sides with
  | some (_, l, r) => derive o r 4096 l []
  | none => none

end Obend.Logic.Program
end
