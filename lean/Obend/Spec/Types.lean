module
/-
# Obend.Spec.Types — proposal types: the elaborator's `PTy`

The types the elaborator computes and proposes to the checker: the `Ty` JSON wire of
`Obend.Core.Packet.typeJson` plus `variant`, with canonical rows (`PTy.canonical`), the
equality the elaborator decides by (`sameTy`), the callable view of a specification (`callable`),
row lookup and overlay, substitution of type variables (`PTy.subst`) and the type of one
`compose` step (`composeTy`). Split out of minidregg `Compiler/ObjectiveBendElaborate.lean`
(commit 092027a2) so `Obend.Spec.Proofs.SpecificationClosure`'s `composeTy_closed` imports the
type computation, not the elaborator.
-/
public import Lean
@[expose] public section
namespace Obend.Spec.Types
open Lean (Json toJson)
set_option autoImplicit false

inductive PTy where
  | natural | boolean | label | emptyRow
  | variable (index : Nat)
  | arrow (reuse parameter : String) (domain codomain : PTy)
  | field (name : String) (member tail : PTy)
  | specification (metadata extension : PTy)
  | variant (row : PTy)
  | computation (plan response result : PTy)
  deriving Inhabited, Repr, BEq

def PTy.row : List (String × PTy) → PTy
  | [] => .emptyRow
  | (n, t) :: rest => .field n t (PTy.row rest)

def arrowTy (d c : PTy) (parameter := "unrestricted") (reuse := "reusable") : PTy := .arrow reuse parameter d c
def extensionTy (t : PTy) : PTy := arrowTy t (arrowTy t t)

def PTy.insertCanonical : PTy → String → PTy → PTy
  | .field prior old tail, name, member =>
    if name == prior then .field name member tail
    else if name < prior then .field name member (.field prior old tail)
    else .field prior old (tail.insertCanonical name member)
  | tail, name, member => .field name member tail

def PTy.canonical : PTy → PTy
  | .arrow r q d c => .arrow r q d.canonical c.canonical
  | .specification m e => .specification m.canonical e.canonical
  | .variant r => .variant r.canonical
  | .computation p r a => .computation p.canonical r.canonical a.canonical
  | .field n m t => t.canonical.insertCanonical n m.canonical
  | other => other

def sameTy : Option PTy → Option PTy → Bool
  | some a, some b => a.canonical == b.canonical
  | _, _ => false

def callable : Option PTy → Option PTy
  | some (.specification _ e) => callable (some e)
  | t => t

def lookupRow : Option PTy → String → Option PTy
  | some (.field n m t), name => if n == name then some m else lookupRow (some t) name
  | _, _ => none

def PTy.json : PTy → Json
  | .natural => Json.mkObj [("tag", "natural")]
  | .boolean => Json.mkObj [("tag", "boolean")]
  | .label => Json.mkObj [("tag", "label")]
  | .emptyRow => Json.mkObj [("tag", "emptyRow")]
  | .variable i => Json.mkObj [("tag", "variable"), ("index", toString i)]
  | .arrow r q d c => Json.mkObj [("tag", "arrow"), ("reuse", r), ("parameter", q), ("domain", d.json), ("codomain", c.json)]
  | .field n m t => Json.mkObj [("tag", "field"), ("name", n), ("member", m.json), ("tail", t.json)]
  | .specification m e => Json.mkObj [("tag", "specification"), ("metadata", m.json), ("extension", e.json)]
  | .variant r => Json.mkObj [("tag", "variant"), ("row", r.json)]
  | .computation p r a => Json.mkObj [("tag", "computation"), ("plan", p.json), ("response", r.json), ("result", a.json)]

def isComputation : Option PTy → Bool
  | some (.computation ..) => true
  | _ => false

/-- `overlay provided inherited`: the provided fields first, then the inherited row
(the first field of a name wins, as Core4 `overlay` after `extend`). -/
def PTy.overlay : PTy → PTy → PTy
  | .field n t rest, inherited => .field n t (rest.overlay inherited)
  | _, inherited => inherited

def isRowTy : PTy → Bool
  | .field .. | .emptyRow => true
  | _ => false

def rowNames : PTy → List String
  | .field n _ t => n :: rowNames t
  | _ => []

def rowFields : PTy → List (String × PTy)
  | .field n t rest => (n, t) :: rowFields rest
  | _ => []

/-- Substitute type variables (`σ i = some t` replaces variable `i`). -/
def PTy.subst (σ : Nat → Option PTy) : PTy → PTy
  | .variable i => (σ i).getD (.variable i)
  | .arrow r q d c => .arrow r q (d.subst σ) (c.subst σ)
  | .field n m t => .field n (m.subst σ) (t.subst σ)
  | .specification m e => .specification (m.subst σ) (e.subst σ)
  | .variant r => .variant (r.subst σ)
  | .computation p r a => .computation (p.subst σ) (r.subst σ) (a.subst σ)
  | other => other

/-- The type of `compose(left, right)`: a specification whose metadata is `metaTy` (the
one SpecMeta type, whatever the operands' metadata) and whose extension runs `right`
over `left` under one final self. It depends on the operands only through their
callable extension types, so composing two `Specification<T>`/`Extension<T>` values
gives `Specification<T>` (`composeTy_closed`). -/
def composeTy (metaTy : PTy) (left right : Option PTy) : Option PTy :=
  match callable left, callable right with
  | some (.arrow _ _ ld (.arrow _ _ li _)), some (.arrow _ _ _ (.arrow _ _ _ rp)) =>
    some (.specification metaTy (arrowTy ld (arrowTy li rp)))
  | _, _ => none

end Obend.Spec.Types

end
