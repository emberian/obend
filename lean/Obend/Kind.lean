module
/-
# Obend.Kind — the kind cell: kinds are nominal

Decided 2026-10-31 (`lean/docs/REPORT-EXTENDS-20261031.md`, DESIGN §5): a kind is a CELL with its own
law, every instance carries its kind's identity, the kind's law is an ancestor of each instance's
law, and dispatch is by kind (the Faré audit's K-KIND-CELL, `fareoo/AUDIT.md` §5).

* A `KindCell` is a kind at a version: its name, its version (the pin), the layout its instances
  have (field names: the name map), the initial state of an instance, its own law, and its parent
  kinds (a kind may inherit from kinds: a prototype for a prototype). `Kinds` is the cells a world
  holds, the current version of each.
* A `KindPin` is a kind's IDENTITY, what an instance carries: the kind's name and the version it was
  resolved at. The reference from an instance to its kind is the third instance of
  `Obend.Intention` (`kindRefs`): the candidates are pins, the chooser is the kind's owner (who
  writes its next version), the support is "the registry names version `v` of `K`" (`holds`), and a
  revised kind leaves every instance that pinned the old version stale by name until it is renewed.
* `create`: `create --from K` births an instance under `K`: it carries `K`'s identity at the world
  and starts at `K`'s initial state.
* `kindPrecedence`: a kind's C4 precedence list over its parent kinds (`Obend.Spec.C4.linearize`).
  An instance's effective law (`effectiveOf`) is `Obend.Law.effectiveVia` with the instance as head
  and its kind as its one parent: the instance's own law, then every kind on its kind's precedence
  list, combined by conjunction. A stale kind pin is refused by name before anything is judged.
* `dispatch`: a generic's implementation for an instance is the first kind on its kind's precedence
  list that implements it. It reads the instance's kind and nothing else: two kinds with the same
  layout are two kinds.

The theorems are `Obend.Kind.Proofs`: `kind_law_inherited`, `create_carries`,
`effective_refuses_stale`, `kind_stale_iff_blocked`, `renew_kind`, `dispatch_by_kind`,
`dispatch_sound`, and the tooth that two kinds with equal fields are distinguished.
-/
public import Obend.Intention
public import Obend.Law.Inherit
public section

namespace Obend.Kind

set_option autoImplicit false

open Obend.Core.Term (Term)
open Obend.Core.Data (Data)

/-- A kind at a version. -/
structure KindCell where
  name : String
  version : Nat
  /-- the field names its instances have -/
  layout : List String
  /-- an instance's state at birth -/
  init : Data
  /-- the kind's own law (closed) -/
  law : Term
  /-- the kinds it inherits from, a local chain -/
  parents : List String

/-- The kind cells a world holds, the current version of each. -/
structure Kinds where
  cells : List KindCell

def Kinds.find (ks : Kinds) (k : String) : Option KindCell := ks.cells.find? (·.name == k)

/-- A kind's identity: its name, and the version it was resolved at. -/
structure KindPin where
  name : String
  version : Nat
deriving DecidableEq, Repr

/-- The registry names version `p.version` of kind `p.name`. -/
@[expose] def holds (ks : Kinds) (p : KindPin) : Bool :=
  match ks.find p.name with
  | some c => c.version == p.version
  | none => false

inductive Refusal where
  | unknown (kind : String)
  /-- the kind was revised since the instance pinned it -/
  | stale (pin : KindPin)
  /-- the kind hierarchy is deeper than the registry: a kind is its own ancestor -/
  | cycle (kind : String)
  | c4 (kind : String) (refusal : Obend.Spec.C4.Refusal)
  | law (refusal : Obend.Law.InheritRefusal)
  /-- an instance named like a kind would shadow the kind's law -/
  | clash (name : String)
  deriving Repr

/-- Resolve a kind reference: the registry's current version of the kind. -/
def resolve (ks : Kinds) (k : String) : Except Refusal KindPin :=
  match ks.find k with
  | some c => .ok ⟨k, c.version⟩
  | none => .error (.unknown k)

theorem resolve_ok {ks : Kinds} {k : String} {p : KindPin} (h : resolve ks k = .ok p) :
    ∃ c, ks.find k = some c ∧ p = ⟨k, c.version⟩ := by
  unfold resolve at h
  split at h
  · rename_i c hc; cases h; exact ⟨c, hc, rfl⟩
  · cases h

/-- **The kind reference** (`Obend.Intention`): an instance's kind, resolved at the registry. -/
def kindRefs : Obend.Intention Kinds String KindPin KindPin Refusal where
  ref := KindPin.name
  supports p := [p]
  holds := holds
  resolve := resolve
  resolve_ref ks k p h := by obtain ⟨c, _, rfl⟩ := resolve_ok h; rfl
  resolve_holds ks k p h := by
    obtain ⟨c, hc, rfl⟩ := resolve_ok h
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    simp [holds, hc]

/-- An instance: its name, its kind's identity, its own law, its state. -/
structure Instance where
  name : String
  kind : KindPin
  law : Term
  state : Data

/-- **`create --from K`**: an instance of `K` named `name` with its own law, carrying `K`'s identity at
the registry and starting at `K`'s initial state. -/
def create (ks : Kinds) (k name : String) (law : Term) : Except Refusal Instance :=
  match ks.find k with
  | some c => .ok ⟨name, ⟨k, c.version⟩, law, c.init⟩
  | none => .error (.unknown k)

/-! ## Kind precedence and the effective law -/

/-- Kind `k`'s C4 precedence list over its parent kinds, `n` bounding the depth of the hierarchy. -/
def kindPrecedence (ks : Kinds) : Nat → String → Except Refusal (List String)
  | 0, k => .error (.cycle k)
  | n + 1, k =>
    match ks.find k with
    | none => .error (.unknown k)
    | some c =>
      match c.parents.mapM (kindPrecedence ks n) with
      | .error e => .error e
      | .ok lists =>
        match Obend.Spec.C4.linearize ⟨fun p => ((c.parents.zip lists).lookup p).getD [p], fun _ => false⟩
            [k] [c.parents] with
        | .ok (l, _) => .ok l
        | .error e => .error (.c4 k e)

/-- The depth bound: no acyclic hierarchy is deeper than the registry. -/
def Kinds.depth (ks : Kinds) : Nat := ks.cells.length + 1

/-- Every kind's law by name, then the instance's own. -/
def lawTable (ks : Kinds) (i : Instance) : List (String × Term) :=
  ks.cells.map (fun c => (c.name, c.law)) ++ [(i.name, i.law)]

/-- The graph an instance's law is linearized over: its kind's precedence list. -/
def instanceGraph (k : String) (lk : List String) : Obend.Spec.C4.Graph :=
  ⟨fun x => if x = k then lk else [x], fun _ => false⟩

/-- **An instance's effective law**: refused by name when its kind pin is stale; otherwise its own
law, then every law on its kind's precedence list, by `Obend.Law.effectiveVia`. -/
@[expose] def effectiveOf (ks : Kinds) (i : Instance) : Except Refusal Term :=
  if !kindRefs.current ks i.kind then .error (.stale i.kind)
  else if (ks.find i.name).isSome then .error (.clash i.name)
  else
    match kindPrecedence ks ks.depth i.kind.name with
    | .error e => .error e
    | .ok lk =>
      match Obend.Law.effectiveVia (instanceGraph i.kind.name lk) (lawTable ks i) i.name [[i.kind.name]] with
      | .ok t => .ok t
      | .error e => .error (.law e)

/-- Renew an instance's kind: resolve its kind again at the registry (`Obend.Intention.renew`). -/
def renewKind (ks : Kinds) (i : Instance) : Except Refusal Instance :=
  match kindRefs.renew ks i.kind with
  | .ok p => .ok { i with kind := p }
  | .error e => .error e

/-! ## Dispatch by kind -/

/-- A method of a generic implemented for a kind. -/
structure Impl (Body : Type) where
  generic : String
  kind : String
  body : Body

/-- The implementation of `generic` for kind `k`, if any. -/
def implFor {Body : Type} (impls : List (Impl Body)) (generic k : String) : Option Body :=
  (impls.find? fun m => m.generic == generic && m.kind == k).map (·.body)

/-- **Dispatch by kind**: the implementation of `generic` of the first kind on the instance's kind's
precedence list that has one (`none` when no kind there implements it). -/
@[expose] def dispatch {Body : Type} (ks : Kinds) (impls : List (Impl Body)) (generic : String) (i : Instance) :
    Except Refusal (Option Body) :=
  match kindPrecedence ks ks.depth i.kind.name with
  | .ok lk => .ok (lk.findSome? (implFor impls generic))
  | .error e => .error e

end Obend.Kind

end
