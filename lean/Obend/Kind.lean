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
* A `KindPin` is what an instance carries: the kind's IDENTITY (its name, stable across versions)
  and the versions it was resolved at, the kind's own and every ancestor's on its precedence list
  (`KindPin.lineage`). The reference from an instance to its kind is the third instance of
  `Obend.Intention` (`kindRefs`): the candidates are pins, the chooser is the kind's owner (who
  writes its next version), the supports are "the registry names version `v` of `K`" for every kind
  of the lineage (`holds`), and revising the kind or any ancestor leaves every instance that pinned
  the old version stale, naming the kind that moved, until it is renewed (Kimi A, 2026-11-01: a pin
  of the kind's own version alone left a descendant current while its effective law changed).
* `create`: `create --from K` births an instance under `K`: it carries `K`'s pin at the registry and
  starts at `K`'s initial state; a name that is a kind's is refused (`clash`).
* `kindPrecedence`: a kind's C4 precedence list over its parent kinds (`Obend.Spec.C4.linearize`).
  `pinnedPrecedence` is the list a current pin was resolved over (stale otherwise). An instance's
  effective law (`effectiveOf`) is `Obend.Law.effectiveVia` with the instance as head and its kind
  as its one parent: the instance's own law, then every kind on its kind's precedence list, combined
  by conjunction. A stale kind pin is refused by name before anything is judged.
* `dispatch`: a generic's implementation for an instance is the first kind on its pinned precedence
  list that implements it, refused by name when the pin is stale. It reads the instance's kind and
  nothing else: two kinds with the same layout are two kinds.

The theorems are `Obend.Kind.Proofs`: `kind_law_inherited`, `create_carries`,
`effective_refuses_stale`, `kind_stale_iff_blocked`, `ancestor_revised_stale`, `renew_kind`,
`dispatch_by_kind`, `dispatch_sound`, `dispatch_refuses_stale`, `create_refuses_clash`, and the tooth
that two kinds with equal fields are distinguished.
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

/-- One kind at one version: what a pin cites of each kind it rests on. -/
structure KindVersion where
  name : String
  version : Nat
deriving DecidableEq, Repr

/-- **A kind pin.** The kind's stable identity (`name`) and the versions it was resolved at: its own
(`version`) and that of every other kind on its C4 precedence list (`ancestors`, in precedence
order). The identity is what a type or a dispatch compares; the versions are what makes the pin
current. A pin rests on every kind its effective law and its dispatch read, so revising an ancestor
makes the pin stale, naming that ancestor (Kimi A, 2026-11-01). -/
structure KindPin where
  name : String
  version : Nat
  ancestors : List KindVersion := []
deriving DecidableEq, Repr

/-- The pinned versions, the kind's own first: the pin's supports. -/
@[expose] def KindPin.lineage (p : KindPin) : List KindVersion := ⟨p.name, p.version⟩ :: p.ancestors

/-- The registry names version `f.version` of kind `f.name`. -/
@[expose] def holds (ks : Kinds) (f : KindVersion) : Bool :=
  match ks.find f.name with
  | some c => c.version == f.version
  | none => false

inductive Refusal where
  | unknown (kind : String)
  /-- the kind, or a kind its precedence list rests on, was revised since the instance pinned it -/
  | stale (pin : KindPin)
  /-- the kind hierarchy is deeper than the registry: a kind is its own ancestor -/
  | cycle (kind : String)
  | c4 (kind : String) (refusal : Obend.Spec.C4.Refusal)
  | law (refusal : Obend.Law.InheritRefusal)
  /-- an instance named like a kind would shadow the kind's law -/
  | clash (name : String)
  deriving Repr

/-! ## Kind precedence -/

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

/-- The kinds on a precedence list at their registry versions. -/
def versionsOf (ks : Kinds) (l : List String) : List KindVersion :=
  l.filterMap fun x => (ks.find x).map fun c => ⟨x, c.version⟩

/-- Resolve a kind reference: the registry's current version of the kind and of every other kind on
its precedence list. -/
def resolve (ks : Kinds) (k : String) : Except Refusal KindPin :=
  match kindPrecedence ks ks.depth k with
  | .error e => .error e
  | .ok lk =>
    match ks.find k with
    | some c => .ok ⟨k, c.version, versionsOf ks (lk.drop 1)⟩
    | none => .error (.unknown k)

theorem versionsOf_holds (ks : Kinds) (l : List String) : ∀ f ∈ versionsOf ks l, holds ks f = true := by
  intro f hf
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hf
  cases hc : ks.find x with
  | none => simp [hc] at hx
  | some c =>
    simp only [hc, Option.map_some, Option.some.injEq] at hx
    subst hx
    simp [holds, hc]

theorem resolve_ok {ks : Kinds} {k : String} {p : KindPin} (h : resolve ks k = .ok p) :
    ∃ lk c, kindPrecedence ks ks.depth k = .ok lk ∧ ks.find k = some c ∧
      p = ⟨k, c.version, versionsOf ks (lk.drop 1)⟩ := by
  unfold resolve at h
  split at h
  · cases h
  · rename_i lk hlk
    split at h
    · rename_i c hc; cases h; exact ⟨lk, c, hlk, hc, rfl⟩
    · cases h

/-- **The kind reference** (`Obend.Intention`): an instance's kind, resolved at the registry. Its
supports are the pin's lineage: the kind's version and every ancestor's. -/
def kindRefs : Obend.Intention Kinds String KindPin KindVersion Refusal where
  ref := KindPin.name
  supports := KindPin.lineage
  holds := holds
  resolve := resolve
  resolve_ref ks k p h := by obtain ⟨_, _, _, _, rfl⟩ := resolve_ok h; rfl
  resolve_holds ks k p h := by
    obtain ⟨lk, c, _, hc, rfl⟩ := resolve_ok h
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · simp [holds, hc]
    · exact versionsOf_holds ks _ f hf

/-- An instance: its name, its kind's identity, its own law, its state. -/
structure Instance where
  name : String
  kind : KindPin
  law : Term
  state : Data

/-- **`create --from K`**: an instance of `K` named `name` with its own law, carrying `K`'s pin at the
registry and starting at `K`'s initial state. Refused by name when the instance would be named like a
kind (its law would shadow the kind's, and `effectiveOf` would refuse it at once). -/
def create (ks : Kinds) (k name : String) (law : Term) : Except Refusal Instance :=
  if (ks.find name).isSome then .error (.clash name)
  else
    match resolve ks k, ks.find k with
    | .ok p, some c => .ok ⟨name, p, law, c.init⟩
    | .error e, _ => .error e
    | .ok _, none => .error (.unknown k)

/-! ## The effective law -/

/-- Every kind's law by name, then the instance's own. -/
def lawTable (ks : Kinds) (i : Instance) : List (String × Term) :=
  ks.cells.map (fun c => (c.name, c.law)) ++ [(i.name, i.law)]

/-- The graph an instance's law is linearized over: its kind's precedence list. -/
def instanceGraph (k : String) (lk : List String) : Obend.Spec.C4.Graph :=
  ⟨fun x => if x = k then lk else [x], fun _ => false⟩

/-- The precedence list a current pin was resolved over: the registry's, refused as stale unless its
names are the pin's lineage (a kind whose parents moved without a new version is not the kind that
was pinned). -/
@[expose] def pinnedPrecedence (ks : Kinds) (p : KindPin) : Except Refusal (List String) :=
  if !kindRefs.current ks p then .error (.stale p)
  else
    match kindPrecedence ks ks.depth p.name with
    | .error e => .error e
    | .ok lk => if lk == p.lineage.map (·.name) then .ok lk else .error (.stale p)

/-- **An instance's effective law**: refused by name when its kind pin is stale (its kind or any
ancestor revised); otherwise its own law, then every law on its kind's precedence list, by
`Obend.Law.effectiveVia`. -/
@[expose] def effectiveOf (ks : Kinds) (i : Instance) : Except Refusal Term :=
  if !kindRefs.current ks i.kind then .error (.stale i.kind)
  else if (ks.find i.name).isSome then .error (.clash i.name)
  else
    match pinnedPrecedence ks i.kind with
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

/-- **Dispatch by kind**: the implementation of `generic` of the first kind on the instance's pinned
precedence list that has one (`none` when no kind there implements it). A stale pin is refused by
name, as `effectiveOf` refuses it: one accepted pin is one dispatch decision. -/
@[expose] def dispatch {Body : Type} (ks : Kinds) (impls : List (Impl Body)) (generic : String) (i : Instance) :
    Except Refusal (Option Body) :=
  match pinnedPrecedence ks i.kind with
  | .ok lk => .ok (lk.findSome? (implFor impls generic))
  | .error e => .error e

end Obend.Kind

end
