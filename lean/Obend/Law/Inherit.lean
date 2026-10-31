module
/-
# Obend.Law.Inherit — laws with parents, combined by conjunction along a C4 precedence list

The Faré audit's K-LAW-INHERIT (`fareoo/AUDIT.md` §1): a law may name parent laws; the effective
law of a node is every law on its C4 precedence list (`Obend.Spec.C4.linearize`: the node first,
then its ancestors), each applied once, in precedence order, combined by CONJUNCTION. A child may
only add: an effective law never admits what an ancestor refuses (`inherited_never_widens`). The
combination is attenuation, not override; overriding a parent is re-lawing the parent.

`effective lin` is a Core4 term: `λ old. λ new. λ req.` then, for each `(name, law)` of `lin` in
order, `case (law old new req) [ok ↦ the rest, refused r ↦ refused {by = name, reason = r}]`, and
`ok` at the end. So a refusal NAMES the ancestor whose clause refused, and carries that ancestor's
own reason (`effective_refusal_names`). The effective law's verdict is therefore
`inheritedVerdictTy` (`refused` carries `{by, reason}`), not `verdictTy`: an effective law is what
a kernel judges by, never itself a parent (parents are combined by their own laws, along the
linearization).

What it means is a theorem over `Evaluates` (`Obend.Law.Proofs.Inherit`):
`effective_law_eval : Admits (effective lin) o n rq ↔ ∀ p ∈ lin, Admits p.2 o n rq`, for closed
parent laws.
-/
public import Obend.Law.Syntax
public import Obend.Law.Claim
public import Obend.Spec.C4
@[expose] public section
namespace Obend.Law
open Obend.Core.Term (Term Evaluates)
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
set_option autoImplicit false

/-- `sum {ok : {}, refused : {by : label, reason : label}}`. -/
def inheritedVerdictTy : Ty :=
  .variant (.field "ok" unitTy (.field "refused" (.field "by" .label (.field "reason" .label .emptyRow)) .emptyRow))

def inheritedLawTy (S : Ty) : Ty := fnTy S (fnTy S (fnTy reqTy inheritedVerdictTy))

/-- The refusal of ancestor `name`, its reason the arm's payload (`bound 0`). -/
def blameT (name : String) : Term := .inject "refused" (.record [("by", .label name), ("reason", .bound 0)])

/-- The refusal value naming `name` with reason `why`. -/
def blamed (name : String) (why : Term) : Term := .inject "refused" (.record [("by", .label name), ("reason", why)])

/-- Each law of `lin` at cursor `a`, in order; the first refusal reported with its law's name. -/
def chainAt (a : At) : List (String × Term) → Term
  | [] => okT
  | (name, law) :: rest =>
    .case (.app (.app (.app law a.old) a.new) a.req) [("ok", chainAt a.under rest), ("refused", blameT name)]

/-- The effective law of a precedence list of named laws. -/
def effective (lin : List (String × Term)) : Term := law3 (chainAt ⟨0⟩ lin)

/-- The effective law refuses `old → new` under `req`, naming ancestor `name` and its reason. -/
def RefusedBy (law : Term) (old new req : Data) (name : String) (why : Term) : Prop :=
  Evaluates (applyLaw law old new req) (blamed name why)

/-! ## From a C4 linearization -/

inductive InheritRefusal
  /-- the parent graph has no C4 linearization -/
  | c4 (refusal : Obend.Spec.C4.Refusal)
  /-- a name on the precedence list has no law -/
  | unknownLaw (name : String)
  /-- a law with a free index would mean something different in every position -/
  | openLaw (name : String)
  deriving DecidableEq, Repr

/-- Each name's law, closed, in order. -/
def resolve (laws : List (String × Term)) : List String → Except InheritRefusal (List (String × Term))
  | [] => .ok []
  | name :: rest =>
    match laws.lookup name with
    | none => .error (.unknownLaw name)
    | some law =>
      if closedB law then
        match resolve laws rest with
        | .ok ls => .ok ((name, law) :: ls)
        | .error e => .error e
      else .error (.openLaw name)

/-- The C4 precedence list of `head` with local parent chains `parents`. What it is, for every graph,
is proved of `Obend.Spec.C4.linearize` itself (`Obend.Spec.Proofs.C4`): it starts at `head`, names
nothing twice, and keeps every local chain and every parent's own precedence list in order
(`precedence_ok`). -/
def precedence (g : Obend.Spec.C4.Graph) (head : String) (parents : List (List String)) :
    Except InheritRefusal (List String) :=
  match Obend.Spec.C4.linearize g [head] parents with
  | .ok (lin, _) => .ok lin
  | .error e => .error (.c4 e)

/-! ## Trees -/

/-- A single-inheritance hierarchy: each name's parent, if any. -/
structure Tree where
  parent : String → Option String

/-- The chain from `x` toward the root, at most `n` steps up. -/
def Tree.chain (t : Tree) : Nat → String → List String
  | 0, x => [x]
  | n + 1, x => x :: match t.parent x with
    | some p => t.chain n p
    | none => []

/-- The local parent chains of `x` in a tree: its one parent, or none. -/
def Tree.parents (t : Tree) (x : String) : List (List String) :=
  match t.parent x with
  | some p => [[p]]
  | none => []

/-- A tree as a C4 graph: each name's precedence is its chain (to depth `n`); no suffix nodes. -/
def Tree.graph (t : Tree) (n : Nat) : Obend.Spec.C4.Graph := ⟨t.chain n, fun _ => false⟩

/-- The effective law of `head`: its C4 precedence list, each name resolved to its law. -/
def effectiveVia (g : Obend.Spec.C4.Graph) (laws : List (String × Term)) (head : String)
    (parents : List (List String)) : Except InheritRefusal Term :=
  match precedence g head parents with
  | .error e => .error e
  | .ok names =>
    match resolve laws names with
    | .ok ls => .ok (effective ls)
    | .error e => .error e

end Obend.Law
