module
/-
# Obend.Law.Claim — a certifying-shape checker for `keeps` claims (nano LANG-83, LANG-92)

`Claim.keeps inv law` names an invariant and a law among a package's named terms. `guardedBy`
checks a restricted law shape: every literal `ok` leaf is dominated by the true branch of
`ifBool (app I (bound k)) _ _` (the invariant applied to the new state), except an arm of a
`case` on `req.occasion` labelled `relaw` (a relaw leaves the state unchanged). An adoption is
not excepted. `Obend.Law.Proofs.Claim.guardedBy_sound` states what the checker means;
`keeps_step` and `chain_keeps` lift it to a law's admitted steps and to a history.

A law that keeps the invariant by a helper-returned verdict, or by an equivalent inline test,
need not have the accepted shape; the checker refuses it (it is sound, not complete).

Term equality: Core4's `Term` derives no `DecidableEq` (it is nested), so the checker compares
the generic encodings (`Obend.Core.TermTraverse.encode`, injective) with a structural `treeEq`.
-/
public import Obend.Law.Syntax
public import Obend.Core.TermTraverse
@[expose] public section
namespace Obend.Law
open Obend.Core.Term (Term Evaluates)
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Tag encode)
open Obend.Core.Data (Data)
set_option autoImplicit false

deriving instance DecidableEq for Obend.Core.TermTraverse.Tag

mutual
def treeEq : Tree Tag → Tree Tag → Bool
  | .var i, .var j => i == j
  | .bind a, .bind b => treeEq a b
  | .node t cs, .node u ds => decide (t = u) && treesEq cs ds
  | _, _ => false
def treesEq : List (Tree Tag) → List (Tree Tag) → Bool
  | [], [] => true
  | a :: as, b :: bs => treeEq a b && treesEq as bs
  | _, _ => false
end

/-- Syntactic equality of Core4 terms, through their encodings. -/
def termEq (a b : Term) : Bool := treeEq (encode a) (encode b)

mutual
/-- Every free index of the shape is below `n`. (`Tree.all` is not reduced by the kernel in a
`module`; this structural walk is.) -/
def scopedB : Nat → Tree Tag → Bool
  | n, .var i => decide (i < n)
  | n, .bind b => scopedB (n + 1) b
  | n, .node _ cs => scopedsB n cs
def scopedsB : Nat → List (Tree Tag) → Bool
  | _, [] => true
  | n, c :: cs => scopedB n c && scopedsB n cs
end

/-- No free de Bruijn index: the term means the same under every substitution. -/
def closedB (t : Term) : Bool := scopedB 0 (encode t)

/-- `c` is the invariant `I` applied to the value at index `k`. -/
def isGuardCond (I : Term) (k : Nat) : Term → Bool
  | .app f (.bound j) => j == k && termEq f I
  | _ => false

/-- `s` reads the occasion of the request at index `r`. -/
def isOccasion (r : Nat) : Term → Bool
  | .get (.bound j) name => j == r && name == "occasion"
  | _ => false

mutual
/-- Every `ok` leaf of `t` is dominated by the true branch of `ifBool (app I (bound k)) _ _`, or sits
in the `relaw` arm of a `case` on the occasion of the request at `r`; `k` is the index of `new` and
`r` of `req` at the current depth (`1` and `0` under a law's three binders). Only a literal
`inject` leaf may be an `ok`; every other former is refused, so the walk is sound by construction. -/
def guardedBy (I : Term) : (k r : Nat) → Term → Bool
  | k, r, .ifBool c a b => (isGuardCond I k c || guardedBy I k r a) && guardedBy I k r b
  | k, r, .case s arms => guardedArms I (k + 1) (r + 1) (isOccasion r s) arms
  | _, _, .inject l _ => l != "ok"
  | _, _, _ => false

/-- Each arm's body is guarded, or (`occ`: the case is on the occasion) the arm is `relaw`. -/
def guardedArms (I : Term) (k r : Nat) (occ : Bool) : List (String × Term) → Bool
  | [] => true
  | (l, body) :: arms => ((occ && l == "relaw") || guardedBy I k r body) && guardedArms I k r occ arms
end

/-- A claim a package makes of itself. -/
inductive Claim
  /-- every state an object holds satisfies the named invariant (a closed `S → boolean`): the named
  law refuses every birth, adoption, retirement, write and invoke whose new state fails it -/
  | keeps (inv law : String)
  deriving DecidableEq, Repr

/-- The certifying-shape check of a claim against a package's named terms: the invariant is
closed, the law is `λ λ λ b`, and `b` is in certifying shape. -/
def checkClaim (fields : List (String × Term)) : Claim → Bool
  | .keeps inv law =>
    match fields.lookup inv, fields.lookup law with
    | some I, some (.lam (.lam (.lam b))) => closedB I && guardedBy I 1 0 b
    | _, _ => false

/-- The invariant holds of `n`. -/
def Keeps (I : Term) (n : Data) : Prop := Evaluates (.app I n.term) (.boolean true)

/-- One step a law admits: from `o`, under `rq`, to `n`; a relaw leaves the state unchanged. -/
def LawStep (law : Term) (o rq n : Data) : Prop :=
  Admits law o n rq ∧ ∀ x, rq.field "occasion" = some (.variant "relaw" x) → n = o

/-- A history from `o`: each `(request, new state)` a step from the state before it. -/
inductive Chain (R : Data → Data → Data → Prop) : Data → List (Data × Data) → Prop
  | nil (o : Data) : Chain R o []
  | cons {o rq n : Data} {rest : List (Data × Data)} : R o rq n → Chain R n rest → Chain R o ((rq, n) :: rest)

end Obend.Law
