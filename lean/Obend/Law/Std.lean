module
/-
# Obend.Law.Std — the law library: generators of closed Core4 terms (nano LANG-20)

A stdlib law is a Lean function that EMITS a closed Core4 term of type `lawTy S`. Nothing here runs
at admission: a kernel applies the emitted term like any other law (`applyLaw`). What each law
MEANS is a theorem in `Obend.Law.Proofs.Std`, proved over the reference semantics (`Evaluates`),
never by evaluating the term.

Every law is `lawOf S birth adopt relaw retire change` (or `lawOf6` with separate write and invoke
clauses), so every law states what it does at a birth, an adoption, a relaw and a retirement:
there is no default arm (LANG-19, LANG-24, KERNEL-70).

Ported from nanodregg `Lang/Std.lean` (origin/main `2dcc9ea`). What changed with the target:
Core4 has no bytes and no digests, so member and agent ids are `label`s compared by `labelEqual`,
and the incoming laws of an `adopt`/`relaw` are one `label`; Core4's conditional is `ifBool`;
equality is typed (`equal` on naturals, `labelEqual` on labels, `eqAt` picks by the guarded field's
type). There are no packages here, so nano's `pkgOf`, `methodOf`, `stepTo` are not ported, and a
machine's method index is the method's place in the list the author passes.
-/
public import Obend.Law.Syntax
public section
namespace Obend.Law
open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty)
set_option autoImplicit false

/-- Why a generator refuses its parameters: a law it emitted would mean something other than its
name says, or nothing at all. -/
inductive StdRefusal
  /-- a quorum member listed twice would hold two votes -/
  | duplicateMember
  /-- a quorum threshold outside `1 ≤ k ≤ members` (k = 0 commits unapproved) -/
  | badThreshold
  /-- more members than `membersMax` (one mask bit each, below `2^64`) -/
  | tooManyMembers
  /-- an allowlist of more than `idsMax` ids -/
  | tooManyIds
  /-- a machine of more than `edgesMax` edges -/
  | tooManyEdges
  /-- an epoch of width 0 (every act would fault) -/
  | zeroWidth
  | duplicateState
  | unknownState (state : String)
  | unknownMethod (method : String)
  deriving DecidableEq, Repr

@[expose] def need (c : Bool) (e : StdRefusal) : Except StdRefusal Unit := if c then .ok () else .error e

/-! ## Authority narrowing

Authority is the kernel's: every admitted act has as its `principal` the object's owner, reached
directly or through a grant chain. A law only NARROWS that authority. -/

/-- The signer is the principal, so no delegate acts through a grant. -/
@[expose] def ownerSigns (S : Ty) : Term :=
  let c (a : At) := allOf [(eqLabel (a.reqF "agent") (a.reqF "principal"), "not signed by the owner")]
  lawOf S c c c c c

/-- `agent` is one of `ids`. -/
@[expose] def listedT (ids : List String) (a : At) : Term :=
  anyOf (ids.map fun i => eqLabel (a.reqF "agent") (.label i))

/-- Only the listed members (`agent`, the signer) may create, adopt, re-law, retire or change the
object. `allowlistLaw` is the unchecked term (what the theorems are about). -/
@[expose] def allowlistLaw (S : Ty) (ids : List String) : Term :=
  let c (a : At) := allOf [(listedT ids a, "not on the allowlist")]
  lawOf S c c c c c

/-- The most ids an allowlist names. -/
@[expose] def idsMax : Nat := 256

@[expose] def allowlist (S : Ty) (ids : List String) : Except StdRefusal Term := do
  need (ids.length ≤ idsMax) .tooManyIds
  pure (allowlistLaw S ids)

/-! ## Bounds -/

/-- Natural field `f` is at most `maxT` (a term at the clause's depth) in every state the object
reaches, its seed included. A relaw and a retirement are admitted: neither changes the state. -/
@[expose] def boundedWith (S : Ty) (f : String) (maxT : Term) : Term :=
  let c (a : At) := allOf [(leNat (a.newF f) maxT, f ++ " over the bound")]
  lawOf S c c (fun _ => okT) (fun _ => okT) c

@[expose] def bounded (S : Ty) (f : String) (max : Nat) : Term := boundedWith S f (natT max)

/-! ## Equality at the guarded field's type -/

/-- Equality at the guarded field's type: `labelEqual` at `label`, an `ifBool` at `boolean`; at a
record type (a row) field by field, each at its own type, in row order; `equal` otherwise (a field
of a sum, arrow or other type faults the comparison). A record is compared only at the fields its
type names, so `true` means equal data when the data fits the type
(`Obend.Law.Proofs.Std.eqAt_data`). -/
@[expose] def eqAt (T : Ty) (x y : Term) : Term :=
  match T with
  | .label => eqLabel x y
  | .boolean => .ifBool x y (notT y)
  | .field f M tail => andT (eqAt M (.get x f) (.get y f)) (eqAt tail x y)
  | .emptyRow => trueT
  | _ => eqNat x y

/-! ## Quorum: k of n members approve one proposal, which is then the only change admitted

State fields (besides the author's): `approvals : nat`, a bitmask over `members` (bit i: member i
approved the CURRENT proposal); `proposal : proposalTy T`, either `set v` (field `guarded` becomes
`v`) or `laws L` (the object's laws are replaced by exactly `L`). A change is exactly one of:
commit (`guarded` changes, only to the proposed `v`, with ≥ k approvals, approvals reset);
propose (`guarded` unchanged, `proposal` changes, approvals reset); approve (only `approvals`
changes, by the SIGNER's own unset bit); no-op. Every change and relaw is by a member. A birth and
an ADOPTION have no approvals (approvals written under earlier laws prove nothing, LANG-24). A
retirement is refused `quorum`. -/

@[expose] def membersMax : Nat := 63

@[expose] def proposalTy (T : Ty) : Ty := .variant (.field "laws" .label (.field "set" T .emptyRow))

@[expose] def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

/-- Bit `i` of a mask, as `0` or `1`. -/
@[expose] def bit (t : Term) (i : Nat) : Term := modNat (divNat t (natT (pow2 i))) (natT 2)

/-- The number of set bits among the first `cnt`. -/
@[expose] def popcount (t : Term) (cnt : Nat) : Term :=
  (List.range cnt).foldl (fun acc i => addNat acc (bit t i)) (natT 0)

/-- What `popcount` computes, in Lean. -/
@[expose] def popcountNat (a cnt : Nat) : Nat :=
  (List.range cnt).foldl (fun acc i => acc + a / pow2 i % 2) 0

@[expose] def isMember (members : List String) (a : At) : Term := listedT members a

/-- `p` and `q` (proposals, as clauses) are the same proposal. Inside the inner arm `bound 0` is
`q`'s payload and `bound 1` is `p`'s. -/
@[expose] def sameProposal (T : Ty) (a : At) (p q : At → Term) : Term :=
  .case (p a)
    [("laws", .case (q a.under) [("laws", eqLabel (.bound 0) (.bound 1)), ("set", falseT)]),
     ("set", .case (q a.under) [("laws", falseT), ("set", eqAt T (.bound 0) (.bound 1))])]

/-- The old proposal is `set v` with `v` the new value of `guarded`. -/
@[expose] def proposedSet (T : Ty) (guarded : String) (a : At) : Term :=
  .case (a.oldF "proposal") [("laws", falseT), ("set", eqAt T (.bound 0) (a.under.newF guarded))]

/-- The old proposal is `laws L` with `L` the incoming laws (a relaw clause only). -/
@[expose] def proposedLaws (a : At) : Term :=
  .case (a.oldF "proposal") [("laws", eqLabel (.bound 0) a.under.payload), ("set", falseT)]

/-- An approval: member `m` (the signer) sets its own bit `i`, which was unset. -/
@[expose] def approvalBy (a : At) (m : String) (i : Nat) : Term :=
  andT (eqNat (bit (a.oldF "approvals") i) (natT 0))
    (andT (eqNat (a.newF "approvals") (addNat (a.oldF "approvals") (natT (pow2 i))))
      (eqLabel (a.reqF "agent") (.label m)))

@[expose] def quorumLaw (S T : Ty) (members : List String) (k : Nat) (guarded : String) : Term :=
  let cnt := members.length
  let quorate (a : At) := leNat (natT k) (popcount (a.oldF "approvals") cnt)
  let reset (a : At) := eqNat (a.newF "approvals") (natT 0)
  let change (a : At) : Term :=
    guards [(isMember members a, "not a member"),
            (ltNat (a.newF "approvals") (natT (pow2 cnt)), "approvals out of range")]
      (.ifBool (notT (eqAt T (a.newF guarded) (a.oldF guarded)))
        (allOf [(quorate a, "no quorum"), (proposedSet T guarded a, "not the proposal"),
                (reset a, "approvals not reset")])
        (.ifBool (notT (sameProposal T a (fun b => b.newF "proposal") (fun b => b.oldF "proposal")))
          (allOf [(reset a, "approvals not reset")])
          (.ifBool (eqNat (a.newF "approvals") (a.oldF "approvals")) okT
            (guard (anyOf (members.zipIdx.map fun (m, i) => approvalBy a m i)) "not an approval" okT))))
  let relawC (a : At) := guards [(isMember members a, "not a member")]
    (allOf [(quorate a, "no quorum"), (proposedLaws a, "not the proposal")])
  let fresh (a : At) := allOf [(reset a, "approvals at birth")]
  lawOf S fresh fresh relawC (fun _ => refusedT "quorum") change

@[expose] def quorum (S T : Ty) (members : List String) (k : Nat) (guarded : String) : Except StdRefusal Term := do
  need (members.length ≤ membersMax) .tooManyMembers
  need (decide members.Nodup) .duplicateMember
  need (1 ≤ k && k ≤ members.length) .badThreshold
  pure (quorumLaw S T members k guarded)

/-! ## Rate: at most `limit` changes of `guarded` per epoch of `W` heights

State fields: `count : nat`, `epoch : nat`. The call's signed window (`notBefore`, `validUntil`)
must lie inside one epoch, `notBefore / W`, and the state's epoch is that one; within it `count`
rises by one for each change of `guarded`, up to `limit`; a later epoch restarts it. A relaw and a
retirement are admitted: neither changes the state. -/

@[expose] def inOneEpoch (W : Nat) (a : At) : List (Term × String) :=
  [(eqNat (divNat (a.reqF "validUntil") (natT W)) (divNat (a.reqF "notBefore") (natT W)),
      "window spans epochs"),
   (eqNat (a.newF "epoch") (divNat (a.reqF "notBefore") (natT W)), "epoch is not the call's window")]

@[expose] def windowedLaw (S T : Ty) (W limit : Nat) (guarded : String) : Term :=
  let inc (a : At) := Term.ifBool (eqAt T (a.newF guarded) (a.oldF guarded)) (natT 0) (natT 1)
  let fresh (a : At) := guards (inOneEpoch W a) (allOf [(eqNat (a.newF "count") (natT 0), "count at birth")])
  lawOf S fresh fresh
    (fun _ => okT) (fun _ => okT)
    (fun a => guards (inOneEpoch W a)
      (.ifBool (eqNat (a.newF "epoch") (a.oldF "epoch"))
        (allOf [(eqNat (a.newF "count") (addNat (a.oldF "count") (inc a)), "count not bumped"),
                (leNat (a.newF "count") (natT limit), "over the rate limit")])
        (allOf [(ltNat (a.oldF "epoch") (a.newF "epoch"), "epoch went back"),
                (eqNat (a.newF "count") (inc a), "count not reset"),
                (leNat (a.newF "count") (natT limit), "over the rate limit")])))

@[expose] def windowed (S T : Ty) (W limit : Nat) (guarded : String) : Except StdRefusal Term := do
  need (0 < W) .zeroWidth
  pure (windowedLaw S T W limit guarded)

/-! ## Machines: a finite-state field moved only by methods along named edges

Field `f` is a sum of empty records over `states`. A birth and an adoption start at `initial`; an
invoke of method `m` moves `f` from `x` to `y` only along an edge `(x, m, y)`; a write, a relaw
and a retirement are refused (a machine changes only by its methods, so a machine object is
permanent). -/

@[expose] def stateTy (states : List String) : Ty :=
  .variant (states.foldr (fun s row => .field s .emptyRow row) .emptyRow)

/-- `t` (a term of `stateTy states`) is the state `s`. -/
@[expose] def isState (states : List String) (t : Term) (s : String) : Term :=
  .case t (states.map fun x => (x, .boolean (decide (x = s))))

@[expose] def machineLaw (S : Ty) (f : String) (states : List String) (initial : String)
    (edges : List (String × Nat × String)) : Term :=
  let frozen (_ : At) := refusedT "a machine changes only by its methods"
  let start (a : At) := allOf [(isState states (a.newF f) initial, f ++ " does not start at " ++ initial)]
  lawOf6 start start frozen frozen frozen
    (fun a => allOf [(anyOf (edges.map fun (x, m, y) =>
      andT (eqNat a.payload (natT m))
        (andT (isState states (a.oldF f) x) (isState states (a.newF f) y))), "no edge")])

/-- A method's index: its place in `methods`. -/
@[expose] def methodIndex (methods : List String) (m : String) : Option Nat := methods.idxOf? m

@[expose] def resolveEdges (states methods : List String) (edges : List (String × String × String)) :
    Except StdRefusal (List (String × Nat × String)) :=
  edges.mapM fun (x, m, y) => do
    need (states.contains x) (.unknownState x)
    need (states.contains y) (.unknownState y)
    match methodIndex methods m with
    | some i => pure (x, i, y)
    | none => throw (.unknownMethod m)

@[expose] def edgesMax : Nat := 256

@[expose] def machine (S : Ty) (f : String) (states : List String) (initial : String) (methods : List String)
    (edges : List (String × String × String)) : Except StdRefusal Term := do
  need (decide states.Nodup) .duplicateState
  need (edges.length ≤ edgesMax) .tooManyEdges
  need (states.contains initial) (.unknownState initial)
  pure (machineLaw S f states initial (← resolveEdges states methods edges))

/-! ## Invariants kept: the certifying shape of a `keeps` claim (nano LANG-83/92, `Obend.Law.Claim`) -/

/-- `keeps S inv`: every birth, adoption, retirement, write and invoke is refused `invariant` unless
`inv new` (`inv` a closed `S → boolean`); a relaw admits (the state is unchanged). A retirement
judges `inv` over the last state: it is the guarded clause rather than `ok` so the law stays in
certifying shape (`Obend.Law.Proofs.Claim.keeps_guarded`). -/
@[expose] def keeps (S : Ty) (inv : Term) : Term :=
  let c (a : At) := guard (.app inv a.new) "invariant" okT
  lawOf S c c (fun _ => okT) c c

end Obend.Law
