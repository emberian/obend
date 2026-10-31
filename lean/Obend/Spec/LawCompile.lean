module
/-
# Obend.Spec.LawCompile — the enforced `law` fragment compiled to closed Core4 laws

`Obend.Spec.Law` parses `law NAME: EXPR` and gives it a meaning, `LawExpr.denote`, over the
declared state as data. This module compiles it to what a kernel installs: a closed Core4 term of
type `lawTy S` (`Obend.Law.Syntax`) built from the Law combinators, for the declared state type
`S`. The meaning theorems are `Obend.Spec.Proofs.LawCompile`: on every state that fits `S` at the
fields the law reads (`Fits`), the compiled law ADMITS a write exactly when `denote` holds and
REFUSES it, naming the law, exactly when it does not; and the compiled law checks at `lawTy S`
under `Bidirectional.checkAgainst` with no annotations.

What the fragment reads, and how the compiled term reads it:

* `new.FIELD`: field `FIELD` of the new state at the type `S` gives it. A natural is itself, a
  boolean `1` or `0` (`scalarOf`); a field `S` lacks, or holds at another type, is ABSENT, and
  every comparison with an absent reading is false (`denote`'s rule), statically.
* `request.subject`, `request.caller`: the request's `optNatTy` fields, absent at `none`;
  `request.turn`: its natural field; `ledger.height`: the record's `height`, which `requestAt`
  takes from the ledger's `Consensus`, never from the request (`Obend.Law.reqTy`).
* `monotone(F)` and `writeOnce(F)`: the old state's `F` against the new one's. At a first write
  there is no old state (`denote … none …`): `monotone` is false and `writeOnce` true.
* Integer constants: every reading is a natural (`scalarOf`), so a comparison with a negative
  constant is decided statically (`x == -2`, `x <= -2` false; `x <= y + -2` is `x + 2 <= y`).

The occasions (`lawOf6`, LANG-19/24, KERNEL-70): a `write` and an `invoke` are writes of the state,
judged with the old state; a `birth` is a first write, judged with none; an `adopt` (this law being
added over a state the object already has) is judged as the identity write of that state, old =
new, so a law is never installed over a state it would refuse and `monotone` does not refuse it for
want of a prior state; a `retire` writes no state and is admitted. A refusal's reason is the law's
name.

A `relaw` of a package law is REFUSED, naming the package (`relawRefusal`). A package law is part
of the pinned program a receiver re-executes byte for byte, so the path to change it is a package
upgrade (the carry), not a relaw. Relaw remains the path for object-level laws, and the metarule (a
law must admit its own amendment) is satisfied for package laws by the upgrade path, not by relaw.
-/
public import Obend.Spec.Law
public import Obend.Law.Std
public import Obend.Core.Bidirectional
public section
namespace Obend.Spec.LawCompile
open Obend.Law
open Obend.Spec.Law (LawRef LawExpr Facts)
open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
set_option autoImplicit false

/-! ## How a field reads -/

/-- The scalar kinds a field reads as. -/
inductive Kind where
  | nat
  | bool
  deriving DecidableEq, Repr

/-- How field `f` of the state type `S` reads: a natural, a boolean, or not at all. -/
@[expose] def fieldKind (S : Ty) (f : String) : Option Kind :=
  match Obend.Core.Bidirectional.rowMember S f with
  | some .natural => some .nat
  | some .boolean => some .bool
  | _ => none

/-- A field's term as the natural `scalarOf` reads: a boolean is `1` or `0`. -/
@[expose] def scalarRead : Kind → Term → Term
  | .nat, t => t
  | .bool, t => .ifBool t (natT 1) (natT 0)

/-- A reading: whether it is present (a boolean term) and its value (a natural term, meaningful
only when present). Both sit at the clause's cursor. -/
structure Read where
  present : Term
  value : Term

/-- `t : optNatTy` is `some`. -/
@[expose] def isSomeT (t : Term) : Term := .case t [("none", falseT), ("some", trueT)]
/-- The payload of `t : optNatTy` (`0` at `none`). -/
@[expose] def payloadT (t : Term) : Term := .case t [("none", natT 0), ("some", .bound 0)]

/-- A field read at the type `S` gives it. -/
@[expose] def fieldRead (S : Ty) (f : String) (t : Term) : Read :=
  match fieldKind S f with
  | some k => ⟨trueT, scalarRead k t⟩
  | none => ⟨falseT, natT 0⟩

/-- An optional request fact. -/
@[expose] def optRead (t : Term) : Read := ⟨isSomeT t, payloadT t⟩

/-- What a reference reads at cursor `a`. -/
@[expose] def refRead (S : Ty) (a : At) : LawRef → Read
  | .field f => fieldRead S f (a.newF f)
  | .subject => optRead (a.reqF "subject")
  | .caller => optRead (a.reqF "caller")
  | .height => ⟨trueT, a.reqF "height"⟩
  | .turn => ⟨trueT, a.reqF "turn"⟩

@[expose] def orT (a b : Term) : Term := .ifBool a trueT b
@[expose] def impliesT (a b : Term) : Term := .ifBool a b trueT

/-- Both readings present, and `cmp` of their values. -/
@[expose] def both (x y : Read) (cmp : Term → Term → Term) : Term :=
  andT x.present (andT y.present (cmp x.value y.value))

/-! ## The condition and the law -/

/-- Where an act's old state comes from: none (a first write), the prior state (a write), or the
new state itself (an adoption: the identity write of the state the law is added over). -/
inductive OldSrc where
  | none
  | prior
  | same
  deriving DecidableEq, Repr

/-- The old state's field `f` at cursor `a`. -/
@[expose] def oldRead (src : OldSrc) (a : At) (f : String) : Term :=
  match src with
  | .same => a.newF f
  | _ => a.oldF f

/-- The fragment as a boolean Core4 term at cursor `a`; `src` says where the act's old state comes
from (`monotone`, `writeOnce` read it). -/
@[expose] def cond (S : Ty) (src : OldSrc) (a : At) : LawExpr → Term
  | .eqC r c =>
    if 0 ≤ c then andT (refRead S a r).present (eqNat (refRead S a r).value (natT c.toNat)) else falseT
  | .leC r c =>
    if 0 ≤ c then andT (refRead S a r).present (leNat (refRead S a r).value (natT c.toNat)) else falseT
  | .inC r cs =>
    andT (refRead S a r).present
      (anyOf ((cs.filter (0 ≤ ·)).map fun c => eqNat (refRead S a r).value (natT c.toNat)))
  | .eqR l r => both (refRead S a l) (refRead S a r) eqNat
  | .leR l r => both (refRead S a l) (refRead S a r) leNat
  | .leROff l r k =>
    if 0 ≤ k then both (refRead S a l) (refRead S a r) fun x y => leNat x (addNat y (natT k.toNat))
    else both (refRead S a l) (refRead S a r) fun x y => leNat (addNat x (natT (-k).toNat)) y
  | .monotone f =>
    if src = .none then falseT else
      match fieldKind S f with
      | some k => leNat (scalarRead k (oldRead src a f)) (scalarRead k (a.newF f))
      | none => falseT
  | .writeOnce f =>
    if src = .none then trueT else
      match fieldKind S f with
      | some k => .ifBool (eqNat (scalarRead k (oldRead src a f)) (natT 0)) trueT
          (eqNat (scalarRead k (a.newF f)) (scalarRead k (oldRead src a f)))
      | none => trueT
  | .not e => notT (cond S src a e)
  | .and l r => andT (cond S src a l) (cond S src a r)
  | .or l r => orT (cond S src a l) (cond S src a r)
  | .implies l r => impliesT (cond S src a l) (cond S src a r)

/-- The clause: the condition, else refuse with the law's name. -/
@[expose] def clause (S : Ty) (name : String) (e : LawExpr) (src : OldSrc) (a : At) : Term :=
  guard (cond S src a e) name okT

/-- Why a relaw of a package law is refused: it names the package, whose upgrade is the path. -/
@[expose] def relawRefusal (pkg : String) : String :=
  "package law of " ++ pkg ++ ": changed by a package upgrade, not a relaw"

/-- **The compiled law** `name` of package `pkg` over the state type `S`: a write or an invoke is
judged with the old state, a birth as a first write, an adoption as the identity write; a relaw is
refused naming the package; a retirement is admitted. -/
@[expose] def compile (S : Ty) (pkg name : String) (e : LawExpr) : Term :=
  lawOf6 (clause S name e .none) (clause S name e .same) (fun _ => refusedT (relawRefusal pkg))
    (fun _ => okT) (clause S name e .prior) (clause S name e .prior)

/-- A package's laws, each compiled, by name (the kernel installs every one: an act is admitted
when each admits). -/
@[expose] def compilePackage (S : Ty) (pkg : String) (laws : List (String × LawExpr)) : List (String × Term) :=
  laws.map fun (name, e) => (name, compile S pkg name e)

/-- The old state an act is judged with, as `denote` takes it. -/
@[expose] def oldOf (src : OldSrc) (o n : Data) : Option Data :=
  match src with
  | .none => none
  | .prior => some o
  | .same => some n

/-! ## What the theorems quantify over -/

/-- The request a kernel builds for an act with the fragment's facts. -/
@[expose] def reqOf (agent principal : String) (notBefore validUntil : Nat) (occasion : Data) (facts : Facts) : Data :=
  requestAt agent principal notBefore validUntil occasion facts.subject facts.caller ⟨facts.height⟩ facts.turn

/-- The state's fields fit `S` at field `f`: a natural or boolean field of `S` holds a natural or
boolean (the first field so named), and a field `S` does not read as a scalar holds no scalar. -/
@[expose] def fitsField (S : Ty) (fs : List (String × Data)) (f : String) : Bool :=
  match fieldKind S f, fieldsLookup f fs with
  | some .nat, some (.natural _) => true
  | some .bool, some (.boolean _) => true
  | none, _ => (Obend.Spec.Law.firstScalarField f fs).isNone
  | _, _ => false

/-- A state FITS `S` for the law `e`: a record whose fields fit `S` at every field `e` reads. -/
@[expose] def Fits (S : Ty) (e : LawExpr) : Data → Bool
  | .record fs => e.fields.all (fitsField S fs)
  | _ => false

/-- The verdict a meaning predicts. -/
@[expose] def verdictOf (name : String) : Bool → Term
  | true => okT
  | false => refusedT name

end Obend.Spec.LawCompile

end
