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
  `request.height`, `request.turn`: its natural fields (`Obend.Law.reqTy`).
* `monotone(F)` and `writeOnce(F)`: the old state's `F` against the new one's. At a first write
  there is no old state (`denote … none …`): `monotone` is false and `writeOnce` true.
* Integer constants: every reading is a natural (`scalarOf`), so a comparison with a negative
  constant is decided statically (`x == -2`, `x <= -2` false; `x <= y + -2` is `x + 2 <= y`).

The occasions (`lawOf6`, LANG-19/24, KERNEL-70): a `write` and an `invoke` are writes of the state,
judged with the old state; a `birth` is a first write, judged with none; an `adopt` (this law being
added over a state the object already has) is judged as a first write of that state, so a law is
never installed over a state it would refuse; a `relaw` and a `retire` write no state and are
admitted. A refusal's reason is the law's name.
-/
public import Obend.Spec.Law
public import Obend.Law.Std
public import Obend.Core.Bidirectional
@[expose] public section
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
def fieldKind (S : Ty) (f : String) : Option Kind :=
  match Obend.Core.Bidirectional.rowMember S f with
  | some .natural => some .nat
  | some .boolean => some .bool
  | _ => none

/-- A field's term as the natural `scalarOf` reads: a boolean is `1` or `0`. -/
def scalarRead : Kind → Term → Term
  | .nat, t => t
  | .bool, t => .ifBool t (natT 1) (natT 0)

/-- A reading: whether it is present (a boolean term) and its value (a natural term, meaningful
only when present). Both sit at the clause's cursor. -/
structure Read where
  present : Term
  value : Term

/-- `t : optNatTy` is `some`. -/
def isSomeT (t : Term) : Term := .case t [("none", falseT), ("some", trueT)]
/-- The payload of `t : optNatTy` (`0` at `none`). -/
def payloadT (t : Term) : Term := .case t [("none", natT 0), ("some", .bound 0)]

/-- A field read at the type `S` gives it. -/
def fieldRead (S : Ty) (f : String) (t : Term) : Read :=
  match fieldKind S f with
  | some k => ⟨trueT, scalarRead k t⟩
  | none => ⟨falseT, natT 0⟩

/-- An optional request fact. -/
def optRead (t : Term) : Read := ⟨isSomeT t, payloadT t⟩

/-- What a reference reads at cursor `a`. -/
def refRead (S : Ty) (a : At) : LawRef → Read
  | .field f => fieldRead S f (a.newF f)
  | .subject => optRead (a.reqF "subject")
  | .caller => optRead (a.reqF "caller")
  | .height => ⟨trueT, a.reqF "height"⟩
  | .turn => ⟨trueT, a.reqF "turn"⟩

def orT (a b : Term) : Term := .ifBool a trueT b
def impliesT (a b : Term) : Term := .ifBool a b trueT

/-- Both readings present, and `cmp` of their values. -/
def both (x y : Read) (cmp : Term → Term → Term) : Term :=
  andT x.present (andT y.present (cmp x.value y.value))

/-! ## The condition and the law -/

/-- The fragment as a boolean Core4 term at cursor `a`; `hasOld` says whether the act has an old
state (`monotone`, `writeOnce` read it). -/
def cond (S : Ty) (hasOld : Bool) (a : At) : LawExpr → Term
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
    if hasOld then
      match fieldKind S f with
      | some k => leNat (scalarRead k (a.oldF f)) (scalarRead k (a.newF f))
      | none => falseT
    else falseT
  | .writeOnce f =>
    if hasOld then
      match fieldKind S f with
      | some k => .ifBool (eqNat (scalarRead k (a.oldF f)) (natT 0)) trueT
          (eqNat (scalarRead k (a.newF f)) (scalarRead k (a.oldF f)))
      | none => trueT
    else trueT
  | .not e => notT (cond S hasOld a e)
  | .and l r => andT (cond S hasOld a l) (cond S hasOld a r)
  | .or l r => orT (cond S hasOld a l) (cond S hasOld a r)
  | .implies l r => impliesT (cond S hasOld a l) (cond S hasOld a r)

/-- The clause: the condition, else refuse with the law's name. -/
def clause (S : Ty) (name : String) (e : LawExpr) (hasOld : Bool) (a : At) : Term :=
  guard (cond S hasOld a e) name okT

/-- **The compiled law** `name` over the state type `S`: a write or an invoke is judged with the
old state, a birth or an adoption as a first write; a relaw and a retirement are admitted. -/
def compile (S : Ty) (name : String) (e : LawExpr) : Term :=
  lawOf6 (clause S name e false) (clause S name e false) (fun _ => okT) (fun _ => okT)
    (clause S name e true) (clause S name e true)

/-- A package's laws, each compiled, by name (the kernel installs every one: an act is admitted
when each admits). -/
def compilePackage (S : Ty) (laws : List (String × LawExpr)) : List (String × Term) :=
  laws.map fun (name, e) => (name, compile S name e)

/-! ## What the theorems quantify over -/

/-- The request a kernel builds for an act with the fragment's facts. -/
def reqOf (agent principal : String) (notBefore validUntil : Nat) (occasion : Data) (facts : Facts) : Data :=
  requestAt agent principal notBefore validUntil occasion facts.subject facts.caller facts.height facts.turn

/-- The state's fields fit `S` at field `f`: a natural or boolean field of `S` holds a natural or
boolean (the first field so named), and a field `S` does not read as a scalar holds no scalar. -/
def fitsField (S : Ty) (fs : List (String × Data)) (f : String) : Bool :=
  match fieldKind S f, fieldsLookup f fs with
  | some .nat, some (.natural _) => true
  | some .bool, some (.boolean _) => true
  | none, _ => (Obend.Spec.Law.firstScalarField f fs).isNone
  | _, _ => false

/-- A state FITS `S` for the law `e`: a record whose fields fit `S` at every field `e` reads. -/
def Fits (S : Ty) (e : LawExpr) : Data → Bool
  | .record fs => e.fields.all (fitsField S fs)
  | _ => false

/-- The verdict a meaning predicts. -/
def verdictOf (name : String) : Bool → Term
  | true => okT
  | false => refusedT name

end Obend.Spec.LawCompile

end
