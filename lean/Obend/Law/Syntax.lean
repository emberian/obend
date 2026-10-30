module
/-
# Obend.Law.Syntax — the law's types, the `At` cursor, the verdict combinators, the skeleton

Ported from nanodregg `Lang/Std.lean` (origin/main `2dcc9ea`, decisions LANG-8, LANG-19, LANG-20,
LANG-24) onto Core4 `Term`. A law is a closed Core4 term of type `lawTy S`,
`S → S → Req → Verdict`, applied to the old state, the new state and the request
(`applyLaw`). `Verdict = sum {ok : {}, refused : label}` (LANG-8; Core4 has no bytes, so the
author's reason is a `label`). The request carries an `occasion`, a sum with one arm per act the
kernel judges (LANG-19, LANG-24, KERNEL-70):

    birth : {}   adopt : label   relaw : label   retire : {}   write : {}   invoke : nat

`adopt` and `relaw` carry the incoming laws' ids (text: Core4 has no bytes), `invoke` the method
index. A law is built by `lawOf S birth adopt relaw retire change` (`lawOf6` with a separate write
and invoke clause): a `case` on `req.occasion` with an arm for every act and no default.

Clauses are written against `At`, which counts the binders between the law's three arguments and
the clause, so a clause may open a `case` of its own (`At.under`) and still name `old`, `new` and
`req` correctly. What a law MEANS is a theorem over Core4's reference semantics
(`Obend.Law.Proofs.Std`), never an evaluation of the term: `Admits` and `Refuses` below are stated
over `Evaluates`.

Deviation from the brief's `reqTy S`: the request type does not depend on the state type (it did
not in nano either), so it is `reqTy`, and `lawTy S` is the only type indexed by `S`.
-/
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Data
@[expose] public section
namespace Obend.Law
open Obend.Core.Term (Term Evaluates Primitive)
open Obend.Core.Ty (Ty Reuse Quantity)
open Obend.Core.Data (Data)
set_option autoImplicit false

/-! ## Types -/

/-- The empty record's type: a record's type is its field row. -/
def unitTy : Ty := .emptyRow

/-- One arm per act, in label order (the order a `case` on it states its arms). -/
def occasionRow : Ty :=
  .field "adopt" .label (.field "birth" unitTy (.field "invoke" .natural
    (.field "relaw" .label (.field "retire" unitTy (.field "write" unitTy .emptyRow)))))

def occasionTy : Ty := .variant occasionRow

/-- `sum {ok : {}, refused : label}` (LANG-8). -/
def verdictTy : Ty := .variant (.field "ok" unitTy (.field "refused" .label .emptyRow))

/-- The request a law judges: the signer (`agent`), the authority it acts under (`principal`), the
signed window (`notBefore`, `validUntil`) and the occasion. -/
def reqTy : Ty :=
  .field "agent" .label (.field "notBefore" .natural (.field "occasion" occasionTy
    (.field "principal" .label (.field "validUntil" .natural .emptyRow))))

/-- A reusable, unrestricted arrow: a law may be applied any number of times. -/
def fnTy (domain codomain : Ty) : Ty := .arrow .reusable .unrestricted domain codomain

/-- `S → S → Req → Verdict`. -/
def lawTy (S : Ty) : Ty := fnTy S (fnTy S (fnTy reqTy verdictTy))

/-! ## The cursor -/

/-- Where a clause sits: `depth` binders below the law's `old`, `new`, `req`. -/
structure At where
  depth : Nat

namespace At
def old (a : At) : Term := .bound (a.depth + 2)
def new (a : At) : Term := .bound (a.depth + 1)
def req (a : At) : Term := .bound a.depth
/-- One binder further in (inside an arm of a `case` the clause opens itself). -/
def under (a : At) : At := ⟨a.depth + 1⟩
/-- The occasion's payload (`lawOf`'s arm binder, one binder below the law's arguments). -/
def payload (a : At) : Term := .bound (a.depth - 1)
def oldF (a : At) (f : String) : Term := .get a.old f
def newF (a : At) (f : String) : Term := .get a.new f
def reqF (a : At) (f : String) : Term := .get a.req f
end At

/-! ## Verdicts and combinators -/

def okT : Term := .inject "ok" (.record [])
def refusedT (why : String) : Term := .inject "refused" (.label why)

/-- `c` must hold, else refuse with `why`; then `rest`. -/
def guard (c : Term) (why : String) (rest : Term) : Term := .ifBool c rest (refusedT why)

/-- Each condition in order, each with its reason; `rest` if all hold. -/
def guards : List (Term × String) → Term → Term
  | [], t => t
  | (c, w) :: r, t => guard c w (guards r t)

/-- Every condition, then `ok`. -/
def allOf (l : List (Term × String)) : Term := guards l okT

def trueT : Term := .boolean true
def falseT : Term := .boolean false
def andT (a b : Term) : Term := .ifBool a b falseT
def notT (a : Term) : Term := .ifBool a falseT trueT

/-- Some condition holds (`false` for none). -/
def anyOf : List Term → Term
  | [] => falseT
  | c :: r => .ifBool c trueT (anyOf r)

def natT (k : Nat) : Term := .nat k

def eqNat (a b : Term) : Term := .binary .equal a b
def eqLabel (a b : Term) : Term := .binary .labelEqual a b
def leNat (a b : Term) : Term := .binary .lessEqual a b
def ltNat (a b : Term) : Term := .binary .less a b
def addNat (a b : Term) : Term := .binary .add a b
def divNat (a b : Term) : Term := .binary .divide a b
def modNat (a b : Term) : Term := .binary .modulo a b

/-! ## The law skeleton -/

/-- `case req.occasion` with one arm per act, in `occasionRow`'s order. In every arm the payload
is `bound 0` and the clause sits at depth 1. `adopt` is this law judging the state it is being
ADDED over (KERNEL-27); `relaw` this law, in force, judging its replacement; `retire` this law
judging the object's end over its last state (`old = new`, KERNEL-70). -/
def lawCase6 (birth adopt relaw retire write invoke : At → Term) : Term :=
  let a : At := ⟨1⟩
  .case (.get (.bound 0) "occasion")
    [("adopt", adopt a), ("birth", birth a), ("invoke", invoke a), ("relaw", relaw a),
     ("retire", retire a), ("write", write a)]

/-- `λ old. λ new. λ req. body`. -/
def law3 (body : Term) : Term := .lam (.lam (.lam body))

/-- A law with one clause per act. -/
def lawOf6 (birth adopt relaw retire write invoke : At → Term) : Term :=
  law3 (lawCase6 birth adopt relaw retire write invoke)

/-- The common case: writes and invokes judged alike, as a CHANGE. -/
def lawCase (birth adopt relaw retire change : At → Term) : Term :=
  lawCase6 birth adopt relaw retire change change

/-- `S` names the state type the law is written for (`lawTy S`); Core4's lambdas carry no
annotation, so the term does not mention it. -/
def lawOf (_S : Ty) (birth adopt relaw retire change : At → Term) : Term :=
  law3 (lawCase birth adopt relaw retire change)

/-- The body under a law's three binders. -/
def lawBody : Term → Term
  | .lam (.lam (.lam b)) => b
  | t => t

/-! ## Data and what a law means -/

/-- The first field `f` of a record (as the reference semantics' `get` selects it). -/
def fieldsLookup (f : String) : List (String × Data) → Option Data
  | [] => none
  | (g, d) :: rest => if g == f then some d else fieldsLookup f rest

def _root_.Obend.Core.Data.Data.field (d : Data) (f : String) : Option Data :=
  match d with
  | .record fs => fieldsLookup f fs
  | _ => none

/-- The law applied to the old state, the new state and the request. -/
def applyLaw (law : Term) (old new req : Data) : Term :=
  .app (.app (.app law old.term) new.term) req.term

/-- The law ADMITS `old → new` under `req`: applied, it evaluates to `ok`. -/
def Admits (law : Term) (old new req : Data) : Prop :=
  ∃ w, Evaluates (applyLaw law old new req) (.inject "ok" w)

/-- The law REFUSES `old → new` under `req` with reason `why`. -/
def Refuses (law : Term) (old new req : Data) (why : String) : Prop :=
  Evaluates (applyLaw law old new req) (refusedT why)

/-- A request: who signs, under whose authority, in which window, on which occasion. -/
def request (agent principal : String) (notBefore validUntil : Nat) (occasion : Data) : Data :=
  .record [("agent", .label agent), ("notBefore", .natural notBefore), ("occasion", occasion),
    ("principal", .label principal), ("validUntil", .natural validUntil)]

/-- The occasions, as data. -/
def birthO : Data := .variant "birth" (.record [])
def adoptO (laws : String) : Data := .variant "adopt" (.label laws)
def relawO (laws : String) : Data := .variant "relaw" (.label laws)
def retireO : Data := .variant "retire" (.record [])
def writeO : Data := .variant "write" (.record [])
def invokeO (method : Nat) : Data := .variant "invoke" (.natural method)

/-- Which arm the change clause is: a write or an invoke. -/
def IsChange (occasion : Data) : Prop :=
  (∃ x, occasion = .variant "write" x) ∨ (∃ x, occasion = .variant "invoke" x)

end Obend.Law
