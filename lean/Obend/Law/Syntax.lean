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

Consensus time (`review/VISION-CLAUDE-20261031.md` §2.1 item 4): the request record's `height` is
the LEDGER's, never the submitter's. `requestAt` takes it as a `Consensus` (the ledger's facts every
law reads); what a submitter sends is a `Submission`, which has no height field and may only CLAIM
the height it was made at (`seen`); `sealAt` builds the request at the ledger's consensus, refusing a
claim from the future (`futureHeight`), so no law can read a height a request chose
(`seal_claim_irrelevant`).

Deviation from the brief's `reqTy S`: the request type does not depend on the state type (it did
not in nano either), so it is `reqTy`, and `lawTy S` is the only type indexed by `S`.
-/
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Data
public section
namespace Obend.Law
open Obend.Core.Term (Term Evaluates Primitive)
open Obend.Core.Ty (Ty Reuse Quantity)
open Obend.Core.Data (Data)
set_option autoImplicit false

/-! ## Types -/

/-- The empty record's type: a record's type is its field row. -/
@[expose] def unitTy : Ty := .emptyRow

/-- One arm per act, in label order (the order a `case` on it states its arms). -/
@[expose] def occasionRow : Ty :=
  .field "adopt" .label (.field "birth" unitTy (.field "invoke" .natural
    (.field "relaw" .label (.field "retire" unitTy (.field "write" unitTy .emptyRow)))))

@[expose] def occasionTy : Ty := .variant occasionRow

/-- `sum {ok : {}, refused : label}` (LANG-8). -/
@[expose] def verdictTy : Ty := .variant (.field "ok" unitTy (.field "refused" .label .emptyRow))

/-- An optional natural: `sum {none : {}, some : nat}`. -/
@[expose] def optNatTy : Ty := .variant (.field "none" unitTy (.field "some" .natural .emptyRow))

/-- The request a law judges: the signer (`agent`), the authority it acts under (`principal`), the
signed window (`notBefore`, `validUntil`) and the occasion; and the kernel's facts of the act that
the enforced `law` fragment reads (`Obend.Spec.Law.Facts`): the `subject` whose authority the act
carries and the `caller` (each absent in a frame that has none), the `height` and the kernel `turn`.
Fields in label order. -/
@[expose] def reqTy : Ty :=
  .field "agent" .label (.field "caller" optNatTy (.field "height" .natural
    (.field "notBefore" .natural (.field "occasion" occasionTy
    (.field "principal" .label (.field "subject" optNatTy (.field "turn" .natural
    (.field "validUntil" .natural .emptyRow))))))))

/-- A reusable, unrestricted arrow: a law may be applied any number of times. -/
@[expose] def fnTy (domain codomain : Ty) : Ty := .arrow .reusable .unrestricted domain codomain

/-- `S → S → Req → Verdict`. -/
@[expose] def lawTy (S : Ty) : Ty := fnTy S (fnTy S (fnTy reqTy verdictTy))

/-! ## The cursor -/

/-- Where a clause sits: `depth` binders below the law's `old`, `new`, `req`. -/
structure At where
  depth : Nat

namespace At
@[expose] def old (a : At) : Term := .bound (a.depth + 2)
@[expose] def new (a : At) : Term := .bound (a.depth + 1)
@[expose] def req (a : At) : Term := .bound a.depth
/-- One binder further in (inside an arm of a `case` the clause opens itself). -/
@[expose] def under (a : At) : At := ⟨a.depth + 1⟩
/-- The occasion's payload (`lawOf`'s arm binder, one binder below the law's arguments). -/
@[expose] def payload (a : At) : Term := .bound (a.depth - 1)
@[expose] def oldF (a : At) (f : String) : Term := .get a.old f
@[expose] def newF (a : At) (f : String) : Term := .get a.new f
@[expose] def reqF (a : At) (f : String) : Term := .get a.req f
end At

/-! ## Verdicts and combinators -/

@[expose] def okT : Term := .inject "ok" (.record [])
@[expose] def refusedT (why : String) : Term := .inject "refused" (.label why)

/-- `c` must hold, else refuse with `why`; then `rest`. -/
@[expose] def guard (c : Term) (why : String) (rest : Term) : Term := .ifBool c rest (refusedT why)

/-- Each condition in order, each with its reason; `rest` if all hold. -/
@[expose] def guards : List (Term × String) → Term → Term
  | [], t => t
  | (c, w) :: r, t => guard c w (guards r t)

/-- Every condition, then `ok`. -/
@[expose] def allOf (l : List (Term × String)) : Term := guards l okT

@[expose] def trueT : Term := .boolean true
@[expose] def falseT : Term := .boolean false
@[expose] def andT (a b : Term) : Term := .ifBool a b falseT
@[expose] def notT (a : Term) : Term := .ifBool a falseT trueT

/-- Some condition holds (`false` for none). -/
@[expose] def anyOf : List Term → Term
  | [] => falseT
  | c :: r => .ifBool c trueT (anyOf r)

@[expose] def natT (k : Nat) : Term := .nat k

@[expose] def eqNat (a b : Term) : Term := .binary .equal a b
@[expose] def eqLabel (a b : Term) : Term := .binary .labelEqual a b
@[expose] def leNat (a b : Term) : Term := .binary .lessEqual a b
@[expose] def ltNat (a b : Term) : Term := .binary .less a b
@[expose] def addNat (a b : Term) : Term := .binary .add a b
@[expose] def divNat (a b : Term) : Term := .binary .divide a b
@[expose] def modNat (a b : Term) : Term := .binary .modulo a b

/-! ## The law skeleton -/

/-- `case req.occasion` with one arm per act, in `occasionRow`'s order. In every arm the payload
is `bound 0` and the clause sits at depth 1. `adopt` is this law judging the state it is being
ADDED over (KERNEL-27); `relaw` this law, in force, judging its replacement; `retire` this law
judging the object's end over its last state (`old = new`, KERNEL-70). -/
@[expose] def lawCase6 (birth adopt relaw retire write invoke : At → Term) : Term :=
  let a : At := ⟨1⟩
  .case (.get (.bound 0) "occasion")
    [("adopt", adopt a), ("birth", birth a), ("invoke", invoke a), ("relaw", relaw a),
     ("retire", retire a), ("write", write a)]

/-- `λ old. λ new. λ req. body`. -/
@[expose] def law3 (body : Term) : Term := .lam (.lam (.lam body))

/-- A law with one clause per act. -/
@[expose] def lawOf6 (birth adopt relaw retire write invoke : At → Term) : Term :=
  law3 (lawCase6 birth adopt relaw retire write invoke)

/-- The common case: writes and invokes judged alike, as a CHANGE. -/
@[expose] def lawCase (birth adopt relaw retire change : At → Term) : Term :=
  lawCase6 birth adopt relaw retire change change

/-- `S` names the state type the law is written for (`lawTy S`); Core4's lambdas carry no
annotation, so the term does not mention it. -/
@[expose] def lawOf (_S : Ty) (birth adopt relaw retire change : At → Term) : Term :=
  law3 (lawCase birth adopt relaw retire change)

/-- The body under a law's three binders. -/
@[expose] def lawBody : Term → Term
  | .lam (.lam (.lam b)) => b
  | t => t

/-! ## Data and what a law means -/

/-- The first field `f` of a record (as the reference semantics' `get` selects it). -/
@[expose] def fieldsLookup (f : String) : List (String × Data) → Option Data
  | [] => none
  | (g, d) :: rest => if g == f then some d else fieldsLookup f rest

@[expose] def _root_.Obend.Core.Data.Data.field (d : Data) (f : String) : Option Data :=
  match d with
  | .record fs => fieldsLookup f fs
  | _ => none

/-- The law applied to the old state, the new state and the request. -/
@[expose] def applyLaw (law : Term) (old new req : Data) : Term :=
  .app (.app (.app law old.term) new.term) req.term

/-- The law ADMITS `old → new` under `req`: applied, it evaluates to `ok`. -/
@[expose] def Admits (law : Term) (old new req : Data) : Prop :=
  ∃ w, Evaluates (applyLaw law old new req) (.inject "ok" w)

/-- The law REFUSES `old → new` under `req` with reason `why`. -/
@[expose] def Refuses (law : Term) (old new req : Data) (why : String) : Prop :=
  Evaluates (applyLaw law old new req) (refusedT why)

/-- An optional natural, as data. -/
@[expose] def optNat : Option Nat → Data
  | none => .variant "none" (.record [])
  | some k => .variant "some" (.natural k)

/-- **The ledger's facts every law reads**: the consensus height. A ledger supplies it; a request
never does. -/
structure Consensus where
  height : Nat
  deriving DecidableEq, Repr

/-- A request with the kernel's facts: who signs, under whose authority, in which window, on which
occasion; the subject and caller (if any), the turn; and the ledger's consensus `c`, whose height is
the record's `height`. -/
@[expose] def requestAt (agent principal : String) (notBefore validUntil : Nat) (occasion : Data)
    (subject caller : Option Nat) (c : Consensus) (turn : Nat) : Data :=
  .record [("agent", .label agent), ("caller", optNat caller), ("height", .natural c.height),
    ("notBefore", .natural notBefore), ("occasion", occasion), ("principal", .label principal),
    ("subject", optNat subject), ("turn", .natural turn), ("validUntil", .natural validUntil)]

/-- A request: who signs, under whose authority, in which window, on which occasion (no subject,
no caller, turn 0, at the genesis consensus). -/
@[expose] def request (agent principal : String) (notBefore validUntil : Nat) (occasion : Data) : Data :=
  requestAt agent principal notBefore validUntil occasion none none ⟨0⟩ 0

/-- **What a submitter sends**: everything a request carries except the ledger's facts. `seen` is
the height the submitter claims it acted at: a claim the ledger checks, never a value a law reads. -/
structure Submission where
  agent : String
  principal : String
  notBefore : Nat
  validUntil : Nat
  occasion : Data
  subject : Option Nat
  caller : Option Nat
  turn : Nat
  seen : Option Nat

/-- Why a submission cannot be sealed. -/
inductive SealRefusal where
  /-- the submission claims a height the ledger has not reached -/
  | futureHeight (claimed current : Nat)
  deriving DecidableEq, Repr

/-- The request a submission becomes at consensus `c`. -/
def Submission.request (s : Submission) (c : Consensus) : Data :=
  requestAt s.agent s.principal s.notBefore s.validUntil s.occasion s.subject s.caller c s.turn

/-- **Seal a submission at the ledger's consensus**: the request's height is the ledger's; a claim of
a height the ledger has not reached is refused. -/
@[expose] def sealAt (c : Consensus) (s : Submission) : Except SealRefusal Data :=
  match s.seen with
  | some h => if c.height < h then .error (.futureHeight h c.height) else .ok (s.request c)
  | none => .ok (s.request c)

/-- A sealed request is the submission at the ledger's consensus. -/
theorem seal_ok {c : Consensus} {s : Submission} {d : Data} (h : sealAt c s = .ok d) : d = s.request c := by
  unfold sealAt at h; split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h; rfl

/-- The sealed request's height is the ledger's. -/
theorem seal_height {c : Consensus} {s : Submission} {d : Data} (h : sealAt c s = .ok d) :
    d.field "height" = some (.natural c.height) := by
  rw [seal_ok h]; simp [Submission.request, requestAt, Data.field, fieldsLookup]

/-- **The claim is irrelevant to what a law reads**: two submissions that differ only in the height
they claim seal, when both seal, to the same request. -/
theorem seal_claim_irrelevant {c : Consensus} {s : Submission} {h h' : Option Nat} {d d' : Data}
    (hd : sealAt c { s with seen := h } = .ok d) (hd' : sealAt c { s with seen := h' } = .ok d') : d = d' := by
  rw [seal_ok hd, seal_ok hd']; rfl

/-- **A claim from the future is refused**, naming the claim and the ledger's height. -/
theorem seal_future {c : Consensus} {s : Submission} {h : Nat} (hs : s.seen = some h) (hlt : c.height < h) :
    sealAt c s = .error (.futureHeight h c.height) := by
  simp [sealAt, hs, hlt]

/-- A claim at or before the ledger's height seals. -/
theorem seal_past {c : Consensus} {s : Submission} {h : Nat} (hs : s.seen = some h) (hle : h ≤ c.height) :
    sealAt c s = .ok (s.request c) := by
  simp [sealAt, hs, Nat.not_lt.2 hle]

/-- The occasions, as data. -/
@[expose] def birthO : Data := .variant "birth" (.record [])
@[expose] def adoptO (laws : String) : Data := .variant "adopt" (.label laws)
@[expose] def relawO (laws : String) : Data := .variant "relaw" (.label laws)
@[expose] def retireO : Data := .variant "retire" (.record [])
@[expose] def writeO : Data := .variant "write" (.record [])
@[expose] def invokeO (method : Nat) : Data := .variant "invoke" (.natural method)

/-- Which arm the change clause is: a write or an invoke. -/
@[expose] def IsChange (occasion : Data) : Prop :=
  (∃ x, occasion = .variant "write" x) ∨ (∃ x, occasion = .variant "invoke" x)

end Obend.Law
