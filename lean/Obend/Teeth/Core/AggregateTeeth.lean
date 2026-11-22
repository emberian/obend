module
/- The aggregate contract as teeth (lane C2, 2026-11-01): returning a resource through a record,
nesting it, matching it, capturing it in a closure, and crossing a quotation, each accepted with the
consuming destructor (`Term.split`) and refused when the destructor would drop or share what the
record holds. Each refusal is the checker's own, named; the mutation checks exercise the destructor quantity,
field coverage, and the reported binding.

Programs are `λ(h : linear Custody 0). …`: the handle must reach the result exactly once. -/
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Core.Code
public import Obend.Tactic.Tooth
import all Obend.Core.Ty
import all Obend.Core.Check
import all Obend.Core.Bidirectional
import all Obend.Core.Code

public section
namespace Obend.Teeth.Core.AggregateTeeth
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
set_option autoImplicit false

def custody : Ty := .custody 0
def handleType : Ty := .arrow .once .linear custody custody
def handleAnnotation : LambdaAnnotation := ⟨custody, custody, .linear, .once⟩

/-! ### Returning: the singleton round trip -/

/-- `λ(h : linear Custody). let {held = x} = {held = h} in x`, the parameter at quantity `q`. -/
def roundTrip (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("held", .bound 0)]) ["held"] (.lam (.bound 0))), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 1] then some ⟨custody, custody, q, .once⟩
    else none, {}⟩

/-- The split rule requires a linear destructor whenever the target uses a linear binding. -/
theorem split_requires_linear (a : Assumptions) (q : Quantity) (ctx : Context) (uses : Uses)
    (h : linearFree ctx uses = false) : caseAllowed a q ctx uses = (q == .linear) := by
  cases q <;> simp [caseAllowed, h]

#tooth split_requires_linear by mutation caseAllowed := fun _ _ _ _ => true

/-- The singleton round trip `{held = h}.held` (refused, `linearProjected`) becomes typable through
the destructor: the record is consumed once and its field bound `linear`. -/
theorem round_trip_accepts_iff_linear (q : Quantity) :
    (checkAgainst (roundTrip q) [] handleType).toBool = (q == .linear) := by
  cases q <;> decide

#tooth round_trip_accepts_iff_linear by mutation checkAgainst := fun _ _ _ => .error .invalidAssumptions

/-- TOOTH (Gate G1 `mustBeLinear` + destructor quantity): binding a `custody` field `affine` is
already refused as `.invalidContext [0, 1]`, while for a custody-free `linear` binding (`roundTripLinearNat`),
the destructor itself refuses `affine` with `.linearArgumentDropped [0] 0 .affine`. -/
def linearNatType : Ty := .arrow .once .linear .natural .natural

def roundTripLinearNat (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("held", .bound 0)]) ["held"] (.lam (.bound 0))), fun path =>
    if path = [] then some ⟨.natural, .natural, .linear, .once⟩
    else if path = [0, 1] then some ⟨.natural, .natural, q, .once⟩
    else none, {}⟩

example :
    (match checkAgainst (roundTrip .affine) [] handleType with
      | .error (.invalidContext [0, 1]) => true
      | _ => false) = true := by decide

example :
    (match checkAgainst (roundTripLinearNat .affine) [] linearNatType with
      | .error (.linearArgumentDropped [0] 0 .affine) => true
      | _ => false) = true := by decide

/-- The projection the destructor replaces is still refused: `{held = h}.held` drops the record's
other fields (there are none here, and the rule does not count them). -/
example :
    (match checkAgainst ⟨.lam (.get (.record [("held", .bound 0)]) "held"),
        fun path => if path = [] then some handleAnnotation else none, {}⟩ [] handleType with
      | .error (.linearProjected [0] 0) => true
      | _ => false) = true := by decide

/-! ### Splitting drops nothing -/

/-- `λ(h : linear Custody). let {held = x, …} = {held = h, tag = 0} in x` with names `ns`. -/
def partialSplit (ns : List String) (body : Term) (functionType : Ty) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("held", .bound 0), ("tag", .nat 0)]) ns body), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 1] then some ⟨custody, functionType, .linear, .once⟩
    else none, {}⟩

/-- TOOTH (a destructor names every field of its target): naming `held` alone would drop `tag`, and
is refused, naming the field. -/
example :
    (match checkAgainst (partialSplit ["held"] (.lam (.bound 0)) custody) [] handleType with
      | .error (.fieldDropped [0] "tag") => true
      | _ => false) = true := by decide

/-- Naming both fields, `tag` bound `affine` and unused (a shareable field holds no handle here, but
the target uses one, so every parameter is `linear`): refused at the `tag` parameter, which drops
it. The coarse quantity rule is stated in `SplitSpine`: the target's uses decide every parameter. -/
example :
    (match checkAgainst (partialSplit ["held", "tag"] (.lam (.lam (.bound 1)))
        (.arrow .once .affine .natural custody)) [] handleType with
      | .error (.linearArgumentDropped [0] 0 .affine) => true
      | _ => false) = true := by
  decide

/-- Acceptance of a destructor accounts for every label on its target row. -/
theorem covered_label_mem (row : Ty) (names : List String) (label : String)
    (hc : SplitCovers row names = true) (hl : label ∈ spineLabels row) : label ∈ names := by
  have all := (Bool.and_eq_true_iff.mp hc).2
  simpa using List.all_eq_true.mp all label hl

#tooth covered_label_mem by mutation SplitCovers := fun _ _ => true

/-- Skipping covered fields reports the first omitted label, wherever it occurs in the row. -/
theorem uncovered_label_of_find (row : Ty) (names : List String) (label : String)
    (h : (spineLabels row).find? (fun name => !names.contains name) = some label) :
    uncoveredLabel row names = label :=
  congrArg (fun found : Option String => found.getD "") h

#tooth uncovered_label_of_find by mutation uncoveredLabel := fun _ _ => ""

/-! ### Nesting -/

def innerRow : Ty := .field "inner" custody .emptyRow

/-- `λh. let {outer = o} = {outer = {inner = h}} in let {inner = x} = o in x`. -/
def nested (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("outer", .record [("inner", .bound 0)])]) ["outer"]
      (.lam (.split (.bound 0) ["inner"] (.lam (.bound 0))))), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 1] then some ⟨innerRow, custody, q, .once⟩
    else if path = [0, 1, 0, 1] then some ⟨custody, custody, .linear, .once⟩
    else none, {}⟩

example : (checkAgainst (nested .linear) [] handleType).toBool = true := by decide

/-- TOOTH (a nested aggregate is consumed whole at each level): on `custody`, Gate G1 rejects the
`affine` outer binder context (`.invalidContext [0, 1, 0, 1]`), and on a custody-free `linear` binding
(`nestedLinearNat`), the outer destructor rejects `affine` with `.linearArgumentDropped [0] 0 .affine`. -/
def innerNatRow : Ty := .field "inner" .natural .emptyRow

def nestedLinearNat (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("outer", .record [("inner", .bound 0)])]) ["outer"]
      (.lam (.split (.bound 0) ["inner"] (.lam (.bound 0))))), fun path =>
    if path = [] then some ⟨.natural, .natural, .linear, .once⟩
    else if path = [0, 1] then some ⟨innerNatRow, .natural, q, .once⟩
    else if path = [0, 1, 0, 1] then some ⟨.natural, .natural, .linear, .once⟩
    else none, {}⟩

example :
    (match checkAgainst (nested .affine) [] handleType with
      | .error (.invalidContext [0, 1, 0, 1]) => true
      | _ => false) = true := by decide

example :
    (match checkAgainst (nestedLinearNat .affine) [] linearNatType with
      | .error (.linearArgumentDropped [0] 0 .affine) => true
      | _ => false) = true := by decide

/-! ### Matching -/

def heldRow : Ty := .field "held" custody .emptyRow
def wrapped : Ty := .variant (.field "l" heldRow .emptyRow)

/-- `λh. case l {held = h} of l p. let {held = x} = p in x`, the inner parameter at `q`. -/
def matched (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.case (.inject "l" (.record [("held", .bound 0)]))
      [("l", .split (.bound 0) ["held"] (.lam (.bound 0)))]), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 0] then some ⟨heldRow, wrapped, .linear, .once⟩
    else if path = [0, 1, 0, 1] then some ⟨custody, custody, q, .once⟩
    else none, {}⟩

/-- A `linear` sum's payload is bound `linear`, and the destructor consumes it. -/
example : (checkAgainst (matched .linear) [] handleType).toBool = true := by decide

/-- TOOTH (the matched payload is a `linear` hypothesis; its destructor binds its field `linear`):
Gate G1 refuses `affine` on `custody` (`.invalidContext [0, 1, 0, 1]`), and on a custody-free `linear`
payload (`matchedLinearNat`), the inner destructor refuses `.linearArgumentDropped [0, 1, 0] 0 .affine`. -/
def heldNatRow : Ty := .field "held" .natural .emptyRow
def wrappedNat : Ty := .variant (.field "l" heldNatRow .emptyRow)

def matchedLinearNat (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.case (.inject "l" (.record [("held", .bound 0)]))
      [("l", .split (.bound 0) ["held"] (.lam (.bound 0)))]), fun path =>
    if path = [] then some ⟨.natural, .natural, .linear, .once⟩
    else if path = [0, 0] then some ⟨heldNatRow, wrappedNat, .linear, .once⟩
    else if path = [0, 1, 0, 1] then some ⟨.natural, .natural, q, .once⟩
    else none, {}⟩

example :
    (match checkAgainst (matched .affine) [] handleType with
      | .error (.invalidContext [0, 1, 0, 1]) => true
      | _ => false) = true := by decide

example :
    (match checkAgainst (matchedLinearNat .affine) [] linearNatType with
      | .error (.linearArgumentDropped [0, 1, 0] 0 .affine) => true
      | _ => false) = true := by decide

/-! ### Capture -/

def thunkType : Ty := .arrow .once .affine .natural custody

/-- `λh. let {f = g} = {f = λ(u : Nat). h} in g 0`: the handle is captured by a once closure held
in a record; the destructor hands the closure to `g` at quantity `q`, and the call returns the handle. -/
def captured (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("f", .lam (.bound 1))]) ["f"] (.lam (.app (.bound 0) (.nat 0)))), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 0, 0] then some ⟨.natural, custody, .affine, .once⟩
    else if path = [0, 1] then some ⟨thunkType, custody, q, .once⟩
    else none, {}⟩

example : (checkAgainst (captured .linear) [] handleType).toBool = true := by decide

/-- TOOTH (a captured handle is not dropped): the closure bound `affine`, which may never call it, is
refused at the destructor, naming the handle. (Bound `unrestricted` it is refused at its own binder:
a once closure is not shareable.) -/
example :
    (match checkAgainst (captured .affine) [] handleType with
      | .error (.linearArgumentDropped [0] 0 .affine) => true
      | _ => false) = true := by decide

example :
    (checkAgainst (captured .unrestricted) [] handleType).toBool = false := by decide

/-- A refused destructor identifies the captured binding at the path being checked. -/
theorem affine_split_refusal (path : List Nat) (ctx : Context) (uses : Uses) (i : Nat)
    (h : firstLinearUse ctx uses = some i) :
    caseRefusal path .affine ctx uses = .linearArgumentDropped path i .affine := by
  simp [caseRefusal, h]

#tooth affine_split_refusal by mutation caseRefusal := fun path _ _ _ => .capturesNotShareable path

/-! ### Crossing a quotation -/

/-- The round trip, quoted and imported back, is the same checked program: a destructor crosses the
code boundary intact (`Code.import_roundtrip` on the program the checker accepts). -/
example :
    ∃ checked, checkAgainst (roundTrip .linear) [] handleType = .ok checked := by
  have accepted := round_trip_accepts_iff_linear .linear
  revert accepted
  cases checkAgainst (roundTrip .linear) [] handleType with
  | ok c => intro _; exact ⟨c, rfl⟩
  | error e => intro h; simp [Except.toBool] at h

/-- The round trip as held code: its term and the finite annotation tree the checker reads. -/
def roundTripHeld : Obend.Core.Code.Held :=
  ⟨(roundTrip .linear).term,
    .node (some handleAnnotation) [.node none [Obend.Core.Proofs.BidirectionalCompleteness.emptyTree,
      .node (some ⟨custody, custody, .linear, .once⟩) []]], {}, []⟩

/-- A reader of this encoding with no kinds and a grant the round trip is within. -/
def roundTripReader : Obend.Core.Code.Reader := ⟨0, 1000, [], fun _ _ _ => false⟩

example :
    (checkAgainst roundTripHeld.annotated [] handleType).toBool = true := by decide

/-- **Crossing a quotation.** The checked round trip, quoted and imported back at its type, is the
same program: a destructor crosses the code boundary intact (`Code.import_roundtrip`). -/
example :
    ∃ c, Obend.Core.Code.importWith roundTripReader [] handleType {}
        (Obend.Core.Code.quotation 0 roundTripHeld) = .ok c ∧ c.val = roundTripHeld := by
  have accepted : (checkAgainst roundTripHeld.annotated [] handleType).toBool = true := by decide
  have within : Obend.Elab.Work.checkWork roundTripHeld.annotated ≤ roundTripReader.grant := by
    decide +kernel
  revert accepted
  cases h : checkAgainst roundTripHeld.annotated [] handleType with
  | ok k =>
    intro _
    exact ⟨_, Obend.Core.Code.import_roundtrip roundTripReader roundTripHeld rfl
      (fun _ hk => by simp [roundTripHeld] at hk) within h, rfl⟩
  | error e => intro hb; simp [Except.toBool] at hb

example :
    Obend.Core.Code.unquote (Obend.Core.Code.quote (roundTrip .linear).term) = some (roundTrip .linear).term :=
  Obend.Core.Code.quote_roundtrip _

end Obend.Teeth.Core.AggregateTeeth
end
