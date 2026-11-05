module
/- The aggregate contract as teeth (lane C2, 2026-11-01): returning a resource through a record,
nesting it, matching it, capturing it in a closure, and crossing a quotation, each accepted with the
consuming destructor (`Term.split`) and refused when the destructor would drop or share what the
record holds. Each refusal is the checker's own, named; each `#tooth` mutates the one premise or
quantity the refusal rests on.

Programs are `λ(h : linear Custody 0). …`: the handle must reach the result exactly once. -/
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Core.Code
public import Obend.Tactic.Tooth
import all Obend.Core.Ty
import all Obend.Core.Check
import all Obend.Core.Bidirectional
import all Obend.Core.Code

namespace Obend.Teeth.Core.AggregateTeeth
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
set_option autoImplicit false

@[expose] public def custody : Ty := .custody 0
@[expose] public def handleType : Ty := .arrow .once .linear custody custody
@[expose] public def handleAnnotation : LambdaAnnotation := ⟨custody, custody, .linear, .once⟩

/-! ### Returning: the singleton round trip -/

/-- The destructor's parameter quantity in the round trip. -/
@[expose] public def destructorQuantity : Quantity := .affine

/-- `λ(h : linear Custody). let {held = x} = {held = h} in x`, the parameter at quantity `q`. -/
@[expose] public def roundTrip (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("held", .bound 0)]) ["held"] (.lam (.bound 0))), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 1] then some ⟨custody, custody, q, .once⟩
    else none, {}⟩

/-- The singleton round trip `{held = h}.held` (refused, `linearProjected`) becomes typable through
the destructor: the record is consumed once and its field bound `linear`. -/
public theorem round_trip_accepted :
    (checkAgainst (roundTrip .linear) [] handleType).toBool = true := by decide

/-- TOOTH (the destructor binds a `linear` record's field `linear`): binding it `affine`, which may
drop it, is refused, naming hypothesis `0`. -/
public theorem round_trip_affine_refused :
    (match checkAgainst (roundTrip destructorQuantity) [] handleType with
      | .error (.linearArgumentDropped [0] 0 .affine) => true
      | _ => false) = true := by decide

#tooth round_trip_affine_refused by mutation destructorQuantity := .linear

/-- The projection the destructor replaces is still refused: `{held = h}.held` drops the record's
other fields (there are none here, and the rule does not count them). -/
example :
    (match checkAgainst ⟨.lam (.get (.record [("held", .bound 0)]) "held"),
        fun path => if path = [] then some handleAnnotation else none, {}⟩ [] handleType with
      | .error (.linearProjected [0] 0) => true
      | _ => false) = true := by decide

/-! ### Splitting drops nothing -/

/-- The names a partial destructor gives. -/
@[expose] public def partialNames : List String := ["held"]

/-- `λ(h : linear Custody). let {held = x, …} = {held = h, tag = 0} in x` with names `ns`. -/
@[expose] public def partialSplit (ns : List String) (body : Term) (functionType : Ty) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("held", .bound 0), ("tag", .nat 0)]) ns body), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 1] then some ⟨custody, functionType, .linear, .once⟩
    else none, {}⟩

/-- TOOTH (a destructor names every field of its target): naming `held` alone would drop `tag`, and
is refused, naming the field. -/
public theorem dropped_field_refused :
    (match checkAgainst (partialSplit partialNames (.lam (.bound 0)) custody) [] handleType with
      | .error (.fieldDropped [0] "tag") => true
      | _ => false) = true := by decide

#tooth dropped_field_refused by mutation partialNames := ["held", "tag"]

/-- Naming both fields, `tag` bound `affine` and unused (a shareable field holds no handle here, but
the target uses one, so every parameter is `linear`): refused at the `tag` parameter, which drops
it. The coarse quantity rule is stated in `SplitSpine`: the target's uses decide every parameter. -/
example :
    (match checkAgainst (partialSplit ["held", "tag"] (.lam (.lam (.bound 1)))
        (.arrow .once .affine .natural custody)) [] handleType with
      | .error (.linearArgumentDropped [0] 0 .affine) => true
      | _ => false) = true := by
  decide

/-! ### Nesting -/

@[expose] public def innerRow : Ty := .field "inner" custody .emptyRow

/-- `λh. let {outer = o} = {outer = {inner = h}} in let {inner = x} = o in x`. -/
@[expose] public def nested (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("outer", .record [("inner", .bound 0)])]) ["outer"]
      (.lam (.split (.bound 0) ["inner"] (.lam (.bound 0))))), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 1] then some ⟨innerRow, custody, q, .once⟩
    else if path = [0, 1, 0, 1] then some ⟨custody, custody, .linear, .once⟩
    else none, {}⟩

/-- The outer parameter's quantity in the nesting fixture. -/
@[expose] public def nestedQuantity : Quantity := .affine

example : (checkAgainst (nested .linear) [] handleType).toBool = true := by decide

/-- TOOTH (a nested aggregate is consumed whole at each level): the outer field bound `affine` is
refused. -/
public theorem nested_affine_refused :
    (match checkAgainst (nested nestedQuantity) [] handleType with
      | .error (.linearArgumentDropped [0] 0 .affine) => true
      | _ => false) = true := by decide

#tooth nested_affine_refused by mutation nestedQuantity := .linear

/-! ### Matching -/

@[expose] public def heldRow : Ty := .field "held" custody .emptyRow
@[expose] public def wrapped : Ty := .variant (.field "l" heldRow .emptyRow)

/-- `λh. case l {held = h} of l p. let {held = x} = p in x`, the inner parameter at `q`. -/
@[expose] public def matched (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.case (.inject "l" (.record [("held", .bound 0)]))
      [("l", .split (.bound 0) ["held"] (.lam (.bound 0)))]), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 0] then some ⟨heldRow, wrapped, .linear, .once⟩
    else if path = [0, 1, 0, 1] then some ⟨custody, custody, q, .once⟩
    else none, {}⟩

@[expose] public def matchedQuantity : Quantity := .affine

/-- A `linear` sum's payload is bound `linear`, and the destructor consumes it. -/
example : (checkAgainst (matched .linear) [] handleType).toBool = true := by decide

/-- TOOTH (the matched payload is a `linear` hypothesis; its destructor binds its field `linear`). -/
public theorem matched_affine_refused :
    (match checkAgainst (matched matchedQuantity) [] handleType with
      | .error (.linearArgumentDropped [0, 1, 0] 0 .affine) => true
      | _ => false) = true := by decide

#tooth matched_affine_refused by mutation matchedQuantity := .linear

/-! ### Capture -/

@[expose] public def thunkType : Ty := .arrow .once .affine .natural custody

/-- `λh. let {f = g} = {f = λ(u : Nat). h} in g 0`: the handle is captured by a once closure held
in a record; the destructor hands the closure to `g` at quantity `q`, and the call returns the handle. -/
@[expose] public def captured (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.split (.record [("f", .lam (.bound 1))]) ["f"] (.lam (.app (.bound 0) (.nat 0)))), fun path =>
    if path = [] then some handleAnnotation
    else if path = [0, 0, 0] then some ⟨.natural, custody, .affine, .once⟩
    else if path = [0, 1] then some ⟨thunkType, custody, q, .once⟩
    else none, {}⟩

@[expose] public def capturedQuantity : Quantity := .affine

example : (checkAgainst (captured .linear) [] handleType).toBool = true := by decide

/-- TOOTH (a captured handle is not dropped): the closure bound `affine`, which may never call it, is
refused at the destructor, naming the handle. (Bound `unrestricted` it is refused at its own binder:
a once closure is not shareable.) -/
public theorem captured_dropped_refused :
    (match checkAgainst (captured capturedQuantity) [] handleType with
      | .error (.linearArgumentDropped [0] 0 .affine) => true
      | _ => false) = true := by decide

#tooth captured_dropped_refused by mutation capturedQuantity := .linear

example :
    (checkAgainst (captured .unrestricted) [] handleType).toBool = false := by decide

/-! ### Crossing a quotation -/

/-- The round trip, quoted and imported back, is the same checked program: a destructor crosses the
code boundary intact (`Code.import_roundtrip` on the program the checker accepts). -/
public theorem round_trip_accepted_certificate :
    ∃ checked, checkAgainst (roundTrip .linear) [] handleType = .ok checked := by
  have accepted := round_trip_accepted
  revert accepted
  cases checkAgainst (roundTrip .linear) [] handleType with
  | ok c => intro _; exact ⟨c, rfl⟩
  | error e => intro h; simp [Except.toBool] at h

/-- The round trip as held code: its term and the finite annotation tree the checker reads. -/
@[expose] public def roundTripHeld : Obend.Core.Code.Held :=
  ⟨(roundTrip .linear).term,
    .node (some handleAnnotation) [.node none [Obend.Core.Proofs.BidirectionalCompleteness.emptyTree,
      .node (some ⟨custody, custody, .linear, .once⟩) []]], {}, []⟩

/-- A reader of this encoding with no kinds and a grant the round trip is within. -/
@[expose] public def roundTripReader : Obend.Core.Code.Reader := ⟨0, 1000, [], fun _ _ _ => false⟩

public theorem roundTripHeld_accepted :
    (checkAgainst roundTripHeld.annotated [] handleType).toBool = true := by decide

/-- **Crossing a quotation.** The checked round trip, quoted and imported back at its type, is the
same program: a destructor crosses the code boundary intact (`Code.import_roundtrip`). -/
public theorem round_trip_crosses_quotation :
    ∃ c, Obend.Core.Code.importWith roundTripReader [] handleType {}
        (Obend.Core.Code.quotation 0 roundTripHeld) = .ok c ∧ c.val = roundTripHeld := by
  have accepted := roundTripHeld_accepted
  have within : Obend.Elab.Work.checkWork roundTripHeld.annotated ≤ roundTripReader.grant := by
    decide +kernel
  revert accepted
  cases h : checkAgainst roundTripHeld.annotated [] handleType with
  | ok k =>
    intro _
    exact ⟨_, Obend.Core.Code.import_roundtrip roundTripReader roundTripHeld rfl
      (fun _ hk => by simp [roundTripHeld] at hk) within h, rfl⟩
  | error e => intro hb; simp [Except.toBool] at hb

public theorem round_trip_quote_roundtrip :
    Obend.Core.Code.unquote (Obend.Core.Code.quote (roundTrip .linear).term) = some (roundTrip .linear).term :=
  Obend.Core.Code.quote_roundtrip _

end Obend.Teeth.Core.AggregateTeeth
