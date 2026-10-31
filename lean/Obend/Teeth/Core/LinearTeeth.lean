module
/- `linear` separates from `affine` in the kernel (decided 2026-11-01; `lean/docs/REPORT-LINEAR-20261101.md`).

Four premises carry it. `PartialTyping.lambda` requires `Quantity.fits` of the parameter's own
count, so a `linear` binder is used exactly once; `argumentAllowed` requires `linearFree` of an
argument passed to a non-`linear` parameter, so a `linear` hypothesis is never handed to a callee
that may drop it (`erased`, `affine`) or share it (`unrestricted`); the joins (`ifBool`, `ifZero`,
`case` arms) require `branchesAgree`, so every branch uses it equally, and join by `joinUses`; the
projections (`get`, `reflect`, `metadata`, `project`) require `linearFree` of their target, so no
dropped sibling holds one. Both checkers name the refusal: `linearBinderUnused`,
`linearArgumentDropped`, `linearBranchesDisagree`, `linearProjected`.

Each tooth below is the same program at `affine` and at `linear`: accepted at one, refused at the
other, so the refusal is the quantity's and nothing else's. -/
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Tactic.Tooth
import all Obend.Core.Ty

namespace Obend.Teeth.Core.LinearTeeth
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences)
set_option autoImplicit false

/-- The quantity of the custody parameter in the fixtures. -/
@[expose] public def custodyQuantity : Quantity := .linear

/-- `λ(h : Custody). 0`: the custody is dropped. -/
@[expose] public def droppedCustody (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.nat 0), fun path => if path = [] then some ⟨.custody 0, .natural, q, .once⟩ else none, {}⟩

@[expose] public def droppedCustodyType (q : Quantity) : Ty := .arrow .once q (.custody 0) .natural

/-- TOOTH (a dropped `linear` custody is refused, by name, at its binder). -/
public theorem dropped_linear_custody_refused :
    (match checkAgainst (droppedCustody custodyQuantity) [] (droppedCustodyType custodyQuantity) with
      | .error (.linearBinderUnused []) => true
      | _ => false) = true := by decide

/-- The fuel checker refuses it too. -/
public theorem dropped_linear_custody_refused_by_check :
    (check (droppedCustody custodyQuantity) [] 4).isNone = true := by decide

/-- The same program with an `affine` custody is accepted: dropping is within "at most once". -/
public theorem dropped_affine_custody_accepted :
    (checkAgainst (droppedCustody .affine) [] (droppedCustodyType .affine)).toBool = true := by decide

#tooth dropped_linear_custody_refused by mutation custodyQuantity := .affine

/-- `λ(h : Custody). (λ(z : Custody). 0) h`: the custody is passed to a callee whose parameter has
quantity `q`. -/
@[expose] public def handedCustody (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.app (.lam (.nat 0)) (.bound 0)), fun path =>
    if path = [] then some ⟨.custody 0, .natural, .linear, .once⟩
    else if path = [0] then some ⟨.arrow .once q (.custody 0) .natural, .natural, .affine, .once⟩
    else if path = [0, 0] then some ⟨.custody 0, .natural, q, .once⟩
    else none, {}⟩

/-- The callee's quantity in the laundering fixture. -/
@[expose] public def calleeQuantity : Quantity := .affine

/-- TOOTH (a `linear` hypothesis handed to an `affine` callee, which drops it, is refused by name:
the argument at `[0, 1]` uses hypothesis `0`). The binder count is one, so exact discharge at the
binder alone would have accepted it. -/
public theorem laundered_custody_refused :
    (match checkAgainst (handedCustody calleeQuantity) [] (droppedCustodyType .linear) with
      | .error (.linearArgumentDropped [0, 1] 0 .affine) => true
      | _ => false) = true := by decide

#tooth laundered_custody_refused by mutation calleeQuantity := .linear

/-- With a `linear` callee the obligation moves to it, and it is refused at the callee's own binder,
which drops it: the drop is found wherever the custody goes. -/
public theorem handed_to_linear_refused_at_callee :
    (match checkAgainst (handedCustody .linear) [] (droppedCustodyType .linear) with
      | .error (.linearBinderUnused [0, 0]) => true
      | _ => false) = true := by decide

/-- A `linear` custody that flows into a `linear` slot which uses it is accepted:
`λ(h : Custody). (λ(z : Custody). z) h`. -/
@[expose] public def passedCustody : AnnotatedTerm :=
  ⟨.lam (.app (.lam (.bound 0)) (.bound 0)), fun path =>
    if path = [] then some ⟨.custody 0, .custody 0, .linear, .once⟩
    else if path = [0] then some ⟨.arrow .once .linear (.custody 0) (.custody 0), .custody 0, .affine, .once⟩
    else if path = [0, 0] then some ⟨.custody 0, .custody 0, .linear, .once⟩
    else none, {}⟩

public theorem passed_linear_custody_accepted :
    (checkAgainst passedCustody [] (.arrow .once .linear (.custody 0) (.custody 0))).toBool = true := by decide

/-! ### The two gaps exact discharge left at the binder, closed

A branch that drops a `linear` hypothesis the other branch uses (`branchesAgree`), and a projection
that drops a sibling holding one (`linearFree` at `get`, `reflect`, `metadata`, `project`). -/

/-- `λ(h : Nat). if c then h else e`, with `h` of quantity `q`. -/
@[expose] public def branching (q : Quantity) (whenFalse : Term) : AnnotatedTerm :=
  ⟨.lam (.ifBool (.boolean true) (.bound 0) whenFalse), fun path =>
    if path = [] then some ⟨.natural, .natural, q, .once⟩ else none, {}⟩

/-- The false branch of the branch fixture. -/
@[expose] public def falseBranch : Term := .nat 0

/-- TOOTH (a branch drops a `linear` hypothesis the other uses: refused by name at the join, naming
hypothesis `0`). Counting by sum this was one use and accepted. -/
public theorem dropped_on_branch_refused :
    (match checkAgainst (branching .linear falseBranch) [] (.arrow .once .linear .natural .natural) with
      | .error (.linearBranchesDisagree [0] 0) => true
      | _ => false) = true := by decide

#tooth dropped_on_branch_refused by mutation falseBranch := .bound 0

/-- Both branches use it once: one use on every path, accepted (by sum it was two, refused). -/
public theorem used_on_every_branch_accepted :
    (checkAgainst (branching .linear (.bound 0)) [] (.arrow .once .linear .natural .natural)).toBool = true := by
  decide

/-- An `affine` hypothesis joins by maximum: used on one branch, or on both, it is used at most once. -/
public theorem affine_branches_accepted :
    (checkAgainst (branching .affine falseBranch) [] (.arrow .once .affine .natural .natural)).toBool = true ∧
    (checkAgainst (branching .affine (.bound 0)) [] (.arrow .once .affine .natural .natural)).toBool = true := by
  decide

/-- The quantity of the projected fixture's parameter. -/
@[expose] public def siblingQuantity : Quantity := .linear

/-- `λ(h : Nat). {kept = 1, held = h}.kept`: the projection keeps `kept` and drops `held`. -/
@[expose] public def siblingDropped (q : Quantity) : AnnotatedTerm :=
  ⟨.lam (.get (.record [("kept", .nat 1), ("held", .bound 0)]) "kept"), fun path =>
    if path = [] then some ⟨.natural, .natural, q, .once⟩ else none, {}⟩

/-- TOOTH (a projection drops a sibling holding a `linear` hypothesis: refused by name at the
projection, naming hypothesis `0`). The binder count is one, so the binder rule alone accepted it. -/
public theorem sibling_projection_refused :
    (match checkAgainst (siblingDropped siblingQuantity) [] (.arrow .once siblingQuantity .natural .natural) with
      | .error (.linearProjected [0] 0) => true
      | _ => false) = true := by decide

#tooth sibling_projection_refused by mutation siblingQuantity := .affine

/-- At `affine` the same projection is accepted: the dropped sibling may be dropped. -/
public theorem sibling_projection_affine_accepted :
    (checkAgainst (siblingDropped .affine) [] (.arrow .once .affine .natural .natural)).toBool = true := by decide


/-! ### Four rules that let a `Step` discard what a subterm held (lane Sound, 11-01)

Gemini's checkpoint review, item 1. Each fixture below is `λ(h : Nat). body` with `h` of quantity `q`;
at `linear`, `body` was accepted by both checkers before 11-01 (measured on the tree at `9d75d59`), and
one or two `Step`s from `body` (open in `h`) lose the use of `h`. Each is now refused by name at
`linear` and accepted at `affine`. -/

/-- The quantity of `h` in the four fixtures. -/
@[expose] public def heldQuantity : Quantity := .linear

/-- `λh. {meta = h; λx. x} 3`: applying a specification calls its extension and discards the
metadata (`Step.applySpecification`). -/
@[expose] public def specificationBody : Term := .app (.specification (.bound 0) (.lam (.bound 0))) (.nat 3)
@[expose] public def specificationDrop (q : Quantity) : AnnotatedTerm :=
  ⟨.lam specificationBody, fun p => if p = [] then some ⟨.natural, .natural, q, .once⟩
    else if p = [0, 0, 1] then some ⟨.natural, .natural, .unrestricted, .reusable⟩ else none, {}⟩

public theorem specification_drops_in_one_step :
    Step specificationBody (.app (.lam (.bound 0)) (.nat 3)) ∧
      occurrences 1 specificationBody = [1] ∧ occurrences 1 (.app (.lam (.bound 0)) (.nat 3)) = [0] :=
  ⟨.applySpecification _ _ _, by decide, by decide⟩

/-- TOOTH: the metadata of the specification at `[0, 0]` uses `h`. -/
public theorem specification_metadata_refused :
    (match checkAgainst (specificationDrop heldQuantity) [] (.arrow .once heldQuantity .natural .natural) with
      | .error (.linearMetadata [0, 0] 0) => true
      | _ => false) = true := by decide

#tooth specification_metadata_refused by mutation heldQuantity := .affine

public theorem specification_metadata_refused_by_check :
    (check (specificationDrop .linear) [] 16).isNone = true := by decide

/-- `λh. {a = h} with {a = 0}`: the extension overwrites the field holding `h` (`Step.extendRecord`). -/
@[expose] public def oneField : Ty := .field "a" .natural .emptyRow
@[expose] public def extendBody : Term := .extend (.record [("a", .bound 0)]) [("a", .nat 0)]
@[expose] public def extendDrop (q : Quantity) : AnnotatedTerm :=
  ⟨.lam extendBody, fun p => if p = [] then some ⟨.natural, overlay oneField oneField, q, .once⟩ else none, {}⟩

public theorem extend_drops_in_one_step :
    Step extendBody (.record [("a", .nat 0)]) ∧
      occurrences 1 extendBody = [1] ∧ occurrences 1 (.record [("a", .nat 0)]) = [0] :=
  ⟨.extendRecord _ _, by decide, by decide⟩

/-- TOOTH: the target of the extension at `[0]` uses `h`. -/
public theorem extend_overwrite_refused :
    (match checkAgainst (extendDrop heldQuantity) [] (.arrow .once heldQuantity .natural (overlay oneField oneField)) with
      | .error (.linearOverwritten [0] 0) => true
      | _ => false) = true := by decide

#tooth extend_overwrite_refused by mutation heldQuantity := .affine

/-- `λh. case l h of l x. 0`: the arm binds the payload `unrestricted` and drops it
(`Step.caseInject`). -/
@[expose] public def oneLabel : Ty := .variant (.field "l" .natural .emptyRow)
@[expose] public def caseBody : Term := .case (.inject "l" (.bound 0)) [("l", .nat 0)]
@[expose] public def caseDrop (q : Quantity) : AnnotatedTerm :=
  ⟨.lam caseBody, fun p => if p = [] then some ⟨.natural, .natural, q, .once⟩
    else if p = [0] then some ⟨oneLabel, .natural, .unrestricted, .reusable⟩ else none, {}⟩

public theorem case_drops_in_one_step :
    Step caseBody (.nat 0) ∧ occurrences 1 caseBody = [1] ∧ occurrences 1 (.nat 0) = [0] :=
  ⟨by simpa [caseBody, instantiate, Term.substitute] using Step.caseInject "l" (.bound 0) [("l", .nat 0)] (.nat 0) rfl,
    by decide, by decide⟩

/-- TOOTH: the scrutinee of the `case` at `[0]` uses `h`. -/
public theorem case_scrutinee_refused :
    (match checkAgainst (caseDrop heldQuantity) [] (.arrow .once heldQuantity .natural .natural) with
      | .error (.linearScrutinee [0] 0) => true
      | _ => false) = true := by decide

#tooth case_scrutinee_refused by mutation heldQuantity := .affine

/-- The same arm duplicating the payload, `case l h of l x. x + x`, is a copy of `h` in one step. -/
public theorem case_copies_in_one_step :
    Step (.case (.inject "l" (.bound 0)) [("l", .binary .add (.bound 0) (.bound 0))])
        (.binary .add (.bound 0) (.bound 0)) ∧
      occurrences 1 (.binary .add (.bound 0) (.bound 0)) = [2] :=
  ⟨by simpa [instantiate, Term.substitute] using
      Step.caseInject "l" (.bound 0) [("l", .binary .add (.bound 0) (.bound 0))] (.binary .add (.bound 0) (.bound 0)) rfl,
    by decide⟩

/-- `λh. case (done (l h)) of l x. done 0`, a sequencing `case`: `done` steps to its value, and the
plain `case` then drops it. Two steps; a fifth rule beside Gemini's four. -/
@[expose] public def activity (result : Ty) : Ty := .computation (.variant .emptyRow) .natural result
@[expose] public def doneBody : Term := .case (.done (.inject "l" (.bound 0))) [("l", .done (.nat 0))]
@[expose] public def doneDrop (q : Quantity) : AnnotatedTerm :=
  ⟨.lam doneBody, fun p => if p = [] then some ⟨.natural, activity .natural, q, .once⟩
    else if p = [0] then some ⟨activity oneLabel, activity .natural, .unrestricted, .reusable⟩ else none, {}⟩

public theorem done_drops_in_two_steps :
    Steps doneBody (.done (.nat 0)) ∧ occurrences 1 doneBody = [1] ∧ occurrences 1 (.done (.nat 0)) = [0] :=
  ⟨.next (.caseTarget _ (.done _)) (.next (by
      simpa [instantiate, Term.substitute] using
        Step.caseInject "l" (.bound 0) [("l", .done (.nat 0))] (.done (.nat 0)) rfl) (.refl _)),
    by decide, by decide⟩

/-- TOOTH: the value of the `done` at `[0, 0]` uses `h`. -/
public theorem done_value_refused :
    (match checkAgainst (doneDrop heldQuantity) [] (.arrow .once heldQuantity .natural (activity .natural)) with
      | .error (.linearReturned [0, 0] 0) => true
      | _ => false) = true := by decide

#tooth done_value_refused by mutation heldQuantity := .affine

/-- NOT A HOLE: `ifZero` and `ifBool` eliminate their scrutinee. `λh. ifZero h 0 (p. p + p)` is
accepted at `linear`: the test is the one use of `h`. `Step.successor` fires only at a literal, which
holds no hypothesis, and binds the predecessor, a fresh literal; `step_conserves_linear` covers both
rules with no new premise. -/
@[expose] public def ifZeroBody : Term := .ifZero (.bound 0) (.nat 0) (.binary .add (.bound 0) (.bound 0))
public theorem ifZero_scrutinee_accepted :
    (checkAgainst ⟨.lam ifZeroBody, fun p => if p = [] then some ⟨.natural, .natural, .linear, .once⟩ else none, {}⟩
      [] (.arrow .once .linear .natural .natural)).toBool = true := by decide

/-! ### Refusals that name their own clause (Kimi's review A) -/

/-- `λ(h : linear Nat). h + h`: overuse names the binder's quantity (it said `affine` for every one). -/
public theorem linear_overuse_named :
    (match checkAgainst ⟨.lam (.binary .add (.bound 0) (.bound 0)),
        fun p => if p = [] then some ⟨.natural, .natural, .linear, .once⟩ else none, {}⟩
        [] (.arrow .once .linear .natural .natural) with
      | .error (.binderOverused [] 0 .linear 2) => true
      | _ => false) = true := by decide

public theorem erased_use_named :
    (match checkAgainst ⟨.lam (.bound 0),
        fun p => if p = [] then some ⟨.natural, .natural, .erased, .once⟩ else none, {}⟩
        [] (.arrow .once .erased .natural .natural) with
      | .error (.binderOverused [] 0 .erased 1) => true
      | _ => false) = true := by decide

/-- An `affine` hypothesis passed to an `unrestricted` parameter of shareable type: the captures, not
the type, are what is not shareable (it said `notShareable` of the type). -/
public theorem unrestricted_argument_captures_named :
    (match checkAgainst ⟨.lam (.app (.lam (.bound 0)) (.bound 0)), fun p =>
        if p = [] then some ⟨.natural, .natural, .affine, .once⟩
        else if p = [0, 0] then some ⟨.natural, .natural, .unrestricted, .reusable⟩ else none, {}⟩
        [] (.arrow .once .affine .natural .natural) with
      | .error (.capturesNotShareable [0, 1]) => true
      | _ => false) = true := by decide

/-- An activity passed as an argument is `activityMisplaced` (it said `notShareable`). -/
public theorem activity_argument_named :
    (match checkAgainst ⟨.app (.lam (.nat 0)) (.done (.nat 0)), fun p =>
        if p = [0] then some ⟨activity .natural, .natural, .affine, .reusable⟩ else none, {}⟩
        [] .natural with
      | .error (.activityMisplaced [1] _) => true
      | _ => false) = true := by decide

/-- An empty record against a row with a field: expected the row, actual the empty row (the two were
reversed). -/
public theorem empty_fields_mismatch_ordered :
    (match checkAgainst ⟨.record [], fun p => if p = [] then some ⟨.emptyRow, oneField, .unrestricted, .reusable⟩
        else none, {}⟩ [] oneField with
      | .error (.typeMismatch [] expected actual) => expected == oneField && actual == .emptyRow
      | _ => false) = true := by decide

end Obend.Teeth.Core.LinearTeeth
