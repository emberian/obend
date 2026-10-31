module
/- `linear` separates from `affine` in the kernel (decided 2026-11-01; `lean/docs/REPORT-LINEAR-20261101.md`).

Two premises carry it. `PartialTyping.lambda` requires `Quantity.fits` of the parameter's own count,
so a `linear` binder is used exactly once; `argumentAllowed` requires `linearFree` of an argument
passed to a non-`linear` parameter, so a `linear` hypothesis is never handed to a callee that may
drop it (`erased`, `affine`) or share it (`unrestricted`). Both checkers name the refusal:
`linearBinderUnused` at the lambda, `linearArgumentDropped` at the argument.

Each tooth below is the same program at `affine` and at `linear`: accepted at one, refused at the
other, so the refusal is the quantity's and nothing else's. -/
public import Obend.Core.Bidirectional
public import Obend.Tactic.Tooth

namespace Obend.Teeth.Core.LinearTeeth
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
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

end Obend.Teeth.Core.LinearTeeth
