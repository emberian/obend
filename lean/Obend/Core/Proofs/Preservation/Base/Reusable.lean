module
/- Reusable terms and their combinators. -/
public import Obend.Core.MachineTyping
public import Obend.Core.RuntimeOrigins
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.TypeGraphHead
public import Obend.Core.Proofs.Adequacy.Defs
public import Obend.Core.Proofs.Adequacy.Scoped
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Check
namespace Obend.Core.Proofs.Preservation
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine Obend.Core.MachineTyping
set_option autoImplicit false

/-- A binder of a body with reusable captures is used only if `unrestricted`, so it fits every
quantity but `linear`, which demands one use. -/
public theorem reusable_binder_fits {variables : List Nat} {binding : Binding} {context : Context} {uses : Uses}
    (captures : reusableCaptures variables (binding :: context) uses = true) (notLinear : binding.quantity ≠ .linear) :
    binding.quantity.fits (uses.headD 0) = true := by
  cases uses with
  | nil => cases h : binding.quantity <;> simp_all [Quantity.fits]
  | cons head tail =>
      have facts : (head == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true := by
        simp only [reusableCaptures, Bool.and_eq_true, List.zip_cons_cons, List.all_cons] at captures
        exact captures.2.1
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at facts
      rcases facts with zero | ⟨unrestricted, _⟩
      · cases h : binding.quantity <;> simp_all [Quantity.fits]
      · simp [unrestricted, Quantity.fits]

public structure ReusableTerm (assumptions : Assumptions) (context : Context) (term : Term) (type : Ty) where
  uses : Uses
  derivation : PartialTyping assumptions context term type uses
  captures : reusableCaptures assumptions.shareableVariables context uses = true

@[expose] public def ReusableTerm.weaken {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty}
    (typed : ReusableTerm assumptions context term type) (binding : Binding)
    (valid : validContext assumptions.shareableVariables [binding] = true) :
    ReusableTerm assumptions (binding :: context) (term.rename Nat.succ) type :=
  ⟨0::typed.uses,source_weaken typed.derivation binding valid,
    by simpa only [List.insertIdx_zero] using reusable_captures_insert assumptions.shareableVariables context typed.uses 0 binding typed.captures (Nat.zero_le _)⟩

@[expose] public def ReusableTerm.«variable» {assumptions : Assumptions} {context : Context} {index : Nat} {binding : Binding}
    (found : context[index]? = some binding) (quantity : binding.quantity = .unrestricted)
    (shareable : binding.type.shareableUnder assumptions.shareableVariables = true) :
    ReusableTerm assumptions context (.bound index) binding.type :=
  ⟨variableUses context index,.bound found,reusable_variable found quantity shareable⟩

@[expose] public def ReusableTerm.apply {assumptions : Assumptions} {context : Context}
    {function argument : Term} {functionType domain codomain : Ty} {reuse : Reuse}
    (fn : ReusableTerm assumptions context function functionType) (arg : ReusableTerm assumptions context argument domain)
    (callableEq : callable functionType = .arrow reuse .unrestricted domain codomain)
    (shareable : domain.shareableUnder assumptions.shareableVariables = true) :
    ReusableTerm assumptions context (.app function argument) codomain :=
  ⟨addUses fn.uses arg.uses,.application fn.derivation arg.derivation callableEq rfl
    (by simpa [argumentAllowed,shareable,Ty.shareableUnder_not_computation _ _ shareable,
      linearFree_of_reusableCaptures arg.captures] using arg.captures),
    reusable_add_uses assumptions.shareableVariables context fn.uses arg.uses fn.captures arg.captures⟩

@[expose] public def ReusableTerm.abstraction {assumptions : Assumptions} {context : Context} {body : Term}
    {domain codomain : Ty} {quantity : Quantity}
    (bodyTyped : ReusableTerm assumptions (⟨domain,quantity⟩ :: context) body codomain)
    (valid : validContext assumptions.shareableVariables (⟨domain,quantity⟩ :: context) = true)
    (notLinear : quantity ≠ .linear := by decide) :
    ReusableTerm assumptions context (.lam body) (.arrow .reusable quantity domain codomain) :=
  ⟨bodyTyped.uses.tail,.lambda (annotation := ⟨domain,codomain,quantity,.reusable⟩) bodyTyped.derivation (reusable_uses_safe _ _ _ bodyTyped.captures) valid
    (by simpa [reusableAllowed] using reusable_tail bodyTyped.captures) (reusable_binder_fits bodyTyped.captures notLinear),
    reusable_tail bodyTyped.captures⟩

public theorem source_weaken_twice {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context term type uses) (first second : Binding)
    (firstValid : validContext assumptions.shareableVariables [first] = true)
    (secondValid : validContext assumptions.shareableVariables [second] = true) :
    PartialTyping assumptions (second :: first :: context) (term.rename (fun index => index+2)) type (0::0::uses) := by
  have shifted := source_weaken (source_weaken typed first firstValid) second secondValid
  have equation := Obend.Core.Proofs.Adequacy.scoped_rename_comp (source_scoped typed) Nat.succ Nat.succ
  simpa [equation,Nat.succ_eq_add_one,Nat.add_assoc] using shifted

theorem add_zero_uses (context : Context) (uses : Uses) (length : uses.length = context.length) :
    addUses uses (zeroUses context) = uses := by
  induction context generalizing uses with
  | nil => cases uses <;> simp_all [addUses,zeroUses]
  | cons binding context ih =>
      cases uses with
      | nil => simp at length
      | cons head tail =>
        have tailLength : tail.length = context.length := Nat.succ.inj length
        simpa [addUses,zeroUses,List.replicate_succ,List.zipWith] using congrArg (List.cons head) (ih tail tailLength)

public theorem add_uses_comm (first second : Uses) : addUses first second = addUses second first := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons head tail ih =>
      cases second with
      | nil => rfl
      | cons other rest =>
        simp only [addUses,List.zipWith]
        rw [Nat.add_comm head other]
        congr 1
        exact ih rest

@[expose] public def ReusableTerm.shiftTwo {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty}
    (typed : ReusableTerm assumptions context term type) (first second : Binding)
    (firstValid : validContext assumptions.shareableVariables [first] = true)
    (secondValid : validContext assumptions.shareableVariables [second] = true) :
    ReusableTerm assumptions (second :: first :: context) (term.rename (fun index => index+2)) type :=
  ⟨0::0::typed.uses,source_weaken_twice typed.derivation first second firstValid secondValid,
    by
      have once := reusable_captures_insert assumptions.shareableVariables context typed.uses 0 first typed.captures (Nat.zero_le _)
      simp only [List.insertIdx_zero] at once
      simpa only [List.insertIdx_zero] using
        reusable_captures_insert assumptions.shareableVariables (first :: context) (0::typed.uses) 0 second once (Nat.zero_le _)⟩

public theorem stack_convert_path {assumptions : Assumptions} {types : AddressTypes}
    {first last result : Ty} {stack : List Frame}
    (path : ConversionPath assumptions first last)
    (continuation : StackTyping assumptions types stack last result) :
    StackTyping assumptions types stack first result := by
  induction path with
  | refl => exact continuation
  | step prior agreement ih => exact ih (.conversion agreement continuation)

/-- Unresolved holes have no source typing derivation, including through conversion. -/
public theorem source_not_hole {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    ∀ n σ, term ≠ .hole n σ := by
  apply PartialTyping.rec
    (motive_1 := fun _ term _ _ _ => ∀ n σ, term ≠ .hole n σ)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := source)
  case conversion =>
    intro context term actual expected uses prior agreement ih
    obend_cases term with []
  all_goals (intros; simp_all)

/-- Variable source derivations disclose the actual environment binding even
when the authored result has crossed one or several row/alias conversions. -/
public theorem source_bound_assignment {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .bound index => ∃ binding, context[index]? = some binding ∧
        ConversionPath assumptions binding.type type
    | _ => True := by
  apply PartialTyping.rec
    (motive_1 := fun context term type _ _ => match term with
      | .bound index => ∃ binding, context[index]? = some binding ∧
          ConversionPath assumptions binding.type type
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := source)
  case bound =>
    intro context index binding found; exact ⟨binding,found,.refl binding.type⟩
  case conversion =>
    intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨binding,found,path⟩ := ih
    exact ⟨binding,found,.step path agreement⟩
  all_goals (intros; trivial)

public theorem safe_add_uses_right (context : Context) (first second : Uses)
    (firstLength : first.length = context.length) (secondLength : second.length = context.length)
    (safe : safeUses context (addUses first second) = true) : safeUses context second = true := by
  rw [add_uses_comm] at safe
  exact safe_add_uses_left context second first secondLength firstLength safe

end Obend.Core.Proofs.Preservation
