module
/-
# Obend.Spec.Proofs.SpecificationClosure — `Specification<T>` is closed under `compose` (OB-LTUO LT1)

Every specification has the one public type `specification(SpecMeta, Extension<T>)`: `SpecMeta` is
first-order data (built-in sums `SpecMeta`/`SpecClaims`, `Obend.Spec.Elaborate.specMetaName`), so
neither a claim nor a composition changes the public type. Two levels are stated here:

* the front end's own type computation: `composeTy_closed` — composing two operands that are each
  `Specification<T>` or `Extension<T>` has type `Specification<T>`, for EVERY target `T` (symbolic);
* the Core4 typing relation: `compose_typed` — the term the elaborator lowers one `compose` step to,
  `specification (composed{inherited, wrapping}) (mix lower upper)` with no binder (`composeLowering`),
  has a `PartialTyping` derivation at every shareable target `T` and every operand kind, built
  generically in `T`; `compose_step_typed` is the first step of a chain, provenance read off each
  operand. So the no-refusal theorem (`Obend.Spec.Proofs.FrontEndAdequacy.accepted_never_refused`)
  covers every program built from it.

The compiled surface `.obend` acceptance and refusal vectors live in Tier-2A
`tests/extracted/SpecLawVectorsTest.lean`. Statements as in minidregg
`Compiler/ObjectiveBendSpecificationClosure.lean` (commit 092027a2).
-/
public import Obend.Spec.Types
public import Obend.Spec.Elaborate
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Term
public import Obend.Core.Proofs.Preservation.Base.Insert
public section
namespace Obend.Spec.Proofs.SpecificationClosure
open Obend.Core.Ty
open Obend.Core.Check
open Obend.Core.Term
open Obend.Core.Proofs.Preservation (reusable_add_uses)
open Obend.Spec.Types Obend.Spec.Elaborate
set_option autoImplicit false

/-! ## The front end's type computation -/

section FrontEnd

/-- An operand of `compose` at target `T`: a specification (any one metadata type) or a
bare extension. -/
def operandTy (metaTy T : PTy) : Bool → PTy
  | true => .specification metaTy (extensionTy T)
  | false => extensionTy T

theorem composeTy_closed (metaTy T : PTy) (left right : Bool) :
    composeTy metaTy (some (operandTy metaTy T left)) (some (operandTy metaTy T right)) =
      some (.specification metaTy (extensionTy T)) := by
  cases left <;> cases right <;> simp [composeTy, Obend.Spec.Types.callable, operandTy, extensionTy, arrowTy]

/-- Folding `compose(e₁, …, eₙ)` left to right stays at `Specification<T>`. -/
theorem composeTy_fold_closed (metaTy T : PTy) (first : Bool) (rest : List Bool) :
    rest.foldl (fun acc next => composeTy metaTy acc (some (operandTy metaTy T next)))
      (some (operandTy metaTy T first)) =
      (if rest.isEmpty then some (operandTy metaTy T first) else some (.specification metaTy (extensionTy T))) := by
  induction rest generalizing first with
  | nil => simp
  | cons next more ih =>
    rw [List.foldl_cons, composeTy_closed,
      show some (PTy.specification metaTy (extensionTy T)) = some (operandTy metaTy T true) from rfl, ih true]
    cases more <;> simp [operandTy]

end FrontEnd

/-! ## The Core4 checker accepts the compose lowering at every target -/

/-- Recursive-sum variables as the elaborator assigns them in a program whose first
specification metadata it resolves: `SpecClaims` is reached first (inside `declared`). -/
def claimsVariable : Nat := 1
def metaVariable : Nat := 2

def specClaimsRow : Ty :=
  .field "none" .emptyRow
    (.field "claim" (.field "name" .label (.field "status" .label (.field "rest" (.variable claimsVariable) .emptyRow)))
      .emptyRow)
def composedPayload : Ty :=
  .field "inherited" (.variable metaVariable) (.field "wrapping" (.variable metaVariable) .emptyRow)
def specMetaRow : Ty :=
  .field "declared" (.field "name" .label (.field "interface" .label (.field "claims" (.variable claimsVariable) .emptyRow)))
    (.field "composed" composedPayload (.field "extension" .emptyRow .emptyRow))
def metaAssumptions : Assumptions :=
  ⟨[(claimsVariable, .variant specClaimsRow), (metaVariable, .variant specMetaRow)], [claimsVariable, metaVariable], [], []⟩

def extTy (T : Ty) : Ty := .arrow .reusable .unrestricted T (.arrow .reusable .unrestricted T T)
def specTy (T : Ty) : Ty := .specification (.variable metaVariable) (extTy T)
def coreOperandTy (T : Ty) : Bool → Ty
  | true => specTy T
  | false => extTy T

/-- An operand's provenance, as the elaborator lowers it. -/
def provenance (isSpecification : Bool) (operand : Obend.Core.Term.Term) : Obend.Core.Term.Term :=
  if isSpecification then .metadata operand else .inject "extension" (.record [])

/-- One `compose` step as the elaborator lowers it (`Obend.Spec.Elaborate.composeStep`): the composite's
metadata `SpecMeta.composed{inherited, wrapping}` and its extension `mix lower upper`, with no binder. -/
def composeLowering (inherited wrapping lower upper : Term) : Term :=
  .specification (.inject "composed" (.record [("inherited", inherited), ("wrapping", wrapping)])) (.mix lower upper)

theorem shareableUnder_of_shareable (vars : List Nat) (type : Ty) (h : type.shareable = true) :
    type.shareableUnder vars = true := by
  induction type <;> simp_all [Ty.shareable, Ty.shareableUnder]

theorem metaAssumptions_valid : metaAssumptions.valid = true := by decide

theorem operand_shareable (T : Ty) (shareable : T.shareable = true) (b : Bool) :
    (coreOperandTy T b).shareableUnder metaAssumptions.shareableVariables = true := by
  have under := shareableUnder_of_shareable metaAssumptions.shareableVariables T shareable
  cases b <;> simp_all [coreOperandTy, specTy, extTy, Ty.shareableUnder, Ty.shareable, metaAssumptions, metaVariable, claimsVariable]

theorem operand_callable (T : Ty) (b : Bool) :
    callable (coreOperandTy T b) = .arrow .reusable .unrestricted T (.arrow .reusable .unrestricted T T) := by
  cases b <;> rfl

theorem meta_conversion : sameType metaAssumptions (.variant specMetaRow) (.variable metaVariable) = true :=
  sameType_symm (Obend.Core.EquiRecursiveAgreement.agrees_alias metaAssumptions metaVariable (.variant specMetaRow) rfl rfl)

/-- An operand's provenance has type `SpecMeta` (the bounded variable), with the operand's uses when it
is a specification and none otherwise. -/
theorem provenance_typed (T : Ty) {context : Context} {operand : Term} {uses : Uses} (b : Bool)
    (typed : PartialTyping metaAssumptions context operand (coreOperandTy T b) uses)
    (free : linearFree context uses = true) :
    PartialTyping metaAssumptions context (provenance b operand) (.variable metaVariable)
      (if b then uses else zeroUses context) := by
  cases b
  · exact .conversion (.inject (fuel := 4) (.record (.nil context) rfl) (by decide) rfl) meta_conversion
  · exact .metadata typed free

/-- The compose lowering is typable by the Core4 typing relation at EVERY shareable target `T`: two
operands at `Specification<T>` or `Extension<T>` whose captures are reusable, and two provenance terms
at `SpecMeta` that use no `linear` hypothesis, give a `Specification<T>` with the uses of all four.
The derivation is built here, generically in `T`. -/
theorem compose_typed (T : Ty) (shareable : T.shareable = true) {context : Context} (left right : Bool)
    {inherited wrapping lower upper : Term} {iu wu lu uu : Uses}
    (inheritedTyped : PartialTyping metaAssumptions context inherited (.variable metaVariable) iu)
    (wrappingTyped : PartialTyping metaAssumptions context wrapping (.variable metaVariable) wu)
    (lowerTyped : PartialTyping metaAssumptions context lower (coreOperandTy T left) lu)
    (upperTyped : PartialTyping metaAssumptions context upper (coreOperandTy T right) uu)
    (captures : reusableCaptures metaAssumptions.shareableVariables context (addUses lu uu) = true)
    (free : linearFree context (addUses iu (addUses wu (zeroUses context))) = true) :
    PartialTyping metaAssumptions context (composeLowering inherited wrapping lower upper) (specTy T)
      (addUses (addUses iu (addUses wu (zeroUses context))) (addUses lu uu)) := by
  have under := shareableUnder_of_shareable metaAssumptions.shareableVariables T shareable
  have metaTyped : PartialTyping metaAssumptions context
      (.inject "composed" (.record [("inherited", inherited), ("wrapping", wrapping)]))
      (.variable metaVariable) (addUses iu (addUses wu (zeroUses context))) :=
    .conversion (.inject (fuel := 4) (.record (.cons inheritedTyped (.cons wrappingTyped (.nil context) rfl) rfl) rfl)
      (by decide) rfl) meta_conversion
  have mixTyped : PartialTyping metaAssumptions context (.mix lower upper) (extTy T) (addUses lu uu) :=
    .mix lowerTyped upperTyped (operand_callable T left) (operand_callable T right) captures under under under
  exact .specification metaTyped mixTyped rfl rfl free

theorem zero_captures (variables : List Nat) : ∀ context : Context,
    reusableCaptures variables context (zeroUses context) = true
  | [] => rfl
  | _ :: rest => by
    have ih := zero_captures variables rest
    simp only [reusableCaptures, zeroUses, List.length_replicate, beq_self_eq_true, Bool.true_and,
      List.all_eq_true] at ih ⊢
    simpa [List.replicate_succ, List.zip] using ih

/-- The step the elaborator emits, with each provenance read off its own operand (the first step of a
chain; a later step reuses the previous step's metadata term, an instance of `compose_typed`). -/
theorem compose_step_typed (T : Ty) (shareable : T.shareable = true) {context : Context} (left right : Bool)
    {lower upper : Term} {lu uu : Uses}
    (lowerTyped : PartialTyping metaAssumptions context lower (coreOperandTy T left) lu)
    (upperTyped : PartialTyping metaAssumptions context upper (coreOperandTy T right) uu)
    (lowerCaptures : reusableCaptures metaAssumptions.shareableVariables context lu = true)
    (upperCaptures : reusableCaptures metaAssumptions.shareableVariables context uu = true) :
    ∃ uses, PartialTyping metaAssumptions context
      (composeLowering (provenance left lower) (provenance right upper) lower upper) (specTy T) uses := by
  have zero := zero_captures metaAssumptions.shareableVariables context
  have captures := reusable_add_uses _ _ _ _ lowerCaptures upperCaptures
  refine ⟨_, compose_typed T shareable left right
    (provenance_typed T left lowerTyped (linearFree_of_reusableCaptures lowerCaptures))
    (provenance_typed T right upperTyped (linearFree_of_reusableCaptures upperCaptures))
    lowerTyped upperTyped captures (linearFree_of_reusableCaptures (variables := metaAssumptions.shareableVariables) ?_)⟩
  cases left <;> cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    first
    | exact reusable_add_uses _ _ _ _ lowerCaptures (reusable_add_uses _ _ _ _ upperCaptures zero)
    | exact reusable_add_uses _ _ _ _ zero (reusable_add_uses _ _ _ _ upperCaptures zero)
    | exact reusable_add_uses _ _ _ _ lowerCaptures (reusable_add_uses _ _ _ _ zero zero)
    | exact reusable_add_uses _ _ _ _ zero (reusable_add_uses _ _ _ _ zero zero)

/-- Pure kernel inhabitedness witness for `compose_step_typed` (`T := .natural`, `left := false`,
`right := false`, identity extension `λ self super => super`). -/
theorem compose_step_typed_inhabited :
    let idExt : Term := .lam (.lam (.bound 0))
    ∃ uses, PartialTyping metaAssumptions []
      (composeLowering (provenance false idExt) (provenance false idExt) idExt idExt)
      (specTy .natural) uses := by
  let idExt : Term := .lam (.lam (.bound 0))
  let innerAnn : LambdaAnnotation :=
    { reuse := .reusable, parameter := .unrestricted, domain := .natural, codomain := .natural }
  let outerAnn : LambdaAnnotation :=
    { reuse := .reusable, parameter := .unrestricted, domain := .natural,
      codomain := .arrow .reusable .unrestricted .natural .natural }
  have hInner : PartialTyping metaAssumptions [⟨.natural, .unrestricted⟩, ⟨.natural, .unrestricted⟩]
      (.bound 0) .natural [1, 0] :=
    .bound (binding := ⟨.natural, .unrestricted⟩) rfl
  have hMid : PartialTyping metaAssumptions [⟨.natural, .unrestricted⟩]
      (.lam (.bound 0)) (.arrow .reusable .unrestricted .natural .natural) [0] :=
    .lambda (annotation := innerAnn) hInner rfl rfl rfl rfl
  have hId : PartialTyping metaAssumptions [] idExt (coreOperandTy .natural false) [] :=
    .lambda (annotation := outerAnn) hMid rfl rfl rfl rfl
  exact compose_step_typed .natural rfl false false hId hId rfl rfl

end Obend.Spec.Proofs.SpecificationClosure

end
