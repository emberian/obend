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
  generically in `T`; `compose_step_typed` is the first step of a chain, provenance read off each operand. So the no-refusal theorem
  (`Obend.Spec.Proofs.FrontEndAdequacy.accepted_never_refused`, statement unchanged) covers every
  program built from it; `twice_accepted` and `claim_spec_accepted` exhibit the surface programs the
  old metadata typing refused, and the teeth after them the refusals that stay.

Statements as in minidregg `Compiler/ObjectiveBendSpecificationClosure.lean` (commit 092027a2); the
reflection contract is minidregg docs/objective-bend/REFLECTION.md. An exposed-section leaf: nothing
imports it.
-/
public import Obend.Spec.FrontEnd
public meta import Obend.Spec.FrontEnd
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Term
public import Obend.AssertCompiled
public import Obend.Core.Proofs.Preservation.Base.Insert
public section
namespace Obend.Spec.Proofs.SpecificationClosure
open Lean (Json toJson)
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
  ⟨[(claimsVariable, .variant specClaimsRow), (metaVariable, .variant specMetaRow)], [claimsVariable, metaVariable], []⟩

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

theorem meta_conversion : sameType metaAssumptions (.variant specMetaRow) (.variable metaVariable) = true := by
  apply sameType_extends
  decide

/-- An operand's provenance has type `SpecMeta` (the bounded variable), with the operand's uses when it
is a specification and none otherwise. -/
theorem provenance_typed (T : Ty) {context : Context} {operand : Term} {uses : Uses} (b : Bool)
    (typed : PartialTyping metaAssumptions context operand (coreOperandTy T b) uses)
    (free : linearFree context uses = true) :
    PartialTyping metaAssumptions context (provenance b operand) (.variable metaVariable)
      (if b then uses else zeroUses context) := by
  cases b
  · exact .conversion (.inject (fuel := 4) (.record (.nil context)) (by decide) rfl) meta_conversion
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
    .conversion (.inject (fuel := 4) (.record (.cons inheritedTyped (.cons wrappingTyped (.nil context) rfl) rfl))
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

/-! ## Surface programs the old metadata typing refused, now accepted -/

open Obend.Spec.FrontEnd in
def acceptsSource (source entry : String) : Bool :=
  let m : SourceModule := ⟨"Probe", source, Sha256.hexString source, []⟩
  match FrontEnd.lower [m] 0 entry (Json.arr #[]) (Json.arr #[])
      (Json.mkObj [("heap", toJson "100000"), ("stack", toJson "100000"), ("ticks", toJson "100000")]) "definition" with
  | .ok l => (FrontEnd.accept l).toBool
  | .error _ => false

/-- The audit's witness (LTUO probe W01): `Specification<Nat>` is closed under compose. -/
def twiceSource : String :=
  "edition ObjectiveBend 1\n" ++
  "def twice(e: Extension<Nat>) -> Specification<Nat>:\n  compose(e, e)\n"

theorem twice_accepted : acceptsSource twiceSource "twice" = true := by native_decide

/-- LTUO probe W02: a spec with a claim inhabits `Specification<T>`. -/
def claimSpecSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  claim positive: self.n == 41n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

theorem claim_spec_accepted : acceptsSource claimSpecSource "asSpecification" = true := by native_decide

/-- Teeth: the refusal is not gone wholesale — a claim that is not Bool is still refused
(claims are checked code in their own knot field), and a spec at another target is
not a `Specification<Counter>`. -/
def badClaimSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  claim positive: self.n + 1n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

theorem non_boolean_claim_refused : acceptsSource badClaimSource "asSpecification" = false := by native_decide

/-- `law` is no longer a spec clause: it names an ENFORCED predicate (GPT-6 row G), and a
property nothing checks is a `claim`. The old spelling refuses at parse, never reinterpreted. -/
def lawKeywordSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  law positive: self.n == 41n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

theorem law_keyword_refused : acceptsSource lawKeywordSource "asSpecification" = false := by native_decide

def wrongTargetSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\nrecord Other:\n  n: Nat\n  m: Nat\n" ++
  "spec Start for Counter:\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Other>:\n  Start\n"

theorem wrong_target_refused : acceptsSource wrongTargetSource "asSpecification" = false := by native_decide

/-! ## The open inherited row of a closed spec (OB-LTUO LT2 D3)

`fix` over declared plain specs with a seed that is not a whole target instantiates each
layer at the row actually beneath it and discharges the target at the end. -/

def reviewSpecs : String :=
  "edition ObjectiveBend 1\nrecord Review:\n  review(value: Nat) -> Nat\n  twice(value: Nat) -> Nat\n" ++
  "spec Base for Review:\n  def review(value: Nat) -> Nat:\n    value + 1n\n" ++
  "spec Twice for Review:\n  requires review(value: Nat) -> Nat\n  def twice(value: Nat) -> Nat:\n    self.review(self.review(value))\n" ++
  "spec Augmented for Review:\n  def review(value: Nat) -> Nat:\n    super.review(value) + 1n\n"

/-- LTUO probe W05: no placeholder seed. -/
theorem empty_seed_accepted :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Base, Twice, Augmented), {}).twice(3n)\n") "run" = true := by
  native_decide

/-- A target member nobody provides is refused (W06's shape: Twice's requirement unmet). -/
theorem unprovided_requirement_refused :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Twice, Augmented), {}).twice(3n)\n") "run" = false := by
  native_decide

/-- A `super` read with nothing beneath it is refused. -/
theorem inherited_unprovided_refused :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Augmented, Base, Twice), {}).twice(3n)\n") "run" = false := by
  native_decide

/-- A requirement at another type than the target's member is refused (W07). -/
theorem requires_signature_refused :
    acceptsSource ("edition ObjectiveBend 1\nrecord R:\n  review(value: Nat) -> Nat\n" ++
      "spec S for R:\n  requires review(value: String) -> Nat\n  def review(value: Nat) -> Nat:\n    value\n" ++
      "def run() -> Nat:\n  fix(S, {}).review(1n)\n") "run" = false := by
  native_decide

/-! ## Open declarations over Self and Super (OB-LTUO LT2 step 3b) -/

def fourthFieldSource : String :=
  "edition ObjectiveBend 1\nrecord X:\n  x: Nat\nrecord XY:\n  x: Nat\n  y: Nat\n" ++
  "record XYZW:\n  x: Nat\n  y: Nat\n  z: Nat\n  w: Nat\n" ++
  "extension AddY[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:\n" ++
  "  extend(super, {y: 2n * self.x})\n" ++
  "extension AddZW(self: XYZW, super: XY) -> XYZW:\n  extend(super, {z: self.y, w: self.z + 1n})\n" ++
  "def run() -> Nat:\n  fix(compose(AddY, AddZW), {x: 5n}).w\n"

/-- An extension written over what it uses is reused at a self it never named (W09b). -/
theorem open_extension_reused_accepted : acceptsSource fourthFieldSource "run" = true := by native_decide

def heavierSpec : String :=
  "spec Heavier[Self has {weight: Nat, heavier(other: Self) -> Self}, Super has {weight: Nat}]:\n" ++
  "  def heavier(other: Self) -> Self:\n    if other.weight <= self.weight then self else other\n"

/-- An F-bounded binary method closes at a recursive record (W10). -/
theorem binary_self_accepted :
    acceptsSource ("edition ObjectiveBend 1\nrecord Node:\n  weight: Nat\n  heavier(other: Node) -> Node\n" ++
      heavierSpec ++ "def node(n: Nat) -> Node:\n  fix(Heavier, {weight: n})\n") "node" = true := by native_decide

/-- ... and is refused where the self's method has another type (the F-bound is discharged). -/
theorem f_bound_mismatch_refused :
    acceptsSource ("edition ObjectiveBend 1\nrecord Pair:\n  weight: Nat\n  heavier(other: Nat) -> Pair\n" ++
      heavierSpec ++ "def pair(n: Nat) -> Pair:\n  fix(Heavier, {weight: n})\n") "pair" = false := by native_decide

/-- A template is checked against its binder alone: reading an undeclared self member refuses. -/
theorem unbound_self_member_refused :
    acceptsSource ("edition ObjectiveBend 1\n" ++
      "extension Bad[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:\n" ++
      "  extend(super, {y: self.z})\ndef zero() -> Nat:\n  0n\n") "zero" = false := by native_decide

/-- The built-in module declaring `SpecMeta`/`SpecClaims` is Objective Bend source the
front end's own parser reads. -/
theorem builtin_parses : Elaborate.builtinModule.toBool = true := by native_decide

#assert_compiled twice_accepted
#assert_compiled claim_spec_accepted
#assert_compiled non_boolean_claim_refused
#assert_compiled law_keyword_refused
#assert_compiled wrong_target_refused
#assert_compiled builtin_parses
#assert_compiled empty_seed_accepted
#assert_compiled unprovided_requirement_refused
#assert_compiled inherited_unprovided_refused
#assert_compiled requires_signature_refused
#assert_compiled open_extension_reused_accepted
#assert_compiled binary_self_accepted
#assert_compiled f_bound_mismatch_refused
#assert_compiled unbound_self_member_refused
end Obend.Spec.Proofs.SpecificationClosure

end
