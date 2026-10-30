module
public import Obend.Core.Ty
public import Obend.Core.Term
public import Obend.AxiomPin
@[expose] public section
namespace Obend.Core.Check
open Obend.Core.Ty Obend.Core.Term
set_option autoImplicit false

structure Assumptions where
  bounds : Bounds := []
  shareableVariables : List Nat := []
  /-- Rigid variables (OB-LTUO LT2 D2): a template's `Self`, checked once against its
  declared bound. A rigid variable's bound is a LOWER bound: members are looked up
  through it (`Ty.lookup`, `Ty.isRow`), but it is never an alias, so no conversion
  equates the variable with its bound row. Emitted programs have `rigid = []`, where
  `alias` is `bounds.lookup` and the checker is the alias checker. -/
  rigid : List Nat := []

/-- The declared head a variable unfolds to in a conversion: its bound unless it is rigid. -/
def Assumptions.alias (assumptions : Assumptions) (index : Nat) : Option Ty :=
  if assumptions.rigid.contains index then none else assumptions.bounds.lookup index

theorem Assumptions.alias_bound {assumptions : Assumptions} {index : Nat} {bound : Ty}
    (found : assumptions.alias index = some bound) : assumptions.bounds.lookup index = some bound := by
  unfold Assumptions.alias at found
  split at found
  · cases found
  · exact found

theorem Assumptions.alias_of_rigid_nil {assumptions : Assumptions} (open_ : assumptions.rigid = [])
    (index : Nat) : assumptions.alias index = assumptions.bounds.lookup index := by
  simp [Assumptions.alias, open_]

theorem Assumptions.alias_rigid {assumptions : Assumptions} {index : Nat}
    (rigid : assumptions.rigid.contains index = true) : assumptions.alias index = none := by
  unfold Assumptions.alias; rw [if_pos rigid]

/-- More fuel never turns an accepted row into a refused one. -/
theorem Ty.isRow_mono {bounds : Bounds} : ∀ {fuel fuel' : Nat} {type : Ty},
    type.isRow bounds fuel = true → fuel ≤ fuel' → type.isRow bounds fuel' = true
  | 0, _, _, h, _ => by simp [Ty.isRow] at h
  | fuel + 1, fuel', type, h, le => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    cases type with
    | emptyRow => rfl
    | field _ _ tail => simp only [Ty.isRow] at h ⊢; exact Ty.isRow_mono h (by omega)
    | «variable» index =>
      simp only [Ty.isRow] at h ⊢
      split at h
      · exact Ty.isRow_mono h (by omega)
      · cases h
    | _ => simp [Ty.isRow] at h

/-- More fuel never changes a successful lookup. -/
theorem Ty.lookup_mono {bounds : Bounds} : ∀ {fuel fuel' : Nat} {type : Ty} {name : String} {member : Ty},
    type.lookup bounds fuel name = some member → fuel ≤ fuel' → type.lookup bounds fuel' name = some member
  | 0, _, _, _, _, h, _ => by simp [Ty.lookup] at h
  | fuel + 1, fuel', type, name, member, h, le => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    cases type with
    | field prior m tail =>
      simp only [Ty.lookup] at h ⊢
      split at h
      · rw [if_pos ‹_›]; exact h
      · rw [if_neg ‹_›]; exact Ty.lookup_mono h (by omega)
    | «variable» index =>
      simp only [Ty.lookup, Option.bind_eq_bind] at h ⊢
      cases found : bounds.lookup index with
      | none => simp [found] at h
      | some bound => simp only [found, Option.bind_some] at h ⊢; exact Ty.lookup_mono h (by omega)
    | _ => simp [Ty.lookup] at h

/-- Finite guarded shareability premises are checked from the declared bounds.
A recursive immutable row may refer to itself; a custody/once member rejects
its shareability even when hidden under that recursive row. -/
def Assumptions.valid (assumptions : Assumptions) : Bool :=
  assumptions.shareableVariables.all (fun index =>
    match assumptions.bounds.lookup index with
    | none => false
    | some bound => bound.shareableUnder assumptions.shareableVariables) &&
  -- No rigid variable names an activity, so a type agreement never turns an
  -- activity into a suspendable type or back (`Ty.isComputation` is invariant).
  assumptions.bounds.all (fun bound => !bound.2.isComputation)

/-- Annotated recursive aliases unfold one declared head only. This explicit
fragment supports the generated global-record knot without an arbitrary subtype
oracle or unrestricted recursive definitional conversion. An alias never names
an activity, so no agreement crosses between an activity and a suspendable type
(`sameType_isComputation`), whatever the bounds say. -/
def sameType (assumptions : Assumptions) (actual expected : Ty) : Bool :=
  actual.canonical == expected.canonical ||
    (match actual with
      | .variable index => !expected.isComputation &&
          (assumptions.alias index).map Ty.canonical == some expected.canonical
      | _ => false) ||
    (match expected with
      | .variable index => !actual.isComputation &&
          (assumptions.alias index).map Ty.canonical == some actual.canonical
      | _ => false)

theorem sameType_isComputation {assumptions : Assumptions} {actual expected : Ty}
    (agreement : sameType assumptions actual expected = true) :
    actual.isComputation = expected.isComputation := by
  simp only [sameType,Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasActual) | aliasExpected
  · rw [← Ty.canonical_isComputation actual, ← Ty.canonical_isComputation expected]
    simpa using congrArg Ty.isComputation (by simpa using canonical : actual.canonical = expected.canonical)
  · cases actual <;> simp at aliasActual
    simp_all [Ty.isComputation]
  · cases expected <;> simp at aliasExpected
    simp_all [Ty.isComputation]

/-- The checker converts an inferred type to a declared one only when the two
agree AND the conversion does not manufacture shareability. `Ty.canonical`
forgets a shadowed member (first-field shadowing), so a row hiding a custody or
a once closure behind a later field of the same name is canonically equal to a
row that is shareable; `sameType` alone would let such a value be bound
unrestricted and duplicated. Every conversion the checker inserts goes through
this; the relation `PartialTyping.conversion` keeps plain `sameType` because the
machine proofs rebuild conversions from canonical equality alone. -/
def agree (assumptions : Assumptions) (actual expected : Ty) : Bool :=
  sameType assumptions actual expected &&
    (!expected.shareableUnder assumptions.shareableVariables ||
      actual.shareableUnder assumptions.shareableVariables)

theorem agree_sameType {assumptions : Assumptions} {actual expected : Ty}
    (agreement : agree assumptions actual expected = true) :
    sameType assumptions actual expected = true :=
  (Bool.and_eq_true_iff.mp agreement).1

/-- A checked conversion never turns a non-shareable type into a shareable one. -/
theorem agree_shareable {assumptions : Assumptions} {actual expected : Ty}
    (agreement : agree assumptions actual expected = true)
    (expectedShareable : expected.shareableUnder assumptions.shareableVariables = true) :
    actual.shareableUnder assumptions.shareableVariables = true := by
  have second := (Bool.and_eq_true_iff.mp agreement).2
  simpa [expectedShareable] using second

/-- Source positions address the annotation of each actual lambda. Missing
annotations are refused, not guessed or silently replaced by Data types. An
injection's position carries the type of its constructor function: domain is
the declared payload type, codomain the declared variant; a sum type is never
guessed from one label. -/
abbrev Annotations := List Nat → Option LambdaAnnotation
structure AnnotatedTerm where
  term : Term
  annotations : Annotations
  assumptions : Assumptions := {}
def AnnotatedTerm.erase (source : AnnotatedTerm) : Term := source.term

def callable : Ty → Ty
  | .specification _ extension => callable extension
  | other => other

def reusableAllowed (assumptions : Assumptions) (reuse : Reuse)
    (context : Context) (uses : Uses) : Bool :=
  reuse != .reusable || reusableCaptures assumptions.shareableVariables context uses

/-- An argument becomes a shared heap thunk, so it is never an activity (rule
`effect-as-argument`); an unrestricted one must also be shareable. -/
def argumentAllowed (assumptions : Assumptions) (quantity : Quantity)
    (context : Context) (type : Ty) (uses : Uses) : Bool :=
  !type.isComputation && (quantity != .unrestricted ||
    (type.shareableUnder assumptions.shareableVariables &&
      reusableCaptures assumptions.shareableVariables context uses))

def overlay : Ty → Ty → Ty
  | .field name member rest, inherited => .field name member (overlay rest inherited)
  | _, inherited => inherited

def primitiveTypes : Primitive → Ty × Ty
  | .add | .multiply | .subtract | .divide | .modulo => (.natural, .natural)
  | .equal | .less | .lessEqual => (.natural, .boolean)
  | .conjunction => (.boolean, .boolean)
  | .labelEqual => (.label, .boolean)

def literalType (_value : String) : Ty := .label

mutual
/-- A derivation over the independent runtime syntax. This judges partial
computations only: Fix is not evaluated by Lean's definitional conversion. -/
inductive PartialTyping (assumptions : Assumptions) : Context → Term → Ty → Uses → Prop where
  | bound {context : Context} {index : Nat} {binding : Binding} :
      context[index]? = some binding →
      PartialTyping assumptions context (.bound index) binding.type (variableUses context index)
  | natural (context : Context) (value : Nat) :
      PartialTyping assumptions context (.nat value) .natural (zeroUses context)
  | boolean (context : Context) (value : Bool) :
      PartialTyping assumptions context (.boolean value) .boolean (zeroUses context)
  | label (context : Context) (value : String) :
      PartialTyping assumptions context (.label value) (literalType value) (zeroUses context)
  | lambda {context : Context} {body : Term} {annotation : LambdaAnnotation} {uses : Uses} :
      PartialTyping assumptions (⟨annotation.domain, annotation.parameter⟩ :: context)
        body annotation.codomain uses →
      safeUses (⟨annotation.domain, annotation.parameter⟩ :: context) uses = true →
      validContext assumptions.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: context) = true →
      reusableAllowed assumptions annotation.reuse context uses.tail = true →
      PartialTyping assumptions context (.lam body)
        (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain) uses.tail
  | conversion {context : Context} {term : Term} {actual expected : Ty} {uses : Uses} :
      PartialTyping assumptions context term actual uses → sameType assumptions actual expected = true →
      PartialTyping assumptions context term expected uses
  | application {context : Context} {function argument : Term} {functionType argumentType domain codomain : Ty}
      {functionUses argumentUses : Uses} {reuse : Reuse} {quantity : Quantity} :
      PartialTyping assumptions context function functionType functionUses →
      PartialTyping assumptions context argument argumentType argumentUses →
      callable functionType = .arrow reuse quantity domain codomain → argumentType = domain →
      argumentAllowed assumptions quantity context argumentType argumentUses = true →
      PartialTyping assumptions context (.app function argument) codomain (addUses functionUses argumentUses)
  | record {context : Context} {fields : List (String × Term)} {row : Ty} {uses : Uses} :
      FieldsTyping assumptions context fields row uses →
      PartialTyping assumptions context (.record fields) row uses
  | get {context : Context} {target : Term} {targetType member : Ty} {uses : Uses} {name : String} {fuel : Nat} :
      PartialTyping assumptions context target targetType uses →
      targetType.lookup assumptions.bounds fuel name = some member →
      PartialTyping assumptions context (.get target name) member uses
  | extend {context : Context} {target : Term} {fields : List (String × Term)}
      {targetType row : Ty} {targetUses fieldUses : Uses} {fuel : Nat} :
      PartialTyping assumptions context target targetType targetUses →
      FieldsTyping assumptions context fields row fieldUses →
      targetType.isRow assumptions.bounds fuel = true →
      PartialTyping assumptions context (.extend target fields) (overlay row targetType) (addUses targetUses fieldUses)
  | specification {context : Context} {metadata extension : Term} {metadataType extensionType : Ty} {mu eu : Uses} :
      PartialTyping assumptions context metadata metadataType mu →
      PartialTyping assumptions context extension extensionType eu →
      metadataType.isComputation = false → extensionType.isComputation = false →
      PartialTyping assumptions context (.specification metadata extension)
        (.specification metadataType extensionType) (addUses mu eu)
  | prototype {context : Context} {spec target : Term} {specType targetType : Ty} {su tu : Uses} :
      PartialTyping assumptions context spec specType su → PartialTyping assumptions context target targetType tu →
      specType.isComputation = false → targetType.isComputation = false →
      PartialTyping assumptions context (.prototype spec target) (.prototype specType targetType) (addUses su tu)
  | reflect {context : Context} {target : Term} {specType targetType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.prototype specType targetType) uses →
      PartialTyping assumptions context (.reflect target) specType uses
  | metadata {context : Context} {target : Term} {metadataType extensionType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.specification metadataType extensionType) uses →
      PartialTyping assumptions context (.metadata target) metadataType uses
  | project {context : Context} {target : Term} {specType targetType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.prototype specType targetType) uses →
      PartialTyping assumptions context (.project target) targetType uses
  | mix {context : Context} {lower upper : Term} {lowerType upperType self inherited middle provided : Ty} {lu uu : Uses} :
      PartialTyping assumptions context lower lowerType lu →
      PartialTyping assumptions context upper upperType uu →
      callable lowerType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle) →
      callable upperType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted middle provided) →
      reusableCaptures assumptions.shareableVariables context (addUses lu uu) = true →
      self.shareableUnder assumptions.shareableVariables = true →
      inherited.shareableUnder assumptions.shareableVariables = true →
      middle.shareableUnder assumptions.shareableVariables = true →
      PartialTyping assumptions context (.mix lower upper)
        (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) (addUses lu uu)
  | fix {context : Context} {spec inheritedTerm : Term} {specType inherited target : Ty} {su iu : Uses} :
      PartialTyping assumptions context spec specType su →
      callable specType = .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target) →
      PartialTyping assumptions context inheritedTerm inherited iu →
      target.shareableUnder assumptions.shareableVariables = true →
      argumentAllowed assumptions .unrestricted context inherited iu = true →
      reusableCaptures assumptions.shareableVariables context su = true →
      PartialTyping assumptions context (.fix spec inheritedTerm) target (addUses su iu)
  | binary {context : Context} {primitive : Primitive} {left right : Term} {input output : Ty} {lu ru : Uses} :
      primitiveTypes primitive = (input, output) →
      PartialTyping assumptions context left input lu → PartialTyping assumptions context right input ru →
      PartialTyping assumptions context (.binary primitive left right) output (addUses lu ru)
  | ifZero {context : Context} {value zero successor : Term} {result : Ty} {vu zu su : Uses} :
      PartialTyping assumptions context value .natural vu → PartialTyping assumptions context zero result zu →
      PartialTyping assumptions (⟨.natural,.unrestricted⟩ :: context) successor result su →
      safeUses (⟨.natural,.unrestricted⟩ :: context) su = true →
      PartialTyping assumptions context (.ifZero value zero successor) result (addUses vu (addUses zu su.tail))
  | inject {context : Context} {tag : String} {payload : Term} {payloadType row : Ty} {uses : Uses} {fuel : Nat} :
      PartialTyping assumptions context payload payloadType uses →
      row.lookup assumptions.bounds fuel tag = some payloadType →
      payloadType.isComputation = false →
      PartialTyping assumptions context (.inject tag payload) (.variant row) uses
  | case {context : Context} {scrutinee : Term} {arms : List (String × Term)} {row result : Ty} {su au : Uses} :
      PartialTyping assumptions context scrutinee (.variant row) su →
      ArmsTyping assumptions context arms row result au →
      PartialTyping assumptions context (.case scrutinee arms) result (addUses su au)
  | ifBool {context : Context} {condition whenTrue whenFalse : Term} {result : Ty} {cu tu fu : Uses} :
      PartialTyping assumptions context condition .boolean cu →
      PartialTyping assumptions context whenTrue result tu →
      PartialTyping assumptions context whenFalse result fu →
      PartialTyping assumptions context (.ifBool condition whenTrue whenFalse) result (addUses cu (addUses tu fu))
  /-- Yield a Plan (a sum of first-order actions); the response is data. -/
  | perform {context : Context} {plan : Term} {planType response : Ty} {uses : Uses} :
      PartialTyping assumptions context plan planType uses →
      planType.isPlan = true → response.isData = true →
      PartialTyping assumptions context (.perform plan) (.computation planType response response) uses
  /-- A pure value where an activity is expected. -/
  | done {context : Context} {value : Term} {planType response result : Ty} {uses : Uses} :
      PartialTyping assumptions context value result uses → result.isComputation = false →
      PartialTyping assumptions context (.done value) (.computation planType response result) uses
  /-- Sequencing: the activity's result selects an arm; every arm is an activity
  over the same plan/response types. This is the only `bind`. -/
  | effectCase {context : Context} {scrutinee : Term} {arms : List (String × Term)}
      {planType response row result : Ty} {su au : Uses} :
      PartialTyping assumptions context scrutinee (.computation planType response (.variant row)) su →
      ArmsTyping assumptions context arms row (.computation planType response result) au →
      result.isComputation = false →
      PartialTyping assumptions context (.case scrutinee arms) (.computation planType response result) (addUses su au)
inductive FieldsTyping (assumptions : Assumptions) : Context → List (String × Term) → Ty → Uses → Prop where
  | nil (context : Context) : FieldsTyping assumptions context [] .emptyRow (zeroUses context)
  | cons {context : Context} {name : String} {body : Term} {rest : List (String × Term)} {type row : Ty} {bu ru : Uses} :
      PartialTyping assumptions context body type bu → FieldsTyping assumptions context rest row ru →
      type.isComputation = false →
      FieldsTyping assumptions context ((name,body) :: rest) (.field name type row) (addUses bu ru)
/-- Arms in source order build a CLOSED row: with the scrutinee at that variant
row, every label has exactly the arm the machine's first-match lookup selects.
Each body binds the payload unrestricted (so its type must be shareable). -/
inductive ArmsTyping (assumptions : Assumptions) : Context → List (String × Term) → Ty → Ty → Uses → Prop where
  | nil (context : Context) (result : Ty) : ArmsTyping assumptions context [] .emptyRow result (zeroUses context)
  | cons {context : Context} {name : String} {body : Term} {rest : List (String × Term)} {payload row result : Ty} {bu ru : Uses} :
      PartialTyping assumptions (⟨payload,.unrestricted⟩ :: context) body result bu →
      safeUses (⟨payload,.unrestricted⟩ :: context) bu = true →
      payload.shareableUnder assumptions.shareableVariables = true →
      ArmsTyping assumptions context rest row result ru →
      ArmsTyping assumptions context ((name,body) :: rest) (.field name payload row) result (addUses bu.tail ru)
end

structure Inferred (assumptions : Assumptions) (context : Context) (term : Term) where
  type : Ty
  uses : Uses
  derivation : PartialTyping assumptions context term type uses
structure InferredFields (assumptions : Assumptions) (context : Context) (fields : List (String × Term)) where
  type : Ty
  uses : Uses
  derivation : FieldsTyping assumptions context fields type uses
structure InferredArms (assumptions : Assumptions) (context : Context) (arms : List (String × Term)) where
  row : Ty
  result : Ty
  uses : Uses
  derivation : ArmsTyping assumptions context arms row result uses

/-- The scrutinee's row guides arm binder types; one declared variable head
unfolds, as in sameType. The final sameType premise is what is trusted. -/
def variantRow (assumptions : Assumptions) : Ty → Option Ty
  | .variant row => some row
  | .variable index => match assumptions.alias index with
    | some (.variant row) => some row
    | _ => none
  | _ => none

mutual
/-- Fuel bounds only the checker, never the runtime or meaning of Fix. Failure
means outside this annotated fragment/budget; it is not a proof of ill-typing in
any stronger language. The result carries a runtime-syntax derivation. -/
def infer (assumptions : Assumptions) (annotations : Annotations) (context : Context)
    (position : List Nat) : Nat → (term : Term) → Option (Inferred assumptions context term)
  | 0, _ => none
  | fuel + 1, .bound index => do
      let binding ← context[index]?
      if h : context[index]? = some binding then
        some ⟨binding.type, variableUses context index, .bound h⟩ else none
  | _ + 1, .nat value => some ⟨.natural, zeroUses context, .natural context value⟩
  | _ + 1, .boolean value => some ⟨.boolean, zeroUses context, .boolean context value⟩
  | _ + 1, .label value => some ⟨literalType value, zeroUses context, .label context value⟩
  | fuel + 1, .lam body => do
      let annotation ← annotations position
      let result ← infer assumptions annotations (⟨annotation.domain, annotation.parameter⟩ :: context) (position ++ [0]) fuel body
      if ht : agree assumptions result.type annotation.codomain = true then
        if hs : safeUses (⟨annotation.domain, annotation.parameter⟩ :: context) result.uses = true then
          if hv : validContext assumptions.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: context) = true then
            if hc : reusableAllowed assumptions annotation.reuse context result.uses.tail = true then
              some ⟨.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain, result.uses.tail,
                .lambda (.conversion result.derivation (agree_sameType ht)) hs hv hc⟩
            else none
          else none
        else none
      else none
  | fuel + 1, .app function argument => do
      let fn ← infer assumptions annotations context (position ++ [0]) fuel function
      let arg ← infer assumptions annotations context (position ++ [1]) fuel argument
      match hft : callable fn.type with
      | .arrow reuse quantity domain codomain =>
          if hat : agree assumptions arg.type domain = true then
            if hc : argumentAllowed assumptions quantity context domain arg.uses = true then
              some ⟨codomain, addUses fn.uses arg.uses, .application fn.derivation (.conversion arg.derivation (agree_sameType hat)) hft rfl hc⟩
            else none
          else none
      | _ => none
  | fuel + 1, .record fields => do
      let result ← inferFields assumptions annotations context position 0 fuel fields
      some ⟨result.type, result.uses, .record result.derivation⟩
  | fuel + 1, .get target name => do
      let result ← infer assumptions annotations context (position ++ [0]) fuel target
      let member ← result.type.lookup assumptions.bounds (fuel + 1) name
      if hm : result.type.lookup assumptions.bounds (fuel + 1) name = some member then
        some ⟨member, result.uses, .get result.derivation hm⟩ else none
  | fuel + 1, .extend target fields => do
      let prior ← infer assumptions annotations context (position ++ [0]) fuel target
      let members ← inferFields assumptions annotations context (position ++ [1]) 0 fuel fields
      if hr : prior.type.isRow assumptions.bounds (fuel + 64) = true then
        some ⟨overlay members.type prior.type, addUses prior.uses members.uses,
          .extend prior.derivation members.derivation hr⟩ else none
  | fuel + 1, .specification metadata extension => do
      let descriptor ← infer assumptions annotations context (position ++ [0]) fuel metadata
      let body ← infer assumptions annotations context (position ++ [1]) fuel extension
      if hm : descriptor.type.isComputation = false then
        if he : body.type.isComputation = false then
          some ⟨.specification descriptor.type body.type, addUses descriptor.uses body.uses,
            .specification descriptor.derivation body.derivation hm he⟩
        else none
      else none
  | fuel + 1, .prototype spec target => do
      let code ← infer assumptions annotations context (position ++ [0]) fuel spec
      let value ← infer assumptions annotations context (position ++ [1]) fuel target
      if hs : code.type.isComputation = false then
        if ht : value.type.isComputation = false then
          some ⟨.prototype code.type value.type, addUses code.uses value.uses,
            .prototype code.derivation value.derivation hs ht⟩
        else none
      else none
  | fuel + 1, .reflect target => do
      let result ← infer assumptions annotations context (position ++ [0]) fuel target
      match ht : result.type with
      | .prototype specType targetType =>
          some ⟨specType, result.uses, .reflect (ht ▸ result.derivation)⟩
      | _ => none
  | fuel + 1, .metadata target => do
      let result ← infer assumptions annotations context (position ++ [0]) fuel target
      match ht : result.type with
      | .specification metadataType extensionType =>
          some ⟨metadataType, result.uses, .metadata (ht ▸ result.derivation)⟩
      | _ => none
  | fuel + 1, .project target => do
      let result ← infer assumptions annotations context (position ++ [0]) fuel target
      match ht : result.type with
      | .prototype specType targetType =>
          some ⟨targetType, result.uses, .project (ht ▸ result.derivation)⟩
      | _ => none
  | fuel + 1, .mix lower upper => do
      let first ← infer assumptions annotations context (position ++ [0]) fuel lower
      let second ← infer assumptions annotations context (position ++ [1]) fuel upper
      match ht : callable first.type, hs : callable second.type with
      | .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle),
        .arrow .reusable .unrestricted self' (.arrow .reusable .unrestricted middle' provided) =>
          if hc : self' = self then
            if hm : middle' = middle then
              if captures : reusableCaptures assumptions.shareableVariables context (addUses first.uses second.uses) = true then
                if shareSelf : self.shareableUnder assumptions.shareableVariables = true then
                  if shareInherited : inherited.shareableUnder assumptions.shareableVariables = true then
                    if shareMiddle : middle.shareableUnder assumptions.shareableVariables = true then
                      some ⟨.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided),
                        addUses first.uses second.uses,
                        .mix first.derivation second.derivation ht (by simpa [hc, hm] using hs)
                          captures shareSelf shareInherited shareMiddle⟩
                    else none
                  else none
                else none
              else none
            else none
          else none
      | _, _ => none
  | fuel + 1, .fix spec inheritedTerm => do
      let code ← infer assumptions annotations context (position ++ [0]) fuel spec
      let base ← infer assumptions annotations context (position ++ [1]) fuel inheritedTerm
      match ht : callable code.type with
      | .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited output) =>
          if ho : output = target then
            if hb : agree assumptions base.type inherited = true then
              if hs : target.shareableUnder assumptions.shareableVariables = true then
                if ha : argumentAllowed assumptions .unrestricted context inherited base.uses = true then
                  if hc : reusableCaptures assumptions.shareableVariables context code.uses = true then
                    some ⟨target, addUses code.uses base.uses,
                      .fix code.derivation (by simpa [ho] using ht) (.conversion base.derivation (agree_sameType hb)) hs ha hc⟩
                  else none
                else none
              else none
            else none
          else none
      | _ => none
  | fuel + 1, .binary primitive left right => do
      let l ← infer assumptions annotations context (position ++ [0]) fuel left
      let r ← infer assumptions annotations context (position ++ [1]) fuel right
      if hl : l.type = (primitiveTypes primitive).1 then
        if hr : r.type = (primitiveTypes primitive).1 then
          some ⟨(primitiveTypes primitive).2, addUses l.uses r.uses,
            .binary (Prod.eta _) (hl ▸ l.derivation) (hr ▸ r.derivation)⟩
        else none
      else none
  | fuel + 1, .ifZero value zero successor => do
      let condition ← infer assumptions annotations context (position ++ [0]) fuel value
      let z ← infer assumptions annotations context (position ++ [1]) fuel zero
      let s ← infer assumptions annotations (⟨.natural,.unrestricted⟩ :: context) (position ++ [2]) fuel successor
      if ht : condition.type = .natural then
        if hb : s.type = z.type then
          if hu : safeUses (⟨.natural,.unrestricted⟩ :: context) s.uses = true then
            some ⟨z.type, addUses condition.uses (addUses z.uses s.uses.tail),
              .ifZero (ht ▸ condition.derivation) z.derivation (hb ▸ s.derivation) hu⟩
          else none
        else none
      else none
  | fuel + 1, .inject tag payload => do
      let annotation ← annotations position
      let value ← infer assumptions annotations context (position ++ [0]) fuel payload
      if hk : annotation.parameter = .unrestricted ∧ annotation.reuse = .reusable then
        match annotation.codomain with
        | .variant row =>
            if hm : row.lookup assumptions.bounds (fuel + 1) tag = some annotation.domain then
              if hs : agree assumptions value.type annotation.domain = true then
                if hp : annotation.domain.isComputation = false then
                  some ⟨.variant row, value.uses, .inject (.conversion value.derivation (agree_sameType hs)) hm hp⟩
                else none
              else none
            else none
        | .variable index =>
          -- A recursive sum is declared as its bounded variable: inject at the
          -- bound's row, then convert to the variable (one declared head unfolds),
          -- so a nested injection already carries the sum's declared name.
          match assumptions.alias index with
          | some (.variant row) =>
            if hm : row.lookup assumptions.bounds (fuel + 1) tag = some annotation.domain then
              if hs : agree assumptions value.type annotation.domain = true then
                if hp : annotation.domain.isComputation = false then
                  if hc : sameType assumptions (.variant row) (.variable index) = true then
                    some ⟨.variable index, value.uses,
                      .conversion (.inject (.conversion value.derivation (agree_sameType hs)) hm hp) hc⟩
                  else none
                else none
              else none
            else none
          | _ => none
        | _ => none
      else none
  | fuel + 1, .case scrutinee arms => do
      let value ← infer assumptions annotations context (position ++ [0]) fuel scrutinee
      match value.type with
      | .computation _ _ produced =>
        let row ← variantRow assumptions produced
        let typed ← inferArms assumptions annotations context (position ++ [1]) 0 row none fuel arms
        match hr : typed.result with
        | .computation planType response result =>
          if hc : agree assumptions value.type (.computation planType response (.variant typed.row)) = true then
            if hn : result.isComputation = false then
              some ⟨.computation planType response result, addUses value.uses typed.uses,
                .effectCase (.conversion value.derivation (agree_sameType hc)) (hr ▸ typed.derivation) hn⟩
            else none
          else none
        | _ => none
      | _ =>
      let row ← variantRow assumptions value.type
      let typed ← inferArms assumptions annotations context (position ++ [1]) 0 row none fuel arms
      if hc : agree assumptions value.type (.variant typed.row) = true then
        some ⟨typed.result, addUses value.uses typed.uses, .case (.conversion value.derivation (agree_sameType hc)) typed.derivation⟩
      else none
  | fuel + 1, .ifBool condition whenTrue whenFalse => do
      let c ← infer assumptions annotations context (position ++ [0]) fuel condition
      let t ← infer assumptions annotations context (position ++ [1]) fuel whenTrue
      let f ← infer assumptions annotations context (position ++ [2]) fuel whenFalse
      if hc : c.type = .boolean then
        if hb : f.type = t.type then
          some ⟨t.type, addUses c.uses (addUses t.uses f.uses),
            .ifBool (hc ▸ c.derivation) t.derivation (hb ▸ f.derivation)⟩
        else none
      else none
  | fuel + 1, .perform plan => do
      -- The annotation at a perform's position is its effect signature:
      -- domain = the Plan sum, codomain = the response data type.
      let annotation ← annotations position
      let value ← infer assumptions annotations context (position ++ [0]) fuel plan
      if hs : agree assumptions value.type annotation.domain = true then
        if hp : annotation.domain.isPlan = true then
          if hr : annotation.codomain.isData = true then
            some ⟨.computation annotation.domain annotation.codomain annotation.codomain, value.uses,
              .perform (.conversion value.derivation (agree_sameType hs)) hp hr⟩
          else none
        else none
      else none
  | fuel + 1, .done inner => do
      -- The annotation at `done` names the activity's Plan and response types.
      let annotation ← annotations position
      let value ← infer assumptions annotations context (position ++ [0]) fuel inner
      if hn : value.type.isComputation = false then
        some ⟨.computation annotation.domain annotation.codomain value.type, value.uses,
          .done value.derivation hn⟩
      else none

def inferFields (assumptions : Assumptions) (annotations : Annotations) (context : Context)
    (position : List Nat) (index : Nat) : Nat → (fields : List (String × Term)) → Option (InferredFields assumptions context fields)
  | 0, _ => none
  | _ + 1, [] => some ⟨.emptyRow, zeroUses context, .nil context⟩
  | fuel + 1, (name,body) :: rest => do
      let first ← infer assumptions annotations context (position ++ [index]) fuel body
      let later ← inferFields assumptions annotations context position (index + 1) fuel rest
      if hc : first.type.isComputation = false then
        some ⟨.field name first.type later.type, addUses first.uses later.uses, .cons first.derivation later.derivation hc⟩
      else none

/-- Every arm body is checked under its label's payload type in the scrutinee
row; all arms must agree exactly on the result type. Empty arm lists have no
result type to infer and are refused here (the relation itself permits them). -/
def inferArms (assumptions : Assumptions) (annotations : Annotations) (context : Context)
    (position : List Nat) (index : Nat) (scrutineeRow : Ty) (expected : Option Ty) :
    Nat → (arms : List (String × Term)) → Option (InferredArms assumptions context arms)
  | 0, _ => none
  | _ + 1, [] => match expected with
    | some result => some ⟨.emptyRow, result, zeroUses context, .nil context result⟩
    | none => none
  | fuel + 1, (name,body) :: rest => do
      let payload ← scrutineeRow.lookup assumptions.bounds (fuel + 1) name
      if hs : payload.shareableUnder assumptions.shareableVariables = true then
        let first ← infer assumptions annotations (⟨payload,.unrestricted⟩ :: context) (position ++ [index]) fuel body
        if hu : safeUses (⟨payload,.unrestricted⟩ :: context) first.uses = true then
          let later ← inferArms assumptions annotations context position (index + 1) scrutineeRow (some first.type) fuel rest
          if hl : later.result = first.type then
            some ⟨.field name payload later.row, first.type, addUses first.uses.tail later.uses,
              .cons first.derivation hu hs (hl ▸ later.derivation)⟩
          else none
        else none
      else none
end

structure Checked (source : AnnotatedTerm) (context : Context) where
  type : Ty
  uses : Uses
  derivation : PartialTyping source.assumptions context source.erase type uses
  safe : safeUses context uses = true
  contextValid : validContext source.assumptions.shareableVariables context = true
  assumptionsValid : source.assumptions.valid = true

def check (source : AnnotatedTerm) (context : Context) (fuel : Nat) : Option (Checked source context) := do
  let result ← infer source.assumptions source.annotations context [] fuel source.term
  if hs : safeUses context result.uses = true then
    if hv : validContext source.assumptions.shareableVariables context = true then
      if ha : source.assumptions.valid = true then
        some ⟨result.type, result.uses, result.derivation, hs, hv, ha⟩ else none
    else none
  else none

/-- Successful checking constructs a derivation for exactly the consumed runtime
term, together with capture/usage premises. This is not preservation/adequacy. -/
theorem checked_erasure (source : AnnotatedTerm) (context : Context)
    (result : Checked source context) :
    PartialTyping source.assumptions context source.erase result.type result.uses := result.derivation

theorem partial_beta_law (body argument : Term) :
    Step (.app (.lam body) argument) (instantiate body argument) := .beta body argument

/-- Inherited/required/provided annotations all feed checking. Requirements are
finite structural row contracts, independently checked against future Self;
provider type is the heterogeneous two-arrow family, not a subtype oracle. -/
structure CheckedExtension (source : AnnotatedTerm) (context : Context)
    (family : ExtensionFamilies) (futureSelf : Ty) where
  checked : Checked source context
  shape : checked.type = family.functionType futureSelf
  required : futureSelf.supports source.assumptions.bounds 64 family.required = true

def checkExtension (source : AnnotatedTerm) (context : Context) (fuel : Nat)
    (family : ExtensionFamilies) (futureSelf : Ty) : Option (CheckedExtension source context family futureSelf) := do
  let result ← check source context fuel
  if ht : result.type = family.functionType futureSelf then
    if hr : futureSelf.supports source.assumptions.bounds 64 family.required = true then
      some ⟨result,ht,hr⟩ else none
  else none

/-- Reusability is justified by a checked capture premise, not by the immutable
shape of a closure/record wrapper. This holds for every lambda derivation. -/
theorem reusable_lambda_capture_rule {assumptions : Assumptions} {context : Context}
    {body : Term} {annotation : LambdaAnnotation} {uses : Uses}
    (_bodyTyped : PartialTyping assumptions (⟨annotation.domain,annotation.parameter⟩ :: context)
      body annotation.codomain uses)
    (_safe : safeUses (⟨annotation.domain,annotation.parameter⟩ :: context) uses = true)
    (_valid : validContext assumptions.shareableVariables (⟨annotation.domain,annotation.parameter⟩ :: context) = true)
    (captures : reusableAllowed assumptions annotation.reuse context uses.tail = true)
    (reusable : annotation.reuse = .reusable) :
    reusableCaptures assumptions.shareableVariables context uses.tail = true := by
  simpa [reusableAllowed, reusable] using captures

/-- Total logic proves a contextual reduction law despite the discarded
argument being any partial computation, including a divergent Fix. -/
theorem ignores_any_partial_argument (argument : Term) :
    Evaluates (.app (.lam (.nat 7)) argument) (.nat 7) :=
  by
    refine ⟨.next (.beta _ _) ?_, .natural 7⟩
    simpa [instantiate, Term.substitute] using (Steps.refl (.nat 7))

/-- A conversion never turns a non-shareable type shareable, whatever the rows. -/
theorem agree_never_manufactures_shareability (assumptions : Assumptions) (actual expected : Ty)
    (agreement : agree assumptions actual expected = true)
    (expectedShareable : expected.shareableUnder assumptions.shareableVariables = true) :
    actual.shareableUnder assumptions.shareableVariables = true :=
  agree_shareable agreement expectedShareable

/-! ## Activities: the plan and response types the activity teeth and proofs share -/
def planRow : Ty := .field "write" (.field "after" .natural .emptyRow) .emptyRow
def planType : Ty := .variant planRow
def responseType : Ty := .variant (.field "written" .emptyRow (.field "refused" .emptyRow .emptyRow))

/-- An activity is never shareable, so it is never a fix target, mix operand or
unrestricted binder either. -/
theorem computation_not_shareable (plan response result : Ty) (variables : List Nat) :
    (Ty.computation plan response result).shareableUnder variables = false := rfl

#assert_axioms agree_never_manufactures_shareability

end Obend.Core.Check

end