module
/-
# Obend.Spec.BidirectionalSurfaceElab — surface terms to checked core terms

A bidirectional elaborator from a named surface language to the core calculus of
`Obend.Core.Check`. The surface has what the front end's `Obend.Spec.Syntax.Expr` has and the core
does not: variables by name, `let`, annotations that may be left out where an expected type
supplies them, an effect performed by label, and a law asserted of a record.

`elabSurface` recurses on the surface term in one of two modes (Pierce and Turner 2000; Dunfield
and Krishnaswami 2021): `synthSurface` infers a type, `checkSurface` checks against one. An
expected type flows into a lambda's body, a `let`'s bound value, a call's argument and an effect's
payload; everywhere else the term synthesizes and the two types are compared by the core's
`sameType`. What comes back (`Elaborated`) is a core `Term` together with its `PartialTyping`
derivation, so the result is well typed by construction and no second checker is trusted.

Effects are rows. `perform ℓ payload` lowers to `.perform (.inject ℓ payload)`, whose core type is
an activity over the ambient plan row `env.planRow`; it elaborates only when `ℓ` is a label of
that row. A law is not a term: `law name inv subject` lowers to `subject` and leaves an
`Obligation` behind. `Residual` carries the obligations, in source order and one per annotation,
with the proof that each reads only fields its subject's row has.

Refusals are `Diagnostic`s naming what failed. The theorems at the end say when the unbound
variable, effect leak and linearity refusals fire.
-/
public import Obend.Spec.Syntax
public import Obend.Spec.Types
public import Obend.Spec.Law
public import Obend.Core.Bidirectional
public import Obend.Core.Ty
import all Obend.Core.Check
import all Obend.Core.Bidirectional

public section
namespace Obend.Spec.BidirectionalSurfaceElab
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
open Obend.Spec.Law (LawExpr)
open Obend.Spec.Types (PTy)
set_option autoImplicit false

/-! ## Surface terms -/

mutual
inductive Surface where
  | var (name : String)
  | nat (value : Nat)
  | bool (value : Bool)
  /-- `fun (param : quantity domain) => body`; the domain may be left to the expected type. -/
  | lam (param : String) (quantity : Quantity) (reuse : Reuse) (domain : Option Ty) (body : Surface)
  /-- `let name : type = value in body`; the type may be left to synthesis. -/
  | letE (name : String) (quantity : Quantity) (type : Option Ty) (value body : Surface)
  | record (fields : SurfaceFields)
  | member (target : Surface) (name : String)
  | extend (target : Surface) (fields : SurfaceFields)
  | call (callee argument : Surface)
  /-- Perform the effect `effect` of the ambient row with `payload`. -/
  | perform (effect : String) (payload : Surface)
  /-- Assert the law `invariant`, named `name`, of the record `subject`. -/
  | law (name : String) (invariant : LawExpr) (subject : Surface)
inductive SurfaceFields where
  | nil
  | cons (name : String) (value : Surface) (rest : SurfaceFields)
end

mutual
/-- The law annotations of a term, in source order. -/
def Surface.laws : Surface → List (String × LawExpr)
  | .var _ => []
  | .nat _ => []
  | .bool _ => []
  | .lam _ _ _ _ body => body.laws
  | .letE _ _ _ value body => value.laws ++ body.laws
  | .record fields => fields.laws
  | .member target _ => target.laws
  | .extend target fields => target.laws ++ fields.laws
  | .call callee argument => callee.laws ++ argument.laws
  | .perform _ payload => payload.laws
  | .law name invariant subject => (name, invariant) :: subject.laws
def SurfaceFields.laws : SurfaceFields → List (String × LawExpr)
  | .nil => []
  | .cons _ value rest => value.laws ++ rest.laws
end

mutual
/-- The effect row a term infers: every label it performs, in source order. -/
def Surface.effects : Surface → List String
  | .var _ => []
  | .nat _ => []
  | .bool _ => []
  | .lam _ _ _ _ body => body.effects
  | .letE _ _ _ value body => value.effects ++ body.effects
  | .record fields => fields.effects
  | .member target _ => target.effects
  | .extend target fields => target.effects ++ fields.effects
  | .call callee argument => callee.effects ++ argument.effects
  | .perform effect payload => effect :: payload.effects
  | .law _ _ subject => subject.effects
def SurfaceFields.effects : SurfaceFields → List String
  | .nil => []
  | .cons _ value rest => value.effects ++ rest.effects
end

def SurfaceFields.ofList : List (String × Surface) → SurfaceFields
  | [] => .nil
  | (name, value) :: rest => .cons name value (SurfaceFields.ofList rest)

/-! ## Diagnostics -/

/-- Why a surface term was refused. -/
inductive Diagnostic where
  | unboundVariable (name : String)
  /-- The binder `name` at `quantity` is used `count` times in its scope. -/
  | linearityViolation (name : String) (quantity : Quantity) (count : Nat)
  /-- A binder outside `name`'s scope is used more often than its quantity allows. -/
  | binderOverused (name : String)
  /-- A `linear` hypothesis reaches a position that would drop or share it. -/
  | linearEscapes (position : String)
  | capturesNotShareable (name : String)
  | notShareable (name : String) (type : Ty)
  | rowLabelMissing (label : String) (row : Ty)
  | duplicateLabel
  | notARow (type : Ty)
  | notAFunction (type : Ty)
  | typeMismatch (expected actual : Ty)
  | missingAnnotation (name : String)
  /-- The effect is not a label of the ambient effect row. -/
  | effectLeak (effect : String) (allowed : Ty)
  | effectRowNotData (row : Ty)
  /-- An activity where a value is required (an argument, a field, a bound value). -/
  | activityMisplaced (type : Ty)
  /-- The law `law` reads `field`, which its subject's row does not have. -/
  | lawOutsideRow (law : String) (field : String) (row : Ty)
  | unknownAnnotation (text : String)
  | unsupported (form : String)
  deriving Repr, DecidableEq

def need (premise : Bool) (diagnostic : Diagnostic) : Except Diagnostic (PLift (premise = true)) :=
  if h : premise = true then .ok ⟨h⟩ else .error diagnostic

/-! ## Environments, scopes and residuals -/

/-- What elaboration is relative to: the core assumptions, and the ambient effect signature (the
plan row an activity may yield from, and the type of a response). -/
structure Env where
  assumptions : Assumptions := {}
  planRow : Ty := .emptyRow
  response : Ty := .emptyRow

/-- Names in scope, innermost first, each with its core binding. -/
abbrev Scope := List (String × Binding)

/-- The core context a scope stands for. -/
abbrev context (scope : Scope) : Context := scope.map (·.2)

/-- The de Bruijn index of the innermost binder named `name`. -/
def resolve : Scope → String → Option Nat
  | [], _ => none
  | (bound, _) :: rest, name => if bound = name then some 0 else (resolve rest name).map (· + 1)

theorem resolve_sound (scope : Scope) (name : String) :
    ∀ index, resolve scope name = some index → ∃ binding, scope[index]? = some (name, binding) := by
  induction scope with
  | nil => intro index h; simp [resolve] at h
  | cons head rest ih =>
    intro index h
    simp only [resolve] at h
    by_cases same : head.1 = name
    · simp only [same, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨head.2, by simp [← same]⟩
    · simp only [same, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨inner, found, rfl⟩ := h
      obtain ⟨b, hb⟩ := ih inner found
      exact ⟨b, by simpa using hb⟩

/-- The innermost binder of a name wins. -/
example : resolve [("x", ⟨.natural, .linear⟩), ("y", ⟨.boolean, .unrestricted⟩),
    ("x", ⟨.boolean, .unrestricted⟩)] "x" = some 0 := by simp [resolve]

theorem resolve_none_iff : ∀ (scope : Scope) (name : String),
    resolve scope name = none ↔ ∀ binding, (name, binding) ∉ scope
  | [], _ => by simp [resolve]
  | (bound, binding) :: rest, name => by
    by_cases same : bound = name
    · subst same
      constructor
      · intro h; simp [resolve] at h
      · intro h; exact absurd (by simp) (h binding)
    · have ih := resolve_none_iff rest name
      simp only [resolve, same, ↓reduceIte, Option.map_eq_none_iff, ih, List.mem_cons,
        Prod.mk.injEq, not_or]
      constructor
      · intro h b
        exact ⟨fun e => same e.1.symm, h b⟩
      · intro h b
        exact (h b).2

/-- A residual proof obligation: the law, and the row type of the record it is asserted of. -/
structure Obligation where
  name : String
  invariant : LawExpr
  subject : Ty
  deriving Repr, DecidableEq

def Obligation.key (o : Obligation) : String × LawExpr := (o.name, o.invariant)

/-- Every field the law reads is a field of its subject's row. -/
def Obligation.Scoped (env : Env) (o : Obligation) : Prop :=
  ∀ field ∈ o.invariant.fields, ∃ member fuel,
    o.subject.lookup env.assumptions.bounds fuel field = some member

/-- The label is in the ambient effect row. -/
def EffectIn (env : Env) (effect : String) : Prop :=
  ∃ payload fuel, env.planRow.lookup env.assumptions.bounds fuel effect = some payload

/-- What elaborating a term with the law annotations `laws` and the effects `effects` leaves
behind: one obligation per annotation in order, each scoped, and every effect in the row. -/
structure Residual (env : Env) (laws : List (String × LawExpr)) (effects : List String) where
  obligations : List Obligation
  kept : obligations.map Obligation.key = laws
  inScope : ∀ o ∈ obligations, o.Scoped env
  contained : ∀ effect ∈ effects, EffectIn env effect

def Residual.nil {env : Env} : Residual env [] [] :=
  ⟨[], by simp, by simp, by simp⟩

def Residual.append {env : Env} {l₁ l₂ : List (String × LawExpr)} {e₁ e₂ : List String}
    (a : Residual env l₁ e₁) (b : Residual env l₂ e₂) : Residual env (l₁ ++ l₂) (e₁ ++ e₂) :=
  ⟨a.obligations ++ b.obligations, by rw [List.map_append, a.kept, b.kept],
    fun o h => (List.mem_append.1 h).elim (a.inScope o) (b.inScope o),
    fun effect h => (List.mem_append.1 h).elim (a.contained effect) (b.contained effect)⟩

def Residual.addLaw {env : Env} {l : List (String × LawExpr)} {e : List String}
    (a : Residual env l e) (o : Obligation) (reads : o.Scoped env) :
    Residual env (o.key :: l) e :=
  ⟨o :: a.obligations, by rw [List.map_cons, a.kept],
    fun o' h => by
      rcases List.mem_cons.1 h with same | later
      · rw [same]; exact reads
      · exact a.inScope o' later,
    a.contained⟩

def Residual.addEffect {env : Env} {l : List (String × LawExpr)} {e : List String}
    (a : Residual env l e) {effect : String} (allowed : EffectIn env effect) :
    Residual env l (effect :: e) :=
  ⟨a.obligations, a.kept, a.inScope,
    fun effect' h => by
      rcases List.mem_cons.1 h with same | later
      · rw [same]; exact allowed
      · exact a.contained effect' later⟩

/-- The payload type the ambient row gives the effect, if the row has it. -/
def effectAllowed (env : Env) (effect : String) : Option Ty :=
  lookupV env.assumptions.bounds [] env.planRow effect

theorem effectAllowed_sound {env : Env} {effect : String} {payload : Ty} :
    effectAllowed env effect = some payload →
    ∃ fuel, env.planRow.lookup env.assumptions.bounds fuel effect = some payload := by
  intro allowed
  exact (lookupV_iff _ _ _ _).1 allowed

/-- A row with a `log` action allows it, at its payload type. -/
example : effectAllowed { planRow := .field "log" .natural .emptyRow } "log" = some .natural := by
  decide +kernel

/-- The effect-leak refusal fires exactly on labels outside the row. -/
theorem effectAllowed_none_iff (env : Env) (effect : String) :
    effectAllowed env effect = none ↔ ¬ EffectIn env effect := by
  constructor
  · rintro refused ⟨payload, fuel, found⟩
    have : effectAllowed env effect = some payload := (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
    rw [refused] at this
    cases this
  · intro outside
    cases allowed : effectAllowed env effect with
    | none => rfl
    | some payload =>
      obtain ⟨fuel, found⟩ := effectAllowed_sound allowed
      exact absurd ⟨payload, fuel, found⟩ outside

/-- The first field a law reads that the subject's row lacks. -/
def lawScope (env : Env) (subject : Ty) (invariant : LawExpr) : Option String :=
  invariant.fields.find? fun field => (lookupV env.assumptions.bounds [] subject field).isNone

theorem lawScope_sound {env : Env} {subject : Ty} {invariant : LawExpr} (name : String) :
    lawScope env subject invariant = none → Obligation.Scoped env ⟨name, invariant, subject⟩ := by
  intro inScope field reads
  have present := (List.find?_eq_none.1 inScope) field reads
  cases found : lookupV env.assumptions.bounds [] subject field with
  | none => simp [found] at present
  | some member =>
    obtain ⟨fuel, h⟩ := (lookupV_iff _ _ _ _).1 found
    exact ⟨member, fuel, h⟩

/-- Whether every residual obligation's invariant holds of a state transition. -/
def obligationsHold (obligations : List Obligation) (facts : Law.Facts)
    (old : Option Obend.Core.Data.Data) (new : Obend.Core.Data.Data) : Bool :=
  obligations.all fun o => o.invariant.denote facts old new

/-! ## Elaborated terms -/

/-- A surface term elaborated: the core term, its type and uses, the typing derivation of exactly
that term, and what the term leaves to be discharged. -/
structure Elaborated (env : Env) (scope : Scope) (source : Surface) where
  term : Term
  type : Ty
  uses : Uses
  derivation : PartialTyping env.assumptions (context scope) term type uses
  residual : Residual env source.laws source.effects

structure ElaboratedFields (env : Env) (scope : Scope) (source : SurfaceFields) where
  fields : List (String × Term)
  row : Ty
  uses : Uses
  derivation : FieldsTyping env.assumptions (context scope) fields row uses
  residual : Residual env source.laws source.effects

/-- What a call is asked: synthesize a type, or check against one. -/
inductive Mode where
  | synth
  | check (expected : Ty)

def Mode.ofOption : Option Ty → Mode
  | none => .synth
  | some expected => .check expected

/-- The answer a mode asks for. -/
abbrev Result (env : Env) (scope : Scope) (source : Surface) : Mode → Type
  | .synth => Elaborated env scope source
  | .check expected => { e : Elaborated env scope source // e.type = expected }

def Result.toElaborated {env : Env} {scope : Scope} {source : Surface} :
    (mode : Mode) → Result env scope source mode → Elaborated env scope source
  | .synth, e => e
  | .check _, e => e.val

/-- The mode switch: a synthesized type meets an expected one through the core's conversion. -/
def finish {env : Env} {scope : Scope} {source : Surface} :
    (mode : Mode) → Elaborated env scope source → Except Diagnostic (Result env scope source mode)
  | .synth, e => .ok e
  | .check expected, e =>
    if agrees : sameType env.assumptions e.type expected = true then
      .ok ⟨⟨e.term, expected, e.uses, .conversion e.derivation agrees, e.residual⟩, rfl⟩
    else .error (.typeMismatch expected e.type)

/-- Where a lambda's domain and its body's mode come from: an expected arrow supplies both, an
annotation supplies the domain, and with neither the lambda is refused. -/
def lamPlan (param : String) (domain : Option Ty) : Mode → Except Diagnostic (Ty × Mode)
  | .check (.arrow _ _ expectedDomain codomain) => .ok (domain.getD expectedDomain, .check codomain)
  | _ =>
    match domain with
    | some annotated => .ok (annotated, .synth)
    | none => .error (.missingAnnotation param)

/-- Close a body over its binder: the core's lambda rule, each premise a named refusal. -/
def abstract {env : Env} {scope : Scope} (param : String) (quantity : Quantity) (reuse : Reuse)
    (domain : Ty) {body : Term} {codomain : Ty} {uses : Uses}
    (typed : PartialTyping env.assumptions (⟨domain, quantity⟩ :: context scope) body codomain uses) :
    Except Diagnostic (PLift (PartialTyping env.assumptions (context scope) (.lam body)
      (.arrow reuse quantity domain codomain) uses.tail)) := do
  let ⟨fits⟩ ← need (quantity.fits (uses.headD 0))
    (.linearityViolation param quantity (uses.headD 0))
  let ⟨safe⟩ ← need (safeUses (⟨domain, quantity⟩ :: context scope) uses) (.binderOverused param)
  let ⟨valid⟩ ← need (validContext env.assumptions.shareableVariables
    (⟨domain, quantity⟩ :: context scope)) (.notShareable param domain)
  let ⟨captures⟩ ← need (reusableAllowed env.assumptions reuse (context scope) uses.tail)
    (.capturesNotShareable param)
  pure ⟨.lambda (annotation := ⟨domain, codomain, quantity, reuse⟩) typed safe valid captures fits⟩

/-- Why an argument may not be passed: an activity is never an argument; otherwise a `linear`
hypothesis would reach a parameter that may drop or share it. -/
def argumentDiagnostic (position : String) (type : Ty) : Diagnostic :=
  if type.isComputation then .activityMisplaced type else .linearEscapes position

mutual
/-- Synthesis and checking, by the surface term's shape. -/
def elabSurface (env : Env) (scope : Scope) :
    (source : Surface) → (mode : Mode) → Except Diagnostic (Result env scope source mode)
  | .var name, mode =>
    match resolve scope name with
    | none => .error (.unboundVariable name)
    | some index =>
      match found : (context scope)[index]? with
      | none => .error (.unboundVariable name)
      | some binding =>
        finish mode ⟨.bound index, binding.type, variableUses (context scope) index, .bound found, .nil⟩
  | .nat value, mode =>
    finish mode ⟨.nat value, .natural, zeroUses (context scope), .natural _ value, .nil⟩
  | .bool value, mode =>
    finish mode ⟨.boolean value, .boolean, zeroUses (context scope), .boolean _ value, .nil⟩
  | .lam param quantity reuse domain body, mode => do
    let (binderType, bodyMode) ← lamPlan param domain mode
    let b := Result.toElaborated bodyMode
      (← elabSurface env ((param, ⟨binderType, quantity⟩) :: scope) body bodyMode)
    let ⟨typed⟩ ← abstract param quantity reuse binderType b.derivation
    finish mode ⟨.lam b.term, .arrow reuse quantity binderType b.type, b.uses.tail, typed, b.residual⟩
  | .letE name quantity type value body, mode => do
    let v := Result.toElaborated (Mode.ofOption type)
      (← elabSurface env scope value (Mode.ofOption type))
    let b ← elabSurface env ((name, ⟨v.type, quantity⟩) :: scope) body .synth
    let ⟨function⟩ ← abstract name quantity .once v.type b.derivation
    let ⟨allowed⟩ ← need (argumentAllowed env.assumptions quantity (context scope) v.type v.uses)
      (argumentDiagnostic name v.type)
    finish mode ⟨.app (.lam b.term) v.term, b.type, addUses b.uses.tail v.uses,
      .application (reuse := .once) (quantity := quantity) (domain := v.type) (codomain := b.type)
        function v.derivation rfl rfl allowed,
      v.residual.append b.residual⟩
  | .record fields, mode => do
    let fs ← elabFields env scope fields
    let ⟨distinct⟩ ← need (labelsDistinct fs.fields) .duplicateLabel
    finish mode ⟨.record fs.fields, fs.row, fs.uses, .record fs.derivation distinct, fs.residual⟩
  | .member target name, mode => do
    let t ← elabSurface env scope target .synth
    match found : lookupV env.assumptions.bounds [] t.type name with
    | none => .error (.rowLabelMissing name t.type)
    | some member => do
      let ⟨kept⟩ ← need (linearFree (context scope) t.uses) (.linearEscapes name)
      finish mode ⟨.get t.term name, member, t.uses,
        (by obtain ⟨fuel, h⟩ := (lookupV_iff _ _ _ _).1 found; exact .get t.derivation h kept),
        t.residual⟩
  | .extend target fields, mode => do
    let t ← elabSurface env scope target .synth
    let fs ← elabFields env scope fields
    let ⟨isRow⟩ ← need (isRowV env.assumptions.bounds [] t.type) (.notARow t.type)
    let ⟨distinct⟩ ← need (labelsDistinct fs.fields) .duplicateLabel
    let ⟨kept⟩ ← need (linearFree (context scope) t.uses) (.linearEscapes "extend")
    finish mode ⟨.extend t.term fs.fields, overlay fs.row t.type, addUses t.uses fs.uses,
      (by obtain ⟨fuel, h⟩ := (isRowV_iff _ _).1 isRow
          exact .extend t.derivation fs.derivation distinct h kept),
      t.residual.append fs.residual⟩
  | .call callee argument, mode => do
    let f ← elabSurface env scope callee .synth
    match shape : callable f.type with
    | .arrow reuse quantity domain codomain => do
      let a ← elabSurface env scope argument (.check domain)
      let ⟨allowed⟩ ← need (argumentAllowed env.assumptions quantity (context scope) a.val.type
        a.val.uses) (argumentDiagnostic "argument" a.val.type)
      finish mode ⟨.app f.term a.val.term, codomain, addUses f.uses a.val.uses,
        .application f.derivation a.val.derivation shape a.property allowed,
        f.residual.append a.val.residual⟩
    | _ => .error (.notAFunction f.type)
  | .perform effect payload, mode =>
    match allowed : effectAllowed env effect with
    | none => .error (.effectLeak effect env.planRow)
    | some payloadType => do
      let p ← elabSurface env scope payload (.check payloadType)
      let ⟨value⟩ ← need (!payloadType.isComputation) (.activityMisplaced payloadType)
      let ⟨plan⟩ ← need env.planRow.isData (.effectRowNotData env.planRow)
      let ⟨response⟩ ← need env.response.isData (.effectRowNotData env.response)
      finish mode ⟨.perform (.inject effect p.val.term),
        .computation (.variant env.planRow) env.response env.response, p.val.uses,
        (by
          obtain ⟨fuel, h⟩ := effectAllowed_sound allowed
          have typed := p.val.derivation
          rw [p.property] at typed
          exact .perform (.inject typed h (by simpa using value)) plan response),
        p.val.residual.addEffect
          (by obtain ⟨fuel, h⟩ := effectAllowed_sound allowed; exact ⟨payloadType, fuel, h⟩)⟩
  | .law name invariant subject, mode => do
    let t ← elabSurface env scope subject .synth
    match inScope : lawScope env t.type invariant with
    | some field => .error (.lawOutsideRow name field t.type)
    | none =>
      finish mode ⟨t.term, t.type, t.uses, t.derivation,
        t.residual.addLaw ⟨name, invariant, t.type⟩ (lawScope_sound name inScope)⟩
/-- Record fields, synthesized in source order. -/
def elabFields (env : Env) (scope : Scope) :
    (source : SurfaceFields) → Except Diagnostic (ElaboratedFields env scope source)
  | .nil => .ok ⟨[], .emptyRow, zeroUses (context scope), .nil _, .nil⟩
  | .cons name value rest => do
    let v ← elabSurface env scope value .synth
    let r ← elabFields env scope rest
    let ⟨isValue⟩ ← need (!v.type.isComputation) (.activityMisplaced v.type)
    pure ⟨(name, v.term) :: r.fields, .field name v.type r.row, addUses v.uses r.uses,
      .cons v.derivation r.derivation (by simpa using isValue), v.residual.append r.residual⟩
end

/-- Infer a type for a surface term. -/
def synthSurface (env : Env) (scope : Scope) (source : Surface) :
    Except Diagnostic (Elaborated env scope source) :=
  elabSurface env scope source .synth

/-- Check a surface term against a type. -/
def checkSurface (env : Env) (scope : Scope) (source : Surface) (expected : Ty) :
    Except Diagnostic { e : Elaborated env scope source // e.type = expected } :=
  elabSurface env scope source (.check expected)

/-- Both modes accept: a record synthesizes its row, and a numeral checks against `natural`. -/
example : (synthSurface {} [] (.record (.cons "balance" (.nat 10) .nil))).toOption.isSome = true := by
  decide +kernel

example : (checkSurface {} [] (.nat 3) .natural).toOption.isSome = true := by decide +kernel

/-! ## Soundness -/

/-- **Synthesis is sound.** An accepted term's core term is well typed at the synthesized type
in the scope's context; its obligations are its law annotations, one each and in order, each
reading only fields of its subject; and every effect it performs is in the ambient row. -/
theorem synthSurface_sound {env : Env} {scope : Scope} {source : Surface}
    {out : Elaborated env scope source} :
    synthSurface env scope source = .ok out →
    PartialTyping env.assumptions (context scope) out.term out.type out.uses ∧
      out.residual.obligations.map Obligation.key = source.laws ∧
      (∀ o ∈ out.residual.obligations, o.Scoped env) ∧
      (∀ effect ∈ source.effects, EffectIn env effect) :=
  fun _ => ⟨out.derivation, out.residual.kept, out.residual.inScope, out.residual.contained⟩

/-- **Checking is sound.** An accepted term's core term is well typed at the expected type. -/
theorem checkSurface_sound {env : Env} {scope : Scope} {source : Surface} {expected : Ty}
    {out : { e : Elaborated env scope source // e.type = expected }} :
    checkSurface env scope source expected = .ok out →
    PartialTyping env.assumptions (context scope) out.val.term expected out.val.uses ∧
      out.val.residual.obligations.map Obligation.key = source.laws ∧
      (∀ o ∈ out.val.residual.obligations, o.Scoped env) ∧
      (∀ effect ∈ source.effects, EffectIn env effect) := by
  intro _
  refine ⟨?_, out.val.residual.kept, out.val.residual.inScope, out.val.residual.contained⟩
  have typed := out.val.derivation
  rw [out.property] at typed
  exact typed

/-- **No law is dropped.** Every law annotation of an accepted term has its obligation. -/
theorem law_obligation_not_dropped {env : Env} {scope : Scope} {source : Surface}
    (out : Elaborated env scope source) {name : String} {invariant : LawExpr}
    (annotated : (name, invariant) ∈ source.laws) :
    ∃ o ∈ out.residual.obligations, o.name = name ∧ o.invariant = invariant := by
  rw [← out.residual.kept] at annotated
  obtain ⟨o, member, key⟩ := List.mem_map.1 annotated
  have parts := Prod.mk.inj key
  exact ⟨o, member, parts.1, parts.2⟩

/-- **Discharging the residue enforces the source.** If the obligations hold of a transition,
every law the source annotates holds of it. -/
theorem law_obligations_enforce {env : Env} {scope : Scope} {source : Surface}
    (out : Elaborated env scope source) (facts : Law.Facts)
    (old : Option Obend.Core.Data.Data) (new : Obend.Core.Data.Data)
    (discharged : obligationsHold out.residual.obligations facts old new = true)
    {name : String} {invariant : LawExpr} (annotated : (name, invariant) ∈ source.laws) :
    invariant.denote facts old new = true := by
  obtain ⟨o, member, _, same⟩ := law_obligation_not_dropped out annotated
  have holds := (List.all_eq_true.1 discharged) o member
  rw [← same]
  exact holds

/-- **Refusal completeness for effects.** A term that performs an effect outside the ambient row
is refused, wherever in the term the effect is. -/
theorem effect_leak_refused {env : Env} {scope : Scope} {source : Surface} {effect : String}
    (performed : effect ∈ source.effects) (outside : ¬ EffectIn env effect) :
    ∃ diagnostic, synthSurface env scope source = .error diagnostic := by
  cases result : synthSurface env scope source with
  | error diagnostic => exact ⟨diagnostic, rfl⟩
  | ok out => exact absurd (out.residual.contained effect performed) outside

/-- **Refusal completeness for laws.** A term whose law annotations cannot all be scoped has no
elaboration: there is no accepted result with an obligation that reads a missing field. -/
theorem unscoped_law_never_accepted {env : Env} {scope : Scope} {source : Surface}
    (out : Elaborated env scope source) {name : String} {invariant : LawExpr}
    (annotated : (name, invariant) ∈ source.laws) :
    ∃ subject, Obligation.Scoped env ⟨name, invariant, subject⟩ := by
  obtain ⟨o, member, sameName, sameInvariant⟩ := law_obligation_not_dropped out annotated
  refine ⟨o.subject, ?_⟩
  have reads := out.residual.inScope o member
  rw [← sameName, ← sameInvariant]
  exact reads

/-! ## Diagnostic honesty -/

/-- The unbound-variable refusal fires on every name no binder in scope has, in either mode. -/
theorem unbound_variable_refused (env : Env) (scope : Scope) (name : String) (mode : Mode)
    (unbound : resolve scope name = none) :
    elabSurface env scope (.var name) mode = .error (.unboundVariable name) := by
  rw [elabSurface.eq_def]
  simp only [unbound]

/-- The effect-leak refusal names the effect and the row it is missing from. -/
theorem effect_leak_refused_here (env : Env) (scope : Scope) (effect : String) (payload : Surface)
    (mode : Mode) (outside : effectAllowed env effect = none) :
    elabSurface env scope (.perform effect payload) mode =
      .error (.effectLeak effect env.planRow) := by
  rw [elabSurface.eq_def]
  simp only
  split
  · rfl
  · rename_i found
    rw [outside] at found
    cases found

/-- The linearity refusal fires whenever a binder's use count does not fit its quantity: a
`linear` binder dropped (count 0) or duplicated (count 2 or more) is refused by name. -/
theorem linearity_violation_refused {env : Env} {scope : Scope} (param : String)
    (quantity : Quantity) (reuse : Reuse) (domain : Ty) {body : Term} {codomain : Ty} {uses : Uses}
    (typed : PartialTyping env.assumptions (⟨domain, quantity⟩ :: context scope) body codomain uses)
    (misfit : quantity.fits (uses.headD 0) = false) :
    abstract (scope := scope) param quantity reuse domain typed =
      .error (.linearityViolation param quantity (uses.headD 0)) := by
  have refused : need (quantity.fits (uses.headD 0))
      (.linearityViolation param quantity (uses.headD 0)) =
      .error (.linearityViolation param quantity (uses.headD 0)) := by
    simp only [need, misfit, Bool.false_eq_true, ↓reduceDIte]
  unfold abstract
  rw [refused]
  rfl

/-- A `linear` binder fits exactly one use. -/
theorem linear_fits_iff (count : Nat) : Quantity.linear.fits count = true ↔ count = 1 := by
  simp [Quantity.fits]

/-! ## From the front end's AST -/

def quantityOf : String → Option Quantity
  | "erased" => some .erased
  | "affine" => some .affine
  | "linear" => some .linear
  | "unrestricted" => some .unrestricted
  | "default" => some .unrestricted
  | _ => none

def reuseOf : String → Option Reuse
  | "once" => some .once
  | "reusable" => some .reusable
  | _ => none

/-- A proposal type (`Obend.Spec.Types.PTy`, whose quantities are text) as a core type. -/
def ofPTy : PTy → Except Diagnostic Ty
  | .natural => .ok .natural
  | .boolean => .ok .boolean
  | .label => .ok .label
  | .emptyRow => .ok .emptyRow
  | .variable index => .ok (.variable index)
  | .arrow reuse parameter domain codomain =>
    match reuseOf reuse, quantityOf parameter with
    | some r, some q => do
      let d ← ofPTy domain
      let c ← ofPTy codomain
      pure (.arrow r q d c)
    | none, _ => .error (.unknownAnnotation reuse)
    | _, none => .error (.unknownAnnotation parameter)
  | .field name member tail => do
    let m ← ofPTy member
    let t ← ofPTy tail
    pure (.field name m t)
  | .specification metadata extension => do
    let m ← ofPTy metadata
    let e ← ofPTy extension
    pure (.specification m e)
  | .variant row => do
    let r ← ofPTy row
    pure (.variant r)
  | .computation plan response result => do
    let p ← ofPTy plan
    let r ← ofPTy response
    let a ← ofPTy result
    pure (.computation p r a)

/-- Type annotations of the front end, resolved through proposal types. -/
def resolveTypes (types : String → Option PTy) (text : String) : Option Ty :=
  match types text with
  | some proposal => (ofPTy proposal).toOption
  | none => none

/-- A decimal numeral's value, digit by digit. -/
def numeralValue : List Char → Nat → Option Nat
  | [], value => some value
  | digit :: rest, value =>
    if '0' ≤ digit ∧ digit ≤ '9' then numeralValue rest (value * 10 + (digit.toNat - '0'.toNat))
    else none

def numeral (text : String) : Option Nat :=
  match text.toList with
  | [] => none
  | digits => numeralValue digits 0

/-- The front end's expression as a surface term. `perform.ℓ(payload)` is the effect form. The
forms the core fragment here has no rule for are refused by name. -/
def ofSyntax (types : String → Option Ty) : Nat → Syntax.Expr → Except Diagnostic Surface
  | 0, _ => .error (.unsupported "nesting capacity")
  | _ + 1, .var name => .ok (.var name)
  | _ + 1, .nat value =>
    match numeral value with
    | some n => .ok (.nat n)
    | none => .error (.unsupported "numeral")
  | _ + 1, .bool value => .ok (.bool value)
  | fuel + 1, .record fields => do
    let fs ← fields.mapM fun field => do
      let value ← ofSyntax types fuel field.2
      pure (field.1, value)
    pure (.record (SurfaceFields.ofList fs))
  | fuel + 1, .extend inherited fields => do
    let target ← ofSyntax types fuel inherited
    let fs ← fields.mapM fun field => do
      let value ← ofSyntax types fuel field.2
      pure (field.1, value)
    pure (.extend target (SurfaceFields.ofList fs))
  | fuel + 1, .member target name => do
    let t ← ofSyntax types fuel target
    pure (.member t name)
  | fuel + 1, .call (.member (.var "perform") effect) [payload] => do
    let p ← ofSyntax types fuel payload
    pure (.perform effect p)
  | fuel + 1, .call callee args => do
    let f ← ofSyntax types fuel callee
    let arguments ← args.mapM (ofSyntax types fuel)
    pure (arguments.foldl Surface.call f)
  | fuel + 1, .closure params _ body => do
    let b ← ofSyntax types fuel body
    params.foldrM (fun param inner =>
      match quantityOf param.quantity with
      | some quantity => .ok (Surface.lam param.name quantity .reusable (types param.type) inner)
      | none => .error (.unknownAnnotation param.quantity)) b
  | fuel + 1, .letE name type value body => do
    let v ← ofSyntax types fuel value
    let b ← ofSyntax types fuel body
    pure (.letE name .unrestricted (types type) v b)
  | _ + 1, _ => .error (.unsupported "expression form")

/-- A contract's step under its law: the step is the subject, the law the assertion. -/
def ofContract (types : String → Option Ty) (contract : Syntax.ContractDecl) :
    Except Diagnostic Surface :=
  match contract.step, contract.law with
  | some step, some invariant => do
    let subject ← ofSyntax types 4096 step
    pure (.law contract.name invariant subject)
  | some step, none => ofSyntax types 4096 step
  | none, _ => .error (.unsupported "contract without a step")

end Obend.Spec.BidirectionalSurfaceElab

end
