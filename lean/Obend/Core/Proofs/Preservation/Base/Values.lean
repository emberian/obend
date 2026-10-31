module
/- Runtime value forms and their callable types. -/
public import Obend.Core.MachineTyping
public import Obend.Core.RuntimeOrigins
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.TypeGraphHead
public import Obend.Core.Proofs.Adequacy.Defs
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Preservation.Base.Heads
namespace Obend.Core.Proofs.Preservation
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine Obend.Core.MachineTyping
set_option autoImplicit false

/- Structural conversion preserves graph head classes and relates actual
components. Exact canonical-head conversion is intentionally not asserted. -/

@[expose] public section
section StructuralRuntime
variable {assumptions : Assumptions}

public theorem canonical_same_type (assumptions : Assumptions) (first second : Ty)
    (agreement : first.canonical = second.canonical) : sameType assumptions first second = true := by
  exact (sameType_iff assumptions first second).mpr
    (Obend.Core.CanonicalExtension.of_canonical_eq
      (Obend.Core.EquiRecursiveAgreement.canonical_laws assumptions) agreement)

public abbrev CapturedFunction := Obend.Core.MachineTyping.Next.FunctionOrigin

@[expose] public def CapturedFunction.arrow {assumptions : Assumptions} {types : AddressTypes}
    {body : Term} {environment : Environment} (captured : CapturedFunction assumptions types body environment) : Ty :=
  Obend.Core.MachineTyping.Next.FunctionOrigin.arrow captured

public def RuntimeHead (assumptions : Assumptions) (value : RuntimeValue) (type : Ty) : Prop :=
  match value with
  | .natural _ => TypeGraph.labelHead ((TypeGraph.graph assumptions).label (.type type)) = .ordinary .natural
  | .boolean _ => TypeGraph.labelHead ((TypeGraph.graph assumptions).label (.type type)) = .ordinary .boolean
  | .label _ => TypeGraph.labelHead ((TypeGraph.graph assumptions).label (.type type)) = .ordinary .label
  | .closure _ _ => ∃ reuse quantity,
      TypeGraph.labelHead ((TypeGraph.graph assumptions).label (.type type)) = .ordinary (.arrow reuse quantity)
  | .record _ => TypeGraph.FiniteRow assumptions type
  | .specification _ _ => TypeGraph.labelHead ((TypeGraph.graph assumptions).label (.type type)) = .ordinary .specification
  | .prototype _ _ => TypeGraph.labelHead ((TypeGraph.graph assumptions).label (.type type)) = .ordinary .prototype
  | .variant _ _ => TypeGraph.labelHead ((TypeGraph.graph assumptions).label (.type type)) = .ordinary .variant

theorem runtimeHead_transport {value : RuntimeValue} {actual expected : Ty}
    (related : TypeGraph.Equivalent assumptions actual expected)
    (origin : RuntimeHead assumptions value actual) : RuntimeHead assumptions value expected := by
  have heads := TypeGraph.equivalent_head related
  cases value with
  | record fields => exact (TypeGraph.equivalent_finite_row_iff related).mp origin
  | closure body environment =>
    obtain ⟨reuse,quantity,shape⟩ := origin
    exact ⟨reuse,quantity,heads.symm.trans shape⟩
  | natural n | boolean n | label n | specification n m | prototype n m | variant n m =>
    exact heads.symm.trans origin


theorem value_head_correct {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) : RuntimeHead assumptions value type := by
  induction typed with
  | natural value | boolean value | label value =>
    simp [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
      AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag]
  | closure env source safe valid captures =>
    rename_i body environment context annotation uses
    refine ⟨annotation.reuse,annotation.parameter,?_⟩
    simp [TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,
      AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag]
  | record isRow members => exact isRow
  | specification metadata ext | prototype metadata ext | variant metadata ext path =>
    simp [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,
      AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag]
  | conversion prior converted ih => exact runtimeHead_transport ((sameType_iff assumptions _ _).mp converted) ih

/-- This syntactic discriminator is used only for direct runtime constructors,
not to normalize aliases or decide semantic row equality. -/
public def rowSyntax : Ty → Bool
  | .variable _ | .field _ _ _ | .emptyRow => true
  | _ => false

/-- The `*_value_form` arms below pass this instantiated (`finiteRow_nonrow (type := …) rfl`): Lean
v4.35's simp discharger proves `rowSyntax t = false` for a constructor `t` but then fails to assign
the proof to the hypothesis (`failed to assign proof`), so the conditional rewrite never fires. -/
theorem finiteRow_nonrow {type : Ty} (nonrow : rowSyntax type = false) :
    TypeGraph.FiniteRow assumptions type ↔ False := by
  constructor
  · rintro ⟨fuel,finite⟩
    cases fuel <;> cases type <;> simp_all [rowSyntax,Ty.isRow]
  · intro impossible; exact False.elim impossible

theorem natural_value_form {types : AddressTypes} {value : RuntimeValue}
    (typed : ValueTyping assumptions types value .natural) :
    ∃ number, value = .natural number := by
  have shape := value_head_correct typed
  obend_cases value with [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
    AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag,
    rowSyntax,finiteRow_nonrow (type := .natural) rfl]

theorem boolean_value_form {types : AddressTypes} {value : RuntimeValue}
    (typed : ValueTyping assumptions types value .boolean) :
    ∃ boolean, value = .boolean boolean := by
  have shape := value_head_correct typed
  obend_cases value with [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
    AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag,
    rowSyntax,finiteRow_nonrow (type := .boolean) rfl]

theorem label_value_form {types : AddressTypes} {value : RuntimeValue}
    (typed : ValueTyping assumptions types value .label) :
    ∃ name, value = .label name := by
  have shape := value_head_correct typed
  obend_cases value with [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
    AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag,
    rowSyntax,finiteRow_nonrow (type := .label) rfl]

theorem specification_value_form {types : AddressTypes} {value : RuntimeValue} {metadataType extensionType : Ty}
    (typed : ValueTyping assumptions types value (.specification metadataType extensionType)) :
    ∃ metadata extension, value = .specification metadata extension := by
  have shape := value_head_correct typed
  obend_cases value with [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
    AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag,
    rowSyntax,finiteRow_nonrow (type := (.specification metadataType extensionType)) rfl]

theorem prototype_value_form {types : AddressTypes} {value : RuntimeValue} {specType targetType : Ty}
    (typed : ValueTyping assumptions types value (.prototype specType targetType)) :
    ∃ spec target, value = .prototype spec target := by
  have shape := value_head_correct typed
  obend_cases value with [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
    AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag,
    rowSyntax,finiteRow_nonrow (type := (.prototype specType targetType)) rfl]

theorem variant_value_form {types : AddressTypes} {value : RuntimeValue} {row : Ty}
    (typed : ValueTyping assumptions types value (.variant row)) :
    ∃ tag address, value = .variant tag address := by
  have shape := value_head_correct typed
  obend_cases value with [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
    AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag,
    rowSyntax,finiteRow_nonrow (type := (.variant row)) rfl]

theorem closure_value_form {types : AddressTypes} {value : RuntimeValue} {reuse : Reuse} {quantity : Quantity} {domain codomain : Ty}
    (typed : ValueTyping assumptions types value (.arrow reuse quantity domain codomain)) :
    ∃ body environment, value = .closure body environment := by
  have shape := value_head_correct typed
  obend_cases value with [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
    AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag,
    rowSyntax,finiteRow_nonrow (type := (.arrow reuse quantity domain codomain)) rfl]

theorem value_typed_not_computation {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) : type.isComputation = false := by
  cases type with
  | computation plan response result =>
    have shape := value_head_correct typed
    obend_cases value with [RuntimeHead,TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,literalType,
      AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag,
      rowSyntax,finiteRow_nonrow (type := (.computation plan response result)) rfl]
  | _ => rfl

theorem value_specification_fields {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ metadata extension, value = .specification metadata extension →
      ∃ metadataType extensionType,
        types[metadata]? = some metadataType ∧ types[extension]? = some extensionType ∧
        sameType assumptions (.specification metadataType extensionType) type = true := by
  intro metadata extension same
  obtain ⟨metadataType,extensionType,assignedMetadata,assignedExtension,related⟩ :=
    Obend.Core.MachineTyping.Next.value_specification_origin
      (fun a b h => (sameType_iff assumptions a b).mp h) typed metadata extension same
  exact ⟨metadataType,extensionType,assignedMetadata,assignedExtension,(sameType_iff assumptions _ _).mpr related⟩

theorem value_prototype_fields {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ spec target, value = .prototype spec target →
      ∃ specType targetType,
        types[spec]? = some specType ∧ types[target]? = some targetType ∧
        sameType assumptions (.prototype specType targetType) type = true := by
  intro spec target same
  obtain ⟨specType,targetType,assignedSpec,assignedTarget,related⟩ :=
    Obend.Core.MachineTyping.Next.value_prototype_origin
      (fun a b h => (sameType_iff assumptions a b).mp h) typed spec target same
  exact ⟨specType,targetType,assignedSpec,assignedTarget,(sameType_iff assumptions _ _).mpr related⟩

theorem value_closure_fields {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ body environment, value = .closure body environment →
      ∃ origin : Obend.Core.MachineTyping.Next.FunctionOrigin assumptions types body environment,
        sameType assumptions origin.arrow type = true := by
  intro body environment same
  obtain ⟨origin,related⟩ := Obend.Core.MachineTyping.Next.value_closure_origin
    (fun a b h => (sameType_iff assumptions a b).mp h) typed body environment same
  exact ⟨origin,(sameType_iff assumptions _ _).mpr related⟩

theorem computation_same_type_inj {plan response result plan' response' result' : Ty}
    (converted : sameType assumptions (.computation plan response result)
      (.computation plan' response' result') = true) :
    sameType assumptions plan plan' = true ∧ sameType assumptions response response' = true ∧
      sameType assumptions result result' = true := by
  obtain ⟨plans,responses,results⟩ := TypeGraph.computation_components ((sameType_iff assumptions _ _).mp converted)
  exact ⟨(sameType_iff assumptions _ _).mpr plans,(sameType_iff assumptions _ _).mpr responses,(sameType_iff assumptions _ _).mpr results⟩

/-- Structural agreement with an activity exposes an actual activity on the
other side and relates its components separately. No canonical identity follows. -/
theorem sameType_activity_components {actual expected plan response produced : Ty}
    (converted : sameType assumptions actual expected = true)
    (source : actual = .computation plan response produced) :
    ∃ plan' response' produced', expected = .computation plan' response' produced' ∧
      sameType assumptions plan plan' = true ∧ sameType assumptions response response' = true ∧
      sameType assumptions produced produced' = true := by
  subst actual
  have activity := TypeGraph.equivalent_isComputation ((sameType_iff assumptions _ _).mp converted)
  cases expected with
  | computation plan' response' produced' =>
    obtain ⟨plans,responses,results⟩ := computation_same_type_inj converted
    exact ⟨plan',response',produced',rfl,plans,responses,results⟩
  | _ => simp [Ty.isComputation] at activity

theorem callable_value_form {types : AddressTypes} {value : RuntimeValue}
    {functionType domain codomain : Ty} {reuse : Reuse} {quantity : Quantity}
    (typed : ValueTyping assumptions types value functionType)
    (callableEq : callable functionType = .arrow reuse quantity domain codomain) :
    (∃ body environment, value = .closure body environment) ∨
      (∃ metadata extension, value = .specification metadata extension) := by
  cases functionType with
  | arrow r q d c => exact Or.inl (closure_value_form typed)
  | specification metadata extension => exact Or.inr (specification_value_form typed)
  | _ => simp [callable] at callableEq

public theorem closure_callable_type {functionType : Ty}
    {reuse actualReuse : Reuse} {quantity actualQuantity : Quantity}
    {domain codomain actualDomain actualCodomain : Ty}
    (related : TypeGraph.Equivalent assumptions (.arrow actualReuse actualQuantity actualDomain actualCodomain) functionType)
    (callableEq : callable functionType = .arrow reuse quantity domain codomain) :
    functionType = .arrow reuse quantity domain codomain := by
  cases functionType with
  | arrow r q d c => exact callableEq
  | specification metadata extension =>
    have heads := TypeGraph.equivalent_head related
    simp [TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,
      AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag] at heads
  | _ => simp [callable] at callableEq

theorem specification_callable_type {functionType : Ty}
    {reuse : Reuse} {quantity : Quantity} {domain codomain metadata extension : Ty}
    (related : TypeGraph.Equivalent assumptions (.specification metadata extension) functionType)
    (callableEq : callable functionType = .arrow reuse quantity domain codomain) :
    ∃ metadataType extensionType, functionType = .specification metadataType extensionType := by
  cases functionType with
  | specification metadata extension => exact ⟨metadata,extension,rfl⟩
  | arrow r q d c =>
    have heads := TypeGraph.equivalent_head related
    simp [TypeGraph.graph,TypeGraph.observe,TypeGraph.labelHead,
      AliasExposure.expose,AliasExposure.exposeWalk,AliasExposure.constructorHead,TypeGraph.rowTag] at heads
  | _ => simp [callable] at callableEq

/-- Activity continuations retain their own component representatives. The
incoming produced type agrees with the arm row; it need not canonicalize to it. -/
theorem stack_effect_case {types : AddressTypes} {stack : List Frame} {input result : Ty}
    (typed : StackTyping assumptions types stack input result) :
    ∀ arms environment rest plan response produced, stack = .case arms environment :: rest →
      TypeGraph.Equivalent assumptions input (.computation plan response produced) →
      ∃ row planType responseType branch context uses,
        EnvironmentTyping types context environment ∧
        ArmsTyping assumptions context arms row (.computation planType responseType branch) uses ∧
        validContext assumptions.shareableVariables context = true ∧
        TypeGraph.Equivalent assumptions produced (.variant row) ∧
        StackTyping assumptions types rest (.computation planType responseType branch) result := by
  induction typed with
  | nil => intro arms environment rest plan response produced impossible; simp at impossible
  | cons frameTyped restTyped ih =>
    intro arms environment rest plan response produced same related
    cases same
    cases frameTyped with
    | case environmentTyped armsTyped valid =>
      have activity := TypeGraph.equivalent_isComputation related
      simp [Ty.isComputation] at activity
    | effectCase environmentTyped armsTyped valid pure =>
      have producedRelated := (TypeGraph.computation_components related).2.2
      exact ⟨_,_,_,_,_,_,environmentTyped,armsTyped,valid,
        (TypeGraph.equivalent_equivalence assumptions).symm producedRelated,restTyped⟩
  | conversion converted restTyped ih =>
    intro arms environment rest plan response produced same related
    have next := (TypeGraph.equivalent_equivalence assumptions).trans
      ((TypeGraph.equivalent_equivalence assumptions).symm ((sameType_iff assumptions _ _).mp converted)) related
    exact ih arms environment rest plan response produced same next
  | returns pure restTyped ih =>
    intro arms environment rest plan response produced same related
    have activity := TypeGraph.equivalent_isComputation related
    change _ = true at activity
    rw [pure] at activity
    cases activity

end StructuralRuntime
end

public theorem stack_argument_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ argument environment rest, stack = .argument argument environment :: rest →
      ∃ functionType domain codomain reuse quantity,
        ∃ origin : ClosureTyping assumptions types ⟨argument,environment⟩ domain,
          callable functionType = .arrow reuse quantity domain codomain ∧
          argumentAllowed assumptions quantity origin.context domain origin.uses = true ∧
          ValueTyping assumptions types value functionType ∧
          StackTyping assumptions types rest codomain result := by
  induction continuation with
  | nil type => intro argument environment rest impossible; simp at impossible
  | cons frame restTyped =>
      intro argument environment rest same; cases same
      cases frame with
      | argument origin callableEq copyAllowed => exact ⟨_,_,_,_,_,origin,callableEq,copyAllowed,valueTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro argument environment rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

end Obend.Core.Proofs.Preservation
