module
/- Runtime inversion after structural conversion. Address assignments and
MachineTyping constructors need no representation change. Origins keep their
actual components and relate their complete constructor type to the requested
type; exact canonical-head preservation is deliberately absent. -/
public import Obend.Core.MachineTyping
public import Obend.Core.TypeGraphHead
@[expose] public section
namespace Obend.Core.MachineTyping.Next
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine
open Obend.Core.MachineTyping
set_option autoImplicit false

structure FunctionOrigin (assumptions : Assumptions) (types : AddressTypes)
    (body : Term) (environment : Environment) where
  context : Context
  annotation : LambdaAnnotation
  uses : Uses
  environmentTyped : EnvironmentTyping types context environment
  bodyTyped : PartialTyping assumptions (⟨annotation.domain,annotation.parameter⟩ :: context)
    body annotation.codomain uses
  safe : safeUses (⟨annotation.domain,annotation.parameter⟩ :: context) uses = true
  valid : validContext assumptions.shareableVariables (⟨annotation.domain,annotation.parameter⟩ :: context) = true
  captures : reusableAllowed assumptions annotation.reuse context uses.tail = true

def FunctionOrigin.arrow {assumptions : Assumptions} {types : AddressTypes}
    {body : Term} {environment : Environment} (origin : FunctionOrigin assumptions types body environment) : Ty :=
  .arrow origin.annotation.reuse origin.annotation.parameter origin.annotation.domain origin.annotation.codomain

section Conversion
variable {assumptions : Assumptions}
variable (conversion : ∀ a b, sameType assumptions a b = true → TypeGraph.Equivalent assumptions a b)
include conversion

include conversion

theorem conversionPath_candidate {first last : Ty} (path : ConversionPath assumptions first last) :
    TypeGraph.Equivalent assumptions first last := by
  induction path with
  | refl => exact (TypeGraph.equivalent_equivalence assumptions).refl _
  | step prior agree ih =>
    exact (TypeGraph.equivalent_equivalence assumptions).trans ih (conversion _ _ agree)

theorem value_closure_origin {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ body environment, value = .closure body environment →
      ∃ origin : FunctionOrigin assumptions types body environment,
        TypeGraph.Equivalent assumptions origin.arrow type := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | record isRow members => intros; contradiction
  | specification metadata ext => intros; contradiction
  | prototype spec target => intros; contradiction
  | variant lookup assigned path => intros; contradiction
  | closure env source safe valid captures =>
    intro body environment same
    cases same
    exact ⟨⟨_,_,_,env,source,safe,valid,captures⟩,
      (TypeGraph.equivalent_equivalence assumptions).refl _⟩
  | conversion prior agree ih =>
    intro body environment same
    obtain ⟨origin,related⟩ := ih body environment same
    exact ⟨origin,(TypeGraph.equivalent_equivalence assumptions).trans related (conversion _ _ agree)⟩

theorem value_specification_origin {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ metadata extension, value = .specification metadata extension →
      ∃ metadataType extensionType,
        types[metadata]? = some metadataType ∧ types[extension]? = some extensionType ∧
        TypeGraph.Equivalent assumptions (.specification metadataType extensionType) type := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | record isRow members => intros; contradiction
  | closure env source safe valid captures => intros; contradiction
  | prototype spec target => intros; contradiction
  | variant lookup assigned path => intros; contradiction
  | specification metadataAssigned extensionAssigned =>
    intro metadata extension same
    cases same
    exact ⟨_,_,metadataAssigned,extensionAssigned,(TypeGraph.equivalent_equivalence assumptions).refl _⟩
  | conversion prior agree ih =>
    intro metadata extension same
    obtain ⟨metadataType,extensionType,metadataAssigned,extensionAssigned,related⟩ := ih metadata extension same
    exact ⟨metadataType,extensionType,metadataAssigned,extensionAssigned,
      (TypeGraph.equivalent_equivalence assumptions).trans related (conversion _ _ agree)⟩

theorem value_prototype_origin {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ spec target, value = .prototype spec target →
      ∃ specType targetType,
        types[spec]? = some specType ∧ types[target]? = some targetType ∧
        TypeGraph.Equivalent assumptions (.prototype specType targetType) type := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | record isRow members => intros; contradiction
  | closure env source safe valid captures => intros; contradiction
  | specification metadata ext => intros; contradiction
  | variant lookup assigned path => intros; contradiction
  | prototype specAssigned targetAssigned =>
    intro spec target same
    cases same
    exact ⟨_,_,specAssigned,targetAssigned,(TypeGraph.equivalent_equivalence assumptions).refl _⟩
  | conversion prior agree ih =>
    intro spec target same
    obtain ⟨specType,targetType,specAssigned,targetAssigned,related⟩ := ih spec target same
    exact ⟨specType,targetType,specAssigned,targetAssigned,
      (TypeGraph.equivalent_equivalence assumptions).trans related (conversion _ _ agree)⟩

theorem value_variant_origin {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ tag address, value = .variant tag address →
      ∃ row member actual fuel,
        row.lookup assumptions.bounds fuel tag = some member ∧ types[address]? = some actual ∧
        ConversionPath assumptions actual member ∧ TypeGraph.Equivalent assumptions (.variant row) type := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | record isRow members => intros; contradiction
  | closure env source safe valid captures => intros; contradiction
  | specification metadata ext => intros; contradiction
  | prototype spec target => intros; contradiction
  | variant lookup assigned path =>
    intro tag address same
    cases same
    exact ⟨_,_,_,_,lookup,assigned,path,(TypeGraph.equivalent_equivalence assumptions).refl _⟩
  | conversion prior agree ih =>
    intro tag address same
    obtain ⟨row,member,actual,fuel,lookup,assigned,path,related⟩ := ih tag address same
    exact ⟨row,member,actual,fuel,lookup,assigned,path,
      (TypeGraph.equivalent_equivalence assumptions).trans related (conversion _ _ agree)⟩

theorem value_record_origin {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ fields, value = .record fields →
      ∃ row, (∃ fuel, row.isRow assumptions.bounds fuel = true) ∧
        (∀ fuel name member, row.lookup assumptions.bounds fuel name = some member →
          ∃ address actual, fields.find? (fun field => field.1 == name) = some (name,address) ∧
            types[address]? = some actual ∧ ConversionPath assumptions actual member) ∧
        TypeGraph.Equivalent assumptions row type := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | closure env source safe valid captures => intros; contradiction
  | specification metadata ext => intros; contradiction
  | prototype spec target => intros; contradiction
  | variant lookup assigned path => intros; contradiction
  | record isRow members =>
    intro fields same
    cases same
    exact ⟨_,isRow,members,(TypeGraph.equivalent_equivalence assumptions).refl _⟩
  | conversion prior agree ih =>
    intro fields same
    obtain ⟨row,isRow,members,related⟩ := ih fields same
    exact ⟨row,isRow,members,
      (TypeGraph.equivalent_equivalence assumptions).trans related (conversion _ _ agree)⟩

def scalarType : RuntimeValue → Option Ty
  | .natural _ => some .natural
  | .boolean _ => some .boolean
  | .label value => some (literalType value)
  | _ => none

theorem value_scalar_origin {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ scalar, scalarType value = some scalar → TypeGraph.Equivalent assumptions scalar type := by
  induction typed with
  | natural value =>
    intro scalar same
    cases same
    exact (TypeGraph.equivalent_equivalence assumptions).refl _
  | boolean value =>
    intro scalar same
    cases same
    exact (TypeGraph.equivalent_equivalence assumptions).refl _
  | label value =>
    intro scalar same
    cases same
    exact (TypeGraph.equivalent_equivalence assumptions).refl _
  | record isRow members => intro scalar same; simp [scalarType] at same
  | closure env source safe valid captures => intro scalar same; simp [scalarType] at same
  | specification metadata ext => intro scalar same; simp [scalarType] at same
  | prototype spec target => intro scalar same; simp [scalarType] at same
  | variant lookup assigned path => intro scalar same; simp [scalarType] at same
  | conversion prior agree ih =>
    intro scalar same
    exact (TypeGraph.equivalent_equivalence assumptions).trans (ih scalar same) (conversion _ _ agree)

end Conversion

end Obend.Core.MachineTyping.Next
