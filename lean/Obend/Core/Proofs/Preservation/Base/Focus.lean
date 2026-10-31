module
/- Source focus and the value inversions the case modules share. -/
public import Obend.Core.MachineTyping
public import Obend.Core.RuntimeOrigins
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.TypeGraphHead
public import Obend.Core.Proofs.Adequacy.Defs
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Preservation.Base.Reusable
namespace Obend.Core.Proofs.Preservation
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine Obend.Core.MachineTyping
set_option autoImplicit false

@[expose] public def sourceFocus (term : Term) (environment : Environment) : Option (Term × Frame) :=
  match term with
  | .get target name => some (target,.field name)
  | .reflect target => some (target,.reflect)
  | .metadata target => some (target,.metadata)
  | .project target => some (target,.project)
  | .extend target fields => some (target,.extend fields environment)
  | .binary primitive left right => some (left,.binaryLeft primitive right environment)
  | .ifZero value zero successor => some (value,.condition zero successor environment)
  | .case scrutinee arms => some (scrutinee,.case arms environment)
  | .ifBool condition whenTrue whenFalse => some (condition,.ifBool whenTrue whenFalse environment)
  | _ => none

public structure FocusedSource (assumptions : Assumptions) (types : AddressTypes)
    (target : Term) (environment : Environment) (frame : Frame) (expected : Ty) where
  current : Ty
  output : Ty
  origin : ClosureTyping assumptions types ⟨target,environment⟩ current
  continuation : FrameTyping assumptions types frame current output
  result : ConversionPath assumptions output expected

/-- Source projections and overlays carry their actual demanded origin and
continuation typing, retaining lexical quantities and finite conversion paths. -/
theorem source_focus_typed {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    ∀ types environment, EnvironmentTyping types context environment →
      safeUses context uses = true → validContext assumptions.shareableVariables context = true →
      match sourceFocus term environment with
      | some (target,frame) => Nonempty (FocusedSource assumptions types target environment frame type)
      | none => True := by
  apply PartialTyping.rec
    (motive_1 := fun context term type uses _ => ∀ types environment,
      EnvironmentTyping types context environment → safeUses context uses = true →
      validContext assumptions.shareableVariables context = true →
      match sourceFocus term environment with
      | some (target,frame) => Nonempty (FocusedSource assumptions types target environment frame type)
      | none => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (t := source)
  case conversion =>
    intro context term actual expected uses prior agreement ih types environment environmentTyped safe valid
    have focused := ih types environment environmentTyped safe valid
    cases found : sourceFocus term environment with
    | none => trivial
    | some pair =>
      obtain ⟨target,frame⟩ := pair
      rw [found] at focused
      obtain ⟨data⟩ := focused
      exact ⟨⟨data.current,data.output,data.origin,data.continuation,.step data.result agreement⟩⟩
  case get =>
    intro context target targetType member uses name fuel targetTyped lookup _ ih types environment environmentTyped safe valid
    exact ⟨⟨targetType,member,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.field lookup,.refl member⟩⟩
  case extend =>
    intro context target fields targetType row targetUses fieldUses rowFuel targetTyped fieldsTyped rowValid ihTarget ihFields types environment environmentTyped safe valid
    have targetSafe := safe_add_uses_left context targetUses fieldUses (source_uses_length targetTyped)
      (source_uses_length (PartialTyping.record fieldsTyped)) safe
    have fieldsSafe := safe_add_uses_right context targetUses fieldUses (source_uses_length targetTyped)
      (source_uses_length (PartialTyping.record fieldsTyped)) safe
    exact ⟨⟨targetType,overlay row targetType,⟨context,targetUses,environmentTyped,targetTyped,targetSafe,valid⟩,
      .extend environmentTyped fieldsTyped fieldsSafe valid rowValid,.refl _⟩⟩
  case reflect =>
    intro context target specType targetType uses targetTyped _ ih types environment environmentTyped safe valid
    exact ⟨⟨.prototype specType targetType,specType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.reflect _ _,.refl _⟩⟩
  case metadata =>
    intro context target metadataType extensionType uses targetTyped _ ih types environment environmentTyped safe valid
    exact ⟨⟨.specification metadataType extensionType,metadataType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.metadata _ _,.refl _⟩⟩
  case project =>
    intro context target specType targetType uses targetTyped _ ih types environment environmentTyped safe valid
    exact ⟨⟨.prototype specType targetType,targetType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.project _ _,.refl _⟩⟩
  case binary =>
    intro context primitive left right input output lu ru primitiveEq leftTyped rightTyped ihLeft ihRight types environment environmentTyped safe valid
    have leftSafe := safe_add_uses_left context lu ru (source_uses_length leftTyped) (source_uses_length rightTyped) safe
    have rightSafe := safe_add_uses_right context lu ru (source_uses_length leftTyped) (source_uses_length rightTyped) safe
    have inputEq : (primitiveTypes primitive).1 = input := congrArg Prod.fst primitiveEq
    have outputEq : (primitiveTypes primitive).2 = output := congrArg Prod.snd primitiveEq
    let rightOrigin : ClosureTyping assumptions types ⟨right,environment⟩ input :=
      ⟨context,ru,environmentTyped,rightTyped,rightSafe,valid⟩
    have rightOrigin' : ClosureTyping assumptions types ⟨right,environment⟩ (primitiveTypes primitive).1 := by
      rw [inputEq]; exact rightOrigin
    have frame : FrameTyping assumptions types (.binaryLeft primitive right environment) input output := by
      simpa only [inputEq,outputEq] using FrameTyping.binaryLeft rightOrigin'
    exact ⟨⟨input,output,⟨context,lu,environmentTyped,leftTyped,leftSafe,valid⟩,frame,.refl _⟩⟩
  case ifZero =>
    intro context value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe _ ihValue ihZero ihSuccessor types environment environmentTyped safe valid
    have vuLength := source_uses_length valueTyped
    have zuLength := source_uses_length zeroTyped
    have suLength : su.tail.length = context.length := by simp [List.length_tail,source_uses_length successorTyped]
    have branchLength : (joinUses zu su.tail).length = context.length := by
      simp [joinUses,List.length_zipWith,zuLength,suLength]
    have valueSafe := safe_add_uses_left context vu (joinUses zu su.tail) vuLength branchLength safe
    have branchSafe := safe_add_uses_right context vu (joinUses zu su.tail) vuLength branchLength safe
    have zeroSafe := safe_join_uses_left context zu su.tail zuLength suLength branchSafe
    let zeroOrigin : ClosureTyping assumptions types ⟨zero,environment⟩ result :=
      ⟨context,zu,environmentTyped,zeroTyped,zeroSafe,valid⟩
    exact ⟨⟨.natural,result,⟨context,vu,environmentTyped,valueTyped,valueSafe,valid⟩,
      .condition zeroOrigin environmentTyped successorTyped successorSafe valid,.refl _⟩⟩
  case case =>
    intro context scrutinee arms row result su au scrutineeTyped armsTyped _ ihScrutinee ihArms types environment environmentTyped safe valid
    have scrutineeSafe := safe_add_uses_left context su au (source_uses_length scrutineeTyped) (arms_uses_length armsTyped) safe
    exact ⟨⟨.variant row,result,⟨context,su,environmentTyped,scrutineeTyped,scrutineeSafe,valid⟩,
      .case environmentTyped armsTyped valid,.refl _⟩⟩
  case ifBool =>
    intro context condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped _ ihCondition ihTrue ihFalse types environment environmentTyped safe valid
    have cuLength := source_uses_length conditionTyped
    have tuLength := source_uses_length trueTyped
    have fuLength := source_uses_length falseTyped
    have branchLength : (joinUses tu fu).length = context.length := by
      simp [joinUses,List.length_zipWith,tuLength,fuLength]
    have conditionSafe := safe_add_uses_left context cu (joinUses tu fu) cuLength branchLength safe
    have branchSafe := safe_add_uses_right context cu (joinUses tu fu) cuLength branchLength safe
    have trueSafe := safe_join_uses_left context tu fu tuLength fuLength branchSafe
    have falseSafe := safe_join_uses_right context tu fu tuLength fuLength branchSafe
    exact ⟨⟨.boolean,result,⟨context,cu,environmentTyped,conditionTyped,conditionSafe,valid⟩,
      .ifBool ⟨context,tu,environmentTyped,trueTyped,trueSafe,valid⟩ ⟨context,fu,environmentTyped,falseTyped,falseSafe,valid⟩,.refl _⟩⟩
  case effectCase =>
    intro context scrutinee arms planType response row result su au scrutineeTyped armsTyped pure _ ihScrutinee ihArms types environment environmentTyped safe valid
    have scrutineeSafe := safe_add_uses_left context su au (source_uses_length scrutineeTyped) (arms_uses_length armsTyped) safe
    exact ⟨⟨.computation planType response (.variant row),.computation planType response result,
      ⟨context,su,environmentTyped,scrutineeTyped,scrutineeSafe,valid⟩,
      .effectCase environmentTyped armsTyped valid pure,.refl _⟩⟩
  case nil =>
    intros; trivial
  case cons =>
    intros; trivial
  case nil =>
    intros; trivial
  case cons =>
    intros; trivial
  all_goals (intros; simp [sourceFocus])

/-- Focusing projection/overlay, binary and conditional source forms preserves the typed stack
at the exact raw-machine step; no source annotation or row oracle is assumed. -/
public theorem typed_source_focus_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {term target : Term} {environment : Environment} {frame : Frame}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate term environment)
    (focus : sourceFocus term environment = some (target,frame)) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    have focused := source_focus_typed origin.source types environment origin.environment origin.safe origin.contextValid
    rw [focus] at focused
    obtain ⟨data⟩ := focused
    have next : stepRaw state = {state with control := .evaluate target environment,stack := frame :: state.stack} := by
      obend_cases term with [sourceFocus,stepRaw,evaluate]
    refine ⟨step_certificate typed data.current ?_ ?_ ?_⟩
    · simpa [next] using typed.heap
    · simpa [next] using ControlTyping.evaluate data.origin
    · simpa [next] using StackTyping.cons data.continuation (stack_convert_path data.result typed.stack)

public theorem record_value_form {assumptions : Assumptions} {types : AddressTypes} {value : RuntimeValue} {row : Ty}
    (typed : ValueTyping assumptions types value row) (fuel : Nat)
    (isRow : row.isRow assumptions.bounds fuel = true) : ∃ fields, value = .record fields := by
  induction typed generalizing fuel with
  | record finite members => exact ⟨_, rfl⟩
  | conversion prior converted ih =>
    obtain ⟨depth, finite⟩ := TypeGraph.equivalent_finite_row_transport
      ((sameType_iff assumptions _ _).mp converted) fuel isRow
    exact ih depth finite
  | natural value | boolean value | label value | closure environment body safe valid captures
    | specification metadata ext | prototype spec target | variant rowLookup assigned path =>
    cases fuel <;> simp [Ty.isRow, literalType] at isRow

public theorem stack_update_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ address rest, stack = .update address :: rest →
      ∃ addressType, types[address]? = some addressType ∧
        ValueTyping assumptions types value addressType ∧
        StackTyping assumptions types rest addressType result := by
  induction continuation with
  | nil type => intro address rest impossible; simp at impossible
  | cons frame restTyped =>
      intro address rest same
      cases same
      cases frame with
      | update assigned _ => exact ⟨_,assigned,valueTyped,restTyped⟩
  | conversion agreement restTyped ih =>
      exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro address rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

public theorem source_convert_path {assumptions : Assumptions} {context : Context} {term : Term}
    {first last : Ty} {uses : Uses} (typed : PartialTyping assumptions context term first uses)
    (path : ConversionPath assumptions first last) : PartialTyping assumptions context term last uses := by
  induction path with
  | refl => exact typed
  | step prior agreement ih => exact .conversion ih agreement

public theorem value_variant_fields {assumptions : Assumptions} {types : AddressTypes} {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    ∀ tag address, value = .variant tag address →
      ∃ (row member actual : Ty) (fuel : Nat), row.lookup assumptions.bounds fuel tag = some member ∧
        types[address]? = some actual ∧ ConversionPath assumptions actual member ∧
        TypeGraph.Equivalent assumptions (.variant row) type := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | closure environment body safe valid captures => intros; contradiction
  | record isRow members => intros; contradiction
  | specification metadata ext => intros; contradiction
  | prototype spec target => intros; contradiction
  | variant lookup assigned path =>
    intro tag address same
    cases same
    exact ⟨_, _, _, _, lookup, assigned, path, (TypeGraph.equivalent_equivalence assumptions).refl _⟩
  | conversion prior converted ih =>
    intro tag address same
    obtain ⟨row, member, actual, fuel, lookup, assigned, path, related⟩ := ih tag address same
    exact ⟨row, member, actual, fuel, lookup, assigned, path,
      (TypeGraph.equivalent_equivalence assumptions).trans related ((sameType_iff assumptions _ _).mp converted)⟩

end Obend.Core.Proofs.Preservation
