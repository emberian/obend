module
/- `graph_stepRaw_names` and `graph_stepRaw`: every raw transition preserves the graph relation. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
public import Obend.Core.Proofs.Adequacy.CasesControl
public import Obend.Core.Proofs.Adequacy.CasesEval
public import Obend.Core.Proofs.Adequacy.CasesReturn
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

/-- EVERY running/finished raw transition retains a specified source name assignment on all already allocated addresses. New names are constructed from actual allocations. -/
 public theorem graph_stepRaw_names {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  -- one named field per branch of `stepRaw`; the case split itself is `StepCases.apply`
  refine StepCases.apply (P := fun state => GraphRepresentsBy meaning state source → ResultControl (stepRaw state).control → ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source)
    { complete := fun state value control represented successful => by exact ⟨meaning,(fun _ _ => rfl),by simpa [stepRaw,control] using represented⟩
      yielded := fun state plan control represented successful => by exact ⟨meaning,(fun _ _ => rfl),by simpa [stepRaw,control] using represented⟩
      refused := fun state reason control represented successful => by simp [stepRaw,control,ResultControl] at successful
      blackhole := fun state address control represented successful => by simp [stepRaw,control,ResultControl] at successful
      enter := fun state address control represented successful => by
        cases found : state.heap[address]? with
        | none => simp [stepRaw,control,found,ResultControl] at successful
        | some cell =>
            cases cell with
            | suspended origin => exact graph_enter_suspended_names represented control found
            | cached origin value => exact graph_enter_cached_names represented control found
            | evaluating origin => simp [stepRaw,control,found,ResultControl] at successful
      evaluate_hole := fun state n payload environment control represented successful => by
        obend_cases payload with [stepRaw, control, ResultControl]
      evaluate_bound := fun state index environment control represented successful => by
        cases found : environment[index]? with
        | none => simp [stepRaw,control,found,ResultControl] at successful
        | some address => exact graph_evaluate_bound_names represented control found
      evaluate_lam := fun state body environment control represented successful => by exact graph_evaluate_immediate_names (immediate := .closure body) represented control
      evaluate_nat := fun state number environment control represented successful => by exact graph_evaluate_immediate_names (immediate := .natural number) represented control
      evaluate_boolean := fun state value environment control represented successful => by exact graph_evaluate_immediate_names (immediate := .boolean value) represented control
      evaluate_label := fun state name environment control represented successful => by exact graph_evaluate_immediate_names (immediate := .label name) represented control
      evaluate_app := fun state function argument environment control represented successful => by exact graph_evaluate_context_names (context := .argument argument) represented control
      evaluate_mix := fun state lower upper environment control represented successful => by exact graph_evaluate_mix_names represented control
      evaluate_fix := fun state spec inherited environment control represented successful => by exact graph_evaluate_fix_names represented control
      evaluate_specification := fun state descriptor extension environment control represented successful => by exact graph_evaluate_pair_names (kind := .specification) represented control
      evaluate_prototype := fun state spec target environment control represented successful => by exact graph_evaluate_pair_names (kind := .prototype) represented control
      evaluate_record := fun state fields environment control represented successful => by exact graph_evaluate_record_names represented control
      evaluate_reflect := fun state term environment control represented successful => by exact graph_evaluate_context_names (context := .reflect) represented control
      evaluate_metadata := fun state term environment control represented successful => by exact graph_evaluate_context_names (context := .metadata) represented control
      evaluate_project := fun state term environment control represented successful => by exact graph_evaluate_context_names (context := .project) represented control
      evaluate_get := fun state target name environment control represented successful => by exact graph_evaluate_context_names (context := .field name) represented control
      evaluate_extend := fun state inherited fields environment control represented successful => by exact graph_evaluate_context_names (context := .extend fields) represented control
      evaluate_ifZero := fun state value zero body environment control represented successful => by exact graph_evaluate_context_names (context := .condition zero body) represented control
      evaluate_binary := fun state primitive left right environment control represented successful => by exact graph_evaluate_context_names (context := .binary primitive right) represented control
      evaluate_inject := fun state tag payload environment control represented successful => by exact graph_evaluate_inject_names represented control
      evaluate_case := fun state scrutinee arms environment control represented successful => by exact graph_evaluate_context_names (context := .case arms) represented control
      evaluate_ifBool := fun state condition whenTrue whenFalse environment control represented successful => by exact graph_evaluate_context_names (context := .ifBool whenTrue whenFalse) represented control
      evaluate_perform := fun state plan environment control represented successful => by
        cases shared : forcingShared state.stack with
        | true => simp [stepRaw,control,shared,ResultControl] at successful
        | false => exact graph_evaluate_perform_names represented control shared
      evaluate_done := fun state value environment control represented successful => by exact graph_evaluate_done_names represented control
      return_nil := fun state value control frames represented successful => by exact graph_complete_return_names represented control frames
      return_update := fun state value address rest control frames represented successful => by exact graph_cache_update_names represented control frames
      return_argument := fun state value argument environment rest control frames represented successful => by
        cases value with
        | closure body captured => exact graph_closure_call_names represented control frames
        | specification descriptor extension => exact graph_specification_call_names represented control frames
        | natural _ | boolean _ | label _ | record _ | prototype _ _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_reflect := fun state value rest control frames represented successful => by
        cases value with
        | prototype spec target => exact graph_object_access_names (access := .reflect) represented control frames
        | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_metadata := fun state value rest control frames represented successful => by
        cases value with
        | specification descriptor extension => exact graph_object_access_names (access := .metadata) represented control frames
        | closure _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_project := fun state value rest control frames represented successful => by
        cases value with
        | prototype spec target => exact graph_object_access_names (access := .project) represented control frames
        | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_field := fun state value name rest control frames represented successful => by
        cases value with
        | record fields =>
            cases found : fields.find? (fun field => field.1 == name) with
            | none => simp [stepRaw,control,frames,found,ResultControl] at successful
            | some field =>
                obtain ⟨key,address⟩ := field
                exact graph_field_return_names represented control frames found
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_extend := fun state value fields environment rest control frames represented successful => by
        cases value with
        | record inherited => exact graph_extend_record_names represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_condition := fun state value zero body environment rest control frames represented successful => by
        cases value with
        | natural number =>
            cases number with
            | zero => exact graph_condition_zero_names represented control frames
            | succ number => exact graph_condition_successor_names represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | record _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_binaryLeft := fun state value primitive right environment rest control frames represented successful => by exact graph_binary_left_return_names represented control frames
      return_binaryRight := fun state value primitive left rest control frames represented successful => by
        cases dispatch : (valueTerm left).bind (fun l => (valueTerm value).bind (primitiveResult primitive l)) with
        | none => simp [stepRaw,control,frames,dispatch,ResultControl] at successful
        | some result =>
            cases scalar : scalarValue result with
            | none => simp [stepRaw,control,frames,dispatch,scalar,ResultControl] at successful
            | some next => exact graph_primitive_return_names represented control frames dispatch scalar
      return_case := fun state value arms environment rest control frames represented successful => by
        cases value with
        | variant tag payload =>
            cases found : arms.find? (fun arm => arm.1 == tag) with
            | none => simp [stepRaw,control,frames,found,ResultControl] at successful
            | some arm =>
                obtain ⟨key,body⟩ := arm
                exact graph_case_return_names represented control frames found
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_ifBool := fun state value whenTrue whenFalse environment rest control frames represented successful => by
        cases value with
        | boolean value => exact graph_ifBool_return_names represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
    } state represented successful


set_option maxHeartbeats 800000 in
/-- All actual raw transition cases preserve the graph relation when the
successor is running or finished. No syntactic fragment, evaluator oracle or
implementation-selected coverage premise is used. Operational invariants for
fault/blackhole successors are proved independently in DemandInvariant. -/
 theorem graph_via_names {state : State} {source : Term}
    (represented : GraphRepresents state source) (successful : ResultControl (stepRaw state).control) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  obtain ⟨next,_,advanced⟩ := graph_stepRaw_names ⟨lexical,busy,final,names,heap,focus,control,stack⟩ successful
  exact graphBy_graph advanced

 public theorem graph_stepRaw {state : State} {source : Term}
    (represented : GraphRepresents state source) (successful : ResultControl (stepRaw state).control) :
    GraphRepresents (stepRaw state) source := by
  -- one named field per branch of `stepRaw`; the case split itself is `StepCases.apply`
  refine StepCases.apply (P := fun state => GraphRepresents state source → ResultControl (stepRaw state).control → GraphRepresents (stepRaw state) source)
    { complete := fun state value control represented successful => by simpa [stepRaw,control] using represented
      yielded := fun state plan control represented successful => by simpa [stepRaw,control] using represented
      refused := fun state reason control represented successful => by simp [stepRaw,control,ResultControl] at successful
      blackhole := fun state address control represented successful => by simp [stepRaw,control,ResultControl] at successful
      enter := fun state address control represented successful => by
        cases found : state.heap[address]? with
        | none => simp [stepRaw,control,found,ResultControl] at successful
        | some cell =>
            cases cell with
            | suspended origin => exact graph_enter_suspended represented control found
            | cached origin value => exact graph_enter_cached represented control found
            | evaluating origin => simp [stepRaw,control,found,ResultControl] at successful
      evaluate_hole := fun state n payload environment control represented successful => by
        obend_cases payload with [stepRaw, control, ResultControl]
      evaluate_bound := fun state index environment control represented successful => by
        cases found : environment[index]? with
        | none => simp [stepRaw,control,found,ResultControl] at successful
        | some address => exact graph_evaluate_bound represented control found
      evaluate_lam := fun state body environment control represented successful => by exact graph_evaluate_immediate (immediate := .closure body) represented control
      evaluate_nat := fun state number environment control represented successful => by exact graph_evaluate_immediate (immediate := .natural number) represented control
      evaluate_boolean := fun state value environment control represented successful => by exact graph_evaluate_immediate (immediate := .boolean value) represented control
      evaluate_label := fun state name environment control represented successful => by exact graph_evaluate_immediate (immediate := .label name) represented control
      evaluate_app := fun state function argument environment control represented successful => by exact graph_evaluate_context (context := .argument argument) represented control
      evaluate_mix := fun state lower upper environment control represented successful => by exact graph_evaluate_mix represented control
      evaluate_fix := fun state spec inherited environment control represented successful => by exact graph_evaluate_fix represented control
      evaluate_specification := fun state descriptor extension environment control represented successful => by exact graph_evaluate_pair (kind := .specification) represented control
      evaluate_prototype := fun state spec target environment control represented successful => by exact graph_evaluate_pair (kind := .prototype) represented control
      evaluate_record := fun state fields environment control represented successful => by exact graph_evaluate_record represented control
      evaluate_reflect := fun state term environment control represented successful => by exact graph_evaluate_context (context := .reflect) represented control
      evaluate_metadata := fun state term environment control represented successful => by exact graph_evaluate_context (context := .metadata) represented control
      evaluate_project := fun state term environment control represented successful => by exact graph_evaluate_context (context := .project) represented control
      evaluate_get := fun state target name environment control represented successful => by exact graph_evaluate_context (context := .field name) represented control
      evaluate_extend := fun state inherited fields environment control represented successful => by exact graph_evaluate_context (context := .extend fields) represented control
      evaluate_ifZero := fun state value zero body environment control represented successful => by exact graph_evaluate_context (context := .condition zero body) represented control
      evaluate_binary := fun state primitive left right environment control represented successful => by exact graph_evaluate_context (context := .binary primitive right) represented control
      evaluate_inject := fun state _ _ environment control represented successful => by exact graph_via_names represented successful
      evaluate_case := fun state _ _ environment control represented successful => by exact graph_via_names represented successful
      evaluate_ifBool := fun state _ _ _ environment control represented successful => by exact graph_via_names represented successful
      evaluate_perform := fun state _ environment control represented successful => by exact graph_via_names represented successful
      evaluate_done := fun state _ environment control represented successful => by exact graph_via_names represented successful
      return_nil := fun state value control frames represented successful => by exact graph_complete_return represented control frames
      return_update := fun state value address rest control frames represented successful => by exact graph_cache_update represented control frames
      return_argument := fun state value argument environment rest control frames represented successful => by
        cases value with
        | closure body captured => exact graph_closure_call represented control frames
        | specification descriptor extension => exact graph_specification_call represented control frames
        | natural _ | boolean _ | label _ | record _ | prototype _ _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_reflect := fun state value rest control frames represented successful => by
        cases value with
        | prototype spec target => exact graph_object_access (access := .reflect) represented control frames
        | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_metadata := fun state value rest control frames represented successful => by
        cases value with
        | specification descriptor extension => exact graph_object_access (access := .metadata) represented control frames
        | closure _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_project := fun state value rest control frames represented successful => by
        cases value with
        | prototype spec target => exact graph_object_access (access := .project) represented control frames
        | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_field := fun state value name rest control frames represented successful => by
        cases value with
        | record fields =>
            cases found : fields.find? (fun field => field.1 == name) with
            | none => simp [stepRaw,control,frames,found,ResultControl] at successful
            | some field =>
                obtain ⟨key,address⟩ := field
                exact graph_field_return represented control frames found
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_extend := fun state value fields environment rest control frames represented successful => by
        cases value with
        | record inherited => exact graph_extend_record represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_condition := fun state value zero body environment rest control frames represented successful => by
        cases value with
        | natural number =>
            cases number with
            | zero => exact graph_condition_zero represented control frames
            | succ number => exact graph_condition_successor represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | record _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_binaryLeft := fun state value primitive right environment rest control frames represented successful => by exact graph_binary_left_return represented control frames
      return_binaryRight := fun state value primitive left rest control frames represented successful => by
        cases dispatch : (valueTerm left).bind (fun l => (valueTerm value).bind (primitiveResult primitive l)) with
        | none => simp [stepRaw,control,frames,dispatch,ResultControl] at successful
        | some result =>
            cases scalar : scalarValue result with
            | none => simp [stepRaw,control,frames,dispatch,scalar,ResultControl] at successful
            | some next => exact graph_primitive_return represented control frames dispatch scalar
      return_case := fun state value _ _ rest control frames represented successful => by exact graph_via_names represented successful
      return_ifBool := fun state value _ _ _ rest control frames represented successful => by exact graph_via_names represented successful
    } state represented successful

/-- A concrete cyclic heap instance: its one address denotes the source Fix;
the saved origin captures that same address and denotes its independent source
unfolding. Neither this witness nor the lexical invariant forbids the cycle. -/
 theorem initial_fix_graph {spec inherited : Term}
    (hs : Scoped 0 spec) (hi : Scoped 0 inherited) :
    GraphRepresents (stepRaw (initial (.fix spec inherited))) (.fix spec inherited) := by
  have lexical := stepRaw_lexicalInvariant (initial_lexicalInvariant (Scoped.fix hs hi))
  let meaning : AddressMeaning := fun _ => .fix spec inherited
  have rs : spec.rename Nat.succ = spec := scoped_rename_identity hs _ (by intros; omega)
  have ri : inherited.rename Nat.succ = inherited := scoped_rename_identity hi _ (by intros; omega)
  have ss : spec.substitute (environmentSubstitution meaning [0]) = spec :=
    scoped_substitute_identity hs _ (by intros; omega)
  have si : inherited.substitute (environmentSubstitution meaning [0]) = inherited :=
    scoped_substitute_identity hi _ (by intros; omega)
  refine ⟨lexical,stepRaw_busyInvariant (initial_busyInvariant _),stepRaw_finalStackInvariant (initial_finalStackInvariant _),meaning,?_,?_,.fix spec inherited,?_,?_⟩
  · intro address allocated
    exact Scoped.fix hs hi
  · intro address cell found
    simp [initial,stepRaw] at found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have zero : address = 0 := by simpa using bound
    subst address
    simp at found
    subst cell
    constructor
    · simpa [closeOrigin,closeTerm,cellOrigin,Term.substitute,rs,ri,ss,si,
        environmentSubstitution,meaning] using Steps.next (Step.fix spec inherited) (Steps.refl _)
    · trivial
  · simp [initial,stepRaw,controlMeaning,meaning]
  · simp only [initial,stepRaw,StackRealizes]
    exact .refl _

end Obend.Core.Proofs.Adequacy
