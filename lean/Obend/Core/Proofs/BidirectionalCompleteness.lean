module
/- Full annotated completeness on the whole declarative grammar. Annotation
witnesses are finite trees produced inside existential propositions, never by
eliminating a typing proof into data. Rule representatives preserve the exact
usage vector while conversion composes agreement without changing annotations. -/
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.Preservation.Base.Reusable
public import Obend.Core.Proofs.Preservation.Base.Values

namespace Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
set_option autoImplicit false

/-- Every syntax constructor is covered by the annotated completeness theorem.
The independent typing premise excludes holes and invalid programs. -/
@[expose] public def checkCovered (_term : Term) : Bool := true

@[expose] public def synthCovered (_term : Term) : Bool := true

public theorem all_syntax_covered (term : Term) :
    checkCovered term = true ∧ synthCovered term = true := ⟨rfl, rfl⟩

public inductive AnnotationTree where
  | node (here : Option LambdaAnnotation) (children : List AnnotationTree)

@[expose] public def emptyTree : AnnotationTree := .node none []

namespace AnnotationTree
@[expose] public def child : AnnotationTree → Nat → AnnotationTree
  | .node _ children, index => children[index]?.getD emptyTree

/-- Lookup recurses on the path, so finite child lists require no nested-tree
termination argument or trusted code. -/
@[expose] public def lookup : List Nat → AnnotationTree → Option LambdaAnnotation
  | [], .node here _ => here
  | index :: path, tree => lookup path (child tree index)
end AnnotationTree

@[expose] public def treeAnnotations (tree : AnnotationTree) : Annotations :=
  fun path => tree.lookup path

/-- One global annotation map realizes a local finite tree at a source path.
This is a locality hypothesis on data, not a second induction on the checker. -/
@[expose] public def Realizes (annotations : Annotations) (path : List Nat) (tree : AnnotationTree) : Prop :=
  ∀ suffix, annotations (path ++ suffix) = tree.lookup suffix

theorem Realizes.root {annotations : Annotations} {path : List Nat}
    {here : Option LambdaAnnotation} {children : List AnnotationTree}
    (realizes : Realizes annotations path (.node here children)) : annotations path = here := by
  simpa only [List.append_nil, AnnotationTree.lookup] using realizes []

theorem Realizes.child {annotations : Annotations} {path : List Nat} {tree : AnnotationTree}
    (realizes : Realizes annotations path tree) (index : Nat) :
    Realizes annotations (path ++ [index]) (tree.child index) := by
  intro suffix
  simpa only [List.append_assoc, List.cons_append, List.nil_append, AnnotationTree.lookup] using
    realizes (index :: suffix)

theorem treeAnnotations_realizes (tree : AnnotationTree) : Realizes (treeAnnotations tree) [] tree := by
  intro suffix
  rfl

/-- A list of child trees mounted at the exact numeric field/arm positions. -/
@[expose] public def ForestRealizes (annotations : Annotations) (path : List Nat) (index : Nat)
    (trees : List AnnotationTree) : Prop :=
  ∀ offset, Realizes annotations (path ++ [index + offset]) (trees[offset]?.getD emptyTree)

theorem Realizes.forest {annotations : Annotations} {path : List Nat}
    {here : Option LambdaAnnotation} {children : List AnnotationTree}
    (realizes : Realizes annotations path (.node here children)) :
    ForestRealizes annotations path 0 children := by
  intro offset
  simpa only [Nat.zero_add, AnnotationTree.child] using realizes.child offset

theorem ForestRealizes.head {annotations : Annotations} {path : List Nat} {index : Nat}
    {tree : AnnotationTree} {trees : List AnnotationTree}
    (realizes : ForestRealizes annotations path index (tree :: trees)) :
    Realizes annotations (path ++ [index]) tree := by
  simpa using realizes 0

theorem ForestRealizes.tail {annotations : Annotations} {path : List Nat} {index : Nat}
    {tree : AnnotationTree} {trees : List AnnotationTree}
    (realizes : ForestRealizes annotations path index (tree :: trees)) :
    ForestRealizes annotations path (index + 1) trees := by
  intro offset
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using realizes (offset + 1)

@[expose] public def Yields {α : Type} (result : Except CheckRefusal α) (P : α → Prop) : Prop :=
  match result with
  | .ok value => P value
  | .error _ => False

theorem Yields.elim {α : Type} {result : Except CheckRefusal α} {P : α → Prop}
    (yielded : Yields result P) : ∃ value, result = .ok value ∧ P value := by
  cases result with
  | ok value => exact ⟨value, rfl, yielded⟩
  | error _ => exact False.elim yielded

@[expose] public def Completes (assumptions : Assumptions) (context : Context)
    (term : Term) (type : Ty) (uses : Uses) (tree : AnnotationTree) : Prop :=
  ∀ annotations path, Realizes annotations path tree →
    Yields (synthAt assumptions annotations context path term)
      (fun result => sameType assumptions result.type type = true ∧ result.uses = uses) ∧
    ∀ expected, sameType assumptions type expected = true →
      Yields (checkAt assumptions annotations context path term expected) (fun result => result.uses = uses)

@[expose] public def FieldsComplete (assumptions : Assumptions) (context : Context)
    (fields : List (String × Term)) (row : Ty) (uses : Uses) (trees : List AnnotationTree) : Prop :=
  ∀ annotations path index, ForestRealizes annotations path index trees →
    Yields (checkFields assumptions annotations context path index fields row) (fun result => result.uses = uses)

theorem completes_conversion {assumptions : Assumptions} {context : Context} {term : Term}
    {actual expected : Ty} {uses : Uses} {tree : AnnotationTree}
    (complete : Completes assumptions context term actual uses tree)
    (agrees : sameType assumptions actual expected = true) :
    Completes assumptions context term expected uses tree := by
  intro annotations path realizes
  obtain ⟨synth, check⟩ := complete annotations path realizes
  constructor
  · obtain ⟨result, yielded, agreement, usage⟩ := synth.elim
    rw [yielded]
    exact ⟨sameType_trans agreement agrees, usage⟩
  · intro target agreement
    exact check target (sameType_trans agrees agreement)

theorem finish_complete {assumptions : Assumptions} {annotations : Annotations} {context : Context}
    {path : List Nat} {term : Term} {derived : Ty} {uses : Uses}
    (synthesized : Synth assumptions context term)
    (unfolds : ∀ mode, elaborate assumptions annotations context path term mode =
      finish assumptions annotations path synthesized mode)
    (agrees : sameType assumptions synthesized.type derived = true) (sameUses : synthesized.uses = uses) :
    Yields (synthAt assumptions annotations context path term)
      (fun result => sameType assumptions result.type derived = true ∧ result.uses = uses) ∧
    ∀ expected, sameType assumptions derived expected = true →
      Yields (checkAt assumptions annotations context path term expected) (fun result => result.uses = uses) := by
  constructor
  · change Yields (elaborate assumptions annotations context path term .synth) _
    rw [unfolds .synth]
    simp only [finish, ascribe, Yields]
    split
    · split
      · rename_i ascribed _ same
        exact ⟨sameType_trans (sameType_symm same) agrees, sameUses⟩
      · exact ⟨agrees, sameUses⟩
    · exact ⟨agrees, sameUses⟩
  · intro expected agreement
    have accepted : sameType assumptions synthesized.type expected = true := sameType_trans agrees agreement
    change Yields (elaborate assumptions annotations context path term (.check expected)) _
    rw [unfolds, finish, dif_pos accepted]
    exact sameUses

public theorem completes_bound {assumptions : Assumptions} {context : Context}
    {index : Nat} {binding : Binding} (found : context[index]? = some binding) :
    ∃ tree, Completes assumptions context (.bound index) binding.type (variableUses context index) tree := by
  refine ⟨emptyTree, ?_⟩
  intro annotations path _
  apply finish_complete ⟨binding.type, variableUses context index, .bound found⟩
  · intro mode
    rw [elaborate]
    split
    · rename_i actual discovered
      rw [found] at discovered
      cases discovered
      rfl
    · rename_i absent
      rw [found] at absent
      contradiction
  · exact sameType_refl _ _
  · rfl

public theorem completes_natural (assumptions : Assumptions) (context : Context) (value : Nat) :
    ∃ tree, Completes assumptions context (.nat value) .natural (zeroUses context) tree := by
  refine ⟨emptyTree, ?_⟩
  intro annotations path _
  apply finish_complete ⟨.natural, zeroUses context, .natural context value⟩
  · intro mode
    rfl
  · exact sameType_refl _ _
  · rfl

public theorem completes_boolean (assumptions : Assumptions) (context : Context) (value : Bool) :
    ∃ tree, Completes assumptions context (.boolean value) .boolean (zeroUses context) tree := by
  refine ⟨emptyTree, ?_⟩
  intro annotations path _
  apply finish_complete ⟨.boolean, zeroUses context, .boolean context value⟩
  · intro mode
    rfl
  · exact sameType_refl _ _
  · rfl

public theorem completes_label (assumptions : Assumptions) (context : Context) (value : String) :
    ∃ tree, Completes assumptions context (.label value) (literalType value) (zeroUses context) tree := by
  refine ⟨emptyTree, ?_⟩
  intro annotations path _
  apply finish_complete ⟨literalType value, zeroUses context, .label context value⟩
  · intro mode
    rfl
  · exact sameType_refl _ _
  · rfl

theorem modes_complete {assumptions : Assumptions} {annotations : Annotations} {context : Context}
    {path : List Nat} {term : Term} {derived : Ty} {uses : Uses}
    (synthesized : Synth assumptions context term)
    (synth : synthAt assumptions annotations context path term = .ok synthesized)
    (checks : ∀ expected, checkAt assumptions annotations context path term expected =
      finish assumptions annotations path synthesized (.check expected))
    (agrees : sameType assumptions synthesized.type derived = true) (sameUses : synthesized.uses = uses) :
    Yields (synthAt assumptions annotations context path term)
      (fun result => sameType assumptions result.type derived = true ∧ result.uses = uses) ∧
    ∀ expected, sameType assumptions derived expected = true →
      Yields (checkAt assumptions annotations context path term expected) (fun result => result.uses = uses) := by
  constructor
  · rw [synth]
    exact ⟨agrees, sameUses⟩
  · intro expected agreement
    have accepted : sameType assumptions synthesized.type expected = true := sameType_trans agrees agreement
    rw [checks, finish, dif_pos accepted]
    exact sameUses

public theorem completes_lambda {assumptions : Assumptions} {context : Context} {body : Term}
    {annotation : LambdaAnnotation} {uses : Uses}
    (safe : safeUses (⟨annotation.domain, annotation.parameter⟩ :: context) uses = true)
    (valid : validContext assumptions.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: context) = true)
    (captures : reusableAllowed assumptions annotation.reuse context uses.tail = true)
    (fits : annotation.parameter.fits (uses.headD 0) = true)
    (ih : ∃ tree, Completes assumptions (⟨annotation.domain, annotation.parameter⟩ :: context)
      body annotation.codomain uses tree) :
    ∃ tree, Completes assumptions context (.lam body)
      (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain) uses.tail tree := by
  obtain ⟨bodyTree, completeBody⟩ := ih
  refine ⟨.node (some annotation) [bodyTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have child : Realizes annotations (path ++ [0]) bodyTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨result, accepted, sameUses⟩ :=
    ((completeBody annotations (path ++ [0]) child).2 annotation.codomain (sameType_refl _ _)).elim
  have safe' : safeUses (⟨annotation.domain, annotation.parameter⟩ :: context) result.uses = true := by
    rw [sameUses]; exact safe
  have captures' : reusableAllowed assumptions annotation.reuse context result.uses.tail = true := by
    rw [sameUses]; exact captures
  have fits' : annotation.parameter.fits (result.uses.headD 0) = true := by
    rw [sameUses]; exact fits
  let synthesized : Synth assumptions context (.lam body) :=
    ⟨.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain,
      result.uses.tail, .lambda result.derivation safe' valid captures' fits'⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.lam body) .synth = .ok synthesized
    rw [elaborate]
    simp [root, accepted, bind, Except.bind, Functor.map, Except.map,
      pure, Except.pure, need_ok safe', need_ok valid, need_ok captures', need_ok fits', synthesized]
  · intro expected
    change elaborate assumptions annotations context path (.lam body) (.check expected) = _
    rw [elaborate]
    simp [root, accepted, bind, Except.bind, Functor.map, Except.map,
      pure, Except.pure, need_ok safe', need_ok valid, need_ok captures', need_ok fits', synthesized, checkedSynth]
  · exact sameType_refl _ _
  · exact congrArg List.tail sameUses

public theorem fields_nil_complete (assumptions : Assumptions) (context : Context) :
    ∃ trees, FieldsComplete assumptions context [] .emptyRow (zeroUses context) trees := by
  refine ⟨[], ?_⟩
  intro annotations path index _
  rfl

public theorem fields_cons_complete {assumptions : Assumptions} {context : Context}
    {name : String} {body : Term} {rest : List (String × Term)} {type row : Ty} {bu ru : Uses}
    (nonComputation : type.isComputation = false)
    (head : ∃ tree, Completes assumptions context body type bu tree)
    (tail : ∃ trees, FieldsComplete assumptions context rest row ru trees) :
    ∃ trees, FieldsComplete assumptions context ((name, body) :: rest)
      (.field name type row) (addUses bu ru) trees := by
  obtain ⟨bodyTree, completeBody⟩ := head
  obtain ⟨restTrees, completeRest⟩ := tail
  refine ⟨bodyTree :: restTrees, ?_⟩
  intro annotations path index realizes
  obtain ⟨first, checkedFirst, firstUses⟩ :=
    ((completeBody annotations (path ++ [index]) realizes.head).2 type (sameType_refl _ _)).elim
  obtain ⟨later, checkedLater, laterUses⟩ :=
    (completeRest annotations path (index + 1) realizes.tail).elim
  have nonActivity : (!type.isComputation) = true := by simp [nonComputation]
  rw [checkFields]
  simp only [↓reduceDIte, checkedFirst, checkedLater, bind, Except.bind, need_ok nonActivity,
    pure, Except.pure, Yields]
  change addUses first.uses later.uses = addUses bu ru
  rw [firstUses, laterUses]

@[expose] public def hint (domain codomain : Ty) : LambdaAnnotation :=
  ⟨domain, codomain, .unrestricted, .reusable⟩

public theorem completes_record {assumptions : Assumptions} {context : Context}
    {fields : List (String × Term)} {row : Ty} {uses : Uses}
    (ih : ∃ trees, FieldsComplete assumptions context fields row uses trees) :
    ∃ tree, Completes assumptions context (.record fields) row uses tree := by
  obtain ⟨trees, completeFields⟩ := ih
  refine ⟨.node (some (hint .emptyRow row)) trees, ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  obtain ⟨result, accepted, sameUses⟩ := (completeFields annotations path 0 realizes.forest).elim
  let synthesized : Synth assumptions context (.record fields) := ⟨row, result.uses, .record result.derivation⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.record fields) .synth = .ok synthesized
    rw [elaborate]
    simp [introduce, root, hint, accepted, bind, Except.bind, Functor.map, Except.map,
      pure, Except.pure, synthesized]
  · intro expected
    change elaborate assumptions annotations context path (.record fields) (.check expected) = _
    rw [elaborate]
    simp [introduce, root, hint, accepted, bind, Except.bind, Functor.map, Except.map,
      pure, Except.pure, synthesized, checkedSynth]
  · exact sameType_refl _ _
  · exact sameUses

public theorem completes_done {assumptions : Assumptions} {context : Context} {value : Term}
    {plan response result : Ty} {uses : Uses} (nonComputation : result.isComputation = false)
    (ih : ∃ tree, Completes assumptions context value result uses tree) :
    ∃ tree, Completes assumptions context (.done value) (.computation plan response result) uses tree := by
  obtain ⟨valueTree, completeValue⟩ := ih
  refine ⟨.node (some (hint .emptyRow (.computation plan response result))) [valueTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have child : Realizes annotations (path ++ [0]) valueTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨inner, accepted, sameUses⟩ :=
    ((completeValue annotations (path ++ [0]) child).2 result (sameType_refl _ _)).elim
  have nonActivity : (!result.isComputation) = true := by simp [nonComputation]
  let synthesized : Synth assumptions context (.done value) :=
    ⟨.computation plan response result, inner.uses, .done inner.derivation nonComputation⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.done value) .synth = .ok synthesized
    rw [elaborate]
    simp [root, hint, accepted, need_ok nonActivity, bind, Except.bind, Functor.map, Except.map,
      pure, Except.pure, synthesized]
  · intro expected
    change elaborate assumptions annotations context path (.done value) (.check expected) = _
    rw [elaborate]
    simp [root, hint, accepted, need_ok nonActivity, bind, Except.bind, Functor.map, Except.map,
      pure, Except.pure, synthesized]
  · exact sameType_refl _ _
  · exact sameUses

public theorem completes_application {assumptions : Assumptions} {context : Context}
    {function argument : Term} {functionType domain codomain : Ty} {fu au : Uses}
    {reuse : Reuse} {quantity : Quantity}
    (shape : callable functionType = .arrow reuse quantity domain codomain)
    (allowed : argumentAllowed assumptions quantity context domain au = true)
    (ihF : ∃ tree, Completes assumptions context function functionType fu tree)
    (ihA : ∃ tree, Completes assumptions context argument domain au tree) :
    ∃ tree, Completes assumptions context (.app function argument) codomain (addUses fu au) tree := by
  obtain ⟨functionTree, completeFunction⟩ := ihF
  obtain ⟨argumentTree, completeArgument⟩ := ihA
  refine ⟨.node (some (hint functionType codomain)) [functionTree, argumentTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atFunction : Realizes annotations (path ++ [0]) functionTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atArgument : Realizes annotations (path ++ [1]) argumentTree := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨fn, checkedFn, fnUses⟩ :=
    ((completeFunction annotations (path ++ [0]) atFunction).2 functionType (sameType_refl _ _)).elim
  obtain ⟨arg, checkedArg, argUses⟩ :=
    ((completeArgument annotations (path ++ [1]) atArgument).2 domain (sameType_refl _ _)).elim
  have allowed' : argumentAllowed assumptions quantity context domain arg.uses = true := by
    rw [argUses]; exact allowed
  let synthesized : Synth assumptions context (.app function argument) :=
    ⟨codomain, addUses fn.uses arg.uses, .application fn.derivation arg.derivation shape rfl allowed'⟩
  apply finish_complete synthesized
  · intro mode
    rw [elaborate]
    simp [root, hint, checkedFn, checkedArg, rawHead, shape, need_ok allowed',
      bind, Except.bind, Functor.map, Except.map, pure, Except.pure, synthesized, checkedSynth]
    split
    · rename_i r q d c observed
      rw [rawHead, shape] at observed
      cases observed
      simp [checkedArg, need_ok allowed', bind, Except.bind, pure, Except.pure, synthesized]
    · rename_i absent
      exact (absent reuse quantity domain codomain (by rw [rawHead]; exact shape)).elim
  · exact sameType_refl _ _
  · change addUses fn.uses arg.uses = addUses fu au
    rw [fnUses, argUses]

public theorem completes_get {assumptions : Assumptions} {context : Context} {target : Term}
    {targetType member : Ty} {uses : Uses} {name : String} {fuel : Nat}
    (found : targetType.lookup assumptions.bounds fuel name = some member)
    (free : linearFree context uses = true)
    (ih : ∃ tree, Completes assumptions context target targetType uses tree) :
    ∃ tree, Completes assumptions context (.get target name) member uses tree := by
  obtain ⟨targetTree, completeTarget⟩ := ih
  refine ⟨.node (some (hint targetType member)) [targetTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have child : Realizes annotations (path ++ [0]) targetTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨value, accepted, sameUses⟩ :=
    ((completeTarget annotations (path ++ [0]) child).2 targetType (sameType_refl _ _)).elim
  have lookup : lookupV assumptions.bounds [] targetType name = some member :=
    (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
  have free' : linearFree context value.uses = true := by rw [sameUses]; exact free
  let synthesized : Synth assumptions context (.get target name) :=
    ⟨member, value.uses, .get value.derivation found free'⟩
  apply finish_complete synthesized
  · intro mode
    rw [elaborate]
    simp only [root, hint, accepted, bind, Except.bind, Functor.map, Except.map, checkedSynth]
    split
    · rename_i disclosed actual
      rw [lookup] at actual
      cases actual
      rw [need_ok free']
    · rename_i absent
      rw [lookup] at absent
      contradiction
  · exact sameType_refl _ _
  · exact sameUses

public theorem completes_reflect {assumptions : Assumptions} {context : Context} {target : Term}
    {specType targetType : Ty} {uses : Uses}
    (free : linearFree context uses = true)
    (ih : ∃ tree, Completes assumptions context target (.prototype specType targetType) uses tree) :
    ∃ tree, Completes assumptions context (.reflect target) specType uses tree := by
  obtain ⟨targetTree, completeTarget⟩ := ih
  refine ⟨.node (some (hint (.prototype specType targetType) specType)) [targetTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have child : Realizes annotations (path ++ [0]) targetTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨value, accepted, sameUses⟩ :=
    ((completeTarget annotations (path ++ [0]) child).2 (.prototype specType targetType) (sameType_refl _ _)).elim
  have free' : linearFree context value.uses = true := by rw [sameUses]; exact free
  let synthesized : Synth assumptions context (.reflect target) :=
    ⟨specType, value.uses, .reflect value.derivation free'⟩
  apply finish_complete synthesized
  · intro mode
    rw [elaborate]
    simp [root, hint, accepted, rawHead, checkedSynth, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure, synthesized]
    split
    · rename_i first second observed
      rw [rawHead] at observed
      cases observed
      rw [need_ok free']
    · rename_i absent
      exact (absent specType targetType (rawHead (.prototype specType targetType))).elim
  · exact sameType_refl _ _
  · exact sameUses

public theorem completes_metadata {assumptions : Assumptions} {context : Context} {target : Term}
    {metadataType extensionType : Ty} {uses : Uses}
    (free : linearFree context uses = true)
    (ih : ∃ tree, Completes assumptions context target (.specification metadataType extensionType) uses tree) :
    ∃ tree, Completes assumptions context (.metadata target) metadataType uses tree := by
  obtain ⟨targetTree, completeTarget⟩ := ih
  refine ⟨.node (some (hint (.specification metadataType extensionType) metadataType)) [targetTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have child : Realizes annotations (path ++ [0]) targetTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨value, accepted, sameUses⟩ :=
    ((completeTarget annotations (path ++ [0]) child).2 (.specification metadataType extensionType) (sameType_refl _ _)).elim
  have free' : linearFree context value.uses = true := by rw [sameUses]; exact free
  let synthesized : Synth assumptions context (.metadata target) :=
    ⟨metadataType, value.uses, .metadata value.derivation free'⟩
  apply finish_complete synthesized
  · intro mode
    rw [elaborate]
    simp [root, hint, accepted, rawHead, checkedSynth, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure, synthesized]
    split
    · rename_i first second observed
      rw [rawHead] at observed
      cases observed
      rw [need_ok free']
    · rename_i absent
      exact (absent metadataType extensionType (rawHead (.specification metadataType extensionType))).elim
  · exact sameType_refl _ _
  · exact sameUses

public theorem completes_project {assumptions : Assumptions} {context : Context} {target : Term}
    {specType targetType : Ty} {uses : Uses}
    (free : linearFree context uses = true)
    (ih : ∃ tree, Completes assumptions context target (.prototype specType targetType) uses tree) :
    ∃ tree, Completes assumptions context (.project target) targetType uses tree := by
  obtain ⟨targetTree, completeTarget⟩ := ih
  refine ⟨.node (some (hint (.prototype specType targetType) targetType)) [targetTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have child : Realizes annotations (path ++ [0]) targetTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨value, accepted, sameUses⟩ :=
    ((completeTarget annotations (path ++ [0]) child).2 (.prototype specType targetType) (sameType_refl _ _)).elim
  have free' : linearFree context value.uses = true := by rw [sameUses]; exact free
  let synthesized : Synth assumptions context (.project target) :=
    ⟨targetType, value.uses, .project value.derivation free'⟩
  apply finish_complete synthesized
  · intro mode
    rw [elaborate]
    simp [root, hint, accepted, rawHead, checkedSynth, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure, synthesized]
    split
    · rename_i first second observed
      rw [rawHead] at observed
      cases observed
      rw [need_ok free']
    · rename_i absent
      exact (absent specType targetType (rawHead (.prototype specType targetType))).elim
  · exact sameType_refl _ _
  · exact sameUses

public theorem completes_specification {assumptions : Assumptions} {context : Context}
    {metadata extension : Term} {metadataType extensionType : Ty} {mu eu : Uses}
    (pureFirst : metadataType.isComputation = false) (pureSecond : extensionType.isComputation = false)
    (free : linearFree context mu = true)
    (ihFirst : ∃ tree, Completes assumptions context metadata metadataType mu tree)
    (ihSecond : ∃ tree, Completes assumptions context extension extensionType eu tree) :
    ∃ tree, Completes assumptions context (.specification metadata extension)
      (.specification metadataType extensionType) (addUses mu eu) tree := by
  obtain ⟨firstTree, completeFirst⟩ := ihFirst
  obtain ⟨secondTree, completeSecond⟩ := ihSecond
  refine ⟨.node (some (hint .emptyRow (.specification metadataType extensionType))) [firstTree, secondTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atFirst : Realizes annotations (path ++ [0]) firstTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atSecond : Realizes annotations (path ++ [1]) secondTree := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨first, checkedFirst, firstUses⟩ :=
    ((completeFirst annotations (path ++ [0]) atFirst).2 metadataType (sameType_refl _ _)).elim
  obtain ⟨second, checkedSecond, secondUses⟩ :=
    ((completeSecond annotations (path ++ [1]) atSecond).2 extensionType (sameType_refl _ _)).elim
  have firstPure : (!metadataType.isComputation) = true := by simp [pureFirst]
  have secondPure : (!extensionType.isComputation) = true := by simp [pureSecond]
  have free' : linearFree context first.uses = true := by rw [firstUses]; exact free
  let synthesized : Synth assumptions context (.specification metadata extension) :=
    ⟨.specification metadataType extensionType, addUses first.uses second.uses,
      .specification first.derivation second.derivation pureFirst pureSecond free'⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.specification metadata extension) .synth = .ok synthesized
    rw [elaborate]
    simp [introduce, root, hint, checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, need_ok free', bind, Except.bind, Functor.map,
      Except.map, pure, Except.pure, synthesized, checkedSynth]
    split
    · rename_i failed equation
      split at equation
      · rename_i firstType secondType observed
        rw [rawHead] at observed
        cases observed
        simp only [checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, need_ok free', bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
      · rename_i absent
        exact (absent metadataType extensionType (rawHead (.specification metadataType extensionType))).elim
    · rename_i answer equation
      split at equation
      · rename_i firstType secondType observed
        rw [rawHead] at observed
        cases observed
        simp only [checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, need_ok free', bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
        rfl
      · rename_i absent
        exact (absent metadataType extensionType (rawHead (.specification metadataType extensionType))).elim
  · intro expected
    change elaborate assumptions annotations context path (.specification metadata extension) (.check expected) = _
    rw [elaborate]
    simp [introduce, root, hint, checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, need_ok free', bind, Except.bind, Functor.map,
      Except.map, pure, Except.pure, synthesized, checkedSynth]
    split
    · rename_i failed equation
      split at equation
      · rename_i firstType secondType observed
        rw [rawHead] at observed
        cases observed
        simp only [checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, need_ok free', bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
      · rename_i absent
        exact (absent metadataType extensionType (rawHead (.specification metadataType extensionType))).elim
    · rename_i answer equation
      split at equation
      · rename_i firstType secondType observed
        rw [rawHead] at observed
        cases observed
        simp only [checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, need_ok free', bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
        rfl
      · rename_i absent
        exact (absent metadataType extensionType (rawHead (.specification metadataType extensionType))).elim
  · exact sameType_refl _ _
  · change addUses first.uses second.uses = addUses mu eu
    rw [firstUses, secondUses]

public theorem completes_prototype {assumptions : Assumptions} {context : Context}
    {spec target : Term} {specType targetType : Ty} {su tu : Uses}
    (pureFirst : specType.isComputation = false) (pureSecond : targetType.isComputation = false)
    (ihFirst : ∃ tree, Completes assumptions context spec specType su tree)
    (ihSecond : ∃ tree, Completes assumptions context target targetType tu tree) :
    ∃ tree, Completes assumptions context (.prototype spec target)
      (.prototype specType targetType) (addUses su tu) tree := by
  obtain ⟨firstTree, completeFirst⟩ := ihFirst
  obtain ⟨secondTree, completeSecond⟩ := ihSecond
  refine ⟨.node (some (hint .emptyRow (.prototype specType targetType))) [firstTree, secondTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atFirst : Realizes annotations (path ++ [0]) firstTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atSecond : Realizes annotations (path ++ [1]) secondTree := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨first, checkedFirst, firstUses⟩ :=
    ((completeFirst annotations (path ++ [0]) atFirst).2 specType (sameType_refl _ _)).elim
  obtain ⟨second, checkedSecond, secondUses⟩ :=
    ((completeSecond annotations (path ++ [1]) atSecond).2 targetType (sameType_refl _ _)).elim
  have firstPure : (!specType.isComputation) = true := by simp [pureFirst]
  have secondPure : (!targetType.isComputation) = true := by simp [pureSecond]
  let synthesized : Synth assumptions context (.prototype spec target) :=
    ⟨.prototype specType targetType, addUses first.uses second.uses,
      .prototype first.derivation second.derivation pureFirst pureSecond⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.prototype spec target) .synth = .ok synthesized
    rw [elaborate]
    simp [introduce, root, hint, checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, bind, Except.bind, Functor.map,
      Except.map, pure, Except.pure, synthesized, checkedSynth]
    split
    · rename_i failed equation
      split at equation
      · rename_i firstType secondType observed
        rw [rawHead] at observed
        cases observed
        simp only [checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
      · rename_i absent
        exact (absent specType targetType (rawHead (.prototype specType targetType))).elim
    · rename_i answer equation
      split at equation
      · rename_i firstType secondType observed
        rw [rawHead] at observed
        cases observed
        simp only [checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
        rfl
      · rename_i absent
        exact (absent specType targetType (rawHead (.prototype specType targetType))).elim
  · intro expected
    change elaborate assumptions annotations context path (.prototype spec target) (.check expected) = _
    rw [elaborate]
    simp [introduce, root, hint, checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, bind, Except.bind, Functor.map,
      Except.map, pure, Except.pure, synthesized, checkedSynth]
    split
    · rename_i failed equation
      split at equation
      · rename_i firstType secondType observed
        rw [rawHead] at observed
        cases observed
        simp only [checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
      · rename_i absent
        exact (absent specType targetType (rawHead (.prototype specType targetType))).elim
    · rename_i answer equation
      split at equation
      · rename_i firstType secondType observed
        rw [rawHead] at observed
        cases observed
        simp only [checkedFirst, checkedSecond, need_ok firstPure, need_ok secondPure, bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
        rfl
      · rename_i absent
        exact (absent specType targetType (rawHead (.prototype specType targetType))).elim
  · exact sameType_refl _ _
  · change addUses first.uses second.uses = addUses su tu
    rw [firstUses, secondUses]

public theorem completes_binary {assumptions : Assumptions} {context : Context}
    {primitive : Primitive} {left right : Term} {input output : Ty} {lu ru : Uses}
    (shape : primitiveTypes primitive = (input, output))
    (ihL : ∃ tree, Completes assumptions context left input lu tree)
    (ihR : ∃ tree, Completes assumptions context right input ru tree) :
    ∃ tree, Completes assumptions context (.binary primitive left right) output (addUses lu ru) tree := by
  have inputEq : (primitiveTypes primitive).1 = input := congrArg Prod.fst shape
  have outputEq : (primitiveTypes primitive).2 = output := congrArg Prod.snd shape
  subst input
  subst output
  obtain ⟨leftTree, completeLeft⟩ := ihL
  obtain ⟨rightTree, completeRight⟩ := ihR
  refine ⟨.node (some (hint (primitiveTypes primitive).1 (primitiveTypes primitive).2)) [leftTree, rightTree], ?_⟩
  intro annotations path realizes
  have atLeft : Realizes annotations (path ++ [0]) leftTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atRight : Realizes annotations (path ++ [1]) rightTree := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨first, checkedFirst, firstUses⟩ :=
    ((completeLeft annotations (path ++ [0]) atLeft).2 (primitiveTypes primitive).1 (sameType_refl _ _)).elim
  obtain ⟨second, checkedSecond, secondUses⟩ :=
    ((completeRight annotations (path ++ [1]) atRight).2 (primitiveTypes primitive).1 (sameType_refl _ _)).elim
  let synthesized : Synth assumptions context (.binary primitive left right) :=
    ⟨(primitiveTypes primitive).2, addUses first.uses second.uses, .binary shape first.derivation second.derivation⟩
  apply finish_complete synthesized
  · intro mode
    rw [elaborate]
    simp [checkedFirst, checkedSecond, bind, Except.bind, pure, Except.pure, synthesized]
  · exact sameType_refl _ _
  · change addUses first.uses second.uses = addUses lu ru
    rw [firstUses, secondUses]

public theorem completes_ifBool {assumptions : Assumptions} {context : Context}
    {condition whenTrue whenFalse : Term} {result : Ty} {cu tu fu : Uses}
    (ihC : ∃ tree, Completes assumptions context condition .boolean cu tree)
    (ihT : ∃ tree, Completes assumptions context whenTrue result tu tree)
    (ihF : ∃ tree, Completes assumptions context whenFalse result fu tree)
    (agreeing : branchesAgree context tu fu = true) :
    ∃ tree, Completes assumptions context (.ifBool condition whenTrue whenFalse) result
      (addUses cu (joinUses tu fu)) tree := by
  obtain ⟨conditionTree, completeCondition⟩ := ihC
  obtain ⟨trueTree, completeTrue⟩ := ihT
  obtain ⟨falseTree, completeFalse⟩ := ihF
  refine ⟨.node (some (hint .emptyRow result)) [conditionTree, trueTree, falseTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atCondition : Realizes annotations (path ++ [0]) conditionTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atTrue : Realizes annotations (path ++ [1]) trueTree := by
    simpa [AnnotationTree.child] using realizes.child 1
  have atFalse : Realizes annotations (path ++ [2]) falseTree := by
    simpa [AnnotationTree.child] using realizes.child 2
  obtain ⟨conditionValue, checkedCondition, conditionUses⟩ :=
    ((completeCondition annotations (path ++ [0]) atCondition).2 .boolean (sameType_refl _ _)).elim
  obtain ⟨trueValue, checkedTrue, trueUses⟩ :=
    ((completeTrue annotations (path ++ [1]) atTrue).2 result (sameType_refl _ _)).elim
  obtain ⟨falseValue, checkedFalse, falseUses⟩ :=
    ((completeFalse annotations (path ++ [2]) atFalse).2 result (sameType_refl _ _)).elim
  have agreeing' : branchesAgree context trueValue.uses falseValue.uses = true := by
    rw [trueUses, falseUses]; exact agreeing
  let synthesized : Synth assumptions context (.ifBool condition whenTrue whenFalse) :=
    ⟨result, addUses conditionValue.uses (joinUses trueValue.uses falseValue.uses),
      .ifBool conditionValue.derivation trueValue.derivation falseValue.derivation agreeing'⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.ifBool condition whenTrue whenFalse) .synth = .ok synthesized
    rw [elaborate]
    simp [introduce, root, hint, checkedCondition, checkedTrue, checkedFalse, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure, synthesized, need_ok agreeing']
  · intro expected
    change elaborate assumptions annotations context path (.ifBool condition whenTrue whenFalse) (.check expected) = _
    rw [elaborate]
    simp [introduce, root, hint, checkedCondition, checkedTrue, checkedFalse, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure, synthesized, checkedSynth, need_ok agreeing']
  · exact sameType_refl _ _
  · change addUses conditionValue.uses (joinUses trueValue.uses falseValue.uses) = addUses cu (joinUses tu fu)
    rw [conditionUses, trueUses, falseUses]

public theorem completes_perform {assumptions : Assumptions} {context : Context}
    {plan : Term} {planType response : Ty} {uses : Uses}
    (isPlan : planType.isPlan = true) (data : response.isData = true)
    (ih : ∃ tree, Completes assumptions context plan planType uses tree) :
    ∃ tree, Completes assumptions context (.perform plan) (.computation planType response response) uses tree := by
  obtain ⟨planTree, completePlan⟩ := ih
  refine ⟨.node (some (hint planType response)) [planTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have child : Realizes annotations (path ++ [0]) planTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨value, accepted, sameUses⟩ :=
    ((completePlan annotations (path ++ [0]) child).2 planType (sameType_refl _ _)).elim
  let synthesized : Synth assumptions context (.perform plan) :=
    ⟨.computation planType response response, value.uses, .perform value.derivation isPlan data⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.perform plan) .synth = .ok synthesized
    rw [elaborate]
    simp [introduce, root, hint, accepted, need_ok isPlan, need_ok data, bind, Except.bind, Functor.map,
      Except.map, pure, Except.pure, synthesized, checkedSynth]
    split
    · rename_i failed equation
      split at equation
      · rename_i planType1 response1 result observed
        rw [rawHead] at observed
        cases observed
        simp only [accepted, need_ok isPlan, need_ok data, bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
      · rename_i absent
        exact (absent planType response response (rawHead (.computation planType response response))).elim
    · rename_i answer equation
      split at equation
      · rename_i planType1 response1 result observed
        rw [rawHead] at observed
        cases observed
        simp only [accepted, need_ok isPlan, need_ok data, bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
        rfl
      · rename_i absent
        exact (absent planType response response (rawHead (.computation planType response response))).elim
  · intro expected
    change elaborate assumptions annotations context path (.perform plan) (.check expected) = _
    rw [elaborate]
    simp [introduce, root, hint, accepted, need_ok isPlan, need_ok data, bind, Except.bind, Functor.map,
      Except.map, pure, Except.pure, synthesized, checkedSynth]
    split
    · rename_i failed equation
      split at equation
      · rename_i planType1 response1 result observed
        rw [rawHead] at observed
        cases observed
        simp only [accepted, need_ok isPlan, need_ok data, bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
      · rename_i absent
        exact (absent planType response response (rawHead (.computation planType response response))).elim
    · rename_i answer equation
      split at equation
      · rename_i planType1 response1 result observed
        rw [rawHead] at observed
        cases observed
        simp only [accepted, need_ok isPlan, need_ok data, bind, Except.bind, pure, Except.pure, dif_pos rfl] at equation
        cases equation
        rfl
      · rename_i absent
        exact (absent planType response response (rawHead (.computation planType response response))).elim
  · exact sameType_refl _ _
  · exact sameUses

public theorem completes_ifZero {assumptions : Assumptions} {context : Context}
    {value zero successor : Term} {result : Ty} {vu zu su : Uses}
    (safe : safeUses (⟨.natural, .unrestricted⟩ :: context) su = true)
    (agreeing : branchesAgree context zu su.tail = true)
    (ihV : ∃ tree, Completes assumptions context value .natural vu tree)
    (ihZ : ∃ tree, Completes assumptions context zero result zu tree)
    (ihS : ∃ tree, Completes assumptions (⟨.natural, .unrestricted⟩ :: context) successor result su tree) :
    ∃ tree, Completes assumptions context (.ifZero value zero successor) result
      (addUses vu (joinUses zu su.tail)) tree := by
  obtain ⟨valueTree, completeValue⟩ := ihV
  obtain ⟨zeroTree, completeZero⟩ := ihZ
  obtain ⟨successorTree, completeSuccessor⟩ := ihS
  refine ⟨.node (some (hint .emptyRow result)) [valueTree, zeroTree, successorTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atValue : Realizes annotations (path ++ [0]) valueTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atZero : Realizes annotations (path ++ [1]) zeroTree := by
    simpa [AnnotationTree.child] using realizes.child 1
  have atSuccessor : Realizes annotations (path ++ [2]) successorTree := by
    simpa [AnnotationTree.child] using realizes.child 2
  obtain ⟨first, checkedFirst, firstUses⟩ :=
    ((completeValue annotations (path ++ [0]) atValue).2 .natural (sameType_refl _ _)).elim
  obtain ⟨base, checkedBase, baseUses⟩ :=
    ((completeZero annotations (path ++ [1]) atZero).2 result (sameType_refl _ _)).elim
  obtain ⟨next, checkedNext, nextUses⟩ :=
    ((completeSuccessor annotations (path ++ [2]) atSuccessor).2 result (sameType_refl _ _)).elim
  have safe' : safeUses (⟨.natural, .unrestricted⟩ :: context) next.uses = true := by
    rw [nextUses]; exact safe
  have agreeing' : branchesAgree context base.uses next.uses.tail = true := by
    rw [baseUses, nextUses]; exact agreeing
  let synthesized : Synth assumptions context (.ifZero value zero successor) :=
    ⟨result, addUses first.uses (joinUses base.uses next.uses.tail),
      .ifZero first.derivation base.derivation next.derivation safe' agreeing'⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.ifZero value zero successor) .synth = .ok synthesized
    rw [elaborate]
    simp [introduce, root, hint, checkedFirst, checkedBase, checkedNext, need_ok safe', need_ok agreeing', bind,
      Except.bind, Functor.map, Except.map, pure, Except.pure, synthesized]
  · intro expected
    change elaborate assumptions annotations context path (.ifZero value zero successor) (.check expected) = _
    rw [elaborate]
    simp [introduce, root, hint, checkedFirst, checkedBase, checkedNext, need_ok safe', need_ok agreeing', bind,
      Except.bind, Functor.map, Except.map, pure, Except.pure, synthesized, checkedSynth]
  · exact sameType_refl _ _
  · change addUses first.uses (joinUses base.uses next.uses.tail) = addUses vu (joinUses zu su.tail)
    rw [firstUses, baseUses, nextUses]

public theorem completes_extend {assumptions : Assumptions} {context : Context}
    {target : Term} {fields : List (String × Term)} {targetType row : Ty} {tu fu : Uses} {fuel : Nat}
    (isRow : targetType.isRow assumptions.bounds fuel = true)
    (free : linearFree context tu = true)
    (ihT : ∃ tree, Completes assumptions context target targetType tu tree)
    (ihF : ∃ trees, FieldsComplete assumptions context fields row fu trees) :
    ∃ tree, Completes assumptions context (.extend target fields) (overlay row targetType) (addUses tu fu) tree := by
  obtain ⟨targetTree, completeTarget⟩ := ihT
  obtain ⟨fieldTrees, completeFields⟩ := ihF
  refine ⟨.node (some (hint targetType row)) [targetTree, .node none fieldTrees], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atTarget : Realizes annotations (path ++ [0]) targetTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atFields : Realizes annotations (path ++ [1]) (.node none fieldTrees) := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨prior, checkedPrior, priorUses⟩ :=
    ((completeTarget annotations (path ++ [0]) atTarget).2 targetType (sameType_refl _ _)).elim
  obtain ⟨members, checkedMembers, memberUses⟩ :=
    (completeFields annotations (path ++ [1]) 0 atFields.forest).elim
  have rowAccepted : isRowV assumptions.bounds [] targetType = true :=
    (isRowV_iff _ _).2 ⟨fuel, isRow⟩
  have free' : linearFree context prior.uses = true := by rw [priorUses]; exact free
  let synthesized : Synth assumptions context (.extend target fields) :=
    ⟨overlay row targetType, addUses prior.uses members.uses, .extend prior.derivation members.derivation isRow free'⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.extend target fields) .synth = .ok synthesized
    rw [elaborate]
    simp [root, hint, checkedPrior, checkedMembers, need_ok rowAccepted, need_ok (sameType_refl assumptions targetType),
      need_ok free', checkedSynth, bind, Except.bind, Functor.map, Except.map, pure, Except.pure, synthesized]
  · intro expected
    change elaborate assumptions annotations context path (.extend target fields) (.check expected) = _
    rw [elaborate]
    simp [finish, root, hint, checkedPrior, checkedMembers, need_ok rowAccepted,
      need_ok (sameType_refl assumptions targetType), need_ok free', checkedSynth, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure, synthesized] <;> rfl
  · exact sameType_refl _ _
  · change addUses prior.uses members.uses = addUses tu fu
    rw [priorUses, memberUses]

public theorem completes_inject {assumptions : Assumptions} {context : Context}
    {tag : String} {payload : Term} {payloadType row : Ty} {uses : Uses} {fuel : Nat}
    (found : row.lookup assumptions.bounds fuel tag = some payloadType)
    (nonComputation : payloadType.isComputation = false)
    (ih : ∃ tree, Completes assumptions context payload payloadType uses tree) :
    ∃ tree, Completes assumptions context (.inject tag payload) (.variant row) uses tree := by
  obtain ⟨payloadTree, completePayload⟩ := ih
  refine ⟨.node (some (hint payloadType (.variant row))) [payloadTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have injHead : injectionHead assumptions annotations path (.variant row) = .variant row := by
    simp [injectionHead, rawHead]
  have child : Realizes annotations (path ++ [0]) payloadTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨value, accepted, sameUses⟩ :=
    ((completePayload annotations (path ++ [0]) child).2 payloadType (sameType_refl _ _)).elim
  have lookup : lookupV assumptions.bounds [] row tag = some payloadType :=
    (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
  have nonActivity : (!payloadType.isComputation) = true := by simp [nonComputation]
  let synthesized : Synth assumptions context (.inject tag payload) :=
    ⟨.variant row, value.uses, .inject value.derivation found nonComputation⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.inject tag payload) .synth = .ok synthesized
    rw [elaborate]
    simp only [introduce, root, hint, rawHead, Option.isSome_some, ↓reduceIte]
    split
    · rename_i disclosed actual
      have identified : disclosed = row := by
        simpa only [injHead, Ty.variant.injEq] using actual.symm
      subst disclosed
      split
      · rename_i member actual
        rw [lookup] at actual
        cases actual
        simp [accepted, need_ok nonActivity, bind, Except.bind, Functor.map, Except.map,
          pure, Except.pure, synthesized]
      · rename_i absent
        rw [lookup] at absent
        contradiction
    · rename_i absent
      exact (absent row injHead).elim
  · intro expected
    change elaborate assumptions annotations context path (.inject tag payload) (.check expected) = _
    rw [elaborate]
    simp only [introduce, root, hint, rawHead, Option.isSome_some, ↓reduceIte]
    split
    · rename_i disclosed actual
      have identified : disclosed = row := by
        simpa only [injHead, Ty.variant.injEq] using actual.symm
      subst disclosed
      split
      · rename_i member actual
        rw [lookup] at actual
        cases actual
        simp [accepted, need_ok nonActivity, bind, Except.bind, Functor.map, Except.map,
          pure, Except.pure, synthesized, checkedSynth]
      · rename_i absent
        rw [lookup] at absent
        contradiction
    · rename_i absent
      exact (absent row injHead).elim
  · exact sameType_refl _ _
  · exact sameUses

public theorem completes_mix {assumptions : Assumptions} {context : Context}
    {lower upper : Term} {lowerType upperType self inherited middle provided : Ty} {lu uu : Uses}
    (shapeL : callable lowerType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle))
    (shapeU : callable upperType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted middle provided))
    (captures : reusableCaptures assumptions.shareableVariables context (addUses lu uu) = true)
    (shareSelf : self.shareableUnder assumptions.shareableVariables = true)
    (shareInherited : inherited.shareableUnder assumptions.shareableVariables = true)
    (shareMiddle : middle.shareableUnder assumptions.shareableVariables = true)
    (ihL : ∃ tree, Completes assumptions context lower lowerType lu tree)
    (ihU : ∃ tree, Completes assumptions context upper upperType uu tree) :
    ∃ tree, Completes assumptions context (.mix lower upper)
      (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided))
      (addUses lu uu) tree := by
  obtain ⟨lowerTree, completeLower⟩ := ihL
  obtain ⟨upperTree, completeUpper⟩ := ihU
  refine ⟨.node (some (hint lowerType upperType)) [lowerTree, upperTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atLower : Realizes annotations (path ++ [0]) lowerTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atUpper : Realizes annotations (path ++ [1]) upperTree := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨first, checkedFirst, firstUses⟩ :=
    ((completeLower annotations (path ++ [0]) atLower).2 lowerType (sameType_refl _ _)).elim
  obtain ⟨second, checkedSecond, secondUses⟩ :=
    ((completeUpper annotations (path ++ [1]) atUpper).2 upperType (sameType_refl _ _)).elim
  have captures' : reusableCaptures assumptions.shareableVariables context (addUses first.uses second.uses) = true := by
    rw [firstUses, secondUses]; exact captures
  let synthesized : Synth assumptions context (.mix lower upper) :=
    ⟨.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided),
      addUses first.uses second.uses,
      .mix first.derivation second.derivation shapeL shapeU captures' shareSelf shareInherited shareMiddle⟩
  apply finish_complete synthesized
  · intro mode
    rw [elaborate]
    simp [root, hint, checkedFirst, checkedSecond, rawHead, shapeL, shapeU,
      need_ok captures', need_ok shareSelf, need_ok shareInherited, need_ok shareMiddle,
      checkedSynth, bind, Except.bind, Functor.map, Except.map, pure, Except.pure, synthesized]
    split
    · rename_i s i m s' m' p observedL observedU
      rw [rawHead, shapeL] at observedL
      rw [rawHead, shapeU] at observedU
      cases observedL
      cases observedU
      simp [need_ok captures', need_ok shareSelf, need_ok shareInherited, need_ok shareMiddle,
        bind, Except.bind, pure, Except.pure, synthesized]
    · rename_i absent
      exact (absent self inherited middle self middle provided
        (by rw [rawHead]; exact shapeL) (by rw [rawHead]; exact shapeU)).elim
  · exact sameType_refl _ _
  · change addUses first.uses second.uses = addUses lu uu
    rw [firstUses, secondUses]

public theorem completes_fix {assumptions : Assumptions} {context : Context}
    {spec inheritedTerm : Term} {specType inherited target : Ty} {su iu : Uses}
    (shape : callable specType = .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target))
    (share : target.shareableUnder assumptions.shareableVariables = true)
    (allowed : argumentAllowed assumptions .unrestricted context inherited iu = true)
    (captures : reusableCaptures assumptions.shareableVariables context su = true)
    (ihS : ∃ tree, Completes assumptions context spec specType su tree)
    (ihI : ∃ tree, Completes assumptions context inheritedTerm inherited iu tree) :
    ∃ tree, Completes assumptions context (.fix spec inheritedTerm) target (addUses su iu) tree := by
  obtain ⟨specTree, completeSpec⟩ := ihS
  obtain ⟨inheritedTree, completeInherited⟩ := ihI
  refine ⟨.node (some (hint specType target)) [specTree, inheritedTree], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atSpec : Realizes annotations (path ++ [0]) specTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atInherited : Realizes annotations (path ++ [1]) inheritedTree := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨code, checkedCode, codeUses⟩ :=
    ((completeSpec annotations (path ++ [0]) atSpec).2 specType (sameType_refl _ _)).elim
  obtain ⟨base, checkedBase, baseUses⟩ :=
    ((completeInherited annotations (path ++ [1]) atInherited).2 inherited (sameType_refl _ _)).elim
  have allowed' : argumentAllowed assumptions .unrestricted context inherited base.uses = true := by
    rw [baseUses]; exact allowed
  have captures' : reusableCaptures assumptions.shareableVariables context code.uses = true := by
    rw [codeUses]; exact captures
  let synthesized : Synth assumptions context (.fix spec inheritedTerm) :=
    ⟨target, addUses code.uses base.uses,
      .fix code.derivation shape base.derivation share allowed' captures'⟩
  apply finish_complete synthesized
  · intro mode
    rw [elaborate]
    simp [root, hint, checkedCode, checkedBase, rawHead, shape,
      need_ok share, need_ok allowed', need_ok captures', checkedSynth, bind, Except.bind,
      Functor.map, Except.map, pure, Except.pure, synthesized]
    split
    · rename_i t i out observed
      rw [rawHead, shape] at observed
      cases observed
      simp [checkedBase, need_ok share, need_ok allowed', need_ok captures',
        bind, Except.bind, pure, Except.pure, synthesized]
    · rename_i absent
      exact (absent target inherited target (by rw [rawHead]; exact shape)).elim
  · exact sameType_refl _ _
  · change addUses code.uses base.uses = addUses su iu
    rw [codeUses, baseUses]

@[expose] public def ArmsComplete (assumptions : Assumptions) (context : Context) (q : Quantity)
    (arms : List (String × Term)) (row result : Ty) (uses : Uses) (trees : List AnnotationTree) : Prop :=
  ∀ annotations path index head, ForestRealizes annotations path index trees →
    labelsDistinct arms = true →
    (∀ name, name ∈ arms.map Prod.fst → rowMember head name = rowMember row name) →
    Yields (checkArms assumptions annotations context q path index head result arms)
      (fun answer => answer.row = row ∧ answer.uses = uses ∧ answer.quantity = q)

theorem labelsDistinct_cons {name : String} {body : Term} {rest : List (String × Term)}
    (distinct : labelsDistinct ((name, body) :: rest) = true) :
    name ∉ rest.map Prod.fst ∧ labelsDistinct rest = true := by
  simp only [labelsDistinct, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at distinct
  refine ⟨?_, distinct.2⟩
  intro member
  obtain ⟨⟨label, term⟩, inside, rfl⟩ := List.mem_map.mp member
  exact distinct.1 _ inside rfl

public theorem arms_nil_complete (assumptions : Assumptions) (context : Context) (q : Quantity) (result : Ty) :
    ∃ trees, ArmsComplete assumptions context q [] .emptyRow result (zeroUses context) trees := by
  refine ⟨[], ?_⟩
  intro annotations path index head _ _ _
  exact ⟨rfl, rfl, rfl⟩

public theorem arms_cons_complete {assumptions : Assumptions} {context : Context}
    {q : Quantity} {name : String} {body : Term} {rest : List (String × Term)} {payload row result : Ty} {bu ru : Uses}
    (safe : safeUses (⟨payload, q⟩ :: context) bu = true)
    (share : validContext assumptions.shareableVariables [⟨payload, q⟩] = true)
    (fits : q.fits (bu.headD 0) = true)
    (agreeing : (rest.isEmpty || branchesAgree context bu.tail ru) = true)
    (ihB : ∃ tree, Completes assumptions (⟨payload, q⟩ :: context) body result bu tree)
    (ihR : ∃ trees, ArmsComplete assumptions context q rest row result ru trees) :
    ∃ trees, ArmsComplete assumptions context q ((name, body) :: rest) (.field name payload row) result
      (joinUses bu.tail ru) trees := by
  obtain ⟨bodyTree, completeBody⟩ := ihB
  obtain ⟨restTrees, completeRest⟩ := ihR
  refine ⟨bodyTree :: restTrees, ?_⟩
  intro annotations path index head realizes distinct members
  obtain ⟨fresh, restDistinct⟩ := labelsDistinct_cons distinct
  have found : rowMember head name = some payload := by
    rw [members name (by simp)]
    simp [rowMember]
  obtain ⟨first, checkedFirst, firstUses⟩ :=
    ((completeBody annotations (path ++ [index]) realizes.head).2 result (sameType_refl _ _)).elim
  have safe' : safeUses (⟨payload, q⟩ :: context) first.uses = true := by
    rw [firstUses]; exact safe
  have fits' : q.fits (first.uses.headD 0) = true := by rw [firstUses]; exact fits
  have tailMembers : ∀ label, label ∈ rest.map Prod.fst → rowMember head label = rowMember row label := by
    intro label inside
    rw [members label (by simp [inside])]
    have different : name ≠ label := fun same => fresh (same ▸ inside)
    simp [rowMember, different]
  obtain ⟨later, checkedLater, laterRow, laterUses, laterQ⟩ :=
    (completeRest annotations path (index + 1) head realizes.tail restDistinct tailMembers).elim
  have agreeing' : (rest.isEmpty || branchesAgree context first.uses.tail later.uses) = true := by
    rw [firstUses, laterUses]; exact agreeing
  rw [checkArms]
  simp only [found, need_ok share, checkedFirst, need_ok safe', need_ok fits', checkedLater, need_ok agreeing',
    dif_pos laterQ, bind, Except.bind, pure, Except.pure, Yields]
  refine ⟨?_, ?_, trivial⟩
  · show Ty.field name payload later.row = Ty.field name payload row; rw [laterRow]
  · show joinUses first.uses.tail later.uses = joinUses bu.tail ru; rw [firstUses, laterUses]

public theorem completes_case {assumptions : Assumptions} {context : Context}
    {scrutinee : Term} {arms : List (String × Term)} {row result : Ty} {su au : Uses} {q : Quantity}
    (distinct : labelsDistinct arms = true) (allowed : caseAllowed assumptions q context su = true)
    (ihS : ∃ tree, Completes assumptions context scrutinee (.variant row) su tree)
    (ihA : ∃ trees, ArmsComplete assumptions context q arms row result au trees) :
    ∃ tree, Completes assumptions context (.case scrutinee arms) result (addUses su au) tree := by
  obtain ⟨scrutineeTree, completeScrutinee⟩ := ihS
  obtain ⟨armTrees, completeArms⟩ := ihA
  refine ⟨.node (some ⟨.variant row, result, q, .reusable⟩) [scrutineeTree, .node none armTrees], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atScrutinee : Realizes annotations (path ++ [0]) scrutineeTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atArms : Realizes annotations (path ++ [1]) (.node none armTrees) := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨value, checkedValue, valueUses⟩ :=
    ((completeScrutinee annotations (path ++ [0]) atScrutinee).2 (.variant row) (sameType_refl _ _)).elim
  obtain ⟨answer, checkedArms, answerRow, answerUses, answerQ⟩ :=
    (completeArms annotations (path ++ [1]) 0 row atArms.forest distinct (fun _ _ => rfl)).elim
  rcases answer with ⟨actualRow, armUses, actualQ, armDerivation⟩
  change actualRow = row at answerRow
  subst actualRow
  change actualQ = q at answerQ
  subst actualQ
  change armUses = au at answerUses
  have allowed' : caseAllowed assumptions q context value.uses = true := by rw [valueUses]; exact allowed
  let synthesized : Synth assumptions context (.case scrutinee arms) :=
    ⟨result, addUses value.uses armUses, .case value.derivation armDerivation distinct allowed'⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.case scrutinee arms) .synth = .ok synthesized
    cases arms <;> rw [elaborate] <;>
      simp [root, hint, checkedValue, checkedArms, rawHead, need_ok distinct,
        need_ok (sameType_refl assumptions (.variant row)), need_ok allowed', caseQuantityAt_some root, bind, Except.bind, Functor.map, Except.map,
        pure, Except.pure, synthesized, checkedSynth]
  · intro expected
    change elaborate assumptions annotations context path (.case scrutinee arms) (.check expected) = _
    cases arms <;> rw [elaborate] <;>
      simp [root, hint, checkedValue, checkedArms, rawHead, need_ok distinct,
        need_ok (sameType_refl assumptions (.variant row)), need_ok allowed', caseQuantityAt_some root, bind, Except.bind, Functor.map, Except.map,
        pure, Except.pure, synthesized, checkedSynth]
  · exact sameType_refl _ _
  · change addUses value.uses armUses = addUses su au
    rw [valueUses, answerUses]

public theorem completes_effectCase {assumptions : Assumptions} {context : Context}
    {scrutinee : Term} {arms : List (String × Term)} {plan response row result : Ty} {su au : Uses} {q : Quantity}
    (nonComputation : result.isComputation = false) (distinct : labelsDistinct arms = true)
    (allowed : caseAllowed assumptions q context su = true)
    (ihS : ∃ tree, Completes assumptions context scrutinee (.computation plan response (.variant row)) su tree)
    (ihA : ∃ trees, ArmsComplete assumptions context q arms row (.computation plan response result) au trees) :
    ∃ tree, Completes assumptions context (.case scrutinee arms) (.computation plan response result)
      (addUses su au) tree := by
  obtain ⟨scrutineeTree, completeScrutinee⟩ := ihS
  obtain ⟨armTrees, completeArms⟩ := ihA
  refine ⟨.node (some ⟨.computation plan response (.variant row), .computation plan response result, q, .reusable⟩)
    [scrutineeTree, .node none armTrees], ?_⟩
  intro annotations path realizes
  have root := realizes.root
  have rawHead (type : Ty) : representativeHead assumptions annotations path type = type := by
    simp [representativeHead, root]
  have atScrutinee : Realizes annotations (path ++ [0]) scrutineeTree := by
    simpa [AnnotationTree.child] using realizes.child 0
  have atArms : Realizes annotations (path ++ [1]) (.node none armTrees) := by
    simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨value, checkedValue, valueUses⟩ :=
    ((completeScrutinee annotations (path ++ [0]) atScrutinee).2
      (.computation plan response (.variant row)) (sameType_refl _ _)).elim
  obtain ⟨answer, checkedArms, answerRow, answerUses, answerQ⟩ :=
    (completeArms annotations (path ++ [1]) 0 row atArms.forest distinct (fun _ _ => rfl)).elim
  rcases answer with ⟨actualRow, armUses, actualQ, armDerivation⟩
  change actualRow = row at answerRow
  subst actualRow
  change actualQ = q at answerQ
  subst actualQ
  change armUses = au at answerUses
  have nonActivity : (!result.isComputation) = true := by simp [nonComputation]
  have allowed' : caseAllowed assumptions q context value.uses = true := by rw [valueUses]; exact allowed
  let synthesized : Synth assumptions context (.case scrutinee arms) :=
    ⟨.computation plan response result, addUses value.uses armUses,
      .effectCase value.derivation armDerivation nonComputation distinct allowed'⟩
  apply modes_complete synthesized
  · change elaborate assumptions annotations context path (.case scrutinee arms) .synth = .ok synthesized
    cases arms <;> rw [elaborate] <;>
      simp [root, hint, checkedValue, checkedArms, rawHead, need_ok distinct, need_ok nonActivity, need_ok allowed', caseQuantityAt_some root,
        need_ok (sameType_refl assumptions (.computation plan response (.variant row))),
        need_ok (sameType_refl assumptions (.computation plan response result)), bind, Except.bind,
        Functor.map, Except.map, pure, Except.pure, synthesized, checkedSynth]
  · intro expected
    change elaborate assumptions annotations context path (.case scrutinee arms) (.check expected) = _
    cases arms <;> rw [elaborate] <;>
      simp [root, hint, checkedValue, checkedArms, rawHead, need_ok distinct, need_ok nonActivity, need_ok allowed', caseQuantityAt_some root,
        need_ok (sameType_refl assumptions (.computation plan response (.variant row))),
        need_ok (sameType_refl assumptions (.computation plan response result)), bind, Except.bind,
        Functor.map, Except.map, pure, Except.pure, synthesized, checkedSynth]
  · exact sameType_refl _ _
  · change addUses value.uses armUses = addUses su au
    rw [valueUses, answerUses]

/-- The simultaneous induction covers every declarative constructor. Its
existential result stays in Prop throughout, despite containing a data witness. -/
public theorem complete {assumptions : Assumptions} {context : Context} {term : Term}
    {derived : Ty} {uses : Uses} (typed : PartialTyping assumptions context term derived uses) :
    ∃ tree, Completes assumptions context term derived uses tree := by
  refine PartialTyping.rec
    (motive_1 := fun context term derived uses _ => ∃ tree, Completes assumptions context term derived uses tree)
    (motive_2 := fun context fields row uses _ => ∃ trees, FieldsComplete assumptions context fields row uses trees)
    (motive_3 := fun context q arms row result uses _ => ∃ trees, ArmsComplete assumptions context q arms row result uses trees)
    ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend ?specification
    ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject ?case ?ifBool ?perform ?done
    ?effectCase ?fieldsNil ?fieldsCons ?armsNil ?armsCons typed
  case bound =>
    intro Γ index binding found
    exact completes_bound found
  case natural => exact completes_natural assumptions
  case boolean => exact completes_boolean assumptions
  case label => exact completes_label assumptions
  case lambda =>
    intro Γ body annotation bodyUses _ safe valid captures fits ih
    exact completes_lambda safe valid captures fits ih
  case conversion =>
    intro Γ term actual expected uses _ agreement ih
    obtain ⟨tree, completeTerm⟩ := ih
    exact ⟨tree, completes_conversion completeTerm agreement⟩
  case application =>
    intro Γ function argument functionType argumentType domain codomain fu au reuse quantity
      _ _ shape argumentEq allowed ihF ihA
    subst argumentType
    exact completes_application shape allowed ihF ihA
  case record =>
    intro Γ fields row uses _ ih
    exact completes_record ih
  case get =>
    intro Γ target targetType member uses name fuel _ found free ih
    exact completes_get found free ih
  case extend =>
    intro Γ target fields targetType row tu fu fuel _ _ isRow free ihT ihF
    exact completes_extend isRow free ihT ihF
  case specification =>
    intro Γ metadata extension metadataType extensionType mu eu _ _ pureM pureE free ihM ihE
    exact completes_specification pureM pureE free ihM ihE
  case prototype =>
    intro Γ spec target specType targetType su tu _ _ pureS pureT ihS ihT
    exact completes_prototype pureS pureT ihS ihT
  case reflect =>
    intro Γ target specType targetType uses _ free ih
    exact completes_reflect free ih
  case metadata =>
    intro Γ target metadataType extensionType uses _ free ih
    exact completes_metadata free ih
  case project =>
    intro Γ target specType targetType uses _ free ih
    exact completes_project free ih
  case mix =>
    intro Γ lower upper lowerType upperType self inherited middle provided lu uu _ _
      shapeL shapeU captures shareSelf shareInherited shareMiddle ihL ihU
    exact completes_mix shapeL shapeU captures shareSelf shareInherited shareMiddle ihL ihU
  case fix =>
    intro Γ spec inheritedTerm specType inherited target su iu _ shape _ share allowed captures ihS ihI
    exact completes_fix shape share allowed captures ihS ihI
  case binary =>
    intro Γ primitive left right input output lu ru shape _ _ ihL ihR
    exact completes_binary shape ihL ihR
  case ifZero =>
    intro Γ value zero successor result vu zu su _ _ _ safe agreeing ihV ihZ ihS
    exact completes_ifZero safe agreeing ihV ihZ ihS
  case inject =>
    intro Γ tag payload payloadType row uses fuel _ found nonComputation ih
    exact completes_inject found nonComputation ih
  case case =>
    intro Γ scrutinee arms row result su au q _ _ distinct allowed ihS ihA
    exact completes_case distinct allowed ihS ihA
  case ifBool =>
    intro Γ condition whenTrue whenFalse result cu tu fu _ _ _ agreeing ihC ihT ihF
    exact completes_ifBool ihC ihT ihF agreeing
  case perform =>
    intro Γ plan planType response uses _ isPlan data ih
    exact completes_perform isPlan data ih
  case done =>
    intro Γ value plan response result uses _ nonComputation ih
    exact completes_done nonComputation ih
  case effectCase =>
    intro Γ scrutinee arms plan response row result su au q _ _ nonComputation distinct allowed ihS ihA
    exact completes_effectCase nonComputation distinct allowed ihS ihA
  case fieldsNil => exact fields_nil_complete assumptions
  case fieldsCons =>
    intro Γ name body rest type row bu ru _ _ nonComputation ihB ihR
    exact fields_cons_complete nonComputation ihB ihR
  case armsNil => intro Γ q result; exact arms_nil_complete assumptions Γ q result
  case armsCons =>
    intro Γ q name body rest payload row result bu ru _ safe share fits _ agreeing ihB ihR
    exact arms_cons_complete safe share fits agreeing ihB ihR

/-- Every certified erased term has suitable annotations, without a fragment
restriction, and the checker reconstructs exactly its occurrence-count vector. -/
public theorem annotated_complete {source : AnnotatedTerm} {context : Context} {derived : Ty} {uses : Uses}
    (typed : PartialTyping source.assumptions context source.term derived uses)
    (safe : safeUses context uses = true)
    (valid : validContext source.assumptions.shareableVariables context = true)
    (assumptionsValid : source.assumptions.valid = true) :
    ∃ annotations, ∃ checked,
      checkAgainst { source with annotations := annotations } context derived = .ok checked ∧ checked.uses = uses := by
  obtain ⟨tree, completeTerm⟩ := complete typed
  let annotations := treeAnnotations tree
  obtain ⟨result, accepted, sameUses⟩ :=
    ((completeTerm annotations [] (treeAnnotations_realizes tree)).2 derived (sameType_refl _ _)).elim
  have safe' : safeUses context result.uses = true := by rw [sameUses]; exact safe
  refine ⟨annotations, ⟨derived, result.uses, result.derivation, safe', valid, assumptionsValid⟩, ?_, sameUses⟩
  simp only [checkAgainst, accepted, bind, Except.bind, need_ok safe', need_ok valid,
    need_ok assumptionsValid, pure, Except.pure]

public theorem full_annotated {source : AnnotatedTerm} {context : Context}
    (certificate : Checked source context) :
    ∃ annotations, ∃ checked,
      checkAgainst { source with annotations := annotations } context certificate.type = .ok checked := by
  obtain ⟨annotations, checked, accepted, _⟩ :=
    annotated_complete certificate.derivation certificate.safe certificate.contextValid certificate.assumptionsValid
  exact ⟨annotations, checked, accepted⟩

/-- An explicitly noncomputable name for the existential annotation witness.
The checker remains executable; selecting a derivation-dependent witness uses
classical choice rather than illegal computational elimination from Prop. -/
@[expose] public noncomputable def annotateFromDerivation {source : AnnotatedTerm} {context : Context}
    (certificate : Checked source context) : Annotations :=
  Classical.choose (full_annotated certificate)

public theorem annotateFromDerivation_checks {source : AnnotatedTerm} {context : Context}
    (certificate : Checked source context) : ∃ checked,
    checkAgainst { source with annotations := annotateFromDerivation certificate } context certificate.type = .ok checked :=
  Classical.choose_spec (full_annotated certificate)

/-- The old full-corollary obstruction: a shadowed record containing a lambda
converted to an arrow alias. Positional row annotations repair it even before
the agreement relation is strengthened to structural congruence. -/
@[expose] public def shadowRow : Ty := .field "a" (.variable 0) (.field "a" .natural .emptyRow)

@[expose] public def shadowAnnotations : Annotations
  | [] => some (hint .emptyRow shadowRow)
  | [0] => some (hint .natural .natural)
  | _ => none

@[expose] public def shadowAssumptions : Assumptions :=
  ⟨[(0, .arrow .reusable .unrestricted .natural .natural)], [0], []⟩

@[expose] public def shadowSource : AnnotatedTerm :=
  ⟨.record [("a", .lam (.bound 0)), ("a", .nat 0)], shadowAnnotations, shadowAssumptions⟩

public theorem arrow_alias_agrees :
    sameType shadowAssumptions (.arrow .reusable .unrestricted .natural .natural) (.variable 0) = true := by
  apply sameType_extends
  decide

/-- Positional annotations retain the hidden field's source type and select a
valid binder for the visible lambda before converting to its arrow alias. -/
public theorem shadow_record_now_checks : (checkAgainst shadowSource [] shadowRow).toBool = true := by
  have aliases := arrow_alias_agrees
  dsimp only [shadowAssumptions] at aliases
  simp [checkAgainst, checkAt, shadowSource, shadowRow, shadowAnnotations, shadowAssumptions,
    elaborate, introduce, checkFields, hint, finish, need, aliases, sameType_refl,
    checkedSynth, variableUses, zeroUses, addUses, safeUses, safeQuantity, Quantity.fits, linearFree, validContext,
    reusableAllowed, reusableCaptures, Assumptions.valid, Ty.isComputation, Ty.shareableUnder,
    Ty.shareable, List.getElem?_cons_zero, bind, Except.bind, pure, Except.pure,
    Functor.map, Except.map, Except.toBool]


/-- Canonical syntax laws retained independently of recursive agreement. -/
theorem insertCanonical_callable (row : Ty) (name : String) (member : Ty) :
    callable (row.insertCanonical name member) = row.insertCanonical name member := by
  cases row <;> simp only [Ty.insertCanonical]
  all_goals repeat' first | split
  all_goals rfl

theorem callable_canonical : ∀ type : Ty, callable type.canonical = (callable type).canonical
  | .specification _ extension => by simp [Ty.canonical, callable, callable_canonical extension]
  | .field name member tail => by simp [Ty.canonical, callable, insertCanonical_callable]
  | .arrow .. | .natural | .label | .boolean | .variable _ | .emptyRow | .prototype .. | .custody _ | .variant _
  | .computation .. => rfl


theorem rowMember_eq_finiteLookup : ∀ (row : Ty) (name : String),
    rowMember row name = Obend.Core.Proofs.Preservation.finiteLookup row name
  | .field prior member tail, name => by
    simp [rowMember, Obend.Core.Proofs.Preservation.finiteLookup, rowMember_eq_finiteLookup tail name]
  | .natural, _ | .label, _ | .boolean, _ | .variable _, _ | .arrow .., _ | .emptyRow, _ | .specification .., _
  | .prototype .., _ | .custody _, _ | .variant _, _ | .computation .., _ => rfl

theorem rowMember_canonical (row : Ty) (name : String) :
    rowMember row.canonical name = (rowMember row name).map Ty.canonical := by
  rw [rowMember_eq_finiteLookup, rowMember_eq_finiteLookup, Obend.Core.Proofs.Preservation.canonical_lookup]

theorem isData_insertCanonical (name : String) (member : Ty) (data : member.isData = true) :
    ∀ (row : Ty), row.isData = true → (row.insertCanonical name member).isData = true
  | .field prior old tail, h => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    simp only [Ty.insertCanonical]
    by_cases he : name = prior
    · by_cases hs : old.shareable = true <;> simp [he, hs, Ty.isData, data, h.1, h.2]
    · by_cases hl : name < prior
      · simp [he, hl, Ty.isData, data, h.1, h.2]
      · simp [he, hl, Ty.isData, h.1, isData_insertCanonical name member data tail h.2]
  | .emptyRow, _ => by simp [Ty.insertCanonical, Ty.isData, data]
  | .natural, h | .label, h | .boolean, h => by simp [Ty.insertCanonical, Ty.isData, data]
  | .variable _, h | .arrow .., h | .specification .., h | .prototype .., h | .custody _, h
  | .computation .., h => by simp [Ty.isData] at h
  | .variant r, h => by simp only [Ty.isData] at h; simp [Ty.insertCanonical, Ty.isData, data, h]

/-- Canonical form forgets only shadowed members, so it keeps first-order data first-order. -/
theorem isData_canonical : ∀ {type : Ty}, type.isData = true → type.canonical.isData = true
  | .field name member tail, h => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    exact isData_insertCanonical name _ (isData_canonical h.1) _ (isData_canonical h.2)
  | .variant r, h => by simp only [Ty.isData] at h; simp [Ty.canonical, Ty.isData, isData_canonical h]
  | .natural, _ | .label, _ | .boolean, _ | .emptyRow, _ => rfl
  | .variable _, h | .arrow .., h | .specification .., h | .prototype .., h | .custody _, h
  | .computation .., h => by simp [Ty.isData] at h

theorem isPlan_canonical {type : Ty} (h : type.isPlan = true) : type.canonical.isPlan = true := by
  cases type <;> simp [Ty.isPlan] at h
  simp [Ty.canonical, Ty.isPlan, isData_canonical h]


mutual
/-- The usage vector every derivation of a term computes: occurrence counts per slot of a
context of the given length. -/
@[expose] public def occurrences (n : Nat) : Term → Uses
  | .bound index => (List.range n).map fun position => if position = index then 1 else 0
  | .nat _ | .boolean _ | .label _ | .hole _ _ => List.replicate n 0
  | .lam body => (occurrences (n + 1) body).tail
  | .app a b | .binary _ a b | .specification a b | .prototype a b | .mix a b | .fix a b =>
    addUses (occurrences n a) (occurrences n b)
  | .get t _ | .reflect t | .metadata t | .project t | .inject _ t | .perform t | .done t => occurrences n t
  | .record fields => fieldOccurrences n fields
  | .extend target fields => addUses (occurrences n target) (fieldOccurrences n fields)
  | .ifZero v z s => addUses (occurrences n v) (joinUses (occurrences n z) (occurrences (n + 1) s).tail)
  | .case scrutinee arms => addUses (occurrences n scrutinee) (armOccurrences n arms)
  | .ifBool c t f => addUses (occurrences n c) (joinUses (occurrences n t) (occurrences n f))
@[expose] public def fieldOccurrences (n : Nat) : List (String × Term) → Uses
  | [] => List.replicate n 0
  | (_, body) :: rest => addUses (occurrences n body) (fieldOccurrences n rest)
@[expose] public def armOccurrences (n : Nat) : List (String × Term) → Uses
  | [] => List.replicate n 0
  | (_, body) :: rest => joinUses (occurrences (n + 1) body).tail (armOccurrences n rest)
end

/-- Every derivation of a term computes the same usage vector. -/
public theorem uses_determined {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty}
    {uses : Uses} (typed : PartialTyping assumptions context term type uses) :
    uses = occurrences context.length term := by
  refine PartialTyping.rec
    (motive_1 := fun context term _ uses _ => uses = occurrences context.length term)
    (motive_2 := fun context fields _ uses _ => uses = fieldOccurrences context.length fields)
    (motive_3 := fun context _ arms _ _ uses _ => uses = armOccurrences context.length arms)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  all_goals intros
  all_goals simp_all [occurrences, fieldOccurrences, armOccurrences, variableUses, zeroUses]

/-- Two certificates for the same term and context with the same type are the same
certificate: the type is the only free choice. -/
public theorem Checked.eq_of_type {source : AnnotatedTerm} {context : Context} (c d : Checked source context)
    (same : c.type = d.type) : c = d := by
  have hc := uses_determined c.derivation
  have hd := uses_determined d.derivation
  cases c; cases d
  simp only at same hc hd
  subst same
  have uses := hc.trans hd.symm
  subst uses; rfl



/-- A direct identity application. Its bare source still lacks the annotation
needed to synthesize the lambda in function position. -/
@[expose] public def appliedLambda : AnnotatedTerm :=
  ⟨.app (.lam (.bound 0)) (.nat 1), fun _ => none, {}⟩

@[expose] public def appliedLambdaChecked : Checked appliedLambda [] :=
  ⟨.natural, [], .application (functionType := .arrow .reusable .unrestricted .natural .natural)
    (.lambda (annotation := ⟨.natural, .natural, .unrestricted, .reusable⟩)
      (.bound (binding := ⟨.natural, .unrestricted⟩) rfl)
      (by decide) (by decide) (by decide) (by decide))
    (.natural _ _) rfl rfl (by decide), rfl, rfl, rfl⟩

/-- The application chooses its function representative at the root; the lambda
chooses its binder and result at child 0. Other positions require no annotation. -/
@[expose] public def appliedLambdaAnnotations : Annotations
  | [] => some ⟨.arrow .reusable .unrestricted .natural .natural, .natural,
      .unrestricted, .reusable⟩
  | [0] => some ⟨.natural, .natural, .unrestricted, .reusable⟩
  | _ => none

/-- The concrete application regression, updated to the representative protocol. -/
public theorem appliedLambda_annotated_checks :
    (checkAgainst { appliedLambda with annotations := appliedLambdaAnnotations }
      [] .natural).toOption.isSome = true := by
  simp [checkAgainst, checkAt, appliedLambda, appliedLambdaAnnotations,
    elaborate, finish, need, sameType_refl, checkedSynth, representativeHead,
    argumentAllowed, callable, variableUses, zeroUses, addUses, safeUses,
    safeQuantity, Quantity.fits, linearFree, validContext, reusableAllowed, reusableCaptures,
    Assumptions.valid, Ty.isComputation, Ty.shareableUnder, Ty.shareable,
    List.getElem?_cons_zero, bind, Except.bind, pure, Except.pure,
    Functor.map, Except.map, Except.toOption]

/-- Every syntax node is eligible for preparation, but the bare annotation map
still produces the same precise missing-lambda refusal. -/
public theorem appliedLambda_boundary :
    checkCovered appliedLambda.term = true ∧
    (match checkAgainst appliedLambda [] appliedLambdaChecked.type with
      | .error refusal => some refusal
      | .ok _ => none) = some (.missingLambdaAnnotation [0]) := by
  simp [checkCovered, appliedLambda, appliedLambdaChecked, checkAgainst,
    checkAt, elaborate, bind, Except.bind, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]

/-- Historical name retained: the actual obstruction is fixed-source acceptance,
not a missing syntactic fragment premise. Reannotation is necessary. -/
public theorem coverage_premise_needed :
    ¬ ∀ (source : AnnotatedTerm) (context : Context) (certificate : Checked source context),
      ∃ checked, checkAgainst source context certificate.type = .ok checked := by
  intro all
  obtain ⟨checked, accepted⟩ := all appliedLambda [] appliedLambdaChecked
  have refused := appliedLambda_boundary.2
  rw [accepted] at refused
  cases refused

end Obend.Core.Proofs.BidirectionalCompleteness
