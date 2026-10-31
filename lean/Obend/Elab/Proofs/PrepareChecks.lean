module
/- `prepare_checks`: on the syntactic fragment `Checkable`, with assumptions that declare no
aliases, every typed erased term is prepared and the checker accepts the preparation. -/
public import Obend.Elab.Prepare
public import Obend.Elab.Proofs.Refines

namespace Obend.Elab.Proofs.PrepareChecks
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional
open Obend.Core.Term (Term Primitive)
open Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Elab.Prepare Obend.Elab.Proofs.AliasFree Obend.Elab.Proofs.Refines
set_option autoImplicit false

/-! ## The fragment -/

mutual
/-- Terms whose type preparation predicts from the context alone. -/
public inductive Synthable : Term → Prop where
  | bound (index : Nat) : Synthable (.bound index)
  | nat (value : Nat) : Synthable (.nat value)
  | boolean (value : Bool) : Synthable (.boolean value)
  | label (value : String) : Synthable (.label value)
  /-- An application of a synthesizable function. -/
  | app {function argument : Term} : Synthable function → Checkable argument →
      Synthable (.app function argument)
  /-- A let: a lambda applied to a synthesizable argument, with a synthesizable body. -/
  | letIn {body argument : Term} : Synthable body → Synthable argument →
      Synthable (.app (.lam body) argument)
  | get {target : Term} (name : String) : Synthable target → Synthable (.get target name)
  | binary (primitive : Primitive) {left right : Term} : Checkable left → Checkable right →
      Synthable (.binary primitive left right)
/-- Terms preparation checks against an expected type. -/
public inductive Checkable : Term → Prop where
  | synth {term : Term} : Synthable term → Checkable term
  | lam {body : Term} : Checkable body → Checkable (.lam body)
  | letIn {body argument : Term} : Checkable body → Synthable argument →
      Checkable (.app (.lam body) argument)
  | ifBool {condition whenTrue whenFalse : Term} : Checkable condition → Checkable whenTrue →
      Checkable whenFalse → Checkable (.ifBool condition whenTrue whenFalse)
  | record {fields : List (String × Term)} : labelsDistinct fields = true → FieldsCheckable fields →
      Checkable (.record fields)
  | inject (tag : String) {payload : Term} : Checkable payload → Checkable (.inject tag payload)
  | case {scrutinee : Term} {arms : List (String × Term)} : Synthable scrutinee → FieldsCheckable arms →
      Checkable (.case scrutinee arms)
public inductive FieldsCheckable : List (String × Term) → Prop where
  | nil : FieldsCheckable []
  | cons {name : String} {body : Term} {rest : List (String × Term)} : Checkable body →
      FieldsCheckable rest → FieldsCheckable ((name, body) :: rest)
end

/-! ## What preparation guarantees -/

variable {a : Assumptions}

/-- Synthesis: the tree makes the checker synthesize exactly the predicted type, which agrees
with the derived one, and check at every type agreeing with it. -/
@[expose] public def SynthOK (a : Assumptions) (Γ : Context) (t : Term) (derived : Ty) (uses : Uses) : Prop :=
  ∀ path, ∃ tree predicted, prepare a noHints Γ path t .synth = .ok (tree, predicted) ∧
    sameType a predicted derived = true ∧
    ∀ annotations, Realizes annotations path tree →
      Yields (synthAt a annotations Γ path t) (fun r => r.type = predicted ∧ r.uses = uses) ∧
      ∀ expected, sameType a predicted expected = true →
        Yields (checkAt a annotations Γ path t expected) (fun r => r.uses = uses)

/-- Checking at a given expected type. -/
@[expose] public def CheckOK (a : Assumptions) (Γ : Context) (t : Term) (expected : Ty) (uses : Uses) : Prop :=
  ∀ path, ∃ tree result, prepare a noHints Γ path t (.check expected) = .ok (tree, result) ∧
    ∀ annotations, Realizes annotations path tree →
      Yields (checkAt a annotations Γ path t expected) (fun r => r.uses = uses)

/-- Both modes, over every refinement of the context. -/
@[expose] public def Modes (a : Assumptions) (Γ : Context) (t : Term) (derived : Ty) (uses : Uses) : Prop :=
  (Synthable t → ∀ Γ', Refines a Γ' Γ → SynthOK a Γ' t derived uses) ∧
  (Checkable t → ∀ Γ', Refines a Γ' Γ → ∀ expected, sameType a derived expected = true →
    CheckOK a Γ' t expected uses)

/-- What a lambda's derivation (through conversions) provides its let-redex. -/
@[expose] public def LamInv (a : Assumptions) (Γ : Context) (body : Term) (derived : Ty) (uses : Uses) : Prop :=
  ∃ reuse quantity domain codomain bodyUses,
    sameType a (.arrow reuse quantity domain codomain) derived = true ∧ uses = bodyUses.tail ∧
    safeUses (⟨domain, quantity⟩ :: Γ) bodyUses = true ∧
    validContext a.shareableVariables (⟨domain, quantity⟩ :: Γ) = true ∧
    Modes a (⟨domain, quantity⟩ :: Γ) body codomain bodyUses

@[expose] public def Motive (a : Assumptions) (Γ : Context) (t : Term) (derived : Ty) (uses : Uses) : Prop :=
  Modes a Γ t derived uses ∧ ∀ body, t = .lam body → LamInv a Γ body derived uses

theorem yields_elim {α : Type} {result : Except CheckRefusal α} {P : α → Prop}
    (yielded : Yields result P) : ∃ value, result = .ok value ∧ P value := by
  cases result with
  | ok value => exact ⟨value, rfl, yielded⟩
  | error _ => exact False.elim yielded

/-! ## Conversion -/

theorem synthOK_conversion {Γ : Context} {t : Term} {actual expected : Ty} {uses : Uses}
    (ok : SynthOK a Γ t actual uses) (agrees : sameType a actual expected = true) : SynthOK a Γ t expected uses := by
  intro path
  obtain ⟨tree, predicted, prepared, same, run⟩ := ok path
  exact ⟨tree, predicted, prepared, sameType_trans same agrees, run⟩

theorem motive_conversion {Γ : Context} {t : Term} {actual expected : Ty} {uses : Uses}
    (m : Motive a Γ t actual uses) (agrees : sameType a actual expected = true) : Motive a Γ t expected uses := by
  obtain ⟨⟨synth, check⟩, lam⟩ := m
  refine ⟨⟨fun s Γ' r => synthOK_conversion (synth s Γ' r) agrees,
    fun c Γ' r target agreement => check c Γ' r target (sameType_trans agrees agreement)⟩, ?_⟩
  intro body eq
  obtain ⟨reuse, quantity, domain, codomain, bodyUses, same, rest⟩ := lam body eq
  exact ⟨reuse, quantity, domain, codomain, bodyUses, sameType_trans same agrees, rest⟩

/-! ## Leaves -/

/-- An elimination form that both prepares and checks as `finish` of one synthesized type. -/
theorem synthOK_finish {Γ : Context} {t : Term} {derived : Ty} {uses : Uses}
    (predicted : Ty) (agrees : sameType a predicted derived = true)
    (tree : List Nat → AnnotationTree)
    (prepared : ∀ path, prepare a noHints Γ path t .synth = .ok (tree path, predicted))
    (synthesized : ∀ annotations path, Realizes annotations path (tree path) →
      ∃ s : Synth a Γ t, s.type = predicted ∧ s.uses = uses ∧ (annotations path).isNone ∧
        ∀ mode, elaborate a annotations Γ path t mode = finish a annotations path s mode) :
    SynthOK a Γ t derived uses := by
  intro path
  refine ⟨tree path, predicted, prepared path, agrees, ?_⟩
  intro annotations realizes
  obtain ⟨s, sType, sUses, none_, unfolds⟩ := synthesized annotations path realizes
  constructor
  · change Yields (elaborate a annotations Γ path t .synth) _
    rw [unfolds]
    simp only [finish, ascribe]
    rw [Option.isNone_iff_eq_none.mp none_]
    exact ⟨sType, sUses⟩
  · intro expected agreement
    change Yields (elaborate a annotations Γ path t (.check expected)) _
    rw [unfolds, finish, dif_pos (by rw [sType]; exact agreement)]
    exact sUses

/-- A synthesizable form whose check-mode preparation builds the synthesis tree checks too. -/
theorem checkOK_of_synthOK {Γ : Context} {t : Term} {derived expected : Ty} {uses : Uses}
    (ok : SynthOK a Γ t derived uses) (agreement : sameType a derived expected = true)
    (sameTree : ∀ path tree predicted, prepare a noHints Γ path t .synth = .ok (tree, predicted) →
      prepare a noHints Γ path t (.check expected) = .ok (tree, expected)) :
    CheckOK a Γ t expected uses := by
  intro path
  obtain ⟨tree, predicted, prepared, same, run⟩ := ok path
  refine ⟨tree, expected, sameTree path tree predicted prepared, ?_⟩
  intro annotations realizes
  exact (run annotations realizes).2 expected (sameType_trans same agreement)

theorem variableUses_length {Γ Γ' : Context} (h : Γ'.length = Γ.length) (index : Nat) :
    variableUses Γ' index = variableUses Γ index := by simp [variableUses, h]

theorem zeroUses_length {Γ Γ' : Context} (h : Γ'.length = Γ.length) : zeroUses Γ' = zeroUses Γ := by
  simp [zeroUses, h]

theorem realizes_root {annotations : Annotations} {path : List Nat}
    {here : Option LambdaAnnotation} {children : List AnnotationTree}
    (realizes : Realizes annotations path (.node here children)) : annotations path = here := by
  simpa only [List.append_nil, AnnotationTree.lookup] using realizes []

theorem realizes_child {annotations : Annotations} {path : List Nat}
    {here : Option LambdaAnnotation} {children : List AnnotationTree}
    (realizes : Realizes annotations path (.node here children)) (index : Nat) (tree : AnnotationTree)
    (at_ : children[index]? = some tree) : Realizes annotations (path ++ [index]) tree := by
  intro suffix
  simpa only [List.append_assoc, List.cons_append, List.nil_append, AnnotationTree.lookup,
    AnnotationTree.child, at_, Option.getD_some] using realizes (index :: suffix)

theorem leaf_none {annotations : Annotations} {path : List Nat} (realizes : Realizes annotations path leaf) :
    (annotations path).isNone = true := by
  simp [realizes_root realizes]

theorem motive_bound {Γ : Context} {index : Nat} {binding : Binding} (found : Γ[index]? = some binding) :
    Motive a Γ (.bound index) binding.type (variableUses Γ index) := by
  have synth : ∀ Γ', Refines a Γ' Γ → SynthOK a Γ' (.bound index) binding.type (variableUses Γ index) := by
    intro Γ' r
    obtain ⟨binding', found', agrees, _⟩ := refines_getElem r found
    refine synthOK_finish binding'.type agrees (fun _ => leaf) (fun path => by simp [prepare, found', pure, Except.pure]) ?_
    intro annotations path realizes
    refine ⟨⟨binding'.type, variableUses Γ' index, .bound found'⟩, rfl,
      variableUses_length (refines_length r) index, leaf_none realizes, ?_⟩
    intro mode
    rw [elaborate]
    split
    · rename_i b h; rw [found'] at h; cases h; rfl
    · rename_i h; rw [found'] at h; contradiction
  refine ⟨⟨fun _ => synth, fun c Γ' r expected agreement => ?_⟩, fun _ h => by cases h⟩
  refine checkOK_of_synthOK (synth Γ' r) agreement ?_
  intro path tree predicted prepared
  obtain ⟨binding', found', _⟩ := refines_getElem r found
  simp [prepare, found', pure, Except.pure] at prepared ⊢
  exact prepared.1

theorem motive_literal {Γ : Context} {t : Term} {type : Ty}
    (derivation : ∀ Γ : Context, PartialTyping a Γ t type (zeroUses Γ))
    (synthesizable : Synthable t) (notLam : ∀ body, t ≠ .lam body)
    (prepared : ∀ Γ path mode, prepare a noHints Γ path t mode =
      .ok (leaf, match mode with | .synth => type | .check expected => expected))
    (unfolds : ∀ annotations Γ path mode, elaborate a annotations Γ path t mode =
      finish a annotations path ⟨type, zeroUses Γ, derivation Γ⟩ mode) :
    Motive a Γ t type (zeroUses Γ) := by
  have synth : ∀ Γ', Refines a Γ' Γ → SynthOK a Γ' t type (zeroUses Γ) := by
    intro Γ' r
    refine synthOK_finish type (sameType_refl _ _) (fun _ => leaf) (fun path => prepared Γ' path .synth) ?_
    intro annotations path realizes
    exact ⟨⟨type, zeroUses Γ', derivation Γ'⟩, rfl, zeroUses_length (refines_length r), leaf_none realizes,
      unfolds annotations Γ' path⟩
  refine ⟨⟨fun _ => synth, fun _ Γ' r expected agreement => ?_⟩, fun body h => absurd h (notLam body)⟩
  refine checkOK_of_synthOK (synth Γ' r) agreement ?_
  intro path tree predicted p
  rw [prepared] at p ⊢
  cases p; rfl

theorem motive_natural (Γ : Context) (value : Nat) : Motive a Γ (.nat value) .natural (zeroUses Γ) :=
  motive_literal (fun Γ => .natural Γ value) (.nat value) (fun _ h => by cases h)
    (fun _ _ mode => by cases mode <;> rfl) (fun _ _ _ _ => rfl)

theorem motive_boolean (Γ : Context) (value : Bool) : Motive a Γ (.boolean value) .boolean (zeroUses Γ) :=
  motive_literal (fun Γ => .boolean Γ value) (.boolean value) (fun _ h => by cases h)
    (fun _ _ mode => by cases mode <;> rfl) (fun _ _ _ _ => rfl)

theorem motive_label (Γ : Context) (value : String) : Motive a Γ (.label value) (literalType value) (zeroUses Γ) :=
  motive_literal (fun Γ => .label Γ value) (.label value) (fun _ h => by cases h)
    (fun _ _ mode => by cases mode <;> rfl) (fun _ _ _ _ => rfl)

theorem motive_lambda (none_ : a.bounds = []) {Γ : Context} {body : Term} {annotation : LambdaAnnotation}
    {uses : Uses}
    (safe : safeUses (⟨annotation.domain, annotation.parameter⟩ :: Γ) uses = true)
    (valid : validContext a.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: Γ) = true)
    (captures : reusableAllowed a annotation.reuse Γ uses.tail = true)
    (ih : Motive a (⟨annotation.domain, annotation.parameter⟩ :: Γ) body annotation.codomain uses) :
    Motive a Γ (.lam body) (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain)
      uses.tail := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body' h => ?_⟩
  · have bodyCheckable : Checkable body := by
      cases c with
      | synth s => cases s
      | lam b => exact b
    obtain ⟨d', c', rfl, hd, hc⟩ := arrow_inv none_ (sameType_symm agreement)
    have binder : Refines a (⟨d'.canonical, annotation.parameter⟩ :: Γ')
        (⟨annotation.domain, annotation.parameter⟩ :: Γ) :=
      refines_same_quantity (sameType_trans (sameType_symm (sameType_canonical a d')) hd) r
    have bodyOK := ih.1.2 bodyCheckable _ binder c'.canonical
      (sameType_trans (sameType_symm hc) (sameType_canonical a c'))
    intro path
    obtain ⟨bodyTree, bodyResult, bodyPrepared, bodyRun⟩ := bodyOK (path ++ [0])
    refine ⟨.node none [bodyTree], .arrow annotation.reuse annotation.parameter d' c', ?_, ?_⟩
    · simp [prepare, noHints, whnf_eq none_, Ty.canonical, bodyPrepared, bind, Except.bind, pure, Except.pure]
    · intro annotations realizes
      have root := realizes_root realizes
      have child := realizes_child realizes 0 bodyTree rfl
      obtain ⟨checked, accepted, sameUses⟩ := yields_elim (bodyRun annotations child)
      have safe' : safeUses (⟨d'.canonical, annotation.parameter⟩ :: Γ') checked.uses = true := by
        rw [sameUses]; exact safeUses_refines binder safe
      have valid' : validContext a.shareableVariables (⟨d'.canonical, annotation.parameter⟩ :: Γ') = true :=
        validContext_refines none_ binder valid
      have captures' : reusableAllowed a annotation.reuse Γ' checked.uses.tail = true := by
        rw [sameUses]
        exact reusableAllowed_refines none_ (match binder with | .cons _ tail => tail) captures
      change Yields (elaborate a annotations Γ' path (.lam body) (.check _)) _
      rw [elaborate]
      simp only [root]
      split
      · rename_i reuse' parameter' domain' codomain' shape
        simp only [representativeHead, root, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          whnf_eq none_, Ty.canonical, Ty.arrow.injEq] at shape
        obtain ⟨rfl, rfl, rfl, rfl⟩ := shape
        simp [checkAt] at accepted
        simp [accepted, need_ok safe', need_ok valid', need_ok captures', bind, Except.bind, pure,
          Except.pure, Yields]
        exact congrArg List.tail sameUses
      · rename_i hne
        exfalso
        exact hne annotation.reuse annotation.parameter d'.canonical c'.canonical
          (by simp [representativeHead, root, whnf_eq none_, Ty.canonical])
  · cases h
    exact ⟨annotation.reuse, annotation.parameter, annotation.domain, annotation.codomain, uses,
      sameType_refl _ _, rfl, safe, valid, ih.1⟩

/-! ## Applications -/

/-- An application annotated with its function's representative and written codomain. -/
theorem app_run {annotations : Annotations} {Γ : Context} {path : List Nat} {function argument : Term}
    {functionType domain codomain : Ty} {reuse : Reuse} {quantity : Quantity} {fu au : Uses}
    (root : annotations path = some (hint functionType codomain))
    (shape : callable functionType = .arrow reuse quantity domain codomain)
    (functionChecks : Yields (checkAt a annotations Γ (path ++ [0]) function functionType) (fun r => r.uses = fu))
    (argumentChecks : Yields (checkAt a annotations Γ (path ++ [1]) argument domain) (fun r => r.uses = au))
    (allowed : argumentAllowed a quantity Γ domain au = true) :
    Yields (synthAt a annotations Γ path (.app function argument))
      (fun r => r.type = codomain ∧ r.uses = addUses fu au) ∧
    ∀ expected, sameType a codomain expected = true →
      Yields (checkAt a annotations Γ path (.app function argument) expected) (fun r => r.uses = addUses fu au) := by
  obtain ⟨fn, fnOk, fnUses⟩ := yields_elim functionChecks
  obtain ⟨arg, argOk, argUses⟩ := yields_elim argumentChecks
  have allowed' : argumentAllowed a quantity Γ domain arg.uses = true := by rw [argUses]; exact allowed
  have rawHead : representativeHead a annotations path functionType = functionType := by
    simp [representativeHead, root]
  simp only [checkAt] at fnOk argOk
  constructor
  · change Yields (elaborate a annotations Γ path (.app function argument) .synth) _
    rw [elaborate]
    simp only [root, hint, fnOk, Except.map, bind, Except.bind, checkedSynth]
    split
    · rename_i r q d c observed
      rw [rawHead, shape] at observed
      cases observed
      simp [argOk, need_ok allowed', pure, Except.pure, finish, ascribe, root, hint, sameType_refl, Yields,
        fnUses, argUses]
    · rename_i absent
      exact (absent reuse quantity domain codomain (by rw [rawHead]; exact shape)).elim
  · intro expected agreement
    change Yields (elaborate a annotations Γ path (.app function argument) (.check expected)) _
    rw [elaborate]
    simp only [root, hint, fnOk, Except.map, bind, Except.bind, checkedSynth]
    split
    · rename_i r q d c observed
      rw [rawHead, shape] at observed
      cases observed
      simp [argOk, need_ok allowed', pure, Except.pure, finish, agreement, Yields, fnUses, argUses]
    · rename_i absent
      exact (absent reuse quantity domain codomain (by rw [rawHead]; exact shape)).elim

/-- A lambda carrying its own annotation checks at that annotation's arrow. -/
theorem lam_run {annotations : Annotations} {Γ : Context} {path : List Nat} {body : Term}
    {annotation : LambdaAnnotation} {bodyUses : Uses}
    (root : annotations path = some annotation)
    (bodyChecks : Yields (checkAt a annotations (⟨annotation.domain, annotation.parameter⟩ :: Γ) (path ++ [0])
      body annotation.codomain) (fun r => r.uses = bodyUses))
    (safe : safeUses (⟨annotation.domain, annotation.parameter⟩ :: Γ) bodyUses = true)
    (valid : validContext a.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: Γ) = true)
    (captures : reusableAllowed a annotation.reuse Γ bodyUses.tail = true) :
    Yields (checkAt a annotations Γ path (.lam body)
      (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain))
      (fun r => r.uses = bodyUses.tail) := by
  obtain ⟨checked, ok, sameUses⟩ := yields_elim bodyChecks
  have safe' : safeUses (⟨annotation.domain, annotation.parameter⟩ :: Γ) checked.uses = true := by
    rw [sameUses]; exact safe
  have captures' : reusableAllowed a annotation.reuse Γ checked.uses.tail = true := by
    rw [sameUses]; exact captures
  simp only [checkAt] at ok
  change Yields (elaborate a annotations Γ path (.lam body) (.check _)) _
  rw [elaborate]
  simp [root, ok, need_ok safe', need_ok valid, need_ok captures', bind, Except.bind, pure, Except.pure,
    finish, checkedSynth, sameType_refl, Yields, sameUses]

theorem applyPrepared_arrow {hints : Annotations} {Γ : Context} {path : List Nat} {argument : Term} {mode : Mode}
    {functionTree : AnnotationTree} {functionType domain codomain : Ty} {reuse : Reuse} {quantity : Quantity}
    {prepareArgument : Ty → Except PrepareRefusal AnnotationTree} {argumentTree : AnnotationTree}
    (shape : callable functionType = .arrow reuse quantity domain codomain)
    (argumentPrepared : prepareArgument domain = .ok argumentTree) :
    applyPrepared a hints Γ path argument mode functionTree functionType prepareArgument =
      .ok (.node (some (hint functionType codomain)) [functionTree, argumentTree],
        match mode with | .synth => codomain | .check expected => expected) := by
  cases mode <;> simp [applyPrepared, shape, argumentPrepared, bind, Except.bind, pure, Except.pure]

theorem prepare_app_general {hints : Annotations} {Γ : Context} {path : List Nat} {function argument : Term}
    {mode : Mode} (notLam : ∀ body, function ≠ .lam body) :
    prepare a hints Γ path (.app function argument) mode = (do
      let (functionTree, functionType) ← prepare a hints Γ (path ++ [0]) function .synth
      applyPrepared a hints Γ path argument mode functionTree functionType
        (fun domain => do
          let (tree, _) ← prepare a hints Γ (path ++ [1]) argument (.check domain)
          pure tree)) := by
  cases function with
  | lam body => exact absurd rfl (notLam body)
  | _ => simp only [prepare]

theorem synthable_not_lam {t : Term} (s : Synthable t) (body : Term) : t ≠ .lam body := by
  cases s <;> simp

theorem motive_application (none_ : a.bounds = []) {Γ : Context} {function argument : Term}
    {functionType domain codomain : Ty} {fu au : Uses} {reuse : Reuse} {quantity : Quantity}
    (shape : callable functionType = .arrow reuse quantity domain codomain)
    (allowed : argumentAllowed a quantity Γ domain au = true)
    (ihF : Motive a Γ function functionType fu) (ihA : Motive a Γ argument domain au)
    (argumentUses : au = occurrences Γ.length argument) :
    Motive a Γ (.app function argument) codomain (addUses fu au) := by
  -- the general application, from a synthesizable function
  have general : Synthable function → Checkable argument → ∀ Γ', Refines a Γ' Γ →
      SynthOK a Γ' (.app function argument) codomain (addUses fu au) ∧
      ∀ path tree predicted expected,
        prepare a noHints Γ' path (.app function argument) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.app function argument) (.check expected) = .ok (tree, expected) := by
    intro sf ca Γ' r
    have notLam := synthable_not_lam sf
    have fOK := ihF.1.1 sf Γ' r
    refine ⟨?_, ?_⟩
    · intro path
      obtain ⟨ft, fT, fPrepared, fSame, fRun⟩ := fOK (path ++ [0])
      obtain ⟨d', c', fShape, hd, hc⟩ := callable_transport none_ fSame shape
      obtain ⟨xt, _, xPrepared, xRun⟩ := ihA.1.2 ca Γ' r d' (sameType_symm hd) (path ++ [1])
      refine ⟨.node (some (hint fT c')) [ft, xt], c', ?_, hc, ?_⟩
      · rw [prepare_app_general notLam]
        simp only [fPrepared, bind, Except.bind]
        exact applyPrepared_arrow fShape (by simp [xPrepared, bind, Except.bind, pure, Except.pure])
      · intro annotations realizes
        have fChild := realizes_child realizes 0 ft rfl
        have xChild := realizes_child realizes 1 xt rfl
        exact app_run (realizes_root realizes) fShape ((fRun annotations fChild).2 fT (sameType_refl _ _))
          (xRun annotations xChild) (argumentAllowed_refines none_ r hd allowed)
    · intro path tree predicted expected prepared
      rw [prepare_app_general notLam] at prepared ⊢
      obtain ⟨ft, fT, fPrepared, fSame, _⟩ := fOK (path ++ [0])
      obtain ⟨d', c', fShape, hd, _⟩ := callable_transport none_ fSame shape
      obtain ⟨xt, _, xPrepared, _⟩ := ihA.1.2 ca Γ' r d' (sameType_symm hd) (path ++ [1])
      have hArg : (do
          let (tree, _) ← prepare a noHints Γ' (path ++ [1]) argument (.check d')
          pure tree : Except PrepareRefusal AnnotationTree) = .ok xt := by
        simp [xPrepared, bind, Except.bind, pure, Except.pure]
      simp only [fPrepared, bind, Except.bind] at prepared ⊢
      rw [applyPrepared_arrow fShape hArg] at prepared ⊢
      cases prepared; rfl
  -- the let-redex: the lambda's own derivation, through conversions
  have letIn : ∀ body, function = .lam body → Synthable argument → ∀ Γ', Refines a Γ' Γ →
      (Synthable body → SynthOK a Γ' (.app (.lam body) argument) codomain (addUses fu au)) ∧
      (Checkable body → ∀ expected, sameType a codomain expected = true →
        CheckOK a Γ' (.app (.lam body) argument) expected (addUses fu au)) := by
    intro body isLam sx Γ' r
    obtain ⟨reuse0, q0, d0, c0, bodyUses, same, fuEq, safe, valid, bodyModes⟩ := ihF.2 body isLam
    obtain ⟨d1, c1, rfl, hd1, hc1⟩ := arrow_inv none_ (sameType_symm same)
    simp only [callable, Ty.arrow.injEq] at shape
    obtain ⟨rfl, rfl, rfl, rfl⟩ := shape
    have xOK := ihA.1.1 sx Γ' r
    have lengths := refines_length r
    -- the parameter's q0 refines the derivation's
    have binderOf : ∀ argumentType, sameType a argumentType d1 = true →
        BindingRefines a ⟨argumentType, letQuantity a Γ' argumentType argument⟩ ⟨d0, q0⟩ := by
      intro argumentType agrees
      refine ⟨sameType_trans agrees hd1, ?_⟩
      unfold letQuantity
      split
      · rename_i condition
        exact .inr (.inr ⟨rfl, (Bool.and_eq_true_iff.mp condition).1⟩)
      · rename_i condition
        refine .inr (.inl ⟨rfl, fun unrestricted => condition ?_⟩)
        simp only at unrestricted
        subst unrestricted
        simp only [argumentAllowed, Bool.and_eq_true, bne_self_eq_false, Bool.false_or] at allowed
        rw [Bool.and_eq_true_iff, shareable_congr none_ agrees, lengths, ← argumentUses]
        exact ⟨allowed.2.1, reusableCaptures_refines none_ r allowed.2.2⟩
    have allowedOf : ∀ argumentType, sameType a argumentType d1 = true →
        argumentAllowed a (letQuantity a Γ' argumentType argument) Γ' argumentType au = true := by
      intro argumentType agrees
      have notActivity : (!argumentType.isComputation) = true := by
        simp only [argumentAllowed, Bool.and_eq_true] at allowed
        rw [sameType_isComputation agrees]; exact allowed.1
      unfold letQuantity
      split
      · rename_i condition
        rw [lengths, ← argumentUses] at condition
        simp only [argumentAllowed, notActivity, Bool.true_and, bne_self_eq_false, Bool.false_or]
        exact condition
      · simp [argumentAllowed, notActivity]
    have once : ∀ Γ'' uses, reusableAllowed a .once Γ'' uses = true := by intros; rfl
    refine ⟨fun sb => ?_, fun cb expected agreement => ?_⟩
    · intro path
      obtain ⟨xt, xT, xPrepared, xSame, xRun⟩ := xOK (path ++ [1])
      have binder := binderOf xT xSame
      have binderRefines : Refines a (⟨xT, letQuantity a Γ' xT argument⟩ :: Γ') (⟨d0, q0⟩ :: Γ) :=
        .cons binder r
      obtain ⟨bt, bT, bPrepared, bSame, bRun⟩ := bodyModes.1 sb _ binderRefines (path ++ [0] ++ [0])
      let annotation : LambdaAnnotation := ⟨xT, bT, letQuantity a Γ' xT argument, .once⟩
      refine ⟨.node (some (hint (.arrow .once (letQuantity a Γ' xT argument) xT bT) bT))
          [.node (some annotation) [bt], xt], bT, ?_, sameType_trans bSame (sameType_symm hc1), ?_⟩
      · have bPrepared' : prepare a noHints (⟨xT, letQuantity a Γ' xT argument⟩ :: Γ') (path ++ [0, 0]) body .synth
            = .ok (bt, bT) := by simpa using bPrepared
        simp only [prepare, noHints, xPrepared, bPrepared', bind, Except.bind]
        exact applyPrepared_arrow (by rfl) rfl
      · intro annotations realizes
        have fChild := realizes_child realizes 0 _ rfl
        have xChild := realizes_child realizes 1 xt rfl
        have bChild := realizes_child fChild 0 bt rfl
        have bodyChecks := (bRun annotations bChild).2 bT (sameType_refl _ _)
        have fnChecks := lam_run (annotation := annotation) (realizes_root fChild) bodyChecks
          (safeUses_refines binderRefines safe) (validContext_refines none_ binderRefines valid) (once _ _)
        have run := app_run (realizes_root realizes) rfl fnChecks
          ((xRun annotations xChild).2 xT (sameType_refl _ _)) (allowedOf xT xSame)
        rw [fuEq]
        exact run
    · intro path
      obtain ⟨xt, xT, xPrepared, xSame, xRun⟩ := xOK (path ++ [1])
      have binder := binderOf xT xSame
      have binderRefines : Refines a (⟨xT, letQuantity a Γ' xT argument⟩ :: Γ') (⟨d0, q0⟩ :: Γ) :=
        .cons binder r
      obtain ⟨bt, _, bPrepared, bRun⟩ := bodyModes.2 cb _ binderRefines expected
        (sameType_trans (sameType_symm hc1) agreement) (path ++ [0] ++ [0])
      let annotation : LambdaAnnotation := ⟨xT, expected, letQuantity a Γ' xT argument, .once⟩
      refine ⟨.node (some (hint (.arrow .once (letQuantity a Γ' xT argument) xT expected) expected))
          [.node (some annotation) [bt], xt], expected, ?_, ?_⟩
      · have bPrepared' : ∃ t, prepare a noHints (⟨xT, letQuantity a Γ' xT argument⟩ :: Γ') (path ++ [0, 0]) body
            (.check expected) = .ok (bt, t) := ⟨_, by simpa using bPrepared⟩
        obtain ⟨t, bPrepared'⟩ := bPrepared'
        simp only [prepare, noHints, xPrepared, bPrepared', bind, Except.bind, pure, Except.pure]
        exact applyPrepared_arrow (by rfl) rfl
      · intro annotations realizes
        have fChild := realizes_child realizes 0 _ rfl
        have xChild := realizes_child realizes 1 xt rfl
        have bChild := realizes_child fChild 0 bt rfl
        have bodyChecks := bRun annotations bChild
        have fnChecks := lam_run (annotation := annotation) (realizes_root fChild) bodyChecks
          (safeUses_refines binderRefines safe) (validContext_refines none_ binderRefines valid) (once _ _)
        have run := app_run (realizes_root realizes) rfl fnChecks
          ((xRun annotations xChild).2 xT (sameType_refl _ _)) (allowedOf xT xSame)
        rw [fuEq]
        exact run.2 expected (sameType_refl _ _)
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with
    | app sf ca => exact (general sf ca Γ' r).1
    | letIn sb sx => exact (letIn _ rfl sx Γ' r).1 sb
  · cases c with
    | synth s =>
      cases s with
      | app sf ca =>
        obtain ⟨ok, sameTree⟩ := general sf ca Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)
      | letIn sb sx => exact (letIn _ rfl sx Γ' r).2 (.synth sb) expected agreement
    | letIn cb sx => exact (letIn _ rfl sx Γ' r).2 cb expected agreement

/-! ## Projection and primitives -/

theorem motive_get (none_ : a.bounds = []) {Γ : Context} {target : Term} {targetType member : Ty}
    {uses : Uses} {name : String} {fuel : Nat}
    (found : targetType.lookup a.bounds fuel name = some member) (ih : Motive a Γ target targetType uses) :
    Motive a Γ (.get target name) member uses := by
  have lookup : lookupV a.bounds [] targetType name = some member := (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
  have synth : Synthable target → ∀ Γ', Refines a Γ' Γ → SynthOK a Γ' (.get target name) member uses ∧
      ∀ path tree predicted expected, prepare a noHints Γ' path (.get target name) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.get target name) (.check expected) = .ok (tree, expected) := by
    intro st Γ' r
    refine ⟨fun path => ?_, fun path tree predicted expected prepared => ?_⟩
    · obtain ⟨tt, tT, tPrepared, tSame, tRun⟩ := ih.1.1 st Γ' r (path ++ [0])
      obtain ⟨member', found', same'⟩ := lookupV_transport tSame lookup
      refine ⟨.node none [tt], member', ?_, same', ?_⟩
      · simp [prepare, tPrepared, found', bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        obtain ⟨value, ok, vType, vUses⟩ := yields_elim (tRun annotations (realizes_child realizes 0 tt rfl)).1
        simp only [synthAt] at ok
        constructor
        · change Yields (elaborate a annotations Γ' path (.get target name) .synth) _
          rw [elaborate]
          simp only [root, ok, bind, Except.bind]
          split
          · rename_i m h
            rw [vType, found'] at h; cases h
            simp [finish, ascribe, root, Yields, vUses]
          · rename_i h; rw [vType, found'] at h; contradiction
        · intro expected agreement
          change Yields (elaborate a annotations Γ' path (.get target name) (.check expected)) _
          rw [elaborate]
          simp only [root, ok, bind, Except.bind]
          split
          · rename_i m h
            rw [vType, found'] at h; cases h
            simp [finish, agreement, Yields, vUses]
          · rename_i h; rw [vType, found'] at h; contradiction
    · obtain ⟨tt, tT, tPrepared, tSame, _⟩ := ih.1.1 st Γ' r (path ++ [0])
      obtain ⟨member', found', _⟩ := lookupV_transport tSame lookup
      simp [prepare, tPrepared, found', bind, Except.bind, pure, Except.pure] at prepared ⊢
      exact prepared.1
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | get _ st => exact (synth st Γ' r).1
  · cases c with
    | synth s =>
      cases s with
      | get _ st =>
        obtain ⟨ok, sameTree⟩ := synth st Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)

theorem motive_binary {Γ : Context} {primitive : Primitive} {left right : Term} {input output : Ty} {lu ru : Uses}
    (types : primitiveTypes primitive = (input, output))
    (ihL : Motive a Γ left input lu) (ihR : Motive a Γ right input ru) :
    Motive a Γ (.binary primitive left right) output (addUses lu ru) := by
  have hin : input = (primitiveTypes primitive).1 := by rw [types]
  have hout : output = (primitiveTypes primitive).2 := by rw [types]
  subst hin; subst hout
  have synth : Checkable left → Checkable right → ∀ Γ', Refines a Γ' Γ →
      SynthOK a Γ' (.binary primitive left right) (primitiveTypes primitive).2 (addUses lu ru) ∧
      ∀ path tree predicted expected, prepare a noHints Γ' path (.binary primitive left right) .synth = .ok (tree, predicted) →
        prepare a noHints Γ' path (.binary primitive left right) (.check expected) = .ok (tree, expected) := by
    intro cl cr Γ' r
    refine ⟨fun path => ?_, fun path tree predicted expected prepared => ?_⟩
    · obtain ⟨lt, _, lPrepared, lRun⟩ := ihL.1.2 cl Γ' r (primitiveTypes primitive).1 (sameType_refl _ _) (path ++ [0])
      obtain ⟨rt, _, rPrepared, rRun⟩ := ihR.1.2 cr Γ' r (primitiveTypes primitive).1 (sameType_refl _ _) (path ++ [1])
      refine ⟨.node none [lt, rt], (primitiveTypes primitive).2, ?_, sameType_refl _ _, ?_⟩
      · simp [prepare, lPrepared, rPrepared, bind, Except.bind, pure, Except.pure]
      · intro annotations realizes
        have root := realizes_root realizes
        obtain ⟨lv, lOk, lUses⟩ := yields_elim (lRun annotations (realizes_child realizes 0 lt rfl))
        obtain ⟨rv, rOk, rUses⟩ := yields_elim (rRun annotations (realizes_child realizes 1 rt rfl))
        simp only [checkAt] at lOk rOk
        constructor
        · change Yields (elaborate a annotations Γ' path (.binary primitive left right) .synth) _
          rw [elaborate]
          simp [lOk, rOk, bind, Except.bind, finish, ascribe, root, Yields, lUses, rUses]
        · intro expected agreement
          change Yields (elaborate a annotations Γ' path (.binary primitive left right) (.check expected)) _
          rw [elaborate]
          simp [lOk, rOk, bind, Except.bind, finish, agreement, Yields, lUses, rUses]
    · obtain ⟨lt, _, lPrepared, _⟩ := ihL.1.2 cl Γ' r (primitiveTypes primitive).1 (sameType_refl _ _) (path ++ [0])
      obtain ⟨rt, _, rPrepared, _⟩ := ihR.1.2 cr Γ' r (primitiveTypes primitive).1 (sameType_refl _ _) (path ++ [1])
      simp [prepare, lPrepared, rPrepared, bind, Except.bind, pure, Except.pure] at prepared ⊢
      exact prepared.1
  unfold Motive Modes
  refine ⟨⟨fun s Γ' r => ?_, fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  · cases s with | binary _ cl cr => exact (synth cl cr Γ' r).1
  · cases c with
    | synth s =>
      cases s with
      | binary _ cl cr =>
        obtain ⟨ok, sameTree⟩ := synth cl cr Γ' r
        exact checkOK_of_synthOK ok agreement (fun path tree predicted p => sameTree path tree predicted expected p)

/-! ## Introductions checked against their expected type -/

theorem motive_ifBool {Γ : Context} {condition whenTrue whenFalse : Term} {result : Ty} {cu tu fu : Uses}
    (ihC : Motive a Γ condition .boolean cu) (ihT : Motive a Γ whenTrue result tu)
    (ihF : Motive a Γ whenFalse result fu) :
    Motive a Γ (.ifBool condition whenTrue whenFalse) result (addUses cu (addUses tu fu)) := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  obtain ⟨cc, ct, cf⟩ : Checkable condition ∧ Checkable whenTrue ∧ Checkable whenFalse := by
    cases c with
    | synth s => cases s
    | ifBool cc ct cf => exact ⟨cc, ct, cf⟩
  intro path
  obtain ⟨tc, _, pc, rc⟩ := ihC.1.2 cc Γ' r .boolean (sameType_refl _ _) (path ++ [0])
  obtain ⟨tt, _, pt, rt⟩ := ihT.1.2 ct Γ' r expected agreement (path ++ [1])
  obtain ⟨tf, _, pf, rf⟩ := ihF.1.2 cf Γ' r expected agreement (path ++ [2])
  refine ⟨.node none [tc, tt, tf], expected, ?_, ?_⟩
  · simp [prepare, pc, pt, pf, bind, Except.bind, pure, Except.pure]
  · intro annotations realizes
    have root := realizes_root realizes
    obtain ⟨vc, okc, uc⟩ := yields_elim (rc annotations (realizes_child realizes 0 tc rfl))
    obtain ⟨vt, okt, ut⟩ := yields_elim (rt annotations (realizes_child realizes 1 tt rfl))
    obtain ⟨vf, okf, uf⟩ := yields_elim (rf annotations (realizes_child realizes 2 tf rfl))
    simp only [checkAt] at okc okt okf
    change Yields (elaborate a annotations Γ' path (.ifBool condition whenTrue whenFalse) (.check expected)) _
    rw [elaborate]
    simp [introduce, root, okc, okt, okf, bind, Except.bind, pure, Except.pure, Yields, uc, ut, uf]

theorem motive_inject (none_ : a.bounds = []) {Γ : Context} {tag : String} {payload : Term}
    {payloadType row : Ty} {uses : Uses} {fuel : Nat}
    (found : row.lookup a.bounds fuel tag = some payloadType) (nonComputation : payloadType.isComputation = false)
    (ih : Motive a Γ payload payloadType uses) :
    Motive a Γ (.inject tag payload) (.variant row) uses := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  have cp : Checkable payload := by
    cases c with
    | synth s => cases s
    | inject _ cp => exact cp
  obtain ⟨row', rfl, hrow⟩ := variant_inv none_ (sameType_symm agreement)
  have canonicalRow : sameType a row'.canonical row = true :=
    sameType_trans (sameType_symm (sameType_canonical a row')) hrow
  have lookup : lookupV a.bounds [] row tag = some payloadType := (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
  obtain ⟨payload', found', same'⟩ := lookupV_transport canonicalRow lookup
  have nonActivity : (!payload'.isComputation) = true := by
    rw [sameType_isComputation same', nonComputation]; rfl
  have sum : ∀ annotations path, (annotations path) = none →
      injectionHead a annotations path (.variant row') = .variant row'.canonical := by
    intro annotations path none'
    simp [injectionHead, representativeHead, none', whnf_eq none_, Ty.canonical]
  intro path
  obtain ⟨pt, _, pp, rp⟩ := ih.1.2 cp Γ' r payload' (sameType_symm same') (path ++ [0])
  refine ⟨.node none [pt], .variant row', ?_, ?_⟩
  · simp [prepare, noHints, injectionSum, whnf_eq none_, Ty.canonical, found', pp, bind, Except.bind, pure,
      Except.pure]
  · intro annotations realizes
    have root := realizes_root realizes
    obtain ⟨v, ok, vu⟩ := yields_elim (rp annotations (realizes_child realizes 0 pt rfl))
    simp only [checkAt] at ok
    change Yields (elaborate a annotations Γ' path (.inject tag payload) (.check _)) _
    rw [elaborate]
    simp only [introduce, root]
    split
    · rename_i r' shape
      rw [sum annotations path root] at shape
      cases shape
      split
      · rename_i m h
        rw [found'] at h; cases h
        simp [ok, need_ok nonActivity, bind, Except.bind, pure, Except.pure, Yields, vu]
      · rename_i h; rw [found'] at h; contradiction
    · rename_i hne
      exact (hne _ (sum annotations path root)).elim

/-! ## Records -/

/-- Two rows with the same label spine and agreeing members, position by position. -/
@[expose] public def RowAgrees (a : Assumptions) : Ty → Ty → Prop
  | .emptyRow, .emptyRow => True
  | .field n m t, .field n' m' t' => n = n' ∧ sameType a m m' = true ∧ RowAgrees a t t'
  | _, _ => False

theorem rowAgrees_sameType : ∀ {r r' : Ty}, RowAgrees a r r' → sameType a r r' = true := by
  intro r
  induction r with
  | field n m t _ iht =>
    intro r' h
    cases r' <;> simp only [RowAgrees] at h
    obtain ⟨hn, hm, ht⟩ := h
    subst hn; exact sameType_field hm (iht ht)
  | emptyRow => intro r' h; cases r' <;> simp only [RowAgrees] at h; exact sameType_refl _ _
  | _ => intro r' h; cases r' <;> simp only [RowAgrees] at h

theorem lookupV_head (name : String) (member tail : Ty) :
    lookupV a.bounds [] (.field name member tail) name = some member :=
  (lookupV_iff _ _ _ _).2 ⟨1, by simp [Ty.lookup]⟩

theorem lookupV_field_ne {name other : String} {member tail result : Ty} (ne : name ≠ other) :
    lookupV a.bounds [] (.field name member tail) other = some result ↔
      lookupV a.bounds [] tail other = some result := by
  rw [lookupV_iff, lookupV_iff]
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [Ty.lookup] at h
    | succ fuel => simp [Ty.lookup, ne] at h; exact ⟨fuel, h⟩
  · rintro ⟨fuel, h⟩
    exact ⟨fuel + 1, by simp [Ty.lookup, ne, h]⟩

/-- The row a record derivation builds has the fields' labels, in order. -/
theorem lookupRow_agrees {Γ : Context} :
    ∀ {fields : List (String × Term)} {row : Ty} {uses : Uses}, FieldsTyping a Γ fields row uses →
    labelsDistinct fields = true → ∀ (expected : Ty),
    (∀ name member, name ∈ fields.map Prod.fst → lookupV a.bounds [] row name = some member →
      ∃ member', lookupV a.bounds [] expected name = some member' ∧ sameType a member' member = true) →
    ∃ row', lookupRow a expected fields = some row' ∧ RowAgrees a row' row
  | [], _, _, .nil _, _, _, _ => ⟨.emptyRow, rfl, trivial⟩
  | (name, body) :: rest, _, _, .cons (type := type) (row := tail) _ restTyped _, distinct, expected, transport => by
    simp only [labelsDistinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
      beq_iff_eq] at distinct
    obtain ⟨member', found, same⟩ := transport name type (by simp) (lookupV_head name type tail)
    obtain ⟨row', rest', agrees⟩ := lookupRow_agrees restTyped distinct.2 expected (by
      intro other member mem found'
      have ne : name ≠ other := by
        intro h; subst h
        obtain ⟨arm, inside, eq⟩ := List.mem_map.mp mem
        exact distinct.1 arm inside eq
      exact transport other member (by simp [mem]) ((lookupV_field_ne ne).2 found'))
    exact ⟨.field name member' row', by simp [lookupRow, found, rest', bind, Option.bind], rfl, same, agrees⟩

theorem forest_of_node {annotations : Annotations} {path : List Nat} {here : Option LambdaAnnotation}
    {children : List AnnotationTree} (realizes : Realizes annotations path (.node here children)) :
    ForestRealizes annotations path 0 children := by
  intro offset
  intro suffix
  simpa only [Nat.zero_add, List.append_assoc, List.cons_append, List.nil_append, AnnotationTree.lookup,
    AnnotationTree.child] using realizes (offset :: suffix)

theorem forest_head {annotations : Annotations} {path : List Nat} {index : Nat} {tree : AnnotationTree}
    {trees : List AnnotationTree} (realizes : ForestRealizes annotations path index (tree :: trees)) :
    Realizes annotations (path ++ [index]) tree := by
  simpa using realizes 0

theorem forest_tail {annotations : Annotations} {path : List Nat} {index : Nat} {tree : AnnotationTree}
    {trees : List AnnotationTree} (realizes : ForestRealizes annotations path index (tree :: trees)) :
    ForestRealizes annotations path (index + 1) trees := by
  intro offset
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using realizes (offset + 1)

/-- Fields checked positionally against a row agreeing with the derivation's. -/
@[expose] public def FieldsMotive (a : Assumptions) (Γ : Context) (fields : List (String × Term)) (row : Ty)
    (uses : Uses) : Prop :=
  FieldsCheckable fields → ∀ Γ', Refines a Γ' Γ → ∀ row', RowAgrees a row' row → ∀ path index,
    ∃ trees, prepareFieldsCheck a noHints Γ' path index fields row' = .ok trees ∧
      ∀ annotations, ForestRealizes annotations path index trees →
        Yields (checkFields a annotations Γ' path index fields row') (fun r => r.uses = uses)

theorem fieldsMotive_nil (Γ : Context) : FieldsMotive a Γ [] .emptyRow (zeroUses Γ) := by
  intro _ Γ' r row' agrees path index
  cases row' <;> simp [RowAgrees] at agrees
  refine ⟨[], rfl, fun annotations _ => ?_⟩
  simp [checkFields, pure, Except.pure, Yields, zeroUses_length (refines_length r)]

theorem fieldsMotive_cons {Γ : Context} {name : String} {body : Term} {rest : List (String × Term)}
    {type row : Ty} {bu ru : Uses} (nonComputation : type.isComputation = false)
    (ihB : Motive a Γ body type bu) (ihR : FieldsMotive a Γ rest row ru) :
    FieldsMotive a Γ ((name, body) :: rest) (.field name type row) (addUses bu ru) := by
  intro fc Γ' r row' agrees path index
  have ⟨cb, cr⟩ : Checkable body ∧ FieldsCheckable rest := by
    cases fc with | cons cb cr => exact ⟨cb, cr⟩
  cases row' with
  | field name' member' tail' =>
    obtain ⟨hn, hm, ht⟩ := agrees
    subst hn
    obtain ⟨tree, _, pb, rb⟩ := ihB.1.2 cb Γ' r member' (sameType_symm hm) (path ++ [index])
    obtain ⟨trees, pr, rr⟩ := ihR cr Γ' r tail' ht path (index + 1)
    refine ⟨tree :: trees, by simp [prepareFieldsCheck, pb, pr, bind, Except.bind, pure, Except.pure], ?_⟩
    intro annotations realizes
    obtain ⟨vb, okb, ub⟩ := yields_elim (rb annotations (forest_head realizes))
    obtain ⟨vr, okr, ur⟩ := yields_elim (rr annotations (forest_tail realizes))
    simp only [checkAt] at okb
    have nonActivity : (!member'.isComputation) = true := by
      rw [sameType_isComputation hm, nonComputation]; rfl
    rw [checkFields]
    simp [okb, okr, need_ok nonActivity, bind, Except.bind, pure, Except.pure, Yields, ub, ur]
  | _ => all_goals (simp [RowAgrees] at agrees)

theorem motive_record {Γ : Context} {fields : List (String × Term)} {row : Ty} {uses : Uses}
    (typed : FieldsTyping a Γ fields row uses) (ih : FieldsMotive a Γ fields row uses) :
    Motive a Γ (.record fields) row uses := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  obtain ⟨distinct, fc⟩ : labelsDistinct fields = true ∧ FieldsCheckable fields := by
    cases c with
    | synth s => cases s
    | record d fc => exact ⟨d, fc⟩
  obtain ⟨row', found, agrees⟩ := lookupRow_agrees typed distinct expected
    (fun name member _ found => lookupV_transport (sameType_symm agreement) found)
  intro path
  obtain ⟨trees, pf, rf⟩ := ih fc Γ' r row' agrees path 0
  refine ⟨.node (some (selfHint row')) trees, expected, ?_, ?_⟩
  · simp [prepare, distinct, found, pf, bind, Except.bind, pure, Except.pure]
  · intro annotations realizes
    have root := realizes_root realizes
    obtain ⟨v, ok, vu⟩ := yields_elim (rf annotations (forest_of_node realizes))
    have toExpected : sameType a row' expected = true := sameType_trans (rowAgrees_sameType agrees) agreement
    change Yields (elaborate a annotations Γ' path (.record fields) (.check expected)) _
    rw [elaborate]
    simp [introduce, root, selfHint, hint, ok, bind, Except.bind, pure, Except.pure, finish, checkedSynth,
      toExpected, Yields, vu]

/-! ## Cases -/

theorem lookupV_variable (none_ : a.bounds = []) (index : Nat) (name : String) :
    lookupV a.bounds [] (.variable index) name = none := by
  cases h : lookupV a.bounds [] (.variable index) name with
  | none => rfl
  | some m =>
    obtain ⟨fuel, found⟩ := (lookupV_iff _ _ _ _).1 h
    cases fuel <;> simp [Ty.lookup, none_] at found

/-- Without aliases the checker's arm lookup is the row lookup. -/
theorem rowMember_eq (none_ : a.bounds = []) : ∀ (row : Ty) (name : String),
    rowMember row name = lookupV a.bounds [] row name
  | .field prior member tail, name => by
    by_cases h : prior = name
    · subst h; simp [rowMember, lookupV_head]
    · rw [rowMember, if_neg h, rowMember_eq none_ tail name]
      cases e : lookupV a.bounds [] tail name with
      | none =>
        cases e' : lookupV a.bounds [] (.field prior member tail) name with
        | none => rfl
        | some m => rw [(lookupV_field_ne h).1 e'] at e; cases e
      | some m => exact ((lookupV_field_ne h).2 e).symm
  | .variable index, name => by simp [rowMember, lookupV_variable none_]
  | .natural, name | .label, name | .boolean, name | .emptyRow, name | .custody _, name
  | .arrow .., name | .specification .., name | .prototype .., name | .variant _, name
  | .computation .., name => by
    symm
    cases h : lookupV a.bounds [] _ name with
    | none => rfl
    | some m =>
      obtain ⟨fuel, found⟩ := (lookupV_iff _ _ _ _).1 h
      cases fuel <;> simp [Ty.lookup] at found

/-- Every arm's label is found in the scrutinee's row at an agreeing payload. -/
@[expose] public def MembersAgree (a : Assumptions) (row' : Ty) : Ty → Prop
  | .field name payload tail => (∃ payload', rowMember row' name = some payload' ∧ sameType a payload' payload = true) ∧
      MembersAgree a row' tail
  | _ => True

theorem membersAgree_of {Γ : Context} {row' : Ty} :
    ∀ {arms : List (String × Term)} {row result : Ty} {uses : Uses}, ArmsTyping a Γ arms row result uses →
    labelsDistinct arms = true →
    (∀ name member, name ∈ arms.map Prod.fst → lookupV a.bounds [] row name = some member →
      ∃ member', rowMember row' name = some member' ∧ sameType a member' member = true) →
    MembersAgree a row' row
  | [], _, _, _, .nil _ _, _, _ => trivial
  | (name, body) :: rest, _, _, _, .cons (payload := payload) (row := tail) _ _ _ restTyped, distinct, transport => by
    simp only [labelsDistinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
      beq_iff_eq] at distinct
    refine ⟨transport name payload (by simp) (lookupV_head name payload tail), ?_⟩
    exact membersAgree_of restTyped distinct.2 (by
      intro other member mem found'
      have ne : name ≠ other := by
        intro h; subst h
        obtain ⟨arm, inside, eq⟩ := List.mem_map.mp mem
        exact distinct.1 arm inside eq
      exact transport other member (by simp [mem]) ((lookupV_field_ne ne).2 found'))

@[expose] public def ArmsMotive (a : Assumptions) (Γ : Context) (arms : List (String × Term)) (row result : Ty)
    (uses : Uses) : Prop :=
  FieldsCheckable arms → ∀ Γ', Refines a Γ' Γ → ∀ row', MembersAgree a row' row →
    ∀ result', sameType a result result' = true → ∀ path index,
    ∃ trees, prepareArms a noHints Γ' path index row' result' arms = .ok trees ∧
      ∀ annotations, ForestRealizes annotations path index trees →
        Yields (checkArms a annotations Γ' path index row' result' arms)
          (fun r => r.uses = uses ∧ RowAgrees a r.row row)

theorem armsMotive_nil (Γ : Context) (result : Ty) : ArmsMotive a Γ [] .emptyRow result (zeroUses Γ) := by
  intro _ Γ' r row' _ result' _ path index
  refine ⟨[], rfl, fun annotations _ => ?_⟩
  simp [checkArms, pure, Except.pure, Yields, zeroUses_length (refines_length r), RowAgrees]

theorem armsMotive_cons (none_ : a.bounds = []) {Γ : Context} {name : String} {body : Term}
    {rest : List (String × Term)} {payload row result : Ty} {bu ru : Uses}
    (safe : safeUses (⟨payload, .unrestricted⟩ :: Γ) bu = true)
    (share : payload.shareableUnder a.shareableVariables = true)
    (ihB : Motive a (⟨payload, .unrestricted⟩ :: Γ) body result bu) (ihR : ArmsMotive a Γ rest row result ru) :
    ArmsMotive a Γ ((name, body) :: rest) (.field name payload row) result (addUses bu.tail ru) := by
  intro fc Γ' r row' agrees result' agreement path index
  have ⟨cb, cr⟩ : Checkable body ∧ FieldsCheckable rest := by
    cases fc with | cons cb cr => exact ⟨cb, cr⟩
  obtain ⟨⟨payload', found, same⟩, agreesRest⟩ := agrees
  have binder : Refines a (⟨payload', .unrestricted⟩ :: Γ') (⟨payload, .unrestricted⟩ :: Γ) :=
    refines_same_quantity same r
  obtain ⟨tree, _, pb, rb⟩ := ihB.1.2 cb _ binder result' agreement (path ++ [index])
  obtain ⟨trees, pr, rr⟩ := ihR cr Γ' r row' agreesRest result' agreement path (index + 1)
  refine ⟨tree :: trees, by simp [prepareArms, found, pb, pr, bind, Except.bind, pure, Except.pure], ?_⟩
  intro annotations realizes
  obtain ⟨vb, okb, ub⟩ := yields_elim (rb annotations (forest_head realizes))
  obtain ⟨vr, okr, ur, rowR⟩ := yields_elim (rr annotations (forest_tail realizes))
  simp only [checkAt] at okb
  have share' : payload'.shareableUnder a.shareableVariables = true := by
    rw [shareable_congr none_ same]; exact share
  have safe' : safeUses (⟨payload', .unrestricted⟩ :: Γ') vb.uses = true := by
    rw [ub]; exact safeUses_refines binder safe
  rw [checkArms]
  simp [found, okb, okr, need_ok share', need_ok safe', bind, Except.bind, pure, Except.pure, Yields, ub, ur,
    RowAgrees, same, rowR]

theorem members_of_variant (none_ : a.bounds = []) {Γ : Context} {arms : List (String × Term)}
    {row result row1 : Ty} {uses : Uses} (typed : ArmsTyping a Γ arms row result uses)
    (distinct : labelsDistinct arms = true) (agrees : sameType a row1 row = true) :
    MembersAgree a row1.canonical row :=
  membersAgree_of typed distinct (fun name member _ found => by
    rw [rowMember_eq none_]
    exact lookupV_transport (sameType_trans (sameType_symm (sameType_canonical a row1)) agrees) found)

theorem motive_case (none_ : a.bounds = []) {Γ : Context} {scrutinee : Term} {arms : List (String × Term)}
    {row result : Ty} {su au : Uses} (typed : ArmsTyping a Γ arms row result au)
    (distinct : labelsDistinct arms = true)
    (ihS : Motive a Γ scrutinee (.variant row) su) (ihA : ArmsMotive a Γ arms row result au) :
    Motive a Γ (.case scrutinee arms) result (addUses su au) := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  obtain ⟨ss, fa⟩ : Synthable scrutinee ∧ FieldsCheckable arms := by
    cases c with
    | synth s => cases s
    | case ss fa => exact ⟨ss, fa⟩
  intro path
  obtain ⟨st, sT, sp, sSame, sRun⟩ := ihS.1.1 ss Γ' r (path ++ [0])
  obtain ⟨row1, rfl, hrow⟩ := variant_inv none_ sSame
  have ma := members_of_variant none_ typed distinct hrow
  obtain ⟨trees, pa, ra⟩ := ihA fa Γ' r row1.canonical ma expected agreement (path ++ [1]) 0
  refine ⟨.node none [st, .node none trees], expected, ?_, ?_⟩
  · cases arms with
    | nil =>
      simp [prepareArms, pure, Except.pure] at pa; subst pa
      simp [prepare, sp, whnf_eq none_, Ty.canonical, caseRow, Obend.Elab.Prepare.armResult,
        bind, Except.bind, pure, Except.pure]
    | cons =>
      simp [prepare, sp, whnf_eq none_, Ty.canonical, caseRow, Obend.Elab.Prepare.armResult,
        pa, bind, Except.bind, pure, Except.pure]
  · intro annotations realizes
    have root := realizes_root realizes
    have armsForest := forest_of_node (realizes_child realizes 1 _ rfl)
    obtain ⟨v, ok, vType, vUses⟩ := yields_elim (sRun annotations (realizes_child realizes 0 st rfl)).1
    obtain ⟨ta, okA, uA, rowA⟩ := yields_elim (ra annotations armsForest)
    have hHead : representativeHead a annotations path v.type = .variant row1.canonical := by
      rw [vType]; simp [representativeHead, root, whnf_eq none_, Ty.canonical]
    have agreesScrutinee : sameType a v.type (.variant ta.row) = true := by
      rw [vType]; exact sameType_variant (sameType_trans hrow (sameType_symm (rowAgrees_sameType rowA)))
    simp only [synthAt] at ok
    change Yields (elaborate a annotations Γ' path (.case scrutinee arms) (.check expected)) _
    cases arms with
    | nil =>
      rw [elaborate]
      simp [root, ok, hHead, okA, need_ok agreesScrutinee, bind, Except.bind, pure, Except.pure, Yields, vUses, uA]
    | cons arm rest =>
      obtain ⟨name, body⟩ := arm
      rw [elaborate]
      simp [root, ok, hHead, okA, need_ok agreesScrutinee, need_ok distinct, bind, Except.bind, pure,
        Except.pure, Yields, vUses, uA]

theorem motive_effectCase (none_ : a.bounds = []) {Γ : Context} {scrutinee : Term} {arms : List (String × Term)}
    {planType response row result : Ty} {su au : Uses}
    (typed : ArmsTyping a Γ arms row (.computation planType response result) au)
    (nonComputation : result.isComputation = false) (distinct : labelsDistinct arms = true)
    (ihS : Motive a Γ scrutinee (.computation planType response (.variant row)) su)
    (ihA : ArmsMotive a Γ arms row (.computation planType response result) au) :
    Motive a Γ (.case scrutinee arms) (.computation planType response result) (addUses su au) := by
  unfold Motive Modes
  refine ⟨⟨fun s => (by cases s), fun c Γ' r expected agreement => ?_⟩, fun body h => by cases h⟩
  obtain ⟨ss, fa⟩ : Synthable scrutinee ∧ FieldsCheckable arms := by
    cases c with
    | synth s => cases s
    | case ss fa => exact ⟨ss, fa⟩
  intro path
  obtain ⟨st, sT, sp, sSame, sRun⟩ := ihS.1.1 ss Γ' r (path ++ [0])
  obtain ⟨p1, r1, v1, rfl, hp1, hr1, hv1⟩ := computation_inv none_ sSame
  obtain ⟨row1, rfl, hrow⟩ := variant_inv none_ hv1
  obtain ⟨p2, r2, x2, rfl, hp2, hr2, hx2⟩ := computation_inv none_ (sameType_symm agreement)
  have ma := members_of_variant none_ typed distinct hrow
  have canon (t : Ty) : sameType a t.canonical t = true := sameType_symm (sameType_canonical a t)
  have resultAgrees : sameType a (.computation planType response result)
      (.computation p1.canonical r1.canonical x2.canonical) = true :=
    sameType_computation (sameType_symm (sameType_trans (canon p1) hp1))
      (sameType_symm (sameType_trans (canon r1) hr1)) (sameType_symm (sameType_trans (canon x2) hx2))
  obtain ⟨trees, pa, ra⟩ := ihA fa Γ' r row1.canonical ma _ resultAgrees (path ++ [1]) 0
  refine ⟨.node none [st, .node none trees], .computation p2 r2 x2, ?_, ?_⟩
  · cases arms with
    | nil =>
      simp [prepareArms, pure, Except.pure] at pa; subst pa
      simp [prepare, sp, whnf_eq none_, Ty.canonical, caseRow, Obend.Elab.Prepare.armResult,
        bind, Except.bind, pure, Except.pure]
    | cons =>
      simp [prepare, sp, whnf_eq none_, Ty.canonical, caseRow, Obend.Elab.Prepare.armResult,
        pa, bind, Except.bind, pure, Except.pure]
  · intro annotations realizes
    have root := realizes_root realizes
    have armsForest := forest_of_node (realizes_child realizes 1 _ rfl)
    obtain ⟨v, ok, vType, vUses⟩ := yields_elim (sRun annotations (realizes_child realizes 0 st rfl)).1
    obtain ⟨ta, okA, uA, rowA⟩ := yields_elim (ra annotations armsForest)
    have hHead : representativeHead a annotations path v.type =
        .computation p1.canonical r1.canonical (.variant row1.canonical) := by
      rw [vType]; simp [representativeHead, root, whnf_eq none_, Ty.canonical]
    have hExpected : representativeHead a annotations path (.computation p2 r2 x2) =
        .computation p2.canonical r2.canonical x2.canonical := by
      simp [representativeHead, root, whnf_eq none_, Ty.canonical]
    have agreesScrutinee : sameType a v.type
        (.computation p1.canonical r1.canonical (.variant ta.row)) = true := by
      rw [vType]
      exact sameType_computation (sameType_canonical a p1) (sameType_canonical a r1)
        (sameType_variant (sameType_trans hrow (sameType_symm (rowAgrees_sameType rowA))))
    have nonActivity : (!x2.canonical.isComputation) = true := by
      rw [Ty.canonical_isComputation, sameType_isComputation hx2, nonComputation]; rfl
    have agreesExpected : sameType a (.computation p1.canonical r1.canonical x2.canonical)
        (.computation p2 r2 x2) = true :=
      sameType_computation (sameType_trans (canon p1) (sameType_trans hp1 (sameType_symm hp2)))
        (sameType_trans (canon r1) (sameType_trans hr1 (sameType_symm hr2))) (canon x2)
    simp only [synthAt] at ok
    change Yields (elaborate a annotations Γ' path (.case scrutinee arms) (.check _)) _
    cases arms with
    | nil =>
      rw [elaborate]
      simp [root, ok, hHead, hExpected, okA, need_ok agreesScrutinee, need_ok nonActivity,
        need_ok agreesExpected, bind, Except.bind, pure, Except.pure, Yields, vUses, uA]
    | cons arm rest =>
      obtain ⟨name, body⟩ := arm
      rw [elaborate]
      simp [root, ok, hHead, hExpected, okA, need_ok agreesScrutinee, need_ok distinct, need_ok nonActivity,
        need_ok agreesExpected, bind, Except.bind, pure, Except.pure, Yields, vUses, uA]

/-! ## The induction -/

theorem motive_outside {Γ : Context} {t : Term} {derived : Ty} {uses : Uses}
    (notSynth : Synthable t → False) (notCheck : Checkable t → False) (notLam : ∀ body, t ≠ .lam body) :
    Motive a Γ t derived uses :=
  ⟨⟨fun s => (notSynth s).elim, fun c => (notCheck c).elim⟩, fun body h => (notLam body h).elim⟩

/-- Every derivation of a term carries the fragment's guarantees. -/
public theorem motive_of_typing (none_ : a.bounds = []) {Γ : Context} {t : Term} {derived : Ty} {uses : Uses}
    (typed : PartialTyping a Γ t derived uses) : Motive a Γ t derived uses := by
  refine PartialTyping.rec
    (motive_1 := fun Γ t derived uses _ => Motive a Γ t derived uses)
    (motive_2 := fun Γ fields row uses _ => FieldsMotive a Γ fields row uses)
    (motive_3 := fun Γ arms row result uses _ => ArmsMotive a Γ arms row result uses)
    ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend ?specification
    ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject ?case ?ifBool ?perform ?done
    ?effectCase ?fieldsNil ?fieldsCons ?armsNil ?armsCons typed
  case bound => intro Γ index binding found; exact motive_bound found
  case natural => intro Γ value; exact motive_natural Γ value
  case boolean => intro Γ value; exact motive_boolean Γ value
  case label => intro Γ value; exact motive_label Γ value
  case lambda =>
    intro Γ body annotation bodyUses _ safe valid captures ih
    exact motive_lambda none_ safe valid captures ih
  case conversion =>
    intro Γ term actual expected uses _ agreement ih
    exact motive_conversion ih agreement
  case application =>
    intro Γ function argument functionType argumentType domain codomain fu au reuse quantity
      _ argumentTyped shape argumentEq allowed ihF ihA
    subst argumentType
    exact motive_application none_ shape allowed ihF ihA (uses_determined argumentTyped)
  case record =>
    intro Γ fields row uses fieldsTyped ih
    exact motive_record fieldsTyped ih
  case get =>
    intro Γ target targetType member uses name fuel _ found ih
    exact motive_get none_ found ih
  case binary =>
    intro Γ primitive left right input output lu ru shape _ _ ihL ihR
    exact motive_binary shape ihL ihR
  case inject =>
    intro Γ tag payload payloadType row uses fuel _ found nonComputation ih
    exact motive_inject none_ found nonComputation ih
  case case =>
    intro Γ scrutinee arms row result su au _ armsTyped distinct ihS ihA
    exact motive_case none_ armsTyped distinct ihS ihA
  case ifBool =>
    intro Γ condition whenTrue whenFalse result cu tu fu _ _ _ ihC ihT ihF
    exact motive_ifBool ihC ihT ihF
  case effectCase =>
    intro Γ scrutinee arms plan response row result su au _ armsTyped nonComputation distinct ihS ihA
    exact motive_effectCase none_ armsTyped nonComputation distinct ihS ihA
  case fieldsNil => intro Γ; exact fieldsMotive_nil Γ
  case fieldsCons =>
    intro Γ name body rest type row bu ru _ _ nonComputation ihB ihR
    exact fieldsMotive_cons nonComputation ihB ihR
  case armsNil => intro Γ result; exact armsMotive_nil Γ result
  case armsCons =>
    intro Γ name body rest payload row result bu ru _ safe share _ ihB ihR
    exact armsMotive_cons none_ safe share ihB ihR
  all_goals intros
  all_goals refine motive_outside (fun h => ?_) (fun h => ?_) (fun _ h => ?_)
  all_goals cases h
  all_goals (rename_i s; cases s)

/-! ## The theorem -/

theorem treeAnnotations_realizes' (tree : AnnotationTree) : Realizes (treeAnnotations tree) [] tree :=
  fun _ => rfl

/-- **Preparation is complete on the fragment.** An erased term in `Checkable`, typed under
assumptions that declare no aliases, is prepared, and `checkAgainst` accepts the prepared term
at its type with the derivation's exact usage vector. -/
public theorem prepare_checks {source : AnnotatedTerm} {context : Context}
    (noAliases : source.assumptions.bounds = []) (fragment : Checkable source.term)
    (certificate : Checked source context) :
    ∃ annotations checked,
      prepareAnnotations { source with annotations := noHints } context certificate.type = .ok annotations ∧
      checkAgainst { source with annotations := annotations } context certificate.type = .ok checked ∧
      checked.uses = certificate.uses := by
  have m := motive_of_typing noAliases (show PartialTyping _ _ source.term _ _ from certificate.derivation)
  obtain ⟨tree, _, prepared, run⟩ :=
    m.1.2 fragment context (refines_refl context) certificate.type (sameType_refl _ _) []
  obtain ⟨result, accepted, sameUses⟩ := yields_elim (run (treeAnnotations tree) (treeAnnotations_realizes' tree))
  have safe : safeUses context result.uses = true := by rw [sameUses]; exact certificate.safe
  refine ⟨treeAnnotations tree, ⟨certificate.type, result.uses, result.derivation, safe,
    certificate.contextValid, certificate.assumptionsValid⟩, ?_, ?_, sameUses⟩
  · simp [prepareAnnotations, prepared, bind, Except.bind, pure, Except.pure]
  · simp only [checkAt] at accepted
    simp [checkAgainst, checkAt, accepted, bind, Except.bind, need_ok safe, need_ok certificate.contextValid,
      need_ok certificate.assumptionsValid, pure, Except.pure]

/-- The gate's own form: `prepareChecked` accepts every certified erased term of the fragment. -/
public theorem prepareChecked_complete {source : AnnotatedTerm} {context : Context}
    (noAliases : source.assumptions.bounds = []) (fragment : Checkable source.term)
    (certificate : Checked source context) :
    (prepareChecked { source with annotations := noHints } context certificate.type).toBool = true := by
  obtain ⟨annotations, checked, prepared, accepted, _⟩ := prepare_checks noAliases fragment certificate
  simp [prepareChecked, prepared, accepted, bind, Except.bind, pure, Except.pure, Except.toBool]

/-- `annotateFromDerivation`, executable on the fragment: it reads only the erased term, its
context, assumptions and type, never the derivation. -/
@[expose] public def annotateExecutable (source : AnnotatedTerm) (context : Context) (type : Ty) : Annotations :=
  match prepareAnnotations { source with annotations := noHints } context type with
  | .ok annotations => annotations
  | .error _ => noHints

public theorem annotateExecutable_checks {source : AnnotatedTerm} {context : Context}
    (noAliases : source.assumptions.bounds = []) (fragment : Checkable source.term)
    (certificate : Checked source context) :
    ∃ checked, checkAgainst { source with annotations := annotateExecutable source context certificate.type }
      context certificate.type = .ok checked := by
  obtain ⟨annotations, checked, prepared, accepted, _⟩ := prepare_checks noAliases fragment certificate
  have same : annotateExecutable source context certificate.type = annotations := by
    simp [annotateExecutable, prepared]
  rw [same]
  exact ⟨checked, accepted⟩

/-! ## Inhabitants and teeth -/

/-- Astra's probe: `(λx.x) 1` at `Nat`, refused bare because the lambda is in synthesis
position, is in the fragment. -/
public theorem appliedLambda_checkable : Checkable appliedLambda.term :=
  .letIn (.synth (.bound 0)) (.nat 1)

/-- So preparation discovers its annotations and the checker accepts, by the theorem, not by
running anything. -/
public theorem appliedLambda_prepared :
    (prepareChecked { appliedLambda with annotations := noHints } [] .natural).toBool = true :=
  prepareChecked_complete rfl appliedLambda_checkable appliedLambdaChecked

#assert_axioms motive_of_typing prepare_checks prepareChecked_complete annotateExecutable_checks
  appliedLambda_checkable appliedLambda_prepared

end Obend.Elab.Proofs.PrepareChecks
