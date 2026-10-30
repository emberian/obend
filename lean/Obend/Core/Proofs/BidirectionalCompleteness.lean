module
/- Completeness of the bidirectional checker on a fragment stated syntactically.

`synthCovered` and `checkCovered` are decidable predicates on the bare term: variables,
literals and eliminations synthesize; every introduction form (`lam`, `inject`,
`perform`, `done`, `record` with distinct labels, `specification`, `prototype`) and
every branching form (`ifBool`, `ifZero`, `case`, empty arms included) sits in checking
position. `extend` and holes are outside. Annotations play no part: the checker reads
them only in synthesis of introduction forms, which the fragment excludes, and an
elimination's ascription is taken only when it agrees with what was synthesized.

`complete`: a `PartialTyping` derivation of a covered term makes `checkAt` succeed
against every type agreeing with the derived one, with the same usage vector. -/
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.Preservation.Base
public import Obend.AxiomPin
public import Obend.Tactic.Tooth

namespace Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
set_option autoImplicit false

/-! ## The fragment -/

mutual
/-- Terms whose type the checker synthesizes. -/
@[expose] public def synthCovered : Term → Bool
  | .bound _ | .nat _ | .boolean _ | .label _ => true
  | .app function argument => synthCovered function && checkCovered argument
  | .get target _ => synthCovered target
  | .reflect target | .metadata target | .project target => synthCovered target
  | .binary _ left right => checkCovered left && checkCovered right
  | .mix lower upper => synthCovered lower && synthCovered upper
  | .fix spec inherited => synthCovered spec && checkCovered inherited
  | _ => false

/-- Terms the checker checks against a given type. -/
@[expose] public def checkCovered : Term → Bool
  | .lam body => checkCovered body
  | .inject _ payload => checkCovered payload
  | .perform plan => checkCovered plan
  | .done value => checkCovered value
  | .ifBool condition whenTrue whenFalse => checkCovered condition && checkCovered whenTrue && checkCovered whenFalse
  | .ifZero value zero successor => checkCovered value && checkCovered zero && checkCovered successor
  | .case scrutinee arms => synthCovered scrutinee && bodiesCovered arms
  | .record fields => labelsDistinct fields && bodiesCovered fields
  | .specification metadata extension => checkCovered metadata && checkCovered extension
  | .prototype spec target => checkCovered spec && checkCovered target
  | .bound _ | .nat _ | .boolean _ | .label _ => true
  | .app function argument => synthCovered function && checkCovered argument
  | .get target _ => synthCovered target
  | .reflect target | .metadata target | .project target => synthCovered target
  | .binary _ left right => checkCovered left && checkCovered right
  | .mix lower upper => synthCovered lower && synthCovered upper
  | .fix spec inherited => synthCovered spec && checkCovered inherited
  | .extend _ _ | .hole _ _ => false

/-- Every body of a field or arm list is checked. -/
@[expose] public def bodiesCovered : List (String × Term) → Bool
  | [] => true
  | (_, body) :: rest => checkCovered body && bodiesCovered rest
end

/-! ## Contexts that differ only in the spelling of their types -/

/-- Same quantities, canonically equal types. -/
@[expose] public def Similar : Context → Context → Prop
  | [], [] => True
  | b :: Γ, b' :: Γ' => b.quantity = b'.quantity ∧ b.type.canonical = b'.type.canonical ∧ Similar Γ Γ'
  | _, _ => False

theorem Similar.refl : ∀ (Γ : Context), Similar Γ Γ
  | [] => trivial
  | _ :: Γ => ⟨rfl, rfl, Similar.refl Γ⟩

theorem Similar.length : ∀ {Γ Γ' : Context}, Similar Γ Γ' → Γ.length = Γ'.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, h⟩ => by simp [Similar.length h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Similar.get : ∀ {Γ Γ' : Context} {index : Nat} {binding : Binding}, Similar Γ Γ' →
    Γ[index]? = some binding → ∃ binding', Γ'[index]? = some binding' ∧
      binding.quantity = binding'.quantity ∧ binding.type.canonical = binding'.type.canonical
  | [], _, _, _, _, h => by simp at h
  | b :: Γ, b' :: Γ', 0, _, ⟨hq, ht, _⟩, h => by
    simp at h; subst h; exact ⟨b', rfl, hq, ht⟩
  | _ :: Γ, _ :: Γ', i + 1, _, ⟨_, _, hs⟩, h => by
    simp at h ⊢; exact Similar.get hs h
  | _ :: _, [], _, _, h, _ => h.elim

theorem Similar.zeroUses {Γ Γ' : Context} (h : Similar Γ Γ') : zeroUses Γ' = zeroUses Γ := by
  simp [Obend.Core.Ty.zeroUses, h.length]

theorem Similar.variableUses {Γ Γ' : Context} (h : Similar Γ Γ') (index : Nat) :
    Obend.Core.Ty.variableUses Γ' index = Obend.Core.Ty.variableUses Γ index := by
  simp [Obend.Core.Ty.variableUses, h.length]

/-- Any test of a binder that reads its quantity and its type's shareability agrees on
similar contexts. -/
theorem Similar.zip_all (variables : List Nat) (test : Quantity → Bool → Nat → Bool) :
    ∀ {Γ Γ' : Context}, Similar Γ Γ' → ∀ uses : Uses,
      (Γ'.zip uses).all (fun pair => test pair.1.quantity (pair.1.type.shareableUnder variables) pair.2) =
        (Γ.zip uses).all (fun pair => test pair.1.quantity (pair.1.type.shareableUnder variables) pair.2)
  | [], [], _, _ => rfl
  | b :: Γ, b' :: Γ', ⟨hq, ht, hs⟩, uses => by
    have shareable : b'.type.shareableUnder variables = b.type.shareableUnder variables := by
      rw [← Ty.shareableUnder_canonical variables b'.type, ← ht, Ty.shareableUnder_canonical]
    cases uses with
    | nil => rfl
    | cons n ns =>
      simp only [List.zip_cons_cons, List.all_cons, hq, shareable, Similar.zip_all variables test hs ns]
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem Similar.safeUses {Γ Γ' : Context} (similar : Similar Γ Γ') (uses : Uses) :
    Obend.Core.Ty.safeUses Γ' uses = Obend.Core.Ty.safeUses Γ uses := by
  have := similar.zip_all [] (fun quantity _ count => safeQuantity quantity count) uses
  simp only [Obend.Core.Ty.safeUses, similar.length] at this ⊢
  rw [this]

theorem Similar.validContext (variables : List Nat) : ∀ {Γ Γ' : Context}, Similar Γ Γ' →
    Obend.Core.Ty.validContext variables Γ' = Obend.Core.Ty.validContext variables Γ
  | [], [], _ => rfl
  | b :: Γ, b' :: Γ', ⟨hq, ht, hs⟩ => by
    have shareable : b'.type.shareableUnder variables = b.type.shareableUnder variables := by
      rw [← Ty.shareableUnder_canonical variables b'.type, ← ht, Ty.shareableUnder_canonical]
    simp only [Obend.Core.Ty.validContext, List.all_cons] at Similar.validContext ⊢
    rw [← hq, shareable]
    congr 1
    simpa [Obend.Core.Ty.validContext] using Similar.validContext variables hs
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Similar.reusableCaptures (variables : List Nat) {Γ Γ' : Context} (similar : Similar Γ Γ')
    (uses : Uses) :
    Obend.Core.Ty.reusableCaptures variables Γ' uses = Obend.Core.Ty.reusableCaptures variables Γ uses := by
  have := similar.zip_all variables
    (fun quantity shareable count => count == 0 || (quantity == .unrestricted && shareable)) uses
  simp only [Obend.Core.Ty.reusableCaptures, similar.length] at this ⊢
  rw [this]

/-! ## Canonical forms and weak-head forms -/

theorem sameType_of_canonical {assumptions : Assumptions} {actual expected : Ty}
    (equal : actual.canonical = expected.canonical) : sameType assumptions actual expected = true := by
  simp [sameType, equal]

theorem sameType_canonical (assumptions : Assumptions) (type : Ty) :
    sameType assumptions type type.canonical = true := sameType_of_canonical (by simp)

theorem chase_fixed (assumptions : Assumptions) {type : Ty} (fixed : assumptions.unfoldHead type = type) :
    ∀ k, assumptions.chase k type = type
  | 0 => rfl
  | k + 1 => by simp only [Assumptions.chase, fixed]; exact chase_fixed assumptions fixed k

/-- A type agreeing with a non-variable has that type's canonical form as its weak head. -/
theorem whnf_of_sameType {assumptions : Assumptions} {type other : Ty}
    (agreement : sameType assumptions type other = true) (notVariable : ∀ index, other ≠ .variable index) :
    whnf assumptions type = other.canonical := by
  obtain ⟨i, j, hi, -, h⟩ := (sameType_iff _ _ _).1 agreement
  have otherFixed : assumptions.unfoldHead other.canonical = other.canonical := by
    cases hc : other.canonical with
    | «variable» index => exact absurd (Ty.canonical_variable_eq hc) (notVariable index)
    | _ => rfl
  rw [chase_fixed assumptions otherFixed j] at h
  unfold whnf
  rw [show assumptions.bounds.length = (assumptions.bounds.length - i) + i by omega, Assumptions.chase_add, h,
    chase_fixed assumptions otherFixed]

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

theorem callable_notVariable {type : Ty} {reuse : Reuse} {quantity : Quantity} {domain codomain : Ty}
    (shape : callable type = .arrow reuse quantity domain codomain) : ∀ index, type ≠ .variable index := by
  intro index h; subst h; simp [callable] at shape

theorem argumentAllowed_canonical (assumptions : Assumptions) (quantity : Quantity) {Γ Γ' : Context}
    (similar : Similar Γ Γ') (type : Ty) (uses : Uses) :
    argumentAllowed assumptions quantity Γ' type.canonical uses = argumentAllowed assumptions quantity Γ type uses := by
  simp [argumentAllowed, Ty.canonical_isComputation, Ty.shareableUnder_canonical,
    similar.reusableCaptures]

theorem checkAt_def (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat)
    (term : Term) (expected : Ty) : checkAt assumptions annotations context path term expected =
      elaborate assumptions annotations context path term (.check expected) := rfl

theorem synthAt_def (assumptions : Assumptions) (annotations : Annotations) (context : Context) (path : List Nat)
    (term : Term) : synthAt assumptions annotations context path term =
      elaborate assumptions annotations context path term .synth := rfl

/-- A checker run that succeeds, with a property of its result. -/
@[expose] public def Yields {α : Type} (result : Except CheckRefusal α) (P : α → Prop) : Prop :=
  match result with
  | .ok a => P a
  | .error _ => False

theorem Yields.elim {α : Type} {result : Except CheckRefusal α} {P : α → Prop} (h : Yields result P) :
    ∃ a, result = .ok a ∧ P a := by
  cases result with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => exact False.elim h

theorem Yields.ok {α : Type} {a : α} {P : α → Prop} (h : P a) : Yields (.ok a) P := h

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

theorem fieldsTyping_row_notVariable {assumptions : Assumptions} {context : Context}
    {fields : List (String × Term)} {row : Ty} {uses : Uses}
    (typed : FieldsTyping assumptions context fields row uses) : ∀ index, row ≠ .variable index := by
  intro index h; subst h; cases typed

theorem labelsDistinct_cons {name : String} {body : Term} {rest : List (String × Term)}
    (h : labelsDistinct ((name, body) :: rest) = true) :
    name ∉ rest.map Prod.fst ∧ labelsDistinct rest = true := by
  simp only [labelsDistinct, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h
  refine ⟨?_, h.2⟩
  intro mem
  obtain ⟨⟨n, b⟩, hm, rfl⟩ := List.mem_map.mp mem
  exact h.1 _ hm rfl

/-! ## Eliminations: the shared finish -/

/-- If the synthesis core of an elimination produced `s`, both modes succeed as the
derived type demands. -/
theorem finish_complete {assumptions : Assumptions} {annotations : Annotations} {context : Context}
    {path : List Nat} {term : Term} {derived : Ty} {uses : Uses}
    (s : Synth assumptions context term)
    (unfolds : ∀ mode, elaborate assumptions annotations context path term mode =
      finish assumptions annotations path s mode)
    (agrees : sameType assumptions s.type derived = true) (sameUses : s.uses = uses) :
    Yields (synthAt assumptions annotations context path term)
        (fun r => sameType assumptions r.type derived = true ∧ r.uses = uses) ∧
      (∀ expected, sameType assumptions derived expected = true →
        Yields (checkAt assumptions annotations context path term expected) (fun r => r.uses = uses)) := by
  constructor
  · rw [synthAt_def, unfolds .synth]
    simp only [finish, ascribe, Yields]
    split
    · split
      · rename_i ascribed _ same
        exact ⟨sameType_trans (sameType_symm same) agrees, sameUses⟩
      · exact ⟨agrees, sameUses⟩
    · exact ⟨agrees, sameUses⟩
  · intro expected agreement
    have : sameType assumptions s.type expected = true := sameType_trans agrees agreement
    rw [checkAt_def, unfolds, finish, dif_pos this]
    exact sameUses

/-! ## The theorem -/

/-- What completeness says of one derivation. -/
@[expose] public def Motive (assumptions : Assumptions) (annotations : Annotations)
    (context : Context) (term : Term) (derived : Ty) (uses : Uses) : Prop :=
  ∀ context' path, Similar context context' →
    (synthCovered term = true → Yields (synthAt assumptions annotations context' path term)
        (fun r => sameType assumptions r.type derived = true ∧ r.uses = uses)) ∧
    (checkCovered term = true → ∀ expected, sameType assumptions derived expected = true →
        Yields (checkAt assumptions annotations context' path term expected) (fun r => r.uses = uses))

theorem complete_conversion {assumptions : Assumptions} {annotations : Annotations} {context : Context}
    {term : Term} {actual expected : Ty} {uses : Uses}
    (ih : Motive assumptions annotations context term actual uses)
    (agreement : sameType assumptions actual expected = true) :
    Motive assumptions annotations context term expected uses := by
  intro context' path similar
  obtain ⟨synth, check⟩ := ih context' path similar
  refine ⟨fun covered => ?_, fun covered target agrees => check covered target (sameType_trans agreement agrees)⟩
  obtain ⟨r, hr, ht, hu⟩ := (synth covered).elim
  rw [hr]; exact ⟨sameType_trans ht agreement, hu⟩

/-- Record fields checked by label against a weak head whose members are the derived
row's, canonically. -/
@[expose] public def FieldsMotive (assumptions : Assumptions) (annotations : Annotations)
    (context : Context) (fields : List (String × Term)) (row : Ty) (uses : Uses) : Prop :=
  ∀ context' path index head, Similar context context' → bodiesCovered fields = true →
    labelsDistinct fields = true →
    (∀ name, name ∈ fields.map Prod.fst → rowMember head name = (rowMember row name).map Ty.canonical) →
    Yields (checkFieldsByLabel assumptions annotations context' path index head fields)
      (fun r => r.type.canonical = row.canonical ∧ r.uses = uses)

/-- Arms checked against a result agreeing with the derived one, each under the payload
the scrutinee's weak head gives its label. -/
@[expose] public def ArmsMotive (assumptions : Assumptions) (annotations : Annotations)
    (context : Context) (arms : List (String × Term)) (row result : Ty) (uses : Uses) : Prop :=
  ∀ context' path index head expected, Similar context context' → bodiesCovered arms = true →
    labelsDistinct arms = true →
    (∀ name, name ∈ arms.map Prod.fst → rowMember head name = (rowMember row name).map Ty.canonical) →
    sameType assumptions result expected = true →
    Yields (checkArms assumptions annotations context' path index head expected arms)
      (fun r => r.row.canonical = row.canonical ∧ r.uses = uses)

public theorem complete (assumptions : Assumptions) (annotations : Annotations) {context : Context} {term : Term}
    {derived : Ty} {uses : Uses} (typed : PartialTyping assumptions context term derived uses) :
    Motive assumptions annotations context term derived uses := by
  refine PartialTyping.rec
    (motive_1 := fun context term derived uses _ => Motive assumptions annotations context term derived uses)
    (motive_2 := fun context fields row uses _ => FieldsMotive assumptions annotations context fields row uses)
    (motive_3 := fun context arms row result uses _ => ArmsMotive assumptions annotations context arms row result uses)
    ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend ?specification
    ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject ?case ?ifBool ?perform ?done
    ?effectCase ?fieldsNil ?fieldsCons ?armsNil ?armsCons typed
  case bound =>
    intro Γ index binding found Γ' path similar
    obtain ⟨binding', found', -, equal⟩ := similar.get found
    have done := finish_complete (assumptions := assumptions) (annotations := annotations) (path := path)
      (term := .bound index) ⟨binding'.type, variableUses Γ' index, .bound found'⟩
      (by
        intro mode
        rw [elaborate]
        split
        · rename_i binding'' found''
          rw [found'] at found''; cases found''; rfl
        · rename_i missing; rw [found'] at missing; cases missing)
      (sameType_of_canonical equal.symm) (similar.variableUses index)
    exact ⟨fun _ => done.1, fun _ => done.2⟩
  case natural =>
    intro Γ value Γ' path similar
    have done := finish_complete (assumptions := assumptions) (annotations := annotations) (path := path)
      (term := .nat value) ⟨.natural, zeroUses Γ', .natural Γ' value⟩ (by intro mode; rw [elaborate])
      (sameType_refl _ _) similar.zeroUses
    exact ⟨fun _ => done.1, fun _ => done.2⟩
  case boolean =>
    intro Γ value Γ' path similar
    have done := finish_complete (assumptions := assumptions) (annotations := annotations) (path := path)
      (term := .boolean value) ⟨.boolean, zeroUses Γ', .boolean Γ' value⟩ (by intro mode; rw [elaborate])
      (sameType_refl _ _) similar.zeroUses
    exact ⟨fun _ => done.1, fun _ => done.2⟩
  case label =>
    intro Γ value Γ' path similar
    have done := finish_complete (assumptions := assumptions) (annotations := annotations) (path := path)
      (term := .label value) ⟨literalType value, zeroUses Γ', .label Γ' value⟩ (by intro mode; rw [elaborate])
      (sameType_refl _ _) similar.zeroUses
    exact ⟨fun _ => done.1, fun _ => done.2⟩
  case conversion =>
    intro Γ term actual expected uses _ agreement ih
    exact complete_conversion ih agreement
  case lambda =>
    intro Γ body annotation bodyUses bodyTyped safe valid captures ih Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered] at covered
    have head := whnf_of_sameType (sameType_symm agreement) (by intro i h; cases h)
    simp only [Ty.canonical] at head
    have similar' : Similar (⟨annotation.domain, annotation.parameter⟩ :: Γ)
        ((⟨annotation.domain.canonical, annotation.parameter⟩ : Binding) :: Γ') := ⟨rfl, by simp, similar⟩
    obtain ⟨-, checkBody⟩ := ih _ (path ++ [0]) similar'
    obtain ⟨r, hr, hu⟩ := (checkBody covered annotation.codomain.canonical (sameType_canonical _ _)).elim
    have safe' : safeUses ((⟨annotation.domain.canonical, annotation.parameter⟩ : Binding) :: Γ') r.uses = true := by
      rw [similar'.safeUses, hu]; exact safe
    have valid' : validContext assumptions.shareableVariables
        ((⟨annotation.domain.canonical, annotation.parameter⟩ : Binding) :: Γ') = true := by
      rw [similar'.validContext]; exact valid
    have captures' : reusableAllowed assumptions annotation.reuse Γ' r.uses.tail = true := by
      simp only [reusableAllowed] at captures ⊢; rw [similar.reusableCaptures, hu]; exact captures
    rw [checkAt_def, elaborate]
    split
    · rename_i reuse parameter domain codomain shape
      rw [head] at shape
      cases shape
      simp only [checkAt_def] at hr
      simp only [hr, bind, Except.bind, need_ok safe', need_ok valid', need_ok captures', pure, Except.pure, Yields]
      rw [hu]
    · rename_i notArrow
      exact absurd head (notArrow _ _ _ _)
  case application =>
    intro Γ function argument functionType argumentType domain codomain functionUses argumentUses reuse quantity
      fnTyped argTyped shape argEq allowed ihF ihA Γ' path similar
    have key : (synthCovered function && checkCovered argument) = true →
        Yields (synthAt assumptions annotations Γ' path (.app function argument))
          (fun r => sameType assumptions r.type codomain = true ∧ r.uses = addUses functionUses argumentUses) ∧
        (∀ expected, sameType assumptions codomain expected = true →
          Yields (checkAt assumptions annotations Γ' path (.app function argument) expected)
            (fun r => r.uses = addUses functionUses argumentUses)) := by
      intro covered
      simp only [Bool.and_eq_true] at covered
      obtain ⟨rf, hrf, htf, huf⟩ := ((ihF Γ' (path ++ [0]) similar).1 covered.1).elim
      have head := whnf_of_sameType htf (callable_notVariable shape)
      have shapeC : callable (whnf assumptions rf.type) = .arrow reuse quantity domain.canonical codomain.canonical := by
        rw [head, callable_canonical, shape]; rfl
      obtain ⟨ra, hra, hua⟩ := ((ihA Γ' (path ++ [1]) similar).2 covered.2 domain.canonical
        (by rw [argEq]; exact sameType_canonical _ _)).elim
      have allowed' : argumentAllowed assumptions quantity Γ' domain.canonical ra.uses = true := by
        rw [argumentAllowed_canonical _ _ similar, hua, ← argEq]; exact allowed
      refine finish_complete ⟨codomain.canonical, addUses rf.uses ra.uses,
        .application (.conversion rf.derivation (sameType_whnf _ _)) ra.derivation shapeC rfl allowed'⟩
        ?_ (sameType_symm (sameType_canonical _ _)) (by show addUses rf.uses ra.uses = _; rw [huf, hua])
      intro mode
      rw [elaborate]
      simp only [synthAt_def] at hrf
      simp only [hrf, bind, Except.bind]
      split
      · rename_i r q d c hshape
        rw [shapeC] at hshape; cases hshape
        simp only [checkAt_def] at hra
        simp only [hra, need_ok allowed']
      · rename_i notArrow; exact absurd shapeC (notArrow _ _ _ _)
    exact ⟨fun covered => (key covered).1, fun covered => (key covered).2⟩
  case get =>
    intro Γ target targetType member uses name fuel targetTyped lookup ih Γ' path similar
    have key : synthCovered target = true →
        Yields (synthAt assumptions annotations Γ' path (.get target name))
          (fun r => sameType assumptions r.type member = true ∧ r.uses = uses) ∧
        (∀ expected, sameType assumptions member expected = true →
          Yields (checkAt assumptions annotations Γ' path (.get target name) expected) (fun r => r.uses = uses)) := by
      intro covered
      obtain ⟨r, hr, ht, hu⟩ := ((ih Γ' (path ++ [0]) similar).1 covered).elim
      obtain ⟨depth, found, hl, hm⟩ :=
        Obend.Core.Proofs.Preservation.same_type_lookup_transport ht fuel name member lookup
      have hv : lookupV assumptions.bounds [] r.type name = some found := (lookupV_iff _ _ _ _).2 ⟨depth, hl⟩
      refine finish_complete ⟨found, r.uses, .get r.derivation hl⟩ ?_ (sameType_of_canonical hm) hu
      intro mode
      rw [elaborate]
      simp only [synthAt_def] at hr
      simp only [hr, bind, Except.bind]
      split
      · rename_i m found'; rw [hv] at found'; cases found'; rfl
      · rename_i missing; rw [hv] at missing; cases missing
    exact ⟨fun covered => (key covered).1, fun covered => (key covered).2⟩
  case reflect =>
    intro Γ target specType targetType uses targetTyped ih Γ' path similar
    have key : synthCovered target = true →
        Yields (synthAt assumptions annotations Γ' path (.reflect target))
          (fun r => sameType assumptions r.type specType = true ∧ r.uses = uses) ∧
        (∀ expected, sameType assumptions specType expected = true →
          Yields (checkAt assumptions annotations Γ' path (.reflect target) expected) (fun r => r.uses = uses)) := by
      intro covered
      obtain ⟨r, hr, ht, hu⟩ := ((ih Γ' (path ++ [0]) similar).1 covered).elim
      have head := whnf_of_sameType ht (by intro i h; cases h)
      simp only [Ty.canonical] at head
      refine finish_complete ⟨specType.canonical, r.uses,
        .reflect (PartialTyping.conversion (expected := .prototype specType.canonical targetType.canonical)
          r.derivation (head ▸ sameType_whnf assumptions r.type))⟩ ?_ (sameType_symm (sameType_canonical _ _)) hu
      intro mode
      rw [elaborate]
      simp only [synthAt_def] at hr
      simp only [hr, bind, Except.bind]
      split
      · rename_i s t shape; rw [head] at shape; cases shape; rfl
      · rename_i other; exact absurd head (other _ _)
    exact ⟨fun covered => (key covered).1, fun covered => (key covered).2⟩
  case metadata =>
    intro Γ target metadataType extensionType uses targetTyped ih Γ' path similar
    have key : synthCovered target = true →
        Yields (synthAt assumptions annotations Γ' path (.metadata target))
          (fun r => sameType assumptions r.type metadataType = true ∧ r.uses = uses) ∧
        (∀ expected, sameType assumptions metadataType expected = true →
          Yields (checkAt assumptions annotations Γ' path (.metadata target) expected) (fun r => r.uses = uses)) := by
      intro covered
      obtain ⟨r, hr, ht, hu⟩ := ((ih Γ' (path ++ [0]) similar).1 covered).elim
      have head := whnf_of_sameType ht (by intro i h; cases h)
      simp only [Ty.canonical] at head
      refine finish_complete ⟨metadataType.canonical, r.uses,
        .metadata (PartialTyping.conversion (expected := .specification metadataType.canonical extensionType.canonical)
          r.derivation (head ▸ sameType_whnf assumptions r.type))⟩ ?_ (sameType_symm (sameType_canonical _ _)) hu
      intro mode
      rw [elaborate]
      simp only [synthAt_def] at hr
      simp only [hr, bind, Except.bind]
      split
      · rename_i s t shape; rw [head] at shape; cases shape; rfl
      · rename_i other; exact absurd head (other _ _)
    exact ⟨fun covered => (key covered).1, fun covered => (key covered).2⟩
  case project =>
    intro Γ target specType targetType uses targetTyped ih Γ' path similar
    have key : synthCovered target = true →
        Yields (synthAt assumptions annotations Γ' path (.project target))
          (fun r => sameType assumptions r.type targetType = true ∧ r.uses = uses) ∧
        (∀ expected, sameType assumptions targetType expected = true →
          Yields (checkAt assumptions annotations Γ' path (.project target) expected) (fun r => r.uses = uses)) := by
      intro covered
      obtain ⟨r, hr, ht, hu⟩ := ((ih Γ' (path ++ [0]) similar).1 covered).elim
      have head := whnf_of_sameType ht (by intro i h; cases h)
      simp only [Ty.canonical] at head
      refine finish_complete ⟨targetType.canonical, r.uses,
        .project (PartialTyping.conversion (expected := .prototype specType.canonical targetType.canonical)
          r.derivation (head ▸ sameType_whnf assumptions r.type))⟩ ?_ (sameType_symm (sameType_canonical _ _)) hu
      intro mode
      rw [elaborate]
      simp only [synthAt_def] at hr
      simp only [hr, bind, Except.bind]
      split
      · rename_i s t shape; rw [head] at shape; cases shape; rfl
      · rename_i other; exact absurd head (other _ _)
    exact ⟨fun covered => (key covered).1, fun covered => (key covered).2⟩
  case binary =>
    intro Γ primitive left right input output lu ru shape leftTyped rightTyped ihL ihR Γ' path similar
    have key : (checkCovered left && checkCovered right) = true →
        Yields (synthAt assumptions annotations Γ' path (.binary primitive left right))
          (fun r => sameType assumptions r.type output = true ∧ r.uses = addUses lu ru) ∧
        (∀ expected, sameType assumptions output expected = true →
          Yields (checkAt assumptions annotations Γ' path (.binary primitive left right) expected)
            (fun r => r.uses = addUses lu ru)) := by
      intro covered
      simp only [Bool.and_eq_true] at covered
      have hin : (primitiveTypes primitive).1 = input := by rw [shape]
      have hout : (primitiveTypes primitive).2 = output := by rw [shape]
      obtain ⟨rl, hrl, hul⟩ := ((ihL Γ' (path ++ [0]) similar).2 covered.1 (primitiveTypes primitive).1
        (by rw [hin]; exact sameType_refl _ _)).elim
      obtain ⟨rr, hrr, hur⟩ := ((ihR Γ' (path ++ [1]) similar).2 covered.2 (primitiveTypes primitive).1
        (by rw [hin]; exact sameType_refl _ _)).elim
      refine finish_complete ⟨(primitiveTypes primitive).2, addUses rl.uses rr.uses,
        .binary (Prod.eta _) rl.derivation rr.derivation⟩ ?_
        (by show sameType assumptions (primitiveTypes primitive).2 output = true; rw [hout]; exact sameType_refl _ _)
        (by show addUses rl.uses rr.uses = _; rw [hul, hur])
      intro mode
      rw [elaborate]
      simp only [checkAt_def] at hrl hrr
      simp only [hrl, hrr, bind, Except.bind]
    exact ⟨fun covered => (key covered).1, fun covered => (key covered).2⟩
  case extend =>
    intro Γ target fields targetType row targetUses fieldUses fuel _ _ _ _ _ Γ' path similar
    exact ⟨fun covered => by simp [synthCovered] at covered, fun covered => by simp [checkCovered] at covered⟩
  case mix =>
    intro Γ lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped
      lowerShape upperShape captures shareSelf shareInherited shareMiddle ihL ihU Γ' path similar
    have key : (synthCovered lower && synthCovered upper) = true →
        Yields (synthAt assumptions annotations Γ' path (.mix lower upper))
          (fun r => sameType assumptions r.type
            (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) = true ∧
            r.uses = addUses lu uu) ∧
        (∀ expected, sameType assumptions
            (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) expected = true →
          Yields (checkAt assumptions annotations Γ' path (.mix lower upper) expected) (fun r => r.uses = addUses lu uu)) := by
      intro covered
      simp only [Bool.and_eq_true] at covered
      obtain ⟨rl, hrl, htl, hul⟩ := ((ihL Γ' (path ++ [0]) similar).1 covered.1).elim
      obtain ⟨ru, hru, htu, huu⟩ := ((ihU Γ' (path ++ [1]) similar).1 covered.2).elim
      have shapeL : callable (whnf assumptions rl.type) = .arrow .reusable .unrestricted self.canonical
          (.arrow .reusable .unrestricted inherited.canonical middle.canonical) := by
        rw [whnf_of_sameType htl (callable_notVariable lowerShape), callable_canonical, lowerShape]; rfl
      have shapeU : callable (whnf assumptions ru.type) = .arrow .reusable .unrestricted self.canonical
          (.arrow .reusable .unrestricted middle.canonical provided.canonical) := by
        rw [whnf_of_sameType htu (callable_notVariable upperShape), callable_canonical, upperShape]; rfl
      have captures' : reusableCaptures assumptions.shareableVariables Γ' (addUses rl.uses ru.uses) = true := by
        rw [similar.reusableCaptures, hul, huu]; exact captures
      have shareSelf' : self.canonical.shareableUnder assumptions.shareableVariables = true := by
        rw [Ty.shareableUnder_canonical]; exact shareSelf
      have shareInherited' : inherited.canonical.shareableUnder assumptions.shareableVariables = true := by
        rw [Ty.shareableUnder_canonical]; exact shareInherited
      have shareMiddle' : middle.canonical.shareableUnder assumptions.shareableVariables = true := by
        rw [Ty.shareableUnder_canonical]; exact shareMiddle
      refine finish_complete ⟨.arrow .reusable .unrestricted self.canonical
          (.arrow .reusable .unrestricted inherited.canonical provided.canonical), addUses rl.uses ru.uses,
        .mix (.conversion rl.derivation (sameType_whnf _ _)) (.conversion ru.derivation (sameType_whnf _ _))
          shapeL shapeU captures' shareSelf' shareInherited' shareMiddle'⟩ ?_
        (sameType_of_canonical (by simp [Ty.canonical])) (by show addUses rl.uses ru.uses = _; rw [hul, huu])
      intro mode
      rw [elaborate]
      simp only [synthAt_def] at hrl hru
      simp only [hrl, hru, bind, Except.bind]
      split
      · rename_i s i m s' m' p hl hu
        rw [shapeL] at hl; rw [shapeU] at hu
        cases hl; cases hu
        simp only [need_ok captures', need_ok shareSelf', need_ok shareInherited', need_ok shareMiddle', ↓reduceDIte]
      · rename_i other
        exact (other _ _ _ _ _ _ shapeL shapeU).elim
    exact ⟨fun covered => (key covered).1, fun covered => (key covered).2⟩
  case fix =>
    intro Γ spec inheritedTerm specType inherited target su iu specTyped shape inheritedTyped shareTarget allowed
      captures ihS ihI Γ' path similar
    have key : (synthCovered spec && checkCovered inheritedTerm) = true →
        Yields (synthAt assumptions annotations Γ' path (.fix spec inheritedTerm))
          (fun r => sameType assumptions r.type target = true ∧ r.uses = addUses su iu) ∧
        (∀ expected, sameType assumptions target expected = true →
          Yields (checkAt assumptions annotations Γ' path (.fix spec inheritedTerm) expected)
            (fun r => r.uses = addUses su iu)) := by
      intro covered
      simp only [Bool.and_eq_true] at covered
      obtain ⟨rs, hrs, hts, hus⟩ := ((ihS Γ' (path ++ [0]) similar).1 covered.1).elim
      have shapeC : callable (whnf assumptions rs.type) = .arrow .reusable .unrestricted target.canonical
          (.arrow .reusable .unrestricted inherited.canonical target.canonical) := by
        rw [whnf_of_sameType hts (callable_notVariable shape), callable_canonical, shape]; rfl
      obtain ⟨ri, hri, hui⟩ := ((ihI Γ' (path ++ [1]) similar).2 covered.2 inherited.canonical
        (sameType_canonical _ _)).elim
      have shareTarget' : target.canonical.shareableUnder assumptions.shareableVariables = true := by
        rw [Ty.shareableUnder_canonical]; exact shareTarget
      have allowed' : argumentAllowed assumptions .unrestricted Γ' inherited.canonical ri.uses = true := by
        rw [argumentAllowed_canonical _ _ similar, hui]; exact allowed
      have captures' : reusableCaptures assumptions.shareableVariables Γ' rs.uses = true := by
        rw [similar.reusableCaptures, hus]; exact captures
      refine finish_complete ⟨target.canonical, addUses rs.uses ri.uses,
        .fix (.conversion rs.derivation (sameType_whnf _ _)) shapeC ri.derivation shareTarget' allowed' captures'⟩ ?_
        (sameType_symm (sameType_canonical _ _)) (by show addUses rs.uses ri.uses = _; rw [hus, hui])
      intro mode
      rw [elaborate]
      simp only [synthAt_def] at hrs
      simp only [hrs, bind, Except.bind]
      split
      · rename_i t i o hshape
        rw [shapeC] at hshape; cases hshape
        simp only [checkAt_def] at hri
        simp only [hri, bind, Except.bind, need_ok shareTarget', need_ok allowed', need_ok captures', ↓reduceDIte]
      · rename_i other; exact absurd shapeC (other _ _ _)
    exact ⟨fun covered => (key covered).1, fun covered => (key covered).2⟩
  case specification =>
    intro Γ metadata extension metadataType extensionType mu eu mTyped eTyped hm he ihM ihE Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered, Bool.and_eq_true] at covered
    have head := whnf_of_sameType (sameType_symm agreement) (by intro i h; cases h)
    simp only [Ty.canonical] at head
    obtain ⟨rm, hrm, hum⟩ := ((ihM Γ' (path ++ [0]) similar).2 covered.1 _ (sameType_canonical _ _)).elim
    obtain ⟨re, hre, hue⟩ := ((ihE Γ' (path ++ [1]) similar).2 covered.2 _ (sameType_canonical _ _)).elim
    have pm : (!metadataType.canonical.isComputation) = true := by simp [Ty.canonical_isComputation, hm]
    have pe : (!extensionType.canonical.isComputation) = true := by simp [Ty.canonical_isComputation, he]
    rw [checkAt_def, elaborate]
    simp only [introduce]
    split
    · rename_i a b shape
      rw [head] at shape; cases shape
      simp only [checkAt_def] at hrm hre
      simp only [hrm, hre, bind, Except.bind, need_ok pm, need_ok pe, pure, Except.pure, Yields]
      rw [hum, hue]
    · rename_i other; exact absurd head (other _ _)
  case prototype =>
    intro Γ spec target specType targetType su tu sTyped tTyped hs ht ihS ihT Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered, Bool.and_eq_true] at covered
    have head := whnf_of_sameType (sameType_symm agreement) (by intro i h; cases h)
    simp only [Ty.canonical] at head
    obtain ⟨rs, hrs, hus⟩ := ((ihS Γ' (path ++ [0]) similar).2 covered.1 _ (sameType_canonical _ _)).elim
    obtain ⟨rt, hrt, hut⟩ := ((ihT Γ' (path ++ [1]) similar).2 covered.2 _ (sameType_canonical _ _)).elim
    have ps : (!specType.canonical.isComputation) = true := by simp [Ty.canonical_isComputation, hs]
    have pt : (!targetType.canonical.isComputation) = true := by simp [Ty.canonical_isComputation, ht]
    rw [checkAt_def, elaborate]
    simp only [introduce]
    split
    · rename_i a b shape
      rw [head] at shape; cases shape
      simp only [checkAt_def] at hrs hrt
      simp only [hrs, hrt, bind, Except.bind, need_ok ps, need_ok pt, pure, Except.pure, Yields]
      rw [hus, hut]
    · rename_i other; exact absurd head (other _ _)
  case inject =>
    intro Γ tag payload payloadType row uses fuel payloadTyped lookup pure ih Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered] at covered
    have head := whnf_of_sameType (sameType_symm agreement) (by intro i h; cases h)
    simp only [Ty.canonical] at head
    obtain ⟨depth, member, hl, hm⟩ := Obend.Core.Proofs.Preservation.canonical_lookup_transport
      assumptions.bounds row.canonical row (by simp) fuel tag payloadType lookup
    have hv : lookupV assumptions.bounds [] row.canonical tag = some member := (lookupV_iff _ _ _ _).2 ⟨depth, hl⟩
    obtain ⟨r, hr, hu⟩ := ((ih Γ' (path ++ [0]) similar).2 covered member (sameType_of_canonical hm.symm)).elim
    have pp : (!member.isComputation) = true := by
      rw [← Ty.canonical_isComputation, hm, Ty.canonical_isComputation]; simp [pure]
    rw [checkAt_def, elaborate]
    simp only [introduce]
    split
    · rename_i r' shape
      rw [head] at shape; cases shape
      split
      · rename_i m found
        rw [hv] at found; cases found
        simp only [checkAt_def] at hr
        simp only [hr, bind, Except.bind, need_ok pp, pure, Except.pure, Yields]
        exact hu
      · rename_i missing; rw [hv] at missing; cases missing
    · rename_i other; exact absurd head (other _)
  case perform =>
    intro Γ plan planType response uses planTyped isPlan isData ih Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered] at covered
    have head := whnf_of_sameType (sameType_symm agreement) (by intro i h; cases h)
    simp only [Ty.canonical] at head
    obtain ⟨r, hr, hu⟩ := ((ih Γ' (path ++ [0]) similar).2 covered _ (sameType_canonical _ _)).elim
    have plan' := isPlan_canonical isPlan
    have data' := isData_canonical isData
    rw [checkAt_def, elaborate]
    simp only
    split
    · rename_i p q t shape
      rw [head] at shape; cases shape
      simp only [checkAt_def] at hr
      simp only [hr, bind, Except.bind, need_ok plan', need_ok data', pure, Except.pure, Yields, ↓reduceDIte]
      exact hu
    · rename_i other; exact absurd head (other _ _ _)
  case done =>
    intro Γ value planType response result uses valueTyped pure ih Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered] at covered
    have head := whnf_of_sameType (sameType_symm agreement) (by intro i h; cases h)
    simp only [Ty.canonical] at head
    obtain ⟨r, hr, hu⟩ := ((ih Γ' (path ++ [0]) similar).2 covered _ (sameType_canonical _ _)).elim
    have pr : (!result.canonical.isComputation) = true := by simp [Ty.canonical_isComputation, pure]
    rw [checkAt_def, elaborate]
    split
    · rename_i p q t shape
      rw [head] at shape; cases shape
      simp only [checkAt_def] at hr
      simp only [hr, bind, Except.bind, need_ok pr, Except.pure, Yields]
      exact hu
    · rename_i other; exact absurd head (other _ _ _)
  case ifBool =>
    intro Γ condition whenTrue whenFalse result cu tu fu cTyped tTyped fTyped ihC ihT ihF Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered, Bool.and_eq_true] at covered
    obtain ⟨rc, hrc, huc⟩ := ((ihC Γ' (path ++ [0]) similar).2 covered.1.1 .boolean (sameType_refl _ _)).elim
    obtain ⟨rt, hrt, hut⟩ := ((ihT Γ' (path ++ [1]) similar).2 covered.1.2 expected agreement).elim
    obtain ⟨rf, hrf, huf⟩ := ((ihF Γ' (path ++ [2]) similar).2 covered.2 expected agreement).elim
    rw [checkAt_def, elaborate]
    simp only [introduce]
    simp only [checkAt_def] at hrc hrt hrf
    simp only [hrc, hrt, hrf, bind, Except.bind, pure, Except.pure, Yields]
    rw [huc, hut, huf]
  case ifZero =>
    intro Γ value zero successor result vu zu su vTyped zTyped sTyped safe ihV ihZ ihS Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered, Bool.and_eq_true] at covered
    have similar' : Similar (⟨.natural, .unrestricted⟩ :: Γ) (⟨.natural, .unrestricted⟩ :: Γ') :=
      ⟨rfl, rfl, similar⟩
    obtain ⟨rv, hrv, huv⟩ := ((ihV Γ' (path ++ [0]) similar).2 covered.1.1 .natural (sameType_refl _ _)).elim
    obtain ⟨rz, hrz, huz⟩ := ((ihZ Γ' (path ++ [1]) similar).2 covered.1.2 expected agreement).elim
    obtain ⟨rs, hrs, hus⟩ := ((ihS _ (path ++ [2]) similar').2 covered.2 expected agreement).elim
    have safe' : safeUses (⟨.natural, .unrestricted⟩ :: Γ') rs.uses = true := by
      rw [similar'.safeUses, hus]; exact safe
    rw [checkAt_def, elaborate]
    simp only [introduce]
    simp only [checkAt_def] at hrv hrz hrs
    simp only [hrv, hrz, hrs, bind, Except.bind, need_ok safe', pure, Except.pure, Yields]
    rw [huv, huz, hus]
  case record =>
    intro Γ fields row uses fieldsTyped ihF Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered, Bool.and_eq_true] at covered
    have head := whnf_of_sameType (sameType_symm agreement) (fieldsTyping_row_notVariable fieldsTyped)
    obtain ⟨r, hr, hrow, hu⟩ := (ihF Γ' path 0 (whnf assumptions expected) similar covered.2 covered.1
      (fun name _ => by rw [head, rowMember_canonical])).elim
    have agrees : sameType assumptions r.type expected = true :=
      sameType_trans (sameType_of_canonical hrow) agreement
    rw [checkAt_def, elaborate]
    simp only [introduce, dif_pos covered.1]
    simp only [hr, bind, Except.bind, need_ok agrees, pure, Except.pure, Yields]
    exact hu
  case case =>
    intro Γ scrutinee arms row result su au sTyped aTyped distinct ihS ihA Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered, Bool.and_eq_true] at covered
    obtain ⟨rs, hrs, hts, hus⟩ := ((ihS Γ' (path ++ [0]) similar).1 covered.1).elim
    have head := whnf_of_sameType hts (by intro i h; cases h)
    simp only [Ty.canonical] at head
    obtain ⟨ra, hra, hrow, hua⟩ := (ihA Γ' (path ++ [1]) 0 row.canonical expected similar covered.2 distinct
      (fun name _ => rowMember_canonical row name) agreement).elim
    have agrees : sameType assumptions rs.type (.variant ra.row) = true :=
      sameType_trans hts (sameType_of_canonical (by simp [Ty.canonical, hrow]))
    simp only [synthAt_def] at hrs
    cases arms with
    | nil =>
      rw [checkAt_def, elaborate]
      simp only [hrs, bind, Except.bind, head, hra, need_ok agrees, pure, Except.pure, Yields]
      rw [hus, hua]
    | cons arm rest =>
      obtain ⟨name, body⟩ := arm
      rw [checkAt_def, elaborate]
      simp only [hrs, bind, Except.bind, need_ok distinct, head, hra, need_ok agrees, pure, Except.pure, Yields]
      rw [hus, hua]
  case effectCase =>
    intro Γ scrutinee arms planType response row result su au sTyped aTyped pure distinct ihS ihA Γ' path similar
    refine ⟨fun covered => by simp [synthCovered] at covered, fun covered expected agreement => ?_⟩
    simp only [checkCovered, Bool.and_eq_true] at covered
    obtain ⟨rs, hrs, hts, hus⟩ := ((ihS Γ' (path ++ [0]) similar).1 covered.1).elim
    have head := whnf_of_sameType hts (by intro i h; cases h)
    simp only [Ty.canonical] at head
    have headE := whnf_of_sameType (sameType_symm agreement) (by intro i h; cases h)
    simp only [Ty.canonical] at headE
    obtain ⟨ra, hra, hrow, hua⟩ := (ihA Γ' (path ++ [1]) 0 row.canonical
      (.computation planType.canonical response.canonical result.canonical) similar covered.2 distinct
      (fun name _ => rowMember_canonical row name)
      (sameType_of_canonical (by simp [Ty.canonical]))).elim
    have agrees : sameType assumptions rs.type
        (.computation planType.canonical response.canonical (.variant ra.row)) = true :=
      sameType_trans hts (sameType_of_canonical (by simp [Ty.canonical, hrow]))
    have pr : (!result.canonical.isComputation) = true := by simp [Ty.canonical_isComputation, pure]
    have agreesE : sameType assumptions (.computation planType.canonical response.canonical result.canonical)
        expected = true :=
      sameType_trans (sameType_of_canonical (by simp [Ty.canonical])) agreement
    simp only [synthAt_def] at hrs
    cases arms with
    | nil =>
      rw [checkAt_def, elaborate]
      simp only [hrs, bind, Except.bind, head, headE, hra, need_ok agrees, need_ok pr, need_ok agreesE,
        pure, Except.pure, Yields]
      show addUses rs.uses ra.uses = _; rw [hus, hua]
    | cons arm rest =>
      obtain ⟨name, body⟩ := arm
      rw [checkAt_def, elaborate]
      simp only [hrs, bind, Except.bind, need_ok distinct, head, headE, hra, need_ok agrees, need_ok pr,
        need_ok agreesE, pure, Except.pure, Yields]
      show addUses rs.uses ra.uses = _; rw [hus, hua]
  case fieldsNil =>
    intro Γ Γ' path index head similar _ _ _
    simp [checkFieldsByLabel, pure, Except.pure, Yields, similar.zeroUses]
  case fieldsCons =>
    intro Γ name body rest type row bu ru bodyTyped restTyped pure ihB ihR Γ' path index head similar covered distinct
      members
    simp only [bodiesCovered, Bool.and_eq_true] at covered
    obtain ⟨fresh, distinct'⟩ := labelsDistinct_cons distinct
    have found : rowMember head name = some type.canonical := by
      rw [members name (by simp)]; simp [rowMember]
    obtain ⟨rb, hrb, hub⟩ := ((ihB Γ' (path ++ [index]) similar).2 covered.1 _ (sameType_canonical _ _)).elim
    obtain ⟨rr, hrr, hrow, hur⟩ := (ihR Γ' path (index + 1) head similar covered.2 distinct' (fun n mem => by
      rw [members n (by simp [mem])]
      have : name ≠ n := fun e => fresh (e ▸ mem)
      simp [rowMember, this])).elim
    have pt : (!type.canonical.isComputation) = true := by simp [Ty.canonical_isComputation, pure]
    rw [checkFieldsByLabel]
    simp only [found]
    simp only [checkAt_def] at hrb
    simp only [hrb, hrr, bind, Except.bind, need_ok pt, pure, Except.pure, Yields]
    refine ⟨?_, by show addUses rb.uses rr.uses = _; rw [hub, hur]⟩
    simp [Ty.canonical, hrow]
  case armsNil =>
    intro Γ result Γ' path index head expected similar _ _ _ _
    simp [checkArms, pure, Except.pure, Yields, similar.zeroUses]
  case armsCons =>
    intro Γ name body rest payload row result bu ru bodyTyped safe share restTyped ihB ihR Γ' path index head
      expected similar covered distinct members agreement
    simp only [bodiesCovered, Bool.and_eq_true] at covered
    obtain ⟨fresh, distinct'⟩ := labelsDistinct_cons distinct
    have found : rowMember head name = some payload.canonical := by
      rw [members name (by simp)]; simp [rowMember]
    have similar' : Similar (⟨payload, .unrestricted⟩ :: Γ) (⟨payload.canonical, .unrestricted⟩ :: Γ') :=
      ⟨rfl, by simp, similar⟩
    have share' : payload.canonical.shareableUnder assumptions.shareableVariables = true := by
      rw [Ty.shareableUnder_canonical]; exact share
    obtain ⟨rb, hrb, hub⟩ := ((ihB _ (path ++ [index]) similar').2 covered.1 expected agreement).elim
    have safe' : safeUses (⟨payload.canonical, .unrestricted⟩ :: Γ') rb.uses = true := by
      rw [similar'.safeUses, hub]; exact safe
    obtain ⟨rr, hrr, hrow, hur⟩ := (ihR Γ' path (index + 1) head expected similar covered.2 distinct'
      (fun n mem => by
        rw [members n (by simp [mem])]
        have : name ≠ n := fun e => fresh (e ▸ mem)
        simp [rowMember, this]) agreement).elim
    rw [checkArms]
    simp only [found]
    simp only [checkAt_def] at hrb
    simp only [hrb, hrr, bind, Except.bind, need_ok share', need_ok safe', pure, Except.pure, Yields]
    refine ⟨?_, by show addUses rb.uses.tail rr.uses = _; rw [hub, hur]⟩
    simp [Ty.canonical, hrow]

/-- **Completeness on the fragment.** A derivation of a covered term, with the
top-level premises a certificate carries, makes `checkAgainst` succeed against any type
agreeing with the derived one, whatever the annotations, with the derivation's usage
vector. -/
public theorem checkAgainst_complete {source : AnnotatedTerm} {context : Context} {derived expected : Ty}
    {uses : Uses} (typed : PartialTyping source.assumptions context source.term derived uses)
    (covered : checkCovered source.term = true)
    (safe : safeUses context uses = true)
    (valid : validContext source.assumptions.shareableVariables context = true)
    (assumptionsValid : source.assumptions.valid = true)
    (agreement : sameType source.assumptions derived expected = true) :
    ∃ checked, checkAgainst source context expected = .ok checked ∧ checked.uses = uses := by
  obtain ⟨r, hr, hu⟩ := ((complete source.assumptions source.annotations typed context [] (Similar.refl _)).2
    covered expected agreement).elim
  have safe' : safeUses context r.uses = true := by rw [hu]; exact safe
  refine ⟨⟨expected, r.uses, r.derivation, safe', valid, assumptionsValid⟩, ?_, hu⟩
  simp only [checkAgainst, hr, bind, Except.bind, need_ok safe', need_ok valid, need_ok assumptionsValid,
    pure, Except.pure]

/-- The form the slot layer asks: a certificate at `type` for a covered term means the
checker accepts the term at `type`. -/
public theorem checked_covered_accepted {source : AnnotatedTerm} {context : Context}
    (certificate : Checked source context) (covered : checkCovered source.term = true) :
    ∃ checked, checkAgainst source context certificate.type = .ok checked :=
  let ⟨checked, accepted, _⟩ := checkAgainst_complete certificate.derivation covered certificate.safe
    certificate.contextValid certificate.assumptionsValid (sameType_refl _ _)
  ⟨checked, accepted⟩

/-! ## The fragment boundary bites -/

/-- A lambda applied directly: typable at `Nat`, outside the fragment (the lambda sits in
synthesis position), and refused bare, naming the missing annotation. -/
@[expose] public def appliedLambda : AnnotatedTerm := ⟨.app (.lam (.bound 0)) (.nat 1), fun _ => none, {}⟩

/-- Its certificate: the lambda typed at `Nat → Nat`, applied. -/
@[expose] public def appliedLambdaChecked : Checked appliedLambda [] :=
  ⟨.natural, [], .application (functionType := .arrow .reusable .unrestricted .natural .natural)
    (.lambda (annotation := ⟨.natural, .natural, .unrestricted, .reusable⟩) (.bound (binding := ⟨.natural, .unrestricted⟩) rfl)
      (by decide) (by decide) (by decide))
    (.natural _ _) rfl rfl (by decide), rfl, rfl, rfl⟩

public theorem appliedLambda_boundary :
    checkCovered appliedLambda.term = false ∧
    (match checkAgainst appliedLambda [] appliedLambdaChecked.type with
      | .error refusal => some refusal
      | .ok _ => none) = some (.missingLambdaAnnotation [0]) := by decide

/-- Annotating the lambda is enough: the same term then checks. -/
public theorem appliedLambda_annotated_checks :
    (checkAgainst { appliedLambda with annotations := fun _ => some ⟨.natural, .natural, .unrestricted, .reusable⟩ }
      [] .natural).toOption.isSome = true := by decide

/-- The coverage premise cannot be dropped: a certificate whose term is refused at its type. -/
public theorem coverage_premise_needed :
    ¬ ∀ (source : AnnotatedTerm) (context : Context) (certificate : Checked source context),
      ∃ checked, checkAgainst source context certificate.type = .ok checked := by
  intro all
  obtain ⟨checked, accepted⟩ := all appliedLambda [] appliedLambdaChecked
  have refused := appliedLambda_boundary.2
  rw [accepted] at refused
  cases refused

/- The boundary theorem leans on the fragment excluding lambdas in synthesis position:
widen the fragment to everything and its stored proof is rejected. -/
#tooth appliedLambda_boundary by mutation checkCovered := fun _ => true

#assert_axioms complete checkAgainst_complete checked_covered_accepted appliedLambda_boundary coverage_premise_needed
  appliedLambda_annotated_checks whnf_of_sameType callable_canonical isData_canonical rowMember_canonical

end Obend.Core.Proofs.BidirectionalCompleteness
