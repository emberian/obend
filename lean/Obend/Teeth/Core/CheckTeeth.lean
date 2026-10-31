module
/-
# Obend.Core.Proofs.CheckTeeth — the checker's fixtures and the teeth that bite them

Every executable tooth of `Obend.Core.Check`: programs the checker accepts and programs it refuses, by
name (captures, custody, affine use, rows, sums, shadowing, activities), the template fixtures
(`futureRowSource` and its instantiations), and the classification teeth on
`Obend.Core.Packet.refusalKind`. Moved out of `Obend.Core.Check` on 2026-10-30: a tooth edit
rebuilt every importer of the checker; here nothing imports this module. Historical refusal of arrow congruence is retained
explicitly for legacySameType and replaced by a positive public-agreement tooth.
-/
public import Obend.Core.Ty
public import Obend.Core.Term
public import Obend.Core.Check
public import Obend.Core.Packet
public import Obend.Core.RecursiveAgreement
public import Obend.Tactic.MonadicReduction
@[expose] public section
namespace Obend.Core.Proofs.CheckTeeth
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Packet
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

-- These are local reduction rules for this executable fixture module. The
-- closed runs are evaluated by the kernel (`check_reduce`); no second checker lives
-- in this test frontend.
attribute [local simp] check infer inferFields inferArms checkExtension agree
  Assumptions.valid Assumptions.alias callable variantRow overlay primitiveTypes literalType
  reusableAllowed argumentAllowed labelsDistinct
  zeroUses variableUses addUses safeUses safeQuantity validContext reusableCaptures
  Ty.shareable Ty.shareableUnder Ty.isComputation Ty.isData Ty.isPlan
  Ty.isRow Ty.lookup Ty.supports Ty.canonical Ty.insertCanonical Ty.put Ty.tail
  Quantity.fits linearFree joinUses branchesAgree Quantity.agrees ExtensionFamilies.functionType
  sameStep legacySameType Assumptions.orbit Assumptions.unfoldHead
  refusalKind relaxQuantities unrestrictedTy ampleFuel
  planType planRow responseType
  List.range_succ List.replicate_succ List.zipWith List.lookup
  lookupV isRowV lookupW isRowW walkRow unvisited

-- Normalize only a monadic source until its concrete result selects a branch.
attribute [local congr] Obend.Tactic.MonadicReduction.option_bind_source_congr
attribute [local simp ↓] Option.bind_eq_bind

-- Keep graph computation out of definitional-equality checks while reducing
-- the checker. Matching reflexivity after its arguments simplify is cheap.
attribute [local irreducible] sameType Obend.Core.EquiRecursiveAgreement.agrees
  Obend.Core.TypeGraph.candidate
attribute [local simp] sameType_refl sameType_extends

/-- Every checker tooth is a closed run the kernel evaluates. The type-graph worklist recurses on
one `Nat` measure (`FiniteBisimulation.worklist`), so `decide +kernel` reduces it like the rest of
the checker; no simplifier fallback remains. -/
macro "check_reduce" : tactic => `(tactic| decide +kernel)

@[local simp] def reusableNaturalCapture : AnnotatedTerm :=
  ⟨.lam (.bound 1), fun _ => some ⟨.natural,.natural,.erased,.reusable⟩, {}⟩
@[local simp] def custodyCapture (reuse : Reuse) : AnnotatedTerm :=
  ⟨.lam (.bound 1), fun _ => some ⟨.natural,.custody 17,.erased,reuse⟩, {}⟩

theorem reusable_lexical_capture_accepted :
    (check reusableNaturalCapture [⟨.natural,.unrestricted⟩] 8).isSome = true := by check_reduce

theorem custody_in_reusable_closure_refused :
    (check (custodyCapture .reusable) [⟨.custody 17,.linear⟩] 8).isNone = true := by check_reduce

theorem custody_in_once_closure_accepted :
    (check (custodyCapture .once) [⟨.custody 17,.linear⟩] 8).isSome = true := by check_reduce

@[local simp] def duplicateAffine : AnnotatedTerm :=
  ⟨.binary .add (.bound 0) (.bound 0), fun _ => none, {}⟩
theorem duplicate_affine_refused :
    (check duplicateAffine [⟨.natural,.affine⟩] 8).isNone = true := by check_reduce

@[local simp] def hiddenCustody : AnnotatedTerm := ⟨.bound 0, fun _ => none, {}⟩
theorem record_wrapper_does_not_hide_custody :
    (check hiddenCustody [⟨.field "authority" (.custody 17) .emptyRow,.unrestricted⟩] 8).isNone = true := by check_reduce

/-- Independently typed Unit-row→Nat and Nat→Label extensions compose under
one final Nat self; neither targets only records nor homogeneous endomorphisms. -/
@[local simp] def heterogeneousSource : AnnotatedTerm :=
  ⟨.mix (.lam (.lam (.nat 7))) (.lam (.lam (.label "done"))),
    fun position =>
      if position = [0] then some ⟨.natural,.arrow .reusable .unrestricted .emptyRow .natural,.unrestricted,.reusable⟩
      else if position = [0,0] then some ⟨.emptyRow,.natural,.unrestricted,.reusable⟩
      else if position = [1] then some ⟨.natural,.arrow .reusable .unrestricted .natural .label,.unrestricted,.reusable⟩
      else if position = [1,0] then some ⟨.natural,.label,.unrestricted,.reusable⟩ else none, {}⟩
theorem heterogeneous_runtime_mix_accepted :
    (check heterogeneousSource [] 16).isSome = true := by check_reduce

/-- Symbolic future Self has a self-dependent binary method bound; future Super
is passed through as an unknown row and receives a new field. No closed record
or fixed C→V(C) is substituted into this independent source derivation. -/
@[local simp] def futureRowSource : AnnotatedTerm :=
  ⟨.lam (.lam (.extend (.bound 0) [("answer",.nat 42)])),
    fun position =>
      if position = [] then some ⟨.variable 0,
        .arrow .reusable .unrestricted (.variable 1) (.field "answer" .natural (.variable 1)),.unrestricted,.reusable⟩
      else if position = [0] then some ⟨.variable 1,.field "answer" .natural (.variable 1),.unrestricted,.reusable⟩
      else none,
    ⟨[(0,.field "combine" (.arrow .reusable .unrestricted (.variable 0) (.variable 0)) .emptyRow),
       (1,.emptyRow)], [0,1], []⟩⟩

theorem independently_checked_future_rows :
    (check futureRowSource [] 16).isSome = true := by check_reduce

@[local simp] def futureRowChecked : Checked futureRowSource [] :=
  (check futureRowSource [] 16).get independently_checked_future_rows

/-- This source can be separately instantiated at EVERY future Self/Super type
in the declared shareable fragment. Unknown members stay in Super itself, not
in a fixed closed record chosen during extension compilation. -/
@[local simp] def futureRowInstantiation (self super : Ty) : AnnotatedTerm :=
  ⟨futureRowSource.term, fun position =>
    if position = [] then some ⟨self,
      .arrow .reusable .unrestricted super (.field "answer" .natural super),.unrestricted,.reusable⟩
    else if position = [0] then some ⟨super,.field "answer" .natural super,.unrestricted,.reusable⟩
    else none, {}⟩

theorem future_row_instantiation_accepted (self super : Ty)
    (selfShareable : self.shareable = true) (superShareable : super.shareable = true)
    (superRow : super.isRow [] 64 = true) :
    (check (futureRowInstantiation self super) [] 16).isSome = true := by
  simp [check, infer, inferFields, futureRowInstantiation, futureRowSource, agree,
    Assumptions.alias, Assumptions.valid, overlay, zeroUses, variableUses, addUses, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures,
    List.range_succ, List.zipWith, selfShareable, superShareable, (Ty.isRow_mono superRow (by omega) : super.isRow [] 77 = true),
    Ty.isComputation]

/-- A total law provider proves a law ABOUT the partial runtime term; source
law names alone cannot construct this evidence. Compatible retention is chosen
explicitly rather than asserted as a universal consequence of inheritance. -/
structure LawProvider (source : AnnotatedTerm) (law : Term → Prop) where
  evidence : law source.erase

structure RetainedContracts (source : AnnotatedTerm) (laws : List (Term → Prop)) where
  providers : ∀ law ∈ laws, LawProvider source law

@[local simp] def FutureRowTyped (source : Ty → Ty → AnnotatedTerm) : Prop :=
  ∀ self super, self.shareable = true → super.shareable = true → super.isRow [] 64 = true →
    ∃ checked : Checked (source self super) [],
      checked.type = .arrow .reusable .unrestricted self
        (.arrow .reusable .unrestricted super (.field "answer" .natural super))


@[local simp] def futureRowInstanceChecked (self super : Ty)
    (selfShareable : self.shareable = true) (superShareable : super.shareable = true)
    (superRow : super.isRow [] 64 = true) : Checked (futureRowInstantiation self super) [] :=
  (check (futureRowInstantiation self super) [] 16).get
    (future_row_instantiation_accepted self super selfShareable superShareable superRow)

theorem future_row_typed : FutureRowTyped futureRowInstantiation := by
  intro self super hs ht hr
  refine ⟨futureRowInstanceChecked self super hs ht hr, ?_⟩
  simp [futureRowInstanceChecked, check, infer, inferFields, futureRowInstantiation,
    futureRowSource, Assumptions.alias, Assumptions.valid, overlay, zeroUses, variableUses, addUses, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures,
    List.range_succ, List.zipWith, hs, ht, (Ty.isRow_mono hr (by omega) : super.isRow [] 77 = true), Ty.isComputation]

/-- Independently authored code changes a self-sensitive method type at every
future Self instantiation, including negative arrow occurrences. -/
@[local simp] def futureBinaryInstantiation (self super : Ty) : AnnotatedTerm :=
  ⟨.lam (.lam (.extend (.bound 0) [("combine",.lam (.bound 0))])),
    fun position =>
      if position = [] then some ⟨self,
        .arrow .reusable .unrestricted super
          (.field "combine" (.arrow .reusable .unrestricted self self) super),.unrestricted,.reusable⟩
      else if position = [0] then some ⟨super,
        .field "combine" (.arrow .reusable .unrestricted self self) super,.unrestricted,.reusable⟩
      else if position = [0,0,1,0] then some ⟨self,self,.unrestricted,.reusable⟩
      else none, {}⟩

theorem future_binary_instantiation_accepted (self super : Ty)
    (selfShareable : self.shareable = true) (superShareable : super.shareable = true)
    (superRow : super.isRow [] 64 = true) :
    (check (futureBinaryInstantiation self super) [] 20).isSome = true := by
  simp [check, infer, inferFields, futureBinaryInstantiation, agree, Assumptions.alias, Assumptions.valid, overlay,
    zeroUses, variableUses, addUses, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures,
    List.range_succ, List.zipWith, selfShareable, superShareable,
    (Ty.isRow_mono superRow (by omega) : super.isRow [] 81 = true), Ty.isComputation]

@[local simp] def scalarExtend : AnnotatedTerm :=
  ⟨.extend (.nat 3) [("answer",.nat 42)], fun _ => none, {}⟩
theorem scalar_record_extend_refused : (check scalarExtend [] 8).isNone = true := by check_reduce


/-- Mix's generated reusable closure owns both captured operands. The previous
rule accepted this affine free binding despite ordinary lambda refusing it. -/
@[local simp] def extensionNaturalType : Ty :=
  .arrow .reusable .unrestricted .natural (.arrow .reusable .unrestricted .natural .natural)
@[local simp] def capturedMixSource : AnnotatedTerm :=
  ⟨.mix (.bound 0) (.lam (.lam (.bound 0))), fun position =>
    if position = [1] then some ⟨.natural,.arrow .reusable .unrestricted .natural .natural,.unrestricted,.reusable⟩
    else if position = [1,0] then some ⟨.natural,.natural,.unrestricted,.reusable⟩ else none, {}⟩
theorem affine_mix_capture_refused :
    (check capturedMixSource [⟨extensionNaturalType,.affine⟩] 16).isNone = true := by check_reduce

theorem reusable_mix_capture_accepted :
    (check capturedMixSource [⟨extensionNaturalType,.unrestricted⟩] 16).isSome = true := by check_reduce

@[local simp] def recursiveGlobalKnot : AnnotatedTerm :=
  ⟨.get (.fix (.lam (.lam (.record [("answer",.nat 42)]))) (.record [])) "answer",
    fun position =>
      if position = [0,0] then some ⟨.variable 0,
        .arrow .reusable .unrestricted .emptyRow (.variable 0),.unrestricted,.reusable⟩
      else if position = [0,0,0] then some ⟨.emptyRow,.variable 0,.unrestricted,.reusable⟩
      else none,
    ⟨[(0,.field "answer" .natural .emptyRow)],[0],[]⟩⟩
theorem recursive_global_knot_accepted : (check recursiveGlobalKnot [] 16).isSome = true := by check_reduce

@[local simp] def dishonestRecursiveCustody : AnnotatedTerm :=
  ⟨.nat 7, fun _ => none, ⟨[(0,.field "authority" (.custody 17) (.variable 0))],[0],[]⟩⟩
theorem recursive_alias_does_not_hide_custody :
    (check dishonestRecursiveCustody [] 8).isNone = true := by check_reduce

@[local simp] def stringConjunction : AnnotatedTerm :=
  ⟨.binary .conjunction (.label "hello") (.label "world"), fun _ => none, {}⟩
theorem arbitrary_labels_are_not_booleans : (check stringConjunction [] 8).isNone = true := by check_reduce

@[local simp] def reservedStringConjunction : AnnotatedTerm :=
  ⟨.binary .conjunction (.label "true") (.label "false"), fun _ => none, {}⟩
theorem reserved_strings_are_not_booleans :
    (check reservedStringConjunction [] 8).isNone = true := by check_reduce
theorem reserved_string_has_string_type :
    (check ⟨.label "true", fun _ => none, {}⟩ [] 8).map (fun checked => checked.type) = some .label := by check_reduce
theorem explicit_boolean_has_boolean_type :
    (check ⟨.boolean true, fun _ => none, {}⟩ [] 8).map (fun checked => checked.type) = some .boolean := by check_reduce
theorem explicit_boolean_conjunction_accepted :
    (check ⟨.binary .conjunction (.boolean true) (.boolean false), fun _ => none, {}⟩ [] 8).isSome = true := by check_reduce


@[local simp] def independentlyAuthoredFamily : ExtensionFamilies :=
  ⟨.variable 1,
    .field "combine" (.arrow .reusable .unrestricted (.variable 0) (.variable 0)) .emptyRow,
    .field "answer" .natural (.variable 1)⟩

theorem independent_requirements_checked :
    (checkExtension futureRowSource [] 16 independentlyAuthoredFamily (.variable 0)).isSome = true := by check_reduce

@[local simp] def unmetFamily : ExtensionFamilies :=
  { independentlyAuthoredFamily with required := .field "absent" .natural .emptyRow }
theorem absent_future_requirement_refused :
    (checkExtension futureRowSource [] 16 unmetFamily (.variable 0)).isNone = true := by check_reduce


-- The sorting observations use concrete string order. Expose these literal
-- facts rather than exploring both branches of canonical row insertion.
@[local simp] theorem circle_lt_square : ("circle" : String) < "square" := by decide
@[local simp] theorem circle_lt_triangle : ("circle" : String) < "triangle" := by decide
@[local simp] theorem square_lt_triangle : ("square" : String) < "triangle" := by decide
@[local simp] theorem not_square_lt_circle : ¬ ("square" : String) < "circle" := by decide
@[local simp] theorem not_triangle_lt_circle : ¬ ("triangle" : String) < "circle" := by decide
@[local simp] theorem not_triangle_lt_square : ¬ ("triangle" : String) < "square" := by decide

/-- A closed two-label sum; arms checked against it in any source order. -/
@[local simp] def shapeRow : Ty := .field "circle" .natural (.field "square" .natural .emptyRow)
/-- A nonexistent arm cannot manufacture a payload for its continuation. -/
@[local simp ↓] theorem shape_triangle_lookup (fuel : Nat) :
    (Ty.field "circle" .natural (.field "square" .natural .emptyRow)).lookup
      [] fuel "triangle" = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel => cases fuel <;> rfl

@[local simp] def shapeInjection : LambdaAnnotation := ⟨.natural,.variant shapeRow,.unrestricted,.reusable⟩
@[local simp] def shapeCase (arms : List (String × Term)) (tag : String) : AnnotatedTerm :=
  ⟨.case (.inject tag (.nat 4)) arms, fun position => if position = [0] then some shapeInjection else none, {}⟩
@[local simp] def shapeArms : List (String × Term) := [("circle",.bound 0),("square",.binary .add (.bound 0) (.nat 1))]

theorem exhaustive_case_accepted :
    (check (shapeCase shapeArms "square") [] 16).map (fun checked => checked.type) = some .natural := by check_reduce
theorem reordered_arms_accepted :
    (check (shapeCase shapeArms.reverse "circle") [] 16).isSome = true := by decide +kernel
theorem missing_arm_refused :
    (check (shapeCase [("circle",.bound 0)] "circle") [] 16).isNone = true := by check_reduce
theorem extra_arm_refused :
    (check (shapeCase (shapeArms ++ [("triangle",.bound 0)]) "circle") [] 16).isNone = true := by
  decide +kernel
theorem undeclared_injection_refused :
    (check (shapeCase shapeArms "triangle") [] 16).isNone = true := by check_reduce
theorem unannotated_injection_refused :
    (check ⟨.inject "circle" (.nat 4), fun _ => none, {}⟩ [] 16).isNone = true := by check_reduce
theorem arm_results_must_agree :
    (check (shapeCase [("circle",.bound 0),("square",.label "four")] "circle") [] 16).isNone = true := by check_reduce

/-- Natural equality drives a Boolean branch; a label is not a condition. -/
theorem equality_branch_accepted :
    (check ⟨.ifBool (.binary .equal (.nat 2) (.nat 2)) (.label "same") (.label "different"),
      fun _ => none, {}⟩ [] 16).map (fun checked => checked.type) = some .label := by check_reduce
theorem label_condition_refused :
    (check ⟨.ifBool (.label "true") (.nat 1) (.nat 0), fun _ => none, {}⟩ [] 16).isNone = true := by check_reduce
theorem label_equality_accepted :
    (check ⟨.binary .labelEqual (.label "a") (.label "b"), fun _ => none, {}⟩ [] 8).map
      (fun checked => checked.type) = some .boolean := by check_reduce
theorem boolean_label_equality_refused :
    (check ⟨.binary .labelEqual (.boolean true) (.boolean true), fun _ => none, {}⟩ [] 8).isNone = true := by check_reduce

/-- Truncated subtraction, floor division and remainder are Nat-to-Nat; the order primitives are
Nat-to-Bool and drive a Boolean branch; none takes a label or a Boolean operand. -/
theorem nat_primitive_types :
    ∀ primitive, primitive = .subtract ∨ primitive = .divide ∨ primitive = .modulo →
      (check ⟨.binary primitive (.nat 9) (.nat 4), fun _ => none, {}⟩ [] 8).map
        (fun checked => checked.type) = some .natural := by
  intro primitive choice; rcases choice with rfl | rfl | rfl <;> check_reduce
theorem order_primitive_branch_accepted :
    ∀ primitive, primitive = .less ∨ primitive = .lessEqual →
      (check ⟨.ifBool (.binary primitive (.nat 3) (.nat 4)) (.label "below") (.label "above"),
        fun _ => none, {}⟩ [] 16).map (fun checked => checked.type) = some .label := by
  intro primitive choice; rcases choice with rfl | rfl <;> check_reduce
theorem nat_primitive_label_operand_refused :
    ∀ primitive, primitive = .subtract ∨ primitive = .divide ∨ primitive = .less ∨ primitive = .lessEqual ∨
      primitive = .modulo →
      (check ⟨.binary primitive (.label "9") (.nat 4), fun _ => none, {}⟩ [] 8).isNone = true ∧
      (check ⟨.binary primitive (.nat 9) (.boolean true), fun _ => none, {}⟩ [] 8).isNone = true := by
  intro primitive choice; rcases choice with rfl | rfl | rfl | rfl | rfl <;> check_reduce

/-- An affine binding used in two arms is used once on each path: arms join by maximum
(`joinUses`, 2026-11-01; until then arms added and this was refused). -/
theorem affine_in_two_arms_accepted :
    (check ⟨.case (.inject "circle" (.nat 4)) [("circle",.bound 1),("square",.bound 1)],
      fun position => if position = [0] then some shapeInjection else none, {}⟩
      [⟨.natural,.affine⟩] 16).isSome = true := by check_reduce
/-- Arms still add with the scrutinee: an affine binding used by the scrutinee and an arm is refused. -/
theorem affine_in_scrutinee_and_arm_refused :
    (check ⟨.case (.inject "circle" (.bound 0)) [("circle",.bound 1),("square",.nat 0)],
      fun position => if position = [0] then some shapeInjection else none, {}⟩
      [⟨.natural,.affine⟩] 16).isNone = true := by check_reduce
theorem affine_in_one_arm_accepted :
    (check ⟨.case (.inject "circle" (.nat 4)) [("circle",.bound 1),("square",.nat 0)],
      fun position => if position = [0] then some shapeInjection else none, {}⟩
      [⟨.natural,.affine⟩] 16).isSome = true := by check_reduce

/-! ## A recursive sum is injected at its declared bounded variable

`Sums.obend`'s `total` builds `List.cons({head, tail: List.cons(..)})`. The
recursive sum `List` is the bounded variable 0 (bound: the variant row, whose
`tail` member is variable 0); an injection's codomain is that variable, so the
nested payload `tail` agrees with its declared member (cv 01a10564-84a1: the
checker refused this before the injection rule carried the variable codomain,
W3.EVENTS 6b2616db; refused/accepted logs in the W25 evidence). -/

@[local simp] def listRow : Ty :=
  .field "nil" .emptyRow (.field "cons" (.field "head" .natural (.field "tail" (.variable 0) .emptyRow)) .emptyRow)
@[local simp] def listAssumptions : Assumptions := ⟨[(0, .variant listRow)], [0], []⟩
@[local simp] def listAnnotations : Annotations := fun position =>
  if position = [] then
    some ⟨.field "head" .natural (.field "tail" (.variable 0) .emptyRow), .variable 0, .unrestricted, .reusable⟩
  else if position = [0,1] then some ⟨.emptyRow, .variable 0, .unrestricted, .reusable⟩
  else none
@[local simp] def listCons (tail : Term) : AnnotatedTerm :=
  ⟨.inject "cons" (.record [("head", .nat 1), ("tail", tail)]), listAnnotations, listAssumptions⟩

theorem recursive_sum_list_accepted :
    (check (listCons (.inject "nil" (.record []))) [] 32).map (fun checked => checked.type) = some (.variable 0) := by
  check_reduce
/-- Planted ill-typed control: a Nat where the recursive tail belongs. -/
theorem recursive_sum_ill_typed_tail_refused :
    (check (listCons (.nat 3)) [] 32).isNone = true := by check_reduce

/-! ## Canonical shadowing must not manufacture shareability

AUDIT (W25, cv 01a10505-46cf). `Ty.canonical` forgets a shadowed member, so
`{a: Nat, a: custody}` agrees with `{a: Nat}` although only the second is
shareable. Before this change the checker ACCEPTED `shadowProgram (.bound 0)` in
a context holding a linear custody: the custody is built into the second `a` of
a record that is injected at the declared shareable row `{a: Nat}`, and the
arm binds that payload unrestricted. So the judgement labelled a value that
carries a custody (or a once closure) shareable: hole = YES at the type level.
What it did not do: the machine's field lookup is first-match, so the hidden
member is unreachable by `get`/`case`; no program could duplicate the custody
itself. The defect was a mislabelled type that every shareability rule trusts.
Conversions the checker inserts now go through `agree`, which refuses to
manufacture shareability (`shadowed_*_refused` below). -/

@[local simp] def shadowRow : Ty := .field "a" .natural .emptyRow
@[local simp] def shadowSum : Ty := .variant (.field "l" shadowRow .emptyRow)

/-- `case (inject l {a = 1, a = <hidden>}) of l(p) => p.a + p.a`, the payload
declared at the shareable row `{a: Nat}`. -/
@[local simp] def shadowProgram (hidden : Term) (hiddenAnnotation : Annotations) : AnnotatedTerm :=
  ⟨.case (.inject "l" (.record [("a", .nat 1), ("a", hidden)]))
      [("l", .binary .add (.get (.bound 0) "a") (.get (.bound 0) "a"))],
   fun position => if position = [0] then some ⟨shadowRow, shadowSum, .unrestricted, .reusable⟩
     else hiddenAnnotation position, {}⟩

/-- The gap `agree` closed is now closed in the relation itself: canonical form keeps a
non-shareable shadowed member, so the hidden custody row no longer agrees with the
shareable one at all (`Ty.shareableUnder_canonical`), and `agree` still refuses. -/
theorem canonical_agreement_keeps_shareability :
    sameType {} (.field "a" .natural (.field "a" (.custody 17) .emptyRow)) shadowRow = false ∧
    (Ty.field "a" .natural (.field "a" (.custody 17) .emptyRow)).shareable = false ∧
    shadowRow.shareable = true ∧
    agree {} (.field "a" .natural (.field "a" (.custody 17) .emptyRow)) shadowRow = false := by check_reduce

/-- REFUSED (was accepted): a linear custody hidden behind a shadowing field. -/
theorem shadowed_custody_laundering_refused :
    (check (shadowProgram (.bound 0) (fun _ => none)) [⟨.custody 17,.linear⟩] 32).isNone = true := by check_reduce

/-- REFUSED (was accepted): a once closure hidden behind a shadowing field. -/
theorem shadowed_once_closure_laundering_refused :
    (check (shadowProgram (.lam (.bound 0))
      (fun position => if position = [0,0,1] then some ⟨.natural,.natural,.unrestricted,.once⟩ else none))
      [] 32).isNone = true := by check_reduce

/-- Control: the same program with a shareable hidden member is accepted. -/
theorem shadowed_shareable_member_accepted :
    (check (shadowProgram (.bound 0) (fun _ => none)) [⟨.natural,.linear⟩] 32).map
      (fun checked => checked.type) = some .natural := by check_reduce

/-- Control: overriding a field through `extend` (the shadowing's purpose) still
agrees at the shareable row. -/
theorem shadowed_override_accepted :
    (check ⟨.case (.inject "l" (.extend (.record [("a", .nat 0)]) [("a", .nat 1)]))
      [("l", .binary .add (.get (.bound 0) "a") (.get (.bound 0) "a"))],
      fun position => if position = [0] then some ⟨shadowRow, shadowSum, .unrestricted, .reusable⟩ else none, {}⟩
      [] 32).map (fun checked => checked.type) = some .natural := by check_reduce

/-- The classification on this module's own refused fixtures, each also refused
by `check` above: an affine binding used twice is ownership, an accepted
program given too little fuel is the budget, a conjunction of labels is typing,
and capturing custody in a reusable closure is typing (relaxing quantities
cannot make custody shareable). -/
theorem refusal_kind_duplicate_affine :
    refusalKind ⟨duplicateAffine, [⟨.natural,.affine⟩], 8⟩ = .ownership := by check_reduce
theorem refusal_kind_starved_fuel :
    (check (custodyCapture .once) [⟨.custody 17,.linear⟩] 1).isNone = true ∧
      refusalKind ⟨custodyCapture .once, [⟨.custody 17,.linear⟩], 1⟩ = .budget := by check_reduce
theorem refusal_kind_label_conjunction :
    refusalKind ⟨stringConjunction, [], 8⟩ = .typing := by check_reduce
theorem refusal_kind_custody_in_reusable_closure :
    refusalKind ⟨custodyCapture .reusable, [⟨.custody 17,.linear⟩], 8⟩ = .typing := by check_reduce

/-! ## Activities: effects as a type, never in a shared position -/

@[local simp] def writeAction : LambdaAnnotation := ⟨.field "after" .natural .emptyRow,planType,.unrestricted,.reusable⟩
@[local simp] def effectSignature : LambdaAnnotation := ⟨planType,responseType,.unrestricted,.reusable⟩
@[local simp] def writePlan : Term := .inject "write" (.record [("after",.nat 1)])
/-- Annotations for a perform at `site` (its plan injection one level down). -/
@[local simp] def performAt (site : List Nat) (rest : Annotations) : Annotations := fun position =>
  if position = site then some effectSignature else if position = site ++ [0] then some writeAction
  else rest position
@[local simp] def writeActivity (written refused : Term) : Term :=
  .case (.perform writePlan) [("written",written),("refused",refused)]
@[local simp] def armsDone : Annotations := fun position =>
  if position = [1,0] ∨ position = [1,1] then some effectSignature else none

/-- Perform a write, resume with its outcome, select the arm: an activity. -/
theorem effect_case_accepted :
    (check ⟨writeActivity (.done (.nat 1)) (.done (.nat 0)),performAt [0] armsDone,{}⟩ [] 32).map
      (fun checked => checked.type) = some (.computation planType responseType .natural) := by check_reduce
/-- Every arm of an effect case is an activity; a pure arm needs `done`. -/
theorem pure_arm_without_done_refused :
    (check ⟨writeActivity (.nat 1) (.nat 0),performAt [0] armsDone,{}⟩ [] 32).isNone = true := by check_reduce
/-- Rule effect-as-argument: an argument is a shared thunk, so an activity is
refused there even for an affine (non-shareable) parameter... -/
theorem effect_as_argument_refused :
    (check ⟨.app (.lam (.nat 0)) (.perform writePlan),
      performAt [1] (fun position => if position = [0] then
        some ⟨.computation planType responseType responseType,.natural,.affine,.reusable⟩ else none),{}⟩ [] 32).isNone = true := by check_reduce
/-- ...while the same affine parameter accepts a pure argument. -/
theorem pure_affine_argument_accepted :
    (check ⟨.app (.lam (.nat 0)) (.nat 3),
      fun position => if position = [0] then some ⟨.natural,.natural,.affine,.reusable⟩ else none,{}⟩ [] 32).map
      (fun checked => checked.type) = some .natural := by check_reduce
/-- Rule effect-in-field: a record field is a shared cell. -/
theorem effect_in_record_field_refused :
    (check ⟨.record [("next",.perform writePlan)],performAt [0] (fun _ => none),{}⟩ [] 32).isNone = true := by check_reduce
/-- Rule effect-in-payload: a sum payload is a shared cell. -/
theorem effect_in_payload_refused :
    (check ⟨.inject "later" (.perform writePlan),
      performAt [0] (fun position => if position = [] then
        some ⟨.computation planType responseType responseType,
          .variant (.field "later" (.computation planType responseType responseType) .emptyRow),
          .unrestricted,.reusable⟩ else none),{}⟩ [] 32).isNone = true := by check_reduce
/-- Rule effect-in-specification: specification components are shared cells. -/
theorem effect_in_specification_refused :
    (check ⟨.specification (.perform writePlan) (.nat 0),performAt [0] (fun _ => none),{}⟩ [] 32).isNone = true := by check_reduce
/-- Rule plan-is-a-sum: a perform's plan is a sum of first-order actions. -/
theorem scalar_plan_refused :
    (check ⟨.perform (.nat 1),fun position => if position = [] then
      some ⟨.natural,responseType,.unrestricted,.reusable⟩ else none,{}⟩ [] 32).isNone = true := by check_reduce
/-- Rule response-is-data: a closure cannot be a response. -/
theorem closure_response_refused :
    (check ⟨.perform writePlan,fun position =>
      if position = [] then some ⟨planType,.arrow .reusable .unrestricted .natural .natural,.unrestricted,.reusable⟩
      else if position = [0] then some writeAction else none,{}⟩ [] 32).isNone = true := by check_reduce

/-! ### Agreement is the equivalence closure of one-step agreement (2026-10-30) -/

@[local simp] def siblingAliases : Assumptions := ⟨[(1, .natural), (2, .natural)], [], []⟩

/-- Two aliases of the same type: no single step relates them, the closure does. -/
theorem sibling_aliases_agree :
    sameStep siblingAliases (.variable 1) (.variable 2) = false ∧
    sameType siblingAliases (.variable 1) (.variable 2) = true := by check_reduce

/-- The historical head-chain agreement did not descend into constructors. -/
theorem agreement_does_not_descend :
    legacySameType siblingAliases (.arrow .reusable .unrestricted (.variable 1) .boolean)
      (.arrow .reusable .unrestricted .natural .boolean) = false := by check_reduce

/-- Recursive agreement follows aliases below matching constructors. -/
theorem agreement_descends_into_constructors :
    sameType siblingAliases (.arrow .reusable .unrestricted (.variable 1) .boolean)
      (.arrow .reusable .unrestricted .natural .boolean) = true := by check_reduce

/-- A rigid variable is nominal: never its bound, never a sibling alias of that bound. -/
theorem rigid_variable_nominal :
    sameType ⟨[(1, .natural), (2, .natural)], [], [1]⟩ (.variable 1) .natural = false ∧
    sameType ⟨[(1, .natural), (2, .natural)], [], [1]⟩ (.variable 1) (.variable 2) = false := by check_reduce

/-- A cycle of bare aliases agrees within itself and with nothing else; the walk stops. -/
theorem cyclic_aliases_close :
    sameType ⟨[(1, .variable 2), (2, .variable 1)], [], []⟩ (.variable 1) (.variable 2) = true ∧
    sameType ⟨[(1, .variable 2), (2, .variable 1)], [], []⟩ (.variable 1) .natural = false := by check_reduce

/-- The visited-set walk refuses a cycle of bounds and finds what fuel finds elsewhere. -/
theorem visited_walk_cycle :
    lookupV [(1, .variable 2), (2, .variable 1)] [] (.variable 1) "x" = none ∧
    isRowV [(1, .variable 2), (2, .variable 1)] [] (.variable 1) = false ∧
    lookupV [(1, .field "x" .natural (.variable 1))] [] (.variable 1) "x" = some .natural := by check_reduce

end Obend.Core.Proofs.CheckTeeth
end
