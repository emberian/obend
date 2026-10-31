module
/- Activities in the typed graph; lookups and head normalization under agreement. -/
public import Obend.Core.MachineTyping
public import Obend.Core.RuntimeOrigins
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.TypeGraphHead
public import Obend.Core.Proofs.Adequacy.Defs
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Preservation.Base.Weaken
namespace Obend.Core.Proofs.Preservation
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine Obend.Core.MachineTyping
set_option autoImplicit false

/-! ## Activities in the typed graph -/

/-- No heap cell is an activity (CellTyping carries it). -/
public theorem heap_type_pure {assumptions : Assumptions} {types : AddressTypes} {heap : Array Cell}
    (heapTyped : HeapTyping assumptions types heap) {address : Address} {type : Ty}
    (assigned : types[address]? = some type) : type.isComputation = false := by
  obtain ⟨cell,_,cellTyped⟩ := heapTyped.cell address type assigned
  obend_cases cellTyped with []

public theorem conversionPath_isComputation {assumptions : Assumptions} {first last : Ty}
    (path : ConversionPath assumptions first last) : first.isComputation = last.isComputation := by
  induction path with
  | refl => rfl
  | step prior agreement ih => exact ih.trans (sameType_isComputation agreement)

public theorem lookup_not_computation (bounds : Bounds) (fuel : Nat) (row : Ty) (name : String) (member : Ty)
    (lookup : row.lookup bounds fuel name = some member) : row.isComputation = false := by
  cases fuel <;> obend_cases row with [Ty.lookup,Ty.isComputation]

public theorem isRow_not_computation (bounds : Bounds) (fuel : Nat) (row : Ty)
    (isRow : row.isRow bounds fuel = true) : row.isComputation = false := by
  cases fuel <;> obend_cases row with [Ty.isRow,Ty.isComputation]

public theorem callable_arrow_not_computation {type : Ty} {reuse : Reuse} {quantity : Quantity} {domain codomain : Ty}
    (callable : callable type = .arrow reuse quantity domain codomain) : type.isComputation = false := by
  obend_cases type with [Obend.Core.Check.callable,Ty.isComputation]

theorem sameStep_activity_canonical {assumptions : Assumptions} {actual expected plan response produced : Ty}
    (agreement : sameStep assumptions actual expected = true)
    (equal : actual.canonical = (Ty.computation plan response produced).canonical) :
    expected.canonical = (Ty.computation plan response produced).canonical := by
  have activity : actual.isComputation = true := by
    rw [← Ty.canonical_isComputation,equal]; rfl
  simp only [sameStep,Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasActual) | aliasExpected
  · rw [← equal]; exact (by simpa using canonical : actual.canonical = expected.canonical).symm
  · cases actual <;> simp_all [Ty.isComputation]
  · cases expected <;> simp at aliasExpected
    simp_all [Ty.isComputation]

public theorem legacy_sameType_activity_canonical {assumptions : Assumptions} {actual expected plan response produced : Ty}
    (agreement : legacySameType assumptions actual expected = true)
    (equal : actual.canonical = (Ty.computation plan response produced).canonical) :
    expected.canonical = (Ty.computation plan response produced).canonical :=
  legacySameType_lift (fun a e => a.canonical = (Ty.computation plan response produced).canonical →
      e.canonical = (Ty.computation plan response produced).canonical)
    (fun _ h => h) (fun one two h => two (one h)) (fun step h => sameStep_activity_canonical step h)
    agreement equal

public theorem argumentAllowed_not_computation {assumptions : Assumptions} {quantity : Quantity}
    {context : Context} {type : Ty} {uses : Uses}
    (allowed : argumentAllowed assumptions quantity context type uses = true) : type.isComputation = false := by
  simp only [argumentAllowed,Bool.and_eq_true] at allowed
  simpa using allowed.1.1

/-- An activity-typed continuation begins with an effect case: no other frame,
and in particular no update frame (a shared cell being forced), accepts one. -/
public theorem stack_activity_head {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty}
    (typed : StackTyping assumptions types stack input result) :
    input.isComputation = true →
    ∀ frame rest, stack = frame :: rest → ∃ arms environment, frame = .case arms environment := by
  induction typed with
  | nil => intro _ frame rest impossible; simp at impossible
  | cons frameTyped restTyped ih =>
      intro activity frame rest same
      cases same
      cases frameTyped with
      | argument argument callable copy =>
          simp [callable_arrow_not_computation callable] at activity
      | update assigned pure => simp_all
      | field lookup => simp [lookup_not_computation _ _ _ _ _ lookup] at activity
      | extend _ _ _ _ isRow => simp [isRow_not_computation _ _ _ isRow] at activity
      | binaryLeft right => rename_i primitive _ _; cases primitive <;> simp_all [primitiveTypes,Ty.isComputation]
      | binaryRight left => rename_i primitive _; cases primitive <;> simp_all [primitiveTypes,Ty.isComputation]
      | effectCase => exact ⟨_,_,rfl⟩
      | case => exact ⟨_,_,rfl⟩
      | _ => simp_all [Ty.isComputation]
  | conversion agreement restTyped ih =>
      intro activity; exact ih ((sameType_isComputation agreement) ▸ activity)
  | returns pure restTyped ih => intro activity; simp_all

public theorem computation_canonical_inj {plan response result plan' response' result' : Ty}
    (equal : (Ty.computation plan response result).canonical = (Ty.computation plan' response' result').canonical) :
    plan.canonical = plan'.canonical ∧ response.canonical = response'.canonical ∧ result.canonical = result'.canonical := by
  simp only [Ty.canonical,Ty.computation.injEq] at equal
  exact equal

/-- Inversion of an activity continuation at an effect case: the arms are
activities over the case's own Plan/Response, and the incoming activity
produces the case's sum. -/

public theorem heap_typed_set {assumptions : Assumptions} {types : AddressTypes}
    {heap : Array Cell} {address : Address} {type : Ty} {replacement : Cell}
    (heapTyped : HeapTyping assumptions types heap) (assigned : types[address]? = some type)
    (replacementTyped : CellTyping assumptions types replacement type) :
    HeapTyping assumptions types (heap.set! address replacement) := by
  have bound : address < heap.size := by
    rw [← heapTyped.length]
    exact (List.getElem?_eq_some_iff.mp assigned).1
  refine ⟨by simpa [Array.set!] using heapTyped.length, ?_⟩
  intro index indexType indexAssigned
  by_cases same : index = address
  · subst index
    have equality : indexType = type := Option.some.inj (indexAssigned.symm.trans assigned)
    subst indexType
    exact ⟨replacement,by simp [Array.set!,Array.setIfInBounds,bound],replacementTyped⟩
  · obtain ⟨prior,found,typed⟩ := heapTyped.cell index indexType indexAssigned
    exact ⟨prior,by simpa [Array.set!,Array.setIfInBounds,bound,same,Ne.symm same] using found,typed⟩

/-- Pushing a typed thunk/cached predecessor extends the type assignment once;
all old origins, cached values, captures and frame addresses remain typed. -/
public theorem heap_typed_push {assumptions : Assumptions} {types : AddressTypes}
    {heap : Array Cell} {cell : Cell} {type : Ty}
    (heapTyped : HeapTyping assumptions types heap)
    (cellTyped : CellTyping assumptions (types ++ [type]) cell type) :
    HeapTyping assumptions (types ++ [type]) (heap.push cell) := by
  refine ⟨by simp [heapTyped.length], ?_⟩
  intro address assignedType assigned
  by_cases prior : address < types.length
  · have oldAssigned : types[address]? = some assignedType := by
      simpa [List.getElem?_append,prior] using assigned
    obtain ⟨stored,found,typed⟩ := heapTyped.cell address assignedType oldAssigned
    refine ⟨stored,?_,CellTyping.weaken (type_extension_append types [type]) typed⟩
    simpa only [Array.getElem?_push,← heapTyped.length,if_neg (Nat.ne_of_lt prior)] using found
  · have bound : address < types.length + 1 := by
      simpa using (List.getElem?_eq_some_iff.mp assigned).1
    have same : address = types.length := Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt prior)
    subst address
    have equality : assignedType = type := by simpa [List.getElem?_append] using assigned.symm
    subst assignedType
    exact ⟨cell,by rw [heapTyped.length]; exact Array.getElem?_push_size,cellTyped⟩

/-- A typed control cannot already be a semantic/internal refusal. -/
public theorem typed_control_not_refused {assumptions : Assumptions} {types : AddressTypes}
    {control : Control} {type : Ty} (typed : ControlTyping assumptions types control type)
    (reason : Refusal) : control ≠ .refused reason := by
  obend_cases typed with []

/-- Independently qualified graph invariants preserve invalid-update exclusion
for EVERY stepRaw branch. This independent local lemma uses only busy-update
invariants; the all-constructor typing theorem below covers operand refusals. -/
theorem typed_step_no_invalidUpdate {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result) :
    (stepRaw state).control ≠ .refused .invalidUpdate :=
  Obend.Core.Invariant.stepRaw_no_invalidUpdate typed.busy
    (typed_control_not_refused typed.control .invalidUpdate)

/-- The independent graph invariants accompany any locally proved typed raw
transition, without an additional scope or update-stack premise. -/
@[expose] public def step_certificate {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result)
    (current : Ty) (heap : HeapTyping assumptions types (stepRaw state).heap)
    (control : ControlTyping assumptions types (stepRaw state).control current)
    (stack : StackTyping assumptions types (stepRaw state).stack current result) :
    StateTyping assumptions types (stepRaw state) result :=
  ⟨current,heap,control,stack,typed.assumptionsValid,
    Obend.Core.Invariant.stepRaw_lexicalInvariant typed.lexical,
    Obend.Core.Invariant.stepRaw_busyInvariant typed.busy,
    Obend.Core.Invariant.stepRaw_finalStackInvariant typed.terminalStack⟩

/-- Allocating transitions use a genuinely extended assignment; all imported
representation invariants continue over the same raw executor step. -/
@[expose] public def step_alloc_certificate {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result)
    (after : AddressTypes) (current : Ty)
    (heap : HeapTyping assumptions after (stepRaw state).heap)
    (control : ControlTyping assumptions after (stepRaw state).control current)
    (stack : StackTyping assumptions after (stepRaw state).stack current result) :
    StateTyping assumptions after (stepRaw state) result :=
  ⟨current,heap,control,stack,typed.assumptionsValid,
    Obend.Core.Invariant.stepRaw_lexicalInvariant typed.lexical,
    Obend.Core.Invariant.stepRaw_busyInvariant typed.busy,
    Obend.Core.Invariant.stepRaw_finalStackInvariant typed.terminalStack⟩

/-- Lookup of the explicit finite row prefix preserves first-field shadowing.
Rigid/recursive tails stay opaque here; this theorem makes no alias-unfolding
or arbitrary future-field assertion. -/
@[expose] public def finiteLookup : Ty → String → Option Ty
  | .field name member tail, query =>
      if name = query then some member else finiteLookup tail query
  | _, _ => none

theorem insert_canonical_lookup (row : Ty) (name query : String) (member : Ty) :
    finiteLookup (row.insertCanonical name member) query =
      if name = query then some member else finiteLookup row query := by
  induction row with
  | field prior old tail oldIH tailIH =>
      by_cases equal : name = prior
      · subst prior
        by_cases hit : name = query <;> by_cases sh : old.shareable = true <;>
          simp [Ty.insertCanonical,finiteLookup,hit,sh]
      · by_cases before : name < prior
        · simp only [Ty.insertCanonical,if_neg equal,if_pos before]
          by_cases hit : name = query
          <;> by_cases priorHit : prior = query
          <;> simp_all [finiteLookup]
        · simp only [Ty.insertCanonical,if_neg equal,if_neg before]
          by_cases hit : name = query
          <;> by_cases priorHit : prior = query
          <;> simp_all [finiteLookup]
  | _ => rfl

/-- The SAME canonicalizer used by the executable checker preserves every
visible member modulo recursively canonical member types, at arbitrary row
length and duplicate shadowing. It preserves the opaque tail by construction. -/
public theorem canonical_lookup (row : Ty) (query : String) :
    finiteLookup row.canonical query = (finiteLookup row query).map Ty.canonical := by
  induction row with
  | field name member tail memberIH tailIH =>
      simp only [Ty.canonical,insert_canonical_lookup,finiteLookup]
      split <;> simp_all
  | _ => rfl

/-- Finite named-row comparison cannot change a visible member's canonical
meaning. This is a general canonical-equality law, not a closed fixture test. -/
theorem canonical_row_lookup_agreement (first second : Ty) (query : String)
    (agreement : first.canonical = second.canonical) :
    (finiteLookup first query).map Ty.canonical = (finiteLookup second query).map Ty.canonical := by
  rw [← canonical_lookup,← canonical_lookup,agreement]

theorem safe_quantity_add_left (quantity : Quantity) (first second : Nat)
    (safe : safeQuantity quantity (first + second) = true) :
    safeQuantity quantity first = true := by
  obend_cases quantity with [safeQuantity]

public theorem safe_add_uses_left (context : Context) (first second : Uses)
    (firstLength : first.length = context.length) (secondLength : second.length = context.length)
    (safe : safeUses context (addUses first second) = true) : safeUses context first = true := by
  induction context generalizing first second with
  | nil =>
      cases first with
      | nil => rfl
      | cons head tail => simp at firstLength
  | cons binding context ih =>
      cases first with
      | nil => simp at firstLength
      | cons first firsts =>
        cases second with
        | nil => simp at secondLength
        | cons second seconds =>
          have fl : firsts.length = context.length := Nat.succ.inj firstLength
          have sl : seconds.length = context.length := Nat.succ.inj secondLength
          have decomposed : safeQuantity binding.quantity (first+second) = true ∧
              safeUses context (addUses firsts seconds) = true := by
            simpa [safeUses,addUses,List.zipWith,List.zip,List.all_cons,fl,sl] using safe
          have head := safe_quantity_add_left binding.quantity first second decomposed.1
          have tail := ih firsts seconds fl sl decomposed.2
          simpa [safeUses,List.zip,List.all_cons,fl,head] using tail

@[expose] public def isVariable : Ty → Bool
  | .variable _ => true
  | _ => false

theorem insert_canonical_not_variable (row : Ty) (name : String) (member : Ty) :
    isVariable (row.insertCanonical name member) = false := by
  cases row <;> simp only [Ty.insertCanonical]
  all_goals repeat' first | split
  all_goals rfl

theorem canonical_is_variable (type : Ty) : isVariable type.canonical = isVariable type := by
  obend_cases type with [Ty.canonical,insert_canonical_not_variable]
  all_goals rfl

theorem canonical_variable_inverse {type : Ty} {index : Nat}
    (equal : type.canonical = .variable index) : type = .variable index := by
  have isVar : isVariable type = true := by rw [← canonical_is_variable,equal]; rfl
  cases type <;> simp [isVariable] at isVar
  simpa [Ty.canonical] using equal

theorem insert_canonical_tail (row : Ty) (name : String) (member : Ty) :
    (row.insertCanonical name member).tail = row.tail := by
  induction row with
  | field prior old tail oldIH tailIH =>
      simp only [Ty.insertCanonical]
      split
      · split <;> rfl
      · split <;> simp_all [Ty.tail]
  | _ => rfl

theorem canonical_tail (row : Ty) : row.canonical.tail = row.tail.canonical := by
  obend_cases induction row with [Ty.canonical,Ty.tail,insert_canonical_tail]

/-- A successful finite lookup either uses the explicit prefix or discloses
its precise unknown tail alias and the already-bounded lookup into that alias.
Cycles are permitted; the theorem never asks an alias to terminate. -/
public theorem lookup_prefix_or_alias (bounds : Bounds) (fuel : Nat) (row : Ty)
    (name : String) (member : Ty) (lookup : row.lookup bounds fuel name = some member) :
    finiteLookup row name = some member ∨
      (finiteLookup row name = none ∧ ∃ index bound depth,
        row.tail = .variable index ∧ bounds.lookup index = some bound ∧ bound.lookup bounds depth name = some member) := by
  induction fuel generalizing row with
  | zero => simp [Ty.lookup] at lookup
  | succ fuel ih =>
      cases row with
      | field prior type tail =>
          by_cases hit : prior = name
          · left; simpa [Ty.lookup,finiteLookup,hit] using lookup
          · have next : tail.lookup bounds fuel name = some member := by simpa [Ty.lookup,hit] using lookup
            rcases ih tail next with visible | ⟨absent,index,bound,depth,tailEq,found,next⟩
            · exact Or.inl (by simpa [finiteLookup,hit] using visible)
            · exact Or.inr ⟨by simpa [finiteLookup,hit] using absent,index,bound,depth,tailEq,found,next⟩
      | «variable» index =>
          cases found : bounds.lookup index with
          | none => simp [Ty.lookup,found] at lookup
          | some bound =>
            exact Or.inr ⟨rfl,index,bound,fuel,rfl,found,by simpa [Ty.lookup,found] using lookup⟩
      | _ => simp [Ty.lookup] at lookup

theorem finite_lookup_realizes (bounds : Bounds) (row : Ty) (name : String) (member : Ty)
    (visible : finiteLookup row name = some member) :
    ∃ fuel, row.lookup bounds fuel name = some member := by
  induction row with
  | field prior type tail typeIH tailIH =>
      by_cases hit : prior = name
      · exact ⟨1,by simpa [finiteLookup,Ty.lookup,hit] using visible⟩
      · obtain ⟨fuel,lookup⟩ := tailIH (by simpa [finiteLookup,hit] using visible)
        exact ⟨fuel+1,by simpa [Ty.lookup,hit] using lookup⟩
  | _ => simp [finiteLookup] at visible

theorem alias_tail_lookup_realizes (bounds : Bounds) (row : Ty) (name : String) (member : Ty)
    (absent : finiteLookup row name = none) (index : Nat) (bound : Ty) (depth : Nat)
    (tail : row.tail = .variable index) (found : bounds.lookup index = some bound)
    (lookup : bound.lookup bounds depth name = some member) :
    ∃ fuel, row.lookup bounds fuel name = some member := by
  induction row with
  | field prior type rest typeIH restIH =>
      have hit : prior ≠ name := by intro same; simp [finiteLookup,same] at absent
      obtain ⟨fuel,next⟩ := restIH (by simpa [finiteLookup,hit] using absent) tail
      exact ⟨fuel+1,by simpa [Ty.lookup,hit] using next⟩
  | «variable» prior =>
      have same : prior = index := by simpa [Ty.tail] using tail
      subst prior
      exact ⟨depth+1,by simpa [Ty.lookup,found] using lookup⟩
  | _ => simp [Ty.tail] at tail

/-- The checker's finite row equality transports every actual bounded lookup,
including a disclosed recursive tail. Address member types retain a concrete
canonical-equality proof; unknown members are never fabricated. -/
public theorem canonical_lookup_transport (bounds : Bounds) (actual expected : Ty)
    (agreement : actual.canonical = expected.canonical) (fuel : Nat) (name : String) (member : Ty)
    (lookup : expected.lookup bounds fuel name = some member) :
    ∃ depth actualMember, actual.lookup bounds depth name = some actualMember ∧
      actualMember.canonical = member.canonical := by
  have prefixes := canonical_row_lookup_agreement actual expected name agreement
  rcases lookup_prefix_or_alias bounds fuel expected name member lookup with visible | ⟨absent,index,bound,depth,tail,found,next⟩
  · rw [visible] at prefixes
    cases actualPrefix : finiteLookup actual name with
    | none => simp [actualPrefix] at prefixes
    | some actualMember =>
      obtain ⟨depth,actualLookup⟩ := finite_lookup_realizes bounds actual name actualMember actualPrefix
      exact ⟨depth,actualMember,actualLookup,by simpa [actualPrefix] using prefixes⟩
  · have actualAbsent : finiteLookup actual name = none := by
      rw [absent] at prefixes
      cases actualPrefix : finiteLookup actual name <;> simp_all
    have tails : actual.tail.canonical = expected.tail.canonical := by
      simpa only [canonical_tail] using congrArg Ty.tail agreement
    have actualTail : actual.tail = .variable index :=
      canonical_variable_inverse (by simpa [tail,Ty.canonical] using tails)
    obtain ⟨fuel,actualLookup⟩ := alias_tail_lookup_realizes bounds actual name member actualAbsent index bound depth actualTail found next
    exact ⟨fuel,member,actualLookup,rfl⟩

theorem same_step_lookup_transport {assumptions : Assumptions} {actual expected : Ty}
    (agreement : sameStep assumptions actual expected = true) (fuel : Nat) (name : String) (member : Ty)
    (lookup : expected.lookup assumptions.bounds fuel name = some member) :
    ∃ depth actualMember, actual.lookup assumptions.bounds depth name = some actualMember ∧
      actualMember.canonical = member.canonical := by
  simp only [sameStep,Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasActual) | aliasExpected
  · exact canonical_lookup_transport assumptions.bounds actual expected (by simpa using canonical) fuel name member lookup
  · cases actual <;> simp at aliasActual
    rename_i index
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at aliasActual
    | some bound =>
      have found := Assumptions.alias_bound aliased
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = expected.canonical := by simpa [aliased] using aliasActual
      obtain ⟨depth,actualMember,actualLookup,memberEq⟩ := canonical_lookup_transport assumptions.bounds bound expected equal fuel name member lookup
      exact ⟨depth+1,actualMember,by simpa [Ty.lookup,found] using actualLookup,memberEq⟩
  · cases expected <;> simp at aliasExpected
    rename_i index
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at aliasExpected
    | some bound =>
      have found := Assumptions.alias_bound aliased
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = actual.canonical := by simpa [aliased] using aliasExpected
      cases fuel with
      | zero => simp [Ty.lookup] at lookup
      | succ fuel =>
        have next : bound.lookup assumptions.bounds fuel name = some member := by simpa [Ty.lookup,found] using lookup
        exact canonical_lookup_transport assumptions.bounds actual bound equal.symm fuel name member next

public theorem same_type_lookup_transport {assumptions : Assumptions} {actual expected : Ty}
    (related : sameType assumptions actual expected = true) (fuel : Nat) (name : String) (member : Ty)
    (lookup : expected.lookup assumptions.bounds fuel name = some member) :
    ∃ depth actualMember, actual.lookup assumptions.bounds depth name = some actualMember ∧
      sameType assumptions actualMember member = true := by
  obtain ⟨depth, actualMember, found, members⟩ :=
    TypeGraph.equivalent_lookup_transport ((sameType_iff assumptions _ _).mp related) fuel name member lookup
  exact ⟨depth, actualMember, found, (sameType_iff assumptions _ _).mpr members⟩

public inductive HeadNormalizes (bounds : Bounds) : Ty → Ty → Prop where
  | direct (type : Ty) : isVariable type = false → HeadNormalizes bounds type type.canonical
  | alias {index : Nat} {bound result : Ty} : bounds.lookup index = some bound →
      HeadNormalizes bounds bound result → HeadNormalizes bounds (.variable index) result

public theorem head_normalizes_unique {bounds : Bounds} {type first second : Ty}
    (one : HeadNormalizes bounds type first) (two : HeadNormalizes bounds type second) :
    first = second := by
  induction one with
  | direct type terminal =>
      cases two with
      | direct => rfl
      | alias found prior => simp [isVariable] at terminal
  | alias found prior ih =>
      cases two with
      | direct type terminal => simp [isVariable] at terminal
      | alias found' prior' =>
        have same := Option.some.inj (found.symm.trans found')
        subst same
        exact ih prior'

theorem canonical_agreement_normalizes {bounds : Bounds} {first second result : Ty}
    (agreement : first.canonical = second.canonical)
    (normal : HeadNormalizes bounds first result) : HeadNormalizes bounds second result := by
  cases normal with
  | direct first terminal =>
      have terminal' : isVariable second = false := by
        rw [← canonical_is_variable,← agreement,canonical_is_variable,terminal]
      simpa [agreement] using (HeadNormalizes.direct second terminal' : HeadNormalizes bounds second second.canonical)
  | alias found prior =>
      have equal := canonical_variable_inverse agreement.symm
      rw [equal]
      exact .alias found prior

/-- Every successful checker's SAME finite type agreement preserves any head
normalization witness. Thus a row/alias conversion cannot turn a Nat value into
Bool/String or a scalar into a callable/record. Cyclic aliases remain partial. -/
theorem same_step_preserves_head {assumptions : Assumptions} {first second result : Ty}
    (agreement : sameStep assumptions first second = true)
    (normal : HeadNormalizes assumptions.bounds first result) :
    HeadNormalizes assumptions.bounds second result := by
  simp only [sameStep,Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasFirst) | aliasSecond
  · exact canonical_agreement_normalizes (by simpa using canonical) normal
  · cases first <;> simp at aliasFirst
    rename_i index
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at aliasFirst
    | some bound =>
      have found := Assumptions.alias_bound aliased
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = second.canonical := by simpa [aliased] using aliasFirst
      cases normal with
      | direct type terminal => simp [isVariable] at terminal
      | alias found' prior =>
        have same := Option.some.inj (found'.symm.trans found)
        subst same
        exact canonical_agreement_normalizes equal prior
  · cases second <;> simp at aliasSecond
    rename_i index
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at aliasSecond
    | some bound =>
      have found := Assumptions.alias_bound aliased
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = first.canonical := by simpa [aliased] using aliasSecond
      exact .alias found (canonical_agreement_normalizes equal.symm normal)

/-- Exact head normalization belongs to the legacy head-only closure. It is
false for structural equality; runtime consumers now use component agreement. -/
public theorem legacy_same_type_preserves_head {assumptions : Assumptions} {first second result : Ty}
    (agreement : legacySameType assumptions first second = true)
    (normal : HeadNormalizes assumptions.bounds first result) :
    HeadNormalizes assumptions.bounds second result :=
  legacySameType_lift (fun a e => ∀ result, HeadNormalizes assumptions.bounds a result → HeadNormalizes assumptions.bounds e result)
    (fun _ _ h => h) (fun one two result h => two result (one result h))
    (fun step result h => same_step_preserves_head step h) agreement result normal

public inductive HeadKind where
  | natural | boolean | label | function | row | specification | prototype | custody | variable | variant
  | computation
  deriving DecidableEq

@[expose] public def typeHead : Ty → HeadKind
  | .natural => .natural | .boolean => .boolean | .label => .label
  | .arrow _ _ _ _ => .function | .emptyRow | .field _ _ _ => .row
  | .specification _ _ => .specification | .prototype _ _ => .prototype
  | .custody _ => .custody | .variable _ => .variable | .variant _ => .variant
  | .computation _ _ _ => .computation

@[expose] public def valueHead : RuntimeValue → HeadKind
  | .natural _ => .natural | .boolean _ => .boolean | .label _ => .label
  | .closure _ _ => .function | .record _ => .row
  | .specification _ _ => .specification | .prototype _ _ => .prototype
  | .variant _ _ => .variant

theorem insert_canonical_row_head (row : Ty) (name : String) (member : Ty) :
    typeHead (row.insertCanonical name member) = .row := by
  cases row <;> simp only [Ty.insertCanonical]
  all_goals repeat' first | split
  all_goals rfl

theorem canonical_type_head (type : Ty) : typeHead type.canonical = typeHead type := by
  obend_cases type with [Ty.canonical,insert_canonical_row_head]
  all_goals rfl

theorem row_head_normalizes (bounds : Bounds) (fuel : Nat) (row : Ty)
    (isRow : row.isRow bounds fuel = true) :
    ∃ head, HeadNormalizes bounds row head ∧ typeHead head = .row := by
  induction fuel generalizing row with
  | zero => simp [Ty.isRow] at isRow
  | succ fuel ih =>
      cases row with
      | emptyRow => exact ⟨.emptyRow,.direct .emptyRow rfl,rfl⟩
      | field name member tail =>
        exact ⟨_,.direct (.field name member tail) rfl,canonical_type_head _⟩
      | «variable» index =>
        simp only [Ty.isRow] at isRow
        cases found : bounds.lookup index with
        | none => simp [found] at isRow
        | some bound =>
          obtain ⟨head,normal,kind⟩ := ih bound (by simpa [found] using isRow)
          exact ⟨head,.alias found normal,kind⟩
      | _ => simp [Ty.isRow] at isRow


end Obend.Core.Proofs.Preservation
