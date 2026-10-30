module
/- Executable resource and row observations, before any equality integration.
Streams are graph observations: an emission contains the raw tail state. Calling
`streamStep` on that tail starts a fresh epsilon scan, preserving infinitely
many hidden resourceful fields without constructing an infinite Lean list. -/
public import Obend.Core.AliasExposure
public import Obend.Core.ResourceSemantics
public import Obend.AxiomPin
@[expose] public section
namespace Obend.Core.RecursiveRows
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-- Resource observations now use the proved greatest-safe-predicate decision.
The former branch-local DFS and its implementation-specific helper lemmas are
retired; stream scanning continues to use this single semantic implementation. -/
def shareable (assumptions : Assumptions) (t : Ty) : Bool :=
  Obend.Core.ResourceSemantics.shareable assumptions t

theorem shareable_iff (assumptions : Assumptions) (t : Ty) :
    shareable assumptions t = true ↔
      Obend.Core.FiniteSafety.Safe (Obend.Core.ResourceSemantics.graph assumptions) t :=
  Obend.Core.ResourceSemantics.shareable_iff assumptions t

theorem shareable_unfold (assumptions : Assumptions) (t : Ty) :
    shareable assumptions t = true ↔
      (Obend.Core.ResourceSemantics.head assumptions t).1 = true ∧
      ∀ child ∈ (Obend.Core.ResourceSemantics.head assumptions t).2,
        shareable assumptions child = true :=
  Obend.Core.ResourceSemantics.shareable_unfold assumptions t

theorem shareable_eq_of_expose_eq {assumptions : Assumptions} {left right : Ty}
    (same : expose assumptions left = expose assumptions right) :
    shareable assumptions left = shareable assumptions right :=
  Obend.Core.ResourceSemantics.shareable_eq_of_expose_eq same

theorem shareable_terminal {assumptions : Assumptions} {t : Ty} {value : Bool}
    (terminal : Obend.Core.ResourceSemantics.head assumptions t = (value,[])) :
    shareable assumptions t = value := by
  apply Obend.Core.FiniteSafety.bool_ext
  rw [shareable_unfold]
  simp [terminal]

@[simp] theorem shareable_natural (assumptions : Assumptions) :
    shareable assumptions .natural = true := by
  apply shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,constructorHead]

@[simp] theorem shareable_label (assumptions : Assumptions) :
    shareable assumptions .label = true := by
  apply shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,constructorHead]

@[simp] theorem shareable_boolean (assumptions : Assumptions) :
    shareable assumptions .boolean = true := by
  apply shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,constructorHead]

@[simp] theorem shareable_emptyRow (assumptions : Assumptions) :
    shareable assumptions .emptyRow = true := by
  apply shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,constructorHead]

@[simp] theorem shareable_custody (assumptions : Assumptions) (identity : Nat) :
    shareable assumptions (.custody identity) = false := by
  apply shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,constructorHead]

@[simp] theorem shareable_arrow (assumptions : Assumptions) (reuse : Reuse)
    (quantity : Quantity) (domain codomain : Ty) :
    shareable assumptions (.arrow reuse quantity domain codomain) = (reuse == .reusable) := by
  apply shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,constructorHead]

@[simp] theorem shareable_computation (assumptions : Assumptions) (plan response result : Ty) :
    shareable assumptions (.computation plan response result) = false := by
  apply shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,constructorHead]

theorem shareable_field (assumptions : Assumptions) (name : String) (member tail : Ty) :
    shareable assumptions (.field name member tail) =
      (shareable assumptions member && shareable assumptions tail) :=
  Obend.Core.ResourceSemantics.shareable_field assumptions name member tail

theorem shareable_specification (assumptions : Assumptions) (metadata extension : Ty) :
    shareable assumptions (.specification metadata extension) =
      (shareable assumptions metadata && shareable assumptions extension) :=
  Obend.Core.ResourceSemantics.shareable_specification assumptions metadata extension

theorem shareable_prototype (assumptions : Assumptions) (spec target : Ty) :
    shareable assumptions (.prototype spec target) =
      (shareable assumptions spec && shareable assumptions target) :=
  Obend.Core.ResourceSemantics.shareable_prototype assumptions spec target

theorem shareable_variant (assumptions : Assumptions) (row : Ty) :
    shareable assumptions (.variant row) = shareable assumptions row :=
  Obend.Core.ResourceSemantics.shareable_variant assumptions row

inductive Tail where
  | closed
  | productiveCycle
  | nominal (index : Nat)
  | unproductive (representative : Nat)
  | nonRow (type : Ty)
  deriving DecidableEq, Repr

inductive StreamStep where
  | end (tail : Tail)
  /-- The next stream state is `(tail, label, false)`. Epsilon visitation is
  reset after every emission, including hidden resourceful emissions. -/
  | emit (member tail : Ty)
  deriving DecidableEq, Repr

/-- A finite epsilon walk to the next field of one label. The first matching
member is visible; subsequent matching members survive only if resourceful.
Repeated states on this skip path terminate, rather than emit a false field. -/
def scanStream (assumptions : Assumptions) (remaining : List Ty)
    (label : String) (first : Bool) (row : Ty) : StreamStep :=
  match expose assumptions row with
  | .nominal index => .end (.nominal index)
  | .unproductive index => .end (.unproductive index)
  | .constructor observation =>
    match observation.tag, observation.children with
    | .emptyRow, _ => .end .closed
    | .field name, [member, tail] =>
      if present : row ∈ remaining then
        if name == label && (first || !shareable assumptions member) then .emit member tail
        else scanStream assumptions (remaining.erase row) label first tail
      else .end .closed
    | _, _ => .end (.nonRow row)
termination_by remaining.length
decreasing_by
  all_goals
    rw [List.length_erase_of_mem present]
    have positive := List.length_pos_of_mem present
    omega

def streamStep (assumptions : Assumptions) (row : Ty) (label : String) (first : Bool) : StreamStep :=
  scanStream assumptions (support assumptions row row) label first row

/-- The residual row tail is independent of its fields. A productive field-tail
cycle is distinguished from a finite closed row; resource obligations live in label streams. -/
def scanResidual (assumptions : Assumptions) (remaining : List Ty) (row : Ty) : Tail :=
  match expose assumptions row with
  | .nominal index => .nominal index
  | .unproductive index => .unproductive index
  | .constructor observation =>
    match observation.tag, observation.children with
    | .emptyRow, _ => .closed
    | .field _, [_, tail] =>
      if present : row ∈ remaining then scanResidual assumptions (remaining.erase row) tail
      else .productiveCycle
    | _, _ => .nonRow row
termination_by remaining.length
decreasing_by
  all_goals
    rw [List.length_erase_of_mem present]
    have positive := List.length_pos_of_mem present
    omega

def residual (assumptions : Assumptions) (row : Ty) : Tail :=
  scanResidual assumptions (support assumptions row row) row

/-- Sorted insertion with duplicate suppression. This is deliberately local to
the row's exposed tail path; unrelated bound bodies contribute no labels. -/
def insertLabel (name : String) : List String → List String
  | [] => [name]
  | prior :: rest =>
    if name = prior then prior :: rest
    else if name < prior then name :: prior :: rest
    else prior :: insertLabel name rest

theorem mem_insertLabel (name item : String) (labels : List String) :
    item ∈ insertLabel name labels ↔ item = name ∨ item ∈ labels := by
  induction labels with
  | nil => simp [insertLabel]
  | cons prior rest ih =>
    simp only [insertLabel]
    split
    · rename_i same
      subst prior
      simp
    · split <;> simp [ih, or_assoc, or_comm, or_left_comm]

def scanLabels (assumptions : Assumptions) (remaining : List Ty) (row : Ty) : List String :=
  match expose assumptions row with
  | .constructor observation =>
    match observation.tag, observation.children with
    | .field name, [_, tail] =>
      if present : row ∈ remaining then
        insertLabel name (scanLabels assumptions (remaining.erase row) tail)
      else []
    | _, _ => []
  | _ => []
termination_by remaining.length
decreasing_by
  all_goals
    rw [List.length_erase_of_mem present]
    have positive := List.length_pos_of_mem present
    omega

/-- A row-local finite alphabet, sorted and deduplicated as it is collected.
Alias-only and productive field-tail cycles both terminate the prefix scan. -/
def labels (assumptions : Assumptions) (row : Ty) : List String :=
  scanLabels assumptions (support assumptions row row) row

theorem labels_alias_tail_sorted_unique :
    labels ⟨[(0, .field "a" .natural (.field "z" .boolean .emptyRow)),
      (1, .field "unused" .natural .emptyRow)], [], []⟩
      (.field "z" .natural (.variable 0)) = ["a", "z"] := by
  simp [labels, scanLabels, insertLabel, support, subterms, expose, exposeWalk,
    Assumptions.alias, constructorHead, Ty.isComputation, List.lookup, List.erase, Bool.beq_eq_decide_eq]

theorem labels_productive_cycle_finite :
    labels ⟨[(0, .field "a" .natural (.variable 0))], [], []⟩ (.variable 0) = ["a"] := by
  simp [labels, scanLabels, insertLabel, support, subterms, expose, exposeWalk,
    Assumptions.alias, constructorHead, Ty.isComputation, List.lookup, List.erase, Bool.beq_eq_decide_eq]

theorem shadow_natural_alias_discarded :
    streamStep ⟨[(0, .natural)], [], []⟩
      (.field "a" (.variable 0) .emptyRow) "a" false = .end .closed := by
  have aliasShare : shareable ⟨[(0, .natural)], [], []⟩ (.variable 0) = true := by
    apply shareable_terminal
    simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,Assumptions.alias,
      constructorHead,Ty.isComputation,List.lookup]
  simp [streamStep, scanStream, residual, scanResidual, aliasShare, shareable_natural, shareable_custody,
    support, subterms, expose, exposeWalk, Assumptions.alias, constructorHead,
    cycleRepresentative, Ty.isComputation, List.lookup, List.erase, Bool.beq_eq_decide_eq]

theorem shadow_custody_alias_retained :
    streamStep ⟨[(0, .custody 7)], [], []⟩
      (.field "a" (.variable 0) .emptyRow) "a" false = .emit (.variable 0) .emptyRow := by
  have aliasShare : shareable ⟨[(0, .custody 7)], [], []⟩ (.variable 0) = false := by
    apply shareable_terminal
    simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,Assumptions.alias,
      constructorHead,Ty.isComputation,List.lookup]
  simp [streamStep, scanStream, residual, scanResidual, aliasShare, shareable_natural, shareable_custody,
    support, subterms, expose, exposeWalk, Assumptions.alias, constructorHead,
    cycleRepresentative, Ty.isComputation, List.lookup, List.erase, Bool.beq_eq_decide_eq]

theorem alias_tail_field_exposed :
    streamStep ⟨[(0, .field "b" .natural .emptyRow)], [], []⟩
      (.field "a" .boolean (.variable 0)) "b" true = .emit .natural .emptyRow := by
  simp [streamStep, scanStream, residual, scanResidual, shareable_natural, shareable_custody,
    support, subterms, expose, exposeWalk, Assumptions.alias, constructorHead,
    cycleRepresentative, Ty.isComputation, List.lookup, List.erase, Bool.beq_eq_decide_eq]

theorem cyclic_shareable_shadow_stream_finite :
    streamStep ⟨[(0, .field "a" .natural (.variable 0))], [], []⟩
      (.variable 0) "a" false = .end .closed := by
  simp [streamStep, scanStream, residual, scanResidual, shareable_natural, shareable_custody,
    support, subterms, expose, exposeWalk, Assumptions.alias, constructorHead,
    cycleRepresentative, Ty.isComputation, List.lookup, List.erase, Bool.beq_eq_decide_eq]

theorem cyclic_resourceful_shadow_stream_recursive :
    streamStep ⟨[(0, .field "a" (.custody 7) (.variable 0))], [], []⟩
      (.variable 0) "a" false = .emit (.custody 7) (.variable 0) := by
  simp [streamStep, scanStream, residual, scanResidual, shareable_natural, shareable_custody,
    support, subterms, expose, exposeWalk, Assumptions.alias, constructorHead,
    cycleRepresentative, Ty.isComputation, List.lookup, List.erase, Bool.beq_eq_decide_eq]

theorem cyclic_row_residual_productive :
    residual ⟨[(0, .field "a" (.custody 7) (.variable 0))], [], []⟩ (.variable 0) = .productiveCycle := by
  simp [streamStep, scanStream, residual, scanResidual, shareable_natural, shareable_custody,
    support, subterms, expose, exposeWalk, Assumptions.alias, constructorHead,
    cycleRepresentative, Ty.isComputation, List.lookup, List.erase, Bool.beq_eq_decide_eq]

theorem productive_recursive_row_shareable :
    shareable ⟨[(0, .field "a" .natural (.variable 0))], [], []⟩ (.variable 0) = true := by
  let assumptions : Assumptions := ⟨[(0, .field "a" .natural (.variable 0))], [], []⟩
  have exposedHead : Obend.Core.ResourceSemantics.head assumptions (.variable 0) =
      (true,[.natural,.variable 0]) := by
    simp [Obend.Core.ResourceSemantics.head,assumptions,expose,exposeWalk,
      Assumptions.alias,constructorHead,Ty.isComputation,List.lookup]
  apply (shareable_iff assumptions (.variable 0)).mpr
  refine ⟨fun t => t = .variable 0 ∨ t = .natural,?_,Or.inl rfl⟩
  intro t member
  rcases member with isVariable | natural
  · subst t
    change (Obend.Core.ResourceSemantics.head assumptions (.variable 0)).1 = true ∧
      ∀ child ∈ (Obend.Core.ResourceSemantics.head assumptions (.variable 0)).2,
        child = .variable 0 ∨ child = .natural
    rw [exposedHead]
    simp [or_comm]
  · subst t
    change (Obend.Core.ResourceSemantics.head assumptions .natural).1 = true ∧
      ∀ child ∈ (Obend.Core.ResourceSemantics.head assumptions .natural).2,
        child = .variable 0 ∨ child = .natural
    simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,constructorHead]

theorem unproductive_alias_shareable :
    shareable ⟨[(0, .variable 0)], [0], []⟩ (.variable 0) = true := by
  apply shareable_terminal
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,Assumptions.alias,
    constructorHead,cycleRepresentative,Ty.isComputation,List.lookup,List.erase,
    Bool.beq_eq_decide_eq]

theorem custody_recursive_row_not_shareable :
    shareable ⟨[(0, .field "a" (.custody 7) (.variable 0))], [], []⟩ (.variable 0) = false := by
  apply Obend.Core.FiniteSafety.bool_ext
  rw [shareable_unfold]
  simp [Obend.Core.ResourceSemantics.head,expose,exposeWalk,Assumptions.alias,
    constructorHead,Ty.isComputation,List.lookup]

#assert_axioms shareable_iff shareable_unfold shareable_eq_of_expose_eq shareable_terminal
  shareable_natural shareable_label shareable_boolean shareable_emptyRow shareable_custody
  shareable_arrow shareable_computation shareable_field shareable_specification
  shareable_prototype shareable_variant
  shadow_natural_alias_discarded shadow_custody_alias_retained
  mem_insertLabel labels_alias_tail_sorted_unique labels_productive_cycle_finite
  alias_tail_field_exposed cyclic_shareable_shadow_stream_finite
  cyclic_resourceful_shadow_stream_recursive cyclic_row_residual_productive
  productive_recursive_row_shareable unproductive_alias_shareable custody_recursive_row_not_shareable

public theorem scanStream_emit_support
    (assumptions : Assumptions) (left right : Ty)
    (remaining : List Ty) (label : String) (first : Bool)
    (row member tail : Ty)
    (present : row ∈ support assumptions left right)
    (emitted : scanStream assumptions remaining label first row = .emit member tail) :
    member ∈ support assumptions left right ∧ tail ∈ support assumptions left right := by
  rw [scanStream] at emitted
  split at emitted
  · contradiction
  · contradiction
  · rename_i observation exposed
    have closed := expose_children_support present exposed
    split at emitted
    · contradiction
    · rename_i name fieldMember fieldTail tag children
      have memberPresent : fieldMember ∈ support assumptions left right := by
        apply closed fieldMember
        simp [children]
      have tailPresent : fieldTail ∈ support assumptions left right := by
        apply closed fieldTail
        simp [children]
      split at emitted
      · rename_i available
        split at emitted
        · cases emitted
          exact ⟨memberPresent, tailPresent⟩
        · exact scanStream_emit_support assumptions left right (remaining.erase row)
            label first fieldTail member tail tailPresent emitted
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have available : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem available]
  have positive := List.length_pos_of_mem available
  omega

public theorem streamStep_emit_support
    {assumptions : Assumptions} {left right row member tail : Ty}
    {label : String} {first : Bool}
    (present : row ∈ support assumptions left right)
    (emitted : streamStep assumptions row label first = .emit member tail) :
    member ∈ support assumptions left right ∧ tail ∈ support assumptions left right :=
  scanStream_emit_support assumptions left right _ label first row member tail present emitted

public theorem scanResidual_nonRow_support
    (assumptions : Assumptions) (left right : Ty)
    (remaining : List Ty) (row result : Ty)
    (present : row ∈ support assumptions left right)
    (returned : scanResidual assumptions remaining row = .nonRow result) :
    result ∈ support assumptions left right := by
  rw [scanResidual] at returned
  split at returned
  · contradiction
  · contradiction
  · rename_i observation exposed
    have closed := expose_children_support present exposed
    split at returned
    · contradiction
    · rename_i name fieldMember fieldTail tag children
      have tailPresent : fieldTail ∈ support assumptions left right := by
        apply closed fieldTail
        simp [children]
      split at returned
      · rename_i available
        exact scanResidual_nonRow_support assumptions left right (remaining.erase row)
          fieldTail result tailPresent returned
      · contradiction
    · cases returned
      exact present
termination_by remaining.length
decreasing_by
  have available : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem available]
  have positive := List.length_pos_of_mem available
  omega

public theorem residual_nonRow_support
    {assumptions : Assumptions} {left right row result : Ty}
    (present : row ∈ support assumptions left right)
    (returned : residual assumptions row = .nonRow result) :
    result ∈ support assumptions left right :=
  scanResidual_nonRow_support assumptions left right _ row result present returned

#assert_axioms scanStream_emit_support streamStep_emit_support
  scanResidual_nonRow_support residual_nonRow_support


@[expose] public def fieldLabels (nodes : List Ty) : List String :=
  nodes.filterMap (fun
    | .field name _ _ => some name
    | _ => none)

public theorem field_name_mem_fieldLabels
    {nodes : List Ty} {name : String} {member tail : Ty}
    (present : Ty.field name member tail ∈ nodes) : name ∈ fieldLabels nodes :=
  List.mem_filterMap.mpr ⟨.field name member tail, present, rfl⟩

/-- A local row alphabet introduces no labels outside the finite raw syntax
support. Alias tails are accounted for by the exposed-field origin theorem. -/
public theorem scanLabels_mem_fieldLabels
    (assumptions : Assumptions) (left right : Ty)
    (remaining : List Ty) (row : Ty) (name : String)
    (present : row ∈ support assumptions left right)
    (listed : name ∈ scanLabels assumptions remaining row) :
    name ∈ fieldLabels (support assumptions left right) := by
  rw [scanLabels] at listed
  split at listed
  · rename_i observation exposed
    split at listed
    · rename_i fieldName member tail tag children
      have shape : observation = ⟨.field fieldName, [member, tail]⟩ := by
        cases observation
        simp_all
      have exactHead : expose assumptions row = .constructor ⟨.field fieldName, [member, tail]⟩ := by
        simpa only [shape] using exposed
      have fieldPresent := expose_field_mem_support present exactHead
      have tailPresent : tail ∈ support assumptions left right :=
        expose_children_support present exactHead tail (by simp)
      split at listed
      · rename_i available
        rcases (mem_insertLabel fieldName name _).mp listed with same | nested
        · subst name
          exact field_name_mem_fieldLabels fieldPresent
        · exact scanLabels_mem_fieldLabels assumptions left right (remaining.erase row)
            tail name tailPresent nested
      · simp at listed
    · simp at listed
  · simp at listed
termination_by remaining.length
decreasing_by
  have available : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem available]
  have positive := List.length_pos_of_mem available
  omega

public theorem labels_mem_fieldLabels
    {assumptions : Assumptions} {left right row : Ty} {name : String}
    (present : row ∈ support assumptions left right)
    (listed : name ∈ labels assumptions row) :
    name ∈ fieldLabels (support assumptions left right) :=
  scanLabels_mem_fieldLabels assumptions left right _ row name present listed

#assert_axioms field_name_mem_fieldLabels scanLabels_mem_fieldLabels labels_mem_fieldLabels


end Obend.Core.RecursiveRows
end
