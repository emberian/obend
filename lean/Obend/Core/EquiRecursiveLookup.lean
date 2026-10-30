module
public import Obend.Core.FieldCongruence
@[expose] public section
namespace Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.FiniteBisimulation (Children)
namespace Rows
export Obend.Core.RecursiveRows (labels_expose_eq residual_expose_eq)
end Rows
set_option autoImplicit false

/-- Finite directional lookup still consults rigid lower bounds. -/
def BoundLookup (a : Assumptions) (row : Ty) (name : String) (member : Ty) : Prop :=
  ∃ fuel, row.lookup a.bounds fuel name = some member

def FiniteRow (a : Assumptions) (row : Ty) : Prop :=
  ∃ fuel, row.isRow a.bounds fuel = true

 theorem lookup_field (a : Assumptions) (prior name : String) (fieldMember tail member : Ty) :
    BoundLookup a (.field prior fieldMember tail) name member ↔
      (if prior = name then fieldMember = member else BoundLookup a tail name member) := by
  by_cases same : prior = name
  · simp only [same, ↓reduceIte]
    constructor
    · rintro ⟨fuel, found⟩
      cases fuel with
      | zero => simp [Ty.lookup] at found
      | succ fuel => simpa [Ty.lookup, same] using found
    · intro equal
      exact ⟨1, by simp [Ty.lookup, same, equal]⟩
  · simp only [same, ↓reduceIte]
    constructor
    · rintro ⟨fuel, found⟩
      cases fuel with
      | zero => simp [Ty.lookup] at found
      | succ fuel => exact ⟨fuel, by simpa [Ty.lookup, same] using found⟩
    · rintro ⟨fuel, found⟩
      exact ⟨fuel + 1, by simpa [Ty.lookup, same] using found⟩

 theorem lookup_alias_chain {a : Assumptions} {start finish : Ty} {path : List Nat}
    (chain : AliasChain a start path finish) (name : String) (member : Ty) :
    BoundLookup a start name member ↔ BoundLookup a finish name member := by
  induction chain with
  | nil _ => exact Iff.rfl
  | @cons index body finish path aliased pure nested ih =>
    have bound := Assumptions.alias_bound aliased
    rw [← ih]
    constructor
    · rintro ⟨fuel, found⟩
      cases fuel with
      | zero => simp [Ty.lookup] at found
      | succ fuel => exact ⟨fuel, by simpa [Ty.lookup, bound] using found⟩
    · rintro ⟨fuel, found⟩
      exact ⟨fuel + 1, by simpa [Ty.lookup, bound] using found⟩

 theorem row_alias_chain {a : Assumptions} {start finish : Ty} {path : List Nat}
    (chain : AliasChain a start path finish) : FiniteRow a start ↔ FiniteRow a finish := by
  induction chain with
  | nil _ => exact Iff.rfl
  | @cons index body finish path aliased pure nested ih =>
    have bound := Assumptions.alias_bound aliased
    rw [← ih]
    constructor
    · rintro ⟨fuel, found⟩
      cases fuel with
      | zero => simp [Ty.isRow] at found
      | succ fuel => exact ⟨fuel, by simpa [Ty.isRow, bound] using found⟩
    · rintro ⟨fuel, found⟩
      exact ⟨fuel + 1, by simpa [Ty.isRow, bound] using found⟩

 theorem expose_constructor_chain (a : Assumptions) (t : Ty) (observation : Constructor)
    (head : expose a t = .constructor observation) :
    ∃ source path, AliasChain a t path source ∧ constructorHead source = .constructor observation := by
  obtain ⟨path, finish, chain, _, _, stopped⟩ :=
    exposeWalk_trace a (a.bounds.map Prod.fst) [] (initial_covers a) t
  change Stopped a (visitPath [] path) finish (expose a t) at stopped
  generalize output : expose a t = observed at stopped
  have shape : observed = .constructor observation := output.symm.trans head
  cases stopped with
  | productive source nonvariable => exact ⟨finish, path, chain, shape⟩
  | unbound fresh missing => contradiction
  | activity fresh found blocked => contradiction
  | cycle seen => contradiction

 theorem expose_nominal_chain (a : Assumptions) (t : Ty) (index : Nat)
    (head : expose a t = .nominal index) : ∃ path, AliasChain a t path (.variable index) := by
  obtain ⟨path, finish, chain, _, _, stopped⟩ :=
    exposeWalk_trace a (a.bounds.map Prod.fst) [] (initial_covers a) t
  change Stopped a (visitPath [] path) finish (expose a t) at stopped
  generalize output : expose a t = observed at stopped
  have shape : observed = .nominal index := output.symm.trans head
  cases stopped with
  | productive source nonvariable => cases finish <;> simp_all [constructorHead]
  | unbound fresh missing =>
    have same := Head.nominal.inj shape
    exact ⟨path, by simpa only [same] using chain⟩
  | activity fresh found blocked =>
    have same := Head.nominal.inj shape
    exact ⟨path, by simpa only [same] using chain⟩
  | cycle seen => contradiction

 theorem exposed_field_lookup (a : Assumptions) (row : Ty) (fieldName name : String)
    (fieldMember tail member : Ty)
    (head : expose a row = .constructor ⟨.field fieldName, [fieldMember, tail]⟩) :
    BoundLookup a row name member ↔ BoundLookup a (.field fieldName fieldMember tail) name member := by
  obtain ⟨source, path, chain, raw⟩ := expose_constructor_chain a row _ head
  have same : source = .field fieldName fieldMember tail := by
    cases source <;> simp_all [constructorHead]
  subst source
  exact lookup_alias_chain chain name member

 theorem exposed_field_row (a : Assumptions) (row : Ty) (name : String) (member tail : Ty)
    (head : expose a row = .constructor ⟨.field name, [member, tail]⟩) :
    FiniteRow a row ↔ FiniteRow a tail := by
  obtain ⟨source, path, chain, raw⟩ := expose_constructor_chain a row _ head
  have same : source = .field name member tail := by cases source <;> simp_all [constructorHead]
  subst source
  rw [row_alias_chain chain]
  constructor
  · rintro ⟨fuel, found⟩
    cases fuel with
    | zero => simp [Ty.isRow] at found
    | succ fuel => exact ⟨fuel, found⟩
  · rintro ⟨fuel, found⟩
    exact ⟨fuel + 1, found⟩

 theorem exposed_empty_row (a : Assumptions) (row : Ty)
    (head : expose a row = .constructor ⟨.emptyRow, []⟩) : FiniteRow a row := by
  obtain ⟨source, path, chain, raw⟩ := expose_constructor_chain a row _ head
  have same : source = .emptyRow := by cases source <;> simp_all [constructorHead]
  subst source
  exact (row_alias_chain chain).mpr ⟨1, rfl⟩

 theorem stream_emission_realizes (a : Assumptions) (remaining : List Ty) (row : Ty)
    (name : String) (member tail : Ty)
    (emitted : Rows.scanStream a remaining name true row = .emit member tail) :
    BoundLookup a row name member := by
  rw [Rows.scanStream] at emitted
  split at emitted
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at emitted
    · contradiction
    · rename_i fieldName fieldMember fieldTail tag children
      have shape : observation = ⟨.field fieldName, [fieldMember, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      apply (exposed_field_lookup a row fieldName name fieldMember fieldTail member exposed).mpr
      rw [lookup_field]
      split at emitted
      · rename_i present
        split at emitted
        · rename_i matched
          have same : fieldName = name := eq_of_beq (by simpa using matched)
          have payload : fieldMember = member := by cases emitted; rfl
          simpa only [same, ↓reduceIte] using payload
        · rename_i skipped
          have different : fieldName ≠ name := by
            intro same
            simp [same] at skipped
          simp only [different, ↓reduceIte]
          exact stream_emission_realizes a (remaining.erase row) fieldTail name member tail emitted
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

 theorem stream_nominal_realizes (a : Assumptions) (remaining : List Ty) (row : Ty)
    (name : String) (index : Nat) (member : Ty)
    (ended : Rows.scanStream a remaining name true row = .end (.nominal index))
    (lookup : BoundLookup a (.variable index) name member) : BoundLookup a row name member := by
  rw [Rows.scanStream] at ended
  split at ended
  · rename_i actual exposed
    have same : actual = index := by simpa using ended
    have head : expose a row = .nominal index := by simpa only [same] using exposed
    obtain ⟨path, chain⟩ := expose_nominal_chain a row index head
    exact (lookup_alias_chain chain name member).mpr lookup
  · simp_all
  · rename_i observation exposed
    split at ended
    · simp_all
    · rename_i fieldName fieldMember fieldTail tag children
      have shape : observation = ⟨.field fieldName, [fieldMember, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      apply (exposed_field_lookup a row fieldName name fieldMember fieldTail member exposed).mpr
      rw [lookup_field]
      split at ended
      · rename_i present
        split at ended
        · simp_all
        · rename_i skipped
          have different : fieldName ≠ name := by intro same; simp [same] at skipped
          simp only [different, ↓reduceIte]
          exact stream_nominal_realizes a (remaining.erase row) fieldTail name index member ended lookup
      · simp_all
    · simp_all
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

 theorem absent_nominal_scan (a : Assumptions) (remaining : List Ty) (row : Ty)
    (name : String) (index : Nat) (absent : name ∉ Rows.scanLabels a remaining row)
    (ending : Rows.scanResidual a remaining row = .nominal index) :
    Rows.scanStream a remaining name true row = .end (.nominal index) := by
  rw [Rows.scanResidual] at ending
  split at ending
  · rename_i actual exposed
    rw [Rows.scanStream, exposed]
    cases ending
    rfl
  · contradiction
  · rename_i observation exposed
    split at ending
    · contradiction
    · rename_i fieldName member tail tag children
      have shape : observation = ⟨.field fieldName, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      rw [Rows.scanStream, exposed]
      rw [Rows.scanLabels, exposed] at absent
      split at ending
      · rename_i present
        simp only [present, ↓reduceDIte] at absent ⊢
        have different : fieldName ≠ name := by
          intro same
          exact absent ((Rows.mem_insertLabel fieldName name _).mpr (.inl same.symm))
        have nested : name ∉ Rows.scanLabels a (remaining.erase row) tail := by
          intro inside
          exact absent ((Rows.mem_insertLabel fieldName name _).mpr (.inr inside))
        simp only [show (fieldName == name) = false from by simpa using different,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact absent_nominal_scan a (remaining.erase row) tail name index nested ending
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

 theorem residual_nominal_expose_eq (a : Assumptions) (left right : Ty) (index : Nat)
    (heads : expose a left = expose a right) (ending : RR.residual a right = .nominal index) :
    RR.residual a left = .nominal index := by
  cases one : expose a left with
  | nominal actual =>
    have two : expose a right = .nominal actual := heads.symm.trans one
    simpa [RR.residual, Rows.scanResidual, one, two] using ending
  | unproductive actual =>
    have two : expose a right = .unproductive actual := heads.symm.trans one
    simp [RR.residual, Rows.scanResidual, two] at ending
  | constructor observation =>
    have two : expose a right = .constructor observation := heads.symm.trans one
    by_cases row : rowTag observation.tag = true
    · rw [Rows.residual_expose_eq a left right observation one heads row]
      exact ending
    · rw [(nonrow_scans a right observation two row).2] at ending
      contradiction

 theorem visible_expose_eq (a : Assumptions) (left right : Ty) (name : String) (member : Ty)
    (heads : expose a left = expose a right)
    (visible : ∃ tail, RR.streamStep a right name true = .emit member tail) :
    ∃ tail, RR.streamStep a left name true = .emit member tail := by
  obtain ⟨tail, emitted⟩ := visible
  have same := RowHit.stream_emission_expose_eq a name true left right heads
  rw [emitted] at same
  cases returned : RR.streamStep a left name true with
  | «end» ending => simp [returned, RowHit.emission] at same
  | emit actual rest =>
    have equal : (actual, rest) = (member, tail) := by simpa [returned, RowHit.emission] using same
    have payload : actual = member := congrArg Prod.fst equal
    exact ⟨rest, by simpa only [payload] using returned⟩

/-- Directional bound lookup splits at its first rigid/opaque nominal frontier;
transparent alias prefixes contribute no extra fields. -/
theorem bound_lookup_decompose (a : Assumptions) (fuel : Nat) (row : Ty) (name : String) (member : Ty)
    (found : row.lookup a.bounds fuel name = some member) :
    (∃ tail, RR.streamStep a row name true = .emit member tail) ∨
      ∃ index, name ∉ RR.labels a row ∧ RR.residual a row = .nominal index ∧
        BoundLookup a (.variable index) name member := by
  cases fuel with
  | zero => simp [Ty.lookup] at found
  | succ fuel =>
    cases row with
    | field prior fieldMember tail =>
      by_cases same : prior = name
      · have payload : fieldMember = member := by simpa [Ty.lookup, same] using found
        subst prior
        subst fieldMember
        left
        have observed := RowHit.stream_emit_observe_eq a name true (.field name member tail) member tail
          (by simp [RowHit.step, raw_field_observation])
        cases returned : RR.streamStep a (.field name member tail) name true <;>
          simp_all [observe]
      · have nested : tail.lookup a.bounds fuel name = some member := by simpa [Ty.lookup, same] using found
        rcases bound_lookup_decompose a fuel tail name member nested with visible | frontier
        · left
          obtain ⟨rest, emitted⟩ := visible
          have observed := RowHit.stream_skip_observe_eq a name true (.field prior fieldMember tail) tail
            (by simp [RowHit.step, raw_field_observation, same, Bool.beq_eq_decide_eq])
          simp only [observe, emitted] at observed
          cases returned : RR.streamStep a (.field prior fieldMember tail) name true <;>
            simp_all [observe]
        · right
          obtain ⟨index, absent, ending, lookup⟩ := frontier
          refine ⟨index, ?_, ?_, lookup⟩
          · rw [Rows.labels_field]
            intro inside
            rcases (Rows.mem_insertLabel prior name _).mp inside with equal | later
            · exact same equal.symm
            · exact absent later
          · rw [Rows.residual_field, ending]
    | «variable» index =>
      cases bound : a.bounds.lookup index with
      | none => simp [Ty.lookup, bound] at found
      | some body =>
        have nested : body.lookup a.bounds fuel name = some member := by simpa [Ty.lookup, bound] using found
        cases aliased : a.alias index with
        | none =>
          right
          have nominal := expose_without_alias a index aliased
          exact ⟨index, by simp [RR.labels, Rows.scanLabels, nominal],
            by simp [RR.residual, Rows.scanResidual, nominal], ⟨fuel + 1, found⟩⟩
        | some disclosed =>
          have actual : disclosed = body := Option.some.inj ((Assumptions.alias_bound aliased).symm.trans bound)
          subst disclosed
          have pure : body.isComputation = false := by
            cases body <;> simp_all [Ty.isComputation, Ty.lookup]
            cases fuel <;> simp_all [Ty.lookup]
          have heads := expose_alias a index body aliased pure
          rcases bound_lookup_decompose a fuel body name member nested with visible | frontier
          · exact .inl (visible_expose_eq a _ body name member heads visible)
          · obtain ⟨frontier, absent, ending, lookup⟩ := frontier
            exact .inr ⟨frontier, by simpa only [Rows.labels_expose_eq a _ body heads] using absent,
              residual_nominal_expose_eq a _ body frontier heads ending, lookup⟩
    | _ => simp [Ty.lookup] at found
termination_by fuel

/-- Equi-recursive agreement transports directional bounded lookup. Result
members are related by the same agreement, including recursive member types. -/
theorem equivalent_lookup_transport {a : Assumptions} {actual expected : Ty}
    (agreement : Equivalent a actual expected) (fuel : Nat) (name : String) (member : Ty)
    (lookup : expected.lookup a.bounds fuel name = some member) :
    ∃ depth actualMember, actual.lookup a.bounds depth name = some actualMember ∧
      Equivalent a actualMember member := by
  have view := equivalent_row_interface agreement
  rcases bound_lookup_decompose a fuel expected name member lookup with visible | frontier
  · obtain ⟨tail, emitted⟩ := visible
    obtain ⟨labels, children⟩ := Obend.Core.FinitePresentation.bisimilar_closed (graph a) _ _ (view.streams name)
    cases returned : RR.streamStep a actual name true with
    | «end» ending => simp [graph, observe, returned, emitted] at labels
    | emit actualMember rest =>
      have members : Equivalent a actualMember member := by
        have nested : Equivalent a actualMember member ∧ StreamEquivalent a rest tail name false := by
          simpa [graph, observe, returned, emitted, Children, Equivalent, StreamEquivalent] using children
        exact nested.1
      obtain ⟨depth, found⟩ := stream_emission_realizes a _ actual name actualMember rest returned
      exact ⟨depth, actualMember, found, members⟩
  · obtain ⟨index, absent, ending, lookup⟩ := frontier
    have actualAbsent : name ∉ RR.labels a actual := by simpa only [view.alphabet] using absent
    have actualEnding : RR.residual a actual = .nominal index := by
      have kind := view.residualKind
      rw [ending] at kind
      cases result : RR.residual a actual <;> simp_all [tailKind]
    have ended := absent_nominal_scan a _ actual name index actualAbsent actualEnding
    obtain ⟨depth, found⟩ := stream_nominal_realizes a _ actual name index member ended lookup
    exact ⟨depth, member, found, (equivalent_equivalence a).refl member⟩

 theorem exposed_empty_tag_row (a : Assumptions) (row : Ty) (observation : Constructor)
    (head : expose a row = .constructor observation) (tag : observation.tag = .emptyRow) :
    FiniteRow a row := by
  obtain ⟨source, path, chain, raw⟩ := expose_constructor_chain a row observation head
  have tagged : (match constructorHead source with
      | .constructor actual => actual.tag
      | _ => .natural) = .emptyRow := by rw [raw]; exact tag
  have same : source = .emptyRow := by
    cases source <;> simp only [constructorHead] at tagged <;> first | contradiction | rfl
  subst source
  exact (row_alias_chain chain).mpr ⟨1, rfl⟩

 theorem residual_closed_realizes (a : Assumptions) (remaining : List Ty) (row : Ty)
    (ending : Rows.scanResidual a remaining row = .closed) : FiniteRow a row := by
  rw [Rows.scanResidual] at ending
  split at ending
  · contradiction
  · contradiction
  · rename_i observation exposed
    split at ending
    · rename_i tag
      exact exposed_empty_tag_row a row observation exposed tag
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      apply (exposed_field_row a row name member tail exposed).mpr
      split at ending
      · exact residual_closed_realizes a (remaining.erase row) tail ending
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

 theorem residual_nominal_row_realizes (a : Assumptions) (remaining : List Ty) (row : Ty) (index : Nat)
    (ending : Rows.scanResidual a remaining row = .nominal index)
    (finite : FiniteRow a (.variable index)) : FiniteRow a row := by
  rw [Rows.scanResidual] at ending
  split at ending
  · rename_i actual exposed
    have same : actual = index := by simpa using ending
    have head : expose a row = .nominal index := by simpa only [same] using exposed
    obtain ⟨path, chain⟩ := expose_nominal_chain a row index head
    exact (row_alias_chain chain).mpr finite
  · contradiction
  · rename_i observation exposed
    split at ending
    · contradiction
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      apply (exposed_field_row a row name member tail exposed).mpr
      split at ending
      · exact residual_nominal_row_realizes a (remaining.erase row) tail index ending finite
      · contradiction
    · contradiction
termination_by remaining.length
decreasing_by
  have present : row ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

 theorem residual_closed_expose_eq (a : Assumptions) (left right : Ty)
    (heads : expose a left = expose a right) (ending : RR.residual a right = .closed) :
    RR.residual a left = .closed := by
  cases one : expose a left with
  | nominal actual =>
    have two : expose a right = .nominal actual := heads.symm.trans one
    simp [RR.residual, Rows.scanResidual, two] at ending
  | unproductive actual =>
    have two : expose a right = .unproductive actual := heads.symm.trans one
    simp [RR.residual, Rows.scanResidual, two] at ending
  | constructor observation =>
    have two : expose a right = .constructor observation := heads.symm.trans one
    by_cases row : rowTag observation.tag = true
    · rw [Rows.residual_expose_eq a left right observation one heads row]
      exact ending
    · rw [(nonrow_scans a right observation two row).2] at ending
      contradiction

 theorem finite_row_decompose (a : Assumptions) (fuel : Nat) (row : Ty)
    (finite : row.isRow a.bounds fuel = true) :
    RR.residual a row = .closed ∨ ∃ index,
      RR.residual a row = .nominal index ∧ FiniteRow a (.variable index) := by
  cases fuel with
  | zero => simp [Ty.isRow] at finite
  | succ fuel =>
    cases row with
    | emptyRow =>
      left
      simp [RR.residual, Rows.scanResidual, expose, exposeWalk, constructorHead]
    | field name member tail =>
      rw [Rows.residual_field]
      exact finite_row_decompose a fuel tail finite
    | «variable» index =>
      cases bound : a.bounds.lookup index with
      | none => simp [Ty.isRow, bound] at finite
      | some body =>
        have nested : body.isRow a.bounds fuel = true := by simpa [Ty.isRow, bound] using finite
        cases aliased : a.alias index with
        | none =>
          right
          have nominal := expose_without_alias a index aliased
          exact ⟨index, by simp [RR.residual, Rows.scanResidual, nominal], ⟨fuel + 1, finite⟩⟩
        | some disclosed =>
          have actual : disclosed = body := Option.some.inj ((Assumptions.alias_bound aliased).symm.trans bound)
          subst disclosed
          have pure : body.isComputation = false := by
            cases body <;> simp_all [Ty.isComputation, Ty.isRow]
            cases fuel <;> simp_all [Ty.isRow]
          have heads := expose_alias a index body aliased pure
          rcases finite_row_decompose a fuel body nested with closed | frontier
          · exact .inl (residual_closed_expose_eq a _ body heads closed)
          · obtain ⟨frontier, ending, finite⟩ := frontier
            exact .inr ⟨frontier, residual_nominal_expose_eq a _ body frontier heads ending, finite⟩
    | _ => simp [Ty.isRow] at finite
termination_by fuel

/-- Finite rowness is preserved. A productive field cycle is not a finite
closed row; nominal lower-bound rowness is transported at the same identity. -/
theorem equivalent_finite_row_transport {a : Assumptions} {actual expected : Ty}
    (agreement : Equivalent a actual expected) (fuel : Nat)
    (finite : expected.isRow a.bounds fuel = true) :
    ∃ depth, actual.isRow a.bounds depth = true := by
  have view := equivalent_row_interface agreement
  rcases finite_row_decompose a fuel expected finite with closed | frontier
  · have ending : RR.residual a actual = .closed := by
      have kind := view.residualKind
      rw [closed] at kind
      cases result : RR.residual a actual <;> simp_all [tailKind]
    exact residual_closed_realizes a _ actual ending
  · obtain ⟨index, ending, finite⟩ := frontier
    have actualEnding : RR.residual a actual = .nominal index := by
      have kind := view.residualKind
      rw [ending] at kind
      cases result : RR.residual a actual <;> simp_all [tailKind]
    exact residual_nominal_row_realizes a _ actual index actualEnding finite

 theorem equivalent_finite_row_iff {a : Assumptions} {actual expected : Ty}
    (agreement : Equivalent a actual expected) : FiniteRow a actual ↔ FiniteRow a expected := by
  constructor
  · rintro ⟨fuel, finite⟩
    exact equivalent_finite_row_transport ((equivalent_equivalence a).symm agreement) fuel finite
  · rintro ⟨fuel, finite⟩
    exact equivalent_finite_row_transport agreement fuel finite

#assert_axioms lookup_alias_chain row_alias_chain expose_constructor_chain expose_nominal_chain
  stream_emission_realizes stream_nominal_realizes absent_nominal_scan
  bound_lookup_decompose equivalent_lookup_transport
  residual_closed_realizes residual_nominal_row_realizes finite_row_decompose
  equivalent_finite_row_transport equivalent_finite_row_iff
end Obend.Core.TypeGraph
