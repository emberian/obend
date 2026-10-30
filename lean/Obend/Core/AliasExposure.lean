module
/- Finite syntax support and productive alias-head observations.

This is a frontend scaffold, NOT a replacement for `sameType`. In particular,
raw fields are exposed as syntax constructors, NOT row equality observations.
No consumer may interpret this raw graph as canonical row equality. -/
public import Obend.Core.Assumptions
public import Obend.AxiomPin
@[expose] public section
namespace Obend.Core.AliasExposure
open Obend.Core.Ty Obend.Core.Check
set_option autoImplicit false

/-- Original syntax is retained, including hidden fields and alias tails. -/
def subterms : Ty → List Ty
  | t@(.arrow _ _ a b) | t@(.field _ a b) | t@(.specification a b)
  | t@(.prototype a b) => t :: (subterms a ++ subterms b)
  | t@(.variant a) => t :: subterms a
  | t@(.computation a b c) => t :: (subterms a ++ subterms b ++ subterms c)
  | t => [t]

theorem self_mem_subterms (t : Ty) : t ∈ subterms t := by
  cases t <;> simp [subterms]

/-- Taking a subterm twice remains inside the original finite syntax. -/
theorem subterms_trans (t s c : Ty) (hs : s ∈ subterms t) (hc : c ∈ subterms s) : c ∈ subterms t := by
  induction t with
  | arrow reuse quantity a b iha ihb | field name a b iha ihb
  | specification a b iha ihb | prototype a b iha ihb =>
    simp only [subterms, List.mem_cons, List.mem_append] at hs ⊢
    rcases hs with rfl | ha | hb
    · simpa only [subterms, List.mem_cons, List.mem_append] using hc
    · exact .inr (.inl (iha ha))
    · exact .inr (.inr (ihb hb))
  | variant a ih =>
    simp only [subterms, List.mem_cons] at hs ⊢
    rcases hs with rfl | ha
    · simpa only [subterms, List.mem_cons, List.mem_append] using hc
    · exact .inr (ih ha)
  | computation a b d iha ihb ihd =>
    simp only [subterms, List.mem_cons, List.mem_append] at hs ⊢
    rcases hs with rfl | (ha | hb) | hd
    · simpa only [subterms, List.mem_cons, List.mem_append] using hc
    · exact .inr (.inl (.inl (iha ha)))
    · exact .inr (.inl (.inr (ihb hb)))
    · exact .inr (.inr (ihd hd))
  | _ =>
    simp only [subterms, List.mem_singleton] at hs
    subst s
    exact hc

/-- A finite (not necessarily duplicate-free) support. Avoiding deduplication
also avoids imposing an incidental node numbering on semantic observations. -/
def support (assumptions : Assumptions) (left right : Ty) : List Ty :=
  subterms left ++ subterms right ++ assumptions.bounds.flatMap (fun b => subterms b.2)

theorem left_mem_support (assumptions : Assumptions) (left right : Ty) :
    left ∈ support assumptions left right := by
  simp [support, self_mem_subterms]

theorem right_mem_support (assumptions : Assumptions) (left right : Ty) :
    right ∈ support assumptions left right := by
  simp [support, self_mem_subterms]

theorem bound_subterm_mem_support (assumptions : Assumptions) (left right : Ty)
    (binding : Nat × Ty) (present : binding ∈ assumptions.bounds)
    (member : Ty) (inside : member ∈ subterms binding.2) :
    member ∈ support assumptions left right := by
  have contained : member ∈ assumptions.bounds.flatMap (fun b => subterms b.2) :=
    List.mem_flatMap.mpr ⟨binding, present, inside⟩
  simp [support, contained]

/-- The support is closed under syntax children, including children reached
inside a bound rather than inside either query root. -/
theorem support_subterms {assumptions : Assumptions} {left right t child : Ty}
    (present : t ∈ support assumptions left right) (inside : child ∈ subterms t) :
    child ∈ support assumptions left right := by
  simp only [support, List.mem_append] at present ⊢
  rcases present with (hl | hr) | hb
  · exact .inl (.inl (subterms_trans left t child hl inside))
  · exact .inl (.inr (subterms_trans right t child hr inside))
  · obtain ⟨binding, member, nested⟩ := List.mem_flatMap.mp hb
    exact .inr (List.mem_flatMap.mpr
      ⟨binding, member, subterms_trans binding.2 t child nested inside⟩)

theorem alias_mem_support {assumptions : Assumptions} {left right body : Ty} {index : Nat}
    (found : assumptions.alias index = some body) : body ∈ support assumptions left right := by
  have bound := Assumptions.alias_bound found
  obtain ⟨pre, post, equal, _⟩ := List.lookup_eq_some_iff.mp bound
  exact bound_subterm_mem_support assumptions left right (index, body)
    (by rw [equal]; simp) body (self_mem_subterms body)

/-- Tags never erase quantities, reuse, custody identity, or field labels.
This observes original syntax, rather than the quotient needed for row equality. -/
inductive Tag where
  | natural | label | boolean | emptyRow
  | arrow (reuse : Reuse) (quantity : Quantity)
  | specification | prototype | variant | computation
  | custody (identity : Nat)
  | field (name : String)
  deriving DecidableEq, Repr

structure Constructor where
  tag : Tag
  children : List Ty
  deriving DecidableEq, Repr

inductive Head where
  | constructor (observation : Constructor)
  | nominal (index : Nat)
  /-- The minimum variable in the actual head-only cycle, excluding a prefix
  that merely leads into it. A head-only SCC never proves arbitrary equality. -/
  | unproductive (representative : Nat)
  deriving DecidableEq, Repr

def constructorHead : Ty → Head
  | .natural => .constructor ⟨.natural, []⟩
  | .label => .constructor ⟨.label, []⟩
  | .boolean => .constructor ⟨.boolean, []⟩
  | .emptyRow => .constructor ⟨.emptyRow, []⟩
  | .arrow reuse quantity a b => .constructor ⟨.arrow reuse quantity, [a,b]⟩
  | .specification a b => .constructor ⟨.specification, [a,b]⟩
  | .prototype a b => .constructor ⟨.prototype, [a,b]⟩
  | .custody identity => .constructor ⟨.custody identity, []⟩
  | .variant row => .constructor ⟨.variant, [row]⟩
  | .computation a b c => .constructor ⟨.computation, [a,b,c]⟩
  | .field name member tail => .constructor ⟨.field name, [member, tail]⟩
  | .variable index => .nominal index

theorem constructorHead_children (t : Ty) (observation : Constructor) (found : constructorHead t = .constructor observation) :
    ∀ child ∈ observation.children, child ∈ subterms t := by
  cases t <;> simp only [constructorHead, Head.constructor.injEq] at found
  all_goals try cases found
  all_goals simp [subterms, self_mem_subterms]

def cycleRepresentative (index : Nat) (visited : List Nat) : Nat :=
  (visited.takeWhile (fun prior => prior != index)).foldl min index

/-- Every alias still available is either already visited or in the finite
remaining support. This makes exhaustion impossible by construction. -/
def Covers (assumptions : Assumptions) (visited remaining : List Nat) : Prop :=
  ∀ index body, assumptions.alias index = some body → index ∈ visited ∨ index ∈ remaining

theorem covers_step {assumptions : Assumptions} {visited remaining : List Nat}
    (covers : Covers assumptions visited remaining) (index : Nat) :
    Covers assumptions (index :: visited) (remaining.erase index) := by
  intro other body found
  by_cases same : other = index
  · exact Or.inl (by simp [same])
  · rcases covers other body found with seen | fresh
    · exact Or.inl (List.mem_cons_of_mem _ seen)
    · exact Or.inr ((List.mem_erase_of_ne same).mpr fresh)

/-- Each fresh alias removes one available key. The invariant ensures that a
fresh alias can always be removed, so this walk needs no arbitrary fuel case. -/
def exposeWalk (assumptions : Assumptions) (remaining visited : List Nat)
    (covers : Covers assumptions visited remaining) (t : Ty) : Head :=
  match t with
  | .variable index =>
    if seen : index ∈ visited then .unproductive (cycleRepresentative index visited)
    else match found : assumptions.alias index with
      | none => .nominal index
      | some body =>
        if body.isComputation then .nominal index
        else exposeWalk assumptions (remaining.erase index) (index :: visited)
          (covers_step covers index) body
  | t => constructorHead t
termination_by remaining.length
decreasing_by
  have fresh : index ∈ remaining := (covers index body found).resolve_left seen
  have positive := List.length_pos_of_mem fresh
  rw [List.length_erase_of_mem fresh]
  omega

theorem initial_covers (assumptions : Assumptions) :
    Covers assumptions [] (assumptions.bounds.map Prod.fst) := by
  intro index body found
  have bound := Assumptions.alias_bound found
  obtain ⟨pre, suffix, equal, _⟩ := List.lookup_eq_some_iff.mp bound
  right
  rw [equal]
  simp

/-- No caller-supplied fuel: the walk consumes the finite bound-key support. -/
def expose (assumptions : Assumptions) (t : Ty) : Head :=
  exposeWalk assumptions (assumptions.bounds.map Prod.fst) [] (initial_covers assumptions) t

theorem expose_rigid (assumptions : Assumptions) (index : Nat)
    (rigid : assumptions.rigid.contains index = true) :
    expose assumptions (.variable index) = .nominal index := by
  simp only [expose, exposeWalk, List.not_mem_nil, ↓reduceDIte]
  split <;> simp_all [Assumptions.alias]

theorem expose_without_alias (assumptions : Assumptions) (index : Nat)
    (absent : assumptions.alias index = none) :
    expose assumptions (.variable index) = .nominal index := by
  simp only [expose, exposeWalk, List.not_mem_nil, ↓reduceDIte]
  split <;> simp_all

/-- The activity barrier applies even to invalid assumption environments, as
in `Assumptions.unfoldHead`; it is not delegated to a caller's validity proof. -/
theorem expose_computation_alias (assumptions : Assumptions) (index : Nat) (body : Ty)
    (found : assumptions.alias index = some body) (activity : body.isComputation = true) :
    expose assumptions (.variable index) = .nominal index := by
  simp only [expose, exposeWalk, List.not_mem_nil, ↓reduceDIte]
  split <;> simp_all

theorem computation_alias_refused_probe :
    expose ⟨[(0, .computation .emptyRow .natural .natural)], [], []⟩ (.variable 0) =
      .nominal 0 := by
  simp [expose, exposeWalk, Assumptions.alias, constructorHead, cycleRepresentative, Ty.isComputation, List.lookup]

theorem productive_alias_probe :
    expose ⟨[(0, .arrow .once .affine (.variable 0) .natural)], [], []⟩ (.variable 0) =
      .constructor ⟨.arrow .once .affine, [.variable 0, .natural]⟩ := by
  simp [expose, exposeWalk, Assumptions.alias, constructorHead, cycleRepresentative, Ty.isComputation, List.lookup]

theorem unproductive_cycle_probe :
    expose ⟨[(0, .variable 1), (1, .variable 0)], [], []⟩ (.variable 0) =
      .unproductive 0 := by
  simp [expose, exposeWalk, Assumptions.alias, constructorHead, cycleRepresentative, Ty.isComputation, List.lookup]

theorem unproductive_cycle_same_class_probe :
    expose ⟨[(0, .variable 1), (1, .variable 0)], [], []⟩ (.variable 1) =
      .unproductive 0 := by
  simp [expose, exposeWalk, Assumptions.alias, constructorHead, cycleRepresentative, Ty.isComputation, List.lookup]

theorem cycle_prefix_probe :
    expose ⟨[(0, .variable 2), (2, .variable 3), (3, .variable 2)], [], []⟩ (.variable 0) =
      .unproductive 2 := by
  simp [expose, exposeWalk, Assumptions.alias, constructorHead, cycleRepresentative, Ty.isComputation, List.lookup]

theorem raw_field_observation (assumptions : Assumptions) (name : String) (member tail : Ty) :
    expose assumptions (.field name member tail) = .constructor ⟨.field name, [member, tail]⟩ := by
  simp [expose, exposeWalk, constructorHead]

#assert_axioms constructorHead_children subterms_trans support_subterms alias_mem_support self_mem_subterms left_mem_support right_mem_support bound_subterm_mem_support
  covers_step initial_covers expose_rigid expose_without_alias productive_alias_probe
  expose_computation_alias computation_alias_refused_probe
  unproductive_cycle_probe unproductive_cycle_same_class_probe cycle_prefix_probe raw_field_observation

/-- Alias exposure may leave the query root's syntax, but every disclosed
constructor child remains in the roots-and-bounds support. -/
public theorem exposeWalk_children_support
    (assumptions : Assumptions) (left right : Ty)
    (remaining visited : List Nat) (covers : Covers assumptions visited remaining)
    (t : Ty) (observation : Constructor)
    (present : t ∈ support assumptions left right)
    (observed : exposeWalk assumptions remaining visited covers t = .constructor observation) :
    ∀ child ∈ observation.children, child ∈ support assumptions left right := by
  cases t with
  | «variable» index =>
    by_cases seen : index ∈ visited
    · rw [exposeWalk] at observed
      simp [seen] at observed
    · cases found : assumptions.alias index with
      | none =>
        rw [exposeWalk] at observed
        simp only [seen, ↓reduceDIte] at observed
        split at observed <;> simp_all
      | some body =>
        rw [exposeWalk] at observed
        simp only [seen, ↓reduceDIte] at observed
        split at observed
        · rename_i absent
          rw [found] at absent
          contradiction
        · rename_i disclosed actual
          have same : disclosed = body := by
            rw [found] at actual
            exact Option.some.inj actual.symm
          subst disclosed
          split at observed
          · contradiction
          · exact exposeWalk_children_support assumptions left right
              (remaining.erase index) (index :: visited) (covers_step covers index)
              body observation (alias_mem_support found) observed
  | _ =>
    simp only [exposeWalk] at observed
    intro child inside
    exact support_subterms present (constructorHead_children _ observation observed child inside)
termination_by remaining.length
decreasing_by
  have fresh : index ∈ remaining := (covers index body found).resolve_left seen
  rw [List.length_erase_of_mem fresh]
  have positive := List.length_pos_of_mem fresh
  omega

public theorem expose_children_support
    {assumptions : Assumptions} {left right t : Ty} {observation : Constructor}
    (present : t ∈ support assumptions left right)
    (observed : expose assumptions t = .constructor observation) :
    ∀ child ∈ observation.children, child ∈ support assumptions left right :=
  exposeWalk_children_support assumptions left right _ [] (initial_covers assumptions)
    t observation present observed

#assert_axioms exposeWalk_children_support expose_children_support


/-- Every productive observation originates at an actual syntax node in the
query-and-bounds support, even when disclosure crossed several alias heads. -/
public theorem exposeWalk_origin
    (assumptions : Assumptions) (left right : Ty)
    (remaining visited : List Nat) (covers : Covers assumptions visited remaining)
    (t : Ty) (observation : Constructor)
    (present : t ∈ support assumptions left right)
    (observed : exposeWalk assumptions remaining visited covers t = .constructor observation) :
    ∃ source ∈ support assumptions left right, constructorHead source = .constructor observation := by
  cases t with
  | «variable» index =>
    by_cases seen : index ∈ visited
    · rw [exposeWalk] at observed
      simp [seen] at observed
    · cases found : assumptions.alias index with
      | none =>
        rw [exposeWalk] at observed
        simp only [seen, ↓reduceDIte] at observed
        split at observed <;> simp_all
      | some body =>
        rw [exposeWalk] at observed
        simp only [seen, ↓reduceDIte] at observed
        split at observed
        · rename_i absent
          rw [found] at absent
          contradiction
        · rename_i disclosed actual
          have same : disclosed = body := by
            rw [found] at actual
            exact Option.some.inj actual.symm
          subst disclosed
          split at observed
          · contradiction
          · exact exposeWalk_origin assumptions left right
              (remaining.erase index) (index :: visited) (covers_step covers index)
              body observation (alias_mem_support found) observed
  | _ =>
    simp only [exposeWalk] at observed
    exact ⟨_, present, observed⟩
termination_by remaining.length
decreasing_by
  have fresh : index ∈ remaining := (covers index body found).resolve_left seen
  rw [List.length_erase_of_mem fresh]
  have positive := List.length_pos_of_mem fresh
  omega

public theorem expose_origin
    {assumptions : Assumptions} {left right t : Ty} {observation : Constructor}
    (present : t ∈ support assumptions left right)
    (observed : expose assumptions t = .constructor observation) :
    ∃ source ∈ support assumptions left right, constructorHead source = .constructor observation :=
  exposeWalk_origin assumptions left right _ [] (initial_covers assumptions)
    t observation present observed

/-- A disclosed field's exact raw syntax occurs in the finite support. -/
public theorem expose_field_mem_support
    {assumptions : Assumptions} {left right t member tail : Ty} {name : String}
    (present : t ∈ support assumptions left right)
    (observed : expose assumptions t = .constructor ⟨.field name, [member, tail]⟩) :
    Ty.field name member tail ∈ support assumptions left right := by
  obtain ⟨source, sourcePresent, raw⟩ := expose_origin present observed
  cases source <;> simp_all [constructorHead]

#assert_axioms exposeWalk_origin expose_origin expose_field_mem_support


end Obend.Core.AliasExposure
end
