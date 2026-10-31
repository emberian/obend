module
/- Finite syntax support and productive alias-head observations.

This is a frontend scaffold, NOT a replacement for `sameType`. In particular,
raw fields are exposed as syntax constructors, NOT row equality observations.
No consumer may interpret this raw graph as canonical row equality. -/
public import Obend.Core.Assumptions
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


theorem takeWhile_before_repeat (index : Nat) (pre post : List Nat)
    (fresh : index ∉ pre) :
    (pre ++ index :: post).takeWhile (fun other => other != index) = pre := by
  induction pre with
  | nil => simp
  | cons other rest ih =>
    have different : other ≠ index := by
      intro equal
      apply fresh
      simp [equal]
    have tailFresh : index ∉ rest := fun present => fresh (List.mem_cons_of_mem _ present)
    simp [different, ih tailFresh]

public theorem cycleRepresentative_segment (index : Nat) (pre post : List Nat)
    (fresh : index ∉ pre) :
    cycleRepresentative index (pre ++ index :: post) = pre.foldl min index := by
  unfold cycleRepresentative
  rw [takeWhile_before_repeat index pre post fresh]

theorem foldl_min_seed (a b : Nat) (xs : List Nat) :
    xs.foldl min (min a b) = min a (xs.foldl min b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [Nat.min_assoc, ih]

/-- Rotating a finite cycle changes its starting variable, but not its minimum.
This is the algebraic step needed when two fresh walks detect that cycle at
different vertices. -/
public theorem cycle_min_rotate (first last : Nat) (middle : List Nat) :
    (first :: middle).foldl min last = (middle ++ [last]).foldl min first := by
  simp only [List.foldl_cons, List.foldl_append, List.foldl_nil]
  rw [foldl_min_seed]
  exact Nat.min_comm _ _

/-- A forward path records exactly the alias variables expanded, and stops
before expanding its final type. -/
public inductive AliasChain (assumptions : Assumptions) : Ty → List Nat → Ty → Prop where
  | nil (t : Ty) : AliasChain assumptions t [] t
  | cons {index : Nat} {body finish : Ty} {path : List Nat} :
      assumptions.alias index = some body → body.isComputation = false →
      AliasChain assumptions body path finish →
      AliasChain assumptions (.variable index) (index :: path) finish

@[expose] public def erasePath (remaining : List Nat) : List Nat → List Nat
  | [] => remaining
  | index :: path => erasePath (remaining.erase index) path

@[expose] public def visitPath (visited : List Nat) : List Nat → List Nat
  | [] => visited
  | index :: path => visitPath (index :: visited) path

@[expose] public def pathCovers (assumptions : Assumptions) (remaining visited : List Nat)
    (covers : Covers assumptions visited remaining) :
    (path : List Nat) → Covers assumptions (visitPath visited path) (erasePath remaining path)
  | [] => covers
  | index :: path => pathCovers assumptions (remaining.erase index) (index :: visited)
      (covers_step covers index) path

public theorem visitPath_reverse (visited path : List Nat) :
    visitPath visited path = path.reverse ++ visited := by
  induction path generalizing visited with
  | nil => rfl
  | cons index path ih =>
    simp [visitPath, ih, List.reverse_cons, List.append_assoc]

/-- A valid fresh path can be replayed under any compatible visited prefix.
This supplies the operational part of rotating a discovered alias cycle. -/
public theorem exposeWalk_replay
    {assumptions : Assumptions} {start finish : Ty} {path : List Nat}
    (chain : AliasChain assumptions start path finish)
    (distinct : path.Nodup)
    (remaining visited : List Nat) (covers : Covers assumptions visited remaining)
    (fresh : ∀ index ∈ path, index ∉ visited) :
    exposeWalk assumptions remaining visited covers start =
      exposeWalk assumptions (erasePath remaining path) (visitPath visited path)
        (pathCovers assumptions remaining visited covers path) finish := by
  induction chain generalizing remaining visited with
  | nil => rfl
  | @cons index body finish path found pure chain ih =>
    have notVisited : index ∉ visited := fresh index (by simp)
    have tailDistinct : path.Nodup := (List.nodup_cons.mp distinct).2
    have notInTail : index ∉ path := (List.nodup_cons.mp distinct).1
    have tailFresh : ∀ other ∈ path, other ∉ index :: visited := by
      intro other inside present
      rcases List.mem_cons.mp present with same | old
      · subst other
        exact notInTail inside
      · exact fresh other (List.mem_cons_of_mem _ inside) old
    rw [exposeWalk]
    simp only [notVisited, ↓reduceDIte]
    split
    · rename_i absent
      rw [found] at absent
      contradiction
    · rename_i disclosed actual
      have same : disclosed = body := by
        rw [found] at actual
        exact Option.some.inj actual.symm
      subst disclosed
      simp only [pure, Bool.false_eq_true, ↓reduceIte]
      exact ih tailDistinct (remaining.erase index) (index :: visited)
        (covers_step covers index) tailFresh

/-- A stopped orbit either reaches a productive head, a terminal nominal
variable, or a repeated variable whose actual cycle supplies the minimum. -/
public inductive Stopped (assumptions : Assumptions) (visited : List Nat) : Ty → Head → Prop where
  | productive (t : Ty) : (∀ index, t ≠ .variable index) →
      Stopped assumptions visited t (constructorHead t)
  | unbound {index : Nat} : index ∉ visited → assumptions.alias index = none →
      Stopped assumptions visited (.variable index) (.nominal index)
  | activity {index : Nat} {body : Ty} : index ∉ visited →
      assumptions.alias index = some body → body.isComputation = true →
      Stopped assumptions visited (.variable index) (.nominal index)
  | cycle {index : Nat} : index ∈ visited →
      Stopped assumptions visited (.variable index)
        (.unproductive (cycleRepresentative index visited))

/-- Every finite exposure has a fresh, repetition-free deterministic path to
its stopping point. This records the path needed for replay/rotation proofs. -/
public theorem exposeWalk_trace
    (assumptions : Assumptions) (remaining visited : List Nat)
    (covers : Covers assumptions visited remaining) (t : Ty) :
    ∃ path finish,
      AliasChain assumptions t path finish ∧ path.Nodup ∧
      (∀ index ∈ path, index ∉ visited) ∧
      Stopped assumptions (visitPath visited path) finish
        (exposeWalk assumptions remaining visited covers t) := by
  cases t with
  | «variable» index =>
    by_cases seen : index ∈ visited
    · refine ⟨[], .variable index, .nil _, by simp, by simp, ?_⟩
      simp only [visitPath, exposeWalk, seen, ↓reduceDIte]
      exact .cycle seen
    · cases found : assumptions.alias index with
      | none =>
        have terminal : exposeWalk assumptions remaining visited covers (.variable index) = .nominal index := by
          rw [exposeWalk]
          simp only [seen, ↓reduceDIte]
          split <;> simp_all
        refine ⟨[], .variable index, .nil _, by simp, by simp, ?_⟩
        simpa only [visitPath, terminal] using (Stopped.unbound seen found)
      | some body =>
        by_cases blocked : body.isComputation = true
        · have terminal : exposeWalk assumptions remaining visited covers (.variable index) = .nominal index := by
            rw [exposeWalk]
            simp only [seen, ↓reduceDIte]
            split <;> simp_all
          refine ⟨[], .variable index, .nil _, by simp, by simp, ?_⟩
          simpa only [visitPath, terminal] using (Stopped.activity seen found blocked)
        · have pure : body.isComputation = false := by cases h : body.isComputation <;> simp_all
          obtain ⟨path, finish, chain, distinct, fresh, stopped⟩ :=
            exposeWalk_trace assumptions (remaining.erase index) (index :: visited)
              (covers_step covers index) body
          have notInPath : index ∉ path := by
            intro present
            exact fresh index present (by simp)
          have pathFresh : ∀ other ∈ index :: path, other ∉ visited := by
            intro other present
            rcases List.mem_cons.mp present with same | nested
            · simpa only [same] using seen
            · intro old
              exact fresh other nested (List.mem_cons_of_mem _ old)
          have stepped := exposeWalk_replay
            (AliasChain.cons found pure (AliasChain.nil body)) (by simp)
            remaining visited covers (by simpa using seen)
          simp only [erasePath, visitPath] at stepped
          refine ⟨index :: path, finish, .cons found pure chain,
            List.nodup_cons.mpr ⟨notInPath, distinct⟩, pathFresh, ?_⟩
          simpa only [visitPath, stepped] using stopped
  | _ =>
    refine ⟨[], _, .nil _, by simp, by simp, ?_⟩
    simp only [visitPath, exposeWalk]
    apply Stopped.productive
    intro index impossible
    cases impossible
termination_by remaining.length
decreasing_by
  have fresh : index ∈ remaining := (covers index body found).resolve_left seen
  rw [List.length_erase_of_mem fresh]
  have positive := List.length_pos_of_mem fresh
  omega

theorem chain_uncons {assumptions : Assumptions} {index : Nat} {path : List Nat} {finish : Ty}
    (chain : AliasChain assumptions (.variable index) path finish) :
    (path = [] ∧ finish = .variable index) ∨
      ∃ body rest, assumptions.alias index = some body ∧ body.isComputation = false ∧
        path = index :: rest ∧ AliasChain assumptions body rest finish := by
  cases chain with
  | nil => exact .inl ⟨rfl, rfl⟩
  | cons found pure tail => exact .inr ⟨_, _, found, pure, rfl, tail⟩

theorem chain_append {assumptions : Assumptions} {start middle finish : Ty} {pre post : List Nat}
    (one : AliasChain assumptions start pre middle)
    (two : AliasChain assumptions middle post finish) :
    AliasChain assumptions start (pre ++ post) finish := by
  induction one with
  | nil => exact two
  | cons found pure tail ih => exact .cons found pure (ih two)

theorem chain_nonempty_start {assumptions : Assumptions} {start finish : Ty}
    {index : Nat} {rest : List Nat} (chain : AliasChain assumptions start (index :: rest) finish) :
    start = .variable index := by
  cases chain
  rfl

theorem takeWhile_append_after_repeat (index : Nat) (pre post : List Nat)
    (repeated : index ∈ pre) :
    (pre ++ post).takeWhile (fun other => other != index) =
      pre.takeWhile (fun other => other != index) := by
  induction pre with
  | nil => simp at repeated
  | cons other rest ih =>
    by_cases same : other = index
    · subst other
      simp
    · have inside : index ∈ rest := by simpa [same, Ne.symm same] using repeated
      have comparison : (other != index) = true := by simp [same]
      simp [List.takeWhile, comparison, ih inside]

theorem exposeWalk_seen (assumptions : Assumptions) (remaining visited : List Nat)
    (covers : Covers assumptions visited remaining) (index : Nat) (seen : index ∈ visited) :
    exposeWalk assumptions remaining visited covers (.variable index) =
      .unproductive (cycleRepresentative index visited) := by
  rw [exposeWalk]
  simp only [seen, ↓reduceDIte]

theorem exposeWalk_unbound (assumptions : Assumptions) (remaining visited : List Nat)
    (covers : Covers assumptions visited remaining) (index : Nat)
    (fresh : index ∉ visited) (absent : assumptions.alias index = none) :
    exposeWalk assumptions remaining visited covers (.variable index) = .nominal index := by
  rw [exposeWalk]
  simp only [fresh, ↓reduceDIte]
  split <;> simp_all

theorem exposeWalk_activity (assumptions : Assumptions) (remaining visited : List Nat)
    (covers : Covers assumptions visited remaining) (index : Nat) (body : Ty)
    (fresh : index ∉ visited) (found : assumptions.alias index = some body)
    (blocked : body.isComputation = true) :
    exposeWalk assumptions remaining visited covers (.variable index) = .nominal index := by
  rw [exposeWalk]
  simp only [fresh, ↓reduceDIte]
  split <;> simp_all

/-- Productive heads do not consult the visitation history. This is the base
case needed by an orbit proof of general one-alias invariance. -/
public theorem exposeWalk_nonvariable
    (assumptions : Assumptions) (remaining visited : List Nat)
    (covers : Covers assumptions visited remaining) (t : Ty)
    (nonvariable : ∀ index, t ≠ .variable index) :
    exposeWalk assumptions remaining visited covers t = constructorHead t := by
  cases t with
  | «variable» index => exact False.elim (nonvariable index rfl)
  | _ => simp only [exposeWalk]

public theorem expose_nonvariable
    (assumptions : Assumptions) (t : Ty)
    (nonvariable : ∀ index, t ≠ .variable index) :
    expose assumptions t = constructorHead t :=
  exposeWalk_nonvariable assumptions _ [] (initial_covers assumptions) t nonvariable


/-- Full one-step alias invariance, including incoming alias prefixes and
head-only cycles. Fresh traces supply the actual cycle, whose minimum is
unchanged when the starting edge rotates it. -/
public theorem expose_alias (assumptions : Assumptions) (index : Nat) (body : Ty)
    (found : assumptions.alias index = some body) (pure : body.isComputation = false) :
    expose assumptions (.variable index) = expose assumptions body := by
  obtain ⟨path, finish, chain, distinct, fresh, stopped⟩ :=
    exposeWalk_trace assumptions (assumptions.bounds.map Prod.fst) []
      (initial_covers assumptions) (.variable index)
  change Stopped assumptions (visitPath [] path) finish
    (expose assumptions (.variable index)) at stopped
  rcases chain_uncons chain with ⟨empty, ending⟩ | ⟨disclosed, rest, actual, _, pathEq, bodyChain⟩
  · subst path
    subst finish
    generalize terminalOutput : expose assumptions (.variable index) = terminal at stopped
    cases stopped <;> simp_all [visitPath]
  · have same : disclosed = body := Option.some.inj (actual.symm.trans found)
    subst disclosed
    subst path
    have restDistinct : rest.Nodup := (List.nodup_cons.mp distinct).2
    have rootNotInRest : index ∉ rest := (List.nodup_cons.mp distinct).1
    have replay := exposeWalk_replay bodyChain restDistinct
      (assumptions.bounds.map Prod.fst) [] (initial_covers assumptions) (by simp)
    change expose assumptions body =
      exposeWalk assumptions _ (visitPath [] rest) _ finish at replay
    generalize rootOutput : expose assumptions (.variable index) = result at stopped ⊢
    cases stopped with
    | productive terminal nonvariable =>
      rw [replay, exposeWalk_nonvariable assumptions _ _ _ _ nonvariable]
    | @unbound terminal stopFresh absent =>
      have bodyFresh : terminal ∉ visitPath [] rest := by
        intro inside
        apply stopFresh
        simpa [visitPath_reverse, or_comm] using
          (List.mem_cons_of_mem index (by simpa [visitPath_reverse] using inside))
      rw [replay, exposeWalk_unbound assumptions _ _ _ terminal bodyFresh absent]
    | @activity terminal activityBody stopFresh activityFound blocked =>
      have bodyFresh : terminal ∉ visitPath [] rest := by
        intro inside
        apply stopFresh
        simpa [visitPath_reverse, or_comm] using
          (List.mem_cons_of_mem index (by simpa [visitPath_reverse] using inside))
      rw [replay, exposeWalk_activity assumptions _ _ _ terminal activityBody
        bodyFresh activityFound blocked]
    | @cycle terminal repeated =>
      have position : terminal = index ∨ terminal ∈ rest := by
        simpa [visitPath_reverse, or_comm] using repeated
      rcases position with atRoot | inRest
      · subst terminal
        cases rest with
        | nil =>
          cases bodyChain
          exact rootOutput.symm
        | cons first middle =>
          have bodyEq := chain_nonempty_start bodyChain
          subst body
          have rotatedChain := chain_append bodyChain
            (AliasChain.cons found pure (AliasChain.nil (.variable first)))
          have rotatedDistinct : ((first :: middle) ++ [index]).Nodup := by
            apply List.nodup_append.mpr
            refine ⟨restDistinct, by simp, ?_⟩
            intro a inside b singleton same
            have last : b = index := by simpa using singleton
            subst b
            subst a
            exact rootNotInRest inside
          have rotatedReplay := exposeWalk_replay rotatedChain rotatedDistinct
            (assumptions.bounds.map Prod.fst) [] (initial_covers assumptions) (by simp)
          change expose assumptions (.variable first) =
            exposeWalk assumptions _ (visitPath [] ((first :: middle) ++ [index])) _
              (.variable first) at rotatedReplay
          have rotatedSeen : first ∈ visitPath [] ((first :: middle) ++ [index]) := by
            simp [visitPath_reverse]
          rw [rotatedReplay, exposeWalk_seen assumptions _ _ _ first rotatedSeen]
          have originalMinimum :
              cycleRepresentative index (visitPath [] (index :: first :: middle)) =
                (first :: middle).reverse.foldl min index := by
            rw [visitPath_reverse]
            simp only [List.reverse_cons, List.append_nil]
            simpa only [List.reverse_cons] using
              (cycleRepresentative_segment index ((first :: middle).reverse) []
                (by simpa [and_comm] using rootNotInRest))
          have rotatedFresh : first ∉ index :: middle.reverse := by
            intro inside
            rcases List.mem_cons.mp inside with same | nested
            · have rootOccurs : index ∈ first :: middle := by simp [← same]
              exact rootNotInRest rootOccurs
            · exact (List.nodup_cons.mp restDistinct).1 (by simpa using nested)
          have rotatedMinimum :
              cycleRepresentative first (visitPath [] ((first :: middle) ++ [index])) =
                (index :: middle.reverse).foldl min first := by
            rw [visitPath_reverse]
            simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
              List.append_nil, List.cons_append, List.nil_append]
            exact cycleRepresentative_segment first (index :: middle.reverse) [] rotatedFresh
          rw [originalMinimum, rotatedMinimum]
          congr 1
          simpa only [List.reverse_cons] using (cycle_min_rotate index first middle.reverse).symm
      · have bodySeen : terminal ∈ visitPath [] rest := by
          simpa [visitPath_reverse] using inRest
        rw [replay, exposeWalk_seen assumptions _ _ _ terminal bodySeen]
        congr 1
        simp only [cycleRepresentative, visitPath_reverse, List.reverse_cons, List.append_nil]
        rw [takeWhile_append_after_repeat terminal rest.reverse [index]
          (by simpa using inRest)]

/-- One-step invariance for aliases already naming a productive constructor.
The general theorem must additionally handle variable-to-variable paths and
rotation of the minimum representative of head-only cycles. -/
public theorem expose_alias_nonvariable
    (assumptions : Assumptions) (index : Nat) (body : Ty)
    (found : assumptions.alias index = some body)
    (pure : body.isComputation = false)
    (nonvariable : ∀ other, body ≠ .variable other) :
    expose assumptions (.variable index) = expose assumptions body := by
  rw [expose_nonvariable assumptions body nonvariable]
  unfold expose
  rw [exposeWalk]
  simp only [List.not_mem_nil, ↓reduceDIte]
  split
  · rename_i absent
    rw [found] at absent
    contradiction
  · rename_i disclosed actual
    have same : disclosed = body := by
      rw [found] at actual
      exact Option.some.inj actual.symm
    subst disclosed
    simp only [pure, Bool.false_eq_true, ↓reduceIte]
    exact exposeWalk_nonvariable assumptions _ _ _ body nonvariable


end Obend.Core.AliasExposure
end
