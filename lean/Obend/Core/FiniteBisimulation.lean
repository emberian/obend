module
/- A finite deterministic graph kernel. The frontend must expose productive
observations before using this module: an edge is a constructor child, never an
unproductive alias-unfolding obligation. No user-supplied fuel is involved. -/
public import Lean
public import Obend.AxiomPin
@[expose] public section
namespace Obend.Core.FiniteBisimulation
set_option autoImplicit false

structure Graph (Label : Type) (n : Nat) where
  label : Fin n → Label
  successors : Fin n → List (Fin n)

/-- Pointwise related lists, including equality of arity. -/
def Children {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | x :: xs, y :: ys => R x y ∧ Children R xs ys
  | _, _ => False

instance childrenDecidable {α : Type} (R : α → α → Prop)
    [DecidableRel R] (xs ys : List α) : Decidable (Children R xs ys) := by
  cases xs with
  | nil => cases ys <;> unfold Children <;> infer_instance
  | cons x xs =>
    cases ys with
    | nil => unfold Children; infer_instance
    | cons y ys =>
      have : Decidable (Children R xs ys) := childrenDecidable R xs ys
      unfold Children
      infer_instance

theorem children_mono {α : Type} {R S : α → α → Prop}
    (imp : ∀ x y, R x y → S x y) {xs ys : List α}
    (h : Children R xs ys) : Children S xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> exact h
  | cons x xs ih =>
    cases ys with
    | nil => exact h
    | cons y ys => exact ⟨imp x y h.1, ih h.2⟩

theorem children_refl {α : Type} (xs : List α) : Children Eq xs xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨rfl, ih⟩

theorem children_symm {α : Type} {R : α → α → Prop} {xs ys : List α}
    (h : Children R xs ys) : Children (fun x y => R y x) ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> exact h
  | cons x xs ih =>
    cases ys with
    | nil => exact h
    | cons y ys => exact ⟨h.1, ih h.2⟩

theorem children_comp {α : Type} {R S : α → α → Prop}
    {xs ys zs : List α} (one : Children R xs ys) (two : Children S ys zs) :
    Children (fun x z => ∃ y, R x y ∧ S y z) xs zs := by
  induction xs generalizing ys zs with
  | nil =>
    cases ys with
    | nil => cases zs <;> exact two
    | cons y ys => exact False.elim one
  | cons x xs ih =>
    cases ys with
    | nil => exact False.elim one
    | cons y ys =>
      cases zs with
      | nil => exact False.elim two
      | cons z zs => exact ⟨⟨y,one.1,two.1⟩,ih one.2 two.2⟩

def Bisimulation {Label : Type} {n : Nat} (g : Graph Label n)
    (R : Fin n → Fin n → Prop) : Prop :=
  ∀ x y, R x y → g.label x = g.label y ∧ Children R (g.successors x) (g.successors y)

/-- Membership in some closed relation; the relation need not be decidable. -/
def Bisimilar {Label : Type} {n : Nat} (g : Graph Label n) (x y : Fin n) : Prop :=
  ∃ R, Bisimulation g R ∧ R x y

theorem bisimilar_refl {Label : Type} {n : Nat} (g : Graph Label n) (x : Fin n) :
    Bisimilar g x x := by
  refine ⟨Eq, ?_, rfl⟩
  intro a b h
  subst b
  exact ⟨rfl, children_refl _⟩

theorem bisimilar_symm {Label : Type} {n : Nat} {g : Graph Label n} {x y : Fin n}
    (h : Bisimilar g x y) : Bisimilar g y x := by
  obtain ⟨R,closed,related⟩ := h
  refine ⟨fun a b => R b a, ?_, related⟩
  intro a b h
  obtain ⟨labels,children⟩ := closed b a h
  exact ⟨labels.symm,children_symm children⟩

theorem bisimilar_trans {Label : Type} {n : Nat} {g : Graph Label n} {x y z : Fin n}
    (one : Bisimilar g x y) (two : Bisimilar g y z) : Bisimilar g x z := by
  obtain ⟨R,rc,hr⟩ := one
  obtain ⟨S,sc,hs⟩ := two
  refine ⟨fun a c => ∃ b, R a b ∧ S b c, ?_, ⟨y,hr,hs⟩⟩
  intro a c h
  obtain ⟨b,hab,hbc⟩ := h
  obtain ⟨lab,cab⟩ := rc a b hab
  obtain ⟨lbc,cbc⟩ := sc b c hbc
  exact ⟨lab.trans lbc, children_comp cab cbc⟩

theorem bisimilar_equivalence {Label : Type} {n : Nat} (g : Graph Label n) :
    Equivalence (Bisimilar g) :=
  ⟨bisimilar_refl g, bisimilar_symm, bisimilar_trans⟩

abbrev Pair (n : Nat) := Fin n × Fin n

def InRelation {n : Nat} (pairs : List (Pair n)) (x y : Fin n) : Prop :=
  (x,y) ∈ pairs

instance {n : Nat} (pairs : List (Pair n)) : DecidableRel (InRelation pairs) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ pairs))

/-- One simultaneous deletion round. A pair survives only if its observations
agree and every corresponding child pair remains a candidate. -/
def prune {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (pairs : List (Pair n)) : List (Pair n) :=
  pairs.filter (fun p => decide (g.label p.1 = g.label p.2 ∧
    Children (InRelation pairs) (g.successors p.1) (g.successors p.2)))

theorem mem_prune {Label : Type} [DecidableEq Label] {n : Nat} {g : Graph Label n}
    {pairs : List (Pair n)} {x y : Fin n} :
    InRelation (prune g pairs) x y ↔ InRelation pairs x y ∧
      g.label x = g.label y ∧ Children (InRelation pairs) (g.successors x) (g.successors y) := by
  simp [prune,InRelation]

theorem prune_subset {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (pairs : List (Pair n)) : ∀ x y, InRelation (prune g pairs) x y → InRelation pairs x y := by
  intro x y h
  exact (mem_prune.mp h).1

theorem prune_decreases {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (pairs : List (Pair n)) (different : prune g pairs ≠ pairs) :
    (prune g pairs).length < pairs.length := by
  have sub : List.Sublist (prune g pairs) pairs := List.filter_sublist
  have le := sub.length_le
  have ne : (prune g pairs).length ≠ pairs.length := fun h => different (sub.eq_of_length h)
  omega

/-- The data is the computed relation; all other fields erase. The greatest
property quantifies over arbitrary mathematical relations, not just lists. -/
structure Solution {Label : Type} {n : Nat} (g : Graph Label n) (initial : List (Pair n)) where
  pairs : List (Pair n)
  subset : ∀ x y, InRelation pairs x y → InRelation initial x y
  closed : Bisimulation g (InRelation pairs)
  greatest : ∀ R, Bisimulation g R →
    (∀ x y, R x y → InRelation initial x y) →
    ∀ x y, R x y → InRelation pairs x y

/-- Refine to a fixed point. Every nonterminal recursive call strictly removes
a candidate. Starting from all pairs therefore takes at most n*n such rounds. -/
def refine {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (initial : List (Pair n)) : Solution g initial :=
  if fixed : prune g initial = initial then
    { pairs := initial
      subset := fun _ _ h => h
      closed := by
        intro x y h
        have hp : InRelation (prune g initial) x y := fixed.symm ▸ h
        exact (mem_prune.mp hp).2
      greatest := fun _ _ contained => contained }
  else
    let next := refine g (prune g initial)
    { pairs := next.pairs
      subset := fun x y h => prune_subset g initial x y (next.subset x y h)
      closed := next.closed
      greatest := by
        intro R closed contained
        apply next.greatest R closed
        intro x y related
        obtain ⟨labels,children⟩ := closed x y related
        exact mem_prune.mpr ⟨contained x y related,labels,
          children_mono contained children⟩ }
termination_by initial.length
decreasing_by exact prune_decreases g initial fixed

def allPairs (n : Nat) : List (Pair n) :=
  (List.finRange n).flatMap (fun x => (List.finRange n).map (fun y => (x,y)))

theorem mem_allPairs {n : Nat} (x y : Fin n) : InRelation (allPairs n) x y := by
  apply List.mem_flatMap.mpr
  refine ⟨x,List.mem_finRange x,?_⟩
  exact List.mem_map.mpr ⟨y,List.mem_finRange y,rfl⟩

theorem allPairs_length (n : Nat) : (allPairs n).length = n * n := by
  have count (nodes : List (Fin n)) :
      (nodes.flatMap (fun x => (List.finRange n).map (fun y => (x,y)))).length =
        nodes.length * n := by
    induction nodes with
    | nil => simp
    | cons x xs ih => simp [List.flatMap_cons,ih,Nat.add_mul,Nat.add_comm]
  simpa [allPairs] using count (List.finRange n)

def greatest {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n) :
    Solution g (allPairs n) := refine g (allPairs n)

def same {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (x y : Fin n) : Bool := decide (InRelation (greatest g).pairs x y)

theorem same_iff {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (x y : Fin n) : same g x y = true ↔ Bisimilar g x y := by
  simp only [same,decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨InRelation (greatest g).pairs,(greatest g).closed,h⟩
  · intro h
    obtain ⟨R,closed,related⟩ := h
    exact (greatest g).greatest R closed (fun a b _ => mem_allPairs a b) x y related

theorem same_equivalence {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n) :
    Equivalence (fun x y => same g x y = true) := by
  refine ⟨?_,?_,?_⟩
  · intro x; exact (same_iff g x x).mpr (bisimilar_refl g x)
  · intro x y h; exact (same_iff g y x).mpr (bisimilar_symm ((same_iff g x y).mp h))
  · intro x y z one two
    exact (same_iff g x z).mpr (bisimilar_trans ((same_iff g x y).mp one) ((same_iff g y z).mp two))

instance {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n) (x y : Fin n) :
    Decidable (Bisimilar g x y) :=
  decidable_of_iff (same g x y = true) (same_iff g x y)

theorem children_iff_zip {α : Type} {R : α → α → Prop} (xs ys : List α) :
    Children R xs ys ↔ xs.length = ys.length ∧ ∀ p ∈ xs.zip ys, R p.1 p.2 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [Children]
  | cons x xs ih =>
    cases ys with
    | nil => simp [Children]
    | cons y ys =>
      simp only [Children,List.length_cons,Nat.succ.injEq,List.zip_cons_cons,
        List.mem_cons,forall_eq_or_imp,ih]
      constructor
      · intro h; exact ⟨h.2.1,h.1,h.2.2⟩
      · intro h; exact ⟨h.2.1,h.1,h.2.2⟩

/-- Every pair in an obligation list lies in one common bisimulation. -/
def Covered {Label : Type} {n : Nat} (g : Graph Label n) (obligations : List (Pair n)) : Prop :=
  ∃ R, Bisimulation g R ∧ ∀ p ∈ obligations, R p.1 p.2

def VisitedInvariant {Label : Type} {n : Nat} (g : Graph Label n)
    (visited pending : List (Pair n)) : Prop :=
  ∀ p ∈ visited, g.label p.1 = g.label p.2 ∧
    Children (fun x y => InRelation visited x y ∨ InRelation pending x y)
      (g.successors p.1) (g.successors p.2)

theorem covered_advance {Label : Type} {n : Nat} (g : Graph Label n)
    (visited : List (Pair n)) (p : Pair n) (pending : List (Pair n)) :
    Covered g (visited ++ p :: pending) ↔
    Covered g ((p :: visited) ++ ((g.successors p.1).zip (g.successors p.2) ++ pending)) := by
  constructor
  · rintro ⟨R,closed,contains⟩
    have root : R p.1 p.2 := contains p (by simp)
    have children := (children_iff_zip _ _).mp (closed _ _ root).2
    refine ⟨R,closed,?_⟩
    intro q hq
    rcases List.mem_append.mp hq with seen | queued
    · rcases List.mem_cons.mp seen with equal | old
      · simpa [equal] using root
      · exact contains q (by simp [old])
    · rcases List.mem_append.mp queued with child | rest
      · exact children.2 q child
      · exact contains q (by simp [rest])
  · rintro ⟨R,closed,contains⟩
    refine ⟨R,closed,?_⟩
    intro q hq
    simp only [List.mem_append,List.mem_cons] at hq
    rcases hq with old | rfl | rest
    · exact contains q (by simp [old])
    · exact contains q (by simp)
    · exact contains q (by simp [rest])

theorem covered_skip {Label : Type} {n : Nat} (g : Graph Label n)
    (visited : List (Pair n)) (p : Pair n) (pending : List (Pair n)) (seen : p ∈ visited) :
    Covered g (visited ++ p :: pending) ↔ Covered g (visited ++ pending) := by
  constructor
  · rintro ⟨R,closed,contains⟩
    refine ⟨R,closed,?_⟩
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with old | rest
    · exact contains q (by simp [old])
    · exact contains q (by simp [rest])
  · rintro ⟨R,closed,contains⟩
    refine ⟨R,closed,?_⟩
    intro q hq
    simp only [List.mem_append,List.mem_cons] at hq
    rcases hq with old | rfl | rest
    · exact contains q (by simp [old])
    · exact contains q (by simp [seen])
    · exact contains q (by simp [rest])

theorem visited_advance {Label : Type} {n : Nat} {g : Graph Label n}
    {visited pending : List (Pair n)} {p : Pair n}
    (valid : VisitedInvariant g visited (p :: pending))
    (labels : g.label p.1 = g.label p.2)
    (arity : (g.successors p.1).length = (g.successors p.2).length) :
    VisitedInvariant g (p :: visited) ((g.successors p.1).zip (g.successors p.2) ++ pending) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | old
  · refine ⟨labels,(children_iff_zip _ _).mpr ⟨arity,?_⟩⟩
    intro child hc
    exact Or.inr (List.mem_append_left _ hc)
  · obtain ⟨equal,children⟩ := valid q old
    refine ⟨equal,children_mono ?_ children⟩
    intro a b h
    rcases h with hv | hp
    · exact Or.inl (List.mem_cons_of_mem p hv)
    · rcases List.mem_cons.mp hp with root | rest
      · exact Or.inl (List.mem_cons.mpr (Or.inl root))
      · exact Or.inr (List.mem_append_right _ rest)

theorem visited_skip {Label : Type} {n : Nat} {g : Graph Label n}
    {visited pending : List (Pair n)} {p : Pair n}
    (valid : VisitedInvariant g visited (p :: pending)) (seen : p ∈ visited) :
    VisitedInvariant g visited pending := by
  intro q hq
  obtain ⟨equal,children⟩ := valid q hq
  refine ⟨equal,children_mono ?_ children⟩
  intro a b h
  rcases h with hv | hp
  · exact Or.inl hv
  · rcases List.mem_cons.mp hp with root | rest
    · apply Or.inl
      show (a,b) ∈ visited
      rw [root]
      exact seen
    · exact Or.inr rest

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α]
    (xs ys : List α) (distinct : xs.Nodup) (contained : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨fresh,tailDistinct⟩ := List.nodup_cons.mp distinct
    have member : a ∈ ys := contained a (by simp)
    have tailContained : ∀ x ∈ xs, x ∈ ys.erase a := by
      intro x hx
      have unequal : x ≠ a := by
        intro same
        subst x
        exact fresh hx
      exact (List.mem_erase_of_ne unequal).mpr (contained x (List.mem_cons_of_mem a hx))
    have bounded := ih (ys.erase a) tailDistinct tailContained
    have removed := List.length_erase_of_mem member
    have positive := List.length_pos_of_mem member
    simp only [List.length_cons]
    omega

theorem visited_length_le {n : Nat} (visited : List (Pair n)) (distinct : visited.Nodup) :
    visited.length ≤ n * n := by
  have bound := nodup_length_le_of_subset visited (allPairs n) distinct
    (fun pair _ => mem_allPairs pair.1 pair.2)
  simpa only [allPairs_length] using bound

/-- A revisit checks only the sparse visited list. A fresh pair must expose
matching constructors before its successors are queued. The cardinality proof
and no-duplicate invariant erase; no `allPairs` list is allocated. -/
def worklist {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (visited pending : List (Pair n)) (distinct : visited.Nodup)
    (valid : VisitedInvariant g visited pending) : Decidable (Covered g (visited ++ pending)) :=
  match pending with
  | [] => .isTrue (by
      refine ⟨InRelation visited,?_,?_⟩
      · intro x y h
        obtain ⟨labels,children⟩ := valid (x,y) h
        refine ⟨labels,children_mono ?_ children⟩
        intro a b h
        rcases h with seen | impossible
        · exact seen
        · exact False.elim (by simpa [InRelation] using impossible)
      · intro p hp; simpa [InRelation] using hp)
  | p :: pending =>
    if seen : p ∈ visited then
      letI : Decidable (Covered g (visited ++ pending)) :=
        worklist g visited pending distinct (visited_skip valid seen)
      decidable_of_iff _ (covered_skip g visited p pending seen).symm
    else
      if compatible : g.label p.1 = g.label p.2 ∧
          (g.successors p.1).length = (g.successors p.2).length then
        let nextDistinct : (p :: visited).Nodup := List.nodup_cons.mpr ⟨seen,distinct⟩
        letI : Decidable (Covered g ((p :: visited) ++
            ((g.successors p.1).zip (g.successors p.2) ++ pending))) :=
          worklist g (p :: visited)
            ((g.successors p.1).zip (g.successors p.2) ++ pending) nextDistinct
            (visited_advance valid compatible.1 compatible.2)
        decidable_of_iff _ (covered_advance g visited p pending).symm
      else .isFalse (by
        rintro ⟨R,closed,contains⟩
        obtain ⟨labels,children⟩ := closed _ _ (contains p (by simp))
        exact compatible ⟨labels,((children_iff_zip _ _).mp children).1⟩)
termination_by (n * n - visited.length,pending.length)
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have unseen : p ∉ visited := by assumption
      have bound := visited_length_le (p :: visited) (List.nodup_cons.mpr ⟨unseen,distinct⟩)
      simp only [List.length_cons] at bound
      omega

def visitedSame {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (x y : Fin n) : Bool :=
  letI : Decidable (Covered g ([] ++ [(x,y)])) :=
    worklist g [] [(x,y)] (by simp) (by intro p hp; simp at hp)
  decide (Covered g ([] ++ [(x,y)]))

theorem visitedSame_iff {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (x y : Fin n) : visitedSame g x y = true ↔ Bisimilar g x y := by
  simp only [visitedSame,decide_eq_true_eq]
  constructor
  · rintro ⟨R,closed,contains⟩
    exact ⟨R,closed,contains (x,y) (by simp)⟩
  · rintro ⟨R,closed,related⟩
    refine ⟨R,closed,?_⟩
    intro p hp
    have equal : p = (x,y) := by simpa using hp
    subst p
    exact related

theorem visitedSame_eq_same {Label : Type} [DecidableEq Label] {n : Nat}
    (g : Graph Label n) (x y : Fin n) : visitedSame g x y = same g x y := by
  cases one : visitedSame g x y <;> cases two : same g x y
  · rfl
  · exact False.elim (Bool.false_ne_true (one.symm.trans
      ((visitedSame_iff g x y).mpr ((same_iff g x y).mp two))))
  · exact False.elim (Bool.false_ne_true (two.symm.trans
      ((same_iff g x y).mpr ((visitedSame_iff g x y).mp one))))
  · rfl

theorem visitedSame_equivalence {Label : Type} [DecidableEq Label] {n : Nat}
    (g : Graph Label n) : Equivalence (fun x y => visitedSame g x y = true) := by
  simpa only [visitedSame_eq_same] using same_equivalence g

namespace Probes

/-- Node zero has period one; nodes one and two form a period-two cycle.
All expose the same unary constructor, so cycle length is unobservable. -/
def differentPeriods : Graph Nat 3 where
  label := fun _ => 0
  successors := fun x => [if x.val = 0 then 0 else if x.val = 1 then 2 else 1]

theorem different_periods_bisimilar : Bisimilar differentPeriods 0 1 := by
  refine ⟨fun _ _ => True,?_,True.intro⟩
  intro x y _
  exact ⟨rfl,And.intro True.intro True.intro⟩

theorem different_periods_accepted : visitedSame differentPeriods 0 1 = true :=
  (visitedSame_iff _ _ _).mpr different_periods_bisimilar

/-- The roots agree; their first children expose different labels. -/
def reachableMismatch : Graph Bool 4 where
  label := fun x => x.val == 3
  successors := fun x => [if x.val = 0 then 2 else 3]

theorem reachable_mismatch_not_bisimilar : ¬ Bisimilar reachableMismatch 0 1 := by
  rintro ⟨R,closed,related⟩
  have child : R (2 : Fin 4) (3 : Fin 4) := by
    simpa [reachableMismatch,Children] using (closed 0 1 related).2
  have mismatch := (closed 2 3 child).1
  change false = true at mismatch
  cases mismatch

theorem reachable_mismatch_rejected : visitedSame reachableMismatch 0 1 = false := by
  cases result : visitedSame reachableMismatch 0 1 with
  | false => rfl
  | true => exact False.elim (reachable_mismatch_not_bisimilar
      ((visitedSame_iff _ _ _).mp result))

/-- Equal labels do not excuse a missing constructor child. -/
def arityMismatch : Graph Nat 2 where
  label := fun _ => 0
  successors := fun x => if x.val = 0 then [] else [1]

theorem arity_mismatch_not_bisimilar : ¬ Bisimilar arityMismatch 0 1 := by
  rintro ⟨R,closed,related⟩
  simpa [arityMismatch,Children] using (closed 0 1 related).2

theorem arity_mismatch_rejected : visitedSame arityMismatch 0 1 = false := by
  cases result : visitedSame arityMismatch 0 1 with
  | false => rfl
  | true => exact False.elim (arity_mismatch_not_bisimilar
      ((visitedSame_iff _ _ _).mp result))

-- These evaluate the actual worklist, independently of the semantic proofs.
#guard visitedSame differentPeriods 0 1
#guard !(visitedSame reachableMismatch 0 1)
#guard !(visitedSame arityMismatch 0 1)

end Probes

#assert_axioms same_iff same_equivalence bisimilar_equivalence visitedSame_iff visitedSame_eq_same
  visitedSame_equivalence allPairs_length visited_length_le Probes.different_periods_accepted
  Probes.reachable_mismatch_rejected Probes.arity_mismatch_rejected

end Obend.Core.FiniteBisimulation
