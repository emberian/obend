module
public import Obend.Core.Term
@[expose] public section
namespace Obend.Core.Traverse
open Obend.Core.Term
set_option autoImplicit false

/-- Constructor payloads are opaque to the traversal. A binder edge binds exactly
one index; arbitrary child lists include the nested field/arm lists of `Term`. -/
inductive Tree (Tag : Type) where
  | var (index : Nat)
  | bind (body : Tree Tag)
  | node (tag : Tag) (children : List (Tree Tag))

namespace Tree
variable {Tag : Type}

/-- The sole recursive rebuilding traversal. The environment's action and lift
are parameters, so renaming and substitution share the same recursion. -/
def traverse {Env : Type} (onVar : Env → Nat → Tree Tag) (lift : Env → Env)
    (env : Env) : Tree Tag → Tree Tag
  | .var i => onVar env i
  | .bind body => .bind (traverse onVar lift (lift env) body)
  | .node tag children => .node tag (children.map (traverse onVar lift env))

/-- Induction exposing the membership hypotheses for arbitrary child lists. -/
theorem inductionOn (t : Tree Tag) {P : Tree Tag → Prop}
    (var : ∀ i, P (.var i))
    (bind : ∀ body, P body → P (.bind body))
    (node : ∀ tag children, (∀ child ∈ children, P child) → P (.node tag children)) : P t := by
  cases t with
  | var i => exact var i
  | bind body => exact bind body (inductionOn body var bind node)
  | node tag children =>
    apply node tag children
    intro child member
    exact inductionOn child var bind node
termination_by sizeOf t
decreasing_by
  · simp +arith
  · have := List.sizeOf_lt_of_mem member
    simp +arith; omega

abbrev rename (f : Nat → Nat) (t : Tree Tag) : Tree Tag :=
  traverse (fun f i => .var (f i)) liftRename f t

def liftSubst (σ : Nat → Tree Tag) : Nat → Tree Tag
  | 0 => .var 0
  | i+1 => rename Nat.succ (σ i)

abbrev substitute (σ : Nat → Tree Tag) (t : Tree Tag) : Tree Tag :=
  traverse (fun σ i => σ i) liftSubst σ t

@[simp] theorem liftRename_comp (f g : Nat → Nat) :
    (fun i => liftRename g (liftRename f i)) = liftRename (fun i => g (f i)) := by
  funext i; cases i <;> rfl

theorem rename_comp (t : Tree Tag) (f g : Nat → Nat) :
    rename g (rename f t) = rename (fun i => g (f i)) t := by
  induction t using inductionOn generalizing f g with
  | var i => simp only [rename, traverse]
  | bind body ih => simp only [rename, traverse, ih, liftRename_comp]
  | node tag children ih =>
    simp only [rename, traverse, List.map_map]
    congr 1
    exact List.map_congr_left (fun child member => ih child member f g)

@[simp] theorem rename_id (t : Tree Tag) : rename id t = t := by
  have lifted : liftRename id = id := by funext i; cases i <;> rfl
  induction t using inductionOn with
  | var i => simp only [rename, traverse, id_eq]
  | bind body ih => simp only [rename, traverse, lifted, ih]
  | node tag children ih =>
    simp only [rename, traverse]
    congr 1
    exact (List.map_congr_left (fun child member => ih child member)).trans (List.map_id _)

theorem rename_substitute (t : Tree Tag) (f : Nat → Nat) (σ : Nat → Tree Tag) :
    substitute σ (rename f t) = substitute (fun i => σ (f i)) t := by
  have lifted : ∀ (f : Nat → Nat) (σ : Nat → Tree Tag), (fun i => liftSubst σ (liftRename f i)) =
      liftSubst (fun i => σ (f i)) := by
    intro f σ; funext i; cases i <;> rfl
  induction t using inductionOn generalizing f σ with
  | var i => simp only [rename, substitute, traverse]
  | bind body ih => simp only [rename, substitute, traverse, ih, lifted]
  | node tag children ih =>
    simp only [rename, substitute, traverse, List.map_map]
    congr 1
    exact List.map_congr_left (fun child member => ih child member f σ)

theorem substitute_rename (t : Tree Tag) (σ : Nat → Tree Tag) (f : Nat → Nat) :
    rename f (substitute σ t) = substitute (fun i => rename f (σ i)) t := by
  have lifted : ∀ (σ : Nat → Tree Tag) (f : Nat → Nat), (fun i => rename (liftRename f) (liftSubst σ i)) =
      liftSubst (fun i => rename f (σ i)) := by
    intro σ f; funext i
    cases i with
    | zero => simp only [liftSubst, rename, traverse, liftRename]
    | succ i => simp only [liftSubst, rename_comp]; rfl
  induction t using inductionOn generalizing σ f with
  | var i => simp only [rename, substitute, traverse]
  | bind body ih => simp only [rename, substitute, traverse, ih, lifted]
  | node tag children ih =>
    simp only [rename, substitute, traverse, List.map_map]
    congr 1
    exact List.map_congr_left (fun child member => ih child member σ f)

theorem substitute_comp (t : Tree Tag) (σ τ : Nat → Tree Tag) :
    substitute τ (substitute σ t) = substitute (fun i => substitute τ (σ i)) t := by
  have lifted : ∀ (σ τ : Nat → Tree Tag), (fun i => substitute (liftSubst τ) (liftSubst σ i)) =
      liftSubst (fun i => substitute τ (σ i)) := by
    intro σ τ; funext i
    cases i with
    | zero => simp only [liftSubst, substitute, traverse]
    | succ i =>
      simp only [liftSubst, rename_substitute, substitute_rename]
  induction t using inductionOn generalizing σ τ with
  | var i => simp only [substitute, traverse]
  | bind body ih => simp only [substitute, traverse, ih, lifted]
  | node tag children ih =>
    simp only [substitute, traverse, List.map_map]
    congr 1
    exact List.map_congr_left (fun child member => ih child member σ τ)

/-- All free indices satisfy a predicate. Bound indices satisfy it automatically. -/
def All (p : Nat → Prop) : Tree Tag → Prop
  | .var i => p i
  | .bind body => All (fun i => match i with | 0 => True | j+1 => p j) body
  | .node _ children => ∀ child ∈ children, All p child

abbrev Scoped (n : Nat) (t : Tree Tag) : Prop := All (fun i => i < n) t

/-- Boolean counterpart of `All`, sharing exactly its binder policy. -/
def all (p : Nat → Bool) : Tree Tag → Bool
  | .var i => p i
  | .bind body => all (fun i => match i with | 0 => true | j+1 => p j) body
  | .node _ children => (children.map (all p)).all id

/-- Whether a free de Bruijn index occurs (not the type checker's usage grades). -/
def uses (i : Nat) (t : Tree Tag) : Bool := !all (fun j => j != i) t

theorem all_eq_true (t : Tree Tag) (p : Nat → Bool) : all p t = true ↔ All (fun i => p i = true) t := by
  induction t using inductionOn generalizing p with
  | var i => simp only [all, All]
  | bind body ih =>
    simp only [all, All, ih]
    have same : (fun i => (match i with | 0 => true | j+1 => p j) = true) =
        (fun i => match i with | 0 => True | j+1 => p j = true) := by
      funext i; cases i <;> simp
    rw [same]
  | node tag children ih => simp only [all, All, List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]; exact forall_congr' (fun c => forall_congr' (fun h => ih c h p))

theorem all_congr (t : Tree Tag) (p q : Nat → Prop) (same : ∀ i, p i ↔ q i) :
    All p t ↔ All q t := by
  have : p = q := funext (fun i => propext (same i))
  rw [this]

theorem traverse_congr_on {Env : Type} (onVar : Env → Nat → Tree Tag) (lift : Env → Env)
    (R : (Nat → Prop) → Env → Env → Prop)
    (variables : ∀ p e e', R p e e' → ∀ i, p i → onVar e i = onVar e' i)
    (lifts : ∀ p e e', R p e e' → R (fun i => match i with | 0 => True | j+1 => p j) (lift e) (lift e'))
    (t : Tree Tag) (p : Nat → Prop) (h : All p t) (e e' : Env) (same : R p e e') :
    traverse onVar lift e t = traverse onVar lift e' t := by
  induction t using inductionOn generalizing p e e' with
  | var i => simp only [All] at h; simpa only [traverse] using variables p e e' same i h
  | bind body ih =>
    simp only [All] at h
    simpa only [traverse] using congrArg Tree.bind (ih _ h _ _ (lifts p e e' same))
  | node tag children ih =>
    simp only [All] at h
    simp only [traverse]
    congr 1
    exact List.map_congr_left (fun c hc => ih c hc p (h c hc) e e' same)

theorem rename_congr_on (t : Tree Tag) (p : Nat → Prop) (h : All p t)
    (f g : Nat → Nat) (same : ∀ i, p i → f i = g i) : rename f t = rename g t := by
  apply traverse_congr_on _ _ (fun p f g => ∀ i, p i → f i = g i) _ _ t p h f g same
  · intro p f g h i hi; exact congrArg Tree.var (h i hi)
  · intro p f g h i hi; cases i with
    | zero => rfl
    | succ i => exact congrArg Nat.succ (h i hi)

theorem scoped_rename_identity (t : Tree Tag) (n : Nat) (h : Scoped n t)
    (f : Nat → Nat) (same : ∀ i, i < n → f i = i) : rename f t = t :=
  (rename_congr_on t _ h f id same).trans (rename_id t)

theorem substitute_id (t : Tree Tag) : substitute Tree.var t = t := by
  have lifted : liftSubst (Tree.var : Nat → Tree Tag) = Tree.var := by
    funext i; cases i <;> simp only [liftSubst, rename, traverse]
  induction t using inductionOn with
  | var i => simp only [substitute, traverse]
  | bind body ih => simpa only [substitute, traverse, lifted] using congrArg Tree.bind ih
  | node tag children ih =>
    simp only [substitute, traverse]
    exact congrArg (Tree.node tag) ((List.map_congr_left (fun c hc => ih c hc)).trans (List.map_id _))

theorem substitute_congr_on (t : Tree Tag) (p : Nat → Prop) (h : All p t)
    (σ τ : Nat → Tree Tag) (same : ∀ i, p i → σ i = τ i) : substitute σ t = substitute τ t := by
  apply traverse_congr_on _ _ (fun p σ τ => ∀ i, p i → σ i = τ i) _ _ t p h σ τ same
  · intro p σ τ h i hi; exact h i hi
  · intro p σ τ h i hi; cases i with
    | zero => rfl
    | succ i => exact congrArg (rename Nat.succ) (h i hi)

theorem scoped_substitute_identity (t : Tree Tag) (n : Nat) (h : Scoped n t)
    (σ : Nat → Tree Tag) (same : ∀ i, i < n → σ i = .var i) : substitute σ t = t :=
  (substitute_congr_on t _ h σ Tree.var same).trans (substitute_id t)

theorem all_rename (t : Tree Tag) (p q : Nat → Prop) (h : All p t)
    (f : Nat → Nat) (maps : ∀ i, p i → q (f i)) : All q (rename f t) := by
  induction t using inductionOn generalizing p q f with
  | var i => simpa only [rename, traverse, All] using maps i (by simpa only [All] using h)
  | bind body ih =>
    simp only [rename, traverse, All] at h ⊢
    apply ih _ _ h _
    intro i hi; cases i with
    | zero => trivial
    | succ i => exact maps i hi
  | node tag children ih =>
    simp only [rename, traverse, All] at h ⊢
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact ih a ha p q (h a ha) f maps

theorem all_substitute (t : Tree Tag) (p q : Nat → Prop) (h : All p t)
    (σ : Nat → Tree Tag) (maps : ∀ i, p i → All q (σ i)) : All q (substitute σ t) := by
  induction t using inductionOn generalizing p q σ with
  | var i => simpa only [substitute, traverse, All] using maps i (by simpa only [All] using h)
  | bind body ih =>
    simp only [substitute, traverse, All] at h ⊢
    apply ih _ _ h _
    intro i hi; cases i with
    | zero => simp only [liftSubst, All]
    | succ i => exact all_rename (σ i) q _ (maps i hi) Nat.succ (fun _ hi => hi)
  | node tag children ih =>
    simp only [substitute, traverse, All] at h ⊢
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact ih a ha p q (h a ha) σ maps

theorem scoped_rename (t : Tree Tag) (n m : Nat) (h : Scoped n t)
    (f : Nat → Nat) (maps : ∀ i, i < n → f i < m) : Scoped m (rename f t) :=
  all_rename t _ _ h f maps

theorem scoped_substitute (t : Tree Tag) (n m : Nat) (h : Scoped n t)
    (σ : Nat → Tree Tag) (maps : ∀ i, i < n → Scoped m (σ i)) : Scoped m (substitute σ t) :=
  all_substitute t _ _ h σ maps

#assert_axioms rename_comp rename_id rename_substitute substitute_rename substitute_comp
  all_eq_true all_congr traverse_congr_on rename_congr_on scoped_rename_identity
  substitute_id substitute_congr_on scoped_substitute_identity all_rename all_substitute
  scoped_rename scoped_substitute

end Tree
end Obend.Core.Traverse
end
