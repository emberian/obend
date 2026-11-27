module
public import Obend.Category.Refines

/-! Quantification along a function on state predicates. The graph of the function and
its converse give the two adjunctions from `GaloisRefinement.ofRel`. In a commuting
square, changing the base commutes with quantification on all predicates exactly when
every point of the matching fiber lifts. All statements are constructive. -/

public section
namespace Obend.Category.Projection
set_option autoImplicit false

universe u v w z
variable {E : Type u} {B : Type v}

/-- Reindex a base predicate along the projection. -/
@[expose] def pull (p : E → B) (Q : B → Prop) (e : E) : Prop := Q (p e)

/-- Existential image along the graph of `p`. -/
@[expose] def existsAlong (p : E → B) (S : E → Prop) : B → Prop :=
  (GaloisRefinement.ofRel (fun e b => p e = b)).alpha S

/-- Universal image via the converse graph of `p`. -/
@[expose] def forallAlong (p : E → B) (S : E → Prop) : B → Prop :=
  (GaloisRefinement.ofRel (fun b e => p e = b)).gamma S

theorem existsAlong_iff (p : E → B) (S : E → Prop) (b : B) :
    existsAlong p S b ↔ ∃ e, p e = b ∧ S e := Iff.rfl

theorem forallAlong_iff (p : E → B) (S : E → Prop) (b : B) :
    forallAlong p S b ↔ ∀ e, p e = b → S e := Iff.rfl

/-- The right adjoint for the forward graph agrees pointwise with reindexing. -/
theorem graph_gamma (p : E → B) (Q : B → Prop) (e : E) :
    (GaloisRefinement.ofRel (fun e b => p e = b)).gamma Q e ↔ pull p Q e := by
  change (∀ b, p e = b → Q b) ↔ Q (p e)
  exact ⟨fun h => h _ rfl, fun h _ eq => eq ▸ h⟩

/-- The left adjoint for the converse graph also agrees with reindexing. -/
theorem converse_alpha (p : E → B) (Q : B → Prop) (e : E) :
    (GaloisRefinement.ofRel (fun b e => p e = b)).alpha Q e ↔ pull p Q e := by
  change (∃ b, p e = b ∧ Q b) ↔ Q (p e)
  exact ⟨fun ⟨_, eq, h⟩ => eq ▸ h, fun h => ⟨_, rfl, h⟩⟩

/-- ∃ₚ ⊣ p*. -/
theorem exists_adj (p : E → B) (S : E → Prop) (Q : B → Prop) :
    PredLe (existsAlong p S) Q ↔ PredLe S (pull p Q) := by
  refine ((GaloisRefinement.ofRel (fun e b => p e = b)).adj S Q).trans ?_
  exact ⟨fun h e he => (graph_gamma p Q e).mp (h e he),
         fun h e he => (graph_gamma p Q e).mpr (h e he)⟩

/-- p* ⊣ ∀ₚ. -/
theorem forall_adj (p : E → B) (Q : B → Prop) (S : E → Prop) :
    PredLe (pull p Q) S ↔ PredLe Q (forallAlong p S) := by
  refine Iff.trans ?_ ((GaloisRefinement.ofRel (fun b e => p e = b)).adj Q S)
  exact ⟨fun h e he => h e ((converse_alpha p Q e).mp he),
         fun h e he => h e ((converse_alpha p Q e).mpr he)⟩

variable {E' : Type w} {B' : Type z}

/-- Every element of the fiber of `p` over `k b'` has a lift in the fiber of `p'`
over `b'`. A pullback square supplies unique lifts; these laws need only existence. -/
@[expose] def FiberwiseSurjective (p : E → B) (p' : E' → B')
    (i : E' → E) (k : B' → B) : Prop :=
  ∀ b' e, p e = k b' → ∃ e', p' e' = b' ∧ i e' = e

/-- Existential Beck–Chevalley for all predicates characterizes fiberwise surjectivity.
For necessity take the singleton predicate of the element whose lift is required. -/
theorem exists_baseChange_iff (p : E → B) (p' : E' → B') (i : E' → E) (k : B' → B)
    (comm : ∀ x, p (i x) = k (p' x)) :
    (∀ (S : E → Prop) b', existsAlong p' (pull i S) b' ↔ pull k (existsAlong p S) b') ↔
      FiberwiseSurjective p p' i k := by
  constructor
  · intro h b' e he
    exact (h (fun y => y = e) b').mpr ⟨e, he, rfl⟩
  · intro lifts S b'
    constructor
    · rintro ⟨x, hx, hs⟩
      exact ⟨i x, (comm x).trans (congrArg k hx), hs⟩
    · rintro ⟨e, he, hs⟩
      obtain ⟨x, hx, rfl⟩ := lifts b' e he
      exact ⟨x, hx, hs⟩

/-- Universal Beck–Chevalley has the same exact criterion constructively. For necessity
take as predicate the image of the smaller fiber; all its own elements belong to it. -/
theorem forall_baseChange_iff (p : E → B) (p' : E' → B') (i : E' → E) (k : B' → B)
    (comm : ∀ x, p (i x) = k (p' x)) :
    (∀ (S : E → Prop) b', forallAlong p' (pull i S) b' ↔ pull k (forallAlong p S) b') ↔
      FiberwiseSurjective p p' i k := by
  constructor
  · intro h b' e he
    have inImage := (h (fun y => ∃ x, p' x = b' ∧ i x = y) b').mp
      (fun x hx => ⟨x, hx, rfl⟩)
    exact inImage e he
  · intro lifts S b'
    constructor
    · intro h e he
      obtain ⟨x, hx, rfl⟩ := lifts b' e he
      exact h x hx
    · intro h x hx
      exact h (i x) ((comm x).trans (congrArg k hx))

end Obend.Category.Projection
end
