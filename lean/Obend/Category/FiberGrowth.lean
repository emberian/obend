module
public import Obend.Category.Projection

/-!
# Predicate quantifiers when a fiber grows

`some e` identifies a retained point and `none` the fresh point. A postcondition
may change even on retained points. The unconditional decomposition therefore
restricts the *postcondition* to the old carrier. Comparing with an independent
precondition requires agreement, only on the fiber being queried.
-/
public section
namespace Obend.Category.FiberGrowth
open Obend.Category.Projection
set_option autoImplicit false

universe u v w z
variable {E : Type u} {B : Type v} {D : Type w} {V : Type z}

/-- Extend a projection by one point lying over `name`. -/
@[expose] def insert (p : E → B) (name : B) : Option E → B
  | none => name
  | some e => p e

@[simp] theorem insert_some (p : E → B) (name : B) (e : E) :
    insert p name (some e) = p e := rfl

@[simp] theorem insert_none (p : E → B) (name : B) : insert p name none = name := rfl

theorem exists_insert_iff (p : E → B) (name : B) (post : Option E → Prop) (b : B) :
    existsAlong (insert p name) post b ↔
      existsAlong p (fun e => post (some e)) b ∨ (name = b ∧ post none) := by
  constructor
  · rintro ⟨_ | e, he, h⟩
    · exact .inr ⟨he, h⟩
    · exact .inl ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨he, h⟩)
    · exact ⟨some e, he, h⟩
    · exact ⟨none, he, h⟩

theorem forall_insert_iff (p : E → B) (name : B) (post : Option E → Prop) (b : B) :
    forallAlong (insert p name) post b ↔
      forallAlong p (fun e => post (some e)) b ∧ (name = b → post none) := by
  constructor
  · exact fun h => ⟨fun e => h (some e), h none⟩
  · rintro ⟨old, fresh⟩ (_ | e)
    · exact fresh
    · exact old e

theorem exists_at_insert (p : E → B) (name : B) (post : Option E → Prop) :
    existsAlong (insert p name) post name ↔
      existsAlong p (fun e => post (some e)) name ∨ post none := by
  exact (exists_insert_iff p name post name).trans
    (or_congr Iff.rfl ⟨And.right, fun h => ⟨rfl, h⟩⟩)

theorem forall_at_insert (p : E → B) (name : B) (post : Option E → Prop) :
    forallAlong (insert p name) post name ↔
      forallAlong p (fun e => post (some e)) name ∧ post none := by
  exact (forall_insert_iff p name post name).trans
    (and_congr Iff.rfl ⟨fun h => h rfl, fun h _ => h⟩)

/-- Simultaneous transport of the observations of a predicate on one old fiber. -/
private theorem restrict_iff (p : E → B) (pre : E → Prop) (post : Option E → Prop) (b : B)
    (agree : ∀ e, p e = b → (post (some e) ↔ pre e)) :
    (existsAlong p (fun e => post (some e)) b ↔ existsAlong p pre b) ∧
    (forallAlong p (fun e => post (some e)) b ↔ forallAlong p pre b) := by
  exact ⟨⟨fun ⟨e, he, h⟩ => ⟨e, he, (agree e he).mp h⟩,
          fun ⟨e, he, h⟩ => ⟨e, he, (agree e he).mpr h⟩⟩,
         ⟨fun h e he => (agree e he).mp (h e he), fun h e he => (agree e he).mpr (h e he)⟩⟩

/-- Witnesses need only persist in the forward direction on the queried old fiber. -/
theorem exists_preserved (p : E → B) (name b : B) (pre : E → Prop) (post : Option E → Prop)
    (keep : ∀ e, p e = b → pre e → post (some e)) :
    existsAlong p pre b → existsAlong (insert p name) post b := by
  exact fun ⟨e, he, h⟩ => ⟨some e, he, keep e he h⟩

/-- A universal fact reflects to the old fiber if each retained observation reflects. -/
theorem forall_reflected (p : E → B) (name b : B) (pre : E → Prop) (post : Option E → Prop)
    (reflect : ∀ e, p e = b → post (some e) → pre e) :
    forallAlong (insert p name) post b → forallAlong p pre b := by
  exact fun h e he => reflect e he (h (some e) he)

/-- Insertion anywhere else leaves *both* answers at this name intact. -/
theorem unchanged_away (p : E → B) (name b : B) (elsewhere : name ≠ b)
    (pre : E → Prop) (post : Option E → Prop)
    (agree : ∀ e, p e = b → (post (some e) ↔ pre e)) :
    (existsAlong (insert p name) post b ↔ existsAlong p pre b) ∧
    (forallAlong (insert p name) post b ↔ forallAlong p pre b) := by
  obtain ⟨oldEx, oldAll⟩ := restrict_iff p pre post b agree
  refine ⟨(exists_insert_iff p name post b).trans ?_, (forall_insert_iff p name post b).trans ?_⟩
  · exact ⟨fun h => h.elim oldEx.mp (fun fresh => (elsewhere fresh.1).elim),
           fun h => .inl (oldEx.mpr h)⟩
  · exact ⟨fun h => oldAll.mp h.1, fun h => ⟨oldAll.mpr h, fun eq => (elsewhere eq).elim⟩⟩

/-- The fresh witness can leave the existential answer unchanged exactly when its
truth already implies the existence of an old witness. -/
theorem exists_unchanged_at_iff (p : E → B) (name : B) (pre : E → Prop) (post : Option E → Prop)
    (agree : ∀ e, p e = name → (post (some e) ↔ pre e)) :
    (existsAlong (insert p name) post name ↔ existsAlong p pre name) ↔
      (post none → existsAlong p pre name) := by
  have split := (exists_at_insert p name post).trans
    (or_congr (restrict_iff p pre post name agree).1 Iff.rfl)
  exact ⟨fun stable fresh => stable.mp (split.mpr (.inr fresh)),
         fun recover => split.trans ⟨fun h => h.elim id recover, Or.inl⟩⟩

/-- The universal answer is unchanged exactly when an old proof covers the fresh point. -/
theorem forall_unchanged_at_iff (p : E → B) (name : B) (pre : E → Prop) (post : Option E → Prop)
    (agree : ∀ e, p e = name → (post (some e) ↔ pre e)) :
    (forallAlong (insert p name) post name ↔ forallAlong p pre name) ↔
      (forallAlong p pre name → post none) := by
  have split := (forall_at_insert p name post).trans
    (and_congr (restrict_iff p pre post name agree).2 Iff.rfl)
  exact ⟨fun stable old => (split.mp (stable.mpr old)).2,
         fun accepts => split.trans ⟨And.left, fun old => ⟨old, accepts old⟩⟩⟩

/-- Necessary and sufficient fresh-point obligations for preserving both answers.
The fresh truth must lie between the old universal and old existential. -/
theorem unchanged_at_iff (p : E → B) (name : B) (pre : E → Prop) (post : Option E → Prop)
    (agree : ∀ e, p e = name → (post (some e) ↔ pre e)) :
    ((existsAlong (insert p name) post name ↔ existsAlong p pre name) ∧
     (forallAlong (insert p name) post name ↔ forallAlong p pre name)) ↔
    ((post none → existsAlong p pre name) ∧ (forallAlong p pre name → post none)) :=
  and_congr (exists_unchanged_at_iff p name pre post agree) (forall_unchanged_at_iff p name pre post agree)

/-- Both answers cannot agree after adding the first point over a name. This
impossibility needs no decision of the predicate at that point. -/
theorem no_joint_agreement_on_empty (p : E → B) (name : B) (empty : ∀ e, p e ≠ name)
    (pre : E → Prop) (post : Option E → Prop) :
    ¬ ((existsAlong (insert p name) post name ↔ existsAlong p pre name) ∧
       (forallAlong (insert p name) post name ↔ forallAlong p pre name)) := by
  intro both
  have agree : ∀ e, p e = name → (post (some e) ↔ pre e) := fun e he => (empty e he).elim
  obtain ⟨freshToOld, oldToFresh⟩ := (unchanged_at_iff p name pre post agree).mp both
  have old : forallAlong p pre name := (forallAlong_iff ..).mpr fun e he => (empty e he).elim
  obtain ⟨e, he, _⟩ := (existsAlong_iff ..).mp (freshToOld (oldToFresh old))
  exact empty e he

/-- A copy agreeing with its source preserves both answers, even in a mixed fiber.
The antecedent is about this particular predicate; identity-sensitive observations may fail it. -/
theorem unchanged_of_copy (p : E → B) (source : E) (pre : E → Prop) (post : Option E → Prop)
    (agree : ∀ e, p e = p source → (post (some e) ↔ pre e))
    (copied : post none ↔ pre source) :
    (existsAlong (insert p (p source)) post (p source) ↔ existsAlong p pre (p source)) ∧
    (forallAlong (insert p (p source)) post (p source) ↔ forallAlong p pre (p source)) := by
  apply (unchanged_at_iff p (p source) pre post agree).mpr
  exact ⟨fun h => (existsAlong_iff ..).mpr ⟨source, rfl, copied.mp h⟩,
    fun h => copied.mpr ((forallAlong_iff ..).mp h source rfl)⟩

/-- The old-to-new inclusion misses the fresh point over its name. -/
theorem inclusion_misses_fiber (p : E → B) (name : B) :
    ¬ FiberwiseSurjective (insert p name) p some id := by
  intro lifts
  obtain ⟨e, _, h⟩ := lifts name none rfl
  cases h

/-- In the opposite direction, identify the duplicate with its source. Every old
point has a lift via `some`, including points in other fibers. -/
theorem collapse_lifts (p : E → B) (source : E) :
    FiberwiseSurjective p (insert p (p source)) (fun e => e.getD source) id :=
  fun _ e h => ⟨some e, h, rfl⟩

/-- All predicates on the old carrier extend canonically by interpreting the fresh
point as its source. Both quantifiers then commute with this extension at every name. -/
theorem collapse_preserves (p : E → B) (source : E) (pre : E → Prop) (b : B) :
    let post := pull (fun e : Option E => e.getD source) pre
    (existsAlong (insert p (p source)) post b ↔ existsAlong p pre b) ∧
    (forallAlong (insert p (p source)) post b ↔ forallAlong p pre b) := by
  have comm : ∀ e : Option E, p (e.getD source) = id (insert p (p source) e) := by
    intro e
    cases e <;> rfl
  exact ⟨(exists_baseChange_iff _ _ _ _ comm).mpr (collapse_lifts p source) pre b,
         (forall_baseChange_iff _ _ _ _ comm).mpr (collapse_lifts p source) pre b⟩

/-- Arbitrarily many fresh points can be quantified in one pass. The two summands
are the retained and inserted populations, with their own maps to names. -/
theorem exists_batch_iff (p : E → B) (added : D → B) (post : E ⊕ D → Prop) (b : B) :
    existsAlong (Sum.elim p added) post b ↔
      existsAlong p (fun e => post (.inl e)) b ∨ existsAlong added (fun d => post (.inr d)) b := by
  constructor
  · rintro ⟨e | d, he, h⟩
    · exact .inl ⟨e, he, h⟩
    · exact .inr ⟨d, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨d, hd, h⟩)
    · exact ⟨.inl e, he, h⟩
    · exact ⟨.inr d, hd, h⟩

theorem forall_batch_iff (p : E → B) (added : D → B) (post : E ⊕ D → Prop) (b : B) :
    forallAlong (Sum.elim p added) post b ↔
      forallAlong p (fun e => post (.inl e)) b ∧ forallAlong added (fun d => post (.inr d)) b := by
  constructor
  · exact fun h => ⟨fun e => h (.inl e), fun d => h (.inr d)⟩
  · rintro ⟨old, fresh⟩ (e | d)
    · exact old e
    · exact fresh d

/-! ## Observable values across arbitrary world changes

The two worlds may have unrelated carriers. Their objects are visible through
maps to a common observation type; asking a property of that value may distinguish
fewer points than asking a property of the identifier. -/

/-- The named fiber realizes the observation `v`. -/
@[expose] def observes (p : E → B) (h : E → V) (b : B) (v : V) : Prop :=
  existsAlong p (fun e => h e = v) b

theorem observes_iff (p : E → B) (h : E → V) (b : B) (v : V) :
    observes p h b v ↔ ∃ e, p e = b ∧ h e = v := Iff.rfl

private theorem obs_transfer (p : E → B) (h : E → V) (p' : D → B) (h' : D → V) (b : B)
    (includeValues : ∀ v, observes p h b v → observes p' h' b v) (Q : V → Prop) :
    (existsAlong p (fun e => Q (h e)) b → existsAlong p' (fun d => Q (h' d)) b) ∧
    (forallAlong p' (fun d => Q (h' d)) b → forallAlong p (fun e => Q (h e)) b) := by
  have lift (e : E) (he : p e = b) : observes p' h' b (h e) :=
    includeValues (h e) ⟨e, he, rfl⟩
  constructor
  · rintro ⟨e, he, good⟩
    obtain ⟨d, hd, eq⟩ := lift e he
    exact ⟨d, hd, Eq.mpr (congrArg Q eq) good⟩
  · intro good e he
    obtain ⟨d, hd, eq⟩ := lift e he
    exact Eq.mp (congrArg Q eq) (good d hd)

/-- Every existential predicate of the observation is unchanged exactly when
the fiber realizes the same values in both worlds. Singleton queries test necessity. -/
theorem exists_observations_iff (p : E → B) (h : E → V) (p' : D → B) (h' : D → V) (b : B) :
    (∀ Q : V → Prop, existsAlong p (fun e => Q (h e)) b ↔
      existsAlong p' (fun d => Q (h' d)) b) ↔
    (∀ v, observes p h b v ↔ observes p' h' b v) := by
  constructor
  · exact fun same v => same (· = v)
  · intro same Q
    exact ⟨(obs_transfer p h p' h' b (fun v => (same v).mp) Q).1,
           (obs_transfer p' h' p h b (fun v => (same v).mpr) Q).1⟩

/-- Universal queries alone determine exactly the same observation image,
constructively: test membership in each world's own image in turn. -/
theorem forall_observations_iff (p : E → B) (h : E → V) (p' : D → B) (h' : D → V) (b : B) :
    (∀ Q : V → Prop, forallAlong p (fun e => Q (h e)) b ↔
      forallAlong p' (fun d => Q (h' d)) b) ↔
    (∀ v, observes p h b v ↔ observes p' h' b v) := by
  constructor
  · intro same v
    have old : forallAlong p (fun e => observes p h b (h e)) b := fun e he => ⟨e, he, rfl⟩
    have new : forallAlong p' (fun d => observes p' h' b (h' d)) b := fun d hd => ⟨d, hd, rfl⟩
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (same (observes p' h' b)).mpr new e he
    · rintro ⟨d, hd, rfl⟩
      exact (same (observes p h b)).mp old d hd
  · intro same Q
    exact ⟨(obs_transfer p' h' p h b (fun v => (same v).mpr) Q).2,
           (obs_transfer p h p' h' b (fun v => (same v).mp) Q).2⟩

/-- At the only name of an inhabited one-point world, insertion makes “some ID
is fresh” true and “every ID is retained” false. Both old observations agree
with the restrictions of the new predicates. -/
theorem strict_growth_witness :
    let p := fun (_ : Unit) => ()
    (¬ existsAlong p (fun _ => False) ()) ∧ existsAlong (insert p ()) (· = none) () ∧
    forallAlong p (fun _ => True) () ∧ ¬ forallAlong (insert p ()) (· ≠ none) () := by
  exact ⟨fun ⟨_, _, h⟩ => h, ⟨none, rfl, rfl⟩, fun _ _ => True.intro,
    fun allRetained => allRetained none rfl rfl⟩

end Obend.Category.FiberGrowth
end
