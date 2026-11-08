module
/- Balanced literal-array lookup in ordinary Core4 syntax. Every branch compares
one unchanged index against a static offset, so syntax has linear size and
logarithmic depth. The public wrapper supplies the out-of-bounds zero. -/
public import Obend.Hardware.Gpu.ArrayProduct
@[expose] public section
namespace Obend.Hardware.Gpu.ArraySource.Core
open Obend.Core.Term Obend.Equiv
set_option autoImplicit false

/-- Balanced decision tree, with absolute index thresholds. -/
def lookupBody (xs : List Nat) (base : Nat) (index : Term) : Term :=
  if xs.length ≤ 1 then .nat (xs.getD 0 0)
  else
    let k := xs.length / 2
    .ifBool (.binary .less index (.nat (base + k)))
      (lookupBody (xs.take k) base index)
      (lookupBody (xs.drop k) (base + k) index)
termination_by xs.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

theorem lookupBody_substitute (xs : List Nat) (base : Nat) (index : Term) (σ : Nat → Term) :
    (lookupBody xs base index).substitute σ = lookupBody xs base (index.substitute σ) := by
  by_cases h : xs.length ≤ 1
  · rw [lookupBody, lookupBody]
    simp only [h, ↓reduceIte, Term.substitute]
  · rw [lookupBody, lookupBody]
    simp only [h, ↓reduceIte, Term.substitute]
    rw [lookupBody_substitute (xs.take (xs.length / 2)),
      lookupBody_substitute (xs.drop (xs.length / 2))]
termination_by xs.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

theorem lookupBody_rename (xs : List Nat) (base : Nat) (index : Term) (ρ : Nat → Nat) :
    (lookupBody xs base index).rename ρ = lookupBody xs base (index.rename ρ) := by
  by_cases h : xs.length ≤ 1
  · rw [lookupBody, lookupBody]
    simp only [h, ↓reduceIte, Term.rename]
  · rw [lookupBody, lookupBody]
    simp only [h, ↓reduceIte, Term.rename]
    rw [lookupBody_rename (xs.take (xs.length / 2)),
      lookupBody_rename (xs.drop (xs.length / 2))]
termination_by xs.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

theorem lookupBody_steps (xs : List Nat) (base i : Nat) (hi : i < xs.length) :
    Steps (lookupBody xs base (.nat (base + i))) (.nat (xs.getD i 0)) := by
  rw [lookupBody]
  split
  · rename_i h
    have hz : i = 0 := by omega
    subst i
    exact .refl _
  · rename_i h
    have hk : 0 < xs.length / 2 ∧ xs.length / 2 < xs.length := by omega
    refine .next (.ifCondition _ _ (.primitive .less _ _ _ (.natural _) (.natural _) rfl)) ?_
    by_cases hil : i < xs.length / 2
    · have hc : base + i < base + xs.length / 2 := by omega
      simp only [hc, decide_true]
      refine .next (.ifTrue _ _) ?_
      have ih := lookupBody_steps (xs.take (xs.length / 2)) base i (by simp; omega)
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hil] using ih
    · have hc : ¬base + i < base + xs.length / 2 := by omega
      simp only [hc, decide_false]
      refine .next (.ifFalse _ _) ?_
      have ih := lookupBody_steps (xs.drop (xs.length / 2)) (base + xs.length / 2)
        (i - xs.length / 2) (by simp; omega)
      have he : base + xs.length / 2 + (i - xs.length / 2) = base + i := by omega
      have he' : xs.length / 2 + (i - xs.length / 2) = i := by omega
      simpa only [he, List.getD_eq_getElem?_getD, List.getElem?_drop, he'] using ih
termination_by xs.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- A closed total function from natural indices to natural elements. -/
def encodeNats (xs : List Nat) : Term :=
  .lam (.ifBool (.binary .less (.bound 0) (.nat xs.length))
    (lookupBody xs 0 (.bound 0)) (.nat 0))

theorem encodeNats_substitute (xs : List Nat) (σ : Nat → Term) :
    (encodeNats xs).substitute σ = encodeNats xs := by
  simp only [encodeNats, Term.substitute, lookupBody_substitute, liftSubstitution]

theorem encodeNats_rename (xs : List Nat) (ρ : Nat → Nat) :
    (encodeNats xs).rename ρ = encodeNats xs := by
  simp only [encodeNats, Term.rename, lookupBody_rename, liftRename]

theorem encodeNats_apply (xs : List Nat) (i : Nat) :
    Steps (.app (encodeNats xs) (.nat i)) (.nat (xs.getD i 0)) := by
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, lookupBody_substitute]
  refine .next (.ifCondition _ _ (.primitive .less _ _ _ (.natural _) (.natural _) rfl)) ?_
  by_cases hi : i < xs.length
  · simp only [hi, decide_true]
    refine .next (.ifTrue _ _) ?_
    simpa only [Nat.zero_add] using lookupBody_steps xs 0 i hi
  · simp only [hi, decide_false]
    refine .next (.ifFalse _ _) ?_
    have hz : xs.getD i 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
    rw [hz]
    exact .refl _

end Obend.Hardware.Gpu.ArraySource.Core
end
