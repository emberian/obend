module
/- The former finite canonical/head-alias agreement, isolated from the checker
so recursive agreement can be integrated without an import cycle. Names and
semantics are preserved at this extraction checkpoint. -/
public import Obend.Core.Assumptions
public import Obend.AxiomPin
@[expose] public section
namespace Obend.Core.Check
open Obend.Core.Ty
set_option autoImplicit false

/-- One step of type agreement: canonical equality, or one declared head of an
alias variable unfolded on one side (the whole of the relation's conversion before
2026-10-30). An alias never names an activity, so no step crosses between an
activity and a suspendable type (`sameStep_isComputation`), whatever the bounds say.
It is symmetric but not transitive: `α₁ := Nat`, `α₂ := Nat` gives `α₁ ~ Nat ~ α₂`
and no step `α₁ ~ α₂`. `legacySameType` is its equivalence closure. -/
def sameStep (assumptions : Assumptions) (actual expected : Ty) : Bool :=
  actual.canonical == expected.canonical ||
    (match actual with
      | .variable index => !expected.isComputation &&
          (assumptions.alias index).map Ty.canonical == some expected.canonical
      | _ => false) ||
    (match expected with
      | .variable index => !actual.isComputation &&
          (assumptions.alias index).map Ty.canonical == some actual.canonical
      | _ => false)

theorem sameStep_isComputation {assumptions : Assumptions} {actual expected : Ty}
    (agreement : sameStep assumptions actual expected = true) :
    actual.isComputation = expected.isComputation := by
  simp only [sameStep,Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasActual) | aliasExpected
  · rw [← Ty.canonical_isComputation actual, ← Ty.canonical_isComputation expected]
    simpa using congrArg Ty.isComputation (by simpa using canonical : actual.canonical = expected.canonical)
  · cases actual <;> simp at aliasActual
    simp_all [Ty.isComputation]
  · cases expected <;> simp at aliasExpected
    simp_all [Ty.isComputation]

theorem sameStep_symm_of {assumptions : Assumptions} {actual expected : Ty}
    (agreement : sameStep assumptions actual expected = true) : sameStep assumptions expected actual = true := by
  simp only [sameStep, Bool.or_eq_true] at agreement ⊢
  rcases agreement with (c | x) | y
  · exact .inl (.inl (by simpa using (by simpa using c : actual.canonical = expected.canonical).symm))
  · exact .inr x
  · exact .inl (.inr y)

theorem sameStep_symm (assumptions : Assumptions) (actual expected : Ty) :
    sameStep assumptions actual expected = sameStep assumptions expected actual := by
  cases h : sameStep assumptions actual expected
  · cases h' : sameStep assumptions expected actual
    · rfl
    · rw [sameStep_symm_of h'] at h; cases h
  · exact (sameStep_symm_of h).symm

/-- A canonical type with its declared alias head unfolded once: a transparent alias
variable whose bound is not an activity becomes its bound's canonical form; every
other type (rigid, unbound, any non-variable) is a fixed point. -/
def Assumptions.unfoldHead (assumptions : Assumptions) : Ty → Ty
  | .variable index => match assumptions.alias index with
    | some bound => if bound.isComputation then .variable index else bound.canonical
    | none => .variable index
  | other => other

/-- `k` head unfoldings. -/
def Assumptions.chase (assumptions : Assumptions) : Nat → Ty → Ty
  | 0, type => type
  | k + 1, type => assumptions.chase k (assumptions.unfoldHead type)

/-- The first `k + 1` points of a type's head-unfolding orbit. -/
def Assumptions.orbit (assumptions : Assumptions) : Nat → Ty → List Ty
  | 0, type => [type]
  | k + 1, type => type :: assumptions.orbit k (assumptions.unfoldHead type)

/-- Type agreement: the equivalence closure of `sameStep`, decided. Two types agree
when the head-unfolding orbits of their canonical forms meet within as many steps as
there are declared bounds (`Assumptions.chase_bounded`: no orbit has a point it does
not reach that soon). Unfolding is hereditary along alias heads and stops at a rigid
variable, an unbound one, a non-variable, or a cycle; it does not descend into
constructors, so `α → Bool` and `Nat → Bool` stay distinct (as they were). Rigid
variables stay nominal: `Assumptions.alias` never unfolds one. An equivalence
(`legacySameType_equivalence`); an alias never names an activity (`legacySameType_isComputation`). -/
def legacySameType (assumptions : Assumptions) (actual expected : Ty) : Bool :=
  actual.canonical == expected.canonical ||
    (assumptions.orbit assumptions.bounds.length actual.canonical).any
      (fun point => (assumptions.orbit assumptions.bounds.length expected.canonical).contains point)

/-! ### `legacySameType` is the equivalence closure of `sameStep` -/

theorem Assumptions.chase_add (assumptions : Assumptions) (a : Nat) : ∀ (b : Nat) (type : Ty),
    assumptions.chase (a + b) type = assumptions.chase a (assumptions.chase b type)
  | 0, _ => rfl
  | b + 1, type => by
    show assumptions.chase (a + b) (assumptions.unfoldHead type) = _
    rw [Assumptions.chase_add assumptions a b]; rfl

theorem Assumptions.chase_succ' (assumptions : Assumptions) (k : Nat) (type : Ty) :
    assumptions.chase (k + 1) type = assumptions.unfoldHead (assumptions.chase k type) := by
  rw [Nat.add_comm, Assumptions.chase_add]; rfl

theorem Assumptions.mem_orbit (assumptions : Assumptions) : ∀ (k : Nat) (type point : Ty),
    point ∈ assumptions.orbit k type ↔ ∃ i, i ≤ k ∧ assumptions.chase i type = point
  | 0, type, point => by
    simp only [Assumptions.orbit, List.mem_singleton]
    constructor
    · intro h; exact ⟨0, Nat.le_refl _, h.symm⟩
    · rintro ⟨i, hi, rfl⟩; cases Nat.le_zero.mp hi; rfl
  | k + 1, type, point => by
    simp only [Assumptions.orbit, List.mem_cons, Assumptions.mem_orbit assumptions k]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, Nat.zero_le _, rfl⟩
      · exact ⟨i + 1, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => exact .inl rfl
      | succ i => exact .inr ⟨i, by omega, rfl⟩

theorem legacySameType_iff (assumptions : Assumptions) (actual expected : Ty) :
    legacySameType assumptions actual expected = true ↔
      ∃ i j, i ≤ assumptions.bounds.length ∧ j ≤ assumptions.bounds.length ∧
        assumptions.chase i actual.canonical = assumptions.chase j expected.canonical := by
  simp only [legacySameType, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem,
    Assumptions.mem_orbit]
  constructor
  · rintro (h | ⟨point, ⟨i, hi, rfl⟩, ⟨j, hj, hp⟩⟩)
    · exact ⟨0, 0, Nat.zero_le _, Nat.zero_le _, h⟩
    · exact ⟨i, j, hi, hj, hp.symm⟩
  · rintro ⟨i, j, hi, hj, h⟩
    exact .inr ⟨_, ⟨i, hi, rfl⟩, ⟨j, hj, h.symm⟩⟩

/-- A duplicate-free list drawn from `keys` is no longer than `keys`. -/
theorem nodup_length_le {α : Type} [DecidableEq α] : ∀ {l keys : List α},
    l.Nodup → (∀ x ∈ l, x ∈ keys) → l.length ≤ keys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, keys, nd, sub => by
    have hx : x ∈ keys := sub x (List.mem_cons_self ..)
    have nx : x ∉ xs := (List.nodup_cons.mp nd).1
    have sub' : ∀ y ∈ xs, y ∈ keys.erase x := fun y hy =>
      (List.mem_erase_of_ne (by intro e; subst e; exact nx hy)).mpr (sub y (List.mem_cons_of_mem _ hy))
    have := nodup_length_le (List.nodup_cons.mp nd).2 sub'
    rw [List.length_erase_of_mem hx] at this
    have : 0 < keys.length := List.length_pos_of_mem hx
    simp only [List.length_cons]; omega

theorem Assumptions.alias_key {assumptions : Assumptions} {index : Nat} {bound : Ty}
    (found : assumptions.alias index = some bound) :
    Ty.variable index ∈ assumptions.bounds.map (fun entry => Ty.variable entry.1) := by
  have found := Assumptions.alias_bound found
  generalize assumptions.bounds = bounds at found ⊢
  induction bounds with
  | nil => simp at found
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases h : index = key
    · subst h; exact List.mem_cons_self ..
    · have : rest.lookup index = some bound := by
        simpa [List.lookup, show (index == key) = false from by simpa using h] using found
      exact List.mem_cons_of_mem _ (ih this)

/-- Every point of a head-unfolding orbit is reached within as many steps as there
are declared bounds: either the orbit reaches a fixed point, or two of its first
`bounds.length + 1` points are the same alias variable and it cycles. -/
theorem Assumptions.chase_bounded (assumptions : Assumptions) (type : Ty) (m : Nat) :
    ∃ m', m' ≤ assumptions.bounds.length ∧ assumptions.chase m' type = assumptions.chase m type := by
  let N := assumptions.bounds.length
  by_cases fixed : ∃ k, k ≤ N ∧ assumptions.unfoldHead (assumptions.chase k type) = assumptions.chase k type
  · obtain ⟨k, hk, hfix⟩ := fixed
    have stay : ∀ d, assumptions.chase (k + d) type = assumptions.chase k type := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih => rw [← Nat.add_assoc, Assumptions.chase_succ', ih, hfix]
    by_cases hm : m ≤ k
    · exact ⟨m, Nat.le_trans hm hk, rfl⟩
    · refine ⟨k, hk, ?_⟩
      have := stay (m - k)
      rw [show k + (m - k) = m by omega] at this
      exact this.symm
  · -- every one of the first N + 1 points is a distinct-or-repeating alias variable
    have moving : ∀ k, k ≤ N → assumptions.chase k type ∈
        assumptions.bounds.map (fun entry => Ty.variable entry.1) := by
      intro k hk
      have nf : assumptions.unfoldHead (assumptions.chase k type) ≠ assumptions.chase k type :=
        fun h => fixed ⟨k, hk, h⟩
      generalize assumptions.chase k type = point at nf
      cases point with
      | «variable» index =>
        cases found : assumptions.alias index with
        | none => simp [Assumptions.unfoldHead, found] at nf
        | some bound => exact Assumptions.alias_key found
      | _ => simp [Assumptions.unfoldHead] at nf
    let l := (List.range (N + 1)).map (fun k => assumptions.chase k type)
    have notNodup : ¬ l.Nodup := by
      intro nd
      have := nodup_length_le nd (by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
        exact moving k (by simpa [Nat.lt_succ_iff] using List.mem_range.mp hk))
      simp [l, N] at this
      omega
    have ⟨p, q, hp, hq, hpq, same⟩ : ∃ p q, p ≤ N ∧ q ≤ N ∧ p < q ∧
        assumptions.chase p type = assumptions.chase q type := by
      unfold List.Nodup at notNodup
      rw [List.pairwise_iff_getElem] at notNodup
      simp only [Classical.not_forall, Classical.not_not] at notNodup
      obtain ⟨i, j, hi, hj, hij, same⟩ := notNodup
      simp only [l, List.length_map, List.length_range] at hi hj
      refine ⟨i, j, by omega, by omega, hij, ?_⟩
      simpa [l] using same
    -- periodic from p with period q - p
    have period : ∀ d, assumptions.chase (q + d) type = assumptions.chase (p + d) type := by
      intro d
      rw [Nat.add_comm q d, Nat.add_comm p d, Assumptions.chase_add, Assumptions.chase_add, same]
    have reduce : ∀ n m, m < n → ∃ m', m' < q ∧ assumptions.chase m' type = assumptions.chase m type := by
      intro n
      induction n with
      | zero => intro m h; omega
      | succ n ih =>
        intro m hmn
        by_cases hm : m < q
        · exact ⟨m, hm, rfl⟩
        · obtain ⟨m', hm', e⟩ := ih (p + (m - q)) (by omega)
          refine ⟨m', hm', ?_⟩
          rw [e, ← period, show q + (m - q) = m by omega]
    obtain ⟨m', hm', e⟩ := reduce (m + 1) m (Nat.lt_succ_self m)
    exact ⟨m', by omega, e⟩

theorem legacySameType_refl (assumptions : Assumptions) (type : Ty) : legacySameType assumptions type type = true := by
  simp [legacySameType]

theorem legacySameType_symm {assumptions : Assumptions} {actual expected : Ty}
    (agreement : legacySameType assumptions actual expected = true) : legacySameType assumptions expected actual = true := by
  obtain ⟨i, j, hi, hj, h⟩ := (legacySameType_iff _ _ _).1 agreement
  exact (legacySameType_iff _ _ _).2 ⟨j, i, hj, hi, h.symm⟩

theorem legacySameType_trans {assumptions : Assumptions} {first middle last : Ty}
    (one : legacySameType assumptions first middle = true) (two : legacySameType assumptions middle last = true) :
    legacySameType assumptions first last = true := by
  obtain ⟨i, j, -, -, h₁⟩ := (legacySameType_iff _ _ _).1 one
  obtain ⟨k, l, -, -, h₂⟩ := (legacySameType_iff _ _ _).1 two
  obtain ⟨a, ha, ea⟩ := assumptions.chase_bounded first.canonical (k + i)
  obtain ⟨c, hc, ec⟩ := assumptions.chase_bounded last.canonical (j + l)
  refine (legacySameType_iff _ _ _).2 ⟨a, c, ha, hc, ?_⟩
  rw [ea, ec, Assumptions.chase_add, h₁, ← Assumptions.chase_add, Nat.add_comm k j,
    Assumptions.chase_add, h₂, ← Assumptions.chase_add, Nat.add_comm]

/-- Type agreement is an equivalence on types. -/
theorem legacySameType_equivalence (assumptions : Assumptions) :
    Equivalence (fun actual expected => legacySameType assumptions actual expected = true) :=
  ⟨legacySameType_refl assumptions, legacySameType_symm, legacySameType_trans⟩

/-- A finite chain of agreement steps, in either direction. -/
inductive SameChain (assumptions : Assumptions) : Ty → Ty → Prop where
  | refl (type : Ty) : SameChain assumptions type type
  | step {first middle last : Ty} : SameChain assumptions first middle →
      sameStep assumptions middle last = true → SameChain assumptions first last

theorem SameChain.trans {assumptions : Assumptions} {first middle last : Ty}
    (one : SameChain assumptions first middle) (two : SameChain assumptions middle last) :
    SameChain assumptions first last := by
  induction two with
  | refl => exact one
  | step _ agreement ih => exact .step ih agreement

theorem SameChain.symm {assumptions : Assumptions} {first last : Ty}
    (chain : SameChain assumptions first last) : SameChain assumptions last first := by
  induction chain with
  | refl => exact .refl _
  | step _ agreement ih =>
    exact SameChain.trans (.step (.refl _) (by rw [sameStep_symm]; exact agreement)) ih

theorem sameStep_legacySameType {assumptions : Assumptions} {actual expected : Ty}
    (agreement : sameStep assumptions actual expected = true) : legacySameType assumptions actual expected = true := by
  have viaAlias : ∀ {index : Nat} {other : Ty}, (!other.isComputation) = true →
      (assumptions.alias index).map Ty.canonical = some other.canonical →
      legacySameType assumptions (.variable index) other = true := by
    intro index other pure found
    have pure : other.isComputation = false := by simpa using pure
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at found
    | some bound =>
      have equal : bound.canonical = other.canonical := by simpa [aliased] using found
      have boundPure : bound.isComputation = false := by
        rw [← Ty.canonical_isComputation, equal, Ty.canonical_isComputation]; exact pure
      have positive : 1 ≤ assumptions.bounds.length := by
        have := Assumptions.alias_key aliased
        have := List.length_pos_of_mem this
        rw [List.length_map] at this
        exact Nat.succ_le_of_lt this
      refine (legacySameType_iff _ _ _).2 ⟨1, 0, positive, Nat.zero_le _, ?_⟩
      simp [Assumptions.chase, Assumptions.unfoldHead, Ty.canonical, aliased, boundPure, equal]
  simp only [sameStep, Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasActual) | aliasExpected
  · simp [legacySameType, (by simpa using canonical : actual.canonical = expected.canonical)]
  · cases actual with
    | «variable» index =>
      exact viaAlias (Bool.and_eq_true_iff.mp aliasActual).1 (by simpa using (Bool.and_eq_true_iff.mp aliasActual).2)
    | _ => simp at aliasActual
  · cases expected with
    | «variable» index =>
    exact legacySameType_symm (viaAlias (Bool.and_eq_true_iff.mp aliasExpected).1
      (by simpa using (Bool.and_eq_true_iff.mp aliasExpected).2))
    | _ => simp at aliasExpected

theorem SameChain.legacySameType {assumptions : Assumptions} {first last : Ty}
    (chain : SameChain assumptions first last) : legacySameType assumptions first last = true := by
  induction chain with
  | refl => exact legacySameType_refl _ _
  | step _ agreement ih => exact legacySameType_trans ih (sameStep_legacySameType agreement)

theorem Ty.canonical_variable_eq {type : Ty} {index : Nat} (equal : type.canonical = .variable index) :
    type = .variable index := by
  cases type <;> simp [Ty.canonical] at equal ⊢
  · exact equal
  · rename_i name member tail
    revert equal
    generalize tail.canonical = row
    cases row <;> simp only [Ty.insertCanonical]
    all_goals repeat' first | split
    all_goals simp

/-- Every point of the orbit of a type's canonical form is the canonical form of a
type a chain of steps reaches. -/
theorem Assumptions.chase_chain (assumptions : Assumptions) (type : Ty) : ∀ k,
    ∃ reached, SameChain assumptions type reached ∧
      reached.canonical = assumptions.chase k type.canonical
  | 0 => ⟨type, .refl _, rfl⟩
  | k + 1 => by
    obtain ⟨reached, chain, equal⟩ := assumptions.chase_chain type k
    rw [Assumptions.chase_succ', ← equal]
    cases point : reached.canonical with
    | «variable» index =>
      have isVar := Ty.canonical_variable_eq point
      subst isVar
      cases aliased : assumptions.alias index with
      | none => exact ⟨_, chain, by simp [Assumptions.unfoldHead, aliased, Ty.canonical]⟩
      | some bound =>
        by_cases pure : bound.isComputation = true
        · exact ⟨_, chain, by simp [Assumptions.unfoldHead, aliased, pure, Ty.canonical]⟩
        · refine ⟨bound, .step chain ?_, by simp [Assumptions.unfoldHead, aliased, pure]⟩
          simp [sameStep, aliased, pure]
    | _ => exact ⟨reached, chain, by simp [point, Assumptions.unfoldHead]⟩

/-- Agreement decomposes into steps: every lemma proved of one step lifts. -/
theorem legacySameType_chain {assumptions : Assumptions} {actual expected : Ty}
    (agreement : legacySameType assumptions actual expected = true) : SameChain assumptions actual expected := by
  obtain ⟨i, j, -, -, h⟩ := (legacySameType_iff _ _ _).1 agreement
  obtain ⟨a, chainA, ea⟩ := assumptions.chase_chain actual i
  obtain ⟨e, chainE, ee⟩ := assumptions.chase_chain expected j
  have step : sameStep assumptions a e = true := by simp [sameStep, ea, ee, h]
  exact SameChain.trans (.step chainA step) chainE.symm

/-- Lifting: a transitive, reflexive relation that holds across one step holds across
every agreement. -/
theorem legacySameType_lift {assumptions : Assumptions} (P : Ty → Ty → Prop)
    (refl : ∀ type, P type type) (trans : ∀ {a b c}, P a b → P b c → P a c)
    (step : ∀ {a b}, sameStep assumptions a b = true → P a b)
    {actual expected : Ty} (agreement : legacySameType assumptions actual expected = true) : P actual expected := by
  have chain := legacySameType_chain agreement
  clear agreement
  induction chain with
  | refl => exact refl _
  | step _ agreement ih => exact trans ih (step agreement)

theorem legacySameType_isComputation {assumptions : Assumptions} {actual expected : Ty}
    (agreement : legacySameType assumptions actual expected = true) :
    actual.isComputation = expected.isComputation := by
  have chain := legacySameType_chain agreement
  clear agreement
  induction chain with
  | refl => rfl
  | step _ agreement ih => exact ih.trans (sameStep_isComputation agreement)

#assert_axioms sameStep_isComputation sameStep_symm_of sameStep_symm Assumptions.chase_add
  Assumptions.chase_succ' Assumptions.mem_orbit legacySameType_iff nodup_length_le
  Assumptions.alias_key Assumptions.chase_bounded legacySameType_refl legacySameType_symm
  legacySameType_trans legacySameType_equivalence SameChain.trans SameChain.symm
  sameStep_legacySameType SameChain.legacySameType Ty.canonical_variable_eq Assumptions.chase_chain
  legacySameType_chain legacySameType_lift legacySameType_isComputation

end Obend.Core.Check
