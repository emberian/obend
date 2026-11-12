module
public import Obend.Crypto.Multilinear
public import Obend.Tactic.Tooth
public import Std

public section
set_option autoImplicit false
namespace Obend.SymbolicZk.Datalog
open Std

class ProvenanceSemiringOps (K : Type) where
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K

class LawfulProvenanceSemiring (K : Type) extends ProvenanceSemiringOps K where
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_mul : ∀ a, mul zero a = zero
  mul_zero : ∀ a, mul a zero = zero

instance : LawfulProvenanceSemiring Bool where
  zero := false
  one := true
  add := (· || ·)
  mul := (· && ·)
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  add_zero := by decide
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide

instance : LawfulProvenanceSemiring Nat where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  left_distrib := Nat.mul_add
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

/-- `none` is infinity, rather than the (finite) zero-cost multiplicative unit. -/
structure TropicalMinCost where
  cost : Option Nat
  deriving DecidableEq, Repr

@[expose] def tropicalAdd (a b : TropicalMinCost) : TropicalMinCost :=
  ⟨match a.cost, b.cost with
   | none, y => y
   | x, none => x
   | some x, some y => some (min x y)⟩

@[expose] def tropicalMul (a b : TropicalMinCost) : TropicalMinCost :=
  ⟨match a.cost, b.cost with
   | some x, some y => some (x + y)
   | _, _ => none⟩

instance : LawfulProvenanceSemiring TropicalMinCost where
  zero := ⟨none⟩
  one := ⟨some 0⟩
  add := tropicalAdd
  mul := tropicalMul
  add_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    cases a <;> cases b <;> cases c <;> simp [tropicalAdd, Nat.min_assoc]
  add_comm := by
    rintro ⟨a⟩ ⟨b⟩
    cases a <;> cases b <;> simp [tropicalAdd, Nat.min_comm]
  zero_add := by rintro ⟨a⟩; cases a <;> rfl
  add_zero := by rintro ⟨a⟩; cases a <;> rfl
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    cases a <;> cases b <;> cases c <;> simp [tropicalMul, Nat.add_assoc]
  mul_comm := by
    rintro ⟨a⟩ ⟨b⟩
    cases a <;> cases b <;> simp [tropicalMul, Nat.add_comm]
  one_mul := by rintro ⟨a⟩; cases a <;> simp [tropicalMul]
  mul_one := by rintro ⟨a⟩; cases a <;> simp [tropicalMul]
  left_distrib := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    cases a <;> cases b <;> cases c <;> simp [tropicalAdd, tropicalMul, Nat.add_min_add_left]
  zero_mul := by rintro ⟨a⟩; cases a <;> rfl
  mul_zero := by rintro ⟨a⟩; cases a <;> rfl

instance : LawfulProvenanceSemiring Obend.Crypto.Goldilocks where
  zero := Obend.Crypto.CommRingOps.zero
  one := Obend.Crypto.CommRingOps.one
  add := Obend.Crypto.CommRingOps.add
  mul := Obend.Crypto.CommRingOps.mul
  add_assoc := Obend.Crypto.LawfulCommRing.add_assoc
  add_comm := Obend.Crypto.LawfulCommRing.add_comm
  zero_add := Obend.Crypto.LawfulCommRing.zero_add
  add_zero := Obend.Crypto.LawfulCommRing.add_zero
  mul_assoc := Obend.Crypto.LawfulCommRing.mul_assoc
  mul_comm := Obend.Crypto.LawfulCommRing.mul_comm
  one_mul := Obend.Crypto.LawfulCommRing.one_mul
  mul_one := Obend.Crypto.LawfulCommRing.mul_one
  left_distrib := Obend.Crypto.LawfulCommRing.left_distrib
  zero_mul := Obend.Crypto.LawfulCommRing.zero_mul
  mul_zero := Obend.Crypto.LawfulCommRing.mul_zero

abbrev RelId := Nat
abbrev SymId := Nat

/-- Arity is checked against a schema, so different relations may have different arities. -/
structure GroundTuple where
  rel : RelId
  args : Array SymId
  deriving DecidableEq, Repr, Inhabited

@[expose] def GroundTuple.HasArity (arity : RelId → Nat) (t : GroundTuple) : Prop :=
  t.args.size = arity t.rel

/-- The standard lexicographic comparator reads the argument array directly. -/
@[expose] def tupleCmp (a b : GroundTuple) : Ordering :=
  compareLex (compareOn GroundTuple.rel) (compareOn GroundTuple.args) a b

instance : TransCmp tupleCmp :=
  inferInstanceAs (TransCmp (compareLex (compareOn GroundTuple.rel) (compareOn GroundTuple.args)))

@[expose] def TupleLt (a b : GroundTuple) : Prop := tupleCmp a b = .lt

instance (a b : GroundTuple) : Decidable (TupleLt a b) := inferInstanceAs (Decidable (_ = _))

theorem lt_irrefl (a : GroundTuple) : ¬ TupleLt a a := by
  simp [TupleLt, ReflCmp.compare_self]

theorem lt_trans {a b c : GroundTuple} (hab : TupleLt a b) (hbc : TupleLt b c) : TupleLt a c :=
  TransCmp.lt_trans hab hbc

theorem eq_of_cmp_eq {a b : GroundTuple} (h : tupleCmp a b = .eq) : a = b := by
  have he := compareLex_eq_eq.mp h
  have hr : a.rel = b.rel := LawfulEqOrd.eq_of_compare he.1
  have ha : a.args = b.args := LawfulEqOrd.eq_of_compare he.2
  cases a; cases b
  simp_all

theorem lt_asymm {a b : GroundTuple} (hab : TupleLt a b) : ¬ TupleLt b a :=
  fun hba => lt_irrefl a (lt_trans hab hba)

theorem tuple_trichotomy (a b : GroundTuple) : TupleLt a b ∨ a = b ∨ TupleLt b a := by
  cases hc : tupleCmp a b with
  | lt => exact Or.inl hc
  | eq => exact Or.inr (Or.inl (eq_of_cmp_eq hc))
  | gt => exact Or.inr (Or.inr (OrientedCmp.lt_of_gt hc))

abbrev KRelationSpec (K : Type) := GroundTuple → K

/-- Explicit finite support; zero weights may cancel even in a lawful semiring. -/
def FiniteSupport {K : Type} [ProvenanceSemiringOps K] (v : KRelationSpec K) : Prop :=
  ∃ keys : Array GroundTuple, ∀ q, v q ≠ ProvenanceSemiringOps.zero → q ∈ keys

structure SortedKTable (K : Type) where
  entries : Array (GroundTuple × K)

open ProvenanceSemiringOps

/-- Pairwise sortedness is a proof invariant, not a quadratic runtime check. -/
def SortedKTable.WF {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K) : Prop :=
  (∀ (i j : Fin t.entries.size), i.val < j.val → TupleLt t.entries[i.val].1 t.entries[j.val].1) ∧
  (∀ i : Fin t.entries.size, t.entries[i.val].2 ≠ zero)

/-- Half-open binary search. The fuel is only a termination bound; each recursive call
halves the remaining interval. All table accesses are direct array reads. -/
def search {K : Type} (es : Array (GroundTuple × K)) (q : GroundTuple) :
    Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if h : mid < es.size then
        match tupleCmp q es[mid].1 with
        | .lt => search es q fuel lo mid
        | .eq => some mid
        | .gt => search es q fuel (mid + 1) hi
      else none
    else none

/-- O(log n) comparisons, each costing O(arity) in the worst case. -/
def lookupFast {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K) (q : GroundTuple) : K :=
  match search t.entries q (t.entries.size + 1) 0 t.entries.size with
  | none => zero
  | some i => (t.entries[i]?.map Prod.snd).getD zero

/-- Declarative lookup, independent of binary-search control flow. -/
def lookupSpec {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K) (q : GroundTuple) : K :=
  ((t.entries.toList.find? (fun e => e.1 == q)).map Prod.snd).getD zero

inductive GapCert where
  | emptyTable
  | belowFirst
  | aboveLast
  | adjacentGap (i : Nat)
  deriving DecidableEq, Repr

/-- At most two direct reads. Bounds and strictness are checked, not asserted by the prover. -/
def verifyGapCert {K : Type} (t : SortedKTable K) (q : GroundTuple) : GapCert → Bool
  | .emptyTable => t.entries.size == 0
  | .belowFirst => if h : 0 < t.entries.size then decide (TupleLt q t.entries[0].1) else false
  | .aboveLast => if h : 0 < t.entries.size then
      decide (TupleLt t.entries[t.entries.size - 1].1 q) else false
  | .adjacentGap i => if h : i + 1 < t.entries.size then
      decide (TupleLt t.entries[i].1 q) && decide (TupleLt q t.entries[i + 1].1) else false

/-- Fully grounded rules: this table is the complete grounding, not a prover-selected join subset. -/
structure GroundRule where
  head : GroundTuple
  body : Array GroundTuple
  deriving Repr

def evalRuleSpec {K : Type} [ProvenanceSemiringOps K] (v : KRelationSpec K) (r : GroundRule) : K :=
  r.body.foldl (fun w q => mul w (v q)) one

def tpSpec {K : Type} [ProvenanceSemiringOps K] (p : Array GroundRule)
    (v : KRelationSpec K) (q : GroundTuple) : K :=
  p.foldl (fun w r => if r.head = q then add w (evalRuleSpec v r) else w) zero



private theorem index_lt_of_key_lt {K : Type} [ProvenanceSemiringOps K] {t : SortedKTable K}
    (hw : t.WF) (i j : Fin t.entries.size) (h : TupleLt t.entries[i.val].1 t.entries[j.val].1) : i.val < j.val := by
  by_cases hij : i.val < j.val
  · exact hij
  · by_cases he : i = j
    · subst j; exact False.elim (lt_irrefl _ h)
    · have hji : j.val < i.val := by have hne : i.val ≠ j.val := fun h => he (Fin.ext h); omega
      exact False.elim (lt_asymm h (hw.1 j i hji))

private theorem index_eq_of_key_eq {K : Type} [ProvenanceSemiringOps K] {t : SortedKTable K}
    (hw : t.WF) (i j : Fin t.entries.size) (h : t.entries[i.val].1 = t.entries[j.val].1) : i = j := by
  by_cases hlt : i.val < j.val
  · have hlt' := hw.1 i j hlt
    rw [h] at hlt'
    exact False.elim (lt_irrefl _ hlt')
  · by_cases hgt : j.val < i.val
    · have hgt' := hw.1 j i hgt
      rw [h] at hgt'
      exact False.elim (lt_irrefl _ hgt')
    · apply Fin.ext; omega

/-- An existing key is found by the logarithmic search, at its unique index. -/
theorem search_find {K : Type} [ProvenanceSemiringOps K] {t : SortedKTable K}
    (hw : t.WF) (q : GroundTuple) (i : Fin t.entries.size) (hq : q = t.entries[i.val].1)
    (fuel lo hi : Nat) (hlo : lo ≤ i.val) (hhi : i.val < hi) (hb : hi ≤ t.entries.size)
    (hf : hi - lo < fuel) : search t.entries q fuel lo hi = some i.val := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ f ih =>
    have hlh : lo < hi := by omega
    let mid := (lo + hi) / 2
    have hml : lo ≤ mid := by dsimp [mid]; omega
    have hmh : mid < hi := by dsimp [mid]; omega
    have hm : mid < t.entries.size := by omega
    have hm' : (lo + hi) / 2 < t.entries.size := hm
    simp only [search, hlh, ↓reduceIte, hm']
    change (match tupleCmp q t.entries[mid].1 with
      | .lt => search t.entries q f lo mid
      | .eq => some mid
      | .gt => search t.entries q f (mid + 1) hi) = some i.val
    cases hc : tupleCmp q t.entries[mid].1 with
    | lt =>
      have hil := index_lt_of_key_lt hw i ⟨mid, hm⟩ (by simpa only [hq, TupleLt] using hc)
      exact ih lo mid hlo hil (by omega) (by omega)
    | eq =>
      have he := index_eq_of_key_eq hw i ⟨mid, hm⟩ (hq.symm.trans (eq_of_cmp_eq hc))
      exact congrArg some (congrArg Fin.val he).symm
    | gt =>
      have hmi := index_lt_of_key_lt hw ⟨mid, hm⟩ i (by
        simpa only [hq, TupleLt] using (OrientedCmp.lt_of_gt hc))
      dsimp at hmi
      exact ih (mid + 1) hi (by omega) hhi hb (by omega)

/-- Search never manufactures an index or reports a different key. -/
theorem search_some {K : Type} (es : Array (GroundTuple × K)) (q : GroundTuple)
    (fuel lo hi i : Nat) (h : search es q fuel lo hi = some i) :
    ∃ hb : i < es.size, es[i].1 = q := by
  induction fuel generalizing lo hi with
  | zero => simp [search] at h
  | succ f ih =>
    simp only [search] at h
    split at h
    · split at h
      · split at h
        · exact ih _ _ h
        · have he : (lo + hi) / 2 = i := Option.some.inj h
          subst i
          exact ⟨by assumption, (eq_of_cmp_eq (by assumption)).symm⟩
        · exact ih _ _ h
      · cases h
    · cases h

theorem lookupFast_eq_spec {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K)
    (hw : t.WF) (q : GroundTuple) : lookupFast t q = lookupSpec t q := by
  unfold lookupSpec lookupFast
  cases hh : t.entries.toList.find? (fun e => e.1 == q) with
  | none =>
    have hn := List.find?_eq_none.mp hh
    cases hs : search t.entries q (t.entries.size + 1) 0 t.entries.size with
    | none => rfl
    | some i =>
      obtain ⟨hi, he⟩ := search_some _ _ _ _ _ _ hs
      have hm : t.entries[i] ∈ t.entries.toList := by simp
      have hc := hn _ hm
      simp [he] at hc
  | some e =>
    have hm : e ∈ t.entries := by simpa using List.mem_of_find?_eq_some hh
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hm
    have hkey : e.1 = q := by simpa using (List.find?_some hh)
    rw [search_find hw q ⟨i, hi⟩ (by rw [he, hkey]) _ _ _ (by omega) hi (by omega) (by omega)]
    dsimp only
    rw [Array.getElem?_eq_some_getElem t.entries i hi]
    simp [he]

/-- Absence in the authenticated sorted table implies zero lookup. -/
theorem lookupFast_of_absent {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K)
    (q : GroundTuple) (ha : ∀ i : Fin t.entries.size, t.entries[i.val].1 ≠ q) :
    lookupFast t q = zero := by
  unfold lookupFast
  cases hs : search t.entries q (t.entries.size + 1) 0 t.entries.size with
  | none => rfl
  | some i =>
    obtain ⟨hi, he⟩ := search_some _ _ _ _ _ _ hs
    exact False.elim (ha ⟨i, hi⟩ he)

theorem absent_of_lookupFast {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K)
    (hw : t.WF) (q : GroundTuple) (h : lookupFast t q = zero) :
    ∀ i : Fin t.entries.size, t.entries[i.val].1 ≠ q := by
  intro i hi
  unfold lookupFast at h
  rw [search_find hw q i hi.symm _ _ _ (by omega) i.isLt (by omega) (by omega)] at h
  dsimp only at h
  rw [Array.getElem?_eq_some_getElem t.entries i.val i.isLt] at h
  simp only [Option.map_some, Option.getD_some] at h
  exact hw.2 i h

/-- All four gap forms establish genuine key absence using sortedness globally. -/
theorem gap_absent {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K)
    (hw : t.WF) (q : GroundTuple) (cert : GapCert) (h : verifyGapCert t q cert = true) :
    ∀ j : Fin t.entries.size, t.entries[j.val].1 ≠ q := by
  intro j he
  cases cert with
  | emptyTable => have hz : t.entries.size = 0 := by simpa [verifyGapCert] using h
                  have := j.isLt; omega
  | belowFirst =>
    simp only [verifyGapCert] at h
    split at h
    · rename_i hn
      have hq : TupleLt q t.entries[0].1 := of_decide_eq_true h
      by_cases hj : j.val = 0
      · have he' : t.entries[0].1 = q := by
          change t.entries[j.val].1 = q at he
          simpa only [hj] using he
        rw [he'] at hq
        exact lt_irrefl _ hq
      · exact lt_asymm hq (by simpa only [he] using hw.1 ⟨0, hn⟩ j (by change 0 < j.val; omega))
    · cases h
  | aboveLast =>
    simp only [verifyGapCert] at h
    split at h
    · rename_i hn
      have hq : TupleLt t.entries[t.entries.size - 1].1 q := of_decide_eq_true h
      by_cases hj : j.val = t.entries.size - 1
      · have he' : t.entries[t.entries.size - 1].1 = q := by
          change t.entries[j.val].1 = q at he
          simpa only [hj] using he
        rw [he'] at hq
        exact lt_irrefl _ hq
      · exact lt_asymm hq (by simpa only [he] using hw.1 j ⟨t.entries.size - 1, by omega⟩ (by change j.val < t.entries.size - 1; omega))
    · cases h
  | adjacentGap i =>
    simp only [verifyGapCert] at h
    split at h
    · rename_i hn
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
      have hl : TupleLt t.entries[i].1 q := of_decide_eq_true hl
      have hr : TupleLt q t.entries[i + 1].1 := of_decide_eq_true hr
      have hleft := index_lt_of_key_lt hw ⟨i, by omega⟩ j (by simpa only [he] using hl)
      have hright := index_lt_of_key_lt hw j ⟨i + 1, hn⟩ (by simpa only [he] using hr)
      dsimp at hleft hright
      omega
    · cases h

theorem sortedGapNonMembership_sound {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K)
    (hw : t.WF) (q : GroundTuple) (cert : GapCert) (h : verifyGapCert t q cert = true) :
    lookupFast t q = zero := lookupFast_of_absent t q (gap_absent t hw q cert h)

/-- Locate the first key above an absent query. The bounded induction is constructive. -/
theorem verifyGapCert_complete {K : Type} [ProvenanceSemiringOps K]
    (t : SortedKTable K) (hw : t.WF) (q : GroundTuple)
    (hz : lookupFast t q = zero) :
    ∃ c, verifyGapCert (K := K) t q c = true := by
  have ha := absent_of_lookupFast t hw q hz
  by_cases hz : t.entries.size = 0
  · exact ⟨.emptyTable, by simp [verifyGapCert, hz]⟩
  have hn : 0 < t.entries.size := by omega
  have walk : ∀ k, ∀ hk : k < t.entries.size,
      TupleLt t.entries[k].1 q → ∃ c, verifyGapCert (K := K) t q c = true := by
    intro k hk hleft
    induction fuel : t.entries.size - k using Nat.strongRecOn generalizing k with
    | ind fuel ih =>
      by_cases hend : k + 1 < t.entries.size
      · rcases tuple_trichotomy q t.entries[k + 1].1 with hright | heq | hnext
        · exact ⟨.adjacentGap k, by simp [verifyGapCert, hend, hleft, hright]⟩
        · exact False.elim (ha ⟨k + 1, hend⟩ heq.symm)
        · exact ih (t.entries.size - (k + 1)) (by omega) (k + 1) hend hnext rfl
      · have heq : k = t.entries.size - 1 := by omega
        exact ⟨.aboveLast, by simpa [verifyGapCert, hn, ← heq] using hleft⟩
  rcases tuple_trichotomy q t.entries[0].1 with hl | he | hr
  · exact ⟨.belowFirst, by simp [verifyGapCert, hn, hl]⟩
  · exact False.elim (ha ⟨0, hn⟩ he.symm)
  · exact walk 0 hn hr

def evalRuleFast {K : Type} [ProvenanceSemiringOps K]
    (t : SortedKTable K) (r : GroundRule) : K :=
  r.body.foldl (fun w q => mul w (lookupFast t q)) one

theorem evalRuleFast_eq_spec {K : Type} [ProvenanceSemiringOps K]
    (t : SortedKTable K) (r : GroundRule) (hw : t.WF) :
    evalRuleFast t r = evalRuleSpec (lookupSpec t) r := by
  simp only [evalRuleFast, evalRuleSpec, lookupFast_eq_spec t hw]

example : verifyGapCert (⟨#[(⟨1, #[]⟩, true), (⟨3, #[]⟩, true)]⟩ : SortedKTable Bool)
    ⟨2, #[]⟩ (.adjacentGap 0) = true := by simp [verifyGapCert, TupleLt, tupleCmp, compareLex, compareOn, Nat.compare_eq_lt]

/-- List specification for the two-pointer merge. Equal keys are added and a
cancelling sum is removed, so the representation also works over rings. -/
def mergeRows {K : Type} [ProvenanceSemiringOps K] [DecidableEq K] :
    List (GroundTuple × K) → List (GroundTuple × K) → List (GroundTuple × K)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if TupleLt x.1 y.1 then x :: mergeRows xs (y :: ys)
    else if TupleLt y.1 x.1 then y :: mergeRows (x :: xs) ys
    else let w := add x.2 y.2
         if w = zero then mergeRows xs ys else (x.1,w) :: mergeRows xs ys
termination_by xs ys => xs.length + ys.length

@[expose] def RowsWF {K : Type} [ProvenanceSemiringOps K] (xs : List (GroundTuple × K)) : Prop :=
  xs.Pairwise (fun a b => TupleLt a.1 b.1) ∧ ∀ e ∈ xs, e.2 ≠ zero

@[expose] def sumRows {K : Type} [ProvenanceSemiringOps K] (q : GroundTuple) : List (GroundTuple × K) → K
  | [] => zero
  | e :: es => if e.1 = q then add e.2 (sumRows q es) else sumRows q es

private theorem key_eq_of_not_lt (a b : GroundTuple) (hab : ¬ TupleLt a b) (hba : ¬ TupleLt b a) : a = b := by
  rcases tuple_trichotomy a b with h | h | h
  · exact False.elim (hab h)
  · exact h
  · exact False.elim (hba h)

theorem mergeRows_keys {K : Type} [ProvenanceSemiringOps K] [DecidableEq K]
    (xs ys : List (GroundTuple × K)) (q : GroundTuple)
    (h : ∃ e ∈ mergeRows xs ys, e.1 = q) :
    (∃ e ∈ xs, e.1 = q) ∨ (∃ e ∈ ys, e.1 = q) := by
  induction n : xs.length + ys.length using Nat.strongRecOn generalizing xs ys with
  | ind n ih =>
    cases xs with
    | nil => exact Or.inr (by simpa [mergeRows] using h)
    | cons x xs =>
      cases ys with
      | nil => exact Or.inl (by simpa [mergeRows] using h)
      | cons y ys =>
        rw [mergeRows] at h
        split at h
        · obtain ⟨e, he, hq⟩ := h
          rcases List.mem_cons.mp he with he | he
          · exact Or.inl ⟨x, by simp, by simpa [he] using hq⟩
          · rcases ih _ (by simp only [List.length_cons] at n ⊢; omega) xs (y::ys) ⟨e,he,hq⟩ rfl with hl | hr
            · exact Or.inl (by rcases hl with ⟨e,he,hq⟩; exact ⟨e, by simp [he], hq⟩)
            · exact Or.inr hr
        · split at h
          · obtain ⟨e, he, hq⟩ := h
            rcases List.mem_cons.mp he with he | he
            · exact Or.inr ⟨y, by simp, he ▸ hq⟩
            · rcases ih _ (by simp only [List.length_cons] at n ⊢; omega) (x::xs) ys ⟨e,he,hq⟩ rfl with hl | hr
              · exact Or.inl hl
              · exact Or.inr (by rcases hr with ⟨e,he,hq⟩; exact ⟨e, by simp [he], hq⟩)
          · dsimp only at h
            split at h
            · rcases ih _ (by simp only [List.length_cons] at n ⊢; omega) xs ys h rfl with hl | hr
              · exact Or.inl (by rcases hl with ⟨e,he,hq⟩; exact ⟨e, by simp [he], hq⟩)
              · exact Or.inr (by rcases hr with ⟨e,he,hq⟩; exact ⟨e, by simp [he], hq⟩)
            · obtain ⟨e, he, hq⟩ := h
              rcases List.mem_cons.mp he with he | he
              · exact Or.inl ⟨x, by simp, by simpa [he] using hq⟩
              · rcases ih _ (by simp only [List.length_cons] at n ⊢; omega) xs ys ⟨e,he,hq⟩ rfl with hl | hr
                · exact Or.inl (by rcases hl with ⟨e,he,hq⟩; exact ⟨e, by simp [he], hq⟩)
                · exact Or.inr (by rcases hr with ⟨e,he,hq⟩; exact ⟨e, by simp [he], hq⟩)

private theorem rows_cons {K : Type} [ProvenanceSemiringOps K] {x : GroundTuple × K}
    {xs : List (GroundTuple × K)} : RowsWF (x::xs) ↔
      (∀ y ∈ xs, TupleLt x.1 y.1) ∧ RowsWF xs ∧ x.2 ≠ zero := by
  simp [RowsWF, List.pairwise_cons, and_assoc, and_left_comm, and_comm]

private theorem above_merge {K : Type} [ProvenanceSemiringOps K] [DecidableEq K]
    {q : GroundTuple} {xs ys : List (GroundTuple × K)}
    (hx : ∀ e ∈ xs, TupleLt q e.1) (hy : ∀ e ∈ ys, TupleLt q e.1) :
    ∀ e ∈ mergeRows xs ys, TupleLt q e.1 := by
  intro e he
  rcases mergeRows_keys xs ys e.1 ⟨e,he,rfl⟩ with ⟨a,ha,hkey⟩ | ⟨a,ha,hkey⟩
  · rw [← hkey]; exact hx a ha
  · rw [← hkey]; exact hy a ha

theorem mergeRows_wf {K : Type} [ProvenanceSemiringOps K] [DecidableEq K]
    (xs ys : List (GroundTuple × K)) (hx : RowsWF xs) (hy : RowsWF ys) :
    RowsWF (mergeRows xs ys) := by
  induction n : xs.length + ys.length using Nat.strongRecOn generalizing xs ys with
  | ind n ih =>
    cases xs with
    | nil => simpa [mergeRows] using hy
    | cons x xs =>
      cases ys with
      | nil => simpa [mergeRows] using hx
      | cons y ys =>
        have hxs := rows_cons.mp hx
        have hys := rows_cons.mp hy
        rw [mergeRows]
        split
        · rename_i hxy
          apply rows_cons.mpr
          refine ⟨above_merge hxs.1 ?_, ih _ (by simp only [List.length_cons] at n ⊢; omega) xs (y::ys) hxs.2.1 hy rfl, hxs.2.2⟩
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hxy
          · exact lt_trans hxy (hys.1 e he)
        · rename_i hxy
          split
          · rename_i hyx
            apply rows_cons.mpr
            refine ⟨above_merge ?_ hys.1, ih _ (by simp only [List.length_cons] at n ⊢; omega) (x::xs) ys hx hys.2.1 rfl, hys.2.2⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact hyx
            · exact lt_trans hyx (hxs.1 e he)
          · rename_i hyx
            have hkey := key_eq_of_not_lt x.1 y.1 hxy hyx
            have hw := ih _ (by simp only [List.length_cons] at n ⊢; omega) xs ys hxs.2.1 hys.2.1 rfl
            dsimp only
            split
            · exact hw
            · rename_i hn
              exact rows_cons.mpr ⟨above_merge hxs.1 (by simpa [hkey] using hys.1), hw, hn⟩

private theorem add_shuffle {K : Type} [LawfulProvenanceSemiring K] (a b c d : K) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [LawfulProvenanceSemiring.add_assoc, ← LawfulProvenanceSemiring.add_assoc b c d,
    LawfulProvenanceSemiring.add_comm b c, LawfulProvenanceSemiring.add_assoc c b d,
    ← LawfulProvenanceSemiring.add_assoc]

private theorem add_left_comm {K : Type} [LawfulProvenanceSemiring K] (a b c : K) :
    add a (add b c) = add b (add a c) := by
  rw [← LawfulProvenanceSemiring.add_assoc, LawfulProvenanceSemiring.add_comm a b,
    LawfulProvenanceSemiring.add_assoc]

theorem sumRows_merge {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (xs ys : List (GroundTuple × K)) (q : GroundTuple) :
    sumRows q (mergeRows xs ys) = add (sumRows q xs) (sumRows q ys) := by
  induction n : xs.length + ys.length using Nat.strongRecOn generalizing xs ys with
  | ind n ih =>
    cases xs with
    | nil => simp [mergeRows, sumRows, LawfulProvenanceSemiring.zero_add]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeRows, sumRows, LawfulProvenanceSemiring.add_zero]
      | cons y ys =>
        rw [mergeRows]
        split
        · rw [sumRows, ih _ (by simp only [List.length_cons] at n ⊢; omega) xs (y::ys) rfl]
          by_cases he : x.1 = q <;> simp [sumRows, he, LawfulProvenanceSemiring.add_assoc]
        · rename_i hxy
          split
          · rw [sumRows, ih _ (by simp only [List.length_cons] at n ⊢; omega) (x::xs) ys rfl]
            by_cases he : y.1 = q
            · simp only [sumRows, he, ↓reduceIte]
              exact add_left_comm _ _ _
            · simp [sumRows, he]
          · rename_i hyx
            have hkey := key_eq_of_not_lt x.1 y.1 hxy hyx
            have hs := ih _ (by simp only [List.length_cons] at n ⊢; omega) xs ys rfl
            dsimp only
            split
            · rename_i hz
              rw [hs]
              by_cases he : x.1 = q
              · have hey : y.1 = q := hkey.symm.trans he
                simp only [sumRows, he, hey, ↓reduceIte]
                rw [add_shuffle, hz, LawfulProvenanceSemiring.zero_add]
              · simp [sumRows, he, ← hkey]
            · by_cases he : x.1 = q
              · have hey : y.1 = q := hkey.symm.trans he
                simp only [sumRows, he, hey, ↓reduceIte, hs]
                exact (add_shuffle _ _ _ _).symm
              · simp [sumRows, he, ← hkey, hs]

/-- Runtime merge: two slice cursors and a uniquely owned array accumulator. Each
step advances at least one cursor; no sorting, rescanning, or list conversion occurs. -/
def mergeArrayGo {K : Type} [ProvenanceSemiringOps K] [DecidableEq K]
    (xs ys : Subarray (GroundTuple × K)) (out : Array (GroundTuple × K)) : Array (GroundTuple × K) :=
  if hx : 0 < xs.size then
    if hy : 0 < ys.size then
      let x := xs[0]
      let y := ys[0]
      if TupleLt x.1 y.1 then mergeArrayGo (xs.drop 1) ys (out.push x)
      else if TupleLt y.1 x.1 then mergeArrayGo xs (ys.drop 1) (out.push y)
      else if add x.2 y.2 = zero then mergeArrayGo (xs.drop 1) (ys.drop 1) out
      else mergeArrayGo (xs.drop 1) (ys.drop 1) (out.push (x.1, add x.2 y.2))
    else out ++ xs.toArray
  else out ++ ys.toArray
termination_by xs.size + ys.size
decreasing_by all_goals simp only [Subarray.size_drop]; omega

private theorem slice_cons {A : Type} (xs : Subarray A) (h : 0 < xs.size) :
    xs.toList = xs[0] :: (xs.drop 1).toList := by
  rw [Subarray.toList_drop, Subarray.getElem_eq_getElem_toList]
  simpa using (List.drop_eq_getElem_cons (l := xs.toList) (i := 0) (by simpa using h))

theorem mergeArrayGo_refines {K : Type} [ProvenanceSemiringOps K] [DecidableEq K]
    (xs ys : Subarray (GroundTuple × K)) (out : Array (GroundTuple × K)) :
    (mergeArrayGo xs ys out).toList = out.toList ++ mergeRows xs.toList ys.toList := by
  induction n : xs.size + ys.size using Nat.strongRecOn generalizing xs ys out with
  | ind n ih =>
    rw [mergeArrayGo]
    split
    · rename_i hx
      split
      · rename_i hy
        have hxl := slice_cons xs hx
        have hyl := slice_cons ys hy
        have il := ih ((xs.drop 1).size + ys.size) (by simp only [Subarray.size_drop]; omega) (xs.drop 1) ys
        have ir := ih (xs.size + (ys.drop 1).size) (by simp only [Subarray.size_drop]; omega) xs (ys.drop 1)
        have ib := ih ((xs.drop 1).size + (ys.drop 1).size) (by simp only [Subarray.size_drop]; omega) (xs.drop 1) (ys.drop 1)
        dsimp only
        split
        · rename_i hlt
          rw [il _ rfl, hxl, hyl, mergeRows]
          simp only [hlt, ↓reduceIte, Array.toList_push, List.append_assoc, List.singleton_append]
        · rename_i hlt
          split
          · rename_i hgt
            rw [ir _ rfl, hxl, hyl, mergeRows]
            simp only [hlt, hgt, ↓reduceIte, Array.toList_push, List.append_assoc, List.singleton_append]
          · rename_i hgt
            split
            · rename_i hz
              rw [ib _ rfl, hxl, hyl, mergeRows]
              simp only [hlt, hgt, hz, ↓reduceIte]
            · rename_i hz
              rw [ib _ rfl, hxl, hyl, mergeRows]
              simp only [hlt, hgt, hz, ↓reduceIte, Array.toList_push, List.append_assoc, List.singleton_append]
      · rename_i hy
        have hnil : ys.toList = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
        have hm : mergeRows xs.toList [] = xs.toList := by cases xs.toList <;> simp [mergeRows]
        simp [hnil, hm]
    · rename_i hx
      have hnil : xs.toList = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      simp [hnil, mergeRows]

def mergeAddSorted {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (t₁ t₂ : SortedKTable K) : SortedKTable K :=
  ⟨mergeArrayGo t₁.entries[*...*] t₂.entries[*...*] #[]⟩

private theorem table_wf_iff {K : Type} [ProvenanceSemiringOps K] (t : SortedKTable K) :
    t.WF ↔ RowsWF t.entries.toList := by
  simp only [SortedKTable.WF, RowsWF, List.pairwise_iff_getElem]
  constructor
  · rintro ⟨hs, hn⟩
    constructor
    · intro i j hi hj hij
      exact hs ⟨i, by simpa using hi⟩ ⟨j, by simpa using hj⟩ hij
    · intro e he
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      exact hn ⟨i, by simpa using hi⟩
  · rintro ⟨hs, hn⟩
    exact ⟨fun i j hij => hs i.val j.val (by simp) (by simp) hij,
      fun i => hn t.entries[i.val] (by simp)⟩

theorem mergeAddSorted_wf {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (t₁ t₂ : SortedKTable K) (h₁ : t₁.WF) (h₂ : t₂.WF) : (mergeAddSorted t₁ t₂).WF := by
  rw [table_wf_iff]
  simpa [mergeAddSorted, mergeArrayGo_refines] using
    mergeRows_wf t₁.entries.toList t₂.entries.toList ((table_wf_iff t₁).mp h₁) ((table_wf_iff t₂).mp h₂)

private theorem sumRows_absent {K : Type} [LawfulProvenanceSemiring K] (xs : List (GroundTuple × K))
    (q : GroundTuple) (h : ∀ e ∈ xs, e.1 ≠ q) : sumRows q xs = zero := by
  induction xs with
  | nil => rfl
  | cons e es ih => simp [sumRows, h e (by simp), ih (fun e he => h e (by simp [he]))]

private theorem lookupList_sum {K : Type} [LawfulProvenanceSemiring K]
    (xs : List (GroundTuple × K)) (hw : RowsWF xs) (q : GroundTuple) :
    ((xs.find? (fun e => e.1 == q)).map Prod.snd).getD zero = sumRows q xs := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    have hh := rows_cons.mp hw
    by_cases he : e.1 = q
    · have hz := sumRows_absent es q (fun a ha heq => by
        have hl := hh.1 a ha
        rw [he, heq] at hl
        exact lt_irrefl q hl)
      simp [List.find?, sumRows, he, hz, LawfulProvenanceSemiring.add_zero]
    · have hbeq : (e.1 == q) = false := beq_eq_false_iff_ne.mpr he
      simp [List.find?, sumRows, he, hbeq, ih hh.2.1]

theorem lookupFast_mergeAddSorted {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (t₁ t₂ : SortedKTable K) (h₁ : t₁.WF) (h₂ : t₂.WF) (q : GroundTuple) :
    lookupFast (mergeAddSorted t₁ t₂) q = add (lookupFast t₁ q) (lookupFast t₂ q) := by
  rw [lookupFast_eq_spec _ (mergeAddSorted_wf t₁ t₂ h₁ h₂), lookupFast_eq_spec _ h₁, lookupFast_eq_spec _ h₂]
  unfold lookupSpec
  rw [lookupList_sum _ ((table_wf_iff _).mp (mergeAddSorted_wf t₁ t₂ h₁ h₂)),
    lookupList_sum _ ((table_wf_iff _).mp h₁), lookupList_sum _ ((table_wf_iff _).mp h₂)]
  simp [mergeAddSorted, mergeArrayGo_refines, sumRows_merge]

def singletonTable {K : Type} [ProvenanceSemiringOps K] [DecidableEq K]
    (e : GroundTuple × K) : SortedKTable K :=
  if e.2 = zero then ⟨#[]⟩ else ⟨#[e]⟩

private theorem singletonTable_wf {K : Type} [ProvenanceSemiringOps K] [DecidableEq K]
    (e : GroundTuple × K) : (singletonTable e).WF := by
  rw [table_wf_iff]
  by_cases he : e.2 = zero <;> simp [singletonTable, he, RowsWF]

/-- Balanced merging builds a canonical table in O(n log n), including duplicate
rule heads and cancellation. Each leaf contributes exactly one weighted occurrence. -/
def buildSorted {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (es : Array (GroundTuple × K)) : SortedKTable K :=
  if h : es.size ≤ 1 then
    if hn : 0 < es.size then singletonTable es[0] else ⟨#[]⟩
  else
    let mid := es.size / 2
    mergeAddSorted (buildSorted (es.extract 0 mid)) (buildSorted (es.extract mid es.size))
termination_by es.size
decreasing_by all_goals simp only [Array.size_extract]; omega

theorem buildSorted_wf {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (es : Array (GroundTuple × K)) : (buildSorted es).WF := by
  induction n : es.size using Nat.strongRecOn generalizing es with
  | ind n ih =>
    rw [buildSorted]
    split
    · split
      · exact singletonTable_wf _
      · exact (table_wf_iff _).mpr ⟨.nil, by simp⟩
    · apply mergeAddSorted_wf
      · exact ih _ (by simp only [Array.size_extract]; omega) _ rfl
      · exact ih _ (by simp only [Array.size_extract]; omega) _ rfl

private theorem sumRows_append {K : Type} [LawfulProvenanceSemiring K]
    (xs ys : List (GroundTuple × K)) (q : GroundTuple) :
    sumRows q (xs ++ ys) = add (sumRows q xs) (sumRows q ys) := by
  induction xs with
  | nil => simp [sumRows, LawfulProvenanceSemiring.zero_add]
  | cons e es ih =>
    by_cases he : e.1 = q <;> simp [sumRows, he, ih, LawfulProvenanceSemiring.add_assoc]

private theorem sumRows_singletonTable {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (e : GroundTuple × K) (q : GroundTuple) :
    sumRows q (singletonTable e).entries.toList = sumRows q [e] := by
  by_cases he : e.2 = zero <;> by_cases hq : e.1 = q <;>
    simp [singletonTable, he, sumRows, hq, LawfulProvenanceSemiring.zero_add]

theorem buildSorted_sum {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (es : Array (GroundTuple × K)) (q : GroundTuple) :
    sumRows q (buildSorted es).entries.toList = sumRows q es.toList := by
  induction n : es.size using Nat.strongRecOn generalizing es with
  | ind n ih =>
    rw [buildSorted]
    split
    · rename_i hsmall
      split
      · rename_i hn
        have he : es.toList = [es[0]] := by
          apply List.ext_getElem
          · simp; omega
          · intro i hi hj
            have hi0 : i = 0 := by simp at hj; omega
            subst i; simp
        simpa [he] using sumRows_singletonTable es[0] q
      · have hz : es.size = 0 := by omega
        have he := Array.size_eq_zero_iff.mp hz
        simp [he, sumRows]
    · rename_i hbig
      simp only [mergeAddSorted, mergeArrayGo_refines, Array.toList_mkSlice_rii,
        List.nil_append, sumRows_merge]
      rw [ih _ (by simp only [Array.size_extract]; omega) _ rfl,
        ih _ (by simp only [Array.size_extract]; omega) _ rfl, ← sumRows_append]
      congr 1
      simp only [Array.toList_extract, List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero]
      rw [List.take_of_length_le (l := es.toList.drop (es.size / 2)) (i := es.size - es.size / 2) (by simp), List.take_append_drop]

def tpFast {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (p : Array GroundRule) (t : SortedKTable K) : SortedKTable K :=
  buildSorted (p.map (fun r => (r.head, evalRuleFast t r)))

theorem tpFast_wf {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (p : Array GroundRule) (t : SortedKTable K) : (tpFast p t).WF := buildSorted_wf _

private theorem tp_fold_sum {K : Type} [LawfulProvenanceSemiring K]
    (p : List GroundRule) (v : KRelationSpec K) (q : GroundTuple) (init : K) :
    p.foldl (fun w r => if r.head = q then add w (evalRuleSpec v r) else w) init =
      add init (sumRows q (p.map (fun r => (r.head, evalRuleSpec v r)))) := by
  induction p generalizing init with
  | nil => simp [sumRows, LawfulProvenanceSemiring.add_zero]
  | cons r rs ih =>
    by_cases he : r.head = q <;> simp [sumRows, he, ih, LawfulProvenanceSemiring.add_assoc]

theorem lookupFast_tpFast_eq_tpSpec {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (p : Array GroundRule) (t : SortedKTable K) (hw : t.WF) (q : GroundTuple) :
    lookupFast (tpFast p t) q = tpSpec p (lookupSpec t) q := by
  rw [lookupFast_eq_spec _ (tpFast_wf p t)]
  unfold lookupSpec
  rw [lookupList_sum _ ((table_wf_iff _).mp (tpFast_wf p t))]
  change sumRows q (buildSorted _).entries.toList = _
  rw [buildSorted_sum]
  simp only [Array.toList_map, evalRuleFast_eq_spec t _ hw]
  unfold tpSpec
  rw [← Array.foldl_toList, tp_fold_sum, LawfulProvenanceSemiring.zero_add]
  rfl

/-- Delta product expansion includes every monomial containing at least one delta
factor exactly once. This is valid for non-idempotent provenance as well as Bool. -/
def evalRuleDeltaFast {K : Type} [ProvenanceSemiringOps K]
    (base delta : SortedKTable K) (r : GroundRule) : K :=
  (r.body.foldl (fun (acc : K × K) q =>
    let b := lookupFast base q
    let d := lookupFast delta q
    (mul acc.1 b, add (mul acc.2 (add b d)) (mul acc.1 d))) (one,zero)).2

def semiNaiveStepFast {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (p : Array GroundRule) (base delta : SortedKTable K) : SortedKTable K :=
  buildSorted (p.map fun r => (r.head, evalRuleDeltaFast base delta r))

theorem semiNaiveStepFast_wf {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (p : Array GroundRule) (base delta : SortedKTable K) : (semiNaiveStepFast p base delta).WF :=
  buildSorted_wf _

private theorem mul_add_left {K : Type} [LawfulProvenanceSemiring K] (a b c : K) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  rw [LawfulProvenanceSemiring.mul_comm, LawfulProvenanceSemiring.left_distrib,
    LawfulProvenanceSemiring.mul_comm c a, LawfulProvenanceSemiring.mul_comm c b]

/-- The delta expansion is exact, including cross terms and repeated premises. -/
theorem evalRuleDeltaFast_decomposition {K : Type} [LawfulProvenanceSemiring K] [DecidableEq K]
    (base delta : SortedKTable K) (hb : base.WF) (hd : delta.WF) (r : GroundRule) :
    evalRuleFast (mergeAddSorted base delta) r =
      add (evalRuleFast base r) (evalRuleDeltaFast base delta r) := by
  let step := fun (acc : K × K) q =>
    (mul acc.1 (lookupFast base q),
      add (mul acc.2 (add (lookupFast base q) (lookupFast delta q))) (mul acc.1 (lookupFast delta q)))
  have fstHom := Array.foldl_hom (fun a : K × K => a.1)
    (g₁ := step) (g₂ := fun w q => mul w (lookupFast base q))
    (xs := r.body) (init := (one,zero)) (fun _ _ => rfl)
  have sumHom := Array.foldl_hom (fun a : K × K => add a.1 a.2)
    (g₁ := step) (g₂ := fun w q => mul w (add (lookupFast base q) (lookupFast delta q)))
    (xs := r.body) (init := (one,zero)) (fun a q => by
      dsimp [step]
      rw [mul_add_left, LawfulProvenanceSemiring.left_distrib, LawfulProvenanceSemiring.add_assoc]
      rw [LawfulProvenanceSemiring.add_comm (mul a.1 (lookupFast delta q))])
  unfold evalRuleFast evalRuleDeltaFast
  simp only [lookupFast_mergeAddSorted base delta hb hd]
  rw [fstHom]
  simpa only [LawfulProvenanceSemiring.add_zero] using sumHom

#tooth sumRows_merge by mutation mergeRows := fun xs _ => xs
#tooth buildSorted_sum by mutation buildSorted := fun _ => ⟨#[]⟩

/-- Symbolic lineage before quotienting by semiring equations. -/
inductive ProvExpr (VarId : Type) where
  | zero | one | var (v : VarId)
  | add (a b : ProvExpr VarId)
  | mul (a b : ProvExpr VarId)
  deriving Repr, DecidableEq

instance {V : Type} : ProvenanceSemiringOps (ProvExpr V) where
  zero := .zero
  one := .one
  add := .add
  mul := .mul

@[expose] def evalProvGoldilocks {V : Type} (env : V → Obend.Crypto.Goldilocks) :
    ProvExpr V → Obend.Crypto.Goldilocks
  | .zero => zero
  | .one => one
  | .var v => env v
  | .add a b => add (evalProvGoldilocks env a) (evalProvGoldilocks env b)
  | .mul a b => mul (evalProvGoldilocks env a) (evalProvGoldilocks env b)

/-- This quotient identifies polynomial *functions over Goldilocks*, not formal
polynomials over ℕ: field identities are intentionally included. -/
@[expose] def provSetoid (V : Type) : Setoid (ProvExpr V) where
  r a b := ∀ env, evalProvGoldilocks env a = evalProvGoldilocks env b
  iseqv := ⟨fun _ _ => rfl, fun h env => (h env).symm,
    fun h₁ h₂ env => (h₁ env).trans (h₂ env)⟩

abbrev ProvPolynomial (V : Type) := Quotient (provSetoid V)

@[expose] def evalPolynomial {V : Type} (env : V → Obend.Crypto.Goldilocks) :
    ProvPolynomial V → Obend.Crypto.Goldilocks :=
  Quotient.lift (evalProvGoldilocks env) (fun _ _ h => h env)

@[expose] def provMap₂ {V : Type} (op : ProvExpr V → ProvExpr V → ProvExpr V)
    (hop : ∀ a a' b b', (provSetoid V).r a a' → (provSetoid V).r b b' →
      (provSetoid V).r (op a b) (op a' b')) (a b : ProvPolynomial V) : ProvPolynomial V :=
  Quotient.lift (fun x => Quotient.lift (fun y => Quotient.mk _ (op x y))
    (fun y y' hy => Quotient.sound (hop x x y y' (fun _ => rfl) hy)) b)
    (fun x x' hx => Quotient.inductionOn b (fun y =>
      Quotient.sound (hop x x' y y hx (fun _ => rfl)))) a

instance {V : Type} : ProvenanceSemiringOps (ProvPolynomial V) where
  zero := Quotient.mk _ .zero
  one := Quotient.mk _ .one
  add := provMap₂ ProvExpr.add (by
    intro a b c d ha hc env
    simp only [evalProvGoldilocks, ha env, hc env])
  mul := provMap₂ ProvExpr.mul (by
    intro a b c d ha hc env
    simp only [evalProvGoldilocks, ha env, hc env])

theorem polynomial_ext {V : Type} {a b : ProvPolynomial V}
    (h : ∀ env, evalPolynomial env a = evalPolynomial env b) : a = b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => exact Quotient.sound h

@[simp] theorem evalPolynomial_add {V : Type} (env : V → Obend.Crypto.Goldilocks)
    (a b : ProvPolynomial V) : evalPolynomial env (add a b) =
      add (evalPolynomial env a) (evalPolynomial env b) := by
  induction a using Quotient.inductionOn with
  | h a => induction b using Quotient.inductionOn; rfl

@[simp] theorem evalPolynomial_mul {V : Type} (env : V → Obend.Crypto.Goldilocks)
    (a b : ProvPolynomial V) : evalPolynomial env (mul a b) =
      mul (evalPolynomial env a) (evalPolynomial env b) := by
  induction a using Quotient.inductionOn with
  | h a => induction b using Quotient.inductionOn; rfl

@[simp] theorem evalPolynomial_zero {V : Type} (env : V → Obend.Crypto.Goldilocks) :
    evalPolynomial env zero = zero := rfl
@[simp] theorem evalPolynomial_one {V : Type} (env : V → Obend.Crypto.Goldilocks) :
    evalPolynomial env one = one := rfl

instance {V : Type} : LawfulProvenanceSemiring (ProvPolynomial V) where
  add_assoc a b c := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.add_assoc])
  add_comm a b := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.add_comm])
  zero_add a := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.zero_add])
  add_zero a := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.add_zero])
  mul_assoc a b c := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.mul_assoc])
  mul_comm a b := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.mul_comm])
  one_mul a := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.one_mul])
  mul_one a := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.mul_one])
  left_distrib a b c := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.left_distrib])
  zero_mul a := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.zero_mul])
  mul_zero a := polynomial_ext (fun env => by simp [LawfulProvenanceSemiring.mul_zero])

structure ProvenanceHom {K L : Type} [ProvenanceSemiringOps K] [ProvenanceSemiringOps L]
    (f : K → L) : Prop where
  map_zero : f zero = zero
  map_one : f one = one
  map_add : ∀ a b, f (add a b) = add (f a) (f b)
  map_mul : ∀ a b, f (mul a b) = mul (f a) (f b)

theorem evalRuleSpec_hom {K L : Type} [ProvenanceSemiringOps K] [ProvenanceSemiringOps L]
    {f : K → L} (hf : ProvenanceHom f) (v : KRelationSpec K) (r : GroundRule) :
    f (evalRuleSpec v r) = evalRuleSpec (fun q => f (v q)) r := by
  unfold evalRuleSpec
  rw [← Array.foldl_hom f (g₂ := fun w q => mul w (f (v q))) (fun a b => (hf.map_mul a (v b)).symm), hf.map_one]

theorem tpSpec_hom {K L : Type} [ProvenanceSemiringOps K] [ProvenanceSemiringOps L]
    {f : K → L} (hf : ProvenanceHom f) (p : Array GroundRule) (v : KRelationSpec K)
    (q : GroundTuple) : f (tpSpec p v q) = tpSpec p (fun a => f (v a)) q := by
  unfold tpSpec
  rw [← Array.foldl_hom f (g₂ := fun w r => if r.head = q then add w (evalRuleSpec (fun a => f (v a)) r) else w) (fun a r => by
    by_cases he : r.head = q <;> simp [he, hf.map_add, evalRuleSpec_hom hf]), hf.map_zero]

theorem evalProvGoldilocks_hom {V : Type} (env : V → Obend.Crypto.Goldilocks) :
    ProvenanceHom (evalProvGoldilocks env) := ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem evalPolynomial_hom {V : Type} (env : V → Obend.Crypto.Goldilocks) :
    ProvenanceHom (evalPolynomial env) :=
  ⟨rfl, rfl, evalPolynomial_add env, evalPolynomial_mul env⟩

#tooth gap_absent by mutation verifyGapCert := fun _ _ _ => true

end Obend.SymbolicZk.Datalog
