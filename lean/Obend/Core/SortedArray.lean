module
/-
# Obend.Core.SortedArray — strictly sorted arrays: binary search and the sorted `UInt64` set

`SortedBy key a` says `a` strictly increases under `key`; `search` is a half-open binary search over
such an array, equal to the linear list specification `findSpec` (`search_eq_spec`). It is the
lookup of the tree's sorted tables: CapTP's Swiss table and digest sets, the ledger's seats, joint
co-receipts.

`SortedU64Set` is the tree's one sorted set of `UInt64` keys: an `Array UInt64` carrying its strict
order as a field, logarithmic `contains` by `search`, and deduplicating `insert` by `insertKey`.
`contains_eq_spec` and `spec_insert` are its laws. A machine that keeps a `List UInt64` ghost of the
set beside it (`Obend.Logic.EnvHarness`, `Obend.Polis.HermesEnv`) relates the two by `SimulatesSet`.
-/
public section
namespace Obend.Core.SortedArray

set_option autoImplicit false

/-- Strict ordering is a representation invariant, not a cached lookup certificate. -/
@[expose] def SortedBy {α : Type} (key : α → Nat) (a : Array α) : Prop :=
  ∀ i j (hi : i < a.size) (hj : j < a.size), i < j → key a[i] < key a[j]

/-- Half-open interval binary search. Fuel is only a termination bound; each recursive
call halves the interval. No array slices or linear fallback are evaluated. -/
@[expose] def search {α : Type} (key : α → Nat) (a : Array α) (k : Nat) :
    Nat → Nat → Nat → Option α
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if hm : mid < a.size then
        if key a[mid] < k then search key a k fuel (mid + 1) hi
        else if k < key a[mid] then search key a k fuel lo mid
        else some a[mid]
      else none
    else none

theorem search_sound {α : Type} (key : α → Nat) (a : Array α) (k : Nat)
    (fuel lo hi : Nat) (x : α) (h : search key a k fuel lo hi = some x) :
    ∃ i, ∃ h : i < a.size, a[i] = x ∧ key x = k := by
  induction fuel generalizing lo hi with
  | zero => simp [search] at h
  | succ fuel ih =>
    simp only [search] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h
    · exact ih _ _ h
    · split at h
      · exact ih _ _ h
      · have hx := Option.some.inj h
        refine ⟨_, ‹_ < a.size›, hx, ?_⟩
        subst x
        omega

theorem search_complete {α : Type} (key : α → Nat) (a : Array α)
    (hs : SortedBy key a) (k fuel lo hi i : Nat) (hiA : hi ≤ a.size)
    (hlen : hi - lo < fuel) (hil : lo ≤ i) (hih : i < hi)
    (hk : key (a[i]'(by omega)) = k) :
    search key a k fuel lo hi = some a[i] := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
    have hmid : (lo + hi) / 2 < hi := by omega
    have hmlo : lo ≤ (lo + hi) / 2 := by omega
    have hmA : (lo + hi) / 2 < a.size := by omega
    simp only [search, show lo < hi by omega, hmA, ite_true, dite_true]
    split
    · have hmi : (lo + hi) / 2 < i := by
        apply Decidable.byContradiction
        intro hn
        have he : i ≤ (lo + hi) / 2 := by omega
        rcases Nat.lt_or_eq_of_le he with he | he
        · have := hs i ((lo + hi) / 2) (by omega) hmA he
          omega
        · subst i; omega
      exact ih ((lo + hi) / 2 + 1) hi hiA (by omega) (by omega) hih hk
    · split
      · have him : i < (lo + hi) / 2 := by
          apply Decidable.byContradiction
          intro hn
          have he : (lo + hi) / 2 ≤ i := by omega
          rcases Nat.lt_or_eq_of_le he with he | he
          · have := hs ((lo + hi) / 2) i hmA (by omega) he
            omega
          · subst i; omega
        exact ih lo ((lo + hi) / 2) (by omega) (by omega) hil him hk
      · have he : i = (lo + hi) / 2 := by
          rcases Nat.lt_trichotomy i ((lo + hi) / 2) with hl | he | hr
          · have := hs i _ (by omega) hmA hl; omega
          · exact he
          · have := hs _ i hmA (by omega) hr; omega
        subst i
        rfl

/-- Mathematical lookup is a linear list specification, independent of binary search. -/
@[expose] def findSpec {α : Type} (key : α → Nat) (a : Array α) (k : Nat) : Option α :=
  a.toList.find? (fun x => key x == k)

theorem search_eq_spec {α : Type} (key : α → Nat) (a : Array α)
    (hs : SortedBy key a) (k : Nat) :
    search key a k (a.size + 1) 0 a.size = findSpec key a k := by
  cases hf : findSpec key a k with
  | none =>
    cases he : search key a k (a.size + 1) 0 a.size with
    | none => rfl
    | some x =>
      obtain ⟨i, hi, hx, hk⟩ := search_sound key a k _ _ _ x he
      have hn := List.find?_eq_none.mp hf x
      have hm : x ∈ a.toList := by simp [← hx, Array.mem_iff_getElem]; exact ⟨i, hi, rfl⟩
      simp [hk] at hn
      exact False.elim (hn (by simpa using hm))
  | some x =>
    have hm := List.mem_of_find?_eq_some hf
    have hk : key x = k := by simpa using List.find?_some hf
    have hm' : x ∈ a := by simpa using hm
    obtain ⟨i, hi, hx⟩ := Array.mem_iff_getElem.mp hm'
    have hc := search_complete key a hs k (a.size + 1) 0 a.size i
      (by omega) (by omega) (by omega) hi (by simpa [hx] using hk)
    simpa [hx] using hc

/-- Sorted set insertion deduplicates and preserves the order. -/
@[expose] def insertKey (k : UInt64) : List UInt64 → List UInt64
  | [] => [k]
  | x :: xs => if k.toNat < x.toNat then k :: x :: xs
    else if k = x then x :: xs else x :: insertKey k xs

@[simp] theorem mem_insertKey (k x : UInt64) (xs : List UInt64) :
    x ∈ insertKey k xs ↔ x = k ∨ x ∈ xs := by
  induction xs with
  | nil => simp [insertKey]
  | cons y ys ih =>
    simp only [insertKey]
    split
    · simp only [List.mem_cons] <;> grind
    · split
      · simp_all
      · simp only [List.mem_cons, ih] <;> grind

theorem insertKey_sorted (k : UInt64) (xs : List UInt64)
    (h : xs.Pairwise (fun a b => a.toNat < b.toNat)) :
    (insertKey k xs).Pairwise (fun a b => a.toNat < b.toNat) := by
  induction xs with
  | nil => simp [insertKey]
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
    simp only [insertKey]
    split
    · apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_cons.mpr ⟨hx, ht⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with he | hm
      · subst y; assumption
      · have := hx y hm; omega
    · split
      · exact List.pairwise_cons.mpr ⟨hx, ht⟩
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ih ht⟩
        intro y hy
        rcases (mem_insertKey k y xs).mp hy with he | hm
        · subst y
          have hne : k.toNat ≠ x.toNat := by
            intro he; have : k = x := UInt64.toNat_inj.mp he; contradiction
          omega
        · exact hx y hm

/-- The sorted set of `UInt64` keys: an array strictly increasing as a representation invariant. -/
structure SortedU64Set where
  data : Array UInt64
  sorted : data.toList.Pairwise (fun a b => a.toNat < b.toNat)
  deriving DecidableEq, Repr

@[expose] def SortedU64Set.empty : SortedU64Set := ⟨#[], by simp⟩
@[expose] def SortedU64Set.spec (s : SortedU64Set) (k : UInt64) : Prop := k ∈ s.data.toList

@[expose] def SortedU64Set.contains (s : SortedU64Set) (k : UInt64) : Bool :=
  (search UInt64.toNat s.data k.toNat (s.data.size + 1) 0 s.data.size).isSome

@[expose] def SortedU64Set.insert (s : SortedU64Set) (k : UInt64) : SortedU64Set :=
  ⟨(insertKey k s.data.toList).toArray, by simpa using insertKey_sorted k _ s.sorted⟩

theorem SortedU64Set.contains_eq_spec (s : SortedU64Set) (k : UInt64) :
    s.contains k = true ↔ s.spec k := by
  have hs : SortedBy UInt64.toNat s.data := by
    intro i j hi hj hij
    exact (List.pairwise_iff_getElem.mp s.sorted) i j (by simpa) (by simpa) hij
  unfold contains
  rw [search_eq_spec _ _ hs]
  simp only [findSpec, List.isSome_find?, List.any_eq_true, beq_iff_eq, spec]
  constructor
  · rintro ⟨x, hx, he⟩; have : x = k := UInt64.toNat_inj.mp he; simpa [this] using hx
  · intro hk; exact ⟨k, hk, rfl⟩

@[simp] theorem SortedU64Set.spec_insert (s : SortedU64Set) (k x : UInt64) :
    (s.insert k).spec x ↔ x = k ∨ s.spec x := by simp [insert, spec]

theorem SortedU64Set.contains_list (s : SortedU64Set) (k : UInt64) :
    s.contains k = s.data.toList.contains k := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_spec]
  simp only [spec, List.contains_iff_mem]

/-- The set refines the list `spec` a machine keeps beside it. -/
def SimulatesSet (spec : List UInt64) (s : SortedU64Set) : Prop := s.data.toList = spec

theorem SortedU64Set.simulates_empty : SimulatesSet [] SortedU64Set.empty := by
  unfold SimulatesSet; rfl

theorem SortedU64Set.simulates_insert {spec : List UInt64} {s : SortedU64Set}
    (h : SimulatesSet spec s) (k : UInt64) : SimulatesSet (insertKey k spec) (s.insert k) := by
  unfold SimulatesSet at h ⊢
  simp [SortedU64Set.insert, h]

theorem SortedU64Set.contains_iff_mem {spec : List UInt64} {s : SortedU64Set}
    (h : SimulatesSet spec s) (k : UInt64) : s.contains k = true ↔ k ∈ spec := by
  rw [s.contains_eq_spec, SortedU64Set.spec, ← h]

/-- Inserting removes no member. -/
theorem SortedU64Set.contains_insert_of_contains (s : SortedU64Set) (k x : UInt64)
    (h : s.contains x = true) : (s.insert k).contains x = true := by
  rw [contains_eq_spec] at h ⊢
  exact (spec_insert s k x).mpr (.inr h)

theorem SortedU64Set.contains_insert_self (s : SortedU64Set) (k : UInt64) :
    (s.insert k).contains k = true := by
  rw [contains_eq_spec]
  exact (spec_insert s k k).mpr (.inl rfl)

example : ((SortedU64Set.empty.insert 42).insert 7).insert 42 =
    ⟨#[7, 42], by decide⟩ := by decide
example : (((SortedU64Set.empty.insert 42).insert 7).insert 19).contains 19 = true ∧
    (((SortedU64Set.empty.insert 42).insert 7).insert 19).contains 18 = false := by decide

end Obend.Core.SortedArray

end
