module
/-
# Obend.SymbolicZk.LinMem — consume-once multiset memory

A linear memory is one whose cells are written once and read once: an interaction net's wires, a
visibly pushdown stack's cells. For such a memory the read/write timestamp routing of a general RAM
argument is not needed. A trace is four tables (`init`, `produced`, `consumed`, `finalCells`) and it
is valid when

* allocation ids are fresh (`uniqueAllocIds`),
* every consumption is strictly after its cell's birth (`causalConsumed`),
* `init ⊎ produced = consumed ⊎ final` as multisets (`multisetBalanced`).

Two tiers. `LinMemSpec` states the three conditions over lists (`Nodup`, `Perm`).
`verifyLinMemExec` checks them on arrays: one merge sort of each side, one adjacent pass, one pass
over the events, one array comparison. `verifyLinMemExec_iff_spec` is their equivalence.

`linmem_sound` reads an accepted trace as a matching: every consumed event has its own supply cell,
born strictly earlier, no supply cell serves two events, and every final cell is a supply cell that no
event consumed.

The last section is a lifetime ledger over natural-number ids (`Ledger`): given the id sets a system
exposes at successive times, with ids never reused, it writes the trace of births and deaths and
`Ledger.toTrace_spec` proves that trace valid. `Obend.Hardware.HvmConfluence` drives it with the
wires of a Δ-net reduction.

The array helpers of the first section (`adjacentAll`, `mergeSortBy`, `binSearch`) are generic; the
memo table of `Obend.Equiv.ClairvoyantBook` uses them too.
-/
public section
namespace Obend.SymbolicZk
set_option autoImplicit false

/-! ## 1. Array passes and their list specifications -/

/-- The adjacent pass over `fuel` positions from `i`. -/
def adjacentFrom {α : Type} (r : α → α → Bool) (a : Array α) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, i => if h : i + 1 < a.size then r a[i] a[i + 1] && adjacentFrom r a fuel (i + 1) else true

/-- The adjacent pass: `r a[j] a[j+1]` for every `j` from `i` on. -/
def adjacentAll {α : Type} (r : α → α → Bool) (a : Array α) (i : Nat) : Bool :=
  adjacentFrom r a (a.size - i) i

/-- The list reading of the adjacent pass. -/
@[expose] def chainB {α : Type} (r : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: l => r x y && chainB r (y :: l)

theorem adjacentFrom_eq_chainB {α : Type} (r : α → α → Bool) (a : Array α) :
    ∀ (n i : Nat), a.size - i = n → adjacentFrom r a n i = chainB r (a.toList.drop i) := by
  intro n
  induction n with
  | zero =>
    intro i h
    have e : a.toList.drop i = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
    rw [e]
    rfl
  | succ n ih =>
    intro i h
    have hi : i < a.toList.length := by simp only [Array.length_toList]; omega
    have e0 : a.toList.drop i = a[i]'(by omega) :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi]; simp only [Array.getElem_toList]
    rw [e0]
    by_cases h1 : i + 1 < a.size
    · have hi1 : i + 1 < a.toList.length := by simp only [Array.length_toList]; omega
      have e1 : a.toList.drop (i + 1) = a[i + 1] :: a.toList.drop (i + 1 + 1) := by
        rw [List.drop_eq_getElem_cons hi1]; simp only [Array.getElem_toList]
      simp only [adjacentFrom, h1, ↓reduceDIte]
      rw [ih (i + 1) (by omega), e1]
      simp only [chainB]
    · have e1 : a.toList.drop (i + 1) = [] :=
        List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
      rw [e1]
      simp only [adjacentFrom, h1, ↓reduceDIte, chainB]

/-- For a transitive relation the adjacent pass decides `Pairwise`. -/
theorem chainB_iff_pairwise {α : Type} {r : α → α → Bool}
    (trans : ∀ a b c, r a b = true → r b c = true → r a c = true) :
    ∀ l : List α, chainB r l = true ↔ l.Pairwise (fun a b => r a b = true)
  | [] => by simp [chainB]
  | [x] => by simp [chainB]
  | x :: y :: l => by
    have ih := chainB_iff_pairwise trans (y :: l)
    constructor
    · intro h
      have h' : (r x y && chainB r (y :: l)) = true := h
      rw [Bool.and_eq_true] at h'
      have hp := ih.1 h'.2
      refine List.Pairwise.cons ?_ hp
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h'.1
      · exact trans _ _ _ h'.1 (List.rel_of_pairwise_cons hp hz)
    · intro h
      have hx := List.rel_of_pairwise_cons h (List.mem_cons_self (a := y) (l := l))
      have hp := ih.2 (List.Pairwise.of_cons h)
      show (r x y && chainB r (y :: l)) = true
      rw [Bool.and_eq_true]
      exact ⟨hx, hp⟩

theorem adjacentAll_iff_pairwise {α : Type} {r : α → α → Bool}
    (trans : ∀ a b c, r a b = true → r b c = true → r a c = true) (a : Array α) :
    adjacentAll r a 0 = true ↔ a.toList.Pairwise (fun x y => r x y = true) := by
  rw [adjacentAll, adjacentFrom_eq_chainB r a _ 0 rfl, List.drop_zero]
  exact chainB_iff_pairwise trans _

/-- One pass over `fuel` positions from `i`: `p` holds at each. -/
def allFrom {α : Type} (p : α → Bool) (a : Array α) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, i => if h : i < a.size then p a[i] && allFrom p a fuel (i + 1) else true

/-- One pass: `p` holds of every element. -/
def arrayAll {α : Type} (p : α → Bool) (a : Array α) : Bool := allFrom p a a.size 0

theorem allFrom_eq {α : Type} (p : α → Bool) (a : Array α) :
    ∀ (n i : Nat), a.size - i = n → allFrom p a n i = (a.toList.drop i).all p := by
  intro n
  induction n with
  | zero =>
    intro i h
    have e : a.toList.drop i = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
    rw [e]
    rfl
  | succ n ih =>
    intro i h
    have hi : i < a.size := by omega
    have e0 : a.toList.drop i = a[i] :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact hi)]
      simp only [Array.getElem_toList]
    simp only [allFrom, hi, ↓reduceDIte]
    rw [ih (i + 1) (by omega), e0, List.all_cons]

theorem arrayAll_iff {α : Type} (p : α → Bool) (a : Array α) :
    arrayAll p a = true ↔ ∀ x ∈ a.toList, p x = true := by
  rw [arrayAll, allFrom_eq p a a.size 0 (Nat.sub_zero _), List.drop_zero, List.all_eq_true]

/-- The merge loop of two sorted arrays into an accumulator. -/
def mergeInto {α : Type} (le : α → α → Bool) (xs ys : Array α) (i j : Nat) (acc : Array α) :
    Array α :=
  if hi : i < xs.size then
    if hj : j < ys.size then
      if le xs[i] ys[j] = true then mergeInto le xs ys (i + 1) j (acc.push xs[i])
      else mergeInto le xs ys i (j + 1) (acc.push ys[j])
    else mergeInto le xs ys (i + 1) j (acc.push xs[i])
  else if hj : j < ys.size then mergeInto le xs ys i (j + 1) (acc.push ys[j])
  else acc
termination_by (xs.size - i) + (ys.size - j)

theorem mergeInto_toList {α : Type} (le : α → α → Bool) (xs ys : Array α) :
    ∀ (n i j : Nat) (acc : Array α), (xs.size - i) + (ys.size - j) = n →
      (mergeInto le xs ys i j acc).toList
        = acc.toList ++ List.merge (xs.toList.drop i) (ys.toList.drop j) le := by
  intro n
  induction n with
  | zero =>
    intro i j acc h
    have hi : ¬ i < xs.size := by omega
    have hj : ¬ j < ys.size := by omega
    have ei : xs.toList.drop i = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
    have ej : ys.toList.drop j = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
    rw [mergeInto, ei, ej]
    simp only [hi, hj, ↓reduceDIte, List.nil_merge, List.append_nil]
  | succ n ih =>
    intro i j acc h
    rw [mergeInto]
    by_cases hi : i < xs.size
    · have ei : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact hi)]
        simp only [Array.getElem_toList]
      by_cases hj : j < ys.size
      · have ej : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
          rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact hj)]
          simp only [Array.getElem_toList]
        simp only [hi, hj, ↓reduceDIte]
        by_cases hle : le xs[i] ys[j] = true
        · simp only [hle, ite_true]
          rw [ih (i + 1) j _ (by omega), ei, ej, List.cons_merge_cons_pos le _ _ hle, ← ej]
          simp only [Array.toList_push, List.append_assoc, List.singleton_append]
        · simp only [hle, Bool.false_eq_true, ↓reduceIte]
          rw [ih i (j + 1) _ (by omega), ei, ej, List.cons_merge_cons_neg le _ _ hle, ← ei]
          simp only [Array.toList_push, List.append_assoc, List.singleton_append]
      · have ej : ys.toList.drop j = [] :=
          List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
        simp only [hi, hj, ↓reduceDIte]
        rw [ih (i + 1) j _ (by omega), ei, ej]
        simp only [List.merge_right, Array.toList_push, List.append_assoc, List.singleton_append]
    · have ei : xs.toList.drop i = [] :=
        List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
      by_cases hj : j < ys.size
      · have ej : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
          rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact hj)]
          simp only [Array.getElem_toList]
        simp only [hi, hj, ↓reduceDIte]
        rw [ih i (j + 1) _ (by omega), ei, ej]
        simp only [List.nil_merge, Array.toList_push, List.append_assoc, List.singleton_append]
      · have ej : ys.toList.drop j = [] :=
          List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)
        simp only [hi, hj, ↓reduceDIte]
        rw [ei, ej]
        simp only [List.nil_merge, List.append_nil]

/-- Top-down merge sort of an array: `O(n log n)` comparisons. -/
def mergeSortBy {α : Type} (le : α → α → Bool) (arr : Array α) : Array α :=
  if arr.size ≤ 1 then arr
  else
    mergeInto le (mergeSortBy le (arr.extract 0 (arr.size / 2)))
      (mergeSortBy le (arr.extract (arr.size / 2) arr.size)) 0 0 (Array.mkEmpty arr.size)
termination_by arr.size
decreasing_by all_goals (simp only [Array.size_extract]; omega)

theorem extract_halves {α : Type} (arr : Array α) :
    (arr.extract 0 (arr.size / 2)).toList ++ (arr.extract (arr.size / 2) arr.size).toList
      = arr.toList := by
  rw [← Array.toList_append, Array.extract_append_extract]
  simp [Nat.max_eq_right (Nat.div_le_self arr.size 2)]

theorem mergeSortBy_toList {α : Type} (le : α → α → Bool) (arr : Array α) (h : ¬ arr.size ≤ 1) :
    (mergeSortBy le arr).toList
      = List.merge (mergeSortBy le (arr.extract 0 (arr.size / 2))).toList
          (mergeSortBy le (arr.extract (arr.size / 2) arr.size)).toList le := by
  rw [mergeSortBy]
  simp only [h, ↓reduceIte]
  rw [mergeInto_toList le _ _ _ 0 0 _ rfl]
  simp

theorem mergeSortBy_perm {α : Type} (le : α → α → Bool) :
    ∀ (n : Nat) (arr : Array α), arr.size = n → (mergeSortBy le arr).toList.Perm arr.toList := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro arr hn
    by_cases h : arr.size ≤ 1
    · rw [mergeSortBy]
      simp only [h, ↓reduceIte]
      exact List.Perm.refl _
    · rw [mergeSortBy_toList le arr h]
      have p1 := ih (arr.extract 0 (arr.size / 2)).size (by simp only [Array.size_extract]; omega)
        _ rfl
      have p2 := ih (arr.extract (arr.size / 2) arr.size).size
        (by simp only [Array.size_extract]; omega) _ rfl
      refine (List.merge_perm_append le).trans ?_
      rw [← extract_halves arr]
      exact List.Perm.append p1 p2

theorem mergeSortBy_sorted {α : Type} {le : α → α → Bool}
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) :
    ∀ (n : Nat) (arr : Array α), arr.size = n →
      (mergeSortBy le arr).toList.Pairwise (fun a b => le a b = true) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro arr hn
    by_cases h : arr.size ≤ 1
    · rw [mergeSortBy]
      simp only [h, ↓reduceIte]
      have hl : arr.toList.length ≤ 1 := by simpa using h
      generalize arr.toList = l at hl
      match l, hl with
      | [], _ => exact List.Pairwise.nil
      | [x], _ => exact List.pairwise_singleton _ _
    · rw [mergeSortBy_toList le arr h]
      have p1 := ih (arr.extract 0 (arr.size / 2)).size (by simp only [Array.size_extract]; omega)
        _ rfl
      have p2 := ih (arr.extract (arr.size / 2) arr.size).size
        (by simp only [Array.size_extract]; omega) _ rfl
      exact List.pairwise_merge trans total _ _ p1 p2

/-- Binary search of a sorted array for the element `cmp` calls `.eq`; `cmp x` orders the element
`x` against the probe. -/
def binSearch {α : Type} (arr : Array α) (cmp : α → Ordering) (lo hi : Nat) : Option α :=
  if h : lo < hi then
    if hm : lo + (hi - lo) / 2 < arr.size then
      match cmp arr[lo + (hi - lo) / 2] with
      | .lt => binSearch arr cmp (lo + (hi - lo) / 2 + 1) hi
      | .gt => binSearch arr cmp lo (lo + (hi - lo) / 2)
      | .eq => some arr[lo + (hi - lo) / 2]
    else none
  else none
termination_by hi - lo

theorem binSearch_of_ge {α : Type} (arr : Array α) (cmp : α → Ordering) {lo hi : Nat}
    (h : hi ≤ lo) : binSearch arr cmp lo hi = none := by
  rw [binSearch]
  simp only [Nat.not_lt.mpr h, ↓reduceDIte]

/-- What the search returns is an element of the array that `cmp` calls equal. -/
theorem binSearch_sound {α : Type} (arr : Array α) (cmp : α → Ordering) :
    ∀ (n lo hi : Nat) (x : α), hi - lo = n → binSearch arr cmp lo hi = some x →
      x ∈ arr.toList ∧ cmp x = .eq := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi x hn hx
    rw [binSearch] at hx
    by_cases h : lo < hi
    · by_cases hm : lo + (hi - lo) / 2 < arr.size
      · simp only [h, hm, ↓reduceDIte] at hx
        cases hc : cmp arr[lo + (hi - lo) / 2] with
        | lt => rw [hc] at hx; exact ih _ (by omega) _ _ x rfl hx
        | gt => rw [hc] at hx; exact ih _ (by omega) _ _ x rfl hx
        | eq =>
          rw [hc] at hx
          cases hx
          exact ⟨Array.mem_toList_iff.mpr (Array.getElem_mem hm), hc⟩
      · simp only [h, hm, ↓reduceDIte] at hx; cases hx
    · simp only [h, ↓reduceDIte] at hx; cases hx

/-- On an array strictly increasing in a key, with `cmp` the comparison of that key against a probe
`k`, the search finds the element of key `k` wherever it is. -/
theorem binSearch_complete {α : Type} (arr : Array α) (cmp : α → Ordering) (key : α → Nat) (k : Nat)
    (hcmp : ∀ x, cmp x = compare (key x) k)
    (hsorted : ∀ (i j : Nat) (hi : i < arr.size) (hj : j < arr.size), i < j → key arr[i] < key arr[j]) :
    ∀ (n lo hi j : Nat) (hj : j < arr.size), hi - lo = n → hi ≤ arr.size → lo ≤ j → j < hi →
      key arr[j] = k → binSearch arr cmp lo hi = some arr[j] := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi j hj hn hhs hlo hhi hk
    rw [binSearch]
    have h : lo < hi := by omega
    have hm : lo + (hi - lo) / 2 < arr.size := by omega
    simp only [h, hm, ↓reduceDIte]
    have hmid := hcmp arr[lo + (hi - lo) / 2]
    rcases Nat.lt_trichotomy (lo + (hi - lo) / 2) j with hlt | heq | hgt
    · have := hsorted _ _ hm hj hlt
      rw [Nat.compare_eq_lt.mpr (by omega)] at hmid
      rw [hmid]
      exact ih _ (by omega) _ _ j hj rfl hhs (by omega) hhi hk
    · have e : arr[lo + (hi - lo) / 2] = arr[j] := by simp only [heq]
      rw [e] at hmid ⊢
      rw [Nat.compare_eq_eq.mpr hk] at hmid
      rw [hmid]
    · have := hsorted _ _ hj hm hgt
      rw [Nat.compare_eq_gt.mpr (by omega)] at hmid
      rw [hmid]
      exact ih _ (by omega) _ _ j hj rfl (by omega) hlo hgt hk

/-- **The search is `find?`**: on an array strictly increasing in a key, binary search for the key
`k` is the linear search for it. -/
theorem binSearch_eq_find? {α : Type} (arr : Array α) (cmp : α → Ordering) (key : α → Nat) (k : Nat)
    (hcmp : ∀ x, cmp x = compare (key x) k)
    (hsorted : arr.toList.Pairwise (fun a b => key a < key b)) :
    binSearch arr cmp 0 arr.size = arr.toList.find? (fun x => key x == k) := by
  have hidx : ∀ (i j : Nat) (hi : i < arr.size) (hj : j < arr.size), i < j →
      key arr[i] < key arr[j] := by
    intro i j hi hj hlt
    have := List.pairwise_iff_getElem.1 hsorted i j (by simpa using hi) (by simpa using hj) hlt
    simpa only [Array.getElem_toList] using this
  cases hf : arr.toList.find? (fun x => key x == k) with
  | none =>
    cases hb : binSearch arr cmp 0 arr.size with
    | none => rfl
    | some x =>
      obtain ⟨hx, hc⟩ := binSearch_sound arr cmp _ 0 arr.size x rfl hb
      rw [hcmp x, Nat.compare_eq_eq] at hc
      have := List.find?_eq_none.1 hf x hx
      simp only [hc, beq_self_eq_true, not_true_eq_false] at this
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hk : key x = k := by simpa using List.find?_some hf
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
    have hj' : j < arr.size := by simpa using hj
    have := binSearch_complete arr cmp key k hcmp hidx _ 0 arr.size j hj' rfl (Nat.le_refl _)
      (Nat.zero_le _) hj' (by simpa only [Array.getElem_toList] using hk)
    simpa only [Array.getElem_toList] using this

/-! ## 2. Cells, events and traces -/

/-- A cell: its allocation id, the step at which it was written, and what it holds. -/
structure LinCell where
  allocId : UInt64
  birthStep : UInt64
  payload : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- A cell read (and so destroyed) at `consumeStep`. -/
structure ConsumedEvent where
  cell : LinCell
  consumeStep : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- The four committed tables. -/
structure LinMemTrace where
  init : Array LinCell
  produced : Array LinCell
  consumed : Array ConsumedEvent
  finalCells : Array LinCell
  deriving Repr, Inhabited

/-- Every cell that ever existed. -/
@[expose] def LinMemTrace.supply (tr : LinMemTrace) : Array LinCell := tr.init ++ tr.produced

/-- Every cell accounted for: the consumed ones, then the survivors. -/
@[expose] def LinMemTrace.demand (tr : LinMemTrace) : Array LinCell :=
  tr.consumed.map ConsumedEvent.cell ++ tr.finalCells

/-! ## 3. The reasoning tier -/

@[expose] def uniqueAllocIds (tr : LinMemTrace) : Prop :=
  ((tr.init.toList ++ tr.produced.toList).map LinCell.allocId).Nodup

@[expose] def causalConsumed (tr : LinMemTrace) : Prop :=
  ∀ ev ∈ tr.consumed.toList, ev.cell.birthStep < ev.consumeStep

@[expose] def multisetBalanced (tr : LinMemTrace) : Prop :=
  (tr.init.toList ++ tr.produced.toList).Perm
    (tr.consumed.toList.map ConsumedEvent.cell ++ tr.finalCells.toList)

/-- A valid linear-memory trace. -/
@[expose] def LinMemSpec (tr : LinMemTrace) : Prop :=
  uniqueAllocIds tr ∧ causalConsumed tr ∧ multisetBalanced tr

instance (tr : LinMemTrace) : Decidable (LinMemSpec tr) := by
  unfold LinMemSpec uniqueAllocIds causalConsumed multisetBalanced
  infer_instance

/-! ## 4. The execution tier -/

/-- The sort order: by allocation id, then birth step, then payload. -/
def cellLe (a b : LinCell) : Bool :=
  a.allocId < b.allocId ||
    (a.allocId == b.allocId &&
      (a.birthStep < b.birthStep || (a.birthStep == b.birthStep && a.payload ≤ b.payload)))

/-- Strictly increasing allocation ids. -/
def allocLt (a b : LinCell) : Bool := a.allocId < b.allocId

def mergeSortCells (arr : Array LinCell) : Array LinCell := mergeSortBy cellLe arr

/-- One adjacent pass: the ids of a sorted supply strictly increase. -/
def checkStrictlyIncreasingAllocId (sortedSupply : Array LinCell) : Bool :=
  adjacentAll allocLt sortedSupply 0

/-- One pass: every event is strictly after its cell's birth. -/
def checkCausalExec (consumed : Array ConsumedEvent) : Bool :=
  arrayAll (fun ev => ev.cell.birthStep < ev.consumeStep) consumed

/-- The checker: two sorts, two passes, one comparison. -/
def verifyLinMemExec (tr : LinMemTrace) : Bool :=
  checkStrictlyIncreasingAllocId (mergeSortCells tr.supply) && checkCausalExec tr.consumed &&
    mergeSortCells tr.supply == mergeSortCells tr.demand

/-! ## 5. The two tiers agree -/

theorem cellLe_iff (a b : LinCell) : cellLe a b = true ↔
    a.allocId.toNat < b.allocId.toNat ∨ (a.allocId.toNat = b.allocId.toNat ∧
      (a.birthStep.toNat < b.birthStep.toNat ∨
        (a.birthStep.toNat = b.birthStep.toNat ∧ a.payload.toNat ≤ b.payload.toNat))) := by
  simp only [cellLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]

theorem cellLe_trans (a b c : LinCell) (h1 : cellLe a b = true) (h2 : cellLe b c = true) :
    cellLe a c = true := by
  rw [cellLe_iff] at *; omega

theorem cellLe_total (a b : LinCell) : (cellLe a b || cellLe b a) = true := by
  rw [Bool.or_eq_true, cellLe_iff, cellLe_iff]; omega

theorem cellLe_antisymm (a b : LinCell) (h1 : cellLe a b = true) (h2 : cellLe b a = true) :
    a = b := by
  rw [cellLe_iff] at h1 h2
  have e1 : a.allocId = b.allocId := UInt64.toNat_inj.mp (by omega)
  have e2 : a.birthStep = b.birthStep := UInt64.toNat_inj.mp (by omega)
  have e3 : a.payload = b.payload := UInt64.toNat_inj.mp (by omega)
  cases a; cases b; simp_all

theorem allocLt_trans (a b c : LinCell) (h1 : allocLt a b = true) (h2 : allocLt b c = true) :
    allocLt a c = true := by
  simp only [allocLt, decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at *; omega

theorem mergeSortCells_perm (arr : Array LinCell) :
    (mergeSortCells arr).toList.Perm arr.toList :=
  mergeSortBy_perm cellLe _ arr rfl

theorem mergeSortCells_sorted (arr : Array LinCell) :
    (mergeSortCells arr).toList.Pairwise (fun a b => cellLe a b = true) :=
  mergeSortBy_sorted cellLe_trans cellLe_total _ arr rfl

/-- On a list sorted by `cellLe`, strictly increasing ids are exactly distinct ids. -/
theorem sorted_strict_iff_nodup (l : List LinCell)
    (hs : l.Pairwise (fun a b => cellLe a b = true)) :
    l.Pairwise (fun a b => allocLt a b = true) ↔ (l.map LinCell.allocId).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  constructor
  · intro h
    refine h.imp ?_
    intro a b hab
    simp only [allocLt, decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at hab
    intro e
    rw [e] at hab
    omega
  · intro h
    refine (hs.and h).imp ?_
    intro a b hab
    obtain ⟨hle, hne⟩ := hab
    rw [cellLe_iff] at hle
    have : a.allocId.toNat ≠ b.allocId.toNat := fun e => hne (UInt64.toNat_inj.mp e)
    simp only [allocLt, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
    omega

theorem checkStrictlyIncreasingAllocId_iff (arr : Array LinCell) :
    checkStrictlyIncreasingAllocId (mergeSortCells arr) = true ↔
      (arr.toList.map LinCell.allocId).Nodup := by
  rw [checkStrictlyIncreasingAllocId, adjacentAll_iff_pairwise allocLt_trans,
    sorted_strict_iff_nodup _ (mergeSortCells_sorted arr)]
  exact ((mergeSortCells_perm arr).map _).nodup_iff

theorem checkCausalExec_iff (consumed : Array ConsumedEvent) :
    checkCausalExec consumed = true ↔
      ∀ ev ∈ consumed.toList, ev.cell.birthStep < ev.consumeStep := by
  rw [checkCausalExec, arrayAll_iff]
  simp only [decide_eq_true_eq]

/-- Two arrays sort to the same array exactly when they are permutations of each other. -/
theorem mergeSortCells_eq_iff_perm (a b : Array LinCell) :
    mergeSortCells a = mergeSortCells b ↔ a.toList.Perm b.toList := by
  constructor
  · intro h
    have := mergeSortCells_perm a
    rw [h] at this
    exact this.symm.trans (mergeSortCells_perm b)
  · intro h
    have p : (mergeSortCells a).toList.Perm (mergeSortCells b).toList :=
      (mergeSortCells_perm a).trans (h.trans (mergeSortCells_perm b).symm)
    have e := p.eq_of_pairwise (le := fun x y => cellLe x y = true)
      (fun x y _ _ h1 h2 => cellLe_antisymm x y h1 h2) (mergeSortCells_sorted a)
      (mergeSortCells_sorted b)
    exact Array.toList_inj.mp e

/-- **`Spec ↔ Exec`**: the array checker accepts exactly the valid traces. -/
theorem verifyLinMemExec_iff_spec (tr : LinMemTrace) :
    verifyLinMemExec tr = true ↔ LinMemSpec tr := by
  rw [verifyLinMemExec, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq,
    checkStrictlyIncreasingAllocId_iff, checkCausalExec_iff, mergeSortCells_eq_iff_perm]
  simp only [LinMemTrace.supply, LinMemTrace.demand, Array.toList_append, Array.toList_map,
    LinMemSpec, uniqueAllocIds, causalConsumed, multisetBalanced, and_assoc]

/-! ## 6. An accepted trace is a matching -/

/-- The reading of a valid trace: each consumed event has its own source cell in the supply, born
strictly before the event; no supply cell serves two events; every final cell is one supply cell,
and no event consumed it. -/
structure CausalMatching (tr : LinMemTrace) where
  srcOf : Fin tr.consumed.size → Fin tr.supply.size
  exact : ∀ i, tr.supply[srcOf i] = tr.consumed[i].cell
  causal : ∀ i, (tr.supply[srcOf i]).birthStep < tr.consumed[i].consumeStep
  injective : ∀ i₁ i₂, srcOf i₁ = srcOf i₂ → i₁ = i₂
  distinctIds : ∀ i₁ i₂ : Fin tr.consumed.size, i₁ ≠ i₂ →
    tr.consumed[i₁].cell.allocId ≠ tr.consumed[i₂].cell.allocId
  unspent : ∀ c ∈ tr.finalCells.toList,
    (∃ j : Fin tr.supply.size, tr.supply[j] = c ∧ ∀ j' : Fin tr.supply.size, tr.supply[j'] = c → j' = j) ∧
      ∀ ev ∈ tr.consumed.toList, ev.cell.allocId ≠ c.allocId

theorem nodup_of_nodup_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) :
    l.Nodup := by
  rw [List.Nodup, List.pairwise_map] at h
  exact h.imp fun hne e => hne (congrArg f e)

theorem nodup_getElem_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (e : l[i] = l[j]) : i = j := by
  have hp := List.pairwise_iff_getElem.1 h
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd e (hp i j hi hj hlt)
  · exact heq
  · exact absurd e.symm (hp j i hj hi hgt)

/-- The matching of a valid trace: an event's source is the position of its cell in the supply. -/
def causalMatching (tr : LinMemTrace) (h : LinMemSpec tr) : CausalMatching tr :=
  have hsup : tr.supply.toList = tr.init.toList ++ tr.produced.toList := by
    simp only [LinMemTrace.supply, Array.toList_append]
  have hN : (tr.supply.toList.map LinCell.allocId).Nodup := by rw [hsup]; exact h.1
  have hS : tr.supply.toList.Nodup := nodup_of_nodup_map _ hN
  have hP : tr.supply.toList.Perm
      (tr.consumed.toList.map ConsumedEvent.cell ++ tr.finalCells.toList) := by
    rw [hsup]; exact h.2.2
  have hN' : ((tr.consumed.toList.map ConsumedEvent.cell).map LinCell.allocId ++
      tr.finalCells.toList.map LinCell.allocId).Nodup := by
    rw [← List.map_append]; exact ((hP.map _).nodup_iff).1 hN
  have hmemC : ∀ i : Fin tr.consumed.size, tr.consumed[i].cell ∈ tr.supply.toList := fun i =>
    hP.mem_iff.2 (List.mem_append_left _ (List.mem_map.2
      ⟨tr.consumed[i], Array.mem_toList_iff.mpr (Array.getElem_mem i.2), rfl⟩))
  have hidx : ∀ i : Fin tr.consumed.size,
      tr.supply.toList.idxOf tr.consumed[i].cell < tr.supply.size := fun i => by
    have := List.idxOf_lt_length_of_mem (hmemC i)
    simpa only [Array.length_toList] using this
  have hexact : ∀ i : Fin tr.consumed.size,
      tr.supply[(⟨tr.supply.toList.idxOf tr.consumed[i].cell, hidx i⟩ : Fin tr.supply.size)]
        = tr.consumed[i].cell := fun i => by
    have := List.getElem_idxOf (x := tr.consumed[i].cell) (xs := tr.supply.toList)
      (by simpa only [Array.length_toList] using hidx i)
    simpa only [Array.getElem_toList, Fin.getElem_fin] using this
  have hdist : ∀ i₁ i₂ : Fin tr.consumed.size, i₁ ≠ i₂ →
      tr.consumed[i₁].cell.allocId ≠ tr.consumed[i₂].cell.allocId := fun i₁ i₂ hne e => by
    have hC := (List.nodup_append.1 hN').1
    have l1 : i₁.1 < ((tr.consumed.toList.map ConsumedEvent.cell).map LinCell.allocId).length := by
      simp only [List.length_map, Array.length_toList]; exact i₁.2
    have l2 : i₂.1 < ((tr.consumed.toList.map ConsumedEvent.cell).map LinCell.allocId).length := by
      simp only [List.length_map, Array.length_toList]; exact i₂.2
    have := nodup_getElem_inj hC l1 l2 (by
      simp only [List.getElem_map, Array.getElem_toList]; exact e)
    exact hne (Fin.ext this)
  { srcOf := fun i => ⟨tr.supply.toList.idxOf tr.consumed[i].cell, hidx i⟩
    exact := hexact
    causal := fun i => by
      rw [hexact i]
      exact h.2.1 _ (Array.mem_toList_iff.mpr (Array.getElem_mem i.2))
    injective := fun i₁ i₂ e => by
      refine Decidable.byContradiction fun hne => hdist i₁ i₂ hne ?_
      have e1 := hexact i₁
      have e2 := hexact i₂
      rw [← e1, ← e2]
      simp only [e]
    distinctIds := hdist
    unspent := fun c hc => by
      have hcS : c ∈ tr.supply.toList := hP.mem_iff.2 (List.mem_append_right _ hc)
      have hlt : tr.supply.toList.idxOf c < tr.supply.size := by
        simpa only [Array.length_toList] using List.idxOf_lt_length_of_mem hcS
      have hget : tr.supply[(⟨tr.supply.toList.idxOf c, hlt⟩ : Fin tr.supply.size)] = c := by
        have := List.getElem_idxOf (x := c) (xs := tr.supply.toList)
          (by simpa only [Array.length_toList] using hlt)
        simpa only [Array.getElem_toList, Fin.getElem_fin] using this
      refine ⟨⟨⟨_, hlt⟩, hget, ?_⟩, ?_⟩
      · intro j' hj'
        apply Fin.ext
        refine nodup_getElem_inj hS (by simpa only [Array.length_toList] using j'.2)
          (by simpa only [Array.length_toList] using hlt) ?_
        simp only [Array.getElem_toList]
        exact hj'.trans hget.symm
      · intro ev hev
        exact (List.nodup_append.1 hN').2.2 _
          (List.mem_map.2 ⟨ev.cell, List.mem_map.2 ⟨ev, hev, rfl⟩, rfl⟩) _
          (List.mem_map.2 ⟨c, hc, rfl⟩) }

/-- **`linmem_sound`**: a trace the array checker accepts has a causal matching: no cell is read
before it is written, none is read twice, and what is left over was never read. -/
theorem linmem_sound (tr : LinMemTrace) (h : verifyLinMemExec tr = true) :
    Nonempty (CausalMatching tr) :=
  ⟨causalMatching tr ((verifyLinMemExec_iff_spec tr).1 h)⟩

/-! ## 7. A lifetime ledger

A system that exposes a set of natural-number ids at each time (the wires of a net, the cells of a
stack) and never reuses an id writes a linear-memory trace: an id is produced at the first time it is
seen and consumed at the first time it is gone. -/

/-- Duplicates removed, keeping the last occurrence. -/
@[expose] def dedup : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

theorem mem_dedup {x : Nat} : ∀ {l : List Nat}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | y :: l => by
    by_cases h : y ∈ l
    · simp only [dedup, h, ↓reduceIte, List.mem_cons, mem_dedup (l := l)]
      constructor
      · exact Or.inr
      · rintro (rfl | h')
        · exact h
        · exact h'
    · simp only [dedup, h, ↓reduceIte, List.mem_cons, mem_dedup (l := l)]

theorem nodup_dedup : ∀ l : List Nat, (dedup l).Nodup
  | [] => by simp [dedup]
  | y :: l => by
    by_cases h : y ∈ l
    · simp only [dedup, h, ↓reduceIte]; exact nodup_dedup l
    · simp only [dedup, h, ↓reduceIte]
      exact List.nodup_cons.2 ⟨fun hm => h (mem_dedup.1 hm), nodup_dedup l⟩

/-- The ledger: the time, an id bound, and the four tables over `(id, birth)` cells. -/
structure Ledger where
  step : Nat
  next : Nat
  init : List (Nat × Nat)
  produced : List (Nat × Nat)
  consumed : List ((Nat × Nat) × Nat)
  live : List (Nat × Nat)
  deriving Repr

/-- The ledger at time 0: the ids present are the initial cells. -/
@[expose] def Ledger.start (vs : List Nat) (next : Nat) : Ledger :=
  { step := 0, next := next, init := (dedup vs).map (·, 0), produced := [], consumed := [],
    live := (dedup vs).map (·, 0) }

/-- One tick: the live cells whose id is gone are consumed now, the ids not seen before are
produced now. -/
@[expose] def Ledger.advance (L : Ledger) (vs : List Nat) (next' : Nat) : Ledger :=
  { step := L.step + 1
    next := next'
    init := L.init
    produced := L.produced ++
      ((dedup vs).filter fun x => !(L.live.map (·.1)).contains x).map (·, L.step + 1)
    consumed := L.consumed ++ (L.live.filter fun c => !vs.contains c.1).map (·, L.step + 1)
    live := (L.live.filter fun c => vs.contains c.1) ++
      ((dedup vs).filter fun x => !(L.live.map (·.1)).contains x).map (·, L.step + 1) }

/-- What a ledger keeps true. -/
structure Ledger.Inv (L : Ledger) : Prop where
  nodup : ((L.init ++ L.produced).map (·.1)).Nodup
  below : ∀ c ∈ L.init ++ L.produced, c.1 < L.next
  causal : ∀ ev ∈ L.consumed, ev.1.2 < ev.2
  bornBy : ∀ c ∈ L.live, c.2 ≤ L.step
  deadBy : ∀ ev ∈ L.consumed, ev.2 ≤ L.step
  balance : (L.init ++ L.produced).Perm (L.consumed.map (·.1) ++ L.live)

theorem Ledger.start_inv (vs : List Nat) (next : Nat) (h : ∀ x ∈ vs, x < next) :
    (Ledger.start vs next).Inv where
  nodup := by
    simp only [Ledger.start, List.append_nil, List.map_map]
    have : ((fun x : Nat × Nat => x.1) ∘ fun x : Nat => (x, 0)) = id := rfl
    rw [this, List.map_id]
    exact nodup_dedup vs
  below := by
    intro c hc
    simp only [Ledger.start, List.append_nil, List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact h x (mem_dedup.1 hx)
  causal := by intro ev hev; simp [Ledger.start] at hev
  bornBy := by
    intro c hc
    simp only [Ledger.start, List.mem_map] at hc
    obtain ⟨x, _, rfl⟩ := hc
    exact Nat.le_refl _
  deadBy := by intro ev hev; simp [Ledger.start] at hev
  balance := by simp [Ledger.start]

/-- The ids of the live cells are the ids last exposed. -/
theorem Ledger.start_live (vs : List Nat) (next x : Nat) :
    x ∈ (Ledger.start vs next).live.map (·.1) ↔ x ∈ vs := by
  simp only [Ledger.start, List.map_map]
  have : ((fun x : Nat × Nat => x.1) ∘ fun x : Nat => (x, 0)) = id := rfl
  rw [this, List.map_id]
  exact mem_dedup

theorem Ledger.advance_live (L : Ledger) (vs : List Nat) (next' x : Nat) :
    x ∈ (L.advance vs next').live.map (·.1) ↔ x ∈ vs := by
  simp only [Ledger.advance, List.map_append, List.mem_append, List.mem_map, List.mem_filter,
    List.contains_eq_mem, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    mem_dedup]
  constructor
  · rintro (⟨c, ⟨_, hc⟩, rfl⟩ | ⟨c, ⟨y, ⟨hy, _⟩, rfl⟩, rfl⟩)
    · exact hc
    · exact hy
  · intro hx
    by_cases hl : ∃ c, c ∈ L.live ∧ c.1 = x
    · obtain ⟨c, hc, rfl⟩ := hl
      exact Or.inl ⟨c, ⟨hc, hx⟩, rfl⟩
    · refine Or.inr ⟨(x, L.step + 1), ⟨x, ⟨hx, ?_⟩, rfl⟩, rfl⟩
      rintro ⟨c, hc, e⟩
      exact hl ⟨c, hc, e⟩

/-- A tick keeps the invariant when no id comes back: every exposed id is live or at least the
bound, and the new bound covers them. -/
theorem Ledger.advance_inv (L : Ledger) (h : L.Inv) (vs : List Nat) (next' : Nat)
    (hfresh : ∀ x ∈ vs, x ∈ L.live.map (·.1) ∨ L.next ≤ x) (hnext : ∀ x ∈ vs, x < next')
    (hmono : L.next ≤ next') : (L.advance vs next').Inv where
  nodup := by
    simp only [Ledger.advance, ← List.append_assoc, List.map_append (l₁ := L.init ++ L.produced),
      List.map_map]
    have e : ((fun x : Nat × Nat => x.1) ∘ fun x : Nat => (x, L.step + 1)) = id := rfl
    rw [e, List.map_id]
    refine List.nodup_append.2 ⟨h.nodup, (nodup_dedup vs).sublist List.filter_sublist, ?_⟩
    intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    have hlt := h.below c hc
    simp only [List.mem_filter, mem_dedup, List.contains_eq_mem, Bool.not_eq_true',
      decide_eq_false_iff_not] at hb
    rcases hfresh b hb.1 with hl | hge
    · exact absurd hl hb.2
    · omega
  below := by
    intro c hc
    simp only [Ledger.advance, ← List.append_assoc, List.mem_append (s := L.init ++ L.produced),
      List.mem_map, List.mem_filter, mem_dedup] at hc
    rcases hc with hc | ⟨x, ⟨hx, _⟩, rfl⟩
    · exact Nat.lt_of_lt_of_le (h.below c hc) hmono
    · exact hnext x hx
  causal := by
    intro ev hev
    simp only [Ledger.advance, List.mem_append, List.mem_map, List.mem_filter] at hev
    rcases hev with hev | ⟨c, ⟨hc, _⟩, rfl⟩
    · exact h.causal ev hev
    · exact Nat.lt_succ_of_le (h.bornBy c hc)
  bornBy := by
    intro c hc
    simp only [Ledger.advance, List.mem_append, List.mem_map, List.mem_filter] at hc
    rcases hc with ⟨hc, _⟩ | ⟨x, _, rfl⟩
    · exact Nat.le_succ_of_le (h.bornBy c hc)
    · exact Nat.le_refl _
  deadBy := by
    intro ev hev
    simp only [Ledger.advance, List.mem_append, List.mem_map, List.mem_filter] at hev
    rcases hev with hev | ⟨c, _, rfl⟩
    · exact Nat.le_succ_of_le (h.deadBy ev hev)
    · exact Nat.le_refl _
  balance := by
    simp only [Ledger.advance, ← List.append_assoc, List.map_append, List.map_map]
    have e : ((fun x : (Nat × Nat) × Nat => x.1) ∘ fun x : Nat × Nat => (x, L.step + 1)) = id := rfl
    rw [e, List.map_id]
    refine List.Perm.append_right _ ?_
    refine h.balance.trans ?_
    rw [List.append_assoc]
    refine List.Perm.append_left _ ?_
    have := List.filter_append_perm (fun c : Nat × Nat => vs.contains c.1) L.live
    exact (this.symm.trans List.perm_append_comm)

/-- The ledger as a trace: ids and steps as 64-bit words, payload 0. -/
@[expose] def ledgerCell (c : Nat × Nat) : LinCell := ⟨UInt64.ofNat c.1, UInt64.ofNat c.2, 0⟩

@[expose] def Ledger.toTrace (L : Ledger) : LinMemTrace :=
  { init := (L.init.map ledgerCell).toArray
    produced := (L.produced.map ledgerCell).toArray
    consumed := (L.consumed.map fun ev => ⟨ledgerCell ev.1, UInt64.ofNat ev.2⟩).toArray
    finalCells := (L.live.map ledgerCell).toArray }

theorem nodup_map_of_injOn {α β : Type} (f : α → β) :
    ∀ (l : List α), l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => by simp
  | x :: l, hn, hinj => by
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hn
    refine ⟨?_, nodup_map_of_injOn f l hn.2 fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    intro hm
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
    have := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self e
    exact hn.1 (this ▸ hy)

/-- **The ledger writes valid traces**: with ids and steps below `2^64`, the trace of a ledger that
kept its invariant satisfies `LinMemSpec`. -/
theorem Ledger.toTrace_spec (L : Ledger) (h : L.Inv) (hn : L.next ≤ 2 ^ 64) (hs : L.step < 2 ^ 64) :
    LinMemSpec L.toTrace := by
  refine ⟨?_, ?_, ?_⟩
  · show (((L.init.map ledgerCell).toArray.toList ++ (L.produced.map ledgerCell).toArray.toList).map
      LinCell.allocId).Nodup
    simp only [← List.map_append, List.map_map]
    have e : (LinCell.allocId ∘ ledgerCell) = (fun n => UInt64.ofNat n) ∘ (fun c : Nat × Nat => c.1) :=
      rfl
    rw [e, ← List.map_map]
    refine nodup_map_of_injOn _ _ h.nodup ?_
    intro a ha b hb hab
    obtain ⟨ca, hca, rfl⟩ := List.mem_map.1 ha
    obtain ⟨cb, hcb, rfl⟩ := List.mem_map.1 hb
    have la := h.below ca hca
    have lb := h.below cb hcb
    have := congrArg UInt64.toNat hab
    simp only [UInt64.toNat_ofNat'] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · intro ev hev
    simp only [Ledger.toTrace, List.mem_map] at hev
    obtain ⟨e, he, rfl⟩ := hev
    have c1 := h.causal e he
    have c2 := h.deadBy e he
    show UInt64.ofNat e.1.2 < UInt64.ofNat e.2
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact c1
  · show ((L.init.map ledgerCell).toArray.toList ++ (L.produced.map ledgerCell).toArray.toList).Perm
      (((L.consumed.map fun ev => (⟨ledgerCell ev.1, UInt64.ofNat ev.2⟩ : ConsumedEvent)).toArray.toList.map
        ConsumedEvent.cell) ++ (L.live.map ledgerCell).toArray.toList)
    simp only [List.map_map, ← List.map_append]
    have e : (ConsumedEvent.cell ∘ fun ev : (Nat × Nat) × Nat =>
        (⟨ledgerCell ev.1, UInt64.ofNat ev.2⟩ : ConsumedEvent)) = ledgerCell ∘ (fun ev => ev.1) := rfl
    rw [e, ← List.map_map, ← List.map_append]
    exact h.balance.map _

end Obend.SymbolicZk
