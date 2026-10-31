module
/- Ranks and compaction. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

/-! ## Ranks and compaction -/

theorem foldl_rankStep (l : List Bool) : ∀ (acc : Array Nat) (c : Nat),
    (l.foldl rankStep (acc, c)).2 = c + l.count true ∧
    (l.foldl rankStep (acc, c)).1.size = acc.size + l.length ∧
    (∀ i, i < acc.size → (l.foldl rankStep (acc, c)).1[i]? = acc[i]?) ∧
    (∀ i, i < l.length → (l.foldl rankStep (acc, c)).1[acc.size + i]? = some (c + (l.take i).count true)) := by
  induction l with
  | nil => intro acc c; simp
  | cons m rest ih =>
    intro acc c
    obtain ⟨count, size, prefix_, entries⟩ := ih (acc.push c) (if m then c + 1 else c)
    simp only [List.foldl_cons, rankStep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [count]; cases m <;> simp <;> omega
    · rw [size]; simp; omega
    · intro i bound
      rw [prefix_ i (by simp; omega)]
      simp [Array.getElem?_push, show i ≠ acc.size by omega]
    · intro i bound
      cases i with
      | zero =>
        simpa [Array.getElem?_push] using prefix_ acc.size (by simp)
      | succ j =>
        have := entries j (by simpa using bound)
        rw [show acc.size + (j + 1) = (acc.push c).size + j by simp; omega, this]
        cases m <;> simp <;> omega

public theorem rankTable_spec (marks : Array Bool) :
    (rankTable marks).2 = marks.count true ∧
    (rankTable marks).1.size = marks.size ∧
    ∀ i, i < marks.size → (rankTable marks).1[i]? = some ((marks.toList.take i).count true) := by
  have spec := foldl_rankStep marks.toList #[] 0
  simp only [rankTable, ← Array.foldl_toList]
  refine ⟨by simpa using spec.1, by simpa using spec.2.1, ?_⟩
  intro i bound
  simpa using spec.2.2.2 i (by simpa using bound)

public theorem filterMap_zip_getElem {α β : Type} (h : α → β) :
    ∀ (L : List α) (M : List Bool) (i : Nat) (c : α), L[i]? = some c → M[i]? = some true →
      ((L.zip M).filterMap fun entry => if entry.2 then some (h entry.1) else none)[(M.take i).count true]? =
        some (h c) := by
  intro L
  induction L with
  | nil => intro M i c found; simp at found
  | cons a L ih =>
    intro M i c found marked
    cases M with
    | nil => simp at marked
    | cons m M =>
      cases i with
      | zero =>
        simp at found marked
        subst found; subst marked
        simp
      | succ j =>
        simp only [List.getElem?_cons_succ] at found marked
        have := ih M j c found marked
        cases m <;> simpa [List.count_cons] using this

public theorem filterMap_zip_length {α β : Type} (h : α → β) :
    ∀ (L : List α) (M : List Bool), L.length = M.length →
      ((L.zip M).filterMap fun entry => if entry.2 then some (h entry.1) else none).length = M.count true := by
  intro L
  induction L with
  | nil => intro M same; cases M <;> simp_all
  | cons a L ih =>
    intro M same
    cases M with
    | nil => simp at same
    | cons m M =>
      have := ih M (by simpa using same)
      cases m <;> simp [this]

theorem count_take_le (M : List Bool) {a b : Nat} (le : a ≤ b) :
    (M.take a).count true ≤ (M.take b).count true := by
  have : (M.take b).take a = M.take a := by rw [List.take_take]; congr 1; omega
  rw [← this]
  exact (List.take_sublist _ _).count_le _

theorem count_take_succ (M : List Bool) {i : Nat} (marked : M[i]? = some true) :
    (M.take (i + 1)).count true = (M.take i).count true + 1 := by
  rw [List.take_add_one, marked]; simp

public theorem count_take_lt (M : List Bool) {i j : Nat} (lt : i < j) (marked : M[i]? = some true) :
    (M.take i).count true < (M.take j).count true := by
  have := count_take_le M (show i + 1 ≤ j by omega)
  rw [count_take_succ M marked] at this; omega

public theorem count_take_lt_count (M : List Bool) {i : Nat} (marked : M[i]? = some true) :
    (M.take i).count true < M.count true := by
  have bound : i < M.length := (List.getElem?_eq_some_iff.mp marked).1
  have := count_take_lt M bound marked
  rwa [List.take_length] at this

public theorem compact_size (f : Nat → Nat) (heap : Array Cell) (marks : Array Bool)
    (size : marks.size = heap.size) : (compact f heap marks).size = marks.count true := by
  rw [← Array.length_toList, compact, Array.toList_filterMap, Array.toList_zip, ← Array.count_toList]
  exact filterMap_zip_length _ _ _ (by simpa using size.symm)

public theorem compact_getElem (f : Nat → Nat) (heap : Array Cell) (marks : Array Bool)
    {a : Nat} {c : Cell} (found : heap[a]? = some c) (marked : marks[a]? = some true) :
    (compact f heap marks)[(marks.toList.take a).count true]? = some (renameCell f c) := by
  rw [← Array.getElem?_toList, compact, Array.toList_filterMap, Array.toList_zip]
  exact filterMap_zip_getElem _ _ _ _ _ (by simpa using found) (by simpa using marked)

end Obend.Core.Collect
