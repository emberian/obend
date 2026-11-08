module
public import Obend.Hardware.Gpu.BlockCoreMemory
@[expose] public section
namespace Obend.Hardware.Gpu.BlockCoreEncoding
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- Literal input memory only. The source program is a separate symbolic term;
no output evaluator is used to construct this encoding. -/
def rows : List (List Nat) → Term
  | [] => .lam (.lam (.nat 0))
  | r::rs => .lam (.ifZero (.bound 0) (encodeNats r) (.app (rows rs) (.bound 0)))

@[simp] theorem rows_substitute (rs : List (List Nat)) (σ : Nat → Term) :
    (rows rs).substitute σ = rows rs := by
  induction rs generalizing σ with
  | nil => simp [rows, Term.substitute]
  | cons r rs ih => simp [rows, Term.substitute, encodeNats_substitute, ih,
      liftSubstitution]

theorem rows_apply (rs : List (List Nat)) (a i : Nat) :
    Steps (.app (.app (rows rs) (.nat a)) (.nat i)) (.nat ((rs.getD a []).getD i 0)) := by
  induction rs generalizing a with
  | nil =>
    refine .next (.application _ (.beta _ _)) ?_
    simp only [rows, instantiate, Term.substitute]
    refine .next (.beta _ _) ?_
    simp only [instantiate, Term.substitute, List.getD_nil]
    exact .refl _
  | cons r rs ih =>
    refine .next (.application _ (.beta _ _)) ?_
    simp only [rows, instantiate, Term.substitute, encodeNats_substitute, rows_substitute, liftSubstitution]
    cases a with
    | zero =>
      refine .next (.application _ (.zero _ _)) ?_
      exact encodeNats_apply r i
    | succ a =>
      refine .next (.application _ (.successor a _ _)) ?_
      simp only [instantiate, Term.substitute, rows_substitute, List.getD_cons_succ, liftSubstitution]
      exact ih a

theorem map_getD {α β : Type} (f : α → β) (xs : List α) (d : α) (i : Nat) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

def memory (mem : Memory) : Term := rows (mem.toList.map fun row => row.toList.map (·.toNat))

theorem memory_sound (mem : Memory) : BlockCoreMemory.Denotes (memory mem) mem := by
  intro a i
  have h := rows_apply (mem.toList.map fun row => row.toList.map (·.toNat)) a i
  have outer := map_getD (fun row : Array Word => row.toList.map (·.toNat)) mem.toList #[] a
  have inner := map_getD (fun w : Word => w.toNat) (mem.toList.getD a #[]).toList 0#64 i
  simp only [Array.toList_empty, List.map_nil] at outer
  change (List.map (fun w : Word => w.toNat) (mem.toList.getD a #[]).toList).getD i 0 = _ at inner
  rw [outer, inner] at h
  simpa only [memory, List.getD_eq_getElem?_getD, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?] using h

end Obend.Hardware.Gpu.BlockCoreEncoding
end
