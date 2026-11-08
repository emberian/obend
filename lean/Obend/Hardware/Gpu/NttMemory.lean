module
public import Obend.Hardware.Gpu.NttTwiddles
public import Obend.Hardware.Gpu.NttSchedule
public import Obend.Hardware.Gpu.BlockLower
@[expose] public section
namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.BlockLower

/-- Every accepted transform's static schedule processes exactly its bit count. -/
theorem uploadSchedule_sum (n : Nat) : (uploadSchedule n).sum = Nat.log2 n := by
  unfold uploadSchedule
  exact uploadDegrees_sum _ _ _ (by split <;> decide) (Nat.le_refl _)

theorem sourceUploads_output (n : Nat) : (sourceUploads n).2 ≤ 1 :=
  buildUploads_output n (uploadSchedule n) 0 0 (by decide)

theorem initial_input (n : Nat) (input : Array Word) :
    (initialMemory (nttBlockProgram n) [input]).getD 0 #[] = input := by
  simp [initialMemory,nttBlockProgram]

/-- Initialization has exactly the shape used by the indexed lowering; no
input-dependent admission condition occurs here. -/
theorem initial_good (n : Nat) (input : Array Word) (hi : input.size = n) :
    BlockLower.Good (nttBlockProgram n) (initialMemory (nttBlockProgram n) [input]) := by
  constructor
  · simp [initialMemory,nttBlockProgram]
  · intro a ha
    have hab : a < 5 := ha
    have cases : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;>
      simp [initialMemory,nttBlockProgram,buffer,hi,twiddlePowers_size]

/-- Constant table entries are the actual runtime root powers for every index. -/
theorem initial_twiddle_value (n : Nat) (input : Array Word) (i : Nat) (hi : i < n) :
    (((initialMemory (nttBlockProgram n) [input]).getD 4 #[]).getD i 0#64).toNat =
      modPow (rootOfUnity n) i := by
  rw [initial_twiddles,twiddlePowers_toNat n _ i hi]

theorem maxFold_seed {α : Type} (f : α → Nat) (xs : List α) (seed : Nat) :
    seed ≤ xs.foldl (fun acc x => max acc (f x)) seed := by
  induction xs generalizing seed with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem maxFold_member {α : Type} (f : α → Nat) (xs : List α) (seed : Nat)
    (x : α) (hx : x ∈ xs) : f x ≤ xs.foldl (fun acc x => max acc (f x)) seed := by
  induction xs generalizing seed with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right _ _) (maxFold_seed f xs _)
    · exact ih _ hx

/-- Static shared storage covers each actual upload, including its packed tiles. -/
theorem sharedWords_covers (n : Nat) (d : Dispatch) (hd : d ∈ (sourceUploads n).1) :
    BlockNtt.tileSize d * BlockNtt.packing d ≤ sharedWords n :=
  maxFold_member (fun d => BlockNtt.tileSize d * BlockNtt.packing d) _ 1 d hd

theorem good_device (n : Nat) (mem : Memory) (hg : BlockLower.Good (nttBlockProgram n) mem)
    (a : Nat) (ha : a ≤ 1) : (mem.getD a #[]).size = n := by
  have h := hg.2 a (by change a < 5; omega)
  have cases : a=0 ∨ a=1 := by omega
  rcases cases with rfl | rfl <;> simpa [buffer,nttBlockProgram] using h

theorem good_shared (n : Nat) (mem : Memory) (hg : BlockLower.Good (nttBlockProgram n) mem)
    (a : Nat) (ha : a=2 ∨ a=3) : (mem.getD a #[]).size = sharedWords n := by
  have h := hg.2 a (by change a < 5; omega)
  rcases ha with rfl | rfl <;> simpa [buffer,nttBlockProgram] using h

theorem good_constants (n : Nat) (mem : Memory) (hg : BlockLower.Good (nttBlockProgram n) mem) :
    (mem.getD 4 #[]).size = n := by
  simpa [buffer,nttBlockProgram] using hg.2 4 (by change 4 < 5; decide)

theorem dispatch_good (p : Program) (d : Dispatch) (mem : Memory)
    (hg : BlockLower.Good p mem) : BlockLower.Good p (evalDispatch d mem) := by
  unfold evalDispatch
  induction List.range d.groups generalizing mem with
  | nil => exact hg
  | cons g gs ih => exact ih _ (evalGroup_good p d g mem hg)

end Obend.Hardware.Gpu.Ntt
