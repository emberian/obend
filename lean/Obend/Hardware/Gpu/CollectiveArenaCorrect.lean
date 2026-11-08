module
public import Obend.Hardware.Gpu.CollectiveArena
public import Obend.Hardware.Gpu.CollectiveBuildCorrect
@[expose] public section

/-! Public physical collective semantics. The only premises are successful
executable construction and admission. Flat memory and scratch are arbitrary. -/
namespace Obend.Hardware.Gpu.CollectiveArenaCorrect
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.ArrayEmit Obend.Hardware.Gpu.CollectiveArena
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveBuildCorrect
set_option autoImplicit false

theorem evalFold_read_congr (op : ReduceOp) (shape : FoldShape) (read read' : Nat → Word)
    (h : ∀ i < shape.inputLen, read i = read' i) : evalFold op shape read = evalFold op shape read' := by
  apply List.map_congr_left
  intro range hr
  apply foldRange_congr
  intro i hi hilen
  have hb := shape.ranges_bound range hr
  exact h i (by omega)

theorem placement_pull_value (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (flat : FlatMemory) (a i : Nat) (hv : Valid p a i) :
    valueAt (pullMemory p (arenaIndex first) (memoryOfFlat q flat)) a i =
      flat (address q (arenaIndex first a) i) := by
  exact (pullMemory_renames p (arenaIndex first) (memoryOfFlat q flat) a i hv).symm.trans
    ((memoryOfFlat_represents q flat) _ _ (placement_valid p q words src dst first h a i hv)).symm

/-- Exact fold output of the compiled physical block action, for every flat memory. -/
theorem build_arena_value (op : ReduceOp) (shape : FoldShape) (depth : Nat) (source block : Program)
    (words src dst : Nat) (hbuild : build op shape depth = .ok source)
    (hsource : source.check = .ok ()) (harena : inArena source words src dst = .ok block)
    (hblock : block.check = .ok ()) (flat : FlatMemory) (i : Nat) (hi : i < shape.outLen) :
    lowerProgram block flat (.device,dst+i) =
      (evalFold op shape (fun j => flat (.device,src+j))).getD i 0#64 := by
  obtain ⟨first,hplace⟩ := inArena_placement source block words src dst harena
  have hb := build_boundaries op shape depth source hbuild
  let mem := pullMemory source (arenaIndex first) (memoryOfFlat block flat)
  have hg : Obend.Hardware.Gpu.BlockLower.Good source mem :=
    placement_pullMemory_good source block words src dst first hplace _ (memoryOfFlat_good block flat)
  have hv : Valid source 1 i := ⟨by omega,by simpa [hb.2.2.2.2] using hi⟩
  have hphysical := placement_lowerProgram_value source block words src dst first hplace hsource hblock
    (memoryOfFlat block flat) flat (memoryOfFlat_good block flat) (memoryOfFlat_represents block flat) 1 i hv
  have haddr : address block (arenaIndex first 1) i = (.device,dst+i) := by
    simp [address,placement_buffer source block words src dst first hplace 1 (by omega),
      (placement_bases source block words src dst first hplace).2,hb.2.2.2.2]
  rw [haddr] at hphysical
  have hvalue := congrArg (fun xs : List Word => xs.getD i 0#64)
    (build_value op shape depth source hbuild hsource mem hg)
  have hvalue' : valueAt (evalProgram source mem) 1 i = (evalFold op shape (valueAt mem 0)).getD i 0#64 := by
    simpa [List.getD_eq_getElem?_getD,hi] using hvalue
  rw [hphysical,hvalue']
  congr 1
  apply evalFold_read_congr
  intro j hj
  have hvj : Valid source 0 j := ⟨by omega,by simpa [hb.2.2.2.1] using hj⟩
  rw [placement_pull_value source block words src dst first hplace flat 0 j hvj]
  congr 1
  simp [address,placement_buffer source block words src dst first hplace 0 (by omega),
    (placement_bases source block words src dst first hplace).1,hb.2.2.2.1]

/-- Input boundary cells are preserved even though they lie inside the live arena. -/
theorem build_arena_input_frame (op : ReduceOp) (shape : FoldShape) (depth : Nat) (source block : Program)
    (words src dst : Nat) (hbuild : build op shape depth = .ok source)
    (hsource : source.check = .ok ()) (harena : inArena source words src dst = .ok block)
    (hblock : block.check = .ok ()) (flat : FlatMemory) (i : Nat) (hi : i < shape.inputLen) :
    lowerProgram block flat (.device,src+i) = flat (.device,src+i) := by
  obtain ⟨first,hplace⟩ := inArena_placement source block words src dst harena
  have hb := build_boundaries op shape depth source hbuild
  let mem := pullMemory source (arenaIndex first) (memoryOfFlat block flat)
  have hg : Obend.Hardware.Gpu.BlockLower.Good source mem :=
    placement_pullMemory_good source block words src dst first hplace _ (memoryOfFlat_good block flat)
  have hv : Valid source 0 i := ⟨by omega,by simpa [hb.2.2.2.1] using hi⟩
  have hphysical := placement_lowerProgram_value source block words src dst first hplace hsource hblock
    (memoryOfFlat block flat) flat (memoryOfFlat_good block flat) (memoryOfFlat_represents block flat) 0 i hv
  have haddr : address block (arenaIndex first 0) i = (.device,src+i) := by
    simp [address,placement_buffer source block words src dst first hplace 0 (by omega),
      (placement_bases source block words src dst first hplace).1,hb.2.2.2.1]
  rw [haddr] at hphysical
  rw [hphysical,build_input_frame op shape depth source hbuild hsource mem hg i]
  have hread := placement_pull_value source block words src dst first hplace flat 0 i hv
  simpa [haddr] using hread

/-- Every original live graph word outside the output interval is unchanged.
This includes the input interval and gaps between all live allocations. -/
theorem build_arena_frame (op : ReduceOp) (shape : FoldShape) (depth : Nat) (source block : Program)
    (words src dst : Nat) (hbuild : build op shape depth = .ok source)
    (hsource : source.check = .ok ()) (harena : inArena source words src dst = .ok block)
    (hblock : block.check = .ok ()) (flat : FlatMemory) (j : Nat) (hj : j < words)
    (hout : j < dst ∨ dst+shape.outLen ≤ j) :
    lowerProgram block flat (.device,j) = flat (.device,j) := by
  obtain ⟨first,hplace⟩ := inArena_placement source block words src dst harena
  have hb := build_boundaries op shape depth source hbuild
  by_cases hin : src ≤ j ∧ j < src+shape.inputLen
  · have he : src+(j-src) = j := by omega
    simpa [he] using build_arena_input_frame op shape depth source block words src dst hbuild hsource
      harena hblock flat (j-src) (by omega)
  · apply placement_live_frame source block words src dst first hplace hsource flat j hj
    · rw [hb.2.2.2.1]
      simp only
      omega
    · simpa [hb.2.2.2.2] using hout

end Obend.Hardware.Gpu.CollectiveArenaCorrect
end
