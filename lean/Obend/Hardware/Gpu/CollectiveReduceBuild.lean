module
public import Obend.Hardware.Gpu.CollectiveReduceExec
@[expose] public section

/-! Public reduction correctness. All descriptor and allocation premises of the
recursive proof are discharged from the successful executable builder. -/
namespace Obend.Hardware.Gpu.CollectiveReduceBuild
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.Gpu.CollectiveTrace Obend.Hardware.Gpu.CollectiveHierarchy
open Obend.Hardware.Gpu.CollectiveCorrect Obend.Hardware.Gpu.CollectiveCompose
open Obend.Hardware.Gpu.CollectiveExecute Obend.Hardware.Gpu.CollectiveBuildFacts
open Obend.Hardware.Gpu.CollectiveReduceExec
set_option autoImplicit false

/-- A successful builder has passed its actual tuning-range guard. -/
theorem build_tile_bounds (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (h : build op shape depth = .ok p) : 1 ≤ depth ∧ depth ≤ 8 := by
  by_cases ht : 1 ≤ depth ∧ depth ≤ 8
  · exact ht
  · simp [build,ht,throw,throwThe,bind,Except.bind] at h

@[simp] theorem initialBuild_size (inputSize outputSize depth : Nat) :
    (initialBuild inputSize outputSize depth).buffers.size = 2+2*(depth+1) := by
  simp [initialBuild,treeRows]
  omega

theorem initialTree_outside (depth a : Nat) (ha : a < 2) : Outside (initialTree depth) a := by
  intro k hk
  simp only [initialTree]
  constructor <;> omega

theorem initialTree_below (inputSize outputSize depth : Nat) :
    RowsBelow (initialTree depth) (initialBuild inputSize outputSize depth).buffers.size := by
  intro k hk
  simp only [initialTree] at hk ⊢
  rw [initialBuild_size]
  constructor <;> omega

theorem initialTree_split (depth : Nat) : Split (initialTree depth) := by
  intro k hk j hj
  simp only [initialTree] at hk hj ⊢
  omega

theorem initialBuild_input (inputSize outputSize depth : Nat) :
    buffer (toProgram (initialBuild inputSize outputSize depth)) 0 = ⟨inputSize,.device,[]⟩ := by
  simp [buffer,toProgram,initialBuild]

theorem initialBuild_output (inputSize outputSize depth : Nat) :
    buffer (toProgram (initialBuild inputSize outputSize depth)) 1 = ⟨outputSize,.device,[]⟩ := by
  simp [buffer,toProgram,initialBuild]

/-- The public reduction builder computes evalFold for every shape-correct memory,
including arbitrary scratch contents, and preserves its input array. -/
theorem build_reduce_correct (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (hcheck : p.check = .ok ())
    (hmode : shape.mode = none) (mem : Memory) (hg : Good p mem) :
    (List.range shape.outLen).map (valueAt (evalProgram p mem) 1) =
      evalFold op shape (valueAt mem 0) ∧
    (∀ i, valueAt (evalProgram p mem) 0 i = valueAt mem 0 i) := by
  obtain ⟨state,hrun,hp⟩ := build_success op shape depth p
    (build_tile_bounds op shape depth p hbuild) hbuild
  rw [buildAction_initial,hmode] at hrun
  simp only [Option.isSome_none,ite_false] at hrun
  let before := initialBuild shape.inputLen shape.segments.length depth
  have hs0 : 0 < before.buffers.size := by simp [before]; omega
  have hs1 : 1 < before.buffers.size := by simp [before]; omega
  have hv := reduceChunks_correct p hcheck op (initialTree depth) 0 1 (segments shape.segments)
    (Nat.log2 (max 1 shape.inputLen)+2) before state hrun
    (by intro d hd; simpa [hp,toProgram] using hd) hs0 hs1
    (initialTree_outside depth 0 (by decide)) (initialTree_outside depth 1 (by decide))
    (by decide) (initialTree_below _ _ _) (layout_segments shape.segments) mem hg
  have heval : evalTail before state mem = evalProgram p mem := by
    simp [evalTail,before,initialBuild,evalTrace,hp,toProgram,evalProgram]
  rw [heval] at hv
  constructor
  · apply descriptor_output_eq_evalFold
    simpa [hmode] using hv.1
  · intro i
    exact hv.2 0 hs0 (initialTree_outside depth 0 (by decide)) i (by simp)

/-- Boundary metadata survives every fresh summary allocation and emitted trace. -/
theorem build_reduce_boundaries (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (hmode : shape.mode = none) :
    p.inputs = [0] ∧ p.outputs = [1] ∧ 2 ≤ p.buffers.length ∧
      buffer p 0 = ⟨shape.inputLen,.device,[]⟩ ∧
      buffer p 1 = ⟨shape.segments.length,.device,[]⟩ := by
  obtain ⟨state,hrun,hp⟩ := build_success op shape depth p
    (build_tile_bounds op shape depth p hbuild) hbuild
  rw [buildAction_initial,hmode] at hrun
  simp only [Option.isSome_none,ite_false] at hrun
  let before := initialBuild shape.inputLen shape.segments.length depth
  have he := reduceInto_extends op (initialTree depth) (2^depth) 0 1 shape.segments
    (Nat.log2 (max 1 shape.inputLen)+2) before state hrun
  have hs := extends_buffer_size before state he
  have hzero : 0 < before.buffers.size := by simp [before]; omega
  have hone : 1 < before.buffers.size := by simp [before]; omega
  refine ⟨by simp [hp,toProgram],by simp [hp,toProgram],?_,?_,?_⟩
  · simp only [hp,toProgram,Array.length_toList]
    have hb := initialBuild_size shape.inputLen shape.segments.length depth
    change before.buffers.size = _ at hb
    omega
  · rw [hp]
    change state.buffers.toList.getD 0 default = _
    rw [extends_buffer before state he 0 hzero]
    exact initialBuild_input _ _ _
  · rw [hp]
    change state.buffers.toList.getD 1 default = _
    rw [extends_buffer before state he 1 hone]
    exact initialBuild_output _ _ _

end Obend.Hardware.Gpu.CollectiveReduceBuild
end
