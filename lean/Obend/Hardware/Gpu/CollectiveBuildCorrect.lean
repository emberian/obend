module
public import Obend.Hardware.Gpu.CollectiveReduceBuild
public import Obend.Hardware.Gpu.CollectiveScanExec
@[expose] public section

/-! Public collective correctness: successful source construction and source
admission imply the existing segmented fold semantics under the actual
ArrayKernel evaluator, for every shape-correct initial memory. -/
namespace Obend.Hardware.Gpu.CollectiveBuildCorrect
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.Gpu.CollectiveTrace Obend.Hardware.Gpu.CollectiveHierarchy
open Obend.Hardware.Gpu.CollectiveCorrect Obend.Hardware.Gpu.CollectiveCompose
open Obend.Hardware.Gpu.CollectiveExecute Obend.Hardware.Gpu.CollectiveBuildFacts
open Obend.Hardware.Gpu.CollectiveReduceBuild Obend.Hardware.Gpu.CollectiveScanExec
set_option autoImplicit false

/-- Public scan construction computes the requested segmented prefix folds and
preserves the input array. Scratch may initially contain arbitrary words. -/
theorem build_scan_correct (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (hcheck : p.check = .ok ())
    (mode : ScanMode) (hmode : shape.mode = some mode) (mem : Memory) (hg : Good p mem) :
    (List.range shape.outLen).map (valueAt (evalProgram p mem) 1) =
      evalFold op shape (valueAt mem 0) ∧
    (∀ i, valueAt (evalProgram p mem) 0 i = valueAt mem 0 i) := by
  obtain ⟨state,hrun,hp⟩ := build_success op shape depth p
    (build_tile_bounds op shape depth p hbuild) hbuild
  rw [buildAction_initial,hmode] at hrun
  simp only [Option.isSome_some,ite_true] at hrun
  let before := initialBuild shape.inputLen shape.inputLen depth
  have hs0 : 0 < before.buffers.size := by simp only [before,initialBuild_size]; omega
  have hs1 : 1 < before.buffers.size := by simp only [before,initialBuild_size]; omega
  have hv := scanChunks_correct p hcheck op (initialTree depth) mode 0 1 (segments shape.segments)
    (Nat.log2 (max 1 shape.inputLen)+2) before state hrun
    (by intro d hd; simpa [hp,toProgram] using hd) hs0 hs1
    (initialTree_outside depth 0 (by decide)) (initialTree_outside depth 1 (by decide))
    (by decide) (initialTree_below _ _ _) (initialTree_split depth)
    (layout_segments shape.segments) mem hg
  have heval : evalTail before state mem = evalProgram p mem := by
    simp [evalTail,before,initialBuild,evalTrace,hp,toProgram,evalProgram]
  rw [heval] at hv
  constructor
  · apply descriptor_output_eq_evalFold
    simpa [hmode] using hv.1
  · intro i
    exact hv.2 0 hs0 (initialTree_outside depth 0 (by decide)) i (by simp)

/-- Universal correctness of the actual public builder, both reduction forms
and both scan modes, with arbitrary empty segments and arbitrary input words.
The only runtime hypotheses are successful construction/admission and memory
shape; there is no hypothesis asserting an output value. -/
theorem build_correct (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (hcheck : p.check = .ok ())
    (mem : Memory) (hg : Good p mem) :
    (List.range shape.outLen).map (valueAt (evalProgram p mem) 1) =
      evalFold op shape (valueAt mem 0) ∧
    (∀ i, valueAt (evalProgram p mem) 0 i = valueAt mem 0 i) := by
  cases hmode : shape.mode with
  | none => exact build_reduce_correct op shape depth p hbuild hcheck hmode mem hg
  | some mode => exact build_scan_correct op shape depth p hbuild hcheck mode hmode mem hg

theorem build_value (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (hcheck : p.check = .ok ())
    (mem : Memory) (hg : Good p mem) :
    (List.range shape.outLen).map (valueAt (evalProgram p mem) 1) =
      evalFold op shape (valueAt mem 0) :=
  (build_correct op shape depth p hbuild hcheck mem hg).1

theorem build_input_frame (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (hcheck : p.check = .ok ())
    (mem : Memory) (hg : Good p mem) (i : Nat) :
    valueAt (evalProgram p mem) 0 i = valueAt mem 0 i :=
  (build_correct op shape depth p hbuild hcheck mem hg).2 i

theorem segmentRanges_length (mode : Option ScanMode) (start : Nat) (ns : List Nat) :
    (segmentRanges mode start ns).length = (if mode.isSome then ns.sum else ns.length) := by
  induction ns generalizing start with
  | nil => cases mode <;> rfl
  | cons n ns ih => cases mode <;> simp [segmentRanges,ih]

theorem shape_output_size (shape : FoldShape) :
    shape.outLen = (if shape.mode.isSome then shape.inputLen else shape.segments.length) := by
  cases shape <;> simp [FoldShape.outLen,FoldShape.ranges,FoldShape.mode,FoldShape.inputLen,
    FoldShape.segments,segmentRanges_length]

/-- Both public boundary arrays retain their exact declared size and ids through
all fresh hierarchy allocations; this applies to every fold shape. -/
theorem build_boundaries (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) :
    p.inputs = [0] ∧ p.outputs = [1] ∧ 2 ≤ p.buffers.length ∧
      buffer p 0 = ⟨shape.inputLen,.device,[]⟩ ∧ buffer p 1 = ⟨shape.outLen,.device,[]⟩ := by
  obtain ⟨state,hrun,hp⟩ := build_success op shape depth p
    (build_tile_bounds op shape depth p hbuild) hbuild
  rw [buildAction_initial] at hrun
  let before := initialBuild shape.inputLen (if shape.mode.isSome then shape.inputLen else shape.segments.length) depth
  have he : Extends before state := by
    cases hm : shape.mode with
    | none =>
      simp only [hm,Option.isSome_none,ite_false] at hrun
      have h := reduceInto_extends op (initialTree depth) (2^depth) 0 1 shape.segments
        (Nat.log2 (max 1 shape.inputLen)+2) _ state hrun
      simpa only [before,hm,Option.isSome_none,ite_false] using h
    | some mode =>
      simp only [hm,Option.isSome_some,ite_true] at hrun
      have h := scanInto_extends op mode (initialTree depth) (2^depth) 0 1 shape.segments
        (Nat.log2 (max 1 shape.inputLen)+2) _ state hrun
      simpa only [before,hm,Option.isSome_some,ite_true] using h
  have hs := extends_buffer_size before state he
  have hzero : 0 < before.buffers.size := by simp only [before,initialBuild_size]; omega
  have hone : 1 < before.buffers.size := by simp only [before,initialBuild_size]; omega
  refine ⟨by simp [hp,toProgram],by simp [hp,toProgram],?_,?_,?_⟩
  · simp only [hp,toProgram,Array.length_toList]
    have hb := initialBuild_size shape.inputLen (if shape.mode.isSome then shape.inputLen else shape.segments.length) depth
    change before.buffers.size = _ at hb
    omega
  · rw [hp]
    change state.buffers.toList.getD 0 default = _
    rw [extends_buffer before state he 0 hzero]
    exact initialBuild_input _ _ _
  · rw [hp]
    change state.buffers.toList.getD 1 default = _
    rw [extends_buffer before state he 1 hone,shape_output_size]
    exact initialBuild_output _ _ _

theorem build_input_size (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) : (buffer p 0).size = shape.inputLen := by
  rw [(build_boundaries op shape depth p hbuild).2.2.2.1]

theorem build_output_size (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) : (buffer p 1).size = shape.outLen := by
  rw [(build_boundaries op shape depth p hbuild).2.2.2.2]

theorem build_noConstants (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) : ∀ b ∈ p.buffers, b.storage ≠ .constant := by
  obtain ⟨state,hrun,hp⟩ := build_success op shape depth p
    (build_tile_bounds op shape depth p hbuild) hbuild
  rw [buildAction_initial] at hrun
  have hn : NoConstants state := by
    cases hm : shape.mode with
    | none =>
      simp only [hm,Option.isSome_none,ite_false] at hrun
      exact reduceChunks_noConstants op (initialTree depth) (2^depth) 0 1 (segments shape.segments)
        _ _ state hrun (initialBuild_noConstants _ _ _)
    | some mode =>
      simp only [hm,Option.isSome_some,ite_true] at hrun
      exact scanChunks_noConstants op mode (initialTree depth) (2^depth) 0 1 (segments shape.segments)
        _ _ state hrun (initialBuild_noConstants _ _ _)
  intro b hb
  exact hn b (by simpa [hp,toProgram] using hb)

/-- The actual upload initializer satisfies the sole memory-shape premise of
build_value whenever the input vector has the declared source length. -/
theorem build_initialMemory_good (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (input : Array Word) (hsize : input.size = shape.inputLen) :
    Good p (initialMemory p [input]) := by
  have hb := build_boundaries op shape depth p hbuild
  apply initMemory_single_good p input hb.1 (by omega)
  · rw [build_input_size op shape depth p hbuild]
    exact hsize
  · exact build_noConstants op shape depth p hbuild

/-- End-to-end value theorem starting with the actual ArrayKernel upload
initializer, without a memory-shape premise on the caller. -/
theorem build_initialMemory_value (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (hcheck : p.check = .ok ())
    (input : Array Word) (hsize : input.size = shape.inputLen) :
    (List.range shape.outLen).map (valueAt (evalProgram p (initialMemory p [input])) 1) =
      evalFold op shape (fun i => input.getD i (0#64)) := by
  have hg := build_initialMemory_good op shape depth p hbuild input hsize
  have h := build_value op shape depth p hbuild hcheck (initialMemory p [input]) hg
  have hb := build_boundaries op shape depth p hbuild
  have hlen : 0 < p.buffers.length := by omega
  have hread : valueAt (initialMemory p [input]) 0 = fun i => input.getD i (0#64) := by
    funext i
    simp [valueAt,initialMemory,hb.1,Array.getD_eq_getD_getElem?,hlen]
  rw [hread] at h
  exact h

end Obend.Hardware.Gpu.CollectiveBuildCorrect
end
