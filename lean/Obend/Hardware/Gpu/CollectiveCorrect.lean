module
public import Obend.Hardware.Gpu.CollectiveBlock
public import Obend.Hardware.Gpu.PhaseSemantics
@[expose] public section

/-! The materialized collective phases implement the ordered tree equations.
All conclusions concern ArrayKernel.evalPhase/evalGroup, not a second evaluator.
Admission supplies bounds and scatter uniqueness; row invariants describe inputs
established by preceding phases, never assumed output correctness.
-/
namespace Obend.Hardware.Gpu.CollectiveCorrect
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
set_option autoImplicit false

/-- The actual upsweep register program combines adjacent ordered children. -/
theorem upPhase_value (p : Program) (op : ReduceOp) (parents src dst g : Nat)
    (mem : Memory) (hg : Good p mem)
    (hb : PhaseInBounds p (upPhase op parents src dst) g)
    (hn : ((upPhase op parents src dst).writeAddresses g).Nodup)
    (i : Nat) (hi : i < parents) :
    valueAt (evalPhase (upPhase op parents src dst) g mem) dst i =
      upStep op (valueAt mem src) i := by
  have h := evalPhase_value_written p (upPhase op parents src dst) mem g i hg hb hn hi
    ⟨dst,.lane,2⟩ (by simp [upPhase])
  simpa [upPhase, upStep, runRegisters, loadRegisters, twice, next, Ix.eval, valueAt, Std.HashMap.getD_insert] using h

/-- The left child receives the actual parent's prefix without recombination. -/
theorem downPhase_left (p : Program) (op : ReduceOp) (parents totals src dst g : Nat)
    (mem : Memory) (hg : Good p mem)
    (hb : PhaseInBounds p (downPhase op parents totals src dst) g)
    (hn : ((downPhase op parents totals src dst).writeAddresses g).Nodup)
    (i : Nat) (hi : i < parents) :
    valueAt (evalPhase (downPhase op parents totals src dst) g mem) dst (2*i) =
      downLeft (valueAt mem src) i := by
  have h := evalPhase_value_written p (downPhase op parents totals src dst) mem g i hg hb hn hi
    ⟨dst,twice,0⟩ (by simp [downPhase])
  simpa [downPhase, downLeft, runRegisters, loadRegisters, twice, next, Ix.eval, valueAt, Std.HashMap.getD_insert] using h

/-- The right child receives parent-prefix combined with the left subtree total. -/
theorem downPhase_right (p : Program) (op : ReduceOp) (parents totals src dst g : Nat)
    (mem : Memory) (hg : Good p mem)
    (hb : PhaseInBounds p (downPhase op parents totals src dst) g)
    (hn : ((downPhase op parents totals src dst).writeAddresses g).Nodup)
    (i : Nat) (hi : i < parents) :
    valueAt (evalPhase (downPhase op parents totals src dst) g mem) dst (2*i+1) =
      downRight op (valueAt mem totals) (valueAt mem src) i := by
  have h := evalPhase_value_written p (downPhase op parents totals src dst) mem g i hg hb hn hi
    ⟨dst,next,2⟩ (by simp [downPhase])
  simpa [downPhase, downRight, runRegisters, loadRegisters, twice, next, Ix.eval, valueAt, Std.HashMap.getD_insert] using h

/-- Child-indexed form used by the row and prefix invariants. -/
theorem downPhase_value (p : Program) (op : ReduceOp) (parents totals src dst g : Nat)
    (mem : Memory) (hg : Good p mem)
    (hb : PhaseInBounds p (downPhase op parents totals src dst) g)
    (hn : ((downPhase op parents totals src dst).writeAddresses g).Nodup)
    (i : Nat) (hi : i < 2*parents) :
    valueAt (evalPhase (downPhase op parents totals src dst) g mem) dst i =
      downStep op (valueAt mem totals) (valueAt mem src) i := by
  have hp : i/2 < parents := by omega
  by_cases he : i%2 = 0
  · have hidx : 2*(i/2) = i := by omega
    rw [← hidx]
    rw [downPhase_left p op parents totals src dst g mem hg hb hn (i/2) hp, downStep_even]
  · have hidx : 2*(i/2)+1 = i := by omega
    rw [← hidx]
    rw [downPhase_right p op parents totals src dst g mem hg hb hn (i/2) hp, downStep_odd]

/-- Source bounds and uniqueness produce the upsweep row invariant, universally. -/
theorem upPhase_fold (p : Program) (op : ReduceOp) (parents src dst g : Nat)
    (mem : Memory) (hg : Good p mem)
    (hb : PhaseInBounds p (upPhase op parents src dst) g)
    (hn : ((upPhase op parents src dst).writeAddresses g).Nodup)
    (read : Nat → Word) (start level : Nat)
    (hr : ∀ j < 2*parents, valueAt mem src j =
      foldRange op read (start+j*2^level) (2^level) op.identity)
    (i : Nat) (hi : i < parents) :
    valueAt (evalPhase (upPhase op parents src dst) g mem) dst i =
      foldRange op read (start+i*2^(level+1)) (2^(level+1)) op.identity := by
  rw [upPhase_value p op parents src dst g mem hg hb hn i hi]
  exact upStep_fold op read start level (valueAt mem src) i (hr _ (by omega)) (hr _ (by omega))

/-- Actual downsweep execution establishes the next exclusive-prefix row. -/
theorem downPhase_fold (p : Program) (op : ReduceOp) (parents totals src dst g : Nat)
    (mem : Memory) (hg : Good p mem)
    (hb : PhaseInBounds p (downPhase op parents totals src dst) g)
    (hn : ((downPhase op parents totals src dst).writeAddresses g).Nodup)
    (read : Nat → Word) (start level : Nat) (init : Word)
    (ht : ∀ j < 2*parents, valueAt mem totals j =
      foldRange op read (start+j*2^level) (2^level) op.identity)
    (hp : ∀ j < parents, valueAt mem src j = foldRange op read start (j*2^(level+1)) init)
    (i : Nat) (hi : i < 2*parents) :
    valueAt (evalPhase (downPhase op parents totals src dst) g mem) dst i =
      foldRange op read start (i*2^level) init := by
  rw [downPhase_value p op parents totals src dst g mem hg hb hn i hi]
  exact downStep_fold op read start level parents (valueAt mem totals) (valueAt mem src) init ht hp i hi

/-- A valid load phase is an indexed copy from the immutable input snapshot. -/
theorem loadPhase_value (p : Program) (src dst valid g : Nat) (offset : Ix)
    (mem : Memory) (hg : Good p mem) (hb : PhaseInBounds p (loadPhase src dst valid offset) g)
    (hn : ((loadPhase src dst valid offset).writeAddresses g).Nodup)
    (i : Nat) (hi : i < valid) :
    valueAt (evalPhase (loadPhase src dst valid offset) g mem) dst i =
      valueAt mem src (offset.eval g i+i) := by
  have h := evalPhase_value_written p (loadPhase src dst valid offset) mem g i hg hb hn hi
    ⟨dst,.lane,0⟩ (by simp [loadPhase])
  simpa [loadPhase, runRegisters, loadRegisters, Ix.eval, valueAt, Std.HashMap.getD_insert] using h

/-- Padding is the selected monoid's identity, not a special case for addition. -/
theorem fillPhase_value (p : Program) (op : ReduceOp) (dst start count g : Nat)
    (mem : Memory) (hg : Good p mem) (hb : PhaseInBounds p (fillPhase op dst start count) g)
    (hn : ((fillPhase op dst start count).writeAddresses g).Nodup)
    (i : Nat) (hi : i < count) :
    valueAt (evalPhase (fillPhase op dst start count) g mem) dst (start+i) = op.identity := by
  have h := evalPhase_value_written p (fillPhase op dst start count) mem g i hg hb hn hi
    ⟨dst,.add (.lit start) .lane,0⟩ (by simp [fillPhase])
  simpa [fillPhase, runRegisters, loadRegisters, Ix.eval, evalElemOp, valueAt,
    Obend.Hardware.OpenHypergraph.evalHypergraphOpBv] using h

/-- Any phase whose declared stores target other arrays preserves this array. -/
theorem phase_frame_array (p : Program) (ph : Phase) (g a : Nat) (mem : Memory)
    (hg : Good p mem) (hb : PhaseInBounds p ph g)
    (ha : ∀ w ∈ ph.writes, w.array ≠ a) (i : Nat) :
    valueAt (evalPhase ph g mem) a i = valueAt mem a i := by
  apply evalPhase_value_untouched p ph mem g a i hg hb
  intro h
  obtain ⟨l, _, h⟩ := List.mem_flatMap.mp h
  obtain ⟨w, hw, he⟩ := List.mem_map.mp h
  exact ha w hw (congrArg Prod.fst he)

/-- Every materialized upsweep row is its ordered reference subtree reduction.
The schedule is exactly the range/map tail used by CollectiveBlock.upsweep. -/
theorem upRows_value (p : Program) (op : ReduceOp) (base depth g : Nat)
    (mem : Memory) (read : Nat → Word) (hg : Good p mem)
    (hrow : ∀ i < 2^depth, valueAt mem base i = read i)
    (hb : ∀ k < depth,
      PhaseInBounds p (upPhase op (2^(depth-k-1)) (base+k) (base+k+1)) g)
    (hn : ∀ k < depth,
      ((upPhase op (2^(depth-k-1)) (base+k) (base+k+1)).writeAddresses g).Nodup)
    (steps : Nat) (hs : steps ≤ depth) :
    let result := ((List.range steps).map fun k =>
      upPhase op (2^(depth-k-1)) (base+k) (base+k+1)).foldl
        (fun m ph => evalPhase ph g m) mem
    ∀ k ≤ steps, ∀ i < 2^(depth-k),
      valueAt result (base+k) i = upValue op read 0 k i := by
  induction steps with
  | zero =>
    dsimp only
    intro k hk i hi
    have : k = 0 := by omega
    subst k
    simpa [upValue] using hrow i (by simpa using hi)
  | succ steps ih =>
    have hsd : steps < depth := by omega
    have previous := ih (by omega)
    let phases := (List.range steps).map fun k =>
      upPhase op (2^(depth-k-1)) (base+k) (base+k+1)
    let before := phases.foldl (fun m ph => evalPhase ph g m) mem
    have hgood : Good p before := evalGroup_good p ⟨0, phases⟩ g mem hg
    have hwidth : 2 * 2^(depth-steps-1) = 2^(depth-steps) := by
      have he : depth-steps = (depth-steps-1)+1 := by omega
      calc
        2 * 2^(depth-steps-1) = 2^((depth-steps-1)+1) := by simp [Nat.pow_succ, Nat.mul_comm]
        _ = 2^(depth-steps) := congrArg (2^·) he.symm
    dsimp only
    simp only [List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    intro k hk i hi
    by_cases he : k = steps+1
    · subst k
      simp only [← Nat.add_assoc]
      rw [upPhase_value p op (2^(depth-steps-1)) (base+steps) (base+steps+1)
        g before hgood (hb steps hsd) (hn steps hsd) i (by simpa [Nat.sub_sub] using hi)]
      have hip : i < 2^(depth-steps-1) := by simpa [Nat.sub_sub] using hi
      simp only [upStep, upValue]
      rw [previous steps (Nat.le_refl _) (2*i) (by rw [← hwidth]; omega),
        previous steps (Nat.le_refl _) (2*i+1) (by rw [← hwidth]; omega)]
    · have hk' : k ≤ steps := by omega
      rw [phase_frame_array p _ g (base+k) before hgood (hb steps hsd) ?_ i]
      · exact previous k hk' i hi
      · intro w hw
        simp only [upPhase, List.mem_singleton] at hw
        subst w
        simp only
        omega

/-- A whole schedule preserves arrays absent from every declared store. -/
theorem phases_frame_array (p : Program) (phases : List Phase) (g a : Nat) (mem : Memory)
    (hg : Good p mem) (hb : ∀ ph ∈ phases, PhaseInBounds p ph g)
    (ha : ∀ ph ∈ phases, ∀ w ∈ ph.writes, w.array ≠ a) (i : Nat) :
    valueAt (phases.foldl (fun m ph => evalPhase ph g m) mem) a i = valueAt mem a i := by
  apply evalPhases_value_untouched p phases mem g a i hg hb
  intro ph hph h
  obtain ⟨l, _, h⟩ := List.mem_flatMap.mp h
  obtain ⟨w, hw, he⟩ := List.mem_map.mp h
  exact ha ph hph w hw (congrArg Prod.fst he)

/-- Complete descending row traversal. The root prefixes may already contain a
hierarchical seed; only the explicit register program performs the fixup. -/
theorem downRows_value (p : Program) (op : ReduceOp) (up down height g : Nat)
    (read : Nat → Word) (start : Nat) (init : Word)
    (hsplit : ∀ k ≤ height, ∀ j ≤ height, up+k ≠ down+j)
    (depth : Nat) (hd : depth ≤ height) (mem : Memory) (hg : Good p mem)
    (ht : ∀ k ≤ depth, ∀ i < 2^(height-k), valueAt mem (up+k) i =
      foldRange op read (start+i*2^k) (2^k) op.identity)
    (hp : ∀ i < 2^(height-depth), valueAt mem (down+depth) i =
      foldRange op read start (i*2^depth) init)
    (hb : ∀ k < depth, PhaseInBounds p
      (downPhase op (2^(height-k-1)) (up+k) (down+k+1) (down+k)) g)
    (hn : ∀ k < depth, ((downPhase op (2^(height-k-1)) (up+k) (down+k+1) (down+k)).writeAddresses g).Nodup) :
    ∀ i < 2^height,
    valueAt (((List.range depth).reverse.map fun k =>
      downPhase op (2^(height-k-1)) (up+k) (down+k+1) (down+k)).foldl
      (fun m ph => evalPhase ph g m) mem) down i = foldRange op read start i init := by
  induction depth generalizing mem with
  | zero => simpa using hp
  | succ depth ih =>
    have hdh : depth < height := by omega
    let ph := downPhase op (2^(height-depth-1)) (up+depth) (down+depth+1) (down+depth)
    let after := evalPhase ph g mem
    have hgood : Good p after := foldWrites_good p mem (phaseWrites ph mem g) hg
    have hwidth : 2 * 2^(height-depth-1) = 2^(height-depth) := by
      have he : height-depth = height-depth-1+1 := by omega
      calc
        2 * 2^(height-depth-1) = 2^(height-depth-1+1) := by simp [Nat.pow_succ, Nat.mul_comm]
        _ = 2^(height-depth) := congrArg (2^·) he.symm
    have ht' : ∀ k ≤ depth, ∀ i < 2^(height-k), valueAt after (up+k) i =
        foldRange op read (start+i*2^k) (2^k) op.identity := by
      intro k hk i hi
      rw [phase_frame_array p ph g (up+k) mem hg (hb depth (by omega)) ?_ i]
      · exact ht k (by omega) i hi
      · intro w hw
        simp only [ph, downPhase, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> simp only <;>
          exact (hsplit k (by omega) depth (by omega)).symm
    have hp' : ∀ i < 2^(height-depth), valueAt after (down+depth) i =
        foldRange op read start (i*2^depth) init := by
      intro i hi
      apply downPhase_fold p op (2^(height-depth-1)) (up+depth) (down+depth+1)
        (down+depth) g mem hg (hb depth (by omega)) (hn depth (by omega)) read start depth init
      · intro j hj
        exact ht depth (by omega) j (by simpa [hwidth] using hj)
      · intro j hj
        simpa [Nat.add_assoc] using hp j (by simpa [Nat.sub_sub] using hj)
      · simpa [hwidth] using hi
    have result := ih (by omega) after hgood ht' hp' (fun k hk => hb k (by omega))
      (fun k hk => hn k (by omega))
    simpa [List.range_succ, List.reverse_append, List.map_append, List.foldl_append,
      ph, after] using result

/-- The seed is loaded once from its real prefix buffer, or materialized as the identity. -/
theorem seedPhase_value (p : Program) (op : ReduceOp) (dst g : Nat)
    (seed : Option (Nat × Ix)) (mem : Memory) (hg : Good p mem)
    (hb : PhaseInBounds p (seedPhase op dst seed) g)
    (hn : ((seedPhase op dst seed).writeAddresses g).Nodup) :
    valueAt (evalPhase (seedPhase op dst seed) g mem) dst 0 =
      match seed with
      | none => op.identity
      | some (src,index) => valueAt mem src (index.eval g 0) := by
  cases seed with
  | none => exact fillPhase_value p op dst 0 1 g mem hg hb hn 0 (by decide)
  | some seed =>
    rcases seed with ⟨src,index⟩
    have h := evalPhase_value_written p (seedPhase op dst (some (src,index))) mem g 0 hg hb hn
      (by simp [seedPhase]) ⟨dst,.lit 0,0⟩ (by simp [seedPhase])
    simpa [seedPhase, runRegisters, loadRegisters, Ix.eval, valueAt] using h

/-- The final copy implements exclusive or inclusive output from the same rows. -/
theorem storeScanPhase_value (p : Program) (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (dst valid g : Nat) (offset : Ix) (mem : Memory) (hg : Good p mem)
    (hb : PhaseInBounds p (storeScanPhase op mode tree dst valid offset) g)
    (hn : ((storeScanPhase op mode tree dst valid offset).writeAddresses g).Nodup)
    (i : Nat) (hi : i < valid) :
    valueAt (evalPhase (storeScanPhase op mode tree dst valid offset) g mem)
      dst (offset.eval g i+i) =
      if mode = .inclusive then op.combine (valueAt mem tree.down i) (valueAt mem tree.up i)
      else valueAt mem tree.down i := by
  have h := evalPhase_value_written p (storeScanPhase op mode tree dst valid offset) mem g i hg hb hn hi
    ⟨dst,.add offset .lane,if mode == .inclusive then 2 else 0⟩ (by simp [storeScanPhase])
  cases mode <;> simpa [storeScanPhase, runRegisters, loadRegisters, Ix.eval, valueAt,
    Std.HashMap.getD_insert] using h

/-- Loading the valid leaves and filling the remaining leaves produces precisely
identity padding of the original source snapshot, without an invalid source read. -/
theorem paddedLoad_value (p : Program) (op : ReduceOp) (src dst valid depth g start : Nat)
    (offset : Ix) (mem : Memory) (hg : Good p mem) (hv : valid ≤ 2^depth)
    (hoff : ∀ i < valid, offset.eval g i = start)
    (hbl : PhaseInBounds p (loadPhase src dst valid offset) g)
    (hnl : ((loadPhase src dst valid offset).writeAddresses g).Nodup)
    (hbf : valid < 2^depth → PhaseInBounds p (fillPhase op dst valid (2^depth-valid)) g)
    (hnf : valid < 2^depth → ((fillPhase op dst valid (2^depth-valid)).writeAddresses g).Nodup)
    (i : Nat) (hi : i < 2^depth) :
    valueAt (([loadPhase src dst valid offset] ++
      (if valid < 2^depth then [fillPhase op dst valid (2^depth-valid)] else [])).foldl
        (fun m ph => evalPhase ph g m) mem) dst i =
      paddedRead op (valueAt mem src) start valid i := by
  let loaded := evalPhase (loadPhase src dst valid offset) g mem
  have hgood : Good p loaded := foldWrites_good p mem (phaseWrites _ mem g) hg
  by_cases hf : valid < 2^depth
  · simp only [hf, ite_true, List.singleton_append, List.foldl_cons, List.foldl_nil]
    by_cases hv' : i < valid
    · have hframe : valueAt (evalPhase (fillPhase op dst valid (2^depth-valid)) g loaded) dst i =
          valueAt loaded dst i := by
        apply evalPhase_value_untouched p _ loaded g dst i hgood (hbf hf)
        simp only [Phase.writeAddresses, fillPhase, List.flatMap_cons, List.map_cons,
          List.map_nil, Ix.eval, List.flatMap_nil, List.append_nil]
        intro h
        obtain ⟨l, _, he⟩ := List.mem_flatMap.mp h
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at he
        omega
      rw [hframe, loadPhase_value p src dst valid g offset mem hg hbl hnl i hv', hoff i hv']
      simp [paddedRead, hv']
    · have hix : valid+(i-valid) = i := by omega
      have hfill := fillPhase_value p op dst valid (2^depth-valid) g loaded hgood (hbf hf)
        (hnf hf) (i-valid) (by omega)
      rw [hix] at hfill
      simpa [paddedRead, hv'] using hfill
  · simp only [hf, ite_false, List.append_nil, List.foldl_cons, List.foldl_nil]
    have hiv : i < valid := by omega
    rw [loadPhase_value p src dst valid g offset mem hg hbl hnl i hiv, hoff i hiv]
    simp [paddedRead, hiv]

/-- Every actual upsweep row computes the corresponding ordered padded subtree. -/
theorem upsweep_rows (p : Program) (op : ReduceOp) (tree : Trees) (src valid depth g start : Nat)
    (offset : Ix) (mem : Memory) (hg : Good p mem) (hv : valid ≤ 2^depth)
    (hoff : ∀ i < valid, offset.eval g i = start)
    (hb : ∀ ph ∈ upsweep op tree src valid depth offset, PhaseInBounds p ph g)
    (hn : ∀ ph ∈ upsweep op tree src valid depth offset, (ph.writeAddresses g).Nodup) :
    ∀ k ≤ depth, ∀ i < 2^(depth-k),
    valueAt ((upsweep op tree src valid depth offset).foldl (fun m ph => evalPhase ph g m) mem)
      (tree.up+k) i = upValue op (paddedRead op (valueAt mem src) start valid) 0 k i := by
  let prep := [loadPhase src tree.up valid offset] ++
    (if valid < 2^depth then [fillPhase op tree.up valid (2^depth-valid)] else [])
  let loaded := prep.foldl (fun m ph => evalPhase ph g m) mem
  have hgood : Good p loaded := evalGroup_good p ⟨0,prep⟩ g mem hg
  have hload : loadPhase src tree.up valid offset ∈ upsweep op tree src valid depth offset := by simp [upsweep]
  have hfill : valid < 2^depth → fillPhase op tree.up valid (2^depth-valid) ∈
      upsweep op tree src valid depth offset := by intro h; simp [upsweep,h]
  have hrow : ∀ i < 2^depth, valueAt loaded tree.up i =
      paddedRead op (valueAt mem src) start valid i :=
    paddedLoad_value p op src tree.up valid depth g start offset mem hg hv hoff
      (hb _ hload) (hn _ hload) (fun h => hb _ (hfill h)) (fun h => hn _ (hfill h))
  have hstep : ∀ k < depth, upPhase op (2^(depth-k-1)) (tree.up+k) (tree.up+k+1) ∈
      upsweep op tree src valid depth offset := by
    intro k hk
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  have result := upRows_value p op tree.up depth g loaded
    (paddedRead op (valueAt mem src) start valid) hgood hrow
    (fun k hk => hb _ (hstep k hk)) (fun k hk => hn _ (hstep k hk)) depth (Nat.le_refl _)
  simpa only [upsweep, List.foldl_append, prep, loaded] using result

/-- The public upsweep's stores are confined to its compact row allocation. -/
theorem upsweep_store (op : ReduceOp) (tree : Trees) (src valid depth : Nat) (offset : Ix)
    (ph : Phase) (hph : ph ∈ upsweep op tree src valid depth offset)
    (w : Write) (hw : w ∈ ph.writes) : ∃ k ≤ depth, w.array = tree.up+k := by
  simp only [upsweep, List.mem_append, List.mem_singleton] at hph
  rcases hph with (rfl | hf) | hu
  · simp only [loadPhase, List.mem_singleton] at hw
    subst w
    exact ⟨0, Nat.zero_le _, by simp⟩
  · split at hf
    next h =>
      simp only [List.mem_singleton] at hf
      subst ph
      simp only [fillPhase, List.mem_singleton] at hw
      subst w
      exact ⟨0, Nat.zero_le _, by simp⟩
    next h => simp at hf
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hu
    simp only [upPhase, List.mem_singleton] at hw
    subst w
    exact ⟨k+1, by have := List.mem_range.mp hk; omega, by simp [Nat.add_assoc]⟩

/-- Initial prefix supplied to a local scan, read from the input snapshot. -/
def seedValue (op : ReduceOp) (mem : Memory) (g : Nat) : Option (Nat × Ix) → Word
  | none => op.identity
  | some (a,ix) => valueAt mem a (ix.eval g 0)

/-- Concrete complete local scan: actual loads, padding, upsweep, seed,
downsweep, and store agree with the ordered input prefix for every valid lane. -/
theorem scanGroup_value (p : Program) (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst valid depth g start : Nat) (offset : Ix) (seed : Option (Nat × Ix))
    (mem : Memory) (hg : Good p mem) (hv : valid ≤ 2^depth)
    (hoff : ∀ i < valid, offset.eval g i = start)
    (hsplit : ∀ k ≤ depth, ∀ j ≤ depth, tree.up+k ≠ tree.down+j)
    (hseed : ∀ a ix, seed = some (a,ix) → ∀ k ≤ depth, tree.up+k ≠ a)
    (hb : ∀ ph ∈ scanPhases op mode tree src dst valid depth offset seed, PhaseInBounds p ph g)
    (hn : ∀ ph ∈ scanPhases op mode tree src dst valid depth offset seed, (ph.writeAddresses g).Nodup)
    (i : Nat) (hi : i < valid) :
    valueAt (evalGroup ⟨0,scanPhases op mode tree src dst valid depth offset seed⟩ g mem) dst (start+i) =
      foldRange op (valueAt mem src) start (i+mode.extra)
        (seedValue op mem g seed) := by
  let up := upsweep op tree src valid depth offset
  let sp := seedPhase op (tree.down+depth) seed
  let down := (List.range depth).reverse.map fun k =>
    downPhase op (2^(depth-k-1)) (tree.up+k) (tree.down+k+1) (tree.down+k)
  let out := storeScanPhase op mode tree dst valid offset
  let m1 := up.foldl (fun m ph => evalPhase ph g m) mem
  let m2 := evalPhase sp g m1
  let m3 := down.foldl (fun m ph => evalPhase ph g m) m2
  let read := paddedRead op (valueAt mem src) start valid
  let init := seedValue op mem g seed
  have hup : ∀ ph ∈ up, ph ∈ scanPhases op mode tree src dst valid depth offset seed := by
    intro ph h; simp only [scanPhases, List.mem_append, List.mem_singleton]; exact Or.inl (Or.inl (Or.inl h))
  have hsp : sp ∈ scanPhases op mode tree src dst valid depth offset seed := by simp [scanPhases,sp]
  have hdown : ∀ ph ∈ down, ph ∈ scanPhases op mode tree src dst valid depth offset seed := by
    intro ph h; simp only [scanPhases, List.mem_append, List.mem_singleton]; exact Or.inl (Or.inr h)
  have hout : out ∈ scanPhases op mode tree src dst valid depth offset seed := by simp [scanPhases,out]
  have hg1 : Good p m1 := evalGroup_good p ⟨0,up⟩ g mem hg
  have hg2 : Good p m2 := foldWrites_good p m1 (phaseWrites sp m1 g) hg1
  have hg3 : Good p m3 := evalGroup_good p ⟨0,down⟩ g m2 hg2
  have rows := upsweep_rows p op tree src valid depth g start offset mem hg hv hoff
    (fun ph h => hb ph (hup ph h)) (fun ph h => hn ph (hup ph h))
  have seedframe : ∀ a ix, seed = some (a,ix) → ∀ j, valueAt m1 a j = valueAt mem a j := by
    intro a ix he j
    apply phases_frame_array p up g a mem hg (fun ph h => hb ph (hup ph h)) _ j
    intro ph hp w hw
    obtain ⟨k,hk,heq⟩ := upsweep_store op tree src valid depth offset ph hp w hw
    rw [heq]
    exact hseed a ix he k hk
  have root : valueAt m2 (tree.down+depth) 0 = init := by
    rw [seedPhase_value p op (tree.down+depth) g seed m1 hg1 (hb sp hsp) (hn sp hsp)]
    cases seed with
    | none => rfl
    | some a => exact seedframe a.1 a.2 rfl _
  have sstores : ∀ w ∈ sp.writes, w.array = tree.down+depth := by
    intro w hw
    cases seed <;> simp only [sp, seedPhase, fillPhase, List.mem_singleton] at hw <;> subst w <;> rfl
  have row2 : ∀ k ≤ depth, ∀ j < 2^(depth-k), valueAt m2 (tree.up+k) j =
      foldRange op read (0+j*2^k) (2^k) op.identity := by
    intro k hk j hj
    rw [phase_frame_array p sp g (tree.up+k) m1 hg1 (hb sp hsp) ?_ j]
    · exact (rows k hk j hj).trans (upValue_eq_fold op read 0 k j)
    · intro w hw
      rw [sstores w hw]
      exact (hsplit k hk depth (Nat.le_refl _)).symm
  have dmember : ∀ k < depth, downPhase op (2^(depth-k-1)) (tree.up+k) (tree.down+k+1) (tree.down+k) ∈ down := by
    intro k hk
    exact List.mem_map.mpr ⟨k, List.mem_reverse.mpr (List.mem_range.mpr hk), rfl⟩
  have prefixes : ∀ j < 2^depth, valueAt m3 tree.down j = foldRange op read 0 j init :=
    downRows_value p op tree.up tree.down depth g read 0 init hsplit depth (Nat.le_refl _) m2 hg2 row2
      (by
        intro j hj
        have hj0 : j = 0 := by simpa using hj
        subst j
        simpa [foldRange] using root)
      (fun k hk => hb _ (hdown _ (dmember k hk)))
      (fun k hk => hn _ (hdown _ (dmember k hk)))
  have leaf : valueAt m3 tree.up i = read i := by
    rw [phases_frame_array p down g tree.up m2 hg2 (fun ph h => hb ph (hdown ph h)) ?_ i]
    · simpa [foldRange] using row2 0 (Nat.zero_le _) i (by simpa using (show i < 2^depth by omega))
    · intro ph hp w hw
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
      have hk' : k < depth := List.mem_range.mp (List.mem_reverse.mp hk)
      simp only [downPhase, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;>
        exact (by simpa using (hsplit 0 (Nat.zero_le _) k (by omega)).symm)
  simp only [evalGroup, scanPhases, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change valueAt (evalPhase out g m3) dst (start+i) = _
  rw [← hoff i hi, storeScanPhase_value p op mode tree dst valid g offset m3 hg3
    (hb out hout) (hn out hout) i hi, prefixes i (by omega), leaf, hoff i hi]
  have hend : i+mode.extra ≤ valid := by cases mode <;> simp [ScanMode.extra] <;> omega
  rw [← padded_prefix op (valueAt mem src) start valid (i+mode.extra) init hend]
  cases mode <;> simp [ScanMode.extra, foldRange_succ, read]

/-- Complete local reduction includes the empty-segment identity store. -/
theorem reduceGroup_value (p : Program) (op : ReduceOp) (tree : Trees)
    (src dst valid depth g start : Nat) (offset result : Ix) (mem : Memory)
    (hg : Good p mem) (hv : valid ≤ 2^depth)
    (hoff : ∀ i < valid, offset.eval g i = start)
    (hb : ∀ ph ∈ reducePhases op tree src dst valid depth offset result, PhaseInBounds p ph g)
    (hn : ∀ ph ∈ reducePhases op tree src dst valid depth offset result, (ph.writeAddresses g).Nodup) :
    valueAt (evalGroup ⟨0,reducePhases op tree src dst valid depth offset result⟩ g mem)
      dst (result.eval g 0) = foldRange op (valueAt mem src) start valid op.identity := by
  by_cases hz : valid = 0
  · subst valid
    let ph : Phase :=
      { lanes := 1
        reads := []
        code := [⟨.scalar (.const op.identity.toInt),[],0⟩]
        writes := [⟨dst,result,0⟩] }
    have hp : ph ∈ reducePhases op tree src dst 0 depth offset result := by simp [reducePhases,ph]
    have h := evalPhase_value_written p ph mem g 0 hg (hb ph hp) (hn ph hp) (by simp [ph])
      ⟨dst,result,0⟩ (by simp [ph])
    simpa [reducePhases, evalGroup, ph, runRegisters, loadRegisters, evalElemOp,
      Obend.Hardware.OpenHypergraph.evalHypergraphOpBv, foldRange, valueAt] using h
  · let up := upsweep op tree src valid depth offset
    let m1 := up.foldl (fun m ph => evalPhase ph g m) mem
    let out : Phase := {lanes := 1, reads := [⟨0,tree.up+depth,.lit 0⟩], code := [], writes := [⟨dst,result,0⟩]}
    have hup : ∀ ph ∈ up, ph ∈ reducePhases op tree src dst valid depth offset result := by
      intro ph hp; simp only [reducePhases, beq_iff_eq, hz, ite_false, List.mem_append]; exact Or.inl hp
    have hout : out ∈ reducePhases op tree src dst valid depth offset result := by simp [reducePhases,hz,out]
    have hg1 : Good p m1 := evalGroup_good p ⟨0,up⟩ g mem hg
    have rows := upsweep_rows p op tree src valid depth g start offset mem hg hv hoff
      (fun ph hp => hb ph (hup ph hp)) (fun ph hp => hn ph (hup ph hp)) depth (Nat.le_refl _) 0 (by simp)
    have h := evalPhase_value_written p out m1 g 0 hg1 (hb out hout) (hn out hout) (by simp [out])
      ⟨dst,result,0⟩ (by simp [out])
    have hr : valueAt (evalPhase out g m1) dst (result.eval g 0) = valueAt m1 (tree.up+depth) 0 := by
      simpa [out, runRegisters, loadRegisters, Ix.eval, valueAt] using h
    have hend := hr.trans (rows.trans (padded_reduce op (valueAt mem src) start valid depth hv))
    simpa only [reducePhases, beq_iff_eq, hz, ite_false, evalGroup, List.foldl_append,
      List.foldl_cons, List.foldl_nil, out, m1, up] using hend

/-- Static scatter classification for the actual scan schedule. -/
theorem scanPhases_store (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst valid depth : Nat) (offset : Ix) (seed : Option (Nat × Ix))
    (ph : Phase) (hph : ph ∈ scanPhases op mode tree src dst valid depth offset seed)
    (w : Write) (hw : w ∈ ph.writes) :
    (∃ k ≤ depth, w.array = tree.up+k ∨ w.array = tree.down+k) ∨
      (w.array = dst ∧ w.index = .add offset .lane ∧ ph.lanes = valid) := by
  simp only [scanPhases, List.mem_append, List.mem_singleton] at hph
  rcases hph with ((hu | hs) | hd) | ho
  · obtain ⟨k,hk,he⟩ := upsweep_store op tree src valid depth offset ph hu w hw
    exact Or.inl ⟨k,hk,Or.inl he⟩
  · subst ph
    have he : w.array = tree.down+depth := by
      cases seed <;> simp only [seedPhase, fillPhase, List.mem_singleton] at hw <;> subst w <;> rfl
    exact Or.inl ⟨depth,Nat.le_refl _,Or.inr he⟩
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hd
    have hk' : k < depth := List.mem_range.mp (List.mem_reverse.mp hk)
    simp only [downPhase, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact Or.inl ⟨k,by omega,Or.inr rfl⟩
  · subst ph
    simp only [storeScanPhase, List.mem_singleton] at hw
    subst w
    exact Or.inr ⟨rfl,rfl,rfl⟩

/-- A scan group preserves every cell outside its scratch rows and output interval. -/
theorem scanGroup_frame (p : Program) (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst valid depth g start : Nat) (offset : Ix) (seed : Option (Nat × Ix))
    (mem : Memory) (hg : Good p mem)
    (hoff : ∀ l < valid, offset.eval g l = start)
    (hb : ∀ ph ∈ scanPhases op mode tree src dst valid depth offset seed, PhaseInBounds p ph g)
    (a i : Nat) (hup : ∀ k ≤ depth, tree.up+k ≠ a) (hdown : ∀ k ≤ depth, tree.down+k ≠ a)
    (hout : a = dst → i < start ∨ start+valid ≤ i) :
    valueAt (evalGroup ⟨0,scanPhases op mode tree src dst valid depth offset seed⟩ g mem) a i =
      valueAt mem a i := by
  apply evalGroup_value_untouched p _ mem g a i hg hb
  intro ph hp h
  obtain ⟨l,hl,hw⟩ := List.mem_flatMap.mp h
  obtain ⟨w,hw,he⟩ := List.mem_map.mp hw
  have heq := Prod.mk.inj he
  rcases scanPhases_store op mode tree src dst valid depth offset seed ph hp w hw with hs | ho
  · obtain ⟨k,hk,hu | hd⟩ := hs
    · exact hup k hk (hu.symm.trans heq.1)
    · exact hdown k hk (hd.symm.trans heq.1)
  · have hld : l < valid := by simpa [ho.2.2] using List.mem_range.mp hl
    have hae : a = dst := heq.1.symm.trans ho.1
    have hie : start+l = i := by simpa [ho.2.1,Ix.eval,hoff l hld] using heq.2
    have := hout hae
    omega

/-- Static scatter classification for the actual reduction schedule. -/
theorem reducePhases_store (op : ReduceOp) (tree : Trees) (src dst valid depth : Nat)
    (offset result : Ix) (ph : Phase)
    (hph : ph ∈ reducePhases op tree src dst valid depth offset result)
    (w : Write) (hw : w ∈ ph.writes) :
    (∃ k ≤ depth, w.array = tree.up+k) ∨ (w.array = dst ∧ w.index = result ∧ ph.lanes = 1) := by
  by_cases hz : valid = 0
  · simp only [reducePhases, beq_iff_eq, hz, ite_true, List.mem_singleton] at hph
    subst ph
    simp only [List.mem_singleton] at hw
    subst w
    exact Or.inr ⟨rfl,rfl,rfl⟩
  · simp only [reducePhases, beq_iff_eq, hz, ite_false, List.mem_append, List.mem_singleton] at hph
    rcases hph with hu | ho
    · exact Or.inl (upsweep_store op tree src valid depth offset ph hu w hw)
    · subst ph
      simp only [List.mem_singleton] at hw
      subst w
      exact Or.inr ⟨rfl,rfl,rfl⟩

/-- A reduction group changes only its scratch rows and one aggregate slot. -/
theorem reduceGroup_frame (p : Program) (op : ReduceOp) (tree : Trees)
    (src dst valid depth g : Nat) (offset result : Ix) (mem : Memory) (hg : Good p mem)
    (hb : ∀ ph ∈ reducePhases op tree src dst valid depth offset result, PhaseInBounds p ph g)
    (a i : Nat) (hup : ∀ k ≤ depth, tree.up+k ≠ a) (hout : a = dst → result.eval g 0 ≠ i) :
    valueAt (evalGroup ⟨0,reducePhases op tree src dst valid depth offset result⟩ g mem) a i =
      valueAt mem a i := by
  apply evalGroup_value_untouched p _ mem g a i hg hb
  intro ph hp h
  obtain ⟨l,hl,hw⟩ := List.mem_flatMap.mp h
  obtain ⟨w,hw,he⟩ := List.mem_map.mp hw
  have heq := Prod.mk.inj he
  rcases reducePhases_store op tree src dst valid depth offset result ph hp w hw with hs | ho
  · obtain ⟨k,hk,hu⟩ := hs
    exact hup k hk (hu.symm.trans heq.1)
  · have hl0 : l = 0 := by have := List.mem_range.mp hl; rw [ho.2.2] at this; omega
    subst l
    exact hout (heq.1.symm.trans ho.1) (by simpa [ho.2.1] using heq.2)

end Obend.Hardware.Gpu.CollectiveCorrect
end
