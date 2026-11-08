module
public import Obend.Hardware.Gpu.CollectiveTrace
public import Obend.Hardware.Gpu.CollectiveCorrect
@[expose] public section

/-! Metadata invariants of the actual collective builder. Allocation receipts
name concrete buffer ranges; no execution-result premise is used. -/
namespace Obend.Hardware.Gpu.CollectiveBuildFacts
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTrace
open Obend.Hardware.Gpu.CollectiveCorrect Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

@[simp] theorem treeRows_length (depth : Nat) : (treeRows depth).length = depth+1 := by
  simp [treeRows]

@[simp] theorem treeRows_get (depth k : Nat) (hk : k ≤ depth) :
    (treeRows depth).getD k default = ⟨2^(depth-k),.shared,[]⟩ := by
  simp [treeRows,List.getD_eq_getElem?_getD,show k < depth+1 by omega]

@[simp] theorem allocateTrees_run (depth : Nat) (s : Build) :
    (allocateTrees depth).run s = .ok
      (⟨s.buffers.size,s.buffers.size+depth+1,depth⟩,
        {s with buffers := s.buffers ++ (treeRows depth).toArray ++ (treeRows depth).toArray}) := rfl

theorem allocateTrees_success (depth : Nat) (before after : Build) (tree : Trees)
    (h : (allocateTrees depth).run before = .ok (tree,after)) :
    tree.up = before.buffers.size ∧ tree.down = before.buffers.size+depth+1 ∧ tree.depth = depth ∧
      after.buffers.toList = before.buffers.toList ++ treeRows depth ++ treeRows depth ∧
      after.dispatches = before.dispatches := by
  simp only [allocateTrees_run,Except.ok.injEq,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩
  simp

theorem allocateTrees_extends (depth : Nat) (before after : Build) (tree : Trees)
    (h : (allocateTrees depth).run before = .ok (tree,after)) : Extends before after := by
  obtain ⟨_,_,_,hb,hd⟩ := allocateTrees_success depth before after tree h
  exact ⟨⟨treeRows depth ++ treeRows depth,by simpa [List.append_assoc] using hb⟩,
    ⟨[],by simp [hd]⟩⟩

/-- Both row families are disjoint and every preexisting buffer is outside them. -/
theorem allocateTrees_disjoint (depth : Nat) (before after : Build) (tree : Trees)
    (h : (allocateTrees depth).run before = .ok (tree,after)) :
    (∀ k ≤ depth, ∀ j ≤ depth, tree.up+k ≠ tree.down+j) ∧
    (∀ a < before.buffers.size, ∀ k ≤ depth, tree.up+k ≠ a ∧ tree.down+k ≠ a) := by
  obtain ⟨hu,hd,_,_,_⟩ := allocateTrees_success depth before after tree h
  constructor
  · intro k hk j hj; omega
  · intro a ha k hk; constructor <;> omega

theorem allocateTrees_size (depth : Nat) (before after : Build) (tree : Trees)
    (h : (allocateTrees depth).run before = .ok (tree,after)) :
    after.buffers.size = before.buffers.size+2*(depth+1) := by
  have hb := (allocateTrees_success depth before after tree h).2.2.2.1
  have := congrArg List.length hb
  simp only [List.length_append,Array.length_toList,treeRows_length] at this
  omega

/-- Future allocations start beyond both materialized tree row families. -/
theorem allocateTrees_before_fresh (depth : Nat) (before after : Build) (tree : Trees)
    (h : (allocateTrees depth).run before = .ok (tree,after)) :
    ∀ k ≤ depth, tree.up+k < after.buffers.size ∧ tree.down+k < after.buffers.size := by
  obtain ⟨hu,hd,_,_,_⟩ := allocateTrees_success depth before after tree h
  have hs := allocateTrees_size depth before after tree h
  intro k hk; constructor <;> omega

/-- Ordinary allocation returns a fresh index and preserves all preceding metadata. -/
theorem allocate_fresh (size : Nat) (storage : Storage) (before after : Build) (id : Nat)
    (h : (allocate size storage).run before = .ok (id,after)) :
    id = before.buffers.size ∧ after.buffers.size = id+1 ∧
    (∀ a < before.buffers.size, a ≠ id) ∧ Extends before after := by
  obtain ⟨rfl,rfl⟩ := allocate_success size storage before after id h
  exact ⟨rfl,by simp,by intro a ha; omega,allocate_extends size storage before⟩

theorem localReduce_extends (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (before after : Build) (h : (localReduce op tree src dst cs).run before = .ok ((),after)) :
    Extends before after := by
  rw [localReduce_success op tree src dst cs before after h]
  exact appendTrace_extends _ _

theorem localScan_extends (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (seed : Option Nat) (before after : Build)
    (h : (localScan op mode tree src dst cs seed).run before = .ok ((),after)) : Extends before after := by
  rw [localScan_success op mode tree src dst cs seed before after h]
  exact appendTrace_extends _ _

/-- Composition of append-only builder actions, independent of their return values. -/
theorem bind_extends {α β : Type} (first : BuildM α) (next : α → BuildM β)
    (hfirst : ∀ s t a, first.run s = .ok (a,t) → Extends s t)
    (hnext : ∀ a s t b, (next a).run s = .ok (b,t) → Extends s t)
    (before after : Build) (b : β) (h : (first >>= next).run before = .ok (b,after)) :
    Extends before after := by
  obtain ⟨a,middle,ha,hb⟩ := bind_success first next before after b h
  exact extends_trans _ _ _ (hfirst before middle a ha) (hnext a middle after b hb)

theorem reduceChunksInto_extends (op : ReduceOp) (tree : Trees) (tile src dst : Nat) (cs : List Chunk)
    (fuel : Nat) (before after : Build)
    (h : (reduceChunksInto op tree tile src dst cs fuel).run before = .ok ((),after)) : Extends before after := by
  induction fuel generalizing src dst cs before after with
  | zero =>
    change (Except.error "collective reduction: insufficient hierarchy depth" : Except String (Unit × Build)) = .ok ((),after) at h
    cases h
  | succ fuel ih =>
    unfold reduceChunksInto at h
    obtain ⟨u,s0,hs,hrest⟩ := bind_success _ _ _ _ _ h
    cases u
    have he0 := localReduce_extends op tree src dst (cs.filter (·.length ≤ tile)) before s0 hs
    split at hrest
    · obtain ⟨total,s1,ha,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨u,s2,hl,hr⟩ := bind_success _ _ _ _ _ hrest
      cases u
      have he1 := (allocate_fresh (splitChunks tile (cs.filter (tile < ·.length))).length .device s0 s1 total ha).2.2.2
      have he2 := localReduce_extends op tree src total (splitChunks tile (cs.filter (tile < ·.length))) s1 s2 hl
      have he3 := ih total dst _ s2 after hr
      exact extends_trans _ _ _ he0 (extends_trans _ _ _ (extends_trans _ _ _ he1 he2) he3)
    · have he : s0 = after := congrArg Prod.snd (Except.ok.inj hrest)
      subst after
      exact he0

theorem scanChunksInto_extends (op : ReduceOp) (mode : ScanMode) (tree : Trees) (tile src dst : Nat)
    (cs : List Chunk) (fuel : Nat) (before after : Build)
    (h : (scanChunksInto op mode tree tile src dst cs fuel).run before = .ok ((),after)) : Extends before after := by
  induction fuel generalizing mode src dst cs before after with
  | zero =>
    change (Except.error "collective scan: insufficient hierarchy depth" : Except String (Unit × Build)) = .ok ((),after) at h
    cases h
  | succ fuel ih =>
    unfold scanChunksInto at h
    obtain ⟨u,s0,hs,hrest⟩ := bind_success _ _ _ _ _ h
    cases u
    have he0 := localScan_extends op mode tree src dst (cs.filter (·.length ≤ tile)) none before s0 hs
    split at hrest
    · obtain ⟨total,s1,ha,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨prefixes,s2,hb,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨u,s3,hl,hrest⟩ := bind_success _ _ _ _ _ hrest
      cases u
      obtain ⟨u,s4,hr,hrest⟩ := bind_success _ _ _ _ _ hrest
      cases u
      have he1 := (allocate_fresh (splitChunks tile (cs.filter (tile < ·.length))).length .device s0 s1 total ha).2.2.2
      have he2 := (allocate_fresh (splitChunks tile (cs.filter (tile < ·.length))).length .device s1 s2 prefixes hb).2.2.2
      have he3 := localReduce_extends op tree src total (splitChunks tile (cs.filter (tile < ·.length))) s2 s3 hl
      have he4 := ih .exclusive total prefixes _ s3 s4 hr
      have he5 := localScan_extends op mode tree src dst (splitChunks tile (cs.filter (tile < ·.length))) (some prefixes) s4 after hrest
      exact extends_trans _ _ _ he0 (extends_trans _ _ _ (extends_trans _ _ _ (extends_trans _ _ _ (extends_trans _ _ _ he1 he2) he3) he4) he5)
    · have he : s0 = after := congrArg Prod.snd (Except.ok.inj hrest)
      subst after
      exact he0

theorem reduceInto_extends (op : ReduceOp) (tree : Trees) (tile src dst : Nat) (ns : List Nat)
    (fuel : Nat) (before after : Build)
    (h : (reduceInto op tree tile src dst ns fuel).run before = .ok ((),after)) : Extends before after :=
  reduceChunksInto_extends op tree tile src dst (segments ns) fuel before after h

theorem scanInto_extends (op : ReduceOp) (mode : ScanMode) (tree : Trees) (tile src dst : Nat)
    (ns : List Nat) (fuel : Nat) (before after : Build)
    (h : (scanInto op mode tree tile src dst ns fuel).run before = .ok ((),after)) : Extends before after :=
  scanChunksInto_extends op mode tree tile src dst (segments ns) fuel before after h

/-- Exact shared buffer metadata at every allocated upsweep row. -/
theorem allocateTrees_up_buffer (depth : Nat) (before after : Build) (tree : Trees)
    (h : (allocateTrees depth).run before = .ok (tree,after)) (k : Nat) (hk : k ≤ depth) :
    buffer (toProgram after) (tree.up+k) = ⟨2^(depth-k),.shared,[]⟩ := by
  obtain ⟨hu,_,_,hb,_⟩ := allocateTrees_success depth before after tree h
  have hkl : k < (treeRows depth).length := by simp; omega
  simp only [buffer,toProgram,hb,hu,List.append_assoc,List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), Array.length_toList, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hkl]
  exact treeRows_get depth k hk

/-- Exact shared buffer metadata at every allocated downsweep row. -/
theorem allocateTrees_down_buffer (depth : Nat) (before after : Build) (tree : Trees)
    (h : (allocateTrees depth).run before = .ok (tree,after)) (k : Nat) (hk : k ≤ depth) :
    buffer (toProgram after) (tree.down+k) = ⟨2^(depth-k),.shared,[]⟩ := by
  obtain ⟨_,hd,_,hb,_⟩ := allocateTrees_success depth before after tree h
  simp only [buffer,toProgram,hb,hd,List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append,Array.length_toList,treeRows_length]
  have hi : before.buffers.size+depth+1+k-(before.buffers.size+(depth+1)) = k := by omega
  rw [hi]
  exact treeRows_get depth k hk

/-- Fresh buffers stay distinct from every earlier id after arbitrary builder extensions. -/
theorem fresh_after_extends (before middle after : Build) (he : Extends before middle)
    (size : Nat) (storage : Storage) (id : Nat)
    (ha : (allocate size storage).run middle = .ok (id,after)) :
    before.buffers.size ≤ id ∧ (∀ a < before.buffers.size, a ≠ id) := by
  have hs := extends_buffer_size before middle he
  have hi := (allocate_success size storage middle after id ha).1
  constructor
  · omega
  · intro a h; omega

/-- The two public boundary allocations are fixed, fresh, and precede all scratch. -/
theorem boundary_allocations (inputSize outputSize : Nat) :
    ((do
      let src ← allocate inputSize
      let dst ← allocate outputSize
      pure (src,dst)) : BuildM (Nat × Nat)).run {} =
      .ok ((0,1), {buffers := #[⟨inputSize,.device,[]⟩,⟨outputSize,.device,[]⟩]}) := rfl

/-- Exact prefix construction of every public collective, independent of hierarchy depth. -/
def initialBuild (inputSize outputSize depth : Nat) : Build :=
  {buffers := #[⟨inputSize,.device,[]⟩,⟨outputSize,.device,[]⟩] ++
    (treeRows depth).toArray ++ (treeRows depth).toArray}

def initialTree (depth : Nat) : Trees := ⟨2,2+depth+1,depth⟩

theorem initial_allocations (inputSize outputSize depth : Nat) :
    ((do
      let src ← allocate inputSize
      let dst ← allocate outputSize
      let tree ← allocateTrees depth
      pure (src,dst,tree)) : BuildM (Nat × Nat × Trees)).run {} =
      .ok ((0,1,initialTree depth),initialBuild inputSize outputSize depth) := rfl

/-- The actual build action starts its recursive algorithm in this exact metadata state. -/
theorem buildAction_initial (op : ReduceOp) (shape : FoldShape) (depth : Nat) :
    (buildAction op shape depth).run {} =
      (match shape.mode with
       | none => reduceInto op (initialTree depth) (2^depth) 0 1 shape.segments
           (Nat.log2 (max 1 shape.inputLen)+2)
       | some mode => scanInto op mode (initialTree depth) (2^depth) 0 1 shape.segments
           (Nat.log2 (max 1 shape.inputLen)+2)).run
        (initialBuild shape.inputLen (if shape.mode.isSome then shape.inputLen else shape.segments.length) depth) := by
  rfl

/-- A shape-correct row update preserves the source memory representation. -/
theorem good_setRow (p : Program) (mem : Memory) (hg : Good p mem) (a : Nat)
    (ha : a < p.buffers.length) (row : Array Word) (hr : row.size = (buffer p a).size) :
    Good p (mem.setIfInBounds a row) := by
  have ham : a < mem.size := by rw [hg.1]; exact ha
  constructor
  · simpa using hg.1
  · intro b hb
    have hbm : b < mem.size := by rw [hg.1]; exact hb
    by_cases he : a = b
    · subst b
      simpa [Array.getD_eq_getD_getElem?,Array.getElem?_setIfInBounds,ham] using hr
    · simpa [Array.getD_eq_getD_getElem?,Array.getElem?_setIfInBounds,he] using hg.2 b hb

/-- Zero allocation has the exact declared dimensions, including arbitrary scratch sizes. -/
theorem zeroMemory_good (p : Program) :
    Good p (p.buffers.toArray.map fun b => Array.replicate b.size (0#64)) := by
  constructor
  · simp
  · intro a ha
    simp [buffer,Array.getD_eq_getD_getElem?,List.getD_eq_getElem?_getD,ha]

/-- Actual upload initialization is Good for a single shape-correct input and
nonconstant allocation metadata, the public collective builder's storage discipline. -/
theorem initMemory_single_good (p : Program) (input : Array Word)
    (hin : p.inputs = [0]) (hbuf : 0 < p.buffers.length)
    (hsize : input.size = (buffer p 0).size)
    (hn : ∀ b ∈ p.buffers, b.storage ≠ .constant) : Good p (initialMemory p [input]) := by
  have hmap : (p.buffers.toArray.map fun b =>
      if b.storage == .constant then b.values.toArray else Array.replicate b.size (0#64)) =
      p.buffers.toArray.map (fun b => Array.replicate b.size (0#64)) := by
    apply Array.map_congr_left
    intro b hb
    simp [hn b (by simpa using hb)]
  have hlist : p.buffers.map (fun b =>
      if b.storage = .constant then b.values.toArray else Array.replicate b.size (0#64)) =
      p.buffers.map (fun b => Array.replicate b.size (0#64)) := by
    apply List.map_congr_left
    intro b hb
    simp [hn b hb]
  simpa [initialMemory,hin,hmap,hlist] using
    good_setRow p _ (zeroMemory_good p) 0 hbuf input hsize

/-- Collective state allocates only mutable device/shared buffers. -/
def NoConstants (s : Build) : Prop := ∀ b ∈ s.buffers.toList, b.storage ≠ .constant

theorem allocate_noConstants (n : Nat) (before after : Build) (id : Nat)
    (h : (allocate n .device).run before = .ok (id,after)) (hn : NoConstants before) : NoConstants after := by
  obtain ⟨_,rfl⟩ := allocate_success n .device before after id h
  intro b hb
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hn b hb
  · simp

theorem localReduce_noConstants (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (before after : Build) (h : (localReduce op tree src dst cs).run before = .ok ((),after))
    (hn : NoConstants before) : NoConstants after := by
  rw [localReduce_success op tree src dst cs before after h]
  exact hn

theorem localScan_noConstants (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (seed : Option Nat) (before after : Build)
    (h : (localScan op mode tree src dst cs seed).run before = .ok ((),after))
    (hn : NoConstants before) : NoConstants after := by
  rw [localScan_success op mode tree src dst cs seed before after h]
  exact hn

theorem initialBuild_noConstants (inputSize outputSize depth : Nat) :
    NoConstants (initialBuild inputSize outputSize depth) := by
  intro b hb
  simp only [initialBuild,Array.toList_append,List.toList_toArray,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with ((rfl | rfl) | ht) | ht
  · simp
  · simp
  all_goals
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht
    simp

theorem reduceChunks_noConstants (op : ReduceOp) (tree : Trees) (tile src dst : Nat) (cs : List Chunk)
    (fuel : Nat) (before after : Build)
    (h : (reduceChunksInto op tree tile src dst cs fuel).run before = .ok ((),after))
    (hn : NoConstants before) : NoConstants after := by
  induction fuel generalizing src dst cs before after with
  | zero =>
    change (Except.error "collective reduction: insufficient hierarchy depth" : Except String (Unit × Build)) = .ok ((),after) at h
    cases h
  | succ fuel ih =>
    unfold reduceChunksInto at h
    obtain ⟨u,s0,hs,hrest⟩ := bind_success _ _ _ _ _ h
    cases u
    have hn0 := localReduce_noConstants op tree src dst _ before s0 hs hn
    split at hrest
    · obtain ⟨total,s1,ha,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨u,s2,hl,hr⟩ := bind_success _ _ _ _ _ hrest
      cases u
      exact ih total dst _ s2 after hr
        (localReduce_noConstants op tree src total _ s1 s2 hl (allocate_noConstants _ s0 s1 total ha hn0))
    · have he : s0 = after := congrArg Prod.snd (Except.ok.inj hrest)
      simpa [← he] using hn0

theorem scanChunks_noConstants (op : ReduceOp) (mode : ScanMode) (tree : Trees) (tile src dst : Nat)
    (cs : List Chunk) (fuel : Nat) (before after : Build)
    (h : (scanChunksInto op mode tree tile src dst cs fuel).run before = .ok ((),after))
    (hn : NoConstants before) : NoConstants after := by
  induction fuel generalizing mode src dst cs before after with
  | zero =>
    change (Except.error "collective scan: insufficient hierarchy depth" : Except String (Unit × Build)) = .ok ((),after) at h
    cases h
  | succ fuel ih =>
    unfold scanChunksInto at h
    obtain ⟨u,s0,hs,hrest⟩ := bind_success _ _ _ _ _ h
    cases u
    have hn0 := localScan_noConstants op mode tree src dst _ none before s0 hs hn
    split at hrest
    · obtain ⟨total,s1,ha,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨prefixes,s2,hb,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨u,s3,hl,hrest⟩ := bind_success _ _ _ _ _ hrest
      cases u
      obtain ⟨u,s4,hr,hrest⟩ := bind_success _ _ _ _ _ hrest
      cases u
      have hn1 := allocate_noConstants _ s0 s1 total ha hn0
      have hn2 := allocate_noConstants _ s1 s2 prefixes hb hn1
      have hn3 := localReduce_noConstants op tree src total _ s2 s3 hl hn2
      have hn4 := ih .exclusive total prefixes _ s3 s4 hr hn3
      exact localScan_noConstants op mode tree src dst _ (some prefixes) s4 after hrest hn4
    · have he : s0 = after := congrArg Prod.snd (Except.ok.inj hrest)
      simpa [← he] using hn0

end Obend.Hardware.Gpu.CollectiveBuildFacts
end
