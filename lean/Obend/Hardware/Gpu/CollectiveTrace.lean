module
public import Obend.Hardware.Gpu.CollectiveBlock
public import Obend.Hardware.Gpu.BlockLower
@[expose] public section

/-! Builder traces and source execution composition for GPU collectives.
These lemmas describe the actual StateT builder and ArrayKernel evaluator. They
do not assume a scan/reduction result. Allocation changes metadata only: the
execution proof can use memory for the final program throughout the trace.
-/
namespace Obend.Hardware.Gpu.CollectiveTrace
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

def toProgram (s : Build) (inputs outputs : List Nat := []) : Program :=
  ⟨s.buffers.toList, inputs, outputs, s.dispatches.toList⟩

def evalTrace (ds : List Dispatch) (mem : Memory) : Memory :=
  ds.foldl (fun m d => evalDispatch d m) mem

def evalTail (before after : Build) (mem : Memory) : Memory :=
  evalTrace (after.dispatches.toList.drop before.dispatches.size) mem

def Extends (before after : Build) : Prop :=
  (∃ bs, after.buffers.toList = before.buffers.toList ++ bs) ∧
  (∃ ds, after.dispatches.toList = before.dispatches.toList ++ ds)

def appendTrace (s : Build) (ds : List Dispatch) : Build :=
  {s with dispatches := s.dispatches ++ ds.toArray}

@[simp] theorem appendTrace_nil (s : Build) : appendTrace s [] = s := by
  simp [appendTrace]

theorem appendTrace_append (s : Build) (as bs : List Dispatch) :
    appendTrace (appendTrace s as) bs = appendTrace s (as ++ bs) := by
  simp [appendTrace, Array.append_assoc]

theorem appendTrace_extends (s : Build) (ds : List Dispatch) : Extends s (appendTrace s ds) := by
  exact ⟨⟨[],by simp [appendTrace]⟩,⟨ds,by simp [appendTrace]⟩⟩

theorem extends_refl (s : Build) : Extends s s :=
  ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem extends_trans (a b c : Build) (hab : Extends a b) (hbc : Extends b c) :
    Extends a c := by
  obtain ⟨⟨bs, hbs⟩, ⟨ds, hds⟩⟩ := hab
  obtain ⟨⟨cs, hcs⟩, ⟨es, hes⟩⟩ := hbc
  exact ⟨⟨bs ++ cs, by simp [hcs, hbs, List.append_assoc]⟩,
    ⟨ds ++ es, by simp [hes, hds, List.append_assoc]⟩⟩

@[simp] theorem evalTrace_nil (mem : Memory) : evalTrace [] mem = mem := rfl

@[simp] theorem evalTrace_cons (d : Dispatch) (ds : List Dispatch) (mem : Memory) :
    evalTrace (d::ds) mem = evalTrace ds (evalDispatch d mem) := rfl

theorem evalTrace_append (as bs : List Dispatch) (mem : Memory) :
    evalTrace (as ++ bs) mem = evalTrace bs (evalTrace as mem) := by
  simp [evalTrace, List.foldl_append]

theorem evalTrace_flatMap {α : Type} (xs : List α) (f : α → List Dispatch) (mem : Memory) :
    evalTrace (xs.flatMap f) mem = xs.foldl (fun m x => evalTrace (f x) m) mem := by
  induction xs generalizing mem with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, evalTrace_append, List.foldl_cons, ih]

theorem evalTail_of_append (before after : Build) (ds : List Dispatch)
    (h : after.dispatches.toList = before.dispatches.toList ++ ds) (mem : Memory) :
    evalTail before after mem = evalTrace ds mem := by
  simp [evalTail, h, ← Array.length_toList, List.drop_append_length]

@[simp] theorem evalTail_refl (s : Build) (mem : Memory) : evalTail s s mem = mem := by
  simp [evalTail, evalTrace, ← Array.length_toList]

theorem evalTail_trans (a b c : Build) (hab : Extends a b) (hbc : Extends b c)
    (mem : Memory) : evalTail a c mem = evalTail b c (evalTail a b mem) := by
  obtain ⟨ds, hds⟩ := hab.2
  obtain ⟨es, hes⟩ := hbc.2
  have hac : c.dispatches.toList = a.dispatches.toList ++ (ds ++ es) := by
    simp [hes, hds, List.append_assoc]
  rw [evalTail_of_append _ _ _ hac, evalTail_of_append _ _ _ hes,
    evalTail_of_append _ _ _ hds, evalTrace_append]

theorem evalProgram_append (p : Program) (ds : List Dispatch) (mem : Memory) :
    evalProgram {p with dispatches := p.dispatches ++ ds} mem =
      evalTrace ds (evalProgram p mem) := by
  simp [evalProgram, evalTrace, List.foldl_append]

@[simp] theorem evalTail_empty (s : Build) (mem : Memory) (ins outs : List Nat) :
    evalTail {} s mem = evalProgram (toProgram s ins outs) mem := rfl

theorem evalDispatch_good (p : Program) (d : Dispatch) (mem : Memory)
    (hg : Good p mem) : Good p (evalDispatch d mem) := by
  unfold evalDispatch
  induction List.range d.groups generalizing mem with
  | nil => exact hg
  | cons g gs ih => exact ih _ (evalGroup_good p d g mem hg)

theorem evalTrace_good (p : Program) (ds : List Dispatch) (mem : Memory)
    (hg : Good p mem) : Good p (evalTrace ds mem) := by
  induction ds generalizing mem with
  | nil => exact hg
  | cons d ds ih => exact ih _ (evalDispatch_good p d mem hg)

theorem evalTail_good (p : Program) (before after : Build) (mem : Memory)
    (hg : Good p mem) : Good p (evalTail before after mem) :=
  evalTrace_good p _ mem hg

@[simp] theorem allocate_run (size : Nat) (storage : Storage) (s : Build) :
    (allocate size storage).run s =
      .ok (s.buffers.size, {s with buffers := s.buffers.push ⟨size,storage,[]⟩}) := rfl

theorem allocate_extends (size : Nat) (storage : Storage) (s : Build) :
    Extends s {s with buffers := s.buffers.push ⟨size,storage,[]⟩} := by
  exact ⟨⟨[⟨size,storage,[]⟩], by simp⟩, ⟨[], by simp⟩⟩

@[simp] theorem allocate_evalTail (size : Nat) (storage : Storage) (s : Build) (mem : Memory) :
    evalTail s {s with buffers := s.buffers.push ⟨size,storage,[]⟩} mem = mem := by
  simp [evalTail, evalTrace, ← Array.length_toList]

theorem allocate_success (size : Nat) (storage : Storage) (before after : Build) (id : Nat)
    (h : (allocate size storage).run before = .ok (id, after)) :
    id = before.buffers.size ∧
      after = {before with buffers := before.buffers.push ⟨size,storage,[]⟩} := by
  simpa using h.symm

theorem emit_run (groups : Nat) (phases : List Phase) (s : Build) :
    (emit groups phases).run s = .ok ((),
      if groups > 0 && !phases.isEmpty then
        {s with dispatches := s.dispatches.push ⟨groups,phases⟩} else s) := by
  unfold emit
  split <;> rfl

theorem emit_extends (groups : Nat) (phases : List Phase) (before after : Build)
    (h : (emit groups phases).run before = .ok ((), after)) : Extends before after := by
  rw [emit_run] at h
  split at h
  · cases h
    exact ⟨⟨[], by simp⟩, ⟨[⟨groups,phases⟩], by simp⟩⟩
  · cases h
    exact extends_refl before

theorem emit_evalTail (groups : Nat) (phases : List Phase) (before after : Build)
    (h : (emit groups phases).run before = .ok ((), after)) (mem : Memory) :
    evalTail before after mem =
      if groups > 0 && !phases.isEmpty then evalDispatch ⟨groups,phases⟩ mem else mem := by
  rw [emit_run] at h
  split at h
  · rename_i hc
    cases h
    simp [hc, evalTail, Array.toList_push, ← Array.length_toList, evalTrace]
  · rename_i hc
    cases h
    simp [hc]

@[simp] theorem pure_run {α : Type} (value : α) (s : Build) :
    (pure value : BuildM α).run s = .ok (value,s) := rfl

theorem bind_run {α β : Type} (first : BuildM α) (next : α → BuildM β) (s : Build) :
    (first >>= next).run s = (first.run s >>= fun (a,t) => (next a).run t) := by
  simp [StateT.run, bind, StateT.bind]

def emitted (groups : Nat) (phases : List Phase) : List Dispatch :=
  if groups > 0 && !phases.isEmpty then [⟨groups,phases⟩] else []

theorem evalTrace_emitted (groups : Nat) (phases : List Phase) (mem : Memory) :
    evalTrace (emitted groups phases) mem = evalDispatch ⟨groups,phases⟩ mem := by
  by_cases hg : groups = 0
  · subst groups; simp [emitted, evalTrace, evalDispatch]
  · by_cases hp : phases = []
    · subst phases
      simp only [emitted, List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        if_false, evalTrace_nil, evalDispatch, evalGroup, List.foldl_nil]
      induction List.range groups with
      | nil => rfl
      | cons x xs ih => exact ih
    · have hpos : groups > 0 := by omega
      simp [emitted, hpos, hp, evalTrace]

theorem emit_run_append (groups : Nat) (phases : List Phase) (s : Build) :
    (emit groups phases).run s = .ok ((),appendTrace s (emitted groups phases)) := by
  rw [emit_run]
  unfold emitted
  split <;> simp [appendTrace]

/-- Fold a list of builder steps whose only effect is their explicit emitted
dispatch list. This is the for-in loop used by both local collective builders. -/
theorem forIn_trace_run {α : Type} (xs : List α)
    (step : α → Unit → BuildM (ForInStep Unit)) (trace : α → List Dispatch)
    (hstep : ∀ a s, (step a ()).run s = .ok (.yield (),appendTrace s (trace a))) (s : Build) :
    (forIn xs () step : BuildM Unit).run s = .ok ((),appendTrace s (xs.flatMap trace)) := by
  induction xs generalizing s with
  | nil => simp only [List.forIn_nil, List.flatMap_nil, appendTrace_nil]; rfl
  | cons a xs ih =>
    rw [List.forIn_cons, bind_run, hstep]
    simp only [bind, Except.bind]
    rw [ih, appendTrace_append]
    rfl

def reduceDispatches (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk) : List Dispatch :=
  (buckets cs).flatMap fun (valid,bucket) =>
    emitted bucket.length (reducePhases op tree src dst valid (tileDepth valid)
      (descriptor bucket (·.start)) (descriptor bucket (·.result)))

def scanDispatches (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (prefixBuffer : Option Nat) : List Dispatch :=
  (buckets cs).flatMap fun (valid,bucket) =>
    if valid > 0 then
      emitted bucket.length (scanPhases op mode tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (prefixBuffer.map fun a => (a,descriptor bucket (·.result))))
    else []

theorem localReduce_run (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk) (s : Build) :
    (localReduce op tree src dst cs).run s =
      .ok ((),appendTrace s (reduceDispatches op tree src dst cs)) := by
  unfold localReduce
  rw [bind_run, forIn_trace_run (trace := fun (valid,bucket) =>
    emitted bucket.length (reducePhases op tree src dst valid (tileDepth valid)
      (descriptor bucket (·.start)) (descriptor bucket (·.result))))]
  · rfl
  · intro a before
    rcases a with ⟨valid,bucket⟩
    rw [bind_run, emit_run_append]
    rfl

theorem localScan_run (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (prefixBuffer : Option Nat) (s : Build) :
    (localScan op mode tree src dst cs prefixBuffer).run s =
      .ok ((),appendTrace s (scanDispatches op mode tree src dst cs prefixBuffer)) := by
  unfold localScan
  rw [bind_run, forIn_trace_run (trace := fun (valid,bucket) =>
    if valid > 0 then
      emitted bucket.length (scanPhases op mode tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (prefixBuffer.map fun a => (a,descriptor bucket (·.result))))
    else [])]
  · rfl
  · intro a before
    rcases a with ⟨valid,bucket⟩
    dsimp only
    by_cases hv : valid > 0
    · simp only [if_pos hv]
      rw [bind_run, emit_run_append]; rfl
    · simp [hv, pure, StateT.pure, StateT.run, Except.pure]

theorem localReduce_success (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (before after : Build) (h : (localReduce op tree src dst cs).run before = .ok ((),after)) :
    after = appendTrace before (reduceDispatches op tree src dst cs) := by
  simpa only [localReduce_run, Except.ok.injEq, Prod.mk.injEq, true_and] using h.symm

theorem localScan_success (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (prefixBuffer : Option Nat) (before after : Build)
    (h : (localScan op mode tree src dst cs prefixBuffer).run before = .ok ((),after)) :
    after = appendTrace before (scanDispatches op mode tree src dst cs prefixBuffer) := by
  simpa only [localScan_run, Except.ok.injEq, Prod.mk.injEq, true_and] using h.symm

theorem localReduce_evalTail (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (before after : Build) (h : (localReduce op tree src dst cs).run before = .ok ((),after))
    (mem : Memory) : evalTail before after mem = evalTrace (reduceDispatches op tree src dst cs) mem := by
  rw [localReduce_success op tree src dst cs before after h]
  apply evalTail_of_append
  simp [appendTrace]

theorem localScan_evalTail (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (prefixBuffer : Option Nat) (before after : Build)
    (h : (localScan op mode tree src dst cs prefixBuffer).run before = .ok ((),after))
    (mem : Memory) : evalTail before after mem = evalTrace (scanDispatches op mode tree src dst cs prefixBuffer) mem := by
  rw [localScan_success op mode tree src dst cs prefixBuffer before after h]
  apply evalTail_of_append
  simp [appendTrace]

theorem bind_success {α β : Type} (first : BuildM α) (next : α → BuildM β)
    (before after : Build) (value : β)
    (h : (first >>= next).run before = .ok (value, after)) :
    ∃ a middle, first.run before = .ok (a, middle) ∧
      (next a).run middle = .ok (value, after) := by
  cases hf : first.run before with
  | error err =>
    change first before = .error err at hf
    simp [StateT.run, bind, StateT.bind, Except.bind, hf] at h
  | ok result =>
    rcases result with ⟨a, middle⟩
    change first before = .ok (a,middle) at hf
    exact ⟨a, middle, rfl, by simpa [StateT.run, bind, StateT.bind, Except.bind, hf] using h⟩

/-- Any two append-only builder actions compose as their actual emitted traces.
The hypotheses are metadata preservation, not output correctness. -/
theorem bind_evalTail {α β : Type} (first : BuildM α) (next : α → BuildM β)
    (before after : Build) (value : β)
    (h : (first >>= next).run before = .ok (value, after))
    (hfirst : ∀ a s, first.run before = .ok (a,s) → Extends before s)
    (hnext : ∀ a s t b, (next a).run s = .ok (b,t) → Extends s t) (mem : Memory) :
    ∃ a middle, first.run before = .ok (a,middle) ∧
      (next a).run middle = .ok (value,after) ∧
      Extends before after ∧
      evalTail before after mem = evalTail middle after (evalTail before middle mem) := by
  obtain ⟨a,middle,ha,hb⟩ := bind_success first next before after value h
  have h1 := hfirst a middle ha
  have h2 := hnext a middle after value hb
  exact ⟨a,middle,ha,hb,extends_trans _ _ _ h1 h2,evalTail_trans _ _ _ h1 h2 mem⟩

theorem extends_buffer (before after : Build) (h : Extends before after)
    (a : Nat) (ha : a < before.buffers.size) :
    after.buffers.toList.getD a default = before.buffers.toList.getD a default := by
  obtain ⟨bs,hbs⟩ := h.1
  rw [hbs]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha]

theorem extends_buffer_size (before after : Build) (h : Extends before after) :
    before.buffers.size ≤ after.buffers.size := by
  obtain ⟨bs,hbs⟩ := h.1
  have := congrArg List.length hbs
  simp only [List.length_append, Array.length_toList] at this
  omega

theorem extends_valid (before after : Build) (h : Extends before after)
    (a i : Nat) (hv : Valid (toProgram before) a i) : Valid (toProgram after) a i := by
  have hs := extends_buffer_size before after h
  have ha : a < before.buffers.size := hv.1
  constructor
  · simpa [toProgram] using Nat.lt_of_lt_of_le ha hs
  · change i < (after.buffers.toList.getD a default).size
    rw [extends_buffer before after h a ha]
    exact hv.2

theorem memory_push_preserves (mem : Memory) (row : Array Word) (a : Nat)
    (ha : a < mem.size) : (mem.push row).getD a #[] = mem.getD a #[] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt ha,
    Array.getElem?_eq_getElem ha]

/-- Extending a metadata buffer list and its matching memory preserves Good.
Execution may instead allocate all rows up front and use evalTail_good. -/
theorem good_push (p : Program) (mem : Memory) (b : Buffer) (row : Array Word)
    (hg : Good p mem) (hrow : row.size = b.size) :
    Good {p with buffers := p.buffers ++ [b]} (mem.push row) := by
  constructor
  · simp [hg.1]
  · intro a ha
    change a < (p.buffers ++ [b]).length at ha
    by_cases hold : a < p.buffers.length
    · have hm : a < mem.size := by rw [hg.1]; exact hold
      rw [memory_push_preserves mem row a hm, hg.2 a hold]
      simp only [buffer, List.getD_eq_getElem?_getD, List.getElem?_append_left hold]
    · have he : a = p.buffers.length := by simp only [List.length_append, List.length_singleton] at ha; omega
      subst a
      have hnew : (mem.push row).getD p.buffers.length #[] = row := by
        rw [← hg.1]
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
      rw [hnew, hrow]
      simp [buffer, List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- Descriptors depend only on their immutable table and group id; buffer
allocation and preceding execution cannot alter the selected chunk reference. -/
@[simp] theorem descriptor_eval (cs : List Chunk) (f : Chunk → Nat) (g l : Nat) :
    (descriptor cs f).eval g l = ((cs.toArray.map f)[g]?).getD 0 := rfl

theorem descriptor_eval_member (cs : List Chunk) (f : Chunk → Nat) (g l : Nat)
    (hg : g < cs.length) : (descriptor cs f).eval g l = f cs[g] := by
  simp [descriptor, Ix.eval, hg]

theorem buckets_complete (cs : List Chunk) (c : Chunk) (hc : c ∈ cs) :
    (c.length,cs.filter (·.length == c.length)) ∈ buckets cs := by
  apply List.mem_map.mpr
  refine ⟨c.length, ?_, rfl⟩
  simp only [List.mem_eraseDups]
  exact List.mem_map.mpr ⟨c,hc,rfl⟩

theorem bucket_member (cs bucket : List Chunk) (valid : Nat)
    (hb : (valid,bucket) ∈ buckets cs) (c : Chunk) (hc : c ∈ bucket) :
    c ∈ cs ∧ c.length = valid := by
  obtain ⟨n,_,he⟩ := List.mem_map.mp hb
  cases he
  simpa using List.mem_filter.mp hc

/-- Name the exact action embedded in `CollectiveBlock.build`; the following
equality connects this spelling to the executable builder definition. -/
def buildAction (op : ReduceOp) (shape : FoldShape) (tileLog : Nat) : BuildM Unit := do
  let src ← allocate shape.inputLen
  let dst ← allocate (if shape.mode.isSome then shape.inputLen else shape.segments.length)
  let tree ← allocateTrees tileLog
  let fuel := Nat.log2 (max 1 shape.inputLen)+2
  match shape.mode with
  | none => reduceInto op tree (2^tileLog) src dst shape.segments fuel
  | some mode => scanInto op mode tree (2^tileLog) src dst shape.segments fuel

theorem build_eq_action (op : ReduceOp) (shape : FoldShape) (tileLog : Nat)
    (ht : 1 ≤ tileLog ∧ tileLog ≤ 8) :
    build op shape tileLog = (do
      let (_,state) ← (buildAction op shape tileLog).run {}
      pure (toProgram state [0] [1])) := by
  simp [build, buildAction, toProgram, ht.1, ht.2,
    bind, Except.bind, pure, Except.pure] <;> rfl

theorem build_success (op : ReduceOp) (shape : FoldShape) (tileLog : Nat) (p : Program)
    (ht : 1 ≤ tileLog ∧ tileLog ≤ 8) (h : build op shape tileLog = .ok p) :
    ∃ state, (buildAction op shape tileLog).run {} = .ok ((),state) ∧
      p = toProgram state [0] [1] := by
  rw [build_eq_action op shape tileLog ht] at h
  cases hr : (buildAction op shape tileLog).run {} with
  | error err => simp [hr, bind, Except.bind] at h
  | ok result =>
    rcases result with ⟨u,state⟩
    cases u
    exact ⟨state,rfl,by simpa [hr, bind, Except.bind, pure, Except.pure] using h.symm⟩

theorem build_success_eval (op : ReduceOp) (shape : FoldShape) (tileLog : Nat) (p : Program)
    (ht : 1 ≤ tileLog ∧ tileLog ≤ 8) (h : build op shape tileLog = .ok p) (mem : Memory) :
    ∃ state, (buildAction op shape tileLog).run {} = .ok ((),state) ∧
      p.buffers = state.buffers.toList ∧ p.dispatches = state.dispatches.toList ∧
      evalProgram p mem = evalTail {} state mem := by
  obtain ⟨state,hs,rfl⟩ := build_success op shape tileLog p ht h
  exact ⟨state,hs,rfl,rfl,rfl⟩

end Obend.Hardware.Gpu.CollectiveTrace
end
