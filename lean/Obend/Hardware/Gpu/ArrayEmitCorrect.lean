module
public import Obend.Hardware.Gpu.ArrayEmit
public import Obend.Hardware.Gpu.CollectiveArenaCorrect
@[expose] public section

/-! Receipts and composition for the actual semantic action compiler.
Receipts retain source construction, both admission checks, arena placement and
the exact generated action list. They do not contain an expected-output oracle.
-/
namespace Obend.Hardware.Gpu.ArrayEmitCorrect
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArrayEmit Obend.Hardware.Gpu.ArraySchedule
set_option autoImplicit false

/-- Pointwise receipt for a monadic list map, retaining the exact ordering. -/
inductive Aligned {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Aligned relation [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      relation a b → Aligned relation as bs → Aligned relation (a::as) (b::bs)

theorem Aligned.left_mem {α β : Type} {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Aligned r xs ys) (x : α) (hx : x ∈ xs) : ∃ y ∈ ys, r x y := by
  induction h with
  | nil => simp at hx
  | @cons a b as bs hab ht ih =>
    rcases List.mem_cons.mp hx with he | hm
    · subst x; exact ⟨b,by simp,hab⟩
    · obtain ⟨y,hy,hr⟩ := ih hm
      exact ⟨y,List.mem_cons_of_mem _ hy,hr⟩

/-- Generic ordered-state simulation used by the stage/action composition. -/
theorem Aligned.foldl_rel {α β σ τ : Type} {r : α → β → Prop}
    {xs : List α} {ys : List β} (h : Aligned r xs ys)
    (f : σ → α → σ) (g : τ → β → τ) (R : σ → τ → Prop)
    (step : ∀ x ∈ xs, ∀ y, r x y → ∀ s t, R s t → R (f s x) (g t y))
    (s : σ) (t : τ) (hst : R s t) : R (xs.foldl f s) (ys.foldl g t) := by
  induction h generalizing s t with
  | nil => exact hst
  | @cons a b as bs hab ht ih =>
    apply ih
    · intro x hx y hr s t hst
      exact step x (List.mem_cons_of_mem _ hx) y hr s t hst
    · exact step a (by simp) b hab s t hst

theorem except_bind_success {α β : Type} (first : Except String α)
    (next : α → Except String β) (value : β) (h : (first >>= next) = .ok value) :
    ∃ a, first = .ok a ∧ next a = .ok value := by
  cases first with
  | error err => simp [bind,Except.bind] at h
  | ok a => exact ⟨a,rfl,by simpa [bind,Except.bind] using h⟩

theorem mapM_success {α β : Type} (f : α → Except String β) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) : Aligned (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := by simpa [pure,Except.pure] using h.symm
    subst ys
    exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨y,hy,hrest⟩ := except_bind_success (f x) _ ys h
    obtain ⟨tail,ht,hyz⟩ := except_bind_success (xs.mapM f) _ ys hrest
    have he : ys = y::tail := by simpa [pure,Except.pure] using hyz.symm
    subst ys
    exact .cons hy (ih tail ht)

theorem compileKernel_ordinary (p : GpuProgram) (k : Kernel) (h : ordinary k = true) :
    compileKernel p k = .ok [] := by
  cases hb : k.body <;> simp [ordinary,hb] at h <;>
    simp [compileKernel,hb,pure,Except.pure]

/-- Every collective action carries the actual source build and admission
receipts needed by the collective theorem and arena simulation. -/
theorem compileKernel_fold_success (p : GpuProgram) (k : Kernel)
    (op : ReduceOp) (shape : FoldShape) (src : Nat) (hb : k.body = .fold op shape src)
    (actions : List Action) (h : compileKernel p k = .ok actions) :
    k.count = shape.outLen ∧ ∃ source block,
      CollectiveBlock.build op shape = .ok source ∧ source.check = .ok () ∧
      inArena source p.words src k.dstBase = .ok block ∧ block.check = .ok () ∧
      SourceProtocol.checkProgram block workgroupSize = true ∧ actions = [.collective block] := by
  by_cases hc : k.count = shape.outLen
  · refine ⟨hc,?_⟩
    simp only [compileKernel,hb] at h
    simp [hc,bind,Except.bind,pure,Except.pure] at h
    cases hs : CollectiveBlock.build op shape with
    | error err => simp [hs,bind,Except.bind] at h
    | ok source =>
      simp only [hs,bind,Except.bind] at h
      cases hsc : source.check with
      | error err => simp [hsc,bind,Except.bind] at h
      | ok unit =>
        cases unit
        simp only [hsc,bind,Except.bind] at h
        cases ha : inArena source p.words src k.dstBase with
        | error err => simp [ha,bind,Except.bind] at h
        | ok block =>
          simp only [ha,bind,Except.bind] at h
          cases hbc : block.check with
          | error err => simp [hbc,bind,Except.bind] at h
          | ok unit =>
            cases unit
            simp only [hbc,bind,Except.bind] at h
            by_cases hp : SourceProtocol.checkProgram block workgroupSize = true
            · exact ⟨source,block,rfl,hsc,ha,hbc,hp,
                by simpa [hp,pure,Except.pure,bind,Except.bind] using h.symm⟩
            · simp [hp,pure,Except.pure,bind,Except.bind] at h
  · simp [compileKernel,hb,hc,bind,Except.bind,pure,Except.pure] at h

theorem compileStage_success (p : GpuProgram) (stage : GpuStage) (index : Nat)
    (actions : List Action) (h : compileStage p stage index = .ok actions) :
    checkStage p.tables stage = true ∧ checkBounds p.words p.tables stage = true ∧
      ∃ folds, Aligned (fun k a => compileKernel p k = .ok a) stage.kernels folds ∧
        actions = ordinaryActions stage index ++ folds.flatten := by
  by_cases hs : checkStage p.tables stage = true
  · by_cases hb : checkBounds p.words p.tables stage = true
    · simp only [compileStage] at h
      simp [hs,hb,bind,Except.bind,pure,Except.pure] at h
      cases hm : stage.kernels.mapM (compileKernel p) with
      | error err => simp [hm] at h
      | ok folds =>
        refine ⟨hs,hb,folds,mapM_success _ _ _ hm,?_⟩
        simpa [hm] using h.symm
    · simp [compileStage,hs,hb,bind,Except.bind,pure,Except.pure] at h
  · simp [compileStage,hs,bind,Except.bind,pure,Except.pure] at h

theorem compileStages_success (p : GpuProgram) (stages : List (GpuStage × Nat))
    (actions : List Action) (h : compileStages p stages = .ok actions) :
    ∃ parts, Aligned (fun s a => compileStage p s.1 s.2 = .ok a) stages parts ∧
      actions = parts.flatten := by
  unfold compileStages at h
  obtain ⟨parts,hp,ha⟩ := except_bind_success _ _ actions h
  exact ⟨parts,mapM_success _ _ _ hp,by simpa [pure,Except.pure] using ha.symm⟩

theorem compile_boundaries (p : GpuProgram) (compiled : Schedule)
    (h : compile p = .ok compiled) : checkBoundaries p = true := by
  by_cases hb : checkBoundaries p = true
  · exact hb
  · simp [compile,hb,bind,Except.bind,pure,Except.pure] at h

theorem checkBoundaries_sound (p : GpuProgram) (h : checkBoundaries p = true)
    (w : Nat) (hw : w ∈ p.inputs ++ p.outputs) :
    w < p.wireBase.length ∧ w < p.wireLen.length ∧
      p.wireBase.getD w 0 + p.wireLen.getD w 0 ≤ p.words := by
  simp only [checkBoundaries,List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  have hv := h w hw
  exact ⟨hv.1.1,hv.1.2,hv.2⟩

theorem compile_success (p : GpuProgram) (compiled : Schedule) (h : compile p = .ok compiled) :
    ∃ parts, Aligned (fun s a => compileStage p s.1 s.2 = .ok a) p.stages.zipIdx parts ∧
      compiled.actions.toList = parts.flatten ∧ compiled.words = requiredWords p parts.flatten := by
  have hb := compile_boundaries p compiled h
  simp only [compile] at h
  simp [hb,bind,Except.bind,pure,Except.pure] at h
  obtain ⟨actions,ha,hc⟩ := except_bind_success _ _ compiled h
  obtain ⟨parts,hp,he⟩ := compileStages_success p _ actions ha
  have hs : compiled = ⟨requiredWords p actions,actions.toArray⟩ := by
    simpa [pure,Except.pure] using hc.symm
  subst compiled
  exact ⟨parts,hp,by simp [he],by simp [he]⟩

/-- Actual successful compilation certifies every source frontier's physical
read/write separation and its bounded live-memory footprint. -/
theorem compile_checks (p : GpuProgram) (compiled : Schedule) (h : compile p = .ok compiled)
    (stage : GpuStage) (hs : stage ∈ p.stages) :
    checkStage p.tables stage = true ∧ checkBounds p.words p.tables stage = true := by
  obtain ⟨parts,hp,_⟩ := compile_success p compiled h
  have hm : stage ∈ p.stages.zipIdx.map Prod.fst := by simpa [List.zipIdx_map_fst] using hs
  obtain ⟨si,hsi,he⟩ := List.mem_map.mp hm
  obtain ⟨actions,_,ha⟩ := hp.left_mem si hsi
  have hc := compileStage_success p si.1 si.2 actions ha
  rw [← he]
  exact ⟨hc.1,hc.2.1⟩

@[simp] theorem evalActions_nil (p : GpuProgram) (flat : BlockLower.FlatMemory) :
    evalActions p [] flat = flat := rfl

@[simp] theorem evalActions_cons (p : GpuProgram) (action : Action) (actions : List Action)
    (flat : BlockLower.FlatMemory) : evalActions p (action::actions) flat =
      evalActions p actions (action.eval p.consts p.tables flat) := rfl

theorem evalActions_append (p : GpuProgram) (as bs : List Action) (flat : BlockLower.FlatMemory) :
    evalActions p (as ++ bs) flat = evalActions p bs (evalActions p as flat) := by
  simp [evalActions,List.foldl_append]

theorem evalActions_flatten (p : GpuProgram) (parts : List (List Action)) (flat : BlockLower.FlatMemory) :
    evalActions p parts.flatten flat = parts.foldl (fun m actions => evalActions p actions m) flat := by
  induction parts generalizing flat with
  | nil => rfl
  | cons actions parts ih => simp only [List.flatten_cons,evalActions_append,List.foldl_cons,ih]

/-- Empty ordinary frontiers emit no action; their semantics is still exactly
the empty snapshot stage. Non-device memory is untouched in either case. -/
theorem ordinaryActions_device (p : GpuProgram) (stage : GpuStage) (index : Nat)
    (flat : BlockLower.FlatMemory) (a : Nat) :
    evalActions p (ordinaryActions stage index) flat (.device,a) =
      runStage p.consts p.tables (fun i => flat (.device,i)) ⟨stage.kernels.filter ordinary⟩ a := by
  unfold ordinaryActions
  dsimp only
  split
  · rename_i h
    have he : stage.kernels.filter ordinary = [] := List.isEmpty_iff.mp h
    simp [he,evalActions,runStage]
  · simp [evalActions,Action.eval]

theorem ordinaryActions_frame (p : GpuProgram) (stage : GpuStage) (index : Nat)
    (flat : BlockLower.FlatMemory) (address : BlockLower.Address) (h : address.1 ≠ .device) :
    evalActions p (ordinaryActions stage index) flat address = flat address := by
  unfold ordinaryActions
  dsimp only
  split <;> simp [evalActions,Action.eval,h]


/-- The source step corresponding to a post-frontier kernel action. -/
def foldStep (p : GpuProgram) (entry : Nat → Word) (k : Kernel) : Nat → Word :=
  if ordinary k then entry else runKernel p.consts p.tables entry k

theorem foldStep_foldl (p : GpuProgram) (ks : List Kernel) (entry : Nat → Word) :
    ks.foldl (foldStep p) entry =
      runSequential p.consts p.tables entry (ks.filter (fun k => !ordinary k)) := by
  unfold runSequential
  rw [List.foldl_filter]
  congr 1
  funext m k
  cases h : ordinary k <;> simp [foldStep,h]

theorem foldStep_agreeBelow (p : GpuProgram) (k : Kernel)
    (entry other : Nat → Word) (ha : AgreeBelow p.words entry other)
    (hb : KernelBounded p.words p.tables k) :
    AgreeBelow p.words (foldStep p entry k) (foldStep p other k) := by
  unfold foldStep
  split
  · exact ha
  · exact runStage_agreeBelow p.consts p.tables p.words entry other ⟨[k]⟩ ha
      (by intro x hx; simpa using (List.mem_singleton.mp hx ▸ hb))

/-- Ordered composition is independent of the representation of collective
scratch. Only the graph's bounded live allocation is related between steps. -/
theorem compiledKernels_simulation (p : GpuProgram) (ks : List Kernel)
    (parts : List (List Action))
    (hp : Aligned (fun k a => compileKernel p k = .ok a) ks parts)
    (hb : ∀ k ∈ ks, KernelBounded p.words p.tables k)
    (step : ∀ k ∈ ks, ∀ actions, compileKernel p k = .ok actions →
      ∀ flat, AgreeBelow p.words
        (fun a => evalActions p actions flat (.device,a))
        (foldStep p (fun a => flat (.device,a)) k))
    (flat : BlockLower.FlatMemory) (entry : Nat → Word)
    (he : AgreeBelow p.words (fun a => flat (.device,a)) entry) :
    AgreeBelow p.words (fun a => evalActions p parts.flatten flat (.device,a))
      (runSequential p.consts p.tables entry (ks.filter (fun k => !ordinary k))) := by
  rw [evalActions_flatten,←foldStep_foldl]
  apply hp.foldl_rel (foldStep p) (fun m actions => evalActions p actions m)
    (fun e m => AgreeBelow p.words (fun a => m (.device,a)) e)
  · intro k hk actions hc e m hm a ha
    exact (step k hk actions hc m a ha).trans
      (foldStep_agreeBelow p k _ e hm (hb k hk) a ha)
  · exact he


/-- Every concrete kernel expansion computes its fold and preserves every other
live graph word. All premises are receipts from the executable compiler. -/
theorem compileKernel_simulation (p : GpuProgram) (k : Kernel) (actions : List Action)
    (hc : compileKernel p k = .ok actions) (flat : BlockLower.FlatMemory) :
    AgreeBelow p.words (fun a => evalActions p actions flat (.device,a))
      (foldStep p (fun a => flat (.device,a)) k) := by
  by_cases ho : ordinary k = true
  · have he : actions = [] := Except.ok.inj (hc.symm.trans (compileKernel_ordinary p k ho))
    subst actions
    intro a _
    simp [foldStep,ho]
  · cases hb : k.body with
    | fold op shape src =>
      obtain ⟨hcount,source,block,hbuild,hsource,harena,hblock,_,hactions⟩ :=
        compileKernel_fold_success p k op shape src hb actions hc
      subst actions
      intro a ha
      simp only [evalActions,Action.eval,List.foldl_cons,List.foldl_nil,foldStep,ordinary,hb,
        Bool.false_eq_true,ite_false,runKernel_apply]
      by_cases hw : k.owns a = true
      · have hown : k.dstBase ≤ a ∧ a < k.dstBase+k.count := by
          simpa [Kernel.owns] using hw
        have hoff : a-k.dstBase < shape.outLen := by omega
        have hadd : k.dstBase+(a-k.dstBase) = a := by omega
        simpa [hw,kernelValue,hb,hadd] using
          CollectiveArenaCorrect.build_arena_value op shape 8 source block
            p.words src k.dstBase hbuild hsource harena hblock flat (a-k.dstBase) hoff
      · have hout : a < k.dstBase ∨ k.dstBase+shape.outLen ≤ a := by
          simp only [Kernel.owns,decide_eq_true_eq] at hw
          omega
        simpa [hw] using CollectiveArenaCorrect.build_arena_frame op shape 8 source block
          p.words src k.dstBase hbuild hsource harena hblock flat a ha hout
    | prog code => simp [ordinary,hb] at ho
    | gather ixb base => simp [ordinary,hb] at ho
    | concat b0 l0 b1 => simp [ordinary,hb] at ho
    | const cb => simp [ordinary,hb] at ho

private theorem compileStage_simulation_of_kernel (p : GpuProgram) (stage : GpuStage)
    (index : Nat) (actions : List Action) (hc : compileStage p stage index = .ok actions)
    (localSound : ∀ k ∈ stage.kernels, ∀ actions, compileKernel p k = .ok actions →
      ∀ flat, AgreeBelow p.words (fun a => evalActions p actions flat (.device,a))
        (foldStep p (fun a => flat (.device,a)) k))
    (flat : BlockLower.FlatMemory) :
    AgreeBelow p.words (fun a => evalActions p actions flat (.device,a))
      (runStage p.consts p.tables (fun a => flat (.device,a)) stage) := by
  obtain ⟨hs,hb,parts,hp,ha⟩ := compileStage_success p stage index actions hc
  rw [ha,evalActions_append]
  have h := compiledKernels_simulation p stage.kernels parts hp
    (checkBounds_sound p.words p.tables stage hb) localSound
    (evalActions p (ordinaryActions stage index) flat)
    (runStage p.consts p.tables (fun a => flat (.device,a)) ⟨stage.kernels.filter ordinary⟩)
    (by intro a _; exact ordinaryActions_device p stage index flat a)
  change AgreeBelow p.words _ (runOrdinaryThenFolds p.consts p.tables _ stage.kernels) at h
  rw [checked_ordinary_then_folds_eq_stage p.consts p.tables _ stage hs] at h
  exact h

private theorem compileStages_simulation_of_stage (p : GpuProgram)
    (stages : List (GpuStage × Nat)) (parts : List (List Action))
    (hp : Aligned (fun si actions => compileStage p si.1 si.2 = .ok actions) stages parts)
    (stageSound : ∀ si ∈ stages, ∀ actions, compileStage p si.1 si.2 = .ok actions →
      ∀ flat, AgreeBelow p.words (fun a => evalActions p actions flat (.device,a))
        (runStage p.consts p.tables (fun a => flat (.device,a)) si.1))
    (flat : BlockLower.FlatMemory) (entry : Nat → Word)
    (he : AgreeBelow p.words (fun a => flat (.device,a)) entry) :
    AgreeBelow p.words (fun a => evalActions p parts.flatten flat (.device,a))
      (runStages p.consts p.tables entry (stages.map Prod.fst)) := by
  rw [evalActions_flatten]
  simp only [runStages,List.foldl_map]
  apply hp.foldl_rel (fun e si => runStage p.consts p.tables e si.1)
    (fun m actions => evalActions p actions m)
    (fun e m => AgreeBelow p.words (fun a => m (.device,a)) e)
  · intro si hsi actions hc e m hm a ha
    have hb := (compileStage_success p si.1 si.2 actions hc).2.1
    exact (stageSound si hsi actions hc m a ha).trans
      (runStage_agreeBelow p.consts p.tables p.words _ e si.1 hm
        (checkBounds_sound p.words p.tables si.1 hb) a ha)
  · exact he


/-- The actual emitted action sequence refines each admitted source stage. -/
theorem compileStage_correct (p : GpuProgram) (stage : GpuStage) (index : Nat)
    (actions : List Action) (hc : compileStage p stage index = .ok actions)
    (flat : BlockLower.FlatMemory) :
    AgreeBelow p.words (fun a => evalActions p actions flat (.device,a))
      (runStage p.consts p.tables (fun a => flat (.device,a)) stage) := by
  exact compileStage_simulation_of_kernel p stage index actions hc
    (fun k _ actions hk m => compileKernel_simulation p k actions hk m) flat

/-- Successful executable compilation suffices: every live device word agrees
with the original snapshot-stage evaluator, for arbitrary initial flat storage. -/
theorem compile_correct (p : GpuProgram) (compiled : Schedule)
    (hc : compile p = .ok compiled) (flat : BlockLower.FlatMemory) :
    AgreeBelow p.words (fun a => evalActions p compiled.actions.toList flat (.device,a))
      (runStages p.consts p.tables (fun a => flat (.device,a)) p.stages) := by
  obtain ⟨parts,hp,ha,_⟩ := compile_success p compiled hc
  rw [ha]
  have h := compileStages_simulation_of_stage p p.stages.zipIdx parts hp
    (fun si _ actions hs m => compileStage_correct p si.1 si.2 actions hs m)
    flat (fun a => flat (.device,a)) (fun _ _ => rfl)
  simpa only [List.zipIdx_map_fst] using h

/-- Read the graph output boundaries after the exact semantic action list used
by text emission. -/
def compiledOutputs (p : GpuProgram) (compiled : Schedule) (flat : BlockLower.FlatMemory) : List Vec :=
  p.outputs.map fun w => (List.range (p.wireLen.getD w 0)).map fun e =>
    evalActions p compiled.actions.toList flat (.device,p.wireBase.getD w 0+e)

/-- End-to-end equality to the existing GPU graph evaluator. Successful compile
is the sole static premise; boundary validity is checked by that same compile. -/
theorem compile_runProgram (p : GpuProgram) (compiled : Schedule)
    (hc : compile p = .ok compiled) (flat : BlockLower.FlatMemory) :
    compiledOutputs p compiled flat = runProgram p (fun a => flat (.device,a)) := by
  unfold compiledOutputs runProgram
  apply List.map_congr_left
  intro w hw
  have hb := checkBoundaries_sound p (compile_boundaries p compiled hc) w
    (List.mem_append_right _ hw)
  apply List.map_congr_left
  intro e he
  have he' : e < p.wireLen.getD w 0 := List.mem_range.mp he
  exact compile_correct p compiled hc flat _ (by omega)

end Obend.Hardware.Gpu.ArrayEmitCorrect
end
