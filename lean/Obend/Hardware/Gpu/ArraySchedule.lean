module
public import Obend.Hardware.Gpu
@[expose] public section

/-! Structural serialization of an array frontier. Every premise describes
declared physical reads/writes, never the values produced by a collective.
Distinct kernels may be serialized only when preceding writes preserve later
reads. A kernel may still read its own output range elementwise: each singleton
stage retains snapshot semantics internally.
-/
namespace Obend.Hardware.Gpu.ArraySchedule
open Obend.Hardware.ArrayHypergraph
set_option autoImplicit false

/-- Exact physical read footprint, including arbitrary gather indices. Fold
footprints conservatively include the whole declared input, including empty
segments; no value-dependent reads occur in the kernel language. -/
def KernelReads (ix : List Nat) (k : Kernel) (a : Nat) : Prop :=
  match k.body with
  | .prog code _ => ∃ ins ∈ code, ∃ base, .read base ∈ ins.args ∧
      ∃ e < k.count, a = base+e
  | .gather ixb base => ∃ e < k.count, a = base+ix.getD (ixb+e) 0
  | .concat base len other => ∃ e < k.count,
      (e < len ∧ a = base+e) ∨ (¬e < len ∧ a = other+(e-len))
  | .const _ => False
  | .fold _ shape base => ∃ i < shape.inputLen, a = base+i

def ReadWriteSeparated (ix : List Nat) (writer reader : Kernel) : Prop :=
  ∀ a, writer.owns a = true → ¬KernelReads ix reader a

def WritesSeparated (a b : Kernel) : Prop :=
  ∀ address, a.owns address = true → b.owns address = true → False

def Independent (ix : List Nat) (a b : Kernel) : Prop :=
  WritesSeparated a b ∧ ReadWriteSeparated ix a b ∧ ReadWriteSeparated ix b a

theorem independent_symm (ix : List Nat) (a b : Kernel) (h : Independent ix a b) :
    Independent ix b a := ⟨fun x hx hy => h.1 x hy hx,h.2.2,h.2.1⟩

abbrev Interval := Nat × Nat

def InInterval (range : Interval) (a : Nat) : Prop := range.1 ≤ a ∧ a < range.1+range.2

def maxIndex : List Nat → Nat
  | [] => 0
  | n::ns => max n (maxIndex ns)

theorem getD_le_maxIndex (xs : List Nat) (i : Nat) : xs.getD i 0 ≤ maxIndex xs := by
  induction xs generalizing i with
  | nil => simp [maxIndex]
  | cons x xs ih =>
    cases i with
    | zero => exact Nat.le_max_left _ _
    | succ i => exact Nat.le_trans (ih i) (Nat.le_max_right _ _)

def gatherExtent (ix : List Nat) (base count : Nat) : Nat :=
  if count == 0 then 0 else maxIndex ((ix.drop base).take count)+1

theorem gatherIndex_bound (ix : List Nat) (base count e : Nat) (he : e < count) :
    ix.getD (base+e) 0 < gatherExtent ix base count := by
  have heq : ((ix.drop base).take count).getD e 0 = ix.getD (base+e) 0 := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_take,he,List.getElem?_drop]
  have hm := getD_le_maxIndex ((ix.drop base).take count) e
  rw [heq] at hm
  have hc : count ≠ 0 := by omega
  simpa [gatherExtent,hc,List.getD_eq_getElem?_getD] using Nat.lt_succ_of_le hm

/-- Compact read ranges. A gather visits only its own immutable index slice;
folds require one interval regardless of their input length. -/
def readIntervals (ix : List Nat) (k : Kernel) : List Interval :=
  match k.body with
  | .prog code _ => code.flatMap fun ins => ins.args.filterMap fun arg =>
      match arg with
      | .read base => some (base,k.count)
      | _ => none
  | .gather ixb base => [(base,gatherExtent ix ixb k.count)]
  | .concat base len other => [(base,min len k.count),(other,k.count-len)]
  | .const _ => []
  | .fold _ shape base => [(base,shape.inputLen)]

theorem kernelReads_covered (ix : List Nat) (k : Kernel) (a : Nat)
    (h : KernelReads ix k a) : ∃ range ∈ readIntervals ix k, InInterval range a := by
  cases hb : k.body with
  | prog code out =>
    simp only [KernelReads,hb] at h
    obtain ⟨ins,hi,base,hr,e,he,rfl⟩ := h
    refine ⟨(base,k.count),?_,by simp [InInterval]; omega⟩
    simp only [readIntervals,hb]
    exact List.mem_flatMap.mpr ⟨ins,hi,List.mem_filterMap.mpr ⟨.read base,hr,rfl⟩⟩
  | gather ixb base =>
    simp only [KernelReads,hb] at h
    obtain ⟨e,he,rfl⟩ := h
    refine ⟨(base,gatherExtent ix ixb k.count),by simp [readIntervals,hb],?_⟩
    have := gatherIndex_bound ix ixb k.count e he
    simp only [InInterval]
    omega
  | concat base len other =>
    simp only [KernelReads,hb] at h
    obtain ⟨e,he,hr⟩ := h
    rcases hr with ⟨hl,rfl⟩ | ⟨hl,rfl⟩
    · refine ⟨(base,min len k.count),by simp [readIntervals,hb],?_⟩
      simp only [InInterval]
      omega
    · refine ⟨(other,k.count-len),by simp [readIntervals,hb],?_⟩
      simp only [InInterval]
      omega
  | const base => simp [KernelReads,hb] at h
  | fold op shape base =>
    simp only [KernelReads,hb] at h
    obtain ⟨i,hi,rfl⟩ := h
    exact ⟨(base,shape.inputLen),by simp [readIntervals,hb],by simp [InInterval]; omega⟩

def intervalSeparated (a b : Interval) : Bool :=
  a.2 == 0 || b.2 == 0 || a.1+a.2 ≤ b.1 || b.1+b.2 ≤ a.1

theorem intervalSeparated_sound (a b : Interval) (h : intervalSeparated a b = true)
    (x : Nat) (ha : InInterval a x) (hb : InInterval b x) : False := by
  simp only [intervalSeparated,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  unfold InInterval at ha hb
  omega

def checkIndependent (ix : List Nat) (a b : Kernel) : Bool :=
  intervalSeparated (a.dstBase,a.count) (b.dstBase,b.count) &&
    (readIntervals ix b).all (intervalSeparated (a.dstBase,a.count)) &&
    (readIntervals ix a).all (intervalSeparated (b.dstBase,b.count))

theorem checkIndependent_sound (ix : List Nat) (a b : Kernel)
    (h : checkIndependent ix a b = true) : Independent ix a b := by
  simp only [checkIndependent,Bool.and_eq_true,List.all_eq_true] at h
  refine ⟨?_,?_,?_⟩
  · intro x ha hb
    exact intervalSeparated_sound _ _ h.1.1 x
      (by simpa [InInterval,Kernel.owns] using ha)
      (by simpa [InInterval,Kernel.owns] using hb)
  · intro x ha hr
    obtain ⟨range,hm,hx⟩ := kernelReads_covered ix b x hr
    exact intervalSeparated_sound _ _ (h.1.2 range hm) x
      (by simpa [InInterval,Kernel.owns] using ha) hx
  · intro x hb hr
    obtain ⟨range,hm,hx⟩ := kernelReads_covered ix a x hr
    exact intervalSeparated_sound _ _ (h.2 range hm) x
      (by simpa [InInterval,Kernel.owns] using hb) hx

def checkKernels (ix : List Nat) : List Kernel → Bool
  | [] => true
  | k::ks => ks.all (checkIndependent ix k) && checkKernels ix ks

theorem checkKernels_sound (ix : List Nat) (ks : List Kernel)
    (h : checkKernels ix ks = true) : ks.Pairwise (Independent ix) := by
  induction ks with
  | nil => exact .nil
  | cons k ks ih =>
    simp only [checkKernels,Bool.and_eq_true,List.all_eq_true] at h
    exact List.pairwise_cons.mpr ⟨fun r hr => checkIndependent_sound ix k r (h.1 r hr),ih h.2⟩

/-- Value-independent admission for the actual ordinary-then-collectives
schedule. It permits each kernel's self-aliasing and checks only other kernels. -/
def checkStage (ix : List Nat) (stage : GpuStage) : Bool := checkKernels ix stage.kernels

theorem checkStage_sound (ix : List Nat) (stage : GpuStage) (h : checkStage ix stage = true) :
    stage.kernels.Pairwise (Independent ix) := checkKernels_sound ix stage.kernels h

def KernelBounded (words : Nat) (ix : List Nat) (k : Kernel) : Prop :=
  k.dstBase+k.count ≤ words ∧ ∀ a, KernelReads ix k a → a < words

def checkBounds (words : Nat) (ix : List Nat) (stage : GpuStage) : Bool :=
  stage.kernels.all fun k => k.dstBase+k.count ≤ words &&
    (readIntervals ix k).all (fun range => range.1+range.2 ≤ words)

theorem checkBounds_sound (words : Nat) (ix : List Nat) (stage : GpuStage)
    (h : checkBounds words ix stage = true) (k : Kernel) (hk : k ∈ stage.kernels) :
    KernelBounded words ix k := by
  simp only [checkBounds,List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨hw,hr⟩ := h k hk
  refine ⟨hw,?_⟩
  intro a ha
  obtain ⟨range,hm,hx⟩ := kernelReads_covered ix k a ha
  have hb := hr range hm
  unfold InInterval at hx
  omega

def AgreeBelow (words : Nat) (a b : Nat → Word) : Prop := ∀ i < words, a i = b i

theorem runKCode_congr (c : List Word) (entry other : Nat → Word) (e : Nat)
    (loc : Nat → Word) (code : List KInstr)
    (h : ∀ ins ∈ code, ∀ base, .read base ∈ ins.args → entry (base+e) = other (base+e)) :
    runKCode c entry e loc code = runKCode c other e loc code := by
  induction code generalizing loc with
  | nil => rfl
  | cons ins code ih =>
    have ha : ins.args.map (readOperand c entry e loc) = ins.args.map (readOperand c other e loc) := by
      apply List.map_congr_left
      intro arg harg
      cases arg with
      | read base => exact h ins (by simp) base harg
      | cst i => rfl
      | tmp w => rfl
    have hs : stepKInstr c entry e loc ins = stepKInstr c other e loc ins := by
      unfold stepKInstr
      rw [ha]
    simp only [runKCode, List.foldl_cons]
    rw [hs]
    exact ih _ (fun i hi b hb => h i (by simp [hi]) b hb)

theorem kernelValue_congr (c : List Word) (ix : List Nat) (entry other : Nat → Word)
    (k : Kernel) (e : Nat) (he : e < k.count)
    (h : ∀ a, KernelReads ix k a → entry a = other a) :
    kernelValue c ix entry k e = kernelValue c ix other k e := by
  cases hb : k.body with
  | prog code out =>
    simp only [kernelValue,hb]
    apply congrArg (fun (f : Nat → Word) => f out)
    apply runKCode_congr
    intro ins hi base hr
    exact h (base+e) (by simp only [KernelReads,hb]; exact ⟨ins,hi,base,hr,e,he,rfl⟩)
  | gather ixb base =>
    simpa only [kernelValue,hb] using
      h _ (by simp only [KernelReads,hb]; exact ⟨e,he,rfl⟩)
  | concat base len otherBase =>
    simp only [kernelValue,hb]
    by_cases hl : e < len
    · rw [if_pos hl,if_pos hl]
      exact h _ (by simp only [KernelReads,hb]; exact ⟨e,he,Or.inl ⟨hl,rfl⟩⟩)
    · rw [if_neg hl,if_neg hl]
      exact h _ (by simp only [KernelReads,hb]; exact ⟨e,he,Or.inr ⟨hl,rfl⟩⟩)
  | const base => simp only [kernelValue,hb]
  | fold op shape base =>
    simp only [kernelValue,hb]
    congr 1
    unfold evalFold
    apply List.map_congr_left
    intro range hr
    apply foldRange_congr
    intro i hi hbnd
    apply h (base+i)
    simp only [KernelReads,hb]
    exact ⟨i,by have := shape.ranges_bound range hr; omega,rfl⟩

def runKernel (c : List Word) (ix : List Nat) (entry : Nat → Word) (k : Kernel) : Nat → Word :=
  runStage c ix entry ⟨[k]⟩

@[simp] theorem runKernel_apply (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (k : Kernel) (a : Nat) : runKernel c ix entry k a =
      if k.owns a then kernelValue c ix entry k (a-k.dstBase) else entry a := by
  cases h : k.owns a <;> simp [runKernel,runStage,List.find?_cons,h]

theorem owns_offset (k : Kernel) (a : Nat) (ha : k.owns a = true) : a-k.dstBase < k.count := by
  simp only [Kernel.owns,decide_eq_true_eq] at ha
  omega

theorem runKernel_reads_unchanged (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (writer reader : Kernel) (h : ReadWriteSeparated ix writer reader)
    (a : Nat) (ha : KernelReads ix reader a) : runKernel c ix entry writer a = entry a := by
  rw [runKernel_apply]
  have hw : writer.owns a = false := by
    cases he : writer.owns a with
    | false => rfl
    | true => exact False.elim (h a he ha)
  simp [hw]

theorem runKernel_value_unchanged (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (writer reader : Kernel) (h : ReadWriteSeparated ix writer reader)
    (e : Nat) (he : e < reader.count) :
    kernelValue c ix (runKernel c ix entry writer) reader e = kernelValue c ix entry reader e :=
  kernelValue_congr c ix _ entry reader e he (runKernel_reads_unchanged c ix entry writer reader h)

theorem runStage_frame (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (ks : List Kernel) (a : Nat) (h : ∀ k ∈ ks, k.owns a = false) :
    runStage c ix entry ⟨ks⟩ a = entry a := by
  have hf : ks.find? (fun k => k.owns a) = none := by
    exact List.find?_eq_none.mpr (fun k hk => by simp [h k hk])
  simp [runStage,hf]

/-- Temporary collective storage above the live graph allocation need not agree
between executions. Declared read bounds are enough for subsequent kernels. -/
theorem runStage_agreeBelow (c : List Word) (ix : List Nat) (words : Nat)
    (entry other : Nat → Word) (stage : GpuStage)
    (h : AgreeBelow words entry other)
    (hb : ∀ k ∈ stage.kernels, KernelBounded words ix k) :
    AgreeBelow words (runStage c ix entry stage) (runStage c ix other stage) := by
  intro a ha
  cases hf : stage.kernels.find? (fun k => k.owns a) with
  | none => simpa [runStage,hf] using h a ha
  | some k =>
    have hk := List.mem_of_find?_eq_some hf
    have ho : k.owns a = true := List.find?_some (p := fun k : Kernel => k.owns a) hf
    simp only [runStage,hf]
    exact kernelValue_congr c ix entry other k _ (owns_offset k a ho)
      (fun i hi => h i ((hb k hk).2 i hi))

theorem runStage_cons (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (k : Kernel) (ks : List Kernel) (a : Nat) :
    runStage c ix entry ⟨k::ks⟩ a =
      if k.owns a then kernelValue c ix entry k (a-k.dstBase) else runStage c ix entry ⟨ks⟩ a := by
  cases h : k.owns a <;> simp [runStage,List.find?_cons,h]

/-- One kernel can execute before the rest exactly when its stores neither
clobber their reads nor overlap their destination words. -/
theorem runStage_split_head (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (k : Kernel) (ks : List Kernel) (h : ∀ r ∈ ks, Independent ix k r) :
    runStage c ix (runKernel c ix entry k) ⟨ks⟩ = runStage c ix entry ⟨k::ks⟩ := by
  funext a
  rw [runStage_cons]
  by_cases hk : k.owns a = true
  · have hrest : ∀ r ∈ ks, r.owns a = false := by
      intro r hr
      cases hh : r.owns a with
      | false => rfl
      | true => exact False.elim ((h r hr).1 a hk hh)
    rw [runStage_frame c ix _ ks a hrest,runKernel_apply]
    simp [hk]
  · have hk' : k.owns a = false := by cases hh : k.owns a <;> simp_all
    simp only [hk',Bool.false_eq_true,if_false]
    cases hf : ks.find? (fun r => r.owns a) with
    | none => simp [runStage,hf,runKernel_apply,hk']
    | some r =>
      have hr : r ∈ ks := List.mem_of_find?_eq_some hf
      have ho : r.owns a = true := List.find?_some (p := fun r : Kernel => r.owns a) hf
      simp only [runStage,hf]
      exact runKernel_value_unchanged c ix entry k r (h r hr).2.1 _ (owns_offset r a ho)

def runSequential (c : List Word) (ix : List Nat) (entry : Nat → Word) (ks : List Kernel) : Nat → Word :=
  ks.foldl (runKernel c ix) entry

/-- Universal snapshot-to-sequential theorem, preserving the exact original
kernel evaluator and allowing self-aliasing inside a singleton map kernel. -/
theorem runSequential_eq_stage (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (ks : List Kernel) (h : ks.Pairwise (Independent ix)) :
    runSequential c ix entry ks = runStage c ix entry ⟨ks⟩ := by
  induction ks generalizing entry with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨hh,ht⟩ := List.pairwise_cons.mp h
    change runSequential c ix (runKernel c ix entry k) ks = _
    rw [ih _ ht]
    exact runStage_split_head c ix entry k ks hh

theorem owner_unique (ix : List Nat) (ks : List Kernel) (h : ks.Pairwise (Independent ix))
    (k r : Kernel) (hk : k ∈ ks) (hr : r ∈ ks) (a : Nat)
    (hka : k.owns a = true) (hra : r.owns a = true) : k = r := by
  induction ks with
  | nil => simp at hk
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hk with rfl | hkTail
    · rcases List.mem_cons.mp hr with rfl | hrTail
      · rfl
      · exact False.elim ((hx r hrTail).1 a hka hra)
    · rcases List.mem_cons.mp hr with rfl | hrTail
      · exact False.elim ((hx k hkTail).1 a hra hka)
      · exact ih ht hkTail hrTail

theorem runStage_perm (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (as bs : List Kernel) (hp : as.Perm bs) (h : as.Pairwise (Independent ix)) :
    runStage c ix entry ⟨as⟩ = runStage c ix entry ⟨bs⟩ := by
  funext a
  cases ha : as.find? (fun k => k.owns a) with
  | none =>
    have hb : bs.find? (fun k => k.owns a) = none := by
      apply List.find?_eq_none.mpr
      intro k hk
      exact List.find?_eq_none.mp ha k (hp.mem_iff.mpr hk)
    simp [runStage,ha,hb]
  | some k =>
    have hk := List.mem_of_find?_eq_some ha
    have hka : k.owns a = true := List.find?_some (p := fun k : Kernel => k.owns a) ha
    cases hb : bs.find? (fun r => r.owns a) with
    | none => exact False.elim (List.find?_eq_none.mp hb k (hp.mem_iff.mp hk) hka)
    | some r =>
      have hr := List.mem_of_find?_eq_some hb
      have hra : r.owns a = true := List.find?_some (p := fun r : Kernel => r.owns a) hb
      have he := owner_unique ix as h k r hk (hp.mem_iff.mpr hr) a hka hra
      subst r
      simp [runStage,ha,hb]

theorem runSequential_append (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (as bs : List Kernel) : runSequential c ix entry (as ++ bs) =
      runSequential c ix (runSequential c ix entry as) bs := by
  simp [runSequential,List.foldl_append]

def ordinary (k : Kernel) : Bool := match k.body with
  | .fold _ _ _ => false
  | _ => true

def ordinaryFirst (ks : List Kernel) : List Kernel :=
  ks.filter ordinary ++ ks.filter (fun k => !ordinary k)

def runOrdinaryThenFolds (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (ks : List Kernel) : Nat → Word :=
  runSequential c ix (runStage c ix entry ⟨ks.filter ordinary⟩) (ks.filter (fun k => !ordinary k))

/-- The concrete ordering used by ArrayEmit: one ordinary frontier followed by
each fold in original order. Physical read/write independence justifies both the
partition and the subsequent individual collective dispatch sequences. -/
theorem ordinary_then_folds_eq_stage (c : List Word) (ix : List Nat) (entry : Nat → Word)
    (ks : List Kernel) (h : ks.Pairwise (Independent ix)) :
    runOrdinaryThenFolds c ix entry ks = runStage c ix entry ⟨ks⟩ := by
  have hp : (ordinaryFirst ks).Perm ks := List.filter_append_perm ordinary ks
  have ho : (ordinaryFirst ks).Pairwise (Independent ix) :=
    h.perm hp.symm (fun {a b} => independent_symm ix a b)
  have hfirst : (ks.filter ordinary).Pairwise (Independent ix) :=
    (List.pairwise_append.mp ho).1
  unfold runOrdinaryThenFolds
  rw [← runSequential_eq_stage c ix entry _ hfirst, ← runSequential_append]
  change runSequential c ix entry (ordinaryFirst ks) = _
  rw [runSequential_eq_stage c ix entry _ ho]
  exact runStage_perm c ix entry _ _ hp ho

theorem checked_ordinary_then_folds_eq_stage (c : List Word) (ix : List Nat)
    (entry : Nat → Word) (stage : GpuStage) (h : checkStage ix stage = true) :
    runOrdinaryThenFolds c ix entry stage.kernels = runStage c ix entry stage :=
  ordinary_then_folds_eq_stage c ix entry stage.kernels (checkStage_sound ix stage h)

end Obend.Hardware.Gpu.ArraySchedule
end
