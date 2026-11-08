/-
# Obend.Hardware.Gpu.Rdna2.Schedule — a graph's emitted schedule as certified stages

What the emitter dispatches for a graph is `ArrayEmit.compile`'s action list (`ArrayEmit.Schedule`): an
elementwise action is one dispatch of the plan's ordinary kernels (`runStage`), a collective is an admitted
block program (`ArrayKernel.Program`, its dispatches emitted by `BlockEmit`). Both are read here as
certificate stages (`Cert.Spec`) over one flat memory (`BlockLower.FlatMemory`) whose device space is the
wire buffer: `elemSpec` is a plan stage (its table `gpuTableUpTo`, its meaning the action's), and a
collective's dispatches are `Block.blockSpec`. The host's index buffer is `ArrayEmit.scheduleTables`, the
function the plan's `tables` is written from, so each collective's descriptor tables sit where its shaders
read them.

`certifySchedule_sound`: if the certificate accepts and its residuals hold, then for every wire buffer the
dumped programs, run on the model as the host dispatches them, succeed and leave in every word of the
buffer what `ArrayEmit.evalActions` (the semantics `ArrayEmitCorrect.compile_runProgram` relates to the
plan) leaves in the device space.
-/
module

public import Obend.Hardware.Gpu.Rdna2.Block
public import Obend.Hardware.Gpu.ArrayEmit

@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2.Schedule

open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.Gpu.ArrayEmit Obend.Hardware.Gpu.ArraySchedule
open Obend.Hardware.Gpu.Rdna2 Obend.Hardware.Gpu.Rdna2.Block Tm

/-- The flat memory whose device space is `f`, every other space zero. -/
def ofDevice (f : Nat → Word) : FlatMemory := fun a => if a.1 = .device then f a.2 else 0

/-- The stages of one action, each awaiting the LDS its dump allocates: an elementwise action is one
dispatch meaning `Action.eval`; a collective is one `blockSpec` per dispatch, with no constants. -/
def actionSpecs (p : GpuProgram) (words : Nat) : Action → List (Nat → Spec FlatMemory)
  | a@(.elementwise _ stage) => [fun lds =>
      { threads := stage.threads, lds := lds,
        table := fun rd => gpuTableUpTo p.consts.toArray p.tables.toArray stage rd (foldCache rd stage) words,
        den := a.eval p.consts p.tables }]
  | .collective b => b.dispatches.map fun d lds => blockSpec b d words #[] lds

def specsOf (p : GpuProgram) (words : Nat) (acts : List Action) : List (Nat → Spec FlatMemory) :=
  acts.flatMap (actionSpecs p words)

/-- Every dispatch of the schedule with the LDS dwords its dump states. -/
def scheduleSpecs (p : GpuProgram) (words : Nat) (acts : List Action) (ldss : List Nat) : List (Spec FlatMemory) :=
  ((specsOf p words acts).zip ldss).map fun y => y.1 y.2

/-- An elementwise action reads and writes only inside the buffer (`ArraySchedule.checkBounds`). -/
def actionBounded (p : GpuProgram) (words : Nat) : Action → Bool
  | .elementwise _ stage => checkBounds words p.tables stage
  | .collective _ => true

/-- The certificate of a schedule's dumps `progs` (dispatch `k` with `ldss[k]` dwords of LDS). -/
def certifySchedule (p : GpuProgram) (sched : Schedule) (ldss : List Nat) (progs : List Program)
    (rs : List Residual) : Bool :=
  let acts := sched.actions.toList
  sched.words < 2 ^ 29 && p.words ≤ sched.words && (specsOf p sched.words acts).length == ldss.length &&
  acts.all (actionBounded p sched.words) &&
  match checkProgram sched.words (layoutMem sched.words p.consts (scheduleTables p acts))
      (scheduleSpecs p sched.words acts ldss) progs {} {} with
  | some need => need.toList.all rs.contains
  | none => false

/-- The residuals the schedule's dumps need (for the generator of the module that proves them). -/
def neededSchedule (p : GpuProgram) (sched : Schedule) (ldss : List Nat) (progs : List Program) :
    Option (List Residual) :=
  let acts := sched.actions.toList
  (checkProgram sched.words (layoutMem sched.words p.consts (scheduleTables p acts))
    (scheduleSpecs p sched.words acts ldss) progs {} {}).map (·.toList)

/-! ## Each stage keeps its promise -/

theorem elem_sound (p : GpuProgram) (words : Nat) (k : Nat) (stage : GpuStage) (lds : Nat)
    (hb : checkBounds words p.tables stage = true) :
    ({ threads := stage.threads, lds := lds,
       table := fun rd => gpuTableUpTo p.consts.toArray p.tables.toArray stage rd (foldCache rd stage) words,
       den := (Action.elementwise k stage).eval p.consts p.tables } : Spec FlatMemory).Sound words
      (projB words) (ConstsOk #[]) := by
  refine ⟨?_, fun part h => nomatch h⟩
  intro rd env x T _ hrd hT
  let E := projB words x
  have hrd' : (fun j => (rd j).ev env) = E := funext hrd
  have hkb := checkBounds_sound words p.tables stage hb
  have hagree : AgreeBelow words (runStage p.consts p.tables (fun i => x (.device, i)) stage)
      (runStage p.consts p.tables E stage) :=
    runStage_agreeBelow _ _ words _ _ stage (fun i hi => by simp [E, projB, hi]) hkb
  have hden : ∀ i, i < words → projB words ((Action.elementwise k stage).eval p.consts p.tables x) i
      = runStage p.consts p.tables E stage i := by
    intro i hi
    simp only [projB, hi, ite_true, Action.eval]
    exact hagree i hi
  have spec := gpuTableUpTo_spec _ _ stage rd _ words T hT
  refine ⟨fun j h => absurd h (Nat.not_lt_zero _), fun i t ht => ?_, fun i hi => ?_⟩
  · obtain ⟨hi, kk, hf, hkv⟩ := (spec i).1 t ht
    refine ⟨hi, ?_⟩
    rw [hden i hi]
    have hk := pKernel_sound env _ _ _ kk _ t (kvOf_sound (foldCache_mem rd stage) _ _ _ hkv)
    rw [List.toList_toArray, List.toList_toArray, hrd'] at hk
    show t.ev env = runStage p.consts p.tables E stage i
    unfold runStage; rw [hf]; exact hk
  · by_cases h : i < words
    · rw [hden i h]
      have hn := (spec i).2 hi h
      show runStage p.consts p.tables E stage i = E i
      unfold runStage; rw [hn]
    · simp [projB, h]

theorem specs_sound (p : GpuProgram) (words : Nat) (acts : List Action) (ldss : List Nat)
    (hb : acts.all (actionBounded p words) = true) :
    ∀ s ∈ scheduleSpecs p words acts ldss, s.Sound words (projB words) (ConstsOk #[]) := by
  intro s hs
  obtain ⟨⟨f, l⟩, hm, rfl⟩ := List.mem_map.mp hs
  obtain ⟨a, ha, hf⟩ := List.mem_flatMap.mp (List.of_mem_zip hm).1
  have hba := List.all_eq_true.mp hb a ha
  cases a with
  | elementwise k stage =>
    simp only [actionSpecs, List.mem_singleton] at hf
    subst hf
    exact elem_sound p words k stage l hba
  | collective b =>
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hf
    exact blockSpec_sound b d words #[] l

/-! ## The stages compose to the schedule's meaning -/

theorem zip_den {σ : Type} : ∀ (fs : List (Nat → Spec σ)) (ls : List Nat) (x : σ), fs.length = ls.length →
    (∀ f ∈ fs, ∀ l, (f l).den = (f 0).den) →
    ((fs.zip ls).map fun y => y.1 y.2).foldl (fun x s => s.den x) x = fs.foldl (fun x f => (f 0).den x) x
  | [], [], _, _, _ => rfl
  | f :: fs, l :: ls, x, h, hd => by
    simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons]
    rw [hd f List.mem_cons_self l]
    exact zip_den fs ls _ (by simpa using h) fun g hg => hd g (List.mem_cons_of_mem _ hg)
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

theorem actionSpecs_den (p : GpuProgram) (words : Nat) (a : Action) :
    ∀ f ∈ actionSpecs p words a, ∀ l, (f l).den = (f 0).den := by
  intro f hf l
  cases a with
  | elementwise k stage => simp only [actionSpecs, List.mem_singleton] at hf; subst hf; rfl
  | collective b => obtain ⟨d, -, rfl⟩ := List.mem_map.mp hf; rfl

theorem actionSpecs_foldl (p : GpuProgram) (words : Nat) (a : Action) (x : FlatMemory) :
    (actionSpecs p words a).foldl (fun x f => (f 0).den x) x = a.eval p.consts p.tables x := by
  cases a with
  | elementwise k stage => rfl
  | collective b =>
    simp only [actionSpecs, List.foldl_map, Action.eval, lowerProgram]
    rfl

theorem specsOf_foldl (p : GpuProgram) (words : Nat) :
    ∀ (acts : List Action) (x : FlatMemory),
      (specsOf p words acts).foldl (fun x f => (f 0).den x) x = evalActions p acts x
  | [], _ => rfl
  | a :: acts, x => by
    simp only [specsOf, List.flatMap_cons, List.foldl_append] at *
    rw [actionSpecs_foldl]
    exact specsOf_foldl p words acts _

/-! ## The certificate -/

/-- If the certificate is accepted and every residual it names holds, then for every content `f` of the
wire buffer, the decoded programs, run on the model as the host dispatches the schedule, succeed and leave
in every word of the buffer what the schedule's actions leave in the device space. -/
theorem certifySchedule_sound (p : GpuProgram) (sched : Schedule) (ldss : List Nat) (progs : List Program)
    (rs : List Residual) (hc : certifySchedule p sched ldss progs rs = true) (hrs : ∀ r ∈ rs, r.Holds)
    (f : Nat → Word) :
    ∃ m, runDispatch (dispatchesOf (scheduleSpecs p sched.words sched.actions.toList ldss) progs)
        (memOf sched.words p.consts (scheduleTables p sched.actions.toList) f) = some m ∧
      ∀ i, i < sched.words → wordAt m i = evalActions p sched.actions.toList (ofDevice f) (.device, i) := by
  unfold certifySchedule at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hw, -⟩, hlen⟩, hb⟩, hcp⟩ := hc
  split at hcp
  · rename_i need hneed
    have hfin : ∀ r, need.contains r = true → r.Holds := by
      intro r hr
      apply hrs
      have := List.all_eq_true.mp hcp r (by rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]; exact hr)
      simpa using this
    have hss := specs_sound p sched.words sched.actions.toList ldss hb
    have h0 := memOf_start sched.words p.consts (scheduleTables p sched.actions.toList) hw f
    have hproj : projB sched.words (ofDevice f) = fun j => if j < sched.words then f j else 0 := by
      funext j; simp [projB, ofDevice]
    rw [← hproj] at h0
    obtain ⟨m, known', hrun, hend, -⟩ := checkProgram_sound (x := ofDevice f) hw _ progs {} {} need _ hss
      hneed hfin h0 (fun j h => absurd h (Nat.not_lt_zero _))
    refine ⟨m, hrun, fun i hi => ?_⟩
    obtain ⟨lo, hi', e0, e1, e⟩ := hend.word i hi
    have a0 : wDw + UInt64.ofNat (2 * i) = dwLo i := rfl
    unfold wordAt
    rw [a0, e0, e1]
    simp only [Option.getD_some]
    rw [e]
    unfold scheduleSpecs
    rw [zip_den _ _ _ hlen (fun g hg => by
      obtain ⟨a, -, ha⟩ := List.mem_flatMap.mp hg
      exact actionSpecs_den p _ a g ha), specsOf_foldl]
    simp only [projB, hi, ite_true]
  · simp at hcp

end Obend.Hardware.Gpu.Rdna2.Schedule
