module
public import Obend.Hardware.Gpu.ArrayEmit
public import Obend.Hardware.Gpu.PhaseSemantics
@[expose] public section

/-! Buffer renaming is a simulation of the actual ArrayKernel evaluator.
The arena's unused rows frame unrelated live graph storage; scratch contents are
arbitrary. Physical boundary placement is proved against BlockLower.bufferBase.
-/
namespace Obend.Hardware.Gpu.CollectiveArena
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArrayEmit Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.Gpu.PhaseSemantics
set_option autoImplicit false

/-- Source cells and their renamed destination cells contain the same words. -/
def Renames (p : Program) (f : Nat → Nat) (source target : Memory) : Prop :=
  ∀ a i, Valid p a i → valueAt target (f a) i = valueAt source a i

def renameWrite (f : Nat → Nat) (w : Nat × Nat × Word) : Nat × Nat × Word :=
  (f w.1,w.2.1,w.2.2)

def renameDispatch (f : Nat → Nat) (d : Dispatch) : Dispatch :=
  {d with phases := d.phases.map (renamePhase f)}

theorem applyWrite_rename (p q : Program) (f : Nat → Nat) (hf : Function.Injective f)
    (hvmap : ∀ a i, Valid p a i → Valid q (f a) i)
    (source target : Memory) (hgs : Obend.Hardware.Gpu.BlockLower.Good p source) (hgt : Obend.Hardware.Gpu.BlockLower.Good q target)
    (hr : Renames p f source target) (w : Nat × Nat × Word) (hw : Valid p w.1 w.2.1) :
    Renames p f (applyWrite source w) (applyWrite target (renameWrite f w)) := by
  intro a i hai
  rw [applyWrite_value q target (renameWrite f w) hgt (hvmap _ _ hw),
    applyWrite_value p source w hgs hw]
  simp only [renameWrite, writeLoc, Prod.mk.injEq, hf.eq_iff]
  split <;> simp_all [Renames]

theorem loadRegisters_rename (p : Program) (f : Nat → Nat) (ph : Phase) (g l : Nat)
    (source target : Memory) (hr : Renames p f source target)
    (hb : ∀ r ∈ ph.reads, Valid p r.array (r.index.eval g l)) :
    loadRegisters (renamePhase f ph) target g l = loadRegisters ph source g l := by
  unfold loadRegisters renamePhase
  simp only [List.foldl_map]
  have hreads : ∀ reads : List Read, (∀ r ∈ reads, Valid p r.array (r.index.eval g l)) →
      ∀ regs : Registers,
      reads.foldl (fun regs r => regs.insert r.dst (valueAt target (f r.array) (r.index.eval g l))) regs =
      reads.foldl (fun regs r => regs.insert r.dst (valueAt source r.array (r.index.eval g l))) regs := by
    intro reads h
    induction reads with
    | nil => intro regs; rfl
    | cons r rs ih =>
      intro regs
      simp only [List.foldl_cons]
      rw [hr r.array _ (h r (by simp))]
      exact ih (fun r hr => h r (by simp [hr])) _
  exact hreads ph.reads hb ∅

theorem phaseWrites_rename (p : Program) (f : Nat → Nat) (ph : Phase) (g : Nat)
    (source target : Memory) (hr : Renames p f source target) (hb : PhaseInBounds p ph g) :
    phaseWrites (renamePhase f ph) target g = (phaseWrites ph source g).map (renameWrite f) := by
  unfold phaseWrites
  simp only [renamePhase, List.map_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro l hl
  have hload := loadRegisters_rename p f ph g l source target hr (hb.1 l (List.mem_range.mp hl))
  simpa only [laneWrites, renamePhase, hload, List.map_map, Function.comp_def, renameWrite] using
    congrArg (fun regs => ph.writes.map fun w => (f w.array, w.index.eval g l, regs.getD w.value 0#64))
      (congrArg (runRegisters ph.code) hload)

theorem foldWrites_rename (p q : Program) (f : Nat → Nat) (hf : Function.Injective f)
    (hvmap : ∀ a i, Valid p a i → Valid q (f a) i) (ws : List (Nat × Nat × Word))
    (source target : Memory) (hgs : Obend.Hardware.Gpu.BlockLower.Good p source) (hgt : Obend.Hardware.Gpu.BlockLower.Good q target)
    (hr : Renames p f source target) (hw : ∀ w ∈ ws, Valid p w.1 w.2.1) :
    Renames p f (ws.foldl applyWrite source) ((ws.map (renameWrite f)).foldl applyWrite target) := by
  induction ws generalizing source target with
  | nil => exact hr
  | cons w ws ih =>
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (applyWrite_good p source w hgs) (applyWrite_good q target _ hgt)
      (applyWrite_rename p q f hf hvmap source target hgs hgt hr w (hw w (by simp)))
      (fun w h => hw w (by simp [h]))

theorem evalPhase_rename (p q : Program) (f : Nat → Nat) (hf : Function.Injective f)
    (hvmap : ∀ a i, Valid p a i → Valid q (f a) i) (ph : Phase) (g : Nat)
    (source target : Memory) (hgs : Obend.Hardware.Gpu.BlockLower.Good p source) (hgt : Obend.Hardware.Gpu.BlockLower.Good q target)
    (hr : Renames p f source target) (hb : PhaseInBounds p ph g) :
    Renames p f (evalPhase ph g source) (evalPhase (renamePhase f ph) g target) := by
  change Renames p f ((phaseWrites ph source g).foldl applyWrite source)
    ((phaseWrites (renamePhase f ph) target g).foldl applyWrite target)
  rw [phaseWrites_rename p f ph g source target hr hb]
  exact foldWrites_rename p q f hf hvmap _ source target hgs hgt hr (phaseWrites_valid p ph source g hb)

/-- Simulations preserve arbitrary paired state through an actual list traversal. -/
theorem fold_rename {α : Type} (p q : Program) (f : Nat → Nat) (xs : List α)
    (left right : α → Memory → Memory)
    (hs : ∀ x ∈ xs, ∀ s t, Obend.Hardware.Gpu.BlockLower.Good p s → Obend.Hardware.Gpu.BlockLower.Good q t → Renames p f s t →
      Obend.Hardware.Gpu.BlockLower.Good p (left x s) ∧ Obend.Hardware.Gpu.BlockLower.Good q (right x t) ∧ Renames p f (left x s) (right x t))
    (s t : Memory) (hgs : Obend.Hardware.Gpu.BlockLower.Good p s) (hgt : Obend.Hardware.Gpu.BlockLower.Good q t) (hr : Renames p f s t) :
    Obend.Hardware.Gpu.BlockLower.Good p (xs.foldl (fun m x => left x m) s) ∧
    Obend.Hardware.Gpu.BlockLower.Good q (xs.foldl (fun m x => right x m) t) ∧
    Renames p f (xs.foldl (fun m x => left x m) s) (xs.foldl (fun m x => right x m) t) := by
  induction xs generalizing s t with
  | nil => exact ⟨hgs,hgt,hr⟩
  | cons x xs ih =>
    have hx := hs x (by simp) s t hgs hgt hr
    exact ih (fun x h => hs x (by simp [h])) _ _ hx.1 hx.2.1 hx.2.2

theorem evalGroup_rename (p q : Program) (f : Nat → Nat) (hf : Function.Injective f)
    (hvmap : ∀ a i, Valid p a i → Valid q (f a) i) (d : Dispatch) (g : Nat)
    (source target : Memory) (hgs : Obend.Hardware.Gpu.BlockLower.Good p source) (hgt : Obend.Hardware.Gpu.BlockLower.Good q target)
    (hr : Renames p f source target) (hb : ∀ ph ∈ d.phases, PhaseInBounds p ph g) :
    Renames p f (evalGroup d g source) (evalGroup (renameDispatch f d) g target) := by
  have h := fold_rename p q f d.phases (fun ph m => evalPhase ph g m)
    (fun ph m => evalPhase (renamePhase f ph) g m) (by
      intro ph hp s t hs ht hr
      exact ⟨foldWrites_good p s _ hs, foldWrites_good q t _ ht,
        evalPhase_rename p q f hf hvmap ph g s t hs ht hr (hb ph hp)⟩) source target hgs hgt hr
  simpa [evalGroup,renameDispatch,List.foldl_map] using h.2.2

theorem evalDispatch_rename (p q : Program) (f : Nat → Nat) (hf : Function.Injective f)
    (hvmap : ∀ a i, Valid p a i → Valid q (f a) i) (d : Dispatch)
    (source target : Memory) (hgs : Obend.Hardware.Gpu.BlockLower.Good p source) (hgt : Obend.Hardware.Gpu.BlockLower.Good q target)
    (hr : Renames p f source target) (hb : DispatchInBounds p d) :
    Renames p f (evalDispatch d source) (evalDispatch (renameDispatch f d) target) := by
  exact (fold_rename p q f (List.range d.groups) (evalGroup d) (evalGroup (renameDispatch f d))
    (fun g hg s t hs ht hr => ⟨evalGroup_good p d g s hs, evalGroup_good q _ g t ht,
      evalGroup_rename p q f hf hvmap d g s t hs ht hr (hb g (List.mem_range.mp hg))⟩)
    source target hgs hgt hr).2.2

theorem dispatch_good (p : Program) (d : Dispatch) (mem : Memory) (hg : Obend.Hardware.Gpu.BlockLower.Good p mem) :
    Obend.Hardware.Gpu.BlockLower.Good p (evalDispatch d mem) := by
  unfold evalDispatch
  induction List.range d.groups generalizing mem with
  | nil => exact hg
  | cons g gs ih => exact ih _ (evalGroup_good p d g mem hg)

/-- Universal program simulation: only buffer identifiers change. -/
theorem evalProgram_rename (p q : Program) (f : Nat → Nat) (hf : Function.Injective f)
    (hvmap : ∀ a i, Valid p a i → Valid q (f a) i)
    (hds : q.dispatches = p.dispatches.map (renameDispatch f))
    (source target : Memory) (hgs : Obend.Hardware.Gpu.BlockLower.Good p source) (hgt : Obend.Hardware.Gpu.BlockLower.Good q target)
    (hr : Renames p f source target) (hc : p.check = .ok ()) :
    Renames p f (evalProgram p source) (evalProgram q target) := by
  have hb := boundsSafe_sound p (p.check_boundsSafe hc)
  have h := fold_rename p q f p.dispatches evalDispatch
    (fun d t => evalDispatch (renameDispatch f d) t)
    (fun d hd s t hs ht hr => ⟨dispatch_good p d s hs, dispatch_good q _ t ht,
      evalDispatch_rename p q f hf hvmap d s t hs ht hr (hb d hd)⟩)
    source target hgs hgt hr
  simpa [evalProgram,hds,List.foldl_map] using h.2.2

theorem arenaIndex_injective (first : Bool) : Function.Injective (arenaIndex first) := by
  intro a b h
  cases first <;> by_cases ha0 : a = 0 <;> by_cases ha1 : a = 1 <;>
    by_cases hb0 : b = 0 <;> by_cases hb1 : b = 1 <;>
    simp [arenaIndex,ha0,ha1,hb0,hb1] at h <;> omega

/-- The padding rows make a canonical prefix allocation with exact boundary bases. -/
def arenaBuffers (p : Program) (words src dst : Nat) (first : Bool) : List Buffer :=
  let a := buffer p 0
  let b := buffer p 1
  let lo := if first then src else dst
  let hi := if first then dst else src
  let x := if first then a else b
  let y := if first then b else a
  [⟨lo,.device,[]⟩,x,⟨hi-lo-x.size,.device,[]⟩,y,⟨words-hi-y.size,.device,[]⟩] ++ p.buffers.drop 2

/-- Receipt consists entirely of checked metadata and exact builder output. -/
structure Placement (p q : Program) (words src dst : Nat) (first : Bool) : Prop where
  size : 2 ≤ p.buffers.length
  input_device : (buffer p 0).storage = .device
  output_device : (buffer p 1).storage = .device
  input_bound : src+(buffer p 0).size ≤ words
  output_bound : dst+(buffer p 1).size ≤ words
  separated : if first then src+(buffer p 0).size ≤ dst else dst+(buffer p 1).size ≤ src
  buffers : q.buffers = arenaBuffers p words src dst first
  inputs : q.inputs = p.inputs.map (arenaIndex first)
  outputs : q.outputs = p.outputs.map (arenaIndex first)
  dispatches : q.dispatches = p.dispatches.map (renameDispatch (arenaIndex first))

theorem inArena_placement (p q : Program) (words src dst : Nat)
    (h : inArena p words src dst = .ok q) : ∃ first, Placement p q words src dst first := by
  unfold inArena at h
  simp only [bind, Except.bind, pure, Except.pure, throw] at h
  split at h
  · rename_i header
    split at h
    · rename_i bounds
      split at h
      · rename_i separation
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at header bounds
        refine ⟨decide (src+(buffer p 0).size ≤ dst), ?_⟩
        constructor
        · simpa using header.2
        · simpa [buffer] using bounds.1.1.1
        · simpa [buffer] using bounds.1.1.2
        · simpa [buffer] using bounds.1.2
        · simpa [buffer] using bounds.2
        · split <;> simp_all [buffer] <;> omega
        · simp [arenaBuffers,buffer]
        · rfl
        · rfl
        · rfl
      · cases h
    · cases h
  · cases h

theorem placement_buffer (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (a : Nat) (ha : a < p.buffers.length) :
    buffer q (arenaIndex first a) = buffer p a := by
  rw [buffer, h.buffers]
  rcases a with _ | a
  · cases first <;> simp [arenaIndex,arenaBuffers,buffer]
  · rcases a with _ | a
    · cases first <;> simp [arenaIndex,arenaBuffers,buffer]
    · simp [arenaIndex,arenaBuffers,buffer,List.getD_eq_getElem?_getD,
        List.getElem?_append_right, List.getElem?_drop, Nat.add_assoc]
      congr 2 <;> omega

theorem placement_valid (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (a i : Nat) (hv : Valid p a i) :
    Valid q (arenaIndex first a) i := by
  refine ⟨?_, ?_⟩
  · rw [h.buffers]
    simp only [arenaBuffers,List.length_append,List.length_cons,List.length_nil,List.length_drop]
    have ha := hv.1
    have hs := h.size
    cases first <;> by_cases ha0 : a=0 <;> by_cases ha1 : a=1 <;>
      simp [arenaIndex,ha0,ha1] <;> omega
  · rw [placement_buffer p q words src dst first h a hv.1]
    exact hv.2

/-- Input and output addresses are exactly their graph live-range bases. -/
theorem placement_bases (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) :
    bufferBase q (arenaIndex first 0) = src ∧ bufferBase q (arenaIndex first 1) = dst := by
  have h0 := placement_buffer p q words src dst first h 0 (by have := h.size; omega)
  have h1 := placement_buffer p q words src dst first h 1 (by have := h.size; omega)
  unfold bufferBase
  rw [h0,h1,h.input_device,h.output_device]
  simp only [lengths,h.buffers]
  have hs := h.separated
  cases first <;> simp [arenaIndex,arenaBuffers,wirePrefix,h.input_device,h.output_device] at * <;> omega

/-- The public arena constructor is connected to the universal renaming simulation. -/
theorem inArena_evalProgram (p q : Program) (words src dst : Nat)
    (h : inArena p words src dst = .ok q) (source target : Memory)
    (hgs : Obend.Hardware.Gpu.BlockLower.Good p source) (hgt : Obend.Hardware.Gpu.BlockLower.Good q target) (hc : p.check = .ok ()) :
    ∃ first, Placement p q words src dst first ∧
      (Renames p (arenaIndex first) source target →
        Renames p (arenaIndex first) (evalProgram p source) (evalProgram q target)) := by
  obtain ⟨first,hp⟩ := inArena_placement p q words src dst h
  exact ⟨first,hp, fun hr => evalProgram_rename p q (arenaIndex first) (arenaIndex_injective first)
    (placement_valid p q words src dst first hp) hp.dispatches source target hgs hgt hr hc⟩

/-- A flat store traversal frames every address absent from its concrete stores. -/
theorem flatWrites_frame (ws : List FlatWrite) (flat : FlatMemory) (a : Address)
    (h : ∀ w ∈ ws, w.1 ≠ a) : (ws.foldl flatStore flat) a = flat a := by
  induction ws generalizing flat with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons, ih _ (fun w hw => h w (by simp [hw]))]
    simp [flatStore, (h w (by simp)).symm]

theorem lowerPhase_frame (p : Program) (ph : Phase) (g : Nat) (flat : FlatMemory) (a : Address)
    (h : ∀ l < ph.lanes, ∀ w ∈ ph.writes, address p w.array (w.index.eval g l) ≠ a) :
    lowerPhase p ph g flat a = flat a := by
  apply flatWrites_frame
  intro w hw
  obtain ⟨l,hl,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact h l (List.mem_range.mp hl) v hv

theorem flatFold_frame {α : Type} (xs : List α) (step : α → FlatMemory → FlatMemory)
    (a : Address) (h : ∀ x ∈ xs, ∀ flat, step x flat a = flat a) (flat : FlatMemory) :
    (xs.foldl (fun flat x => step x flat) flat) a = flat a := by
  induction xs generalizing flat with
  | nil => rfl
  | cons x xs ih => exact (ih (fun y hy => h y (by simp [hy])) _).trans (h x (by simp) flat)

/-- Universal physical frame rule over the emitter's actual flattened evaluator. -/
theorem lowerProgram_frame (p : Program) (flat : FlatMemory) (a : Address)
    (h : ∀ d ∈ p.dispatches, ∀ g < d.groups, ∀ ph ∈ d.phases, ∀ l < ph.lanes,
      ∀ w ∈ ph.writes, address p w.array (w.index.eval g l) ≠ a) :
    lowerProgram p flat a = flat a := by
  apply flatFold_frame p.dispatches (lowerDispatch p) a _ flat
  intro d hd flat
  apply flatFold_frame (List.range d.groups) (fun g f => lowerPhases p d.phases g f) a _ flat
  intro g hg flat
  apply flatFold_frame d.phases (fun ph f => lowerPhase p ph g f) a _ flat
  intro ph hp flat
  exact lowerPhase_frame p ph g flat a (h d hd g (List.mem_range.mp hg) ph hp)

/-- Device summaries are beyond the graph's entire live allocation. Shared rows
have a different storage space and cannot alias device cells. -/
theorem placement_device_tail (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (a : Nat) (ha : a < p.buffers.length)
    (ha2 : 2 ≤ a) (hd : (buffer p a).storage = .device) :
    words ≤ bufferBase q (arenaIndex first a) := by
  have hab : arenaIndex first a = a+3 := by simp [arenaIndex, show a≠0 by omega, show a≠1 by omega]
  have hmap := placement_buffer p q words src dst first h a ha
  have hlen : 4 < (lengths q .device).length := by
    simp [lengths,h.buffers,arenaBuffers]
  have hm := wirePrefix_mono (lengths q .device) 4 (arenaIndex first a) (by rw [hab]; omega) hlen
  have hsum : wirePrefix (lengths q .device) 4 + (lengths q .device).getD 4 0 = words := by
    have hs := h.separated
    have hb0 := h.input_bound
    have hb1 := h.output_bound
    cases first <;>
      simp [lengths,h.buffers,arenaBuffers,wirePrefix,h.input_device,h.output_device] at * <;> omega
  rw [hsum] at hm
  simpa [bufferBase,hmap,hd] using hm

/-- Below the scratch arena, a renamed device address belongs to a boundary. -/
theorem placement_live_address (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (a i j : Nat) (ha : a < p.buffers.length)
    (hj : j < words) (he : address q (arenaIndex first a) i = (.device,j)) : a = 0 ∨ a = 1 := by
  by_cases hn : a = 0 ∨ a = 1
  · exact hn
  exfalso
  have ha2 : 2 ≤ a := by omega
  have hstorage : (buffer p a).storage = .device := by
    have hh := congrArg Prod.fst he
    simpa [address,placement_buffer p q words src dst first h a ha] using hh
  have hb := placement_device_tail p q words src dst first h a ha ha2 hstorage
  have hix := congrArg Prod.snd he
  simp only [address] at hix
  omega

/-- Every non-boundary live cell is framed by arena execution. Bounds on actual
stores come from admission; no output-value hypothesis appears. -/
theorem placement_live_frame (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (hc : p.check = .ok ())
    (flat : FlatMemory) (j : Nat) (hj : j < words)
    (hsrc : j < src ∨ src+(buffer p 0).size ≤ j)
    (hdst : j < dst ∨ dst+(buffer p 1).size ≤ j) :
    lowerProgram q flat (.device,j) = flat (.device,j) := by
  apply lowerProgram_frame
  intro d hd g hg ph hp l hl w hw he
  rw [h.dispatches] at hd
  obtain ⟨d0,hd0,rfl⟩ := List.mem_map.mp hd
  obtain ⟨ph0,hp0,rfl⟩ := List.mem_map.mp hp
  obtain ⟨w0,hw0,rfl⟩ := List.mem_map.mp hw
  have hv := (boundsSafe_sound p (p.check_boundsSafe hc) d0 hd0 g hg ph0 hp0).2 l hl w0 hw0
  have he' : address q (arenaIndex first w0.array) (w0.index.eval g l) = (.device,j) := he
  have cases := placement_live_address p q words src dst first h w0.array (w0.index.eval g l) j hv.1 hj he'
  have hix := congrArg Prod.snd he'
  simp only [address] at hix
  rcases cases with hzero | hone
  · rw [hzero, (placement_bases p q words src dst first h).1] at hix
    have hbound := hv.2
    rw [hzero] at hbound
    omega
  · rw [hone, (placement_bases p q words src dst first h).2] at hix
    have hbound := hv.2
    rw [hone] at hbound
    omega

/-- With read-only source boundaries, every other live graph cell is preserved. -/
theorem placement_output_frame (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (hc : p.check = .ok ())
    (flat : FlatMemory) (j : Nat) (hj : j < words)
    (hinput : ∀ d ∈ p.dispatches, ∀ ph ∈ d.phases, ∀ w ∈ ph.writes, w.array ≠ 0)
    (hdst : j < dst ∨ dst+(buffer p 1).size ≤ j) :
    lowerProgram q flat (.device,j) = flat (.device,j) := by
  apply lowerProgram_frame
  intro d hd g hg ph hp l hl w hw he
  rw [h.dispatches] at hd
  obtain ⟨d0,hd0,rfl⟩ := List.mem_map.mp hd
  obtain ⟨ph0,hp0,rfl⟩ := List.mem_map.mp hp
  obtain ⟨w0,hw0,rfl⟩ := List.mem_map.mp hw
  have hv := (boundsSafe_sound p (p.check_boundsSafe hc) d0 hd0 g hg ph0 hp0).2 l hl w0 hw0
  have he' : address q (arenaIndex first w0.array) (w0.index.eval g l) = (.device,j) := he
  have cases := placement_live_address p q words src dst first h w0.array (w0.index.eval g l) j hv.1 hj he'
  have hix := congrArg Prod.snd he'
  simp only [address] at hix
  rcases cases with hzero | hone
  · exact hinput d0 hd0 ph0 hp0 w0 hw0 hzero
  · rw [hone, (placement_bases p q words src dst first h).2] at hix
    have hbound := hv.2
    rw [hone] at hbound
    omega

/-- Pull any arena state back to the original buffer numbering. This chooses the
source scratch contents from the actual target state, imposing no zeroing premise. -/
def pullMemory (p : Program) (f : Nat → Nat) (target : Memory) : Memory :=
  (List.range p.buffers.length).toArray.map fun a => target.getD (f a) #[]

theorem pullMemory_row (p : Program) (f : Nat → Nat) (target : Memory) (a : Nat)
    (ha : a < p.buffers.length) :
    (pullMemory p f target).getD a #[] = target.getD (f a) #[] := by
  simp [pullMemory,Array.getD_eq_getD_getElem?,ha]

theorem pullMemory_renames (p : Program) (f : Nat → Nat) (target : Memory) :
    Renames p f (pullMemory p f target) target := by
  intro a i hv
  simp only [valueAt,pullMemory_row p f target a hv.1]

theorem placement_pullMemory_good (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (target : Memory)
    (hg : Obend.Hardware.Gpu.BlockLower.Good q target) :
    Obend.Hardware.Gpu.BlockLower.Good p (pullMemory p (arenaIndex first) target) := by
  constructor
  · simp [pullMemory]
  · intro a ha
    rw [pullMemory_row p (arenaIndex first) target a ha]
    have hfa : arenaIndex first a < q.buffers.length := by
      rw [h.buffers]
      simp only [arenaBuffers,List.length_append,List.length_cons,List.length_nil,List.length_drop]
      have hs := h.size
      cases first <;> by_cases ha0 : a=0 <;> by_cases ha1 : a=1 <;>
        simp [arenaIndex,ha0,ha1] <;> omega
    rw [hg.2 _ hfa,placement_buffer p q words src dst first h a ha]

/-- A concrete arena word after physical lowering is the original collective's
result at its source buffer coordinate. Initial scratch is pulled from target. -/
theorem placement_lowerProgram_value (p q : Program) (words src dst : Nat) (first : Bool)
    (h : Placement p q words src dst first) (hc : p.check = .ok ()) (hqc : q.check = .ok ())
    (target : Memory) (flat : FlatMemory) (hg : Obend.Hardware.Gpu.BlockLower.Good q target)
    (hr : Represents q target flat) (a i : Nat) (hv : Valid p a i) :
    lowerProgram q flat (address q (arenaIndex first a) i) =
      valueAt (evalProgram p (pullMemory p (arenaIndex first) target)) a i := by
  have hp := placement_pullMemory_good p q words src dst first h target hg
  have hs := evalProgram_rename p q (arenaIndex first) (arenaIndex_injective first)
    (placement_valid p q words src dst first h) h.dispatches _ target hp hg
    (pullMemory_renames p (arenaIndex first) target) hc
  have hflat := checkedProgram_sound q target flat hg hr hqc
  exact (hflat _ _ (placement_valid p q words src dst first h a i hv)).trans (hs a i hv)

/-- Canonical structured view of arbitrary flat storage, including scratch. -/
def memoryOfFlat (p : Program) (flat : FlatMemory) : Memory :=
  (List.range p.buffers.length).toArray.map fun a =>
    (List.range (buffer p a).size).toArray.map fun i => flat (address p a i)

theorem memoryOfFlat_good (p : Program) (flat : FlatMemory) :
    Obend.Hardware.Gpu.BlockLower.Good p (memoryOfFlat p flat) := by
  constructor
  · simp [memoryOfFlat]
  · intro a ha
    simp [memoryOfFlat,Array.getD_eq_getD_getElem?,ha]

theorem memoryOfFlat_represents (p : Program) (flat : FlatMemory) :
    Represents p (memoryOfFlat p flat) flat := by
  intro a i hv
  simp [memoryOfFlat,Array.getD_eq_getD_getElem?,hv.1,hv.2]

end Obend.Hardware.Gpu.CollectiveArena
end
