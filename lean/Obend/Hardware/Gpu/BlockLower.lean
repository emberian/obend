module
public import Obend.Hardware.ArrayKernel
@[expose] public section

namespace Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
set_option autoImplicit false

/-- The arithmetic used by WGSL's u32 index expressions. -/
def evalIndex32 (g l : Nat) : Ix → BitVec 32
  | .lit n => BitVec.ofNat 32 n
  | .group => BitVec.ofNat 32 g
  | .lane => BitVec.ofNat 32 l
  | .add a b => evalIndex32 g l a + evalIndex32 g l b
  | .mul a b => evalIndex32 g l a * evalIndex32 g l b
  | .div a n => evalIndex32 g l a / BitVec.ofNat 32 n
  | .mod a n => evalIndex32 g l a % BitVec.ofNat 32 n

/-- The admission check prevents intermediate overflow, not only out-of-bounds
final addresses. Accepted source indices equal actual u32 expressions exactly. -/
theorem checkedIndex_sound (g l : Nat) (i : Ix) (h : i.u32Safe g l = true) :
    (evalIndex32 g l i).toNat = i.eval g l := by
  induction i with
  | lit n =>
    simp only [Ix.u32Safe, decide_eq_true_eq] at h
    simp [evalIndex32, Ix.eval, Nat.mod_eq_of_lt h]
  | group =>
    simp only [Ix.u32Safe, decide_eq_true_eq] at h
    simp [evalIndex32, Ix.eval, Nat.mod_eq_of_lt h]
  | lane =>
    simp only [Ix.u32Safe, decide_eq_true_eq] at h
    simp [evalIndex32, Ix.eval, Nat.mod_eq_of_lt h]
  | add a b ia ib =>
    simp only [Ix.u32Safe, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [evalIndex32, Ix.eval, ia h.1.1, ib h.1.2, Nat.mod_eq_of_lt h.2]
  | mul a b ia ib =>
    simp only [Ix.u32Safe, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [evalIndex32, Ix.eval, ia h.1.1, ib h.1.2, Nat.mod_eq_of_lt h.2]
  | div a n ia =>
    simp only [Ix.u32Safe, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [evalIndex32, Ix.eval, BitVec.toNat_udiv, ia h.1.1, Nat.mod_eq_of_lt h.2]
  | mod a n ia =>
    simp only [Ix.u32Safe, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [evalIndex32, Ix.eval, BitVec.toNat_umod, ia h.1.1, Nat.mod_eq_of_lt h.2]

def wirePrefix : List Nat → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | n :: ns, i+1 => n + wirePrefix ns i

theorem wirePrefix_mono (ns : List Nat) (a b : Nat) (hab : a < b) (ha : a < ns.length) :
    wirePrefix ns a + ns.getD a 0 ≤ wirePrefix ns b := by
  induction ns generalizing a b with
  | nil => simp at ha
  | cons n ns ih =>
    cases a with
    | zero => cases b with
      | zero => omega
      | succ b => simp [wirePrefix]
    | succ a => cases b with
      | zero => omega
      | succ b =>
        simp only [wirePrefix, List.getD_cons_succ, List.length_cons] at *
        have := ih a b (by omega) (by omega)
        omega

def lengths (p : Program) (s : Storage) : List Nat :=
  p.buffers.map fun b => if b.storage == s then b.size else 0

def buffer (p : Program) (a : Nat) : Buffer := p.buffers.getD a default

def bufferBase (p : Program) (a : Nat) : Nat :=
  wirePrefix (lengths p (buffer p a).storage) a

def bufferBases (p : Program) : List Nat :=
  (List.range p.buffers.length).map (bufferBase p)

abbrev Address := Storage × Nat
abbrev FlatMemory := Address → Word
abbrev FlatWrite := Address × Word

def address (p : Program) (a i : Nat) : Address :=
  ((buffer p a).storage, bufferBase p a + i)

def Valid (p : Program) (a i : Nat) : Prop :=
  a < p.buffers.length ∧ i < (buffer p a).size

theorem lengths_getD (p : Program) (a : Nat) (ha : a < p.buffers.length) (s : Storage) :
    (lengths p s).getD a 0 = if (buffer p a).storage == s then (buffer p a).size else 0 := by
  simp [lengths, buffer, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem ha]

/-- Distinct in-bounds array elements have distinct physical addresses, including
when arrays live in different storage classes. -/
theorem address_injective (p : Program) (a i b j : Nat)
    (ha : Valid p a i) (hb : Valid p b j) (h : address p a i = address p b j) :
    a = b ∧ i = j := by
  have hs : (buffer p a).storage = (buffer p b).storage := congrArg Prod.fst h
  have hi : bufferBase p a + i = bufferBase p b + j := congrArg Prod.snd h
  by_cases hab : a = b
  · subst b
    exact ⟨rfl, by omega⟩
  · have hla : (lengths p (buffer p a).storage).getD a 0 = (buffer p a).size := by
      rw [lengths_getD p a ha.1]; simp
    have hlb : (lengths p (buffer p a).storage).getD b 0 = (buffer p b).size := by
      rw [lengths_getD p b hb.1]; simp [hs]
    simp only [bufferBase, ← hs] at hi
    rcases Nat.lt_or_gt_of_ne hab with hab | hba
    · have hm := wirePrefix_mono (lengths p (buffer p a).storage) a b hab (by simpa [lengths] using ha.1)
      rw [hla] at hm
      have := ha.2
      omega
    · have hm := wirePrefix_mono (lengths p (buffer p a).storage) b a hba (by simpa [lengths] using hb.1)
      rw [hlb] at hm
      have := hb.2
      omega

def Good (p : Program) (mem : Memory) : Prop :=
  mem.size = p.buffers.length ∧
    ∀ a < p.buffers.length, (mem.getD a #[]).size = (buffer p a).size

theorem applyWrite_get (mem : Memory) (a i : Nat) (v : Word)
    (ha : a < mem.size) (hi : i < (mem.getD a #[]).size) (b j : Nat) :
    ((applyWrite mem (a, i, v)).getD b #[]).getD j 0#64 =
      if a = b ∧ i = j then v else (mem.getD b #[]).getD j 0#64 := by
  by_cases hab : a = b
  · subst b
    simp only [applyWrite, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
      if_pos rfl, Array.getElem?_eq_getElem ha, Option.map_some, Option.getD_some]
    by_cases hij : i = j
    · subst j
      have hi' : i < (mem[a]'ha).size := by
        simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ha,
          Option.getD_some] using hi
      simp [Array.getElem?_setIfInBounds, hi']
    · simp [Array.getElem?_setIfInBounds, hij]
  · simp [applyWrite, Array.getD_eq_getD_getElem?, Array.getElem?_modify, hab]

def flatStore (flat : FlatMemory) (w : FlatWrite) : FlatMemory :=
  fun a => if a = w.1 then w.2 else flat a

def Represents (p : Program) (mem : Memory) (flat : FlatMemory) : Prop :=
  ∀ a i, Valid p a i → flat (address p a i) = (mem.getD a #[]).getD i 0#64

theorem applyWrite_good (p : Program) (mem : Memory) (w : Nat × Nat × Word)
    (hg : Good p mem) : Good p (applyWrite mem w) := by
  constructor
  · simpa [applyWrite] using hg.1
  · intro a ha
    have hm : a < mem.size := by rw [hg.1]; exact ha
    by_cases he : w.1 = a
    · subst a
      simpa [applyWrite, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
        Array.getElem?_eq_getElem hm] using hg.2 w.1 ha
    · simpa [applyWrite, Array.getD_eq_getD_getElem?, Array.getElem?_modify, he]
        using hg.2 a ha

theorem flatStore_sound (p : Program) (mem : Memory) (flat : FlatMemory)
    (a i : Nat) (v : Word) (hg : Good p mem) (hf : Represents p mem flat)
    (hv : Valid p a i) :
    Represents p (applyWrite mem (a, i, v)) (flatStore flat (address p a i, v)) := by
  intro b j hb
  have ha : a < mem.size := by rw [hg.1]; exact hv.1
  have hi : i < (mem.getD a #[]).size := by rw [hg.2 a hv.1]; exact hv.2
  rw [applyWrite_get mem a i v ha hi b j]
  by_cases he : address p b j = address p a i
  · obtain ⟨hab, hij⟩ := address_injective p b j a i hb hv he
    subst b; subst j
    simp [flatStore]
  · have hne : ¬(a = b ∧ i = j) := by
      rintro ⟨rfl, rfl⟩; exact he rfl
    simp only [flatStore, he, ite_false, hne]
    exact hf b j hb

def lowerLoads (p : Program) (flat : FlatMemory) (g l : Nat)
    (reads : List Read) (regs : Registers) : Registers :=
  reads.foldl (fun m r => m.insert r.dst (flat (address p r.array (r.index.eval g l)))) regs

theorem lowerLoads_eq (p : Program) (mem : Memory) (flat : FlatMemory) (g l : Nat)
    (reads : List Read) (regs : Registers) (hf : Represents p mem flat)
    (hv : ∀ r ∈ reads, Valid p r.array (r.index.eval g l)) :
    lowerLoads p flat g l reads regs = reads.foldl (fun m r => m.insert r.dst
      ((mem.getD r.array #[]).getD (r.index.eval g l) 0#64)) regs := by
  induction reads generalizing regs with
  | nil => rfl
  | cons r rs ih =>
    simp only [lowerLoads, List.foldl_cons]
    rw [hf r.array (r.index.eval g l) (hv r (by simp))]
    exact ih _ (fun r hr => hv r (by simp [hr]))

def lowerWrite (p : Program) (w : Nat × Nat × Word) : FlatWrite :=
  (address p w.1 w.2.1, w.2.2)

/-- The target independently loads flat addresses, executes registers, and writes
flat addresses. This is the model read by the generic WGSL emitter. -/
def lowerLaneWrites (p : Program) (ph : Phase) (flat : FlatMemory) (g l : Nat) : List FlatWrite :=
  let regs := runRegisters ph.code (lowerLoads p flat g l ph.reads ∅)
  ph.writes.map fun w => (address p w.array (w.index.eval g l), regs.getD w.value 0#64)

theorem lowerLaneWrites_sound (p : Program) (ph : Phase) (mem : Memory)
    (flat : FlatMemory) (g l : Nat) (hf : Represents p mem flat)
    (hv : ∀ r ∈ ph.reads, Valid p r.array (r.index.eval g l)) :
    lowerLaneWrites p ph flat g l = (laneWrites ph mem g l).map (lowerWrite p) := by
  unfold lowerLaneWrites
  rw [lowerLoads_eq p mem flat g l ph.reads ∅ hf hv]
  simp [laneWrites, loadRegisters, lowerWrite, List.map_map]

def phaseWrites (ph : Phase) (mem : Memory) (g : Nat) : List (Nat × Nat × Word) :=
  (List.range ph.lanes).flatMap (laneWrites ph mem g)

def lowerPhaseWrites (p : Program) (ph : Phase) (flat : FlatMemory) (g : Nat) : List FlatWrite :=
  (List.range ph.lanes).flatMap (lowerLaneWrites p ph flat g)

/-- All output addresses and values, for all lanes of every source map. This
is a universal translation theorem, not an NTT input-vector comparison. -/
theorem lowerPhaseWrites_sound (p : Program) (ph : Phase) (mem : Memory)
    (flat : FlatMemory) (g : Nat) (hf : Represents p mem flat)
    (hv : ∀ l < ph.lanes, ∀ r ∈ ph.reads, Valid p r.array (r.index.eval g l)) :
    lowerPhaseWrites p ph flat g = (phaseWrites ph mem g).map (lowerWrite p) := by
  simp only [lowerPhaseWrites, phaseWrites, List.map_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro l hl
  exact lowerLaneWrites_sound p ph mem flat g l hf (hv l (List.mem_range.mp hl))

theorem foldWrites_good (p : Program) (mem : Memory) (ws : List (Nat × Nat × Word))
    (hg : Good p mem) : Good p (ws.foldl applyWrite mem) := by
  induction ws generalizing mem with
  | nil => exact hg
  | cons w ws ih => exact ih _ (applyWrite_good p mem w hg)

theorem foldWrites_sound (p : Program) (mem : Memory) (flat : FlatMemory)
    (ws : List (Nat × Nat × Word)) (hg : Good p mem) (hf : Represents p mem flat)
    (hv : ∀ w ∈ ws, Valid p w.1 w.2.1) :
    Represents p (ws.foldl applyWrite mem) ((ws.map (lowerWrite p)).foldl flatStore flat) := by
  induction ws generalizing mem flat with
  | nil => exact hf
  | cons w ws ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ _ (applyWrite_good p mem w hg)
      (flatStore_sound p mem flat w.1 w.2.1 w.2.2 hg hf (hv w (by simp)))
      (fun w hw => hv w (by simp [hw]))

def lowerPhase (p : Program) (ph : Phase) (g : Nat) (flat : FlatMemory) : FlatMemory :=
  (lowerPhaseWrites p ph flat g).foldl flatStore flat

def PhaseInBounds (p : Program) (ph : Phase) (g : Nat) : Prop :=
  (∀ l < ph.lanes, ∀ r ∈ ph.reads, Valid p r.array (r.index.eval g l)) ∧
  (∀ l < ph.lanes, ∀ w ∈ ph.writes, Valid p w.array (w.index.eval g l))

/-- Full phase simulation: indexed array loads and all parallel results lower to
disjoint flat storage ranges, preserving every in-bounds array element. The
memory-model argument justifying simultaneous execution is separate (Workgroup).
-/
theorem lowerPhase_sound (p : Program) (ph : Phase) (mem : Memory)
    (flat : FlatMemory) (g : Nat) (hg : Good p mem) (hf : Represents p mem flat)
    (hb : PhaseInBounds p ph g) :
    Represents p (evalPhase ph g mem) (lowerPhase p ph g flat) := by
  unfold lowerPhase
  rw [lowerPhaseWrites_sound p ph mem flat g hf hb.1]
  apply foldWrites_sound p mem flat (phaseWrites ph mem g) hg hf
  intro w hw
  obtain ⟨l, hl, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v, hv, he⟩ := List.mem_map.mp hw
  subst w
  exact hb.2 l (List.mem_range.mp hl) v hv

def lowerPhases (p : Program) (phases : List Phase) (g : Nat) (flat : FlatMemory) : FlatMemory :=
  phases.foldl (fun f ph => lowerPhase p ph g f) flat

/-- Composition across every shared-memory exchange in an upload. -/
theorem lowerPhases_sound (p : Program) (phases : List Phase) (mem : Memory)
    (flat : FlatMemory) (g : Nat) (hg : Good p mem) (hf : Represents p mem flat)
    (hb : ∀ ph ∈ phases, PhaseInBounds p ph g) :
    Represents p (phases.foldl (fun m ph => evalPhase ph g m) mem)
      (lowerPhases p phases g flat) := by
  induction phases generalizing mem flat with
  | nil => exact hf
  | cons ph phases ih =>
    simp only [List.foldl_cons, lowerPhases]
    exact ih _ _ (foldWrites_good p mem (phaseWrites ph mem g) hg)
      (lowerPhase_sound p ph mem flat g hg hf (hb ph (by simp)))
      (fun ph h => hb ph (by simp [h]))

theorem evalGroup_good (p : Program) (d : Dispatch) (g : Nat) (mem : Memory)
    (hg : Good p mem) : Good p (evalGroup d g mem) := by
  unfold evalGroup
  induction d.phases generalizing mem with
  | nil => exact hg
  | cons ph phases ih =>
    exact ih _ (foldWrites_good p mem (phaseWrites ph mem g) hg)

/-- Simulation composes through a sequence of maps without requiring any
particular schedule length, lane count, radix, or arithmetic operation. -/
theorem fold_sim {α : Type} (p : Program) (xs : List α)
    (source : α → Memory → Memory) (target : α → FlatMemory → FlatMemory)
    (hs : ∀ x ∈ xs, ∀ m f, Good p m → Represents p m f →
      Good p (source x m) ∧ Represents p (source x m) (target x f))
    (mem : Memory) (flat : FlatMemory) (hg : Good p mem) (hf : Represents p mem flat) :
    Good p (xs.foldl (fun m x => source x m) mem) ∧
    Represents p (xs.foldl (fun m x => source x m) mem)
      (xs.foldl (fun f x => target x f) flat) := by
  induction xs generalizing mem flat with
  | nil => exact ⟨hg, hf⟩
  | cons x xs ih =>
    obtain ⟨hgood, hsim⟩ := hs x (by simp) mem flat hg hf
    exact ih (fun x hx => hs x (by simp [hx])) _ _ hgood hsim

def lowerDispatch (p : Program) (d : Dispatch) (flat : FlatMemory) : FlatMemory :=
  (List.range d.groups).foldl (fun f g => lowerPhases p d.phases g f) flat

def DispatchInBounds (p : Program) (d : Dispatch) : Prop :=
  ∀ g < d.groups, ∀ ph ∈ d.phases, PhaseInBounds p ph g

theorem boundsSafe_sound (p : Program) (h : p.boundsSafe = true) :
    ∀ d ∈ p.dispatches, DispatchInBounds p d := by
  simp only [Program.boundsSafe, List.all_eq_true, List.mem_range,
    Bool.and_eq_true, Program.accessSafe, decide_eq_true_eq] at h
  intro d hd g hg ph hph
  constructor
  · intro l hl r hr
    have hh := (h d hd g hg ph hph l hl).1 r hr
    exact ⟨hh.1.1, hh.2⟩
  · intro l hl w hw
    have hh := (h d hd g hg ph hph l hl).2 w hw
    exact ⟨hh.1.1, hh.2⟩

theorem lowerDispatch_sound (p : Program) (d : Dispatch) (mem : Memory)
    (flat : FlatMemory) (hg : Good p mem) (hf : Represents p mem flat)
    (hb : DispatchInBounds p d) :
    Good p (evalDispatch d mem) ∧
    Represents p (evalDispatch d mem) (lowerDispatch p d flat) := by
  apply fold_sim p (List.range d.groups) (evalGroup d)
    (fun g f => lowerPhases p d.phases g f) _ mem flat hg hf
  intro g h m f hm hmf
  exact ⟨evalGroup_good p d g m hm,
    lowerPhases_sound p d.phases m f g hm hmf (hb g (List.mem_range.mp h))⟩

def lowerProgram (p : Program) (flat : FlatMemory) : FlatMemory :=
  p.dispatches.foldl (fun f d => lowerDispatch p d f) flat

/-- Universal indexed-array to flat-storage lowering, through all phases,
workgroups, and ordered dispatches. Bounds are explicit and finite; the source
admission gate checks them alongside race and initialization conditions. -/
theorem lowerProgram_sound (p : Program) (mem : Memory) (flat : FlatMemory)
    (hg : Good p mem) (hf : Represents p mem flat)
    (hb : ∀ d ∈ p.dispatches, DispatchInBounds p d) :
    Represents p (evalProgram p mem) (lowerProgram p flat) := by
  exact (fold_sim p p.dispatches evalDispatch (lowerDispatch p)
    (fun d hd m f hm hmf => lowerDispatch_sound p d m f hm hmf (hb d hd))
    mem flat hg hf).2

/-- The exact executable admission gate supplies the bounds hypothesis of the
whole-program lowering theorem; callers do not provide a separate proof. -/
theorem checkedProgram_sound (p : Program) (mem : Memory) (flat : FlatMemory)
    (hg : Good p mem) (hf : Represents p mem flat) (hc : p.check = .ok ()) :
    Represents p (evalProgram p mem) (lowerProgram p flat) :=
  lowerProgram_sound p mem flat hg hf (boundsSafe_sound p (p.check_boundsSafe hc))

end Obend.Hardware.Gpu.BlockLower
