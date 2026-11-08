module
public import Obend.Hardware.Gpu.Workgroup
public import Obend.Hardware.Gpu.BlockLower
@[expose] public section

/-!
The source protocol labels locations by all-buffer prefixes, while lowering uses separate physical
address spaces. On valid elements these are injective relabelings of the same array coordinates;
therefore the Vulkan trace and the emitted address model agree on every possible alias.
-/
namespace Obend.Hardware.Gpu.SourceProtocol
open Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Memory
set_option autoImplicit false

theorem arrayBase_eq_prefix (bs : List Buffer) (a : Nat) :
    Workgroup.arrayBase bs a = BlockLower.wirePrefix (bs.map (·.size)) a := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    cases a with
    | zero => rfl
    | succ a => simp only [Workgroup.arrayBase, List.map_cons, BlockLower.wirePrefix, ih]

/-- The protocol keeps constant buffers distinct from writable storage, even though both have
Vulkan storage-memory semantics. Their labels are not collapsed to their per-binding offsets. -/
theorem arrayLoc_injective (p : Program) (a i b j : Nat)
    (ha : BlockLower.Valid p a i) (hb : BlockLower.Valid p b j)
    (h : Workgroup.arrayLoc p.buffers a i = Workgroup.arrayLoc p.buffers b j) :
    a = b ∧ i = j := by
  have he := congrArg Loc.idx h
  change Workgroup.arrayBase p.buffers a + i = Workgroup.arrayBase p.buffers b + j at he
  rw [arrayBase_eq_prefix, arrayBase_eq_prefix] at he
  have hla : (p.buffers.map (·.size)).getD a 0 = (BlockLower.buffer p a).size := by
    simp [BlockLower.buffer, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ha.1]
  have hlb : (p.buffers.map (·.size)).getD b 0 = (BlockLower.buffer p b).size := by
    simp [BlockLower.buffer, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hb.1]
  by_cases hab : a = b
  · subst b
    exact ⟨rfl, by omega⟩
  · rcases Nat.lt_or_gt_of_ne hab with hab | hba
    · have hm := BlockLower.wirePrefix_mono (p.buffers.map (·.size)) a b hab
        (by simpa using ha.1)
      rw [hla] at hm
      have := ha.2
      omega
    · have hm := BlockLower.wirePrefix_mono (p.buffers.map (·.size)) b a hba
        (by simpa using hb.1)
      rw [hlb] at hm
      have := hb.2
      omega

/-- Exact alias correspondence between the G4 source trace and physical lowering. -/
theorem source_address_eq_iff (p : Program) (a i b j : Nat)
    (ha : BlockLower.Valid p a i) (hb : BlockLower.Valid p b j) :
    Workgroup.arrayLoc p.buffers a i = Workgroup.arrayLoc p.buffers b j ↔
      BlockLower.address p a i = BlockLower.address p b j := by
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := arrayLoc_injective p a i b j ha hb h
    rfl
  · intro h
    obtain ⟨rfl, rfl⟩ := BlockLower.address_injective p a i b j ha hb h
    rfl

/-- A value-independent event identity and its phase/location key. -/
structure Access where
  node : Nat
  key : Nat × Nat
  write : Bool

/-- Different storage classes get different keys. Nat arithmetic here cannot wrap. -/
def locationKey (l : Loc) : Nat := 2 * l.idx + if l.space == .workgroup then 1 else 0

def Compatible (a b : Access) : Prop := a.key = b.key → a.write = false ∧ b.write = false

/-- A write cannot share a phase/location with any previous access; a read cannot share one
with a previous write. Both sets are updated in place by the executable checker. -/
def separatedAux (seen writes : Std.HashSet (Nat × Nat)) : List Access → Bool
  | [] => true
  | a :: rest => !(writes.contains a.key) && (!a.write || !(seen.contains a.key)) &&
      separatedAux (seen.insert a.key) (if a.write then writes.insert a.key else writes) rest

private theorem separatedAux_sound (xs : List Access) (seen writes : Std.HashSet (Nat × Nat))
    (h : separatedAux seen writes xs = true) :
    xs.Pairwise Compatible ∧
      ∀ a ∈ xs, writes.contains a.key = false ∧ (a.write = true → seen.contains a.key = false) := by
  induction xs generalizing seen writes with
  | nil => simp
  | cons a xs ih =>
    simp only [separatedAux, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
    have hr := ih (seen.insert a.key) (if a.write then writes.insert a.key else writes) h.2
    refine ⟨List.pairwise_cons.mpr ⟨?_, hr.1⟩, ?_⟩
    · intro b hb heq
      have hb' := hr.2 b hb
      have haFalse : a.write = false := by
        cases ha : a.write with
        | false => rfl
        | true =>
          have hf := hb'.1
          simp [ha, ← heq] at hf
      have hbFalse : b.write = false := by
        cases hbWrite : b.write with
        | false => rfl
        | true =>
          have hf := hb'.2 hbWrite
          simp [← heq] at hf
      exact ⟨haFalse, hbFalse⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · refine ⟨h.1.1, ?_⟩
        intro ha
        rcases h.1.2 with hf | hf
        · rw [ha] at hf; contradiction
        · exact hf
      · have hb' := hr.2 b hb
        constructor
        · cases ha : a.write with
          | false => simpa [ha] using hb'.1
          | true =>
            have hf := hb'.1
            simp only [ha, ↓reduceIte, Std.HashSet.contains_insert,
              Bool.or_eq_false_iff] at hf
            exact hf.2
        · intro hw
          have hf := hb'.2 hw
          simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at hf
          exact hf.2

private theorem compatible_symm (a b : Access) (h : Compatible a b) : Compatible b a :=
  fun heq => (h heq.symm).symm

private theorem pairwise_compatible_mem (xs : List Access) (h : xs.Pairwise Compatible)
    (a b : Access) (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : Compatible a b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hx, hs⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with hax | haTail
    · subst a
      rcases List.mem_cons.mp hb with hbx | hbTail
      · exact False.elim (hne hbx.symm)
      · exact hx b hbTail
    · rcases List.mem_cons.mp hb with hbx | hbTail
      · subst b
        exact compatible_symm x a (hx a haTail)
      · exact ih hs haTail hbTail

/-- Read G4 nodes through the certified Array implementation. This does not construct any of G4's
quadratic relations and does not evaluate arithmetic values. -/
def accesses (P : Shape) (c : Workgroup.PhaseLayout) : List Access :=
  let ns := Workgroup.nodesFast P
  (List.range ns.size).filterMap fun a =>
    let n := ns[a]?.getD default
    n.ev.loc?.map fun l => ⟨a, (c.phase a, locationKey l), n.ev.isWrite⟩

def separatedFast (P : Shape) (c : Workgroup.PhaseLayout) : Bool :=
  separatedAux ∅ ∅ (accesses P c)

private theorem access_mem (P : Shape) (c : Workgroup.PhaseLayout) (a : Nat) (l : Loc)
    (ha : a < P.nodes.length) (hl : (P.nodes.getD a default).ev.loc? = some l) :
    ⟨a, (c.phase a, locationKey l), (P.nodes.getD a default).ev.isWrite⟩ ∈ accesses P c := by
  apply List.mem_filterMap.mpr
  refine ⟨a, ?_, ?_⟩
  · simpa [Workgroup.nodesFast_eq] using List.mem_range.mpr ha
  · simpa [Workgroup.nodesFast_eq, List.getD_eq_getElem?_getD, hl] using
      congrArg (Option.map fun l =>
        (⟨a, (c.phase a, locationKey l), (P.nodes.getD a default).ev.isWrite⟩ : Access)) hl

/-- The linear-time executable checker establishes exactly the phase separation hypothesis used
by G4's race-freedom theorem, for arbitrary event values and arbitrary phase layouts. -/
theorem separatedFast_sound (P : Shape) (c : Workgroup.PhaseLayout)
    (h : separatedFast P c = true) : c.Separated P := by
  have hp := (separatedAux_sound (accesses P c) ∅ ∅ h).1
  intro a ha b hb hne hloc hw
  have haBound : a < P.nodes.length := List.mem_range.mp (List.mem_filter.mp ha).1
  have hbBound : b < P.nodes.length := List.mem_range.mp (List.mem_filter.mp hb).1
  have haMem : (P.nodes.getD a default).ev.loc?.isSome = true := (List.mem_filter.mp ha).2
  have hbMem : (P.nodes.getD b default).ev.loc?.isSome = true := (List.mem_filter.mp hb).2
  cases hla : (P.nodes.getD a default).ev.loc? with
  | none => simp only [hla, Option.isSome_none, Bool.false_eq_true] at haMem
  | some la =>
    cases hlb : (P.nodes.getD b default).ev.loc? with
    | none => simp only [hlb, Option.isSome_none, Bool.false_eq_true] at hbMem
    | some lb =>
      have heqLoc : la = lb := by
        change (P.nodes.getD a default).sameLoc (P.nodes.getD b default) = true at hloc
        simpa only [Node.sameLoc, hla, hlb, beq_iff_eq] using hloc
      subst lb
      have hcomp := pairwise_compatible_mem (accesses P c) hp
        ⟨a, (c.phase a, locationKey la), (P.nodes.getD a default).ev.isWrite⟩
        ⟨b, (c.phase b, locationKey la), (P.nodes.getD b default).ev.isWrite⟩
        (access_mem P c a la haBound hla) (access_mem P c b la hbBound hlb)
        (fun he => hne (congrArg Access.node he))
      intro hphase
      have hf := hcomp (by simp [hphase])
      have hfa : (P.nodes.getD a default).ev.isWrite = false := hf.1
      have hfb : (P.nodes.getD b default).ev.isWrite = false := hf.2
      rw [hfa, hfb] at hw
      contradiction

/-- Mandatory protocol admission for the emitter. Checks the actual physical-lane assignment and
both barrier instances, with no arithmetic evaluation and no Vulkan relation enumeration. -/
def checkProgram (p : Program) (width : Nat := 64) : Bool :=
  p.dispatches.all fun d => (List.range d.groups).all fun group =>
    let protocol := Workgroup.sourceProtocolTrace p d group width
    let layout := Workgroup.sourceProtocolLayout p d group width
    layout.geometryFast protocol && separatedFast protocol layout

/-- Each admitted group supplies the exact structural premises consumed by the G4 rules. -/
theorem checkProgram_group (p : Program) (width : Nat) (h : checkProgram p width = true)
    (d : Dispatch) (hd : d ∈ p.dispatches) (group : Nat) (hg : group < d.groups) :
    let protocol := Workgroup.sourceProtocolTrace p d group width
    let layout := Workgroup.sourceProtocolLayout p d group width
    layout.geometryFast protocol = true ∧ layout.Separated protocol := by
  simp only [checkProgram, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  have hs := h d hd group hg
  exact ⟨hs.1, separatedFast_sound _ _ hs.2⟩

/-- Admission of the concrete schedule establishes race freedom for every workgroup and every
memory input, using the existing Vulkan G4 relation rather than a separate memory model. -/
theorem checkProgram_not_racy (p : Program) (width : Nat) (h : checkProgram p width = true)
    (d : Dispatch) (hd : d ∈ p.dispatches) (group : Nat) (hg : group < d.groups) (mem : Memory) :
    (Workgroup.sourceTrace p d mem group width).static.racy = false := by
  have hs := checkProgram_group p width h d hd group hg
  exact Workgroup.sourceTrace_not_racy p d mem group width
    (Workgroup.sourceProtocolLayout p d group width) hs.1 hs.2

/-- The same mandatory admission establishes sequential read visibility in every well-formed,
Vulkan-consistent execution. The preceding writer is selected from phase numbers by the theorem;
no per-input outcome, latest-write certificate, or happens-before fact is assumed. -/
theorem checkProgram_read_sequential (p : Program) (width : Nat) (h : checkProgram p width = true)
    (d : Dispatch) (hd : d ∈ p.dispatches) (group : Nat) (hg : group < d.groups)
    (mem : Memory) (w : List Nat) (r : Nat)
    (hw : Wf w (Workgroup.sourceTrace p d mem group width).spec)
    (hc : (Workgroup.sourceTrace p d mem group width).consistent w = true)
    (hr : r ∈ (Workgroup.sourceTrace p d mem group width).static.reads)
    (hplain : ((Workgroup.sourceTrace p d mem group width).nodes.getD r default).ev.isWrite = false) :
    (Workgroup.sourceTrace p d mem group width).static.valueOfRead w r =
      Workgroup.phaseReadValue (Workgroup.sourceTrace p d mem group width)
        (Workgroup.sourceProtocolLayout p d group width) w r := by
  have hs := checkProgram_group p width h d hd group hg
  exact Workgroup.sourceTrace_read_sequential p d mem group width
    (Workgroup.sourceProtocolLayout p d group width) w r hs.1 hs.2 hw hc hr hplain

end Obend.Hardware.Gpu.SourceProtocol
