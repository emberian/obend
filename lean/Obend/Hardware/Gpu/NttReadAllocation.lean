module
public import Obend.Hardware.Gpu.NttPhaseReads
public import Obend.Hardware.Gpu.NttFieldCorrect
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt.PhaseMetadata
open ArrayKernel ArrayBuild GoldilocksSource BlockNtt
open GoldilocksSourceCorrect NttFieldCorrect

/-- Actual loaded registers are distinct and have already been allocated. -/
structure ReadAllocation (st : Build) (reads : List Read) : Prop where
  unique : (reads.map Read.dst).Nodup
  bound : ∀ r, r ∈ reads → r.dst < st.lengths.size

theorem ReadAllocation.mono {before after : Build} {reads : List Read}
    (h : ReadAllocation before reads) (he : BuildExtends before after) : ReadAllocation after reads :=
  ⟨h.unique,fun r hr => Nat.lt_of_lt_of_le (h.bound r hr) he.size_le⟩

theorem ReadAllocation.append {before after : Build} {reads : List Read}
    (h : ReadAllocation before reads) (he : BuildExtends before after) (r : Read)
    (fresh : before.lengths.size ≤ r.dst) (bound : r.dst < after.lengths.size) :
    ReadAllocation after (reads++[r]) := by
  constructor
  · rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨h.unique,by simp,?_⟩
    intro a ha b hb
    obtain ⟨read,hm,rfl⟩ := List.mem_map.mp ha
    have hbr : b=r.dst := by simpa using hb
    have hlt := h.bound read hm
    omega
  · intro read hr
    rcases List.mem_append.mp hr with hr | hr
    · exact Nat.lt_of_lt_of_le (h.bound read hr) he.size_le
    · have : read=r := by simpa using hr
      subst read
      exact bound

theorem load_allocation (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build)
    (h : ReadAllocation st s.1) :
    ReadAllocation ((forIn xs s (loadBody src index)).run st).2
      ((forIn xs s (loadBody src index)).run st).1.1 := by
  apply forIn_state_preserves xs _ (fun ss state => ReadAllocation state ss.1) _ s st h
  intro slot ss state hs
  simp only [loadBody,PhaseMetadata.bind_run,PhaseMetadata.pure_run,ForInStep.value]
  apply hs.append (newWire_extends state 1)
  · simp [newWire_run]
  · simp [newWire_run]

theorem canon_allocation (k : GlConsts) (xs : List Nat) (regs : Array Nat) (reads : List Read)
    (st : Build) (h : ReadAllocation st reads) :
    ReadAllocation ((forIn xs regs (canonBody k)).run st).2 reads := by
  apply forIn_state_preserves xs _ (fun _ state => ReadAllocation state reads) _ regs st h
  intro slot rs state hs
  simp only [canonBody,PhaseMetadata.bind_run,PhaseMetadata.pure_run]
  exact hs.mono (glCanon_extends state 1 k rs[slot]!)

theorem input_allocation (n count p radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) (h : ReadAllocation st s.1) :
    ReadAllocation ((forIn xs s (inputBody n count p radix stride k)).run st).2
      ((forIn xs s (inputBody n count p radix stride k)).run st).1.1 := by
  apply forIn_state_preserves xs _ (fun ss state => ReadAllocation state ss.1) _ s st h
  intro slot ss state hs
  simp only [inputBody,PhaseMetadata.bind_run,PhaseMetadata.pure_run,ForInStep.value]
  have hn := newWire_extends state 1
  have hm := glMul_extends ((newWire 1).run state).2 1 k ss.2[slot]! ((newWire 1).run state).1
  apply hs.append (hn.trans hm)
  · simp [newWire_run]
  · have hb : ((newWire 1).run state).1 < ((newWire 1).run state).2.lengths.size := by simp [newWire_run]
    exact Nat.lt_of_lt_of_le hb hm.size_le

theorem butterfly_read_bounds (k : GlConsts) (a b : Nat) (twiddle : Option Ix) (st : Build)
    (r : Read) (hr : ((butterfly k a b twiddle).run st).1.read=some r) :
    st.lengths.size ≤ r.dst ∧ r.dst < ((butterfly k a b twiddle).run st).2.lengths.size := by
  have hc := butterfly_coordinates st k a b twiddle
  dsimp only at hc
  rw [hc.2.2.2] at hr
  cases twiddle with
  | none => cases hr
  | some index =>
    simp only [Option.map_some,Option.some.injEq] at hr
    rw [←hr]
    simp only [Option.isSome_some,Bool.true_eq,ite_true] at hc
    constructor <;> dsimp only <;> omega

theorem pair_allocation (n count done radix stride : Nat) (k : GlConsts) (round j : Nat)
    (s : PairState) (st : Build) (h : ReadAllocation st s.1) :
    ReadAllocation ((pairBody n count done radix stride k round j s).run st).2
      ((pairBody n count done radix stride k round j s).run st).1.value.1 := by
  simp only [pairBody,PhaseMetadata.bind_run]
  split
  · exact h.mono (butterfly_extends _ _ _ _ _)
  · rename_i r hr
    have hb := butterfly_read_bounds _ _ _ _ _ r hr
    exact h.append (butterfly_extends _ _ _ _ _) r hb.1 hb.2

theorem rounds_allocation (n count done radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) (h : ReadAllocation st s.1) :
    ReadAllocation ((forIn xs s (roundBody n count done radix stride k)).run st).2
      ((forIn xs s (roundBody n count done radix stride k)).run st).1.1 := by
  apply forIn_state_preserves xs _ (fun ss state => ReadAllocation state ss.1) _ s st h
  intro round ss state hs
  simp only [roundBody,PhaseMetadata.bind_run,PhaseMetadata.pure_run,ForInStep.value]
  apply forIn_state_preserves (List.range (radix/2)) _ (fun ss state => ReadAllocation state ss.1) _ ss state hs
  exact fun j ss state hs => pair_allocation n count done radix stride k round j ss state hs

/-- Fresh read destinations are an unconditional fact of actual phase construction. -/
theorem phaseAction_allocation (n count p done degree src : Nat) (first : Bool) (st : Build) :
    ReadAllocation ((phaseAction n count p done degree src first).run st).2
      ((phaseAction n count p done degree src first).run st).1.1 := by
  let radix := 2^degree
  let stride := count/(2^done*radix)
  let loaded := (forIn (List.range radix) ([],#[])
    (loadBody src (phaseLoadIndex n count radix stride first))).run st
  have hl : ReadAllocation loaded.2 loaded.1.1 :=
    load_allocation src _ _ ([],#[]) st ⟨by simp,by intro r hr; cases hr⟩
  let constants := (glConsts 1).run loaded.2
  have hk : ReadAllocation constants.2 loaded.1.1 := hl.mono (glConsts_extends loaded.2 1 (by decide))
  let canonical := if first && p==1 then
    (forIn (List.range radix) loaded.1.2 (canonBody constants.1)).run constants.2
    else (loaded.1.2,constants.2)
  have hc : ReadAllocation canonical.2 loaded.1.1 := by
    dsimp only [canonical]
    split
    · exact canon_allocation _ _ _ _ _ hk
    · exact hk
  let twisted := if first && p>1 then
    (forIn (List.range radix) (loaded.1.1,canonical.1)
      (inputBody n count p radix stride constants.1)).run canonical.2
    else ((loaded.1.1,canonical.1),canonical.2)
  have ht : ReadAllocation twisted.2 twisted.1.1 := by
    dsimp only [twisted]
    split
    · exact input_allocation _ _ _ _ _ _ _ _ _ hc
    · exact hc
  let transformed := (forIn (List.range degree) twisted.1
    (roundBody n count done radix stride constants.1)).run twisted.2
  have hf : ReadAllocation transformed.2 transformed.1.1 := rounds_allocation _ _ _ _ _ _ _ _ _ ht
  rw [phaseAction_run]
  exact hf

theorem phase_reads_unique (n count bits p done degree src dst : Nat) (first last : Bool) :
    ((phase n count bits p done degree src dst first last).reads.map Read.dst).Nodup :=
  (phaseAction_allocation n count p done degree src first {}).unique

private theorem loadFold_frame (reads : List Read) (mem : Memory) (group lane key : Nat)
    (regs : Registers) (h : ∀ r, r ∈ reads → r.dst ≠ key) :
    (reads.foldl (fun regs r => regs.insert r.dst
      ((mem.getD r.array #[]).getD (r.index.eval group lane) 0#64)) regs).getD key 0#64 = regs.getD key 0#64 := by
  induction reads generalizing regs with
  | nil => rfl
  | cons r reads ih =>
    rw [List.foldl_cons,ih _ (fun rr hr => h rr (by simp [hr]))]
    have hn := h r (by simp)
    simp [Std.HashMap.getD_insert,hn,Ne.symm hn]

private theorem loadFold_member (reads : List Read) (mem : Memory) (group lane : Nat)
    (regs : Registers) (hu : (reads.map Read.dst).Nodup)
    (r : Read) (hr : r ∈ reads) :
    (reads.foldl (fun regs r => regs.insert r.dst
      ((mem.getD r.array #[]).getD (r.index.eval group lane) 0#64)) regs).getD r.dst 0#64 =
      (mem.getD r.array #[]).getD (r.index.eval group lane) 0#64 := by
  induction reads generalizing regs with
  | nil => cases hr
  | cons read reads ih =>
    simp only [List.map_cons,List.nodup_cons] at hu
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with h | h
    · subst r
      rw [loadFold_frame reads mem group lane read.dst _ (by
        intro r hr he
        apply hu.1
        exact List.mem_map.mpr ⟨r,hr,he⟩)]
      simp [Std.HashMap.getD_insert]
    · exact ih _ hu.2 h

/-- Every actual declared load is visible at its register in the phase's real
HashMap loader. Freshness prevents later reads from overwriting that binding. -/
theorem phase_loadRegisters_value (n count bits p done degree src dst : Nat) (first last : Bool)
    (mem : Memory) (group lane : Nat) (r : Read)
    (hr : r ∈ (phase n count bits p done degree src dst first last).reads) :
    (loadRegisters (phase n count bits p done degree src dst first last) mem group lane).getD r.dst 0#64 =
      (mem.getD r.array #[]).getD (r.index.eval group lane) 0#64 := by
  exact loadFold_member _ mem group lane ∅ (phase_reads_unique n count bits p done degree src dst first last) r hr

end Obend.Hardware.Gpu.Ntt.PhaseMetadata
