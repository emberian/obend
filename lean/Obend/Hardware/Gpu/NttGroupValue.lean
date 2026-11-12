module
public import Obend.Hardware.Gpu.NttPackedValue
public import Obend.Hardware.Gpu.NttPhaseCoverage
@[expose] public section

namespace Obend.Hardware.Gpu.NttGroupValue
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.Gpu.NttDispatchGeometry Obend.Hardware.Gpu.NttPackedValue
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.GoldilocksSource
set_option autoImplicit false

def tileInput (total bits logP src G : Nat) (initial : Memory) : Nat → Nat :=
  preparedInput (2^total) (2^bits) (2^logP) G true
    (fun i => (valueAt initial src (G+i*(2^total/2^bits))).toNat)

def observed (bits logP stride tile G done input i : Nat) : Nat :=
  if done=bits then outputAddress (2^logP) (2^bits) G (reverseIndex bits i)
  else tileIndex stride tile input i

structure State (total bits logP src dst stride k group : Nat) (initial : Memory)
    (done input : Nat) (mem : Memory) : Prop where
  good : Good (nttBlockProgram (2^total)) mem
  table : ∀ i, i<2^total → (valueAt mem 4 i).toNat=modPow (rootOfUnity (2^total)) i
  source : ∀ i, valueAt mem src i=valueAt initial src i
  start : done=0 → input=src
  middle : 0<done → done<bits → input=2 ∨ input=3
  value : ∀ tile, tile<k → ∀ i, i<2^bits → 0<done →
    (valueAt mem input (observed bits logP stride tile (group*k+tile) done input i)).toNat =
      difStages bits 0 done (tileInput total bits logP src (group*k+tile) initial) i

theorem packed_row_frame (n bits p done degree src dst stride k group a : Nat)
    (first last : Bool) (mem : Memory) (ha : dst≠a) :
    (evalPhase (batchPhase stride k (phase n (2^bits) bits p done degree src dst first last)) group mem).getD a #[] =
      mem.getD a #[] := by
  apply evalPhase_row_frame
  intro w hw
  change w ∈ (phase n (2^bits) bits p done degree src dst first last).writes.map _ at hw
  obtain ⟨old,hold,he⟩ := List.mem_map.mp hw
  subst w
  change old.array ≠ a
  rw [phase_write_array n (2^bits) bits p done degree src dst first last old hold]
  exact ha

theorem state_step (total bits logP src dst stride k group : Nat) (initial : Memory)
    (ht : total≤32) (hp : logP+bits≤total) (hsrc : src≤1) (hdst : dst≤1) (hne : src≠dst)
    (hstride : 2^bits≤stride) (hshared : stride*k≤sharedWords (2^total))
    (hgroups : ∀ tile, tile<k → group*k+tile<2^total/2^bits)
    (done input chunk : Nat) (hc : 0<chunk) (_hc2 : chunk≤2) (hd : done+chunk≤bits)
    (mem : Memory) (hs : State total bits logP src dst stride k group initial done input mem) :
    State total bits logP src dst stride k group initial (done+chunk)
      (phaseOutput bits dst done input chunk)
      (evalPhase (batchPhase stride k
        (phase (2^total) (2^bits) bits (2^logP) done chunk input
          (phaseOutput bits dst done input chunk) (done==0) (done+chunk==bits))) group mem) := by
  let out := phaseOutput bits dst done input chunk
  let ph := batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done chunk input out
    (done==0) (done+chunk==bits))
  have hdone : done<bits := by omega
  have hin : input≤3 := by
    by_cases hz : done=0
    · rw [hs.start hz]; omega
    · rcases hs.middle (by omega) hdone with h | h <;> omega
  have hfirst : (done==0)=true → input≤1 := by
    intro h; rw [hs.start (by simpa using h)]; exact hsrc
  have hout : out=dst ∨ out=2 ∨ out=3 := by
    dsimp only [out,phaseOutput]
    split
    · exact Or.inl rfl
    · split <;> simp
  have hdevice : (done+chunk==bits)=true → out≤1 := by
    intro h; simpa only [out,phaseOutput,h,ite_true] using hdst
  have hlocal : (done+chunk==bits)=false → out=2 ∨ out=3 := by
    intro h; dsimp only [out,phaseOutput]; simp only [h,Bool.false_eq_true,ite_false]; split <;> simp
  have hsource : out≠src := by rcases hout with h | h | h <;> omega
  have hfour : out≠4 := by rcases hout with h | h | h <;> omega
  refine ⟨foldWrites_good _ mem (phaseWrites ph mem group) hs.good,?_,?_,?_,?_,?_⟩
  · intro i hi
    change ((evalPhase ph group mem).getD 4 #[] |>.getD i 0#64).toNat = _
    rw [packed_row_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfour]
    exact hs.table i hi
  · intro i
    change ((evalPhase ph group mem).getD src #[]).getD i 0#64 = _
    rw [packed_row_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsource]
    exact hs.source i
  · omega
  · intro _ hlt
    exact hlocal (by simp; omega)
  · intro tile htile i hi _
    obtain ⟨lane,hlane,r,hr,hindex⟩ := phase_index_cover bits done chunk i hd hi
    let entry : Nat → Nat := if done=0 then
      (fun i => (valueAt initial src (group*k+tile+i*(2^total/2^bits))).toNat)
      else difStages bits 0 done (tileInput total bits logP src (group*k+tile) initial)
    have hentry : ∀ j, j<2^bits →
        (valueAt (tileMemory stride tile mem) input
          (if (done==0) then group*k+tile+j*(2^total/2^bits) else j)).toNat=entry j := by
      intro j hj
      by_cases hz : done=0
      · have he := hs.start hz
        simp only [hz,beq_self_eq_true,ite_true,entry,he]
        rw [tileMemory_value _ _ _ _ _ (by omega)]
        have hh : (src==2 || src==3)=false := by simp; omega
        simp only [tileIndex,hh,Bool.false_eq_true,ite_false]
        rw [hs.source]
      · have hh : (done==0)=false := by simp [hz]
        simp only [hh,Bool.false_eq_true,ite_false,entry,if_neg hz]
        rw [tileMemory_value _ _ _ _ _ (by intro _; omega)]
        have hv := hs.value tile htile j hj (by omega)
        simpa only [observed,if_neg (by omega : done≠bits)] using hv
    have hcanonical : (done==0)=false → ∀ j, j<2^bits → entry j<goldilocksP := by
      intro hz j hj
      have hz' : done≠0 := by simpa using hz
      simp only [entry,if_neg hz']
      apply difStages_canonical bits 0 done (by omega) _ _ j hj
      exact preparedInput_canonical _ _ _ _ _ true _ (by simp)
    have hv := packed_phase_value total bits logP done chunk input out stride k group tile lane r
      (done==0) (done+chunk==bits) mem entry ht hp hd hin hfirst hstride hshared hdevice hlocal
      hgroups htile hlane hr hs.good hentry hcanonical hs.table
    have hidx := phase_index_lt bits done chunk lane r hd hlane hr
    rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ _ hidx,hindex] at hv
    have haddr : tileIndex stride tile out
        (if (done+chunk==bits) then outputAddress (2^logP) (2^bits) (group*k+tile) (reverseIndex bits i) else i) =
        observed bits logP stride tile (group*k+tile) (done+chunk) out i := by
      by_cases he : done+chunk=bits
      · have ho : out=dst := by simp [out,phaseOutput,he]
        have hh : (dst==2 || dst==3)=false := by simp; omega
        simp [he,observed,ho,tileIndex,hh]
      · simp [he,observed]
    change (valueAt (evalPhase ph group mem) out _).toNat = _ at hv
    unfold outputAddress at haddr
    rw [haddr] at hv
    rw [hv]
    by_cases hz : done=0
    · subst done
      simp only [entry,tileInput,Nat.zero_add,beq_self_eq_true,ite_true]
    · have hh : (done==0)=false := by simp [hz]
      simp only [preparedInput,hh,Bool.false_eq_true,ite_false,entry,if_neg hz]
      rw [difStages_fuse]
      simp only [Nat.zero_add]
      congr 2

/-- One actual packed workgroup computes every assigned tile's DFT. Scratch
memory is arbitrary apart from the ordinary row-size invariant. -/
theorem group_value (total logP bits src dst group : Nat) (mem : Memory)
    (ht : total≤32) (hp : logP+bits≤total) (hb : 0<bits)
    (hsrc : src≤1) (hdst : dst≤1) (hne : src≠dst)
    (hm : dispatch (2^total) logP bits src dst ∈ (sourceUploads (2^total)).1)
    (hgroup : group < (batchTiles (tileSize (dispatch (2^total) logP bits src dst))
      (dispatch (2^total) logP bits src dst)).groups)
    (hg : Good (nttBlockProgram (2^total)) mem)
    (htable : ∀ i, i<2^total → (valueAt mem 4 i).toNat=modPow (rootOfUnity (2^total)) i)
    (tile : Nat) (htile : tile<packing (dispatch (2^total) logP bits src dst))
    (r : Nat) (hr : r<2^bits) :
    (valueAt (evalGroup (batchTiles (tileSize (dispatch (2^total) logP bits src dst))
      (dispatch (2^total) logP bits src dst)) group mem) dst
      (outputAddress (2^logP) (2^bits)
        (group*packing (dispatch (2^total) logP bits src dst)+tile) r)).toNat =
      dft (2^bits) (rootOfUnity (2^bits))
        (tileInput total bits logP src
          (group*packing (dispatch (2^total) logP bits src dst)+tile) mem) r := by
  let d := dispatch (2^total) logP bits src dst
  let stride := tileSize d
  let k := packing d
  have hgroups : ∀ t, t<k → group*k+t<2^total/2^bits := by
    intro t ht
    exact packed_group_bound d group t hgroup ht
  have hs : State total bits logP src dst stride k group mem 0 src mem :=
    ⟨hg,htable,fun _ => rfl,fun _ => rfl,by omega,by omega⟩
  have hv := dispatch_phases_invariant (2^total) logP bits src dst stride group hb
    (State total bits logP src dst stride k group mem)
    (state_step total bits logP src dst stride k group mem ht hp hsrc hdst hne
      (dispatch_tileSize_lower _ _ _ _ _ hb) (sharedWords_covers _ _ hm) hgroups)
    mem hs
  have hval := hv.value tile htile (reverseIndex bits r) (reverseIndex_lt bits r hr) hb
  simp only [observed,ite_true,reverseIndex_involution bits r hr] at hval
  rw [hval]
  rw [difStages_eq_dft bits (by omega) _ _ _ (reverseIndex_lt bits r hr),
    reverseIndex_involution bits r hr]
  exact preparedInput_canonical _ _ _ _ _ true _ (by simp)

end Obend.Hardware.Gpu.NttGroupValue
end
