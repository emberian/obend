module
public import Obend.Hardware.Gpu.NttPhaseValue
public import Obend.Hardware.Gpu.NttDispatchGeometry
@[expose] public section

/-! Actual packed phase values, with all bounds and scatter obligations derived
from source metadata. No checker or computed-output premise is required. -/
namespace Obend.Hardware.Gpu.NttPackedValue
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.Gpu.NttDispatchGeometry Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.Gpu.PhaseSemantics Obend.Hardware.Gpu.GoldilocksSource
set_option autoImplicit false

theorem packed_phase_value (total bits logP done degree src dst stride k group tile lane r : Nat)
    (first last : Bool) (mem : Memory) (entry : Nat → Nat)
    (htotal : total≤32) (hp : logP+bits≤total) (hd : done+degree≤bits)
    (hsrc : src≤3) (hfirst : first=true → src≤1)
    (hstride : 2^bits≤stride) (hshared : stride*k≤sharedWords (2^total))
    (hdevice : last=true → dst≤1) (hlocal : last=false → dst=2 ∨ dst=3)
    (hgroups : ∀ t, t<k → group*k+t<2^total/2^bits)
    (htile : tile<k) (hlane : lane<2^bits/2^degree) (hr : r<2^degree)
    (hgood : Good (nttBlockProgram (2^total)) mem)
    (hentry : ∀ i, i<2^bits →
      (valueAt (tileMemory stride tile mem) src (if first then group*k+tile+i*(2^total/2^bits) else i)).toNat=entry i)
    (hcanonical : first=false → ∀ i, i<2^bits → entry i<goldilocksP)
    (htable : ∀ i, i<2^total → (valueAt mem 4 i).toNat=modPow (rootOfUnity (2^total)) i) :
    (valueAt (evalPhase (batchPhase stride k
      (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)) group mem) dst
      (tileIndex stride tile dst
        ((phaseSaveIndex (2^bits) bits (2^logP) (2^degree)
          (2^bits/(2^done*2^degree)) last r).eval (group*k+tile) lane))).toNat =
    difStages bits done degree
      (preparedInput (2^total) (2^bits) (2^logP) (group*k+tile) first entry)
      (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  let ph := phase (2^total) (2^bits) bits (2^logP) done degree src dst first last
  have hreads : TileReads stride k ph group tile lane (tileMemory stride tile mem) mem := by
    apply tileMemory_reads
    intro read hread ha
    have hb := PhaseMetadata.phase_read_index_bound total bits (2^logP) done degree src dst
      (group*k+tile) lane first last (by omega) hd (hgroups _ htile) hlane read hread
    rcases hb with ⟨harray,hi⟩ | ⟨harray,_⟩
    · have hf : first=false := by
        cases first
        · rfl
        · have := hfirst rfl; omega
      simp only [hf,Bool.false_eq_true,ite_false] at hi
      exact Nat.lt_of_lt_of_le hi hstride
    · omega
  have hv := evalPhase_batch_value (nttBlockProgram (2^total)) stride k ph group tile lane
    (tileMemory stride tile mem) mem hgood
    (packed_phase_inBounds total bits logP done degree src dst stride k group first last
      hp hd hsrc hfirst hstride hshared hdevice hlocal hgroups)
    (batch_phase_addresses_nodup (2^total) bits (2^logP) done degree src dst stride k first last
      group (Nat.two_pow_pos _) hd hstride hdevice hlocal)
    htile hlane hreads _ (phase_slot_write (2^total) (2^bits) bits (2^logP) done degree src dst first last r hr)
  rw [hv]
  apply phase_register_value total bits (2^logP) done degree src dst (group*k+tile) lane first last
    (tileMemory stride tile mem) entry htotal (by omega) (Nat.two_pow_pos _) hd
    (hgroups _ htile) hlane hentry hcanonical _ r hr
  intro i hi
  change (valueAt (tileMemory stride tile mem) 4 i).toNat = _
  rw [tileMemory_value stride tile mem 4 i (by omega)]
  exact htable i hi

end Obend.Hardware.Gpu.NttPackedValue
end
