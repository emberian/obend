module
public import Obend.Hardware.Gpu.NttPhaseReads
public import Obend.Hardware.Gpu.NttBatchCorrect
public import Obend.Hardware.Gpu.NttMemory
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open ArrayKernel BlockNtt PhaseMetadata
open NttBatchCorrect BlockLower

/-- Read bounds of the actual packed source phase in the actual NTT buffers.
The proof derives the original invocation and read form from emitted metadata. -/
theorem packed_phase_reads_valid (total bits p done degree src dst stride k group : Nat)
    (first last : Bool) (hb : bits ≤ total) (hdegree : done+degree ≤ bits)
    (hsrc : src ≤ 3) (hfirst : first=true → src ≤ 1)
    (hstride : 2^bits ≤ stride) (hshared : stride*k ≤ sharedWords (2^total))
    (hgroups : ∀ tile, tile<k → group*k+tile < 2^total/2^bits) :
    ∀ lane < (batchPhase stride k (phase (2^total) (2^bits) bits p done degree src dst first last)).lanes,
      ∀ r ∈ (batchPhase stride k (phase (2^total) (2^bits) bits p done degree src dst first last)).reads,
        Valid (nttBlockProgram (2^total)) r.array (r.index.eval group lane) := by
  intro lane hl r hr
  let lanes := 2^bits/2^degree
  change lane < lanes*k at hl
  have hlanes : 0 < lanes := by
    dsimp only [lanes]
    rw [Nat.pow_div (by omega) (by decide)]
    exact Nat.two_pow_pos _
  have htile : lane/lanes < k := (Nat.div_lt_iff_lt_mul hlanes).mpr (by simpa [Nat.mul_comm] using hl)
  have hlane := Nat.mod_lt lane hlanes
  obtain ⟨read,hread,rfl⟩ := List.mem_map.mp hr
  change Valid _ read.array ((batchIndex stride k lanes read.array read.index).eval group lane)
  rw [batchIndex_eval]
  have hbound := phase_read_index_bound total bits p done degree src dst (group*k+lane/lanes)
    (lane%lanes) first last hb hdegree (hgroups _ htile) hlane read hread
  rcases hbound with ⟨ha,hi⟩ | ⟨ha,hi⟩
  · rw [ha]
    have hcases : src=0 ∨ src=1 ∨ src=2 ∨ src=3 := by omega
    rcases hcases with hzero | hone | htwo | hthree
    · have hsize : (if first then 2^total else 2^bits) ≤ 2^total := by
        split
        · exact Nat.le_refl _
        · exact Nat.pow_le_pow_of_le (by decide) hb
      have hi' := Nat.lt_of_lt_of_le hi hsize
      simpa [hzero,Valid,buffer,nttBlockProgram,tileIndex] using hi'
    · have hsize : (if first then 2^total else 2^bits) ≤ 2^total := by
        split
        · exact Nat.le_refl _
        · exact Nat.pow_le_pow_of_le (by decide) hb
      have hi' := Nat.lt_of_lt_of_le hi hsize
      simpa [hone,Valid,buffer,nttBlockProgram,tileIndex] using hi'
    all_goals
      have hf : first=false := by
        cases first
        · rfl
        · have := hfirst rfl; omega
      simp only [hf,Bool.false_eq_true,ite_false] at hi
      have hi' : read.index.eval (group*k+lane/lanes) (lane%lanes) < stride := Nat.lt_of_lt_of_le hi hstride
      have hp := Nat.mul_le_mul_right stride (by omega : lane/lanes+1 ≤ k)
      rw [Nat.add_mul,Nat.one_mul] at hp
      have hout : read.index.eval (group*k+lane/lanes) (lane%lanes)+(lane/lanes)*stride < sharedWords (2^total) := by
        rw [Nat.mul_comm stride k] at hshared
        omega
      first
      | simpa [htwo,Valid,buffer,nttBlockProgram,tileIndex] using hout
      | simpa [hthree,Valid,buffer,nttBlockProgram,tileIndex] using hout
  · rw [ha]
    simpa [Valid,buffer,nttBlockProgram,tileIndex] using hi

end Obend.Hardware.Gpu.Ntt
