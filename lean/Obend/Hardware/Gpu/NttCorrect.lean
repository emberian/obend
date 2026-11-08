module
public import Obend.Hardware.Gpu.NttDispatchValue
public import Obend.Hardware.Gpu.NttEndToEnd
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.PhaseSemantics

theorem output_port (n : Nat) : (nttBlockProgram n).outputs.getD 0 0 = (sourceUploads n).2 := by
  simp [nttBlockProgram]

/-- Every supported power-of-two transform, every input word and every output
coordinate: the actual source evaluator is the natural-order Goldilocks DFT.
There is no admission, computed-output, or finite-size certificate premise. -/
theorem nttBlockProgram_dft_power (bits : Nat) (hbits : bits ≤ 25) (hpos : 0 < bits)
    (input : Array Word) (hinput : input.size = 2^bits) (i : Nat) (hi : i < 2^bits) :
    (valueAt (evalProgram (nttBlockProgram (2^bits))
      (initialMemory (nttBlockProgram (2^bits)) [input])) (sourceUploads (2^bits)).2 i).toNat =
      dft (2^bits) (rootOfUnity (2^bits)) (fun j => (input.getD j 0#64).toNat) i := by
  apply program_value_of_uploads bits hbits hpos input hinput
  · intro done degree current mem hdegree hdone hcurrent hmember hgood htable
    exact NttDispatchValue.upload_dft bits done degree current (1-current) mem
      (by omega) hdone (uploadSchedule_bounds (2^bits) degree hdegree).1
      hcurrent (by omega) (by omega) hmember hgood htable
  · exact hi

/-- Universal equality at the actual declared output port, for exactly the
size domain accepted by the NTT source frontend. Inputs may be noncanonical. -/
theorem nttBlockProgram_dft (n : Nat) (hn : NttSource.Supported n)
    (input : Array Word) (hinput : input.size = n) (i : Nat) (hi : i < n) :
    (valueAt (evalProgram (nttBlockProgram n) (initialMemory (nttBlockProgram n) [input]))
      ((nttBlockProgram n).outputs.getD 0 0) i).toNat =
      dft n (rootOfUnity n) (fun j => (input.getD j 0#64).toNat) i := by
  have hk := NttSource.supported_log n hn
  have h := nttBlockProgram_dft_power (Nat.log2 n) hk.2 hk.1 input
    (by simpa only [← hn.2.1] using hinput) i (by simpa only [← hn.2.1] using hi)
  simpa only [← hn.2.1,output_port] using h

end Obend.Hardware.Gpu.Ntt

namespace Obend.Hardware.Gpu.NttSource
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.Ntt

/-- The actual encoded block source and its admitted general GPU lowering both
return the DFT. The remaining premises describe input shape, source admission
and the flat-memory representation, never an answer or transform property. -/
theorem source_to_gpu_dft_encoded (n : Nat) (plan : BlockPlan.Plan) (hc : compile n = .ok plan)
    (input : Array Word) (hinput : input.size = n) (flat : FlatMemory)
    (hf : Represents (nttBlockProgram n) (initialMemory (nttBlockProgram n) [input]) flat)
    (i : Nat) (hi : i < n) :
    let value := dft n (rootOfUnity n) (fun j => (input.getD j 0#64).toNat) i
    Steps (BlockPlan.observe (program n)
      (BlockCoreEncoding.memory (initialMemory (nttBlockProgram n) [input]))
      ((nttBlockProgram n).outputs.getD 0 0) i) (.nat value) ∧
    ((lowerProgram (nttBlockProgram n) flat)
      (address (nttBlockProgram n) ((nttBlockProgram n).outputs.getD 0 0) i)).toNat = value := by
  dsimp only
  simp only [output_port]
  have hg := initial_good n input hinput
  have he := compile_source n plan hc
  have hcheck : (nttBlockProgram n).check = .ok () := he ▸ plan.checked
  have hv := output_valid n i hi
  have hl := checkedProgram_sound (nttBlockProgram n) _ flat hg hf hcheck
  have hvalue := nttBlockProgram_dft n (compile_supported n plan hc) input hinput i hi
  rw [output_port] at hvalue
  have htarget : ((lowerProgram (nttBlockProgram n) flat)
      (address (nttBlockProgram n) (sourceUploads n).2 i)).toNat =
      dft n (rootOfUnity n) (fun j => (input.getD j 0#64).toNat) i := by
    rw [hl _ _ hv]
    exact hvalue
  constructor
  · have hs := source_to_gpu_encoded n plan hc _ flat hg hf _ i hv
    rw [htarget] at hs
    exact hs
  · exact htarget

end Obend.Hardware.Gpu.NttSource
