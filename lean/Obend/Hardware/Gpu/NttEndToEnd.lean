module
public import Obend.Hardware.Gpu.NttValue
public import Obend.Hardware.Gpu.NttSource
@[expose] public section
namespace Obend.Hardware.Gpu.NttSource
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.Ntt

/-- Composition boundary for the upload proof: the actual encoded Core4 source
and the admitted GPU lowering return the same natural-order DFT word. -/
theorem encoded_dft_of_uploads (bits : Nat) (hbits : bits ≤ 25) (hpos : 0 < bits)
    (input : Array Word) (hinput : input.size = 2^bits)
    (plan : BlockPlan.Plan) (hc : compile (2^bits) = .ok plan)
    (flat : FlatMemory)
    (hf : Represents (nttBlockProgram (2^bits))
      (initialMemory (nttBlockProgram (2^bits)) [input]) flat)
    (uploads : ∀ done degree current mem,
      degree ∈ uploadSchedule (2^bits) → done+degree ≤ bits → current ≤ 1 →
      BlockNtt.dispatch (2^bits) done degree current (1-current) ∈ (sourceUploads (2^bits)).1 →
      BlockLower.Good (nttBlockProgram (2^bits)) mem → TwiddleMemory (2^bits) mem →
      UploadDFT bits done degree current (1-current) mem)
    (i : Nat) (hi : i < 2^bits) :
    let value := dft (2^bits) (rootOfUnity (2^bits)) (fun j => (input.getD j 0#64).toNat) i
    Steps (BlockPlan.observe (program (2^bits))
      (BlockCoreEncoding.memory (initialMemory (nttBlockProgram (2^bits)) [input]))
      (sourceUploads (2^bits)).2 i) (.nat value) ∧
    ((lowerProgram (nttBlockProgram (2^bits)) flat)
      (address (nttBlockProgram (2^bits)) (sourceUploads (2^bits)).2 i)).toNat = value := by
  dsimp only
  have hg := initial_good (2^bits) input hinput
  have he := compile_source (2^bits) plan hc
  have hcheck : (nttBlockProgram (2^bits)).check = .ok () := he ▸ plan.checked
  have hv := output_valid (2^bits) i hi
  have hl := checkedProgram_sound (nttBlockProgram (2^bits)) _ flat hg hf hcheck
  have hvalue := program_value_of_uploads bits hbits hpos input hinput uploads i hi
  have htarget : ((lowerProgram (nttBlockProgram (2^bits)) flat)
      (address (nttBlockProgram (2^bits)) (sourceUploads (2^bits)).2 i)).toNat =
      dft (2^bits) (rootOfUnity (2^bits)) (fun j => (input.getD j 0#64).toNat) i := by
    rw [hl _ _ hv]
    exact hvalue
  constructor
  · have hs := source_to_gpu_encoded (2^bits) plan hc _ flat hg hf _ i hv
    rw [htarget] at hs
    exact hs
  · exact htarget

end Obend.Hardware.Gpu.NttSource
