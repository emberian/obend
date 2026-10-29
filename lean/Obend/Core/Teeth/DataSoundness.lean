/-
# Obend.Core.Teeth.DataSoundness — the executed teeth over `sampleRecord` (legacy leaf)

Not a `module`: `decide +kernel` here runs the demand machine on `sampleRecord` through `executeWith`,
which runs `Array` functions whose bodies Lean v4.30.0's `Init` does not expose to `module` files
(`Obend.Core.Teeth.Collect` says the same). The two `source_semantics` theorems consume the two executed
teeth and move with them; `sampleRecord_data`, which needs no run, stays in `Obend.Core.Proofs.DataSoundness`.
-/
import Obend.Core.Proofs.DataSoundness
import Obend.AxiomPin

namespace Obend.Core.Proofs.DataSoundness
open Obend.Core.Term Obend.Core.Machine Obend.Core.Data Obend.Core.Invariant

public theorem sampleRecord_executes :
    (executeWith (fun _ => true) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord).toBool = true := by decide +kernel

public theorem sampleRecord_source_semantics :
    ∃ execution : ExecutionWith (fun _ => true) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord,
      DeepEvaluates sampleRecord execution.extraction.result.value := by
  cases executed : executeWith (fun _ => true) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord with
  | error failure =>
      have ok := sampleRecord_executes
      rw [executed] at ok
      cases ok
  | ok execution => exact ⟨execution,(execution_deepEvaluates sampleRecord_closed execution).2⟩

/-- The same program under the native scalar capacity profile (64-bit). -/
public theorem sampleRecord_executes_native :
    (executeWith (Obend.Core.Capacity.allows ⟨64⟩) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord).toBool = true := by
  decide +kernel

public theorem sampleRecord_native_source_semantics :
    ∃ execution : ExecutionWith (Obend.Core.Capacity.allows ⟨64⟩) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord,
      runBounded ⟨16,16⟩ 64 (initial sampleRecord) = .finished execution.value execution.state ∧
      DeepEvaluates sampleRecord execution.extraction.result.value := by
  cases executed : executeWith (Obend.Core.Capacity.allows ⟨64⟩) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord with
  | error failure =>
      have ok := sampleRecord_executes_native
      rw [executed] at ok
      cases ok
  | ok execution => exact ⟨execution,execution_deepEvaluates sampleRecord_closed execution⟩


#assert_axioms sampleRecord_executes sampleRecord_source_semantics sampleRecord_executes_native
  sampleRecord_native_source_semantics

end Obend.Core.Proofs.DataSoundness
