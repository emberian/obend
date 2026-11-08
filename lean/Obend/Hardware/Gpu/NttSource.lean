module
public import Obend.Hardware.Gpu.Ntt
public import Obend.Hardware.Gpu.BlockPlan
@[expose] public section
namespace Obend.Hardware.Gpu.NttSource
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

/-- The sole NTT's declared size domain. -/
def Supported (n : Nat) : Prop := 2 ≤ n ∧ n = 2^(Nat.log2 n) ∧ n < 2^26
instance (n : Nat) : Decidable (Supported n) := by unfold Supported; infer_instance

/-- The declared size domain is exactly the positive bit counts below 26. -/
theorem supported_log (n : Nat) (h : Supported n) : 0 < Nat.log2 n ∧ Nat.log2 n ≤ 25 := by
  rcases h with ⟨hn,he,hs⟩
  constructor
  · by_cases hz : 0 < Nat.log2 n
    · exact hz
    · have hk : Nat.log2 n = 0 := by omega
      rw [hk] at he
      simp at he
      omega
  · by_cases hz : Nat.log2 n ≤ 25
    · exact hz
    · have hk : 26 ≤ Nat.log2 n := by omega
      have hp : 2^26 ≤ 2^(Nat.log2 n) := Nat.pow_le_pow_right (by decide) hk
      omega

theorem supported_power (bits : Nat) (hp : 0 < bits) (hb : bits ≤ 25) : Supported (2^bits) := by
  constructor
  · have h := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 1 ≤ bits)
    simpa using h
  constructor
  · simp [Nat.log2_two_pow]
  · exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- NTT source admission goes through the general Core4 block fragment. There
is one NTT construction, using shared field arithmetic and the general lowerer. -/
def compile (n : Nat) : Except String BlockPlan.Plan :=
  if Supported n then BlockPlan.check (Ntt.nttBlockProgram n)
  else .error "NTT source: expected a supported power-of-two size below 2^26"

def program (n : Nat) : Term := BlockCoreProgram.source (Ntt.nttBlockProgram n)

theorem compile_source (n : Nat) (plan : BlockPlan.Plan) (h : compile n = .ok plan) :
    plan.source = Ntt.nttBlockProgram n := by
  unfold compile at h
  split at h
  · exact BlockPlan.check_source _ plan h
  · contradiction

theorem compile_supported (n : Nat) (plan : BlockPlan.Plan) (h : compile n = .ok plan) :
    Supported n := by
  unfold compile at h
  split at h
  · assumption
  · contradiction

/-- The actual NTT source, including register tiles and shared phases, reaches
flat GPU semantics through the general block-level Core4 theorem. This statement
is universal over inputs; `NttCorrect` separately proves and composes equality
with the DFT for every supported size. -/
theorem source_to_gpu_encoded (n : Nat) (plan : BlockPlan.Plan) (hc : compile n = .ok plan)
    (mem : Memory) (flat : FlatMemory)
    (hg : BlockLower.Good (Ntt.nttBlockProgram n) mem)
    (hf : Represents (Ntt.nttBlockProgram n) mem flat)
    (array index : Nat) (hv : Valid (Ntt.nttBlockProgram n) array index) :
    Steps (BlockPlan.observe (program n) (BlockCoreEncoding.memory mem) array index)
      (.nat ((lowerProgram (Ntt.nttBlockProgram n) flat)
        (address (Ntt.nttBlockProgram n) array index)).toNat) := by
  have he := compile_source n plan hc
  have h := plan.source_to_gpu_encoded mem flat (he.symm ▸ hg) (he.symm ▸ hf)
    array index (he.symm ▸ hv)
  simpa only [BlockPlan.Plan.term, he, program] using h

end Obend.Hardware.Gpu.NttSource
end
