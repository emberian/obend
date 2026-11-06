/-
# `Obend/Teeth/Hardware/Rdna2Runs.lean` — RADV's RDNA2 programs for the golden graphs, run on the model

Rung G2's correspondence as known-answer runs (`Obend.Hardware.Gpu.Rdna2.Check`): the committed dump of
each graph (`hardware/gpu/isa/<g>.txt`), decoded by the generated decoder and run on the wave model
from each vector of `expected.tsv`, gives the outputs the array-hypergraph model gives. Each is a check
and not a theorem: pinned by `native_decide` and re-run by `#assert_compiled`; the same function runs on
every graph, and with a planted bit flip that must fail, in `hardware/gpu/isa_check.sh` stage 4. Tier 2:
`lake build Teeth`.
-/
import Obend.Hardware.Gpu.Rdna2.Check
import Obend.Hardware.Gpu.Rdna2.Waitcnt
import Obend.AssertCompiled

namespace Obend.Teeth.Hardware.Rdna2Runs
open Obend.Hardware.Gpu.Rdna2

def diamondIsa : String := include_str "../../../../hardware/gpu/isa/diamond.txt"
def diamondPlan : String := include_str "../../../../hardware/gpu/graphs/diamond/plan.json"
def diamondExpected : String := include_str "../../../../hardware/gpu/graphs/diamond/expected.tsv"
-- fixture kept: the golden diamond's dumped programs compute the plan on the model (rung G2)
theorem diamond_runs : checkGraph diamondIsa diamondPlan diamondExpected = true := by native_decide
#assert_compiled diamond_runs

def opticMulIsa : String := include_str "../../../../hardware/gpu/isa/optic-mul.txt"
def opticMulPlan : String := include_str "../../../../hardware/gpu/graphs/optic-mul/plan.json"
def opticMulExpected : String := include_str "../../../../hardware/gpu/graphs/optic-mul/expected.tsv"
-- fixture kept: the multiply optic's dumped programs on the model
theorem opticMul_runs : checkGraph opticMulIsa opticMulPlan opticMulExpected = true := by native_decide
#assert_compiled opticMul_runs

def opticBilinearIsa : String := include_str "../../../../hardware/gpu/isa/optic-bilinear.txt"
def opticBilinearPlan : String := include_str "../../../../hardware/gpu/graphs/optic-bilinear/plan.json"
def opticBilinearExpected : String := include_str "../../../../hardware/gpu/graphs/optic-bilinear/expected.tsv"
-- fixture kept: the bilinear optic's dumped programs on the model
theorem opticBilinear_runs : checkGraph opticBilinearIsa opticBilinearPlan opticBilinearExpected = true := by native_decide
#assert_compiled opticBilinear_runs

def opticLinearmacIsa : String := include_str "../../../../hardware/gpu/isa/optic-linearmac.txt"
def opticLinearmacPlan : String := include_str "../../../../hardware/gpu/graphs/optic-linearmac/plan.json"
def opticLinearmacExpected : String := include_str "../../../../hardware/gpu/graphs/optic-linearmac/expected.tsv"
-- fixture kept: the linear-mac optic's dumped programs on the model
theorem opticLinearmac_runs : checkGraph opticLinearmacIsa opticLinearmacPlan opticLinearmacExpected = true := by native_decide
#assert_compiled opticLinearmac_runs

def allopsIsa : String := include_str "../../../../hardware/gpu/isa/allops.txt"
def allopsPlan : String := include_str "../../../../hardware/gpu/graphs/allops/plan.json"
def allopsExpected : String := include_str "../../../../hardware/gpu/graphs/allops/expected.tsv"
-- fixture kept: every scalar operation with wrap-around, dumped and run on the model
theorem allops_runs : checkGraph allopsIsa allopsPlan allopsExpected = true := by native_decide
#assert_compiled allops_runs

def glmulIsa : String := include_str "../../../../hardware/gpu/isa/glmul-256.txt"
def glmulPlan : String := include_str "../../../../hardware/gpu/graphs/glmul-256/plan.json"
def glmulExpected : String := include_str "../../../../hardware/gpu/graphs/glmul-256/expected.tsv"
-- fixture kept: the Goldilocks multiply over 256 elements, its dumped programs on the model
theorem glmul_runs : checkGraph glmulIsa glmulPlan glmulExpected = true := by native_decide
#assert_compiled glmul_runs

def ntt4Isa : String := include_str "../../../../hardware/gpu/isa/ntt-4.txt"
def ntt4Plan : String := include_str "../../../../hardware/gpu/graphs/ntt-4/plan.json"
def ntt4Expected : String := include_str "../../../../hardware/gpu/graphs/ntt-4/expected.tsv"
-- fixture kept: the 4-point Goldilocks NTT, its dumped programs on the model
theorem ntt4_runs : checkGraph ntt4Isa ntt4Plan ntt4Expected = true := by native_decide
#assert_compiled ntt4_runs

-- fixture kept: the waits of every dumped program of these graphs cover every load before its destination is touched
theorem diamond_waits : checkWaitcntDump diamondIsa = true := by native_decide
#assert_compiled diamond_waits
theorem glmul_waits : checkWaitcntDump glmulIsa = true := by native_decide
#assert_compiled glmul_waits
theorem ntt4_waits : checkWaitcntDump ntt4Isa = true := by native_decide
#assert_compiled ntt4_waits

/-- The gem5 differential vectors (`hardware/gpu/rdna2/gem5_vectors.tsv`): every twin instruction's step
agrees with gem5's Vega body on random register states, register by register. -/
def gem5Vectors : String := include_str "../../../../hardware/gpu/rdna2/gem5_vectors.tsv"
-- fixture kept: the instruction semantics against gem5 (the external executable reference)
theorem gem5_agrees : checkGem5 gem5Vectors = true := by native_decide
#assert_compiled gem5_agrees

end Obend.Teeth.Hardware.Rdna2Runs
