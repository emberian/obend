/-
# `Obend/Teeth/Hardware/Rdna2Runs.lean` — RADV's RDNA2 programs, certified against the plan

Rung G2's certificate per dumped graph (`Obend.Hardware.Gpu.Rdna2.Certified`): the committed dump of each
graph (`hardware/gpu/isa/<g>.txt`) decodes, its waits cover every load, and `certify` accepts it against
the graph's lowering with the proved residuals; by `certifyDump_sound`, for every input, the programs run
on the wave model leave `evalGraph`'s outputs. Each pin is a check of one artifact, by `native_decide`
and re-run by `#assert_compiled`; `hardware/gpu/isa_check.sh` runs the same check on every graph, the
65536-point NTT included, with its time and memory. The vector run of diamond is kept as a smoke test of
the concrete model and the host layout, and the gem5 vectors pin the instruction semantics to their
external reference. Tier 2: `lake build Teeth`.
-/
import Obend.Hardware.Gpu.Rdna2.Certified
import Obend.AssertCompiled

namespace Obend.Teeth.Hardware.Rdna2Runs
open Obend.Hardware.Gpu.Rdna2

def diamondPlan : String := include_str "../../../../hardware/gpu/graphs/diamond/plan.json"
def diamondExpected : String := include_str "../../../../hardware/gpu/graphs/diamond/expected.tsv"

def diamondIsa : String := include_str "../../../../hardware/gpu/isa/diamond.txt"
-- fixture kept: diamond's dumped programs compute the graph for every input (certifyDump_sound)
theorem diamond_certified : certifyNamed "diamond" diamondIsa = true := by native_decide
#assert_compiled diamond_certified

def opticMulIsa : String := include_str "../../../../hardware/gpu/isa/optic-mul.txt"
-- fixture kept: optic-mul's dumped programs compute the graph for every input (certifyDump_sound)
theorem opticMul_certified : certifyNamed "optic-mul" opticMulIsa = true := by native_decide
#assert_compiled opticMul_certified

def opticBilinearIsa : String := include_str "../../../../hardware/gpu/isa/optic-bilinear.txt"
-- fixture kept: optic-bilinear's dumped programs compute the graph for every input (certifyDump_sound)
theorem opticBilinear_certified : certifyNamed "optic-bilinear" opticBilinearIsa = true := by native_decide
#assert_compiled opticBilinear_certified

def opticLinearmacIsa : String := include_str "../../../../hardware/gpu/isa/optic-linearmac.txt"
-- fixture kept: optic-linearmac's dumped programs compute the graph for every input (certifyDump_sound)
theorem opticLinearmac_certified : certifyNamed "optic-linearmac" opticLinearmacIsa = true := by native_decide
#assert_compiled opticLinearmac_certified

def adjointMulAddIsa : String := include_str "../../../../hardware/gpu/isa/adjoint-mul-add.txt"
-- fixture kept: adjoint-mul-add's dumped programs compute the graph for every input (certifyDump_sound)
theorem adjointMulAdd_certified : certifyNamed "adjoint-mul-add" adjointMulAddIsa = true := by native_decide
#assert_compiled adjointMulAdd_certified

def adjointSquareBilinearIsa : String := include_str "../../../../hardware/gpu/isa/adjoint-square-bilinear.txt"
-- fixture kept: adjoint-square-bilinear's dumped programs compute the graph for every input (certifyDump_sound)
theorem adjointSquareBilinear_certified : certifyNamed "adjoint-square-bilinear" adjointSquareBilinearIsa = true := by native_decide
#assert_compiled adjointSquareBilinear_certified

def allopsIsa : String := include_str "../../../../hardware/gpu/isa/allops.txt"
-- fixture kept: allops's dumped programs compute the graph for every input (certifyDump_sound)
theorem allops_certified : certifyNamed "allops" allopsIsa = true := by native_decide
#assert_compiled allops_certified

def muxchainIsa : String := include_str "../../../../hardware/gpu/isa/muxchain.txt"
-- fixture kept: muxchain's dumped programs compute the graph for every input (certifyDump_sound)
theorem muxchain_certified : certifyNamed "muxchain" muxchainIsa = true := by native_decide
#assert_compiled muxchain_certified

def tree512Isa : String := include_str "../../../../hardware/gpu/isa/tree512.txt"
-- fixture kept: tree512's dumped programs compute the graph for every input (certifyDump_sound)
theorem tree512_certified : certifyNamed "tree512" tree512Isa = true := by native_decide
#assert_compiled tree512_certified

def macReverse1000Isa : String := include_str "../../../../hardware/gpu/isa/mac-reverse-1000.txt"
-- fixture kept: mac-reverse-1000's dumped programs compute the graph for every input (certifyDump_sound)
theorem macReverse1000_certified : certifyNamed "mac-reverse-1000" macReverse1000Isa = true := by native_decide
#assert_compiled macReverse1000_certified

def glmul4Isa : String := include_str "../../../../hardware/gpu/isa/glmul-4.txt"
-- fixture kept: glmul-4's dumped programs compute the graph for every input (certifyDump_sound)
theorem glmul4_certified : certifyNamed "glmul-4" glmul4Isa = true := by native_decide
#assert_compiled glmul4_certified

def glmul256Isa : String := include_str "../../../../hardware/gpu/isa/glmul-256.txt"
-- fixture kept: glmul-256's dumped programs compute the graph for every input (certifyDump_sound)
theorem glmul256_certified : certifyNamed "glmul-256" glmul256Isa = true := by native_decide
#assert_compiled glmul256_certified

def ntt4Isa : String := include_str "../../../../hardware/gpu/isa/ntt-4.txt"
-- fixture kept: ntt-4's dumped programs compute the graph for every input (certifyDump_sound)
theorem ntt4_certified : certifyNamed "ntt-4" ntt4Isa = true := by native_decide
#assert_compiled ntt4_certified

def ntt16Isa : String := include_str "../../../../hardware/gpu/isa/ntt-16.txt"
-- fixture kept: ntt-16's dumped programs compute the graph for every input (certifyDump_sound)
theorem ntt16_certified : certifyNamed "ntt-16" ntt16Isa = true := by native_decide
#assert_compiled ntt16_certified

def ntt64Isa : String := include_str "../../../../hardware/gpu/isa/ntt-64.txt"
-- fixture kept: ntt-64's dumped programs compute the graph for every input (certifyDump_sound)
theorem ntt64_certified : certifyNamed "ntt-64" ntt64Isa = true := by native_decide
#assert_compiled ntt64_certified

def ntt1024Isa : String := include_str "../../../../hardware/gpu/isa/ntt-1024.txt"
-- fixture kept: ntt-1024's dumped programs compute the graph for every input (certifyDump_sound)
theorem ntt1024_certified : certifyNamed "ntt-1024" ntt1024Isa = true := by native_decide
#assert_compiled ntt1024_certified

-- fixture kept: smoke test of the concrete model: diamond's dumped programs on the vectors of expected.tsv
theorem diamond_runs : checkGraph diamondIsa diamondPlan diamondExpected = true := by native_decide
#assert_compiled diamond_runs

/-- The gem5 differential vectors (`hardware/gpu/rdna2/gem5_vectors.tsv`): every twin instruction's step
agrees with gem5's Vega body on random register states, register by register. -/
def gem5Vectors : String := include_str "../../../../hardware/gpu/rdna2/gem5_vectors.tsv"
-- fixture kept: the instruction semantics against gem5 (the external executable reference)
theorem gem5_agrees : checkGem5 gem5Vectors = true := by native_decide
#assert_compiled gem5_agrees

end Obend.Teeth.Hardware.Rdna2Runs
