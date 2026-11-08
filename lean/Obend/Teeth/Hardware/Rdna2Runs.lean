/-
# `Obend/Teeth/Hardware/Rdna2Runs.lean` — RADV's RDNA2 programs, certified against the plan

Rung G2's certificate per dumped graph (`Obend.Hardware.Gpu.Rdna2.Certified`): the committed dump of each
graph (`hardware/gpu/isa/<g>.txt`) decodes, its waits cover every load, and `certify` accepts it against
the graph's lowering with the proved residuals; by `certifyDump_sound`, for every input, the programs run
on the wave model leave `evalGraph`'s outputs. Each pin is a check of one artifact, by `native_decide`
and re-run by `#assert_compiled`; `hardware/gpu/isa_check.sh` runs the same check on every graph with its
time and memory. The pins are the graphs that certify today; the block NTTs (an `ArrayKernel` program,
not a `GpuProgram`) wait for the block-program certificate. The vector run of diamond is kept as a smoke test of
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

theorem diamond_certified : certifyNamed "diamond" diamondIsa = true := by native_decide
#assert_compiled diamond_certified

def opticMulIsa : String := include_str "../../../../hardware/gpu/isa/optic-mul.txt"

theorem opticMul_certified : certifyNamed "optic-mul" opticMulIsa = true := by native_decide
#assert_compiled opticMul_certified

def opticBilinearIsa : String := include_str "../../../../hardware/gpu/isa/optic-bilinear.txt"

theorem opticBilinear_certified : certifyNamed "optic-bilinear" opticBilinearIsa = true := by native_decide
#assert_compiled opticBilinear_certified

def opticLinearmacIsa : String := include_str "../../../../hardware/gpu/isa/optic-linearmac.txt"

theorem opticLinearmac_certified : certifyNamed "optic-linearmac" opticLinearmacIsa = true := by native_decide
#assert_compiled opticLinearmac_certified

def adjointMulAddIsa : String := include_str "../../../../hardware/gpu/isa/adjoint-mul-add.txt"

theorem adjointMulAdd_certified : certifyNamed "adjoint-mul-add" adjointMulAddIsa = true := by native_decide
#assert_compiled adjointMulAdd_certified

def tree512Isa : String := include_str "../../../../hardware/gpu/isa/tree512.txt"

theorem tree512_certified : certifyNamed "tree512" tree512Isa = true := by native_decide
#assert_compiled tree512_certified

def macReverse1000Isa : String := include_str "../../../../hardware/gpu/isa/mac-reverse-1000.txt"

theorem macReverse1000_certified : certifyNamed "mac-reverse-1000" macReverse1000Isa = true := by native_decide
#assert_compiled macReverse1000_certified

def arrayRouteIsa : String := include_str "../../../../hardware/gpu/isa/array-route.txt"

theorem arrayRoute_certified : certifyNamed "array-route" arrayRouteIsa = true := by native_decide
#assert_compiled arrayRoute_certified

def soacEmptyIsa : String := include_str "../../../../hardware/gpu/isa/soac-empty.txt"

theorem soacEmpty_certified : certifyNamed "soac-empty" soacEmptyIsa = true := by native_decide
#assert_compiled soacEmpty_certified

def soacNoSegmentsIsa : String := include_str "../../../../hardware/gpu/isa/soac-no-segments.txt"

theorem soacNoSegments_certified : certifyNamed "soac-no-segments" soacNoSegmentsIsa = true := by native_decide
#assert_compiled soacNoSegments_certified

def sourceLeafAffineIsa : String := include_str "../../../../hardware/gpu/isa/source-leaf-affine.txt"

theorem sourceLeafAffine_certified : certifyNamed "source-leaf-affine" sourceLeafAffineIsa = true := by native_decide
#assert_compiled sourceLeafAffine_certified

def sourceLeafFixedSquareIsa : String := include_str "../../../../hardware/gpu/isa/source-leaf-fixed-square.txt"

theorem sourceLeafFixedSquare_certified : certifyNamed "source-leaf-fixed-square" sourceLeafFixedSquareIsa = true := by native_decide
#assert_compiled sourceLeafFixedSquare_certified


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
