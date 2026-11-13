/-
# `Obend/Teeth/Hardware/Rdna2Runs.lean` — RADV's RDNA2 programs, certified against the plan

Rung G2's certificate per dumped graph (`Obend.Hardware.Gpu.Rdna2.Certified`): the committed dump of each
graph (`hardware/gpu/isa/<g>.txt`) decodes, its waits cover every load, and the schedule the emitter
dispatches (elementwise stages and LDS block collectives) is certified with the proved residuals; by
`certifyDump_sound`, for every input, the programs run on the wave model leave `evalGraph`'s outputs. The
NTT's block programs are pinned by `certifyBlockNamed` (`certifyBlockDump_sound`: every device element is
`evalProgram`'s). Each pin is a check of one artifact, by `native_decide` and re-run by
`#assert_compiled`; `hardware/gpu/isa_check.sh` runs the same check on every dump with its time and
memory, the 65536- and 2^20-point NTTs and the large SOACs only there. The vector run of diamond is kept
as a smoke test of the concrete model and the host layout, and the gem5 vectors pin the instruction
semantics to their external reference. Tier 2: `lake build Teeth`.
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

def sourceLeafMuxIsa : String := include_str "../../../../hardware/gpu/isa/source-leaf-mux.txt"

theorem sourceLeafMux_certified : certifyNamed "source-leaf-mux" sourceLeafMuxIsa = true := by native_decide
#assert_compiled sourceLeafMux_certified

def sourceLeafShlIsa : String := include_str "../../../../hardware/gpu/isa/source-leaf-shl.txt"

theorem sourceLeafShl_certified : certifyNamed "source-leaf-shl" sourceLeafShlIsa = true := by native_decide
#assert_compiled sourceLeafShl_certified

def sourceLeafShrIsa : String := include_str "../../../../hardware/gpu/isa/source-leaf-shr.txt"

theorem sourceLeafShr_certified : certifyNamed "source-leaf-shr" sourceLeafShrIsa = true := by native_decide
#assert_compiled sourceLeafShr_certified


def glmul4Isa : String := include_str "../../../../hardware/gpu/isa/glmul-4.txt"

theorem glmul4_certified : certifyNamed "glmul-4" glmul4Isa = true := by native_decide
#assert_compiled glmul4_certified

def glmul256Isa : String := include_str "../../../../hardware/gpu/isa/glmul-256.txt"

theorem glmul256_certified : certifyNamed "glmul-256" glmul256Isa = true := by native_decide
#assert_compiled glmul256_certified

def allopsIsa : String := include_str "../../../../hardware/gpu/isa/allops.txt"

theorem allops_certified : certifyNamed "allops" allopsIsa = true := by native_decide
#assert_compiled allops_certified

def muxchainIsa : String := include_str "../../../../hardware/gpu/isa/muxchain.txt"

theorem muxchain_certified : certifyNamed "muxchain" muxchainIsa = true := by native_decide
#assert_compiled muxchain_certified

def adjointSquareBilinearIsa : String := include_str "../../../../hardware/gpu/isa/adjoint-square-bilinear.txt"

theorem adjointSquareBilinear_certified : certifyNamed "adjoint-square-bilinear" adjointSquareBilinearIsa = true := by native_decide
#assert_compiled adjointSquareBilinear_certified

def soacBoundariesIsa : String := include_str "../../../../hardware/gpu/isa/soac-boundaries.txt"

theorem soacBoundaries_certified : certifyNamed "soac-boundaries" soacBoundariesIsa = true := by native_decide
#assert_compiled soacBoundaries_certified

def ntt4Isa : String := include_str "../../../../hardware/gpu/isa/ntt-4.txt"

theorem ntt4_certified : certifyBlockNamed "ntt-4" ntt4Isa = true := by native_decide
#assert_compiled ntt4_certified

/-- Same-width deletion preserves every branch target. -/
def ntt4NoVscntIsa : String := ntt4Isa.replace "bbfd0000" "bf800000"

theorem ntt4_noVscnt_loads_ok : checkWaitcntDump ntt4NoVscntIsa = true := by native_decide
#assert_compiled ntt4_noVscnt_loads_ok

theorem ntt4_noVscnt_completion_refused : checkVscntBlockDump ntt4NoVscntIsa = false := by native_decide
#assert_compiled ntt4_noVscnt_completion_refused

theorem ntt4_noVscnt_certificate_refused : certifyBlockNamed "ntt-4" ntt4NoVscntIsa = false := by native_decide
#assert_compiled ntt4_noVscnt_certificate_refused

def ntt16Isa : String := include_str "../../../../hardware/gpu/isa/ntt-16.txt"

theorem ntt16_certified : certifyBlockNamed "ntt-16" ntt16Isa = true := by native_decide
#assert_compiled ntt16_certified

def ntt64Isa : String := include_str "../../../../hardware/gpu/isa/ntt-64.txt"

theorem ntt64_certified : certifyBlockNamed "ntt-64" ntt64Isa = true := by native_decide
#assert_compiled ntt64_certified

def ntt1024Isa : String := include_str "../../../../hardware/gpu/isa/ntt-1024.txt"

theorem ntt1024_certified : certifyBlockNamed "ntt-1024" ntt1024Isa = true := by native_decide
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
