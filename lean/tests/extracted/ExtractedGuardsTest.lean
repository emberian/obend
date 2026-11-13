module
/-
# Extracted Compile-Time Guards (`ExtractedGuardsTest`)

Compile-time `#guard` checks evicted from Tier-1 library modules (`Obend.Core.FiniteBisimulation`,
`Obend.Leaf.BytecodeRegisterJit`, `Obend.Leaf.SelfApplicableMix`, `Obend.Trailblaze.LeanFpga`).
These same checks are also executed natively in `lake exe obend-test` (`lean/tools/test/ObendTest.lean`).
-/
import all Obend.Core.FiniteBisimulation
import all Obend.Leaf.BytecodeRegisterJit
import all Obend.Leaf.SelfApplicableMix
import all Obend.Trailblaze.StageBInstances

public section

namespace Obend.Tests.Extracted.ExtractedGuardsTest

section FiniteBisimulation
open Obend.Core.FiniteBisimulation Obend.Core.FiniteBisimulation.Probes

#guard visitedSame differentPeriods 0 1
#guard !(visitedSame reachableMismatch 0 1)
#guard !(visitedSame arityMismatch 0 1)
end FiniteBisimulation

section BytecodeRegisterJit
open Obend.Leaf.BytecodeRegisterJit

#guard execBytecode sumToLoopCode #[0, 30000, 0, 0, 0, 0] 180002 == some 450015000
end BytecodeRegisterJit

section SelfApplicableMix
open Obend.Leaf.SelfApplicableMix

#guard match runMixSpecialize 3000 mixProg (quoteProg objInterp) with
  | some c => checkSpecializesProg 300 mixProg (quoteProg objInterp) c && !hasStaticConstruct c && c.procs.length == 6
  | none => false

#guard match runMixSpecialize 4000 mixProg (quoteProg mixProg) with
  | some cg => checkSpecializesProg 280 mixProg (quoteProg mixProg) cg && !hasStaticConstruct cg && cg.procs.length == 13
  | none => false
end SelfApplicableMix

section LeanFpga
open Obend.Trailblaze.LeanFpga

#guard !(emitHvmNetText sampleLinearDeltaNet).isEmpty
end LeanFpga

end Obend.Tests.Extracted.ExtractedGuardsTest
end
