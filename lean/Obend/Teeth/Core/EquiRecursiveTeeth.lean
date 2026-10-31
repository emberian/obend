module
public import Obend.Core.Check
public meta import Obend.Core.Check
import all Obend.Core.TypeGraph
open Obend.Core.Ty Obend.Core.Check
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
#guard sameType ⟨[(0, .natural)], [], []⟩
  (.arrow .reusable .unrestricted (.variable 0) .boolean)
  (.arrow .reusable .unrestricted .natural .boolean)
#guard !sameType {} .natural .boolean
#guard sameType {} (.field "b" .boolean (.field "a" .natural .emptyRow))
  (.field "a" .natural (.field "b" .boolean .emptyRow))
#guard sameType ⟨[(0, .natural)], [], []⟩
  (.field "a" .boolean (.field "a" (.variable 0) .emptyRow))
  (.field "a" .boolean .emptyRow)
#guard !sameType {} (.field "a" .boolean (.field "a" (.custody 7) .emptyRow))
  (.field "a" .boolean .emptyRow)
#guard !sameType ⟨[(0, .field "a" .natural (.variable 0))], [], []⟩
  (.variable 0) (.field "a" .natural .emptyRow)
#guard sameType ⟨[(0, .arrow .once .linear .natural (.variable 0)),
  (1, .arrow .once .linear .natural (.variable 2)),
  (2, .arrow .once .linear .natural (.variable 1))], [], []⟩ (.variable 0) (.variable 1)
#guard !sameType ⟨[(0, .natural)], [], [0]⟩ (.variable 0) .natural

/-! The same comparisons as theorems the kernel evaluates: the type-graph worklist recurses on one
`Nat` measure, so `decide +kernel` reduces `sameType` on closed types (formerly `equirec_reduce`,
a simp set over the worklist's equations, in `Obend.Core.DecisionReduction`). -/

theorem Obend.Core.FiniteBisimulation.ReductionProbes.cycle :
    Obend.Core.FiniteBisimulation.visitedSame
      Obend.Core.FiniteBisimulation.Probes.differentPeriods 0 1 = true := by decide +kernel

theorem Obend.Core.FiniteBisimulation.ReductionProbes.mismatch :
    Obend.Core.FiniteBisimulation.visitedSame
      Obend.Core.FiniteBisimulation.Probes.reachableMismatch 0 1 = false := by decide +kernel

theorem Obend.Core.DecisionReduction.Probes.atomic_mismatch :
    Obend.Core.TypeGraph.candidate ⟨[],[],[]⟩ .natural .boolean = false := by decide +kernel

theorem Obend.Core.DecisionReduction.Probes.redundant_shadow :
    Obend.Core.TypeGraph.candidate ⟨[],[],[]⟩
      (.field "a" .natural (.field "a" .natural .emptyRow))
      (.field "a" .natural .emptyRow) = true := by decide +kernel

theorem Obend.Core.DecisionReduction.Probes.checker_atomic_mismatch :
    sameType ⟨[],[],[]⟩ .natural .boolean = false := by decide +kernel

theorem Obend.Core.EquiRecursiveTeeth.sameType_alias_cycle_kernel : sameType ⟨[(0, .arrow .once .linear .natural (.variable 0)),
    (1, .arrow .once .linear .natural (.variable 2)),
    (2, .arrow .once .linear .natural (.variable 1))], [], []⟩ (.variable 0) (.variable 1) = true := by
  decide +kernel

theorem Obend.Core.EquiRecursiveTeeth.sameType_row_permutation_kernel : sameType {} (.field "b" .boolean (.field "a" .natural .emptyRow))
    (.field "a" .natural (.field "b" .boolean .emptyRow)) = true := by decide +kernel

theorem Obend.Core.EquiRecursiveTeeth.sameType_custody_shadow_kernel :
    sameType {} (.field "a" .boolean (.field "a" (.custody 7) .emptyRow))
      (.field "a" .boolean .emptyRow) = false := by decide +kernel
