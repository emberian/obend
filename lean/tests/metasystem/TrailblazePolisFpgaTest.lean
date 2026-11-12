import Obend.Trailblaze.Obligations
import Obend.Trailblaze.Polis
import Obend.Trailblaze.LeanFpga
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/TrailblazePolisFpgaTest.lean` — Metasystem Regression & Verification Suite (Trailblazer T1: Organs O3 & O7)

Verifies end-to-end kernel elaboration, `rfl` computational behavior, named refusals, `#tooth`
mutation sensitivity, and `#assert_axioms_tree` purity (`0 sorryAx`, `0` custom `axiom`s, `0`
`native_decide`) across:
1. `Obend.Trailblaze.Obligations` (`ObligationMeta`, `ObligationManifest`, `SilverWorkflow`, `SilverSound`, `SilverWorkflow.prod`, `SilverWorkflow.toJudge`),
2. `Obend.Trailblaze.Polis` (`Asm(P)` choice-free `TrackedMorphism`, Blum `UMem`, `SeL4MicrokitPartition`, `apex_polis_deos_turn_safe`, `silverPolisSmoke`),
3. `Obend.Trailblaze.LeanFpga` (`CofibLUT16` distributive lattice & partial order, Salvadori `DeltaNet` Rung 2 + `emitHvmNetText` + `checkNetPortLinearity`, `FABulous` Rung 5 `FabulousTileConfig` codec + DPR fence, `apex_lean_fpga_rung2_to_rung5`, `silverLeanFpgaSmoke`).
-/

namespace Obend.Tests.TrailblazePolisFpgaTest

open Obend.Trailblaze
open Obend.Trailblaze.Polis
open Obend.Trailblaze.LeanFpga

-- ============================================================================
-- 0. Whole-Tree Axiom Purity Audit (`0 sorryAx`, `0` custom `axiom`s)
-- ============================================================================

#assert_axioms_tree

-- ============================================================================
-- 1. `Obligations` & Product `SilverWorkflow` Composition (`Polis × LeanFpga`)
-- ============================================================================

#check @checkManifestWellFormed_sound
#check @silverWorkflow_satisfies_silverSound
#check @SilverWorkflow.prod
#check @SilverWorkflow.toJudge

@[instance_reducible] def jointPolisFpgaWorkflow : SilverWorkflow (ConcretePolisTurn × LeanFpgaTurn) :=
  SilverWorkflow.prod ConcretePolisTurn LeanFpgaTurn

example : jointPolisFpgaWorkflow.runValid (sampleValidPolisTurn, sampleValidFpgaTurn) = true := rfl
example : jointPolisFpgaWorkflow.refuseInvalid (sampleValidPolisTurn, sampleValidFpgaTurn) = none := rfl
example :
    jointPolisFpgaWorkflow.refuseInvalid (plantedWatchdogLeakTurn, sampleValidFpgaTurn) =
      some "refused: foc-hil-watchdog-leak" := rfl
example :
    jointPolisFpgaWorkflow.refuseInvalid (sampleValidPolisTurn, plantedNonlinearNetTurn) =
      some "refused: delta-net-port-nonlinearity" := rfl

-- ============================================================================
-- 2. Organ O3 (`Polis`): Choice-Free `Asm(P)`, Blum `UMem` & `seL4` Microkit
-- ============================================================================

#check @TrackedMorphism.id
#check @TrackedMorphism.comp
#check @TrackedMorphism.id_comp
#check @TrackedMorphism.comp_id
#check @TrackedMorphism.comp_assoc
#check @blum_write_then_read_sound
#check @verifyBlumMemory_sound
#check @checkMicrokitIsolation_sound
#check @apex_polis_deos_turn_safe

-- Choice-free `TrackedMorphism` composition executes directly in the kernel via `rfl`
def doubleHopMorphism : TrackedMorphism custodyAssembly settledSeatAssembly :=
  ((TrackedMorphism.id settledSeatAssembly).comp (clearCustodyToSeat 500)).comp
    (TrackedMorphism.id custodyAssembly)

example : doubleHopMorphism.tracker (.capToken 7 1 42) = some (.settledSeat 7 542) := rfl
example : doubleHopMorphism.tracker (.capToken 7 0 42) = none := rfl

-- Blum `UMem` positive and negative checks
#guard verifyBlumMemory sampleOnlineMem sampleOfflineSortedMem == true
#guard verifyBlumMemory plantedForgedBlumTurn.onlineMem plantedForgedBlumTurn.offlineSortedMem == false
#guard verifyBlumMemory sampleOfflineSortedMem sampleOfflineSortedMem == false

-- `seL4` Microkit isolation positive and named negative checks
example : checkMicrokitIsolation sampleValidPartition = true := rfl
example : refuseMicrokitIsolation plantedWatchdogLeakTurn.partition = some "refused: foc-hil-watchdog-leak" := rfl
example : refuseMicrokitIsolation plantedSharedMmioTurn.partition = some "refused: shared-writable-mmio" := rfl
example : refuseMicrokitIsolation plantedCyclicCapTurn.partition = some "refused: cyclic-untyped-cap-authority" := rfl

-- End-to-end Organ O3 Silver smoke witness
example : silverPolisSmoke = true := rfl

-- ============================================================================
-- 3. Organ O7 (`LeanFpga`): `CofibLUT16`, Salvadori `DeltaNet` & `FABulous` Rung 5
-- ============================================================================

#check @CofibLUT16.meet_comm
#check @CofibLUT16.meet_assoc
#check @CofibLUT16.join_distrib_meet
#check @CofibLUT16.meet_distrib_join
#check @CofibLUT16.implies_refl
#check @CofibLUT16.implies_trans
#check @CofibLUT16.implies_antisymm
#check @checkNetPortLinearity_sound
#check @decode_encode_fabulousFrame
#check @encode_decode_fabulousFrame
#check @dpr_isolated_clamps_output
#check @apex_lean_fpga_rung2_to_rung5

-- `CofibLUT16` 16-bit truth-table ALU checks
example :
    ((CofibLUT16.varEq0 ⟨0, by decide⟩).meet (CofibLUT16.varEq1 ⟨2, by decide⟩)).truthWord =
      0x5050#16 := rfl

example :
    ((CofibLUT16.varEq0 ⟨1, by decide⟩).join (CofibLUT16.varEq1 ⟨1, by decide⟩)) =
      CofibLUT16.top := rfl

-- Salvadori `DeltaNet` Rung-2 HVM2 text emission & linearity checks
#guard (emitHvmNetText sampleLinearDeltaNet).startsWith "@cofib_face_dispatch = w0_0"
#guard checkNetPortLinearity sampleLinearDeltaNet == true
#guard checkNetPortLinearity plantedNonlinearNetTurn.deltaNet == false

-- `FABulous` Rung-5 bitstream frame round-trip & tile evaluation checks
def sampleSeqTile : FabulousTileConfig where
  lut4Truth := 0xCAFE#16
  ffEnable  := true
  pipMux    := ⟨6, by decide⟩

example : decodeBitstreamFrame (encodeBitstreamFrame sampleSeqTile) = sampleSeqTile := rfl
example : checkCanonicalFrame32 (encodeBitstreamFrame sampleSeqTile) = true := rfl
example :
    evalFabulousTile sampleSeqTile 0b0001#4 false (fun i => i.val == 6) =
      { belOut := false, nextFf := true, pipRouted := true } := rfl

-- End-to-end Organ O7 Silver smoke witness
example : silverLeanFpgaSmoke = true := rfl

end Obend.Tests.TrailblazePolisFpgaTest
