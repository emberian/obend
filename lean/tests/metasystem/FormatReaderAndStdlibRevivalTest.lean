import Obend.Tactic.Tooth
import Obend.AssertAxioms
import Obend.Stdlib

open Obend.Core.Data (Data)
open Obend.Core.Term (Term)
open Obend.Equiv
open Obend.Logic (obligationMeaningWithJudges)
open Obend.Elab.Workbook (workbookFormats)
open Obend.Stdlib

set_option autoImplicit false

/-!
# Metasystem Verification Suite: Revived `.obend` `Obend.Stdlib` & Flagship CAE Modules

Verifies:
1. Compile-time elaboration, law inheritance, and open-recursive evaluation across all 11
   `stdlib/{core,ledger,usd,physical}/*.obend` modules (`StdlibCell`, `StdlibWord64`,
   `StdlibAccount`, `StdlibScenePrim`, `StdQuantumPhotonic`, `StdMultiphysicsPcb`,
   `StdSymplecticSpacecraft`, `StdLcDrivesStator`, `StdMs350FcmlPhaseLeg`,
   `StdCleanroomTcadStack`, `StdCnc5AxisMill`).
2. 8 `#tooth` mutation kills rejecting unbound composition mutations across every flattened/emitted
   `Obend.Stdlib` composition (`stdlib_flatten_and_book_sound`,
   `stdlib_quantum_photonic_flatten_and_book_sound`, and
   `stdlib_pcb_and_spacecraft_flatten_and_book_sound`).
3. Cross-package `OB5`/`LT5` cone-pin invariance (`stdlib_pcb_and_spacecraft_crossPackage_cone_survives`)
   and zero-`sorryAx` / zero-`Classical.choice` axiom hygiene.
-/

/-! ## Part 1: Concrete Evaluation & Package Law Guards Across Revived `Obend.Stdlib` -/

#guard StdlibCell.package.laws.length == 2
#guard StdlibAccount.package.laws.length == 4
#guard StdlibScenePrim.package.laws.length == 3
#guard StdMultiphysicsPcb.package.laws.length == 4
#guard StdSymplecticSpacecraft.package.laws.length == 4

theorem revival_stdlib_all_values_rfl :
    StdlibCell.versionedCellNextAt25_val = .nat 125 ∧
    StdlibCell.versionedCellGasAt4_val = .nat 32 ∧
    StdlibWord64.word64AddSample_val = .nat 155 ∧
    StdlibWord64.word64Qmul32Sample_val = .nat 25769803776 ∧
    StdlibAccount.escrowAvailableAt10_val = .nat 1020 ∧
    StdlibAccount.escrowSettlementAt100_val = .nat 270 ∧
    StdlibScenePrim.composedWorldTransformAt100_val = .nat 140 ∧
    StdlibScenePrim.composedVoxelCostAt5_val = .nat 28 ∧
    StdQuantumPhotonic.clementsPowerAt20Mw_val = .nat 90 ∧
    StdQuantumPhotonic.tetronBraidPhaseAt2_val = .nat 420 ∧
    StdMultiphysicsPcb.tempestDiffImpedanceMohm_val = .nat 100000 ∧
    StdMultiphysicsPcb.tempestEtchedWidthAt120Um_val = .nat 156 ∧
    StdMultiphysicsPcb.tempestCutoffAt12Ghz_val = .nat 96500 ∧
    StdSymplecticSpacecraft.spacecraftCayleyDenomAt200_val = .nat 1040000 ∧
    StdSymplecticSpacecraft.spacecraftImpulseAt500Kg_val = .nat 1741450 ∧
    StdSymplecticSpacecraft.spacecraftTpsAt40g800Kw_val = .nat 1800 ∧
    StdLcDrivesStator.lcDrivesInSlotPeakTemp8kW_val = .nat 122 ∧
    StdMs350FcmlPhaseLeg.ms350LossAt100A_val = .nat 420 ∧
    StdCleanroomTcadStack.q3PowerAt20Mw_val = .nat 143 ∧
    StdCnc5AxisMill.compensatedErrorAt6Dm_val = .nat 26 ∧
    StdCnc5AxisMill.compensatedCommandAt6Dm_val = .nat 10024 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: `#tooth` Mutation Kills on Open `Obend.Stdlib` Soundness Theorems -/

#tooth stdlib_flatten_and_book_sound by mutation
  StdlibCell.versionedCell_comp :=
    { top := { name := "BadCell", flat := false, metadata := .record [], fields := [("bad", .bound 99)] }
      below := []
      seed := [] }

#tooth stdlib_flatten_and_book_sound by mutation
  StdlibAccount.escrowAccount_comp :=
    { top := { name := "BadAccount", flat := false, metadata := .record [], fields := [("bad", .bound 99)] }
      below := []
      seed := [] }

#tooth stdlib_flatten_and_book_sound by mutation
  StdlibScenePrim.composedUsdPrim_comp :=
    { top := { name := "BadPrim", flat := false, metadata := .record [], fields := [("bad", .bound 99)] }
      below := []
      seed := [] }

#tooth stdlib_quantum_photonic_flatten_and_book_sound by mutation
  StdQuantumPhotonic.compensatedClementsArray_comp :=
    { top := { name := "BadClements", flat := false, metadata := .record [], fields := [("bad", .bound 99)] }
      below := []
      seed := [] }

#tooth stdlib_quantum_photonic_flatten_and_book_sound by mutation
  StdQuantumPhotonic.cooledTetronCell_comp :=
    { top := { name := "BadTetron", flat := false, metadata := .record [], fields := [("bad", .bound 99)] }
      below := []
      seed := [] }

#tooth stdlib_pcb_and_spacecraft_flatten_and_book_sound by mutation
  StdlibWord64.pureWord64_comp :=
    { top := { name := "BadWord64", flat := false, metadata := .record [], fields := [("bad", .bound 99)] }
      below := []
      seed := [] }

#tooth stdlib_pcb_and_spacecraft_flatten_and_book_sound by mutation
  StdMultiphysicsPcb.tempestShieldedBoard_comp :=
    { top := { name := "BadPcb", flat := false, metadata := .record [], fields := [("bad", .bound 99)] }
      below := []
      seed := [] }

#tooth stdlib_pcb_and_spacecraft_flatten_and_book_sound by mutation
  StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp :=
    { top := { name := "BadSpacecraft", flat := false, metadata := .record [], fields := [("bad", .bound 99)] }
      below := []
      seed := [] }

/-! ## Part 3: Revived `Obend.Stdlib` Flagship Modules & Axiom Hygiene Audit -/

theorem revival_stdlib_suite_verified (m : String) :
    (StdMultiphysicsPcb.package.laws.length = 4 ∧
     StdSymplecticSpacecraft.package.laws.length = 4 ∧
     StdMultiphysicsPcb.tempestDiffImpedanceMohm_val = .nat 100000 ∧
     StdSymplecticSpacecraft.spacecraftImpulseAt500Kg_val = .nat 1741450 ∧
     StdlibWord64.word64Qmul32Sample_val = .nat 25769803776) ∧
    (Term.get StdMultiphysicsPcb.tempestShieldedBoard_comp.flatten m ≈b
       Term.get StdMultiphysicsPcb.tempestShieldedBoard_comp.object m) ∧
    (Term.get StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp.flatten m ≈b
       Term.get StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp.object m) := by
  have hEval := stdlib_pcb_and_spacecraft_laws_and_eval
  have hSound := stdlib_pcb_and_spacecraft_flatten_and_book_sound m
  exact ⟨⟨hEval.1, hEval.2.1, hEval.2.2.1, hEval.2.2.2.2.2.2.1, hEval.2.2.2.2.2.2.2.2.2⟩,
         hSound.2.2.1, hSound.2.2.2.2.1⟩

open Lean Elab Command in
elab "#verify_revival_zero_choice_axioms" : command => do
  let pureKernelTargets : List Name := [
    ``Obend.Stdlib.stdlib_inherited_laws_count,
    ``Obend.Stdlib.stdlib_open_recursion_eval,
    ``Obend.Stdlib.stdlib_compositions_closed,
    ``Obend.Stdlib.stdlib_quantum_photonic_compositions_closed,
    ``Obend.Stdlib.stdlib_pcb_and_spacecraft_compositions_closed,
    ``Obend.Stdlib.stdlib_pcb_and_spacecraft_laws_and_eval,
    ``revival_stdlib_all_values_rfl
  ]
  for t in pureKernelTargets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    if axs.contains ``Classical.choice then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on Classical.choice"
  let propAndClaimTargets : List Name := [
    ``Obend.Stdlib.stdlib_all_claims_hold,
    ``Obend.Stdlib.stdlib_flatten_and_book_sound,
    ``Obend.Stdlib.stdlib_cell_crossPackage_nextValue_pin_survives,
    ``Obend.Stdlib.stdlib_account_crossPackage_availableAfterFee_cone_survives,
    ``Obend.Stdlib.stdlib_quantum_photonic_flatten_and_book_sound,
    ``Obend.Stdlib.stdlib_quantum_photonic_crossPackage_cone_survives,
    ``Obend.Stdlib.stdlib_revival_flagship_claims_hold,
    ``Obend.Stdlib.stdlib_pcb_and_spacecraft_flatten_and_book_sound,
    ``Obend.Stdlib.stdlib_pcb_and_spacecraft_crossPackage_cone_survives,
    ``revival_stdlib_suite_verified
  ]
  for t in propAndClaimTargets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"

#verify_revival_zero_choice_axioms
