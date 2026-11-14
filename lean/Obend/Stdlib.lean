module

public import Obend.Elab.Workbook
public meta import Obend.Elab.Workbook
public import Obend.Leaf.Static
public import Obend.Spec.CrossPackage
import all Init.Data.String.Defs
import all Init.Data.ByteArray.Basic

/-!
# Obend.Stdlib — Multi-File `.obend` Domain Standard Library (`stdlib/{core,ledger,usd,physical}/*.obend`)

Imports and certifies the complete 10-module `.obend` domain standard library at compile time via
`#import_obend`, including the 4 physical engineering modules:
1. `stdlib/core/Cell.obend` (`StdlibCell`): capability-guarded state cell with `BaseCellSpec`,
   `VersionedCellOverride`, monotonicity/open-recursion/override claims, and `monotone_epoch` /
   `write_once_owner` laws.
2. `stdlib/core/Word64.obend` (`StdlibWord64`): 64-bit modular machine-word and `Q32.32` fixed-point
   specification with two's-complement cancellation, shift floor conservation, signed comparison
   headroom, and exact `Q32.32` product claims.
3. `stdlib/ledger/Account.obend` (`StdlibAccount`): sovereign ledger & escrow account importing
   `../core/Cell.obend as Cell`, with double-entry transfer conservation, fee-cap envelope, and escrow override claims.
4. `stdlib/usd/ScenePrim.obend` (`StdlibScenePrim`): OpenUSD LIVRPS scene primitive importing
   `../core/Cell.obend as Cell`, with xformOp stack composition and LIVRPS local-opinion override claims.
5. `stdlib/physical/MultiphysicsPcbTempest.obend` (`StdMultiphysicsPcb`): differential stripline
   AM-GM bound & mode-impedance product, copper-etch DFM undercut margin, sub-cutoff
   (`λ_min / 20`) Faraday via-fence rule, and dual-rail WDDL constant-weight balance invariants.
6. `stdlib/physical/SymplecticSpacecraft6Dof.obend` (`StdSymplecticSpacecraft`): rational Cayley
   attitude norm preservation & 3D Lagrange orthogonality, multi-stage impulse/mass conservation,
   and radiative-ablative TPS thermal margin laws.
7. Physical standard library (`LcDrivesStator`, `Ms350FcmlPhaseLeg`, `CleanroomTcadStack`, `Cnc5AxisMill`).

Proves compile-time gate acceptance (`FrontEnd.accept`), relational engineering claim verification,
`flatten_sound` / `book_sound`, and `OB5`/`LT5` cross-package cone-pin invariance
(`coneSupports_linkComposition_of_disjoint`, `crossPackage_bEquiv_rebinds_slot_usable`).
-/

public section

namespace Obend.Stdlib

open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Slot
open Obend.Slot.World
open Obend.Spec.CrossPackage
open Obend.Elab.Workbook

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Multi-File `#import_obend` of All 10 `stdlib/{core,ledger,usd,physical}/*.obend` Modules -/

#import_obend "stdlib/core/Cell.obend" as StdlibCell
#import_obend "stdlib/core/Word64.obend" as StdlibWord64
#import_obend "stdlib/ledger/Account.obend" as StdlibAccount
#import_obend "stdlib/usd/ScenePrim.obend" as StdlibScenePrim
#import_obend "stdlib/physical/MultiphysicsPcbTempest.obend" as StdMultiphysicsPcb
#import_obend "stdlib/physical/SymplecticSpacecraft6Dof.obend" as StdSymplecticSpacecraft
#import_obend "stdlib/physical/LcDrivesStator.obend" as StdLcDrivesStator
#import_obend "stdlib/physical/Ms350FcmlPhaseLeg.obend" as StdMs350FcmlPhaseLeg
#import_obend "stdlib/physical/CleanroomTcadStack.obend" as StdCleanroomTcadStack
#import_obend "stdlib/physical/Cnc5AxisMill.obend" as StdCnc5AxisMill

/-- All open-recursion claims across `Cell.obend`, `Account.obend`, and `ScenePrim.obend`
are discharged and their semantic obligation meanings hold. -/
theorem stdlib_all_claims_hold :
    obligationMeaningWithJudges workbookFormats
      StdlibCell.claim_next_value_open_recursion_obj
      StdlibCell.claim_next_value_open_recursion_just ∧
    obligationMeaningWithJudges workbookFormats
      StdlibAccount.claim_available_open_recursion_obj
      StdlibAccount.claim_available_open_recursion_just ∧
    obligationMeaningWithJudges workbookFormats
      StdlibScenePrim.claim_world_transform_open_recursion_obj
      StdlibScenePrim.claim_world_transform_open_recursion_just :=
  ⟨StdlibCell.claim_next_value_open_recursion_holds,
   StdlibAccount.claim_available_open_recursion_holds,
   StdlibScenePrim.claim_world_transform_open_recursion_holds⟩

/-- Multi-module law inheritance: `Account` and `ScenePrim` inherit `Cell.obend`'s 2 laws
(`monotone_epoch`, `write_once_owner`) in addition to their own package laws. -/
theorem stdlib_inherited_laws_count :
    StdlibCell.package.laws.length = 2 ∧
    StdlibAccount.package.laws.length = 4 ∧
    StdlibScenePrim.package.laws.length = 3 := by
  decide +kernel

/-- Concrete open-recursive evaluation across the 3 `.obend` standard library modules:
- `StdlibCell`: `versionedCellNextAt25 = 125` (`100 + 25`), `versionedCellGasAt4 = 32` (`(4 * 5 + 2) + 10`)
- `StdlibAccount` (importing `Cell.baseCell().value = 100`):
  `escrowAvailableAt10 = 1020` (`(100 + 900) + 10 * 2`), `escrowSettlementAt100 = 270` (`(100 + 150) + 20`)
- `StdlibScenePrim` (importing `Cell.baseCell().epoch = 1`):
  `composedWorldTransformAt100 = 140` (`100 + 40`), `composedVoxelCostAt5 = 28` (`5 * (1 + 3) + 8`). -/
theorem stdlib_open_recursion_eval :
    StdlibCell.versionedCellNextAt25_val = .nat 125 ∧
    StdlibCell.versionedCellGasAt4_val = .nat 32 ∧
    StdlibAccount.escrowAvailableAt10_val = .nat 1020 ∧
    StdlibAccount.escrowSettlementAt100_val = .nat 270 ∧
    StdlibScenePrim.composedWorldTransformAt100_val = .nat 140 ∧
    StdlibScenePrim.composedVoxelCostAt5_val = .nat 28 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Flattening and Emitted Books on Stdlib Compositions -/

theorem stdlib_compositions_closed :
    StdlibCell.versionedCell_comp.closedB = true ∧
    StdlibAccount.escrowAccount_comp.closedB = true ∧
    StdlibScenePrim.composedUsdPrim_comp.closedB = true := by
  decide +kernel

/-- **`stdlib_flatten_and_book_sound`**: every member `m` of `versionedCell_comp`,
`escrowAccount_comp`, and `composedUsdPrim_comp` is observationally equivalent (`≈b`) to its
flattened object and emitted `Leaf.Book`. -/
theorem stdlib_flatten_and_book_sound (m : String) :
    (.get StdlibCell.versionedCell_comp.flatten m ≈b .get StdlibCell.versionedCell_comp.object m) ∧
    (.get (emit StdlibCell.versionedCell_comp).link m ≈b .get StdlibCell.versionedCell_comp.object m) ∧
    (.get StdlibAccount.escrowAccount_comp.flatten m ≈b .get StdlibAccount.escrowAccount_comp.object m) ∧
    (.get (emit StdlibAccount.escrowAccount_comp).link m ≈b .get StdlibAccount.escrowAccount_comp.object m) ∧
    (.get StdlibScenePrim.composedUsdPrim_comp.flatten m ≈b .get StdlibScenePrim.composedUsdPrim_comp.object m) ∧
    (.get (emit StdlibScenePrim.composedUsdPrim_comp).link m ≈b .get StdlibScenePrim.composedUsdPrim_comp.object m) := by
  have ⟨hc1, hc2, hc3⟩ := stdlib_compositions_closed
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m,
         flatten_sound _ hc3 m, book_sound _ hc3 m⟩

/-! ## 3. Cross-Package Cone-Pin Survival on Stdlib Compositions (`OB5` / `LT5`) -/

/-- `VersionedCellOverride` modifies `["epoch", "gasCost"]`, which is disjoint from `"value"`
and `"nextValue"` (`nextValue` reads only `"value"`). Linking `VersionedCellOverride` onto
`baseCell_comp` preserves the symbolic unfolding, provenance, and cone pin of `"nextValue"`
and `"value"`. -/
theorem stdlib_cell_crossPackage_nextValue_pin_survives :
    let C := StdlibCell.baseCell_comp
    let L := StdlibCell.versionedCell_comp.top
    (linkComposition C L).symUnfold "nextValue" = C.symUnfold "nextValue" ∧
    (linkComposition C L).provenance "nextValue" = C.provenance "nextValue" ∧
    memberConePin (linkComposition C L) "nextValue" = memberConePin C "nextValue" ∧
    coneSupports (linkComposition C L) (slotReadCone C "nextValue") =
      coneSupports C (slotReadCone C "nextValue") := by
  intro C L
  have hflat : L.flat = false := rfl
  have hnot : "nextValue" ∉ overlayModifiedFields L := by decide +kernel
  have hdisj : ∀ m ∈ slotReadCone C "nextValue", m ∉ overlayModifiedFields L := by decide +kernel
  have ⟨h1, h2, h3⟩ := symUnfold_linkComposition_of_not_mem C L "nextValue" hflat hnot
  have h4 := coneSupports_linkComposition_of_disjoint C L (slotReadCone C "nextValue") hflat hdisj
  exact ⟨h1, h2, h3, h4⟩

/-- `EscrowAccountOverride` modifies `["reserveFloor", "totalSettlement"]`, which is disjoint from
`slotReadCone StdlibAccount.baseAccount_comp "availableAfterFee"` (`["availableAfterFee", "balance", "feeRate"]`).
Linking `EscrowAccountOverride` preserves the entire cone support of `"availableAfterFee"`. -/
theorem stdlib_account_crossPackage_availableAfterFee_cone_survives :
    let C := StdlibAccount.baseAccount_comp
    let L := StdlibAccount.escrowAccount_comp.top
    coneSupports (linkComposition C L) (slotReadCone C "availableAfterFee") =
      coneSupports C (slotReadCone C "availableAfterFee") := by
  intro C L
  have hflat : L.flat = false := rfl
  have hdisj : ∀ m ∈ slotReadCone C "availableAfterFee", m ∉ overlayModifiedFields L := by decide +kernel
  exact coneSupports_linkComposition_of_disjoint C L (slotReadCone C "availableAfterFee") hflat hdisj

/-! ## 4. Revived `Word64`, `MultiphysicsPcbTempest`, `SymplecticSpacecraft6Dof`, and Physical Claims -/

/-- All flagship relational engineering claims across `Word64.obend`,
`MultiphysicsPcbTempest.obend`, `SymplecticSpacecraft6Dof.obend`, and the 4 Tier-1 physical
modules (`LcDrivesStator`, `Ms350FcmlPhaseLeg`, `CleanroomTcadStack`, `Cnc5AxisMill`) are
discharged and their semantic obligation meanings hold. -/
theorem stdlib_revival_flagship_claims_hold :
    obligationMeaningWithJudges workbookFormats
      StdlibWord64.claim_sub64_twos_complement_cancel_obj
      StdlibWord64.claim_sub64_twos_complement_cancel_just ∧
    obligationMeaningWithJudges workbookFormats
      StdlibWord64.claim_slt64_nonneg_no_wrap_headroom_obj
      StdlibWord64.claim_slt64_nonneg_no_wrap_headroom_just ∧
    obligationMeaningWithJudges workbookFormats
      StdMultiphysicsPcb.claim_stripline_impedance_amgm_bound_obj
      StdMultiphysicsPcb.claim_stripline_impedance_amgm_bound_just ∧
    obligationMeaningWithJudges workbookFormats
      StdMultiphysicsPcb.claim_faraday_via_fence_subcutoff_bound_obj
      StdMultiphysicsPcb.claim_faraday_via_fence_subcutoff_bound_just ∧
    obligationMeaningWithJudges workbookFormats
      StdMultiphysicsPcb.claim_wddl_complementary_zero_crowbar_obj
      StdMultiphysicsPcb.claim_wddl_complementary_zero_crowbar_just ∧
    obligationMeaningWithJudges workbookFormats
      StdMultiphysicsPcb.claim_wddl_constant_dynamic_power_obj
      StdMultiphysicsPcb.claim_wddl_constant_dynamic_power_just ∧
    obligationMeaningWithJudges workbookFormats
      StdSymplecticSpacecraft.claim_cayley_planar_attitude_norm_preserved_obj
      StdSymplecticSpacecraft.claim_cayley_planar_attitude_norm_preserved_just ∧
    obligationMeaningWithJudges workbookFormats
      StdSymplecticSpacecraft.claim_cayley_3d_lagrange_orthogonality_obj
      StdSymplecticSpacecraft.claim_cayley_3d_lagrange_orthogonality_just ∧
    obligationMeaningWithJudges workbookFormats
      StdSymplecticSpacecraft.claim_multistage_impulse_mass_conservation_obj
      StdSymplecticSpacecraft.claim_multistage_impulse_mass_conservation_just ∧
    obligationMeaningWithJudges workbookFormats
      StdSymplecticSpacecraft.claim_radiative_ablative_thermal_margin_obj
      StdSymplecticSpacecraft.claim_radiative_ablative_thermal_margin_just ∧
    obligationMeaningWithJudges workbookFormats
      StdLcDrivesStator.claim_inslot_class_h_thermal_envelope_obj
      StdLcDrivesStator.claim_inslot_class_h_thermal_envelope_just ∧
    obligationMeaningWithJudges workbookFormats
      StdMs350FcmlPhaseLeg.claim_fcml_6cell_voltage_stress_reduction_obj
      StdMs350FcmlPhaseLeg.claim_fcml_6cell_voltage_stress_reduction_just ∧
    obligationMeaningWithJudges workbookFormats
      StdCleanroomTcadStack.claim_hkmg_drain_overdrive_envelope_obj
      StdCleanroomTcadStack.claim_hkmg_drain_overdrive_envelope_just ∧
    obligationMeaningWithJudges workbookFormats
      StdCnc5AxisMill.claim_abbe_ruckig_error_contraction_obj
      StdCnc5AxisMill.claim_abbe_ruckig_error_contraction_just :=
  ⟨StdlibWord64.claim_sub64_twos_complement_cancel_holds,
   StdlibWord64.claim_slt64_nonneg_no_wrap_headroom_holds,
   StdMultiphysicsPcb.claim_stripline_impedance_amgm_bound_holds,
   StdMultiphysicsPcb.claim_faraday_via_fence_subcutoff_bound_holds,
   StdMultiphysicsPcb.claim_wddl_complementary_zero_crowbar_holds,
   StdMultiphysicsPcb.claim_wddl_constant_dynamic_power_holds,
   StdSymplecticSpacecraft.claim_cayley_planar_attitude_norm_preserved_holds,
   StdSymplecticSpacecraft.claim_cayley_3d_lagrange_orthogonality_holds,
   StdSymplecticSpacecraft.claim_multistage_impulse_mass_conservation_holds,
   StdSymplecticSpacecraft.claim_radiative_ablative_thermal_margin_holds,
   StdLcDrivesStator.claim_inslot_class_h_thermal_envelope_holds,
   StdMs350FcmlPhaseLeg.claim_fcml_6cell_voltage_stress_reduction_holds,
   StdCleanroomTcadStack.claim_hkmg_drain_overdrive_envelope_holds,
   StdCnc5AxisMill.claim_abbe_ruckig_error_contraction_holds⟩

/-- Package law counts and concrete open-recursive evaluations for `MultiphysicsPcbTempest`,
`SymplecticSpacecraft6Dof`, and `Word64`. -/
theorem stdlib_pcb_and_spacecraft_laws_and_eval :
    StdMultiphysicsPcb.package.laws.length = 4 ∧
    StdSymplecticSpacecraft.package.laws.length = 4 ∧
    StdMultiphysicsPcb.tempestDiffImpedanceMohm_val = .nat 100000 ∧
    StdMultiphysicsPcb.tempestEtchedWidthAt120Um_val = .nat 156 ∧
    StdMultiphysicsPcb.tempestCutoffAt12Ghz_val = .nat 96500 ∧
    StdSymplecticSpacecraft.spacecraftCayleyDenomAt200_val = .nat 1040000 ∧
    StdSymplecticSpacecraft.spacecraftImpulseAt500Kg_val = .nat 1741450 ∧
    StdSymplecticSpacecraft.spacecraftTpsAt40g800Kw_val = .nat 1800 ∧
    StdlibWord64.word64AddSample_val = .nat 155 ∧
    StdlibWord64.word64Qmul32Sample_val = .nat 25769803776 := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stdlib_pcb_and_spacecraft_compositions_closed :
    StdlibWord64.pureWord64_comp.closedB = true ∧
    StdMultiphysicsPcb.tempestShieldedBoard_comp.closedB = true ∧
    StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp.closedB = true := by
  decide +kernel

/-- **`stdlib_pcb_and_spacecraft_flatten_and_book_sound`**: every member `m` of
`pureWord64_comp`, `tempestShieldedBoard_comp`, and `symplecticSpacecraft6Dof_comp` is
observationally equivalent (`≈b`) to its flattened object and emitted `Leaf.Book`. -/
theorem stdlib_pcb_and_spacecraft_flatten_and_book_sound (m : String) :
    (.get StdlibWord64.pureWord64_comp.flatten m ≈b .get StdlibWord64.pureWord64_comp.object m) ∧
    (.get (emit StdlibWord64.pureWord64_comp).link m ≈b .get StdlibWord64.pureWord64_comp.object m) ∧
    (.get StdMultiphysicsPcb.tempestShieldedBoard_comp.flatten m ≈b
      .get StdMultiphysicsPcb.tempestShieldedBoard_comp.object m) ∧
    (.get (emit StdMultiphysicsPcb.tempestShieldedBoard_comp).link m ≈b
      .get StdMultiphysicsPcb.tempestShieldedBoard_comp.object m) ∧
    (.get StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp.flatten m ≈b
      .get StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp.object m) ∧
    (.get (emit StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp).link m ≈b
      .get StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp.object m) := by
  have ⟨hc1, hc2, hc3⟩ := stdlib_pcb_and_spacecraft_compositions_closed
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m,
         flatten_sound _ hc3 m, book_sound _ hc3 m⟩

/-- **`stdlib_pcb_and_spacecraft_crossPackage_cone_survives`**:
1. `TempestFaradayWddlOverride` modifies `["oddModeImpedanceMohm", "copperThicknessUm", "viaFencePitchUm", "viaFenceCutoffMarginGhzMm"]`,
   preserving the entire `slotReadCone` of `"wddlPairChargefJ"` on `baseStriplineBoard_comp`.
2. `CayleySymplecticThermalOverride` modifies `["exhaustVelocityMps", "dryMassKg", "ablativeEnthalpyMjPerKg", "tpsThermalCapacityKwPerM2"]`,
   preserving the entire `slotReadCone` of `"cayleyScaleDenom"` on `nominalRigidSpacecraft_comp`. -/
theorem stdlib_pcb_and_spacecraft_crossPackage_cone_survives :
    let Cp := StdMultiphysicsPcb.baseStriplineBoard_comp
    let Lp := StdMultiphysicsPcb.tempestShieldedBoard_comp.top
    let Cs := StdSymplecticSpacecraft.nominalRigidSpacecraft_comp
    let Ls := StdSymplecticSpacecraft.symplecticSpacecraft6Dof_comp.top
    coneSupports (linkComposition Cp Lp) (slotReadCone Cp "wddlPairChargefJ") =
      coneSupports Cp (slotReadCone Cp "wddlPairChargefJ") ∧
    coneSupports (linkComposition Cs Ls) (slotReadCone Cs "cayleyScaleDenom") =
      coneSupports Cs (slotReadCone Cs "cayleyScaleDenom") := by
  intro Cp Lp Cs Ls
  have hfp : Lp.flat = false := by decide +kernel
  have hdp : ∀ m ∈ slotReadCone Cp "wddlPairChargefJ", m ∉ overlayModifiedFields Lp := by decide +kernel
  have hfs : Ls.flat = false := by decide +kernel
  have hds : ∀ m ∈ slotReadCone Cs "cayleyScaleDenom", m ∉ overlayModifiedFields Ls := by decide +kernel
  exact ⟨coneSupports_linkComposition_of_disjoint Cp Lp (slotReadCone Cp "wddlPairChargefJ") hfp hdp,
         coneSupports_linkComposition_of_disjoint Cs Ls (slotReadCone Cs "cayleyScaleDenom") hfs hds⟩

end Obend.Stdlib

end
