module

public import Obend.Elab.Workbook
public meta import Obend.Elab.Workbook
public import Obend.Leaf.Static
public import Obend.Spec.CrossPackage
public import Obend.Hardware.UserspacePhysical
import all Init.Data.String.Defs
import all Init.Data.ByteArray.Basic

/-!
# Obend.Stdlib — Multi-File `.obend` Domain Standard Library (`stdlib/{core,ledger,usd,physical}/*.obend`)

Imports and certifies the complete 11-module `.obend` domain standard library at compile time via
`#import_obend`, including the 4 Tier-1 hardware physical modules:
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
5. `stdlib/physical/QuantumPhotonicMatter.obend` (`StdQuantumPhotonic`): planar Clements photonic
   CTQW array (with unitary MZI Cauchy–Schwarz bound) and Majorana tetron Lindblad code cell
   (with braid-exchange norm doubling and parity involution claims).
6. `stdlib/physical/MultiphysicsPcbTempest.obend` (`StdMultiphysicsPcb`): differential stripline
   AM-GM bound & mode-impedance product, copper-etch DFM undercut margin, sub-cutoff
   (`λ_min / 20`) Faraday via-fence rule, and dual-rail WDDL constant-weight balance invariants.
7. `stdlib/physical/SymplecticSpacecraft6Dof.obend` (`StdSymplecticSpacecraft`): rational Cayley
   attitude norm preservation & 3D Lagrange orthogonality, multi-stage impulse/mass conservation,
   and radiative-ablative TPS thermal margin laws.
8. Tier-1 hardware physical standard library (`Obend.Hardware.UserspacePhysical`:
   `LcDrivesStator`, `Ms350FcmlPhaseLeg`, `CleanroomTcadStack`, `Cnc5AxisMill`).

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

/-! ## 1. Multi-File `#import_obend` of All 11 `stdlib/{core,ledger,usd,physical}/*.obend` Modules -/

#import_obend "stdlib/core/Cell.obend" as StdlibCell
#import_obend "stdlib/core/Word64.obend" as StdlibWord64
#import_obend "stdlib/ledger/Account.obend" as StdlibAccount
#import_obend "stdlib/usd/ScenePrim.obend" as StdlibScenePrim
#import_obend "stdlib/physical/QuantumPhotonicMatter.obend" as StdQuantumPhotonic
#import_obend "stdlib/physical/MultiphysicsPcbTempest.obend" as StdMultiphysicsPcb
#import_obend "stdlib/physical/SymplecticSpacecraft6Dof.obend" as StdSymplecticSpacecraft
-- `StdLcDrivesStator`, `StdMs350FcmlPhaseLeg`, `StdCleanroomTcadStack`, and `StdCnc5AxisMill`
-- are elaborated once in Tier-1 `Obend.Hardware.UserspacePhysical` and re-exported here.

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

/-! ## 4. Quantum Photonic Matter Standard Library (`stdlib/physical/QuantumPhotonicMatter.obend`) -/

/-- Values the `#import_obend` elaboration of `StdQuantumPhotonic` produced. -/
example :
    StdQuantumPhotonic.clementsPowerAt20Mw_val = .nat 90 ∧
    StdQuantumPhotonic.clementsPhaseAtStep4_val = .nat 150 ∧
    StdQuantumPhotonic.tetronBraidPhaseAt2_val = .nat 420 ∧
    StdQuantumPhotonic.tetronResetRateAt10_val = .nat 72 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem stdlib_quantum_photonic_compositions_closed :
    StdQuantumPhotonic.compensatedClementsArray_comp.closedB = true ∧
    StdQuantumPhotonic.cooledTetronCell_comp.closedB = true := by
  decide +kernel

/-- **`stdlib_quantum_photonic_flatten_and_book_sound`**:
For every member `m`, both composed quantum/photonic objects (`compensatedClementsArray_comp` and
`cooledTetronCell_comp`) are observationally equivalent (`≈b`) to their flattened objects and
emitted `Leaf.Book`s. -/
theorem stdlib_quantum_photonic_flatten_and_book_sound (m : String) :
    (.get StdQuantumPhotonic.compensatedClementsArray_comp.flatten m ≈b
      .get StdQuantumPhotonic.compensatedClementsArray_comp.object m) ∧
    (.get (emit StdQuantumPhotonic.compensatedClementsArray_comp).link m ≈b
      .get StdQuantumPhotonic.compensatedClementsArray_comp.object m) ∧
    (.get StdQuantumPhotonic.cooledTetronCell_comp.flatten m ≈b
      .get StdQuantumPhotonic.cooledTetronCell_comp.object m) ∧
    (.get (emit StdQuantumPhotonic.cooledTetronCell_comp).link m ≈b
      .get StdQuantumPhotonic.cooledTetronCell_comp.object m) := by
  have ⟨hc1, hc2⟩ := stdlib_quantum_photonic_compositions_closed
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m⟩

/-- Disjoint Faddeev–LeVerrier thermal-only override layer modifying only
`["faddeevThermalResidualPpm", "szegedyQuotientStepPhaseMrad"]` (leaving `krawtchoukRatioWeight`
and `transferredOpticalPowerMw` untouched). -/
def faddeevThermalOnlyLayer : Layer where
  name := "QuantumPhotonicMatter.FaddeevThermalOnlyOverride"
  flat := false
  metadata := .record []
  fields := [
    ("faddeevThermalResidualPpm", .nat 0),
    ("szegedyQuotientStepPhaseMrad", .lam (.binary .add (.bound 0) (.nat 50)))
  ]

/-- Disjoint Lindblad cooling-only override layer modifying only
`["breakingScoreFloor", "lindbladResetRateKhz"]` (leaving `cliffordParityGapUeV`
and `ivanovBraidPhaseMrad` untouched). -/
def lindbladCoolingOnlyLayer : Layer where
  name := "QuantumPhotonicMatter.LindbladCoolingOnlyOverride"
  flat := false
  metadata := .record []
  fields := [
    ("breakingScoreFloor", .nat 0),
    ("lindbladResetRateKhz", .lam (.binary .add (.bound 0) (.nat 30)))
  ]

/-- **`stdlib_quantum_photonic_crossPackage_cone_survives`**:
Proves via `coneSupports_linkComposition_of_disjoint` that:
1. `KrawtchoukFaddeevCompensatedOverride` preserves the unmodified cone pin `["transferredOpticalPowerMw"]`,
   and `faddeevThermalOnlyLayer` preserves the full `slotReadCone` of `"transferredOpticalPowerMw"` on `planarWaveguideMesh_comp`.
2. `LindbladCooledTetronOverride` preserves the unmodified cone pin `["ivanovBraidPhaseMrad"]`,
   and `lindbladCoolingOnlyLayer` preserves the full `slotReadCone` of `"ivanovBraidPhaseMrad"` on `baseTetronCell_comp`.
3. Under an observationally equivalent refactor `cert : EquivOverrideCert`, `rebindEquivPin` and
   `crossPackage_bEquiv_rebinds_slot_usable` re-bind the overridden cone pin cleanly while preserving
   `specSlot.usable = true`, `transportSlot.usable = true`, `TransportMeaning`, and observational equivalence (`≈b`). -/
theorem stdlib_quantum_photonic_crossPackage_cone_survives :
    let Cc := StdQuantumPhotonic.planarWaveguideMesh_comp
    let Lc := StdQuantumPhotonic.compensatedClementsArray_comp.top
    let Ct := StdQuantumPhotonic.baseTetronCell_comp
    let Lt := StdQuantumPhotonic.cooledTetronCell_comp.top
    coneSupports (linkComposition Cc Lc) ["transferredOpticalPowerMw"] =
      coneSupports Cc ["transferredOpticalPowerMw"] ∧
    coneSupports (linkComposition Cc faddeevThermalOnlyLayer) (slotReadCone Cc "transferredOpticalPowerMw") =
      coneSupports Cc (slotReadCone Cc "transferredOpticalPowerMw") ∧
    coneSupports (linkComposition Ct Lt) ["ivanovBraidPhaseMrad"] =
      coneSupports Ct ["ivanovBraidPhaseMrad"] ∧
    coneSupports (linkComposition Ct lindbladCoolingOnlyLayer) (slotReadCone Ct "ivanovBraidPhaseMrad") =
      coneSupports Ct (slotReadCone Ct "ivanovBraidPhaseMrad") ∧
    (∀ {objectName target m : String} {L : Layer} {defItem : LeafDef}
       {v' : LeafView} {o : TransportObj} {c : TransportCert} {s : Nat}
       (cert : EquivOverrideCert Ct L m) (Frame : Term),
      (.get Ct.object target ≈b instantiate Frame (.get Ct.object m)) →
      (.get (linkComposition Ct L).object target ≈b instantiate Frame (.get (linkComposition Ct L).object m)) →
      (linkComposition Ct L).closedB = true →
      holdsAt v' (rebindEquivPin cert (memberConePin Ct m)) = true →
      (∀ m' ∈ slotReadCone (linkComposition Ct L) target, m' ≠ m →
        holdsAt v' (memberConePin (linkComposition Ct L) m') = true) →
      (transportSlot o).usable (Support.holds Ct s) c = true →
      (∀ sp ∈ c.supports, sp.member ≠ m →
        Obend.Logic.symUnfold (linkComposition Ct L) s sp.member = Obend.Logic.symUnfold Ct s sp.member) →
      rebindEquivPin cert (memberConePin Ct m) = memberConePin (linkComposition Ct L) m ∧
      specSlot.usable (holdsAt v') (rebindEquivSlotCandidate objectName target cert defItem) = true ∧
      (transportSlot o).usable (Support.holds (linkComposition Ct L) s) (rebindEquivTransportCert cert s c) = true ∧
      TransportMeaning o (rebindEquivTransportCert cert s c) ∧
      (.get (linkComposition Ct L).object target ≈b .get Ct.object target)) := by
  intro Cc Lc Ct Lt
  have hflat_c : Lc.flat = false := by decide +kernel
  have hdisj_c1 : ∀ m ∈ ["transferredOpticalPowerMw"], m ∉ overlayModifiedFields Lc := by decide +kernel
  have hflat_ft : faddeevThermalOnlyLayer.flat = false := rfl
  have hdisj_c2 : ∀ m ∈ slotReadCone Cc "transferredOpticalPowerMw", m ∉ overlayModifiedFields faddeevThermalOnlyLayer := by
    decide +kernel
  have hflat_t : Lt.flat = false := by decide +kernel
  have hdisj_t1 : ∀ m ∈ ["ivanovBraidPhaseMrad"], m ∉ overlayModifiedFields Lt := by decide +kernel
  have hflat_lt : lindbladCoolingOnlyLayer.flat = false := rfl
  have hdisj_t2 : ∀ m ∈ slotReadCone Ct "ivanovBraidPhaseMrad", m ∉ overlayModifiedFields lindbladCoolingOnlyLayer := by
    decide +kernel
  refine ⟨coneSupports_linkComposition_of_disjoint Cc Lc ["transferredOpticalPowerMw"] hflat_c hdisj_c1,
          coneSupports_linkComposition_of_disjoint Cc faddeevThermalOnlyLayer
            (slotReadCone Cc "transferredOpticalPowerMw") hflat_ft hdisj_c2,
          coneSupports_linkComposition_of_disjoint Ct Lt ["ivanovBraidPhaseMrad"] hflat_t hdisj_t1,
          coneSupports_linkComposition_of_disjoint Ct lindbladCoolingOnlyLayer
            (slotReadCone Ct "ivanovBraidPhaseMrad") hflat_lt hdisj_t2, ?_⟩
  intro objectName target m L defItem v' o c s cert Frame htb htl hcl hpin hrest htu htr
  have hreb := @crossPackage_bEquiv_rebinds_slot_usable objectName target m Ct L defItem v' o c s
    cert Frame htb htl hcl hpin hrest htu htr
  exact ⟨rebindEquivPin_memberConePin cert, hreb.2.1, hreb.2.2.1, hreb.2.2.2.1, hreb.2.2.2.2⟩

/-! ## 5. Revived `Word64`, `MultiphysicsPcbTempest`, `SymplecticSpacecraft6Dof`, and Tier-1 Physical Claims -/

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
