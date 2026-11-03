module

public import Obend.Elab.Workbook
public meta import Obend.Elab.Workbook
public import Obend.Leaf.Futamura
public import Obend.Spec.CrossPackage
import all Init.Data.String.Defs
import all Init.Data.ByteArray.Basic

/-!
# Obend.Stdlib — Multi-File `.obend` Domain Standard Library (`stdlib/{core,ledger,usd,physical}/*.obend`)

Imports the multi-file `.obend` domain standard library at compile time via `#import_obend`:
1. `stdlib/core/Cell.obend` (`StdlibCell`): capability-guarded state cell with `BaseCellSpec`,
   `VersionedCellOverride`, `next_value_open_recursion` claim, and `monotone_epoch` / `write_once_owner` laws.
2. `stdlib/ledger/Account.obend` (`StdlibAccount`): sovereign ledger & escrow account importing
   `./Cell.obend as Cell`, with `BaseAccountSpec`, `EscrowAccountOverride`, `available_open_recursion`
   claim, and `monotone_nonce` / `bounded_fee_bps` laws.
3. `stdlib/usd/ScenePrim.obend` (`StdlibScenePrim`): OpenUSD LIVRPS scene primitive importing
   `./Cell.obend as Cell`, with `SubLayerPrimSpec`, `LocalOpinionOverride`,
   `world_transform_open_recursion` claim, and `monotone_frame` law.
4. `stdlib/physical/QuantumPhotonicMatter.obend` (`StdQuantumPhotonic`): planar Clements photonic
   CTQW array (`PlanarWaveguideMeshBase` -> `KrawtchoukFaddeevCompensatedOverride`) and Majorana
   tetron Lindblad code cell (`TetronParitySectorBase` -> `LindbladCooledTetronOverride`), with
   `clements_power_open_recursion` and `tetron_braid_open_recursion` claims.

Proves compile-time gate acceptance (`FrontEnd.accept`), open-recursive claim verification,
`flatten_sound` / `book_sound`, in-place 2nd Futamura specialization (`futamura2BookCompiler_specializes_in_core`,
`inCoreBookCompiler_specializes_from_pinsOnly`), and `OB5`/`LT5` cross-package cone-pin invariance
(`coneSupports_linkComposition_of_disjoint`, `crossPackage_bEquiv_rebinds_slot_usable`).
-/

@[expose] public section

namespace Obend.Stdlib

open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Slot
open Obend.Slot.World
open Obend.Spec.CrossPackage
open Obend.Elab.Workbook

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Multi-File `#import_obend` of `stdlib/{core,ledger,usd}/*.obend` -/

#import_obend "stdlib/core/Cell.obend" as StdlibCell
#import_obend "stdlib/ledger/Account.obend" as StdlibAccount
#import_obend "stdlib/usd/ScenePrim.obend" as StdlibScenePrim
#import_obend "stdlib/physical/QuantumPhotonicMatter.obend" as StdQuantumPhotonic

/-- All three `.obend` standard library modules (`Cell.obend`, `Account.obend`, `ScenePrim.obend`)
pass `FrontEnd.accept` (including multi-file `import ./Cell.obend as Cell` resolution). -/
theorem stdlib_all_accepted :
    StdlibCell.accepted = true ∧
    StdlibAccount.accepted = true ∧
    StdlibScenePrim.accepted = true :=
  ⟨StdlibCell.accepted_eq, StdlibAccount.accepted_eq, StdlibScenePrim.accepted_eq⟩

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

/-! ## 2. Flattening, Emitted Books & In-Place 2nd Futamura Specialization on Stdlib Compositions -/

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

/-- **`stdlib_futamura2_in_core`**: in-place 1-argument `futamura2BookCompiler` specializes
the emitted `Book`s of `StdlibCell`, `StdlibAccount`, and `StdlibScenePrim` directly inside `Core4`. -/
theorem stdlib_futamura2_in_core (pins : List LeafPin) :
    dataPinSpecialize (.app (futamura2BookCompiler StdlibCell.versionedCell_book)
      (encodePinsRecordForBook StdlibCell.versionedCell_book pins)) =
      encodeBookTerm (specializeBook StdlibCell.versionedCell_book pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler StdlibAccount.escrowAccount_book)
      (encodePinsRecordForBook StdlibAccount.escrowAccount_book pins)) =
      encodeBookTerm (specializeBook StdlibAccount.escrowAccount_book pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler StdlibScenePrim.composedUsdPrim_book)
      (encodePinsRecordForBook StdlibScenePrim.composedUsdPrim_book pins)) =
      encodeBookTerm (specializeBook StdlibScenePrim.composedUsdPrim_book pins) :=
  ⟨futamura2BookCompiler_specializes_in_core StdlibCell.versionedCell_book pins,
   futamura2BookCompiler_specializes_in_core StdlibAccount.escrowAccount_book pins,
   futamura2BookCompiler_specializes_in_core StdlibScenePrim.composedUsdPrim_book pins⟩

/-- **`stdlib_inCoreBookCompiler_pinsOnly`**: true `B`-independent in-core pin specialization
via `inCoreBookCompiler` and `encodePinsOnly pins` (with NO `Book` argument to `encodePinsOnly`!)
across `StdlibCell`, `StdlibAccount`, `StdlibScenePrim`, and `modeBranchBook`. -/
theorem stdlib_inCoreBookCompiler_pinsOnly (pins : List LeafPin) :
    dataPinSpecialize (.app (inCoreBookCompiler StdlibCell.versionedCell_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook StdlibCell.versionedCell_book pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler StdlibAccount.escrowAccount_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook StdlibAccount.escrowAccount_book pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler StdlibScenePrim.composedUsdPrim_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook StdlibScenePrim.composedUsdPrim_book pins) ∧
    ((decodeBookTerm?
      (dataPinSpecialize (.app (inCoreBookCompiler modeBranchBook) (encodePinsOnly [⟨"mode", .nat 0⟩])))).bind
      (fun B_res => evalResidualBookAt B_res "compute" (.nat 0))) =
      some (.nat 42) ∧
    ((decodeBookTerm?
      (dataPinSpecialize (.app (inCoreBookCompiler modeBranchBook) (encodePinsOnly [⟨"mode", .nat 1⟩])))).bind
      (fun B_res => evalResidualBookAt B_res "compute" (.nat 0))) =
      some (.nat 99) :=
  ⟨(inCoreBookCompiler_specializes_from_pinsOnly StdlibCell.versionedCell_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly StdlibAccount.escrowAccount_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly StdlibScenePrim.composedUsdPrim_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly modeBranchBook pins).2.2.2.2.1,
   (inCoreBookCompiler_specializes_from_pinsOnly modeBranchBook pins).2.2.2.2.2.1⟩

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

/-- **`stdlib_quantum_photonic_accepted_and_claims_hold`**:
`stdlib/physical/QuantumPhotonicMatter.obend` (`StdQuantumPhotonic`) passes `FrontEnd.accept = true`,
discharges both open-recursion claims (`clements_power_open_recursion` and `tetron_braid_open_recursion`),
and evaluates the open-recursive methods of both composed quantum/photonic objects:
- `clementsPowerAt20Mw = 90` (`20 * 4 + 10`)
- `clementsPhaseAtStep4 = 150` (`(4 * 25) + 50`)
- `tetronBraidPhaseAt2 = 420` (`2 * 90 + 240`)
- `tetronResetRateAt10 = 72` (`(10 * 3 + 12) + 30`). -/
theorem stdlib_quantum_photonic_accepted_and_claims_hold :
    StdQuantumPhotonic.accepted = true ∧
    obligationMeaningWithJudges workbookFormats
      StdQuantumPhotonic.claim_clements_power_open_recursion_obj
      StdQuantumPhotonic.claim_clements_power_open_recursion_just ∧
    obligationMeaningWithJudges workbookFormats
      StdQuantumPhotonic.claim_tetron_braid_open_recursion_obj
      StdQuantumPhotonic.claim_tetron_braid_open_recursion_just ∧
    StdQuantumPhotonic.clementsPowerAt20Mw_val = .nat 90 ∧
    StdQuantumPhotonic.clementsPhaseAtStep4_val = .nat 150 ∧
    StdQuantumPhotonic.tetronBraidPhaseAt2_val = .nat 420 ∧
    StdQuantumPhotonic.tetronResetRateAt10_val = .nat 72 :=
  ⟨StdQuantumPhotonic.accepted_eq,
   StdQuantumPhotonic.claim_clements_power_open_recursion_holds,
   StdQuantumPhotonic.claim_tetron_braid_open_recursion_holds,
   rfl, rfl, rfl, rfl⟩

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

/-- **`stdlib_quantum_photonic_inCore_futamura2`**:
Specializes `StdQuantumPhotonic`'s emitted `Book`s (`compensatedClementsArray_book` and
`cooledTetronCell_book`) directly inside `Core4` via `inCoreBookCompiler` and `encodePinsOnly pins`
(as well as `futamura2BookCompiler`). -/
theorem stdlib_quantum_photonic_inCore_futamura2 (pins : List LeafPin) :
    dataPinSpecialize
      (.app (inCoreBookCompiler StdQuantumPhotonic.compensatedClementsArray_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook StdQuantumPhotonic.compensatedClementsArray_book pins) ∧
    dataPinSpecialize
      (.app (inCoreBookCompiler StdQuantumPhotonic.cooledTetronCell_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook StdQuantumPhotonic.cooledTetronCell_book pins) ∧
    dataPinSpecialize
      (.app (futamura2BookCompiler StdQuantumPhotonic.compensatedClementsArray_book)
        (encodePinsRecordForBook StdQuantumPhotonic.compensatedClementsArray_book pins)) =
      encodeBookTerm (specializeBook StdQuantumPhotonic.compensatedClementsArray_book pins) ∧
    dataPinSpecialize
      (.app (futamura2BookCompiler StdQuantumPhotonic.cooledTetronCell_book)
        (encodePinsRecordForBook StdQuantumPhotonic.cooledTetronCell_book pins)) =
      encodeBookTerm (specializeBook StdQuantumPhotonic.cooledTetronCell_book pins) :=
  ⟨(inCoreBookCompiler_specializes_from_pinsOnly StdQuantumPhotonic.compensatedClementsArray_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly StdQuantumPhotonic.cooledTetronCell_book pins).1,
   futamura2BookCompiler_specializes_in_core StdQuantumPhotonic.compensatedClementsArray_book pins,
   futamura2BookCompiler_specializes_in_core StdQuantumPhotonic.cooledTetronCell_book pins⟩

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

end Obend.Stdlib

end
