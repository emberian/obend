/-
# Obend.Stdlib — Multi-File `.obend` Domain Standard Library (`stdlib/{core,ledger,usd}/*.obend`)

Imports the multi-file `.obend` domain standard library at compile time via `#import_obend`:
1. `stdlib/core/Cell.obend` (`StdlibCell`): capability-guarded state cell with `BaseCellSpec`,
   `VersionedCellOverride`, `next_value_open_recursion` claim, and `monotone_epoch` / `write_once_owner` laws.
2. `stdlib/ledger/Account.obend` (`StdlibAccount`): sovereign ledger & escrow account importing
   `./Cell.obend as Cell`, with `BaseAccountSpec`, `EscrowAccountOverride`, `available_open_recursion`
   claim, and `monotone_nonce` / `bounded_fee_bps` laws.
3. `stdlib/usd/ScenePrim.obend` (`StdlibScenePrim`): OpenUSD LIVRPS scene primitive importing
   `./Cell.obend as Cell`, with `SubLayerPrimSpec`, `LocalOpinionOverride`,
   `world_transform_open_recursion` claim, and `monotone_frame` law.

Proves compile-time gate acceptance (`FrontEnd.accept`), open-recursive claim verification,
`flatten_sound` / `book_sound`, in-place 2nd Futamura specialization (`futamura2BookCompiler_specializes_in_core`),
and `OB5`/`LT5` cross-package cone-pin invariance (`symUnfold_linkComposition_of_not_mem`).
-/
import Obend.Elab.Workbook
import Obend.Leaf.Futamura
import Obend.Spec.CrossPackage

namespace Obend.Stdlib

open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Spec.CrossPackage
open Obend.Elab.Workbook

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Multi-File `#import_obend` of `stdlib/{core,ledger,usd}/*.obend` -/

#import_obend "stdlib/core/Cell.obend" as StdlibCell
#import_obend "stdlib/ledger/Account.obend" as StdlibAccount
#import_obend "stdlib/usd/ScenePrim.obend" as StdlibScenePrim

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

end Obend.Stdlib
