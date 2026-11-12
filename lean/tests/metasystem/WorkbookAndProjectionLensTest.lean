module
/-
# WorkbookAndProjectionLensTest — End-to-End Verification & `#tooth` Mutation Suite
Tests `Obend.Doc.WorkbookEngine`, the 16-projection `Doc.Structured`/`Doc.Graph` algebra,
Putnam/Foster bidirectional lenses, pushout branch merge, capability-scoped Merkle redaction,
and `Obend.FFI.Bridge` workbook & CAE/PDE format gates.
-/
public import Obend.Doc.WorkbookEngine
public import Obend.FFI.Bridge
meta import Obend.Doc.WorkbookEngine
meta import Obend.FFI.Bridge
import Obend.Tactic.Tooth
import all Obend.Tactic.Tooth
import all Obend.Doc.Graph
import all Obend.Doc.Patch
import all Obend.Doc.Section
import all Obend.Doc.Backlinks
import all Obend.Doc.Merge
import all Obend.Doc.Render
import all Obend.Doc.Structured
import all Obend.Doc.ReactiveNotebook
import all Obend.Spec.Sha256
import all Obend.Doc.WorkbookEngine
import all Obend.FFI.BridgeTypes
import all Obend.FFI.Bridge

namespace Obend.Tests.WorkbookAndProjectionLensTest

open Obend.Core.Data (Data)
open Obend.Doc
open Obend.Doc.Reactive (Opcode Instruction ReactiveCell CellKernel scientificKernel)
open Obend.Doc.WorkbookEngine
open Obend.FFI

set_option autoImplicit false

/-! ## 1. 16-Kind `ProjectionKind` Roundtrip & Taxonomy Witness -/
example :
    ProjectionKind.all.length = 16 ∧
    (ProjectionKind.all.all fun k => ProjectionKind.ofLabel k.toLabel == some k) = true ∧
    ProjectionKind.pcbMultiphysicsDfm.isHardware = true ∧
    ProjectionKind.vehicle6DofTrajectory.isHardware = true ∧
    ProjectionKind.pdeConservation.isExecutable = true ∧
    ProjectionKind.feecSimplicialFem.isExecutable = true ∧
    ProjectionKind.zkCustodyReceipt.isContractual = true ∧
    ProjectionKind.frustumRedactedView.isContractual = true := by
  decide +kernel

/-! ## 2. Concrete Multi-Hop Transclusion + Reactive Dirty-Cone + Redaction Fixture -/
private def secAero : WorkbookSection :=
  { sectionKey := "AeroSpec", markdown := "Wing load budget ^rootLoad", blocks := [("rootLoad", 40)] }

private def secBridge : WorkbookSection :=
  { sectionKey := "ControlBridge", markdown := "Transcludes ![[AeroSpec#^rootLoad]]", blocks := [] }

private def mkPinnedCell (cid : String) (kind : ProjectionKind) (fields : List (String × Data)) : StructuredCell :=
  { id := cid
    kind := kind
    ast := .record fields
    pins := fields.map fun (fn, fv) => (fn, computeFieldPin32 fn fv)
    receipt := none }

private def cellVehicle : WorkbookCell :=
  { cellKey := "veh_6dof"
    structured := mkPinnedCell "veh_6dof" .vehicle6DofTrajectory
      [("thrustN", .natural 500), ("massKg", .natural 25), ("se3SymplecticCert", .boolean true)]
    reactive := {
      id := 10, kind := .vehicle6DofTrajectory
      reads := [], defs := ["accel_margin"]
      body := [[{ op := .input, arg := 0 }, { op := .literal, arg := 20 }, { op := .add, arg := 0 }]]
      note := "Cites [[ControlBridge#Load]]"
    } }

private def cellSealedCustody : WorkbookCell :=
  { cellKey := "zk_custody"
    structured := mkPinnedCell "zk_custody" .zkCustodyReceipt
      [("epochLimit", .natural 12), ("thresholdK", .natural 3), ("custodyProof", .boolean true)]
    reactive := {
      id := 20, kind := .zkCustodyReceipt
      reads := [], defs := ["secret_epoch"]
      body := [[{ op := .literal, arg := 12 }]]
    }
    visibility := .sealedPrivate "tier0-custodian" (BitVec.ofNat 256 0xCAFE_BABE) }

private def cellFeecMesh : WorkbookCell :=
  { cellKey := "feec_mesh"
    structured := mkPinnedCell "feec_mesh" .feecSimplicialFem
      [("polynomialOrder", .natural 2), ("meshRefinement", .natural 4), ("pragerSyngeGap", .natural 0)]
    reactive := {
      id := 30, kind := .feecSimplicialFem
      reads := ["secret_epoch"], defs := ["mesh_dof"]
      body := [[{ op := .input, arg := 0 }, { op := .literal, arg := 4 }, { op := .mul, arg := 0 }]]
    } }

/-- Inhabitedness witness: `ValidWorkbookState` is constructively inhabited by a multi-projection
    3-cell workbook with 2-hop markdown transclusion and sealed custody visibility. -/
theorem inhabited_valid_workbook (k : CellKernel) :
    ∃ wb : Workbook,
      ValidWorkbookState k wb ∧
      wb.cells.length = 3 := by
  let secs := [secAero, secBridge]
  let raw := [cellVehicle, cellSealedCustody, cellFeecMesh]
  have hDag : checkWorkbookDag raw = true := by decide
  have hWf : ∀ w ∈ raw, WellFormedCellReads w := by
    intro w hw ck hMem
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simp [cellVehicle] at hMem
    · simp [cellSealedCustody] at hMem
    · simp [cellFeecMesh, citeSymbol] at hMem
      have hChars := congrArg String.toList hMem
      simp [String.toList_append] at hChars
  let wb := evalWorkbookFull k "TestWorkbook" secs raw
  have hEntries : wb.cells.map CachedWorkbookCell.entry = raw :=
    evalWorkbookSchedule_entries k raw (sectionEnvironment secs (secs.length + 1))
  refine ⟨wb, ⟨?_, ?_, ?_⟩, ?_⟩
  · change checkWorkbookDag (wb.cells.map CachedWorkbookCell.entry) = true
    rw [hEntries]; exact hDag
  · change ∀ w ∈ wb.cells.map CachedWorkbookCell.entry, WellFormedCellReads w
    rw [hEntries]; exact hWf
  · change wb = evalWorkbookFull k wb.title wb.sections (wb.cells.map CachedWorkbookCell.entry)
    have hEq : evalWorkbookFull k wb.title wb.sections (wb.cells.map CachedWorkbookCell.entry) =
        evalWorkbookFull k "TestWorkbook" secs raw := by
      change evalWorkbookFull k "TestWorkbook" secs (wb.cells.map CachedWorkbookCell.entry) =
        evalWorkbookFull k "TestWorkbook" secs raw
      rw [hEntries]
    exact hEq.symm
  · change (evalWorkbookSchedule k raw (sectionEnvironment secs (secs.length + 1))).length = 3
    rw [evalWorkbookSchedule_length]
    rfl

/-- Concrete self-citation & 2-cell cycle rejection + hardware CAE/PDE format gate checks. -/
example :
    let selfLoop : WorkbookCell := { cellVehicle with citedKeys := ["veh_6dof"] }
    let cycA : WorkbookCell := { cellVehicle with
      cellKey := "a", reactive := { cellVehicle.reactive with id := 1, reads := ["y"], defs := ["x"], note := "" } }
    let cycB : WorkbookCell := { cellFeecMesh with
      cellKey := "b", reactive := { cellFeecMesh.reactive with id := 2, reads := ["x"], defs := ["y"], note := "" } }
    checkWorkbookDag [selfLoop] = false ∧
    checkWorkbookDag [cycA, cycB] = false ∧
    isHardwareProjectionFormat "mna-dae@1" = true ∧
    isHardwareProjectionFormat "vivado-sta@1" = true ∧
    isHardwareProjectionFormat "openpdk-drc-sta@1" = true ∧
    isHardwareProjectionFormat "hyperbolic-fvm@1" = true ∧
    isHardwareProjectionFormat "pde-approx-defect@1" = true ∧
    isHardwareProjectionFormat "devsim-qfermi@1" = true ∧
    isHardwareProjectionFormat "feec-prager-synge@1" = true ∧
    isHardwareProjectionFormat "se3-vehicle-6dof@1" = true ∧
    isHardwareProjectionFormat "tempest-glitch-emc@1" = true := by
  decide

/-! ## 2b. Compiled End-to-End SHA-256 + cSHAKE256 + JSON Wire Execution -/
#eval (show IO Unit from do
  if isHardwareProjectionFormat "pcb-fake-unknown" ≠ false then
    throw (IO.userError "unknown format must be rejected")
  let secs := [secAero, secBridge]
  let raw := [cellVehicle, cellSealedCustody, cellFeecMesh]
  let wb0 := evalWorkbookFull scientificKernel "TestWorkbook" secs raw
  let secEdit := WorkbookEdit.editSection "AeroSpec" "Updated load ^rootLoad" [("rootLoad", 95)]
  let wb1 := evalWorkbookIncremental scientificKernel wb0 secEdit
  if workbookDirtyCone wb0 secEdit ≠ [10] then
    throw (IO.userError "dirty cone across 2-hop transclusion should be [10]")
  if wb1 ≠ evalWorkbookFull scientificKernel "TestWorkbook" (applyEditToSections secs secEdit) raw then
    throw (IO.userError "incremental vs full workbook mismatch")
  match scrubWorkbookCell scientificKernel wb1 "veh_6dof" ⟨"se3SymplecticCert", .boolean false⟩ with
  | .error (.readOnlyField "se3SymplecticCert") => pure ()
  | _ => throw (IO.userError "read-only proof badge scrub must fail closed")
  let okScrub := scrubWorkbookCell scientificKernel wb1 "feec_mesh" ⟨"polynomialOrder", .natural 5⟩
  if !okScrub.isOk then
    throw (IO.userError "editable parameter scrub should succeed")
  let redacted := projectWorkbookForViewer Obend.Core.Digest.deployed ["public-guest"] wb1
  if verifyRedactedWorkbook scientificKernel Obend.Core.Digest.deployed redacted ≠ true then
    throw (IO.userError "redacted workbook collaborator verification failed")
  let corruptJson := "{corrupted".toUTF8
  match stepWorkbookJsonBytes wb0 corruptJson with
  | .error (-3, _) => pure ()
  | _ => throw (IO.userError "corrupted JSON step must return -3")
  match scrubWorkbookCellJsonBytes wb0 corruptJson with
  | .error (-3, _) => pure ()
  | _ => throw (IO.userError "corrupted JSON scrub must return -3")
  let invalidUtf8 := ByteArray.mk #[0xFF, 0xFE]
  match stepWorkbookJsonBytes wb0 invalidUtf8 with
  | .error (-3, _) => pure ()
  | _ => throw (IO.userError "invalid UTF-8 step must return -3")
  let spoofCite := "{\"op\":\"init\",\"cells\":[{\"cellKey\":\"c1\",\"id\":1,\"reads\":[\"cite::AeroSpec\"]}]}".toUTF8
  match stepWorkbookJsonBytes wb0 spoofCite with
  | .error (-4, _) => pure ()
  | _ => throw (IO.userError "undeclared cite:: read must return -4")
  IO.println "workbook engine, lens scrub, Merkle redaction, and FFI JSON checks passed")

/-! ## 3. Universal `#tooth` Mutation-Sensitivity Suite (15 Kills) -/

-- Tooth 1: Multi-hop transclusion frame sensitivity
#tooth evalCiteKeyFuel_frame_outside_impacted by
  mutation directSectionValue := fun secs citeKey => secs.length + citeKey.length

-- Tooth 2: Workbook DAG acyclicity soundness sensitivity
#tooth checkWorkbookDag_acyclic_sound by
  mutation checkWorkbookDag := fun _ => true

-- Tooth 3: Self-citation cycle refusal sensitivity
#tooth checkWorkbookDag_rejects_self_cite by
  mutation effectiveReactiveCell := fun w => w.reactive

-- Tooth 4: Incremental vs. full workbook equivalence sensitivity
#tooth evalWorkbookIncremental_eq_full by
  mutation evalWorkbookIncremental := fun _ wb _ => wb

-- Tooth 5: Dirty-cone exactness & clean-cell receipt reuse sensitivity
#tooth workbook_edit_recomputes_only_dirty_cone by
  mutation workbookDirtyCone := fun _ _ => []

-- Tooth 6: Read-only proof badge immutability sensitivity
#tooth scrub_readOnly_refused by
  mutation scrubLensCell := fun _ c _ => .ok (c, [])

-- Tooth 7: Putnam/Foster `GetPut` law sensitivity
#tooth lens_get_put by
  mutation updateAssocInPlace := fun _ _ _ => []

-- Tooth 8: Putnam/Foster `PutGet` law sensitivity
#tooth lens_put_get by
  mutation renderLensView := fun kind c =>
    { cellId := c.id, kind := kind, fields := [], verifiedBadge := c.receipt }

-- Tooth 9: Putnam/Foster `PutPut` law sensitivity
#tooth lens_put_put by
  mutation scrubLensCell := fun _ c edit => .ok ({ c with id := edit.fieldName }, [])

-- Tooth 10: Sibling-pin & verified-badge frame preservation sensitivity
#tooth lens_scrub_preserves_sibling_pins by
  mutation scrubLensCell := fun _ c _ => .ok ({ c with receipt := some ByteArray.empty, pins := [] }, [])

-- Tooth 11: Pushout branch merge unconflicted receipt preservation sensitivity
#tooth mergeWorkbookBranches_preserves_unconflicted_receipts by
  mutation mergeWorkbookBranches := fun _ lg rg _ _ _ => ⟨Graph.merge lg rg, [], []⟩

-- Tooth 12: Capability-scoped sealed cell redaction sensitivity
#tooth projectWorkbookForViewer_hides_sealed by
  mutation isCellVisibleToViewer := fun _ _ => true

-- Tooth 13: Redacted workbook collaborator verification completeness sensitivity
#tooth verifyRedactedWorkbook_complete by
  mutation verifyRedactedWorkbook := fun _ _ _ => false

-- Tooth 14: FFI workbook step empty-payload fail-closed refusal sensitivity
#tooth workbookStepJsonCore_empty_refused by
  mutation workbookStepJsonCore := fun s bs => (s, bs, 0)

-- Tooth 15: FFI projection lens scrub empty-payload fail-closed refusal sensitivity
#tooth workbookScrubCellJsonCore_empty_refused by
  mutation workbookScrubCellJsonCore := fun s bs => (s, bs, 0)

/-! ## 4. Kernel Axiom Hygiene Audit (`0 sorryAx`, `0` custom axioms) -/
#print axioms evalWorkbookIncremental_eq_full
#print axioms workbook_edit_recomputes_only_dirty_cone
#print axioms scrub_readOnly_refused
#print axioms lens_get_put
#print axioms lens_put_get
#print axioms lens_put_put
#print axioms lens_scrub_preserves_sibling_pins
#print axioms mergeWorkbookBranches_comm
#print axioms mergeWorkbookBranches_preserves_unconflicted_receipts
#print axioms projectWorkbookForViewer_hides_sealed
#print axioms verifyRedactedWorkbook_complete
#print axioms verifyRedactedWorkbook_binds_or_collides
#print axioms runWorkbookTurns_preserves_valid
#print axioms workbookStepJsonCore_empty_refused
#print axioms workbookScrubCellJsonCore_empty_refused

end Obend.Tests.WorkbookAndProjectionLensTest
