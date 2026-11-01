import Obend.Doc.Structured
import Obend.Doc.Graph
import Obend.Doc.Patch
import Obend.Core.Data

open Obend.Doc
open Obend.Core.Data

set_option autoImplicit false

/-! # Milestone 5 Features 34 & 35: Structured Cells Unit Test Suite -/

-- Test 1: Exactly 10 ProjectionKinds exist
def test_all_ten_projection_kinds : Bool :=
  (ProjectionKind.all.length == 10) &&
  ((ProjectionKind.all.filter ProjectionKind.isHardware).length == 3) &&
  ((ProjectionKind.all.filter ProjectionKind.isExecutable).length == 3) &&
  ((ProjectionKind.all.filter ProjectionKind.isContractual).length == 3)

#guard test_all_ten_projection_kinds == true

-- Test 2: ProjectionKind string roundtrip
def test_projection_kind_roundtrip : Bool :=
  ProjectionKind.all.all fun k =>
    ProjectionKind.ofLabel (ProjectionKind.toLabel k) == some k

#guard test_projection_kind_roundtrip == true

-- Test 3: Structured cell creation and Content wrapping
def test_structured_cell_to_content : Bool :=
  let cell : StructuredCell := {
    id := "cell_01"
    kind := .casSymbolic
    ast := .record [("expr", .label "x + 1")]
    pins := [("pin1", ByteArray.mk #[1, 2, 3])]
    receipt := some (ByteArray.mk #[0xCA, 0xFE])
  }
  let cnt := cell.toContent
  match cnt.toCell? with
  | some c' => c' == cell
  | none => false

#guard test_structured_cell_to_content == true

-- Test 4: Structured cell Core.Data roundtrip
def test_cell_core_data_roundtrip : Bool :=
  let cell : StructuredCell := {
    id := "code_cell"
    kind := .obendCode
    ast := .natural 42
    pins := [("depA", ByteArray.mk #[0xAA, 0xBB])]
    receipt := none
  }
  let d := cellToCoreData cell
  match cellOfCoreData d with
  | some c' => c'.id == cell.id && c'.kind == cell.kind
  | none => false

#guard test_cell_core_data_roundtrip == true

-- Test 5: Pin verification: valid vs stale vs missing
def test_pin_verification : Bool :=
  let pinA : String × ByteArray := ("sigA", ByteArray.mk #[10, 20])
  let envValid : String → Option ByteArray := fun name =>
    if name == "sigA" then some (ByteArray.mk #[10, 20]) else none
  let envStale : String → Option ByteArray := fun name =>
    if name == "sigA" then some (ByteArray.mk #[10, 21]) else none
  let envMissing : String → Option ByteArray := fun _ => none
  (verifyPin pinA envValid == .valid) &&
  (match verifyPin pinA envStale with | .stale .. => true | _ => false) &&
  (verifyPin pinA envMissing == .missing "sigA")

#guard test_pin_verification == true

-- Test 6: Cell pin evaluation and invalidation theorem
def test_all_pins_valid : Bool :=
  let cell : StructuredCell := {
    id := "c_contract"
    kind := .lawContract
    ast := .boolean true
    pins := [("p1", ByteArray.mk #[1]), ("p2", ByteArray.mk #[2])]
  }
  let envGood : String → Option ByteArray := fun name =>
    if name == "p1" then some (ByteArray.mk #[1])
    else if name == "p2" then some (ByteArray.mk #[2])
    else none
  let envBad : String → Option ByteArray := fun name =>
    if name == "p1" then some (ByteArray.mk #[1])
    else if name == "p2" then some (ByteArray.mk #[99])
    else none
  (allPinsValid cell envGood == true) &&
  (allPinsValid cell envBad == false)

#guard test_all_pins_valid == true

-- Test 7: Document patch and cell lookup by ID
def test_document_patch_and_lookup : Bool :=
  let cell : StructuredCell := {
    id := "search_target"
    kind := .ledgerSeat
    ast := .label "seat_0"
  }
  let doc : ObnbDocument := {
    title := "Notebook 1"
    cells := [cell]
  }
  let patch := documentToPatch doc
  let G := Graph.empty.apply patch
  match findCellById G "search_target" with
  | some c => c.id == "search_target" && c.kind == .ledgerSeat
  | none => false

#guard test_document_patch_and_lookup == true
