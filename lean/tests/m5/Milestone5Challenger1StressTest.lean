module
import Obend.Doc.Structured
import Obend.Doc.Graph
import Obend.Doc.Patch
import Obend.Core.Data
import all Obend.Hardware.NotebookProjection
meta import all Obend.Hardware.NotebookProjection
import Obend.Hardware.HDL
import Obend.Hardware.Synth
import Obend.Hardware.Process
import Obend.Hardware.PlaceRoute
import Obend.Hardware.DRC
import Obend.Hardware.Circuits
import all Obend.Vault.Json
meta import Obend.Vault.Json
meta import Obend.Doc.Structured
meta import Obend.Doc.Graph
meta import Obend.Doc.Patch
meta import Obend.Core.Data
meta import Obend.Hardware.HDL
meta import Obend.Hardware.Synth
meta import Obend.Hardware.Process
meta import Obend.Hardware.PlaceRoute
meta import Obend.Hardware.DRC
meta import Obend.Hardware.Circuits
import Lean.Data.Json

open Obend.Doc
open Obend.Core.Data
open Obend.Vault.HardwareProjection
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Process
open Obend.Hardware.PlaceRoute
open Obend.Hardware.DRC
open Obend.Hardware.Circuits
open Obend.Vault.Json
open Lean (Json toJson fromJson?)

set_option autoImplicit false

/-!
# Milestone 5 Challenger 1: Empirical Adversarial Stress Test Suite
Adversarially tests Features 34, 35, 36:
1. Feature 34: ProjectionKind 16 variants pairwise distinctness, decider, wire codecs, category disjointness, and fuzzing.
2. Feature 35: StructuredCell, .obnb codecs, deep AST nesting, corrupt hex/receipts, pin invalidation matrix, document CRDT.
3. Feature 36: Read-only hardware projections, complex RTL DAG verification, multi-corner STA timing closure/violations, multi-layer DRC violations, WaferSpace signoff.
-/

namespace Obend.Challenger.M5

/-! ## 1. Feature 34: ProjectionKind Stress & Fuzzing -/

-- Test 1.1: Pairwise distinctness of all 16 variants
def test_projection_kind_pairwise_distinct : Bool :=
  let all := ProjectionKind.all
  all.all fun a =>
    all.all fun b =>
      if a == b then decide (a = b)
      else !decide (a = b)

#guard test_projection_kind_pairwise_distinct == true

-- Test 1.2: Roundtrip through toLabel / ofLabel for all 16 variants
def test_projection_kind_roundtrip_all : Bool :=
  ProjectionKind.all.all fun k =>
    match ProjectionKind.ofLabel (ProjectionKind.toLabel k) with
    | some k' => k' == k
    | none => false

#guard test_projection_kind_roundtrip_all == true

-- Test 1.3: Fuzzing invalid discriminants in ofLabel
def test_projection_kind_invalid_discriminants : Bool :=
  let invalidLabels : List String := [
    "", " ", "   ", "\n", "\t", "\x00",
    " prose", "prose ", " prose ", "prose\n", "prose\x00",
    "Prose", "PROSE", "pROSE",
    "obendcode", "OBENDCODE", "ObendCode",
    "cassymbolic", "CASSYMBOLIC",
    "leanbridge", "LEANBRIDGE",
    "lawcontract", "LAWCONTRACT",
    "deosaffordance", "DEOSAFFORDANCE",
    "hardwareschematic", "HARDWARESCHEMATIC",
    "hardwaretiming", "HARDWARETIMING",
    "hardwarelayout", "HARDWARELAYOUT",
    "ledgerseat", "LEDGERSEAT",
    "0", "1", "-1", "99",
    "null", "undefined", "true", "false",
    "{}", "[]", "proseX", "Xprose", "pro",
    "<script>alert(1)</script>", "' OR 1=1--"
  ]
  invalidLabels.all fun bad =>
    (ProjectionKind.ofLabel bad).isNone

#guard test_projection_kind_invalid_discriminants == true

-- Test 1.4: Category partition correctness & mutual disjointness
def test_projection_kind_partition_disjointness : Bool :=
  let all := ProjectionKind.all
  let hw := all.filter ProjectionKind.isHardware
  let exe := all.filter ProjectionKind.isExecutable
  let ctr := all.filter ProjectionKind.isContractual
  -- Counts must be exactly 5 each
  (hw.length == 5) &&
  (exe.length == 5) &&
  (ctr.length == 5) &&
  -- Mutual disjointness
  (hw.all fun k => !ProjectionKind.isExecutable k && !ProjectionKind.isContractual k) &&
  (exe.all fun k => !ProjectionKind.isHardware k && !ProjectionKind.isContractual k) &&
  (ctr.all fun k => !ProjectionKind.isHardware k && !ProjectionKind.isExecutable k) &&
  -- Prose is in none of them
  (!ProjectionKind.isHardware .prose) &&
  (!ProjectionKind.isExecutable .prose) &&
  (!ProjectionKind.isContractual .prose) &&
  -- Total accounted for is 5 + 5 + 5 + 1 = 16
  (hw.length + exe.length + ctr.length + 1 == 16)

#guard test_projection_kind_partition_disjointness == true

-- Test 1.5: Core.Data wire serialization and deserialization
def test_projection_kind_data_codec : Bool :=
  let validRoundtrip := ProjectionKind.all.all fun k =>
    ProjectionKind.ofData? (ProjectionKind.toData k) == some k
  let invalidData : List Data := [
    .natural 0,
    .natural 42,
    .boolean true,
    .boolean false,
    .record [],
    .record [("a", .label "prose")],
    .variant "nonexistent" (.label "prose"),
    .label "not_a_kind",
    .label ""
  ]
  let invalidRejected := invalidData.all fun d =>
    (ProjectionKind.ofData? d).isNone
  validRoundtrip && invalidRejected

#guard test_projection_kind_data_codec == true


/-! ## 2. Feature 35: StructuredCell, Codecs, Deep AST & Pin Invalidation -/

-- Test 2.1: Hex codec boundary cases
def test_hex_codecs_boundary : Bool :=
  -- Valid empty
  (hexToByteArray "" == some (ByteArray.mk #[])) &&
  (hexToByteArray "0x" == some (ByteArray.mk #[])) &&
  (hexToByteArray "0X" == some (ByteArray.mk #[])) &&
  -- Valid single byte
  (hexToByteArray "00" == some (ByteArray.mk #[0])) &&
  (hexToByteArray "0x00" == some (ByteArray.mk #[0])) &&
  (hexToByteArray "FF" == some (ByteArray.mk #[255])) &&
  (hexToByteArray "ff" == some (ByteArray.mk #[255])) &&
  -- Valid multi-byte
  (hexToByteArray "0xCAFE" == some (ByteArray.mk #[0xCA, 0xFE])) &&
  (hexToByteArray "deadbeef" == some (ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF])) &&
  -- Invalid odd lengths
  (hexToByteArray "a" == none) &&
  (hexToByteArray "0xa" == none) &&
  (hexToByteArray "123" == none) &&
  (hexToByteArray "0x123" == none) &&
  -- Invalid characters
  (hexToByteArray "0xZZ" == none) &&
  (hexToByteArray "0x1G" == none) &&
  (hexToByteArray "hello" == none) &&
  (hexToByteArray " 00" == none) &&
  -- Roundtrip
  (let b := ByteArray.mk #[0, 1, 15, 16, 127, 128, 254, 255]
   hexToByteArray (byteArrayToHex b) == some b)

#guard test_hex_codecs_boundary == true

-- Test 2.2: Deeply nested AST roundtrip through StructuredCell and cellToCoreData
def mkDeepNestedVariant : Nat → Data
  | 0 => .natural 42
  | n + 1 => .variant "nest" (mkDeepNestedVariant n)

def mkDeepNestedRecord : Nat → Data
  | 0 => .label "leaf"
  | n + 1 => .record [("child", mkDeepNestedRecord n)]

def test_deep_ast_nesting : Bool :=
  let deepVar := mkDeepNestedVariant 50
  let deepRec := mkDeepNestedRecord 50
  let cell1 : StructuredCell := {
    id := "deep_var_cell"
    kind := .casSymbolic
    ast := deepVar
    pins := [("p", ByteArray.mk #[1, 2, 3])]
    receipt := some (ByteArray.mk #[4, 5, 6])
  }
  let cell2 : StructuredCell := {
    id := "deep_rec_cell"
    kind := .leanBridge
    ast := deepRec
    pins := []
    receipt := none
  }
  -- Test Content wrapping roundtrip
  let content1Ok := cell1.toContent.toCell? == some cell1
  let content2Ok := cell2.toContent.toCell? == some cell2
  -- Test Core.Data serialization roundtrip
  let data1 := cellToCoreData cell1
  let data2 := cellToCoreData cell2
  let data1Ok := match cellOfCoreData data1 with
    | some c' => c'.id == cell1.id && c'.kind == cell1.kind && c'.ast == cell1.ast
    | none => false
  let data2Ok := match cellOfCoreData data2 with
    | some c' => c'.id == cell2.id && c'.kind == cell2.kind && c'.ast == cell2.ast
    | none => false
  content1Ok && content2Ok && data1Ok && data2Ok

#guard test_deep_ast_nesting == true

-- Test 2.3: Malformed JSON decoding in contentOf
def test_malformed_json_contentOf : Bool :=
  -- Missing kind
  let bad1 := Json.mkObj [("cell", "c1"), ("ast", Json.mkObj [("nat", 1)])]
  -- Bad kind
  let bad2 := Json.mkObj [("cell", "c2"), ("kind", "unknown_kind"), ("ast", Json.mkObj [("nat", 1)]), ("pins", Json.arr #[]), ("receipt", Json.null)]
  -- Bad pin hash (odd hex length)
  let bad3 := Json.mkObj [
    ("cell", "c3"), ("kind", "prose"), ("ast", Json.mkObj [("nat", 1)]),
    ("pins", Json.arr #[Json.mkObj [("name", "p1"), ("hash", "123")]]),
    ("receipt", Json.null)
  ]
  -- Bad pin hash (non-hex characters)
  let bad4 := Json.mkObj [
    ("cell", "c4"), ("kind", "prose"), ("ast", Json.mkObj [("nat", 1)]),
    ("pins", Json.arr #[Json.mkObj [("name", "p1"), ("hash", "0xZZ")]]),
    ("receipt", Json.null)
  ]
  -- Bad receipt (odd length)
  let bad5 := Json.mkObj [
    ("cell", "c5"), ("kind", "prose"), ("ast", Json.mkObj [("nat", 1)]),
    ("pins", Json.arr #[]),
    ("receipt", "0xABC")
  ]
  -- Bad receipt (invalid chars)
  let bad6 := Json.mkObj [
    ("cell", "c6"), ("kind", "prose"), ("ast", Json.mkObj [("nat", 1)]),
    ("pins", Json.arr #[]),
    ("receipt", "0xGG")
  ]
  (match contentOf bad1 with | .error _ => true | .ok _ => false) &&
  (match contentOf bad2 with | .error _ => true | .ok _ => false) &&
  (match contentOf bad3 with | .error _ => true | .ok _ => false) &&
  (match contentOf bad4 with | .error _ => true | .ok _ => false) &&
  (match contentOf bad5 with | .error _ => true | .ok _ => false) &&
  (match contentOf bad6 with | .error _ => true | .ok _ => false)

#guard test_malformed_json_contentOf == true

-- Test 2.4: Pin invalidation matrix
def test_pin_invalidation_matrix : Bool :=
  let emptyCell : StructuredCell := { id := "c0", kind := .lawContract, ast := .natural 0, pins := [] }
  let singlePinCell : StructuredCell := {
    id := "c1", kind := .lawContract, ast := .natural 0,
    pins := [("dep1", ByteArray.mk #[0xAA, 0xBB])]
  }
  let multiPinCell : StructuredCell := {
    id := "c5", kind := .lawContract, ast := .natural 0,
    pins := [
      ("p1", ByteArray.mk #[1]),
      ("p2", ByteArray.mk #[2]),
      ("p3", ByteArray.mk #[3]),
      ("p4", ByteArray.mk #[4]),
      ("p5", ByteArray.mk #[5])
    ]
  }

  -- 0-pin cell is always valid regardless of env
  let r0 := allPinsValid emptyCell (fun _ => none) == true
  let r0b := allPinsValid emptyCell (fun _ => some (ByteArray.mk #[99])) == true

  -- 1-pin matching env
  let env1Ok : String → Option ByteArray := fun name =>
    if name == "dep1" then some (ByteArray.mk #[0xAA, 0xBB]) else none
  let r1Ok := allPinsValid singlePinCell env1Ok == true

  -- 1-pin stale env (single bit flip)
  let env1Stale : String → Option ByteArray := fun name =>
    if name == "dep1" then some (ByteArray.mk #[0xAA, 0xBC]) else none
  let r1Stale := allPinsValid singlePinCell env1Stale == false

  -- 1-pin missing env
  let envMissing : String → Option ByteArray := fun _ => none
  let r1Missing := allPinsValid singlePinCell envMissing == false

  -- Multi-pin all matching
  let envMultiOk : String → Option ByteArray := fun name =>
    match name with
    | "p1" => some (ByteArray.mk #[1])
    | "p2" => some (ByteArray.mk #[2])
    | "p3" => some (ByteArray.mk #[3])
    | "p4" => some (ByteArray.mk #[4])
    | "p5" => some (ByteArray.mk #[5])
    | _ => none
  let rMultiOk := allPinsValid multiPinCell envMultiOk == true

  -- Multi-pin with 1 stale (p5 corrupted)
  let envMultiStale5 : String → Option ByteArray := fun name =>
    match name with
    | "p1" => some (ByteArray.mk #[1])
    | "p2" => some (ByteArray.mk #[2])
    | "p3" => some (ByteArray.mk #[3])
    | "p4" => some (ByteArray.mk #[4])
    | "p5" => some (ByteArray.mk #[99])
    | _ => none
  let rMultiStale5 := allPinsValid multiPinCell envMultiStale5 == false

  -- Multi-pin with 1 missing (p3 missing)
  let envMultiMissing3 : String → Option ByteArray := fun name =>
    match name with
    | "p1" => some (ByteArray.mk #[1])
    | "p2" => some (ByteArray.mk #[2])
    | "p4" => some (ByteArray.mk #[4])
    | "p5" => some (ByteArray.mk #[5])
    | _ => none
  let rMultiMissing3 := allPinsValid multiPinCell envMultiMissing3 == false

  -- Cell with duplicate pins with conflicting expected hashes
  let conflictCell : StructuredCell := {
    id := "c_conflict", kind := .deosAffordance, ast := .natural 0,
    pins := [("p", ByteArray.mk #[1]), ("p", ByteArray.mk #[2])]
  }
  let envConflict : String → Option ByteArray := fun _ => some (ByteArray.mk #[1])
  let rConflict := allPinsValid conflictCell envConflict == false

  r0 && r0b && r1Ok && r1Stale && r1Missing && rMultiOk && rMultiStale5 && rMultiMissing3 && rConflict

#guard test_pin_invalidation_matrix == true

-- Test 2.5: Document graph patch application and multi-cell retrieval
def test_document_graph_multi_cell_retrieval : Bool :=
  let kinds := ProjectionKind.all
  let cells : List StructuredCell := kinds.zipIdx.map fun (k, i) => {
    id := s!"cell_{i}"
    kind := k
    ast := .natural i
    pins := [("pin", ByteArray.mk #[i.toUInt8])]
    receipt := none
  }
  let doc : ObnbDocument := {
    title := "AllKindsNotebook"
    cells := cells
  }
  let patch := documentToPatch doc
  let G := Graph.empty.apply patch
  -- Verify all 16 cells are found with correct IDs and kinds
  let allFound := cells.all fun c =>
    match findCellById G c.id with
    | some c' => c'.id == c.id && c'.kind == c.kind
    | none => false
  -- Verify nonexistent cell ID returns none
  let noneOk := (findCellById G "nonexistent_id").isNone
  -- Verify Graph size
  let atomCountOk := G.atoms.length == cells.length
  allFound && noneOk && atomCountOk

#guard test_document_graph_multi_cell_retrieval == true


/-! ## 3. Feature 36: Read-Only Hardware Projections & Stress -/

-- Test 3.1: Complex RTL combinational arithmetic tree and DAG check
def test_complex_rtl_dag_projection : Bool :=
  -- Valid module with deep expression tree and multiple wires
  let mValid : Circuit := {
    name := "complex_alu"
    inputNames := ["inA", "inB", "inC", "inD"]
    wires := [
      { wireIdx := 0, name := "w_add", expr := .alu .add (.inputPort 0) (.inputPort 1) },
      { wireIdx := 1, name := "w_sub", expr := .alu .sub (.inputPort 2) (.inputPort 3) },
      { wireIdx := 2, name := "w_mul", expr := .alu .mul (.wireRef 0) (.wireRef 1) },
      { wireIdx := 3, name := "w_mux", expr := .mux (.alu .ult (.wireRef 0) (.wireRef 1)) (.wireRef 2) (.bitNot (.wireRef 2)) }
    ]
    regs := [
      { regIdx := 0, name := "r_sync", domain := .coreClk, resetKind := .syncReset 0, isSynchronizer := false, nextExpr := .wireRef 3 },
      { regIdx := 1, name := "r_cdc", domain := .axiIoClk, resetKind := .resetFree, isSynchronizer := true, nextExpr := .wireRef 0 }
    ]
    outputs := [
      { name := "out_sync", expr := .regRead 0 },
      { name := "out_cdc", expr := .regRead 1 }
    ]
  }
  let cValid := projectCircuit "alu_cell" mValid
  let okValid := match cValid with
    | .cell id kind ast _ _ =>
      (id == "alu_cell") &&
      (kind == .hardwareSchematic) &&
      (match ast with
       | .record fields =>
         match fields.lookup "dag_valid" with
         | some (.boolean true) => true
         | _ => false
       | _ => false)
    | _ => false

  -- Invalid module violating wire index DAG order (wire 0 references forward wire 1)
  let mInvalid : Circuit := {
    name := "cycle_alu"
    inputNames := ["inA"]
    wires := [
      { wireIdx := 0, name := "w0", expr := .wireRef 1 }, -- references wire 1 before wire 1 is declared!
      { wireIdx := 1, name := "w1", expr := .inputPort 0 }
    ]
    regs := []
    outputs := [{ name := "out", expr := .wireRef 0 }]
  }
  let cInvalid := projectCircuit "bad_alu" mInvalid
  let okInvalid := match cInvalid with
    | .cell _ _ ast _ _ =>
      match ast with
      | .record fields =>
        match fields.lookup "dag_valid" with
        | some (.boolean false) => true
        | _ => false
      | _ => false
    | _ => false

  okValid && okInvalid

#guard test_complex_rtl_dag_projection == true

-- Test 3.2: Multi-Corner STA Timing paths (Timing closure vs setup / hold violations)
def test_multi_corner_sta_timing_stress : Bool :=
  let path : TimingPath := {
    name := "crit_path"
    logicLevels := 8
    minLevels := 2
    carryBits := 16
    tileHops := 4
  }
  -- Corner 7nm SS: slow corner
  let cornerSS := corner7nm_SS
  let reqSS := requiredPeriodPs cornerSS path
  -- 1. Setup violation: clock period less than required period
  let shortClock := reqSS - 100
  let cSetupViol := projectTiming "t_setup_viol" cornerSS path shortClock
  let setupViolOk := match cSetupViol with
    | .cell _ .hardwareTiming ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "timing_closed" == some (.boolean false)) &&
        (fields.lookup "status" == some (.label "TIMING_VIOLATION"))
      | _ => false
    | _ => false

  -- 2. Setup closed: clock period plenty of headroom (10000 ps)
  let longClock := reqSS + 5000
  let cClosed := projectTiming "t_closed" cornerSS path longClock
  let closedOk := match cClosed with
    | .cell _ .hardwareTiming ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "timing_closed" == some (.boolean true)) &&
        (fields.lookup "status" == some (.label "TIMING_CLOSED"))
      | _ => false
    | _ => false

  -- 3. Exact boundary: clock period = required period
  let boundaryClock := reqSS
  let cBoundary := projectTiming "t_boundary" cornerSS path boundaryClock
  let boundaryOk := match cBoundary with
    | .cell _ .hardwareTiming ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "timing_closed" == some (.boolean true)) &&
        (fields.lookup "setup_slack_ps" == some (.variant "pos" (.natural 0)))
      | _ => false
    | _ => false

  -- 4. Hold violation corner: corner with very large skew/hold exceeding min arrival
  let extremeHoldCorner : ProcessCorner := {
    corner7nm_SS with
    tHoldPs := 5000,
    tSkewPs := 5000
  }
  let cHoldViol := projectTiming "t_hold_viol" extremeHoldCorner path longClock
  let holdViolOk := match cHoldViol with
    | .cell _ .hardwareTiming ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "timing_closed" == some (.boolean false)) &&
        (fields.lookup "status" == some (.label "TIMING_VIOLATION"))
      | _ => false
    | _ => false

  setupViolOk && closedOk && boundaryOk && holdViolOk

#guard test_multi_corner_sta_timing_stress == true

-- Test 3.3: Multi-Layer DRC Cutline Feature Violations
def test_cutline_drc_stress_violations : Bool :=
  let deck : FoundryDrcDeck := {
    deckName := "TestFoundry_130nm"
    minMetalWidthNm := 140
    minMetalSpacingNm := 140
    minViaWidthNm := 170
    minViaEnclosureNm := 60
    maxResistAspect := 3
  }
  let cleanFeat : CutlineDrcFeature := {
    metalWidthNm := 150
    metalSpacingNm := 150
    viaWidthNm := 180
    viaEnclosureNm := 70
    resistHeightNm := 300
    resistOpeningNm := 150
    ildThicknessNm := 800
  }
  -- Baseline: clean DRC
  let cClean := projectDrc "drc_clean" deck cleanFeat
  let okClean := match cClean with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "drc_clean" == some (.boolean true)) &&
        (fields.lookup "status" == some (.label "DRC_CLEAN"))
      | _ => false
    | _ => false

  -- Violation 1: Metal width too narrow (139 < 140)
  let featWidthViol := { cleanFeat with metalWidthNm := 139 }
  let cWidthViol := projectDrc "drc_w" deck featWidthViol
  let okWidth := match cWidthViol with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "drc_clean" == some (.boolean false)) &&
        (fields.lookup "width_ok" == some (.boolean false)) &&
        (fields.lookup "status" == some (.label "DRC_VIOLATION"))
      | _ => false
    | _ => false

  -- Violation 2: Metal spacing too narrow (139 < 140)
  let featSpacingViol := { cleanFeat with metalSpacingNm := 139 }
  let cSpacingViol := projectDrc "drc_s" deck featSpacingViol
  let okSpacing := match cSpacingViol with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "drc_clean" == some (.boolean false)) &&
        (fields.lookup "spacing_ok" == some (.boolean false)) &&
        (fields.lookup "status" == some (.label "DRC_VIOLATION"))
      | _ => false
    | _ => false

  -- Violation 3: Via width too small (169 < 170)
  let featViaWidthViol := { cleanFeat with viaWidthNm := 169 }
  let cViaWidthViol := projectDrc "drc_vw" deck featViaWidthViol
  let okViaWidth := match cViaWidthViol with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "drc_clean" == some (.boolean false)) &&
        (fields.lookup "via_width_ok" == some (.boolean false)) &&
        (fields.lookup "status" == some (.label "DRC_VIOLATION"))
      | _ => false
    | _ => false

  -- Violation 4: Via enclosure too small (59 < 60)
  let featEnclosureViol := { cleanFeat with viaEnclosureNm := 59 }
  let cEnclosureViol := projectDrc "drc_enc" deck featEnclosureViol
  let okEnclosure := match cEnclosureViol with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "drc_clean" == some (.boolean false)) &&
        (fields.lookup "enclosure_ok" == some (.boolean false)) &&
        (fields.lookup "status" == some (.label "DRC_VIOLATION"))
      | _ => false
    | _ => false

  -- Violation 5: Resist aspect ratio exceeded (height 500 > 3 * opening 150 = 450)
  let featAspectViol := { cleanFeat with resistHeightNm := 500, resistOpeningNm := 150 }
  let cAspectViol := projectDrc "drc_asp" deck featAspectViol
  let okAspect := match cAspectViol with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "drc_clean" == some (.boolean false)) &&
        (fields.lookup "resist_aspect_ok" == some (.boolean false)) &&
        (fields.lookup "status" == some (.label "DRC_VIOLATION"))
      | _ => false
    | _ => false

  -- Violation 6: Resist opening is 0 (division by zero / physical collapse)
  let featZeroOpening := { cleanFeat with resistOpeningNm := 0 }
  let cZeroOpening := projectDrc "drc_zero" deck featZeroOpening
  let okZeroOpening := match cZeroOpening with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "drc_clean" == some (.boolean false)) &&
        (fields.lookup "resist_aspect_ok" == some (.boolean false)) &&
        (fields.lookup "status" == some (.label "DRC_VIOLATION"))
      | _ => false
    | _ => false

  okClean && okWidth && okSpacing && okViaWidth && okEnclosure && okAspect && okZeroOpening

#guard test_cutline_drc_stress_violations == true

-- Test 3.4: Netlist-Bound PnR Layout & Certificate Multi-Condition Stress
def test_pnr_signoff_stress : Bool :=
  -- Baseline: golden netlist-bound PnR layout & certificate pass
  let cPass := projectGdsii "pnr_pass" validAdderPnrCert
  let okPass :=
    checkPnrCertificate validAdderBelNetlist corner7nm_SS 2000 validAdderPnrCert &&
    match cPass with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "placement_injective" == some (.boolean true)) &&
        (fields.lookup "routing_disjoint" == some (.boolean true))
      | _ => false
    | _ => false

  -- Invalidation 1: BEL placement collision
  let cBadPlace := projectGdsii "pnr_bad_place" collidingBelPnrCert
  let okBadPlace :=
    (!checkPnrCertificate validAdderBelNetlist corner7nm_SS 2000 collidingBelPnrCert) &&
    match cBadPlace with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "placement_injective" == some (.boolean false))
      | _ => false
    | _ => false

  -- Invalidation 2: PIP routing short circuit
  let cBadRoute := projectGdsii "pnr_bad_route" shortedWirePnrCert
  let okBadRoute :=
    (!checkPnrCertificate validAdderBelNetlist corner7nm_SS 2000 shortedWirePnrCert) &&
    match cBadRoute with
    | .cell _ .hardwareLayout ast _ _ =>
      match ast with
      | .record fields =>
        (fields.lookup "routing_disjoint" == some (.boolean false))
      | _ => false
    | _ => false

  -- Invalidation 3: Netlist cell-count / LUT-init mismatch
  let okBadNetlist :=
    !checkPnrCertificate { validAdderBelNetlist with cells := [] } corner7nm_SS 2000 validAdderPnrCert

  okPass && okBadPlace && okBadRoute && okBadNetlist

#guard test_pnr_signoff_stress == true

-- Test 3.5: Read-Only Invariance & Purity Check
def test_readonly_projection_invariance : Bool :=
  -- Verify projectCircuit is a pure function that does not alter input
  let m : Circuit := {
    name := "pure_mod"
    inputNames := ["a"]
    wires := []
    regs := []
    outputs := []
  }
  let c1 := projectCircuit "p1" m
  let c2 := projectCircuit "p1" m
  (c1 == c2) && (m.name == "pure_mod")

#guard test_readonly_projection_invariance == true

end Obend.Challenger.M5
