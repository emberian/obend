module

public import Obend.Tactic.Tooth
public import Obend.Leaf.Flatten
public import Obend.Hardware.OpenUSD
public import Obend.Hardware.GeometryCAM
public import Obend.Hardware.Codec
public import Obend.Hardware.Judge
import all Obend.Hardware.OpenUSD
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.Codec
import all Obend.Hardware.Judge

/-!
# Metasystem Test Suite — Unified OpenUSD `SdfLayer` $\to$ `Term.mix`, Linear SSA F-Rep `SsaTapeOp` & Continuous-Time 5-Axis Swept-Volume CAM (`WS-D`)

Comprehensive universal theorem checks, boundary & negative refutation tests, `#tooth`
kernel mutation-killing probes, and `#print axioms` verification (`0 sorryAx`) across:
1. `Obend.Hardware.OpenUSD`:
   - `PrimSpec`, `SdfLayer`, `buildPcpPrimIndex`, `composePrimToTerm`, `composePrimToTerm_eq_composition_object`,
   - `usdArcKind_strength_le_local`, `insertPrimByStrength_localArc_head`,
   - `liverps_local_dominates_term`, `liverps_local_overrides_preceding_reference_eval`,
   - `XformOp3D`, `applyXformOpPoint`, `applyXformStackPoint`, `evalFRepAffine3DXform`,
     `xform_translate_inverse_exact`, `xform_rot90Z_fourfold_identity`, `evalFRepAffine3DXform_enclosesAt`,
   - `computeShellWallThicknessUm`, `mkCertifiedUsdPhysicalState`,
     `computeShellWallThicknessUm_nonneg`, `computeShellWallThicknessUm_lipschitz_lower_bound`.
2. `Obend.Hardware.GeometryCAM`:
   - `.csgDiff` right-branch pruning (`pruneFRepTape_sound`, `pruneFRepTape_size_le`, `csgDiff_right_branch_pruning_sound`),
   - Linear SSA register tape (`SsaTapeOp`, `evalSsaTape`, `pruneSsaTapeForBox`, `compactSsaTape`, `compactSsaTapeFull`),
   - `pruneSsaTapeForBox_sound`, `compactSsaTape_length_le`, `compactSsaTapeFull_length_le`,
     `prune_and_compact_ssa_tape_sound`, `golden_ssa_tape_prune_and_compact_verified`,
   - Continuous-time 5-axis swept-volume CAM (`translateFRep`, `synthesizeSweptVolume`,
     `evalFRepPoint_synthesizeSweptVolume_le_waypoint`, `continuous_swept_volume_no_gouge_sound`).
3. `Obend.Hardware.Codec` & `Obend.Hardware.Judge`:
   - RFC 8949 `0x9A` 4-byte CBOR array-length header (`cborDecodeArrHeader32_encode_append`, `decode_encode_binaryTapeCert`),
   - Fixed-arity domain (`BinaryHwCert`) bypass refusal (`pnr_tape_cert_bypass_refused`,
     `verifyRawBinaryCborCert_refuses_pnr_tape_bypass`),
   - Numeric wire-string field decoding (`extractNatField`, `extractIntField`,
     `extractNatField_and_extractIntField_verified`).
-/

@[expose] public section
namespace Obend.Tests.Metasystem.OpenUsdAndSsaTapeTest

open Obend.Core
open Obend.Core.Term
open Obend.Logic
open Obend.Equiv
open Obend.Leaf
open Obend.Hardware.GeometryCAM
open Obend.Hardware.OpenUSD
open Obend.Hardware.Codec
open Obend.Hardware.Judge
set_option autoImplicit false

/-! ## 1. Pillar 1 Tests: Unified OpenUSD `SdfLayer` $\to$ `Core4` `Term.mix` / `Term.fix` & LIVERPS Dominance -/

def testTargetStatorPath : SdfPath := ["StatorAssembly", "PhaseU", "CoolingJacket"]

def testReferencePrim : PrimSpec where
  path := testTargetStatorPath
  arc := .referencesArc
  fields :=
    [ ("thermalResistance", .nat 29)
    , ("wallThicknessUm", .nat 2400)
    ]

def testLocalOverridePrim : PrimSpec where
  path := testTargetStatorPath
  arc := .localArc
  fields :=
    [ ("thermalResistance", .nat 9)
    ]

def testLayers : List SdfLayer :=
  [ { layerId := "vendor_ref.usda", prims := [testReferencePrim] }
  , { layerId := "local_override.usda", prims := [testLocalOverridePrim] }
  ]

/-- 1.1 Universal LIVERPS local-dominance theorem over `Core4` `Term.mix` & `Obend.Leaf.flatten`. -/
theorem test_liverps_local_dominates_term
    (target : SdfPath) (m : String) (vLocal vWeak : Term)
    (weakArc : UsdArcKind) (seedFields : List (String × Term)) :
    let localSpec : PrimSpec := { path := target, arc := .localArc, fields := [(m, vLocal)] }
    let weakSpec  : PrimSpec := { path := target, arc := weakArc,   fields := [(m, vWeak)] }
    let layers : List SdfLayer :=
      [ { layerId := "localLayer", prims := [localSpec] }
      , { layerId := "weakLayer",  prims := [weakSpec] } ]
    let C := primSpecsToComposition (collectTargetPrims layers target) seedFields
    let resolvedLocal := Obend.Logic.openTerm vLocal C.object (C.superAt 0)
    Steps (.get (composePrimToTerm layers target (.record seedFields)) m) resolvedLocal ∧
    (.get (composePrimToTerm layers target (.record seedFields)) m ≈b resolvedLocal) ∧
    (C.closedB = true → (.get C.flatten m ≈b resolvedLocal)) :=
  liverps_local_dominates_term target m vLocal vWeak weakArc seedFields

/-- 1.2 Universal LIVERPS override corollary: even when a `referencesArc` layer precedes `localArc` in `layers`,
    `composePrimToTerm` sorts by LIVERPS strength and evaluates `.get ... m` to `.nat nLocal`. -/
theorem test_liverps_local_overrides_preceding_reference_eval
    (target : SdfPath) (m : String) (nLocal nRef : Nat) :
    let refLayer   : SdfLayer := { layerId := "vendorRef.usd", prims := [{ path := target, arc := .referencesArc, fields := [(m, .nat nRef)] }] }
    let localLayer : SdfLayer := { layerId := "sessionLocal.usd", prims := [{ path := target, arc := .localArc, fields := [(m, .nat nLocal)] }] }
    let layers := [refLayer, localLayer]
    let C := primSpecsToComposition (collectTargetPrims layers target) []
    Evaluates (.get (composePrimToTerm layers target (.record [])) m) (.nat nLocal) ∧
    (C.closedB = true → (.get C.flatten m ≈b .nat nLocal)) :=
  liverps_local_overrides_preceding_reference_eval target m nLocal nRef

/-- 1.2b Universal two-arc LIVERPS dominance across all 7 arc kinds in both layer orders, plus same-arc sublayer tie-breaking. -/
theorem test_liverps_stronger_arc_and_sublayer_tiebreak
    (target : SdfPath) (m : String) (vStrong vWeak : Term)
    (strongArc weakArc : UsdArcKind) (seedFields : List (String × Term))
    (hLt : weakArc.strength < strongArc.strength) :
    let strongSpec : PrimSpec := { path := target, arc := strongArc, fields := [(m, vStrong)] }
    let weakSpec   : PrimSpec := { path := target, arc := weakArc,   fields := [(m, vWeak)] }
    let strongLayer : SdfLayer := { layerId := "strongLayer", prims := [strongSpec] }
    let weakLayer   : SdfLayer := { layerId := "weakLayer",   prims := [weakSpec] }
    let layersFwd := [strongLayer, weakLayer]
    let layersRev := [weakLayer, strongLayer]
    let CFwd := primSpecsToComposition (collectTargetPrims layersFwd target) seedFields
    let CRev := primSpecsToComposition (collectTargetPrims layersRev target) seedFields
    let resolvedFwd := Obend.Logic.openTerm vStrong CFwd.object (CFwd.superAt 0)
    let resolvedRev := Obend.Logic.openTerm vStrong CRev.object (CRev.superAt 0)
    Steps (.get (composePrimToTerm layersFwd target (.record seedFields)) m) resolvedFwd ∧
    Steps (.get (composePrimToTerm layersRev target (.record seedFields)) m) resolvedRev ∧
    (CFwd.closedB = true → (.get CFwd.flatten m ≈b resolvedFwd)) ∧
    (CRev.closedB = true → (.get CRev.flatten m ≈b resolvedRev)) :=
  liverps_stronger_arc_dominates_term target m vStrong vWeak strongArc weakArc seedFields hLt

theorem test_liverps_sublayer_tiebreak
    (target : SdfPath) (m : String) (v0 v1 : Term)
    (arc : UsdArcKind) (seedFields : List (String × Term)) :
    let spec0 : PrimSpec := { path := target, arc := arc, fields := [(m, v0)] }
    let spec1 : PrimSpec := { path := target, arc := arc, fields := [(m, v1)] }
    let layers : List SdfLayer :=
      [ { layerId := "subLayer0", prims := [spec0] }
      , { layerId := "subLayer1", prims := [spec1] } ]
    let C := primSpecsToComposition (collectTargetPrims layers target) seedFields
    let resolved0 := Obend.Logic.openTerm v0 C.object (C.superAt 0)
    Steps (.get (composePrimToTerm layers target (.record seedFields)) m) resolved0 ∧
    (.get (composePrimToTerm layers target (.record seedFields)) m ≈b resolved0) ∧
    (C.closedB = true → (.get C.flatten m ≈b resolved0)) :=
  liverps_sublayer_tiebreak_dominates_term target m v0 v1 arc seedFields

/-- 1.3 Concrete multi-layer `SdfLayer` `buildPcpPrimIndex` ordering and `Obend.Leaf.Composition.flatten` check. -/
theorem test_sdf_layer_pcp_index_and_flatten :
    let idx := buildPcpPrimIndex testLayers testTargetStatorPath
    idx.length = 2 ∧
    idx.map (·.arc) = [.localArc, .referencesArc] ∧
    Evaluates (.get (composePrimToTerm testLayers testTargetStatorPath (.record [])) "thermalResistance") (.nat 9) := by
  refine ⟨rfl, rfl, ⟨?_, .natural 9⟩⟩
  let C := primSpecsToComposition (collectTargetPrims testLayers testTargetStatorPath) []
  have hProv : Obend.Logic.providesLast C.layers "thermalResistance" = some 0 := rfl
  have hBody : Obend.Logic.bodyAt C.layers 0 "thermalResistance" = some (.nat 9) := rfl
  have hOpen : Obend.Logic.openTerm (.nat 9) C.object (C.superAt 0) = .nat 9 := by
    simp [Obend.Logic.openTerm, Term.substitute]
  rw [composePrimToTerm_eq_composition_object testLayers testTargetStatorPath [], ← hOpen]
  exact Obend.Logic.late_binding C "thermalResistance" 0 (.nat 9) hProv hBody

/-! ## 2. Pillar 2 Tests: 3D `XformOp3D` Spatial Transform Stacks & Certified Geometric Wall Thickness -/

/-- 2.1 Universal `XformOp3D` inverse translation and 4-fold $90^\circ$ $Z$-rotation identity. -/
theorem test_xform_identities (dx dy dz x y z : Int) :
    applyXformStackPoint [.translate dx dy dz, .translate (-dx) (-dy) (-dz)] (x, y, z) = (x, y, z) ∧
    applyXformStackPoint [.rot90Z, .rot90Z, .rot90Z, .rot90Z] (x, y, z) = (x, y, z) :=
  ⟨xform_translate_inverse_exact dx dy dz x y z, xform_rot90Z_fourfold_identity x y z⟩

/-- 2.2 Universal 3D affine enclosure theorem under arbitrary `XformOp3D` stacks. -/
theorem test_evalFRepAffine3DXform_enclosesAt
    (ops : List XformOp3D) (ax ay az : AffineForm3D) (x y z ex ey ez : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (hx : ax.enclosesAt ex ey ez x)
    (hy : ay.enclosesAt ex ey ez y)
    (hz : az.enclosesAt ex ey ez z)
    (e : FRepExpr) :
    (evalFRepAffine3DXform ops ax ay az e).toInterval.contains
      (evalFRepPointXform ops x y z e) :=
  evalFRepAffine3DXform_enclosesAt ops ax ay az x y z ex ey ez hEx hEy hEz hx hy hz e

/-- 2.3 Certified geometric shell wall thickness (`computeShellWallThicknessUm`) and `mkCertifiedUsdPhysicalState`. -/
def testOuterHousingFRep : FRepExpr :=
  .offset 10000 (.add (.add (.sq .varX) (.sq .varY)) (.sq .varZ))

def testInnerBoreFRep : FRepExpr :=
  .offset 6400 (.add (.add (.sq .varX) (.sq .varY)) (.sq .varZ))

theorem test_certified_shell_wall_thickness_and_lifecycle_gate :
    let wallUm := computeShellWallThicknessUm testOuterHousingFRep testInnerBoreFRep (80, 0, 0) 2
    let st := mkCertifiedUsdPhysicalState 10 testOuterHousingFRep testInnerBoreFRep (80, 0, 0) 2 85000 120
    wallUm = 1800 ∧
    st.wallThicknessUm = 1800 ∧
    checkPartLifecycleInvariant 1200 180000 st = true := by
  decide +kernel

theorem test_computeShellWallThicknessUm_lipschitz_lower_bound
    (outer inner : FRepExpr) (px py pz L : Int)
    (hL : 1 ≤ L)
    (hOrder : evalFRepPoint px py pz outer ≤ evalFRepPoint px py pz inner) :
    computeShellWallThicknessUm outer inner (px, py, pz) L * L ≤
      evalFRepPoint px py pz inner - evalFRepPoint px py pz outer :=
  computeShellWallThicknessUm_lipschitz_lower_bound outer inner px py pz L hL hOrder

theorem test_computeShellWallThicknessAffine3DUm_lipschitz_lower_bound
    (ops : List XformOp3D) (outer inner : FRepExpr)
    (ax ay az : AffineForm3D) (x y z ex ey ez lipschitzBound : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (hx : ax.enclosesAt ex ey ez x)
    (hy : ay.enclosesAt ex ey ez y)
    (hz : az.enclosesAt ex ey ez z)
    (hL : 1 ≤ lipschitzBound)
    (hSep : (evalFRepAffine3DXform ops ax ay az outer).toInterval.hi ≤
            (evalFRepAffine3DXform ops ax ay az inner).toInterval.lo) :
    computeShellWallThicknessAffine3DUm ops outer inner ax ay az lipschitzBound * lipschitzBound ≤
      evalFRepPointXform ops x y z inner - evalFRepPointXform ops x y z outer :=
  computeShellWallThicknessAffine3DUm_lipschitz_lower_bound
    ops outer inner ax ay az x y z ex ey ez lipschitzBound hEx hEy hEz hx hy hz hL hSep

/-! ## 3. Pillar 3 Tests: `.csgDiff` Right-Branch Pruning, Linear SSA `SsaTapeOp` & Continuous-Time 5-Axis Swept-Volume CAM -/

/-- 3.1 `.csgDiff` right-branch pruning: when tool `b` completely removes the voxel cell (`ivMaxChoice a (-b) = .right`),
    `pruneFRepTape` simplifies `.csgDiff a b` to `.sub (.const 0) (pruneFRepTape B b)` with exact point evaluation! -/
def testCarvedBox : Box3D where
  xIv := { lo := 0, hi := 2 }
  yIv := { lo := 0, hi := 2 }
  zIv := { lo := 0, hi := 2 }

def testStockExpr : FRepExpr := .add .varX (.const (-50))
def testCarvingToolExpr : FRepExpr := .add .varY (.const (-10))

theorem test_csgDiff_right_branch_prunes_stock :
    let e := FRepExpr.csgDiff testStockExpr testCarvingToolExpr
    let pruned := pruneFRepTape testCarvedBox e
    ivMaxChoice (evalFRepInterval testCarvedBox testStockExpr)
      (ivNeg (evalFRepInterval testCarvedBox testCarvingToolExpr)) = .right ∧
    pruned = .sub (.const 0) testCarvingToolExpr ∧
    frepNodeCount pruned < frepNodeCount e ∧
    evalFRepPoint 1 1 1 pruned = evalFRepPoint 1 1 1 e := by
  decide +kernel

/-- 3.2 Linear SSA register tape (`SsaTapeOp`) interval pruning and backward-liveness compaction soundness. -/
theorem test_ssa_tape_prune_and_compact_sound
    (B : Box3D) (x y z : Int) (tape : List SsaTapeOp) (rootReg : Nat)
    (hBox : B.contains x y z) (hRoot : rootReg < tape.length) :
    let pruned := pruneSsaTapeForBox B tape
    let compacted := compactSsaTape pruned rootReg
    evalSsaTape x y z compacted (compacted.length - 1) = evalSsaTape x y z tape rootReg ∧
    compacted.length ≤ tape.length :=
  prune_and_compact_ssa_tape_sound B x y z tape rootReg hBox hRoot

theorem test_golden_ssa_tape_compaction :
    let box : Box3D :=
      { xIv := { lo := -2, hi := 2 }
      , yIv := { lo := -2, hi := 2 }
      , zIv := { lo := -2, hi := 2 } }
    let ssaStatorTape : List SsaTapeOp :=
      [ .varX, .mul 0 0, .varY, .mul 2 2, .add 1 3, .const 100, .sub 4 5,
        .const 15, .sub 0 7, .mul 8 8, .add 9 3, .const 4, .sub 10 11,
        .minUnion 6 12,
        .add 0 7, .mul 14 14, .add 15 3, .sub 16 11, .neg 17,
        .maxInter 13 18 ]
    let pruned := pruneSsaTapeForBox box ssaStatorTape
    let compacted := compactSsaTape pruned 19
    let fullCompacted := compactSsaTapeFull pruned 19
    ssaStatorTape.length = 20 ∧
    compacted.length = 7 ∧
    fullCompacted.length = 7 ∧
    evalSsaTape 1 1 0 compacted (compacted.length - 1) = evalSsaTape 1 1 0 ssaStatorTape 19 :=
  golden_ssa_tape_prune_and_compact_verified

theorem test_golden_ssa_tape_right_branch_compaction :
    let boxLug : Box3D :=
      { xIv := { lo := 14, hi := 16 }
      , yIv := { lo := -1, hi := 1 }
      , zIv := { lo := -1, hi := 1 } }
    let boxBore : Box3D :=
      { xIv := { lo := -16, hi := -14 }
      , yIv := { lo := -1, hi := 1 }
      , zIv := { lo := -1, hi := 1 } }
    let ssaStatorTape : List SsaTapeOp :=
      [ .varX, .mul 0 0, .varY, .mul 2 2, .add 1 3, .const 100, .sub 4 5,
        .const 15, .sub 0 7, .mul 8 8, .add 9 3, .const 4, .sub 10 11,
        .minUnion 6 12,
        .add 0 7, .mul 14 14, .add 15 3, .sub 16 11, .neg 17,
        .maxInter 13 18 ]
    let ssaBoreTape : List SsaTapeOp :=
      [ .varX, .mul 0 0, .varY, .mul 2 2, .add 1 3, .const 400, .sub 4 5,
        .const 15, .sub 0 7, .mul 8 8, .add 9 3, .const 4, .sub 10 11,
        .minUnion 6 12,
        .add 0 7, .mul 14 14, .add 15 3, .sub 16 11, .neg 17,
        .maxInter 13 18 ]
    let compactedLug  := compactSsaTape (pruneSsaTapeForBox boxLug ssaStatorTape) 19
    let compactedBore := compactSsaTape (pruneSsaTapeForBox boxBore ssaBoreTape) 19
    compactedLug.length = 9 ∧
    compactedBore.length = 10 ∧
    evalSsaTape 15 0 0 compactedLug (compactedLug.length - 1) = evalSsaTape 15 0 0 ssaStatorTape 19 ∧
    evalSsaTape (-15) 0 0 compactedBore (compactedBore.length - 1) = evalSsaTape (-15) 0 0 ssaBoreTape 19 :=
  golden_ssa_tape_right_branch_compaction_verified

/-- 3.3 Continuous-time 5-axis swept-volume CAM envelope (`synthesizeSweptVolume`) soundness. -/
theorem test_continuous_swept_volume_no_gouge
    (B : Box3D) (fStock tool : FRepExpr)
    (waypoints : List (Int × Int × Int))
    (stepLipschitzPad stepDist L : Int)
    (wx wy wz tx ty tz x y z : Int)
    (hNoGouge : checkVoxelNoGouge B (synthesizeSweptVolume tool waypoints stepLipschitzPad) = true)
    (hInBox : B.contains x y z)
    (hWay : (wx, wy, wz) ∈ waypoints)
    (hPad : stepDist * L ≤ stepLipschitzPad)
    (hLip : evalFRepPoint (x - wx) (y - wy) (z - wz) tool -
              evalFRepPoint (x - tx) (y - ty) (z - tz) tool ≤ stepDist * L) :
    0 < evalFRepPoint x y z (translateFRep tx ty tz tool) ∧
    (inSolid x y z fStock → inSolid x y z (.csgDiff fStock (translateFRep tx ty tz tool))) :=
  continuous_swept_volume_no_gouge_sound B fStock tool waypoints stepLipschitzPad stepDist L
    wx wy wz tx ty tz x y z hNoGouge hInBox hWay hPad hLip

def testBallEndMill : FRepExpr :=
  .offset 25 (.add (.add (.sq .varX) (.sq .varY)) (.sq .varZ))

def testWaypoints : List (Int × Int × Int) := [(20, 0, 0), (20, 10, 0), (20, 20, 0)]

def testPartBox : Box3D where
  xIv := { lo := -2, hi := 2 }
  yIv := { lo := -2, hi := 2 }
  zIv := { lo := -2, hi := 2 }

theorem test_concrete_5axis_swept_volume_safe_at_part_origin :
    let swept := synthesizeSweptVolume testBallEndMill testWaypoints 15
    checkVoxelNoGouge testPartBox swept = true ∧
    0 < evalFRepPoint 0 0 0 (translateFRep 20 5 0 testBallEndMill) := by
  decide +kernel

/-! ## 4. Pillar 4 Tests: RFC 8949 `0x9A` 4-Byte Array Header, `.pnr` Tape Bypass Refusal & Wire Field Decoding -/

/-- 4.1 RFC 8949 `0x9A` 4-byte array-length roundtrip on `BinaryTapeCert`. -/
theorem test_binary_tape_cert_roundtrip (c : BinaryTapeCert) (hWf : c.WellFormed) :
    decodeBinaryTapeCert (encodeBinaryTapeCert c) = some c :=
  decode_encode_binaryTapeCert c hWf

/-- 4.2 `.pnr` fixed-arity domain bypass via 1-word `BinaryTapeCert` is strictly refused. -/
theorem test_pnr_tape_bypass_refused :
    let fakePnrTape : BinaryTapeCert := { domain := .pnr, metric0 := 100, metric1 := 100, words := [1] }
    let rawBytes := ByteArray.mk (encodeBinaryTapeCert fakePnrTape).toArray
    verifyBinaryTapeCert fakePnrTape = false ∧
    verifyRawBinaryCborCert .pnr rawBytes = .refused (.binaryCborCertViolation 1) [] :=
  ⟨rfl, verifyRawBinaryCborCert_refuses_pnr_tape_bypass⟩

/-- 4.3 Wire-string numeric field parsers (`extractNatField` / `extractIntField`) drive real certification. -/
theorem test_wire_numeric_field_parsers :
    extractNatField "{\"mode\": \"golden\", \"antennaRatio\": 2400}" "antennaRatio" = some 2400 ∧
    extractIntField "{\"mode\": \"golden\", \"minMarginMv\": -150}" "minMarginMv" = some (-150) ∧
    extractNatField "bendRadiusNm=2000,circumferenceUm=50" "bendRadiusNm" = some 2000 ∧
    (let mrr :=
       { Obend.Hardware.Photonics.goldenSoi220Microring with
         bendRadiusNm := (extractNatField "{\"mode\": \"golden\", \"bendRadiusNm\": 2000}" "bendRadiusNm").getD
           Obend.Hardware.Photonics.goldenSoi220Microring.bendRadiusNm }
     checkPhotonicsPicJudge 0 15000 mrr =
       .refused (.photonicsPicSignoffViolation Obend.Hardware.Photonics.goldenSoi220Microring.ringName) []) ∧
    (let meander :=
       { Obend.Hardware.PCB.goldenDdrMeander with
         numSegments := (extractNatField "{\"mode\": \"golden\", \"numSegments\": 0}" "numSegments").getD
           Obend.Hardware.PCB.goldenDdrMeander.numSegments }
     checkPcbBoardJudge 0 50 meander = .refused (.pcbBoardSignoffViolation "DDR_CLK_MEANDER") []) :=
  extractNatField_and_extractIntField_verified

theorem test_wire_token_boundary_and_decoders :
    extractNatField "{\"max_fanout\": 99, \"mode\": \"calibrated\"}" "fanout" = none ∧
    extractNatField "max_fanout=99,mode=calibrated" "fanout" = none ∧
    extractIntField "{\"extra_minMarginMv\": -500}" "minMarginMv" = none ∧
    (match decodePhotonicsCert "mode=golden,bendRadiusNm=2000,circumferenceUm=50" with
     | .ok c => c.bendRadiusNm == 2000 && c.circumferenceUm == 50 &&
       checkPhotonicsPicJudge 0 15000 c == .refused (.photonicsPicSignoffViolation Obend.Hardware.Photonics.goldenSoi220Microring.ringName) []
     | .error _ => false) = true ∧
    (match decodePcbBoardCert "mode=golden,numSegments=0" with
     | .ok c => c.numSegments == 0 &&
       checkPcbBoardJudge 0 50 c == .refused (.pcbBoardSignoffViolation "DDR_CLK_MEANDER") []
     | .error _ => false) = true :=
  extractNatField_token_boundary_and_decoders_verified

/-! ## 5. `#tooth` Mutation-Killing Probes & `#print axioms` Verification (`0 sorryAx`) -/

/-- Tooth 1: Broken `insertPrimByStrength` that appends `p` after `q` even when `p` is a stronger `localArc`. -/
def insertPrimByStrengthInverted (p : PrimSpec) : List PrimSpec → List PrimSpec
  | [] => [p]
  | q :: rest =>
    if p.arc.strength < q.arc.strength then
      p :: q :: rest
    else
      q :: insertPrimByStrengthInverted p rest

#tooth Obend.Hardware.OpenUSD.insertPrimByStrength_localArc_head by mutation Obend.Hardware.OpenUSD.insertPrimByStrength := insertPrimByStrengthInverted

/-- Tooth 2: Broken `applyXformOpPoint` that adds `dx` instead of subtracting on translation pullback. -/
def applyXformOpPointBrokenTranslate (op : XformOp3D) (pt : Int × Int × Int) : Int × Int × Int :=
  let (x, y, z) := pt
  match op with
  | .translate dx _ _ => (x + dx + 1, y, z)
  | .rot90Z           => (y, -x, z)
  | .rot90X           => (x, z, -y)
  | .rot90Y           => (-z, y, x)
  | .scalePos k       => (Int.ofNat k * x, Int.ofNat k * y, Int.ofNat k * z)

#tooth Obend.Hardware.OpenUSD.xform_translate_inverse_exact by mutation Obend.Hardware.OpenUSD.applyXformOpPoint := applyXformOpPointBrokenTranslate

/-- Tooth 3: Broken `pruneFRepTape` that prunes `.csgDiff a b` on `.right` to `pruneFRepTape B b` (forgetting the unary negation `.sub (.const 0) ...`). -/
def pruneFRepTapeForgotNeg (B : Box3D) (e : FRepExpr) : FRepExpr :=
  match e with
  | .const c      => .const c
  | .varX         => .varX
  | .varY         => .varY
  | .varZ         => .varZ
  | .add a b      => .add (pruneFRepTapeForgotNeg B a) (pruneFRepTapeForgotNeg B b)
  | .sub a b      => .sub (pruneFRepTapeForgotNeg B a) (pruneFRepTapeForgotNeg B b)
  | .scalePos k a => .scalePos k (pruneFRepTapeForgotNeg B a)
  | .sq a         => .sq (pruneFRepTapeForgotNeg B a)
  | .csgUnion a b =>
    match ivMinChoice (evalFRepInterval B a) (evalFRepInterval B b) with
    | .left  => pruneFRepTapeForgotNeg B a
    | .right => pruneFRepTapeForgotNeg B b
    | _      => .csgUnion (pruneFRepTapeForgotNeg B a) (pruneFRepTapeForgotNeg B b)
  | .csgInter a b =>
    match ivMaxChoice (evalFRepInterval B a) (evalFRepInterval B b) with
    | .left  => pruneFRepTapeForgotNeg B a
    | .right => pruneFRepTapeForgotNeg B b
    | _      => .csgInter (pruneFRepTapeForgotNeg B a) (pruneFRepTapeForgotNeg B b)
  | .csgDiff a b  =>
    match ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) with
    | .left  => pruneFRepTapeForgotNeg B a
    | .right => pruneFRepTapeForgotNeg B b
    | _      => .csgDiff (pruneFRepTapeForgotNeg B a) (pruneFRepTapeForgotNeg B b)
  | .offset r a   => .offset r (pruneFRepTapeForgotNeg B a)

#tooth Obend.Hardware.GeometryCAM.csgDiff_right_branch_pruning_sound by mutation Obend.Hardware.GeometryCAM.pruneFRepTape := pruneFRepTapeForgotNeg

/-- Tooth 4: Broken `verifyBinaryTapeCert` that restores the permissive `_ => decide (c.words.length ≥ 1)` catch-all bypass. -/
def verifyBinaryTapeCertPermissive (c : BinaryTapeCert) : Bool :=
  match c.domain with
  | .magnetics           => decide (c.words.length ≥ 3 ∧ c.metric0 > 0 ∧ c.metric1 ≤ 5000000)
  | .mechanicsVonNeumann => decide (c.words.length ≥ 4 ∧ c.metric1 ≤ c.metric0 ∧ c.metric1 > 0)
  | .fluidThermal        => decide (c.words.length ≥ 4 ∧ c.metric0 ≥ 64 ∧ c.metric1 ≤ 165000)
  | .powerElectronics    => decide (c.words.length ≥ 2 ∧ c.metric0 ≤ 1150)
  | .multiphysics        => decide (c.words.length ≥ 2 ∧ c.metric0 > 0)
  | _                    => decide (c.words.length ≥ 1)

#tooth Obend.Hardware.Codec.pnr_tape_cert_bypass_refused by mutation Obend.Hardware.Codec.verifyBinaryTapeCert := verifyBinaryTapeCertPermissive

/-- Tooth 5: Broken `compactSsaTape` that only truncates trailing ops via `tape.take (liveRoot + 1)`
    without eliminating dead preceding branches or single-branch CSG forwarding ops. -/
def compactSsaTapeTruncateOnly (tape : List SsaTapeOp) (rootReg : Nat) : List SsaTapeOp :=
  let liveRoot := resolveSsaLiveRoot tape tape.length rootReg
  tape.take (liveRoot + 1)

#tooth Obend.Hardware.GeometryCAM.golden_ssa_tape_right_branch_compaction_verified by mutation Obend.Hardware.GeometryCAM.compactSsaTape := compactSsaTapeTruncateOnly

#print axioms Obend.Hardware.OpenUSD.liverps_local_dominates_term
#print axioms Obend.Hardware.OpenUSD.liverps_local_overrides_preceding_reference_eval
#print axioms Obend.Hardware.OpenUSD.liverps_stronger_arc_dominates_term
#print axioms Obend.Hardware.OpenUSD.liverps_sublayer_tiebreak_dominates_term
#print axioms Obend.Hardware.OpenUSD.evalFRepAffine3DXform_enclosesAt
#print axioms Obend.Hardware.OpenUSD.computeShellWallThicknessUm_lipschitz_lower_bound
#print axioms Obend.Hardware.OpenUSD.computeShellWallThicknessAffine3DUm_lipschitz_lower_bound
#print axioms Obend.Hardware.GeometryCAM.pruneFRepTape_sound
#print axioms Obend.Hardware.GeometryCAM.csgDiff_right_branch_pruning_sound
#print axioms Obend.Hardware.GeometryCAM.compactSsaTape_length_le
#print axioms Obend.Hardware.GeometryCAM.prune_and_compact_ssa_tape_sound
#print axioms Obend.Hardware.GeometryCAM.golden_ssa_tape_right_branch_compaction_verified
#print axioms Obend.Hardware.GeometryCAM.continuous_swept_volume_no_gouge_sound
#print axioms Obend.Hardware.Codec.decode_encode_binaryTapeCert
#print axioms Obend.Hardware.Codec.pnr_tape_cert_bypass_refused
#print axioms Obend.Hardware.Judge.verifyRawBinaryCborCert_refuses_pnr_tape_bypass
#print axioms Obend.Hardware.Judge.extractNatField_and_extractIntField_verified
#print axioms Obend.Hardware.Judge.extractNatField_token_boundary_and_decoders_verified

end Obend.Tests.Metasystem.OpenUsdAndSsaTapeTest
end
