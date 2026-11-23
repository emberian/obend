import Obend.Hardware.OspcSignalFabric
import Obend.Hardware.OspcProver
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/hardware/Ospc4TileFabulousDpiTest.lean`

Comprehensive verification, `10` genuine `#tooth` mutation-sensitivity kills across every layer
of the Pillar-2 OSPC 4-Tile hardware spine (`RtlSignal` / `cdcSync2FF`, `synthesizeModuleToBels`,
`FABulous`/ECP5 bitstream decode & `Net` refinement, isolated `obend-hw-dpi` codec & server,
and `Obend.Hardware.OspcProver.ospc_4tile_fabulous_ecp5_refines_spec`), plus `#assert_axioms_tree`.
-/

namespace Obend.Tests.Hardware.Ospc4TileFabulousDpiTest

open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Fabulous
open Obend.Hardware.OspcSignalFabric
open Obend.Hardware.OspcProver

set_option autoImplicit false

/-! ## 1. Positive Sanity Checks Across Signal Fabric, Bitstream Decode & DPI Codec -/

#guard (decodeAndExtractFabulous ospcKernelFabric ospcFabricPins ospcFabulousBitstream).toOption == some ospcExtractedNet
#guard ((decodeBin 2 3 ospcFabulousBitstream >>= fun cfg =>
          extract ospcFabulousFabric cfg ospcFabricPins).map Prod.fst).toOption == some ospcExtractedNet
#guard (decodeBin 2 3 corruptSyncBitstream).isOk == false
#guard (decodeBin 2 3 corruptDesyncBitstream).isOk == false
#guard (decodeBin 2 3 corruptFrameSelectBitstream).isOk == false
#guard (decodeBin 2 3 corruptTruncatedBitstream).isOk == false
#guard (decodeAndExtractFabulous ospcKernelFabric ospcFabricPins corruptPipSelectBitstream).isOk == false
#guard (decodeAndExtractFabulous ospcKernelFabric ospcFabricPins corruptI0MuxCarryBitstream).isOk == false
#guard ((decodeBin 2 3 corruptPipSelectBitstream >>= fun cfg =>
          extract ospcFabulousFabric cfg ospcFabricPins)).isOk == false

def testSampleReq : OspcDpiReq :=
  { domain := .hostDpi, seqNo := 0#32, rst := false
  , tile0OpSel := 3#2, tile0InLo64 := 0x0123456789ABCDEF#64, tile0InHi17 := 0x15A5A#17
  , tile0CamWe := 1#1, tile0CamAddr := 7#8, tile0CamWdata := 0xDEADBEEFCAFEBABE#64, tile0CamQtag := 0xDEADBEEFCAFEBABE#64
  , tile1StepEn := 1#1, tile1SymTag := 0x15#6, tile1LutWe := 1#1, tile1LutWaddr := 0x015#12, tile1LutWdata := 0x2A#64
  , tile2RedexEn := 0#1, tile2PeerWord := 0#64, tile2PortWe := 1#1, tile2PortAddr := 2#8, tile2PortWdata := 0x0000001000100003#64
  , tile3StepEn := 0#1, tile3ClauseWe := 1#1, tile3ClauseAddr := 1#8, tile3ClauseWdata := 1#64 }

private def reqOk (r : Except OspcDpiError OspcDpiReq) (expected : OspcDpiReq) : Bool :=
  match r with
  | .ok v => v == expected
  | .error _ => false

private def reqErr (r : Except OspcDpiError OspcDpiReq) (expected : OspcDpiError) : Bool :=
  match r with
  | .ok _ => false
  | .error e => e == expected

#guard (encodeOspcDpiReq testSampleReq).size == 90
#guard reqOk (decodeOspcDpiReq (encodeOspcDpiReq testSampleReq)) testSampleReq
#guard reqErr (decodeOspcDpiReq ((encodeOspcDpiReq testSampleReq).set! 0 0x00)) .badMagic
#guard reqErr (decodeOspcDpiReq ((encodeOspcDpiReq testSampleReq).set! 4 0x02)) .badVersion
#guard reqErr (decodeOspcDpiReq ((encodeOspcDpiReq testSampleReq).set! 5 0x7F)) .badDomainTag
#guard reqErr (decodeOspcDpiReq ((encodeOspcDpiReq testSampleReq).set! 6 0x81)) .badMsgKind
#guard reqErr (decodeOspcDpiReq ((encodeOspcDpiReq testSampleReq).set! 7 0x02)) .badFlags
#guard reqErr (decodeOspcDpiReq ((encodeOspcDpiReq testSampleReq).set! 16 0x04)) .nonCanonicalField

/-! ## 2. `10` Genuine `#tooth` Kernel Mutation-Sensitivity Kills -/

-- Tooth 1 (`RtlSignal` / `cdcSync2FF`): Dropping 1 cycle of synchronizer latency breaks `cdcSync2FF_cycle1`:
def brokenCdc1FF {src dst : ClockDomain} {w : Nat} {iv : BitVec w}
    (s : RtlSignal src w iv) : RtlSignal dst w iv where
  atCycle
    | 0     => iv
    | n + 1 => s.atCycle n
  reset_zero := rfl

#tooth Obend.Hardware.OspcSignalFabric.cdcSync2FF_cycle1 by mutation
  Obend.Hardware.OspcSignalFabric.cdcSync2FF := @brokenCdc1FF

-- Tooth 2 (`ClockDomain` wire tags): Colliding `.hostDpi` and `.fabricCfg` tags breaks `ClockDomain.toTag_injective`:
def brokenDomainTag : ClockDomain → UInt8
  | .proverCore => 0x00
  | .hostDpi    => 0x01
  | .fabricCfg  => 0x01

#tooth Obend.Hardware.OspcSignalFabric.ClockDomain.toTag_injective by mutation
  Obend.Hardware.OspcSignalFabric.ClockDomain.toTag := brokenDomainTag

-- Tooth 3 (`FABulous` LUT4 truth table): Corrupting `OSPC_FACE_LUT4_INIT` breaks `ospc_face_lut4_spec`:
#tooth Obend.Hardware.OspcSignalFabric.ospc_face_lut4_spec by mutation
  Obend.Hardware.OspcSignalFabric.OSPC_FACE_LUT4_INIT := 0xCE8B#16

-- Tooth 4 (`FABulous` LUT4 truth table): Corrupting `OSPC_LIN_LUT4_INIT` breaks `ospc_lin_lut4_spec`:
#tooth Obend.Hardware.OspcSignalFabric.ospc_lin_lut4_spec by mutation
  Obend.Hardware.OspcSignalFabric.OSPC_LIN_LUT4_INIT := 0xFFFF#16

-- Tooth 5 (`FABulous` bitstream decoder): Always refusing in `decodeAndExtractFabulous` breaks universal `ospc_fabulous_bitstream_refines_slice`:
def brokenDecodeAndExtract (_fab : KernelFabric) (_pins : List Pin) (_bs : ByteArray) :
    Except String Net :=
  .error "broken_decoder"

#tooth Obend.Hardware.OspcSignalFabric.ospc_fabulous_bitstream_refines_slice by mutation
  Obend.Hardware.OspcSignalFabric.decodeAndExtractFabulous := brokenDecodeAndExtract

-- Tooth 6 (`FABulous` `Net` multi-cycle refinement): Flipping flop 1 reset value (`rv := false`) breaks universal `ospc_fabulous_bitstream_refines_slice`:
def brokenExtractedNetBadReset : Net where
  gates :=
    [ { init := OSPC_FACE_LUT4_INIT, i0 := .ff 0, i1 := .pin 2, i2 := .pin 0, i3 := .pin 1, site := "X1Y1.A" }
    , { init := OSPC_LIN_LUT4_INIT,  i0 := .ff 1, i1 := .pin 3, i2 := .pin 4, i3 := .const false, site := "X1Y1.B" } ]
  flops :=
    [ { d := .gate 0, en := .const true, sr := .pin 5, rv := false, site := "X1Y1.A" }
    , { d := .gate 1, en := .const true, sr := .pin 5, rv := false, site := "X1Y1.B" } ]
  outs := [(6, .ff 0), (7, .ff 1)]

#tooth Obend.Hardware.OspcSignalFabric.ospc_fabulous_bitstream_refines_slice by mutation
  Obend.Hardware.OspcSignalFabric.ospcExtractedNet := brokenExtractedNetBadReset

-- Tooth 7 (`obend-hw-dpi` codec): Skipping trailing-byte check in `decodeOspcDpiReq` breaks `decodeOspcDpiReq_refuses_trailing_byte`:
def brokenDecodeAllowTrailing (b : ByteArray) : Except OspcDpiError OspcDpiReq := do
  let (req, _tail) ← decodeOspcDpiReqPrefix b.data.toList
  .ok req

#tooth Obend.Hardware.OspcSignalFabric.decodeOspcDpiReq_refuses_trailing_byte by mutation
  Obend.Hardware.OspcSignalFabric.decodeOspcDpiReq := brokenDecodeAllowTrailing

-- Tooth 8 (`obend-hw-dpi` domain boundary): Dropping the `.hostDpi` domain check in `stepOspcDpiServer` breaks `stepOspcDpiServer_refuses_domain_mismatch`:
def brokenStepDpiSkipDomain
    (tileMod : Fin 4 → RtlMemModule) (computeRec : (Fin 4 → MemState) → BitVec 256)
    (st : OspcDpiServerState) (rawReq : ByteArray) :
    Except OspcDpiError (OspcDpiServerState × ByteArray) := do
  let req ← decodeOspcDpiReq rawReq
  if req.seqNo != st.expectedSeq then .error .sequenceMismatch
  else
    let tiles' : Fin 4 → MemState :=
      fun t => stepMemModule (tileMod t) req.rst (req.inputsFor t) (st.tiles t)
    if (tiles' ⟨2, by omega⟩).regs 1 != 1#64 then .error .deltaNetLinearityViolation
    else
      let cyc' := st.cycleCount + 1#32
      let rec256 := computeRec tiles'
      let resp := buildOspcDpiResp tileMod req cyc' st.tiles tiles' rec256
      .ok ({ tiles := tiles', expectedSeq := st.expectedSeq + 1#32, cycleCount := cyc', lastReceipt256 := rec256 },
           encodeOspcDpiResp resp)

#tooth Obend.Hardware.OspcSignalFabric.stepOspcDpiServer_refuses_domain_mismatch by mutation
  Obend.Hardware.OspcSignalFabric.stepOspcDpiServer := brokenStepDpiSkipDomain

-- Tooth 9 (`obend-hw-dpi` linearity guard): Skipping Tile 2 linearity check in `stepOspcDpiServer` breaks `stepOspcDpiServer_refines_spec`:
def brokenStepDpiSkipLinearity
    (tileMod : Fin 4 → RtlMemModule) (computeRec : (Fin 4 → MemState) → BitVec 256)
    (st : OspcDpiServerState) (rawReq : ByteArray) :
    Except OspcDpiError (OspcDpiServerState × ByteArray) := do
  let req ← decodeOspcDpiReq rawReq
  if req.domain != .hostDpi then .error .domainViolation
  else if req.seqNo != st.expectedSeq then .error .sequenceMismatch
  else
    let tiles' : Fin 4 → MemState :=
      fun t => stepMemModule (tileMod t) req.rst (req.inputsFor t) (st.tiles t)
    let cyc' := st.cycleCount + 1#32
    let rec256 := computeRec tiles'
    let resp := buildOspcDpiResp tileMod req cyc' st.tiles tiles' rec256
    .ok ({ tiles := tiles', expectedSeq := st.expectedSeq + 1#32, cycleCount := cyc', lastReceipt256 := rec256 },
         encodeOspcDpiResp resp)

#tooth Obend.Hardware.OspcSignalFabric.stepOspcDpiServer_refines_spec by mutation
  Obend.Hardware.OspcSignalFabric.stepOspcDpiServer := brokenStepDpiSkipLinearity

-- Tooth 10 (Apex theorem): Replacing `ospcTileDatapathRtl` with an empty module breaks `ospc_4tile_fabulous_ecp5_refines_spec`:
def brokenEmptyTileDatapath (_t : Fin 4) : RtlModule :=
  { name := "broken_empty", inputNames := [], inputWidths := [], wires := [], regs := [], outputs := [] }

#tooth Obend.Hardware.OspcProver.ospc_4tile_fabulous_ecp5_refines_spec by mutation
  Obend.Hardware.OspcProver.ospcTileDatapathRtl := brokenEmptyTileDatapath

/-! ## 3. Imported-Tree Axiom Purity Audit (`0 sorryAx`, `0` Custom Axioms, `0` Native) -/

#assert_axioms_tree

end Obend.Tests.Hardware.Ospc4TileFabulousDpiTest
