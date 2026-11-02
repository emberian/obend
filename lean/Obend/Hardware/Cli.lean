module
/-
# Obend.Hardware.Cli — `obend hardware`, `obend fabublox`, and `obend verify` Hardware Receipt Support

Provides CLI commands for hardware synthesis, Leiserson–Saxe retiming, physical Place-and-Route
(PnR) + FABulous bitstream verification, FabuBlox cleanroom recipe verification, and `wafer.space`
(`GF180MCU` / `Sky130` / `IHP SG13G2`) MPW shuttle signoff:

    obend hardware verify-pnr [--mode valid|collision|short] [--out RECEIPT.json]
        check a physical Place-and-Route + bitstream certificate by `hw-pnr-bitstream@1`;
        writes a receipt re-checkable by `obend verify RECEIPT.json`.
    obend hardware verify-retime [--lag1 N] [--out RECEIPT.json]
        check a Leiserson–Saxe integer lag certificate by `hw-retime-sta@1`.
    obend hardware waferspace-signoff [--mode golden|bad_antenna|bad_cmp] [--out RECEIPT.json]
        check a `wafer.space` GF180MCU MPW shuttle signoff certificate by `waferspace-signoff@1`.
    obend fabublox check [--recipe damascene|post_cu_anneal|under_etch] [--out RECEIPT.json]
        check a FabuBlox cleanroom nanofabrication recipe by `fabublox-run@1`.
    obend verify RECEIPT.json
        re-checks any `"kind": "hardware"` receipt through its registered `Obend.Hardware.Judge` format.
-/
public import Lean.Data.Json
public import Obend.Hardware.Judge
public import Obend.Hardware.UserspacePhysical
@[expose] public section

namespace Obend.Hardware.Cli
open Lean (Json toJson)
open Obend.Judge
open Obend.Hardware.Judge

/-- Construct a JSON hardware receipt for `formatName` (`e.g. "hw-pnr-bitstream@1"`). -/
def mkHwReceiptJson (formatName : String) (objJson certJson : Json) : Json :=
  Json.mkObj
    [ ("kind",        toJson "hardware")
    , ("format",      toJson formatName)
    , ("object",      objJson)
    , ("certificate", certJson) ]

/-- Verify a decoded `"kind": "hardware"` JSON receipt using the registered `Obend.Hardware.Judge` format. -/
def verifyHardware (j : Json) : IO UInt32 := do
  let fmtTag := (j.getObjValAs? String "format").toOption.getD ""
  let objStr := ((j.getObjVal? "object").toOption.getD Json.null).compress
  let certStr := ((j.getObjVal? "certificate").toOption.getD Json.null).compress
  match findHardwareFormat? fmtTag with
  | none =>
    IO.eprintln s!"refused: unknown hardware format {fmtTag}"
    return 3
  | some fmt =>
    match fmt.checkBytes 0 objStr certStr with
    | .ok =>
      IO.println s!"verified ({fmtTag}, decidable, kernel)"
      return 0
    | .refused (.malformed m) _ =>
      IO.eprintln s!"refused: malformed {m}"
      return 3
    | .refused (.judge _) _ =>
      IO.eprintln s!"refused: certificate rejected by {fmtTag}"
      return 3
    | .uncovered =>
      IO.eprintln "uncovered"
      return 3

/-- Intercept `obend verify PATH` when `PATH` is a `"kind": "hardware"` receipt; otherwise delegate. -/
def verifyOr (path : String) (otherwise : IO UInt32) : IO UInt32 := do
  let j? := Json.parse (← IO.FS.readFile path)
  match j? with
  | .ok j =>
    if (j.getObjValAs? String "kind").toOption == some "hardware" then
      verifyHardware j
    else
      otherwise
  | .error _ => otherwise

/-- Extract `--flag VALUE` from a CLI argument list. -/
def extractFlag (flagName : String) : List String → Option String × List String
  | [] => (none, [])
  | f :: v :: rest =>
    if f == flagName then
      (some v, rest)
    else
      let (found, rem) := extractFlag flagName (v :: rest)
      (found, f :: rem)
  | [single] => (none, [single])

/-- Run `hw-pnr-bitstream@1` CLI check and optionally emit a receipt. -/
def cmdVerifyPnr (args : List String) : IO UInt32 := do
  let (modeOpt, args1) := extractFlag "--mode" args
  let (outOpt, _)      := extractFlag "--out" args1
  let mode := modeOpt.getD "valid"
  let objJson  := Json.mkObj [("periodPs", toJson (2000 : Nat))]
  let certJson := Json.mkObj [("mode", toJson mode)]
  let recJson  := mkHwReceiptJson "hw-pnr-bitstream@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `hw-retime-sta@1` CLI check and optionally emit a receipt. -/
def cmdVerifyRetime (args : List String) : IO UInt32 := do
  let (lagOpt, args1) := extractFlag "--lag1" args
  let (outOpt, _)     := extractFlag "--out" args1
  let lag1 : Int := match lagOpt.bind String.toInt? with
    | some k => k
    | none   => 1
  let objJson  := Json.mkObj [("periodPs", toJson (2000 : Nat))]
  let certJson := Json.mkObj [("lag1", toJson lag1), ("ioLatencyShift", toJson (0 : Int))]
  let recJson  := mkHwReceiptJson "hw-retime-sta@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `waferspace-signoff@1` CLI check and optionally emit a receipt. -/
def cmdWaferSpaceSignoff (args : List String) : IO UInt32 := do
  let (modeOpt, args1) := extractFlag "--mode" args
  let (outOpt, _)      := extractFlag "--out" args1
  let mode := modeOpt.getD "golden"
  let objJson  := Json.mkObj [("pdk", toJson "gf180mcuD")]
  let certJson := Json.mkObj [("mode", toJson mode)]
  let recJson  := mkHwReceiptJson "waferspace-signoff@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `fabublox-run@1` CLI check and optionally emit a receipt. -/
def cmdFabuBloxCheck (args : List String) : IO UInt32 := do
  let (recipeOpt, args1) := extractFlag "--recipe" args
  let (outOpt, _)        := extractFlag "--out" args1
  let recipe := recipeOpt.getD "damascene"
  let objJson  := Json.mkObj [("maxThermalBudgetCMin", toJson (50000 : Nat))]
  let certJson := Json.mkObj [("recipe", toJson recipe)]
  let recJson  := mkHwReceiptJson "fabublox-run@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `datasheet-fit@1` CLI check and optionally emit a receipt. -/
def cmdDatasheetCheck (args : List String) : IO UInt32 := do
  let (modeOpt, args1) := extractFlag "--mode" args
  let (outOpt, _)      := extractFlag "--out" args1
  let mode := modeOpt.getD "calibrated"
  let objJson  := Json.mkObj [("suite", toJson "obend_74ls_hct_ina_calibrated")]
  let certJson := Json.mkObj [("mode", toJson mode)]
  let recJson  := mkHwReceiptJson "datasheet-fit@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `rf-transceiver-signoff@1` CLI check and optionally emit a receipt. -/
def cmdRfSignoff (args : List String) : IO UInt32 := do
  let (modeOpt, args1) := extractFlag "--mode" args
  let (outOpt, _)      := extractFlag "--out" args1
  let mode := modeOpt.getD "ft8_40m_golden"
  let objJson  := Json.mkObj [("band", toJson "40m")]
  let certJson := Json.mkObj [("mode", toJson mode)]
  let recJson  := mkHwReceiptJson "rf-transceiver-signoff@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `photonics-pic-signoff@1` CLI check and optionally emit a receipt. -/
def cmdPhotonicsSignoff (args : List String) : IO UInt32 := do
  let (modeOpt, args1) := extractFlag "--mode" args
  let (outOpt, _)      := extractFlag "--out" args1
  let mode := modeOpt.getD "golden"
  let objJson  := Json.mkObj [("minFsrPm", toJson (15000 : Nat))]
  let certJson := Json.mkObj [("mode", toJson mode)]
  let recJson  := mkHwReceiptJson "photonics-pic-signoff@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `pcb-board-signoff@1` CLI check and optionally emit a receipt. -/
def cmdPcbSignoff (args : List String) : IO UInt32 := do
  let (modeOpt, args1) := extractFlag "--mode" args
  let (outOpt, _)      := extractFlag "--out" args1
  let mode := modeOpt.getD "golden"
  let objJson  := Json.mkObj [("maxSkewFs", toJson (50 : Nat))]
  let certJson := Json.mkObj [("mode", toJson mode)]
  let recJson  := mkHwReceiptJson "pcb-board-signoff@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `agentic-eda-swap@1` CLI check and optionally emit a receipt. -/
def cmdEdaVaultCheck (args : List String) : IO UInt32 := do
  let (modeOpt, args1) := extractFlag "--mode" args
  let (outOpt, _)      := extractFlag "--out" args1
  let mode := modeOpt.getD "golden"
  let objJson  := Json.mkObj [("minMarginMv", toJson (400 : Int))]
  let certJson := Json.mkObj [("mode", toJson mode)]
  let recJson  := mkHwReceiptJson "agentic-eda-swap@1" objJson certJson
  if let some outPath := outOpt then
    IO.FS.writeFile outPath (recJson.pretty ++ "\n")
    IO.println s!"wrote {outPath}"
  verifyHardware recJson

/-- Run `hw-binary-cbor@1` / `hw-binary-tape-cbor@1` binary CBOR certificate encode/decode/verify and `.obnb` projection (NO JSON). -/
def cmdVerifyCbor (args : List String) : IO UInt32 := do
  let (domOpt, args1)  := extractFlag "--domain" args
  let (modeOpt, args2) := extractFlag "--mode" args1
  let (binInOpt, args3) := extractFlag "--in-bin" args2
  let (binOutOpt, args4) := extractFlag "--out-bin" args3
  let (obnbOutOpt, _)  := extractFlag "--out-obnb" args4
  let domName := domOpt.getD "pnr"
  let mode := modeOpt.getD "golden"
  let expectedDom : Obend.Hardware.Codec.HwCertDomain :=
    if domName == "photonics" then .photonics
    else if domName == "dpr" then .dpr
    else if domName == "eda" then .edaBomSwap
    else if domName == "magnetics" || domName == "femm" then .magnetics
    else if domName == "fluid" || domName == "cooling" then .fluidThermal
    else if domName == "power" || domName == "ms350" then .powerElectronics
    else if domName == "mechanics" || domName == "von_neumann" then .mechanicsVonNeumann
    else .pnr
  let baseCert : Obend.Hardware.Codec.BinaryHwCert :=
    match expectedDom with
    | .photonics => Obend.Hardware.Codec.goldenBinaryPhotonicsCert
    | .dpr => Obend.Hardware.Codec.goldenBinaryDprCert
    | .edaBomSwap => Obend.Hardware.Codec.goldenBinaryEdaSwapCert
    | .magnetics => Obend.Hardware.Codec.goldenBinaryMagneticsCert
    | .fluidThermal => Obend.Hardware.Codec.goldenBinaryFluidThermalCert
    | .powerElectronics => Obend.Hardware.Codec.goldenBinaryPowerElectronicsCert
    | .mechanicsVonNeumann => Obend.Hardware.Codec.goldenBinaryMechanicsCert
    | _ =>
      if mode == "corrupt" then badBinaryPnrCert
      else Obend.Hardware.Codec.goldenBinaryPnrCert
  let defaultBytes : ByteArray :=
    if mode == "tape" then
      let tapeCert := match expectedDom with
        | .mechanicsVonNeumann => Obend.Hardware.Codec.goldenBinaryOctreeTapeCert
        | .fluidThermal => Obend.Hardware.Codec.goldenBinaryEvolutionTapeCert
        | _ => Obend.Hardware.Codec.goldenBinaryFemmTapeCert
      Obend.Hardware.Codec.encodeToByteArray tapeCert
    else
      Obend.Hardware.Codec.encodeToByteArray baseCert
  let rawBytes : ByteArray ← match binInOpt with
    | some inPath => IO.FS.readBinFile inPath
    | none => pure defaultBytes
  if let some outBinPath := binOutOpt then
    IO.FS.writeBinFile outBinPath rawBytes
    IO.println s!"wrote binary CBOR ({rawBytes.size} bytes) to {outBinPath}"
  if let some obnbPath := obnbOutOpt then
    let obnbBytes := Obend.Hardware.Codec.obendHwCborProjectCell rawBytes
    IO.FS.writeBinFile obnbPath obnbBytes
    IO.println s!"wrote binary .obnb Core.Data cell ({obnbBytes.size} bytes) to {obnbPath}"
  match verifyRawBinaryCborCert expectedDom rawBytes with
  | .ok =>
    IO.println s!"verified (hw-binary-cbor@1, domain={domName}, bytes={rawBytes.size}, decidable, kernel)"
    return 0
  | .refused _ _ =>
    IO.eprintln s!"refused: binary CBOR certificate rejected by hw-binary-cbor@1 (domain={domName})"
    return 3
  | .uncovered =>
    IO.eprintln s!"uncovered: binary CBOR certificate obligations uncovered (domain={domName})"
    return 3

/-- Compile a userspace `.obend` physical engineering `Composition` via `compileBookToRtl`
    and emit synthesizable SystemVerilog-2012 via `emitModuleSV`. -/
def cmdEmitSv (args : List String) : IO UInt32 := do
  let (modOpt, args1) := extractFlag "--module" args
  let (outOpt, _)     := extractFlag "--out" args1
  let modChoice := modOpt.getD "lc_drives_stator"
  let (modName, comp) :=
    if modChoice == "cnc_5axis_mill" || modChoice == "cnc_5axis_userspace_mill" then
      ("cnc_5axis_userspace_mill", Obend.Hardware.UserspacePhysical.cnc5AxisMillComp)
    else
      ("lc_drives_userspace_stator", Obend.Hardware.UserspacePhysical.lcDrivesStatorUsdComp)
  match Obend.Hardware.Compiler.compileBookToRtl modName (Obend.Leaf.emit comp) with
  | none =>
    IO.eprintln s!"refused: failed to compile {modName} to RtlModule"
    return 3
  | some m =>
    if !Obend.Hardware.HDL.checkRtlModule m then
      IO.eprintln s!"refused: synthesized RtlModule {m.name} failed DAG/CDC check"
      return 3
    else
      let svText := "/* verilator lint_off UNUSED */\n/* verilator lint_off DECLFILENAME */\n" ++
        Obend.Hardware.HDL.emitModuleSV m
      match outOpt with
      | some outPath =>
        IO.FS.writeFile outPath svText
        IO.println s!"wrote synthesized SystemVerilog module {m.name} ({m.wires.length} wires, {m.outputs.length} outputs) to {outPath}"
        return 0
      | none =>
        IO.print svText
        return 0

/-- CLI entry point for `obend hardware ...` and `obend fabublox ...`. -/
public def main? : List String → Option (IO UInt32)
  | "hardware" :: "verify-pnr" :: rest         => some (cmdVerifyPnr rest)
  | "hardware" :: "verify-retime" :: rest      => some (cmdVerifyRetime rest)
  | "hardware" :: "waferspace-signoff" :: rest => some (cmdWaferSpaceSignoff rest)
  | "hardware" :: "datasheet-check" :: rest    => some (cmdDatasheetCheck rest)
  | "hardware" :: "rf-signoff" :: rest         => some (cmdRfSignoff rest)
  | "hardware" :: "photonics-signoff" :: rest  => some (cmdPhotonicsSignoff rest)
  | "hardware" :: "pcb-signoff" :: rest        => some (cmdPcbSignoff rest)
  | "hardware" :: "eda-vault-check" :: rest    => some (cmdEdaVaultCheck rest)
  | "hardware" :: "verify-cbor" :: rest        => some (cmdVerifyCbor rest)
  | "hardware" :: "verify-tape-cbor" :: rest   => some (cmdVerifyCbor ("--mode" :: "tape" :: rest))
  | "hardware" :: "emit-sv" :: rest            => some (cmdEmitSv rest)
  | "fabublox" :: "check" :: rest              => some (cmdFabuBloxCheck rest)
  | _ => none

end Obend.Hardware.Cli
