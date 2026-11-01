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

/-- CLI entry point for `obend hardware ...` and `obend fabublox ...`. -/
public def main? : List String → Option (IO UInt32)
  | "hardware" :: "verify-pnr" :: rest        => some (cmdVerifyPnr rest)
  | "hardware" :: "verify-retime" :: rest     => some (cmdVerifyRetime rest)
  | "hardware" :: "waferspace-signoff" :: rest => some (cmdWaferSpaceSignoff rest)
  | "fabublox" :: "check" :: rest             => some (cmdFabuBloxCheck rest)
  | _ => none

end Obend.Hardware.Cli
