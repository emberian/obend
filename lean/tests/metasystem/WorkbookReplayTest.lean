import Obend.FFI.Bridge
import Obend.Tactic.Tooth

open Obend.FFI Obend.Vault Obend.Doc.WorkbookEngine

private def initReq := r#"{"op":"init","title":"Flight","sections":[{"sectionKey":"Notes","markdown":"old"}],"cells":[{"id":1,"cellKey":"mesh","kind":"feecSimplicialFem","fields":{"polynomialOrder":2},"literalValue":2}]}"#.toUTF8
private def editReq := r#"{"op":"editCell","targetId":1,"literalValue":3}"#.toUTF8
private def secReq := r#"{"op":"editSection","sectionKey":"Notes","markdown":"new"}"#.toUTF8
private def scrubReq := r#"{"cellKey":"mesh","fieldName":"polynomialOrder","newValue":5}"#.toUTF8
private def cmds : List (WorkbookCommand × ByteArray) := [(.step, initReq), (.step, editReq), (.step, secReq), (.scrub, scrubReq)]

private def expected : IO Workbook := cmds.foldlM (fun wb (cmd, req) => do
  match cmd.apply wb req with
  | .ok (next, _) => return next
  | .error (_, msg) => throw (IO.userError msg)) defaultSessionWorkbook

private def checkState (world : Replay.World) : IO Unit := do
  let wb := workbookFromWorld world
  unless wb == (← expected) && world.store.pages.isEmpty && wb.sections.map (·.markdown) == ["new"] &&
      wb.cells.map (·.result.values) == [[5]] do
    throw (IO.userError "wrong reconstructed workbook or unexpected store page mutation")

def main (args : List String) : IO Unit := do
  let [mode, path] := args | throw (IO.userError "expected write|read and log path")
  if mode == "write" then
    let mut s := SessionState.empty
    for (cmd, req) in cmds do
      let (next, out, code) := match cmd with
        | .step => workbookStepJsonCore s req
        | .scrub => workbookScrubCellJsonCore s req
      unless code == 0 && !out.isEmpty && next.replaySession.log.length == s.replaySession.log.length + 1 do
        throw (IO.userError s!"workbook commit failed: {next.lastError}")
      s := next
    checkState s.world
    let bad := workbookScrubCellJsonCore s r#"{"cellKey":"mesh","fieldName":"nonexistent","newValue":7}"#.toUTF8
    let view := workbookStepJsonCore s r#"{"op":"exportRedacted","clearances":[]}"#.toUTF8
    unless bad.2.2 != 0 && view.2.2 == 0 && view.1.replaySession.log.length == 4 &&
        bad.1.replaySession.log.length == 4 && s.committedRoots.isEmpty do
      throw (IO.userError "refusal, export or receipt-root contract failed")
    let bytes := Log.encodeAllExec Replay.logHash s.replaySession.log
    IO.FS.writeBinFile path bytes
    IO.println s!"WORKBOOK records={s.replaySession.log.length} payload_bytes={s.replaySession.log.map (·.payload.length)} disk_bytes={bytes.size}"
  else if mode == "read" then
    let bytes ← IO.FS.readBinFile path
    let r := Log.recover Replay.logHash Replay.deployed Replay.genesis bytes.data.toList
    unless r.count == 4 && r.tail.isEmpty && r.why.isNone do
      throw (IO.userError "incomplete record stream")
    checkState r.world
    IO.println "WORKBOOK fresh-process recovery matched all fields, pins and receipts"
  else throw (IO.userError "unknown mode")

#print axioms runWorkbook_replays_edit
#print axioms commitWorkbook_replays_edit
#print axioms workbookStepJsonCore_preserves_reachable
#print axioms workbookScrubCellJsonCore_preserves_reachable
#tooth commitWorkbook_replays_edit by
  mutation commitWorkbook := fun s _ _ _ out => (s, out, 0)
