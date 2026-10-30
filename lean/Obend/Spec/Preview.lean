module
/-
# Obend.Spec.Preview — the typed clear preview: check, then run, the SAME decoded core term

The checker and executor consume the SAME actual decoded core term. No generated Lean source
interpreter, output oracle, current native authority or effect receipt is introduced. An activity
runs to its first yield; the preview prints the typed Plan, resumes with each supplied response
(checked against the entry's declared response type) and runs to the next yield. Responses stand in
for the kernel: nothing is admitted.

`preview` is the typed preview on a packet (`dregg.objective-bend.typed-preview.v2`);
`previewCommand` the capture-bound request `dregg.objective-bend.preview-input.v2` →
`preview-result.v2` (capture → elaborate → check → run, NEW_DIR/preview.json); `batchJob` the
in-memory jobs the tests use. Ported from minidregg `Host/ObjectiveBendPreview.lean` and the
preview/batch half of `Host/ObjectiveBendFrontEnd.lean` (commit 092027a2). The one visible
difference from Mini: a machine `diagnostic` is `reprStr` of the outcome, so it names
`Obend.Core.Machine.Suspension.ticks` where Mini named `Minidregg.Theory.ObjectiveBendDemandMachine.Suspension.ticks`.
-/
public import Lean
public import Obend.Core.Check
public import Obend.Core.Packet
public import Obend.Core.Machine
public import Obend.Core.MachineFast
public import Obend.Core.Data
public import Obend.Core.Checkpoint
public import Obend.Spec.DataWire
public import Obend.Spec.Capture
@[expose] public section
namespace Obend.Spec.Preview
open Lean (Json toJson)
open Obend.Core.Check
open Obend.Core.Packet (decodePacket refusalReason typeJson jsonNat)
open Obend.Core.Machine
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data Failure)
open Obend.Spec.DataWire
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
set_option autoImplicit false

def natural (json : Json) (key : String) : Except String Nat := do
  let value ← jsonNat (← json.getObjVal? key)
  if value = 0 || value > 100000 then throw ("preview capacity refused: " ++ key)
  pure value

/-- The weak-head view of a result: a record shows its field NAMES, a sum only its label,
a closure nothing. `resultData` (below) is the deep view. -/
def valueJson : RuntimeValue → Json
  | .boolean value => Json.mkObj [("tag",toJson "boolean"),("value",toJson value)]
  | .natural value => Json.mkObj [("tag",toJson "natural"),("value",toJson (toString value))]
  | .label value => Json.mkObj [("tag",toJson "label"),("value",toJson value)]
  | .closure _ _ => Json.mkObj [("tag",toJson "closure"),("status",toJson "unforced body")]
  | .record fields => Json.mkObj [("tag",toJson "record"),("fields",toJson (fields.map Prod.fst))]
  | .specification _ _ => Json.mkObj [("tag",toJson "specification"),("status",toJson "unforced extension")]
  | .prototype _ _ => Json.mkObj [("tag",toJson "prototype"),("status",toJson "unforced target")]
  | .variant label _ => Json.mkObj [("tag",toJson "variant"),("label",toJson label),("status",toJson "unforced payload")]

def failureName : Failure → String
  | .tickExhausted => "tickExhausted"
  | .budget => "budget" | .duplicateField => "duplicateField" | .executableValue => "executableValue"
  | .suspended => "suspended" | .divergent => "divergent" | .refused => "refused" | .yielded => "yielded"

/-- The deep view of a finished result: the machine's own budgeted materialization
(`Obend.Core.Data.complete`, the path native extraction uses) forces every field
and payload of the finished value in turn, with a fresh allowance of `ticks` machine
steps, at most `heap` nodes and 1 MiB of canonical encoding. Typed data wire: the same as
a yielded Plan. A result that is not first-order data (a closure, a specification, a
prototype anywhere inside), or that exhausts the allowance, has no deep view: `null` and
the failure's name, never a partial value. -/
def resultData (limits : Limits) (budget : Obend.Core.Data.Budget)
    (outcome : Outcome) : Json × Json :=
  match outcome with
  | .finished _ state =>
    match Obend.Core.Data.complete limits budget state with
    | .ok result => (dataJson result.value, toJson "materialized")
    | .error (failure,_) => (Json.null, toJson (failureName failure))
  | _ => (Json.null, toJson "not finished")

/-- Run one turn: to a finish, a yield, or a refusal/suspension/divergence. -/
def runTurn (limits : Limits) (ticks : Nat) (state : State) : Outcome := runBounded limits ticks state

/-- Turns: run, and at each yield extract the Plan, then resume with the next
supplied response if it conforms to the declared response type. -/
def runTurns (limits : Limits) (ticks : Nat) (budget : Obend.Core.Data.Budget)
    (response? : Option Ty) : List Data → State → Array Json → Except String (Outcome × Array Json)
  | responses, state, turns =>
    match runTurn limits ticks state with
    | .yielded plan yielded => do
      let extracted ← match Obend.Core.Data.yieldedPlan limits budget yielded with
        | .ok result => pure result
        | .error (failure,_) => throw ("yielded plan not extractable as data: " ++ reprStr failure)
      let checkpoint := Obend.Core.Checkpoint.encodeState extracted.state
      let turn : List (String × Json) := [("plan",dataJson extracted.value),("planAddress",toJson (toString plan)),
        ("checkpointTokens",toJson (toString checkpoint.length)),
        ("checkpointRoundTrips",toJson (Obend.Core.Checkpoint.roundTrips extracted.state)),
        ("quiescent",toJson (extracted.state.heap.toList.all fun cell => match cell with
          | .evaluating _ => false | _ => true))]
      match responses with
      | [] => pure (.yielded plan extracted.state, turns.push (Json.mkObj turn))
      | response :: rest => do
        let some declared := response? | throw "a yield needs an Activity entry type"
        if !response.conforms declared then
          throw ("response refused: it does not conform to the declared response type " ++ (typeJson declared).compress)
        let some resumed := resume response.term extracted.state | throw "internal: yielded state did not resume"
        runTurns limits ticks budget response? rest resumed
          (turns.push (Json.mkObj (turn ++ [("response",dataJson response)])))
    | other => pure (other, turns)
termination_by responses => responses.length

/-- Receives an actual annotated packet; typing and bounded demand use exactly
packet.source.term. A Boolean assertion supplied by the caller cannot replace
its Checked proof-producing result. -/
def preview (typed limits : Json) (responsesJson : Json := Json.arr #[]) : Except String Json := do
  let packet ← decodePacket typed
  if !packet.context.isEmpty then throw "preview requires a closed source context"
  let heap ← natural limits "heap"
  let stack ← natural limits "stack"
  let ticks ← natural limits "ticks"
  let responses ← (← responsesJson.getArr?).toList.mapM (decodeData 64)
  if responses.length > 64 then throw "preview response capacity refused"
  let some checked := check packet.source packet.context packet.fuel
    | throw (refusalReason packet)
  let response? : Option Ty := match checked.type with
    | .computation _ response _ => some response
    | _ => none
  let (outcome,turns) ← runTurns ⟨heap,stack⟩ ticks ⟨heap,ticks,1048576⟩ response? responses
    (initial packet.source.term) #[]
  let (data,dataStatus) := resultData ⟨heap,stack⟩ ⟨heap,ticks,1048576⟩ outcome
  let state := match outcome with
    | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state | .yielded _ state => state
  let (status,value,diagnostic) := match outcome with
    | .finished value _ => ("finished",valueJson value,Json.null)
    | .suspended reason _ => ("suspended",Json.null,toJson (reprStr reason))
    | .divergent _ _ => ("divergent",Json.null,toJson "blackhole; no catchable source exception")
    | .refused reason _ => ("refused",Json.null,toJson (reprStr reason))
    | .yielded _ _ => ("yielded",Json.null,toJson "waiting for a response")
  pure <| Json.mkObj [("schema",toJson "dregg.objective-bend.typed-preview.v2"),
    ("edition",toJson "objective-bend-1"),("status",toJson status),
    ("type",typeJson checked.type),("uses",toJson checked.uses),
    ("typing",toJson "accepted by actual annotated checker"),
    ("sameDecodedTerm",toJson true),("result",value),("resultData",data),("resultDataStatus",dataStatus),
    ("diagnostic",diagnostic),
    ("turns",Json.arr turns),
    ("heap",toJson (toString state.heap.size)),("stack",toJson (toString state.stack.length)),
    ("limits",limits),("laws",toJson "undischarged unless independent law providers are supplied"),
    ("authority",toJson "none; clear source preview; responses are supplied, not admitted"),
    ("proofScope",toJson "actual compiled checker/executor join; preservation and elaboration adequacy separate")]

/-! ## Commands: preview, batch, identity -/

/-- `^[1-9][0-9]*$` at most `cap`, kept as its decimal text. -/
def count (limits : Json) (key : String) (cap : Nat) : FE String := do
  let some v := text limits key | refuse ("Error: invalid preview capacity: " ++ key) "preview-request"
  match positive (toJson v) cap with
  | some _ => pure v
  | none => refuse ("Error: invalid preview capacity: " ++ key) "preview-request"

/-- The preview: a capture-bound request, elaborated by this front end, checked by the actual
checker and run by the bounded demand machine on the same decoded term. -/
def previewCommand (requestPath dirPath : String) : IO UInt32 := do
  let dir := System.FilePath.mk dirPath
  let bindingRef ← IO.mkRef (Json.mkObj [])
  let bind (k : String) (v : Json) : IO Unit := bindingRef.modify fun b => b.setObjVal! k v
  let run : FE Json := do
    let (requestBytes, request) ← readJson requestPath
    bind "previewRequestSha256" (toJson (sha requestBytes))
    if text request "schema" != some "dregg.objective-bend.preview-input.v2" ||
        (text request "capturePath").isNone || (text request "captureSha256").isNone then
      refuse "Error: preview input schema/capture pin required" "preview-request"
    let captureBytes ← readBytes ((text request "capturePath").getD "")
    if some (sha captureBytes) != text request "captureSha256" then
      refuse "Error: captured package identity differs" "preview-request"
    let loaded ← loadCapture ((text request "capturePath").getD "")
    bind "captureSha256" (toJson (sha captureBytes))
    bind "sourceRequestSha256" ((loaded.json.getObjVal? "requestSha256").toOption.getD .null)
    bind "edition" (toJson "objective-bend-1")
    bind "frontEnd" (toJson identity)
    bind "sourceEntry" ((loaded.json.getObjVal? "sourceEntry").toOption.getD .null)
    bind "modules" (Json.arr (loaded.modules.map SourceModule.binding).toArray)
    let some arguments := (request.getObjVal? "arguments").toOption.bind (fun a => (a.getArr?).toOption)
      | refuse "Error: arguments/projections arrays required" "preview-request"
    let some projections := (request.getObjVal? "projections").toOption.bind (fun a => (a.getArr?).toOption)
      | refuse "Error: arguments/projections arrays required" "preview-request"
    let encoding := (text request "argumentEncoding").getD "legacy-values-v1"
    if encoding != "legacy-values-v1" && encoding != "typed-values-v1" then
      refuse "Error: unknown preview argument encoding" "preview-request"
    let wire := if encoding == "typed-values-v1" then
        Json.mkObj [("schema", toJson "dregg.objective-bend.argument-values.v1"), ("values", Json.arr arguments)]
      else Json.arr arguments
    bind "argumentEncoding" (toJson encoding)
    let limitsIn := (request.getObjVal? "limits").toOption.getD (Json.mkObj [])
    let ticks ← count limitsIn "ticks" 100000
    let heap ← count limitsIn "heap" 100000
    let stack ← count limitsIn "stack" 100000
    let typeFuel ← count limitsIn "typeFuel" 16384
    let responses := (request.getObjVal? "responses").toOption.getD (Json.arr #[])
    match responses.getArr? with
    | .ok a => if a.size > 64 then refuse "Error: preview responses must be an array of at most 64 typed data values" "preview-request"
    | .error _ => refuse "Error: preview responses must be an array of at most 64 typed data values" "preview-request"
    let limits := Json.mkObj [("ticks", toJson ticks), ("heap", toJson heap), ("stack", toJson stack)]
    bind "limits" (Json.mkObj [("ticks", toJson ticks), ("heap", toJson heap), ("stack", toJson stack),
      ("typeFuel", toJson typeFuel)])
    IO.FS.createDirAll dir
    if !(← dir.readDir).isEmpty then refuse "Error: preview output directory must be empty" "preview-request"
    writeNew (dir / "capture.json") (String.fromUTF8! captureBytes)
    let lowered ← liftFE (lower loaded.modules loaded.entryModule loaded.entryDefinition wire (Json.arr projections)
      (Json.mkObj [("ticks", toJson ticks), ("heap", toJson heap), ("stack", toJson stack), ("typeFuel", toJson typeFuel)])
      "application")
    let coreText := pretty lowered.core
    let packetText := pretty lowered.packet
    writeNew (dir / "source.core.json") coreText
    writeNew (dir / "source.typed.json") packetText
    bind "coreSha256" (toJson (Sha256.hexString coreText))
    bind "sourceEntry" (toJson lowered.sourceEntry)
    if let .error message := lowered.proposal then refuse message "objective-source-type-proposal"
    writeNew (dir / "limits.json") (pretty limits)
    let responsesText := pretty responses
    writeNew (dir / "responses.json") responsesText
    bind "typedPacketSha256" (toJson (Sha256.hexString packetText))
    bind "responsesSha256" (toJson (Sha256.hexString responsesText))
    let result ← match preview lowered.packet limits responses with
      | .ok r => pure r
      | .error message => refuse message "objective-typed-preview"
    let output := Json.mkObj [("schema", toJson "dregg.objective-bend.preview-result.v2"),
      ("status", (result.getObjVal? "status").toOption.getD .null), ("binding", ← bindingRef.get),
      ("preview", result), ("authority", toJson "none; source preview only")]
    writeNew (dir / "preview.json") (pretty output)
    return output
  match ← run.run with
  | .ok output => IO.println output.compress; return 0
  | .error d =>
    let refused := Json.mkObj [("schema", toJson "dregg.objective-bend.preview-result.v2"), ("status", toJson "refused"),
      ("binding", ← bindingRef.get), ("diagnostic", d.json), ("authority", toJson "none; source preview only")]
    try
      IO.FS.createDirAll dir
      unless ← (dir / "diagnostic.json").pathExists do IO.FS.writeFile (dir / "diagnostic.json") (pretty refused)
    catch _ => pure ()
    IO.println refused.compress
    return 2

/-! ## Batch (tests): many in-memory jobs, one process -/

/-- A job: `{name, modules:[{name, source, imports:[{alias, module}]}], entryModule,
entryDefinition, arguments, projections?, limits?, mode?}`, or `{name, parse: SOURCE}`. -/
def batchJob (job : Json) : IO Json := do
  let name := (text job "name").getD ""
  if let some source := text job "parse" then
    return match Parse.parseObjective source with
      | .ok ast => Json.mkObj [("name", toJson name), ("ok", toJson true), ("ast", ast)]
      | .error d => Json.mkObj [("name", toJson name), ("ok", toJson false), ("diagnostic", d.json)]
  let run : FE Json := do
    let rows := ((job.getObjVal? "modules").bind Json.getArr?).toOption.getD #[]
    let mut modules : Array SourceModule := #[]
    for row in rows do
      let locks := (((row.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]).toList.map fun l =>
        ({ importAlias := text l "alias", path := none, target := (l.getObjVal? "module").toOption.getD .null,
           sha256 := none } : Lock)
      let (m, _) ← captureModule modules ((text row "name").getD "") ((text row "source").getD "").toUTF8 none locks true
      modules := modules.push m
    let entry := match job.getObjVal? "entryModule" with
      | .ok (.str s) => s.toNat!
      | .ok j => (j.getNat?).toOption.getD (modules.size - 1)
      | .error _ => modules.size - 1
    let lowered ← liftFE (lower modules.toList entry ((text job "entryDefinition").getD "")
      ((job.getObjVal? "arguments").toOption.getD (Json.arr #[])) ((job.getObjVal? "projections").toOption.getD (Json.arr #[]))
      ((job.getObjVal? "limits").toOption.getD (Json.mkObj [("heap", toJson "100000"), ("stack", toJson "100000"),
        ("ticks", toJson "100000")]))
      ((text job "mode").getD "application"))
    let checked : Json := match accept lowered with
      | .ok a => Json.mkObj [("accepted", toJson true), ("type", reprStr a.typed.type |> toJson)]
      | .error d => Json.mkObj [("accepted", toJson false), ("diagnostic", d.json)]
    return Json.mkObj [("core", lowered.core), ("packet", lowered.packet), ("check", checked)]
  match ← run.run with
  | .ok out => return Json.mkObj [("name", toJson name), ("ok", toJson true), ("output", out)]
  | .error d => return Json.mkObj [("name", toJson name), ("ok", toJson false), ("diagnostic", d.json)]

def batchCommand (jobsPath outPath : String) : IO UInt32 := do
  let jobs ← match ← (readJson jobsPath).run with
    | .ok (_, j) => pure ((j.getArr?).toOption.getD #[])
    | .error d => return ← report none d
  let results ← jobs.mapM batchJob
  IO.FS.writeFile outPath ((Json.arr results).compress ++ "\n")
  return 0

def identityJson : Json :=
  Json.mkObj [("schema", toJson "dregg.objective-bend.front-end-identity.v1"), ("frontEnd", toJson identity),
    ("manifest", toJson Identity.manifest)]

end Obend.Spec.Preview

end
