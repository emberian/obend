module
/-
# `obend` — the Objective Bend command (the executable is rooted here, at `Obend.Main`)

Source commands (the front end `Obend.Spec`, 2026-10-30):

    obend check FILE.obend [ENTRY]
        parse FILE as a one-module package and, for ENTRY (or every def/spec/extension), lower it in
        definition mode and run the checker on the front end's own packet (`Obend.Spec.FrontEnd.accept`):
        one JSON receipt per declaration on stdout; exit 2 if any is refused.
    obend run FILE.obend ENTRY [ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]
        the shape of minidregg's docs/tutorial/run.ts: capture FILE as a package (its module named
        from the file name), elaborate ENTRY applied to ARGS (a JSON array: Nats as decimal strings,
        Bools, records), check, run on the demand machine with RESPONSES (a JSON array; a bare label
        stands for that label with an empty payload), and print the short form (`status`, `type`,
        `turn k`, `result`, `diagnostic`) or, with `--json`, the preview's own result. Refusals print
        `status: refused`, `stage`, `message` and exit 2.
    obend check --package PACKAGE.json [ENTRY] | obend run --package PACKAGE.json [ARGS] [RESPONSES] [--ticks N] [--json]
        the same over a `dregg.objective-bend.package-input.v1` (multi-module; the entry is the package's).
    obend identity | parse FILE.obend | capture PACKAGE_SPEC NEW_DIR [--objective-edition-1]
          | elaborate CAPTURE PREFIX [ARGS] [PROJECTIONS] [LIMITS] [application|definition]
          | preview REQUEST NEW_DIR | batch JOBS OUT
        minidregg's `objective-front` commands, unchanged (`Obend.Spec.Capture`, `Obend.Spec.Preview`).

Typed-core packet commands (lane A, 2026-10-31; a packet is `dregg.objective-bend.typed-core.v3`):

    obend check-core FILE.json
        the typing receipt on stdout (exit 0), or the refusal with the kind of rule it broke on
        stderr (exit 2): `Obend.Core.Packet.checkPacketFile`.
    obend run-core FILE.json [--ticks N] [--heap N] [--stack N]
        checks the packet, refuses an open program, runs the term on the demand machine within the
        limits (defaults 100000 ticks, 65536 heap cells, 4096 frames) and prints the outcome as JSON.
        Exit 0 on finished, 3 otherwise, 2 on refusal.
-/
public import Obend.Core.Packet
public import Obend.Elab.Gate
public import Obend.Core.Machine
public import Obend.Core.MachineFast
public import Obend.Spec.Capture
public import Obend.Spec.Preview

open Lean (Json toJson)
open Obend.Core
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
open Obend.Spec.Preview

def usage : String :=
  "usage: obend check FILE.obend [ENTRY] | obend run FILE.obend ENTRY [ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]\n" ++
  "       obend check --package PACKAGE.json [ENTRY] | obend run --package PACKAGE.json [ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]\n" ++
  "       obend identity | parse FILE.obend | capture PACKAGE_SPEC NEW_DIR [--objective-edition-1]\n" ++
  "             | elaborate CAPTURE PREFIX [ARGS] [PROJECTIONS] [LIMITS] [application|definition] | preview REQUEST NEW_DIR | batch JOBS OUT\n" ++
  "       obend check-core FILE.json | obend run-core FILE.json [--ticks N] [--heap N] [--stack N]"

/-! ## The typed-core packet path (lane A) -/

structure RunOptions where
  ticks : Nat := 100000
  heap : Nat := 65536
  stack : Nat := 4096

def parseOptions : List String → RunOptions → Except String RunOptions
  | [], options => .ok options
  | flag :: value :: rest, options =>
    match value.toNat? with
    | none => .error s!"{flag} needs a number, got {value}"
    | some n =>
      match flag with
      | "--ticks" => parseOptions rest { options with ticks := n }
      | "--heap" => parseOptions rest { options with heap := n }
      | "--stack" => parseOptions rest { options with stack := n }
      | _ => .error s!"unknown option {flag}"
  | [flag], _ => .error s!"{flag} needs a value"

def packetValueJson : Machine.RuntimeValue → Json
  | .natural n => toJson n
  | .boolean b => toJson b
  | .label s => toJson s
  | other => toJson (toString (repr other))

def receipt (status : String) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("schema", toJson "dregg.objective-bend.run-receipt.v1"), ("status", toJson status)] ++ fields)

def refusePacket (stage message : String) : IO UInt32 := do
  IO.eprintln (receipt "refused" [("stage", toJson stage), ("message", toJson message)]).compress
  return 2

def runPacket (path : String) (options : RunOptions) : IO UInt32 := do
  let input ← IO.FS.readFile path
  match Json.parse input >>= Packet.decodePacket with
  | .error message => refusePacket "decode" message
  | .ok packet =>
    if packet.context ≠ [] then
      refusePacket "closed" "run needs a closed program: the packet's context is not empty"
    else
      match Obend.Elab.Gate.admit packet with
      | .error _ => refusePacket "objective-source-type-check" (Obend.Elab.Gate.refusalReason packet)
      | .ok admitted =>
        let checked := admitted.checked
        let limits : Machine.Limits := ⟨options.heap, options.stack⟩
        let outcome := Machine.runBounded limits options.ticks (Machine.initial packet.source.term)
        let (status, detail) : String × List (String × Json) :=
          match outcome with
          | .finished value _ => ("finished", [("value", packetValueJson value)])
          | .suspended .ticks _ => ("suspended", [("reason", toJson "ticks")])
          | .suspended .capacity _ => ("suspended", [("reason", toJson "capacity")])
          | .divergent address _ => ("divergent", [("address", toJson address)])
          | .refused reason _ => ("refused", [("reason", toJson (toString (repr reason)))])
          | .yielded plan _ => ("yielded", [("plan", toJson plan)])
        IO.println (receipt status ([("type", Packet.typeJson checked.type), ("ticks", toJson options.ticks)] ++ detail)).compress
        return (if status == "finished" then 0 else 3)

/-! ## The source path: a package in memory -/

/-- The module name `run.ts` gives a file: its base name without `.obend`, every character outside
`[A-Za-z0-9_]` replaced by `_`, a leading run of digits prefixed with `M`. -/
def moduleNameOf (file : String) : String :=
  let base := (System.FilePath.mk file).fileName.getD file
  let stem := if base.endsWith ".obend" then String.ofList (base.toList.take (base.length - 6)) else base
  let cleaned := String.ofList (stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')
  let digits := cleaned.toList.takeWhile Char.isDigit
  if digits.isEmpty then cleaned else "M" ++ cleaned

/-- A package read into memory: its modules (captured in order, every import edge locked) and
its entry. -/
structure Package where
  modules : List SourceModule
  entryModule : Nat
  entryDefinition : String
  /-- The entry module's declaration names (for `check` without an ENTRY). -/
  declarations : List String

/-- One `.obend` file as a package, as `run.ts` builds it. -/
def packageOfFile (file : String) (entry : Option String) : FE Package := do
  let bytes ← readBytes file
  let (m, names) ← captureModule #[] (moduleNameOf file) bytes none [] false
  return ⟨[m], 0, entry.getD "", names⟩

/-- A `dregg.objective-bend.package-input.v1` as a package (`captureSpec`, nothing written). -/
def packageOfSpec (spec : String) (entry : Option String) : FE Package := do
  let c ← captureSpec spec false
  let entryDefinition := entry.getD c.entryDefinition
  let m := c.modules[c.entryModule]!
  let ast ← liftFE (parseSource m.name m.source)
  let decls := ((ast.getObjVal? "declarations").bind Json.getArr?).toOption.getD #[]
  return ⟨c.modules.toList, c.entryModule, entryDefinition, decls.toList.map declarationName⟩

def hostLimits (ticks : String) : Json :=
  Json.mkObj [("ticks", toJson ticks), ("heap", toJson "100000"), ("stack", toJson "10000"), ("checkWork", toJson "65536")]

/-- `run.ts`'s response shorthand: a string is that label with an empty record payload. -/
def responseOf (r : Json) : Json :=
  match r with
  | .str label => Json.mkObj [("tag", toJson "variant"), ("label", toJson label),
      ("payload", Json.mkObj [("tag", toJson "record"), ("fields", Json.arr #[])])]
  | other => other

/-- The preview of `entry` applied to `args`, resumed with `responses`: the typed-preview JSON, or
the diagnostic that refused. The same stages `previewCommand` reports. -/
def previewPackage (p : Package) (args responses : Json) (ticks : String) : FE Json := do
  let lowered ← liftFE (lower p.modules p.entryModule p.entryDefinition args (Json.arr #[]) (hostLimits ticks) "application")
  if let .error message := lowered.proposal then refuse message "objective-source-type-proposal"
  let limits := Json.mkObj [("ticks", toJson ticks), ("heap", toJson "100000"), ("stack", toJson "10000")]
  match preview lowered.packet limits responses with
  | .ok r => pure r
  | .error message => refuse message "objective-typed-preview"

/-! ### The short form of `run.ts`, line for line -/

def typeText (t : Json) : String :=
  let rec go : Nat → Json → String
    | 0, t => t.compress
    | fuel + 1, t =>
      match (t.getObjValAs? String "tag").toOption with
      | some "natural" => "Nat" | some "boolean" => "Bool" | some "label" => "String" | some "emptyRow" => "{}"
      | some "variable" => "variable " ++ ((t.getObjValAs? String "index").toOption.getD "")
      | some "field" =>
        let rec fields : Nat → Json → List String
          | 0, _ => []
          | fuel' + 1, r =>
            if (r.getObjValAs? String "tag").toOption == some "field" then
              (((r.getObjValAs? String "name").toOption.getD "") ++ ": " ++ go fuel ((r.getObjVal? "member").toOption.getD .null)) ::
                fields fuel' ((r.getObjVal? "tail").toOption.getD .null)
            else []
        "{" ++ ", ".intercalate (fields (fuel + 1) t) ++ "}"
      | some "variant" => "sum " ++ go fuel ((t.getObjVal? "row").toOption.getD .null)
      | some "computation" => "Activity<" ++ go fuel ((t.getObjVal? "plan").toOption.getD .null) ++ ", " ++
          go fuel ((t.getObjVal? "response").toOption.getD .null) ++ ", " ++ go fuel ((t.getObjVal? "result").toOption.getD .null) ++ ">"
      | _ => t.compress
  go 4096 t

def dataText (d : Json) : String :=
  let rec go : Nat → Json → String
    | 0, d => d.compress
    | fuel + 1, d =>
      match (d.getObjValAs? String "tag").toOption with
      | some "natural" => (d.getObjValAs? String "value").toOption.getD ""
      | some "boolean" => toString ((d.getObjValAs? Bool "value").toOption.getD false)
      | some "label" => (toJson ((d.getObjValAs? String "value").toOption.getD "")).compress
      | some "record" =>
        let fields := ((d.getObjVal? "fields").bind Json.getArr?).toOption.getD #[]
        "{" ++ ", ".intercalate (fields.toList.map fun f => match f with
          | .str name => name
          | f => ((f.getObjValAs? String "name").toOption.getD "") ++ ": " ++ go fuel ((f.getObjVal? "value").toOption.getD .null)) ++ "}"
      | some "variant" =>
        ((d.getObjValAs? String "label").toOption.getD "") ++ "(" ++
          (match d.getObjVal? "payload" with
            | .ok payload => go fuel payload
            | .error _ => "...") ++ ")"
      | _ => d.compress
  go 4096 d

/-- `status`, `type`, one `turn` line per yield, `result` (the deep view when there is one, else the
weak-head view), `diagnostic`. -/
def shortForm (p : Json) (status : String) : String :=
  let lines : List String := ["status: " ++ status, "type: " ++ typeText ((p.getObjVal? "type").toOption.getD .null)]
  let turns := ((p.getObjVal? "turns").bind Json.getArr?).toOption.getD #[]
  let turnLines := turns.toList.zipIdx.map fun (t, i) =>
    "turn " ++ toString (i + 1) ++ ": yield " ++ dataText ((t.getObjVal? "plan").toOption.getD .null) ++
      (match t.getObjVal? "response" with
        | .ok r => "  <- " ++ dataText r
        | .error _ => "  (waiting)")
  let result := (p.getObjVal? "result").toOption.getD .null
  let resultLines := if result.isNull then [] else
    ["result: " ++ dataText (match (p.getObjVal? "resultData").toOption with
      | some d => if d.isNull then result else d
      | none => result)]
  let diagnostic := (p.getObjVal? "diagnostic").toOption.getD .null
  let diagnosticLines := if diagnostic.isNull then [] else
    ["diagnostic: " ++ (match diagnostic with | .str s => s | other => other.compress)]
  "\n".intercalate (lines ++ turnLines ++ resultLines ++ diagnosticLines)

/-- `status: refused`, `stage`, `message`, as `run.ts` prints a diagnostic. -/
def refusedForm (d : Diagnostic) : String :=
  "status: refused\nstage: " ++ d.stage ++ "\nmessage: " ++ d.message

structure RunArgs where
  args : Json := Json.arr #[]
  responses : Json := Json.arr #[]
  ticks : String := "100000"
  json : Bool := false

/-- `[ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]` in any order of flags, as `run.ts` reads them. -/
def parseRunArgs : List String → RunArgs → List String → Except String (RunArgs × List String)
  | [], r, positional => .ok (r, positional.reverse)
  | "--json" :: rest, r, positional => parseRunArgs rest { r with json := true } positional
  | "--ticks" :: n :: rest, r, positional => parseRunArgs rest { r with ticks := n } positional
  | ["--ticks"], _, _ => .error "--ticks needs a value"
  | x :: rest, r, positional => parseRunArgs rest r (x :: positional)

def runSource (package : FE Package) (rest : List String) : IO UInt32 := do
  let (options, positional) ← match parseRunArgs rest {} [] with
    | .ok v => pure v
    | .error e => do IO.eprintln e; return 64
  let argsJson := positional.getD 0 "[]"
  let responsesJson := positional.getD 1 "[]"
  let parsed : Except String (Json × Json) := do
    let args ← Json.parse argsJson
    let responses ← Json.parse responsesJson
    let responseArray ← responses.getArr?
    pure (args, Json.arr (responseArray.map responseOf))
  let (args, responses) ← match parsed with
    | .ok v => pure v
    | .error e => do IO.eprintln ("arguments and responses must be JSON arrays: " ++ e); return 64
  let result ← (do
    let p ← package
    if p.entryDefinition.isEmpty then refuse "usage: run needs an ENTRY (one def of the file)" "preview-request"
    previewPackage p args responses options.ticks : FE Json).run
  match result with
  | .ok p =>
    let status := (p.getObjValAs? String "status").toOption.getD ""
    if options.json then IO.println p.pretty else IO.println (shortForm p status)
    return 0
  | .error d =>
    if options.json then
      IO.println (Json.mkObj [("status", toJson "refused"), ("diagnostic", d.json)]).pretty
    else IO.println (refusedForm d)
    return 2

/-- `check`: every named declaration lowered in definition mode and accepted by the checker on
the front end's own packet. -/
def checkSource (package : FE Package) : IO UInt32 := do
  match ← package.run with
  | .error d => IO.eprintln d.json.compress; return 2
  | .ok p =>
    let names := if p.entryDefinition.isEmpty then p.declarations else [p.entryDefinition]
    let entryName := (p.modules[p.entryModule]?.map (·.name)).getD ""
    let mut failed := false
    for name in names do
      let key := entryName ++ "." ++ name
      let outcome : Except Diagnostic Json := do
        let lowered ← lower p.modules p.entryModule name (Json.arr #[]) (Json.arr #[]) (hostLimits "100000") "definition"
        let accepted ← accept lowered
        pure (Json.mkObj [("declaration", toJson key), ("status", toJson "accepted"),
          ("type", Packet.typeJson accepted.typed.type), ("uses", toJson accepted.typed.uses)])
      match outcome with
      | .ok receipt => IO.println receipt.compress
      | .error d =>
        -- A record or sum has no knot field: not a refusal of the program.
        if d.message == "missing selected entry" then continue
        failed := true
        IO.println (Json.mkObj [("declaration", toJson key), ("status", toJson "refused"), ("diagnostic", d.json)]).compress
    return (if failed then 2 else 0)

/-! ## Dispatch -/

public def main (args : List String) : IO UInt32 :=
  match args with
  | ["identity"] => do IO.println identityJson.compress; return 0
  | ["parse", path] => parseCommand path
  | ["capture", spec, dir] => captureCommand spec dir false
  | ["capture", spec, dir, "--objective-edition-1"] => captureCommand spec dir true
  | "elaborate" :: capture :: prefix_ :: rest => do
    let a := rest.getD 0 "[]"
    let projections := rest.getD 1 "[]"
    let limits := rest.getD 2 "{\"heap\":\"100000\",\"stack\":\"100000\",\"ticks\":\"100000\"}"
    let mode := rest.getD 3 "application"
    if rest.length > 4 then IO.eprintln usage; return 2
    elaborateCommand capture prefix_ a projections limits mode
  | ["preview", request, dir] => previewCommand request dir
  | ["batch", jobs, out] => batchCommand jobs out
  | ["check-core", path] => Obend.Elab.Gate.checkPacketFile path
  | "run-core" :: path :: rest =>
    match parseOptions rest {} with
    | .ok options => runPacket path options
    | .error message => do IO.eprintln message; return 1
  | ["check", "--package", spec] => checkSource (packageOfSpec spec none)
  | ["check", "--package", spec, entry] => checkSource (packageOfSpec spec (some entry))
  | ["check", file] => checkSource (packageOfFile file none)
  | ["check", file, entry] => checkSource (packageOfFile file (some entry))
  | "run" :: "--package" :: spec :: rest => runSource (packageOfSpec spec none) rest
  | "run" :: file :: entry :: rest => runSource (packageOfFile file (some entry)) rest
  | _ => do IO.eprintln usage; return 64
