module
/-
# Obend.Spec.Capture — lock `.obend` sources as a package, and read a capture back

`capture` reads `dregg.objective-bend.package-input.v1` (edition `objective-bend-1`): modules
`{name, sourcePath, imports: [{alias, path, module, sha256?}], sha256?}`, `entryModule`,
`entryDefinition`. Imports name earlier modules only, by `./NAME.obend`. Each source is read once
as strict UTF-8; optional expected hashes refuse changed bytes. The capture
(`dregg.objective-bend.captured-package.v2`) records the front-end identity, each module's source
copy and SHA-256, and each import edge; there is no stored AST. A capture made by another front end
refuses (`loadCapture`). The `parse`, `capture` and `elaborate` commands live here too; `preview`
and `batch` in `Obend.Spec.Preview`; the dispatch in `Obend.Main`.

Ported from minidregg `Host/ObjectiveBendFrontEnd.lean` (commit 092027a2), the capture half. A
refusal is a `dregg.bend.compiler-diagnostic.v1` on stderr (and in NEW_DIR/diagnostic.json) with
exit 2; `elaborate` exits 1, as its predecessor did.
-/
public import Lean
public import Obend.Spec.Parse
public import Obend.Spec.Syntax
public import Obend.Spec.Elaborate
public import Obend.Spec.FrontEnd
public import Obend.Spec.Sha256
public import Obend.Spec.Identity
@[expose] public section
namespace Obend.Spec.Capture
open Lean (Json toJson)
open Obend.Spec.FrontEnd
set_option autoImplicit false

def identity : String := Identity.identity

abbrev FE := ExceptT Diagnostic IO

def captureStage : String := "objective-package-capture"
def refuse {α : Type} (message : String) (stage : String := captureStage) : FE α :=
  throw { stage, message }
def liftFE {α : Type} (x : Except Diagnostic α) : FE α := ExceptT.mk (pure x)

def sha (bytes : ByteArray) : String := Sha256.hex bytes

def isIdentifier (s : String) : Bool := Parse.isIdent s.toList

def canonicalDecimal (s : String) : Bool :=
  s == "0" || (match s.toList with
    | d :: rest => d != '0' && d.isDigit && rest.all Char.isDigit
    | [] => false)

def utf8Text (bytes : ByteArray) (what : String) : FE String :=
  match Parse.decodeSource bytes with
  | some text => pure text
  | none => refuse ("TypeError: " ++ what ++ " is not valid UTF-8")

def readBytes (path : String) : FE ByteArray := do
  match ← (IO.FS.readBinFile path).toBaseIO with
  | .ok bytes => pure bytes
  | .error e => refuse ("Error: " ++ toString e)

def readJson (path : String) : FE (ByteArray × Json) := do
  let bytes ← readBytes path
  let text ← utf8Text bytes path
  match Json.parse text with
  | .ok json => pure (bytes, json)
  | .error e => refuse ("SyntaxError: " ++ path ++ ": " ++ e)

def text (j : Json) (key : String) : Option String := (j.getObjValAs? String key).toOption

def pretty (j : Json) : String := j.pretty ++ "\n"

/-- Write a file that must not exist (`flag: "wx"`). -/
def writeNew (path : System.FilePath) (contents : String) : FE Unit := do
  if ← path.pathExists then refuse ("Error: EEXIST: file already exists, " ++ path.toString)
  IO.FS.writeFile path contents

/-! ## Capture: one module, in memory -/

/-- A module's import lock as written in a package spec. -/
structure Lock where
  importAlias : Option String
  path : Option String
  target : Json
  sha256 : Option String

def Lock.ofJson (j : Json) : Lock :=
  ⟨text j "alias", text j "path", (j.getObjVal? "module").toOption.getD .null, text j "sha256"⟩

def importIndex (value : Json) (label : String) : FE Nat :=
  match value.getStr? with
  | .ok s => if canonicalDecimal s then pure s.toNat! else refuse ("Error: " ++ label ++ ": canonical decimal index required")
  | .error _ => refuse ("Error: " ++ label ++ ": canonical decimal index required")

def sealedPath (p : String) : Bool :=
  match p.toList with
  | '.' :: '/' :: rest =>
    let stem := rest.take (rest.length - 6)
    Parse.endsWith rest ".obend" && Parse.isIdent stem
  | _ => false

def notUtf8 (name : String) : Diagnostic :=
  ⟨"objective-source-parse", "TypeError: The encoded data was not valid for encoding utf-8", none, some name⟩

/-- Capture module `name` (the next after `prior`): fingerprint, strict decode, parse, distinct
declarations, and every import edge checked against its lock. Returns the module and its
declaration names. -/
def captureModule (prior : Array SourceModule) (name : String) (bytes : ByteArray)
    (expected : Option String) (locks : List Lock) (adopted : Bool) : FE (SourceModule × List String) := do
  let sha256 := sha bytes
  if let some e := expected then
    if e != sha256 then refuse ("Error: changed module bytes: " ++ name)
  let some source := Parse.decodeSource bytes | throw (notUtf8 name)
  let ast ← match Parse.parseObjective source with
    | .ok ast => pure ast
    | .error d => throw ⟨"objective-source-parse", d.message, d.span, some name⟩
  let decls := ((ast.getObjVal? "declarations").bind Json.getArr?).toOption.getD #[]
  let names := decls.toList.map declarationName
  if names.eraseDups.length != names.length then refuse ("Error: duplicate declaration in " ++ name)
  let edges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  if edges.size != locks.length then refuse ("Error: import count differs: " ++ name)
  let aliases := edges.toList.map (fun e => (text e "alias").getD "")
  if aliases.eraseDups.length != aliases.length then refuse ("Error: duplicate import alias in " ++ name)
  let mut imports : List LockedImport := []
  for (edge, lock) in edges.toList.zip locks do
    let target ← importIndex lock.target "import module"
    if target ≥ prior.size then refuse "Error: imports must reference an earlier sealed module"
    let edgeAlias := (text edge "alias").getD ""
    let edgePath := (text edge "path").getD ""
    if lock.importAlias != some edgeAlias || ((!adopted || lock.path.isSome) && lock.path != some edgePath) then
      refuse ("Error: source import path/alias differs: " ++ name)
    if !sealedPath edgePath then
      refuse "Error: Objective edition 1 imports require sealed ./NAME.obend paths (Gen-1 ./NAME.bend is retired)"
    let targetModule := prior[target]!
    if edgePath != "./" ++ targetModule.name ++ ".obend" then refuse ("Error: source import target differs: " ++ name)
    if let some s := lock.sha256 then
      if s != targetModule.sha256 then refuse ("Error: changed imported bytes: " ++ name)
    imports := imports ++ [⟨edgePath, edgeAlias, (edge.getObjVal? "span").toOption.getD .null, target,
      targetModule.name, targetModule.sha256⟩]
  return (⟨name, source, sha256, imports⟩, names)

/-! ## Capture: a package spec -/

structure Captured where
  modules : Array SourceModule
  bytes : Array ByteArray
  entryModule : Nat
  entryDefinition : String
  requestSha256 : String
  requestSchema : String
  adopted : Bool

/-- `dregg.objective-bend.package-input.v1` (or, with `adopt`, a `dregg.bend.package-input.v1`
Studio capture of `.obend` modules): read and lock every module source. -/
def captureSpec (specPath : String) (adopt : Bool) : FE Captured := do
  let (requestBytes, request) ← readJson specPath
  let schema := (text request "schema").getD ""
  let adopted := adopt && schema == "dregg.bend.package-input.v1"
  if !adopted && (schema != "dregg.objective-bend.package-input.v1" || text request "edition" != some "objective-bend-1") then
    refuse "Error: Objective package schema/edition required"
  let modules := ((request.getObjVal? "modules").bind Json.getArr?).toOption.getD #[]
  if modules.isEmpty || modules.size > 256 then refuse "Error: module capacity"
  let mut names : List String := []
  for m in modules do
    let some n := text m "name" | refuse "Error: module name: identifier required"
    if !isIdentifier n then refuse "Error: module name: identifier required"
    names := names ++ [n]
  if names.eraseDups.length != names.length then refuse "Error: duplicate module name"
  let entryModule ← importIndex ((request.getObjVal? "entryModule").toOption.getD .null) "entry module"
  let some entryDefinition := text request "entryDefinition" | refuse "Error: entry definition: identifier required"
  if !isIdentifier entryDefinition then refuse "Error: entry definition: identifier required"
  if entryModule ≥ modules.size then refuse "Error: entry module absent"
  let mut captured : Array SourceModule := #[]
  let mut sources : Array ByteArray := #[]
  let mut declared : Array (List String) := #[]
  let mut total := 0
  for (m, name) in modules.toList.zip names do
    let some sourcePath := text m "sourcePath" | refuse "Error: invalid module record"
    let some locks := ((m.getObjVal? "imports").bind Json.getArr?).toOption | refuse "Error: invalid module record"
    let bytes ← readBytes sourcePath
    total := total + bytes.size
    if total > 4194304 then refuse "Error: source byte capacity"
    let (module, decls) ← captureModule captured name bytes (text m "sha256") (locks.toList.map Lock.ofJson) adopted
    captured := captured.push module
    sources := sources.push bytes
    declared := declared.push decls
  if !(declared[entryModule]!.contains entryDefinition) then refuse "Error: entry declaration absent"
  return ⟨captured, sources, entryModule, entryDefinition, sha requestBytes, schema, adopted⟩

def captureSchema : String := "dregg.objective-bend.captured-package.v2"

def captureJson (c : Captured) (paths : Array String) : Json :=
  Json.mkObj [("schema", toJson captureSchema), ("edition", toJson "objective-bend-1"),
    ("frontEnd", toJson identity), ("requestSha256", toJson c.requestSha256), ("requestSchema", toJson c.requestSchema),
    ("editionSelection", toJson (if c.adopted then "explicit-caller-adoption" else "declared-request")),
    ("modules", Json.arr ((c.modules.zip paths).map fun (m, path) => Json.mkObj [("name", toJson m.name),
      ("sourcePath", toJson path), ("sha256", toJson m.sha256),
      ("imports", Json.arr (m.imports.map LockedImport.json).toArray)])),
    ("entryModule", toJson (toString c.entryModule)), ("entryDefinition", toJson c.entryDefinition),
    ("sourceEntry", toJson (c.modules[c.entryModule]!.name ++ "." ++ c.entryDefinition)),
    ("sourceStatus", toJson "exact locked source"),
    ("semanticStatus", toJson "requires Objective elaboration and execution receipt"),
    ("theoremScope", toJson "no typing or totality theorem asserted")]

/-- Write the locked snapshot: `dir/source/<i>.obend` and `dir/objective.json`. -/
def writeCapture (c : Captured) (dir : System.FilePath) : FE Json := do
  IO.FS.createDirAll (dir / "source")
  let root ← IO.FS.realPath dir
  let mut paths : Array String := #[]
  for i in [0:c.bytes.size] do
    let path := root / "source" / s!"{i}.obend"
    if ← path.pathExists then refuse ("Error: EEXIST: file already exists, " ++ path.toString)
    IO.FS.writeBinFile path c.bytes[i]!
    paths := paths.push path.toString
  let json := captureJson c paths
  writeNew (dir / "objective.json") (pretty json)
  return json

/-! ## Loading a capture -/

structure Loaded where
  bytes : ByteArray
  json : Json
  modules : List SourceModule
  entryModule : Nat
  entryDefinition : String

/-- Re-read a capture: its schema and front end, every source against its fingerprint, every
lock against the module it names. -/
def loadCapture (path : String) : FE Loaded := do
  let (bytes, capture) ← readJson path
  if text capture "schema" != some captureSchema || text capture "edition" != some "objective-bend-1" then
    refuse "Error: unsupported captured edition" "objective-core-elaboration"
  if text capture "frontEnd" != some identity then
    refuse ("Error: capture was produced by another front end (" ++ (text capture "frontEnd").getD "none" ++
      ") than this one (" ++ identity ++ ")") "objective-core-elaboration"
  let rows := ((capture.getObjVal? "modules").bind Json.getArr?).toOption.getD #[]
  if rows.size > 64 then refuse "Error: preview module capacity refused" "objective-core-elaboration"
  let mut modules : Array SourceModule := #[]
  for row in rows do
    let some sourcePath := text row "sourcePath" | refuse "Error: invalid captured module" "objective-core-elaboration"
    let name := (text row "name").getD ""
    let source ← readBytes sourcePath
    if source.size > 2097152 then refuse "Error: preview source capacity refused" "objective-core-elaboration"
    if some (sha source) != text row "sha256" then
      refuse ("Error: captured source hash mismatch " ++ name) "objective-core-elaboration"
    let some decoded := Parse.decodeSource source
      | refuse ("Error: captured source is not UTF-8 " ++ name) "objective-core-elaboration"
    let edges := ((row.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
    let mut imports : List LockedImport := []
    for edge in edges do
      let index := (text edge "module").getD ""
      let target := index.toNat!
      if !canonicalDecimal index || target ≥ modules.size || some modules[target]!.name != text edge "moduleName" ||
          some modules[target]!.sha256 != text edge "sha256" then
        refuse "Error: invalid locked import" "objective-core-elaboration"
      imports := imports ++ [⟨(text edge "path").getD "", (text edge "alias").getD "",
        (edge.getObjVal? "span").toOption.getD .null, target, modules[target]!.name, modules[target]!.sha256⟩]
    modules := modules.push ⟨name, decoded, sha source, imports⟩
  let entryText := (text capture "entryModule").getD ""
  if !canonicalDecimal entryText then refuse "Error: selected module" "objective-core-elaboration"
  return ⟨bytes, capture, modules.toList, entryText.toNat!, (text capture "entryDefinition").getD ""⟩

/-! ## Commands -/

def report (dir : Option System.FilePath) (d : Diagnostic) : IO UInt32 := do
  if let some dir := dir then
    try
      IO.FS.createDirAll dir
      unless ← (dir / "diagnostic.json").pathExists do IO.FS.writeFile (dir / "diagnostic.json") (pretty d.json)
    catch _ => pure ()
  IO.eprintln d.json.compress
  return 2

def parseCommand (path : String) : IO UInt32 := do
  match ← (do
      let bytes ← readBytes path
      let source ← utf8Text bytes path
      liftFE (match Parse.parseObjective source with
        | .ok ast => .ok ast
        | .error d => .error { stage := "objective-source-parse", message := d.message, span := d.span }) : FE Json).run with
  | .ok ast => IO.println ast.compress; return 0
  | .error d => report none d

def captureCommand (spec dir : String) (adopt : Bool) : IO UInt32 := do
  match ← (do writeCapture (← captureSpec spec adopt) dir : FE Json).run with
  | .ok json => IO.println json.compress; return 0
  | .error d => report (some dir) d

def elaborateCommand (capturePath prefix_ argsRaw projectionsRaw limitsRaw mode : String) : IO UInt32 := do
  let run : FE Json := do
    let loaded ← loadCapture capturePath
    let parse (raw what : String) : FE Json := match Json.parse raw with
      | .ok j => pure j
      | .error e => refuse ("SyntaxError: " ++ what ++ ": " ++ e) "objective-core-elaboration"
    let lowered ← liftFE (lower loaded.modules loaded.entryModule loaded.entryDefinition (← parse argsRaw "arguments")
      (← parse projectionsRaw "projections") (← parse limitsRaw "limits") mode)
    let core := lowered.core
    IO.FS.writeFile (prefix_ ++ ".typed.json") (pretty lowered.packet)
    IO.FS.writeFile (prefix_ ++ ".core.json") (pretty core)
    return Json.mkObj [("schema", toJson "dregg.objective-bend.core.v2"), ("sourceEntry", toJson lowered.sourceEntry),
      ("outputPrefix", toJson prefix_), ("coreSha256", toJson (Sha256.hexString core.compress)),
      ("frontEnd", toJson identity),
      ("status", (core.getObjVal? "status").toOption.getD .null)]
  match ← run.run with
  | .ok json => IO.println json.compress; return 0
  | .error d => IO.eprintln d.json.compress; return 1

end Obend.Spec.Capture

end
