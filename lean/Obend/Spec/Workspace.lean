module
/-
# Obend.Spec.Workspace — read a workspace, close it, lower it as one ecosystem knot

A `dregg.objective-bend.workspace.v1` is a workspace's ecosystem root (DESIGN §4): the releases it
reaches, the owners' records it reads, and the entry package being run:

    { "schema": "dregg.objective-bend.workspace.v1", "edition": "objective-bend-1",
      "releases": [ { "name": "commons/record", "version": "2.1.0",
                      "modules": [ { "name": "Record", "sourcePath": "record/Record.obend" } ] } ],
      "records":  [ { "name": "commons/record", "major": 2, "pin": 3, "names": "2.1.0", "owner": "ada" } ],
      "entry":    { "name": "garden", "version": "0.1.0", "modules": [ ... ],
                    "entryModule": "Garden", "entryDefinition": "main" } }

Paths are relative to the workspace file. Each release has exactly one ROOT module, the one whose
first declaration-level line is `package NAME [extends ...]` with its own name; its `law` lines are
the package law. A release's content hash is SHA-256 of `contentManifest` (its name and each
module's name and SHA-256), the hash an extension parent `NAME@0xHASH` names. A `names` of `null`
is a retired line.

Imports: `./NAME.obend` is a module of the same release (an earlier one); `PKG/NAME.obend` is
module `NAME` of package `PKG`, which must be on the importing package's precedence list. No lock
is written for a cross-package edge: the closure's pins are the lock.

The closure (`Obend.Spec.Ecosystem.close`) orders the modules base first (the reverse of the
entry's precedence list), names each `PKG::Module`, and hands the elaborator the packages with their
precedence lists (`Elaborate.PackageInfo`), so the root is one knot of package layers
(`Elaborate.packageKnot`).
-/
public import Lean
public import Obend.Spec.Capture
public import Obend.Spec.Ecosystem
public import Obend.Spec.LawCompile
public import Obend.Spec.PackageLaw
public import Obend.Law.Run
@[expose] public section
namespace Obend.Spec.Workspace
open Lean (Json toJson)
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
open Obend.Spec.Ecosystem
set_option autoImplicit false

def workspaceSchema : String := "dregg.objective-bend.workspace.v1"
def manifestHeader : String := "DREGG/OBJECTIVE-BEND/PACKAGE/v1"
def workspaceStage : String := "objective-workspace"

/-- One module of a release as read: its name, source text and SHA-256, and its parsed AST. -/
structure ReadModule where
  name : String
  source : String
  sha256 : String
  ast : Json

/-- A release as read: what the ecosystem resolves (`release`) and its modules. -/
structure ReadRelease where
  release : Release
  modules : List ReadModule

/-- The text whose SHA-256 is a release's content hash. -/
def contentManifest (name : String) (modules : List ReadModule) : String :=
  manifestHeader ++ "\n" ++ name ++ "\n" ++ String.join (modules.map fun m => m.name ++ " " ++ m.sha256 ++ "\n")

def contentHash (name : String) (modules : List ReadModule) : String :=
  Sha256.hexString (contentManifest name modules)

def wsRefuse {α : Type} (message : String) : FE α := refuse message workspaceStage

def declarations (ast : Json) : Array Json :=
  ((ast.getObjVal? "declarations").bind Json.getArr?).toOption.getD #[]

def parentOf (j : Json) : FE Syntax.ParentRef := do
  let some name := text j "name" | wsRefuse "package parent: name"
  match text j "major", text j "hash" with
  | some major, _ => match major.toNat? with
    | some n => pure (.intention name n)
    | none => wsRefuse "package parent major"
  | _, some hash => pure (.extension name hash)
  | none, none => wsRefuse "package parent: major or hash"

/-- The major line of a version: its first dot-separated component. -/
def majorOf (version : String) : Option Nat := ((version.splitOn ".").head?).bind String.toNat?

/-- Read one release: every module (strict UTF-8, parsed, distinct declarations), its one root
module, its parents, its content hash. -/
def readRelease (dir : System.FilePath) (j : Json) : FE ReadRelease := do
  let some name := text j "name" | wsRefuse "release: name"
  let some version := text j "version" | wsRefuse ("release " ++ name ++ ": version")
  let some major := majorOf version | wsRefuse ("release " ++ name ++ ": version " ++ version ++ " has no major")
  let rows := ((j.getObjVal? "modules").bind Json.getArr?).toOption.getD #[]
  if rows.isEmpty then wsRefuse ("release " ++ name ++ ": no modules")
  let mut modules : List ReadModule := []
  for row in rows do
    let some m := text row "name" | wsRefuse ("release " ++ name ++ ": module name")
    if !isIdentifier m then wsRefuse ("release " ++ name ++ ": module name " ++ m ++ " is not an identifier")
    let some path := text row "sourcePath" | wsRefuse ("release " ++ name ++ ": module " ++ m ++ " sourcePath")
    let bytes ← readBytes (dir / path).toString
    let sha256 := sha bytes
    if let some expected := text row "sha256" then
      if expected != sha256 then wsRefuse ("Error: changed module bytes: " ++ name ++ "::" ++ m)
    let some source := Parse.decodeSource bytes | throw (notUtf8 (name ++ "::" ++ m))
    let ast ← match Parse.parseObjective source with
      | .ok ast => pure ast
      | .error d => throw ⟨"objective-source-parse", d.message, d.span, some (name ++ "::" ++ m)⟩
    let names := (declarations ast).toList.map declarationName
    if names.eraseDups.length != names.length then wsRefuse ("Error: duplicate declaration in " ++ name ++ "::" ++ m)
    modules := modules ++ [⟨m, source, sha256, ast⟩]
  if (modules.map (·.name)).eraseDups.length != modules.length then wsRefuse ("release " ++ name ++ ": duplicate module name")
  let headers := modules.filterMap fun m =>
    ((declarations m.ast).toList.find? fun d => text d "kind" == some "package").map (m.name, ·)
  let [(_, header)] := headers
    | wsRefuse ("release " ++ name ++ " has " ++ toString headers.length ++ " root modules; exactly one module declares `package " ++ name ++ "`")
  if text header "name" != some name then
    wsRefuse ("release " ++ name ++ ": its root module declares package " ++ (text header "name").getD "")
  let parents ← (((header.getObjVal? "parents").bind Json.getArr?).toOption.getD #[]).toList.mapM parentOf
  return ⟨⟨name, version, major, contentHash name modules, parents⟩, modules⟩

def recordLine (j : Json) : FE RecordLine := do
  let some name := text j "name" | wsRefuse "record: name"
  let some major := (j.getObjValAs? Nat "major").toOption | wsRefuse ("record " ++ name ++ ": major")
  let some pin := (j.getObjValAs? Nat "pin").toOption | wsRefuse ("record " ++ name ++ ": pin")
  let fill := text j "names"
  return ⟨name, major, pin, fill, (text j "owner").getD ""⟩

/-- A workspace as read. -/
structure Workspace where
  view : View
  releases : List ReadRelease
  entry : ReadRelease
  entryModule : String
  entryDefinition : String

def readWorkspace (path : String) : FE Workspace := do
  let (_, j) ← readJson path
  if text j "schema" != some workspaceSchema || text j "edition" != some "objective-bend-1" then
    wsRefuse "Error: workspace schema/edition required"
  let dir := (System.FilePath.mk path).parent.getD "."
  let releases ← (((j.getObjVal? "releases").bind Json.getArr?).toOption.getD #[]).toList.mapM (readRelease dir)
  let lines ← (((j.getObjVal? "records").bind Json.getArr?).toOption.getD #[]).toList.mapM recordLine
  let some e := (j.getObjVal? "entry").toOption | wsRefuse "workspace: entry"
  let entry ← readRelease dir e
  let some entryModule := text e "entryModule" | wsRefuse "workspace entry: entryModule"
  let some entryDefinition := text e "entryDefinition" | wsRefuse "workspace entry: entryDefinition"
  return ⟨⟨releases.map (·.release), lines⟩, releases, entry, entryModule, entryDefinition⟩

def Workspace.sourceOf (w : Workspace) (r : Release) : Option ReadRelease :=
  if r == w.entry.release then some w.entry else w.releases.find? (·.release == r)

/-- The closed workspace, ready to lower: the modules base first, each `PKG::Module`, every import
edge locked to the module the closure resolved, and the packages with their precedence lists. -/
structure Closed where
  closure : Closure
  modules : List SourceModule
  decoded : List Syntax.Module
  packages : List Elaborate.PackageInfo
  entryModule : Nat
  entryDefinition : String
  /-- each package's law clauses, from its root module -/
  laws : List (String × List (String × Law.LawExpr))

def qualified (pkg m : String) : String := pkg ++ "::" ++ m

/-- `PKG/NAME.obend` as `(PKG, NAME)`. -/
def packageImport (path : String) : Option (String × String) :=
  if !path.endsWith ".obend" || path.startsWith "./" then none else
  let stem := String.ofList (path.toList.take (path.length - 6))
  match stem.splitOn "/" with
  | [] | [_] => none
  | parts => some ("/".intercalate parts.dropLast, parts.getLast!)

def close' (w : Workspace) : FE Closed := do
  let cl ← match close w.view w.entry.release with
    | .ok cl => pure cl
    | .error r => wsRefuse r.message
  let mut modules : Array SourceModule := #[]
  let mut packages : List Elaborate.PackageInfo := []
  let mut laws : List (String × List (String × Law.LawExpr)) := []
  for pkg in cl.order.reverse do
    let some r := cl.chosen.find? (·.name == pkg) | wsRefuse ("internal: " ++ pkg ++ " is not chosen")
    let some rr := w.sourceOf r | wsRefuse ("internal: no source for " ++ pkg)
    let precedence := (cl.precedence.lookup pkg).getD [pkg]
    for m in rr.modules do
      let edges := ((m.ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
      let mut imports : List LockedImport := []
      for edge in edges do
        let path := (text edge "path").getD ""
        let importAlias := (text edge "alias").getD ""
        let span := (edge.getObjVal? "span").toOption.getD .null
        let (targetPkg, targetModule) ← if path.startsWith "./" && path.endsWith ".obend" then
            pure (pkg, String.ofList ((path.toList.drop 2).take (path.length - 8)))
          else match packageImport path with
            | some (p, n) =>
              if !precedence.contains p || p == pkg then
                wsRefuse ("refused (import-outside-ancestry): " ++ qualified pkg m.name ++ " imports " ++ path ++
                  ", but " ++ p ++ " is not an ancestor of " ++ pkg)
              pure (p, n)
            | none => wsRefuse ("Error: a workspace import is ./NAME.obend or PACKAGE/NAME.obend: " ++ path)
        let key := qualified targetPkg targetModule
        let some target := modules.findIdx? (·.name == key)
          | wsRefuse ("Error: imports must reference an earlier module: " ++ qualified pkg m.name ++ " imports " ++ path)
        imports := imports ++ [⟨path, importAlias, span, target, key, modules[target]!.sha256⟩]
      modules := modules.push ⟨qualified pkg m.name, m.source, m.sha256, imports⟩
    packages := ⟨pkg, rr.modules.map (qualified pkg ·.name), precedence⟩ :: packages
  let moduleList := modules.toList
  let decoded ← liftFE (moduleList.mapM parseModule)
  for (m, d) in moduleList.zip decoded do
    if d.header.isSome then laws := laws ++ [(Elaborate.packageOfModule m.name, d.laws)]
  let entryKey := qualified w.entry.release.name w.entryModule
  let some entryModule := moduleList.findIdx? (·.name == entryKey)
    | wsRefuse ("Error: entry module absent: " ++ entryKey)
  return ⟨cl, moduleList, decoded, packages, entryModule, w.entryDefinition, laws⟩

def readClosed (path : String) : FE Closed := do close' (← readWorkspace path)

/-! ## Reports -/

def pinJson : Pin → Json
  | .intention n m p v h => Json.mkObj [("intention", toJson (n ++ "@^" ++ toString m)), ("pin", toJson p),
      ("version", toJson v), ("hash", toJson h)]
  | .extension n h => Json.mkObj [("extension", toJson (n ++ "@0x" ++ h)), ("hash", toJson h)]

def pinText : Pin → String
  | .intention n m p v _ => n ++ "@^" ++ toString m ++ " = " ++ v ++ " (record pin " ++ toString p ++ ")"
  | .extension n h => n ++ "@0x" ++ String.ofList (h.toList.take 12) ++ "… (fixed)"

/-- The turn a run records: the entry's content hash, every pin, the precedence order. -/
def turnJson (cl : Closure) : Json :=
  Json.mkObj [("schema", toJson "dregg.objective-bend.turn.v1"), ("entry", toJson cl.entry.name),
    ("entryHash", toJson cl.entry.hash), ("order", toJson cl.order), ("pins", Json.arr (cl.pins.map pinJson).toArray)]

def pinOfJson (j : Json) : Except String Pin := do
  if let some intention := text j "intention" then
    let pin ← j.getObjValAs? Nat "pin"
    let version ← j.getObjValAs? String "version"
    let hash ← j.getObjValAs? String "hash"
    match intention.splitOn "@^" with
    | [n, m] => return .intention n m.toNat! pin version hash
    | _ => throw "turn pin: intention"
  match (text j "extension").map (·.splitOn "@0x") with
  | some [n, h] => return .extension n h
  | _ => throw "turn pin: intention or extension"

/-- A recorded turn against a workspace: its entry must be the workspace's entry (same content). -/
def turnOfJson (w : Workspace) (j : Json) : FE Turn := do
  if text j "entryHash" != some w.entry.release.hash then
    wsRefuse "refused (turn-entry): the turn was recorded against other content of the entry package"
  let pins ← match (((j.getObjVal? "pins").bind Json.getArr?).toOption.getD #[]).toList.mapM pinOfJson with
    | .ok ps => pure ps
    | .error e => wsRefuse e
  let order := (((j.getObjVal? "order").bind Json.getArr?).toOption.getD #[]).toList.filterMap (·.getStr?.toOption)
  return ⟨w.entry.release, pins, order⟩

def admissionJson : Admission → Json
  | .admitted cl => Json.mkObj [("status", toJson "admitted"), ("order", toJson cl.order)]
  | .stale p => Json.mkObj [("status", toJson "stale"), ("name", toJson p.name), ("pin", pinJson p),
      ("message", toJson ("stale: " ++ pinText p ++ " moved; the record names another fill now"))]
  | .refused r => Json.mkObj [("status", toJson "refused"), ("message", toJson r.message)]
  | .diverged => Json.mkObj [("status", toJson "diverged"),
      ("message", toJson "every pin is current, but the re-derived closure differs from the turn's")]

/-! ## Judging a write by the effective package law -/

/-- The state type a JSON record of naturals and booleans has (fields in canonical order). -/
def stateOf (j : Json) : Except String (Obend.Core.Data.Data × Obend.Core.Ty.Ty) := do
  let .obj kvs := j | throw "a state is a JSON object of naturals and booleans"
  let fields := (kvs.toList.map fun (k, v) => (k, v)).mergeSort (fun a b => a.1 ≤ b.1)
  let mut data : List (String × Obend.Core.Data.Data) := []
  let mut ty : Obend.Core.Ty.Ty := .emptyRow
  for (k, v) in fields.reverse do
    match v with
    | .bool b => data := (k, .boolean b) :: data; ty := .field k .boolean ty
    | .num n => match n.mantissa.toNat, n.exponent with
      | m, 0 => data := (k, .natural m) :: data; ty := .field k .natural ty
      | _, _ => throw ("state field " ++ k ++ ": a natural")
    | _ => throw ("state field " ++ k ++ ": a natural or a boolean")
  return (.record data, ty)

/-- The effective law of the closure over state type `S`: each package's laws compiled
(`LawCompile.compilePackage`, named by the package), combined along the precedence list
(`Obend.Spec.PackageLaw.effectivePackages`). -/
def effectiveLaw (c : Closed) (S : Obend.Core.Ty.Ty) : Except PackageLaw.OpenClause Obend.Core.Term.Term :=
  PackageLaw.effectivePackages (fun pkg => LawCompile.compilePackage S pkg ((c.laws.lookup pkg).getD [])) c.closure.order

/-- Judge `old → new` as a write by member `agent`: `admitted`, or the refusal naming the
ancestor package and clause, or `undecided` when the reference step runs out. -/
def judge (c : Closed) (old new : Json) : Except String Json := do
  let (o, S) ← stateOf old
  let (n, S') ← stateOf new
  if S != S' then throw "old and new states have different fields"
  let law ← match effectiveLaw c S with
    | .ok t => pure t
    | .error e => throw ("open clause " ++ e.name)
  let rq := Law.requestAt "member" "member" 0 1000000 Law.writeO none none ⟨0⟩ 0
  let r := Law.run 200000 (Law.applyLaw law o n rq)
  let clauses := c.closure.order.flatMap fun pkg => ((c.laws.lookup pkg).getD []).map (PackageLaw.clauseName pkg ·.1)
  if Law.okB r then return Json.mkObj [("status", toJson "admitted"), ("clauses", toJson clauses)]
  match r with
  | some (.inject "refused" (.record [("by", .label by_), ("reason", .label why)])) =>
    return Json.mkObj [("status", toJson "refused"), ("by", toJson by_), ("reason", toJson why),
      ("message", toJson ("refused: " ++ by_ ++ " (" ++ why ++ ")")), ("clauses", toJson clauses)]
  | _ => return Json.mkObj [("status", toJson "undecided"), ("clauses", toJson clauses)]

end Obend.Spec.Workspace

end
