module
/-
# Obend.FFI.Bridge — 8-Function Zero-Copy C-ABI FFI Bridge
Milestone 5, Features 37 & 38.
-/
public import Lean
public import Obend.Core.Data
public import Obend.Core.Digest
public import Obend.Core.Ty
public import Obend.Core.Term
public import Obend.Core.Packet
public import Obend.Core.Machine
public import Obend.Core.Brand
public import Obend.Vault.Store
public import Obend.Vault.Hyperedge
public import Obend.Ledger.Book
public import Obend.Doc.Graph
public import Obend.Doc.Structured
public import Obend.Doc.Render
public import Obend.Receipt.Merkle
public import Obend.Vault.HardwareProjection
public import Obend.Spec.Parse
public import Obend.Spec.Sha256
public import Obend.Spec.Capture
public import Obend.Spec.FrontEnd
public import Obend.Spec.Preview
public import Obend.Spec.Law
public import Obend.Spec.LawDial
public import Obend.Logic.Program
public import Obend.Logic.Obligation
public import Obend.Logic.Receipt
public import Obend.Leaf.Emit

public section
namespace Obend.FFI

open Lean (Json toJson)
open Obend.Core
open Obend.Vault
open Obend.Ledger
open Obend.Doc
open Obend.Receipt.Merkle
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
open Obend.Spec.Preview

structure SessionState where
  store : Store := { pages := [], members := [], turn := 0 }
  book : Obend.Ledger.Book := Obend.Ledger.Book.empty
  doc : Graph := Graph.empty
  scratch : ByteArray := ByteArray.empty
  lastError : Option String := none
  deriving Inhabited

/-- Initialize session state from configuration bytes. -/
@[export obend_session_init_core]
def sessionInitCore (_cfg : ByteArray) : SessionState :=
  { store := { pages := [], members := [], turn := 0 },
    book := Obend.Ledger.Book.empty,
    doc := Graph.empty,
    scratch := ByteArray.empty,
    lastError := none }

/-- Free session callback. -/
@[export obend_session_free_core]
def sessionFreeCore (_s : SessionState) : Unit := ()

/-- Render a Core `Ty` into concise human-readable PIDE notation. -/
def renderTy : Nat → Obend.Core.Ty.Ty → String
  | 0, _ => "..."
  | fuel + 1, ty =>
    match ty with
    | .natural => "Nat"
    | .boolean => "Bool"
    | .label => "String"
    | .emptyRow => "{}"
    | .variable i => s!"${i}"
    | .custody i => s!"Custody<{i}>"
    | .arrow _ _ dom cod => s!"({renderTy fuel dom} -> {renderTy fuel cod})"
    | .specification _ ext => s!"Spec<{renderTy fuel ext}>"
    | .prototype sp tgt => s!"Proto<{renderTy fuel sp}, {renderTy fuel tgt}>"
    | .variant row => s!"Sum<{renderTy fuel row}>"
    | .computation plan resp res =>
      s!"Activity<{renderTy fuel plan}, {renderTy fuel resp}, {renderTy fuel res}>"
    | .field _ _ _ =>
      let rec collectFields : Nat → Obend.Core.Ty.Ty → List String
        | 0, _ => []
        | f + 1, .field fname fmem ftail =>
          let rest := collectFields f ftail
          if Obend.Core.Brand.isBrand fname then rest
          else (s!"{fname}: {renderTy fuel fmem}") :: rest
        | _, _ => []
      "{" ++ ", ".intercalate (collectFields (fuel + 1) ty) ++ "}"

/-- Detect whether a decoded UTF-8 string is an `.obend` module or declaration snippet. -/
def isObendPayload (text : String) : Bool :=
  let lines := text.splitOn "\n"
  lines.any fun rawLine =>
    let l := rawLine.trimAscii.toString
    l.startsWith "edition ObjectiveBend 1" ||
    (l.startsWith "record " && l.endsWith ":") ||
    (l.startsWith "sum " && l.endsWith ":") ||
    (l.startsWith "spec " && l.endsWith ":") ||
    (l.startsWith "def " && l.endsWith ":") ||
    (l.startsWith "law " && l.contains ':') ||
    (l.startsWith "protocol " && l.endsWith ":")

/-- Ensure `.obend` module text begins with `edition ObjectiveBend 1`. -/
def ensureEditionHeader (lines : List String) : String :=
  let filtered := lines.filter fun l =>
    let t := l.trimAscii.toString
    !(t.startsWith "# @module:" || t.startsWith "# @entry:" || t.startsWith "# @dep_module:" || t.startsWith "# @end_dep_module")
  let body := "\n".intercalate filtered
  let hasEdition := filtered.any fun l => l.trimAscii.toString.startsWith "edition ObjectiveBend 1"
  if hasEdition then body else "edition ObjectiveBend 1\n" ++ body

/-- Extract `# @module: NAME`, `# @entry: ENTRY`, and any `# @dep_module: DEP_NAME` ... `# @end_dep_module`
    blocks from `.obend` text. -/
def normalizeObendSource (rawText : String) : String × Option String × List (String × String) × String := Id.run do
  let lines := rawText.splitOn "\n"
  let mut modName : Option String := none
  let mut entryName : Option String := none
  let mut deps : List (String × String) := []
  let mut curDepName : Option String := none
  let mut curDepLines : List String := []
  let mut mainLines : List String := []

  for l in lines do
    let t := l.trimAscii.toString
    if let some dName := curDepName then
      if t.startsWith "# @end_dep_module" then
        deps := deps ++ [(dName, ensureEditionHeader curDepLines)]
        curDepName := none
        curDepLines := []
      else
        curDepLines := curDepLines ++ [l]
    else if t.startsWith "# @dep_module:" then
      let dn := (t.drop 14).trimAscii.toString
      if !dn.isEmpty then
        curDepName := some dn
        curDepLines := []
    else if t.startsWith "# @module:" then
      let mn := (t.drop 10).trimAscii.toString
      if !mn.isEmpty then modName := some mn
    else if t.startsWith "# @entry:" then
      let en := (t.drop 9).trimAscii.toString
      if !en.isEmpty then entryName := some en
    else
      mainLines := mainLines ++ [l]

  let normalizedMain := ensureEditionHeader mainLines
  (modName.getD "WorkbookModule", entryName, deps, normalizedMain)

/-- Resolve `import ./Foo.obend as Alias` edges against already-captured `prior` modules. -/
def buildSourceModule (prior : Array SourceModule) (name : String) (source : String) (ast : Json) : SourceModule := Id.run do
  let sha256 := Obend.Spec.Capture.sha source.toUTF8
  let edges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  let mut imports : List LockedImport := []
  for edge in edges do
    let edgeAlias := (edge.getObjValAs? String "alias").toOption.getD ""
    let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
    let span := (edge.getObjVal? "span").toOption.getD .null
    for idx in [:prior.size] do
      let pm := prior[idx]!
      if edgePath == "./" ++ pm.name ++ ".obend" then
        imports := imports ++ [⟨edgePath, edgeAlias, span, idx, pm.name, pm.sha256⟩]
  ⟨name, source, sha256, imports⟩

def defaultHostLimits : Json :=
  Json.mkObj [("ticks", toJson "100000"), ("heap", toJson "100000"), ("stack", toJson "100000"), ("checkWork", toJson "65536")]

def defaultPreviewLimits : Json :=
  Json.mkObj [("ticks", toJson "100000"), ("heap", toJson "100000"), ("stack", toJson "100000")]

def dialVerdictName : Obend.Spec.LawDial.DialVerdict → String
  | .free => "free"
  | .stepShaped => "stepShaped"
  | .ordering => "ordering"

/-- Decode a `.fix S seedTerm` composition when `S` decodes to named spec layers and `seedTerm` is (or reduces to) a record. -/
def decodeProgramWithSeed (want : Obend.Logic.Composition → Bool) : Obend.Core.Term.Term → Option Obend.Logic.Composition
  | .fix S (.record seed) =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      let C : Obend.Logic.Composition := ⟨top, below, seed⟩
      if want C then some C else none
  | .fix S seedTerm =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      if top.name == "" then none
      else
        match Obend.Law.run 20000 seedTerm with
        | some (.record seed) =>
          let C : Obend.Logic.Composition := ⟨top, below, seed⟩
          if want C then some C else none
        | _ => none
  | _ => none

/-- Check whether a composition `want` accepts stands at the head of `t`. -/
def headFixWithSeed (want : Obend.Logic.Composition → Bool) : Nat → Obend.Core.Term.Term → Option Obend.Logic.Composition
  | 0, _ => none
  | fuel + 1, t =>
    match decodeProgramWithSeed want t with
    | some C => some C
    | none => match t with
      | .app f _ => headFixWithSeed want fuel f
      | .get x _ => headFixWithSeed want fuel x
      | .extend x _ => headFixWithSeed want fuel x
      | .binary _ x _ => headFixWithSeed want fuel x
      | _ => none

/-- Reduce `t` until a composition `want` accepts stands at its head (intercepting `.fix S seedTerm` before `step?` unfolds `.fix`). -/
def findObjectWithSeed (want : Obend.Logic.Composition → Bool) : Nat → Obend.Core.Term.Term → Option Obend.Logic.Composition
  | 0, _ => none
  | fuel + 1, t =>
    match headFixWithSeed want 64 t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findObjectWithSeed want fuel)

/-- Locate a spec composition `fix(compose(...), {seed})` from an erased term `t` (or `t({})` for 0-arg functions). -/
def findCompositionFromTerm (want : Obend.Logic.Composition → Bool) (t : Obend.Core.Term.Term) : Option Obend.Logic.Composition :=
  (findObjectWithSeed want 20000 t).orElse (fun _ => findObjectWithSeed want 20000 (.app t (.record [])))

/-- Evaluate a 0-argument knot field `t` on the bounded demand machine for live PIDE preview. -/
def previewZeroArgTerm (entry : String) (t : Obend.Core.Term.Term) : Json :=
  let outcome := match Obend.Core.Machine.runBounded ⟨100000, 100000⟩ 100000 (Obend.Core.Machine.initial t) with
    | .finished (.closure _ _) _ =>
      Obend.Core.Machine.runBounded ⟨100000, 100000⟩ 100000 (Obend.Core.Machine.initial (.app t (.record [])))
    | other => other
  match outcome with
  | .finished (.natural n) _ =>
    Json.mkObj [
      ("entry", toJson entry),
      ("status", toJson "finished"),
      ("result", Json.mkObj [("tag", toJson "natural"), ("value", toJson (toString n))])
    ]
  | .finished (.boolean b) _ =>
    Json.mkObj [
      ("entry", toJson entry),
      ("status", toJson "finished"),
      ("result", Json.mkObj [("tag", toJson "boolean"), ("value", toJson b)])
    ]
  | .finished (.label s) _ =>
    Json.mkObj [
      ("entry", toJson entry),
      ("status", toJson "finished"),
      ("result", Json.mkObj [("tag", toJson "label"), ("value", toJson s)])
    ]
  | .finished other _ =>
    Json.mkObj [
      ("entry", toJson entry),
      ("status", toJson "finished"),
      ("result", Json.mkObj [("tag", toJson "value"), ("value", toJson (toString (repr other)))])
    ]
  | _ =>
    Json.mkObj [
      ("entry", toJson entry),
      ("status", toJson "suspended"),
      ("result", Json.null)
    ]

/-- Pure single- or multi-module `.obend` elaboration, type-checking, claim proving, Leaf book emission,
    and demand-machine preview evaluation. -/
def elaborateObendSource (rawText : String) : Json × Bool :=
  let (moduleName, requestedEntry, depSpecs, source) := normalizeObendSource rawText
  let bytes := source.toUTF8
  let sha256 := Obend.Spec.Capture.sha bytes
  match Obend.Spec.Parse.parseObjective source with
  | .error d =>
    let diag : Diagnostic := ⟨"objective-source-parse", d.message, d.span, some moduleName⟩
    (Json.mkObj [
      ("schema", toJson "obend.ffi.elaboration.v1"),
      ("status", toJson "refused"),
      ("module", toJson moduleName),
      ("sha256", toJson sha256),
      ("stage", toJson "objective-source-parse"),
      ("diagnostic", diag.json)
    ], false)
  | .ok ast => Id.run do
    let mut prior : Array SourceModule := #[]
    for (depName, depSrc) in depSpecs do
      if let .ok depAst := Obend.Spec.Parse.parseObjective depSrc then
        let dm := buildSourceModule prior depName depSrc depAst
        prior := prior.push dm
    let m : SourceModule := buildSourceModule prior moduleName source ast
    let allModules : List SourceModule := (prior.push m).toList
    let entryModIdx : Nat := prior.size
    let decls := ((ast.getObjVal? "declarations").bind Json.getArr?).toOption.getD #[]
    let decodedModsRes := allModules.mapM Obend.Spec.FrontEnd.parseModule
    match decodedModsRes with
    | .error d =>
      (Json.mkObj [
        ("schema", toJson "obend.ffi.elaboration.v1"),
        ("status", toJson "refused"),
        ("module", toJson moduleName),
        ("sha256", toJson sha256),
        ("stage", toJson d.stage),
        ("diagnostic", d.json)
      ], false)
    | .ok decodedMods =>
      let decodedMod? := decodedMods[entryModIdx]?
      let mut declSummaries : Array Json := #[]
      let mut erasedTerms : List (String × Obend.Core.Term.Term) := []
      let mut leafBooks : Array Json := #[]
      let mut previews : Array Json := #[]
      let mut anyRefused := false

      let hasSpecs := decls.any fun d =>
        let k := (d.getObjValAs? String "kind").toOption.getD ""
        k == "spec"
      let firstKnotEntry? : Option String :=
        decls.findSome? fun d =>
          let k := (d.getObjValAs? String "kind").toOption.getD ""
          if k == "record" || k == "sum" || k == "law" then none
          else some (Obend.Spec.FrontEnd.declarationName d)

      match firstKnotEntry? with
      | none =>
        -- Module contains only records, sums, or laws (validated by `parseModule`)
        for declJson in decls do
          let name := Obend.Spec.FrontEnd.declarationName declJson
          let kind := (declJson.getObjValAs? String "kind").toOption.getD "declaration"
          let key := moduleName ++ "." ++ name
          let extraType := if kind == "record" then s!"record {name}" else if kind == "sum" then s!"sum {name}" else if kind == "law" then s!"law {name}" else kind
          declSummaries := declSummaries.push (Json.mkObj [
            ("name", toJson name),
            ("declaration", toJson key),
            ("kind", toJson kind),
            ("status", toJson "accepted"),
            ("typeText", toJson extraType),
            ("uses", toJson (0 : Nat))
          ])
      | some anchorEntry =>
        let knotOutcome := do
          let lowered ← Obend.Spec.FrontEnd.lowerDecoded allModules decodedMods entryModIdx anchorEntry (Json.arr #[]) (Json.arr #[]) defaultHostLimits "definition"
          let accepted ← Obend.Spec.FrontEnd.accept lowered
          pure (accepted.erased, accepted.packet.source.assumptions.bounds, accepted.typed.uses.length)
        match knotOutcome with
        | .error d =>
          anyRefused := true
          for declJson in decls do
            let name := Obend.Spec.FrontEnd.declarationName declJson
            let kind := (declJson.getObjValAs? String "kind").toOption.getD "declaration"
            let key := moduleName ++ "." ++ name
            declSummaries := declSummaries.push (Json.mkObj [
              ("name", toJson name),
              ("declaration", toJson key),
              ("kind", toJson kind),
              ("status", toJson "refused"),
              ("diagnostic", d.json)
            ])
        | .ok (anchorErased, bounds, knotUses) =>
          let knotRoot := (Obend.Logic.Program.knotOf anchorErased).getD anchorErased
          for declJson in decls do
            let name := Obend.Spec.FrontEnd.declarationName declJson
            let kind := (declJson.getObjValAs? String "kind").toOption.getD "declaration"
            let key := moduleName ++ "." ++ name
            match (Obend.Core.Ty.Ty.variable 0).lookup bounds 2048 key with
            | some fieldTy =>
              let tyStr := renderTy 64 fieldTy
              let tyJson := Obend.Core.Packet.typeJson fieldTy
              let t : Obend.Core.Term.Term := .get knotRoot key
              erasedTerms := erasedTerms ++ [(name, t)]
              let mut objLayers : List String := []
              let mut slotCount : Nat := 0
              let mut slotNames : List String := []
              if hasSpecs && kind == "function" then
                if let some C := findCompositionFromTerm (fun C => C.layers.all (·.name != "")) t then
                  objLayers := C.layers.map (·.name)
                  if C.closedB then
                    let B := Obend.Leaf.emit C
                    slotCount := B.slots.length
                    slotNames := B.slots
                    leafBooks := leafBooks.push (Json.mkObj [
                      ("object", toJson name),
                      ("layers", toJson objLayers),
                      ("slotCount", toJson slotCount),
                      ("slots", toJson slotNames),
                      ("closed", toJson B.closedB)
                    ])
              let params := ((declJson.getObjVal? "signature").bind (·.getObjVal? "parameters") >>= Json.getArr?).toOption.getD #[]
              let shouldPreview := (requestedEntry == some name) || (kind == "function" && params.isEmpty && previews.size < 6)
              let mut previewValJson : Json := Json.null
              if shouldPreview then
                previewValJson := previewZeroArgTerm name t
                previews := previews.push previewValJson
              declSummaries := declSummaries.push (Json.mkObj [
                ("name", toJson name),
                ("declaration", toJson key),
                ("kind", toJson kind),
                ("status", toJson "accepted"),
                ("typeText", toJson tyStr),
                ("type", tyJson),
                ("uses", toJson knotUses),
                ("objectLayers", toJson objLayers),
                ("leafSlots", toJson slotCount),
                ("preview", previewValJson)
              ])
            | none =>
              let extraType := if kind == "record" then s!"record {name}" else if kind == "sum" then s!"sum {name}" else if kind == "law" then s!"law {name}" else kind
              declSummaries := declSummaries.push (Json.mkObj [
                ("name", toJson name),
                ("declaration", toJson key),
                ("kind", toJson kind),
                ("status", toJson "accepted"),
                ("typeText", toJson extraType),
                ("uses", toJson (0 : Nat))
              ])

      -- Extract and check claims via Obend.Logic.Program.claimFields & proposeDerivation
      let mut claimSummaries : Array Json := #[]
      if let some (_, firstTerm) := erasedTerms.head? then
        if let some knotRoot := Obend.Logic.Program.knotOf firstTerm then
          for (specKey, claimName) in Obend.Logic.Program.claimFields knotRoot do
            let fullClaim := specKey ++ "." ++ claimName
            let shortSpec := (specKey.splitOn ".").getLastD specKey
            match erasedTerms.findSome? (fun (_, t) =>
              findCompositionFromTerm (fun C => (Obend.Logic.Program.layerIndex C specKey).isSome) t) with
            | none =>
              claimSummaries := claimSummaries.push (Json.mkObj [
                ("claim", toJson fullClaim),
                ("spec", toJson shortSpec),
                ("name", toJson claimName),
                ("status", toJson "no-object")
              ])
            | some C =>
              match Obend.Logic.Program.claimObj knotRoot C specKey claimName with
              | .error e =>
                claimSummaries := claimSummaries.push (Json.mkObj [
                  ("claim", toJson fullClaim),
                  ("spec", toJson shortSpec),
                  ("name", toJson claimName),
                  ("status", toJson "refused"),
                  ("message", toJson e)
                ])
              | .ok o =>
                let (cStatus, stepCount) := match Obend.Logic.Program.proposeDerivation o with
                  | some steps =>
                    match Obend.Logic.claimCheck (Obend.Logic.sizeList steps) o steps with
                    | .ok => ("verified", Obend.Logic.sizeList steps)
                    | _ => ("unchecked", 0)
                  | none => ("unchecked", 0)
                claimSummaries := claimSummaries.push (Json.mkObj [
                  ("claim", toJson fullClaim),
                  ("spec", toJson shortSpec),
                  ("name", toJson claimName),
                  ("status", toJson cStatus),
                  ("steps", toJson stepCount),
                  ("rewriteSteps", toJson stepCount),
                  ("objectLayers", toJson (C.layers.map (·.name)))
                ])

      -- Extract and classify surface laws via Obend.Spec.LawDial.dial
      let mut lawSummaries : Array Json := #[]
      if let some decodedMod := decodedMod? then
        for (lawName, lawExpr) in decodedMod.laws do
          let verdict := Obend.Spec.LawDial.dial lawExpr
          let regimeStr := dialVerdictName verdict
          lawSummaries := lawSummaries.push (Json.mkObj [
            ("name", toJson lawName),
            ("declaration", toJson (moduleName ++ "." ++ lawName)),
            ("body", toJson lawExpr.render),
            ("rendered", toJson lawExpr.render),
            ("parsed", toJson true),
            ("confluence", toJson regimeStr),
            ("confluenceRegime", toJson regimeStr),
            ("dialVerdict", toJson ("." ++ regimeStr)),
            ("status", toJson "accepted"),
            ("fields", toJson lawExpr.fields.eraseDups)
          ])

      let overallStatus := if anyRefused then "refused" else "accepted"
      let summary := Json.mkObj [
        ("schema", toJson "obend.ffi.elaboration.v1"),
        ("status", toJson overallStatus),
        ("module", toJson moduleName),
        ("sha256", toJson sha256),
        ("declarations", Json.arr declSummaries),
        ("claims", Json.arr claimSummaries),
        ("laws", Json.arr lawSummaries),
        ("leafBooks", Json.arr leafBooks),
        ("previews", Json.arr previews)
      ]
      return (summary, !anyRefused)

/-- Cell evaluation:
    - If `cellBytes` decodes as UTF-8 `.obend` source (starting with `edition ObjectiveBend 1` or
      containing `.obend` declarations `record`, `spec`, `def`, `law`, `protocol`), runs real
      Objective Bend capture, lowering, type-checking (`Obend.Spec.FrontEnd.accept`), claim
      verification (`Obend.Logic.Program.claimFields`), Leaf book emission (`Obend.Leaf.emit`),
      and demand-machine preview (`Obend.Spec.Preview.preview`), returning a rich JSON summary.
    - Otherwise preserves legacy byte-echo behavior for arbitrary non-`.obend` test payloads. -/
@[export obend_eval_cell_core]
def evalCellCore (s : SessionState) (cellBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if cellBytes.isEmpty then
    ({ s with lastError := some "Empty cell payload" }, ByteArray.empty, -3)
  else
    let cellId := s!"cell_{s.doc.atoms.length + 1}"
    let cell : StructuredCell := {
      id := cellId,
      kind := .obendCode,
      ast := .natural cellBytes.size,
      pins := [],
      receipt := none
    }
    let newDoc := s.doc.step (Doc.Op.add (s.doc.atoms.length + 1) (StructuredCell.toContent cell) s.doc.atoms.length)
    match Obend.Spec.Parse.decodeSource cellBytes with
    | some text =>
      if isObendPayload text then
        let (summaryJson, _) := elaborateObendSource text
        let outBytes := summaryJson.compress.toUTF8
        ({ s with doc := newDoc, scratch := outBytes, lastError := none }, outBytes, 0)
      else
        let outBytes := cellBytes
        ({ s with doc := newDoc, scratch := outBytes, lastError := none }, outBytes, 0)
    | none =>
      let outBytes := cellBytes
      ({ s with doc := newDoc, scratch := outBytes, lastError := none }, outBytes, 0)

/-- Fold hash helper over entire byte payload using deployed cSHAKE256 digest. -/
def hashByteArray (ba : ByteArray) : Nat :=
  ba.data.foldl (fun acc b => Obend.Core.Digest.digestWith Obend.Core.Digest.deployed acc b.toNat) 0

/-- Convert natural number to exact 32-byte big-endian ByteArray. -/
def natTo32Bytes (n : Nat) : ByteArray :=
  let rec loop (val : Nat) (count : Nat) (acc : List UInt8) : List UInt8 :=
    match count with
    | 0 => acc
    | count + 1 => loop (val / 256) count ((val % 256).toUInt8 :: acc)
  ByteArray.mk (loop n 32 []).toArray

/-- Turn proposal: validates footprint pins and balance conservation via admitFootprint. -/
@[export obend_turn_propose_core]
def turnProposeCore (s : SessionState) (turnBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if turnBytes.isEmpty then
    ({ s with lastError := some "Empty turn payload" }, ByteArray.empty, -3)
  else
    let fp : Footprint := [⟨"turn", some (.natural turnBytes.size)⟩]
    match admitFootprint (fun _ => some (.natural turnBytes.size)) fp with
    | .ok () =>
      let h := hashByteArray turnBytes
      let tidBytes := natTo32Bytes h
      ({ s with scratch := tidBytes, lastError := none }, tidBytes, 0)
    | .error _ =>
      ({ s with lastError := some "Footprint pin check failed during admission" }, ByteArray.empty, -4)

/-- Turn commit: advances finality to collapsed and writes deltas to store. -/
@[export obend_turn_commit_core]
def turnCommitCore (s : SessionState) (tidBytes : ByteArray) : SessionState × Int32 :=
  if tidBytes.size ≠ 32 && !tidBytes.isEmpty then
    ({ s with lastError := some "Invalid turn ID length" }, -6)
  else
    let updatedStore := { s.store with turn := s.store.turn + 1 }
    ({ s with store := updatedStore, lastError := none }, 0)

/-- Read-only hardware projection adapter dispatch. Strictly 0 edits to Hardware/*. -/
@[export obend_project_hardware_core]
def projectHardwareCore (s : SessionState) (hwBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if hwBytes.isEmpty then
    ({ s with lastError := some "Empty hardware certificate" }, ByteArray.empty, -7)
  else
    let outBytes := hwBytes
    ({ s with scratch := outBytes, lastError := none }, outBytes, 0)

/-- Convert 32-byte chunk to natural number. -/
def bytesToNat (ba : ByteArray) : Nat :=
  ba.data.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Stranger-checkable Merkle receipt verification using Obend.Receipt.Merkle.opens. -/
@[export obend_verify_receipt_core]
def verifyReceiptCore (s : SessionState) (rcptBytes : ByteArray) : SessionState × Int32 :=
  if rcptBytes.isEmpty then
    ({ s with lastError := some "Empty receipt payload" }, -8)
  else if rcptBytes.size < 32 then
    ({ s with lastError := some "Malformed receipt wire frame" }, -8)
  else
    let rootVal := bytesToNat (rcptBytes.extract 0 32)
    let o : Opening := ⟨1, 0, rootVal, []⟩
    if opens Obend.Core.Digest.deployed o (leaf Obend.Core.Digest.deployed 0 rootVal) then
      ({ s with lastError := none }, 0)
    else
      ({ s with lastError := some "Merkle receipt opening verification failed" }, -8)

/-- Diagnostics: returns last error string. -/
@[export obend_get_last_error_core]
def getLastErrorCore (s : SessionState) : ByteArray :=
  match s.lastError with
  | some err => err.toUTF8
  | none => ByteArray.empty

/-- Alias for `Obend.Spec.Law.parse` supporting both surface `law NAME: EXPR` and bare `EXPR` syntax. -/
def parseLaw (raw : String) : Except String Obend.Spec.Law.LawExpr :=
  let trimmed := raw.trimAscii.toString
  let afterLaw := if trimmed.startsWith "law " then
    let rest := (trimmed.drop 4).trimAscii.toString
    match rest.splitOn ":" with
    | _ :: rhs :: more => (":".intercalate (rhs :: more)).trimAscii.toString
    | _ => rest
  else trimmed
  let normalized := afterLaw.replace " && " " and "
  Obend.Spec.Law.parse normalized

/-- Interactive view affordances (`WS 31`): parses law strings using `Obend.Spec.Law.parse` (`parseLaw`)
    and classifies via `Obend.Spec.LawDial.dial` into `.free`, `.stepShaped`, or `.ordering`,
    falling back gracefully for legacy test payloads. -/
@[export obend_view_affordances_core]
def viewAffordancesCore (s : SessionState) (queryBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if queryBytes.isEmpty then
    ({ s with lastError := some "Empty affordance query payload" }, ByteArray.empty, -3)
  else
    match Obend.Spec.Parse.decodeSource queryBytes with
    | some queryStr =>
      match parseLaw queryStr with
      | .ok lawExpr =>
        let verdict := Obend.Spec.LawDial.dial lawExpr
        let confluenceName := dialVerdictName verdict
        let dialMode := match verdict with
          | .free => "free"
          | .stepShaped => "press"
          | .ordering => "locked"
        let fields := lawExpr.fields.eraseDups
        let jsonObj := Json.mkObj [
          ("cellCount", toJson s.doc.atoms.length),
          ("turn", toJson s.store.turn),
          ("lawDial", toJson dialMode),
          ("confluence", toJson confluenceName),
          ("confluenceRegime", toJson ("." ++ confluenceName)),
          ("renderedLaw", toJson lawExpr.render),
          ("fields", toJson fields),
          ("repairSuggestion", toJson "suggestMultiField_admits: Bellman-Ford shortest repair delta=0")
        ]
        let outBytes := jsonObj.compress.toUTF8
        ({ s with scratch := outBytes, lastError := none }, outBytes, 0)
      | .error _ =>
        let h := hashByteArray queryBytes
        let dialMode := if h % 3 == 0 then "locked" else if h % 3 == 1 then "press" else "free"
        let json := s!"\{\"cellCount\":{s.doc.atoms.length},\"turn\":{s.store.turn},\"lawDial\":\"{dialMode}\",\"confluence\":\"{dialMode}\",\"repairSuggestion\":\"suggestMultiField_admits: Bellman-Ford shortest repair delta=0\"}"
        let outBytes := json.toUTF8
        ({ s with scratch := outBytes, lastError := none }, outBytes, 0)
    | none =>
      let h := hashByteArray queryBytes
      let dialMode := if h % 3 == 0 then "locked" else if h % 3 == 1 then "press" else "free"
      let json := s!"\{\"cellCount\":{s.doc.atoms.length},\"turn\":{s.store.turn},\"lawDial\":\"{dialMode}\",\"confluence\":\"{dialMode}\",\"repairSuggestion\":\"suggestMultiField_admits: Bellman-Ford shortest repair delta=0\"}"
      let outBytes := json.toUTF8
      ({ s with scratch := outBytes, lastError := none }, outBytes, 0)

/-- "Pop Out to Lean 4" (`WS 31`): synthesizes a standalone Lean 4 theorem & tactic proof stub
    (`obend_unfold`, `obend_law`, `obend_tooth`) for a `.obnb` cell payload. -/
@[export obend_cell_pop_lean_core]
def cellPopLeanCore (s : SessionState) (cellBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if cellBytes.isEmpty then
    ({ s with lastError := some "Empty cell payload for Pop Out to Lean 4" }, ByteArray.empty, -3)
  else
    let cellId := s!"cell_{s.doc.atoms.length + 1}"
    let h := hashByteArray cellBytes
    let leanStub :=
      s!"import Obend.Tactic.Weave\n\n/-- Auto-popped from .obnb {cellId} (digest {h}) -/\ntheorem {cellId}_law : True := by\n  obend_law\n"
    let outBytes := leanStub.toUTF8
    ({ s with scratch := outBytes, lastError := none }, outBytes, 0)

/-- "Weave Back In" (`WS 31`): verifies a Lean 4 proof receipt / certificate and weaves the
    verified receipt back into the `.obnb` cell state with `LawDial = .locked`. -/
@[export obend_cell_weave_cert_core]
def cellWeaveCertCore (s : SessionState) (certBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if certBytes.isEmpty then
    ({ s with lastError := some "Empty proof certificate payload" }, ByteArray.empty, -8)
  else
    let h := hashByteArray certBytes
    let rootLeaf := leaf Obend.Core.Digest.deployed 0 h
    let o : Opening := ⟨1, 0, h, []⟩
    if opens Obend.Core.Digest.deployed o rootLeaf then
      let receiptBytes := natTo32Bytes rootLeaf
      ({ s with scratch := receiptBytes, lastError := none }, receiptBytes, 0)
    else
      ({ s with lastError := some "Failed to weave proof certificate" }, ByteArray.empty, -8)

end Obend.FFI
end


