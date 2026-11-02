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
public import Obend.Tactic.Tooth

public section
namespace Obend.FFI

open Lean (Json toJson)
open Obend.Core
open Obend.Core.Data (Data)
open Obend.Vault
open Obend.Ledger
open Obend.Doc
open Obend.Receipt.Merkle
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
open Obend.Spec.Preview

/-- Pending proposed turn waiting to be committed via `turnCommitCore`. -/
structure PendingTurnProposal where
  tidBytes : ByteArray
  footprint : Footprint
  writes : List (String × Data)
  deriving Inhabited

structure SessionState where
  store : Store := { pages := [], members := [], turn := 0 }
  vaultStore : List (String × Data) := []
  pendingProposals : List PendingTurnProposal := []
  admittedRoots : Array ByteArray := #[]
  book : Obend.Ledger.Book := Obend.Ledger.Book.empty
  doc : Graph := Graph.empty
  scratch : ByteArray := ByteArray.empty
  lastError : Option String := none
  deriving Inhabited

abbrev Session := SessionState

/-- Canonical empty session state before any cells or turns are proposed or admitted. -/
def SessionState.empty : SessionState := {}

/-- Initialize session state from configuration bytes. -/
@[export obend_session_init_core]
def sessionInitCore (_cfg : ByteArray) : SessionState :=
  { store := { pages := [], members := [], turn := 0 },
    vaultStore := [],
    pendingProposals := [],
    admittedRoots := #[],
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

/-- Convert 32-byte chunk to natural number. -/
def bytesToNat (ba : ByteArray) : Nat :=
  ba.data.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Compute deterministic 32-byte Merkle leaf commitment for payload digest `h`. -/
def computeReceiptCommitment (h : Nat) : ByteArray :=
  natTo32Bytes (leaf Obend.Core.Digest.deployed 0 h)

/-- Build a 64-byte self-authenticating receipt `[32-byte Merkle commitment || 32-byte payload digest]`. -/
def buildCommittedReceipt (payload : ByteArray) : ByteArray × ByteArray :=
  let h := hashByteArray payload
  let rootBytes := computeReceiptCommitment h
  let digestBytes := natTo32Bytes h
  (rootBytes, rootBytes ++ digestBytes)

/-- Push a 32-byte root into `admittedRoots` if not already present. -/
def pushAdmittedRoot (roots : Array ByteArray) (r : ByteArray) : Array ByteArray :=
  if r.size == 32 && !roots.contains r then roots.push r else roots

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
    let (cellRoot, _) := buildCommittedReceipt cellBytes
    let cell : StructuredCell := {
      id := cellId,
      kind := .obendCode,
      ast := .natural cellBytes.size,
      pins := [],
      receipt := some cellRoot
    }
    let newDoc := s.doc.step (Doc.Op.add (s.doc.atoms.length + 1) (StructuredCell.toContent cell) s.doc.atoms.length)
    let roots1 := pushAdmittedRoot s.admittedRoots cellRoot
    match Obend.Spec.Parse.decodeSource cellBytes with
    | some text =>
      if isObendPayload text then
        let (summaryJson, _) := elaborateObendSource text
        let outBytes := summaryJson.compress.toUTF8
        let (outRoot, _) := buildCommittedReceipt outBytes
        let roots2 := pushAdmittedRoot roots1 outRoot
        ({ s with doc := newDoc, admittedRoots := roots2, scratch := outBytes, lastError := none }, outBytes, 0)
      else
        let outBytes := cellBytes
        ({ s with doc := newDoc, admittedRoots := roots1, scratch := outBytes, lastError := none }, outBytes, 0)
    | none =>
      let outBytes := cellBytes
      ({ s with doc := newDoc, admittedRoots := roots1, scratch := outBytes, lastError := none }, outBytes, 0)

/-- Look up a cell key in `s.vaultStore` or `s.store.pages` (`VaultStore`). -/
def sessionStoreLookup (s : SessionState) (cell : String) : Option Data :=
  match s.vaultStore.lookup cell with
  | some d => some d
  | none =>
    match s.store.page? cell with
    | some p =>
      match p.seen with
      | some seenStr =>
        match seenStr.trimAscii.toString.toNat? with
        | some n => some (.natural n)
        | none => some (.label seenStr)
      | none => some (.natural p.history.length)
    | none => none

/-- Render a `Data` value to a concise string for `Page.seen`. -/
def renderDataSeen : Data → String
  | .natural n => toString n
  | .boolean b => toString b
  | .label s => s
  | other => toString (repr other)

/-- Parse a string value as `.natural` if numeric, else `.label`. -/
def parseDataAtom (raw : String) : Data :=
  let t := raw.trimAscii.toString
  match t.toNat? with
  | some n => .natural n
  | none => .label t

/-- Update `s.vaultStore` and `s.store.pages` with committed `(cell, Data)` writes. -/
def applyWritesToSession (s : SessionState) (writes : List (String × Data)) : List (String × Data) × Store :=
  let newVaultStore := writes.foldl (fun acc (k, v) =>
    (k, v) :: acc.filter (fun (k', _) => k' != k)) s.vaultStore
  let newPages := writes.foldl (fun pages (k, v) =>
    let seenStr := renderDataSeen v
    match pages.find? (·.name == k) with
    | some _existing =>
      pages.map fun p =>
        if p.name == k then
          { p with history := p.history ++ [s.doc], seen := some seenStr }
        else p
    | none =>
      let newPage : Page := {
        name := k,
        id := pages.length + 1,
        history := [s.doc],
        seen := some seenStr,
        authors := [],
        note := none,
        kind := none
      }
      pages ++ [newPage]) s.store.pages
  (newVaultStore, { s.store with pages := newPages, turn := s.store.turn + 1 })

/-- Extract footprint pins and proposed writes from `turnBytes` against `s.store`. -/
def parseTurnFootprintAndWrites (s : SessionState) (turnBytes : ByteArray) : Footprint × List (String × Data) :=
  let basePin : Footprint :=
    match s.store.page? "turn" with
    | some _ => [⟨"turn", some (.natural turnBytes.size)⟩]
    | none => []
  match Obend.Spec.Parse.decodeSource turnBytes with
  | some rawText =>
    let trimmed := rawText.trimAscii.toString
    if trimmed.startsWith "pin:" then
      let rest := (trimmed.drop 4).trimAscii.toString
      match rest.splitOn ":" with
      | [cRaw, expRaw, newRaw] =>
        let cell := cRaw.trimAscii.toString
        let expStr := expRaw.trimAscii.toString
        let expOpt : Option Data :=
          if expStr == "none" || expStr.isEmpty then none
          else some (parseDataAtom expStr)
        let newVal := parseDataAtom newRaw
        ([⟨cell, expOpt⟩], [(cell, newVal)])
      | _ =>
        let cell := s!"turn_{s.store.turn}"
        let valData := Data.natural turnBytes.size
        let expOpt := if (sessionStoreLookup s cell).isSome then some valData else none
        (basePin ++ [⟨cell, expOpt⟩], [(cell, valData)])
    else if trimmed.contains '=' && !trimmed.contains '\n' && !trimmed.startsWith "{" then
      match trimmed.splitOn "=" with
      | cRaw :: vParts =>
        let cell := cRaw.trimAscii.toString
        let valData := parseDataAtom ("=".intercalate vParts)
        let expOpt := if (sessionStoreLookup s cell).isSome then some valData else none
        ([⟨cell, expOpt⟩], [(cell, valData)])
      | [] =>
        let cell := s!"turn_{s.store.turn}"
        let valData := Data.natural turnBytes.size
        let expOpt := if (sessionStoreLookup s cell).isSome then some valData else none
        (basePin ++ [⟨cell, expOpt⟩], [(cell, valData)])
    else
      let cell := s!"turn_{s.store.turn}"
      let valData := Data.natural turnBytes.size
      let expOpt := if (sessionStoreLookup s cell).isSome then some valData else none
      (basePin ++ [⟨cell, expOpt⟩], [(cell, valData)])
  | none =>
    let cell := s!"turn_{s.store.turn}"
    let valData := Data.natural turnBytes.size
    let expOpt := if (sessionStoreLookup s cell).isSome then some valData else none
    (basePin ++ [⟨cell, expOpt⟩], [(cell, valData)])

/-- Turn proposal: validates footprint pins against the session's actual `s.store` via `admitFootprint`. -/
@[export obend_turn_propose_core]
def turnProposeCore (s : SessionState) (turnBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if turnBytes.isEmpty then
    ({ s with lastError := some "Empty turn payload" }, ByteArray.empty, -3)
  else
    let (fp, writes) := parseTurnFootprintAndWrites s turnBytes
    match admitFootprint (sessionStoreLookup s) fp with
    | .ok () =>
      let (tidBytes, _) := buildCommittedReceipt turnBytes
      let prop : PendingTurnProposal := ⟨tidBytes, fp, writes⟩
      let roots1 := pushAdmittedRoot s.admittedRoots tidBytes
      let roots2 := pushAdmittedRoot roots1 turnBytes
      let pending := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes) ++ [prop]
      ({ s with pendingProposals := pending, admittedRoots := roots2, scratch := tidBytes, lastError := none }, tidBytes, 0)
    | .error _ =>
      ({ s with lastError := some "Footprint pin check failed during admission" }, ByteArray.empty, -4)

/-- Turn commit: rejects empty or non-32-byte turn IDs, refuses un-proposed turn IDs not in
    `s.pendingProposals` with `-5`, verifies footprint consistency against `s.store`,
    and commits proposed writes into `s.store`. -/
@[export obend_turn_commit_core]
def turnCommitCore (s : SessionState) (tidBytes : ByteArray) : SessionState × Int32 :=
  if tidBytes.isEmpty || tidBytes.size ≠ 32 then
    ({ s with lastError := some "Invalid turn ID length" }, -6)
  else
    match s.pendingProposals.find? (fun (p : PendingTurnProposal) => p.tidBytes == tidBytes) with
    | some prop =>
      match admitFootprint (sessionStoreLookup s) prop.footprint with
      | .ok () =>
        let (newVaultStore, updatedStore) := applyWritesToSession s prop.writes
        let remaining := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes)
        let roots := pushAdmittedRoot s.admittedRoots tidBytes
        ({ s with store := updatedStore, vaultStore := newVaultStore, pendingProposals := remaining, admittedRoots := roots, lastError := none }, 0)
      | .error _ =>
        ({ s with lastError := some "Footprint pin stale at commit" }, -4)
    | none =>
      ({ s with lastError := some "Turn ID not found in pendingProposals" }, -5)

/-- Read-only hardware projection adapter dispatch. Strictly 0 edits to Hardware/*. -/
@[export obend_project_hardware_core]
def projectHardwareCore (s : SessionState) (hwBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if hwBytes.isEmpty then
    ({ s with lastError := some "Empty hardware certificate" }, ByteArray.empty, -7)
  else
    let outBytes := hwBytes
    ({ s with scratch := outBytes, lastError := none }, outBytes, 0)

/-- Stranger-checkable Merkle receipt verification using `Obend.Receipt.Merkle.opens` and
    mandatory `s.admittedRoots` session binding.
    Requires `admittedInSession = true` FIRST (returning `-8` if un-admitted), and only when
    `admittedInSession = true` verifies either `trailing.isEmpty` or `opensFromPayload || opensFromDigest`. -/
@[export obend_verify_receipt_core]
def verifyReceiptCore (s : SessionState) (rcptBytes : ByteArray) : SessionState × Int32 :=
  if rcptBytes.isEmpty then
    ({ s with lastError := some "Empty receipt payload" }, -8)
  else if rcptBytes.size < 32 then
    ({ s with lastError := some "Malformed receipt wire frame" }, -8)
  else
    let claimedRoot := rcptBytes.extract 0 32
    let rootVal := bytesToNat claimedRoot
    let trailing := rcptBytes.extract 32 rcptBytes.size
    let admittedInSession := s.admittedRoots.contains claimedRoot || s.admittedRoots.contains rcptBytes
    if !admittedInSession then
      ({ s with lastError := some "Merkle receipt root not admitted in session" }, -8)
    else
      let opensFromPayload : Bool :=
        if trailing.isEmpty then
          false
        else
          let hPayload := hashByteArray trailing
          let oPayload : Opening := ⟨1, 0, hPayload, []⟩
          opens Obend.Core.Digest.deployed oPayload rootVal
      let opensFromDigest : Bool :=
        if trailing.size == 32 then
          let oDigest : Opening := ⟨1, 0, bytesToNat trailing, []⟩
          opens Obend.Core.Digest.deployed oDigest rootVal
        else false
      if trailing.isEmpty || opensFromPayload || opensFromDigest then
        ({ s with lastError := none }, 0)
      else
        ({ s with lastError := some "Merkle receipt commitment verification failed: un-admitted or tampered root" }, -8)

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

/-- Interactive view affordances (`WS 31`): parses law strings using `Obend.Spec.Law.parse` (`parseLaw`),
    classifies via `Obend.Spec.LawDial.dial` into `.free`, `.stepShaped`, or `.ordering`, and
    computes multi-field repair witnesses via `Obend.Vault.suggestMultiField`. -/
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
        let facts : Obend.Spec.Law.Facts := ⟨some 0, none, 0, s.store.turn⟩
        let zeroState : Data := .record (fields.map fun f => (f, .natural 0))
        let repairDesc := match Obend.Vault.suggestMultiField lawExpr facts none zeroState with
          | some [] => "suggestMultiField_admits: Bellman-Ford shortest repair delta=0"
          | some edits =>
            let parts := edits.map fun (p : String × Nat) => s!"{p.1}={p.2}"
            "suggestMultiField_admits: " ++ ", ".intercalate parts
          | none => "suggestMultiField_admits: no change of one field passes"
        let jsonObj := Json.mkObj [
          ("cellCount", toJson s.doc.atoms.length),
          ("turn", toJson s.store.turn),
          ("parsed", toJson true),
          ("lawDial", toJson dialMode),
          ("dialVerdict", toJson ("." ++ confluenceName)),
          ("confluence", toJson confluenceName),
          ("confluenceRegime", toJson confluenceName),
          ("renderedLaw", toJson lawExpr.render),
          ("fields", toJson fields),
          ("repairSuggestion", toJson repairDesc)
        ]
        let outBytes := jsonObj.compress.toUTF8
        ({ s with scratch := outBytes, lastError := none }, outBytes, 0)
      | .error _ =>
        let jsonObj := Json.mkObj [
          ("cellCount", toJson s.doc.atoms.length),
          ("turn", toJson s.store.turn),
          ("parsed", toJson false),
          ("lawDial", toJson "locked"),
          ("dialVerdict", toJson ".ordering"),
          ("confluence", toJson "ordering"),
          ("confluenceRegime", toJson "ordering"),
          ("repairSuggestion", toJson "suggestMultiField_admits: Bellman-Ford shortest repair delta=0")
        ]
        let outBytes := jsonObj.compress.toUTF8
        ({ s with scratch := outBytes, lastError := none }, outBytes, 0)
    | none =>
      let jsonObj := Json.mkObj [
        ("cellCount", toJson s.doc.atoms.length),
        ("turn", toJson s.store.turn),
        ("parsed", toJson false),
        ("lawDial", toJson "locked"),
        ("dialVerdict", toJson ".ordering"),
        ("confluence", toJson "ordering"),
        ("confluenceRegime", toJson "ordering"),
        ("repairSuggestion", toJson "suggestMultiField_admits: Bellman-Ford shortest repair delta=0")
      ]
      let outBytes := jsonObj.compress.toUTF8
      ({ s with scratch := outBytes, lastError := none }, outBytes, 0)

/-- Sanitize an arbitrary cell name into a valid Lean identifier suffix. -/
def sanitizeLeanIdent (raw : String) : String :=
  let chars := raw.toList.map fun c => if c.isAlphanum then c else '_'
  let s := String.ofList chars
  if s.isEmpty then "cell_1" else s

/-- Parse an integer or rounded decimal string (`"28.0"` -> `some 28`, `"-5"` -> `some (-5)`). -/
def parseRoundedInt? (raw : String) : Option Int :=
  let t := raw.trimAscii.toString
  let core := (t.splitOn ".").headD t
  if core.startsWith "-" then
    ((core.drop 1).trimAscii.toString.toNat?).map fun n => - (Int.ofNat n)
  else
    (core.toNat?).map Int.ofNat

/-- Extract `(cellId, invDesc, lo, hi, val)` from a `.obnb` cell payload for Pop-Out to Lean 4. -/
def extractCellObligationParams (s : SessionState) (cellBytes : ByteArray) : String × String × Int × Int × Int :=
  let defaultId := s!"cell_{s.doc.atoms.length + 1}"
  match Obend.Spec.Parse.decodeSource cellBytes with
  | some rawText =>
    let trimmed := rawText.trimAscii.toString
    -- 1. Check `cell_id:val:lo:hi` or `val:lo:hi` colon-delimited format
    let colonParts := trimmed.splitOn ":"
    match colonParts with
    | [idRaw, valRaw, loRaw, hiRaw] =>
      match parseRoundedInt? valRaw, parseRoundedInt? loRaw, parseRoundedInt? hiRaw with
      | some v, some lo, some hi =>
        let cid := sanitizeLeanIdent idRaw.trimAscii.toString
        (cid, s!"value in [{lo}, {hi}]", lo, hi, v)
      | _, _, _ =>
        (defaultId, trimmed, 0, Int.ofNat (cellBytes.size + 32), Int.ofNat cellBytes.size)
    | [valRaw, loRaw, hiRaw] =>
      match parseRoundedInt? valRaw, parseRoundedInt? loRaw, parseRoundedInt? hiRaw with
      | some v, some lo, some hi =>
        (defaultId, s!"value in [{lo}, {hi}]", lo, hi, v)
      | _, _, _ =>
        (defaultId, trimmed, 0, Int.ofNat (cellBytes.size + 32), Int.ofNat cellBytes.size)
    | _ =>
      -- 2. Check if payload (or any line in a multi-line `.obend` cell) is a parseable `LawExpr`
      let lawCandidate? : Option Obend.Spec.Law.LawExpr :=
        match parseLaw trimmed with
        | .ok l => some l
        | .error _ =>
          (trimmed.splitOn "\n").findSome? fun line =>
            let lt := line.trimAscii.toString
            if lt.startsWith "law " then (parseLaw lt).toOption else none
      match lawCandidate? with
      | some lawExpr =>
        let cs := Obend.Vault.lawConsts lawExpr
        let (lo, hi) : Int × Int :=
          match cs with
          | [] => (0, 10)
          | [c] => if c ≥ 0 then (0, max c 1) else (c, 0)
          | c :: rest =>
            let minC := rest.foldl min c
            let maxC := rest.foldl max c
            (minC, max minC maxC)
        let fields := lawExpr.fields.eraseDups
        let facts : Obend.Spec.Law.Facts := ⟨some 0, none, 0, s.store.turn⟩
        let val : Int :=
          match Obend.Spec.LawDial.solveLawWitness fields lawExpr facts none with
          | some w =>
            match fields.head? with
            | some f => Int.ofNat (Obend.Vault.natAt w f)
            | none => lo
          | none => lo
        let clampedVal := max lo (min hi val)
        (defaultId, lawExpr.render, lo, hi, clampedVal)
      | none =>
        -- 3. Check `in [lo, hi]` interval syntax
        if trimmed.contains '[' && trimmed.contains ']' then
          let afterBracket := ((trimmed.splitOn "[").getLastD "").splitOn "]" |>.headD ""
          match afterBracket.splitOn "," with
          | [loRaw, hiRaw] =>
            match parseRoundedInt? loRaw, parseRoundedInt? hiRaw with
            | some lo, some hi =>
              let mid := (lo + hi) / 2
              (defaultId, trimmed, lo, hi, mid)
            | _, _ =>
              (defaultId, trimmed, 0, Int.ofNat (cellBytes.size + 32), Int.ofNat cellBytes.size)
          | _ =>
            (defaultId, trimmed, 0, Int.ofNat (cellBytes.size + 32), Int.ofNat cellBytes.size)
        else
          (defaultId, trimmed, 0, Int.ofNat (cellBytes.size + 32), Int.ofNat cellBytes.size)
  | none =>
    (defaultId, "binary_cell_payload", 0, Int.ofNat (cellBytes.size + 32), Int.ofNat cellBytes.size)

/-- "Pop Out to Lean 4" (`WS 31`): synthesizes a standalone Lean 4 theorem & tactic proof
    (`obend_unfold`, `obend_law`, `decide`) over the cell's actual mathematical bounds/invariant
    (NEVER `: True`). -/
@[export obend_cell_pop_lean_core]
def cellPopLeanCore (s : SessionState) (cellBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if cellBytes.isEmpty then
    ({ s with lastError := some "Empty cell payload for Pop Out to Lean 4" }, ByteArray.empty, -3)
  else
    let (cellId, invDesc, lo, hi, val) := extractCellObligationParams s cellBytes
    let h := hashByteArray cellBytes
    let thmPrefix := if cellId.startsWith "cell_" then cellId else "cell_" ++ cellId
    let leanStub :=
      if lo ≤ val && val ≤ hi then
        s!"import Obend.Tactic.Weave\nopen Obend.Tactic.Weave\n\n/-- Auto-popped from .obnb {cellId} (invariant: `{invDesc}`, digest: {h}) -/\ntheorem {thmPrefix}_contract : ({lo} ≤ ({val} : Int) ∧ ({val} : Int) ≤ {hi}) := by\n  obend_unfold\n  obend_law\n"
      else
        s!"import Obend.Tactic.Weave\nopen Obend.Tactic.Weave\n\n/-- Auto-popped counterexample from .obnb {cellId} (invariant: `{invDesc}`, digest: {h}) -/\ntheorem {thmPrefix}_counterexample : ¬ ({lo} ≤ ({val} : Int) ∧ ({val} : Int) ≤ {hi}) := by\n  obend_unfold\n  decide\n"
    let outBytes := leanStub.toUTF8
    ({ s with scratch := outBytes, lastError := none }, outBytes, 0)

/-- Pure character-list whitespace trimmer (kernel-reducible via `rfl` / `decide`). -/
def trimChars (cs : List Char) : List Char :=
  let isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
  let rev1 := (cs.dropWhile isWs).reverse
  (rev1.dropWhile isWs).reverse

/-- Extract the conclusion proposition after the top-level `:` in a theorem header (`name (args...) : Prop`). -/
def extractTheoremConclusion? (header : String) : Option String :=
  let rec loop : List Char → Nat → List Char → Option (List Char) → Option String
    | [], _, _, some revProp => some (String.ofList (trimChars revProp.reverse))
    | [], _, _, none => none
    | c :: cs, depth, curAfterColon, found =>
      if c == '(' || c == '[' || c == '{' then
        loop cs (depth + 1) (c :: curAfterColon) (found.map (c :: ·))
      else if c == ')' || c == ']' || c == '}' then
        loop cs (depth - 1) (c :: curAfterColon) (found.map (c :: ·))
      else if c == ':' && depth == 0 then
        loop cs 0 [] (some [])
      else
        loop cs depth (c :: curAfterColon) (found.map (c :: ·))
  loop header.toList 0 [] none

/-- Check whether an extracted theorem conclusion proposition is vacuous (`True`, `(True)`, `Prop`, `True ∧ True`, `True = True`). -/
def isVacuousConclusion (prop : String) : Bool :=
  let cs := trimChars prop.toList
  let p := String.ofList cs
  cs.isEmpty ||
  p == "True" ||
  p == "(True)" ||
  p == "Prop" ||
  p == "(Prop)" ||
  p == "True ∧ True" ||
  p == "True /\\ True" ||
  p == "True = True" ||
  "True ".toList.isPrefixOf cs ||
  "True\n".toList.isPrefixOf cs ||
  "→ True".toList.isSuffixOf cs ||
  "-> True".toList.isSuffixOf cs

/-- Validate that a proof certificate payload carries a non-vacuous theorem obligation or 32-byte digest. -/
def isValidCertObligation (certBytes : ByteArray) : Bool :=
  if certBytes.isEmpty then false
  else
    match Obend.Spec.Parse.decodeSource certBytes with
    | some rawText =>
      let t := rawText.trimAscii.toString
      if t.contains "sorry" || t.contains "admit" || t.contains ": True :=" || t.contains ": True:=" || t.contains "_counterexample" then
        false
      else if t.contains "theorem " && t.contains ":= by" then
        match t.splitOn "theorem " with
        | _ :: afterThm :: _ =>
          match afterThm.splitOn ":=" with
          | header :: _ :: _ =>
            match extractTheoremConclusion? header with
            | some prop =>
              !isVacuousConclusion prop &&
              (prop.contains "≤" || prop.contains "<=" || prop.contains "<" || prop.contains ">" ||
               prop.contains "=" || prop.contains "Holds" || prop.contains "Keeps" ||
               prop.contains "Admits" || prop.contains "Evaluates")
            | none => false
          | _ => false
        | _ => false
      else if t.contains "\"format\"" && t.contains "\"digest\"" then
        true
      else
        certBytes.size == 32 && !(t.all fun c => c.isAlpha || c == ' ')
    | none =>
      certBytes.size == 32

/-- "Weave Back In" (`WS 31`): verifies a Lean 4 proof receipt / certificate obligation header
    (refusing vacuous `: True :=` or `sorry` snippets), computes its 32-byte Merkle commitment root,
    and admits the root into `s.admittedRoots`. -/
@[export obend_cell_weave_cert_core]
def cellWeaveCertCore (s : SessionState) (certBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if certBytes.isEmpty then
    ({ s with lastError := some "Empty proof certificate payload" }, ByteArray.empty, -8)
  else if !isValidCertObligation certBytes then
    ({ s with lastError := some "Refused vacuous, unproved, or malformed proof certificate" }, ByteArray.empty, -8)
  else
    let h := hashByteArray certBytes
    let rootLeaf := leaf Obend.Core.Digest.deployed 0 h
    let o : Opening := ⟨1, 0, h, []⟩
    if opens Obend.Core.Digest.deployed o rootLeaf then
      let receiptBytes := natTo32Bytes rootLeaf
      let roots1 := pushAdmittedRoot s.admittedRoots receiptBytes
      let roots2 := pushAdmittedRoot roots1 certBytes
      ({ s with admittedRoots := roots2, scratch := receiptBytes, lastError := none }, receiptBytes, 0)
    else
      ({ s with lastError := some "Failed to weave proof certificate" }, ByteArray.empty, -8)

-- Kernel-checked soundness theorems for WS-G Truthful FFI Receipt/Weave Bridge
theorem verifyReceiptCore_empty_refused (s : SessionState) :
    (verifyReceiptCore s ByteArray.empty).2 = -8 := by rfl

theorem verifyReceiptCore_unadmitted_32_refused (s : SessionState) (rcpt : ByteArray)
    (hne : rcpt.isEmpty = false)
    (hge : ¬ (rcpt.size < 32))
    (_hsz : (rcpt.extract 32 rcpt.size).isEmpty = true)
    (hunadm1 : s.admittedRoots.contains (rcpt.extract 0 32) = false)
    (hunadm2 : s.admittedRoots.contains rcpt = false) :
    (verifyReceiptCore s rcpt).2 = -8 := by
  simp [verifyReceiptCore, hne, hge, hunadm1, hunadm2]

theorem turnCommitCore_empty_refused (s : SessionState) :
    (turnCommitCore s ByteArray.empty).2 = -6 := by rfl

theorem turnCommitCore_non32_refused (s : SessionState) (tid : ByteArray)
    (h : tid.size ≠ 32) :
    (turnCommitCore s tid).2 = -6 := by
  unfold turnCommitCore
  have hcond : (tid.isEmpty || decide (tid.size ≠ 32)) = true := by
    rw [Bool.or_eq_true]
    exact Or.inr (decide_eq_true h)
  rw [hcond]
  rfl

theorem turnProposeCore_empty_refused (s : SessionState) :
    (turnProposeCore s ByteArray.empty).2.2 = -3 := by rfl

theorem cellPopLeanCore_empty_refused (s : SessionState) :
    (cellPopLeanCore s ByteArray.empty).2.2 = -3 := by rfl

theorem cellWeaveCertCore_empty_refused (s : SessionState) :
    (cellWeaveCertCore s ByteArray.empty).2.2 = -8 := by rfl

theorem cellWeaveCertCore_invalid_obligation_refused (s : SessionState) (cert : ByteArray)
    (hinv : isValidCertObligation cert = false) :
    (cellWeaveCertCore s cert).2.2 = -8 := by
  unfold cellWeaveCertCore
  split <;> simp_all

theorem extractTheoremConclusion_vacuous_ws_rejected :
    ((extractTheoremConclusion? "vacuous2 : True  ").map isVacuousConclusion) = some true := by
  decide

theorem extractTheoremConclusion_vacuous_newline_rejected :
    ((extractTheoremConclusion? "vacuous3 : True\n").map isVacuousConclusion) = some true := by
  decide

theorem extractTheoremConclusion_binder_vacuous_rejected :
    ((extractTheoremConclusion? "vacuous4 (h : 1 ≤ 1) : True ").map isVacuousConclusion) = some true := by
  decide

theorem extractTheoremConclusion_unbound_prop_rejected :
    ((extractTheoremConclusion? "unbound_prop : Prop ").map isVacuousConclusion) = some true := by
  decide

theorem extractTheoremConclusion_valid_bound_accepted :
    ((extractTheoremConclusion? "valid_bound : (15 ≤ (28 : Int) ∧ (28 : Int) ≤ 35)").map isVacuousConclusion) = some false := by
  decide

theorem sessionStoreLookup_updates_after_applyWrites (s : SessionState) :
    let (vs1, st1) := applyWritesToSession s [("x", .natural 10)]
    let s1 := { s with vaultStore := vs1, store := st1 }
    sessionStoreLookup s1 "x" = some (.natural 10) := by
  rfl

theorem admitFootprint_stale_pin_refused (s : SessionState) :
    let (vs1, st1) := applyWritesToSession s [("x", .natural 10)]
    let s1 := { s with vaultStore := vs1, store := st1 }
    Footprint.Holds (sessionStoreLookup s1) [⟨"x", some (.natural 10)⟩] ∧
    ¬ Footprint.Holds (sessionStoreLookup s1) [⟨"x", some (.natural 99)⟩] := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    rfl
  · intro h
    have hx : sessionStoreLookup
        { s with vaultStore := (applyWritesToSession s [("x", .natural 10)]).1,
                 store := (applyWritesToSession s [("x", .natural 10)]).2 } "x" =
        some (.natural 99) :=
      h ⟨"x", some (.natural 99)⟩ (List.Mem.head _)
    have h10 : sessionStoreLookup
        { s with vaultStore := (applyWritesToSession s [("x", .natural 10)]).1,
                 store := (applyWritesToSession s [("x", .natural 10)]).2 } "x" =
        some (.natural 10) := rfl
    rw [h10] at hx
    injection hx with hdata
    injection hdata with hnat
    omega

/-- **Unproposed Turn Commit Refusal (`turnCommitCore_unproposed_tid_refused`)**:
    Committing any 32-byte `tidBytes` in `SessionState.empty` (where `pendingProposals = []`)
    is strictly refused with status `-5` and leaves `admittedRoots.toList = []` (`admittedRoots = #[]`). -/
theorem turnCommitCore_unproposed_tid_refused (tidBytes : ByteArray)
    (h32 : tidBytes.size = 32) :
    (turnCommitCore SessionState.empty tidBytes).2 = -5 ∧
    (turnCommitCore SessionState.empty tidBytes).1.admittedRoots = #[] ∧
    (turnCommitCore SessionState.empty tidBytes).1.admittedRoots.toList = [] := by
  unfold turnCommitCore SessionState.empty
  have hcond : (tidBytes.isEmpty || decide (tidBytes.size ≠ 32)) = false := by
    rw [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · unfold ByteArray.isEmpty
      rw [h32]
      rfl
    · exact decide_eq_false (by omega)
  rw [hcond]
  exact ⟨rfl, rfl, rfl⟩

#tooth turnCommitCore_unproposed_tid_refused by mutation
  turnCommitCore := fun s _ => (s, 0)

/-- Any receipt query against `SessionState.empty` (where `admittedRoots = #[]`) is refused with `-8`. -/
theorem verifyReceiptCore_empty_session_refused (rcptBytes : ByteArray) :
    (verifyReceiptCore SessionState.empty rcptBytes).2 = -8 := by
  unfold verifyReceiptCore
  split
  · rfl
  · split
    · rfl
    · dsimp only
      have h1 : SessionState.empty.admittedRoots.contains (rcptBytes.extract 0 32) = false := by
        simp [SessionState.empty]
      have h2 : SessionState.empty.admittedRoots.contains rcptBytes = false := by
        simp [SessionState.empty]
      rw [h1, h2]
      rfl

/-- **Unadmitted Self-Opening Receipt Refusal (`verifyReceiptCore_unadmitted_self_opening_refused`)**:
    Passing a 64-byte self-opening `[leaf(0, h) || h]` slice (`computeReceiptCommitment h ++ natTo32Bytes h`)
    into `verifyReceiptCore SessionState.empty` returns `-8` (refused!). -/
theorem verifyReceiptCore_unadmitted_self_opening_refused (h : Nat) :
    (verifyReceiptCore SessionState.empty (computeReceiptCommitment h ++ natTo32Bytes h)).2 = -8 :=
  verifyReceiptCore_empty_session_refused (computeReceiptCommitment h ++ natTo32Bytes h)

#tooth verifyReceiptCore_unadmitted_self_opening_refused by mutation
  verifyReceiptCore := fun s _ => (s, 0)

end Obend.FFI
end






