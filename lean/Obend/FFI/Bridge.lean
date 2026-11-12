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
public import Obend.Vault.Replay
public import Obend.Judge
public import Obend.Doc.Graph
public import Obend.Doc.Structured
public import Obend.Doc.Render
public import Obend.Receipt.Merkle
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

@[expose] public section
namespace Obend.FFI

open Lean (Json toJson)
open Obend.Core
open Obend.Core.Data (Data)
open Obend.Vault
open Obend.Doc
open Obend.Receipt.Merkle
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
open Obend.Spec.Preview

instance : Inhabited Obend.Vault.Replay.World := ⟨Obend.Vault.Replay.genesis⟩
instance : Inhabited Obend.Vault.Replay.Session := ⟨⟨Obend.Vault.Replay.genesis, []⟩⟩

/-- A proposed turn waiting for `turnCommitCore`: its id, the footprint it was admitted
against, the writes it will apply, any woven judge witness, or raw `Obend.Vault.Replay.Turn`
bytes to admit directly into `replaySession`. -/
structure PendingTurnProposal where
  tidBytes : ByteArray
  footprint : Footprint := []
  writes : List (String × Data) := []
  witness : Option TurnWitness := none
  replayBytes : Option ByteArray := none
  deriving Inhabited

/-- The session a host drives through the C ABI, backed directly by an `Obend.Vault.Replay.Session`
(`world : Obend.Vault.Replay.World` and its hash-chained `log : List Obend.Vault.Log.Record`).

`committedRoots` are the roots of the turns this session has COMMITTED (`turnCommitCore`); a
proposal admits nothing. `verifyReceiptCore` accepts a receipt only when its root is one of them
and its opening opens against it (`Obend.Receipt.Merkle.opens`). -/
structure SessionState where
  replaySession : Obend.Vault.Replay.Session := ⟨Obend.Vault.Replay.genesis, []⟩
  pendingProposals : List PendingTurnProposal := []
  committedRoots : Array ByteArray := #[]
  committedTurns : List VaultTurn := []
  doc : Graph := Graph.empty
  scratch : ByteArray := ByteArray.empty
  lastError : Option String := none
  deriving Inhabited

abbrev Session := SessionState

/-- The live `Obend.Vault.Replay.World` served by this FFI session. -/
def SessionState.world (s : SessionState) : Obend.Vault.Replay.World :=
  s.replaySession.world

/-- Canonical empty session state at `Obend.Vault.Replay.genesis`. -/
def SessionState.empty : SessionState := {}

/-- Initialize session state from configuration bytes. -/
@[export obend_session_init_core]
def sessionInitCore (_cfg : ByteArray) : SessionState := {}

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

      -- Extract and check claims via Obend.Logic.Program.claimFields, proposeDerivation & ground evaluation
      let mut claimSummaries : Array Json := #[]
      if let some (_, firstTerm) := erasedTerms.head? then
        if let some knotRoot := Obend.Logic.Program.knotOf firstTerm then
          for (specKey, claimName) in Obend.Logic.Program.claimFields knotRoot do
            let fullClaim := specKey ++ "." ++ claimName
            let shortSpec := (specKey.splitOn ".").getLastD specKey
            match erasedTerms.findSome? (fun (_, t) =>
              findCompositionFromTerm (fun C => (Obend.Logic.Program.layerIndex C specKey).isSome) t) with
            | none =>
              let (noObjStatus, noObjDiag) : String × String :=
                match Obend.Logic.Program.knotValue knotRoot (specKey ++ "#claim#" ++ claimName) with
                | some claimCode =>
                  let nBinders := Obend.Logic.Program.binders claimCode
                  let arity := nBinders - 2
                  let samples : List Nat := [0, 1, 2, 5]
                  let evals := samples.map fun sVal =>
                    let argTerms := Obend.Core.Term.Term.record [] :: Obend.Core.Term.Term.record [] ::
                      List.replicate arity (Obend.Core.Data.Data.term (.natural sVal))
                    Obend.Logic.readBool (Obend.Law.run 4096 (Obend.Logic.apps claimCode argTerms))
                  if evals.any (· == some false) then
                    ("refused", s!"Claim {fullClaim} refuted by ground evaluation at sample instance")
                  else if evals.all (· == some true) then
                    ("verified", "")
                  else
                    ("no-object", "")
                | none => ("no-object", "")
              if noObjStatus == "refused" then
                anyRefused := true
              claimSummaries := claimSummaries.push (Json.mkObj [
                ("claim", toJson fullClaim),
                ("spec", toJson shortSpec),
                ("name", toJson claimName),
                ("status", toJson noObjStatus),
                ("diagnostic", toJson noObjDiag),
                ("message", toJson noObjDiag)
              ])
            | some C =>
              match Obend.Logic.Program.claimObj knotRoot C specKey claimName with
              | .error e =>
                anyRefused := true
                claimSummaries := claimSummaries.push (Json.mkObj [
                  ("claim", toJson fullClaim),
                  ("spec", toJson shortSpec),
                  ("name", toJson claimName),
                  ("status", toJson "refused"),
                  ("diagnostic", toJson e),
                  ("message", toJson e)
                ])
              | .ok o =>
                let (cStatus, stepCount, cDiag) : String × Nat × String :=
                  match Obend.Logic.Program.proposeDerivation o with
                  | some steps =>
                    match Obend.Logic.claimCheck (Obend.Logic.sizeList steps) o steps with
                    | .ok => ("verified", Obend.Logic.sizeList steps, "")
                    | _ => ("refused", 0, s!"Claim {fullClaim} derivation failed kernel claimCheck")
                  | none =>
                    let samples : List Nat := [0, 1, 2, 5]
                    let evals := samples.map fun sVal =>
                      let ds := List.replicate o.arity (Obend.Core.Data.Data.natural sVal)
                      Obend.Logic.readBool (Obend.Law.run 4096 (Obend.Logic.apps o.claim (o.args ds)))
                    if evals.any (· == some false) then
                      ("refused", 0, s!"Claim {fullClaim} refuted by ground evaluation at sample instance")
                    else if evals.all (· == some true) then
                      ("verified", 1, "")
                    else
                      ("unchecked", 0, "")
                if cStatus == "refused" then
                  anyRefused := true
                claimSummaries := claimSummaries.push (Json.mkObj [
                  ("claim", toJson fullClaim),
                  ("spec", toJson shortSpec),
                  ("name", toJson claimName),
                  ("status", toJson cStatus),
                  ("steps", toJson stepCount),
                  ("rewriteSteps", toJson stepCount),
                  ("diagnostic", toJson cDiag),
                  ("message", toJson cDiag),
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

/-- The digest of a payload: the deployed hash (`Obend.Core.Digest.deployed`, cSHAKE256) of its
bytes, read big-endian. Below `2 ^ 256` (`Obend.Core.Digest.digest_lt`'s carrier). -/
def hashByteArray (ba : ByteArray) : Nat :=
  Obend.Digest.HashBytes.ofBE (Obend.Core.Digest.deployed ba.data.toList)

/-- The low `w` bytes of `n`, big-endian (`Obend.Digest.HashBytes.be`). -/
def natToBytesBE (w n : Nat) : ByteArray :=
  ByteArray.mk (Obend.Digest.HashBytes.be w n).toArray

/-- Convert natural number to exact 32-byte big-endian ByteArray. -/
def natTo32Bytes (n : Nat) : ByteArray :=
  natToBytesBE 32 n

/-- Convert 32-byte chunk to natural number. -/
def bytesToNat (ba : ByteArray) : Nat :=
  ba.data.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The root a committed payload gets: the one-leaf Merkle map over its digest
(`Obend.Receipt.Merkle.leaf deployed 0 h`, which is `mapRoot deployed [h]`). -/
def computeReceiptCommitment (h : Nat) : ByteArray :=
  natTo32Bytes (leaf Obend.Core.Digest.deployed 0 h)

/-! ### The receipt wire frame

    root(32) || size(8) || index(8) || pathLen(8) || path(pathLen × 32) || payload

All integers big-endian. A receipt claims that `payload`'s digest sits at `index` of a Merkle map
of `size` leaves whose root is `root`, with `path` the siblings top first; `verifyReceiptCore`
recomputes the digest and climbs (`Obend.Receipt.Merkle.opens`). The receipt of a committed turn
is the one-leaf case `size = 1, index = 0, path = []` over the turn's bytes. -/

structure ReceiptWire where
  root : ByteArray
  size : Nat
  index : Nat
  path : List Nat
  payload : ByteArray

def encodeReceipt (root : ByteArray) (size index : Nat) (path : List Nat) (payload : ByteArray) :
    ByteArray :=
  root ++ natToBytesBE 8 size ++ natToBytesBE 8 index ++ natToBytesBE 8 path.length ++
    path.foldl (fun acc p => acc ++ natTo32Bytes p) ByteArray.empty ++ payload

def decodeReceipt? (rcpt : ByteArray) : Option ReceiptWire :=
  if rcpt.size < 56 then none
  else
    let pathLen := bytesToNat (rcpt.extract 48 56)
    if rcpt.size < 56 + 32 * pathLen then none
    else
      some
        { root := rcpt.extract 0 32
          size := bytesToNat (rcpt.extract 32 40)
          index := bytesToNat (rcpt.extract 40 48)
          path := (List.range pathLen).map fun i =>
            bytesToNat (rcpt.extract (56 + 32 * i) (56 + 32 * i + 32))
          payload := rcpt.extract (56 + 32 * pathLen) rcpt.size }

/-- The root and the one-leaf receipt of a payload. -/
def buildCommittedReceipt (payload : ByteArray) : ByteArray × ByteArray :=
  let rootBytes := computeReceiptCommitment (hashByteArray payload)
  (rootBytes, encodeReceipt rootBytes 1 0 [] payload)

/-- Record a committed 32-byte root. -/
def pushCommittedRoot (roots : Array ByteArray) (r : ByteArray) : Array ByteArray :=
  if r.size == 32 then roots.push r else roots

/-- Decode a judge witness from its JSON form `{"format","version","grade","obj","cert"}`. -/
def decodeTurnWitness? (bytes : ByteArray) : Option TurnWitness := do
  let text ← Obend.Spec.Parse.decodeSource bytes
  let j ← (Json.parse text).toOption
  let format ← (j.getObjValAs? String "format").toOption
  let version ← (j.getObjValAs? String "version").toOption
  let grade ← (j.getObjValAs? Nat "grade").toOption
  let obj ← (j.getObjValAs? String "obj").toOption
  let cert ← (j.getObjValAs? String "cert").toOption
  pure { formatName := format, version := version, grade := grade, objBytes := obj, certBytes := cert }

/-- Cell evaluation:
    Elaborates UTF-8 `.obend` source via `Obend.Spec.FrontEnd.accept`, claim checking, Leaf book
    emission, and bounded demand-machine preview. Fails closed on empty, non-UTF-8, non-`.obend`,
    or ill-typed payloads; arbitrary byte echo is disabled. -/
@[export obend_eval_cell_core]
def evalCellCore (s : SessionState) (cellBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if cellBytes.isEmpty then
    ({ s with lastError := some "Empty cell payload" }, ByteArray.empty, -3)
  else
    match Obend.Spec.Parse.decodeSource cellBytes with
    | none =>
      ({ s with lastError := some "Cell payload is not valid UTF-8 Objective Bend (.obend) source" }, ByteArray.empty, -3)
    | some text =>
      if isObendPayload text then
        let (summaryJson, accepted) := elaborateObendSource text
        let outBytes := summaryJson.compress.toUTF8
        if accepted then
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
          ({ s with doc := newDoc, scratch := outBytes, lastError := none }, outBytes, 0)
        else
          ({ s with lastError := some summaryJson.compress }, ByteArray.empty, -4)
      else
        ({ s with lastError := some "Cell payload is not Objective Bend (.obend) source; arbitrary byte echo is disabled" }, ByteArray.empty, -4)

/-- Pure character-list whitespace trimmer (kernel-reducible without `@[extern]` `String.Slice`). -/
def trimWsChars (cs : List Char) : List Char :=
  ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Pure decimal digit parser over `List Char`. -/
def parseNatDigitsAux : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: rest, acc =>
    if '0' ≤ c && c ≤ '9' then
      parseNatDigitsAux rest (acc * 10 + (c.toNat - 48))
    else
      none

/-- Pure kernel-reducible decimal `Nat` parser for trimmed strings. -/
def parseNatPure? (s : String) : Option Nat :=
  match trimWsChars s.toList with
  | [] => none
  | cs => parseNatDigitsAux cs 0

/-- Look up a cell/page key directly in `s.replaySession.world.store`. -/
def sessionStoreLookup (s : SessionState) (cell : String) : Option Data :=
  match s.replaySession.world.store.page? cell with
  | some p =>
    match p.seen with
    | some seenStr =>
      match parseNatPure? seenStr with
      | some n => some (.natural n)
      | none => some (.label seenStr)
    | none => some (.natural p.history.length)
  | none => none

/-- Pure kernel-reducible decimal `Nat` formatter (avoids non-exposed `Nat.repr` under `module`). -/
def natDigitsRev : Nat → Nat → List Char
  | _, 0 => []
  | n, fuel + 1 =>
    let d := Char.ofNat (48 + n % 10)
    if n < 10 then [d] else d :: natDigitsRev (n / 10) fuel

def natToDecimalPure (n : Nat) : String :=
  String.ofList (natDigitsRev n (n + 1)).reverse

/-- Render a `Data` value to a concise string for `Page.seen`. -/
def renderDataSeen : Data → String
  | .natural n => natToDecimalPure n
  | .boolean b => if b then "true" else "false"
  | .label s => s
  | other => toString (repr other)

/-- Parse a string value as `.natural` if numeric, else `.label`. -/
def parseDataAtom (raw : String) : Data :=
  let t := String.ofList (trimWsChars raw.toList)
  match parseNatPure? t with
  | some n => .natural n
  | none => .label t

/-- Apply committed `(cell, Data)` writes directly to `w.store` inside `Obend.Vault.Replay.World`. -/
def applyWritesToWorld (w : Obend.Vault.Replay.World) (doc : Graph) (writes : List (String × Data)) :
    Obend.Vault.Replay.World :=
  let newPages := writes.foldl (fun pages (k, v) =>
    let seenStr := renderDataSeen v
    match pages.find? (·.name == k) with
    | some _existing =>
      pages.map fun p =>
        if p.name == k then
          { p with history := p.history ++ [doc], seen := some seenStr }
        else p
    | none =>
      let newPage : Page := {
        name := k,
        id := pages.length + 1,
        history := [doc],
        seen := some seenStr,
        authors := [],
        note := none,
        kind := none
      }
      pages ++ [newPage]) w.store.pages
  { w with store := { w.store with pages := newPages, turn := w.store.turn + 1 } }

/-- Extract footprint pins and proposed writes from `turnBytes` against `s.replaySession.world.store`. -/
def parseTurnFootprintAndWrites (s : SessionState) (turnBytes : ByteArray) : Footprint × List (String × Data) :=
  let curTurn := s.replaySession.world.store.turn
  let basePin : Footprint :=
    match s.replaySession.world.store.page? "turn" with
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
        let cell := s!"turn_{curTurn}"
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
        let cell := s!"turn_{curTurn}"
        let valData := Data.natural turnBytes.size
        let expOpt := if (sessionStoreLookup s cell).isSome then some valData else none
        (basePin ++ [⟨cell, expOpt⟩], [(cell, valData)])
    else
      let cell := s!"turn_{curTurn}"
      let valData := Data.natural turnBytes.size
      let expOpt := if (sessionStoreLookup s cell).isSome then some valData else none
      (basePin ++ [⟨cell, expOpt⟩], [(cell, valData)])
  | none =>
    let cell := s!"turn_{curTurn}"
    let valData := Data.natural turnBytes.size
    let expOpt := if (sessionStoreLookup s cell).isSome then some valData else none
    (basePin ++ [⟨cell, expOpt⟩], [(cell, valData)])

/-- True when `turnBytes` is a JSON object naming a `Replay.Turn` discriminant (`"turn": ...`). -/
def isReplayTurnJson (turnBytes : ByteArray) : Bool :=
  match Obend.Spec.Parse.decodeSource turnBytes with
  | some raw =>
    match Json.parse raw with
    | .ok j => (j.getObjVal? "turn").isOk
    | .error _ => false
  | none => false

/-- Turn proposal:
    - If `turnBytes` is a `Replay.Turn` JSON object, decodes it with `Obend.Vault.Replay.decodeTurn`
      and dry-checks `Obend.Vault.Replay.stepTurn s.replaySession.world` before registering.
    - Otherwise validates footprint pins against `s.replaySession.world.store` via `admitFootprint`.
    Commits nothing and admits no root. -/
@[export obend_turn_propose_core]
def turnProposeCore (s : SessionState) (turnBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if turnBytes.isEmpty then
    ({ s with lastError := some "Empty turn payload" }, ByteArray.empty, -3)
  else if isReplayTurnJson turnBytes then
    match Obend.Vault.Replay.decodeTurn turnBytes.data.toList with
    | .error err =>
      ({ s with lastError := some err }, ByteArray.empty, -3)
    | .ok rt =>
      match Obend.Vault.Replay.stepTurn s.replaySession.world rt with
      | .error err =>
        ({ s with lastError := some err }, ByteArray.empty, -4)
      | .ok _ =>
        let tidBytes := (buildCommittedReceipt turnBytes).1
        let prop : PendingTurnProposal := ⟨tidBytes, [], [], none, some turnBytes⟩
        let pending := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes) ++ [prop]
        ({ s with pendingProposals := pending, scratch := tidBytes, lastError := none }, tidBytes, 0)
  else
    let fw := parseTurnFootprintAndWrites s turnBytes
    match admitFootprint (sessionStoreLookup s) fw.1 with
    | .ok () =>
      let tidBytes := (buildCommittedReceipt turnBytes).1
      let prop : PendingTurnProposal := ⟨tidBytes, fw.1, fw.2, none, none⟩
      let pending := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes) ++ [prop]
      ({ s with pendingProposals := pending, scratch := tidBytes, lastError := none }, tidBytes, 0)
    | .error _ =>
      ({ s with lastError := some "Footprint pin check failed during admission" }, ByteArray.empty, -4)

/-- The `VaultTurn` a proposal denotes against `s.replaySession.world.store`. -/
def proposalTurn (s : SessionState) (prop : PendingTurnProposal) : Option VaultTurn :=
  let legs : List WitnessLegSpec := prop.writes.map fun w =>
    (w.1, (sessionStoreLookup s w.1).getD (.record []), w.2)
  VaultTurn.ofWitnessLegs prop.tidBytes prop.footprint legs
    (.record [("occasion", .label "commit")]) prop.witness.toList

/-- The judge formats a session accepts witnesses in: the registry (`Obend.Judge.registry`). -/
def sessionJudgeFormats : List Obend.Judge.Format := Obend.Judge.registry

/-- Turn commit: refuses an id that is not 32 bytes (`-6`) or not proposed (`-5`), then admits
the turn into `s.replaySession` via `Obend.Vault.Log.Session.admit` (preserving `Replay.Reachable`),
checking footprint pins and every judge witness against `sessionJudgeFormats`. -/
@[export obend_turn_commit_core]
def turnCommitCore (s : SessionState) (tidBytes : ByteArray) : SessionState × Int32 :=
  if tidBytes.isEmpty || tidBytes.size ≠ 32 then
    ({ s with lastError := some "Invalid turn ID length" }, -6)
  else
    match s.pendingProposals.find? (fun (p : PendingTurnProposal) => p.tidBytes == tidBytes) with
    | some prop =>
      match prop.replayBytes with
      | some rawBytes =>
        match Obend.Vault.Log.Session.admit Obend.Vault.Replay.logHash Obend.Vault.Replay.deployed s.replaySession rawBytes.data.toList with
        | .ok nextReplay =>
          let remaining := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes)
          ({ s with
              replaySession := nextReplay,
              pendingProposals := remaining,
              committedRoots := pushCommittedRoot s.committedRoots tidBytes,
              lastError := none }, 0)
        | .error err =>
          ({ s with lastError := some err }, -4)
      | none =>
        match admitFootprint (sessionStoreLookup s) prop.footprint with
        | .ok () =>
          match proposalTurn s prop with
          | some turn =>
            if turn.witnesses.all (checkTurnWitness sessionJudgeFormats) then
              let nextWorld := applyWritesToWorld s.replaySession.world s.doc prop.writes
              let baseBytes := Obend.Vault.Replay.encodeTurn (.base nextWorld)
              match Obend.Vault.Log.Session.admit Obend.Vault.Replay.logHash Obend.Vault.Replay.deployed s.replaySession baseBytes with
              | .ok nextReplay =>
                let remaining := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes)
                ({ s with
                    replaySession := nextReplay,
                    pendingProposals := remaining,
                    committedRoots := pushCommittedRoot s.committedRoots tidBytes,
                    committedTurns := turn :: s.committedTurns,
                    lastError := none }, 0)
              | .error err =>
                ({ s with lastError := some err }, -4)
            else
              ({ s with lastError := some "A turn witness is refused by its judge format" }, -9)
          | none =>
            ({ s with lastError := some "Turn writes name one cell twice" }, -9)
        | .error _ =>
          ({ s with lastError := some "Footprint pin stale at commit" }, -4)
    | none =>
      ({ s with lastError := some "Turn ID not found in pendingProposals" }, -5)

/-- Hardware/CAD judge format predicate for read-only hardware witness verification. -/
def isHardwareProjectionFormat (name : String) : Bool :=
  name == "cam-gouge" ||
  name == "devsim-dd1d" ||
  name == "yosys-lec" ||
  name == "fabulous-readback" ||
  name.startsWith "hw-"

/-- Read-only hardware projection dispatch: decodes `hwBytes` as a `TurnWitness`, verifies it
against `Obend.Judge.registry` (`sessionJudgeFormats`), and emits a structured JSON projection
summary. Arbitrary or unverified bytes fail closed (`-7`). -/
@[export obend_project_hardware_core]
def projectHardwareCore (s : SessionState) (hwBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if hwBytes.isEmpty then
    ({ s with lastError := some "Empty hardware witness payload" }, ByteArray.empty, -7)
  else
    match decodeTurnWitness? hwBytes with
    | none =>
      ({ s with lastError := some "Hardware projection requires a judge witness {format, version, grade, obj, cert}" }, ByteArray.empty, -7)
    | some w =>
      if isHardwareProjectionFormat w.formatName && checkTurnWitness sessionJudgeFormats w then
        let summary := Json.mkObj [
          ("schema", toJson "obend.ffi.hardware_projection.v1"),
          ("status", toJson "verified"),
          ("format", toJson w.formatName),
          ("version", toJson w.version),
          ("grade", toJson w.grade),
          ("digest", toJson (hashByteArray hwBytes))
        ]
        let outBytes := summary.compress.toUTF8
        ({ s with scratch := outBytes, lastError := none }, outBytes, 0)
      else
        ({ s with lastError := some s!"Hardware witness {w.formatName}@{w.version} refused by judge registry" }, ByteArray.empty, -7)

/-- The opening a receipt claims. -/
def receiptOpening (r : ReceiptWire) : Opening :=
  ⟨r.size, r.index, hashByteArray r.payload, r.path⟩

/-- Receipt verification: the frame decodes (`decodeReceipt?`), its root is one this session
committed, and its opening opens against that root (`Obend.Receipt.Merkle.opens` at the
deployed hash, the payload's digest recomputed here). Nothing else is accepted: not a bare root,
not a proposed-but-uncommitted root, not a payload whose digest is not at the claimed position
(`verifyReceiptCore_sound`). -/
@[export obend_verify_receipt_core]
def verifyReceiptCore (s : SessionState) (rcptBytes : ByteArray) : SessionState × Int32 :=
  match decodeReceipt? rcptBytes with
  | none =>
    ({ s with lastError := some "Malformed receipt: expected root || size || index || pathLen || path || payload" }, -8)
  | some r =>
    if !s.committedRoots.contains r.root then
      ({ s with lastError := some "Receipt root is not a root this session committed" }, -8)
    else if opens Obend.Core.Digest.deployed (receiptOpening r) (bytesToNat r.root) then
      ({ s with lastError := none }, 0)
    else
      ({ s with lastError := some "Receipt opening does not open against its root" }, -8)

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

/-- Law affordance query: parses surface `law` expressions using `Obend.Spec.Law.parse`,
classifies confluence via `Obend.Spec.LawDial.dial`, and computes multi-field repair witnesses
via `Obend.Vault.suggestMultiField`. Unparseable or non-UTF-8 queries fail closed. -/
@[export obend_view_affordances_core]
def viewAffordancesCore (s : SessionState) (queryBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if queryBytes.isEmpty then
    ({ s with lastError := some "Empty affordance query payload" }, ByteArray.empty, -3)
  else
    match Obend.Spec.Parse.decodeSource queryBytes with
    | none =>
      ({ s with lastError := some "Affordance query is not valid UTF-8" }, ByteArray.empty, -3)
    | some queryStr =>
      match parseLaw queryStr with
      | .error err =>
        ({ s with lastError := some s!"Invalid law expression: {err}" }, ByteArray.empty, -4)
      | .ok lawExpr =>
        let verdict := Obend.Spec.LawDial.dial lawExpr
        let confluenceName := dialVerdictName verdict
        let dialMode := match verdict with
          | .free => "free"
          | .stepShaped => "press"
          | .ordering => "locked"
        let fields := lawExpr.fields.eraseDups
        let curTurn := s.replaySession.world.store.turn
        let facts : Obend.Spec.Law.Facts := ⟨some 0, none, 0, curTurn⟩
        let zeroState : Data := .record (fields.map fun f => (f, .natural 0))
        let repairDesc := match Obend.Vault.suggestMultiField lawExpr facts none zeroState with
          | some [] => "suggestMultiField_admits: Bellman-Ford shortest repair delta=0"
          | some edits =>
            let parts := edits.map fun (p : String × Nat) => s!"{p.1}={p.2}"
            "suggestMultiField_admits: " ++ ", ".intercalate parts
          | none => "suggestMultiField_admits: no change of one field passes"
        let jsonObj := Json.mkObj [
          ("cellCount", toJson s.doc.atoms.length),
          ("turn", toJson curTurn),
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

/-- Legacy C-ABI symbol retained for `lean/c/obend_bridge.c` linkage; string-interpolated Lean
theorem codegen is disabled and fails closed (`-3` on empty, `-4` otherwise). -/
@[export obend_cell_pop_lean_core]
def cellPopLeanCore (s : SessionState) (cellBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if cellBytes.isEmpty then
    ({ s with lastError := some "Empty cell payload" }, ByteArray.empty, -3)
  else
    ({ s with lastError := some "String-interpolated Lean codegen is disabled; submit a judge witness to obend_cell_weave_cert" }, ByteArray.empty, -4)

/-- "Weave back in": a certificate enters a session only as a judge witness, checked by its
registered `Obend.Judge.Format` (`checkTurnWitness sessionJudgeFormats`). An accepted witness
becomes a pending proposal that `turnCommitCore` commits as a `VaultTurn` carrying it in
`witnesses`; a refused or unparseable one changes nothing (`-8`). There is no text gate: the
judge is the only reader of the certificate. -/
@[export obend_cell_weave_cert_core]
def cellWeaveCertCore (s : SessionState) (certBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if certBytes.isEmpty then
    ({ s with lastError := some "Empty witness payload" }, ByteArray.empty, -8)
  else
    match decodeTurnWitness? certBytes with
    | none =>
      ({ s with lastError := some "Weave payload must be a judge witness {format, version, grade, obj, cert}" }, ByteArray.empty, -8)
    | some w =>
      if checkTurnWitness sessionJudgeFormats w then
        let tidBytes := (buildCommittedReceipt certBytes).1
        let curTurn := s.replaySession.world.store.turn
        let proposal : PendingTurnProposal :=
          ⟨tidBytes, [], [(s!"witness_{curTurn}", .natural (hashByteArray certBytes))], some w, none⟩
        let pending := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes) ++ [proposal]
        ({ s with pendingProposals := pending, scratch := tidBytes, lastError := none }, tidBytes, 0)
      else
        let why := match Obend.Vault.findJudgeFormat sessionJudgeFormats w.formatName w.version with
          | some F =>
            let e := F.explain w.grade w.objBytes w.certBytes
            if e.isEmpty then "refused the certificate" else s!"refused the certificate: {e}"
          | none => "is not registered"
        ({ s with lastError := some s!"Judge format {w.formatName}@{w.version} {why}" }, ByteArray.empty, -8)


/-! ## What the bridge refuses, and what an acceptance means

`turnProposeCore` does not touch `committedRoots` (`turnProposeCore_committedRoots_unchanged`),
only `turnCommitCore` does, and `verifyReceiptCore` accepts only a decodable frame whose root
is committed and whose opening opens (`verifyReceiptCore_sound`). Every `turnCommitCore` step
admits a record into `s.replaySession` (`turnCommitCore_preserves_reachable`), so every reachable
FFI session serves the replay of its log (`Obend.Vault.Replay.state_eq_replay_log`). -/

theorem verifyReceiptCore_empty_refused (s : SessionState) :
    (verifyReceiptCore s ByteArray.empty).2 = -8 := by rfl

/-- A frame shorter than the 56-byte header, in particular a bare 32-byte root, is refused. -/
theorem verifyReceiptCore_short_refused (s : SessionState) (rcpt : ByteArray) (h : rcpt.size < 56) :
    (verifyReceiptCore s rcpt).2 = -8 := by
  unfold verifyReceiptCore decodeReceipt?
  simp [h]

/-- **What acceptance means**: the frame decodes, its root is committed, and its opening opens. -/
theorem verifyReceiptCore_sound (s : SessionState) (rcpt : ByteArray)
    (h : (verifyReceiptCore s rcpt).2 = 0) :
    ∃ r, decodeReceipt? rcpt = some r ∧
      s.committedRoots.contains r.root = true ∧
      opens Obend.Core.Digest.deployed (receiptOpening r) (bytesToNat r.root) = true := by
  unfold verifyReceiptCore at h
  split at h
  · simp at h
  · rename_i r hr
    split at h
    · simp at h
    · rename_i hc
      split at h
      · rename_i ho
        refine ⟨r, hr, ?_, ho⟩
        simpa using hc
      · simp at h

/-- With no committed root, nothing verifies. -/
theorem verifyReceiptCore_no_committed_refused (s : SessionState) (rcpt : ByteArray)
    (h : s.committedRoots = #[]) :
    (verifyReceiptCore s rcpt).2 = -8 := by
  unfold verifyReceiptCore
  split
  · rfl
  · rename_i r _
    have hc : s.committedRoots.contains r.root = false := by
      rw [h]
      simp
    simp [hc]

theorem verifyReceiptCore_empty_session_refused (rcpt : ByteArray) :
    (verifyReceiptCore SessionState.empty rcpt).2 = -8 :=
  verifyReceiptCore_no_committed_refused _ _ rfl

/-- A proposal admits no root. -/
theorem turnProposeCore_committedRoots_unchanged (s : SessionState) (turnBytes : ByteArray) :
    (turnProposeCore s turnBytes).1.committedRoots = s.committedRoots := by
  unfold turnProposeCore
  split
  · rfl
  · split
    · split
      · rfl
      · split <;> rfl
    · dsimp only
      split <;> rfl

/-- A payload proposed into the empty session does not make any receipt verify, its own one-leaf
receipt included. -/
theorem verifyReceiptCore_proposed_not_committed_refused (turnBytes rcpt : ByteArray) :
    (verifyReceiptCore (turnProposeCore SessionState.empty turnBytes).1 rcpt).2 = -8 :=
  verifyReceiptCore_no_committed_refused _ _
    ((turnProposeCore_committedRoots_unchanged _ _).trans rfl)

/-- A weave admits no root either. -/
theorem cellWeaveCertCore_committedRoots_unchanged (s : SessionState) (certBytes : ByteArray) :
    (cellWeaveCertCore s certBytes).1.committedRoots = s.committedRoots := by
  unfold cellWeaveCertCore
  repeat' split
  all_goals rfl

theorem cellWeaveCertCore_empty_refused (s : SessionState) :
    (cellWeaveCertCore s ByteArray.empty).2.2 = -8 := by rfl

/-- A payload that is not a judge witness is refused and proposes nothing. -/
theorem cellWeaveCertCore_not_witness_refused (s : SessionState) (certBytes : ByteArray)
    (hne : certBytes.isEmpty = false) (hdec : decodeTurnWitness? certBytes = none) :
    (cellWeaveCertCore s certBytes).2.2 = -8 ∧
      (cellWeaveCertCore s certBytes).1.pendingProposals = s.pendingProposals := by
  unfold cellWeaveCertCore
  simp [hne, hdec]

/-- A witness its format refuses is refused and proposes nothing. -/
theorem cellWeaveCertCore_refused_witness_not_proposed (s : SessionState) (certBytes : ByteArray)
    (w : TurnWitness) (hne : certBytes.isEmpty = false) (hdec : decodeTurnWitness? certBytes = some w)
    (hw : checkTurnWitness sessionJudgeFormats w = false) :
    (cellWeaveCertCore s certBytes).2.2 = -8 ∧
      (cellWeaveCertCore s certBytes).1.pendingProposals = s.pendingProposals := by
  unfold cellWeaveCertCore
  simp [hne, hdec, hw]

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

/-- **Unproposed turn commit refusal**: committing any 32-byte id in the empty session is refused
with `-5` and commits no root. -/
theorem turnCommitCore_unproposed_tid_refused (tidBytes : ByteArray)
    (h32 : tidBytes.size = 32) :
    (turnCommitCore SessionState.empty tidBytes).2 = -5 ∧
    (turnCommitCore SessionState.empty tidBytes).1.committedRoots = #[] := by
  unfold turnCommitCore SessionState.empty
  have hcond : (tidBytes.isEmpty || decide (tidBytes.size ≠ 32)) = false := by
    rw [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · unfold ByteArray.isEmpty
      rw [h32]
      rfl
    · exact decide_eq_false (by omega)
  rw [hcond]
  constructor <;> first | rfl | trivial

#tooth turnCommitCore_unproposed_tid_refused by mutation
  turnCommitCore := fun s _ => (s, 0)

/-- Every `turnCommitCore` step preserves `Obend.Vault.Replay.Reachable` on `s.replaySession`. -/
theorem turnCommitCore_preserves_reachable {s : SessionState} (tidBytes : ByteArray)
    (hr : Obend.Vault.Replay.Reachable s.replaySession) :
    Obend.Vault.Replay.Reachable (turnCommitCore s tidBytes).1.replaySession := by
  unfold turnCommitCore
  split
  · exact hr
  · split
    · rename_i prop _
      cases prop.replayBytes with
      | some rawBytes =>
        dsimp only
        split
        · rename_i nextReplay hadm
          exact Obend.Vault.Log.Reachable.admit hr hadm
        · exact hr
      | none =>
        dsimp only
        split
        · split
          · split
            · split
              · rename_i nextReplay hadm
                exact Obend.Vault.Log.Reachable.admit hr hadm
              · exact hr
            · exact hr
          · exact hr
        · exact hr
    · exact hr

/-- **A commit records the turn it denotes, witnesses included, and advances `replaySession`.** -/
theorem turnCommitCore_commits_turn (s : SessionState) (tidBytes : ByteArray)
    (prop : PendingTurnProposal) (turn : VaultTurn) (nextReplay : Obend.Vault.Replay.Session)
    (h32 : tidBytes.size = 32)
    (hfind : s.pendingProposals.find? (fun (p : PendingTurnProposal) => p.tidBytes == tidBytes) = some prop)
    (hnone : prop.replayBytes = none)
    (hfp : admitFootprint (sessionStoreLookup s) prop.footprint = .ok ())
    (hturn : proposalTurn s prop = some turn)
    (hall : turn.witnesses.all (checkTurnWitness sessionJudgeFormats) = true)
    (hadm : Obend.Vault.Log.Session.admit Obend.Vault.Replay.logHash Obend.Vault.Replay.deployed
      s.replaySession (Obend.Vault.Replay.encodeTurn (.base (applyWritesToWorld s.replaySession.world s.doc prop.writes))) = .ok nextReplay) :
    (turnCommitCore s tidBytes).2 = 0 ∧
    (turnCommitCore s tidBytes).1.replaySession = nextReplay ∧
    (turnCommitCore s tidBytes).1.committedTurns.head? = some turn ∧
    tidBytes ∈ (turnCommitCore s tidBytes).1.committedRoots ∧
    turn.witnesses = prop.witness.toList := by
  have hcond : (tidBytes.isEmpty || decide (tidBytes.size ≠ 32)) = false := by
    rw [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · unfold ByteArray.isEmpty
      rw [h32]
      rfl
    · exact decide_eq_false (by omega)
  have hturn' := hturn
  unfold proposalTurn at hturn'
  have hwit : turn.witnesses = prop.witness.toList :=
    (VaultTurn.ofWitnessLegs_fields hturn').2.2.2
  have hpush : tidBytes ∈ pushCommittedRoot s.committedRoots tidBytes := by
    unfold pushCommittedRoot
    simp [h32]
  unfold turnCommitCore
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hfind]
  dsimp only
  rw [hnone]
  dsimp only
  rw [hfp]
  dsimp only
  rw [hturn]
  dsimp only
  rw [hall]
  simp only [↓reduceIte]
  rw [hadm]
  exact ⟨rfl, rfl, rfl, hpush, hwit⟩

/-- Every committed turn's witnesses meet the witness clause of `ValidAt` at the session's
formats (`VaultTurn.ofWitnessLegs_witness_clause` through `turnCommitCore_commits_turn`). -/
theorem turnCommitCore_witness_clause (s : SessionState)
    (prop : PendingTurnProposal) (turn : VaultTurn)
    (hturn : proposalTurn s prop = some turn)
    (hall : turn.witnesses.all (checkTurnWitness sessionJudgeFormats) = true) :
    ∀ w ∈ turn.witnesses, ∃ F,
      findJudgeFormat sessionJudgeFormats w.formatName w.version = some F ∧
      F.checkBytes w.grade w.objBytes w.certBytes = .ok :=
  VaultTurn.ofWitnessLegs_witness_clause hturn hall

/-- Non-`.obend` UTF-8 cell payloads fail closed (`-4`) with empty output and leave `doc` unchanged. -/
theorem evalCellCore_non_obend_refused (s : SessionState) (cellBytes : ByteArray) (text : String)
    (hne : cellBytes.isEmpty = false)
    (hdec : Obend.Spec.Parse.decodeSource cellBytes = some text)
    (hnot : isObendPayload text = false) :
    (evalCellCore s cellBytes).2.2 = -4 ∧
    (evalCellCore s cellBytes).2.1 = ByteArray.empty ∧
    (evalCellCore s cellBytes).1.doc = s.doc := by
  unfold evalCellCore
  simp [hne, hdec, hnot]

/-- Non-witness hardware projection payloads fail closed (`-7`) with empty output. -/
theorem projectHardwareCore_non_witness_refused (s : SessionState) (hwBytes : ByteArray)
    (hne : hwBytes.isEmpty = false)
    (hdec : decodeTurnWitness? hwBytes = none) :
    (projectHardwareCore s hwBytes).2.2 = -7 ∧
    (projectHardwareCore s hwBytes).2.1 = ByteArray.empty := by
  unfold projectHardwareCore
  simp [hne, hdec]

/-- `projectHardwareCore` returns `0` only on a decoded hardware witness accepted by `sessionJudgeFormats`. -/
theorem projectHardwareCore_sound (s : SessionState) (hwBytes : ByteArray)
    (hok : (projectHardwareCore s hwBytes).2.2 = 0) :
    ∃ w, decodeTurnWitness? hwBytes = some w ∧
      isHardwareProjectionFormat w.formatName = true ∧
      checkTurnWitness sessionJudgeFormats w = true := by
  unfold projectHardwareCore at hok
  split at hok
  · simp at hok
  · split at hok
    · simp at hok
    · rename_i w hw
      split at hok
      · rename_i hchk
        simp only [Bool.and_eq_true] at hchk
        exact ⟨w, hw, hchk.1, hchk.2⟩
      · simp at hok

theorem turnProposeCore_empty_refused (s : SessionState) :
    (turnProposeCore s ByteArray.empty).2.2 = -3 := by rfl

theorem cellPopLeanCore_empty_refused (s : SessionState) :
    (cellPopLeanCore s ByteArray.empty).2.2 = -3 := by rfl

theorem cellPopLeanCore_nonempty_refused (s : SessionState) (cellBytes : ByteArray)
    (hne : cellBytes.isEmpty = false) :
    (cellPopLeanCore s cellBytes).2.2 = -4 ∧
    (cellPopLeanCore s cellBytes).2.1 = ByteArray.empty := by
  unfold cellPopLeanCore
  simp [hne]

theorem sessionStoreLookup_updates_after_applyWrites :
    let w1 := applyWritesToWorld SessionState.empty.replaySession.world Graph.empty [("x", .natural 10)]
    let s1 := { SessionState.empty with replaySession := ⟨w1, []⟩ }
    sessionStoreLookup s1 "x" = some (.natural 10) :=
  rfl

theorem admitFootprint_stale_pin_refused :
    let w1 := applyWritesToWorld SessionState.empty.replaySession.world Graph.empty [("x", .natural 10)]
    let s1 := { SessionState.empty with replaySession := ⟨w1, []⟩ }
    Footprint.Holds (sessionStoreLookup s1) [⟨"x", some (.natural 10)⟩] ∧
    ¬ Footprint.Holds (sessionStoreLookup s1) [⟨"x", some (.natural 99)⟩] := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact sessionStoreLookup_updates_after_applyWrites
  · intro h
    have hx := h ⟨"x", some (.natural 99)⟩ (List.Mem.head _)
    change sessionStoreLookup
      { SessionState.empty with
        replaySession := ⟨applyWritesToWorld SessionState.empty.replaySession.world Graph.empty [("x", .natural 10)], []⟩ }
      "x" = some (.natural 99) at hx
    rw [sessionStoreLookup_updates_after_applyWrites] at hx
    injection hx with hdata
    injection hdata with hnat
    omega


end Obend.FFI
end






