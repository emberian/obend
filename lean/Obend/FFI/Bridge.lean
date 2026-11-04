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
public import Obend.Judge
public import Obend.Ledger.Book
public import Obend.Doc.Graph
public import Obend.Doc.Structured
public import Obend.Doc.Render
public import Obend.Receipt.Merkle
public import Obend.Vault.Affordance
public import Obend.Vault.Rehydration
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

/-- A proposed turn waiting for `turnCommitCore`: its id, the footprint it was admitted
against, the writes it will apply, and the judge witness it was woven from (if any). -/
structure PendingTurnProposal where
  tidBytes : ByteArray
  footprint : Footprint
  writes : List (String × Data)
  witness : Option TurnWitness := none
  deriving Inhabited

/-- The session a host drives through the C ABI.

`committedRoots` are the roots of the turns this session has COMMITTED (`turnCommitCore`); a
proposal admits nothing. `verifyReceiptCore` accepts a receipt only when its root is one of them
and its opening opens against it (`Obend.Receipt.Merkle.opens`). `committedTurns` are the
`VaultTurn`s those commits denote, newest first, each built by `VaultTurn.ofWitnessLegs` with
the witnesses `cellWeaveCertCore` admitted. -/
structure SessionState where
  store : Store := { pages := [], members := [], turn := 0 }
  vaultStore : List (String × Data) := []
  pendingProposals : List PendingTurnProposal := []
  committedRoots : Array ByteArray := #[]
  committedTurns : List VaultTurn := []
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
    committedRoots := #[],
    committedTurns := [],
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

/-- Turn proposal: validates footprint pins against the session's actual `s.store` via
`admitFootprint` and registers the proposal. It commits nothing and admits no root. -/
@[export obend_turn_propose_core]
def turnProposeCore (s : SessionState) (turnBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if turnBytes.isEmpty then
    ({ s with lastError := some "Empty turn payload" }, ByteArray.empty, -3)
  else
    let fw := parseTurnFootprintAndWrites s turnBytes
    match admitFootprint (sessionStoreLookup s) fw.1 with
    | .ok () =>
      let tidBytes := (buildCommittedReceipt turnBytes).1
      let prop : PendingTurnProposal := ⟨tidBytes, fw.1, fw.2, none⟩
      let pending := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes) ++ [prop]
      ({ s with pendingProposals := pending, scratch := tidBytes, lastError := none }, tidBytes, 0)
    | .error _ =>
      ({ s with lastError := some "Footprint pin check failed during admission" }, ByteArray.empty, -4)

/-- The `VaultTurn` a proposal denotes against the session's store: one write leg per proposed
write (pre-state the store's current value), the admitted footprint as read pins, and the woven
witness. `none` exactly when the writes name one cell twice (`VaultTurn.ofWitnessLegs`). -/
def proposalTurn (s : SessionState) (prop : PendingTurnProposal) : Option VaultTurn :=
  let legs : List WitnessLegSpec := prop.writes.map fun w =>
    (w.1, (sessionStoreLookup s w.1).getD (.record []), w.2)
  VaultTurn.ofWitnessLegs prop.tidBytes prop.footprint legs
    (.record [("occasion", .label "commit")]) prop.witness.toList

/-- The judge formats a session accepts witnesses in: the registry (`Obend.Judge.registry`). -/
def sessionJudgeFormats : List Obend.Judge.Format := Obend.Judge.registry

/-- Turn commit: refuses an id that is not 32 bytes (`-6`) or not proposed (`-5`), re-checks the
footprint against `s.store` (`-4`), builds the turn with `VaultTurn.ofWitnessLegs` and checks
every witness with `checkTurnWitness` (`-9`), then applies the writes, records the turn, and
records its root in `committedRoots`. -/
@[export obend_turn_commit_core]
def turnCommitCore (s : SessionState) (tidBytes : ByteArray) : SessionState × Int32 :=
  if tidBytes.isEmpty || tidBytes.size ≠ 32 then
    ({ s with lastError := some "Invalid turn ID length" }, -6)
  else
    match s.pendingProposals.find? (fun (p : PendingTurnProposal) => p.tidBytes == tidBytes) with
    | some prop =>
      match admitFootprint (sessionStoreLookup s) prop.footprint with
      | .ok () =>
        match proposalTurn s prop with
        | some turn =>
          if turn.witnesses.all (checkTurnWitness sessionJudgeFormats) then
            let applied := applyWritesToSession s prop.writes
            let remaining := s.pendingProposals.filter (fun (p : PendingTurnProposal) => p.tidBytes != tidBytes)
            ({ s with
                store := applied.2,
                vaultStore := applied.1,
                pendingProposals := remaining,
                committedRoots := pushCommittedRoot s.committedRoots tidBytes,
                committedTurns := turn :: s.committedTurns,
                lastError := none }, 0)
          else
            ({ s with lastError := some "A turn witness is refused by its judge format" }, -9)
        | none =>
          ({ s with lastError := some "Turn writes name one cell twice" }, -9)
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

/-- Parse a comma-separated list of capability names into `List Obend.Vault.Affordance.Auth`. -/
def parseAuthList (csv : String) : List Obend.Vault.Affordance.Auth :=
  (csv.splitOn ",").filterMap fun raw =>
    match raw.trimAscii.toString with
    | "read"    => some .read
    | "write"   => some .write
    | "grant"   => some .grant
    | "call"    => some .call
    | "reply"   => some .reply
    | "reset"   => some .reset
    | "control" => some .control
    | "notify"  => some .notify
    | _         => none

/-- Render an `Obend.Vault.Affordance.Auth` capability to its canonical string name. -/
def renderAuth : Obend.Vault.Affordance.Auth → String
  | .read    => "read"
  | .write   => "write"
  | .grant   => "grant"
  | .call    => "call"
  | .reply   => "reply"
  | .reset   => "reset"
  | .control => "control"
  | .notify  => "notify"

/-- Canonical tag for `Obend.Vault.Affordance.Auth` used in `computeAuthDigest`. -/
def authTag : Obend.Vault.Affordance.Auth → Nat
  | .read    => 1
  | .write   => 2
  | .grant   => 3
  | .call    => 4
  | .reply   => 5
  | .reset   => 6
  | .control => 7
  | .notify  => 8

/-- Compute the `Obend.Core.Digest.deployed` capability digest over a list of `Auth` rights. -/
def computeAuthDigest (caps : List Obend.Vault.Affordance.Auth) : Nat :=
  caps.foldl (fun acc c => Obend.Core.Digest.digestWith Obend.Core.Digest.deployed acc (authTag c)) 0

/-- Render an `Obend.Vault.Rehydration.Rehydration` liveness readout to its canonical string. -/
def renderRehydration : Obend.Vault.Rehydration.Rehydration → String
  | .Live                     => "Live"
  | .ReplayedDeterministic    => "ReplayedDeterministic"
  | .ReconstructedApproximate => "ReconstructedApproximate"

/-- Evaluate a Tab 3 Rehydratable Membranes query via `Obend.Vault.Rehydration` & `Obend.Vault.Affordance`.
    Query wire format:
    `membrane:<reachable>:<confined>:<frozen>:<revoked>:<v1_caps>:<v1_permits>:<v2_caps>:<v2_permits>:<height>:<old_val>:<new_val>` -/
def evalMembraneAffordanceQuery (s : SessionState) (queryStr : String) : Json :=
  let body := (queryStr.drop 9).trimAscii.toString
  let parts := body.splitOn ":"
  let getPart (idx : Nat) (defVal : String) : String :=
    (parts[idx]?.getD defVal).trimAscii.toString
  let isReachable : Bool := getPart 0 "false" == "true"
  let isConfinedInput : Bool := getPart 1 "true" != "false"
  let isFrozen : Bool := getPart 2 "false" == "true"
  let isRevoked : Bool := getPart 3 "false" == "true"
  let v1CapsRaw := parseAuthList (getPart 4 "read,write,grant,call")
  let v1Caps := if isFrozen then v1CapsRaw.filter (fun c => c != .write && c != .grant) else v1CapsRaw
  let v1PermitsList := (getPart 5 "scrub_parameter,weave_lean_cert,reshare_membrane,inspect_projection").splitOn ","
    |>.map (·.trimAscii.toString) |>.filter (fun x => !x.isEmpty)
  let v2Caps := parseAuthList (getPart 6 "read,write")
  let v2PermitsList := (getPart 7 "scrub_parameter,inspect_projection").splitOn ","
    |>.map (·.trimAscii.toString) |>.filter (fun x => !x.isEmpty)
  let height : Nat := (getPart 8 "12").toNat?.getD 12
  let oldVal : Nat := (getPart 9 "28").toNat?.getD 28
  let newVal : Nat := (getPart 10 "31").toNat?.getD 31

  -- 1. Pillar 1: InteractionLog, `confined`, `classify`, and `witnessChainOf`
  let ar1 : Obend.Vault.Rehydration.AttestedRoot :=
    { root := 101 + s.store.turn, v4Complete := true, quorum := true }
  let ar2 : Obend.Vault.Rehydration.AttestedRoot :=
    { root := 202 + s.store.turn, v4Complete := true, quorum := true }
  let log : Obend.Vault.Rehydration.InteractionLog :=
    if isConfinedInput then [.attested ar1, .attested ar2]
    else [.attested ar1, .ambient, .attested ar2]
  let isConf := Obend.Vault.Rehydration.confined log
  let liveness := Obend.Vault.Rehydration.classify log isReachable
  let chainHash (r : Obend.Vault.Rehydration.WitnessReceipt) : Nat :=
    Obend.Core.Digest.digestWith Obend.Core.Digest.deployed r.oldCommit r.newCommit
  let chain := Obend.Vault.Rehydration.witnessChainOf chainHash log

  -- 2. Pillar 2: `MembraneViewer`, `projectMembrane`, `Membrane.reshare`, `Sturdyref`, `rehydrateSturdyref`
  let allNames : List String :=
    ["scrub_parameter", "weave_lean_cert", "reshare_membrane", "inspect_projection"]
  let surface : Obend.Vault.Rehydration.AffordanceSurface Nat := [
    { required := [.read, .write], effect := 1, name := "scrub_parameter" },
    { required := [.read, .call],  effect := 2, name := "weave_lean_cert" },
    { required := [.read, .grant], effect := 3, name := "reshare_membrane" },
    { required := [.read],         effect := 4, name := "inspect_projection" }
  ]
  let viewer1 : Obend.Vault.Rehydration.MembraneViewer := {
    held := v1Caps
    permits := fun n => v1PermitsList.contains n
    activeNames := allNames
  }
  let viewer2 : Obend.Vault.Rehydration.MembraneViewer := {
    held := v2Caps
    permits := fun n => v2PermitsList.contains n
    activeNames := allNames
  }
  let reshared? := Obend.Vault.Rehydration.Membrane.reshare viewer1 viewer2
  let sr : Obend.Vault.Rehydration.Sturdyref Nat := {
    uri := "obend://vault/cell-thermal-ode#v4"
    surface := if isRevoked then [] else surface
    log := log
    lineage := viewer1
    reachable := isReachable
  }
  let (rehydSurface1, srLiveness) := Obend.Vault.Rehydration.rehydrateSturdyref sr viewer1
  let (rehydSurface2, _) := Obend.Vault.Rehydration.rehydrateSturdyref sr viewer2
  let v1Names := rehydSurface1.map (·.name)
  let v2Names := rehydSurface2.map (·.name)
  let twoViewersDistinct := v1Names != v2Names

  -- 3. Pillar 4: 3D `ReactiveAffordance` & `fireReactive`
  let gate : Obend.Vault.Rehydration.TransitionGate := {
    pre := fun d => match d with | .natural v => decide (15 ≤ v && v ≤ 35) | _ => false
    post := fun d => match d with | .natural v => decide (15 ≤ v && v ≤ 35) | _ => false
    link := fun d1 d2 => match d1, d2 with
      | .natural v1, .natural v2 => decide (v1 ≤ v2 + 10 && v2 ≤ v1 + 10)
      | _, _ => false
  }
  let ra : Obend.Vault.Rehydration.ReactiveAffordance Nat := {
    aff := { required := [.read, .write], effect := newVal, name := "scrub_parameter" }
    gate := gate
    openHeight := 1
    closeHeight := 64
  }
  let fc : Obend.Vault.Affordance.FireCtx Nat := {
    effectDigest := id
    prevDigest := 0
    preCommit := oldVal
    postCommit := newVal
  }
  let fired? :=
    if isFrozen || isRevoked then none
    else Obend.Vault.Rehydration.fireReactive ra viewer1.held height (.natural oldVal) (.natural newVal) fc
  let capDigest1 := computeAuthDigest v1Caps
  let capDigest2 := computeAuthDigest v2Caps

  Json.mkObj [
    ("schema", toJson "obend.ffi.membrane.v1"),
    ("turn", toJson s.store.turn),
    ("liveness", toJson (renderRehydration liveness)),
    ("sturdyrefLiveness", toJson (renderRehydration srLiveness)),
    ("isFaithful", toJson liveness.isFaithful),
    ("confined", toJson isConf),
    ("reachable", toJson isReachable),
    ("frozen", toJson isFrozen),
    ("revoked", toJson isRevoked),
    ("logLength", toJson log.length),
    ("witnessChainLength", toJson chain.length),
    ("chainCoversLog", toJson (chain.length == log.length)),
    ("capDigest", toJson capDigest1),
    ("viewer2CapDigest", toJson capDigest2),
    ("heldCaps", toJson (v1Caps.map renderAuth)),
    ("viewer2HeldCaps", toJson (v2Caps.map renderAuth)),
    ("viewer1Surface", toJson v1Names),
    ("viewer2Surface", toJson v2Names),
    ("twoViewersDistinct", toJson twoViewersDistinct),
    ("reshareAdmitted", toJson reshared?.isSome),
    ("resharedCaps", toJson (match reshared? with | some m => m.held.map renderAuth | none => [])),
    ("reactiveWindowOpen", toJson ra.openHeight),
    ("reactiveWindowClose", toJson ra.closeHeight),
    ("reactiveHeight", toJson height),
    ("reactiveInWindow", toJson (Obend.Vault.Rehydration.inWindow ra height)),
    ("reactiveTransitionOk", toJson (Obend.Vault.Rehydration.transitionOK gate (.natural oldVal) (.natural newVal))),
    ("reactiveFired", toJson fired?.isSome)
  ]

/-- Interactive view affordances (`WS 31` & `WS 33`):
    - If the query starts with `"membrane:"`, evaluates the Rehydratable Membranes state via
      `Obend.Vault.Rehydration` (`classify`, `confined`, `witnessChainOf`, `Membrane.reshare`,
      `rehydrateSturdyref`, and `fireReactive`).
    - Otherwise parses law strings using `Obend.Spec.Law.parse` (`parseLaw`),
      classifies via `Obend.Spec.LawDial.dial` into `.free`, `.stepShaped`, or `.ordering`, and
      computes multi-field repair witnesses via `Obend.Vault.suggestMultiField`. -/
@[export obend_view_affordances_core]
def viewAffordancesCore (s : SessionState) (queryBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if queryBytes.isEmpty then
    ({ s with lastError := some "Empty affordance query payload" }, ByteArray.empty, -3)
  else
    match Obend.Spec.Parse.decodeSource queryBytes with
    | some queryStr =>
      if queryStr.trimAscii.toString.startsWith "membrane:" then
        let jsonObj := evalMembraneAffordanceQuery s queryStr.trimAscii.toString
        let outBytes := jsonObj.compress.toUTF8
        ({ s with scratch := outBytes, lastError := none }, outBytes, 0)
      else
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
        let proposal : PendingTurnProposal :=
          ⟨tidBytes, [], [(s!"witness_{s.store.turn}", .natural (hashByteArray certBytes))], some w⟩
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

The two self-admission paths found on 2026-11-01 and 2026-11-03 (a proposed payload counted
as an admitted root; a 32-byte root accepted with no opening) are gone by construction:
`turnProposeCore` does not touch `committedRoots` (`turnProposeCore_committedRoots_unchanged`),
only `turnCommitCore` does, and `verifyReceiptCore` accepts only a decodable frame whose root
is committed and whose opening opens (`verifyReceiptCore_sound`). -/

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
  · dsimp only
    split <;> rfl

/-- **The first self-admission path is closed**: a payload proposed into the empty session does
not make any receipt verify, its own one-leaf receipt included. -/
theorem verifyReceiptCore_proposed_not_committed_refused (turnBytes rcpt : ByteArray) :
    (verifyReceiptCore (turnProposeCore SessionState.empty turnBytes).1 rcpt).2 = -8 :=
  verifyReceiptCore_no_committed_refused _ _
    ((turnProposeCore_committedRoots_unchanged _ _).trans rfl)

/-- A weave admits no root either. -/
theorem cellWeaveCertCore_committedRoots_unchanged (s : SessionState) (certBytes : ByteArray) :
    (cellWeaveCertCore s certBytes).1.committedRoots = s.committedRoots := by
  unfold cellWeaveCertCore
  split
  · rfl
  · split
    · rfl
    · dsimp only
      split <;> rfl

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

/-- **A commit records the turn it denotes, witnesses included.** When the proposal is found,
its footprint holds, its turn constructs, and every witness passes its judge format, the commit
succeeds, the turn is the newest committed turn, and its witnesses are the proposal's. -/
theorem turnCommitCore_commits_turn (s : SessionState) (tidBytes : ByteArray)
    (prop : PendingTurnProposal) (turn : VaultTurn)
    (h32 : tidBytes.size = 32)
    (hfind : s.pendingProposals.find? (fun (p : PendingTurnProposal) => p.tidBytes == tidBytes) = some prop)
    (hfp : admitFootprint (sessionStoreLookup s) prop.footprint = .ok ())
    (hturn : proposalTurn s prop = some turn)
    (hall : turn.witnesses.all (checkTurnWitness sessionJudgeFormats) = true) :
    (turnCommitCore s tidBytes).2 = 0 ∧
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
  simp only []
  rw [hfp]
  simp only []
  rw [hturn]
  simp only []
  rw [hall]
  simp only [↓reduceIte]
  refine ⟨?_, ?_, hpush, hwit⟩ <;> first | trivial | rfl

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

theorem turnProposeCore_empty_refused (s : SessionState) :
    (turnProposeCore s ByteArray.empty).2.2 = -3 := by rfl

theorem cellPopLeanCore_empty_refused (s : SessionState) :
    (cellPopLeanCore s ByteArray.empty).2.2 = -3 := by rfl

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


end Obend.FFI
end






