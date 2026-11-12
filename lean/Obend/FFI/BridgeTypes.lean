module
/-
# Obend.FFI.BridgeTypes — Pure JSON Wire Codecs for Incremental Workbook & Lens Scrubbing
Keeps `Lean.Json` strictly private (`LAW-M2`: `0` `public import Lean`) while providing
fail-closed UTF-8 JSON request/response marshaling for `Obend.FFI.Bridge`.
-/
import Lean
public import Obend.Doc.WorkbookEngine
public import Obend.Spec.Parse

public section
namespace Obend.FFI

open Lean (Json toJson)
open Obend.Core.Data (Data)
open Obend.Doc
open Obend.Doc.Reactive (CellId SymbolName Opcode Instruction CellBody ReactiveCell
  CachedCell scientificKernel)
open Obend.Doc.WorkbookEngine

set_option autoImplicit false

/-- Default empty workbook carried by a freshly initialized `SessionState`. -/
@[expose] def defaultSessionWorkbook : Workbook :=
  { title := "SessionWorkbook", sections := [], cells := [] }

private def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def byteArrayToHex (bs : ByteArray) : String :=
  String.ofList <| bs.data.toList.flatMap fun b =>
    let v := b.toNat
    [hexDigitChar (v / 16), hexDigitChar (v % 16)]

private def bitVec256ToHex (bv : BitVec 256) : String :=
  let bytes : List UInt8 := (List.range 32).map fun i =>
    let shift := (31 - i) * 8
    ((bv >>> shift).toNat % 256).toUInt8
  byteArrayToHex (ByteArray.mk bytes.toArray)

private def nat256ToHex (n : Nat) : String :=
  bitVec256ToHex (BitVec.ofNat 256 n)

private def decodeDataJson (j : Json) : Except String Data :=
  match j with
  | .num n =>
    if n.exponent == 0 && n.mantissa ≥ 0 then .ok (.natural n.mantissa.toNat)
    else .error "Expected non-negative integer for natural Data"
  | .bool b => .ok (.boolean b)
  | .str s => .ok (.label s)
  | .obj _ =>
    if let .ok n := j.getObjValAs? Nat "nat" then .ok (.natural n)
    else if let .ok b := j.getObjValAs? Bool "bool" then .ok (.boolean b)
    else if let .ok s := j.getObjValAs? String "label" then .ok (.label s)
    else .error "Unsupported Data JSON object; expected {nat}, {bool}, or {label}"
  | _ => .error "Unsupported Data JSON value"

private def encodeDataJsonFuel : Nat → Data → Json
  | 0, _ => Json.str "..."
  | _ + 1, .natural n => Json.mkObj [("tag", toJson "natural"), ("value", toJson n)]
  | _ + 1, .boolean b => Json.mkObj [("tag", toJson "boolean"), ("value", toJson b)]
  | _ + 1, .label s => Json.mkObj [("tag", toJson "label"), ("value", toJson s)]
  | fuel + 1, .record fs =>
    Json.mkObj [("tag", toJson "record"),
      ("fields", Json.mkObj (fs.map fun (k, v) => (k, encodeDataJsonFuel fuel v)))]
  | fuel + 1, .variant l payload =>
    Json.mkObj [("tag", toJson "variant"), ("label", toJson l), ("payload", encodeDataJsonFuel fuel payload)]

private def encodeDataJson (d : Data) : Json := encodeDataJsonFuel 32 d

private def decodeFieldsList (j : Json) : Except String (List (String × Data)) := do
  match j.getObjVal? "fields" with
  | .error _ => pure []
  | .ok (.obj kvs) =>
    kvs.toArray.toList.mapM fun ⟨k, v⟩ => do
      let dv ← decodeDataJson v
      pure (k, dv)
  | .ok (.arr pairs) =>
    pairs.toList.mapM fun item => do
      let arr ← item.getArr?
      if h : arr.size = 2 then
        let k ← arr[0].getStr?
        let dv ← decodeDataJson arr[1]
        pure (k, dv)
      else .error "Field entry must be [name, value]"
  | .ok _ => .error "'fields' must be a JSON object or array of [name, value] pairs"

private def decodeOpcode (s : String) : Except String Opcode :=
  match s with
  | "literal" => .ok .literal
  | "input" | "loadLocal" => .ok .input
  | "add" => .ok .add
  | "sub" => .ok .sub
  | "mul" => .ok .mul
  | "div" | "divSafe" => .ok .div
  | _ => .error s!"Unknown reactive opcode '{s}'"

private def decodeInstruction (j : Json) : Except String Instruction := do
  let opStr ← j.getObjValAs? String "op"
  let op ← decodeOpcode opStr
  let arg := (j.getObjValAs? Int "arg").toOption.getD 0
  pure { op := op, arg := arg }

private def decodeCellBody (j : Json) : Except String CellBody := do
  match j.getObjVal? "body" with
  | .ok bodyJson =>
    let outer ← bodyJson.getArr?
    outer.toList.mapM fun progJson => do
      let insns ← progJson.getArr?
      insns.toList.mapM decodeInstruction
  | .error _ =>
    match j.getObjValAs? Int "literalValue" with
    | .ok lit => pure [[{ op := .literal, arg := lit }]]
    | .error _ => pure [[{ op := .literal, arg := 0 }]]

private def decodeStringListField (j : Json) (field : String) : Except String (List String) :=
  match j.getObjVal? field with
  | .error _ => .ok []
  | .ok v => do
    let arr ← v.getArr?
    arr.toList.mapM Json.getStr?

private def decodeBlocksField (j : Json) : Except String (List (String × Int)) :=
  match j.getObjVal? "blocks" with
  | .error _ => .ok []
  | .ok (.arr pairs) =>
    pairs.toList.mapM fun p => do
      let arr ← p.getArr?
      if h : arr.size = 2 then
        let k ← arr[0].getStr?
        let v ← arr[1].getInt?
        pure (k, v)
      else .error "Block entry must be [blockId, intValue]"
  | .ok (.obj kvs) =>
    kvs.toArray.toList.mapM fun ⟨k, v⟩ => do
      let iv ← v.getInt?
      pure (k, iv)
  | .ok _ => .error "'blocks' must be an object or array of [blockId, intValue]"

private def decodeSectionJson (j : Json) : Except String WorkbookSection := do
  let secKey ← j.getObjValAs? String "sectionKey"
  if secKey.isEmpty then .error "Workbook sectionKey must be non-empty"
  let md := (j.getObjValAs? String "markdown").toOption.getD ""
  let blks ← decodeBlocksField j
  pure { sectionKey := secKey, markdown := md, blocks := blks }

private def decodeVisibilityField (j : Json) : Except String CellVisibility :=
  match j.getObjVal? "visibility" with
  | .error _ => .ok .publicCell
  | .ok (.str "public") => .ok .publicCell
  | .ok vObj => do
    let tag ← vObj.getObjValAs? String "sealed"
    if tag.isEmpty then .error "Sealed visibility clearanceTag must be non-empty"
    let saltNat := (vObj.getObjValAs? Nat "salt").toOption.getD 1
    pure (.sealedPrivate tag (BitVec.ofNat 256 saltNat))

private def checkWellFormedReadsB (w : WorkbookCell) : Bool :=
  let cited := allCitedKeys w
  w.reactive.reads.all fun r =>
    match stripCiteSymbolChars r.toList with
    | none => true
    | some ck => cited.contains ck

private def decodeWorkbookCellJson (j : Json) : Except String WorkbookCell := do
  let cellKey ← j.getObjValAs? String "cellKey"
  if cellKey.isEmpty then .error "Workbook cellKey must be non-empty"
  let cid ← j.getObjValAs? Nat "id"
  let kindStr := (j.getObjValAs? String "kind").toOption.getD "obendCode"
  let kind ← match ProjectionKind.ofLabel kindStr with
    | some k => .ok k
    | none => .error s!"Unknown ProjectionKind '{kindStr}'"
  let fields ← decodeFieldsList j
  if !(fields.map Prod.fst).Nodup then
    .error s!"Duplicate record field names in cell '{cellKey}'"
  let pins := fields.map fun (fn, fv) => (fn, computeFieldPin32 fn fv)
  let sc : StructuredCell :=
    { id := cellKey, kind := kind, ast := .record fields, pins := pins, receipt := none }
  let reads ← decodeStringListField j "reads"
  let defs ← decodeStringListField j "defs"
  let citedKeys ← decodeStringListField j "citedKeys"
  let note := (j.getObjValAs? String "note").toOption.getD ""
  let body ← decodeCellBody j
  let vis ← decodeVisibilityField j
  let rc : ReactiveCell :=
    { id := cid, kind := kind, reads := reads, defs := defs, body := body, note := note }
  let wc : WorkbookCell :=
    { cellKey := cellKey, structured := sc, reactive := rc, citedKeys := citedKeys, visibility := vis }
  if !checkWellFormedReadsB wc then
    .error s!"Cell '{cellKey}' reads an undeclared cite:: symbol outside citedKeys/note"
  pure wc

private def encodeProjectedViewJson (v : ProjectedView) : Json :=
  Json.mkObj [
    ("cellId", toJson v.cellId),
    ("kind", toJson v.kind.toLabel),
    ("hasVerifiedBadge", toJson v.verifiedBadge.isSome),
    ("fields", Json.arr <| v.fields.toArray.map fun pf =>
      Json.mkObj [
        ("name", toJson pf.name),
        ("access", toJson (match pf.access with | .scrubbable => "scrubbable" | .readOnlyBadge => "readOnlyBadge")),
        ("value", encodeDataJson pf.value)
      ])
  ]

private def encodeCachedCellJson (c : CachedWorkbookCell) : Json :=
  let view := (lensForKind c.entry.structured.kind).view c.entry.structured
  Json.mkObj [
    ("cellKey", toJson c.entry.cellKey),
    ("id", toJson c.entry.reactive.id),
    ("kind", toJson c.entry.structured.kind.toLabel),
    ("values", toJson c.result.values),
    ("receiptHex", toJson (bitVec256ToHex c.result.receipt)),
    ("citedKeys", toJson (allCitedKeys c.entry)),
    ("view", encodeProjectedViewJson view)
  ]

private def encodeWorkbookStepJson (opName : String) (dirtyCone : List CellId) (wb : Workbook) : ByteArray :=
  let leaves := wb.cells.map (cellSaltedCommitment Obend.Core.Digest.deployed)
  let rootNat := Obend.Receipt.Merkle.mapRoot Obend.Core.Digest.deployed leaves
  let resp := Json.mkObj [
    ("schema", toJson "obend.ffi.workbook_step.v1"),
    ("status", toJson "accepted"),
    ("op", toJson opName),
    ("title", toJson wb.title),
    ("sectionCount", toJson wb.sections.length),
    ("cellCount", toJson wb.cells.length),
    ("dirtyCone", toJson dirtyCone),
    ("merkleRootHex", toJson (nat256ToHex rootNat)),
    ("cells", Json.arr (wb.cells.toArray.map encodeCachedCellJson))
  ]
  resp.compress.toUTF8

private def encodeRedactedWorkbookJson (rwb : RedactedWorkbook) (verified : Bool) : ByteArray :=
  let entriesJson := rwb.entries.toArray.map fun e =>
    match e with
    | .visible c cm _ =>
      Json.mkObj [
        ("mode", toJson "visible"),
        ("cellKey", toJson c.entry.cellKey),
        ("id", toJson c.entry.reactive.id),
        ("kind", toJson c.entry.structured.kind.toLabel),
        ("values", toJson c.result.values),
        ("commitmentHex", toJson (bitVec256ToHex cm))
      ]
    | .redacted cid ck kind bindings cm _ =>
      Json.mkObj [
        ("mode", toJson "redacted"),
        ("cellKey", toJson ck),
        ("id", toJson cid),
        ("kind", toJson kind.toLabel),
        ("exportedDefs", Json.arr (bindings.toArray.map fun (s, v) => Json.arr #[toJson s, toJson v])),
        ("commitmentHex", toJson (bitVec256ToHex cm))
      ]
  let resp := Json.mkObj [
    ("schema", toJson "obend.ffi.workbook_redacted.v1"),
    ("status", toJson (if verified then "verified" else "refused")),
    ("verified", toJson verified),
    ("title", toJson rwb.title),
    ("merkleRootHex", toJson (nat256ToHex rwb.merkleRoot)),
    ("entries", Json.arr entriesJson)
  ]
  resp.compress.toUTF8

/-- Execute a JSON-encoded workbook step (`init`, `editCell`, `editSection`, or `exportRedacted`),
    failing closed on malformed UTF-8/JSON (`-3`) or DAG/schema violations (`-4`). -/
def stepWorkbookJsonBytes (wb : Workbook) (reqBytes : ByteArray) :
    Except (Int32 × String) (Workbook × ByteArray) :=
  if reqBytes.isEmpty then
    .error (-3, "Empty workbook step payload")
  else
    match Obend.Spec.Parse.decodeSource reqBytes with
    | none => .error (-3, "Workbook step payload is not valid UTF-8")
    | some raw =>
      match Json.parse raw with
      | .error err => .error (-3, s!"Invalid workbook step JSON: {err}")
      | .ok j =>
        match j.getObjValAs? String "op" with
        | .error _ => .error (-3, "Workbook step JSON missing string field 'op'")
        | .ok "init" =>
          let title := (j.getObjValAs? String "title").toOption.getD "LiveWorkbook"
          let secsRes : Except String (List WorkbookSection) :=
            match j.getObjVal? "sections" with
            | .error _ => .ok []
            | .ok sj => do
              let arr ← sj.getArr?
              arr.toList.mapM decodeSectionJson
          let cellsRes : Except String (List WorkbookCell) := do
            let cj ← j.getObjVal? "cells"
            let arr ← cj.getArr?
            arr.toList.mapM decodeWorkbookCellJson
          match secsRes, cellsRes with
          | .error e, _ => .error (-4, e)
          | _, .error e => .error (-4, e)
          | .ok secs, .ok rawCells =>
            if !(secs.map WorkbookSection.sectionKey).Nodup then
              .error (-4, "Workbook sections contain duplicate sectionKey")
            else if !checkWorkbookDag rawCells then
              .error (-4, "Workbook DAG admission refused: cycle, self-citation, or duplicate key/export")
            else
              let wb' := evalWorkbookFull scientificKernel title secs rawCells
              let allIds := rawCells.map (fun (w : WorkbookCell) => w.reactive.id)
              .ok (wb', encodeWorkbookStepJson "init" allIds wb')
        | .ok "editCell" =>
          match j.getObjValAs? Nat "targetId" with
          | .error _ => .error (-4, "editCell requires numeric 'targetId'")
          | .ok tid =>
            match wb.cells.find? (fun (c : CachedWorkbookCell) => c.entry.reactive.id == tid) with
            | none => .error (-4, s!"Unknown target cell id {tid}")
            | some existing =>
              let astRes : Except String Data :=
                match j.getObjVal? "fields" with
                | .error _ => .ok existing.entry.structured.ast
                | .ok _ => do
                  let fs ← decodeFieldsList j
                  if !(fs.map Prod.fst).Nodup then
                    .error "Duplicate record field names in editCell"
                  pure (.record fs)
              match astRes, decodeCellBody j with
              | .error e, _ => .error (-4, e)
              | _, .error e => .error (-4, e)
              | .ok newAst, .ok newBody =>
                let edit := WorkbookEdit.editCellBody tid newAst newBody
                let dirty := workbookDirtyCone wb edit
                let wb' := evalWorkbookIncremental scientificKernel wb edit
                .ok (wb', encodeWorkbookStepJson "editCell" dirty wb')
        | .ok "editSection" =>
          match j.getObjValAs? String "sectionKey" with
          | .error _ => .error (-4, "editSection requires string 'sectionKey'")
          | .ok secKey =>
            if !(wb.sections.any (fun s => s.sectionKey == secKey)) then
              .error (-4, s!"Unknown workbook sectionKey '{secKey}'")
            else
              let newMd := (j.getObjValAs? String "markdown").toOption.getD ""
              match decodeBlocksField j with
              | .error e => .error (-4, e)
              | .ok newBlks =>
                let edit := WorkbookEdit.editSection secKey newMd newBlks
                let dirty := workbookDirtyCone wb edit
                let wb' := evalWorkbookIncremental scientificKernel wb edit
                .ok (wb', encodeWorkbookStepJson "editSection" dirty wb')
        | .ok "exportRedacted" =>
          match decodeStringListField j "clearances" with
          | .error e => .error (-4, e)
          | .ok clearances =>
            let rwb := projectWorkbookForViewer Obend.Core.Digest.deployed clearances wb
            let okB := verifyRedactedWorkbook scientificKernel Obend.Core.Digest.deployed rwb
            if okB then .ok (wb, encodeRedactedWorkbookJson rwb true)
            else .error (-8, "Redacted workbook failed Merkle/receipt verification")
        | .ok otherOp =>
          .error (-4, s!"Unsupported workbook step op '{otherOp}'")

/-- Execute a bidirectional Putnam/Foster lens scrub on a workbook cell from UTF-8 JSON bytes,
    refusing read-only proof badges (`-5`), unknown/ill-typed fields (`-4`), and bad JSON (`-3`). -/
def scrubWorkbookCellJsonBytes (wb : Workbook) (reqBytes : ByteArray) :
    Except (Int32 × String) (Workbook × ByteArray) :=
  if reqBytes.isEmpty then
    .error (-3, "Empty workbook scrub payload")
  else
    match Obend.Spec.Parse.decodeSource reqBytes with
    | none => .error (-3, "Workbook scrub payload is not valid UTF-8")
    | some raw =>
      match Json.parse raw with
      | .error err => .error (-3, s!"Invalid workbook scrub JSON: {err}")
      | .ok j =>
        match j.getObjValAs? String "cellKey", j.getObjValAs? String "fieldName", j.getObjVal? "newValue" with
        | .ok cellKey, .ok fieldName, .ok rawVal =>
          match decodeDataJson rawVal with
          | .error e => .error (-4, e)
          | .ok newVal =>
            let viewEdit : ViewEdit := { fieldName := fieldName, newValue := newVal }
            match scrubWorkbookCell scientificKernel wb cellKey viewEdit with
            | .error (.readOnlyField f) =>
              .error (-5, s!"Refused scrub on read-only proof/badge field '{f}'")
            | .error (.unknownField f) =>
              .error (-4, s!"Unknown scrub cell or field '{f}'")
            | .error (.typeMismatch f _) =>
              .error (-4, s!"Type mismatch while scrubbing field '{f}'")
            | .error (.kindMismatch exp act) =>
              .error (-4, s!"Projection kind mismatch: expected {exp.toLabel}, got {act.toLabel}")
            | .error (.malformedCellRecord cid) =>
              .error (-4, s!"Cell '{cid}' AST is not a structured record")
            | .ok (wb', patch) =>
              let dirty : List CellId :=
                match wb.cells.find? (fun (c : CachedWorkbookCell) => c.entry.cellKey == cellKey) with
                | none => []
                | some tc =>
                  let newBody : CellBody := match dataToLiteralInt? newVal with
                    | some lit => [[{ op := .literal, arg := lit }]]
                    | none => tc.entry.reactive.body
                  workbookDirtyCone wb (.editCellBody tc.entry.reactive.id tc.entry.structured.ast newBody)
              let updatedViewJson : Json :=
                match wb'.cells.find? (fun (c : CachedWorkbookCell) => c.entry.cellKey == cellKey) with
                | some uc => encodeProjectedViewJson ((lensForKind uc.entry.structured.kind).view uc.entry.structured)
                | none => Json.null
              let leaves := wb'.cells.map (cellSaltedCommitment Obend.Core.Digest.deployed)
              let rootNat := Obend.Receipt.Merkle.mapRoot Obend.Core.Digest.deployed leaves
              let resp := Json.mkObj [
                ("schema", toJson "obend.ffi.workbook_scrub.v1"),
                ("status", toJson "accepted"),
                ("cellKey", toJson cellKey),
                ("fieldName", toJson fieldName),
                ("patchOps", toJson patch.length),
                ("dirtyCone", toJson dirty),
                ("merkleRootHex", toJson (nat256ToHex rootNat)),
                ("view", updatedViewJson),
                ("cells", Json.arr (wb'.cells.toArray.map encodeCachedCellJson))
              ]
              .ok (wb', resp.compress.toUTF8)
        | _, _, _ =>
          .error (-3, "Workbook scrub JSON requires 'cellKey', 'fieldName', and 'newValue'")

theorem stepWorkbookJsonBytes_empty_refused (wb : Workbook) :
    stepWorkbookJsonBytes wb ByteArray.empty = .error (-3, "Empty workbook step payload") := by
  unfold stepWorkbookJsonBytes; rfl

theorem scrubWorkbookCellJsonBytes_empty_refused (wb : Workbook) :
    scrubWorkbookCellJsonBytes wb ByteArray.empty = .error (-3, "Empty workbook scrub payload") := by
  unfold scrubWorkbookCellJsonBytes; rfl

end Obend.FFI
end
