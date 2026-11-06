module
/-
# Obend.Vault.Json — the world beside a vault, as `.obend/world.json`

Every page with its versions (each a graph: atoms, tombstones, order edges), the text last seen of
its file, who added each atom, the last refusal; the members and their grants; the turn. A cite is
stored whole: its page, span, version, mode and byte commitment (hex), so a pinned cite stays
checkable against the version it names.
-/
public import Obend.Vault.Store
public import Obend.Doc.Structured
public import Obend.Spec.DataWire
public import Lean.Data.Json
@[expose] public section

namespace Obend.Vault.Json

set_option autoImplicit false

open Lean (Json ToJson FromJson toJson fromJson?)
open Obend.Doc Obend.Vault

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex (b : List UInt8) : String :=
  String.ofList (b.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

def unhexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else none

def unhex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← unhexDigit a
    let y ← unhexDigit b
    let r ← unhex rest
    return (x * 16 + y).toUInt8 :: r
  | [_] => none

def spanJson : Span → Json
  | .identity => "identity"
  | .page => "page"
  | .block b => Json.mkObj [("block", b)]
  | .bytes r => Json.mkObj [("bytes", Json.arr #[toJson r.start, toJson r.len])]

def spanOf (j : Json) : Except String Span :=
  match j with
  | .str "identity" => .ok .identity
  | .str "page" => .ok .page
  | _ => match j.getObjValAs? String "block" with
    | .ok b => .ok (.block b)
    | .error _ => do
      let r ← j.getObjValAs? (Array Nat) "bytes"
      match r.toList with
      | [s, l] => .ok (.bytes ⟨s, l⟩)
      | _ => .error "bad span"

def contentJson : Content → Json
  | .text s => Json.mkObj [("t", s)]
  | .cite n c => Json.mkObj [("c", n), ("page", toJson c.page), ("span", spanJson c.span),
      ("v", toJson c.version), ("h", hex c.commitment),
      ("mode", if c.mode == .pinned then "pinned" else "following")]
  | .field n v => Json.mkObj [("f", n), ("value", v)]
  | .cell id k ast pins receipt => Json.mkObj [
      ("cell", toJson id),
      ("kind", toJson (ProjectionKind.toLabel k)),
      ("ast", Obend.Spec.DataWire.dataJson ast),
      ("pins", Json.arr (pins.map fun p => Json.mkObj [("name", toJson p.1), ("hash", toJson (byteArrayToHex p.2))]).toArray),
      ("receipt", match receipt with | some r => toJson (byteArrayToHex r) | none => Json.null)
    ]

def contentOf (j : Json) : Except String Content :=
  match j.getObjValAs? String "cell" with
  | .ok id => do
    let kindStr ← j.getObjValAs? String "kind"
    let some kind := ProjectionKind.ofLabel kindStr | .error "unknown projection kind"
    let astJson ← j.getObjVal? "ast"
    let ast ← Obend.Spec.DataWire.decodeData 100 astJson
    let pinsJson ← j.getObjValAs? (Array Json) "pins"
    let pins ← pinsJson.toList.mapM fun pj => do
      let name ← pj.getObjValAs? String "name"
      let h ← pj.getObjValAs? String "hash"
      let some bytes := hexToByteArray h | .error "bad pin hash"
      return (name, bytes)
    let receipt ← match j.getObjVal? "receipt" with
      | .ok (.str r) => match hexToByteArray r with
        | some b => pure (some b)
        | none => .error "bad receipt hex"
      | _ => pure none
    .ok (.cell id kind ast pins receipt)
  | .error _ =>
    match j.getObjValAs? String "t" with
    | .ok s => .ok (.text s)
    | .error _ => match j.getObjValAs? String "c" with
      | .ok n => do
        let page ← j.getObjValAs? Nat "page"
        let span ← spanOf (← j.getObjVal? "span")
        let v ← j.getObjValAs? Nat "v"
        let h ← j.getObjValAs? String "h"
        let some bytes := unhex h.toList | .error "bad commitment"
        let mode ← j.getObjValAs? String "mode"
        .ok (.cite n ⟨page, span, v, bytes, if mode == "pinned" then .pinned else .following⟩)
      | .error _ => do
        let n ← j.getObjValAs? String "f"
        let v ← j.getObjValAs? String "value"
        .ok (.field n v)

def graphJson (G : Graph) : Json :=
  Json.mkObj [
    ("atoms", Json.arr (G.atoms.map fun (a, c) => Json.arr #[toJson a, contentJson c]).toArray),
    ("dead", toJson G.dead),
    ("edges", Json.arr (G.edges.map fun (a, b) => Json.arr #[toJson a, toJson b]).toArray)]

def pairNat (j : Json) : Except String (Nat × Nat) := do
  let a ← j.getArrVal? 0 >>= fromJson?
  let b ← j.getArrVal? 1 >>= fromJson?
  return (a, b)

def graphOf (j : Json) : Except String Graph := do
  let atoms ← (← j.getObjValAs? (Array Json) "atoms").toList.mapM fun e => do
    let a ← e.getArrVal? 0 >>= fromJson?
    let c ← contentOf (← e.getArrVal? 1)
    return (a, c)
  let dead ← j.getObjValAs? (List Nat) "dead"
  let edges ← (← j.getObjValAs? (Array Json) "edges").toList.mapM pairNat
  return { atoms := atoms, dead := dead, edges := edges }

def kindVersionJson (f : Obend.Kind.KindVersion) : Json :=
  Json.mkObj [("kind", Json.str f.name), ("version", toJson f.version)]

def kindVersionOf (j : Json) : Except String Obend.Kind.KindVersion := do
  return ⟨← j.getObjValAs? String "kind", ← j.getObjValAs? Nat "version"⟩

/-- A page's kind pin: its kind's version, then every ancestor's. -/
def pinJson (p : Obend.Kind.KindPin) : Json :=
  Json.arr (p.lineage.map kindVersionJson).toArray

def pinOf (j : Json) : Except String Obend.Kind.KindPin := do
  match (← (← j.getArr?).toList.mapM kindVersionOf) with
  | f :: rest => return ⟨f.name, f.version, rest⟩
  | [] => throw "a kind pin names its kind"

/-- A page's history, written as its versions' growth: each version that extends the one before it
(its atoms, tombstones and edges the earlier ones and then more, as every authored operation and every
merge leaves it) is written as what it adds (`{"more": …}`); any other in full. A history kept as
whole graphs is the sum of its versions' sizes, quadratic in a page's versions (2026-11-06: a status
of ten pages of 220 versions read and wrote a 17 MB checkpoint); written as growth it is its last
version's size. -/
def historyJson : List Graph → List Json
  | [] => []
  | G :: rest => graphJson G :: go G rest
where
  go (prev : Graph) : List Graph → List Json
    | [] => []
    | G :: rest =>
      let grown := prev.atoms.isPrefixOf G.atoms && prev.dead.isPrefixOf G.dead && prev.edges.isPrefixOf G.edges
      let more : Graph := ⟨G.atoms.drop prev.atoms.length, G.dead.drop prev.dead.length, G.edges.drop prev.edges.length⟩
      (if grown then Json.mkObj [("more", graphJson more)] else graphJson G) :: go G rest

/-- A history as `historyJson` writes it (or every version in full, as earlier logs hold it). -/
def historyOf (js : List Json) : Except String (List Graph) := do
  let (_, out) ← js.foldlM (fun (acc : Option Graph × Array Graph) j => do
    match j.getObjVal? "more", acc.1 with
    | .ok m, some prev =>
      let d ← graphOf m
      let G : Graph := ⟨prev.atoms ++ d.atoms, prev.dead ++ d.dead, prev.edges ++ d.edges⟩
      pure (some G, acc.2.push G)
    | .ok _, none => throw "a history begins with a whole version"
    | .error _, _ =>
      let G ← graphOf j
      pure (some G, acc.2.push G)) ((none : Option Graph), #[])
  return out.toList

/-- A page's JSON with its history in full: each `{"more": …}` written as the whole version it grows
to, as histories were written before `historyJson` (a world those binaries committed to is committed
to in this encoding). -/
def fullHistoryPage (j : Json) : Json :=
  match j.getObjValAs? (Array Json) "history" with
  | .error _ => j
  | .ok hs =>
    let arr (g : Json) (k : String) : Array Json := (g.getObjValAs? (Array Json) k).toOption.getD #[]
    let (_, out) := hs.foldl (fun (acc : Option Json × Array Json) h =>
      match h.getObjVal? "more", acc.1 with
      | .ok m, some prev =>
        let g := Json.mkObj [("atoms", Json.arr (arr prev "atoms" ++ arr m "atoms")),
          ("dead", Json.arr (arr prev "dead" ++ arr m "dead")), ("edges", Json.arr (arr prev "edges" ++ arr m "edges"))]
        (some g, acc.2.push g)
      | _, _ => (some h, acc.2.push h)) ((none : Option Json), #[])
    j.setObjVal! "history" (Json.arr out)

/-- A store's JSON with every history in full (`fullHistoryPage`). -/
def fullHistories (j : Json) : Json :=
  let pages (k : String) (j : Json) : Json := match j.getObjValAs? (Array Json) k with
    | .ok ps => j.setObjVal! k (Json.arr (ps.map fullHistoryPage))
    | .error _ => j
  pages "tombs" (pages "pages" j)

def pageJson (p : Page) : Json :=
  Json.mkObj ([("name", Json.str p.name), ("id", toJson p.id), ("history", Json.arr (historyJson p.history).toArray),
    ("seen", match p.seen with | some t => Json.str t | none => Json.null),
    ("authors", Json.arr (p.authors.map fun (a, w) => Json.arr #[toJson a, Json.str w]).toArray),
    ("note", match p.note with | some t => Json.str t | none => Json.null)] ++
    (match p.kind with | some k => [("kind", pinJson k)] | none => []))

def optStr (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

def pageOf (j : Json) : Except String Page := do
  let name ← j.getObjValAs? String "name"
  let id ← j.getObjValAs? Nat "id"
  let history ← historyOf (← j.getObjValAs? (Array Json) "history").toList
  let authors ← (← j.getObjValAs? (Array Json) "authors").toList.mapM fun e => do
    let a ← e.getArrVal? 0 >>= fromJson?
    let w ← e.getArrVal? 1 >>= fromJson?
    return (a, w)
  let kind ← match j.getObjVal? "kind" with
    | .ok k => some <$> pinOf k
    | .error _ => pure none
  return ⟨name, id, history, optStr j "seen", authors, optStr j "note", kind⟩

def memberJson (m : Member) : Json :=
  Json.mkObj [("name", m.name), ("id", toJson m.id),
    ("grants", Json.arr (m.grants.map fun (v, p) => Json.arr #[Json.str v, Json.str p]).toArray)]

def memberOf (j : Json) : Except String Member := do
  let name ← j.getObjValAs? String "name"
  let id ← j.getObjValAs? Nat "id"
  let grants ← (← j.getObjValAs? (Array Json) "grants").toList.mapM fun e => do
    let v ← e.getArrVal? 0 >>= fromJson?
    let p ← e.getArrVal? 1 >>= fromJson?
    return (v, p)
  return ⟨name, id, grants⟩

def authorsJson (as : List (AtomId × String)) : Json :=
  Json.arr (as.map fun (a, w) => Json.arr #[toJson a, Json.str w]).toArray

def authorsOf (j : Json) : Except String (List (AtomId × String)) := do
  (← j.getArr?).toList.mapM fun e => do
    let a ← e.getArrVal? 0 >>= fromJson?
    let w ← e.getArrVal? 1 >>= fromJson?
    return (a, w)

def pageWriteJson (w : PageWrite) : Json :=
  Json.mkObj ([("versions", Json.arr (w.versions.map fun (G, as) =>
      Json.mkObj [("graph", graphJson G), ("added", authorsJson as)]).toArray)] ++
    (match w.poster with | some p => [("poster", Json.str p)] | none => []))

def pageWriteOf (j : Json) : Except String PageWrite := do
  let vs ← (← j.getObjValAs? (Array Json) "versions").toList.mapM fun v => do
    return (← graphOf (← v.getObjVal? "graph"), ← authorsOf (← v.getObjVal? "added"))
  return { versions := vs, poster := optStr j "poster" }

def candidateJson (c : String × String × PageWrite) : Json :=
  Json.mkObj [("origin", Json.str c.1), ("label", Json.str c.2.1), ("write", pageWriteJson c.2.2)]

def candidateOf (j : Json) : Except String (String × String × PageWrite) := do
  return (← j.getObjValAs? String "origin", ← j.getObjValAs? String "label", ← pageWriteOf (← j.getObjVal? "write"))

def conflictJson (c : PageConflict) : Json :=
  Json.mkObj [("page", Json.str c.page), ("left", candidateJson c.left), ("right", candidateJson c.right)]

def conflictOf (j : Json) : Except String PageConflict := do
  return ⟨← j.getObjValAs? String "page", ← candidateOf (← j.getObjVal? "left"), ← candidateOf (← j.getObjVal? "right")⟩

def schema : String := "obend.vault.world.v1"

def storeJson (s : Store) : Json :=
  let base : List (String × Json) := [("schema", schema), ("turn", toJson s.turn),
    ("members", Json.arr (s.members.map memberJson).toArray),
    ("pages", Json.arr (s.pages.map pageJson).toArray)]
  let tombs : List (String × Json) :=
    if s.tombs.isEmpty then [] else [("tombs", Json.arr (s.tombs.map pageJson).toArray)]
  let conflicts : List (String × Json) :=
    if s.conflicts.isEmpty then [] else [("conflicts", Json.arr (s.conflicts.map conflictJson).toArray)]
  Json.mkObj (base ++ tombs ++ conflicts)

def storeOf (j : Json) : Except String Store := do
  let sc ← j.getObjValAs? String "schema"
  if sc != schema then throw ("not a " ++ schema ++ ": " ++ sc)
  let turn ← j.getObjValAs? Nat "turn"
  let members ← (← j.getObjValAs? (Array Json) "members").toList.mapM memberOf
  let pages ← (← j.getObjValAs? (Array Json) "pages").toList.mapM pageOf
  let tombs ← match j.getObjVal? "tombs" with
    | .ok (.arr ts) => ts.toList.mapM pageOf
    | _ => pure []
  let conflicts ← match j.getObjVal? "conflicts" with
    | .ok (.arr cs) => cs.toList.mapM conflictOf
    | _ => pure []
  return { pages := pages, members := members, turn := turn, tombs := tombs, conflicts := conflicts }

end Obend.Vault.Json

end
