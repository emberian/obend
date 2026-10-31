module
/-
# Obend.Vault.Json — the world beside a vault, as `.obend/world.json`

Every page with its versions (each a graph: atoms, tombstones, order edges), the text last seen of
its file, who added each atom, the last refusal; the members and their grants; the turn. A cite is
stored whole: its page, span, version, mode and byte commitment (hex), so a pinned cite stays
checkable against the version it names.
-/
public import Obend.Vault.Store
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

def contentOf (j : Json) : Except String Content :=
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

def pageJson (p : Page) : Json :=
  Json.mkObj [("name", p.name), ("id", toJson p.id), ("history", Json.arr (p.history.map graphJson).toArray),
    ("seen", match p.seen with | some t => Json.str t | none => Json.null),
    ("authors", Json.arr (p.authors.map fun (a, w) => Json.arr #[toJson a, Json.str w]).toArray),
    ("note", match p.note with | some t => Json.str t | none => Json.null)]

def optStr (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

def pageOf (j : Json) : Except String Page := do
  let name ← j.getObjValAs? String "name"
  let id ← j.getObjValAs? Nat "id"
  let history ← (← j.getObjValAs? (Array Json) "history").toList.mapM graphOf
  let authors ← (← j.getObjValAs? (Array Json) "authors").toList.mapM fun e => do
    let a ← e.getArrVal? 0 >>= fromJson?
    let w ← e.getArrVal? 1 >>= fromJson?
    return (a, w)
  return ⟨name, id, history, optStr j "seen", authors, optStr j "note"⟩

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

def schema : String := "obend.vault.world.v1"

def storeJson (s : Store) : Json :=
  Json.mkObj [("schema", schema), ("turn", toJson s.turn),
    ("members", Json.arr (s.members.map memberJson).toArray),
    ("pages", Json.arr (s.pages.map pageJson).toArray)]

def storeOf (j : Json) : Except String Store := do
  let sc ← j.getObjValAs? String "schema"
  if sc != schema then throw ("not a " ++ schema ++ ": " ++ sc)
  let turn ← j.getObjValAs? Nat "turn"
  let members ← (← j.getObjValAs? (Array Json) "members").toList.mapM memberOf
  let pages ← (← j.getObjValAs? (Array Json) "pages").toList.mapM pageOf
  return { pages := pages, members := members, turn := turn }

end Obend.Vault.Json

end
