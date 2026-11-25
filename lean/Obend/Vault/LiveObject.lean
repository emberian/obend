module
public import Obend.Doc.GroveLiveObject
public import Obend.Vault.Store
import all Obend.Vault.Store

public section
namespace Obend.Vault.LiveObject
open Obend.Doc Obend.Doc.LiveObject Obend.Core.Machine Obend.Core.MachineTyping
open Obend.Core.HeapImage Obend.Core.Data Obend.Codec.Hex Lean
set_option autoImplicit false

/-! ## Total Structural `Core.Data ↔ Json` Codec for Wire Certificates -/

private def atomNumber : Json → Option Nat
  | .num n => if n.exponent == 0 && n.mantissa ≥ 0 then some n.mantissa.toNat else none
  | _ => none

mutual
private def dataToJson : Data → Json
  | .natural n => .arr #[.str "n", .num ⟨.ofNat n, 0⟩]
  | .boolean b => .arr #[.str "b", .bool b]
  | .label s => .arr #[.str "l", .str s]
  | .record fs => .arr #[.str "r", .arr (fieldsToJson fs).toArray]
  | .variant t p => .arr #[.str "v", .str t, dataToJson p]

private def fieldsToJson : List (String × Data) → List Json
  | [] => []
  | (k, v) :: rest => .arr #[.str k, dataToJson v] :: fieldsToJson rest
end

mutual
private def jsonToData : Json → Except String Data
  | .arr ⟨[.str "n", jn]⟩ =>
    match atomNumber jn with
    | some n => .ok (.natural n)
    | none => .error "invalid natural in certificate"
  | .arr ⟨[.str "b", .bool b]⟩ => .ok (.boolean b)
  | .arr ⟨[.str "l", .str s]⟩ => .ok (.label s)
  | .arr ⟨[.str "r", .arr ⟨fs⟩]⟩ => (jsonToFields fs).map .record
  | .arr ⟨[.str "v", .str t, jp]⟩ => (jsonToData jp).map (.variant t)
  | _ => .error "invalid certificate data"

private def jsonToFields : List Json → Except String (List (String × Data))
  | [] => .ok []
  | .arr ⟨[.str k, jv]⟩ :: rest => do
    let v ← jsonToData jv
    let rs ← jsonToFields rest
    pure ((k, v) :: rs)
  | _ :: _ => .error "expected field pair array"
end

mutual
private theorem jsonToData_dataToJson : ∀ d : Data, jsonToData (dataToJson d) = .ok d
  | .natural n => by simp [dataToJson, jsonToData, atomNumber]
  | .boolean b => by simp [dataToJson, jsonToData]
  | .label s => by simp [dataToJson, jsonToData]
  | .variant t p => by simp [dataToJson, jsonToData, Except.map, jsonToData_dataToJson p]
  | .record fs => by simp [dataToJson, jsonToData, Except.map, jsonToFields_fieldsToJson fs]

private theorem jsonToFields_fieldsToJson : ∀ fs : List (String × Data),
    jsonToFields (fieldsToJson fs) = .ok fs
  | [] => rfl
  | (k, v) :: rest => by
    simp [fieldsToJson, jsonToFields, jsonToData_dataToJson v, jsonToFields_fieldsToJson rest]
end

/-! ## Checked Living-Object Wire Write (`core4.checkpoint`) -/

/-- A verified checkpoint write carrying both the machine `State` and its executable
`StateCert` whose verification `checkStateCert cert state = true` is re-checked on decode. -/
structure Write where
  page : String
  atom : AtomId
  parent : AtomId
  name : String
  state : State
  cert : StateCert
  verified : checkStateCert cert state = true

theorem Write.stateTyping (w : Write) :
    Nonempty (StateTyping w.cert.assumptions w.cert.addressTypes w.state w.cert.result) :=
  checkStateCert_sound w.verified

/-- Encode a checkpoint write using zero-`List` `ByteArray` hex (`encodeImageText`) for
the heap image plus canonical JSON for its `StateCert`. -/
def Write.encode (w : Write) : Json :=
  .arr #[.str w.page, .num ⟨.ofNat w.atom, 0⟩, .num ⟨.ofNat w.parent, 0⟩, .str w.name,
    .str (encodeImageText w.state), dataToJson (stateCertData w.cert)]

/-- Decode and re-verify a checkpoint write from untrusted wire JSON.
Rejects invalid hex, invalid heap image bytes, malformed certificates, AND any
state failing executable `StateTyping` / `LexicalInvariant` / `BusyInvariant` / `FinalStackInvariant`. -/
def Write.decode (j : Json) : Except String Write := do
  let .arr a := j | throw "expected checkpoint fields"
  let [.str page, atom, parent, .str name, .str hex, certJson] := a.toList
    | throw "expected page, atom, parent, name, heap image and typing certificate"
  let some id := atomNumber atom | throw "invalid atom"
  let some afterId := atomNumber parent | throw "invalid parent"
  let some state := decodeImageText hex | throw "invalid heap image"
  let certData ← jsonToData certJson
  let some cert := stateCertOf certData | throw "invalid typing certificate"
  if hok : checkStateCert cert state = true then
    return ⟨page, id, afterId, name, state, cert, hok⟩
  else
    throw "checkpoint state failed executable typing verification"

theorem Write.decode_encode (w : Write) : Write.decode w.encode = .ok w := by
  obtain ⟨p, a, parent, name, s, cert, hok⟩ := w
  simp [Write.decode, Write.encode, atomNumber, jsonToData_dataToJson, hok]

/-- Request exactly one ordinary, judged page version. Allocates a fresh atom OR
advances/supersedes an existing live checkpoint atom in place across turns. -/
def Write.version (w : Write) (s : Store) : Except String PageWrite := do
  let some g := (s.page? w.page).bind Page.current | throw "missing checkpoint page"
  let some next := Doc.LiveObject.allocate g w.atom w.parent w.name w.state w.cert
    | throw "checkpoint needs a fresh atom with live parent or an existing live checkpoint atom"
  return { versions := [(next, [(w.atom, Actor.owner.name)])] }

def Write.land (w : Write) (s : Store) : Except String Store := do
  let v ← w.version s
  s.writeTexts [(w.page, v)]

theorem Write.land_frame {w : Write} {s t : Store} (ok : w.land s = .ok t)
    {n : String} (other : n ≠ w.page) : t.page? n = s.page? n := by
  cases hv : w.version s with
  | error msg => simp [Write.land, hv, bind, Except.bind] at ok
  | ok v =>
    apply writeTexts_page?_ne (ws := [(w.page, v)]) (by simpa using other)
    simpa [Write.land, hv, bind, Except.bind] using ok

/-- Choice-free raw read of a live checkpoint state from `Store` (verifies `ByteArray` decode + 256-bit CID). -/
def readAtRaw (s : Store) (page : String) (atom : AtomId) : Option State :=
  ((s.page? page).bind Page.current).bind (Doc.LiveObject.loadRaw · atom)

/-- Verified read of a live checkpoint state from `Store` (verifies `ByteArray` decode, 256-bit CID, and `checkStateCert`). -/
def readAt (s : Store) (page : String) (atom : AtomId) : Option State :=
  ((s.page? page).bind Page.current).bind (Doc.LiveObject.load · atom)

private theorem singleVersion_current {s landed : Store} {page : String} {p : Page}
    {g : Graph} {authors : List (AtomId × String)} (found : s.page? page = some p)
    (ok : s.writeTexts [(page, { versions := [(g, authors)] })] = .ok landed) :
    (landed.page? page).bind Page.current = some g := by
  have named : p.name = page := by simpa using List.find?_some found
  have one : [page].eraseDups.length = 1 := rfl
  cases hp : prepareFrom (p.current.map fun g => (g, p.history.length - 1)) s.entries p
      g authors .owner s.turn Actor.owner.name s.environment with
  | error msg =>
    simp [Store.writeTexts, prepareTexts, found, hp, one] at ok
  | ok pr =>
    have parts := prepareFrom_page hp
    have hn : pr.p.name = page := parts.1 ▸ named
    simp [Store.writeTexts, prepareTexts, found, hp, one] at ok
    split at ok <;> try contradiction
    cases ok
    unfold Store.page? at found ⊢
    unfold Store.landTexts
    simp only
    rw [find?_map_page s _ (fun q => by
      by_cases h : pr.p.name = q.name <;> simp [h]) page, found]
    simp [hn, named, Page.current, parts.2]

/-- Every successful deployed write (fresh allocation OR in-place turn advance) reads back
the exact certified state it admitted. -/
theorem readAt_land {w : Write} {s t : Store} (ok : w.land s = .ok t) :
    readAt t w.page w.atom = some w.state := by
  cases found : s.page? w.page with
  | none => simp [Write.land, Write.version, found, bind, Except.bind] at ok
  | some p =>
    cases current : p.current with
    | none => simp [Write.land, Write.version, found, current, bind, Except.bind] at ok
    | some g =>
      cases allocated : Doc.LiveObject.allocate g w.atom w.parent w.name w.state w.cert with
      | none => simp [Write.land, Write.version, found, current, allocated, bind, Except.bind] at ok
      | some next =>
        have written : s.writeTexts [(w.page, { versions := [(next, [(w.atom, Actor.owner.name)])] })] = .ok t := by
          simpa [Write.land, Write.version, found, current, allocated, bind, Except.bind, pure, Except.pure] using ok
        have latest := singleVersion_current found written
        change ((t.page? w.page).bind Page.current).bind _ = _
        rw [latest]
        exact Doc.LiveObject.load_allocate w.verified allocated

theorem readAtRaw_land {w : Write} {s t : Store} (ok : w.land s = .ok t) :
    readAtRaw t w.page w.atom = some w.state := by
  cases found : s.page? w.page with
  | none => simp [Write.land, Write.version, found, bind, Except.bind] at ok
  | some p =>
    cases current : p.current with
    | none => simp [Write.land, Write.version, found, current, bind, Except.bind] at ok
    | some g =>
      cases allocated : Doc.LiveObject.allocate g w.atom w.parent w.name w.state w.cert with
      | none => simp [Write.land, Write.version, found, current, allocated, bind, Except.bind] at ok
      | some next =>
        have written : s.writeTexts [(w.page, { versions := [(next, [(w.atom, Actor.owner.name)])] })] = .ok t := by
          simpa [Write.land, Write.version, found, current, allocated, bind, Except.bind, pure, Except.pure] using ok
        have latest := singleVersion_current found written
        change ((t.page? w.page).bind Page.current).bind _ = _
        rw [latest]
        exact Doc.LiveObject.loadRaw_allocate allocated

end Obend.Vault.LiveObject
