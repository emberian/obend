module
public import Obend.Doc.GroveLiveObject
public import Obend.Vault.Store
import all Obend.Vault.Store

public section
namespace Obend.Vault.LiveObject
open Obend.Doc Obend.Core.Machine Obend.Core.HeapImage Obend.Codec.Hex Lean
set_option autoImplicit false

structure Write where
  page : String
  atom : AtomId
  parent : AtomId
  name : String
  state : State

def Write.encode (w : Write) : Json :=
  .arr #[.str w.page, .num ⟨.ofNat w.atom, 0⟩, .num ⟨.ofNat w.parent, 0⟩, .str w.name,
    .str (byteArrayToHex (encodeHeapImage w.state))]

private def atomNumber : Json → Option Nat
  | .num n => if n.exponent == 0 && n.mantissa ≥ 0 then some n.mantissa.toNat else none
  | _ => none

def Write.decode (j : Json) : Except String Write := do
  let .arr a := j | throw "expected checkpoint fields"
  let [.str page, atom, parent, .str name, .str hex] := a.toList
    | throw "expected page, atom, parent, name and heap image"
  let some id := atomNumber atom | throw "invalid atom"
  let some afterId := atomNumber parent | throw "invalid parent"
  let some state := Doc.LiveObject.decodeImageText hex | throw "invalid heap image"
  return ⟨page, id, afterId, name, state⟩

theorem Write.decode_encode (w : Write) : Write.decode w.encode = .ok w := by
  obtain ⟨p, a, parent, name, s⟩ := w
  simp [Write.decode, Write.encode, atomNumber]

/-- Request exactly one ordinary, judged page version. Replay decodes a syntactic
image. Source typing belongs to certified producers and their unchanged checkpoints. -/
def Write.version (w : Write) (s : Store) : Except String PageWrite := do
  let some g := (s.page? w.page).bind Page.current | throw "missing checkpoint page"
  let some next := Doc.LiveObject.allocate g w.atom w.parent w.name w.state
    | throw "checkpoint needs a fresh atom and a live parent"
  return {versions := [(next, [(w.atom, Actor.owner.name)])]}

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

/-- Every successful deployed write reads back the very state it admitted.
The conclusion follows through the store's judged page history and its decoder. -/
theorem readAt_land {w : Write} {s t : Store} (ok : w.land s = .ok t) :
    readAt t w.page w.atom = some w.state := by
  cases found : s.page? w.page with
  | none => simp [Write.land, Write.version, found, bind, Except.bind] at ok
  | some p =>
    cases current : p.current with
    | none => simp [Write.land, Write.version, found, current, bind, Except.bind] at ok
    | some g =>
      cases allocated : Doc.LiveObject.allocate g w.atom w.parent w.name w.state with
      | none => simp [Write.land, Write.version, found, current, allocated, bind, Except.bind] at ok
      | some next =>
        have written : s.writeTexts [(w.page, {versions := [(next, [(w.atom, Actor.owner.name)])]})] = .ok t := by
          simpa [Write.land, Write.version, found, current, allocated, bind, Except.bind, pure, Except.pure] using ok
        have latest := singleVersion_current found written
        change ((t.page? w.page).bind Page.current).bind _ = _
        rw [latest]
        exact Doc.LiveObject.load_allocate allocated

end Obend.Vault.LiveObject
