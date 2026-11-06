module
/-
# Obend.Vault.BranchCli — `obend branch`: branches of a store on disk, merged at the tip

A store on disk is one JSON file: its pages (owner, law lines, links, declared merges, state), its
sturdyrefs and revocations, its receipted history and its open conflicts (`Obend.Vault.Branch.Config`).
A branch is a file holding the store it forked from and the acts it posted since. Every act posted
to a branch is judged at once at the branch's own configuration (offline, by `Branch.run`); `merge`
judges them again at the tip.

    obend branch fork STORE BRANCH NAME
    obend branch write BRANCH LABEL PAGE FIELD=N… --as ACTOR [--relies URI,URI]
    obend branch relaw BRANCH LABEL PAGE --as ACTOR [--links P,Q] [--law NAME=TEXT]… [--merge FIELD=KIND]…
    obend branch grant BRANCH LABEL URI CELL --as ACTOR
    obend branch revoke BRANCH LABEL URI --as ACTOR
    obend branch merge STORE LEFT RIGHT TIP
    obend branch resolve TIP K left|right
    obend branch show STORE PAGE

This is `Obend.Vault.Branch` over its own store file; the markdown vault's `obend merge`
(`Obend.Vault.Store.mergeFrom`) is a separate command and is not routed through it.
-/
public import Obend.Vault.Branch
public import Lean.Data.Json
@[expose] public section

namespace Obend.Vault.BranchCli

set_option autoImplicit false

open Lean (Json toJson)
open Obend.Vault Obend.Vault.Branch
open Obend.Core.Data (Data)
open Obend.Vault.Affordance (Auth)

/-! ## The store file -/

def stateToJson : Data → Json
  | .record fs => Json.mkObj (fs.filterMap fun (k, v) => match v with
      | .natural n => some (k, toJson n)
      | .label s => some (k, toJson s)
      | .boolean b => some (k, toJson b)
      | _ => none)
  | _ => Json.mkObj []

def stateOfJson (j : Json) : Except String Data := do
  let o ← j.getObj?
  let fs ← o.toList.mapM fun (k, v) =>
    match v.getNat? with
    | .ok n => pure (k, Data.natural n)
    | .error _ => match v.getStr? with
      | .ok s => pure (k, Data.label s)
      | .error _ => match v.getBool? with
        | .ok b => pure (k, Data.boolean b)
        | .error _ => throw ("field " ++ k ++ ": a number, a string or a boolean")
  pure (.record fs)

def authName : Auth → String
  | .read => "read" | .write => "write" | .grant => "grant" | .call => "call"
  | .reply => "reply" | .reset => "reset" | .control => "control" | .notify => "notify"

def authOf? (s : String) : Option Auth :=
  [Auth.read, .write, .grant, .call, .reply, .reset, .control, .notify].find? (authName · == s)

def sturdyref (uri cell : String) (held : List Auth) : Rehydration.Sturdyref Data :=
  { uri := uri, surface := [], log := [], lineage := { held := held, permits := fun _ => true }, cellId := cell }

def srToJson (sr : Rehydration.Sturdyref Data) : Json :=
  Json.mkObj [("uri", toJson sr.uri), ("cell", toJson sr.cellId), ("held", toJson (sr.lineage.held.map authName))]

def srOfJson (j : Json) : Except String (Rehydration.Sturdyref Data) := do
  let uri ← j.getObjValAs? String "uri"
  let cell ← j.getObjValAs? String "cell"
  let held := ((j.getObjValAs? (List String) "held").toOption.getD ["write"]).filterMap authOf?
  pure (sturdyref uri cell held)

/-- A law's short name: `PAGE: NAME` without the page. -/
def shortName (page n : String) : String :=
  if n.startsWith (page ++ ": ") then String.ofList (n.toList.drop (page.length + 2)) else n

def pageLawsToJson (page : String) (pl : PageLaws) : List (String × Json) :=
  [("owner", toJson pl.owner), ("links", toJson pl.links),
   ("laws", Json.arr (pl.laws.map fun (n, _, t) => toJson [shortName page n, t]).toArray),
   ("merges", Json.arr (pl.merges.map fun (f, k) => toJson [f, k.name]).toArray)]

def pairsOf (j : Json) (key : String) : List (String × String) :=
  ((j.getObjValAs? (List (List String)) key).toOption.getD []).filterMap fun
    | [a, b] => some (a, b)
    | _ => none

def pageLawsOfJson (page : String) (j : Json) : Except String PageLaws := do
  let owner ← j.getObjValAs? String "owner"
  let links := (j.getObjValAs? (List String) "links").toOption.getD []
  let pl ← PageLaws.ofLines page owner links (pairsOf j "laws")
  let merges ← (pairsOf j "merges").mapM fun (f, k) => match MergeKind.ofString? k with
    | some k => pure (f, k)
    | none => throw (page ++ ": merge " ++ f ++ ": no merge kind " ++ k ++ " (add, max, union)")
  pure { pl with merges := merges }

def turnToJson (t : BTurn) : Json :=
  Json.mkObj [("label", toJson t.label), ("actor", toJson t.actor), ("relies", toJson t.relies),
    ("pins", Json.arr (t.turn.readPins.map fun p =>
      Json.mkObj [("cell", toJson p.cell), ("state", (p.observed.map stateToJson).getD Json.null)]).toArray),
    ("writes", Json.arr (t.turn.writeCells.map fun d =>
      Json.mkObj [("cell", toJson d.cell), ("pre", stateToJson d.preState), ("post", stateToJson d.postState)]).toArray)]

def turnOfJson (j : Json) : Except String BTurn := do
  let label ← j.getObjValAs? String "label"
  let actor ← j.getObjValAs? String "actor"
  let relies := (j.getObjValAs? (List String) "relies").toOption.getD []
  let pins ← ((j.getObjVal? "pins").toOption.getD (Json.arr #[])).getArr?
  let pins ← pins.toList.mapM fun p => do
    let cell ← p.getObjValAs? String "cell"
    let st ← p.getObjVal? "state"
    if st.isNull then pure (⟨cell, none⟩ : FootprintPin) else pure ⟨cell, some (← stateOfJson st)⟩
  let ws ← (← j.getObjVal? "writes").getArr?
  let legs ← ws.toList.mapM fun w => do
    pure ((← w.getObjValAs? String "cell"), (← stateOfJson (← w.getObjVal? "pre")),
      (← stateOfJson (← w.getObjVal? "post")))
  match VaultTurn.ofWitnessLegs ByteArray.empty pins legs (.record []) [] with
  | some vt => pure { label := label, actor := actor, turn := vt, relies := relies }
  | none => throw (label ++ ": two legs write one cell")

def conflictToJson : Conflict → Json
  | .writes cs (ln, l) (rn, r) => Json.mkObj [("cells", toJson cs),
      ("left", Json.mkObj [("name", toJson ln), ("turn", turnToJson l)]),
      ("right", Json.mkObj [("name", toJson rn), ("turn", turnToJson r)])]
  | .laws p ln rn => Json.mkObj [("laws", toJson p), ("left", toJson ln), ("right", toJson rn)]

def conflictOfJson (j : Json) : Except String Conflict := do
  match j.getObjValAs? String "laws" with
  | .ok p => pure (.laws p ((j.getObjValAs? String "left").toOption.getD "") ((j.getObjValAs? String "right").toOption.getD ""))
  | .error _ =>
    let cs ← j.getObjValAs? (List String) "cells"
    let l ← j.getObjVal? "left"
    let r ← j.getObjVal? "right"
    pure (.writes cs ((← l.getObjValAs? String "name"), (← turnOfJson (← l.getObjVal? "turn")))
      ((← r.getObjValAs? String "name"), (← turnOfJson (← r.getObjVal? "turn"))))

def receiptToJson (r : Receipt) : Json :=
  Json.mkObj [("seq", toJson r.seq), ("origin", toJson r.origin), ("label", toJson r.label), ("cells", toJson r.cells)]

def receiptOfJson (j : Json) : Except String Receipt := do
  pure ⟨← j.getObjValAs? Nat "seq", ← j.getObjValAs? String "origin", ← j.getObjValAs? String "label",
    ← j.getObjValAs? (List String) "cells"⟩

def configToJson (c : Config) : Json :=
  Json.mkObj [
    ("pages", Json.arr (c.book.map fun (p, pl) =>
      Json.mkObj ([("name", toJson p)] ++ pageLawsToJson p pl ++
        [("state", (c.store p).map stateToJson |>.getD Json.null)])).toArray),
    ("sturdyrefs", Json.arr (c.auth.refs.map srToJson).toArray),
    ("revoked", toJson (c.auth.revoked.map fun (u, b) => [u, b])),
    ("history", Json.arr (c.history.map receiptToJson).toArray),
    ("conflicts", Json.arr (c.conflicts.map conflictToJson).toArray)]

def arrOf (j : Json) (key : String) : Except String (List Json) :=
  match j.getObjVal? key with
  | .ok v => do pure (← v.getArr?).toList
  | .error _ => pure []

def configOfJson (j : Json) : Except String Config := do
  let pages ← (← arrOf j "pages").mapM fun p => do
    let name ← p.getObjValAs? String "name"
    let pl ← pageLawsOfJson name p
    let st ← match p.getObjVal? "state" with
      | .ok s => if s.isNull then pure none else pure (some (← stateOfJson s))
      | .error _ => pure none
    pure (name, pl, st)
  let refs ← (← arrOf j "sturdyrefs").mapM srOfJson
  let history ← (← arrOf j "history").mapM receiptOfJson
  let conflicts ← (← arrOf j "conflicts").mapM conflictOfJson
  let states := pages.map fun (n, _, st) => (n, st)
  pure { store := fun c => ((states.lookup c).getD none),
         book := pages.map fun (n, pl, _) => (n, pl),
         auth := { refs := refs, revoked := pairsOf j "revoked" },
         history := history, conflicts := conflicts }

def actToJson : Act → Json
  | .write t => Json.mkObj [("write", turnToJson t)]
  | .relaw l a p pl => Json.mkObj [("relaw", Json.mkObj ([("label", toJson l), ("actor", toJson a),
      ("page", toJson p)] ++ pageLawsToJson p pl))]
  | .revoke l a u => Json.mkObj [("revoke", Json.mkObj [("label", toJson l), ("actor", toJson a), ("uri", toJson u)])]
  | .grant l a sr => Json.mkObj [("grant", Json.mkObj [("label", toJson l), ("actor", toJson a), ("ref", srToJson sr)])]

def actOfJson (j : Json) : Except String Act := do
  if let .ok w := j.getObjVal? "write" then return .write (← turnOfJson w)
  if let .ok r := j.getObjVal? "relaw" then
    let p ← r.getObjValAs? String "page"
    return .relaw (← r.getObjValAs? String "label") (← r.getObjValAs? String "actor") p (← pageLawsOfJson p r)
  if let .ok r := j.getObjVal? "revoke" then
    return .revoke (← r.getObjValAs? String "label") (← r.getObjValAs? String "actor") (← r.getObjValAs? String "uri")
  if let .ok g := j.getObjVal? "grant" then
    return .grant (← g.getObjValAs? String "label") (← g.getObjValAs? String "actor") (← srOfJson (← g.getObjVal? "ref"))
  throw "an act is a write, a relaw, a revoke or a grant"

/-- A branch on disk: its name, the store it forked from, and its acts. -/
structure BranchFile where
  name : String
  base : Config
  acts : List Act

def branchToJson (b : BranchFile) : Json :=
  Json.mkObj [("name", toJson b.name), ("base", configToJson b.base),
    ("acts", Json.arr (b.acts.map actToJson).toArray)]

def branchOfJson (j : Json) : Except String BranchFile := do
  pure ⟨← j.getObjValAs? String "name", ← configOfJson (← j.getObjVal? "base"),
    ← (← arrOf j "acts").mapM actOfJson⟩

def BranchFile.branch (b : BranchFile) : Branch := ⟨b.name, b.base.history, b.acts⟩

/-! ## The commands -/

def readJson (path : String) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw (IO.userError (path ++ ": " ++ e))

def orThrow {α : Type} (path : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError (path ++ ": " ++ e))

def readConfig (path : String) : IO Config := do orThrow path (configOfJson (← readJson path))
def readBranch (path : String) : IO BranchFile := do orThrow path (branchOfJson (← readJson path))
def writeJson (path : String) (j : Json) : IO Unit := IO.FS.writeFile path (j.pretty ++ "\n")

def flag (name : String) : List String → Option String × List String
  | [] => (none, [])
  | f :: v :: rest => if f == name then (some v, rest) else
    let (r, rest') := flag name (v :: rest)
    (r, f :: rest')
  | [x] => (none, [x])

/-- Every value of a repeated flag. -/
def flags (name : String) : List String → List String × List String
  | [] => ([], [])
  | f :: v :: rest =>
    if f == name then let (vs, r) := flags name rest; (v :: vs, r)
    else let (vs, r) := flags name (v :: rest); (vs, f :: r)
  | [x] => ([], [x])

def splitComma (s : String) : List String := (s.splitOn ",").filter (!·.isEmpty)

def splitEq (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | k :: v :: rest => some (k, "=".intercalate (v :: rest))
  | _ => none

/-- Post an act to a branch, after judging it at the branch's own configuration. -/
def post (path : String) (a : Act) : IO UInt32 := do
  let b ← readBranch path
  let r := b.branch.run b.base
  match admitAct r.config b.name a with
  | .ok _ =>
    writeJson path (branchToJson { b with acts := b.acts ++ [a] })
    IO.println (b.name ++ ": " ++ a.label ++ " admitted on its branch")
    return 0
  | .error e =>
    IO.println (b.name ++ ": " ++ a.label ++ " refused on its branch: " ++ e.text)
    return 3

def showState (d : Data) : String :=
  match d with
  | .record fs => ", ".intercalate (fs.map fun (k, v) => k ++ " " ++ showDatum v)
  | _ => showDatum d

def run (args : List String) : Option (IO UInt32) :=
  let (actor, args) := flag "--as" args
  let (relies, args) := flag "--relies" args
  let (links, args) := flag "--links" args
  let (laws, args) := flags "--law" args
  let (merges, args) := flags "--merge" args
  match args with
  | ["fork", store, path, name] => some do
    let c ← readConfig store
    writeJson path (branchToJson ⟨name, c, []⟩)
    IO.println (name ++ ": forked at receipt " ++ toString (c.history.length - 1))
    return 0
  | "write" :: path :: label :: page :: sets => some do
    let some who := actor | do IO.eprintln "write: --as ACTOR"; return 64
    let b ← readBranch path
    let cur := (b.branch.run b.base).config
    let some pre := cur.store page | do IO.eprintln (page ++ ": no such page on " ++ b.name); return 2
    let post' := sets.foldl (fun d s => match splitEq s with
      | some (k, v) => match v.toNat? with
        | some n => setNat d k n
        | none => d
      | none => d) pre
    match VaultTurn.ofWitnessLegs ByteArray.empty [] [(page, pre, post')] (.record []) [] with
    | some vt => post path (.write { label := label, actor := who, turn := vt, relies := (relies.map splitComma).getD [] })
    | none => return 2
  | ["relaw", path, label, page] => some do
    let some who := actor | do IO.eprintln "relaw: --as ACTOR"; return 64
    let lines := laws.filterMap splitEq
    let ms := (merges.filterMap splitEq).filterMap fun (f, k) => (MergeKind.ofString? k).map (f, ·)
    match PageLaws.ofLines page who ((links.map splitComma).getD []) lines with
    | .ok pl => post path (.relaw label who page { pl with merges := ms })
    | .error e => do IO.eprintln e; return 2
  | ["grant", path, label, uri, cell] => some do
    let some who := actor | do IO.eprintln "grant: --as ACTOR"; return 64
    post path (.grant label who (sturdyref uri cell [.write]))
  | ["revoke", path, label, uri] => some do
    let some who := actor | do IO.eprintln "revoke: --as ACTOR"; return 64
    post path (.revoke label who uri)
  | ["merge", store, left, right, tip] => some do
    let base ← readConfig store
    let l ← readBranch left
    let r ← readBranch right
    match merge base l.branch r.branch with
    | .error e => do IO.println ("not merged: " ++ e); return 3
    | .ok m =>
      for rc in m.tip.history.drop base.history.length do
        IO.println ("landed " ++ toString rc.seq ++ ": " ++ rc.origin ++ "'s " ++ rc.label)
      for (sd, label, e) in m.refused do
        IO.println ("refused: " ++ sideName l.name r.name sd ++ "'s " ++ label ++ ": " ++ e.text)
      for (c, k) in m.tip.conflicts.zipIdx do
        IO.println ("conflict " ++ toString k ++ ": " ++ c.text)
      writeJson tip (configToJson m.tip)
      return 0
  | ["resolve", tip, k, side] => some do
    let c ← readConfig tip
    let some k := k.toNat? | do IO.eprintln "resolve: K is a number"; return 64
    let pick := if side == "right" then Side.right else Side.left
    match resolve c k pick with
    | .ok c' =>
      writeJson tip (configToJson c')
      IO.println ("resolved conflict " ++ toString k ++ ": landed " ++ ((c'.history.getLast?.map (·.label)).getD ""))
      return 0
    | .error e => do IO.println ("not resolved: " ++ e); return 3
  | ["show", store, page] => some do
    let c ← readConfig store
    match c.store page with
    | some d => do IO.println (page ++ ": " ++ showState d); return 0
    | none => do IO.println (page ++ ": no such page"); return 2
  | _ => none

/-- `obend branch …`; `none` when the arguments are not a branch command. -/
def main? : List String → Option (IO UInt32)
  | "branch" :: rest => run rest
  | _ => none

end Obend.Vault.BranchCli

end
