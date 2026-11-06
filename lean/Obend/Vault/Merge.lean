module
/-
# Obend.Vault.Merge — `obend merge`: an offline copy of a vault is a branch, merged at the tip

`cp -R vault laptop` makes an offline copy; both go on writing; `obend merge ../laptop` brings the
copy's work back. The merge is `Obend.Vault.Branch.merge`, over the two stores read as branches of
the base they share:

* **The base** is what the two stores share: page by page, the longest common prefix of the two
  histories (`sharedPrefix`; a page deleted on one side is read from its tomb). The store keeps no
  vault-wide receipt chain yet (the replay lane's log will be one), so the receipt the copy was made
  at is read off the histories: the base's receipts are its pages' versions (`baseReceipts`).
* **A side's acts** are what it did since: for every page whose history moved past the base, a write
  (its state at the base to its state now, as one `writeTurn`, its read pins the pages its laws over
  links read at that side's states, `pinsAt`), and, when the page's laws moved, a relaw. The law book
  is the base's laws, each page linking to every page either side links it to (`bookOf`), so a law
  over links judges every page either side listed under it. Vault writes are the owner's; the
  markdown vault records no sturdyref grants or revocations on a copy, so the authority at the tip is
  the base's.
* **The merge decides everything above the page's text.** Writes of different pages are replayed at
  the tip, here's first; a write whose pins the other side moved is refused by name (`Branch.Refusal.stale`);
  every write is judged by every law of every page in its cone at the tip (`coneRefusal`), its laws
  read from the tip's book. Two writes of one page merge by their texts (`textMerge`): the pushout
  of the two versions (`mergePage`, `mergePage_pushout`), where two edits of one place become a
  section with both candidates; that merged write is judged at the tip like any other. Two versions
  that name one atom differently do not merge: a conflict.
* **Landing.** What the tip landed lands in the store through the vault's own write
  (`Store.write`, which also judges what a page state does not carry: laws over rows, kind pins):
  the other side's writes and the merged pages, each as one new version. Here's writes the tip did
  not land (refused, or held in a conflict) are taken back to the base: the page's store returns to
  its base version, its file keeps here's text as a refused write (`Page.note`), judged again when a
  pin it read moves, exactly as an open keeps a refused write.
-/
public import Obend.Vault.Branch
@[expose] public section

namespace Obend.Vault.Merge

open Obend.Vault Obend.Vault.Branch Obend.Doc Obend.Doc.Graph
open Obend.Core.Data (Data)

set_option autoImplicit false

/-- The versions two replicas of a page share: the longest common prefix of their histories. -/
def sharedPrefix : List Graph → List Graph → List Graph
  | a :: as, b :: bs => if a = b then a :: sharedPrefix as bs else []
  | _, _ => []

theorem sharedPrefix_prefix_left : ∀ (a b : List Graph), sharedPrefix a b <+: a
  | [], _ => by simp [sharedPrefix]
  | _ :: _, [] => by simp [sharedPrefix]
  | x :: xs, y :: ys => by
    simp only [sharedPrefix]
    split
    · exact List.cons_prefix_cons.2 ⟨rfl, sharedPrefix_prefix_left xs ys⟩
    · exact List.nil_prefix

theorem sharedPrefix_prefix_right : ∀ (a b : List Graph), sharedPrefix a b <+: b
  | [], _ => by simp [sharedPrefix]
  | _ :: _, [] => by simp [sharedPrefix]
  | x :: xs, y :: ys => by
    simp only [sharedPrefix]
    split
    · rename_i h; subst h; exact List.cons_prefix_cons.2 ⟨rfl, sharedPrefix_prefix_right xs ys⟩
    · exact List.nil_prefix

/-- The state of a page not born at the base: an empty record. -/
def unborn : Data := .record []

/-- A page's state at the last version of a history, or `unborn`. -/
def stateAt (h : List Graph) : Data :=
  match h.getLast? with
  | some G => pageState G (h.length - 1)
  | none => unborn

/-- A page's history in a store, live or in its tombs. -/
def historyIn (s : Store) (name : String) : List Graph :=
  match s.page? name with
  | some p => p.history
  | none => ((s.tombs.find? (·.name == name)).map (·.history)).getD []

/-- The live history of a page in a store (a deleted page acts on nothing). -/
def liveHistory (s : Store) (name : String) : List Graph := ((s.page? name).map (·.history)).getD []

/-- A page's laws as the tip judges them: its own and its kinds', the laws over rows left to the
vault's own write (`judgePrepared`). -/
def lawsAt (es : List Entry) (name : String) (G : Graph) : Laws :=
  ((lawsFor es name G).toOption.getD []).filter fun l => (lawSubject l.1).isNone

/-- What the merge reads of the two stores. -/
structure Plan where
  /-- the pages merged, here's first -/
  names : List String
  /-- each page's base history -/
  baseOf : String → List Graph
  /-- the base configuration -/
  base : Config
  left : Branch
  right : Branch
  /-- the text merge: each page both sides wrote, merged by `mergePage` -/
  text : TextMerge

/-- The entries of the base: each page born at the base, at its base version. -/
def baseEntries (here other : Store) (names : List String) (baseOf : String → List Graph) : List Entry :=
  names.filterMap fun n =>
    match (baseOf n).getLast?, (here.page? n).map (·.id) <|> (other.page? n).map (·.id) with
    | some G, some id => some ⟨n, id, G, (baseOf n).length - 1⟩
    | _, _ => none

/-- The base's receipts: one per version of every page at the base. -/
def baseReceipts (names : List String) (baseOf : String → List Graph) : List Receipt :=
  (names.flatMap fun n => (List.range (baseOf n).length).map fun k => (n, k)).zipIdx.map
    fun ((n, k), i) => ⟨i, "base", n ++ " v" ++ toString (k + 1), [n]⟩

/-- The pages a version links to, by name, itself left out. -/
def linksAt (es : List Entry) (name : String) (G : Graph) : List String :=
  (citedNames es G).filter (· != name)

/-- A side's write of a page: from its base state to its state now, its read pins the pages its laws
over links read, at the side's states. -/
def writeOf (s : Store) (name : String) (bp : List Graph) (G : Graph) : BTurn :=
  let pins := if hasLinkLaws s.entries name G then pinsAt s.entries (linksAt s.entries name G) else []
  { label := name, actor := "owner",
    turn := writeTurn name (stateAt bp) (pageState G ((liveHistory s name).length - 1)) pins
      (requestAt "owner" 0) }

/-- A side's writes in an order its own pins hold in: a write that pins a page the side also wrote
comes after that write (`fuel` bounds the passes; what is left is appended as it stands). -/
def orderWrites : Nat → List BTurn → List BTurn
  | 0, ws => ws
  | fuel + 1, ws =>
    match ws.partition fun w => w.turn.readPins.all fun p => !(ws.any fun w' => w'.label != w.label && w'.writes.contains p.cell) with
    | ([], rest) => rest
    | (ready, rest) => ready ++ orderWrites fuel rest

/-- A side's acts since the base: a relaw for every page whose laws moved, then its writes. -/
def actsOf (s : Store) (names : List String) (baseOf : String → List Graph) (baseLaws : String → Laws)
    (links : String → List String) : List Act :=
  let moved := names.filter fun n =>
    let h := liveHistory s n
    !h.isEmpty && h != baseOf n
  let relaws := moved.filterMap fun n =>
    match (liveHistory s n).getLast? with
    | some G =>
      let ls := lawsAt s.entries n G
      if ls == baseLaws n then none else some (Act.relaw (n ++ "'s laws") "owner" n ⟨"owner", ls, links n, []⟩)
    | none => none
  let writes := moved.filterMap fun n => (liveHistory s n).getLast?.map (writeOf s n (baseOf n))
  relaws ++ (orderWrites writes.length writes).map Act.write

/-- **Read two stores as two branches of their base.** Pages `skip` names (another merge's: the
ledger's register) are left out: at the base as here holds them, acted on by neither side. -/
def plan (here other : Store) (label : String) (skip : String → Bool := fun _ => false) : Plan :=
  let names := ((here.pages.map (·.name)) ++ (other.pages.map (·.name))).eraseDups
  let baseOf : String → List Graph := fun n =>
    if skip n then liveHistory here n else sharedPrefix (historyIn here n) (historyIn other n)
  let es := baseEntries here other names baseOf
  let baseLaws : String → Laws := fun n => lawsAt es n (((baseOf n).getLast?).getD Graph.empty)
  let links : String → List String := fun n =>
    ((((baseOf n).getLast?).map (linksAt es n)).getD [] ++
      (((liveHistory here n).getLast?).map (linksAt here.entries n)).getD [] ++
      (((liveHistory other n).getLast?).map (linksAt other.entries n)).getD []).eraseDups
  let book : LawBook := names.map fun n => (n, ⟨"owner", baseLaws n, links n, []⟩)
  let store : VaultStore := fun c => if names.contains c then some (stateAt (baseOf c)) else none
  let receipts := baseReceipts names baseOf
  let live := names.filter (!skip ·)
  let text : TextMerge := fun c =>
    match (liveHistory here c).getLast?, (liveHistory other c).getLast? with
    | some A, some B => some ((mergePage A B).map fun M => pageState M (liveHistory here c).length)
    | _, _ => none
  { names, baseOf, text,
    base := { store, book, history := receipts },
    left := ⟨"here", receipts, actsOf here live baseOf baseLaws links⟩,
    right := ⟨label, receipts, actsOf other live baseOf baseLaws links⟩ }

/-! ## Landing what the tip landed -/

/-- The authors of what the other replica added to a page, said as its: its owner is `owner@LABEL`. -/
def addedFrom (label : String) (q : Option Page) (A : Option Graph) (M : Graph) : List (AtomId × String) :=
  (M.atoms.map (·.1)).eraseDups.filter (fun a => !(A.map (·.present a)).getD false) |>.map fun a =>
    (a, match q.bind fun q => q.authors.lookup a with
      | some w => if w == "owner" then "owner@" ++ label else w
      | none => "owner@" ++ label)

/-- Land the other side's version of a page here (merged with here's, `mergePage`), through the
vault's own write. -/
def landPage (s : Store) (other : Store) (label name : String) : Store × String :=
  let q := other.page? name
  match q.bind (·.current) with
  | none => (s, name ++ ": not merged: " ++ label ++ " has no version of it")
  | some B =>
    let (p?, born) : Option Page × Bool := match s.page? name with
      | some p => (some p, false)
      | none =>
        match q with
        | some q =>
          if s.pages.any (·.id == q.id) then (none, true)
          else (some { name, id := q.id, history := [], seen := none, authors := [], note := none }, true)
        | none => (none, true)
    match p? with
    | none => (s, name ++ ": not imported: its id is another page's here")
    | some p =>
      let s := if born then { s with pages := s.pages ++ [p] } else s
      let M? := match p.current with
        | some A => mergePage A B
        | none => some B
      match M? with
      | none => (s, name ++ ": not merged: the two versions name one atom differently (they share no base)")
      | some M =>
        match s.write p M (addedFrom label q p.current M) .owner with
        | .ok s' =>
          let secs := (sections M).length
          (s', name ++ (if born then ": imported from " ++ label else ": merged from " ++ label) ++
            (if secs = 0 then "" else ", " ++ toString secs ++ " section(s) to select"))
        | .error msg => (s, msg)

/-- Here's write of a page that did not settle at the tip: the page's store returns to its base
version; its file keeps here's text, as a refused write that names why. -/
def unsettle (s : Store) (name : String) (bp : List Graph) (why : String) : Store :=
  match s.page? name with
  | some p => { s with pages := s.pages.map fun q => if q.name == name then
      { p with history := bp, note := some why } else q }
  | none => s

/-- A refusal at the tip, said of a vault page. A moved pin is said as the change to make here. -/
def refusalLine (label : String) : Branch.Refusal → String
  | .stale c e cur => "its write at " ++ label ++ " read " ++ c ++ " as it was there (" ++
      stateDiffText e cur ++ "); make the change here, against " ++ c ++ " as it is"
  | r => r.text

/-- The page a landed or refused act names (a merged pair: its first). -/
def actPage : Act → Option String
  | .write t => t.writes.head?
  | _ => none

/-- **Merge another replica's store into this one** (`label` names it). The two stores are read as
branches of their base (`plan`), merged at the tip (`Branch.merge`, with `mergePage` as the text
merge), and what the tip landed lands here. -/
def mergeVault (here other : Store) (label : String) (skip : String → Bool := fun _ => false) :
    Store × List String :=
  let P := plan here other label skip
  match Branch.merge P.base P.left P.right P.text with
  | .error e => (here, ["not merged: " ++ e])
  | .ok m =>
    let landedLeft := (landedOn .left m.landed).flatMap BTurn.writes ++ (landedOn .both m.landed).flatMap BTurn.writes
    let leftWrites := (writesOf P.left.acts).flatMap BTurn.writes
    -- here's writes the tip did not land go back to the base
    let unsettled := leftWrites.filter fun n => !landedLeft.contains n
    let why : String → String := fun n =>
      match m.refused.find? (fun r => r.2.1 == n || r.2.1.startsWith (n ++ " + ")) with
      | some (_, _, r) => "not settled at the merge with " ++ label ++ ": " ++ r.text
      | none =>
        match m.conflicts.find? (fun c => match c with
          | .writes cs _ _ => cs.contains n
          | .laws _ _ _ => false) with
        | some c => "not settled at the merge with " ++ label ++ ": " ++ c.text
        | none => "not settled at the merge with " ++ label
    let s0 := unsettled.foldl (fun s n => unsettle s n (P.baseOf n) (why n)) here
    let notes0 := unsettled.map fun n => n ++ ": here's write was " ++ why n
    -- the other side's writes and the merged pages land, in the tip's order
    let toLand := (m.landed.filter fun x => x.1 != .left).filterMap fun x => actPage x.2
    let (s1, notes1) := toLand.foldl (fun (acc : Store × List String) n =>
      let (s', line) := landPage acc.1 other label n
      (s', acc.2 ++ [line])) (s0, [])
    let refusedRight := (m.refused.filter fun r => r.1 == .right).map fun (_, l, r) =>
      l ++ ": not merged: " ++ refusalLine label r
    let refusedBoth := (m.refused.filter fun r => r.1 == .both).map fun (_, l, r) =>
      l ++ ": not merged: " ++ r.text
    (s1, notes0 ++ notes1 ++ refusedRight ++ refusedBoth ++ m.conflicts.map Conflict.text)

end Obend.Vault.Merge
