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
* **A side's acts** are what it did since: for every page whose history moved past the base, one
  write (its state at the base to its state now, as one `writeTurn`, its read pins the pages its laws
  over links read at that side's states, `pinsAt`). A page's laws are lines of its text, so a change
  of them is that write, judged by the store; the law book names only each page's owner. Vault
  writes are the owner's; the markdown vault records no sturdyref grants or revocations on a copy, so
  the authority at the tip is the base's.
* **One judgment.** The tip's configuration keeps the vault's store itself (`Config.vault`): the
  base store, each page at its base version. Every write carries its text (`BTurn.text`: the versions
  the side wrote since the base, each with the authors of what it added), and the tip judges and
  lands it by the store's own write (`Store.writeText`: `prepareWrite`, `judgePrepared` with its rows,
  kind pins, `poster` and `unresolved`), so landed at the tip and landed in the store are one event
  (`Branch.tip_lands_iff_store_lands`). Writes of different pages are replayed at the tip, here's
  first; a write whose pins the other side moved is refused by name (`Branch.Refusal.stale`). Two
  writes of one page merge by their texts (`TextMerge`): the pushout of the two versions
  (`mergePage`, `mergePage_pushout`), where two edits of one place become a section with both
  candidates, landed after here's versions as one more. Two versions that name one atom differently
  do not merge: a conflict.
* **The tip is the store.** The store the merge leaves is the tip's. Here's writes the tip did not
  land (refused, or held in a conflict) stay at the base version, their files keeping here's text
  as refused writes (`Page.note`), judged again when a pin they read moves, exactly as an open keeps
  a refused write. A conflict is a state of the store (`Store.conflicts`, a `PageConflict` with both
  candidate writes), listed by `obend status`, kept by every open, and resolved by
  `obend branch resolve K left|right`, which lands the chosen candidate through `Branch.resolve` at
  the store as it is, its receipt naming the candidate dropped (`resolveIn`).
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

/-- The authors of what a version adds over the one before it, said as the replica's: the replica's
owner is `owner@LABEL` (here's own: `owner`). -/
def addedFrom (label : String) (q : Option Page) (A : Option Graph) (M : Graph) : List (AtomId × String) :=
  (M.atoms.map (·.1)).eraseDups.filter (fun a => !(A.map (·.present a)).getD false) |>.map fun a =>
    (a, match q.bind fun q => q.authors.lookup a with
      | some w => if w == "owner" && label != "" then "owner@" ++ label else w
      | none => if label == "" then "owner" else "owner@" ++ label)

/-- A side's versions of a page since the base, each with the authors of what it added (`label`:
the replica's name, `""` for here). -/
def versionsSince (s : Store) (label name : String) (bp : List Graph) : List (Graph × List (AtomId × String)) :=
  let h := liveHistory s name
  let vs := h.drop bp.length
  let prevs := (bp.getLast?) :: vs.dropLast.map some
  (vs.zip prevs).map fun (G, A) => (G, addedFrom label (s.page? name) A G)

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

/-- The base's receipts: one per version of every page at the base. -/
def baseReceipts (names : List String) (baseOf : String → List Graph) : List Receipt :=
  (names.flatMap fun n => (List.range (baseOf n).length).map fun k => (n, k)).zipIdx.map
    fun ((n, k), i) => ⟨i, "base", n ++ " v" ++ toString (k + 1), [n]⟩

/-- The pages a version links to, by name, itself left out. -/
def linksAt (es : List Entry) (name : String) (G : Graph) : List String :=
  (citedNames es G).filter (· != name)

/-- The base store: here's, every merged page at its base version (a page only the other has, born
here unborn, with the other's id). -/
def baseStore (here other : Store) (names : List String) (baseOf : String → List Graph) : Store :=
  let mine := here.pages.map fun p => if names.contains p.name then { p with history := baseOf p.name } else p
  let theirs := (names.filter fun n => (here.page? n).isNone).filterMap fun n =>
    (other.page? n).map fun q =>
      ({ name := n, id := q.id, history := baseOf n, seen := none, authors := q.authors, note := none, kind := q.kind } : Page)
  { here with pages := mine ++ theirs }

/-- A side's write of a page: from its base state to its state now, its read pins the pages its laws
over links read, at the side's states, and its text the versions it wrote since the base. -/
def writeOf (s : Store) (label name : String) (bp : List Graph) (G : Graph) : BTurn :=
  let pins := if hasLinkLaws s.entries name G then pinsAt s.entries (linksAt s.entries name G) else []
  { label := name, actor := "owner",
    turn := writeTurn name (stateAt bp) (pageState G ((liveHistory s name).length - 1)) pins
      (requestAt "owner" 0),
    text := some { versions := versionsSince s label name bp } }

/-- A side's writes in an order its own pins hold in: a write that pins a page the side also wrote
comes after that write (`fuel` bounds the passes; what is left is appended as it stands). -/
def orderWrites : Nat → List BTurn → List BTurn
  | 0, ws => ws
  | fuel + 1, ws =>
    match ws.partition fun w => w.turn.readPins.all fun p => !(ws.any fun w' => w'.label != w.label && w'.writes.contains p.cell) with
    | ([], rest) => rest
    | (ready, rest) => ready ++ orderWrites fuel rest

/-- A side's acts since the base: a write of every page whose history moved past it. A page's laws
are lines of its text, so a change of them is a write like any other, judged by the store. -/
def actsOf (s : Store) (label : String) (names : List String) (baseOf : String → List Graph) : List Act :=
  let moved := names.filter fun n =>
    let h := liveHistory s n
    !h.isEmpty && h != baseOf n
  let writes := moved.filterMap fun n => (liveHistory s n).getLast?.map (writeOf s label n (baseOf n))
  (orderWrites writes.length writes).map Act.write

/-- **Read two stores as two branches of their base.** Pages `skip` names (another merge's: the
ledger's register) are left out: at the base as here holds them, acted on by neither side. -/
def plan (here other : Store) (label : String) (skip : String → Bool := fun _ => false) : Plan :=
  let names := ((here.pages.map (·.name)) ++ (other.pages.map (·.name))).eraseDups
  let baseOf : String → List Graph := fun n =>
    if skip n then liveHistory here n else sharedPrefix (historyIn here n) (historyIn other n)
  -- the book names each page's owner; its laws are the store's, judged by the store's own write
  let book : LawBook := names.map fun n => (n, ⟨"owner", [], [], []⟩)
  let store : VaultStore := fun c => if names.contains c then some (stateAt (baseOf c)) else none
  let receipts := baseReceipts names baseOf
  let live := names.filter (!skip ·)
  let merged : String → Option Graph := fun c =>
    match (liveHistory here c).getLast?, (liveHistory other c).getLast? with
    | some A, some B => mergePage A B
    | _, _ => none
  let text : TextMerge :=
    { state := fun c =>
        match (liveHistory here c).getLast?, (liveHistory other c).getLast? with
        | some A, some B => some ((mergePage A B).map fun M => pageState M (liveHistory here c).length)
        | _, _ => none
      write := fun c => (merged c).map fun M =>
        { versions := versionsSince here "" c (baseOf c) ++
            [(M, addedFrom label (other.page? c) (liveHistory here c).getLast? M)] } }
  { names, baseOf, text,
    base := { store, book, history := receipts, vault := some (baseStore here other names baseOf) },
    left := ⟨"here", receipts, actsOf here "" live baseOf⟩,
    right := ⟨label, receipts, actsOf other label live baseOf⟩ }

/-! ## The store the tip leaves -/

/-- Here's write of a page that did not settle at the tip: the page stays at its base version; its
file keeps here's text, as a refused write that names why. -/
def unsettle (s : Store) (name : String) (seen : Option String) (why : String) : Store :=
  { s with pages := s.pages.map fun q => if q.name == name then { q with seen := seen, note := some why } else q }

/-- A refusal at the tip, said of a vault page. A moved pin is said as the change to make here. -/
def refusalLine (label : String) : Branch.Refusal → String
  | .stale c e cur => "its write at " ++ label ++ " read " ++ c ++ " as it was there (" ++
      stateDiffText e cur ++ "); make the change here, against " ++ c ++ " as it is"
  | r => r.text

/-- The page a landed or refused act names (a merged pair: its first). -/
def actPage : Act → Option String
  | .write t => t.writes.head?
  | _ => none

/-- A conflict of the tip, as the store keeps it: a page's two candidate writes. -/
def pageConflict : Conflict → Option PageConflict
  | .writes [c] (ln, l) (rn, r) =>
    match l.text, r.text with
    | some wl, some wr => some ⟨c, (ln, l.label, wl), (rn, r.label, wr)⟩
    | _, _ => none
  | _ => none

/-- How to resolve the `k`th conflict of a store, said. -/
def resolveHint (k : Nat) : String :=
  "; keep one with: obend branch resolve " ++ toString k ++ " left|right"

/-- **Merge another replica's store into this one** (`label` names it). The two stores are read as
branches of their base (`plan`) and merged at the tip (`Branch.merge`, with `mergePage` as the text
merge); the store the tip reached is the store the merge leaves. -/
def mergeVault (here other : Store) (label : String) (skip : String → Bool := fun _ => false) :
    Store × List String :=
  let P := plan here other label skip
  match Branch.merge P.base P.left P.right P.text with
  | .error e => (here, ["not merged: " ++ e])
  | .ok m =>
    let tip := m.tip.vault.getD here
    let landedLeft := (landedOn .left m.landed).flatMap BTurn.writes ++ (landedOn .both m.landed).flatMap BTurn.writes
    let leftWrites := (writesOf P.left.acts).flatMap BTurn.writes
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
    let s0 := unsettled.foldl (fun s n => unsettle s n ((here.page? n).bind (·.seen)) (why n)) tip
    let kept := m.conflicts.filterMap pageConflict
    let s1 := { s0 with conflicts := s0.conflicts ++ kept }
    let notes0 := unsettled.map fun n => n ++ ": here's write was " ++ why n
    let notes1 := (m.landed.filter fun x => x.1 != .left).filterMap fun x => (actPage x.2).map fun n =>
      let secs := ((s1.page? n).bind (·.current)).map (fun G => (sections G).length) |>.getD 0
      n ++ (if (here.page? n).isNone then ": imported from " ++ label else ": merged from " ++ label) ++
        (if secs = 0 then "" else ", " ++ toString secs ++ " section(s) to select")
    let refusedRight := (m.refused.filter fun r => r.1 == .right).map fun (_, l, r) =>
      l ++ ": not merged: " ++ refusalLine label r
    let refusedBoth := (m.refused.filter fun r => r.1 == .both).map fun (_, l, r) =>
      l ++ ": not merged: " ++ r.text
    let conflictLines := (m.conflicts.zipIdx.map fun (c, i) =>
      c.text ++ (if (pageConflict c).isSome then resolveHint (here.conflicts.length + i) else ""))
    (s1, notes0 ++ notes1 ++ refusedRight ++ refusedBoth ++ conflictLines)

/-! ## Resolving a conflict the store keeps -/

/-- The configuration a store is, for resolving its conflicts: the store itself, its pages' states,
and its conflicts as the tip's (`Conflict.writes`, each candidate a write carrying its text). -/
def configOf (s : Store) : Config :=
  let es := s.entries
  -- a page not born reads as `unborn`, as at the merge's base
  let states : VaultStore := fun c =>
    match stateStore es c with
    | some d => some d
    | none => if s.pages.any (·.name == c) then some unborn else none
  { store := states,
    book := s.pages.map fun p => (p.name, ⟨"owner", [], [], []⟩),
    history := [],
    vault := some s,
    conflicts := s.conflicts.map fun pc =>
      let bt (c : String × String × PageWrite) : BTurn :=
        let pre := states pc.page
        { label := c.2.1, actor := "owner",
          turn := writeTurn pc.page (pre.getD unborn) (pre.getD unborn) [] (requestAt "owner" 0),
          text := some c.2.2 }
      .writes [pc.page] (pc.left.1, bt pc.left) (pc.right.1, bt pc.right) }

/-- **Resolve the `k`th conflict a store keeps** by landing one candidate through `Branch.resolve`
at the store as it is: the store's own write of the candidate's text, the other dropped, the
receipt naming it. Returns the store and the receipt. -/
def resolveIn (s : Store) (k : Nat) (pick : Side) : Except String (Store × String) := do
  let c ← Branch.resolve (configOf s) k pick
  let some s' := c.vault | throw "the resolved configuration keeps no store"
  let r := (c.history.getLast?.map (·.label)).getD ""
  return ({ s' with conflicts := s.conflicts.eraseIdx k }, r)

end Obend.Vault.Merge
