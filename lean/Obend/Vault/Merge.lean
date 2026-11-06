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
  (`Branch.tip_lands_iff_store_lands`). Writes that change a page's law lines land first, of
  either side (`BTurn.lawKey`, `lawKeyOf`), so a law the laptop wrote judges a write made here; the
  other writes of different pages are replayed at the tip, here's first; a write whose pins the other side moved is refused by name (`Branch.Refusal.stale`). Two
  writes of one page merge by their texts (`TextMerge`): the pushout of the two versions
  (`mergePage`, `mergePage_pushout`), where two edits of one place become a section with both
  candidates, landed after here's versions as one more. Two versions that name one atom differently
  do not merge: a conflict.
* **The tip is the store.** The store the merge leaves is the tip's, and the tip's states agree with
  it page by page at each page's current version (`mergeVault_agrees`, from `plan_agrees`). Here's writes the tip did not
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
def baseMine (here : Store) (names : List String) (baseOf : String → List Graph) : List Page :=
  here.pages.map fun p => if names.contains p.name then { p with history := baseOf p.name } else p

def baseTheirs (here other : Store) (names : List String) (baseOf : String → List Graph) : List Page :=
  (names.filter fun n => (here.page? n).isNone).filterMap fun n =>
    (other.page? n).map fun q =>
      ({ name := n, id := q.id, history := baseOf n, seen := none, authors := q.authors, note := none, kind := q.kind } : Page)

def baseStore (here other : Store) (names : List String) (baseOf : String → List Graph) : Store :=
  { here with pages := baseMine here names baseOf ++ baseTheirs here other names baseOf }

/-- The law lines (and the kind) a write leaves a page with, when it changes them from the base's:
the write is then a law-changing write, settled before every other write at the tip. -/
def lawKeyOf (bp : List Graph) (G : Graph) : Option String :=
  let old := (bp.getLast?.map settled).getD ""
  let new := settled G
  if lawsKept old new then none
  else some ("\n".intercalate ((lawLines new).map fun (n, v) => n ++ ": " ++ v) ++ "\nkind: " ++
    (kindLine new).getD "")

/-- A side's write of a page: from its base state to its state now, its read pins the pages its laws
over links read, at the side's states, and its text the versions it wrote since the base. -/
def writeOf (s : Store) (label name : String) (bp : List Graph) (G : Graph) : BTurn :=
  let pins := if hasLinkLaws s.entries name G then pinsAt s.entries (linksAt s.entries name G) else []
  { label := name, actor := "owner",
    turn := writeTurn name (stateAt bp) (pageState G ((liveHistory s name).length - 1)) pins
      (requestAt "owner" 0),
    text := some { versions := versionsSince s label name bp },
    lawKey := lawKeyOf bp G }

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

/-- The pages a merge reads: here's, then the other's, each once. -/
def namesOf (here other : Store) : List String := ((here.pages.map (·.name)) ++ (other.pages.map (·.name))).eraseDups

/-- Each page's base history (a page `skip` names: here's). -/
def baseOfPlan (here other : Store) (skip : String → Bool) : String → List Graph := fun n =>
  if skip n then liveHistory here n else sharedPrefix (historyIn here n) (historyIn other n)

/-- The base's store of states: every page merged at its base state. -/
def baseStates (names : List String) (baseOf : String → List Graph) : VaultStore := fun c =>
  if names.contains c then some (stateAt (baseOf c)) else none

/-- **Read two stores as two branches of their base.** Pages `skip` names (another merge's: the
ledger's register) are left out: at the base as here holds them, acted on by neither side. -/
def plan (here other : Store) (label : String) (skip : String → Bool := fun _ => false) : Plan :=
  let names := namesOf here other
  let baseOf := baseOfPlan here other skip
  -- the book names each page's owner; its laws are the store's, judged by the store's own write
  let book : LawBook := names.map fun n => (n, ⟨"owner", [], [], []⟩)
  let store : VaultStore := baseStates names baseOf
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

/-- **A refused write here outlives a merge that did not move its page.** A page whose last write here
was refused keeps that write (its text, `seen`, and why, `note`) in the store the merge leaves when the
merge left the page's history as long as it was here: the tip replayed the page's versions, not the
write waiting in its file. (2026-11-06, found by the swarm vault: a merge of a fork declared before a
lane page was born re-rendered the page from the store, the refused `merged` text in its file was
lost, and no open said so again.) `skip`: the pages the merge itself left unsettled. -/
def keepPending (here : Store) (skip : List String) (s : Store) : Store :=
  here.pages.foldl (fun s p => match p.note with
    | some why =>
      if !skip.contains p.name && (s.page? p.name).map (·.history.length) == some p.history.length then
        unsettle s p.name p.seen why
      else s
    | none => s) s

theorem unsettle_histories (s : Store) (n : String) (seen : Option String) (why : String) :
    (unsettle s n seen why).pages.map (·.history) = s.pages.map (·.history) := by
  unfold unsettle
  simp only [List.map_map]
  congr 1
  funext q
  simp only [Function.comp]
  split <;> rfl

/-- Keeping the pending writes changes no page's history: what the merge landed is what it landed. -/
theorem keepPending_histories (here : Store) (skip : List String) (s : Store) :
    (keepPending here skip s).pages.map (·.history) = s.pages.map (·.history) := by
  unfold keepPending
  generalize here.pages = ps
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases p.note with
    | none => rfl
    | some why =>
      simp only
      split
      · exact unsettle_histories _ _ _ _
      · rfl

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
    let s1 := keepPending here unsettled { s0 with conflicts := s0.conflicts ++ kept }
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
  let states := vaultStates s
  { store := states,
    book := s.pages.map fun p => (p.name, ⟨"owner", [], [], []⟩),
    history := [],
    vault := some s,
    conflicts := s.conflicts.map fun pc =>
      let bt (c : String × String × PageWrite) : BTurn :=
        let pre := (states pc.page).getD unborn
        -- the state the candidate's text lands, which its turn must say (`judgeWrite`)
        let post := match s.writeText pc.page c.2.2 with
          | .ok s' => (vaultStates s' pc.page).getD pre
          | .error _ => pre
        { label := c.2.1, actor := "owner",
          turn := writeTurn pc.page pre post [] (requestAt "owner" 0),
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

/-! ## The base agrees with its store -/

theorem find?_states {l : List Page} {x : String} {h : List Graph}
    (hh : ∀ y ∈ l, y.name = x → y.history = h) :
    (l.find? (·.name == x)).map (fun p => stateAt p.history) =
      if l.any (·.name == x) then some (stateAt h) else none := by
  cases hf : l.find? (·.name == x) with
  | none =>
    have : l.any (·.name == x) = false := by
      rw [List.any_eq_false]
      intro y hy hyx
      exact absurd hyx (by simpa using List.find?_eq_none.1 hf y hy)
    simp [this]
  | some y =>
    have hm := List.mem_of_find?_eq_some hf
    have hy : y.name = x := by simpa using List.find?_some hf
    have : l.any (·.name == x) = true := List.any_eq_true.2 ⟨y, hm, by simp [hy]⟩
    simp [this, hh y hm hy]

theorem page?_none_iff {s : Store} {x : String} : s.page? x = none ↔ ∀ p ∈ s.pages, p.name ≠ x := by
  unfold Store.page?
  rw [List.find?_eq_none]
  simp

theorem page?_some_name {s : Store} {x : String} {p : Page} (h : s.page? x = some p) :
    p ∈ s.pages ∧ p.name = x :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem mem_namesOf {here other : Store} {x : String} :
    x ∈ namesOf here other ↔ (∃ p ∈ here.pages, p.name = x) ∨ ∃ q ∈ other.pages, q.name = x := by
  simp [namesOf, List.mem_eraseDups]

theorem mem_baseMine {here : Store} {names : List String} {baseOf : String → List Graph} {y : Page} :
    y ∈ baseMine here names baseOf → ∃ p ∈ here.pages, y.name = p.name ∧
      (names.contains p.name = true → y.history = baseOf p.name) := by
  intro hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
  refine ⟨p, hp, ?_, fun hc => ?_⟩
  · split <;> rfl
  · simp only [hc, ↓reduceIte]

theorem mem_baseTheirs {here other : Store} {names : List String} {baseOf : String → List Graph} {y : Page} :
    y ∈ baseTheirs here other names baseOf ↔
      y.name ∈ names ∧ here.page? y.name = none ∧ ∃ q, other.page? y.name = some q ∧
        y = { name := y.name, id := q.id, history := baseOf y.name, seen := none, authors := q.authors,
              note := none, kind := q.kind } := by
  unfold baseTheirs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨n, hn, hq⟩
    obtain ⟨hn, hh⟩ := List.mem_filter.1 hn
    cases hq' : other.page? n with
    | none => rw [hq'] at hq; cases hq
    | some q =>
      rw [hq'] at hq
      simp only [Option.map_some, Option.some.injEq] at hq
      subst hq
      exact ⟨hn, by simpa using hh, q, hq', rfl⟩
  · rintro ⟨hn, hh, q, hq, he⟩
    refine ⟨y.name, List.mem_filter.2 ⟨hn, by simp [hh]⟩, ?_⟩
    rw [hq, he]
    rfl

/-- **The base's two views agree**: its store of states is the vault's base store, page by page. -/
theorem baseStore_states (here other : Store) (baseOf : String → List Graph) :
    vaultStates (baseStore here other (namesOf here other) baseOf) = baseStates (namesOf here other) baseOf := by
  funext x
  have hall : ∀ y ∈ baseMine here (namesOf here other) baseOf ++ baseTheirs here other (namesOf here other) baseOf,
      y.name = x → y.history = baseOf x := by
    intro y hy hyx
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨p, hp, hyp, hh⟩ := mem_baseMine hy
      have hin : (namesOf here other).contains p.name = true := by
        simpa using mem_namesOf.2 (.inl ⟨p, hp, rfl⟩)
      rw [hh hin, ← hyp, hyx]
    · obtain ⟨_, _, q, _, he⟩ := mem_baseTheirs.1 hy
      rw [he]
      simp only
      rw [hyx]
  have hany : (baseMine here (namesOf here other) baseOf ++ baseTheirs here other (namesOf here other) baseOf).any
      (·.name == x) = (namesOf here other).contains x := by
    apply Bool.eq_iff_iff.2
    simp only [List.any_append, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, List.contains_iff_mem,
      mem_namesOf]
    constructor
    · rintro (⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩)
      · obtain ⟨p, hp, hyp, _⟩ := mem_baseMine hy
        exact .inl ⟨p, hp, hyp ▸ hyx⟩
      · obtain ⟨_, _, q, hq, _⟩ := mem_baseTheirs.1 hy
        obtain ⟨hqm, hqn⟩ := page?_some_name hq
        exact .inr ⟨q, hqm, hqn.trans hyx⟩
    · rintro (⟨p, hp, hpx⟩ | ⟨q, hq, hqx⟩)
      · refine .inl ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, ?_⟩
        split <;> exact hpx
      · by_cases hh : ∃ p ∈ here.pages, p.name = x
        · obtain ⟨p, hp, hpx⟩ := hh
          refine .inl ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, ?_⟩
          split <;> exact hpx
        · have hnone : here.page? x = none := page?_none_iff.2 fun p hp hpx => hh ⟨p, hp, hpx⟩
          cases hq' : other.page? x with
          | none => exact absurd hqx ((page?_none_iff.1 hq') q hq)
          | some q' =>
            let y : Page := { name := x, id := q'.id, history := baseOf x, seen := none, authors := q'.authors, note := none, kind := q'.kind }
            refine .inr ⟨y, mem_baseTheirs.2 ⟨?_, hnone, q', hq', rfl⟩, rfl⟩
            exact mem_namesOf.2 (.inr ⟨q, hq, hqx⟩)
  unfold vaultStates baseStates
  show ((baseMine here (namesOf here other) baseOf ++ baseTheirs here other (namesOf here other) baseOf).find?
      (·.name == x)).map (fun p => stateAt p.history) = _
  rw [find?_states hall, hany]

/-- **A merge's base agrees**: the store of states it starts from is the vault's base store. -/
theorem plan_agrees (here other : Store) (label : String) (skip : String → Bool) :
    Agrees (plan here other label skip).base := by
  intro v hv x
  simp only [plan, Option.some.injEq] at hv
  subst hv
  show (baseStates (namesOf here other) (baseOfPlan here other skip) x).map Obend.Core.Data.Data.term = _
  rw [baseStore_states]

/-- **After a vault merge the store's page versions and the vault's agree**: the tip's state of every
page is the state of the tip store's page at its current version. -/
theorem mergeVault_agrees (here other : Store) (label : String) (skip : String → Bool) {m : Merged}
    (h : Branch.merge (plan here other label skip).base (plan here other label skip).left
      (plan here other label skip).right (plan here other label skip).text = .ok m) : Agrees m.tip :=
  merge_vault_agrees h (plan_agrees here other label skip)

end Obend.Vault.Merge
