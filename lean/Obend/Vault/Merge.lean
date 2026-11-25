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
import all Obend.Vault.Branch
public import Obend.Vault.IncrementalJudge
public import Std.Data.HashMap
public import Std.Data.HashSet
public section

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
  -- the atoms `M` stores that `A` does not, first occurrences, in `M`'s order: a hash set of `A`'s, so
  -- a page of many versions costs its versions' sizes, not their squares (`eraseDups` and a lookup in
  -- every author were quadratic in a version's atoms, cubic over a page's versions)
  let who : Std.HashMap AtomId String := ((q.map (·.authors)).getD []).foldl
    (fun m (a, w) => if m.contains a then m else m.insert a w) {}
  let seen0 : Std.HashSet AtomId := ((A.map (·.atoms)).getD []).foldl (fun st e => st.insert e.1) {}
  let (_, xs) := M.atoms.foldl (fun (acc : Std.HashSet AtomId × Array AtomId) e =>
    if acc.1.contains e.1 then acc else (acc.1.insert e.1, acc.2.push e.1)) (seen0, #[])
  xs.toList.map fun a =>
    (a, match who.get? a with
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

/-- Optional member authority attribution for an incoming fork (`--for MEMBER` at `obend fork` /
`obend branch`). When `actor = "owner"` (default), all writes run under owner authority; when
attributed to a member, the fork's writes carry `actor`, rely on the capabilities in `tipAuth`
returned by `reliesOf`, and are prepared/judged under `actorRef` at the tip. -/
structure ForkAuth where
  actor : String := "owner"
  tipAuth : Authority := {}
  reliesOf : String → Bool → List String := fun _ _ => []
  actorRef : Actor := .owner

/-- A side's write of a page: from its base state to its state now, its read pins the pages its laws
over links read, at the side's states, and its text the versions it wrote since the base. -/
def writeOf (s : Store) (label name : String) (bp : List Graph) (G : Graph) : BTurn :=
  let pins := if hasLinkLaws s.entries name G then pinsAt s.entries (linksAt s.entries name G) else []
  { label := name, actor := "owner",
    turn := writeTurn name (stateAt bp) (pageState G ((liveHistory s name).length - 1)) pins
      (requestAt "owner" 0),
    text := some { versions := versionsSince s label name bp },
    lawKey := lawKeyOf bp G }

/-- A side's write of a page under `ForkAuth` attribution. -/
def writeOfAuth (s : Store) (label name : String) (bp : List Graph) (G : Graph)
    (auth : ForkAuth := {}) : BTurn :=
  if auth.actor == "owner" then
    writeOf s label name bp G
  else
    let pins := if hasLinkLaws s.entries name G then pinsAt s.entries (linksAt s.entries name G) else []
    let lk := lawKeyOf bp G
    let pw : PageWrite := { versions := versionsSince s label name bp }
    { label := name, actor := auth.actor,
      turn := writeTurn name (stateAt bp) (pageState G ((liveHistory s name).length - 1)) pins
        (requestAt auth.actor 0),
      relies := auth.reliesOf name lk.isSome,
      text := none,
      lawKey := lk,
      texts := [(name, pw)],
      actorRef := auth.actorRef }

/-- A side's writes in an order its own pins hold in: a write that pins a page the side also wrote
comes after that write (`fuel` bounds the passes; what is left is appended as it stands). -/
def orderWrites : Nat → List BTurn → List BTurn
  | 0, ws => ws
  | fuel + 1, ws =>
    match ws.partition fun w => w.turn.readPins.all fun p => !(ws.any fun w' => w'.label != w.label && w'.writes.contains p.cell) with
    | ([], rest) => rest
    | (ready, rest) => ready ++ orderWrites fuel rest

def turnSingleText? (t : BTurn) : Option (String × PageWrite) :=
  match t.text, t.texts, t.turn.writeCells with
  | some pw, _, [d] => some (d.cell, pw)
  | none, [(c, pw)], [d] => if c == d.cell then some (c, pw) else none
  | _, _, _ => none

def trySingleAt (auth : Authority) (book : LawBook) (s : Store) (t : BTurn) : Option Store :=
  let cfg : Config := { store := vaultStates s, book := book, auth := auth, vault := some s }
  match admitWrite cfg "" t with
  | .ok cfg' => cfg'.vault
  | .error _ => none

def simSingleRound (auth : Authority) (book : LawBook) :
    Store → List BTurn → Store × List BTurn × List BTurn
  | s, [] => (s, [], [])
  | s, t :: rest =>
    match trySingleAt auth book s t with
    | some s' =>
      let (s'', ok, rem) := simSingleRound auth book s' rest
      (s'', t :: ok, rem)
    | none =>
      let (s'', ok, rem) := simSingleRound auth book s rest
      (s'', ok, t :: rem)

def simSingles (auth : Authority) (book : LawBook) :
    Nat → Store → List BTurn → Store × List BTurn × List BTurn
  | 0, s, pending => (s, [], pending)
  | fuel + 1, s, pending =>
    let (s', ok, rem) := simSingleRound auth book s pending
    if ok.isEmpty || rem.isEmpty then (s', ok, rem)
    else
      let (s'', ok2, rem2) := simSingles auth book fuel s' rem
      (s'', ok ++ ok2, rem2)

def pruneExternalStale (st : VaultStore) : Nat → List BTurn → List BTurn
  | 0, cand => cand
  | fuel + 1, cand =>
    let cells := cand.flatMap BTurn.writes
    let keep := cand.filter fun t =>
      let extPins := t.turn.readPins.filter (fun p => !cells.contains p.cell) ++
        t.turn.writeCells.map (fun d => ⟨d.cell, some d.preState⟩)
      (Footprint.firstStale? st extPins).isNone
    if keep.length == cand.length then keep
    else pruneExternalStale st fuel keep

def mkCoupledTurn (grp : List BTurn) (sAfter : Store) (actor : String) (actorRef : Actor) :
    Option BTurn :=
  if grp.length < 2 then none else
  let cells := grp.flatMap BTurn.writes
  let texts := grp.filterMap turnSingleText?
  if texts.length != grp.length then none else
  let extPins : Footprint :=
    (grp.flatMap fun t => t.turn.readPins.filter fun p => !cells.contains p.cell).foldl
      (fun acc p => if acc.any (·.cell == p.cell) then acc else acc ++ [p]) []
  let legs : List (String × Data × Data) :=
    grp.flatMap fun t => t.turn.writeCells.map fun d =>
      (d.cell, d.preState, (vaultStates sAfter d.cell).getD d.postState)
  match VaultTurn.ofWitnessLegs ByteArray.empty extPins legs (requestAt actor 0) [] with
  | none => none
  | some vt =>
    let lk : Option String :=
      let keys := grp.filterMap (·.lawKey)
      if keys.isEmpty then none else some ("\n---\n".intercalate keys)
    some
      { label := " + ".intercalate (grp.map (·.label))
        actor := actor
        turn := vt
        relies := (grp.flatMap (·.relies)).eraseDups
        text := none
        lawKey := lk
        texts := texts
        actorRef := actorRef }

def findCoupledGroup (s : Store) (actor : String) (actorRef : Actor) :
    Nat → List BTurn → Option (BTurn × Store × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | fuel + 1, cand0 =>
    let cand := pruneExternalStale (vaultStates s) cand0.length cand0
    if cand.length < 2 then none else
    let texts := cand.filterMap turnSingleText?
    if texts.length != cand.length then none else
    match s.writeTexts texts actorRef with
    | .ok sAfter =>
      (mkCoupledTurn cand sAfter actor actorRef).map fun bt =>
        (bt, sAfter, cand.flatMap BTurn.writes)
    | .error _ =>
      let prs := texts.filterMap fun tw =>
        match prepareTexts s actorRef [tw] with
        | .ok [pr] => some pr
        | _ => none
      let res := turnEntries s.entries (prs.map fun pr => (pr.p, pr.G', []))
      let over := tipOf prs
      let keep := cand.filter fun t =>
        match t.writes.head? >>= fun c => prs.find? (·.p.name == c) with
        | some pr => (judgePrepared s.entries res pr over).toBool
        | none => false
      if keep.length ≥ 2 && keep.length < cand.length then
        findCoupledGroup s actor actorRef fuel keep
      else none

private def pruneExternalStaleSlots (st : VaultStore) :
    Nat → List (BTurn × Option IncrementalJudge.Slot) →
      List (BTurn × Option IncrementalJudge.Slot)
  | 0, items => items
  | fuel + 1, items =>
    let cells := items.flatMap (fun x => x.1.writes)
    let keep := items.filter fun x =>
      let extPins := x.1.turn.readPins.filter (fun p => !cells.contains p.cell) ++
        x.1.turn.writeCells.map (fun d => ⟨d.cell, some d.preState⟩)
      (Footprint.firstStale? st extPins).isNone
    if keep.length == items.length then keep
    else pruneExternalStaleSlots st fuel keep

private theorem pruneExternalStaleSlots_fst (st : VaultStore) :
    ∀ (n : Nat) (items : List (BTurn × Option IncrementalJudge.Slot)),
      (pruneExternalStaleSlots st n items).map Prod.fst =
        pruneExternalStale st n (items.map Prod.fst)
  | 0, _ => rfl
  | fuel + 1, items => by
    simp only [pruneExternalStaleSlots, pruneExternalStale,
      List.flatMap_map, List.filter_map, List.length_map, Function.comp_def]
    cases h : ((items.filter fun x =>
        let extPins := x.1.turn.readPins.filter
            (fun p => !(items.flatMap (fun a => a.1.writes)).contains p.cell) ++
          x.1.turn.writeCells.map (fun d => ⟨d.cell, some d.preState⟩)
        (Footprint.firstStale? st extPins).isNone).length == items.length)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact pruneExternalStaleSlots_fst st fuel _
    · simp only [↓reduceIte]

private theorem pruneExternalStaleSlots_mem (st : VaultStore) (n : Nat) :
    ∀ {items : List (BTurn × Option IncrementalJudge.Slot)}
      {x : BTurn × Option IncrementalJudge.Slot},
      x ∈ pruneExternalStaleSlots st n items → x ∈ items := by
  induction n with
  | zero => intro _ _ hx; exact hx
  | succ fuel ih =>
    intro items x hx
    unfold pruneExternalStaleSlots at hx
    dsimp only at hx
    split at hx
    · exact (List.mem_filter.mp hx).1
    · exact (List.mem_filter.mp (ih hx)).1

private def prepareSingleText? (s : Store) (actorRef : Actor) (tw : String × PageWrite) :
    Option Prepared :=
  match prepareTexts s actorRef [tw] with
  | .ok [pr] => some pr
  | _ => none

private def coupledKeepSpec (s : Store) (actorRef : Actor) (cand : List BTurn) : List BTurn :=
  let texts := cand.filterMap turnSingleText?
  let prs := texts.filterMap (prepareSingleText? s actorRef)
  let res := turnEntries s.entries (prs.map fun pr => (pr.p, pr.G', []))
  let over := tipOf prs
  cand.filter fun t =>
    match t.writes.head? >>= fun c => prs.find? (·.p.name == c) with
    | some pr => (judgePrepared s.entries res pr over).toBool
    | none => false

private def CoupledSlotInv (s : Store) (actorRef : Actor)
    (item : BTurn × Option IncrementalJudge.Slot) : Prop :=
  item.2.map IncrementalJudge.Slot.prepared =
    (turnSingleText? item.1).bind (prepareSingleText? s actorRef)

private def initCoupledSlot (s : Store) (actorRef : Actor) (t : BTurn) :
    BTurn × Option IncrementalJudge.Slot :=
  (t, ((turnSingleText? t).bind (prepareSingleText? s actorRef)).map fun pr => ⟨pr, none⟩)

private theorem initCoupledSlot_fst (s : Store) (actorRef : Actor) :
    ∀ (cand : List BTurn), (cand.map (initCoupledSlot s actorRef)).map Prod.fst = cand
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (initCoupledSlot_fst s actorRef rest)

private theorem initCoupledSlot_inv (s : Store) (actorRef : Actor) (t : BTurn) :
    CoupledSlotInv s actorRef (initCoupledSlot s actorRef t) := by
  unfold CoupledSlotInv initCoupledSlot
  cases (turnSingleText? t).bind (prepareSingleText? s actorRef) <;> rfl

private def evalCoupledSlot (es res : List Entry) (over : IncrementalJudge.Tip)
    (idx : Index.Buckets PageId Entry) (item : BTurn × Option IncrementalJudge.Slot) :
    BTurn × Option (IncrementalJudge.Slot × Bool) :=
  match item.2 with
  | none => (item.1, none)
  | some sl =>
    match IncrementalJudge.validateSlot es res over idx sl with
    | some cache => (item.1, some (⟨sl.prepared, some cache⟩, true))
    | none => (item.1, some (sl, false))

private theorem evalCoupledSlot_fst (es res : List Entry) (over : IncrementalJudge.Tip)
    (idx : Index.Buckets PageId Entry) (item : BTurn × Option IncrementalJudge.Slot) :
    (evalCoupledSlot es res over idx item).1 = item.1 := by
  obtain ⟨_, opt⟩ := item
  unfold evalCoupledSlot
  cases opt with
  | none => rfl
  | some sl => dsimp only; cases IncrementalJudge.validateSlot es res over idx sl <;> rfl

private theorem evalCoupledSlot_prepared (es res : List Entry) (over : IncrementalJudge.Tip)
    (idx : Index.Buckets PageId Entry) (item : BTurn × Option IncrementalJudge.Slot) :
    ((evalCoupledSlot es res over idx item).2.map Prod.fst).map IncrementalJudge.Slot.prepared =
      item.2.map IncrementalJudge.Slot.prepared := by
  obtain ⟨_, opt⟩ := item
  unfold evalCoupledSlot
  cases opt with
  | none => rfl
  | some sl => dsimp only; cases IncrementalJudge.validateSlot es res over idx sl <;> rfl

private theorem evalCoupledSlot_verdict (es res : List Entry) (over : IncrementalJudge.Tip)
    (item : BTurn × Option IncrementalJudge.Slot) :
    (evalCoupledSlot es res over (entryLinkIndex es) item).2.map
        (fun r => (r.1.prepared.p.name, r.2)) =
      (item.2.map IncrementalJudge.Slot.prepared).map
        (fun pr => (pr.p.name, (judgePrepared es res pr over).toBool)) := by
  obtain ⟨_, opt⟩ := item
  unfold evalCoupledSlot
  cases opt with
  | none => rfl
  | some sl =>
    have hv := IncrementalJudge.validateSlot_isSome_eq_judgePrepared es res over sl
    dsimp only [Option.map]
    cases h : IncrementalJudge.validateSlot es res over (entryLinkIndex es) sl
    · rw [h] at hv; simp only [Option.isSome_none] at hv; simp [← hv]
    · rw [h] at hv; simp only [Option.isSome_some] at hv; simp [← hv]

private theorem items_prs_eq (s : Store) (actorRef : Actor) :
    ∀ (items : List (BTurn × Option IncrementalJudge.Slot)),
      (∀ x ∈ items, CoupledSlotInv s actorRef x) →
      (items.filterMap fun x => x.2.map IncrementalJudge.Slot.prepared) =
        ((items.map Prod.fst).filterMap turnSingleText?).filterMap (prepareSingleText? s actorRef)
  | [], _ => rfl
  | x :: xs, hinv => by
    have hx : x.2.map IncrementalJudge.Slot.prepared =
        (turnSingleText? x.1).bind (prepareSingleText? s actorRef) :=
      hinv x (.head _)
    have ih := items_prs_eq s actorRef xs (fun y hy => hinv y (.tail _ hy))
    rw [List.filterMap_cons, hx, ih, List.map_cons, List.filterMap_cons]
    cases turnSingleText? x.1 with
    | none => rfl
    | some tw => rw [List.filterMap_cons]; rfl

private theorem evalCoupledSlots_verdicts (es res : List Entry) (over : IncrementalJudge.Tip) :
    ∀ (items : List (BTurn × Option IncrementalJudge.Slot)),
      ((items.map (evalCoupledSlot es res over (entryLinkIndex es))).filterMap fun y =>
          y.2.map fun r => (r.1.prepared.p.name, r.2)) =
        (items.filterMap fun x => x.2.map IncrementalJudge.Slot.prepared).map
          (fun pr => (pr.p.name, (judgePrepared es res pr over).toBool))
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons,
      evalCoupledSlot_verdict es res over x,
      evalCoupledSlots_verdicts es res over xs]
    cases x.2.map IncrementalJudge.Slot.prepared <;> rfl

private theorem verdict_lookup_eq (es res : List Entry) (over : IncrementalJudge.Tip)
    (prs : List Prepared) (t : BTurn) :
    (match t.writes.head? >>= fun c =>
        (prs.map fun pr => (pr.p.name, (judgePrepared es res pr over).toBool)).find? (·.1 == c) with
      | some kv => kv.2
      | none => false) =
    (match t.writes.head? >>= fun c => prs.find? (·.p.name == c) with
      | some pr => (judgePrepared es res pr over).toBool
      | none => false) := by
  cases t.writes.head? with
  | none => rfl
  | some c =>
    change (match (prs.map fun pr => (pr.p.name, (judgePrepared es res pr over).toBool)).find? (·.1 == c) with
        | some kv => kv.2 | none => false) =
      (match prs.find? (·.p.name == c) with
        | some pr => (judgePrepared es res pr over).toBool | none => false)
    rw [List.find?_map]
    have hcomp : ((fun kv : String × Bool => kv.1 == c) ∘
        fun pr : Prepared => (pr.p.name, (judgePrepared es res pr over).toBool)) =
        (fun pr : Prepared => pr.p.name == c) := by
      funext pr; rfl
    rw [hcomp]
    cases prs.find? (·.p.name == c) <;> rfl

private theorem filter_evalCoupledSlot_fst (es res : List Entry) (over : IncrementalJudge.Tip)
    (idx : Index.Buckets PageId Entry) (P : BTurn → Bool) :
    ∀ (items : List (BTurn × Option IncrementalJudge.Slot)),
      (((items.map (evalCoupledSlot es res over idx)).filter (fun y => P y.1)).map
          (fun y => (y.1, y.2.map Prod.fst))).map Prod.fst =
        (items.map Prod.fst).filter P
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.filter_cons, evalCoupledSlot_fst]
    cases P x.1 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact filter_evalCoupledSlot_fst es res over idx P xs
    | true =>
      simp only [↓reduceIte, List.map_cons, evalCoupledSlot_fst]
      exact congrArg (x.1 :: ·) (filter_evalCoupledSlot_fst es res over idx P xs)

private theorem filter_evalCoupledSlot_inv (s : Store) (actorRef : Actor)
    (es res : List Entry) (over : IncrementalJudge.Tip)
    (idx : Index.Buckets PageId Entry) (P : BTurn → Bool)
    (items : List (BTurn × Option IncrementalJudge.Slot))
    (hinv : ∀ x ∈ items, CoupledSlotInv s actorRef x) :
    ∀ z ∈ ((items.map (evalCoupledSlot es res over idx)).filter (fun y => P y.1)).map
        (fun y => (y.1, y.2.map Prod.fst)),
      CoupledSlotInv s actorRef z := by
  induction items with
  | nil => intro _ hz; nomatch hz
  | cons x xs ih =>
    intro z hz
    have ih' := ih (fun w hw => hinv w (.tail _ hw))
    simp only [List.map_cons, List.filter_cons, evalCoupledSlot_fst] at hz
    cases hp : P x.1 with
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at hz
      exact ih' z hz
    | true =>
      simp only [hp, ↓reduceIte, List.map_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · unfold CoupledSlotInv
        dsimp only
        rw [evalCoupledSlot_fst, evalCoupledSlot_prepared]
        exact hinv x (.head _)
      · exact ih' z hz

private def shrinkCoupledSlots (es : List Entry) (idx : Index.Buckets PageId Entry)
    (items : List (BTurn × Option IncrementalJudge.Slot)) :
    List (BTurn × Option IncrementalJudge.Slot) :=
  let prs := items.filterMap fun x => x.2.map IncrementalJudge.Slot.prepared
  let res := turnEntries es (prs.map fun pr => (pr.p, pr.G', []))
  let over := tipOf prs
  let evaluated := items.map (evalCoupledSlot es res over idx)
  let verdicts := evaluated.filterMap fun y =>
    y.2.map fun r => (r.1.prepared.p.name, r.2)
  (evaluated.filter fun y =>
    match y.1.writes.head? >>= fun c => verdicts.find? (·.1 == c) with
    | some kv => kv.2
    | none => false).map fun y => (y.1, y.2.map Prod.fst)

private theorem shrinkCoupledSlots_fst (s : Store) (actorRef : Actor)
    (items : List (BTurn × Option IncrementalJudge.Slot)) (cand : List BTurn)
    (hcand : items.map Prod.fst = cand)
    (hinv : ∀ x ∈ items, CoupledSlotInv s actorRef x) :
    (shrinkCoupledSlots s.entries (entryLinkIndex s.entries) items).map Prod.fst =
      coupledKeepSpec s actorRef cand := by
  subst hcand
  unfold shrinkCoupledSlots coupledKeepSpec
  dsimp only
  have hprs_eq := items_prs_eq s actorRef items hinv
  rw [hprs_eq]
  generalize hprs : ((items.map Prod.fst).filterMap turnSingleText?).filterMap
    (prepareSingleText? s actorRef) = prs at hprs_eq ⊢
  generalize turnEntries s.entries (prs.map fun pr => (pr.p, pr.G', [])) = res
  generalize tipOf prs = over
  rw [filter_evalCoupledSlot_fst s.entries res over (entryLinkIndex s.entries)
    (fun t => match t.writes.head? >>= fun c =>
        ((items.map (evalCoupledSlot s.entries res over (entryLinkIndex s.entries))).filterMap
          fun y => y.2.map fun r => (r.1.prepared.p.name, r.2)).find? (·.1 == c) with
      | some kv => kv.2
      | none => false) items]
  apply List.filter_congr
  intro t _
  rw [evalCoupledSlots_verdicts s.entries res over items, hprs_eq]
  exact verdict_lookup_eq s.entries res over prs t

private theorem shrinkCoupledSlots_inv (s : Store) (actorRef : Actor)
    (es : List Entry) (idx : Index.Buckets PageId Entry)
    (items : List (BTurn × Option IncrementalJudge.Slot))
    (hinv : ∀ x ∈ items, CoupledSlotInv s actorRef x) :
    ∀ z ∈ shrinkCoupledSlots es idx items, CoupledSlotInv s actorRef z := by
  let prs := items.filterMap fun x => x.2.map IncrementalJudge.Slot.prepared
  let res := turnEntries es (prs.map fun pr => (pr.p, pr.G', []))
  let over := tipOf prs
  let verdicts := (items.map (evalCoupledSlot es res over idx)).filterMap
    fun y => y.2.map fun r => (r.1.prepared.p.name, r.2)
  exact filter_evalCoupledSlot_inv s actorRef es res over idx
    (fun t => match t.writes.head? >>= fun c => verdicts.find? (·.1 == c) with
      | some kv => kv.2 | none => false) items hinv

private def findCoupledGroupSlots (s : Store) (st : VaultStore)
    (idx : Index.Buckets PageId Entry) (actor : String) (actorRef : Actor) :
    Nat → List (BTurn × Option IncrementalJudge.Slot) → Option (BTurn × Store × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | fuel + 1, items0 =>
    let items := pruneExternalStaleSlots st items0.length items0
    if items.length < 2 then none else
    let texts := items.filterMap (fun x => turnSingleText? x.1)
    if texts.length != items.length then none else
    match s.writeTexts texts actorRef with
    | .ok sAfter =>
      let cand := items.map Prod.fst
      (mkCoupledTurn cand sAfter actor actorRef).map fun bt =>
        (bt, sAfter, cand.flatMap BTurn.writes)
    | .error _ =>
      let keep := shrinkCoupledSlots s.entries idx items
      if keep.length ≥ 2 && keep.length < items.length then
        findCoupledGroupSlots s st idx actor actorRef fuel keep
      else none

private theorem findCoupledGroupSlots_eq (s : Store) (actor : String) (actorRef : Actor) :
    ∀ (fuel : Nat) (items0 : List (BTurn × Option IncrementalJudge.Slot)),
      (∀ x ∈ items0, CoupledSlotInv s actorRef x) →
      findCoupledGroupSlots s (vaultStates s) (entryLinkIndex s.entries) actor actorRef fuel items0 =
        findCoupledGroup s actor actorRef fuel (items0.map Prod.fst)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, [_], _ => rfl
  | fuel + 1, x1 :: x2 :: xs, hinv0 => by
    change (let items := pruneExternalStaleSlots (vaultStates s) (x1 :: x2 :: xs).length (x1 :: x2 :: xs)
        if items.length < 2 then none else
        if (items.filterMap (fun x => turnSingleText? x.1)).length != items.length then none else
        match s.writeTexts (items.filterMap (fun x => turnSingleText? x.1)) actorRef with
        | .ok sAfter =>
          (mkCoupledTurn (items.map Prod.fst) sAfter actor actorRef).map fun bt =>
            (bt, sAfter, (items.map Prod.fst).flatMap BTurn.writes)
        | .error _ =>
          let keep := shrinkCoupledSlots s.entries (entryLinkIndex s.entries) items
          if keep.length ≥ 2 && keep.length < items.length then
            findCoupledGroupSlots s (vaultStates s) (entryLinkIndex s.entries) actor actorRef fuel keep
          else none) =
      (let cand := pruneExternalStale (vaultStates s)
          ((x1 :: x2 :: xs).map Prod.fst).length ((x1 :: x2 :: xs).map Prod.fst)
        if cand.length < 2 then none else
        if (cand.filterMap turnSingleText?).length != cand.length then none else
        match s.writeTexts (cand.filterMap turnSingleText?) actorRef with
        | .ok sAfter =>
          (mkCoupledTurn cand sAfter actor actorRef).map fun bt =>
            (bt, sAfter, cand.flatMap BTurn.writes)
        | .error _ =>
          if (coupledKeepSpec s actorRef cand).length ≥ 2 &&
              (coupledKeepSpec s actorRef cand).length < cand.length then
            findCoupledGroup s actor actorRef fuel (coupledKeepSpec s actorRef cand)
          else none)
    dsimp only
    rw [List.length_map]
    generalize hitems : pruneExternalStaleSlots (vaultStates s) (x1 :: x2 :: xs).length
      (x1 :: x2 :: xs) = items
    generalize hcand_def : pruneExternalStale (vaultStates s) (x1 :: x2 :: xs).length
      ((x1 :: x2 :: xs).map Prod.fst) = cand
    have hcand : items.map Prod.fst = cand := by
      rw [← hitems, ← hcand_def]
      exact pruneExternalStaleSlots_fst (vaultStates s) (x1 :: x2 :: xs).length (x1 :: x2 :: xs)
    have hlen : items.length = cand.length := by
      rw [← hcand, List.length_map]
    have htexts : items.filterMap (fun x => turnSingleText? x.1) = cand.filterMap turnSingleText? := by
      rw [← hcand, List.filterMap_map]
      rfl
    have hinv : ∀ x ∈ items, CoupledSlotInv s actorRef x := by
      intro x hx
      rw [← hitems] at hx
      exact hinv0 x (pruneExternalStaleSlots_mem (vaultStates s) (x1 :: x2 :: xs).length hx)
    rw [hlen, htexts]
    by_cases hlt : cand.length < 2
    · simp only [hlt, ↓reduceIte]
    · simp only [hlt, ↓reduceIte]
      by_cases hne : (cand.filterMap turnSingleText?).length != cand.length
      · simp only [hne, ↓reduceIte]
      · simp only [hne, ↓reduceIte]
        cases s.writeTexts (cand.filterMap turnSingleText?) actorRef with
        | ok sAfter =>
          dsimp only
          rw [hcand]
        | error _ =>
          dsimp only
          have hk_eq := shrinkCoupledSlots_fst s actorRef items cand hcand hinv
          have hk_inv := shrinkCoupledSlots_inv s actorRef s.entries (entryLinkIndex s.entries) items hinv
          generalize shrinkCoupledSlots s.entries (entryLinkIndex s.entries) items = keepItems
            at hk_eq hk_inv ⊢
          have hk_len : keepItems.length = (coupledKeepSpec s actorRef cand).length := by
            rw [← hk_eq, List.length_map]
          rw [hk_len]
          cases hgo : (decide ((coupledKeepSpec s actorRef cand).length ≥ 2) &&
              decide ((coupledKeepSpec s actorRef cand).length < cand.length))
          · simp only [Bool.false_eq_true, ↓reduceIte]
          · simp only [↓reduceIte]
            rw [← hk_eq]
            exact findCoupledGroupSlots_eq s actor actorRef fuel keepItems hk_inv

/-- Incremental coupled-group search: prepares single-page `Slot`s and builds `entryLinkIndex s.entries`
once when candidate shrinking begins, retaining each surviving turn's `CachedJudgment` across
shrinking rounds via `IncrementalJudge.validateSlot`. -/
def findCoupledGroupIncremental (s : Store) (actor : String) (actorRef : Actor) :
    Nat → List BTurn → Option (BTurn × Store × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | fuel + 1, cand0 =>
    let st := vaultStates s
    let cand := pruneExternalStale st cand0.length cand0
    if cand.length < 2 then none else
    let texts := cand.filterMap turnSingleText?
    if texts.length != cand.length then none else
    match s.writeTexts texts actorRef with
    | .ok sAfter =>
      (mkCoupledTurn cand sAfter actor actorRef).map fun bt =>
        (bt, sAfter, cand.flatMap BTurn.writes)
    | .error _ =>
      let idx := entryLinkIndex s.entries
      let items := cand.map (initCoupledSlot s actorRef)
      let keep := shrinkCoupledSlots s.entries idx items
      if keep.length ≥ 2 && keep.length < cand.length then
        findCoupledGroupSlots s st idx actor actorRef fuel keep
      else none

theorem findCoupledGroupIncremental_eq (s : Store) (actor : String) (actorRef : Actor)
    (fuel : Nat) (cand0 : List BTurn) :
    findCoupledGroupIncremental s actor actorRef fuel cand0 =
      findCoupledGroup s actor actorRef fuel cand0 := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases cand0 with
    | nil => rfl
    | cons t1 rest =>
      cases rest with
      | nil => rfl
      | cons t2 ts =>
        change (let cand := pruneExternalStale (vaultStates s) (t1 :: t2 :: ts).length (t1 :: t2 :: ts)
            if cand.length < 2 then none else
            if (cand.filterMap turnSingleText?).length != cand.length then none else
            match s.writeTexts (cand.filterMap turnSingleText?) actorRef with
            | .ok sAfter =>
              (mkCoupledTurn cand sAfter actor actorRef).map fun bt =>
                (bt, sAfter, cand.flatMap BTurn.writes)
            | .error _ =>
              let keep := shrinkCoupledSlots s.entries (entryLinkIndex s.entries)
                (cand.map (initCoupledSlot s actorRef))
              if keep.length ≥ 2 && keep.length < cand.length then
                findCoupledGroupSlots s (vaultStates s) (entryLinkIndex s.entries) actor actorRef fuel keep
              else none) =
          (let cand := pruneExternalStale (vaultStates s) (t1 :: t2 :: ts).length (t1 :: t2 :: ts)
            if cand.length < 2 then none else
            if (cand.filterMap turnSingleText?).length != cand.length then none else
            match s.writeTexts (cand.filterMap turnSingleText?) actorRef with
            | .ok sAfter =>
              (mkCoupledTurn cand sAfter actor actorRef).map fun bt =>
                (bt, sAfter, cand.flatMap BTurn.writes)
            | .error _ =>
              if (coupledKeepSpec s actorRef cand).length ≥ 2 &&
                  (coupledKeepSpec s actorRef cand).length < cand.length then
                findCoupledGroup s actor actorRef fuel (coupledKeepSpec s actorRef cand)
              else none)
        dsimp only
        generalize pruneExternalStale (vaultStates s) (t1 :: t2 :: ts).length (t1 :: t2 :: ts) = cand
        by_cases hlt : cand.length < 2
        · simp only [hlt, ↓reduceIte]
        · simp only [hlt, ↓reduceIte]
          by_cases hne : (cand.filterMap turnSingleText?).length != cand.length
          · simp only [hne, ↓reduceIte]
          · simp only [hne, ↓reduceIte]
            cases s.writeTexts (cand.filterMap turnSingleText?) actorRef with
            | ok sAfter => rfl
            | error _ =>
              dsimp only
              have hcand : (cand.map (initCoupledSlot s actorRef)).map Prod.fst = cand :=
                initCoupledSlot_fst s actorRef cand
              have hinv : ∀ x ∈ cand.map (initCoupledSlot s actorRef), CoupledSlotInv s actorRef x := by
                intro x hx
                obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
                exact initCoupledSlot_inv s actorRef t
              have hk_eq := shrinkCoupledSlots_fst s actorRef
                (cand.map (initCoupledSlot s actorRef)) cand hcand hinv
              have hk_inv := shrinkCoupledSlots_inv s actorRef s.entries (entryLinkIndex s.entries)
                (cand.map (initCoupledSlot s actorRef)) hinv
              generalize shrinkCoupledSlots s.entries (entryLinkIndex s.entries)
                (cand.map (initCoupledSlot s actorRef)) = keepItems at hk_eq hk_inv ⊢
              have hk_len : keepItems.length = (coupledKeepSpec s actorRef cand).length := by
                rw [← hk_eq, List.length_map]
              rw [hk_len]
              cases hgo : (decide ((coupledKeepSpec s actorRef cand).length ≥ 2) &&
                  decide ((coupledKeepSpec s actorRef cand).length < cand.length))
              · simp only [Bool.false_eq_true, ↓reduceIte]
              · simp only [↓reduceIte]
                rw [← hk_eq]
                exact findCoupledGroupSlots_eq s actor actorRef fuel keepItems hk_inv

@[csimp]
theorem findCoupledGroup_eq_incremental : @findCoupledGroup = @findCoupledGroupIncremental := by
  funext s actor actorRef fuel cand0
  exact (findCoupledGroupIncremental_eq s actor actorRef fuel cand0).symm

def hasForwardReadPin : List BTurn → Bool
  | [] => false
  | t :: rest =>
    (t.turn.readPins.any fun p => rest.any fun w => w.writes.contains p.cell) || hasForwardReadPin rest

def storeHasBacklinkLaw (s : Store) : Bool :=
  s.pages.any fun p =>
    match p.current with
    | none => false
    | some G => (lawLines (settled G)).any fun (_, v) => (v.splitOn "linked_by").length > 1

/-- Sound fast-path check: a list of topologically ordered single-page writes can contain a
mutually coupled multi-page turn only if `pending.length ≥ 2` and at least one write births an
unborn page, edits a `_kind` page, introduces or faces a `linked_by` backlink law, or retains a
forward/cyclic `readPin` after `orderWrites`. When none holds, single-page replay in `orderWrites`
order is already complete and skips pre-simulation in `plan`. -/
def mayHaveCoupledGroup (hasBacklinks : Bool) (s : Store) (pending : List BTurn) : Bool :=
  if pending.length < 2 then false
  else
    hasBacklinks ||
    hasForwardReadPin pending ||
    pending.any fun t =>
      (match t.lawKey with | some lk => (lk.splitOn "linked_by").length > 1 | none => false) ||
      t.writes.any fun c =>
        c == "_kind" || c.endsWith "/_kind" ||
        match s.page? c with
        | some p => p.history.isEmpty
        | none => true

def scheduleFreeWrites (auth : Authority) (book : LawBook) (actor : String) (actorRef : Actor) :
    Nat → Store → List BTurn → Store × List BTurn
  | 0, s, pending => (s, pending)
  | fuel + 1, s, pending =>
    let (s1, ok1, rem1) := simSingles auth book pending.length s pending
    if rem1.length < 2 then (s1, ok1 ++ rem1)
    else
      let authOk := rem1.filter fun t => (authRefusal auth book t).isNone
      match findCoupledGroup s1 actor actorRef authOk.length authOk with
      | none => (s1, ok1 ++ rem1)
      | some (coupled, s2, usedCells) =>
        let rem2 := rem1.filter fun t => !t.writes.any (usedCells.contains ·)
        let (s3, restOut) := scheduleFreeWrites auth book actor actorRef fuel s2 rem2
        (s3, ok1 ++ [coupled] ++ restOut)

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

def namesOfFast (here other : Store) : List String :=
  Index.eraseDupsFast ((here.pages.map (·.name)) ++ (other.pages.map (·.name)))

@[csimp]
theorem namesOf_eq_fast : @namesOf = @namesOfFast := by
  funext here other
  simp only [namesOf, namesOfFast, Index.eraseDupsFast_eq]

/-- Each page's base history (a page `skip` names: here's). -/
def baseOfPlan (here other : Store) (skip : String → Bool) : String → List Graph := fun n =>
  if skip n then liveHistory here n else sharedPrefix (historyIn here n) (historyIn other n)

/-- The base's store of states: every page merged at its base state. -/
def baseStates (names : List String) (baseOf : String → List Graph) : VaultStore := fun c =>
  if names.contains c then some (stateAt (baseOf c)) else none

/-! ## The frontmatter, merged field by field

Two writes of one page merge by their texts, as the pushout of the two versions. A frontmatter is
not prose: its lines are fields, and two replicas that change two different fields of one page
(the tip a job's `base`, the fork its `spent`) changed two different things. The pushout cannot
tell: a changed line is a deleted atom and an inserted one, and two lines changed next to each other
leave one position with two live successors, a section with both candidates, whose settled text
holds neither. So the frontmatter is merged as fields (`Obend.Doc.mergeCell3` at each key, over the
base's), and written on the pushout as one more version when the pushout's settled frontmatter is
not that merge (`frontFix`); a field both changed to different values is a conflict, and the
pushout's section stands for it. -/

/-- A frontmatter's lines keyed by their field: `none` when a line names no field or two lines name
one (such a frontmatter is merged as text). -/
def frontLines (src : String) : Option (List (String × String)) :=
  let fm := (splitFront src).1
  let kv := fm.filterMap fun l => (splitColon l).map fun (k, _) => (k, l)
  if kv.length == fm.length && (kv.map (·.1)).eraseDups.length == kv.length then some kv else none

/-- One field of a three-way frontmatter merge: its line at the base, here and there, by
`mergeCell3`. -/
def frontCell (base l r : List (String × String)) (k : String) : MergeCellResult (Option String) :=
  mergeCell3 (base.lookup k) (l.lookup k) (r.lookup k)

/-- The value a field merges to (none: absent, or in conflict). -/
def frontValue (base l r : List (String × String)) (k : String) : Option String :=
  match frontCell base l r k with
  | .merged v => v
  | .conflict _ _ _ => none

/-- **A frontmatter merged field by field**: every field here or there, in here's order then
there's, at the line it merges to; `none` when a field was changed on both sides to different
lines. -/
def mergeFront (base l r : List (String × String)) : Option (List (String × String)) :=
  let keys := Obend.Doc.Patch.dedupStringKeys (l.map (·.1) ++ r.map (·.1))
  if keys.all fun k => match frontCell base l r k with | .merged _ => true | .conflict _ _ _ => false then
    some (keys.filterMap fun k => (frontValue base l r k).map fun v => (k, v))
  else none

theorem lookup_none_of_not_mem {l : List (String × String)} {k : String} (h : k ∉ l.map (·.1)) :
    l.lookup k = none := Obend.Doc.Patch.lookup_eq_none_of_not_mem_map_fst h

theorem mem_of_lookup_some {l : List (String × String)} {k v : String} (h : l.lookup k = some v) :
    k ∈ l.map (·.1) := by
  exact Classical.byContradiction fun hn => by rw [lookup_none_of_not_mem hn] at h; cases h

/-- Under disjoint changes, each field merges to the side that changed it (or the base's). -/
theorem frontCell_disjoint {base l r : List (String × String)} {k : String}
    (hd : l.lookup k = base.lookup k ∨ r.lookup k = base.lookup k) :
    frontCell base l r k = .merged (if l.lookup k = base.lookup k then r.lookup k else l.lookup k) := by
  unfold frontCell
  rcases hd with h | h
  · rw [h]; simp
  · by_cases hl : l.lookup k = base.lookup k
    · rw [hl, h]; simp
    · rw [h]; simp [hl]

/-- **A field-wise merge of two frontmatters that change disjoint fields keeps every changed line**:
when no field is changed on both sides, the merge exists, and each field reads, in it, as the side
that changed it wrote it (its line, or its absence), and as the base had it where neither did. -/
theorem mergeFront_keeps (base l r : List (String × String))
    (hd : ∀ k, l.lookup k = base.lookup k ∨ r.lookup k = base.lookup k) :
    ∃ m, mergeFront base l r = some m ∧ ∀ k,
      (l.lookup k ≠ base.lookup k → m.lookup k = l.lookup k) ∧
      (r.lookup k ≠ base.lookup k → m.lookup k = r.lookup k) ∧
      (l.lookup k = base.lookup k → r.lookup k = base.lookup k → m.lookup k = base.lookup k) := by
  have hall : (Obend.Doc.Patch.dedupStringKeys (l.map (·.1) ++ r.map (·.1))).all
      (fun k => match frontCell base l r k with | .merged _ => true | .conflict _ _ _ => false) = true := by
    rw [List.all_eq_true]; intro k _; rw [frontCell_disjoint (hd k)]
  refine ⟨(Obend.Doc.Patch.dedupStringKeys (l.map (·.1) ++ r.map (·.1))).filterMap
      (fun k => (frontValue base l r k).map fun v => (k, v)), by simp only [mergeFront, hall, ite_true], ?_⟩
  intro k
  have hv : frontValue base l r k = (if l.lookup k = base.lookup k then r.lookup k else l.lookup k) := by
    unfold frontValue; rw [frontCell_disjoint (hd k)]
  have hlk : ∀ (m : List (String × String)), m = (Obend.Doc.Patch.dedupStringKeys (l.map (·.1) ++ r.map (·.1))).filterMap
      (fun k => (frontValue base l r k).map fun v => (k, v)) →
      m.lookup k = (if l.lookup k = base.lookup k then r.lookup k else l.lookup k) := by
    intro m hm; subst hm
    rw [Obend.Doc.lookup_filterMap_keyed, hv]
    split
    · rfl
    · rename_i hn
      rw [Obend.Doc.Patch.mem_dedupStringKeys, List.mem_append, not_or] at hn
      rw [lookup_none_of_not_mem hn.1, lookup_none_of_not_mem hn.2]; simp
  have := hlk _ rfl
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · rw [this, ite_eq_right h]
  · rcases hd k with h' | h'
    · rw [this, ite_eq_left h']
    · exact absurd h' h
  · rw [this, ite_eq_left h1, h2]

/-- **A frontmatter merged field by field, a field both changed going to the side that saw the other's
line and moved on**: as `mergeFront`, except that a field changed on both sides to different lines is
the right's when the right's history passes through the left's line (`seenR`), the left's when the left's
passes through the right's (`seenL`), and a conflict (`none`) otherwise. -/
def mergeFrontSeen (base l r : List (String × String)) (seenL seenR : String → List String) :
    Option (List (String × String)) :=
  let keys := Obend.Doc.Patch.dedupStringKeys (l.map (·.1) ++ r.map (·.1))
  let pick : String → Option (Option String) := fun k =>
    match frontCell base l r k with
    | .merged v => some v
    | .conflict _ vl vr =>
      match vl, vr with
      | some x, _ => if (seenR k).contains x then some vr else
          match vr with
          | some y => if (seenL k).contains y then some vl else none
          | none => none
      | none, some y => if (seenL k).contains y then some vl else none
      | none, none => none
  if keys.all fun k => (pick k).isSome then
    some (keys.filterMap fun k => ((pick k).getD none).map fun v => (k, v))
  else none

/-- The rendering with its frontmatter replaced by `m`: the frontmatter ends at the first `---` line
after the first that is outside every section (`none` when the text has no frontmatter, or a section
reaches past its end). -/
def replaceFront (rendered : String) (m : List (String × String)) : Option String :=
  match rendered.splitOn "\n" with
  | first :: rest =>
    if trim first != "---" then none else
    let rec go : List String → Bool → Option (List String)
      | [], _ => none
      | l :: ls, inSec =>
        if l.startsWith "<<<<<<< " then go ls true
        else if l.startsWith ">>>>>>> " then go ls false
        else if !inSec && trim l == "---" then some ls
        else go ls inSec
    (go rest false).map fun body => "\n".intercalate (("---" :: m.map (·.2)) ++ ("---" :: body))
  | [] => none

/-- **The pushout of two versions with its frontmatter merged by field**: `M0`, the pushout, unless the
three frontmatters (the base's `bt`, here's `at`, there's `bs`) merge field by field (`mergeFront`, or
`mergeFrontSeen` over each side's versions since the base, `hl` and `hr`) to other lines than `M0`'s
settled frontmatter holds; then the owner's edit of `M0` to that frontmatter,
the rest of its rendering kept. -/
def frontFix (H : Obend.Digest.HashBytes.Hash) (es : List Entry) (name : String) (who : AtomId → String) (bt at' bs : String)
    (hl hr : List Graph) (M0 : Graph) : Graph :=
  match frontLines bt, frontLines at', frontLines bs with
  | some fb, some fl, some fr =>
    let seen : List Graph → String → List String := fun h k =>
      h.filterMap fun G => (frontLines (settled G)).bind (·.lookup k)
    match (mergeFront fb fl fr).orElse fun _ => mergeFrontSeen fb fl fr (seen hl) (seen hr) with
    | some m =>
      let now := (frontLines (settled M0)).getD []
      if now.length == m.length && m.all (fun kv => now.lookup kv.1 == some kv.2) then M0
      else match replaceFront (render M0 name who) m with
        | some md =>
          let b := editPatch H M0 (align (pieces M0 name who) (contents (resolveIn H es) (stripToks (tokens md)))) "owner"
          if b.ops.isEmpty then M0 else M0.apply b.ops
        | none => M0
    | none => M0
  | _, _, _ => M0

def pairCell {α β γ : Type} (g1 : String → Option α) (g2 : String → Option β)
    (k : String → α → β → Option γ) (x : String) : Option (String × Option γ) :=
  match g1 x, g2 x with
  | some A, some B => some (x, k x A B)
  | _, _ => none

def mergedSpec (H : Obend.Digest.HashBytes.Hash) (here other : Store) (names : List String)
    (baseOf : String → List Graph) : String → Option Graph :=
  let who : String → AtomId → String := fun c => ((here.page? c).map Page.who).getD fun _ => "owner"
  let mergedAll : List (String × Option Graph) := names.filterMap (pairCell
    (fun c => (liveHistory here c).getLast?)
    (fun c => (liveHistory other c).getLast?)
    (fun c A B => (mergePage A B).map fun M0 =>
      frontFix H here.entries c (who c) (((baseOf c).getLast?.map settled).getD "") (settled A) (settled B)
        ((liveHistory here c).drop (baseOf c).length) ((liveHistory other c).drop (baseOf c).length) M0))
  fun c => (mergedAll.lookup c).join

def planWithOps
    (label : String)
    (skip : String → Bool) (auth : ForkAuth)
    (names : List String)
    (histHere histOther liveHere liveOther : String → List Graph)
    (mkBaseOf : (String → Bool) → String → List Graph)
    (mkBaseStates : (String → List Graph) → VaultStore)
    (mkBaseSto : (String → List Graph) → Store)
    (filtIn filtOut : List String → List String → List String)
    (mkWriteHere : String → List Graph → Graph → BTurn)
    (mkWriteOther : String → List Graph → Graph → BTurn)
    (mkMerged : (String → List Graph) → String → Option Graph)
    (mkVers : String → List Graph → List (Graph × List (AtomId × String)))
    (otherPage : String → Option Page) : Plan :=
  let book : LawBook := names.map fun n => (n, ⟨"owner", [], [], []⟩)
  let unauthClash : String → Bool := fun n =>
    if skip n || auth.actor == "owner" then false
    else
      let sp := sharedPrefix (histHere n) (histOther n)
      let hh := liveHere n
      let ho := liveOther n
      !hh.isEmpty && hh != sp && !ho.isEmpty && ho != sp &&
        match ho.getLast? with
        | some G => (authRefusal auth.tipAuth book (mkWriteOther n sp G)).isSome
        | none => false
  let baseOf := mkBaseOf (fun n => skip n || unauthClash n)
  let store : VaultStore := mkBaseStates baseOf
  let receipts := baseReceipts names baseOf
  let live := names.filter (!skip ·)
  let baseSto := mkBaseSto baseOf
  let movedL := live.filter fun n =>
    let h := liveHere n
    !h.isEmpty && h != baseOf n
  let rightBaseOf : String → List Graph := fun n =>
    if unauthClash n then sharedPrefix (histHere n) (histOther n) else baseOf n
  let movedR := live.filter fun n =>
    let h := liveOther n
    !h.isEmpty && h != rightBaseOf n
  let clashSet := filtIn movedL movedR
  let freeNamesL := filtOut movedL clashSet
  let freeNamesR := filtOut movedR clashSet
  let clashL := clashSet.filterMap fun n => (liveHere n).getLast?.map (mkWriteHere n (baseOf n))
  let clashR := clashSet.filterMap fun n => (liveOther n).getLast?.map (mkWriteOther n (baseOf n))
  let rawFreeL := freeNamesL.filterMap fun n => (liveHere n).getLast?.map (mkWriteHere n (baseOf n))
  let rawFreeR := freeNamesR.filterMap fun n => (liveOther n).getLast?.map (mkWriteOther n (rightBaseOf n))
  let ordFreeL := orderWrites rawFreeL.length rawFreeL
  let ordFreeR := orderWrites rawFreeR.length rawFreeR
  let hasBacklinks := (ordFreeL.length ≥ 2 || ordFreeR.length ≥ 2) && storeHasBacklinkLaw baseSto
  let needL := mayHaveCoupledGroup hasBacklinks baseSto ordFreeL
  let needR := mayHaveCoupledGroup hasBacklinks baseSto ordFreeR ||
    (ordFreeR.length ≥ 2 && ordFreeL.any fun t =>
      match t.lawKey with | some lk => (lk.splitOn "linked_by").length > 1 | none => false)
  let (sAfterLeft, schedFreeL) :=
    if needL then
      scheduleFreeWrites auth.tipAuth book "owner" .owner ordFreeL.length baseSto ordFreeL
    else if needR then
      let (s1, _, _) := simSingles auth.tipAuth book ordFreeL.length baseSto ordFreeL
      (s1, ordFreeL)
    else
      (baseSto, ordFreeL)
  let (_, schedFreeR) :=
    if needR then
      scheduleFreeWrites auth.tipAuth book auth.actor auth.actorRef ordFreeR.length sAfterLeft ordFreeR
    else
      (sAfterLeft, ordFreeR)
  let leftTurns := orderWrites (schedFreeL ++ clashL).length (schedFreeL ++ clashL)
  let rightTurns := orderWrites (schedFreeR ++ clashR).length (schedFreeR ++ clashR)
  let merged := mkMerged baseOf
  let text : TextMerge :=
    { state := fun c =>
        match (liveHere c).getLast?, (liveOther c).getLast? with
        | some _, some _ => some ((merged c).map fun M => pageState M (liveHere c).length)
        | _, _ => none
      write := fun c => (merged c).map fun M =>
        { versions := mkVers c (baseOf c) ++
            [(M, addedFrom label (otherPage c) (liveHere c).getLast? M)] } }
  { names, baseOf, text,
    base := { store, book, auth := auth.tipAuth, history := receipts, vault := some baseSto },
    left := ⟨"here", receipts, leftTurns.map Act.write⟩,
    right := ⟨label, receipts, rightTurns.map Act.write⟩ }

/-- **Read two stores as two branches of their base.** Pages `skip` names (another merge's: the
ledger's register) are left out: at the base as here holds them, acted on by neither side.
Coupled non-clashing writes on a branch (whose link/backlink laws require them to land together)
are grouped into atomic multi-page `BTurn`s, and forks attributed to a member (`auth`) carry that
member's authority to the tip. -/
def plan (H : Obend.Digest.HashBytes.Hash) (here other : Store) (label : String)
    (skip : String → Bool := fun _ => false) (auth : ForkAuth := {}) : Plan :=
  let names := namesOf here other
  planWithOps label skip auth names
    (historyIn here) (historyIn other) (liveHistory here) (liveHistory other)
    (baseOfPlan here other)
    (baseStates names)
    (baseStore here other names)
    (fun xs ys => xs.filter (ys.contains ·))
    (fun xs ys => xs.filter (!ys.contains ·))
    (writeOf here "")
    (fun n bp G => writeOfAuth other label n bp G auth)
    (mergedSpec H here other names)
    (versionsSince here "")
    other.page?

theorem lookup_pairCell_nodup {α β γ : Type} (g1 : String → Option α) (g2 : String → Option β)
    (k : String → α → β → Option γ) :
    ∀ (xs : List String), xs.Nodup → ∀ (c : String),
      ((xs.filterMap (pairCell g1 g2 k)).lookup c).join =
        if c ∈ xs then
          match g1 c, g2 c with
          | some A, some B => k c A B
          | _, _ => none
        else none
  | [], _, _ => by simp
  | x :: xs, hnd, c => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    have ih := lookup_pairCell_nodup g1 g2 k xs hxs c
    by_cases hcx : c = x
    · subst hcx
      cases hg1 : g1 c with
      | none =>
        have hpc : pairCell g1 g2 k c = none := by simp [pairCell, hg1]
        rw [List.filterMap_cons, hpc, ih]
        simp [hx]
      | some A =>
        cases hg2 : g2 c with
        | none =>
          have hpc : pairCell g1 g2 k c = none := by simp [pairCell, hg1, hg2]
          rw [List.filterMap_cons, hpc, ih]
          simp [hx]
        | some B =>
          have hpc : pairCell g1 g2 k c = some (c, k c A B) := by simp [pairCell, hg1, hg2]
          rw [List.filterMap_cons, hpc]
          simp
    · have hbeq : (c == x) = false := beq_false_of_ne hcx
      cases hg1 : g1 x with
      | none =>
        have hpc : pairCell g1 g2 k x = none := by simp [pairCell, hg1]
        rw [List.filterMap_cons, hpc, ih]
        simp [hcx]
      | some A =>
        cases hg2 : g2 x with
        | none =>
          have hpc : pairCell g1 g2 k x = none := by simp [pairCell, hg1, hg2]
          rw [List.filterMap_cons, hpc, ih]
          simp [hcx]
        | some B =>
          have hpc : pairCell g1 g2 k x = some (x, k x A B) := by simp [pairCell, hg1, hg2]
          rw [List.filterMap_cons, hpc]
          simp [List.lookup, hbeq, ih, hcx]

def writeOfWithEntries (es : List Entry) (byName : Index.Buckets String Page)
    (label name : String) (bp : List Graph) (G : Graph) : BTurn :=
  let pins := if hasLinkLaws es name G then pinsAt es (linksAt es name G) else []
  let h := ((Index.first byName name).map (·.history)).getD []
  let vs := h.drop bp.length
  let prevs := (bp.getLast?) :: vs.dropLast.map some
  let vers := (vs.zip prevs).map fun (G1, A) => (G1, addedFrom label (Index.first byName name) A G1)
  { label := name, actor := "owner",
    turn := writeTurn name (stateAt bp) (pageState G (h.length - 1)) pins (requestAt "owner" 0),
    text := some { versions := vers },
    lawKey := lawKeyOf bp G }

theorem writeOfWithEntries_fn_eq (s : Store) (label : String) :
    writeOfWithEntries s.entries (Index.ofList Page.name s.pages) label =
      writeOf s label := by
  funext name bp G
  simp only [writeOfWithEntries, writeOf, versionsSince, liveHistory, Index.first_ofList, Store.page?]

def writeOfAuthWithEntries (es : List Entry) (byName : Index.Buckets String Page)
    (label name : String) (bp : List Graph) (G : Graph) (auth : ForkAuth := {}) : BTurn :=
  if auth.actor == "owner" then
    writeOfWithEntries es byName label name bp G
  else
    let pins := if hasLinkLaws es name G then pinsAt es (linksAt es name G) else []
    let lk := lawKeyOf bp G
    let h := ((Index.first byName name).map (·.history)).getD []
    let vs := h.drop bp.length
    let prevs := (bp.getLast?) :: vs.dropLast.map some
    let vers := (vs.zip prevs).map fun (G1, A) => (G1, addedFrom label (Index.first byName name) A G1)
    let pw : PageWrite := { versions := vers }
    { label := name, actor := auth.actor,
      turn := writeTurn name (stateAt bp) (pageState G (h.length - 1)) pins (requestAt auth.actor 0),
      relies := auth.reliesOf name lk.isSome,
      text := none,
      lawKey := lk,
      texts := [(name, pw)],
      actorRef := auth.actorRef }

theorem writeOfAuthWithEntries_eq (s : Store) (label name : String) (bp : List Graph) (G : Graph)
    (auth : ForkAuth) :
    writeOfAuthWithEntries s.entries (Index.ofList Page.name s.pages) label name bp G auth =
      writeOfAuth s label name bp G auth := by
  unfold writeOfAuthWithEntries writeOfAuth
  by_cases ha : auth.actor == "owner"
  · simp only [ha, ↓reduceIte, writeOfWithEntries_fn_eq]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte, versionsSince, liveHistory, Index.first_ofList, Store.page?]

def histInIndexed (byName byTombs : Index.Buckets String Page) (n : String) : List Graph :=
  match Index.first byName n with
  | some p => p.history
  | none => ((Index.first byTombs n).map (·.history)).getD []

theorem histInIndexed_eq (s : Store) :
    histInIndexed (Index.ofList Page.name s.pages) (Index.ofList Page.name s.tombs) = historyIn s := by
  funext n
  simp only [histInIndexed, historyIn, Store.page?, Index.first_ofList]

def liveHistIndexed (byName : Index.Buckets String Page) (n : String) : List Graph :=
  ((Index.first byName n).map (·.history)).getD []

theorem liveHistIndexed_eq (s : Store) :
    liveHistIndexed (Index.ofList Page.name s.pages) = liveHistory s := by
  funext n
  simp only [liveHistIndexed, liveHistory, Store.page?, Index.first_ofList]

theorem isSome_find_id_eq_contains (xs : List String) (x : String) :
    (xs.find? (fun y => id y == x)).isSome = xs.contains x := by
  rw [List.isSome_find?]
  apply Bool.eq_iff_iff.mpr
  simp

def baseStatesIndexed (namesIdx : Index.Buckets String String) (baseOf : String → List Graph) : VaultStore :=
  fun c => if (Index.first namesIdx c).isSome then some (stateAt (baseOf c)) else none

theorem baseStatesIndexed_fn_eq (names : List String) :
    baseStatesIndexed (Index.ofList id names) = baseStates names := by
  funext baseOf c
  simp only [baseStatesIndexed, baseStates, Index.first_ofList, isSome_find_id_eq_contains]

def baseStoreIndexed (here : Store) (names : List String) (namesIdx : Index.Buckets String String)
    (herePages otherPages : Index.Buckets String Page) (baseOf : String → List Graph) : Store :=
  let bMine := here.pages.map fun p =>
    if (Index.first namesIdx p.name).isSome then { p with history := baseOf p.name } else p
  let bTheirs := (names.filter fun n => (Index.first herePages n).isNone).filterMap fun n =>
    (Index.first otherPages n).map fun q =>
      ({ name := n, id := q.id, history := baseOf n, seen := none, authors := q.authors, note := none, kind := q.kind } : Page)
  { here with pages := bMine ++ bTheirs }

theorem baseStoreIndexed_fn_eq (here other : Store) (names : List String) :
    baseStoreIndexed here names (Index.ofList id names)
        (Index.ofList Page.name here.pages) (Index.ofList Page.name other.pages) =
      baseStore here other names := by
  funext baseOf
  simp only [baseStoreIndexed, baseStore, baseMine, baseTheirs, Store.page?,
    Index.first_ofList, isSome_find_id_eq_contains]

def versionsSinceIndexed (byName : Index.Buckets String Page) (live : String → List Graph)
    (label c : String) (bp : List Graph) : List (Graph × List (AtomId × String)) :=
  let h := live c
  let vs := h.drop bp.length
  let prevs := (bp.getLast?) :: vs.dropLast.map some
  (vs.zip prevs).map fun (G1, A) => (G1, addedFrom label (Index.first byName c) A G1)

theorem versionsSinceIndexed_eq (s : Store) (label : String) :
    versionsSinceIndexed (Index.ofList Page.name s.pages) (liveHistory s) label =
      versionsSince s label := by
  funext c bp
  simp only [versionsSinceIndexed, versionsSince, Index.first_ofList, Store.page?]

def baseOfPlanWith (histHere histOther liveHere : String → List Graph) (skip : String → Bool) :
    String → List Graph :=
  fun n => if skip n then liveHere n else sharedPrefix (histHere n) (histOther n)

theorem baseOfPlanWith_eq (here other : Store) :
    baseOfPlanWith (historyIn here) (historyIn other) (liveHistory here) = baseOfPlan here other := by
  funext skip n
  rfl

def filterInIdx (xs ys : List String) : List String :=
  let idx := Index.ofList id ys
  xs.filter fun n => (Index.first idx n).isSome

theorem filterInIdx_fn_eq :
    filterInIdx = (fun (xs ys : List String) => xs.filter (ys.contains ·)) := by
  funext xs ys
  unfold filterInIdx
  simp only [Index.first_ofList, isSome_find_id_eq_contains]

def filterNotInIdx (xs ys : List String) : List String :=
  let idx := Index.ofList id ys
  xs.filter fun n => !(Index.first idx n).isSome

theorem filterNotInIdx_fn_eq :
    filterNotInIdx = (fun (xs ys : List String) => xs.filter (!ys.contains ·)) := by
  funext xs ys
  unfold filterNotInIdx
  simp only [Index.first_ofList, isSome_find_id_eq_contains]

def pageByIdx (idx : Index.Buckets String Page) (c : String) : Option Page :=
  Index.first idx c

theorem pageByIdx_eq (s : Store) :
    pageByIdx (Index.ofList Page.name s.pages) = s.page? := by
  funext c
  exact Index.first_ofList Page.name s.pages c

def mergedFastAt (H : Obend.Digest.HashBytes.Hash) (hereEntries : List Entry)
    (herePages : Index.Buckets String Page) (liveHere liveOther baseOf : String → List Graph)
    (c : String) : Option Graph :=
  match (liveHere c).getLast?, (liveOther c).getLast? with
  | some A, some B => (mergePage A B).map fun M0 =>
      frontFix H hereEntries c (((Index.first herePages c).map Page.who).getD fun _ => "owner")
        (((baseOf c).getLast?.map settled).getD "") (settled A) (settled B)
        ((liveHere c).drop (baseOf c).length) ((liveOther c).drop (baseOf c).length) M0
  | _, _ => none

theorem mergedFastAt_eq (H : Obend.Digest.HashBytes.Hash) (here other : Store) :
    mergedFastAt H here.entries (Index.ofList Page.name here.pages)
        (liveHistory here) (liveHistory other) =
      mergedSpec H here other (namesOf here other) := by
  funext baseOf c
  unfold mergedSpec mergedFastAt
  dsimp only
  rw [lookup_pairCell_nodup _ _ _ (namesOf here other) (Index.eraseDups_nodup _) c]
  simp only [Index.first_ofList, Store.page?]
  by_cases hc : c ∈ namesOf here other
  · simp only [hc, ↓reduceIte]
    cases (liveHistory here c).getLast? <;> cases (liveHistory other c).getLast? <;> rfl
  · simp only [hc, ↓reduceIte]
    have hnone : here.page? c = none := by
      cases hp : here.page? c with
      | none => rfl
      | some p =>
        exfalso
        apply hc
        simp only [namesOf, List.mem_eraseDups, List.mem_append, List.mem_map]
        exact Or.inl ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp⟩
    have hlive : liveHistory here c = [] := by simp [liveHistory, hnone]
    simp [hlive]

/-- Indexed & demand-driven `Merge.plan`: builds `Page` and `Entry` lookup tables once in
`O(N log N)` and computes 3-way `mergePage` + `frontFix` ONLY for clashing pages queried by
`Branch.merge` instead of eagerly merging all `N` untouched pages in the vault. -/
def planIndexed (H : Obend.Digest.HashBytes.Hash) (here other : Store) (label : String)
    (skip : String → Bool := fun _ => false) (auth : ForkAuth := {}) : Plan :=
  let names := namesOf here other
  let namesIdx := Index.ofList id names
  let herePages := Index.ofList Page.name here.pages
  let otherPages := Index.ofList Page.name other.pages
  let hereTombs := Index.ofList Page.name here.tombs
  let otherTombs := Index.ofList Page.name other.tombs
  let hereEntries := here.entries
  let otherEntries := other.entries
  let histHere := histInIndexed herePages hereTombs
  let histOther := histInIndexed otherPages otherTombs
  let liveHere := liveHistIndexed herePages
  let liveOther := liveHistIndexed otherPages
  planWithOps label skip auth names
    histHere histOther liveHere liveOther
    (baseOfPlanWith histHere histOther liveHere)
    (baseStatesIndexed namesIdx)
    (baseStoreIndexed here names namesIdx herePages otherPages)
    filterInIdx
    filterNotInIdx
    (writeOfWithEntries hereEntries herePages "")
    (fun n bp G => writeOfAuthWithEntries otherEntries otherPages label n bp G auth)
    (mergedFastAt H hereEntries herePages liveHere liveOther)
    (versionsSinceIndexed herePages liveHere "")
    (pageByIdx otherPages)

@[csimp]
theorem plan_eq_indexed : @plan = @planIndexed := by
  funext H here other label skip auth
  unfold planIndexed plan
  dsimp only
  simp only [histInIndexed_eq, liveHistIndexed_eq, baseOfPlanWith_eq,
    baseStatesIndexed_fn_eq, baseStoreIndexed_fn_eq, filterInIdx_fn_eq, filterNotInIdx_fn_eq,
    writeOfWithEntries_fn_eq, writeOfAuthWithEntries_eq,
    mergedFastAt_eq, versionsSinceIndexed_eq, pageByIdx_eq]

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
def mergeVault (H : Obend.Digest.HashBytes.Hash) (here other : Store) (label : String)
    (skip : String → Bool := fun _ => false) (auth : ForkAuth := {}) :
    Store × List String :=
  let P := plan H here other label skip auth
  match Branch.merge P.base P.left P.right P.text with
  | .error e => (here, ["not merged: " ++ e])
  | .ok m =>
    let tip := m.tip.vault.getD here
    let landedLeft := (landedOn .left m.landed).flatMap BTurn.writes ++ (landedOn .both m.landed).flatMap BTurn.writes
    let leftWrites := (writesOf P.left.acts).flatMap BTurn.writes
    let unsettled := leftWrites.filter fun n => !landedLeft.contains n
    let why : String → String := fun n =>
      match m.refused.find? (fun r => (r.2.1.splitOn " + ").contains n) with
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
    let actPages : Act → List String
      | .write t => t.writes
      | _ => []
    let notes1 := (m.landed.filter fun x => x.1 != .left).flatMap fun x => (actPages x.2).map fun n =>
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
theorem plan_agrees (H : Obend.Digest.HashBytes.Hash) (here other : Store) (label : String)
    (skip : String → Bool) (auth : ForkAuth := {}) :
    Agrees (plan H here other label skip auth).base := by
  intro v hv x
  simp only [plan, planWithOps, Option.some.injEq] at hv ⊢
  subst hv
  rw [baseStore_states]

/-- **After a vault merge the store's page versions and the vault's agree**: the tip's state of every
page is the state of the tip store's page at its current version. -/
theorem mergeVault_agrees (H : Obend.Digest.HashBytes.Hash) (here other : Store) (label : String)
    (skip : String → Bool) (auth : ForkAuth := {}) {m : Merged}
    (h : Branch.merge (plan H here other label skip auth).base (plan H here other label skip auth).left
      (plan H here other label skip auth).right (plan H here other label skip auth).text = .ok m) :
    Agrees m.tip :=
  merge_vault_agrees h (plan_agrees H here other label skip auth)

end Obend.Vault.Merge
