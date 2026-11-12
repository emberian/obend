module
/-
# Obend.Vault.Branch — branches with consent, and settlement at the tip

An offline copy of a store is a BRANCH: the receipted history it forked at (its base) and the acts
it posted since. Two branches of one base come back together by `merge`, and the merge is judged at
the TIP: the configuration in which both sides' changes of authority and of law are visible.

The state is the vault's turn state (`Obend.Vault.Hyperedge`): a `VaultStore` of page states, every
data write a `VaultTurn` (its read pins, its write cells with pre- and post-state). Beside it a
configuration keeps the LAW BOOK (each page's owner, its law lines read by `lawOfLine` exactly as the
vault reads a page's frontmatter, and the pages it links to), the AUTHORITY (the `Sturdyref`s of
`Obend.Vault.Rehydration` granted so far and the uris revoked, as `Obend.Vault.Carry`'s `LiveWorld`
keeps them), the receipted history, and the conflicts the merges left open.

An act of a branch is a write (a `VaultTurn` by an actor, relying on some sturdyrefs), a change of a
page's laws (`relaw`, the owner's), the grant of a sturdyref (the owner of its cell's) or its
revocation (the same). Every act goes through `admitAct`, on a branch while it is offline and at the
tip when it merges; the difference is only the configuration it is judged at.

* **Merge is a pushout over the base, and a conflict is a state.** The writes of the two sides that
  write no cell in common (`clash`) are replayed at the tip, left then right. The tip is a serial
  order: a write that read a cell the other side wrote is not a conflict but is checked when it
  lands, refused by name if the cell moved under its pins (`Refusal.stale`), and every law over links
  reading the cell is judged at the tip whichever lands first;
  the store the merge reaches agrees with the left's landed turns on the cells they write, with the
  right's on theirs, and with the base everywhere else, and the two write sets are disjoint
  (`merge_is_pushout`). A pair that clashes is kept as a `Conflict.writes` in the tip's state, both
  candidates and the cells named, and neither lands (`clash_is_conflict_state`); `resolve` lands one
  candidate through the same judgment and names the one it drops.
* **Their laws agree.** A clashing pair writing the same cells from the same base merges instead of
  conflicting when every differing field is one its page declares mergeable (`merge FIELD: add`,
  `max`, `union`) and every law that judges the cell is I-confluent for that merge (`confluentLaw`):
  the page's own laws, and the laws over links of every page linking to it (`linkedLaws`). The
  merged state keeps every own law both sides kept (`iconfluent_merge_lawful`, `mergeCell_lawful`)
  and every such law over links, on the identity occasion it is judged on at the cell
  (`iconfluent_merge_links_lawful`, `mergeCell_links_lawful`). A linked law that is not I-confluent
  leaves the pair a conflict, not a refusal: a refused merged pair would drop both writes, where a
  conflict keeps both as candidates until one is chosen. A store that keeps texts merges a page both
  sides wrote by its texts instead (`TextMerge`: the markdown vault's `mergePage` pushout,
  `Obend.Vault.Merge`), and that merged write is judged at the tip like any other; and
  the merged write lands once, as one receipt from both sides (`Side.both`), each side's authority
  checked on its own and the merged write judged at the tip like any other. Identical writes merge
  with no declaration. The store theorem covers it (`merge_is_pushout`'s third part). Two relaws of one page that differ
  are a `Conflict.laws`, and the page keeps its base laws. The merged history extends the base
  (`merge_extends_history`).
* **One judge, in a vault.** A configuration may keep the vault's store itself (`Config.vault`), and a
  write may carry its text (`BTurn.text`). Then the write is judged and landed by the store's own
  write (`Store.writeText`: `prepareWrite`, `judgePrepared` with rows, kind pins, `poster` and
  `unresolved`), and by nothing else: admitted at the tip exactly when the store's write lands, the
  tip keeping exactly the store it reaches, refused in the store's own words
  (`tip_lands_iff_store_lands`, `tip_refuses_iff_store_refuses`), its consent the store's
  (`WriteConsents`, `TextConsents` through `judgePrepared`). The page's laws are lines of its text, so
  in a vault they are the store's, not the book's. The store of states and the vault agree on every
  page at its current version, at the base and so after the merge (`Agrees`, `merge_vault_agrees`).
* **Laws settle first, in every store.** The tip applies relaws before any write, and the writes that
  change a page's law lines (`BTurn.lawKey`: a vault page's law lines are its text), of either side
  and merged, land before every other write (`lawFirst`); a law-changing write that also changes data
  is ordered as a law and judged as a whole. Two such writes of one page leaving different law lines
  do not merge: a conflict, the base laws standing.
* **Pins and the tip's judgment both stand.** A write's pins say what it read on its branch; the tip
  judges it again on what is there. The judgment at the tip is what consent is; the pins are what
  makes a read that moved a refusal by name rather than a silent re-reading (a write whose text was
  composed against a page as it was is not landed against the page as it is), which the vault's
  walkthrough shows (section 8).
* **Consent from the causal cone.** A write is judged by every law of every page in its cone at the
  tip: the written page's own laws (old to new), its laws over links at every page it links to, and
  the laws over links of every page that links to it, at it as written. A landed write has the
  consent of every one of them by the laws' meaning (`landed_consents`, through `judge_admits`); a
  refusal names the law, whose it is (the owner of the page that wrote it) and the page it was
  judged at (`Refusal.law`). The laws over links give the two-page case; the cone is the general one.
* **Settlement at the tip.** The tip applies both sides' grants and revocations first; every write is
  then judged against that authority, never the authority of its own branch. A landed write relied
  only on sturdyrefs live at the tip, and every page it wrote that is not its actor's was granted to
  it by one of them (`settled_at_tip`); a revocation landed by either side is visible at the tip
  (`tip_sees_every_revocation`), so no write relying on a sturdyref revoked on the other side lands
  (`revoked_elsewhere_never_lands`). A write's authority is checked before its pins, and when both
  fail the refusal carries both, the authority reason first (`Refusal.also`,
  `admitWrite_names_authority`): a revoked sturdyref is never hidden behind a moved pin. Revocation is the one non-monotone act: every other act keeps
  every live sturdyref live, and no act unrevokes (`revocation_only_nonmonotone`). A consequence of
  the strict reading: a branch's own write made before its own revocation of the sturdyref it relied
  on does not settle either; authority is read at settlement, not at authoring.
* **Order.** Swapping the sides is not the identity: the tip settles non-write acts left first, and a
  write is judged at the height it lands at (see "Order" below, with both counterexamples as tests).
  The clash relation is symmetric (`clash_comm`, `freeLeft_swap`) and the store depends only on what
  landed (`merge_swap_store`).
* **What a branch cannot learn of the other side's hidden cells** (after `InfoFlow/Confinement` in
  breadstuffs). Integrity: a landed write of a page that is not its actor's carries a live grant
  for it (`settled_at_tip`). Confinement of the store: when the right side's writes access only
  cells of a hidden set `H` and the left's access none of them, the left's landed writes and the tip
  outside `H` are the same whatever the right wrote inside `H`, given the same non-write acts
  (`merge_confines_hidden`). The channels this does not close are named, not hidden:
  1. the merge report and the receipted history carry the other side's labels, the cells its
     receipts name, and which of its acts landed: metadata the merge publishes;
  2. a law over links from a page the left writes INTO a hidden page is judged at that page's state,
     so whether the left's write lands depends on a hidden state (the refusal channel of
     `Confinement`'s `refusal_leaks`); `lean/tests/vault/Branch.lean` exhibits it;
  3. a refusal for a revoked sturdyref names the uri and who revoked it, by design;
  4. a conflict is reported exactly when the other side wrote a cell this side writes, and a stale
     refusal when it wrote a cell this side's write read;
  5. the order the merge replays (left first) and its running time.
-/
public import Obend.Vault.Store
public import Obend.Vault.Rehydration
public import Obend.Tactic.Tooth
@[expose] public section

namespace Obend.Vault.Branch

open Obend.Vault
open Obend.Vault.Rehydration (Sturdyref)
open Obend.Vault.Affordance (Auth fireGate)
open Obend.Spec.Law (LawExpr Facts)
open Obend.Core.Data (Data)
open Obend.Doc (Graph AtomId)

set_option autoImplicit false

/-! ## The law book -/

/-- How a page's field merges when both sides wrote it: a counter that adds (both sides' increases
over the base), a maximum, or a set (a natural read as a bitmask) that unions. -/
inductive MergeKind
  | add
  | max
  | union
deriving DecidableEq, Repr

def MergeKind.ofString? : String → Option MergeKind
  | "add" => some .add
  | "max" => some .max
  | "union" => some .union
  | _ => none

def MergeKind.name : MergeKind → String
  | .add => "add"
  | .max => "max"
  | .union => "union"

/-- The merged value of a field from its base `b` and the two sides' `x` and `y`. -/
def MergeKind.join : MergeKind → Nat → Nat → Nat → Nat
  | .add, b, x, y => b + (x - b) + (y - b)
  | .max, _, x, y => Max.max x y
  | .union, _, x, y => x ||| y

/-- When a field's two writes merge by its kind at all: a counter only grows. -/
def MergeKind.fits : MergeKind → Nat → Nat → Nat → Bool
  | .add, b, x, y => b ≤ x && b ≤ y
  | _, _, _, _ => true

/-- A page's entry in the law book: whose page it is, its laws (`PAGE: NAME`, expression, text, as
`lawOfLine` reads a law line), the pages it links to, and how its fields merge (`merge FIELD: KIND`;
a field with no declared merge does not merge). -/
structure PageLaws where
  owner : String
  laws : Laws := []
  links : List String := []
  merges : List (String × MergeKind) := []
deriving DecidableEq

/-- A page's law book entry from its law lines `(NAME, TEXT)`, read as the vault reads them. -/
def PageLaws.ofLines (page owner : String) (links : List String) (lines : List (String × String)) :
    Except String PageLaws := do
  let laws ← lines.mapM (lawOfLine page)
  pure ⟨owner, laws, links, []⟩

/-- A page's own laws (judged on its write, old to new). -/
def PageLaws.own (pl : PageLaws) : List (String × LawExpr) :=
  (pl.laws.filter fun l => isOwnLaw l.2.2).map fun (n, e, _) => (n, e)

/-- A page's laws over its links (judged at every page it links to). -/
def PageLaws.overLinks (pl : PageLaws) : List (String × LawExpr) := linkLaws pl.laws

/-- A page's laws over its backlinks (judged at every page that links to it, with `listed`). -/
def PageLaws.overLinkedBy (pl : PageLaws) : List (String × LawExpr) := byLaws pl.laws

/-- The text of one of a page's laws, by name. -/
def PageLaws.text (pl : PageLaws) (law : String) : String :=
  ((pl.laws.find? (·.1 == law)).map (·.2.2)).getD ""

abbrev LawBook := List (String × PageLaws)

/-- Set a page's entry. -/
def setLaws (book : LawBook) (page : String) (pl : PageLaws) : LawBook :=
  if book.any (·.1 == page) then book.map fun e => if e.1 == page then (page, pl) else e
  else book ++ [(page, pl)]

/-! ## Authority -/

/-- The sturdyrefs granted so far and the uris revoked, each with who revoked it. -/
structure Authority where
  refs : List (Sturdyref Data) := []
  revoked : List (String × String) := []

namespace Authority

def find? (a : Authority) (u : String) : Option (Sturdyref Data) := a.refs.find? (·.uri == u)

def isRevoked (a : Authority) (u : String) : Bool := a.revoked.any (·.1 == u)

def revokedBy (a : Authority) (u : String) : String :=
  ((a.revoked.find? (·.1 == u)).map (·.2)).getD ""

/-- A sturdyref is live when it was granted and is not revoked. -/
def live (a : Authority) (u : String) : Bool := (a.find? u).isSome && !a.isRevoked u

end Authority

/-- A sturdyref grants a write of a cell when it names the cell and its membrane holds `write`. -/
def grantsWrite (sr : Sturdyref Data) (cell : String) : Bool :=
  sr.cellId == cell && fireGate [.write] sr.lineage.held

/-! ## Acts, receipts, refusals, conflicts -/

/-- A receipt: its place in the history, the branch it came from, the act's label, the cells. -/
structure Receipt where
  seq : Nat
  origin : String
  label : String
  cells : List String
deriving DecidableEq, Repr

/-- A write of a branch: a turn by an actor, relying on the sturdyrefs `relies`. -/
structure BTurn where
  label : String
  actor : String
  turn : VaultTurn
  relies : List String := []
  /-- the text the write lands, in a configuration that keeps the store's texts (`Config.vault`) -/
  text : Option PageWrite := none
  /-- the page's law lines as the write leaves them, when it changes them (a vault's page carries
  its laws in its text): a law-changing write, settled before every other write at the tip -/
  lawKey : Option String := none
  /-- the texts of a multi-page (or actor-attributed) branch turn (`text = none`), paired with cell names -/
  texts : List (String × PageWrite) := []
  /-- the store actor under whose standing `texts` are prepared and judged -/
  actorRef : Actor := .owner

/-- A write that changes a page's law lines. -/
def BTurn.isLaw (t : BTurn) : Bool := t.lawKey.isSome

def BTurn.writes (t : BTurn) : List String := t.turn.writeFootprint

/-- The cells a write touches at a law book: what it pins, what it writes, and the pages the laws
over links of a page it writes read. -/
def BTurn.access (book : LawBook) (t : BTurn) : List String :=
  t.turn.accessFootprint ++ t.writes.flatMap fun c => ((book.lookup c).map (·.links)).getD []

inductive Act
  | write (t : BTurn)
  | relaw (label actor page : String) (pl : PageLaws)
  | revoke (label actor uri : String)
  | grant (label actor : String) (sr : Sturdyref Data)

def Act.label : Act → String
  | .write t => t.label
  | .relaw l .. => l
  | .revoke l .. => l
  | .grant l .. => l

def Act.isWrite : Act → Bool
  | .write _ => true
  | _ => false

def Act.isRevoke : Act → Bool
  | .revoke .. => true
  | _ => false

/-- Why an act was refused. -/
inductive Refusal
  /-- a pin or a pre-state the turn read on its branch is not the state here -/
  | stale (cell : String) (expected current : Option Data)
  | noPage (page : String)
  | unknownRef (uri : String)
  /-- relied on a sturdyref revoked here, by `by_` -/
  | revokedRef (uri by_ : String)
  | unauthorized (cell owner actor : String)
  /-- refused by the law `law` (with its text), `owner`'s, judged at `page` -/
  | law (law owner page text reason : String)
  | undecided (page reason : String)
  | notOwner (page owner actor : String)
  /-- an authority reason and a stale pin at once: both named, the authority first -/
  | also (authority stale : Refusal)
  /-- refused by the store's own judgment of the page's write (`Store.writeText`), its text -/
  | store (page reason : String)

def Refusal.text : Refusal → String
  | .stale c e cur => "stale: it read " ++ c ++ " as it was on its branch (" ++ stateDiffText e cur ++ ")"
  | .noPage p => "no page " ++ p ++ " in the law book here"
  | .unknownRef u => "relied on " ++ u ++ ", which no one granted here"
  | .revokedRef u b => "relied on the sturdyref " ++ u ++ ", revoked at the tip by " ++ b
  | .unauthorized c o a => a ++ " wrote " ++ c ++ ", which is " ++ o ++
      "'s, relying on no live sturdyref that grants it"
  | .law l o p txt _ => "refused by " ++ l ++ " (" ++ o ++ "'s law `" ++ txt ++ "`), judged at " ++ p
  | .undecided p r => "undecided at " ++ p ++ ": " ++ r
  | .notOwner p o a => p ++ " is " ++ o ++ "'s; " ++ a ++ " may not change its laws or its sturdyrefs"
  | .also a p => a.text ++ "; and " ++ p.text
  | .store _ r => r

/-- A merge's open question, kept in the state. -/
inductive Conflict
  /-- two writes whose footprints clash at `cells`: both candidates kept, neither landed -/
  | writes (cells : List String) (left right : String × BTurn)
  /-- both sides changed a page's laws, differently: the page keeps its base laws -/
  | laws (page left right : String)

def Conflict.text : Conflict → String
  | .writes cs (ln, l) (rn, r) => "conflict at " ++ ", ".intercalate cs ++ ": " ++ ln ++ "'s " ++
      l.label ++ " and " ++ rn ++ "'s " ++ r.label ++ " (both kept as candidates; neither landed)"
  | .laws p ln rn => "conflict at the laws of " ++ p ++ ": " ++ ln ++ " and " ++ rn ++
      " both changed them (the base laws stand)"

/-- A configuration: the store, the law book, the authority, the history, the open conflicts, and,
for a vault, the vault's store itself (its pages' texts and histories, its members, kinds and
environment): where it is kept, a write that carries its text is judged and landed by the store's
own write, and nothing else (`tip_lands_iff_store_lands`). -/
structure Config where
  store : VaultStore
  book : LawBook := []
  auth : Authority := {}
  history : List Receipt := []
  conflicts : List Conflict := []
  vault : Option Store := none

/-! ## The judgment of a write -/

def factsAt (h : Nat) : Facts := ⟨some 0, some 0, h, h⟩

/-- The request a write by `actor` at height `h` is judged under. -/
def requestAt (actor : String) (h : Nat) : Data := requestBy actor actor .write (factsAt h)

/-- A page's own laws on its write, old to new, on the states with the fields the laws read. -/
def judgeOwn (page : String) (lin : List (String × LawExpr)) (o n rq : Data) : Verdict :=
  if lin.isEmpty then .admitted
  else judge (rekey lin n).1 page lin (rekey lin o).2 (rekey lin n).2 rq

def ofLinkRefusal (pl : PageLaws) (r : LinkRefusal) : Refusal :=
  if r.law == "" || r.state.isNone then .undecided r.page r.reason
  else .law r.law pl.owner r.page (pl.text r.law) r.reason

/-- The laws over links of `page` judged at the pages `at_`. -/
def linksRefusal (s : VaultStore) (page : String) (pl : PageLaws) (rq : Data) (at_ : List String) :
    Option Refusal :=
  if pl.overLinks.isEmpty then none else (judgeLinksIn s page pl.overLinks rq at_).map (ofLinkRefusal pl)

/-- The laws over links of every page that links to `c`, judged at `c`. -/
def backlinkRefusal (book : LawBook) (s : VaultStore) (rq : Data) (c : String) : Option Refusal :=
  book.findSome? fun e => if e.1 != c && e.2.links.contains c then linksRefusal s e.1 e.2 rq [c] else none

/-- The pages of the book that link to `c`. -/
def linkersOf (book : LawBook) (c : String) : List String :=
  (book.filter fun e => e.1 != c && e.2.links.contains c).map (·.1)

/-- The laws over backlinks in a write's cone: `c`'s own at every page linking to it (each read with
`listed`, whether `c` links back), and those of every page `c` links to, at `c` (with `listed`,
whether that page links back to `c`). -/
def byRefusal (book : LawBook) (s : VaultStore) (rq : Data) (c : String) (pl : PageLaws) : Option Refusal :=
  match (if pl.overLinkedBy.isEmpty then none
      else (judgeLinksIn (listedStore s pl.links) c pl.overLinkedBy rq (linkersOf book c)).map (ofLinkRefusal pl)) with
  | some r => some r
  | none => pl.links.findSome? fun q => match book.lookup q with
    | some ql => if q != c && !ql.overLinkedBy.isEmpty then
        (judgeLinksIn (listedStore s ql.links) q ql.overLinkedBy rq [c]).map (ofLinkRefusal ql) else none
    | none => none

/-- **The cone of a written cell**: its page's own laws, its laws over links at its links, the
laws over links of the pages linking to it, and the laws over backlinks both ways (`byRefusal`), on
the store as written. -/
def coneRefusal (book : LawBook) (s' : VaultStore) (rq : Data) (d : CellDelta) : Option Refusal :=
  match book.lookup d.cell with
  | none => some (.noPage d.cell)
  | some pl =>
    match judgeOwn d.cell pl.own d.preState d.postState rq with
    | .refused law why => some (.law law pl.owner d.cell (pl.text law) why)
    | .undecided why => some (.undecided d.cell why)
    | .admitted =>
      match linksRefusal s' d.cell pl rq pl.links with
      | some r => some r
      | none =>
        match backlinkRefusal book s' rq d.cell with
        | some r => some r
        | none => byRefusal book s' rq d.cell pl

/-- A turn's pins: its read pins and every write cell at its pre-state. -/
def turnPins (t : VaultTurn) : Footprint :=
  t.readPins ++ t.writeCells.map fun d => ⟨d.cell, some d.preState⟩

def pinRefusal (s : VaultStore) (t : VaultTurn) : Option Refusal :=
  match Footprint.firstStale? s (turnPins t) with
  | none => none
  | some (c, e, cur) => some (.stale c e cur)

/-- **The authority check**: every sturdyref relied on is live here, and every page written that is
not the actor's is granted by one of them. Evaluated at the configuration the act is judged at; at
a merge that is the tip. (The `#tooth` below removes it.) -/
def authRefusal (a : Authority) (book : LawBook) (t : BTurn) : Option Refusal :=
  match t.relies.find? (fun u => !a.live u) with
  | some u => some (if a.isRevoked u then .revokedRef u (a.revokedBy u) else .unknownRef u)
  | none =>
    t.turn.writeCells.findSome? fun d =>
      match book.lookup d.cell with
      | none => some (.noPage d.cell)
      | some pl =>
        if pl.owner == t.actor then none
        else if t.relies.any (fun u => ((a.find? u).map (grantsWrite · d.cell)).getD false) then none
        else some (.unauthorized d.cell pl.owner t.actor)

def receiptOf (c : Config) (origin label : String) (cells : List String) : Receipt :=
  ⟨c.history.length, origin, label, cells⟩

/-- The refusal of a write's preconditions: its authority and its pins, both checked; when both fail
the authority reason comes first and the stale pin is kept beside it (`Refusal.also`), so a revoked
sturdyref is never hidden behind a moved pin (`admitWrite_names_authority`). -/
def preRefusal (c : Config) (t : BTurn) : Option Refusal :=
  match authRefusal c.auth c.book t, pinRefusal c.store t.turn with
  | some a, some p => some (.also a p)
  | some a, none => some a
  | none, some p => some p
  | none, none => none

/-- A store's refusal, said without the page's name it begins with. -/
def dropPage (page msg : String) : String :=
  if msg.startsWith (page ++ ": ") then String.ofList (msg.toList.drop (page.length + 2)) else msg

/-- The state of a page not born: an empty record. -/
def unborn : Data := .record []

/-- A page's state at the last version of a history, or `unborn`. -/
def stateAt (h : List Graph) : Data :=
  match h.getLast? with
  | some G => pageState G (h.length - 1)
  | none => unborn

/-- The states a vault's store holds: each page at its current version (`unborn` before its birth). -/
def vaultStates (v : Store) : VaultStore := fun c => (v.page? c).map fun p => stateAt p.history

/-- **The judgment of a write, and what it lands.** In a vault (`Config.vault`), every write is a
write of one page carrying its text, and it is the store's write of it (`Store.writeText`:
`prepareWrite`, `judgePrepared` with its rows, kind pins, `poster` and `unresolved`, and the landing
rule), refused by name in the store's own words; it lands only if the state its turn says it writes
is the state the store lands (so the store of states and the vault never part, `Agrees`). Otherwise
every page in the write's cone is judged on the store of states (`coneRefusal`). -/
def judgeWrite (c : Config) (t : BTurn) : Except Refusal (Option Store) :=
  match c.vault, t.text, t.turn.writeCells with
  | some s, some w, [d] =>
    match s.writeText d.cell w with
    | .error m => .error (.store d.cell (dropPage d.cell m))
    | .ok s' =>
      match vaultStates s' d.cell with
      | some x =>
        if Obend.Law.termEq x.term d.postState.term then .ok (some s')
        else .error (.store d.cell "its turn does not say the state its text lands")
      | none => .error (.store d.cell "its text lands no page")
  | some s, none, ds@(d₀ :: _) =>
    if t.texts.map (·.1) == ds.map (·.cell) then
      match s.writeTexts t.texts t.actorRef with
      | .error m =>
        let pg := d₀.cell
        .error (.store pg (dropPage pg m))
      | .ok s' =>
        if ds.all (fun d => match vaultStates s' d.cell with
            | some x => Obend.Law.termEq x.term d.postState.term
            | none => false) then .ok (some s')
        else .error (.store d₀.cell "its turn does not say the states its texts land")
    else .error (.store (t.writes.headD "") "a write in a vault carries its text, for one page")
  | some _, _, _ => .error (.store (t.writes.headD "") "a write in a vault carries its text, for one page")
  | none, _, _ =>
    match t.turn.writeCells.findSome? (coneRefusal c.book (applyTurn c.store t.turn)
        (requestAt t.actor c.history.length)) with
    | some r => .error r
    | none => .ok c.vault

/-- **Admit a write**: its authority is live, its pins hold, and it is judged (`judgeWrite`): in a
vault by the store's own write, which lands it; otherwise by every page in its cone. -/
def admitWrite (c : Config) (origin : String) (t : BTurn) : Except Refusal Config :=
  match preRefusal c t with
  | some r => .error r
  | none =>
  match judgeWrite c t with
  | .error r => .error r
  | .ok v => .ok { c with
      store := applyTurn c.store t.turn
      vault := v
      history := c.history ++ [receiptOf c origin t.label t.writes] }

def ownerOf (book : LawBook) (page : String) : Option String := (book.lookup page).map (·.owner)

/-- Admit an act. A relaw, a grant and a revocation are their page's owner's. -/
def admitAct (c : Config) (origin : String) : Act → Except Refusal Config
  | .write t => admitWrite c origin t
  | .relaw label actor page pl =>
    let ok : Except Refusal Config :=
      .ok { c with book := setLaws c.book page pl, history := c.history ++ [receiptOf c origin label [page]] }
    match ownerOf c.book page with
    | some o => if o == actor && pl.owner == actor then ok else .error (.notOwner page o actor)
    | none => if pl.owner == actor then ok else .error (.notOwner page pl.owner actor)
  | .revoke label actor uri =>
    match c.auth.find? uri with
    | none => .error (.unknownRef uri)
    | some sr =>
      match ownerOf c.book sr.cellId with
      | none => .error (.noPage sr.cellId)
      | some o =>
        if o == actor then
          .ok { c with auth := { c.auth with revoked := c.auth.revoked ++ [(uri, origin ++ "'s " ++ label)] },
                       history := c.history ++ [receiptOf c origin label [sr.cellId]] }
        else .error (.notOwner sr.cellId o actor)
  | .grant label actor sr =>
    match ownerOf c.book sr.cellId with
    | none => .error (.noPage sr.cellId)
    | some o =>
      if o == actor then
        .ok { c with auth := { c.auth with refs := c.auth.refs ++ [sr] },
                     history := c.history ++ [receiptOf c origin label [sr.cellId]] }
      else .error (.notOwner sr.cellId o actor)

/-! ## Runs, branches, the merge -/

/-- Where a landed write came from: one side, or both (two writes merged by their page's law). -/
inductive Side
  | left
  | right
  | both
deriving DecidableEq, Repr

/-- A run of acts: the configuration reached, the acts that landed, the ones refused and why. -/
structure Run where
  config : Config
  landed : List (Side × Act)
  refused : List (Side × String × Refusal)

/-- Run acts in order; a refused act moves nothing and is kept with its refusal. -/
def runActs (name : Side → String) (c : Config) : List (Side × Act) → Run
  | [] => ⟨c, [], []⟩
  | (sd, a) :: rest =>
    match admitAct c (name sd) a with
    | .ok c' => let r := runActs name c' rest; { r with landed := (sd, a) :: r.landed }
    | .error e => let r := runActs name c rest; { r with refused := (sd, a.label, e) :: r.refused }

/-- Run writes in order (`runActs` on writes, `runActs_writes`). -/
def runWrites (name : Side → String) (c : Config) : List (Side × BTurn) → Run
  | [] => ⟨c, [], []⟩
  | (sd, t) :: rest =>
    match admitWrite c (name sd) t with
    | .ok c' => let r := runWrites name c' rest; { r with landed := (sd, .write t) :: r.landed }
    | .error e => let r := runWrites name c rest; { r with refused := (sd, t.label, e) :: r.refused }

/-- A branch: its name, the history it forked at, the acts it posted since. -/
structure Branch where
  name : String
  base : List Receipt
  acts : List Act := []

/-- An offline copy of a configuration. -/
def fork (c : Config) (name : String) : Branch := ⟨name, c.history, []⟩

def Branch.post (b : Branch) (a : Act) : Branch := { b with acts := b.acts ++ [a] }

/-- The branch run offline, at its own configuration. -/
def Branch.run (c : Config) (b : Branch) : Run := runActs (fun _ => b.name) c (b.acts.map (.left, ·))

def writesOf (acts : List Act) : List BTurn :=
  acts.filterMap fun a => match a with
    | .write t => some t
    | _ => none

def nonWrites (acts : List Act) : List Act := acts.filter (!·.isWrite)

def relawsOf (acts : List Act) : List (String × PageLaws) :=
  acts.filterMap fun a => match a with
    | .relaw _ _ p pl => some (p, pl)
    | _ => none

/-- The pages both sides give different laws. -/
def lawClashes (l r : List Act) : List String :=
  ((relawsOf l).filter fun x => (relawsOf r).any fun y => x.1 == y.1 && x.2 != y.2).map (·.1) |>.eraseDups

def heldRelaw (pages : List String) : Act → Bool
  | .relaw _ _ p _ => pages.contains p
  | _ => false

def sideName (ln rn : String) : Side → String
  | .left => ln
  | .right => rn
  | .both => ln ++ "+" ++ rn

/-- **The tip**: the base with both sides' relaws (those that do not clash), grants and revocations
applied, the left's first. Every write of the merge is judged here. -/
def tipConfig (base : Config) (ln rn : String) (lnw rnw : List Act) : Run :=
  let held := lawClashes lnw rnw
  runActs (sideName ln rn) base
    ((lnw.filter (!heldRelaw held ·)).map (.left, ·) ++ (rnw.filter (!heldRelaw held ·)).map (.right, ·))

/-- The cells where two writes clash: both write them, so one would be a lost update. A cell one
writes and the other only reads is not a clash: the tip is a serial order, so the reader's pins are
checked when it lands and a pin the other side moved refuses it by name (`Refusal.stale`), and every
law over links that reads the cell is judged at the tip whichever lands first. -/
def clash (a b : BTurn) : List String := (a.writes.filter fun c => b.writes.contains c).eraseDups

/-! ### Their laws agree: I-confluent merges

A page may declare how a field merges (`MergeKind`). Two writes of the page from the same base merge
by those declarations when every other field agrees, and the merged state satisfies every own law
of the page whenever both sides did: each law is I-confluent for the merge, decided by `confluentLaw`
(a law that does not read the field; `monotone`; a lower bound `not (new.f <= v)`; an upper bound
`new.f <= v` under `max` only; conjunctions of those), with `iconfluent_merge_lawful` its soundness.
A disjunction reading the field, or an upper bound under `add` or `union`, is not I-confluent: the
two writes stay a conflict. Identical writes merge with no declaration at all, and land once. -/

/-- Is the law `e` I-confluent for merging the field `f` by `k`? -/
def confluentLaw (k : MergeKind) (f : String) : LawExpr → Bool
  | .and a b => confluentLaw k f a && confluentLaw k f b
  | .monotone _ => true
  | .not (.leC (.field _) _) => true
  | .leC (.field g) _ => g != f || k == .max
  | e => !(e.fields.contains f)

/-- How a store merges the texts of a cell both sides wrote, when it keeps texts at all: `none`, the
store keeps no text for the cell (its state merges by its page's declared merges); `some none`, the
two texts do not merge (a conflict); `some (some m)`, the two texts merge into one whose state is
`m` (for the markdown vault, `Obend.Vault.mergePage`'s pushout of the two versions, rendered as
`Obend.Vault.pageState`). A text merge is judged at the tip like any other write. -/
structure TextMerge where
  state : String → Option (Option Data) := fun _ => none
  /-- the text the merged write of a page lands (`BTurn.text`), where the store keeps texts -/
  write : String → Option PageWrite := fun _ => none

/-- A store of states only: no texts. -/
def noText : TextMerge := {}

/-- The laws over links judged at `c`: those of every other page that links to it, as
`backlinkRefusal` judges them at `c` on the identity occasion. -/
def linkedLaws (book : LawBook) (c : String) : List (String × LawExpr) :=
  book.flatMap fun e => if e.1 != c && e.2.links.contains c then e.2.overLinks else []

/-- Merge one declared field into `m` (which starts as the left's state) from the right's `r` over
the base `pre`: equal readings stay; differing readings join by the kind, if it fits. -/
def mergeStep (pre r m : Data) (fk : String × MergeKind) : Option Data :=
  match Obend.Spec.Law.fieldOf fk.1 m, Obend.Spec.Law.fieldOf fk.1 r with
  | some x, some y =>
    if x = y then some m
    else
      let b := ((Obend.Spec.Law.fieldOf fk.1 pre).getD 0).toNat
      if fk.2.fits b x.toNat y.toNat then some (setNat m fk.1 (fk.2.join b x.toNat y.toNat)) else none
  | none, none => some m
  | _, _ => none

/-- The merged state of the left's `l` and the right's `r` over `pre`, field by declared field. -/
def mergeState (pre r : Data) : List (String × MergeKind) → Data → Option Data
  | [], m => some m
  | fk :: rest, m => (mergeStep pre r m fk).bind (mergeState pre r rest)

/-- The merged post-state of one cell both sides wrote from the same pre-state: the merge of their
texts, where the store keeps texts; otherwise the same write, or the merge its page declares, when
every law that judges the cell is I-confluent for it (the page's own laws, and the laws over links
of every page linking to it, `linkedLaws`) and the two directions agree (so every undeclared field
is the same on both sides). -/
def mergeCell (text : TextMerge) (book : LawBook) (da db : CellDelta) : Option Data :=
  if !Obend.Law.termEq da.preState.term db.preState.term then none
  else match text.state da.cell with
  | some r => r
  | none =>
  if Obend.Law.termEq da.postState.term db.postState.term then some da.postState
  else match book.lookup da.cell with
    | none => none
    | some pl =>
      if pl.merges.isEmpty then none
      else if !((pl.own ++ linkedLaws book da.cell).all fun e =>
          pl.merges.all fun fk => confluentLaw fk.2 fk.1 e.2) then none
      else match mergeState da.preState db.postState pl.merges da.postState,
                 mergeState da.preState da.postState pl.merges db.postState with
        | some m, some m' => if Obend.Law.termEq m.term m'.term then some m else none
        | _, _ => none

/-- The merged legs of two writes: every cell of the left's, with the right's write of it. -/
def mergeLegs (text : TextMerge) (book : LawBook) (bs : List CellDelta) :
    List CellDelta → Option (List WitnessLegSpec)
  | [] => some []
  | da :: rest =>
    match bs.find? (·.cell == da.cell) with
    | none => none
    | some db =>
      match mergeCell text book da db with
      | none => none
      | some m => (mergeLegs text book bs rest).map ((da.cell, da.preState, m) :: ·)

/-- **Two writes that merge**: they write the same cells, read nothing the other writes beyond them,
each clashes with no other write of the other side, and every cell merges. The merged write relies
on both sides' sturdyrefs; its actor is the two actors. -/
def mergeFor (text : TextMerge) (book : LawBook) (lw rw : List BTurn) (a b : BTurn) : Option BTurn :=
  if !(b.writes.all a.writes.contains && a.writes.all b.writes.contains) then none
  -- two edits of a page's law lines that differ do not merge: a conflict, the base laws standing
  else if a.isLaw && b.isLaw && a.lawKey != b.lawKey then none
  else if (rw.filter fun b' => !(clash a b').isEmpty).length != 1 then none
  else if (lw.filter fun a' => !(clash a' b).isEmpty).length != 1 then none
  else
    match mergeLegs text book b.turn.writeCells a.turn.writeCells with
    | none => none
    | some legs =>
      (VaultTurn.ofWitnessLegs ByteArray.empty (a.turn.readPins ++ b.turn.readPins) legs a.turn.occasion []).map
        fun vt => { label := a.label ++ " + " ++ b.label,
                    actor := if a.actor == b.actor then a.actor else a.actor ++ "+" ++ b.actor,
                    turn := vt, relies := a.relies ++ b.relies,
                    text := match a.writes with
                      | [c] => text.write c
                      | _ => none,
                    lawKey := if a.isLaw then a.lawKey else b.lawKey }

/-- The writes of the left that clash with no write of the right. -/
def freeLeft (lw rw : List BTurn) : List BTurn :=
  lw.filter fun a => rw.all fun b => (clash a b).isEmpty

def freeRight (lw rw : List BTurn) : List BTurn :=
  rw.filter fun b => lw.all fun a => (clash a b).isEmpty

/-- The clashing pairs that do not merge: conflicts. -/
def writeConflicts (text : TextMerge) (book : LawBook) (ln rn : String) (lw rw : List BTurn) : List Conflict :=
  lw.flatMap fun a => rw.filterMap fun b =>
    let cs := clash a b
    if cs.isEmpty then none else if (mergeFor text book lw rw a b).isSome then none else some (.writes cs (ln, a) (rn, b))

/-- The clashing pairs that merge by their pages' laws: each pair and its merged write. -/
def mergedPairs (text : TextMerge) (book : LawBook) (lw rw : List BTurn) : List (BTurn × BTurn × BTurn) :=
  lw.flatMap fun a => rw.filterMap fun b =>
    if (clash a b).isEmpty then none else (mergeFor text book lw rw a b).map fun m => (a, b, m)

/-- A merged pair lands only when each of its two writes has its own authority at the tip. -/
def pairAuthority (auth : Authority) (book : LawBook) (p : BTurn × BTurn × BTurn) : Option Refusal :=
  match authRefusal auth book p.1, authRefusal auth book p.2.1 with
  | some r, _ => some r
  | none, some r => some r
  | none, none => none

/-- **Laws settle first**: the writes that change a page's law lines, of either side and merged, before
every other write, each part in its order. So the laws at the tip are known before any write that
does not change them is judged, in a vault as in a store whose laws are its book's. -/
def lawFirst (xs : List (Side × BTurn)) : List (Side × BTurn) :=
  xs.filter (·.2.isLaw) ++ xs.filter (!·.2.isLaw)

theorem mem_lawFirst {xs : List (Side × BTurn)} {x : Side × BTurn} : x ∈ lawFirst xs ↔ x ∈ xs := by
  unfold lawFirst
  rw [List.mem_append, List.mem_filter, List.mem_filter]
  cases x.2.isLaw <;> simp

/-- A merge: the tip configuration, what landed, what was refused and why, the conflicts. -/
structure Merged where
  tip : Config
  landed : List (Side × Act)
  refused : List (Side × String × Refusal)
  conflicts : List Conflict

/-- **Merge two branches of `base`**: settle their non-write acts into the tip, keep the clashing
writes as conflicts, replay the others at the tip. A branch that did not fork from `base`'s history
is not merged. The writes that change law lines are replayed first (`lawFirst`). -/
def merge (base : Config) (L R : Branch) (text : TextMerge := noText) : Except String Merged :=
  if L.base ≠ base.history then .error (L.name ++ " did not fork from this history")
  else if R.base ≠ base.history then .error (R.name ++ " did not fork from this history")
  else
    let t := tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)
    let book := t.config.book
    let lw := writesOf L.acts
    let rw := writesOf R.acts
    let cs := (lawClashes (nonWrites L.acts) (nonWrites R.acts)).map (fun p => Conflict.laws p L.name R.name) ++
      writeConflicts text book L.name R.name lw rw
    let mp := mergedPairs text book lw rw
    let pre : List (Side × String × Refusal) := mp.filterMap fun p =>
      (pairAuthority t.config.auth book p).map fun r => (.both, p.2.2.label, r)
    let w := runWrites (sideName L.name R.name) t.config (lawFirst
      ((freeLeft lw rw).map (.left, ·) ++ (freeRight lw rw).map (.right, ·) ++
        ((mp.filter fun p => (pairAuthority t.config.auth book p).isNone).map fun p => (.both, p.2.2))))
    .ok ⟨{ w.config with conflicts := w.config.conflicts ++ cs }, t.landed ++ w.landed,
      t.refused ++ pre ++ w.refused, cs⟩

/-- **Resolve** the `k`th open conflict (from 0) by landing one candidate at the configuration as it
is; the other candidate is dropped, and the receipt says so. -/
def resolve (c : Config) (k : Nat) (pick : Side) : Except String Config :=
  match c.conflicts[k]? with
  | some (.writes _ (ln, l) (rn, r)) =>
    let (o, t, dropped) := match pick with
      | .right => (rn, r, ln ++ "'s " ++ l.label)
      | _ => (ln, l, rn ++ "'s " ++ r.label)
    match admitWrite { c with conflicts := c.conflicts.eraseIdx k } o
        { t with label := t.label ++ " (resolving; dropped " ++ dropped ++ ")" } with
    | .ok c' => .ok c'
    | .error e => .error e.text
  | some (.laws p _ _) => .error ("the conflict at the laws of " ++ p ++ " is resolved by its owner's relaw")
  | none => .error ("no open conflict " ++ toString k)

/-! ## What a write's admission says -/

theorem preRefusal_none {c : Config} {t : BTurn} (h : preRefusal c t = none) :
    authRefusal c.auth c.book t = none ∧ pinRefusal c.store t.turn = none := by
  unfold preRefusal at h
  cases ha : authRefusal c.auth c.book t <;> cases hp : pinRefusal c.store t.turn <;>
    rw [ha, hp] at h <;> first | exact ⟨rfl, rfl⟩ | cases h

/-- **The authority reason is never hidden.** A write whose authority check refuses is refused with
that reason, alone or followed by the stale pin it also has. -/
theorem admitWrite_names_authority {c : Config} {o : String} {t : BTurn} {r : Refusal}
    (h : authRefusal c.auth c.book t = some r) :
    admitWrite c o t = .error r ∨ ∃ p, admitWrite c o t = .error (.also r p) := by
  unfold admitWrite preRefusal
  rw [h]
  cases hp : pinRefusal c.store t.turn with
  | none => exact .inl rfl
  | some p => exact .inr ⟨p, rfl⟩

theorem admitWrite_ok {c c' : Config} {o : String} {t : BTurn} (h : admitWrite c o t = .ok c') :
    pinRefusal c.store t.turn = none ∧ authRefusal c.auth c.book t = none ∧
    ∃ v, judgeWrite c t = .ok v ∧
    c' = { c with store := applyTurn c.store t.turn, vault := v,
                  history := c.history ++ [receiptOf c o t.label t.writes] } := by
  unfold admitWrite at h
  split at h
  · cases h
  · rename_i hpre
    obtain ⟨ha, hp⟩ := preRefusal_none hpre
    split at h
    · cases h
    · rename_i v hc
      cases h
      exact ⟨hp, ha, v, hc, rfl⟩

/-- **Landed at the tip is landed in the store.** In a vault, a write of one page that carries its
text and whose authority and pins hold is admitted exactly when the store's own write of that text
lands (`Store.writeText`) at the state its turn says, and the configuration it reaches keeps exactly
the store that write reaches. One judgment, one event. -/
theorem tip_lands_iff_store_lands {c : Config} {o : String} {t : BTurn} {s s' : Store} {w : PageWrite}
    {d : CellDelta} (hv : c.vault = some s) (ht : t.text = some w) (hw : t.turn.writeCells = [d])
    (hpre : preRefusal c t = none) :
    (∃ c', admitWrite c o t = .ok c' ∧ c'.vault = some s') ↔
      s.writeText d.cell w = .ok s' ∧ (vaultStates s' d.cell).map Data.term = some d.postState.term := by
  unfold admitWrite judgeWrite
  rw [hpre]
  simp only
  rw [hv, ht, hw]
  simp only
  cases hs : s.writeText d.cell w with
  | error m => simp
  | ok s'' =>
    simp only [Except.ok.injEq]
    cases hx : vaultStates s'' d.cell with
    | none =>
      simp only
      constructor
      · rintro ⟨_, h, _⟩; cases h
      · rintro ⟨rfl, h⟩; simp [hx] at h
    | some x =>
      simp only
      by_cases hq : Obend.Law.termEq x.term d.postState.term = true
      · simp only [hq, ↓reduceIte]
        have := Obend.Law.termEq_sound_local hq
        constructor
        · rintro ⟨_, h, hv'⟩
          cases h
          simp only [Option.some.injEq] at hv'
          subst hv'
          exact ⟨rfl, by simp [hx, this]⟩
        · rintro ⟨rfl, _⟩
          exact ⟨_, rfl, rfl⟩
      · simp only [hq, Bool.false_eq_true, ↓reduceIte]
        constructor
        · rintro ⟨_, h, _⟩; cases h
        · rintro ⟨rfl, h⟩
          simp only [hx, Option.map_some, Option.some.injEq] at h
          exact absurd (h ▸ Obend.Law.termEq_refl_local _) hq

/-- The store's refusal of a vault write is the tip's, in the store's words. -/
theorem tip_refuses_iff_store_refuses {c : Config} {o : String} {t : BTurn} {s : Store} {w : PageWrite}
    {d : CellDelta} {m : String} (hv : c.vault = some s) (ht : t.text = some w) (hw : t.turn.writeCells = [d])
    (hpre : preRefusal c t = none) (hm : s.writeText d.cell w = .error m) :
    admitWrite c o t = .error (.store d.cell (dropPage d.cell m)) := by
  unfold admitWrite judgeWrite
  rw [hpre]
  simp only
  rw [hv, ht, hw]
  simp only [hm]

/-- **Multi-page turn landed at the tip is landed in the store.** In a vault, a multi-page (or
actor-attributed) branch turn (`t.text = none`, `t.texts` matching `t.turn.writeCells`) whose
authority and external pins hold is admitted at the tip if and only if `Store.writeTexts` lands
at the states its turn declares, reaching the exact store `Store.writeTexts` produces. -/
theorem tip_lands_texts_iff_store_lands {c : Config} {o : String} {t : BTurn} {s s' : Store}
    {d₀ : CellDelta} {ds : List CellDelta}
    (hv : c.vault = some s) (ht : t.text = none) (hw : t.turn.writeCells = d₀ :: ds)
    (hm : t.texts.map (·.1) = (d₀ :: ds).map (·.cell))
    (hpre : preRefusal c t = none) :
    (∃ c', admitWrite c o t = .ok c' ∧ c'.vault = some s') ↔
      s.writeTexts t.texts t.actorRef = .ok s' ∧
      ∀ d ∈ d₀ :: ds, (vaultStates s' d.cell).map Data.term = some d.postState.term := by
  have hm_beq : (t.texts.map (·.1) == (d₀ :: ds).map (·.cell)) = true := beq_iff_eq.2 hm
  unfold admitWrite judgeWrite
  rw [hpre]
  simp only
  rw [hv, ht, hw]
  simp only [hm_beq, ↓reduceIte]
  cases hs : s.writeTexts t.texts t.actorRef with
  | error m => simp
  | ok s'' =>
    simp only
    by_cases hall : ((d₀ :: ds).all fun d => match vaultStates s'' d.cell with
        | some x => Obend.Law.termEq x.term d.postState.term
        | none => false) = true
    · simp only [hall, ↓reduceIte]
      constructor
      · rintro ⟨_, h, hv'⟩
        cases h
        simp only [Option.some.injEq] at hv'
        subst hv'
        refine ⟨rfl, fun d hd => ?_⟩
        have h1 := List.all_eq_true.1 hall d hd
        cases hx : vaultStates s'' d.cell with
        | none => rw [hx] at h1; cases h1
        | some x =>
          rw [hx] at h1
          simp [Obend.Law.termEq_sound_local h1]
      · rintro ⟨hok, _⟩
        cases hok
        exact ⟨_, rfl, rfl⟩
    · simp only [hall, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨_, h, _⟩; cases h
      · rintro ⟨hok, hd⟩
        cases hok
        exfalso
        apply hall
        rw [List.all_eq_true]
        intro d hmem
        have hdt := hd d hmem
        cases hx : vaultStates s' d.cell with
        | none => simp [hx] at hdt
        | some x =>
          simp only [hx, Option.map_some, Option.some.injEq] at hdt
          exact hdt ▸ Obend.Law.termEq_refl_local _

/-- What the authority check passing says: every sturdyref relied on is live, and every page written
is the actor's or granted by a sturdyref relied on. -/
theorem authRefusal_none {a : Authority} {book : LawBook} {t : BTurn} (h : authRefusal a book t = none) :
    (∀ u ∈ t.relies, a.live u = true) ∧
    ∀ d ∈ t.turn.writeCells, ∃ pl, book.lookup d.cell = some pl ∧
      (pl.owner = t.actor ∨ ∃ u ∈ t.relies, ∃ sr, a.find? u = some sr ∧ grantsWrite sr d.cell = true) := by
  unfold authRefusal at h
  split at h
  · split at h <;> cases h
  · rename_i hf
    refine ⟨fun u hu => ?_, fun d hd => ?_⟩
    · have := List.find?_eq_none.1 hf u hu
      simpa using this
    · have hd' := List.findSome?_eq_none_iff.1 h d hd
      split at hd'
      · cases hd'
      · rename_i pl hl
        refine ⟨pl, hl, ?_⟩
        split at hd'
        · rename_i ho; exact .inl (by simpa using ho)
        · rename_i _ hany
          split at hd'
          · rename_i hany'
            obtain ⟨u, hu, hg⟩ := List.any_eq_true.1 hany'
            refine .inr ⟨u, hu, ?_⟩
            cases hfu : a.find? u with
            | none => rw [hfu] at hg; cases hg
            | some sr => rw [hfu] at hg; exact ⟨sr, rfl, hg⟩
          · cases hd'

/-- Laws over links that passed at every page of `cells`: each page has a state, and the judge
admitted there. -/
theorem judgeLinksIn_none {s : VaultStore} {pkg : String} {lin : List (String × LawExpr)} {rq : Data} :
    ∀ {cells : List String}, judgeLinksIn s pkg lin rq cells = none →
      ∀ c ∈ cells, ∃ x, s c = some x ∧
        judge (rekey lin x).1 pkg lin (rekey lin x).2 (rekey lin x).2 rq = .admitted
  | [], _, c, hc => by cases hc
  | c :: rest, h, c', hc' => by
    simp only [judgeLinksIn] at h
    split at h
    · cases h
    · rename_i x hx
      split at h
      · rename_i hj
        rcases List.mem_cons.1 hc' with rfl | hr
        · exact ⟨x, hx, hj⟩
        · exact judgeLinksIn_none h c' hr
      · cases h
      · cases h

/-- **Consent, by the laws' meaning.** Every law of every page in the cone of the write of `d`
holds: the written page's own laws of its write (old to new), its laws over links at every page it
links to, and the laws over links of every page linking to it, at it as written (`s'`). -/
def Consents (book : LawBook) (s' : VaultStore) (facts : Facts) (d : CellDelta) : Prop :=
  ∃ pl, book.lookup d.cell = some pl ∧
    (∀ p ∈ pl.own, p.2.denote facts (some (rekey pl.own d.preState).2) (rekey pl.own d.postState).2 = true) ∧
    (∀ q ∈ pl.links, ∀ p ∈ pl.overLinks, ∃ x, s' q = some x ∧
      p.2.denote facts (some (rekey pl.overLinks x).2) (rekey pl.overLinks x).2 = true) ∧
    (∀ q ql, (q, ql) ∈ book → q ≠ d.cell → d.cell ∈ ql.links → ∀ p ∈ ql.overLinks, ∃ x, s' d.cell = some x ∧
      p.2.denote facts (some (rekey ql.overLinks x).2) (rekey ql.overLinks x).2 = true) ∧
    (∀ q ql, (q, ql) ∈ book → q ≠ d.cell → d.cell ∈ ql.links → ∀ p ∈ pl.overLinkedBy, ∃ y, s' q = some y ∧
      let x := withListed y (pl.links.contains q)
      p.2.denote facts (some (rekey pl.overLinkedBy x).2) (rekey pl.overLinkedBy x).2 = true) ∧
    (∀ q ∈ pl.links, ∀ ql, book.lookup q = some ql → q ≠ d.cell → ∀ p ∈ ql.overLinkedBy, ∃ y, s' d.cell = some y ∧
      let x := withListed y (ql.links.contains d.cell)
      p.2.denote facts (some (rekey ql.overLinkedBy x).2) (rekey ql.overLinkedBy x).2 = true)

theorem linksRefusal_none {s : VaultStore} {page : String} {pl : PageLaws} {actor : String} {h : Nat}
    {at_ : List String} (hr : linksRefusal s page pl (requestAt actor h) at_ = none) :
    ∀ q ∈ at_, ∀ p ∈ pl.overLinks, ∃ x, s q = some x ∧
      p.2.denote (factsAt h) (some (rekey pl.overLinks x).2) (rekey pl.overLinks x).2 = true := by
  intro q hq p hp
  unfold linksRefusal at hr
  split at hr
  · rename_i he
    rw [List.isEmpty_iff] at he
    rw [he] at hp; cases hp
  · cases hj : judgeLinksIn s page pl.overLinks (requestAt actor h) at_ with
    | some r => rw [hj] at hr; cases hr
    | none =>
      obtain ⟨x, hx, ha⟩ := judgeLinksIn_none hj q hq
      exact ⟨x, hx, judge_admits (k := .write) ha p hp⟩

/-- Laws over backlinks that passed, read through `listedStore`: at each page, its state with
`listed`, and every law holds there. -/
theorem byLinks_none {s : VaultStore} {L : List String} {pkg : String} {lin : List (String × LawExpr)}
    {actor : String} {h : Nat} {cells : List String}
    (hj : judgeLinksIn (listedStore s L) pkg lin (requestAt actor h) cells = none) :
    ∀ c ∈ cells, ∀ p ∈ lin, ∃ y, s c = some y ∧
      let x := withListed y (L.contains c)
      p.2.denote (factsAt h) (some (rekey lin x).2) (rekey lin x).2 = true := by
  intro c hc p hp
  obtain ⟨x, hx, ha⟩ := judgeLinksIn_none hj c hc
  simp only [listedStore] at hx
  cases hy : s c with
  | none => rw [hy] at hx; cases hx
  | some y =>
    rw [hy] at hx
    simp only [Option.map_some, Option.some.injEq] at hx
    subst hx
    exact ⟨y, rfl, judge_admits (k := .write) ha p hp⟩

/-- **The laws over backlinks of a write's cone hold where `byRefusal` found nothing**: the written
page's at every page of the book linking to it, and those of every page it links to, at it. -/
theorem byRefusal_none {book : LawBook} {s : VaultStore} {actor : String} {h : Nat} {c : String}
    {pl : PageLaws} (hr : byRefusal book s (requestAt actor h) c pl = none) :
    (∀ q ql, (q, ql) ∈ book → q ≠ c → c ∈ ql.links → ∀ p ∈ pl.overLinkedBy, ∃ y, s q = some y ∧
      let x := withListed y (pl.links.contains q)
      p.2.denote (factsAt h) (some (rekey pl.overLinkedBy x).2) (rekey pl.overLinkedBy x).2 = true) ∧
    (∀ q ∈ pl.links, ∀ ql, book.lookup q = some ql → q ≠ c → ∀ p ∈ ql.overLinkedBy, ∃ y, s c = some y ∧
      let x := withListed y (ql.links.contains c)
      p.2.denote (factsAt h) (some (rekey ql.overLinkedBy x).2) (rekey ql.overLinkedBy x).2 = true) := by
  unfold byRefusal at hr
  split at hr
  · cases hr
  · rename_i hm
    refine ⟨?_, ?_⟩
    · intro q ql hq hne hlink p hp
      split at hm
      · rename_i he
        rw [List.isEmpty_iff] at he
        rw [he] at hp; cases hp
      · cases hj : judgeLinksIn (listedStore s pl.links) c pl.overLinkedBy (requestAt actor h) (linkersOf book c) with
        | some r => rw [hj] at hm; cases hm
        | none =>
          have hmem : q ∈ linkersOf book c := by
            simp only [linkersOf, List.mem_map, List.mem_filter]
            exact ⟨(q, ql), ⟨hq, by simp [hne, hlink]⟩, rfl⟩
          exact byLinks_none hj q hmem p hp
    · intro q hq ql hql hne p hp
      have hb := List.findSome?_eq_none_iff.1 hr q hq
      simp only [hql] at hb
      have hne' : ql.overLinkedBy.isEmpty = false := by
        cases hx : ql.overLinkedBy with
        | nil => rw [hx] at hp; cases hp
        | cons _ _ => rfl
      have hcond : (q != c && !ql.overLinkedBy.isEmpty) = true := by simp [hne, hne']
      rw [if_pos hcond] at hb
      cases hj : judgeLinksIn (listedStore s ql.links) q ql.overLinkedBy (requestAt actor h) [c] with
      | some r => rw [hj] at hb; cases hb
      | none => exact byLinks_none hj c (List.mem_singleton_self _) p hp

theorem coneRefusal_none {book : LawBook} {s' : VaultStore} {actor : String} {h : Nat} {d : CellDelta}
    (hr : coneRefusal book s' (requestAt actor h) d = none) : Consents book s' (factsAt h) d := by
  unfold coneRefusal at hr
  split at hr
  · cases hr
  · rename_i pl hl
    refine ⟨pl, hl, ?_⟩
    cases hj : judgeOwn d.cell pl.own d.preState d.postState (requestAt actor h) with
    | refused law why => rw [hj] at hr; cases hr
    | undecided why => rw [hj] at hr; cases hr
    | admitted =>
      rw [hj] at hr
      have hown : ∀ p ∈ pl.own, p.2.denote (factsAt h) (some (rekey pl.own d.preState).2)
          (rekey pl.own d.postState).2 = true := by
        intro p hp
        unfold judgeOwn at hj
        split at hj
        · rename_i he
          rw [List.isEmpty_iff] at he
          rw [he] at hp; cases hp
        · exact judge_admits (k := .write) hj p hp
      cases hl' : linksRefusal s' d.cell pl (requestAt actor h) pl.links with
      | some r => rw [hl'] at hr; cases hr
      | none =>
        rw [hl'] at hr
        cases hbk : backlinkRefusal book s' (requestAt actor h) d.cell with
        | some r => rw [hbk] at hr; cases hr
        | none =>
          rw [hbk] at hr
          obtain ⟨hby1, hby2⟩ := byRefusal_none hr
          refine ⟨hown, linksRefusal_none hl', ?_, hby1, hby2⟩
          intro q ql hq hne hlink p hp
          have hb := List.findSome?_eq_none_iff.1 hbk (q, ql) hq
          simp only at hb
          have hcond : (q != d.cell && ql.links.contains d.cell) = true := by
            simp [hne, hlink]
          rw [ite_eq_left hcond] at hb
          exact linksRefusal_none hb d.cell (List.mem_singleton_self _) p hp

/-- **A store's consent to a page's text**: its last version prepared from the page's version as it
is, the versions before it entering the history as written (`Store.writeSince`), and admitted by the
store's judgment (`judgePrepared`). -/
def TextConsents (s : Store) (page : String) (poster : Option String)
    (vs : List (Graph × List (AtomId × String))) : Prop :=
  match vs.getLast? with
  | none => True
  | some (G, a) => ∃ p pr, s.page? page = some p ∧
      prepareFrom (p.current.map fun G0 => (G0, p.history.length - 1)) s.entries
        { p with history := p.history ++ vs.dropLast.map (·.1), authors := p.authors ++ vs.dropLast.flatMap (·.2) }
        G a .owner s.turn (poster.getD "owner") s.environment = .ok pr ∧
      judgePrepared s.entries s.entries pr [] = .ok ()

theorem writeText_consents {s s' : Store} {page : String} {w : PageWrite}
    (h : s.writeText page w = .ok s') : TextConsents s page w.poster w.versions := by
  unfold Store.writeText at h
  unfold TextConsents
  cases hl : w.versions.getLast? with
  | none => trivial
  | some x =>
    obtain ⟨G, a⟩ := x
    rw [hl] at h
    simp only at h ⊢
    unfold Store.writeSince at h
    cases hp : s.page? page with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      simp only at h
      split at h
      · cases h
      · rename_i pr hpr
        split at h
        · cases h
        · rename_i hj
          exact ⟨p, pr, rfl, hpr, hj⟩

/-- **A store's consent to a multi-page (or actor-attributed) branch turn**: every page write in
`ws` prepared against `s` under `who`, and judged together at the turn's tip (`judgeAll`). -/
def TextsConsent (s : Store) (ws : List (String × PageWrite)) (who : Actor) : Prop :=
  ws ≠ [] ∧ ∃ prs, prepareTexts s who ws = .ok prs ∧
    let res := if prs.length ≤ 1 then s.entries else turnEntries s.entries (prs.map fun pr => (pr.p, pr.G', []))
    let over := if prs.length ≤ 1 then [] else tipOf prs
    judgeAll s.entries res over prs = .ok ()

theorem writeTexts_consents {s s' : Store} {ws : List (String × PageWrite)} {who : Actor}
    (hne : ws ≠ []) (h : s.writeTexts ws who = .ok s') : TextsConsent s ws who := by
  unfold Store.writeTexts at h
  have hemp : ws.isEmpty = false := List.isEmpty_eq_false_iff.2 hne
  rw [hemp] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  · cases hp : prepareTexts s who ws with
    | error e => rw [hp] at h; cases h
    | ok prs =>
      rw [hp] at h
      dsimp only at h
      cases hj : judgeAll s.entries
          (if prs.length ≤ 1 then s.entries else turnEntries s.entries (prs.map fun pr => (pr.p, pr.G', [])))
          (if prs.length ≤ 1 then [] else tipOf prs) prs with
      | error e => rw [hj] at h; cases h
      | ok u => exact ⟨hne, prs, hp, hj⟩

/-- **What consent to a write is**, at the configuration it is judged at: in a vault, the store's
consent to its text (`TextConsents` or multi-page `TextsConsent`); otherwise the consent of every
page of its cone (`Consents`). -/
def WriteConsents (c c' : Config) (t : BTurn) : Prop :=
  match c.vault with
  | some s =>
    (∃ w d, t.text = some w ∧ t.turn.writeCells = [d] ∧ TextConsents s d.cell w.poster w.versions) ∨
    (t.text = none ∧ t.texts.map (·.1) = t.turn.writeFootprint ∧ TextsConsent s t.texts t.actorRef)
  | none => ∀ d ∈ t.turn.writeCells, Consents c.book c'.store (factsAt c.history.length) d

theorem write_consents {s s' : Store} {p : Page} {G : Graph} {a : List (AtomId × String)} {po : Option String}
    (h : s.write p G a .owner po = .ok s') :
    ∃ pr, prepareWrite s.entries p G a .owner s.turn (po.getD "owner") s.environment = .ok pr ∧
      judgePrepared s.entries s.entries pr [] = .ok () ∧ s' = s.setPage (p.withChange pr.change) := by
  unfold Store.write commit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hp : prepareWrite s.entries p G a .owner s.turn (po.getD Actor.owner.name) s.environment with
  | error e => rw [hp] at h; cases h
  | ok pr =>
    rw [hp] at h
    simp only at h
    cases hj : judgePrepared s.entries s.entries pr [] with
    | error e => rw [hj] at h; cases h
    | ok u =>
      rw [hj] at h
      cases h
      exact ⟨pr, hp, hj, rfl⟩

/-- **An admitted write was consented to**, at the configuration it was admitted at: in a vault by
the store's judgment of its text, otherwise by every page of its cone. -/
theorem admitWrite_consents {c c' : Config} {o : String} {t : BTurn} (h : admitWrite c o t = .ok c') :
    WriteConsents c c' t := by
  obtain ⟨_, _, v, hj, rfl⟩ := admitWrite_ok h
  unfold judgeWrite at hj
  unfold WriteConsents
  split at hj
  · rename_i s w d hv ht hw
    rw [hv]
    cases hs : s.writeText d.cell w with
    | ok s' => exact .inl ⟨w, d, ht, hw, writeText_consents hs⟩
    | error m => rw [hs] at hj; cases hj
  · rename_i s d₀ ds hv ht hw
    rw [hv]
    split at hj
    · rename_i hm
      have hmap : t.texts.map (·.1) = (d₀ :: ds).map (·.cell) := beq_iff_eq.1 hm
      have hne : t.texts ≠ [] := by
        intro hnil
        rw [hnil] at hmap
        cases hmap
      cases hs : s.writeTexts t.texts t.actorRef with
      | error m => rw [hs] at hj; cases hj
      | ok s' =>
        refine .inr ⟨ht, ?_, writeTexts_consents hne hs⟩
        simpa [VaultTurn.writeFootprint, hw] using hmap
    · cases hj
  · cases hj
  · rename_i hv
    rw [hv]
    split at hj
    · cases hj
    · rename_i hc
      exact fun d hd => coneRefusal_none (List.findSome?_eq_none_iff.1 hc d hd)

theorem admitWrite_keeps {c c' : Config} {o : String} {t : BTurn} (h : admitWrite c o t = .ok c') :
    c'.book = c.book ∧ c'.auth = c.auth ∧ c'.conflicts = c.conflicts := by
  obtain ⟨_, _, _, _, rfl⟩ := admitWrite_ok h
  exact ⟨rfl, rfl, rfl⟩

/-- Every write a run of writes landed was admitted at a configuration with the run's final law book
and authority. -/
theorem runWrites_landed {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × BTurn)},
      (runWrites name c xs).config.book = c.book ∧ (runWrites name c xs).config.auth = c.auth ∧
      (runWrites name c xs).config.conflicts = c.conflicts ∧
      ∀ x ∈ (runWrites name c xs).landed, ∃ sd t, x = (sd, .write t) ∧ (sd, t) ∈ xs ∧
        ∃ c₀ c₁, c₀.book = c.book ∧ c₀.auth = c.auth ∧ admitWrite c₀ (name sd) t = .ok c₁
  | c, [] => ⟨rfl, rfl, rfl, fun _ h => by cases h⟩
  | c, (sd, t) :: rest => by
    simp only [runWrites]
    split
    · rename_i c' hc
      obtain ⟨hb, ha, hk⟩ := admitWrite_keeps hc
      obtain ⟨ib, ia, ik, il⟩ := runWrites_landed (name := name) (c := c') (xs := rest)
      refine ⟨ib.trans hb, ia.trans ha, ik.trans hk, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨sd, t, rfl, List.mem_cons_self .., c, c', rfl, rfl, hc⟩
      · obtain ⟨sd', t', rfl, hm, c₀, c₁, h0b, h0a, h0⟩ := il x hx
        exact ⟨sd', t', rfl, List.mem_cons_of_mem _ hm, c₀, c₁, h0b.trans hb, h0a.trans ha, h0⟩
    · obtain ⟨ib, ia, ik, il⟩ := runWrites_landed (name := name) (c := c) (xs := rest)
      refine ⟨ib, ia, ik, fun x hx => ?_⟩
      obtain ⟨sd', t', rfl, hm, rest'⟩ := il x hx
      exact ⟨sd', t', rfl, List.mem_cons_of_mem _ hm, rest'⟩

theorem runWrites_book {name : Side → String} {c : Config} {xs : List (Side × BTurn)} :
    (runWrites name c xs).config.book = c.book := runWrites_landed.1

theorem runWrites_auth {name : Side → String} {c : Config} {xs : List (Side × BTurn)} :
    (runWrites name c xs).config.auth = c.auth := runWrites_landed.2.1

theorem runWrites_landed_shape {name : Side → String} {c : Config} {xs : List (Side × BTurn)}
    {x : Side × Act} (h : x ∈ (runWrites name c xs).landed) : ∃ sd t, x = (sd, .write t) ∧ (sd, t) ∈ xs := by
  obtain ⟨sd, t, he, hm, _⟩ := runWrites_landed.2.2.2 x h
  exact ⟨sd, t, he, hm⟩

theorem runWrites_mem_landed {name : Side → String} {c : Config} {xs : List (Side × BTurn)}
    {sd : Side} {t : BTurn} (h : (sd, .write t) ∈ (runWrites name c xs).landed) :
    ∃ c₀ c₁, c₀.book = c.book ∧ c₀.auth = c.auth ∧ admitWrite c₀ (name sd) t = .ok c₁ := by
  obtain ⟨sd', t', he, _, rest⟩ := runWrites_landed.2.2.2 _ h
  cases he
  exact rest

theorem runActs_landed_sub {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × Act)}, ∀ x ∈ (runActs name c xs).landed, x ∈ xs
  | _, [], _, h => by cases h
  | c, (sd, a) :: rest, x, hx => by
    simp only [runActs] at hx
    split at hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (runActs_landed_sub x hx)
    · exact List.mem_cons_of_mem _ (runActs_landed_sub x hx)

/-! ## Revocation is the one non-monotone act -/

theorem find?_append_some {a : Authority} {sr : Sturdyref Data} {u : String}
    (h : (a.find? u).isSome = true) : ({ a with refs := a.refs ++ [sr] }.find? u).isSome = true := by
  unfold Authority.find? at h ⊢
  rw [List.find?_append]
  cases hf : a.refs.find? (·.uri == u) with
  | none => rw [hf] at h; cases h
  | some x => rfl

/-- **Revocation is the one non-monotone act.** No act unrevokes a sturdyref; every act but a
revocation keeps every live sturdyref live; a revocation kills the one it names. -/
theorem revocation_only_nonmonotone {c c' : Config} {o : String} {a : Act} (h : admitAct c o a = .ok c') :
    (∀ u, c.auth.isRevoked u = true → c'.auth.isRevoked u = true) ∧
    (a.isRevoke = false → ∀ u, c.auth.live u = true → c'.auth.live u = true) ∧
    (∀ l w u, a = .revoke l w u → c'.auth.live u = false) := by
  cases a with
  | write t =>
    obtain ⟨_, ha, _⟩ := admitWrite_keeps (show admitWrite c o t = .ok c' from h)
    rw [ha]
    exact ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ he => Act.noConfusion he⟩
  | relaw l w p pl =>
    simp only [admitAct] at h
    have : c'.auth = c.auth := by
      split at h
      · split at h
        · cases h; rfl
        · cases h
      · split at h
        · cases h; rfl
        · cases h
    rw [this]
    exact ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ he => Act.noConfusion he⟩
  | revoke l w u =>
    simp only [admitAct] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          refine ⟨fun v hv => ?_, fun he => by simp [Act.isRevoke] at he, fun l' w' u' he => ?_⟩
          · simp only [Authority.isRevoked, List.any_append] at hv ⊢
            rw [hv]; rfl
          · cases he
            simp [Authority.live, Authority.isRevoked]
        · cases h
  | grant l w sr =>
    simp only [admitAct] at h
    split at h
    · cases h
    · split at h
      · cases h
        refine ⟨fun v hv => hv, fun _ v hv => ?_, fun _ _ _ he => Act.noConfusion he⟩
        simp only [Authority.live, Bool.and_eq_true] at hv ⊢
        exact ⟨find?_append_some hv.1, hv.2⟩
      · cases h

theorem runActs_revoked_mono {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × Act)} {u : String}, c.auth.isRevoked u = true →
      (runActs name c xs).config.auth.isRevoked u = true
  | _, [], _, h => h
  | c, (sd, a) :: rest, u, h => by
    simp only [runActs]
    split
    · rename_i c' hc
      exact runActs_revoked_mono ((revocation_only_nonmonotone hc).1 u h)
    · exact runActs_revoked_mono h

theorem admitAct_revoke_revokes {c c' : Config} {o l w u : String} (h : admitAct c o (.revoke l w u) = .ok c') :
    c'.auth.isRevoked u = true := by
  simp only [admitAct] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; simp [Authority.isRevoked]
      · cases h

theorem runActs_revocation_visible {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × Act)} {sd : Side} {l w u : String},
      (sd, .revoke l w u) ∈ (runActs name c xs).landed → (runActs name c xs).config.auth.isRevoked u = true
  | _, [], _, _, _, _, h => by cases h
  | c, (sd', a) :: rest, sd, l, w, u, hx => by
    simp only [runActs] at hx ⊢
    split at hx
    · rename_i c' hc
      rcases List.mem_cons.1 hx with he | hx
      · cases he
        exact runActs_revoked_mono (admitAct_revoke_revokes hc)
      · exact runActs_revocation_visible hx
    · exact runActs_revocation_visible hx

/-! ## The merge -/

theorem merge_ok {base : Config} {L R : Branch} {text : TextMerge} {m : Merged} (h : merge base L R text = .ok m) :
    L.base = base.history ∧ R.base = base.history ∧
    let t := tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)
    let book := t.config.book
    let lw := writesOf L.acts
    let rw := writesOf R.acts
    let cs := (lawClashes (nonWrites L.acts) (nonWrites R.acts)).map (fun p => Conflict.laws p L.name R.name) ++
      writeConflicts text book L.name R.name lw rw
    let mp := mergedPairs text book lw rw
    let pre : List (Side × String × Refusal) := mp.filterMap fun p =>
      (pairAuthority t.config.auth book p).map fun r => (.both, p.2.2.label, r)
    let w := runWrites (sideName L.name R.name) t.config (lawFirst
      ((freeLeft lw rw).map (.left, ·) ++ (freeRight lw rw).map (.right, ·) ++
        ((mp.filter fun p => (pairAuthority t.config.auth book p).isNone).map fun p => (.both, p.2.2))))
    m = ⟨{ w.config with conflicts := w.config.conflicts ++ cs }, t.landed ++ w.landed,
      t.refused ++ pre ++ w.refused, cs⟩ := by
  unfold merge at h
  split at h
  · cases h
  · rename_i hl
    split at h
    · cases h
    · rename_i hr
      cases h
      exact ⟨Classical.not_not.1 hl, Classical.not_not.1 hr, rfl⟩

theorem nonWrites_not_write {acts : List Act} {t : BTurn} : Act.write t ∉ nonWrites acts := by
  intro h
  have := (List.mem_filter.1 h).2
  simp [Act.isWrite] at this

theorem tip_landed_not_write {base : Config} {ln rn : String} {lnw rnw : List Act}
    (hl : ∀ a ∈ lnw, a.isWrite = false) (hr : ∀ a ∈ rnw, a.isWrite = false) {sd : Side} {t : BTurn} :
    (sd, Act.write t) ∉ (tipConfig base ln rn lnw rnw).landed := by
  intro h
  have hm := runActs_landed_sub _ h
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
    cases he
    have := hl _ (List.mem_filter.1 ha).1
    simp [Act.isWrite] at this
  · obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
    cases he
    have := hr _ (List.mem_filter.1 ha).1
    simp [Act.isWrite] at this

theorem nonWrites_isWrite {acts : List Act} : ∀ a ∈ nonWrites acts, a.isWrite = false := by
  intro a ha
  simpa using (List.mem_filter.1 ha).2

/-- A write landed by a merge was admitted at a configuration with the tip's law book and authority. -/
theorem merge_landed_write {base : Config} {L R : Branch} {text : TextMerge} {m : Merged} (h : merge base L R text = .ok m)
    {sd : Side} {t : BTurn} (ht : (sd, .write t) ∈ m.landed) :
    ∃ c₀ c₁, c₀.book = m.tip.book ∧ c₀.auth = m.tip.auth ∧
      admitWrite c₀ (sideName L.name R.name sd) t = .ok c₁ := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  simp only at ht ⊢
  rcases List.mem_append.1 ht with ht | ht
  · exact absurd ht (tip_landed_not_write nonWrites_isWrite nonWrites_isWrite)
  · obtain ⟨c₀, c₁, h0b, h0a, h0⟩ := runWrites_mem_landed ht
    exact ⟨c₀, c₁, h0b.trans runWrites_book.symm, h0a.trans runWrites_auth.symm, h0⟩

/-- **Settlement at the tip.** A write a merge landed relied only on sturdyrefs live at the tip, and
every page it wrote is its actor's or granted to it by one of them, live at the tip: authority read
where every revocation of both sides is visible, never on the write's own branch. -/
theorem settled_at_tip {base : Config} {L R : Branch} {text : TextMerge} {m : Merged} (h : merge base L R text = .ok m)
    {sd : Side} {t : BTurn} (ht : (sd, .write t) ∈ m.landed) :
    (∀ u ∈ t.relies, m.tip.auth.live u = true) ∧
    ∀ d ∈ t.turn.writeCells, ∃ pl, m.tip.book.lookup d.cell = some pl ∧
      (pl.owner = t.actor ∨
        ∃ u ∈ t.relies, ∃ sr, m.tip.auth.find? u = some sr ∧ grantsWrite sr d.cell = true) := by
  obtain ⟨c₀, c₁, hb, ha, h0⟩ := merge_landed_write h ht
  obtain ⟨_, hauth, _, _⟩ := admitWrite_ok h0
  rw [← hb, ← ha]
  exact authRefusal_none hauth

/-- **Every revocation either side landed is visible at the tip.** -/
theorem tip_sees_every_revocation {base : Config} {L R : Branch} {text : TextMerge} {m : Merged} (h : merge base L R text = .ok m)
    {sd : Side} {l w u : String} (hr : (sd, .revoke l w u) ∈ m.landed) : m.tip.auth.isRevoked u = true := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  simp only at hr ⊢
  rw [runWrites_auth]
  rcases List.mem_append.1 hr with hr | hr
  · exact runActs_revocation_visible hr
  · obtain ⟨_, _, he, _⟩ := runWrites_landed_shape hr
    cases he

/-- **A sturdyref revoked on either side carries no write into the merge**: no write relying on it
lands, whichever side wrote it and whatever its own branch said. -/
theorem revoked_elsewhere_never_lands {base : Config} {L R : Branch} {text : TextMerge} {m : Merged}
    (h : merge base L R text = .ok m) {sd sd' : Side} {l w u : String} (hr : (sd', .revoke l w u) ∈ m.landed)
    {t : BTurn} (hu : u ∈ t.relies) : (sd, .write t) ∉ m.landed := by
  intro ht
  have hlive := (settled_at_tip h ht).1 u hu
  have hrev := tip_sees_every_revocation h hr
  simp [Authority.live, hrev] at hlive

/-- **A landed write is consented to at the tip**: it was admitted at a configuration with the tip's
law book and authority, and consented to there (`WriteConsents`): in a vault by the store's judgment
of its text, otherwise by every law of every page in its cone. -/
theorem landed_consents {base : Config} {L R : Branch} {text : TextMerge} {m : Merged} (h : merge base L R text = .ok m)
    {sd : Side} {t : BTurn} (ht : (sd, .write t) ∈ m.landed) :
    ∃ c₀ c₁, c₀.book = m.tip.book ∧ c₀.auth = m.tip.auth ∧
      admitWrite c₀ (sideName L.name R.name sd) t = .ok c₁ ∧ WriteConsents c₀ c₁ t := by
  obtain ⟨c₀, c₁, hb, ha, h0⟩ := merge_landed_write h ht
  exact ⟨c₀, c₁, hb, ha, h0, admitWrite_consents h0⟩

/-! ### The merge is a pushout over the base -/

/-- The turns applied in order. -/
def applyAll (s : VaultStore) (ts : List BTurn) : VaultStore := ts.foldl (fun s t => applyTurn s t.turn) s

def writesAll (ts : List BTurn) : List String := ts.flatMap BTurn.writes

/-- The writes among landed acts, in order. -/
def turnsOf (L : List (Side × Act)) : List BTurn :=
  L.filterMap fun x => match x.2 with
    | .write t => some t
    | _ => none

/-- The writes of one side among the acts landed, in order. -/
def landedOn (sd : Side) (L : List (Side × Act)) : List BTurn :=
  turnsOf (L.filter fun x => x.1 = sd)

theorem landedOn_append (sd : Side) (a b : List (Side × Act)) :
    landedOn sd (a ++ b) = landedOn sd a ++ landedOn sd b := by
  simp [landedOn, turnsOf, List.filter_append, List.filterMap_append]

theorem applyAll_cons (s : VaultStore) (t : BTurn) (rest : List BTurn) :
    applyAll s (t :: rest) = applyAll (applyTurn s t.turn) rest := rfl

theorem applyAll_not_mem : ∀ {s : VaultStore} {ts : List BTurn} {c : String}, c ∉ writesAll ts →
    applyAll s ts c = s c
  | _, [], _, _ => rfl
  | s, t :: rest, c, h => by
    simp only [writesAll, List.flatMap_cons, List.mem_append, not_or] at h
    rw [applyAll_cons, applyAll_not_mem (ts := rest) h.2]
    exact applyTurn_frame_of_not_mem s t.turn c h.1

theorem applyTurn_mem {s s' : VaultStore} {t : VaultTurn} {c : String} (h : c ∈ t.writeFootprint) :
    applyTurn s t c = applyTurn s' t c := by
  simp only [VaultTurn.writeFootprint, List.mem_map] at h
  obtain ⟨d, hd, rfl⟩ := h
  rw [applyTurn_write s t d hd, applyTurn_write s' t d hd]

theorem applyAll_mem : ∀ {s s' : VaultStore} {ts : List BTurn} {c : String}, c ∈ writesAll ts →
    applyAll s ts c = applyAll s' ts c
  | _, _, [], _, h => by cases h
  | s, s', t :: rest, c, h => by
    rw [applyAll_cons, applyAll_cons]
    by_cases hr : c ∈ writesAll rest
    · exact applyAll_mem hr
    · rw [applyAll_not_mem hr, applyAll_not_mem hr]
      simp only [writesAll, List.flatMap_cons, List.mem_append] at h
      rcases h with h | h
      · exact applyTurn_mem h
      · exact absurd h hr

theorem runWrites_append {name : Side → String} :
    ∀ {c : Config} {xs ys : List (Side × BTurn)},
      runWrites name c (xs ++ ys) =
        ⟨(runWrites name (runWrites name c xs).config ys).config,
          (runWrites name c xs).landed ++ (runWrites name (runWrites name c xs).config ys).landed,
          (runWrites name c xs).refused ++ (runWrites name (runWrites name c xs).config ys).refused⟩
  | c, [], ys => rfl
  | c, (sd, t) :: rest, ys => by
    simp only [List.cons_append, runWrites]
    split <;> rw [runWrites_append] <;> rfl

/-- A run of writes reaches the store its landed writes reach. -/
theorem runWrites_store {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × BTurn)},
      (runWrites name c xs).config.store = applyAll c.store (turnsOf (runWrites name c xs).landed)
  | c, [] => rfl
  | c, (sd, t) :: rest => by
    simp only [runWrites]
    split
    · rename_i c' hc
      obtain ⟨_, _, _, _, rfl⟩ := admitWrite_ok hc
      simp only [turnsOf, List.filterMap_cons]
      exact runWrites_store
    · exact runWrites_store

theorem runWrites_landed_side {name : Side → String} (sd : Side) :
    ∀ {c : Config} {xs : List BTurn}, ∀ x ∈ (runWrites name c (xs.map (sd, ·))).landed,
      ∃ t ∈ xs, x = (sd, .write t)
  | _, [], _, h => by cases h
  | c, t :: rest, x, hx => by
    simp only [List.map_cons, runWrites] at hx
    split at hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨t, List.mem_cons_self .., rfl⟩
      · obtain ⟨t', ht', he⟩ := runWrites_landed_side sd x hx
        exact ⟨t', List.mem_cons_of_mem _ ht', he⟩
    · obtain ⟨t', ht', he⟩ := runWrites_landed_side sd x hx
      exact ⟨t', List.mem_cons_of_mem _ ht', he⟩

/-- On acts of one side, `landedOn` that side is every write, and the other side's is empty. -/
theorem landedOn_side (sd : Side) {L : List (Side × Act)} (hL : ∀ x ∈ L, x.1 = sd) :
    landedOn sd L = turnsOf L ∧ ∀ sd', sd' ≠ sd → landedOn sd' L = [] := by
  refine ⟨?_, fun sd' hne => ?_⟩
  · unfold landedOn
    rw [List.filter_eq_self.2 (fun x hx => by simp [hL x hx])]
  · unfold landedOn
    rw [List.filter_eq_nil_iff.2 (fun x hx => by simp [hL x hx, Ne.symm hne])]
    rfl

theorem turnsOf_nonwrites {L : List (Side × Act)} (hL : ∀ x ∈ L, x.2.isWrite = false) : turnsOf L = [] := by
  induction L with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨s, a⟩ := x
    have hx := hL _ (List.mem_cons_self ..)
    have ih' := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    cases a with
    | write t => simp [Act.isWrite] at hx
    | relaw => simpa [turnsOf] using ih'
    | revoke => simpa [turnsOf] using ih'
    | grant => simpa [turnsOf] using ih'

theorem landedOn_nonwrites (sd : Side) {L : List (Side × Act)} (hL : ∀ x ∈ L, x.2.isWrite = false) :
    landedOn sd L = [] :=
  turnsOf_nonwrites fun x hx => hL x (List.mem_filter.1 hx).1

theorem mem_turnsOf {L : List (Side × Act)} {t : BTurn} (h : t ∈ turnsOf L) : ∃ sd, (sd, .write t) ∈ L := by
  obtain ⟨⟨sd, a⟩, hx, he⟩ := List.mem_filterMap.1 h
  cases a with
  | write t' => cases he; exact ⟨sd, hx⟩
  | relaw => cases he
  | revoke => cases he
  | grant => cases he

theorem writes_sub_access (book : LawBook) (t : BTurn) : ∀ c ∈ t.writes, c ∈ t.access book := by
  intro c hc
  unfold BTurn.access
  refine List.mem_append_left _ ?_
  rw [mem_accessFootprint]
  exact .inr hc

theorem mem_clash {a b : BTurn} {c : String} : c ∈ clash a b ↔ c ∈ a.writes ∧ c ∈ b.writes := by
  unfold clash
  simp [List.mem_eraseDups, List.mem_filter]

/-- Writes with no clash: no cell written by both. -/
theorem clash_nil_iff {a b : BTurn} : (clash a b).isEmpty = true ↔ ∀ c ∈ a.writes, c ∉ b.writes := by
  rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h c ha hb
    exact h c (mem_clash.2 ⟨ha, hb⟩)
  · intro h c hc
    exact h c (mem_clash.1 hc).1 (mem_clash.1 hc).2

theorem freeLeft_sub {lw rw : List BTurn} {a : BTurn} (h : a ∈ freeLeft lw rw) :
    a ∈ lw ∧ ∀ b ∈ rw, (clash a b).isEmpty = true := by
  unfold freeLeft at h
  obtain ⟨ha, hall⟩ := List.mem_filter.1 h
  exact ⟨ha, fun b hb => List.all_eq_true.1 hall b hb⟩

theorem freeRight_sub {lw rw : List BTurn} {b : BTurn} (h : b ∈ freeRight lw rw) :
    b ∈ rw ∧ ∀ a ∈ lw, (clash a b).isEmpty = true := by
  unfold freeRight at h
  obtain ⟨hb, hall⟩ := List.mem_filter.1 h
  exact ⟨hb, fun a ha => List.all_eq_true.1 hall a ha⟩

theorem admitAct_nonwrite_keeps {c c' : Config} {o : String} {a : Act} (hw : a.isWrite = false)
    (h : admitAct c o a = .ok c') : c'.store = c.store ∧ c'.vault = c.vault := by
  cases a with
  | write t => simp [Act.isWrite] at hw
  | relaw l w p pl =>
    simp only [admitAct] at h
    split at h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
  | revoke l w u =>
    simp only [admitAct] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h; exact ⟨rfl, rfl⟩
        · cases h
  | grant l w sr =>
    simp only [admitAct] at h
    split at h
    · cases h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h

theorem admitAct_store_nonwrite {c c' : Config} {o : String} {a : Act} (hw : a.isWrite = false)
    (h : admitAct c o a = .ok c') : c'.store = c.store := by
  cases a with
  | write t => simp [Act.isWrite] at hw
  | relaw l w p pl =>
    simp only [admitAct] at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · split at h
      · cases h; rfl
      · cases h
  | revoke l w u =>
    simp only [admitAct] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h; rfl
        · cases h
  | grant l w sr =>
    simp only [admitAct] at h
    split at h
    · cases h
    · split at h
      · cases h; rfl
      · cases h

theorem runActs_store_nonwrites {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × Act)}, (∀ x ∈ xs, x.2.isWrite = false) →
      (runActs name c xs).config.store = c.store
  | _, [], _ => rfl
  | c, (sd, a) :: rest, hw => by
    have hx := hw _ (List.mem_cons_self ..)
    have hrest := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    simp only [runActs]
    split
    · rename_i c' hc
      exact (runActs_store_nonwrites hrest).trans (admitAct_store_nonwrite hx hc)
    · exact runActs_store_nonwrites hrest

/-- The acts the tip settles are none of them writes. -/
theorem tip_input_nonwrites (lnw rnw : List Act) (hl : ∀ a ∈ lnw, a.isWrite = false)
    (hr : ∀ a ∈ rnw, a.isWrite = false) (held : List String) :
    ∀ x ∈ (lnw.filter (!heldRelaw held ·)).map (Side.left, ·) ++
      (rnw.filter (!heldRelaw held ·)).map (Side.right, ·), x.2.isWrite = false := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx; exact hl a (List.mem_filter.1 ha).1
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx; exact hr a (List.mem_filter.1 ha).1

theorem tip_store (base : Config) (ln rn : String) (lacts racts : List Act) :
    (tipConfig base ln rn (nonWrites lacts) (nonWrites racts)).config.store = base.store :=
  runActs_store_nonwrites (tip_input_nonwrites _ _ nonWrites_isWrite nonWrites_isWrite _)

theorem tip_landed_nonwrites (base : Config) (ln rn : String) (lacts racts : List Act) :
    ∀ x ∈ (tipConfig base ln rn (nonWrites lacts) (nonWrites racts)).landed, x.2.isWrite = false :=
  fun x hx => tip_input_nonwrites _ _ nonWrites_isWrite nonWrites_isWrite _ x (runActs_landed_sub x hx)

theorem mergeLegs_cells {text : TextMerge} {book : LawBook} {bs : List CellDelta} :
    ∀ {as : List CellDelta} {legs : List WitnessLegSpec}, mergeLegs text book bs as = some legs →
      legs.map (·.1) = as.map (·.cell)
  | [], legs, h => by simp only [mergeLegs, Option.some.injEq] at h; subst h; rfl
  | da :: rest, legs, h => by
    simp only [mergeLegs] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hr : mergeLegs text book bs rest with
        | none => rw [hr] at h; cases h
        | some ls =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          simp [mergeLegs_cells hr]

/-- A merged write writes exactly the left's cells, which the right's write writes too. -/
theorem mergeFor_writes {text : TextMerge} {book : LawBook} {lw rw : List BTurn} {a b m : BTurn}
    (h : mergeFor text book lw rw a b = some m) : m.writes = a.writes ∧ ∀ c ∈ a.writes, c ∈ b.writes := by
  unfold mergeFor at h
  split at h
  · cases h
  · rename_i hsame
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, List.all_eq_true,
      List.contains_iff_mem] at hsame
    split at h
    · cases h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i legs hlegs
          cases hv : VaultTurn.ofWitnessLegs ByteArray.empty (a.turn.readPins ++ b.turn.readPins) legs
              a.turn.occasion [] with
          | none => rw [hv] at h; cases h
          | some vt =>
            rw [hv] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            refine ⟨?_, hsame.2⟩
            obtain ⟨_, _, hw, _⟩ := VaultTurn.ofWitnessLegs_fields hv
            simp only [BTurn.writes, VaultTurn.writeFootprint, hw, witnessLegs, List.map_map]
            rw [← mergeLegs_cells hlegs]
            rfl

theorem mem_mergedPairs {text : TextMerge} {book : LawBook} {lw rw : List BTurn} {a b m : BTurn}
    (h : (a, b, m) ∈ mergedPairs text book lw rw) : a ∈ lw ∧ b ∈ rw ∧ mergeFor text book lw rw a b = some m := by
  unfold mergedPairs at h
  obtain ⟨a', ha', hm⟩ := List.mem_flatMap.1 h
  obtain ⟨b', hb', he⟩ := List.mem_filterMap.1 hm
  split at he
  · cases he
  · cases hf : mergeFor text book lw rw a' b' with
    | none => rw [hf] at he; cases he
    | some m' =>
      rw [hf] at he
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact ⟨ha', hb', hf⟩

/-- The merged writes a merge replays, each with the pair it came from. -/
theorem mem_mergedTurns {text : TextMerge} {book : LawBook} {lw rw : List BTurn} {auth : Authority} {m : BTurn}
    (h : m ∈ ((mergedPairs text book lw rw).filter fun p => (pairAuthority auth book p).isNone).map (·.2.2)) :
    ∃ a b, a ∈ lw ∧ b ∈ rw ∧ mergeFor text book lw rw a b = some m := by
  obtain ⟨⟨a, b, m'⟩, hp, rfl⟩ := List.mem_map.1 h
  obtain ⟨ha, hb, hm⟩ := mem_mergedPairs (List.mem_filter.1 hp).1
  exact ⟨a, b, ha, hb, hm⟩

theorem applyAll_congr_at {s s' : VaultStore} {c : String} (h : s c = s' c) (ts : List BTurn) :
    applyAll s ts c = applyAll s' ts c := by
  by_cases hc : c ∈ writesAll ts
  · exact applyAll_mem hc
  · rw [applyAll_not_mem hc, applyAll_not_mem hc, h]

theorem mem_landedOn {sd : Side} {L : List (Side × Act)} {t : BTurn} (h : t ∈ landedOn sd L) :
    (sd, .write t) ∈ L := by
  obtain ⟨sd', hx⟩ := mem_turnsOf h
  have hm := List.mem_filter.1 hx
  have he : sd' = sd := by simpa using hm.2
  rw [← he]
  exact hm.1

theorem mem_writesAll_landedOn {sd : Side} {L : List (Side × Act)} {t : BTurn} {c : String}
    (h : (sd, .write t) ∈ L) (hc : c ∈ t.writes) : c ∈ writesAll (landedOn sd L) := by
  unfold writesAll landedOn turnsOf
  refine List.mem_flatMap.2 ⟨t, List.mem_filterMap.2 ⟨(sd, .write t), List.mem_filter.2 ⟨h, by simp⟩, rfl⟩, hc⟩

/-- **The other sides' writes leave a cell they do not write**: the turns landed, applied in order,
read at a cell only one side writes, as that side's turns alone. -/
theorem applyAll_side (sd : Side) (c : String) :
    ∀ {s : VaultStore} {L : List (Side × Act)}, (∀ x ∈ L, ∀ t, x.2 = .write t → x.1 ≠ sd → c ∉ t.writes) →
      applyAll s (turnsOf L) c = applyAll s (landedOn sd L) c
  | _, [], _ => rfl
  | s, (sd', a) :: rest, h => by
    have ih : ∀ s, applyAll s (turnsOf rest) c = applyAll s (landedOn sd rest) c :=
      fun s => applyAll_side sd c (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases a with
    | write t =>
      have hT : turnsOf ((sd', Act.write t) :: rest) = t :: turnsOf rest := rfl
      rw [hT, applyAll_cons, ih]
      by_cases hs : sd' = sd
      · subst hs
        have hL : landedOn sd' ((sd', Act.write t) :: rest) = t :: landedOn sd' rest := by
          simp [landedOn, turnsOf]
        rw [hL, applyAll_cons]
      · have hL : landedOn sd ((sd', Act.write t) :: rest) = landedOn sd rest := by
          simp [landedOn, hs]
        rw [hL]
        exact applyAll_congr_at
          (applyTurn_frame_of_not_mem s t.turn c (h _ (List.mem_cons_self ..) t rfl hs)) _
    | relaw l w p pl =>
      have hT : turnsOf ((sd', Act.relaw l w p pl) :: rest) = turnsOf rest := rfl
      have hL : landedOn sd ((sd', Act.relaw l w p pl) :: rest) = landedOn sd rest := by
        unfold landedOn; rw [List.filter_cons]; split <;> rfl
      rw [hT, hL, ih]
    | revoke l w u =>
      have hT : turnsOf ((sd', Act.revoke l w u) :: rest) = turnsOf rest := rfl
      have hL : landedOn sd ((sd', Act.revoke l w u) :: rest) = landedOn sd rest := by
        unfold landedOn; rw [List.filter_cons]; split <;> rfl
      rw [hT, hL, ih]
    | grant l w sr =>
      have hT : turnsOf ((sd', Act.grant l w sr) :: rest) = turnsOf rest := rfl
      have hL : landedOn sd ((sd', Act.grant l w sr) :: rest) = landedOn sd rest := by
        unfold landedOn; rw [List.filter_cons]; split <;> rfl
      rw [hT, hL, ih]

/-- **The merge is the pushout over the base.** The left's landed writes, the right's, and the
merged writes (pairs merged by their pages' laws) write pairwise disjoint cells — the left's and
the right's apart, the merged apart from both — and the tip's store is the merged writes on their
cells, the left's on theirs, the right's on theirs, and the base everywhere else. -/
theorem merge_is_pushout {base : Config} {L R : Branch} {text : TextMerge} {m : Merged} (h : merge base L R text = .ok m) :
    (∀ c ∈ writesAll (landedOn .left m.landed), c ∉ writesAll (landedOn .right m.landed)) ∧
    (∀ c ∈ writesAll (landedOn .both m.landed),
      c ∉ writesAll (landedOn .left m.landed) ∧ c ∉ writesAll (landedOn .right m.landed)) ∧
    ∀ c, m.tip.store c =
      if c ∈ writesAll (landedOn .both m.landed) then applyAll base.store (landedOn .both m.landed) c
      else if c ∈ writesAll (landedOn .left m.landed) then applyAll base.store (landedOn .left m.landed) c
      else if c ∈ writesAll (landedOn .right m.landed) then applyAll base.store (landedOn .right m.landed) c
      else base.store c := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  simp only
  have hts := tip_store base L.name R.name L.acts R.acts
  have htl := tip_landed_nonwrites base L.name R.name L.acts R.acts
  generalize tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts) = t at hts htl ⊢
  generalize hlf : freeLeft (writesOf L.acts) (writesOf R.acts) = lf
  generalize hrf : freeRight (writesOf L.acts) (writesOf R.acts) = rf
  have hmf : ((mergedPairs text t.config.book (writesOf L.acts) (writesOf R.acts)).filter
      fun p => (pairAuthority t.config.auth t.config.book p).isNone).map (fun p => (Side.both, p.2.2)) =
      (((mergedPairs text t.config.book (writesOf L.acts) (writesOf R.acts)).filter
      fun p => (pairAuthority t.config.auth t.config.book p).isNone).map (·.2.2)).map (Side.both, ·) := by
    rw [List.map_map]; rfl
  rw [hmf]
  have hmem := fun (x : BTurn) (hx : x ∈ ((mergedPairs text t.config.book (writesOf L.acts) (writesOf R.acts)).filter
      fun p => (pairAuthority t.config.auth t.config.book p).isNone).map (·.2.2)) => mem_mergedTurns hx
  generalize ((mergedPairs text t.config.book (writesOf L.acts) (writesOf R.acts)).filter
      fun p => (pairAuthority t.config.auth t.config.book p).isNone).map (·.2.2) = mf at hmem ⊢
  generalize hw : runWrites (sideName L.name R.name) t.config
    (lawFirst (lf.map (Side.left, ·) ++ rf.map (Side.right, ·) ++ mf.map (Side.both, ·))) = w
  have hland : ∀ sd, landedOn sd (t.landed ++ w.landed) = landedOn sd w.landed := by
    intro sd; rw [landedOn_append, landedOn_nonwrites _ htl]; rfl
  rw [hland, hland, hland]
  -- every landed write came from its side's part of the schedule
  have hsub : ∀ {sd : Side} {x : BTurn}, (sd, Act.write x) ∈ w.landed →
      (sd = .left ∧ x ∈ lf) ∨ (sd = .right ∧ x ∈ rf) ∨ (sd = .both ∧ x ∈ mf) := by
    intro sd x hx
    obtain ⟨sd', x', he, hx'⟩ := runWrites_landed_shape (hw ▸ hx)
    simp only [Prod.mk.injEq, Act.write.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases List.mem_append.1 (mem_lawFirst.1 hx') with hx' | hx'
    · rcases List.mem_append.1 hx' with hx' | hx'
      · obtain ⟨a, ha, he⟩ := List.mem_map.1 hx'
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .inl ⟨rfl, ha⟩
      · obtain ⟨a, ha, he⟩ := List.mem_map.1 hx'
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .inr (.inl ⟨rfl, ha⟩)
    · obtain ⟨a, ha, he⟩ := List.mem_map.1 hx'
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .inr (.inr ⟨rfl, ha⟩)
  have hside : ∀ {sd : Side} {c : String}, c ∈ writesAll (landedOn sd w.landed) →
      ∃ x, (sd, Act.write x) ∈ w.landed ∧ c ∈ x.writes := by
    intro sd c hc
    simp only [writesAll, List.mem_flatMap] at hc
    obtain ⟨x, hx, hcx⟩ := hc
    exact ⟨x, mem_landedOn hx, hcx⟩
  have hdisj : ∀ c ∈ writesAll (landedOn .left w.landed), c ∉ writesAll (landedOn .right w.landed) := by
    intro c hc hc'
    obtain ⟨a, ha, hca⟩ := hside hc
    obtain ⟨b, hb, hcb⟩ := hside hc'
    have ha' : a ∈ lf := by rcases hsub ha with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | exact h | cases h
    have hb' : b ∈ rf := by rcases hsub hb with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | cases h
    rw [← hlf] at ha'
    rw [← hrf] at hb'
    exact clash_nil_iff.1 ((freeLeft_sub ha').2 b (freeRight_sub hb').1) c hca hcb
  have hdisjM : ∀ c ∈ writesAll (landedOn .both w.landed),
      c ∉ writesAll (landedOn .left w.landed) ∧ c ∉ writesAll (landedOn .right w.landed) := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := hside hc
    have hx' : x ∈ mf := by rcases hsub hx with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | cases h
    obtain ⟨a, b, ha, hb, hab⟩ := hmem x hx'
    obtain ⟨hxw, hab'⟩ := mergeFor_writes hab
    rw [hxw] at hcx
    refine ⟨fun hc1 => ?_, fun hc2 => ?_⟩
    · obtain ⟨a', ha', hca'⟩ := hside hc1
      have ha'' : a' ∈ lf := by rcases hsub ha' with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | exact h | cases h
      rw [← hlf] at ha''
      exact clash_nil_iff.1 ((freeLeft_sub ha'').2 b hb) c hca' (hab' c hcx)
    · obtain ⟨b', hb', hcb'⟩ := hside hc2
      have hb'' : b' ∈ rf := by rcases hsub hb' with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | cases h
      rw [← hrf] at hb''
      exact clash_nil_iff.1 ((freeRight_sub hb'').2 a ha) c hcx hcb'
  have hst : w.config.store = applyAll base.store (turnsOf w.landed) := by
    rw [← hw, runWrites_store, hts]
  -- a landed write of a side other than `sd` that writes `c` puts `c` among that side's writes
  have hother : ∀ (sd : Side) (c : String),
      (∀ sd', sd' ≠ sd → c ∉ writesAll (landedOn sd' w.landed)) →
      ∀ x ∈ w.landed, ∀ y, x.2 = .write y → x.1 ≠ sd → c ∉ y.writes := by
    intro sd c hnot x hx y he hne hcy
    obtain ⟨sd', a⟩ := x
    simp only at he hne
    subst he
    exact hnot sd' hne (mem_writesAll_landedOn hx hcy)
  refine ⟨hdisj, hdisjM, fun c => ?_⟩
  rw [hst]
  split
  · rename_i hc
    rw [applyAll_side .both c (hother .both c fun sd' hne => by
      cases sd' with
      | left => exact (hdisjM c hc).1
      | right => exact (hdisjM c hc).2
      | both => exact absurd rfl hne)]
  · rename_i hcB
    split
    · rename_i hcL
      rw [applyAll_side .left c (hother .left c fun sd' hne => by
        cases sd' with
        | left => exact absurd rfl hne
        | right => exact hdisj c hcL
        | both => exact hcB)]
    · rename_i hcL
      split
      · rename_i hcR
        rw [applyAll_side .right c (hother .right c fun sd' hne => by
          cases sd' with
          | left => exact hcL
          | right => exact absurd rfl hne
          | both => exact hcB)]
      · rename_i hcR
        rw [applyAll_side .both c (hother .both c fun sd' hne => by
          cases sd' with
          | left => exact hcL
          | right => exact hcR
          | both => exact absurd rfl hne), applyAll_not_mem hcB]

/-! ### A conflict is a state -/

/-- **A clashing pair that does not merge is a conflict kept in the tip's state, and neither write
lands.** -/
theorem clash_is_conflict_state {base : Config} {L R : Branch} {text : TextMerge} {m : Merged} (h : merge base L R text = .ok m)
    {a b : BTurn} (ha : a ∈ writesOf L.acts) (hb : b ∈ writesOf R.acts)
    (hc : (clash a b).isEmpty = false)
    (hn : mergeFor text (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config.book
      (writesOf L.acts) (writesOf R.acts) a b = none) :
    Conflict.writes (clash a b)
        (L.name, a) (R.name, b) ∈ m.tip.conflicts ∧
      (Side.left, Act.write a) ∉ m.landed ∧ (Side.right, Act.write b) ∉ m.landed := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  simp only
  have htl := tip_landed_nonwrites base L.name R.name L.acts R.acts
  generalize tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts) = t at hc hn htl ⊢
  refine ⟨?_, ?_, ?_⟩
  · refine List.mem_append_right _ (List.mem_append_right _ ?_)
    unfold writeConflicts
    refine List.mem_flatMap.2 ⟨a, ha, List.mem_filterMap.2 ⟨b, hb, ?_⟩⟩
    simp [hc, hn]
  · intro hl
    rcases List.mem_append.1 hl with hl | hl
    · have := htl _ hl; simp [Act.isWrite] at this
    · obtain ⟨sd, t', he, hx⟩ := runWrites_landed_shape hl
      cases he
      rcases List.mem_append.1 (mem_lawFirst.1 hx) with hx | hx
      · rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨t'', ht'', he⟩ := List.mem_map.1 hx
          cases he
          have hfree := (freeLeft_sub ht'').2 b hb
          rw [hc] at hfree; cases hfree
        · obtain ⟨_, _, he⟩ := List.mem_map.1 hx; cases he
      · obtain ⟨_, _, he⟩ := List.mem_map.1 hx; cases he
  · intro hl
    rcases List.mem_append.1 hl with hl | hl
    · have := htl _ hl; simp [Act.isWrite] at this
    · obtain ⟨sd, t', he, hx⟩ := runWrites_landed_shape hl
      cases he
      rcases List.mem_append.1 (mem_lawFirst.1 hx) with hx | hx
      · rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨_, _, he⟩ := List.mem_map.1 hx; cases he
        · obtain ⟨t'', ht'', he⟩ := List.mem_map.1 hx
          cases he
          have hfree := (freeRight_sub ht'').2 a ha
          rw [hc] at hfree; cases hfree
      · obtain ⟨_, _, he⟩ := List.mem_map.1 hx; cases he

/-! ### I-confluence: the merged state keeps every law both sides kept -/

section IConfluence

open Obend.Spec.Law (fieldOf fieldLabel firstScalarField firstField LawRef)

/-- The entry map `setNat` applies to a record's fields. -/
def setEntry (f : String) (n : Nat) : String × Data → String × Data :=
  fun (k, x) => if k == f then (k, .natural n) else (k, x)

theorem setNat_record (fs : List (String × Data)) (f : String) (n : Nat) :
    setNat (.record fs) f n = .record (fs.map (setEntry f n)) := rfl

theorem setEntry_fst (f : String) (n : Nat) (p : String × Data) : (setEntry f n p).1 = p.1 := by
  obtain ⟨k, x⟩ := p
  simp only [setEntry]
  split <;> rfl

theorem setEntry_ne {f : String} {n : Nat} {p : String × Data} (h : p.1 ≠ f) : setEntry f n p = p := by
  obtain ⟨k, x⟩ := p
  unfold setEntry
  simp only at h
  simp [h]

theorem setEntry_self {f : String} {n : Nat} {x : Data} : setEntry f n (f, x) = (f, .natural n) := by
  simp [setEntry]

theorem firstScalarField_set_ne {f g : String} {n : Nat} (hg : g ≠ f) :
    ∀ fs : List (String × Data), firstScalarField g (fs.map (setEntry f n)) = firstScalarField g fs
  | [] => rfl
  | (k, x) :: rest => by
    have ih := firstScalarField_set_ne (n := n) hg rest
    rw [List.map_cons]
    by_cases hk : k = f
    · subst hk
      rw [setEntry_self]
      have hkg : ¬ k = g := fun h => hg h.symm
      simp [firstScalarField, hkg, ih]
    · rw [setEntry_ne (by simpa using hk)]
      simp [firstScalarField, ih]

theorem firstField_set_ne {f g : String} {n : Nat} (hg : g ≠ f) :
    ∀ fs : List (String × Data), firstField g (fs.map (setEntry f n)) = firstField g fs
  | [] => rfl
  | (k, x) :: rest => by
    have ih := firstField_set_ne (n := n) hg rest
    rw [List.map_cons]
    by_cases hk : k = f
    · subst hk
      rw [setEntry_self]
      have hkg : ¬ k = g := fun h => hg h.symm
      simp [firstField, hkg, ih]
    · rw [setEntry_ne (by simpa using hk)]
      simp [firstField, ih]

theorem fieldOf_setNat_ne {f g : String} {n : Nat} (hg : g ≠ f) (d : Data) :
    fieldOf g (setNat d f n) = fieldOf g d := by
  cases d with
  | record fs => rw [setNat_record]; exact firstScalarField_set_ne hg fs
  | _ => rfl

theorem fieldLabel_setNat_ne {f g : String} {n : Nat} (hg : g ≠ f) (d : Data) :
    fieldLabel g (setNat d f n) = fieldLabel g d := by
  cases d with
  | record fs => rw [setNat_record]; simp only [fieldLabel, firstField_set_ne hg fs]
  | _ => rfl

theorem firstScalarField_set_self {f : String} {n : Nat} :
    ∀ {fs : List (String × Data)} {x : Int}, firstScalarField f fs = some x →
      firstScalarField f (fs.map (setEntry f n)) = some (n : Int)
  | [], _, h => by cases h
  | (k, v) :: rest, x, h => by
    rw [List.map_cons]
    by_cases hk : k = f
    · subst hk; rw [setEntry_self]; simp [firstScalarField, Obend.Spec.Law.scalarOf]
    · rw [setEntry_ne (by simpa using hk)]
      simp only [firstScalarField, hk, ite_false] at h ⊢
      exact firstScalarField_set_self h

theorem fieldOf_setNat_self {f : String} {n : Nat} {d : Data} {x : Int} (h : fieldOf f d = some x) :
    fieldOf f (setNat d f n) = some (n : Int) := by
  cases d with
  | record fs => rw [setNat_record]; exact firstScalarField_set_self h
  | _ => cases h

theorem firstScalarField_nonneg {f : String} :
    ∀ {fs : List (String × Data)} {x : Int}, firstScalarField f fs = some x → 0 ≤ x
  | [], _, h => by cases h
  | (k, v) :: rest, x, h => by
    simp only [firstScalarField] at h
    split at h
    · split at h
      · rename_i s hs
        cases h
        cases v <;> simp [Obend.Spec.Law.scalarOf] at hs <;> (try subst hs) <;> (try split at hs) <;>
          (try subst hs) <;> omega
      · exact firstScalarField_nonneg h
    · exact firstScalarField_nonneg h

theorem fieldOf_nonneg {f : String} {d : Data} {x : Int} (h : fieldOf f d = some x) : 0 ≤ x := by
  cases d <;> simp only [fieldOf] at h <;> try cases h
  exact firstScalarField_nonneg h

theorem read_setNat {facts : Facts} {f : String} {n : Nat} {d : Data} {ref : LawRef}
    (h : f ∉ ref.fields) : ref.read facts (setNat d f n) = ref.read facts d := by
  cases ref with
  | field g =>
    have : g ≠ f := fun he => h (by simp [LawRef.fields, he])
    simp [LawRef.read, fieldOf_setNat_ne this]
  | _ => rfl

theorem readLabel_setNat {f : String} {n : Nat} {d : Data} {ref : LawRef}
    (h : f ∉ ref.fields) : ref.readLabel (setNat d f n) = ref.readLabel d := by
  cases ref with
  | field g =>
    have : g ≠ f := fun he => h (by simp [LawRef.fields, he])
    simp [LawRef.readLabel, fieldLabel_setNat_ne this]
  | _ => rfl

/-- A law that does not read a field says the same of a state with that field set. -/
theorem denote_setNat_of_not_mem {facts : Facts} {old : Option Data} {f : String} {n : Nat} {d : Data} :
    ∀ {e : LawExpr}, f ∉ e.fields → e.denote facts old (setNat d f n) = e.denote facts old d
  | .eqC ref v, h => by simp only [LawExpr.denote, read_setNat (by simpa [LawExpr.fields] using h)]
  | .leC ref v, h => by simp only [LawExpr.denote, read_setNat (by simpa [LawExpr.fields] using h)]
  | .inC ref v, h => by simp only [LawExpr.denote, read_setNat (by simpa [LawExpr.fields] using h)]
  | .eqR a b, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, read_setNat h.1, read_setNat h.2, readLabel_setNat h.1, readLabel_setNat h.2]
  | .leR a b, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, read_setNat h.1, read_setNat h.2]
  | .leROff a b o, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, read_setNat h.1, read_setNat h.2]
  | .monotone g, h => by
    have : g ≠ f := fun he => h (by simp [LawExpr.fields, he])
    simp only [LawExpr.denote, fieldOf_setNat_ne this]
  | .writeOnce g, h => by
    have : g ≠ f := fun he => h (by simp [LawExpr.fields, he])
    simp only [LawExpr.denote, fieldOf_setNat_ne this, fieldLabel_setNat_ne this]
  | .not a, h => by
    simp only [LawExpr.fields] at h
    simp only [LawExpr.denote, denote_setNat_of_not_mem h]
  | .and a b, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, denote_setNat_of_not_mem h.1, denote_setNat_of_not_mem h.2]
  | .or a b, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, denote_setNat_of_not_mem h.1, denote_setNat_of_not_mem h.2]
  | .implies a b, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, denote_setNat_of_not_mem h.1, denote_setNat_of_not_mem h.2]

theorem MergeKind.le_join (k : MergeKind) (b x y : Nat) : x ≤ k.join b x y := by
  cases k
  · simp only [MergeKind.join]; omega
  · exact Nat.le_max_left x y
  · exact Nat.left_le_or

theorem confluentLaw_fallback {k : MergeKind} {f : String} {e : LawExpr}
    (hc : confluentLaw k f e = true) (hf : f ∈ e.fields) :
    (∃ a b, e = .and a b) ∨ (∃ g, e = .monotone g) ∨ (∃ g v, e = .not (.leC (.field g) v)) ∨
      (∃ g v, e = .leC (.field g) v) := by
  cases e with
  | and a b => exact .inl ⟨a, b, rfl⟩
  | monotone g => exact .inr (.inl ⟨g, rfl⟩)
  | leC ref v =>
    cases ref with
    | field g => exact .inr (.inr (.inr ⟨g, v, rfl⟩))
    | _ => simp [LawExpr.fields, LawRef.fields] at hf
  | not body =>
    cases body with
    | leC ref v =>
      cases ref with
      | field g => exact .inr (.inr (.inl ⟨g, v, rfl⟩))
      | _ => simp [LawExpr.fields, LawRef.fields] at hf
    | _ => simp [confluentLaw, hf] at hc
  | _ => simp [confluentLaw, hf] at hc

/-- One field merged: a law I-confluent for the merge, kept by the left's state `m` and the
right's `r`, is kept by `m` with the field set to the join. -/
theorem confluent_step {k : MergeKind} {f : String} {facts : Facts} {old : Option Data} {m r : Data}
    {x y : Int} (b : Nat) (hx : fieldOf f m = some x) (hy : fieldOf f r = some y) :
    ∀ {e : LawExpr}, confluentLaw k f e = true → e.denote facts old m = true → e.denote facts old r = true →
      e.denote facts old (setNat m f (k.join b x.toNat y.toNat)) = true
  | e, hc, hm, hr => by
    have hx0 := fieldOf_nonneg hx
    have hy0 := fieldOf_nonneg hy
    have hj : x ≤ ((k.join b x.toNat y.toNat : Nat) : Int) := by
      have := k.le_join b x.toNat y.toNat; omega
    by_cases hf : f ∈ e.fields
    · rcases confluentLaw_fallback hc hf with ⟨a, c, rfl⟩ | ⟨g, rfl⟩ | ⟨g, v, rfl⟩ | ⟨g, v, rfl⟩
      · simp only [confluentLaw, Bool.and_eq_true] at hc
        simp only [LawExpr.denote, Bool.and_eq_true] at hm hr ⊢
        exact ⟨confluent_step b hx hy hc.1 hm.1 hr.1, confluent_step b hx hy hc.2 hm.2 hr.2⟩
      · have hg : g = f := by simpa [LawExpr.fields, eq_comm] using hf
        subst hg
        cases old with
        | none => rfl
        | some o =>
          simp only [LawExpr.denote, hx] at hm
          simp only [LawExpr.denote, fieldOf_setNat_self (n := k.join b x.toNat y.toNat) hx]
          split at hm
          · rename_i before after h1 h2
            cases h2
            rw [h1]
            simp only [decide_eq_true_eq] at hm ⊢
            omega
          · cases hm
      · have hg : g = f := by simpa [LawExpr.fields, LawRef.fields, eq_comm] using hf
        subst hg
        simp only [LawExpr.denote, LawRef.read, hx, Bool.not_eq_true', decide_eq_false_iff_not] at hm
        simp only [LawExpr.denote, LawRef.read, fieldOf_setNat_self (n := k.join b x.toNat y.toNat) hx,
          Bool.not_eq_true', decide_eq_false_iff_not]
        omega
      · have hg : g = f := by simpa [LawExpr.fields, LawRef.fields, eq_comm] using hf
        subst hg
        have hk : k = .max := by simpa [confluentLaw] using hc
        subst hk
        simp only [LawExpr.denote, LawRef.read, hx, decide_eq_true_eq] at hm
        simp only [LawExpr.denote, LawRef.read, hy, decide_eq_true_eq] at hr
        have hmax : ((MergeKind.max.join b x.toNat y.toNat : Nat) : Int) ≤ v := by
          show ((Max.max x.toNat y.toNat : Nat) : Int) ≤ v
          rcases Nat.le_total x.toNat y.toNat with h | h
          · rw [Nat.max_eq_right h]; omega
          · rw [Nat.max_eq_left h]; omega
        simp only [LawExpr.denote, LawRef.read]
        rw [fieldOf_setNat_self hx]
        exact decide_eq_true hmax
    · rw [denote_setNat_of_not_mem hf]; exact hm

/-- **I-confluent merge is lawful.** If every law is I-confluent for every declared merge of a page,
the state `mergeState` reaches from the left's `l` and the right's `r` keeps every law both kept. -/
theorem iconfluent_merge_lawful {facts : Facts} {old : Option Data} {pre r : Data} :
    ∀ {merges : List (String × MergeKind)} {l m : Data}, mergeState pre r merges l = some m →
      ∀ {e : LawExpr}, (∀ fk ∈ merges, confluentLaw fk.2 fk.1 e = true) →
        e.denote facts old l = true → e.denote facts old r = true → e.denote facts old m = true
  | [], l, m, h, e, _, hl, _ => by simp only [mergeState, Option.some.injEq] at h; subst h; exact hl
  | fk :: rest, l, m, h, e, hc, hl, hr => by
    simp only [mergeState] at h
    cases hs : mergeStep pre r l fk with
    | none => rw [hs] at h; cases h
    | some l' =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      refine iconfluent_merge_lawful h (fun fk' hfk' => hc fk' (List.mem_cons_of_mem _ hfk')) ?_ hr
      unfold mergeStep at hs
      dsimp only at hs
      split at hs
      · rename_i x y hx hy
        split at hs
        · cases hs; exact hl
        · split at hs
          · cases hs
            exact confluent_step _ hx hy (hc fk (List.mem_cons_self ..)) hl hr
          · cases hs
      · cases hs; exact hl
      · cases hs

/-- A law that does not read a field says the same with that field set in its old state. -/
theorem denote_old_setNat_of_not_mem {facts : Facts} {o : Data} {f : String} {n : Nat} {d : Data} :
    ∀ {e : LawExpr}, f ∉ e.fields → e.denote facts (some (setNat o f n)) d = e.denote facts (some o) d
  | .eqC _ _, _ => rfl
  | .leC _ _, _ => rfl
  | .inC _ _, _ => rfl
  | .eqR _ _, _ => rfl
  | .leR _ _, _ => rfl
  | .leROff _ _ _, _ => rfl
  | .monotone g, h => by
    have : g ≠ f := fun he => h (by simp [LawExpr.fields, he])
    simp only [LawExpr.denote, fieldOf_setNat_ne this]
  | .writeOnce g, h => by
    have : g ≠ f := fun he => h (by simp [LawExpr.fields, he])
    simp only [LawExpr.denote, Option.bind_some, fieldOf_setNat_ne this, fieldLabel_setNat_ne this]
  | .not a, h => by
    simp only [LawExpr.fields] at h
    simp only [LawExpr.denote, denote_old_setNat_of_not_mem h]
  | .and a b, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, denote_old_setNat_of_not_mem h.1, denote_old_setNat_of_not_mem h.2]
  | .or a b, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, denote_old_setNat_of_not_mem h.1, denote_old_setNat_of_not_mem h.2]
  | .implies a b, h => by
    simp only [LawExpr.fields, List.mem_append, not_or] at h
    simp only [LawExpr.denote, denote_old_setNat_of_not_mem h.1, denote_old_setNat_of_not_mem h.2]

/-- One field merged, on the occasion a law over links is judged at a page (the identity write: the
page's state is both its old and its new state). -/
theorem confluent_step_id {k : MergeKind} {f : String} {facts : Facts} {m r : Data}
    {x y : Int} (b : Nat) (hx : fieldOf f m = some x) (hy : fieldOf f r = some y) :
    ∀ {e : LawExpr}, confluentLaw k f e = true → e.denote facts (some m) m = true →
      e.denote facts (some r) r = true →
      e.denote facts (some (setNat m f (k.join b x.toNat y.toNat))) (setNat m f (k.join b x.toNat y.toNat)) = true
  | e, hc, hm, hr => by
    by_cases hf : f ∈ e.fields
    · rcases confluentLaw_fallback hc hf with ⟨a, c, rfl⟩ | ⟨g, rfl⟩ | ⟨g, v, rfl⟩ | ⟨g, v, rfl⟩
      · simp only [confluentLaw, Bool.and_eq_true] at hc
        simp only [LawExpr.denote, Bool.and_eq_true] at hm hr ⊢
        exact ⟨confluent_step_id b hx hy hc.1 hm.1 hr.1, confluent_step_id b hx hy hc.2 hm.2 hr.2⟩
      · have hg : g = f := by simpa [LawExpr.fields, eq_comm] using hf
        subst hg
        simp [LawExpr.denote, fieldOf_setNat_self (n := k.join b x.toNat y.toNat) hx]
      · have h := confluent_step (old := none) b hx hy hc (by simpa only [LawExpr.denote] using hm)
          (by simpa only [LawExpr.denote] using hr)
        simpa only [LawExpr.denote] using h
      · have h := confluent_step (old := none) b hx hy hc (by simpa only [LawExpr.denote] using hm)
          (by simpa only [LawExpr.denote] using hr)
        simpa only [LawExpr.denote] using h
    · rw [denote_old_setNat_of_not_mem hf, denote_setNat_of_not_mem hf]; exact hm

/-- **I-confluent merge keeps the laws over links.** If every law over links judged at a page is
I-confluent for every declared merge of the page, the state `mergeState` reaches keeps every such law
both sides' states kept, on the occasion they are judged at the page (`judgeLinksIn`: the identity
write). -/
theorem iconfluent_merge_links_lawful {facts : Facts} {pre r : Data} :
    ∀ {merges : List (String × MergeKind)} {l m : Data}, mergeState pre r merges l = some m →
      ∀ {e : LawExpr}, (∀ fk ∈ merges, confluentLaw fk.2 fk.1 e = true) →
        e.denote facts (some l) l = true → e.denote facts (some r) r = true →
          e.denote facts (some m) m = true
  | [], l, m, h, e, _, hl, _ => by simp only [mergeState, Option.some.injEq] at h; subst h; exact hl
  | fk :: rest, l, m, h, e, hc, hl, hr => by
    simp only [mergeState] at h
    cases hs : mergeStep pre r l fk with
    | none => rw [hs] at h; cases h
    | some l' =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      refine iconfluent_merge_links_lawful h (fun fk' hfk' => hc fk' (List.mem_cons_of_mem _ hfk')) ?_ hr
      unfold mergeStep at hs
      dsimp only at hs
      split at hs
      · rename_i x y hx hy
        split at hs
        · cases hs; exact hl
        · split at hs
          · cases hs
            exact confluent_step_id _ hx hy (hc fk (List.mem_cons_self ..)) hl hr
          · cases hs
      · cases hs; exact hl
      · cases hs

/-- The declared merge `mergeCell` reaches, when the store keeps no text for the cell: the same
write, or both directions of `mergeState` agreeing, with every law of the cell's cone I-confluent. -/
theorem mergeCell_declared {text : TextMerge} {book : LawBook} {da db : CellDelta} {m : Data}
    (h : mergeCell text book da db = some m) (ht : text.state da.cell = none) {pl : PageLaws}
    (hpl : book.lookup da.cell = some pl) :
    m = da.postState ∨
      (mergeState da.preState db.postState pl.merges da.postState = some m ∧
        ∀ e ∈ pl.own ++ linkedLaws book da.cell, ∀ fk ∈ pl.merges, confluentLaw fk.2 fk.1 e.2 = true) := by
  unfold mergeCell at h
  split at h
  · cases h
  · rw [ht] at h
    simp only at h
    split at h
    · cases h; exact .inl rfl
    · rw [hpl] at h
      simp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hconf
          simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hconf
          split at h
          · rename_i m₁ m₂ h₁ h₂
            split at h
            · cases h
              exact .inr ⟨h₁, hconf⟩
            · cases h
          · cases h

/-- **A merged cell keeps its page's laws.** The post-state `mergeCell` gives, where the store keeps
no text for the cell, keeps every own law of the page that both sides' post-states kept: the same
write trivially, a declared merge by `iconfluent_merge_lawful`. -/
theorem mergeCell_lawful {text : TextMerge} {book : LawBook} {da db : CellDelta} {m : Data}
    (h : mergeCell text book da db = some m) (ht : text.state da.cell = none)
    {pl : PageLaws} (hpl : book.lookup da.cell = some pl) {facts : Facts} {old : Option Data} :
    ∀ p ∈ pl.own, p.2.denote facts old da.postState = true → p.2.denote facts old db.postState = true →
      p.2.denote facts old m = true := by
  intro p hp hl hr
  rcases mergeCell_declared h ht hpl with rfl | ⟨h₁, hconf⟩
  · exact hl
  · exact iconfluent_merge_lawful h₁ (fun fk hfk => hconf p (List.mem_append_left _ hp) fk hfk) hl hr

/-- **A merged cell keeps the laws over links that judge it.** Every law over links of a page linking
to the cell (`linkedLaws`, what `backlinkRefusal` judges at the cell) that both sides' post-states
kept, the merged state keeps, on the occasion it is judged there (`iconfluent_merge_links_lawful`):
a declared merge whose linked laws are I-confluent merges, and is not refused by them at the tip. -/
theorem mergeCell_links_lawful {text : TextMerge} {book : LawBook} {da db : CellDelta} {m : Data}
    (h : mergeCell text book da db = some m) (ht : text.state da.cell = none)
    {pl : PageLaws} (hpl : book.lookup da.cell = some pl) {facts : Facts} :
    ∀ p ∈ linkedLaws book da.cell, p.2.denote facts (some da.postState) da.postState = true →
      p.2.denote facts (some db.postState) db.postState = true → p.2.denote facts (some m) m = true := by
  intro p hp hl hr
  rcases mergeCell_declared h ht hpl with rfl | ⟨h₁, hconf⟩
  · exact hl
  · exact iconfluent_merge_links_lawful h₁ (fun fk hfk => hconf p (List.mem_append_right _ hp) fk hfk) hl hr

end IConfluence

/-! ### Order: what swapping the two sides changes

`merge base L R` and `merge base R L` are not the same function, for two reasons, each exhibited in
`lean/tests/vault/Branch.lean`:
1. the tip settles the non-write acts left first, and their admission depends on order: a grant on
   one side and a revocation of the same sturdyref on the other land in one order (grant, then
   revoke) and not in the other (the revocation finds nothing to revoke), so the tip's authority, and
   every write relying on that sturdyref, depend on which side is called left;
2. a write is judged at the height of the history when it lands (`requestAt`), and the left's free
   writes land before the right's, so a law reading `ledger.height` can admit a write in one order
   and refuse it in the other.
What does not depend on order is proved: the clash relation is symmetric (`clash_comm`), so the free
writes of each side and the held pairs are the same whichever side is left (`freeLeft_swap`), and
the tip's store depends only on which writes landed, not on the order they landed in
(`merge_swap_store`). Merged pairs are left out of `merge_swap_store`: the two orders compute the
merged state from opposite sides and agree on it only up to `termEq`. -/

theorem clash_comm (a b : BTurn) (c : String) : c ∈ clash a b ↔ c ∈ clash b a := by
  rw [mem_clash, mem_clash, and_comm]

theorem clash_isEmpty_comm (a b : BTurn) : (clash a b).isEmpty = (clash b a).isEmpty := by
  cases h1 : (clash a b).isEmpty <;> cases h2 : (clash b a).isEmpty <;> try rfl
  · rw [clash_nil_iff] at h2
    have : (clash a b).isEmpty = true := clash_nil_iff.2 fun c ha hb => h2 c hb ha
    rw [h1] at this; cases this
  · rw [clash_nil_iff] at h1
    have : (clash b a).isEmpty = true := clash_nil_iff.2 fun c hb ha => h1 c ha hb
    rw [h2] at this; cases this

/-- **The free writes do not depend on which side is left.** -/
theorem freeLeft_swap (lw rw : List BTurn) : freeLeft lw rw = freeRight rw lw := by
  unfold freeLeft freeRight
  congr 1
  funext a
  congr 1
  funext b
  exact clash_isEmpty_comm a b

/-- **The store depends on what landed, not on the order it landed in.** When the two orders of a
merge land the same writes of each side (and merge no pair), they reach the same store. -/
theorem merge_swap_store {base : Config} {L R : Branch} {text : TextMerge} {m₁ m₂ : Merged}
    (h₁ : merge base L R text = .ok m₁) (h₂ : merge base R L text = .ok m₂)
    (hl : landedOn .left m₁.landed = landedOn .right m₂.landed)
    (hr : landedOn .right m₁.landed = landedOn .left m₂.landed)
    (hb₁ : landedOn .both m₁.landed = []) (hb₂ : landedOn .both m₂.landed = []) :
    ∀ c, m₁.tip.store c = m₂.tip.store c := by
  obtain ⟨hd₁, _, hs₁⟩ := merge_is_pushout h₁
  obtain ⟨_, _, hs₂⟩ := merge_is_pushout h₂
  intro c
  rw [hs₁ c, hs₂ c, hb₁, hb₂, ← hl, ← hr]
  simp only [writesAll, List.flatMap_nil, List.not_mem_nil, ite_false]
  by_cases hcl : c ∈ writesAll (landedOn .left m₁.landed)
  · have hcr := hd₁ c hcl
    simp only [writesAll] at hcl hcr
    simp [hcl, hcr]
  · simp only [writesAll] at hcl
    simp [hcl]

/-! ### The history -/

theorem admitAct_extends {c c' : Config} {o : String} {a : Act} (h : admitAct c o a = .ok c') :
    c.history <+: c'.history := by
  cases a with
  | write t => obtain ⟨_, _, _, _, rfl⟩ := admitWrite_ok (show admitWrite c o t = .ok c' from h); exact List.prefix_append _ _
  | relaw l w p pl =>
    simp only [admitAct] at h
    split at h
    · split at h
      · cases h; exact List.prefix_append _ _
      · cases h
    · split at h
      · cases h; exact List.prefix_append _ _
      · cases h
  | revoke l w u =>
    simp only [admitAct] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h; exact List.prefix_append _ _
        · cases h
  | grant l w sr =>
    simp only [admitAct] at h
    split at h
    · cases h
    · split at h
      · cases h; exact List.prefix_append _ _
      · cases h

theorem runActs_extends {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × Act)}, c.history <+: (runActs name c xs).config.history
  | _, [] => List.prefix_refl _
  | c, (sd, a) :: rest => by
    simp only [runActs]
    split
    · rename_i c' hc; exact (admitAct_extends hc).trans runActs_extends
    · exact runActs_extends

theorem runWrites_extends {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × BTurn)}, c.history <+: (runWrites name c xs).config.history
  | _, [] => List.prefix_refl _
  | c, (sd, t) :: rest => by
    simp only [runWrites]
    split
    · rename_i c' hc; exact (admitAct_extends (a := .write t) hc).trans runWrites_extends
    · exact runWrites_extends

/-- **The merged history extends the base's**: one receipted history, the base's receipts first. -/
theorem merge_extends_history {base : Config} {L R : Branch} {text : TextMerge} {m : Merged} (h : merge base L R text = .ok m) :
    base.history <+: m.tip.history := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  exact runActs_extends.trans runWrites_extends

/-! ### What a branch cannot learn of the other side's hidden cells -/

/-- With no law-changing write on the right, laws-first keeps the left's writes before the right's. -/
theorem lawFirst_left_right (A B : List BTurn) (hB : ∀ b ∈ B, b.isLaw = false) :
    lawFirst (A.map (Side.left, ·) ++ B.map (Side.right, ·)) =
      (A.filter (·.isLaw) ++ A.filter (!·.isLaw)).map (Side.left, ·) ++ B.map (Side.right, ·) := by
  have h1 : B.filter (·.isLaw) = [] := List.filter_eq_nil_iff.2 fun b hb => by simp [hB b hb]
  have h2 : B.filter (!·.isLaw) = B := List.filter_eq_self.2 fun b hb => by simp [hB b hb]
  unfold lawFirst
  simp only [List.filter_append, List.filter_map, List.map_append]
  have e1 : ((fun x : Side × BTurn => x.2.isLaw) ∘ (Side.right, ·)) = (·.isLaw) := rfl
  have e2 : ((fun x : Side × BTurn => !x.2.isLaw) ∘ (Side.right, ·)) = (!·.isLaw) := rfl
  have e3 : ((fun x : Side × BTurn => x.2.isLaw) ∘ (Side.left, ·)) = (·.isLaw) := rfl
  have e4 : ((fun x : Side × BTurn => !x.2.isLaw) ∘ (Side.left, ·)) = (!·.isLaw) := rfl
  rw [e1, e2, e3, e4, h1, h2]
  simp

/-- **Confinement of the store.** If two right branches have the same name and the same non-write
acts, every write of either accesses only cells of `H` (at the tip's law book), and no write of the
left accesses a cell of `H`, then the left's landed writes are the same against both, and the tip
agrees outside `H`. What the right wrote inside `H` does not reach the left's view of the store. -/
theorem merge_confines_hidden {base : Config} {L R₁ R₂ : Branch} {text : TextMerge} {m₁ m₂ : Merged} {H : List String}
    (h₁ : merge base L R₁ text = .ok m₁) (h₂ : merge base L R₂ text = .ok m₂)
    (hname : R₁.name = R₂.name) (hacts : nonWrites R₁.acts = nonWrites R₂.acts)
    (hlaw₁ : ∀ t ∈ writesOf R₁.acts, t.isLaw = false) (hlaw₂ : ∀ t ∈ writesOf R₂.acts, t.isLaw = false)
    (hR₁ : ∀ t ∈ writesOf R₁.acts, ∀ c ∈ t.access
      (tipConfig base L.name R₁.name (nonWrites L.acts) (nonWrites R₁.acts)).config.book, c ∈ H)
    (hR₂ : ∀ t ∈ writesOf R₂.acts, ∀ c ∈ t.access
      (tipConfig base L.name R₁.name (nonWrites L.acts) (nonWrites R₁.acts)).config.book, c ∈ H)
    (hL : ∀ t ∈ writesOf L.acts, ∀ c ∈ t.access
      (tipConfig base L.name R₁.name (nonWrites L.acts) (nonWrites R₁.acts)).config.book, c ∉ H) :
    landedOn .left m₁.landed = landedOn .left m₂.landed ∧ ∀ c, c ∉ H → m₁.tip.store c = m₂.tip.store c := by
  obtain ⟨_, _, hm₁⟩ := merge_ok h₁
  obtain ⟨_, _, hm₂⟩ := merge_ok h₂
  subst hm₁ hm₂
  simp only
  rw [← hname, ← hacts]
  have htl := tip_landed_nonwrites base L.name R₁.name L.acts R₁.acts
  generalize tipConfig base L.name R₁.name (nonWrites L.acts) (nonWrites R₁.acts) = t at hR₁ hR₂ hL htl ⊢
  -- no write of the left clashes with any write of either right
  have hfree : ∀ (rw : List BTurn), (∀ b ∈ rw, ∀ c ∈ b.access t.config.book, c ∈ H) →
      freeLeft (writesOf L.acts) rw = writesOf L.acts := by
    intro rw hrw
    unfold freeLeft
    rw [List.filter_eq_self]
    intro a ha
    rw [List.all_eq_true]
    intro b hb
    exact clash_nil_iff.2 fun c hc hcb => hL a ha c (writes_sub_access _ a c hc) (hrw b hb c (writes_sub_access _ b c hcb))
  have hnomerge : ∀ (rw : List BTurn), (∀ b ∈ rw, ∀ c ∈ b.access t.config.book, c ∈ H) →
      mergedPairs text t.config.book (writesOf L.acts) rw = [] := by
    intro rw hrw
    rw [List.eq_nil_iff_forall_not_mem]
    rintro ⟨a, b, m⟩ hp
    unfold mergedPairs at hp
    obtain ⟨a', ha', hm⟩ := List.mem_flatMap.1 hp
    obtain ⟨b', hb', he⟩ := List.mem_filterMap.1 hm
    have hcl : (clash a' b').isEmpty = true :=
      clash_nil_iff.2 fun c hc hcb => hL a' ha' c (writes_sub_access _ a' c hc) (hrw b' hb' c (writes_sub_access _ b' c hcb))
    rw [ite_eq_left hcl] at he
    cases he
  rw [hnomerge _ hR₁, hnomerge _ hR₂]
  simp only [List.filter_nil, List.map_nil, List.append_nil]
  rw [hfree _ hR₁, hfree _ hR₂,
    lawFirst_left_right _ _ (fun b hb => hlaw₁ b (freeRight_sub hb).1),
    lawFirst_left_right _ _ (fun b hb => hlaw₂ b (freeRight_sub hb).1), runWrites_append, runWrites_append]
  simp only
  generalize hr1 : runWrites (sideName L.name R₁.name) t.config
    (((writesOf L.acts).filter (·.isLaw) ++ (writesOf L.acts).filter (!·.isLaw)).map (Side.left, ·)) = r1
  have h1 : ∀ x ∈ r1.landed, x.1 = .left := fun x hx => by
    obtain ⟨_, _, rfl⟩ := runWrites_landed_side (name := sideName L.name R₁.name) .left x (hr1 ▸ hx)
    rfl
  have hside : ∀ (rf : List BTurn),
      landedOn .left (t.landed ++ (r1.landed ++
        (runWrites (sideName L.name R₁.name) r1.config (rf.map (Side.right, ·))).landed)) =
      landedOn .left r1.landed := by
    intro rf
    have h2 : ∀ x ∈ (runWrites (sideName L.name R₁.name) r1.config (rf.map (Side.right, ·))).landed,
        x.1 = .right := fun x hx => by
      obtain ⟨_, _, rfl⟩ := runWrites_landed_side (name := sideName L.name R₁.name) .right x hx
      rfl
    rw [landedOn_append, landedOn_append, landedOn_nonwrites _ htl, (landedOn_side .right h2).2 .left (by decide)]
    simp
  have hstore : ∀ (rf : List BTurn), (∀ b ∈ rf, ∀ c ∈ b.access t.config.book, c ∈ H) → ∀ c, c ∉ H →
      (runWrites (sideName L.name R₁.name) r1.config (rf.map (Side.right, ·))).config.store c =
        r1.config.store c := by
    intro rf hrf c hc
    rw [runWrites_store]
    apply applyAll_not_mem
    intro hm
    simp only [writesAll, List.mem_flatMap] at hm
    obtain ⟨b, hb, hcb⟩ := hm
    obtain ⟨sd, hx⟩ := mem_turnsOf hb
    obtain ⟨b', hb', he⟩ := runWrites_landed_side (name := sideName L.name R₁.name) .right _ hx
    cases he
    exact hc (hrf b hb' c (writes_sub_access _ b c hcb))
  refine ⟨by rw [hside, hside], fun c hc => ?_⟩
  rw [hstore (freeRight (writesOf L.acts) (writesOf R₁.acts))
      (fun b hb => hR₁ b (freeRight_sub hb).1) c hc,
    hstore (freeRight (writesOf L.acts) (writesOf R₂.acts))
      (fun b hb => hR₂ b (freeRight_sub hb).1) c hc]

/-! ## The store of states and the vault agree

In a vault the configuration keeps two views of one thing: the store of states the merge's laws
over the pushout speak of (`Config.store`), and the vault's store itself (`Config.vault`), which
judges and lands. They agree page by page, at each page's current version (`Agrees`): a write lands
only when its turn says the state the store lands (`judgeWrite`), every other act leaves both, and
so a merge that starts from agreement ends in it (`merge_vault_agrees`). -/

/-- The store of states and the vault agree on every page: its state is the state of its current
version (as terms). -/
def Agrees (c : Config) : Prop :=
  ∀ v, c.vault = some v → ∀ x, (c.store x).map Data.term = (vaultStates v x).map Data.term

theorem page?_setPage_ne (s : Store) (p : Page) {n : String} (hn : p.name ≠ n) :
    (s.setPage p).page? n = s.page? n := by
  unfold Store.page? Store.setPage
  simp only
  rw [find?_map_page s _ (fun q => by
    split
    · rename_i h; exact (beq_iff_eq.1 h).symm
    · rfl) n]
  cases hq : s.pages.find? (·.name == n) with
  | none => rfl
  | some q =>
    have hqn : q.name = n := by simpa using List.find?_some hq
    have : ¬ q.name = p.name := fun h => hn (h ▸ hqn)
    simp [this]

theorem write_page?_ne {s s' : Store} {p : Page} {G : Graph} {a : List (AtomId × String)} {po : Option String}
    {n : String} (h : s.write p G a .owner po = .ok s') (hn : p.name ≠ n) : s'.page? n = s.page? n := by
  obtain ⟨pr, _, _, rfl⟩ := write_consents h
  exact page?_setPage_ne s _ (by simpa [Page.withChange] using hn)

theorem writeText_page?_ne {s s' : Store} {page n : String} {w : PageWrite} (hn : page ≠ n)
    (h : s.writeText page w = .ok s') : s'.page? n = s.page? n := by
  unfold Store.writeText at h
  cases hl : w.versions.getLast? with
  | none => rw [hl] at h; cases h; rfl
  | some x =>
    obtain ⟨G, a⟩ := x
    rw [hl] at h
    simp only at h
    unfold Store.writeSince at h
    cases hp : s.page? page with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      have hpn : p.name = page := by simpa [Store.page?] using List.find?_some hp
      simp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact page?_setPage_ne s _ (by simpa [Page.withChange] using hpn ▸ hn)

/-- **A write keeps the agreement.** -/
theorem admitWrite_agrees {c c' : Config} {o : String} {t : BTurn} (hc : Agrees c)
    (h : admitWrite c o t = .ok c') : Agrees c' := by
  obtain ⟨_, _, v, hj, rfl⟩ := admitWrite_ok h
  intro v' hv' x
  simp only at hv'
  subst hv'
  unfold judgeWrite at hj
  split at hj
  · rename_i s w d hv ht hw
    cases hs : s.writeText d.cell w with
    | error m => rw [hs] at hj; cases hj
    | ok s' =>
      rw [hs] at hj
      simp only at hj
      cases hx : vaultStates s' d.cell with
      | none => rw [hx] at hj; cases hj
      | some y =>
        rw [hx] at hj
        simp only at hj
        split at hj
        · rename_i hq
          cases hj
          dsimp only
          by_cases hxd : x = d.cell
          · subst hxd
            rw [applyTurn_write c.store t.turn d (by rw [hw]; exact List.mem_singleton_self _), hx]
            simp [Obend.Law.termEq_sound_local hq]
          · have hnot : x ∉ t.turn.writeFootprint := by
              simp [VaultTurn.writeFootprint, hw, hxd]
            rw [applyTurn_frame_of_not_mem _ _ _ hnot]
            have hfr : vaultStates v' x = vaultStates s x := by
              unfold vaultStates
              rw [writeText_page?_ne (Ne.symm hxd) hs]
            rw [hfr]
            exact hc s hv x
        · cases hj
  · rename_i s d₀ ds hv ht hw
    split at hj
    · rename_i hm
      have hmap : t.texts.map (·.1) = (d₀ :: ds).map (·.cell) := beq_iff_eq.1 hm
      cases hs : s.writeTexts t.texts t.actorRef with
      | error m => rw [hs] at hj; cases hj
      | ok s' =>
        rw [hs] at hj
        simp only at hj
        split at hj
        · rename_i hall
          cases hj
          dsimp only
          by_cases hxm : x ∈ t.turn.writeFootprint
          · have hxd : x ∈ (d₀ :: ds).map (·.cell) := by
              simpa [VaultTurn.writeFootprint, hw] using hxm
            obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hxd
            rw [applyTurn_write c.store t.turn d (by rw [hw]; exact hd)]
            have hd_all := List.all_eq_true.1 hall d hd
            cases hx : vaultStates v' d.cell with
            | none => rw [hx] at hd_all; cases hd_all
            | some y =>
              rw [hx] at hd_all
              simp [Obend.Law.termEq_sound_local hd_all]
          · rw [applyTurn_frame_of_not_mem _ _ _ hxm]
            have hnot_texts : x ∉ t.texts.map (·.1) := by
              rw [hmap]
              simpa [VaultTurn.writeFootprint, hw] using hxm
            have hfr : vaultStates v' x = vaultStates s x := by
              unfold vaultStates
              rw [writeTexts_page?_ne hnot_texts hs]
            rw [hfr]
            exact hc s hv x
        · cases hj
    · cases hj
  · cases hj
  · rename_i hv
    split at hj
    · cases hj
    · simp only [Except.ok.injEq] at hj
      rw [hv] at hj
      cases hj

theorem runWrites_agrees {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × BTurn)}, Agrees c → Agrees (runWrites name c xs).config
  | _, [], hc => hc
  | c, (sd, t) :: rest, hc => by
    simp only [runWrites]
    split
    · rename_i c' h'
      exact runWrites_agrees (admitWrite_agrees hc h')
    · exact runWrites_agrees hc

theorem runActs_agrees_nonwrites {name : Side → String} :
    ∀ {c : Config} {xs : List (Side × Act)}, (∀ x ∈ xs, x.2.isWrite = false) → Agrees c →
      Agrees (runActs name c xs).config
  | _, [], _, hc => hc
  | c, (sd, a) :: rest, hw, hc => by
    simp only [runActs]
    split
    · rename_i c' h'
      obtain ⟨hs, hv⟩ := admitAct_nonwrite_keeps (hw _ (List.mem_cons_self ..)) h'
      refine runActs_agrees_nonwrites (fun x hx => hw x (List.mem_cons_of_mem _ hx)) ?_
      intro v hv' x
      rw [hv] at hv'
      rw [hs]
      exact hc v hv' x
    · exact runActs_agrees_nonwrites (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hc

/-- **After a merge the store of states and the vault agree**: every page's state at the tip is the
state of the vault's page at its current version, when they agreed at the base. -/
theorem merge_vault_agrees {base : Config} {L R : Branch} {text : TextMerge} {m : Merged}
    (h : merge base L R text = .ok m) (hb : Agrees base) : Agrees m.tip := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  have ht : Agrees (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config :=
    runActs_agrees_nonwrites (tip_input_nonwrites _ _ nonWrites_isWrite nonWrites_isWrite _) hb
  exact runWrites_agrees ht

/-! ## Teeth -/

/- Removing the tip check (`authRefusal` always passing) loses `settled_at_tip`'s proof. -/
#tooth settled_at_tip by mutation authRefusal := fun _ _ _ => none

/- Judging every write on the store of states, the vault's store kept but not asked, loses the one
judgment. -/
#tooth tip_lands_iff_store_lands by mutation judgeWrite := fun c _ => .ok c.vault

end Obend.Vault.Branch
