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

* **Merge is a pushout over the base, and a conflict is a state.** The writes of the two sides whose
  footprints at the tip are disjoint (Bernstein: neither writes what the other reads or writes, the
  pages its laws over links read included, `BTurn.access`) are replayed at the tip, left then right;
  the store the merge reaches agrees with the left's landed turns on the cells they write, with the
  right's on theirs, and with the base everywhere else, and the two write sets are disjoint
  (`merge_is_pushout`). A pair that clashes is kept as a `Conflict.writes` in the tip's state, both
  candidates and the cells named, and neither lands (`clash_is_conflict_state`); `resolve` lands one
  candidate through the same judgment and names the one it drops. Two relaws of one page that differ
  are a `Conflict.laws`, and the page keeps its base laws. The merged history extends the base
  (`merge_extends_history`).
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
  (`revoked_elsewhere_never_lands`). Revocation is the one non-monotone act: every other act keeps
  every live sturdyref live, and no act unrevokes (`revocation_only_nonmonotone`). A consequence of
  the strict reading: a branch's own write made before its own revocation of the sturdyref it relied
  on does not settle either; authority is read at settlement, not at authoring.
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
  4. a conflict is reported exactly when the other side touched a cell this side accesses;
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

set_option autoImplicit false

/-! ## The law book -/

/-- A page's entry in the law book: whose page it is, its laws (`PAGE: NAME`, expression, text, as
`lawOfLine` reads a law line), and the pages it links to. -/
structure PageLaws where
  owner : String
  laws : Laws := []
  links : List String := []
deriving DecidableEq

/-- A page's law book entry from its law lines `(NAME, TEXT)`, read as the vault reads them. -/
def PageLaws.ofLines (page owner : String) (links : List String) (lines : List (String × String)) :
    Except String PageLaws := do
  let laws ← lines.mapM (lawOfLine page)
  pure ⟨owner, laws, links⟩

/-- A page's own laws (judged on its write, old to new). -/
def PageLaws.own (pl : PageLaws) : List (String × LawExpr) :=
  (pl.laws.filter fun l => !isLinkLaw l.2.2).map fun (n, e, _) => (n, e)

/-- A page's laws over its links (judged at every page it links to). -/
def PageLaws.overLinks (pl : PageLaws) : List (String × LawExpr) := linkLaws pl.laws

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

/-- A configuration: the store, the law book, the authority, the history, the open conflicts. -/
structure Config where
  store : VaultStore
  book : LawBook := []
  auth : Authority := {}
  history : List Receipt := []
  conflicts : List Conflict := []

/-! ## The judgment of a write -/

def factsAt (h : Nat) : Facts := ⟨some 0, some 0, h, h⟩

/-- The request a write by `actor` at height `h` is judged under. -/
def requestAt (actor : String) (h : Nat) : Data := requestBy actor actor .write (factsAt h)

/-- A page's own laws on its write, old to new, on the states with the fields the laws read. -/
def judgeOwn (page : String) (lin : List (String × LawExpr)) (o n rq : Data) : Verdict :=
  if lin.isEmpty then .admitted
  else judge (rekey lin n).1 page lin (rekey lin o).2 (rekey lin n).2 rq

def ofLinkRefusal (pl : PageLaws) (r : LinkRefusal) : Refusal :=
  if r.law == "" then .undecided r.page r.reason
  else .law r.law pl.owner r.page (pl.text r.law) r.reason

/-- The laws over links of `page` judged at the pages `at_`. -/
def linksRefusal (s : VaultStore) (page : String) (pl : PageLaws) (rq : Data) (at_ : List String) :
    Option Refusal :=
  if pl.overLinks.isEmpty then none else (judgeLinksIn s page pl.overLinks rq at_).map (ofLinkRefusal pl)

/-- The laws over links of every page that links to `c`, judged at `c`. -/
def backlinkRefusal (book : LawBook) (s : VaultStore) (rq : Data) (c : String) : Option Refusal :=
  book.findSome? fun e => if e.1 != c && e.2.links.contains c then linksRefusal s e.1 e.2 rq [c] else none

/-- **The cone of a written cell**: its page's own laws, its laws over links at its links, and the
laws over links of the pages linking to it, on the store as written. -/
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
      | none => backlinkRefusal book s' rq d.cell

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

/-- **Admit a write**: its pins hold, its authority is live, every page in its cone consents. -/
def admitWrite (c : Config) (origin : String) (t : BTurn) : Except Refusal Config :=
  match pinRefusal c.store t.turn with
  | some r => .error r
  | none =>
  match authRefusal c.auth c.book t with
  | some r => .error r
  | none =>
  match t.turn.writeCells.findSome? (coneRefusal c.book (applyTurn c.store t.turn)
      (requestAt t.actor c.history.length)) with
  | some r => .error r
  | none => .ok { c with store := applyTurn c.store t.turn,
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

inductive Side
  | left
  | right
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

/-- **The tip**: the base with both sides' relaws (those that do not clash), grants and revocations
applied, the left's first. Every write of the merge is judged here. -/
def tipConfig (base : Config) (ln rn : String) (lnw rnw : List Act) : Run :=
  let held := lawClashes lnw rnw
  runActs (sideName ln rn) base
    ((lnw.filter (!heldRelaw held ·)).map (.left, ·) ++ (rnw.filter (!heldRelaw held ·)).map (.right, ·))

/-- The cells where two writes clash at a law book: one writes what the other touches. -/
def clash (book : LawBook) (a b : BTurn) : List String :=
  ((a.writes.filter fun c => (b.access book).contains c) ++
    (b.writes.filter fun c => (a.access book).contains c)).eraseDups

/-- The writes of the left that clash with no write of the right. -/
def freeLeft (book : LawBook) (lw rw : List BTurn) : List BTurn :=
  lw.filter fun a => rw.all fun b => (clash book a b).isEmpty

def freeRight (book : LawBook) (lw rw : List BTurn) : List BTurn :=
  rw.filter fun b => lw.all fun a => (clash book a b).isEmpty

def writeConflicts (book : LawBook) (ln rn : String) (lw rw : List BTurn) : List Conflict :=
  lw.flatMap fun a => rw.filterMap fun b =>
    let cs := clash book a b
    if cs.isEmpty then none else some (.writes cs (ln, a) (rn, b))

/-- A merge: the tip configuration, what landed, what was refused and why, the conflicts. -/
structure Merged where
  tip : Config
  landed : List (Side × Act)
  refused : List (Side × String × Refusal)
  conflicts : List Conflict

/-- **Merge two branches of `base`**: settle their non-write acts into the tip, keep the clashing
writes as conflicts, replay the others at the tip. A branch that did not fork from `base`'s history
is not merged. -/
def merge (base : Config) (L R : Branch) : Except String Merged :=
  if L.base ≠ base.history then .error (L.name ++ " did not fork from this history")
  else if R.base ≠ base.history then .error (R.name ++ " did not fork from this history")
  else
    let t := tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)
    let book := t.config.book
    let lw := writesOf L.acts
    let rw := writesOf R.acts
    let cs := (lawClashes (nonWrites L.acts) (nonWrites R.acts)).map (fun p => Conflict.laws p L.name R.name) ++
      writeConflicts book L.name R.name lw rw
    let w := runWrites (sideName L.name R.name) t.config
      ((freeLeft book lw rw).map (.left, ·) ++ (freeRight book lw rw).map (.right, ·))
    .ok ⟨{ w.config with conflicts := w.config.conflicts ++ cs }, t.landed ++ w.landed,
      t.refused ++ w.refused, cs⟩

/-- **Resolve** the `k`th open conflict (from 0) by landing one candidate at the configuration as it
is; the other candidate is dropped, and the receipt says so. -/
def resolve (c : Config) (k : Nat) (pick : Side) : Except String Config :=
  match c.conflicts[k]? with
  | some (.writes _ (ln, l) (rn, r)) =>
    let (o, t, dropped) := match pick with
      | .left => (ln, l, rn ++ "'s " ++ r.label)
      | .right => (rn, r, ln ++ "'s " ++ l.label)
    match admitWrite { c with conflicts := c.conflicts.eraseIdx k } o
        { t with label := t.label ++ " (resolving; dropped " ++ dropped ++ ")" } with
    | .ok c' => .ok c'
    | .error e => .error e.text
  | some (.laws p _ _) => .error ("the conflict at the laws of " ++ p ++ " is resolved by its owner's relaw")
  | none => .error ("no open conflict " ++ toString k)

/-! ## What a write's admission says -/

theorem admitWrite_ok {c c' : Config} {o : String} {t : BTurn} (h : admitWrite c o t = .ok c') :
    pinRefusal c.store t.turn = none ∧ authRefusal c.auth c.book t = none ∧
    t.turn.writeCells.findSome? (coneRefusal c.book (applyTurn c.store t.turn)
      (requestAt t.actor c.history.length)) = none ∧
    c' = { c with store := applyTurn c.store t.turn,
                  history := c.history ++ [receiptOf c o t.label t.writes] } := by
  unfold admitWrite at h
  split at h
  · cases h
  · rename_i hp
    split at h
    · cases h
    · rename_i ha
      split at h
      · cases h
      · rename_i hc
        cases h
        exact ⟨hp, ha, hc, rfl⟩

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
      p.2.denote facts (some (rekey ql.overLinks x).2) (rekey ql.overLinks x).2 = true)

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
        refine ⟨hown, linksRefusal_none hl', ?_⟩
        intro q ql hq hne hlink p hp
        have hb := List.findSome?_eq_none_iff.1 hr (q, ql) hq
        simp only at hb
        have hcond : (q != d.cell && ql.links.contains d.cell) = true := by
          simp [hne, hlink]
        rw [ite_eq_left hcond] at hb
        exact linksRefusal_none hb d.cell (List.mem_singleton_self _) p hp

/-- **A write admitted is consented to by its cone**: every law of every page in the cone of every
cell it writes holds, at the configuration it was admitted at. -/
theorem admitWrite_consents {c c' : Config} {o : String} {t : BTurn} (h : admitWrite c o t = .ok c') :
    ∀ d ∈ t.turn.writeCells, Consents c.book c'.store (factsAt c.history.length) d := by
  obtain ⟨_, _, hc, rfl⟩ := admitWrite_ok h
  intro d hd
  exact coneRefusal_none (List.findSome?_eq_none_iff.1 hc d hd)

/-! ## Runs -/

theorem admitWrite_keeps {c c' : Config} {o : String} {t : BTurn} (h : admitWrite c o t = .ok c') :
    c'.book = c.book ∧ c'.auth = c.auth ∧ c'.conflicts = c.conflicts := by
  obtain ⟨_, _, _, rfl⟩ := admitWrite_ok h
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

theorem merge_ok {base : Config} {L R : Branch} {m : Merged} (h : merge base L R = .ok m) :
    L.base = base.history ∧ R.base = base.history ∧
    let t := tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)
    let book := t.config.book
    let lw := writesOf L.acts
    let rw := writesOf R.acts
    let cs := (lawClashes (nonWrites L.acts) (nonWrites R.acts)).map (fun p => Conflict.laws p L.name R.name) ++
      writeConflicts book L.name R.name lw rw
    let w := runWrites (sideName L.name R.name) t.config
      ((freeLeft book lw rw).map (.left, ·) ++ (freeRight book lw rw).map (.right, ·))
    m = ⟨{ w.config with conflicts := w.config.conflicts ++ cs }, t.landed ++ w.landed,
      t.refused ++ w.refused, cs⟩ := by
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
theorem merge_landed_write {base : Config} {L R : Branch} {m : Merged} (h : merge base L R = .ok m)
    {sd : Side} {t : BTurn} (ht : (sd, .write t) ∈ m.landed) :
    ∃ c₀ c₁, c₀.book = m.tip.book ∧ c₀.auth = m.tip.auth ∧
      admitWrite c₀ (sideName L.name R.name sd) t = .ok c₁ := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  simp only at ht ⊢
  rcases List.mem_append.1 ht with ht | ht
  · exact absurd ht (tip_landed_not_write nonWrites_isWrite nonWrites_isWrite)
  · obtain ⟨ib, ia, _, il⟩ := runWrites_landed (name := sideName L.name R.name)
      (c := (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config)
      (xs := ((freeLeft (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config.book
          (writesOf L.acts) (writesOf R.acts)).map (.left, ·) ++
        (freeRight (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config.book
          (writesOf L.acts) (writesOf R.acts)).map (.right, ·)))
    obtain ⟨sd', t', he, _, c₀, c₁, h0b, h0a, h0⟩ := il _ ht
    cases he
    exact ⟨c₀, c₁, h0b.trans ib.symm, h0a.trans ia.symm, h0⟩

/-- **Settlement at the tip.** A write a merge landed relied only on sturdyrefs live at the tip, and
every page it wrote is its actor's or granted to it by one of them, live at the tip: authority read
where every revocation of both sides is visible, never on the write's own branch. -/
theorem settled_at_tip {base : Config} {L R : Branch} {m : Merged} (h : merge base L R = .ok m)
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
theorem tip_sees_every_revocation {base : Config} {L R : Branch} {m : Merged} (h : merge base L R = .ok m)
    {sd : Side} {l w u : String} (hr : (sd, .revoke l w u) ∈ m.landed) : m.tip.auth.isRevoked u = true := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  simp only at hr ⊢
  obtain ⟨_, ia, _, il⟩ := runWrites_landed (name := sideName L.name R.name)
    (c := (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config)
    (xs := ((freeLeft (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config.book
        (writesOf L.acts) (writesOf R.acts)).map (.left, ·) ++
      (freeRight (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config.book
        (writesOf L.acts) (writesOf R.acts)).map (.right, ·)))
  rw [ia]
  rcases List.mem_append.1 hr with hr | hr
  · exact runActs_revocation_visible hr
  · obtain ⟨_, _, he, _⟩ := il _ hr
    cases he

/-- **A sturdyref revoked on either side carries no write into the merge**: no write relying on it
lands, whichever side wrote it and whatever its own branch said. -/
theorem revoked_elsewhere_never_lands {base : Config} {L R : Branch} {m : Merged}
    (h : merge base L R = .ok m) {sd sd' : Side} {l w u : String} (hr : (sd', .revoke l w u) ∈ m.landed)
    {t : BTurn} (hu : u ∈ t.relies) : (sd, .write t) ∉ m.landed := by
  intro ht
  have hlive := (settled_at_tip h ht).1 u hu
  have hrev := tip_sees_every_revocation h hr
  simp [Authority.live, hrev] at hlive

/-- **A landed write is consented to by its cone at the tip**: by every law of every page in the cone
of every cell it writes, read from the tip's law book. -/
theorem landed_consents {base : Config} {L R : Branch} {m : Merged} (h : merge base L R = .ok m)
    {sd : Side} {t : BTurn} (ht : (sd, .write t) ∈ m.landed) :
    ∃ s' height, ∀ d ∈ t.turn.writeCells, Consents m.tip.book s' (factsAt height) d := by
  obtain ⟨c₀, c₁, hb, _, h0⟩ := merge_landed_write h ht
  refine ⟨c₁.store, c₀.history.length, ?_⟩
  rw [← hb]
  exact admitWrite_consents h0

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
      obtain ⟨_, _, _, rfl⟩ := admitWrite_ok hc
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

theorem mem_clash {book : LawBook} {a b : BTurn} {c : String} :
    c ∈ clash book a b ↔ (c ∈ a.writes ∧ c ∈ b.access book) ∨ (c ∈ b.writes ∧ c ∈ a.access book) := by
  unfold clash
  simp [List.mem_eraseDups, List.mem_filter]

/-- Writes with no clash: neither writes a cell the other touches. -/
theorem clash_nil_iff {book : LawBook} {a b : BTurn} :
    (clash book a b).isEmpty = true ↔
      (∀ c ∈ a.writes, c ∉ b.access book) ∧ (∀ c ∈ b.writes, c ∉ a.access book) := by
  rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h
    exact ⟨fun c ha hb => h c (mem_clash.2 (.inl ⟨ha, hb⟩)),
      fun c hb ha => h c (mem_clash.2 (.inr ⟨hb, ha⟩))⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases mem_clash.1 hc with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact h1 c ha hb
    · exact h2 c hb ha

theorem freeLeft_sub {book : LawBook} {lw rw : List BTurn} {a : BTurn} (h : a ∈ freeLeft book lw rw) :
    a ∈ lw ∧ ∀ b ∈ rw, (clash book a b).isEmpty = true := by
  unfold freeLeft at h
  obtain ⟨ha, hall⟩ := List.mem_filter.1 h
  exact ⟨ha, fun b hb => List.all_eq_true.1 hall b hb⟩

theorem freeRight_sub {book : LawBook} {lw rw : List BTurn} {b : BTurn} (h : b ∈ freeRight book lw rw) :
    b ∈ rw ∧ ∀ a ∈ lw, (clash book a b).isEmpty = true := by
  unfold freeRight at h
  obtain ⟨hb, hall⟩ := List.mem_filter.1 h
  exact ⟨hb, fun a ha => List.all_eq_true.1 hall a ha⟩

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

/-- **The merge is the pushout over the base.** The two sides' landed writes write disjoint cells,
and the tip's store is the left's landed writes on the cells they write, the right's on theirs, and
the base everywhere else: the one store that extends both along their writes. -/
theorem merge_is_pushout {base : Config} {L R : Branch} {m : Merged} (h : merge base L R = .ok m) :
    (∀ c ∈ writesAll (landedOn .left m.landed), c ∉ writesAll (landedOn .right m.landed)) ∧
    ∀ c, m.tip.store c =
      if c ∈ writesAll (landedOn .left m.landed) then applyAll base.store (landedOn .left m.landed) c
      else if c ∈ writesAll (landedOn .right m.landed) then applyAll base.store (landedOn .right m.landed) c
      else base.store c := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  simp only
  have hts := tip_store base L.name R.name L.acts R.acts
  have htl := tip_landed_nonwrites base L.name R.name L.acts R.acts
  generalize tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts) = t at hts htl ⊢
  generalize hlf : freeLeft t.config.book (writesOf L.acts) (writesOf R.acts) = lf
  generalize hrf : freeRight t.config.book (writesOf L.acts) (writesOf R.acts) = rf
  rw [runWrites_append]
  simp only
  generalize hr1 : runWrites (sideName L.name R.name) t.config (lf.map (Side.left, ·)) = r1
  generalize hr2 : runWrites (sideName L.name R.name) r1.config (rf.map (Side.right, ·)) = r2
  have h1 : ∀ x ∈ r1.landed, x.1 = .left := fun x hx => by
    obtain ⟨_, _, rfl⟩ := runWrites_landed_side (name := sideName L.name R.name) .left x (hr1 ▸ hx)
    rfl
  have h2 : ∀ x ∈ r2.landed, x.1 = .right := fun x hx => by
    obtain ⟨_, _, rfl⟩ := runWrites_landed_side (name := sideName L.name R.name) .right x (hr2 ▸ hx)
    rfl
  have hLL : landedOn .left (t.landed ++ (r1.landed ++ r2.landed)) = turnsOf r1.landed := by
    rw [landedOn_append, landedOn_append, landedOn_nonwrites _ htl, (landedOn_side .left h1).1,
      (landedOn_side .right h2).2 .left (by decide)]
    simp
  have hRR : landedOn .right (t.landed ++ (r1.landed ++ r2.landed)) = turnsOf r2.landed := by
    rw [landedOn_append, landedOn_append, landedOn_nonwrites _ htl, (landedOn_side .left h1).2 .right (by decide),
      (landedOn_side .right h2).1]
    simp
  rw [hLL, hRR]
  have hsub1 : ∀ a ∈ turnsOf r1.landed, a ∈ lf := by
    intro a ha
    obtain ⟨sd, hx⟩ := mem_turnsOf ha
    obtain ⟨a', ha', he⟩ := runWrites_landed_side (name := sideName L.name R.name) .left _ (hr1 ▸ hx)
    cases he; exact ha'
  have hsub2 : ∀ b ∈ turnsOf r2.landed, b ∈ rf := by
    intro b hb
    obtain ⟨sd, hx⟩ := mem_turnsOf hb
    obtain ⟨b', hb', he⟩ := runWrites_landed_side (name := sideName L.name R.name) .right _ (hr2 ▸ hx)
    cases he; exact hb'
  have hdisj : ∀ c ∈ writesAll (turnsOf r1.landed), c ∉ writesAll (turnsOf r2.landed) := by
    intro c hc hc'
    simp only [writesAll, List.mem_flatMap] at hc hc'
    obtain ⟨a, ha, hca⟩ := hc
    obtain ⟨b, hb, hcb⟩ := hc'
    have ha' := hsub1 a ha
    have hb' := hsub2 b hb
    rw [← hlf] at ha'
    rw [← hrf] at hb'
    have hcl := (freeLeft_sub ha').2 b (freeRight_sub hb').1
    exact (clash_nil_iff.1 hcl).1 c hca (writes_sub_access _ b c hcb)
  have hs1 : r1.config.store = applyAll base.store (turnsOf r1.landed) := by
    rw [← hr1, runWrites_store, hts]
  have hs2 : r2.config.store = applyAll r1.config.store (turnsOf r2.landed) := by
    rw [← hr2, runWrites_store]
  refine ⟨hdisj, fun c => ?_⟩
  rw [hs2]
  split
  · rename_i hc
    rw [applyAll_not_mem (hdisj c hc), hs1]
  · split
    · rename_i _ hc
      exact applyAll_mem hc
    · rename_i hc1 hc2
      rw [applyAll_not_mem hc2, hs1, applyAll_not_mem hc1]

/-! ### A conflict is a state -/

/-- **A clashing pair is a conflict kept in the tip's state, and neither write lands.** -/
theorem clash_is_conflict_state {base : Config} {L R : Branch} {m : Merged} (h : merge base L R = .ok m)
    {a b : BTurn} (ha : a ∈ writesOf L.acts) (hb : b ∈ writesOf R.acts)
    (hc : (clash (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config.book a b).isEmpty = false) :
    Conflict.writes (clash (tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts)).config.book a b)
        (L.name, a) (R.name, b) ∈ m.tip.conflicts ∧
      (Side.left, Act.write a) ∉ m.landed ∧ (Side.right, Act.write b) ∉ m.landed := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  simp only
  have htl := tip_landed_nonwrites base L.name R.name L.acts R.acts
  generalize tipConfig base L.name R.name (nonWrites L.acts) (nonWrites R.acts) = t at hc htl ⊢
  refine ⟨?_, ?_, ?_⟩
  · refine List.mem_append_right _ (List.mem_append_right _ ?_)
    unfold writeConflicts
    refine List.mem_flatMap.2 ⟨a, ha, List.mem_filterMap.2 ⟨b, hb, ?_⟩⟩
    simp [hc]
  · intro hl
    rcases List.mem_append.1 hl with hl | hl
    · have := htl _ hl; simp [Act.isWrite] at this
    · rw [runWrites_append] at hl
      rcases List.mem_append.1 hl with hl | hl
      · obtain ⟨t', ht', he⟩ := runWrites_landed_side (name := sideName L.name R.name) .left _ hl
        cases he
        have hfree := (freeLeft_sub ht').2 b hb
        rw [hc] at hfree; cases hfree
      · obtain ⟨t', _, he⟩ := runWrites_landed_side (name := sideName L.name R.name) .right _ hl
        cases he
  · intro hl
    rcases List.mem_append.1 hl with hl | hl
    · have := htl _ hl; simp [Act.isWrite] at this
    · rw [runWrites_append] at hl
      rcases List.mem_append.1 hl with hl | hl
      · obtain ⟨t', _, he⟩ := runWrites_landed_side (name := sideName L.name R.name) .left _ hl
        cases he
      · obtain ⟨t', ht', he⟩ := runWrites_landed_side (name := sideName L.name R.name) .right _ hl
        cases he
        have hfree := (freeRight_sub ht').2 a ha
        rw [hc] at hfree; cases hfree

/-! ### The history -/

theorem admitAct_extends {c c' : Config} {o : String} {a : Act} (h : admitAct c o a = .ok c') :
    c.history <+: c'.history := by
  cases a with
  | write t => obtain ⟨_, _, _, rfl⟩ := admitWrite_ok (show admitWrite c o t = .ok c' from h); exact List.prefix_append _ _
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
theorem merge_extends_history {base : Config} {L R : Branch} {m : Merged} (h : merge base L R = .ok m) :
    base.history <+: m.tip.history := by
  obtain ⟨_, _, hm⟩ := merge_ok h
  subst hm
  exact runActs_extends.trans runWrites_extends

/-! ### What a branch cannot learn of the other side's hidden cells -/

/-- **Confinement of the store.** If two right branches have the same name and the same non-write
acts, every write of either accesses only cells of `H` (at the tip's law book), and no write of the
left accesses a cell of `H`, then the left's landed writes are the same against both, and the tip
agrees outside `H`. What the right wrote inside `H` does not reach the left's view of the store. -/
theorem merge_confines_hidden {base : Config} {L R₁ R₂ : Branch} {m₁ m₂ : Merged} {H : List String}
    (h₁ : merge base L R₁ = .ok m₁) (h₂ : merge base L R₂ = .ok m₂)
    (hname : R₁.name = R₂.name) (hacts : nonWrites R₁.acts = nonWrites R₂.acts)
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
      freeLeft t.config.book (writesOf L.acts) rw = writesOf L.acts := by
    intro rw hrw
    unfold freeLeft
    rw [List.filter_eq_self]
    intro a ha
    rw [List.all_eq_true]
    intro b hb
    exact clash_nil_iff.2 ⟨fun c hc hcb => hL a ha c (writes_sub_access _ a c hc) (hrw b hb c hcb),
      fun c hc hca => hL a ha c hca (hrw b hb c (writes_sub_access _ b c hc))⟩
  rw [hfree _ hR₁, hfree _ hR₂, runWrites_append, runWrites_append]
  simp only
  generalize hr1 : runWrites (sideName L.name R₁.name) t.config ((writesOf L.acts).map (Side.left, ·)) = r1
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
  rw [hstore (freeRight t.config.book (writesOf L.acts) (writesOf R₁.acts))
      (fun b hb => hR₁ b (freeRight_sub hb).1) c hc,
    hstore (freeRight t.config.book (writesOf L.acts) (writesOf R₂.acts))
      (fun b hb => hR₂ b (freeRight_sub hb).1) c hc]

/-! ## Teeth -/

/- Removing the tip check (`authRefusal` always passing) loses `settled_at_tip`'s proof. -/
#tooth settled_at_tip by mutation authRefusal := fun _ _ _ => none

end Obend.Vault.Branch
