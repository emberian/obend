module
/-
# Obend.Vault.Store — the world kept beside a vault, and what each command does to it

A vault is a directory of markdown; the world beside it (`.obend/`) is a `Store`: every page's
history of versions (graphs, `Obend.Doc`), the text it last read or wrote for the page (`seen`), who
added each atom, and the members with their grants. Every command is a pure function of the store
and the files; `Obend.Vault.Cli` reads and writes them.

* `openVault`: every file whose text is not what the store last saw is a write by the owner: an edit
  of an existing page (`editPatch`, the file lined up against the current rendering) or the birth of
  a new one (`readPage`). Each write is judged by the page's laws (`commit`); an admitted write is a
  new version, a refused one is recorded with its refusal and changes nothing else. Then each page
  is rendered at its current version, and a file is written where its text differs (`writesFor`).
  **Opening twice is a no-op** (`open_idem`): the second open finds every file as the first left it
  and changes neither the store nor any file. This holds for every store and every vault the reader
  accepts (page names unique, as a directory's paths are).
* `mergeFrom`: each page of another replica's store (an offline copy, another process) is merged
  into this one by the pushout of the two current versions (`mergePage_pushout`); a page the other
  has alone is imported. Two replicas that edited one place differently leave a section with two
  candidates, rendered with the command that selects one.
* `postAs`: a member's proposal for a page becomes candidates in sections (`postPatch`); it needs the
  member's `post` grant on the page.
* `selectIn`: keep one candidate of a section (`selectPatch`); the owner, or a member with a `select`
  grant on the page (`select_needs_grant`). The candidate kept stays alive (`select_keeps`).
* `reciteIn`: re-justify the cites of a page that are behind (or unverified) against their sources'
  current versions, and resolve the links that dangled.

Every write goes through `commit`, which judges it by the page's laws and its kinds'
(`Obend.Vault.Law.judge`), and refuses a change of a law line by anyone but the owner (or a member
granted `relaw`).
-/
public import Obend.Vault.Law
public import Obend.Kind.Proofs
public import Obend.Vault.Hyperedge
@[expose] public section

namespace Obend.Vault

set_option autoImplicit false

open Obend.Doc Obend.Doc.Graph Obend.Digest.HashBytes
open Obend.Spec.Law (LawExpr Facts)

/-! ## The store -/

/-- A page of the vault. -/
structure Page where
  name : String
  id : PageId
  /-- its versions, oldest first; empty while its birth has been refused -/
  history : List Graph
  /-- the text the store last read from, or wrote to, its file -/
  seen : Option String
  /-- who added each atom (an atom not listed is the owner's) -/
  authors : List (AtomId × String)
  /-- the last refusal of a write to it -/
  note : Option String
  /-- the pin of its kind (`Obend.Kind.KindPin`): the versions of its kind and of every kind on its
  kind's precedence list when it was born or last adopted its laws; none for a page of no kind -/
  kind : Option Obend.Kind.KindPin := none
deriving Repr

/-- A member: a name, an id (the owner is 0), and grants `(verb, page pattern)`. -/
structure Member where
  name : String
  id : Nat
  grants : List (String × String)
deriving Repr, DecidableEq

structure Store where
  pages : List Page := []
  members : List Member := []
  turn : Nat := 0
  /-- pages whose files were deleted (`forgetMissing`): kept with their history but out of the
  world, so a cite of one fails `missing`; revived when a file returns under their name, or under
  a new name carrying their last text (a rename) -/
  tombs : List Page := []
deriving Repr

def Page.current (p : Page) : Option Graph := p.history.getLast?

/-- Who added an atom. -/
def Page.who (p : Page) (a : AtomId) : String := (p.authors.lookup a).getD "owner"

/-- The page rendered at its current version. -/
def Page.render? (p : Page) : Option String := p.current.map fun G => render G p.name p.who

/-- The world the store keeps: each page's history, by id. -/
def Store.world (s : Store) : World := fun q =>
  match s.pages.find? (·.id == q) with
  | some p => p.history
  | none => []

def Store.page? (s : Store) (name : String) : Option Page := s.pages.find? (·.name == name)

/-! ## Names -/

/-- A page's name's last path component. -/
def baseName (name : String) : String := ((name.splitOn "/").getLast?).getD name

/-- The folder of a page (`""` at the vault's top). -/
def folderOf (name : String) : String := "/".intercalate (name.splitOn "/").dropLast

/-- A page is a kind when it is a folder's `_kind` or under `_kind/`: a kind cell, with its own law lines, and the
initial fields of the pages born under it. -/
def isKind (name : String) : Bool := baseName name == "_kind" || name.startsWith "_kind/"

/-- The folder kinds of a page, innermost first: its folder's `_kind`, then each enclosing
folder's. A kind page itself is an instance of none. -/
def kindsOf (name : String) : List String :=
  if isKind name then [] else
  let parts := (name.splitOn "/").dropLast
  ((List.range (parts.length + 1)).reverse.map fun k =>
    "/".intercalate (parts.take k ++ ["_kind"]))

/-- A kind's own ancestors: the kinds of the folders enclosing its folder. -/
def kindParents (k : String) : List String :=
  if folderOf k == "" then [] else kindsOf (folderOf k)

/-- The kind a page names in its frontmatter (`kind: K`): the identity it carries. -/
def kindLine (src : String) : Option String :=
  ((frontFields src).find? (·.1 == "kind")).map (·.2)

/-- A kind named by a person: the kind page `K` itself, or a folder `K`'s `_kind`. -/
def kindName (k : String) : String := if isKind k then k else (if k == "" then "_kind" else k ++ "/_kind")

/-- A page's id: a hash of its name (so two replicas name a page alike), the first not taken. -/
def pageIdFor (H : Hash) (taken : PageId → Bool) (name : String) : PageId :=
  freshId H taken ("page:" ++ name)

/-! ## Resolving a wikilink -/

/-- What a new cite of a page quotes: the page, the version a new cite names, and that version. -/
structure Entry where
  name : String
  id : PageId
  graph : Graph
  version : Nat

/-- A page by name: exactly, or by its last path component when that is unique. -/
def findEntry (es : List Entry) (name : String) : Option Entry :=
  match es.find? (·.name == name) with
  | some e => some e
  | none => match es.filter (baseName ·.name == name) with
    | [e] => some e
    | _ => none

/-- The resolver of `Obend.Doc.readPage` over the entries, its byte cites committed under `H`. -/
def resolveIn (H : Hash) (es : List Entry) : Resolve := fun name sp =>
  (findEntry es name).bind fun e =>
    match sp with
    | .identity => some ⟨e.id, .identity, 0, [], .following⟩
    | _ => (quoteOf e.graph sp).map fun b => ⟨e.id, sp, e.version, H b, .following⟩

/-- The page a markdown text reads as, before its cites are committed (its bytes are its text's). -/
def draft (md : String) : Graph :=
  Graph.empty.apply (chain root (contents (fun _ sp => some ⟨0, sp, 0, [], .following⟩) (stripToks (tokens md))))

/-- The entries of a store's pages at their current versions. -/
def Store.entries (s : Store) : List Entry :=
  s.pages.filterMap fun p => p.current.map fun G => ⟨p.name, p.id, G, p.history.length - 1⟩

/-! ## Members and grants -/

/-- A grant's page pattern: `*`, a page name, or `folder/*`. -/
def patternMatches (pat page : String) : Bool :=
  pat == "*" || pat == page ||
    (pat.endsWith "/*" && page.startsWith (String.ofList (pat.toList.dropLast)))

/-- The member may do `verb` (`post`, `select`, `relaw`) to the page. -/
def Member.may (m : Member) (verb page : String) : Bool :=
  m.grants.any fun g => g.1 == verb && patternMatches g.2 page

def Store.member? (s : Store) (name : String) : Option Member := s.members.find? (·.name == name)

/-- Who acts: the owner, or a member. -/
inductive Actor
  | owner
  | member (m : Member)

def Actor.name : Actor → String
  | .owner => "owner"
  | .member m => m.name

def Actor.id : Actor → Nat
  | .owner => 0
  | .member m => m.id

def Actor.may : Actor → String → String → Bool
  | .owner, _, _ => true
  | .member m, verb, page => m.may verb page

/-! ## Laws, and the commit every write goes through -/

/-- A LAW OVER LINKS reads `linked.F`: its subject is every page the page links to, not the page
(see "Laws over links" below). -/
def isLinkLaw (txt : String) : Bool := (txt.splitOn "linked.").length > 1

/-- The text of a law over links as the fragment parses it: `linked.F` is the field `F` of the
state it is judged on, the linked page's. -/
def linkLawText (txt : String) : String := txt.replace "linked." "new."

/-- The laws of a page as written in a version, each named `PAGE: NAME`, with its text. A law over
links reads the linked page only: one that also reads `new.` is refused. -/
def lawsIn (pageName : String) (G : Graph) : Except String (List (String × LawExpr × String)) :=
  (lawLines (settled G)).mapM fun (n, txt) =>
    if isLinkLaw txt && (txt.splitOn "new.").length > 1 then
      .error (pageName ++ ": law " ++ n ++ ": a law over links reads the linked page as `linked.`; \
        the page's own fields (`new.`) are not readable in it")
    else match Obend.Spec.Law.parse (if isLinkLaw txt then linkLawText txt else txt) with
    | .ok e => .ok (pageName ++ ": " ++ n, e, txt)
    | .error msg => .error (pageName ++ ": law " ++ n ++ ": " ++ msg)

/-! ## The vault's kinds are kind cells

Decided 2026-11-01 (C1; `lean/docs/REPORT-PARSIMONY-20261101.md`'s decision): a vault's `_kind`
pages are registered as kind cells of `Obend.Kind`, with the page's law lines as the cell's law and
its fields as its layout. The registry resolves a page's kind to a pin (its kind's version and every
ancestor's), linearizes the hierarchy by C4 (a kind page may name several parents, `parents: a, b`;
one that names none has its nearest enclosing folder's kind as its parent), and a pin goes stale when
any kind it rests on is revised (`Obend.Kind.Proofs.kind_stale_iff_blocked`). This replaces the
folder chain (`kindChain`, `kindLaws`) the vault computed on its own. -/

/-- The laws of a page or a kind: `(PAGE: NAME, expression, text)`. -/
abbrev Laws := List (String × LawExpr × String)

/-- The kinds a kind page names as its parents (`parents: a, b`), each a kind name. -/
def parentsLine (src : String) : Option (List String) :=
  ((frontFields src).find? (·.1 == "parents")).map fun (_, v) =>
    (((v.splitOn ",").map fun t => t.trimAscii.toString).filter (!·.isEmpty)).map kindName

/-- A kind page's parents: those it names, or else the nearest enclosing folder's kind the vault
holds. -/
def kindParentsIn (es : List Entry) (k src : String) : List String :=
  match parentsLine src with
  | some ps => ps
  | none => ((kindParents k).filter fun x => es.any (·.name == x)).take 1

/-- **The vault's kind registry**: each `_kind` page at its current version, a kind cell whose law is
its law lines and whose layout and initial state are its other fields. -/
def vaultKinds (es : List Entry) : Except String (Obend.Kind.Kinds Laws) := do
  let cells ← (es.filter fun e => isKind e.name).mapM fun e => do
    let src := settled e.graph
    let laws ← lawsIn e.name e.graph
    let fields := (frontFields src).filter fun f => (lawKey f.1).isNone && f.1 != "kind" && f.1 != "parents"
    let init : Obend.Core.Data.Data := .record (fields.map fun f => (f.1, Obend.Core.Data.Data.label f.2))
    let cell : Obend.Kind.KindCell Laws :=
      ⟨e.name, e.version, fields.map (·.1), init, laws, kindParentsIn es e.name src, [], [laws]⟩
    pure cell
  pure ⟨cells⟩

/-- The kind a page is an instance of: the one it names (`kind: K`, carried by every page born under
`K`), else its nearest folder's kind the vault holds. A kind page is an instance of none. -/
def pageKind (es : List Entry) (name src : String) : Option String :=
  if isKind name then none else
  match kindLine src with
  | some k => some (kindName k)
  | none => (kindsOf name).find? fun x => es.any (·.name == x)

/-- A refusal of the kind registry, said to a person. -/
def kindRefusalText : Obend.Kind.Refusal → String
  | .unknown k => "refused (unknown-kind): no kind page " ++ k
  | .stale p => "refused (stale-kind): " ++ p.name ++ " was revised"
  | .cycle k => "refused (kind-cycle): " ++ k ++ " is its own ancestor"
  | .c4 k _ => "refused (kind-order): the parents of " ++ k ++ " have no C4 order"
  | .law _ => "refused (kind-law)"
  | .clash n => "refused (kind-clash): " ++ n ++ " is a kind"

/-- What a page's laws rest on: its kind's pin at the vault's registry, the kinds on its kind's
precedence list (its kind first), and their laws in that order. -/
structure KindsOf where
  pin : Option Obend.Kind.KindPin
  chain : List String
  laws : Laws

/-- **A page's kinds**: its kind resolved at the vault's registry, linearized by C4. -/
def kindsFor (es : List Entry) (name src : String) : Except String KindsOf :=
  match pageKind es name src with
  | none => .ok ⟨none, [], []⟩
  | some k =>
    match vaultKinds es with
    | .error e => .error e
    | .ok ks =>
      match Obend.Kind.resolve ks k with
      | .error e => .error (kindRefusalText e)
      | .ok pin =>
        let chain := pin.lineage.map (·.name)
        .ok ⟨some pin, chain, chain.flatMap fun x => ((ks.find x).map (·.law)).getD []⟩

/-- A page's kinds, its kind first (for the analyses that ask which kind pages a page's laws read). -/
def kindChain (es : List Entry) (name src : String) : List String :=
  match kindsFor es name src with
  | .ok K => K.chain
  | .error _ => []

/-- The laws a write of `pageName` (at version `G`) is judged by: its own, then its kinds' (its kind
first, along the C4 precedence list). A kind page's own law lines are the laws of the pages born
under it, not of the kind page: a kind whose instances must be dated (`not (new.date == 0)`) starts
them at `date: 0` and is itself born (2026-11-04; before, a kind was judged by its own law lines, so
such a kind could not be born). A kind page is judged by the kinds above it. -/
def ownLaws (pageName : String) (G : Graph) : Except String Laws :=
  if isKind pageName then .ok [] else lawsIn pageName G

def lawsFor (es : List Entry) (pageName : String) (G : Graph) : Except String Laws := do
  let own ← ownLaws pageName G
  let kinds ← kindsFor es pageName (settled G)
  return own ++ kinds.laws

/-- Every law of every kind on a page's chain is among the kinds' laws it collects. -/
theorem kindsFor_laws {es : List Entry} {name src : String} {K : KindsOf} (h : kindsFor es name src = .ok K)
    {ks : Obend.Kind.Kinds Laws} (hks : vaultKinds es = .ok ks) :
    ∀ k ∈ K.chain, ∀ c, ks.find k = some c → ∀ x ∈ c.law, x ∈ K.laws := by
  unfold kindsFor at h
  split at h
  · cases h; intro k hk; cases hk
  · rw [hks] at h
    simp only at h
    split at h
    · cases h
    · cases h
      intro k hk c hc x hx
      exact List.mem_flatMap.2 ⟨k, hk, by simp [hc, hx]⟩

/-- **A kind's laws are an ancestor's**: every law of every kind on a page's precedence list (its
kind first) is among the laws its writes are judged by. -/
theorem lawsFor_kinds {es : List Entry} {name : String} {G : Graph} {laws : Laws}
    (h : lawsFor es name G = .ok laws) {K : KindsOf} (hK : kindsFor es name (settled G) = .ok K)
    {ks : Obend.Kind.Kinds Laws} (hks : vaultKinds es = .ok ks) :
    ∀ k ∈ K.chain, ∀ c, ks.find k = some c → ∀ x ∈ c.law, x ∈ laws := by
  unfold lawsFor at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rw [hK] at h
    cases h
    intro k hk c hc x hx
    exact List.mem_append_right _ (kindsFor_laws hK hks k hk c hc x hx)

/-- **What a vault write is admitted by, its kinds' laws hold of** (`judge_admits`): a write judged
by a page's laws and admitted satisfies, by the fragment's meaning, every law of every kind on the
page's precedence list, its own kind first. -/
theorem kind_law_inherited {es : List Entry} {name : String} {G : Graph} {laws : Laws}
    (hl : lawsFor es name G = .ok laws) {K : KindsOf} (hK : kindsFor es name (settled G) = .ok K)
    {ks : Obend.Kind.Kinds Laws} (hks : vaultKinds es = .ok ks)
    {S : Obend.Core.Ty.Ty} {o n : Obend.Core.Data.Data} {facts : Facts} {who : String} {k : Occ}
    (hj : judge S name (laws.map fun x => (x.1, x.2.1)) o n (requestOf who k facts) = .admitted) :
    ∀ kk ∈ K.chain, ∀ c, ks.find kk = some c → ∀ x ∈ c.law, x.2.1.denote facts (k.old o n) n = true := by
  intro kk hkk c hc x hx
  exact judge_admits hj (x.1, x.2.1) (List.mem_map.2 ⟨x, lawsFor_kinds hl hK hks kk hkk c hc x hx, rfl⟩)

/-- **A write keeps the page's laws** when its law lines and the kind it names are as they were. The
kind line is compared, not only the law lines: retargeting `kind:` changes the kind
(`pageKind`), and so the laws a page is judged by (Kimi's review, 2026-11-01). -/
def lawsKept (old new : String) : Bool :=
  lawLines old == lawLines new && kindLine old == kindLine new

/-- A page's laws read its source only through its law lines and its kind line. -/
theorem lawsFor_of_kept (es : List Entry) (name : String) {G G' : Graph}
    (h : lawsKept (settled G) (settled G') = true) : lawsFor es name G = lawsFor es name G' := by
  simp only [lawsKept, Bool.and_eq_true, beq_iff_eq] at h
  simp only [lawsFor, ownLaws, lawsIn, kindsFor, pageKind, h.1, h.2]

/-- Kept laws keep the kinds. -/
theorem kindChain_of_kept (es : List Entry) (name : String) {old new : String} (h : lawsKept old new = true) :
    kindChain es name old = kindChain es name new := by
  simp only [lawsKept, Bool.and_eq_true, beq_iff_eq] at h
  simp only [kindChain, kindsFor, pageKind, h.2]

-- Comparing the law lines alone lets a write retarget its kind and be judged by the old kind's laws.
#tooth lawsFor_of_kept by mutation lawsKept := fun old new => lawLines old == lawLines new

/-- **A page's pin goes stale exactly when a kind it rests on is revised**, its blocked read naming
the kinds that moved (`Obend.Kind.kind_stale_iff_blocked` at the vault's registry). -/
theorem page_kind_stale_iff_blocked (ks : Obend.Kind.Kinds Laws) (p : Obend.Kind.KindPin) :
    Obend.Kind.kindRefs.current ks p = false ↔
      ((Obend.Kind.kindRefs (Law := Laws)).slot p.name).read (Obend.Kind.holds ks) (some p) =
        .blocked p (p.lineage.filter fun f => !Obend.Kind.holds ks f) :=
  Obend.Kind.kind_stale_iff_blocked ks p

/-- The kinds a pin rests on that the vault's registry has revised. -/
def movedKinds (es : List Entry) (p : Obend.Kind.KindPin) : List Obend.Kind.KindVersion :=
  match vaultKinds es with
  | .ok ks => p.lineage.filter fun f => !Obend.Kind.holds ks f
  | .error _ => []

/-- What a write leaves of a page. -/
structure Change where
  history : List Graph
  seen : String
  authors : List (AtomId × String)
  note : Option String
  /-- the page's kind pin after the write -/
  kind : Option Obend.Kind.KindPin

def Page.withChange (p : Page) (c : Change) : Page :=
  { p with history := c.history, seen := some c.seen, authors := c.authors, note := c.note, kind := c.kind }

/-- A law named `PAGE: NAME`, said from the page `pageName` it binds: `its law NAME`, or the law
with its owner and, for a kind's, whose kind that is. -/
def lawOwnerText (pageName law : String) : String :=
  let owner := ((law.splitOn ": ").head?).getD law
  let kindNote := if owner != pageName && isKind owner then
      " (the kind of " ++ (if folderOf owner == "" then "the vault" else folderOf owner ++ "/") ++
        ", an ancestor of " ++ pageName ++ ")"
    else ""
  if owner == pageName then "its law " ++ String.ofList ((law.toList.drop (owner.length + 2)))
  else law ++ kindNote

/-- Why a write was refused, said to a person. -/
def refusalText (pageName : String) (laws : List (String × LawExpr × String)) (law reason : String)
    (facts : Facts) (old : Option Obend.Core.Data.Data) (new : Obend.Core.Data.Data) (front : List String) : String :=
  match laws.find? (·.1 == law) with
  | some (_, e, txt) =>
    "refused by " ++ lawOwnerText pageName law ++ ": `" ++ txt ++ "` does not hold; " ++ suggest e facts old new front
  | none => "refused by " ++ lawOwnerText pageName law ++ ": " ++ reason

/-! ## Laws over links

A law that reads `linked.F` is a LAW OVER LINKS: its subject is not the page but every page the page
links to (`[[Page]]`, an identity cite, what the `links` measure counts), and it is judged at each
of them, on that page's state, on two occasions: a write of the page (at its links as they stand)
and a write of a linked page (at that page as written, under the laws over links of every page that
links to it). So one write is judged by a fact about two pages: a ledger's `law dated: not
(linked.date == 0)` says every page it lists is dated, and a listed page cannot lose its date.
A law over links reads the linked page (`linked.`, never `new.`) and the request; `monotone` and
`writeOnce` in it are judged as identity writes. It inherits along kinds as any law line does.

The pages a judgment read are the write's footprint. `writeTurn` records the write as a
`VaultTurn` (`Obend.Vault.Hyperedge`): the page written is its one write cell (its state before and
after), and every page its laws over links read is a read pin at the state read. The judgment reads
the store the turn's pins and write describe (`applyTurn turn.readPins.store turn`), and
`judgeLinksIn_of_turn` says it equals the judgment on any store where the pins hold; that is the
premise `no_toctou` asks of a turn judged at one store and admitted at another. -/

/-- The pages a version links to by identity cite, each once, in order. -/
def linkTargets (G : Graph) : List PageId :=
  ((settledAtoms G).filterMap fun a => match G.label a with
    | some (.cite _ c) => if c.span = .identity then some c.page else none
    | _ => none).eraseDups

/-- The entries a version links to, each once. -/
def linkedEntries (es : List Entry) (G : Graph) : List Entry :=
  (linkTargets G).filterMap fun q => es.find? (·.id == q)

/-- The laws over links among a page's laws, as the judge takes them. -/
def linkLaws (laws : Laws) : List (String × LawExpr) :=
  (laws.filter fun l => isLinkLaw l.2.2).map fun (n, e, _) => (n, e)

/-- A page's state from its measures, by name. -/
def stateOfMs (ms : List (String × Nat)) : Obend.Core.Data.Data := stateOf (sortNames (ms.map (·.1))) ms

/-- A state with the fields a law reads added, at 0 where the state has none (`stateOf`'s default):
its keys and itself. -/
def rekey (lin : List (String × LawExpr)) : Obend.Core.Data.Data → List String × Obend.Core.Data.Data
  | .record fs =>
    let vals := fs.filterMap fun (k, d) => match d with | .natural n => some (k, n) | _ => none
    let keys := sortNames (vals.map (·.1) ++ lin.flatMap fun l => l.2.fields)
    (keys, stateOf keys vals)
  | d => ([], d)

/-- Why a judgment over links refused: the page it was at, that page's state (none: it has no
version), the law and the reason. -/
structure LinkRefusal where
  page : String
  state : Option Obend.Core.Data.Data
  law : String
  reason : String

/-- Judge the laws over links `lin` (named under `pkg`) at each page of `cells`, on the state `store`
holds for it: the first refusal, if any. A page the store has no state for cannot be judged and is
refused as such. -/
def judgeLinksIn (store : VaultStore) (pkg : String) (lin : List (String × LawExpr))
    (rq : Obend.Core.Data.Data) : List String → Option LinkRefusal
  | [] => none
  | c :: rest =>
    match store c with
    | none => some ⟨c, none, "", "the linked page " ++ c ++ " has no version to judge"⟩
    | some d =>
      let (keys, n) := rekey lin d
      match judge (stateTy keys) pkg lin n n rq with
      | .admitted => judgeLinksIn store pkg lin rq rest
      | .refused law why => some ⟨c, some n, law, why⟩
      | .undecided why => some ⟨c, some n, "", why⟩

/-- The store a footprint's pins describe: each pinned page at its observed state. -/
def Footprint.store (fp : Footprint) : VaultStore := fun c =>
  (fp.find? (·.cell == c)).bind (·.observed)

/-- Where a footprint holds, the store reads at its pins as the pins say. -/
theorem Footprint.store_of_holds {store : VaultStore} {fp : Footprint} (h : Footprint.Holds store fp) :
    ∀ p ∈ fp, store p.cell = fp.store p.cell := by
  intro p hp
  induction fp with
  | nil => cases hp
  | cons q fp ih =>
    simp only [Footprint.store]
    by_cases hq : q.cell = p.cell
    · rw [List.find?_cons_of_pos (by simp [hq])]
      simp only [Option.bind_some]
      rw [← hq]
      exact h q (List.mem_cons_self ..)
    · rw [List.find?_cons_of_neg (by simp [hq])]
      have hp' : p ∈ fp := by
        rcases List.mem_cons.1 hp with rfl | hp'
        · exact absurd rfl hq
        · exact hp'
      exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) hp'

/-- **A turn reads its own footprint**: at a page the turn pins or writes, the store after the turn
is what the turn's pins and write say, wherever the pins hold. -/
theorem applyTurn_pin {store : VaultStore} {turn : VaultTurn} (h : Footprint.Holds store turn.readPins)
    {c : String} (hc : c ∈ turn.readFootprint ∨ c ∈ turn.writeFootprint) :
    applyTurn store turn c = applyTurn turn.readPins.store turn c := by
  unfold applyTurn
  cases hf : turn.writeCells.find? (fun d => d.cell == c) with
  | some d => rfl
  | none =>
    rcases hc with hr | hw
    · simp only [VaultTurn.readFootprint, List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      exact Footprint.store_of_holds h p hp
    · exfalso
      simp only [VaultTurn.writeFootprint, List.mem_map] at hw
      obtain ⟨d, hd, rfl⟩ := hw
      have := List.find?_eq_none.1 hf d hd
      simp at this

/-- **The verdict over links is the turn's**: judged at pages the turn pins or writes, on any store
where its pins hold, the laws over links say what they say on the store the turn describes. -/
theorem judgeLinksIn_of_turn {store : VaultStore} {turn : VaultTurn} (h : Footprint.Holds store turn.readPins)
    (pkg : String) (lin : List (String × LawExpr)) (rq : Obend.Core.Data.Data) :
    ∀ cells : List String, (∀ c ∈ cells, c ∈ turn.readFootprint ∨ c ∈ turn.writeFootprint) →
      judgeLinksIn (applyTurn store turn) pkg lin rq cells =
        judgeLinksIn (applyTurn turn.readPins.store turn) pkg lin rq cells
  | [], _ => rfl
  | c :: rest, hc => by
    have ih := judgeLinksIn_of_turn h pkg lin rq rest fun x hx => hc x (List.mem_cons_of_mem _ hx)
    simp only [judgeLinksIn]
    rw [applyTurn_pin h (hc c (List.mem_cons_self ..))]
    cases applyTurn turn.readPins.store turn c with
    | none => rfl
    | some d =>
      simp only
      split
      · exact ih
      · rfl
      · rfl

/-- The write of `page` as a turn: its one write cell is the page (its state before and after), its
read pins the pages its laws over links read, at the states read. -/
def writeTurn (page : String) (o n : Obend.Core.Data.Data) (linked : List Entry)
    (rq : Obend.Core.Data.Data) : VaultTurn where
  turnId := ByteArray.empty
  readPins := linked.map fun e => ⟨e.name, some (stateOfMs (measures e.graph e.version))⟩
  writeCells := [{ cell := page, preState := o, postState := n }]
  occasion := rq
  agree := by
    intro d hd
    simp only [List.mem_singleton] at hd
    subst hd
    rfl
  balanced := by
    intro asset
    simp [sumAssetDelta, deltaAsset]
  nodup_cells := by simp

/-- The frontmatter fields among a state's keys: the keys that are not measures. -/
def frontOf (n : Obend.Core.Data.Data) : List String :=
  match n with
  | .record fs => (fs.map (·.1)).filter fun k => !measureNames.contains k
  | _ => []

/-- Why a page's law over its links refused, at a page it links to. -/
def linkRefusalText (pageName : String) (laws : Laws) (r : LinkRefusal) (facts : Facts) : String :=
  match r.state, laws.find? (·.1 == r.law) with
  | some n, some (_, e, txt) =>
    "refused by " ++ lawOwnerText pageName r.law ++ " over its links, at " ++ r.page ++ ": `" ++ txt ++
      "` does not hold there; " ++ suggest e facts none n (frontOf n)
  | _, _ => "refused by " ++ lawOwnerText pageName r.law ++ " over its links, at " ++ r.page ++ ": " ++ r.reason

/-- Why another page's law over its links refused this write, which that page links to. -/
def backlinkRefusalText (linker pageName : String) (laws : Laws) (r : LinkRefusal) (facts : Facts)
    (new : Obend.Core.Data.Data) (front : List String) : String :=
  let who := r.law ++ " (a law over " ++ linker ++ "'s links, of which " ++ pageName ++ " is one)"
  match laws.find? (·.1 == r.law) with
  | some (_, e, txt) => "refused by " ++ who ++ ": `" ++ txt ++ "` does not hold; " ++ suggest e facts none new front
  | none => "refused by " ++ who ++ ": " ++ r.reason

/-- Why a stale kind refuses a write, said to a person. -/
def staleText (pageName who : String) (moved : List Obend.Kind.KindVersion) : String :=
  "refused (stale-kind): the kinds " ++ pageName ++ " was pinned to were revised since (" ++
    ", ".intercalate (moved.map fun f => f.name ++ " at v" ++ toString (f.version + 1)) ++
    "); adopting their laws is the owner's (" ++ who ++ " has no relaw grant on " ++ pageName ++ ")"

/-- **Commit a write**: judge the new version `G'` of page `p` by its laws, and on admission append
it, pinning its kind at the vault's registry. A change of a law line or of the kind the page names
is the owner's, or a member's granted `relaw`; it is judged as the adoption of the new laws over the
page as written. So is a write to a page whose kind pin is stale (a kind it rests on was revised,
`movedKinds`): the owner's write adopts the revised kinds' laws and renews the pin; anyone else's is
refused, naming the kinds that moved. Otherwise the laws are kept (`lawsKept`), and the new laws are
the old ones (`lawsFor_of_kept`). A birth is judged as a first write. The new state carries the
write's own measures (`deletions`, `insertions`: how it changed the current version); the old state
has none (0). -/
def commit (es : List Entry) (p : Page) (G' : Graph) (added : List (AtomId × String)) (who : Actor)
    (turn : Nat) : Except String Change := do
  let authors := p.authors ++ added
  let p' := { p with authors := authors }
  let v := p.history.length
  let newLaws ← lawsFor es p.name G'
  let kinds ← kindsFor es p.name (settled G')
  let moved := match p.kind with
    | some old => movedKinds es old
    | none => []
  let (occ, laws, oldMs) ← match p.current with
    | none => pure (Occ.birth, newLaws, [])
    | some G =>
      if lawsKept (settled G) (settled G') && moved.isEmpty then pure (Occ.write, newLaws, measures G (v - 1))
      else if who.may "relaw" p.name then pure (Occ.adopt, newLaws, measures G (v - 1))
      else if lawsKept (settled G) (settled G') then throw (staleText p.name who.name moved)
      else throw ("refused: changing a law line or the page's kind is the owner's (" ++ who.name ++
        " has no relaw grant on " ++ p.name ++ ")")
  let newMs := measures G' v ++ writeMeasures p.current G'
  let lin := (laws.filter fun l => !isLinkLaw l.2.2).map fun (n, e, _) => (n, e)
  let keys := sortNames (newMs.map (·.1) ++ oldMs.map (·.1) ++ lin.flatMap fun l => l.2.fields)
  let S := stateTy keys
  let n := stateOf keys newMs
  let o := if oldMs.isEmpty then n else stateOf keys oldMs
  let facts : Facts := ⟨some who.id, some who.id, v, turn⟩
  let rq := requestOf who.name occ facts
  match judge S p.name lin o n rq with
  | .admitted =>
    -- the laws over links, judged through the write's turn: this page's at the pages it links to,
    -- and every linking page's at this page as written
    let wt := writeTurn p.name (stateOfMs oldMs) (stateOfMs newMs) (linkedEntries es G') rq
    let world := applyTurn wt.readPins.store wt
    let mine := linkLaws laws
    if let some r := (if mine.isEmpty then none else judgeLinksIn world p.name mine rq wt.readFootprint) then
      throw (linkRefusalText p.name laws r facts)
    for e in es do
      if e.name != p.name && (linkTargets e.graph).contains p.id then
        match lawsFor es e.name e.graph with
        | .ok elaws =>
          let theirs := linkLaws elaws
          if let some r := (if theirs.isEmpty then none else judgeLinksIn world e.name theirs rq [p.name]) then
            throw (backlinkRefusalText e.name p.name elaws r facts (stateOfMs newMs)
              ((scalarFields (settled G')).map (·.1)))
        | .error _ => pure ()
    pure ⟨p.history ++ [G'], render G' p.name p'.who, authors, none, kinds.pin⟩
  | .refused law reason =>
    throw (refusalText p.name laws law reason facts (occ.old o n) n
      ((scalarFields (settled G')).map (·.1)))
  | .undecided why => throw ("undecided: " ++ why)

/-- **Retargeting the kind needs the grant**: a write that changes the kind a page names, by an actor
without `relaw` on the page, is refused, whatever its law lines. -/
theorem commit_kind_needs_relaw (es : List Entry) (p : Page) (G G' : Graph) (added : List (AtomId × String))
    (who : Actor) (turn : Nat) (hc : p.current = some G) (hk : kindLine (settled G) ≠ kindLine (settled G'))
    (hw : who.may "relaw" p.name = false) : ∃ msg, commit es p G' added who turn = .error msg := by
  have hkept : lawsKept (settled G) (settled G') = false := by
    simp [lawsKept, hk]
  unfold commit
  cases lawsFor es p.name G' with
  | error m => exact ⟨m, rfl⟩
  | ok newLaws =>
    cases kindsFor es p.name (settled G') with
    | error m => exact ⟨m, rfl⟩
    | ok kinds =>
      simp only [bind, Except.bind, hc, hkept, hw, Bool.false_and, Bool.false_eq_true, if_false]
      exact ⟨_, rfl⟩

/-- **A stale kind needs the grant**: a write to a page whose kind pin rests on a revised kind, by an
actor without `relaw` on the page, is refused (`staleText` names the kinds that moved). -/
theorem commit_stale_needs_relaw (es : List Entry) (p : Page) (G G' : Graph) (added : List (AtomId × String))
    (who : Actor) (turn : Nat) (hc : p.current = some G) {old : Obend.Kind.KindPin} (hp : p.kind = some old)
    (hm : (movedKinds es old).isEmpty = false)
    (hw : who.may "relaw" p.name = false) : ∃ msg, commit es p G' added who turn = .error msg := by
  unfold commit
  cases lawsFor es p.name G' with
  | error m => exact ⟨m, rfl⟩
  | ok newLaws =>
    cases kindsFor es p.name (settled G') with
    | error m => exact ⟨m, rfl⟩
    | ok kinds =>
      simp only [bind, Except.bind, hc, hp, hm, hw, Bool.and_false, Bool.false_eq_true, if_false]
      split <;> exact ⟨_, rfl⟩

/-! ## Open -/

/-- The owner's write of the text `md` to page `p`: the file lined up against the current rendering,
or a birth. A refused write records the refusal and the text it refused. -/
def ownerWrite (H : Hash) (es : List Entry) (turn : Nat) (p : Page) (md : String) : Change :=
  let cs := contents (resolveIn H es) (stripToks (tokens md))
  let (G', added, same) : Graph × List AtomId × Bool := match p.current with
    | none => (Graph.empty.apply (chain root cs), [], false)
    | some G =>
      let b := editPatch H G (align (pieces G p.name p.who) cs) "owner"
      (G.apply b.ops, b.added, b.ops.isEmpty)
  -- Only the view's marks changed (one deleted, say), or a refused edit was put back: nothing to
  -- write; the view is redrawn, and the page's last write is no longer a refused one.
  if same then ⟨p.history, md, p.authors, none, p.kind⟩ else
  match commit es p G' (added.map (·, "owner")) .owner turn with
  | .ok ch => ch
  | .error msg => ⟨p.history, md, p.authors, some msg, p.kind⟩

/-- One page at open: unchanged if its file is missing or is what the store last saw, unless its
last write was refused: a refusal may rest on another page (a law over links), and that page may
have been mended since, so a refused write is tried again at every open that is not quiet. -/
def openPage (H : Hash) (es : List Entry) (turn : Nat) (p : Page) (file : Option String) : Page :=
  match file with
  | none => p
  | some md => if some md == p.seen && p.note.isNone then p else p.withChange (ownerWrite H es turn p md)

/-- The vault is QUIET for the store: every page's file is missing or is what the store last saw,
and every file is a page's. -/
def quiet (s : Store) (V : List (String × String)) : Bool :=
  s.pages.all (fun p => match V.lookup p.name with
    | none => true
    | some md => some md == p.seen) &&
  V.all fun e => s.pages.any (·.name == e.1)

/-- The text to write to a page's file: what the store holds for it, where the file differs. -/
def writeOf (V : List (String × String)) (p : Page) : Option String :=
  match V.lookup p.name, p.seen with
  | some md, some t => if md == t then none else some t
  | _, _ => none

/-- The files to write: each page whose file differs from the text the store holds for it. -/
def writesFor (s : Store) (V : List (String × String)) : List (String × String) :=
  s.pages.filterMap fun p => (writeOf V p).map fun t => (p.name, t)

/-- The vault after the writes. -/
def overwrite (V w : List (String × String)) : List (String × String) :=
  V.map fun e => (e.1, (w.lookup e.1).getD e.2)

/-- New pages for the files the store does not have, each with a fresh id. -/
def freshPages (H : Hash) (s : Store) (names : List String) : List Page :=
  (names.foldl (fun (acc : List Page) n =>
    let taken := fun q => s.pages.any (·.id == q) || acc.any (·.id == q)
    acc ++ [⟨n, pageIdFor H taken n, [], none, [], none, none⟩]) [])

/-- The entries new cites resolve against at an open: a page whose file changed quotes the file
(the version it is about to become), the others their current version. -/
def openEntries (pages : List Page) (V : List (String × String)) : List Entry :=
  pages.filterMap fun p =>
    match V.lookup p.name with
    | some md => if some md == p.seen then p.current.map fun G => ⟨p.name, p.id, G, p.history.length - 1⟩
      else some ⟨p.name, p.id, draft md, p.history.length⟩
    | none => p.current.map fun G => ⟨p.name, p.id, G, p.history.length - 1⟩

/-! ### Settling: links that resolve now, and the view redrawn -/

/-- What a link written as text should become now that its page may exist: the cite it resolves
to, or nothing. -/
def danglingOf (H : Hash) (es : List Entry) : Content → Option Content
  | .text t =>
    match tokens t with
    | [.link n] => let (pg, sp) := target false n
      (resolveIn H es (String.ofList pg) sp).map fun ct => .cite (String.ofList n) ct
    | [.embed n] => let (pg, sp) := target true n
      (resolveIn H es (String.ofList pg) sp).map fun ct => .cite (String.ofList n) ct
    | _ => none
  | _ => none

/-- Replace each atom of a version that `sel` says should hold something else, in place. -/
def replaceAll (H : Hash) (G : Graph) (ps : List Piece) (sel : Content → Option Content) (who : String) :
    Graph × List AtomId × Nat :=
  ps.foldl (fun (acc : Graph × List AtomId × Nat) pc =>
    match pc with
    | .atom a _ => match (G.label a).bind sel with
      | some c => let b := replacePatch H acc.1 a (atomAfter ps a) c who
        (acc.1.apply b.ops, acc.2.1 ++ b.added, acc.2.2 + 1)
      | none => acc
    | _ => acc) (G, [], 0)

/-- A page whose links dangled when written and whose pages now exist: those links resolved, a
write by the owner (judged like any). A page whose last write was refused is left alone, so the
text the person typed stays in its file. -/
def fixDangling (H : Hash) (s : Store) (p : Page) : Page :=
  if p.note.isSome then p else
  match p.current with
  | none => p
  | some G =>
    let (G', added, n) := replaceAll H G (pieces G p.name p.who) (danglingOf H s.entries) "owner"
    if n = 0 then p else
    match commit s.entries p G' (added.map (·, "owner")) .owner s.turn with
    | .ok ch => p.withChange ch
    | .error _ => p

/-- The page's text at the current view: its current version, each cite whose facts fail marked
with their names (`Obend.Doc.viewAtom`: `![[Beta]]{behind}`). -/
def Page.view (H : Hash) (s : Store) (p : Page) : Option String :=
  p.current.map fun G => renderWith (viewAtom H s.world G) G p.name p.who

/-- The text the store holds for a page's file becomes its view (unless its last write was refused:
then the file keeps what the person typed). -/
def remarkPage (H : Hash) (s : Store) (p : Page) : Page :=
  if p.note.isSome then p else
  match p.view H s with
  | some t => { p with seen := some t }
  | none => p

/-- **Settle** a store: resolve the links that now resolve, then redraw every page's view. -/
def settle (H : Hash) (s : Store) : Store :=
  let s1 : Store := { s with pages := s.pages.map (fixDangling H s) }
  { s1 with pages := s1.pages.map (remarkPage H s1) }

theorem fixDangling_name (H : Hash) (s : Store) (p : Page) : (fixDangling H s p).name = p.name := by
  unfold fixDangling
  repeat (first | rfl | split)

theorem fixDangling_seen (H : Hash) (s : Store) (p : Page) (h : p.seen.isSome) :
    (fixDangling H s p).seen.isSome := by
  unfold fixDangling
  repeat (first | exact h | rfl | split)

theorem remarkPage_name (H : Hash) (s : Store) (p : Page) : (remarkPage H s p).name = p.name := by
  unfold remarkPage; split; · rfl
  split <;> rfl

theorem remarkPage_seen (H : Hash) (s : Store) (p : Page) (h : p.seen.isSome) :
    (remarkPage H s p).seen.isSome := by
  unfold remarkPage; split; · exact h
  split
  · rfl
  · exact h

theorem settle_names (H : Hash) (s : Store) : (settle H s).pages.map (·.name) = s.pages.map (·.name) := by
  simp [settle, List.map_map, Function.comp_def, remarkPage_name, fixDangling_name]

theorem settle_seen (H : Hash) (s : Store) :
    ∀ q ∈ (settle H s).pages, ∃ p ∈ s.pages, q.name = p.name ∧ (p.seen.isSome → q.seen.isSome) := by
  intro q hq
  simp only [settle, List.map_map, List.mem_map, Function.comp_apply] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact ⟨p, hp, by rw [remarkPage_name, fixDangling_name],
    fun h => remarkPage_seen _ _ _ (fixDangling_seen _ _ _ h)⟩

/-- What an open did. -/
structure Opened where
  store : Store
  writes : List (String × String)

/-- **Open a vault.** -/
def openVault (H : Hash) (s : Store) (V : List (String × String)) : Opened :=
  if quiet s V then ⟨s, []⟩ else
  let fresh := (V.filter fun e => !s.pages.any (·.name == e.1)).map (·.1)
  let all := s.pages ++ freshPages H s fresh
  let es := openEntries all V
  let pages := all.zipIdx.map fun (p, i) => openPage H es (s.turn + i) p (V.lookup p.name)
  let s' : Store := settle H { s with pages := pages, turn := s.turn + all.length }
  ⟨s', writesFor s' V⟩

/-! ### Files that are gone: deletions and renames -/

/-- What an open did about files that are gone. -/
structure Forgotten where
  store : Store
  /-- pages deleted: their files gone, moved to the tombs -/
  deleted : List String := []
  /-- pages renamed: a new file carrying a deleted page's last text, `(old name, new name)` -/
  renamed : List (String × String) := []
  /-- tombs revived by a file returning under their own name -/
  revived : List String := []
  /-- pages whose files are gone but which stay, each with the kind whose laws keep it -/
  kept : List (String × String) := []

/-- The kind laws a page is under (its own law lines go with its text; its kinds' do not), or
`none` when its kind does not resolve (then the page is kept, fail closed). -/
def kindLawsOf (s : Store) (p : Page) : Option Laws :=
  match p.current with
  | none => some []
  | some G =>
    match kindsFor s.entries p.name (settled G) with
    | .ok K => some K.laws
    | .error _ => none

/-- **Deleted and renamed files.** A page the store once saw whose file is gone is DELETED: it
moves to the tombs, out of the world (every cite of it fails `missing`; its history is kept), unless
a kind's laws govern it (a posting under the register's kind, a journal page under its kind): such a
page is not deleted by removing its file, and the open writes it back. A file new to the store that
carries a tomb's last text REVIVES that tomb under the new name (a rename: same id, same history, and
cites of it by other pages still hold); a file returning under a tomb's own name revives it there.
Pages the store has not written yet (never `seen`) are never deleted here: a page born this open has
no file to lose. -/
def forgetMissing (s : Store) (V : List (String × String)) : Forgotten := Id.run do
  let gone := s.pages.filter fun p => p.seen.isSome && (V.lookup p.name).isNone
  let mut kept : List (String × String) := []
  let mut deleted : List Page := []
  for p in gone do
    match kindLawsOf s p with
    | some [] => deleted := deleted ++ [p]
    | some ((law, _) :: _) =>
      kept := kept ++ [(p.name, "the law " ++ law)]
    | none => kept := kept ++ [(p.name, "a kind that does not resolve")]
  let mut pages := s.pages.filter fun p => !deleted.any (·.name == p.name)
  let mut tombs := s.tombs ++ deleted
  let mut renamed : List (String × String) := []
  let mut revived : List String := []
  for (n, md) in V do
    if pages.any (·.name == n) then continue
    match tombs.find? (·.name == n) with
    | some t =>
      pages := pages ++ [t]
      tombs := tombs.filter (·.name != n)
      revived := revived ++ [n]
    | none =>
      match tombs.find? (fun t => t.seen == some md) with
      | some t =>
        pages := pages ++ [{ t with name := n }]
        tombs := tombs.filter (·.name != t.name)
        renamed := renamed ++ [(t.name, n)]
      | none => pure ()
  return ⟨{ s with pages := pages, tombs := tombs }, deleted.map (·.name), renamed, revived, kept⟩

/-- A tomb's line in a status: its name and the version it was at. -/
def tombLine (p : Page) : String :=
  p.name ++ ": deleted (was v" ++ toString p.history.length ++ "; a file " ++ p.name ++
    ".md revives it, a new file with its text renames it)"

/-! ### Opening twice is a no-op -/

theorem openPage_name (H : Hash) (es : List Entry) (t : Nat) (p : Page) (f : Option String) :
    (openPage H es t p f).name = p.name := by
  unfold openPage; split
  · rfl
  · split <;> rfl

/-- After an open, a page whose file exists holds some text for it. -/
theorem openPage_seen (H : Hash) (es : List Entry) (t : Nat) (p : Page) (md : String) :
    ∃ u, (openPage H es t p (some md)).seen = some u := by
  simp only [openPage]
  by_cases h : (some md == p.seen && p.note.isNone) = true
  · rw [Bool.and_eq_true] at h
    simp only [h, and_self, ite_true]; exact ⟨md, (beq_iff_eq.1 h.1).symm⟩
  · simp only [h, Bool.false_eq_true, ite_false]; exact ⟨_, rfl⟩

theorem freshPages_names (H : Hash) (s : Store) (names : List String) :
    (freshPages H s names).map (·.name) = names := by
  unfold freshPages
  suffices ∀ (acc : List Page), (names.foldl (fun (acc : List Page) n =>
      let taken := fun q => s.pages.any (·.id == q) || acc.any (·.id == q)
      acc ++ [⟨n, pageIdFor H taken n, [], none, [], none, none⟩]) acc).map (·.name) = acc.map (·.name) ++ names by
    simpa using this []
  induction names with
  | nil => intro acc; simp
  | cons n ns ih => intro acc; rw [List.foldl_cons, ih]; simp

theorem lookup_overwrite (V w : List (String × String)) (n : String) :
    (overwrite V w).lookup n = (V.lookup n).map fun md => (w.lookup n).getD md := by
  induction V with
  | nil => rfl
  | cons e V ih =>
    obtain ⟨k, v⟩ := e
    simp only [overwrite, List.map_cons, List.lookup_cons] at ih ⊢
    by_cases h : n = k
    · subst h; simp
    · have : (n == k) = false := by simpa using h
      simp only [this]; exact ih

theorem overwrite_names (V w : List (String × String)) : (overwrite V w).map (·.1) = V.map (·.1) := by
  simp [overwrite, Function.comp_def]

theorem overwrite_nil (V : List (String × String)) : overwrite V [] = V := by
  simp [overwrite]

theorem lookup_filterMap_none {f : Page → Option String} {n : String} :
    ∀ (ps : List Page), n ∉ ps.map (·.name) →
      (ps.filterMap fun q => (f q).map fun t => (q.name, t)).lookup n = none
  | [], _ => rfl
  | q :: ps, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.filterMap_cons]
    cases f q with
    | none => exact lookup_filterMap_none ps h.2
    | some t =>
      have : (n == q.name) = false := by simpa using h.1
      simp only [Option.map_some, List.lookup_cons, this]
      exact lookup_filterMap_none ps h.2

/-- In a list of pages with distinct names, the entry found for a page's name is that page's. -/
theorem lookup_filterMap {f : Page → Option String} :
    ∀ (ps : List Page), (ps.map (·.name)).Nodup → ∀ p ∈ ps,
      (ps.filterMap fun q => (f q).map fun t => (q.name, t)).lookup p.name = f p
  | [], _, _, hp => by cases hp
  | q :: ps, hnd, p, hp => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.filterMap_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · cases hf : f p with
      | none => exact lookup_filterMap_none ps hnd.1
      | some t => simp
    · have hne : p.name ≠ q.name := fun h => hnd.1 (h ▸ List.mem_map_of_mem hp)
      have : (p.name == q.name) = false := by simpa using hne
      cases f q with
      | none => exact lookup_filterMap ps hnd.2 p hp
      | some t =>
        simp only [Option.map_some, List.lookup_cons, this]
        exact lookup_filterMap ps hnd.2 p hp

/-- After the writes, every page's file is what the store holds for it, and the vault is quiet. -/
theorem quiet_after_writes (s : Store) (V : List (String × String)) (hnd : (s.pages.map (·.name)).Nodup)
    (hseen : ∀ p ∈ s.pages, (V.lookup p.name).isSome → p.seen.isSome)
    (hcover : ∀ e ∈ V, e.1 ∈ s.pages.map (·.name)) :
    quiet s (overwrite V (writesFor s V)) = true := by
  simp only [quiet, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun p hp => ?_, fun e he => ?_⟩
  · rw [lookup_overwrite]
    cases hl : V.lookup p.name with
    | none => rfl
    | some md =>
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hseen p hp (by simp [hl]))
      have hw : (writesFor s V).lookup p.name = writeOf V p := lookup_filterMap s.pages hnd p hp
      simp only [Option.map_some, hw, writeOf, hl, ht]
      by_cases h : md = t
      · subst h; simp
      · have : (md == t) = false := by simpa using h
        simp [this]
  · have h1 : e.1 ∈ (overwrite V (writesFor s V)).map (·.1) := List.mem_map_of_mem he
    rw [overwrite_names] at h1
    obtain ⟨e', he', heq⟩ := List.mem_map.1 h1
    obtain ⟨p, hp, hn⟩ := List.mem_map.1 (hcover e' he')
    exact List.any_eq_true.2 ⟨p, hp, by simp [hn, heq]⟩

theorem nodup_fresh (s : Store) (V : List (String × String)) (hV : (V.map (·.1)).Nodup) :
    (((V.filter fun e => !s.pages.any (·.name == e.1)).map (·.1))).Nodup :=
  hV.sublist (List.Sublist.map _ List.filter_sublist)

/-- After settling and the writes, the vault is quiet: the view is what each file holds. -/
theorem quiet_after_settle (H : Hash) (s : Store) (V : List (String × String))
    (hnd : (s.pages.map (·.name)).Nodup)
    (hseen : ∀ p ∈ s.pages, (V.lookup p.name).isSome → p.seen.isSome)
    (hcover : ∀ e ∈ V, e.1 ∈ s.pages.map (·.name)) :
    quiet (settle H s) (overwrite V (writesFor (settle H s) V)) = true := by
  refine quiet_after_writes _ V (by rw [settle_names]; exact hnd) (fun q hq hl => ?_)
    (fun e he => by rw [settle_names]; exact hcover e he)
  obtain ⟨p, hp, hn, hs⟩ := settle_seen H s q hq
  exact hs (hseen p hp (hn ▸ hl))

/-- **Opening twice is a no-op.** For every store whose page names are distinct and every vault the
reader accepts (file names distinct, as a directory's are): open it, write the files the open says
to write, and open again; the second open changes neither the store nor any file. -/
theorem open_idem (H : Hash) (s : Store) (V : List (String × String))
    (hs : (s.pages.map (·.name)).Nodup) (hV : (V.map (·.1)).Nodup) :
    openVault H (openVault H s V).store (overwrite V (openVault H s V).writes) =
      ⟨(openVault H s V).store, []⟩ := by
  by_cases hq : quiet s V = true
  · simp only [openVault, hq, ite_true, overwrite_nil]
  · have hq' : quiet s V = false := by simpa using hq
    simp only [openVault, hq', Bool.false_eq_true, ite_false]
    generalize hfresh : (V.filter fun e => !s.pages.any (·.name == e.1)).map (·.1) = fresh
    generalize hall : s.pages ++ freshPages H s fresh = all
    generalize hps : (all.zipIdx.map fun (x : Page × Nat) =>
      openPage H (openEntries all V) (s.turn + x.2) x.1 (V.lookup x.1.name)) = pages
    have hnames : pages.map (·.name) = s.pages.map (·.name) ++ fresh := by
      rw [← hps, ← hall, List.map_map]
      have : ((·.name) ∘ fun (x : Page × Nat) =>
          openPage H (openEntries (s.pages ++ freshPages H s fresh) V) (s.turn + x.2) x.1 (V.lookup x.1.name)) =
          (·.name) ∘ Prod.fst := by
        funext x; simp [openPage_name]
      rw [this, ← List.map_map, List.zipIdx_map_fst, List.map_append, freshPages_names]
    have hq2 : quiet (settle H { s with pages := pages, turn := s.turn + all.length })
        (overwrite V (writesFor (settle H { s with pages := pages, turn := s.turn + all.length }) V)) = true := by
      refine quiet_after_settle H _ V ?_ ?_ ?_
      · show (pages.map (·.name)).Nodup
        rw [hnames, List.nodup_append]
        refine ⟨hs, hfresh ▸ nodup_fresh s V hV, ?_⟩
        intro a ha b hb hab
        subst hab
        rw [← hfresh] at hb
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
        have := (List.mem_filter.1 he).2
        obtain ⟨p, hp, hpn⟩ := List.mem_map.1 ha
        simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at this
        exact this p hp hpn
      · intro p hp hl
        show p.seen.isSome
        rw [← hps] at hp
        obtain ⟨⟨q, i⟩, _, rfl⟩ := List.mem_map.1 hp
        simp only [openPage_name] at hl ⊢
        obtain ⟨md, hmd⟩ := Option.isSome_iff_exists.1 hl
        rw [hmd]
        obtain ⟨u, hu⟩ := openPage_seen H (openEntries all V) (s.turn + i) q md
        simp [hu]
      · intro e he
        show e.1 ∈ pages.map (·.name)
        rw [hnames, List.mem_append]
        by_cases h : s.pages.any (·.name == e.1) = true
        · obtain ⟨p, hp, hpn⟩ := List.any_eq_true.1 h
          exact .inl (List.mem_map.2 ⟨p, hp, by simpa using hpn⟩)
        · exact .inr (hfresh ▸ List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simpa using h⟩, rfl⟩)
    simp only [hq2, ite_true]

/-- An open writes a file only where the page's text in the store differs from it, and writes that
text. -/
theorem mem_writes {s : Store} {V : List (String × String)} {n t : String}
    (h : (n, t) ∈ writesFor s V) :
    ∃ p ∈ s.pages, p.name = n ∧ p.seen = some t ∧ ∃ md, V.lookup n = some md ∧ md ≠ t := by
  obtain ⟨p, hp, hw⟩ := List.mem_filterMap.1 h
  cases hwo : writeOf V p with
  | none => simp [hwo] at hw
  | some t' =>
    simp only [hwo, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨p, hp, rfl, ?_⟩
    unfold writeOf at hwo
    split at hwo
    · rename_i md t'' hl hs
      by_cases he : md = t''
      · subst he; simp at hwo
      · have : (md == t'') = false := by simpa using he
        simp only [this, Bool.false_eq_true, ite_false, Option.some.injEq] at hwo
        subst hwo
        exact ⟨hs, md, hl, he⟩
    · cases hwo

#tooth open_idem by mutation writesFor := fun _ _ => []
#tooth open_idem by mutation quiet := fun _ _ => false

/-! ## The other commands

Each takes the store as an open left it and returns the new store, or why it refused. -/

/-- Replace the page of that name. -/
def Store.setPage (s : Store) (p : Page) : Store :=
  { s with pages := s.pages.map fun q => if q.name == p.name then p else q, turn := s.turn + 1 }

/-- A write by `who` of the version `G'` of the page `p`, committed. -/
def Store.write (s : Store) (p : Page) (G' : Graph) (added : List (AtomId × String)) (who : Actor) :
    Except String Store := do
  match commit s.entries p G' added who s.turn with
  | .ok ch => return s.setPage (p.withChange ch)
  | .error msg => throw (p.name ++ ": " ++ msg)

/-! ### Merge -/

/-- `B ⊑ A`, decided: every atom, tombstone and edge of `B` is in `A`. -/
def leB (B A : Graph) : Bool :=
  B.atoms.all (fun e => A.label e.1 == B.label e.1) && B.dead.all A.isDead &&
    B.edges.all fun e => A.edge e.1 e.2

/-- The merge of two versions of a page: their union where they agree on every atom both store. -/
def mergePage (A B : Graph) : Option Graph := if compatB A B then some (Graph.merge A B) else none

/-- **The merge is the pushout** of the two versions: above both, below every page above both. -/
theorem mergePage_pushout {A B M : Graph} (h : mergePage A B = some M) : IsPushout A B M := by
  unfold mergePage at h
  split at h
  · rename_i hc; cases h; exact merge_isPushout (compatible_of_compatB hc)
  · cases h

/-- Merge the pages of another replica's store (`label` names it in the authors of what it added). -/
def mergeFrom (s o : Store) (label : String) : Store × List String := Id.run do
  let mut st := s
  let mut notes : Array String := #[]
  for q in o.pages do
    match st.page? q.name with
    | none =>
      if st.pages.any (·.id == q.id) then
        notes := notes.push (q.name ++ ": not imported: its id is another page's here")
      else if let some G := q.current then
        let authors := q.authors.map fun (a, w) => (a, if w == "owner" then "owner@" ++ label else w)
        let p : Page := { q with authors := authors, seen := some (render G q.name fun a => (authors.lookup a).getD ("owner@" ++ label)), note := none }
        st := { st with pages := st.pages ++ [p] }
        notes := notes.push (q.name ++ ": imported from " ++ label)
    | some p =>
      match p.current, q.current with
      | some A, some B =>
        if leB B A then pure ()
        else match mergePage A B with
          | none => notes := notes.push (p.name ++ ": not merged: the two versions name one atom differently (they share no base)")
          | some M =>
            let added := (B.atoms.map (·.1)).eraseDups.filter (fun a => !A.present a) |>.map fun a =>
              (a, match q.authors.lookup a with
                | some w => if w == "owner" then "owner@" ++ label else w
                | none => "owner@" ++ label)
            match st.write p M added .owner with
            | .ok st' =>
              let secs := (sections M).length
              notes := notes.push (p.name ++ ": merged from " ++ label ++
                (if secs = 0 then "" else ", " ++ toString secs ++ " section(s) to select"))
              st := st'
            | .error msg => notes := notes.push msg
      | _, _ => pure ()
  return (st, notes.toList)

/-! ### Members, posts and selections -/

/-- Add a member with grants. -/
def addMember (s : Store) (name : String) (grants : List (String × String)) : Except String Store :=
  if name == "owner" || s.members.any (·.name == name) then .error ("a member named " ++ name ++ " exists")
  else .ok { s with members := s.members ++ [⟨name, s.members.length + 1, grants⟩] }

/-- The actor named: the owner, or a member. -/
def Store.actor (s : Store) : Option String → Except String Actor
  | none => .ok .owner
  | some n => match s.member? n with
    | some m => .ok (.member m)
    | none => .error ("no member named " ++ n)

/-- **A member's post**: its proposed text of the page, as candidates in sections. -/
def postAs (H : Hash) (s : Store) (who : Actor) (page text : String) : Except String Store := do
  let some p := s.page? page | throw ("no page named " ++ page)
  unless who.may "post" page do
    throw (who.name ++ " may not post to " ++ page ++ " (no post grant)")
  let some G := p.current | throw (page ++ " has no version yet")
  let cs := contents (resolveIn H s.entries) (stripToks (tokens text))
  let b := postPatch H G (align (pieces G p.name p.who) cs) who.name
  if b.ops.isEmpty then throw ("nothing to post: the text is " ++ page ++ "'s")
  let added := b.added.map fun a => (a, if b.asIs.contains a then "as it is" else who.name)
  s.write p (G.apply b.ops) added who

/-- Section `k`, counted from 1: there is no section 0 (it would alias section 1). -/
def sectionAt (G : Graph) (k : Nat) : Option (List (AtomId × List Segment)) :=
  if 1 ≤ k then (sections G)[k - 1]? else none

theorem sectionAt_zero (G : Graph) : sectionAt G 0 = none := rfl

/-- **Select** candidate `i` (from 1) of section `k` (from 1) of a page. -/
def selectIn (s : Store) (who : Actor) (page : String) (k i : Nat) : Except String Store := do
  let some p := s.page? page | throw ("no page named " ++ page)
  unless who.may "select" page do
    throw (who.name ++ " may post to " ++ page ++ " but not select on it (no select grant)")
  let some G := p.current | throw (page ++ " has no version yet")
  let some alts := sectionAt G k | throw (page ++ " has no section " ++ toString k)
  unless 1 ≤ i && i ≤ alts.length do
    throw ("section " ++ toString k ++ " of " ++ page ++ " has " ++ toString alts.length ++ " candidates")
  s.write p (G.apply (selectPatch alts (i - 1))) [] who

/-- **There is no section 0**: selecting in it is refused, whatever the page. -/
theorem select_section_zero_refused (s : Store) (who : Actor) (page : String) (i : Nat) :
    ∃ msg, selectIn s who page 0 i = .error msg := by
  unfold selectIn
  cases s.page? page with
  | none => exact ⟨_, rfl⟩
  | some p =>
    simp only
    split
    · cases p.current with
      | none => exact ⟨_, rfl⟩
      | some G => exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

#tooth select_section_zero_refused by mutation sectionAt := fun G k => (sections G)[k - 1]?

/-- **A selection keeps its candidate**: every run the kept candidate shows is as it was. -/
theorem select_keeps (G : Graph) (alts : List (AtomId × List Segment)) (i : Nat) {a : AtomId}
    {h : AtomId} {keep : List Segment} (hi : alts[i]? = some (h, keep)) (ha : a ∈ segAtoms keep) :
    (G.apply (selectPatch alts i)).label a = G.label a ∧
      (G.apply (selectPatch alts i)).isDead a = G.isDead a := by
  refine apply_frame G _ fun hm => ?_
  simp only [selectPatch, hi, Patch.touches, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨o, ⟨b, hb, rfl⟩, ho⟩ := hm
  simp only [Op.touches, List.mem_singleton] at ho
  subst ho
  have := (List.mem_filter.1 (List.mem_eraseDups.1 hb)).2
  simp [ha] at this

/-- **Selecting needs the grant**: a member without a `select` grant on the page is refused, and the
store is unchanged. -/
theorem select_needs_grant (s : Store) (m : Member) (page : String) (k i : Nat)
    (hp : (s.page? page).isSome) (hm : m.may "select" page = false) :
    ∃ msg, selectIn s (.member m) page k i = .error msg := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hp
  simp [selectIn, hp, Actor.may, hm, Actor.name]
  exact ⟨_, rfl⟩

/-- **Posting needs the grant**, likewise. -/
theorem post_needs_grant (H : Hash) (s : Store) (m : Member) (page text : String)
    (hp : (s.page? page).isSome) (hm : m.may "post" page = false) :
    ∃ msg, postAs H s (.member m) page text = .error msg := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hp
  simp [postAs, hp, Actor.may, hm, Actor.name]
  exact ⟨_, rfl⟩

#tooth mergePage_pushout by mutation mergePage := fun A _ => some A
#tooth select_needs_grant by mutation Actor.may := fun _ _ _ => true
#tooth post_needs_grant by mutation Actor.may := fun _ _ _ => true

/-! ### Birth under a kind -/

/-- **`create --from K PAGE`**:
- When `PAGE` is an instance page (`isKind page = false`), returns the text of a page born under kind `K`:
  its frontmatter names `kind: K` and starts with `K`'s non-law fields; its body is empty.
- When `PAGE` is a kind page (`isKind page = true`, `K-KIND-CELL`), derives a child kind page from parent
  kind `K`: its frontmatter names `parents: K` and inherits `K`'s non-law fields AND `K`'s law lines. -/
def createFrom (s : Store) (k page : String) : Except String String := do
  let kn := kindName k
  if (s.page? page).isSome then throw ("refused: " ++ page ++ " exists")
  let some kp := s.page? kn | throw ("refused (unknown-kind): no kind page " ++ kn)
  let some G := kp.current | throw ("refused (unknown-kind): " ++ kn ++ " has no version")
  let fields := (frontFields (settled G)).filter fun (key, _) => (lawKey key).isNone && key != "kind" && key != "parents"
  if isKind page then
    if kn == page then throw ("refused (kind-cycle): " ++ page ++ " is its own ancestor")
    let laws := (frontFields (settled G)).filter fun (key, _) => (lawKey key).isSome
    return "---\nparents: " ++ kn ++ "\n" ++
      String.join (fields.map fun (key, v) => key ++ ": " ++ v ++ "\n") ++
      String.join (laws.map fun (key, v) => key ++ ": " ++ v ++ "\n") ++ "---\n"
  else
    return "---\nkind: " ++ kn ++ "\n" ++
      String.join (fields.map fun (key, v) => key ++ ": " ++ v ++ "\n") ++ "---\n"

/-- **`createFrom_kind_preserves_ancestor_laws` (`K-KIND-CELL`)**:
1. When `isKind page = true` and `createFrom s k page = .ok md`, `page` does not yet exist in `s`,
   parent kind `kn = kindName k` exists in `s` at version `G` with `kn ≠ page`, and `md` is the
   derived child kind markdown naming `parents: <kn>` and inheriting both `kn`'s layout fields and
   all of `kn`'s law lines.
2. Any write to an instance page `instName` (version `G_inst`) whose resolved kind chain `K.chain`
   includes both `page` and its ancestor `kindName k` is required to satisfy every law of `page`
   AND every law of `kindName k`. -/
theorem createFrom_kind_preserves_ancestor_laws
    {s : Store} {k page md : String}
    (hkind : isKind page = true)
    (hcf : createFrom s k page = .ok md) :
    (s.page? page).isSome = false ∧
    kindName k ≠ page ∧
    (∃ kp G,
      s.page? (kindName k) = some kp ∧
      kp.current = some G ∧
      let fields := (frontFields (settled G)).filter fun (key, _) => (lawKey key).isNone && key != "kind" && key != "parents"
      let laws := (frontFields (settled G)).filter fun (key, _) => (lawKey key).isSome
      md = "---\nparents: " ++ kindName k ++ "\n" ++
        String.join (fields.map fun (key, v) => key ++ ": " ++ v ++ "\n") ++
        String.join (laws.map fun (key, v) => key ++ ": " ++ v ++ "\n") ++ "---\n") ∧
    (∀ (es : List Entry) (instName : String) (G_inst : Graph) (laws : Laws)
       (K : KindsOf) (ks : Obend.Kind.Kinds Laws)
       (S : Obend.Core.Ty.Ty) (o n : Obend.Core.Data.Data) (facts : Facts) (who : String) (occ : Occ),
      lawsFor es instName G_inst = .ok laws →
      kindsFor es instName (settled G_inst) = .ok K →
      vaultKinds es = .ok ks →
      judge S instName (laws.map fun x => (x.1, x.2.1)) o n (requestOf who occ facts) = .admitted →
      kindName k ∈ K.chain →
      ∀ cParent, ks.find (kindName k) = some cParent →
      ∀ x ∈ cParent.law, x.2.1.denote facts (occ.old o n) n = true) := by
  unfold createFrom at hcf
  simp only [bind, Except.bind, pure, Except.pure, hkind, ite_true] at hcf
  split at hcf
  · cases hcf
  · rename_i hpage_none
    split at hcf
    · rename_i kp hkp
      split at hcf
      · rename_i G hG
        split at hcf
        · cases hcf
        · rename_i hne
          cases hcf
          have hne' : kindName k ≠ page := by
            intro heq
            exact hne (beq_iff_eq.2 heq)
          refine ⟨by simpa using hpage_none, hne', ⟨kp, G, hkp, hG, rfl⟩, ?_⟩
          intro es instName G_inst laws K ks S o n facts who occ hl hK hks hj hmem cParent hcParent x hx
          exact kind_law_inherited hl hK hks hj (kindName k) hmem cParent hcParent x hx
      · cases hcf
    · cases hcf

/-! ### Re-citing -/

/-- Whether a cite holds at the store's world: the cite intention's `current` (`Obend.Doc.cites`). -/
def Store.citeHolds (H : Hash) (s : Store) (c : Cite) : Bool := (cites H).current s.world c

/-- What an atom should hold now: a cite re-justified against its source's current version, or a
dangling wikilink resolved; `none` when it is fine as it is. -/
def reciteOf (H : Hash) (s : Store) (c : Content) : Option Content :=
  let es := s.entries
  match c with
  | .cite n ct =>
    if s.citeHolds H ct then none else
    let (pg, sp) := target (ct.span == .page) n.toList
    (resolveIn H es (String.ofList pg) sp).map fun ct' => .cite n ct'
  | .text t =>
    match tokens t with
    | [.link n] => let (pg, sp) := target false n
      (resolveIn H es (String.ofList pg) sp).map fun ct => .cite (String.ofList n) ct
    | [.embed n] => let (pg, sp) := target true n
      (resolveIn H es (String.ofList pg) sp).map fun ct => .cite (String.ofList n) ct
    | _ => none
  | _ => none

/-- **Re-cite a page**: each cite that is behind, unverified or missing, re-justified against its
source's current version; each dangling link whose page now exists, resolved. -/
def reciteIn (H : Hash) (s : Store) (who : Actor) (page : String) : Except String (Store × Nat) := do
  let some p := s.page? page | throw ("no page named " ++ page)
  unless who.may "write" page do throw (who.name ++ " may not write " ++ page)
  let some G := p.current | throw (page ++ " has no version yet")
  let (G', added, n) := replaceAll H G (pieces G p.name p.who) (reciteOf H s) who.name
  if n = 0 then return (s, 0)
  let s' ← s.write p G' (added.map (·, who.name)) who
  return (s', n)

/-! ## What a person is told -/

/-- Why a fact fails, in words. -/
def factWords (s : Store) (name : String) : Fact → String
  | .current c =>
    "behind: " ++ name ++ " moved on (v" ++ toString (c.version + 1) ++ " → v" ++
      toString (s.world c.page).length ++ ") and the bytes it quotes changed"
  | .verifies _ => "unverified: the bytes it quotes no longer match its commitment"
  | .present _ => "missing: " ++ name ++ " has no version"
  | _ => "dead"

/-- Each cite of a page's current version, with whether it holds and, if not, why. -/
def citeReport (H : Hash) (s : Store) (p : Page) : List (String × Bool × String) :=
  match p.current with
  | none => []
  | some G =>
    (pieces G p.name p.who).filterMap fun pc => match pc with
      | .atom a txt => match G.label a with
        | some (.cite n c) =>
          let target := ((s.pages.find? (·.id == c.page)).map (·.name)).getD n
          let fails := (citeFacts c).filter fun f => !holds H s.world f
          let kind := match c.span with
            | .identity => "link" | .page => "embed" | .block _ => "block quote" | .bytes _ => "byte quote"
          some (txt ++ " (" ++ kind ++ ")", fails.isEmpty,
            if fails.isEmpty then (if c.span == .identity then "current: " ++ target ++ " exists"
              else "current: the bytes it quotes are " ++ target ++ "'s now")
            else ", ".intercalate (fails.map (factWords s target)))
        | some (.text t) => if (t.startsWith "[[" || t.startsWith "![[") && t.endsWith "]]" then
            some (t ++ " (link)", false, "dangling: no page of that name") else none
        | _ => none
      | _ => none

/-- The open sections of a page, with their candidates' authors. -/
def sectionReport (p : Page) : List String :=
  match p.current with
  | none => []
  | some G => (sections G).zipIdx.map fun (alts, k) =>
    "section " ++ toString (k + 1) ++ ": " ++ toString alts.length ++ " candidates (" ++
      ", ".intercalate (alts.map fun (h, _) => p.who h) ++ "); keep one with: obend select " ++ p.name ++ " " ++
      toString (k + 1) ++ " N"

end Obend.Vault

end
