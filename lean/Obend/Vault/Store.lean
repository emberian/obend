module
/-
# Obend.Vault.Store — the world kept beside a vault, and what each command does to it

A vault is a directory of markdown; the world beside it (`.obend/`) is a `Store`: every page's
history of versions (graphs, `Obend.Doc`), the text it last read or wrote for the page (`seen`), who
added each atom, and the members with their grants. Every command is a pure function of the store
and the files; `Obend.Vault.Cli` reads and writes them.

* `openVault`: every file whose text is not what the store last saw is a write by the owner: an edit
  of an existing page (`editPatch`, the file lined up against the current rendering) or the birth of
  a new one (`readPage`). Each write is a turn (`admitWrites`): judged by the page's laws (`commit`)
  against the store at the moment of its judgment, a kind before its instances; an admitted write is
  a new version, a refused one is kept with the pins its judgment read and is judged again exactly
  when a pin moves (a page it read is written). An open leaves every refused write's pins holding
  (`open_admitted`). Then each page is rendered at its current version, and a file is written where
  its text differs (`writesFor`). **Opening twice is a no-op** (`open_idem`): the second open finds
  every file as the first left it and changes neither the store nor any file. This holds for every
  store and every vault the reader accepts (page names unique, as a directory's paths are).
* `mergePage`: the merge of two versions of a page, the pushout of the two (`mergePage_pushout`).
  Two replicas that edited one place differently leave a section with two candidates, rendered with
  the command that selects one. Merging another replica's store (an offline copy) is
  `Obend.Vault.Merge.mergeVault`: the two stores read as branches of their base and merged at the
  tip (`Obend.Vault.Branch.merge`), with `mergePage` as the merge of a page both sides wrote.
* `postAs`: a member's proposal for a page becomes candidates in sections (`postPatch`); it needs the
  member's `post` grant on the page.
* `selectIn`: keep one candidate of a section (`selectPatch`); the owner, or a member with a `select`
  grant on the page (`select_needs_grant`). The candidate kept stays alive (`select_keeps`).
* `reciteIn`: re-justify the cites of a page that are behind (or unverified) against their sources'
  current versions, and resolve the links that dangled.

A backticked name (`judge_admits`) is a cite of the ENVIRONMENT, the census's list of the library's
constants that a kind page names (`environment: PATH`; `Obend.Vault.Page`, "Names cited in
backticks"); `new.unresolved` counts the page's (or the row's) names the environment lacks and
`new.unresolvedInserted` the names a write's inserted lines cite that it lacks, and a refusal of a
law reading either names the names.

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

/-- The text of a write to a page: the versions it appends, each with the authors of the atoms it
adds, and whose text it is (`new.poster`; the writer's own when none). -/
structure PageWrite where
  versions : List (Graph × List (AtomId × String)) := []
  poster : Option String := none
deriving Repr

/-- A merge's open question about a page (`Obend.Vault.Merge`): two writes of it that do not merge,
each with the replica it came from and its label, both kept until one is chosen
(`obend branch resolve`); neither has landed. -/
structure PageConflict where
  page : String
  left : String × String × PageWrite
  right : String × String × PageWrite
deriving Repr

structure Store where
  pages : List Page := []
  members : List Member := []
  turn : Nat := 0
  /-- pages whose files were deleted (`forgetMissing`): kept with their history but out of the
  world, so a cite of one fails `missing`; revived when a file returns under their name, or under
  a new name carrying their last text (a rename) -/
  tombs : List Page := []
  /-- the names a cite in backticks resolves against (`Obend.Vault.Page.Environment`), read from
  the file a kind page names (`environment: PATH`) at every open (`Obend.Vault.Cli.openDir`); not
  kept in the world, since it is the machine's library, not the vault's -/
  environment : Environment := #[]
  /-- the merges' open conflicts, each a page's two candidate writes (`PageConflict`) -/
  conflicts : List PageConflict := []
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

/-- One law line `(NAME, TEXT)` of the page `pageName`, read as the judge takes it: named
`PAGE: NAME`, with its text (`Obend.Vault.Branch` reads a law book's lines through it). -/
def lawOfLine (pageName : String) : String × String → Except String (String × LawExpr × String)
  | (n, txt) =>
    if isLinkLaw txt && (txt.splitOn "new.").length > 1 then
      .error (pageName ++ ": law " ++ n ++ ": a law over links reads the linked page as `linked.`; \
        the page's own fields (`new.`) are not readable in it")
    else match Obend.Spec.Law.parse (if isLinkLaw txt then linkLawText txt else txt) with
    | .ok e => .ok (pageName ++ ": " ++ n, e, txt)
    | .error msg => .error (pageName ++ ": law " ++ n ++ ": " ++ msg)

/-- The laws of a page as written in a version, each named `PAGE: NAME`, with its text. A law over
links reads the linked page only: one that also reads `new.` is refused. -/
def lawsIn (pageName : String) (G : Graph) : Except String (List (String × LawExpr × String)) :=
  (lawLines (settled G)).mapM (lawOfLine pageName)

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
    {S : Obend.Core.Ty.Ty} {o n : Obend.Core.Data.Data} {facts : Facts} {who pr : String} {k : Occ}
    (hj : judge S name (laws.map fun x => (x.1, x.2.1)) o n (requestBy who pr k facts) = .admitted) :
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
    let posted := match labelAt new "poster" with
      | some w => if e.fields.contains "poster" then "; posted by " ++ w else ""
      | none => ""
    "refused by " ++ lawOwnerText pageName law ++ ": `" ++ txt ++ "` does not hold; " ++ suggest e facts old new front ++ posted
  | none => "refused by " ++ lawOwnerText pageName law ++ ": " ++ reason

/-- Why a law over rows refused a write, at the row it refused. -/
def rowRefusalText (pageName : String) (laws : Laws) (law reason : String) (facts : Facts)
    (old : Option Obend.Core.Data.Data) (new : Obend.Core.Data.Data) (mark title : String) : String :=
  let where_ := " at " ++ mark ++ " " ++ title
  match laws.find? (·.1 == law) with
  | some (_, e, txt) =>
    "refused by " ++ lawOwnerText pageName law ++ where_ ++ ": `" ++ txt ++ "` does not hold there; " ++
      suggest e facts old new []
  | none => "refused by " ++ lawOwnerText pageName law ++ where_ ++ ": " ++ reason

/-- The state's reading of the names a version cites that the environment lacks. -/
def unresolvedOf (env : Environment) (G : Graph) : List (String × Nat) :=
  [("unresolved", (unresolvedNames env (settled G)).length)]

/-- The names a refusal of a law over `unresolved` or `unresolvedInserted` is about. -/
def lackingNote (laws : Laws) (law : String) (unresolved inserted : List String) : String :=
  match laws.find? (·.1 == law) with
  | some (_, e, _) =>
    let names := (if e.fields.contains "unresolvedInserted" then inserted else []) ++
      (if e.fields.contains "unresolved" then unresolved else [])
    if names.isEmpty then "" else "; names the environment lacks: " ++ ", ".intercalate names.eraseDups
  | none => ""

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

/-- The laws over links among a page's laws, as the judge takes them. -/
def linkLaws (laws : Laws) : List (String × LawExpr) :=
  (laws.filter fun l => isLinkLaw l.2.2).map fun (n, e, _) => (n, e)

/-- The label fields of a version: its frontmatter's words, the measures' names excepted. -/
def labelsOf (G : Graph) : List (String × String) :=
  (labelFields (settled G)).filter fun (k, _) => !measureNames.contains k

/-- A page's state from its measures and label fields, by name. -/
def pageState (G : Graph) (v : Nat) : Obend.Core.Data.Data :=
  let ms := measures G v
  let ls := labelsOf G
  stateOfWith (sortNames (ms.map (·.1) ++ ls.map (·.1))) (ls.map (·.1)) ms ls

/-- The store of page states a judgment over links reads: each entry's name to its state. -/
def stateStore (es : List Entry) : VaultStore := fun c =>
  (es.find? (·.name == c)).map fun e => pageState e.graph e.version

/-- A state's scalar or label, said. -/
def showDatum : Obend.Core.Data.Data → String
  | .natural n => toString n
  | .label s => s
  | .boolean b => toString b
  | _ => "…"

/-- How a pinned state differs from the state here, field by field (the first three), said to a
person. -/
def stateDiffText (expected current : Option Obend.Core.Data.Data) : String :=
  match expected, current with
  | some (.record es), some (.record cs) =>
    let diffs := es.filterMap fun (k, v) => match cs.lookup k with
      | some w => if Obend.Law.termEq v.term w.term then none else some (k ++ " " ++ showDatum v ++ " → " ++ showDatum w)
      | none => some (k ++ " " ++ showDatum v ++ " → none")
    ", ".intercalate (diffs.take 3) ++ (if diffs.length > 3 then ", …" else "")
  | _, none => "no page of that name here"
  | _, _ => "a different state here"

/-! ## An unset label is `""`

A law that compares a field with a label constant (`new.commit == "abc"`, `new.state in ["a", "b"]`)
reads that field as a label. Where the page does not write the field at all, the field is an UNSET
LABEL, `""`, not the natural 0: so `not (new.commit == "")` refuses a page with no `commit:` line, as
it says. (2026-11-06, found by the swarm vault: before, the absent field was typed a natural, the
comparison with `""` was false, and that law admitted a merged lane with no commit.) A field the page
writes as a natural stays a natural. -/

/-- The fields a law compares with a label constant. -/
def labelCompared : LawExpr → List String
  | .eqR (.field f) (.labelConst _) => [f]
  | .eqR (.labelConst _) (.field f) => [f]
  | .not e => labelCompared e
  | .and l r | .or l r | .implies l r => labelCompared l ++ labelCompared r
  | _ => []

/-- The fields the laws `lin` compare with a label constant that none of `present` names: each is
read as the unset label `""`. -/
def unsetLabels (lin : List (String × LawExpr)) (present : List String) : List String :=
  ((lin.flatMap fun l => labelCompared l.2).filter fun f => !present.contains f).eraseDups

theorem firstField_map_self (f : String) (g : String → Obend.Core.Data.Data) :
    ∀ ks : List String, f ∈ ks → Obend.Spec.Law.firstField f (ks.map fun k => (k, g k)) = some (g f)
  | [], h => by cases h
  | k :: ks, h => by
    simp only [List.map_cons, Obend.Spec.Law.firstField]
    by_cases hk : k = f
    · subst hk; simp
    · simp only [hk, ite_false]
      exact firstField_map_self f g ks (by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hk
        · exact h)

theorem firstScalarField_map_none (f : String) (g : String → Obend.Core.Data.Data)
    (hg : Obend.Spec.Law.scalarOf (g f) = none) :
    ∀ ks : List String, Obend.Spec.Law.firstScalarField f (ks.map fun k => (k, g k)) = none
  | [] => rfl
  | k :: ks => by
    simp only [List.map_cons, Obend.Spec.Law.firstScalarField]
    by_cases hk : k = f
    · subst hk; simp [hg, firstScalarField_map_none k g hg ks]
    · simp [hk, firstScalarField_map_none f g hg ks]

/-- **An unset label reads `""`.** In a page state built with `f` among its keys and its labels and
no label value for `f`, the field `f` is the label `""`. -/
theorem unset_label_reads_empty {keys labels : List String} {vals : List (String × Nat)}
    {lvals : List (String × String)} {f : String} (hk : f ∈ keys) (hl : f ∈ labels)
    (hv : lvals.lookup f = none) :
    Obend.Spec.Law.fieldLabel f (stateOfWith keys labels vals lvals) = some "" := by
  have hm := firstField_map_self f (fun k => if labels.contains k then Obend.Core.Data.Data.label ((lvals.lookup k).getD "")
    else Obend.Core.Data.Data.natural ((vals.lookup k).getD 0)) keys hk
  unfold stateOfWith Obend.Spec.Law.fieldLabel
  simp only [hm]
  simp [hl, hv]

/-- **So a law requiring a label refuses its absence.** On such a state, `not (new.f == "")` does not
hold, whatever the facts and the old state: the law means what it says. -/
theorem unset_label_refused {keys labels : List String} {vals : List (String × Nat)}
    {lvals : List (String × String)} {f : String} (hk : f ∈ keys) (hl : f ∈ labels)
    (hv : lvals.lookup f = none) (facts : Facts) (old : Option Obend.Core.Data.Data) :
    (LawExpr.not (.eqR (.field f) (.labelConst ""))).denote facts old
      (stateOfWith keys labels vals lvals) = false := by
  have h := unset_label_reads_empty (vals := vals) hk hl hv
  have hn : Obend.Spec.Law.fieldOf f (stateOfWith keys labels vals lvals) = none := by
    unfold Obend.Spec.Law.fieldOf stateOfWith
    exact firstScalarField_map_none f _ (by simp [hl, Obend.Spec.Law.scalarOf]) keys
  simp [LawExpr.denote, Obend.Spec.Law.LawRef.read, Obend.Spec.Law.LawRef.readLabel, hn, h]

/-- A state with the fields a law reads added, at 0 where the state has none (`stateOfWith`'s
default): its type and itself. -/
def rekey (lin : List (String × LawExpr)) : Obend.Core.Data.Data → Obend.Core.Ty.Ty × Obend.Core.Data.Data
  | .record fs =>
    let vals := fs.filterMap fun (k, d) => match d with | .natural n => some (k, n) | _ => none
    let lvals := fs.filterMap fun (k, d) => match d with | .label s => some (k, s) | _ => none
    let keys := sortNames (fs.map (·.1) ++ lin.flatMap fun l => l.2.fields)
    let labels := lvals.map (·.1) ++ unsetLabels lin (fs.map (·.1))
    (stateTyWith keys labels, stateOfWith keys labels vals lvals)
  | d => (stateTy [], d)

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
      let (S, n) := rekey lin d
      match judge S pkg lin n n rq with
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

/-- The pages a version links to (identity cites), by name as the entries `res` the cites were
resolved against name them. At an open a page not yet born is among them: a law over links is judged
at it and refused there (it has no version) until it is. -/
def citedNames (res : List Entry) (G : Graph) : List String :=
  ((settledAtoms G).filterMap fun a => match G.label a with
    | some (.cite _ c) => if c.span = .identity then (res.find? (·.id == c.page)).map (·.name) else none
    | _ => none).eraseDups

/-- The pins of a write over the pages `cells`: each at the state the store `es` holds for it. -/
def pinsAt (es : List Entry) (cells : List String) : Footprint :=
  cells.map fun c => ⟨c, stateStore es c⟩

/-- The write of `page` as a turn: its one write cell is the page (its state before and after), its
read pins the pages its laws over links read, at the states read. -/
def writeTurn (page : String) (o n : Obend.Core.Data.Data) (pins : Footprint)
    (rq : Obend.Core.Data.Data) : VaultTurn where
  turnId := ByteArray.empty
  readPins := pins
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

/-- A write as the judge takes it, before it is judged: the page, its new version, the laws and the
occasion, the state type, the old and new states, the request. `commit` judges one; a turn over
several pages (`commitTurn`) judges each of its writes at the tip of all of them. -/
structure Prepared where
  p : Page
  G' : Graph
  authors : List (AtomId × String)
  laws : Laws
  kinds : KindsOf
  occ : Occ
  S : Obend.Core.Ty.Ty
  o : Obend.Core.Data.Data
  n : Obend.Core.Data.Data
  facts : Facts
  rq : Obend.Core.Data.Data
  lin : List (String × LawExpr)
  poster : String
  who : Actor
  env : Environment

/-- **The one landing rule**: an admitted write appends its version, renders it, and pins its kind. -/
def Prepared.change (pr : Prepared) : Change :=
  ⟨pr.p.history ++ [pr.G'], render pr.G' pr.p.name ({ pr.p with authors := pr.authors }).who, pr.authors,
    none, pr.kinds.pin⟩

/-- The occasion of a write that adopts new laws (its own law lines changed, or its kind's): an
ADOPTION judges the laws at the new state alone (`Occ.old .adopt`), which is right only when the write
says nothing new but its laws; a write that also changes a field of its frontmatter is judged as the
write it is, from its old state, under the new laws (2026-11-06: the first write after a kind gained
`monotone(spent)` lowered `spent` and was admitted, the law holding vacuously). -/
def adoptionOccasion (old new : String) : Occ :=
  if scalarFields old == scalarFields new && labelFields old == labelFields new then Occ.adopt else Occ.write

theorem adoptionOccasion_adopt {old new : String} (h : adoptionOccasion old new = Occ.adopt) :
    scalarFields old = scalarFields new ∧ labelFields old = labelFields new := by
  unfold adoptionOccasion at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc
  · cases h

/-- Prepare the write of `G'` to `p` (see `commit`): the refusals that come before the laws are
asked (a change of a law line or of the kind by an actor without `relaw`, a stale kind), the laws,
the states and the request. -/
def prepareWrite (es : List Entry) (p : Page) (G' : Graph) (added : List (AtomId × String)) (who : Actor)
    (turn : Nat) (poster : String := who.name) (env : Environment := #[]) : Except String Prepared := do
  let authors := p.authors ++ added
  let v := p.history.length
  let newLaws ← lawsFor es p.name G'
  let kinds ← kindsFor es p.name (settled G')
  let moved := match p.kind with
    | some old => movedKinds es old
    | none => []
  let (occ, laws, oldMs, oldLs) ← match p.current with
    | none => pure (Occ.birth, newLaws, [], [])
    | some G =>
      if lawsKept (settled G) (settled G') && moved.isEmpty then
        pure (Occ.write, newLaws, measures G (v - 1) ++ unresolvedOf env G, labelsOf G)
      else if who.may "relaw" p.name then
        pure (adoptionOccasion (settled G) (settled G'), newLaws, measures G (v - 1) ++ unresolvedOf env G, labelsOf G)
      else if lawsKept (settled G) (settled G') then throw (staleText p.name who.name moved)
      else throw ("refused: changing a law line or the page's kind is the owner's (" ++ who.name ++
        " has no relaw grant on " ++ p.name ++ ")")
  let newMs := measures G' v ++ unresolvedOf env G' ++ writeMeasures env p.current G'
  -- the write's provenance is a label the laws read: `new.poster`, the member whose text this is
  let newLs := ("poster", poster) :: labelsOf G'
  let lin := (laws.filter fun l => !isLinkLaw l.2.2 && (lawSubject l.1).isNone).map fun (n, e, _) => (n, e)
  let labels := (newLs.map (·.1) ++ oldLs.map (·.1) ++
    unsetLabels lin (newLs.map (·.1) ++ oldLs.map (·.1) ++ newMs.map (·.1) ++ oldMs.map (·.1))).eraseDups
  let keys := sortNames (newMs.map (·.1) ++ oldMs.map (·.1) ++ labels ++ lin.flatMap fun l => l.2.fields)
  let S := stateTyWith keys labels
  let n := stateOfWith keys labels newMs newLs
  let o := if oldMs.isEmpty then n else stateOfWith keys labels oldMs oldLs
  let facts : Facts := ⟨some who.id, some who.id, v, turn⟩
  let rq := requestBy who.name poster occ facts
  pure ⟨p, G', authors, laws, kinds, occ, S, o, n, facts, rq, lin, poster, who, env⟩

/-- A store with some pages read at given states (the other writes of a turn, at their new states). -/
def overlay (over : List (String × Obend.Core.Data.Data)) (store : VaultStore) : VaultStore := fun c =>
  match over.lookup c with
  | some d => some d
  | none => store c

/-- **Judge a prepared write**: its laws on its old and new states, its rows, and the laws over links
(this page's at the pages it links to, every linking page's at this page), read on the store its
write turn describes with the pages `over` at the states given (the tip of a turn over several
pages; `[]` for a write alone). -/
def judgePrepared (es res : List Entry) (pr : Prepared) (over : List (String × Obend.Core.Data.Data)) :
    Except String Unit := do
  let p := pr.p
  let G' := pr.G'
  let v := p.history.length
  let (laws, occ, S, o, n, facts, rq, lin, poster, who, env) :=
    (pr.laws, pr.occ, pr.S, pr.o, pr.n, pr.facts, pr.rq, pr.lin, pr.poster, pr.who, pr.env)
  match judge S p.name lin o n rq with
  | .admitted =>
    -- the laws over rows (`law NAME per ##`): each row the marker begins, in the new version and in
    -- the old, judged on its own measures and its write's (`rowMeasures`); a row of the old version
    -- the new lacks is a write of it to nothing
    for mark in (laws.filterMap fun l => lawSubject l.1).eraseDups do
      let rl := (laws.filter fun l => lawSubject l.1 == some mark).map fun (n, e, _) => (n, e)
      let newRows := rowsOf mark G'
      let oldRows := match p.current with
        | some G => rowsOf mark G
        | none => []
      for title in (newRows.map (·.1) ++ oldRows.map (·.1)).eraseDups do
        let atoms := (newRows.lookup title).getD []
        let oldAtoms := oldRows.lookup title
        let rowLs := [("poster", poster)]
        let nMs := rowMeasures env G' v atoms oldAtoms
        let keys := sortNames (nMs.map (·.1) ++ ["poster"] ++ rl.flatMap fun l => l.2.fields)
        let S' := stateTyWith keys ["poster"]
        let n' := stateOfWith keys ["poster"] nMs rowLs
        let (occ', o') := match occ, oldAtoms, p.current with
          | .adopt, _, _ => (Occ.adopt, n')
          | _, some oa, some G => (Occ.write, stateOfWith keys ["poster"] (rowMeasures env G (v - 1) oa none) rowLs)
          | _, _, _ => (Occ.birth, n')
        match judge S' p.name rl o' n' (requestBy who.name poster occ' facts) with
        | .admitted => pure ()
        | .refused law reason =>
          let rowText := String.join (atoms.map G'.atomText)
          let insText := String.join (((atoms.filter fun a => !(oldAtoms.getD []).contains a)).map G'.atomText)
          throw (rowRefusalText p.name laws law reason facts (occ'.old o' n') n' mark title ++
            lackingNote laws law (unresolvedNames env rowText) (unresolvedNames env insText))
        | .undecided why => throw ("undecided: " ++ why)
    -- the laws over links, judged through the write's turn: this page's at the pages it links to,
    -- and every linking page's at this page as written
    let wt := writeTurn p.name o n (pinsAt es (citedNames res G')) rq
    let world := overlay over (applyTurn wt.readPins.store wt)
    let mine := linkLaws laws
    if let some r := (if mine.isEmpty then none else judgeLinksIn world p.name mine rq wt.readFootprint) then
      throw (linkRefusalText p.name laws r facts)
    for e in es do
      if e.name != p.name && (linkTargets e.graph).contains p.id then
        match lawsFor es e.name e.graph with
        | .ok elaws =>
          let theirs := linkLaws elaws
          if let some r := (if theirs.isEmpty then none else judgeLinksIn world e.name theirs rq [p.name]) then
            throw (backlinkRefusalText e.name p.name elaws r facts n
              ((scalarFields (settled G')).map (·.1)))
        | .error _ => pure ()
    pure ()
  | .refused law reason =>
    throw (refusalText p.name laws law reason facts (occ.old o n) n
      ((scalarFields (settled G')).map (·.1)) ++
      lackingNote laws law (unresolvedNames env (settled G')) (unresolvedInsertedNames env p.current G'))
  | .undecided why => throw ("undecided: " ++ why)


/-- **Commit a write**: judge the new version `G'` of page `p` by its laws, and on admission append
it, pinning its kind at the vault's registry. A change of a law line or of the kind the page names
is the owner's, or a member's granted `relaw`; it is judged as the adoption of the new laws over the
page as written. So is a write to a page whose kind pin is stale (a kind it rests on was revised,
`movedKinds`): the owner's write adopts the revised kinds' laws and renews the pin; anyone else's is
refused, naming the kinds that moved. Otherwise the laws are kept (`lawsKept`), and the new laws are
the old ones (`lawsFor_of_kept`). A birth is judged as a first write. The new state carries the
write's own measures (`deletions`, `insertions`: how it changed the current version); the old state
has none (0). The laws and the states a law over links reads are the store's (`es`); the cites of
`G'` were resolved against `res` (at an open, the files as they are about to become), which names
the pages they link to. -/
def commit (es : List Entry) (p : Page) (G' : Graph) (added : List (AtomId × String)) (who : Actor)
    (turn : Nat) (poster : String := who.name) (res : List Entry := es) (env : Environment := #[]) :
    Except String Change := do
  let pr ← prepareWrite es p G' added who turn poster env
  judgePrepared es res pr []
  pure pr.change

/-- A refusal before the laws are asked is the commit's. -/
theorem commit_of_prepare_error {es : List Entry} {p : Page} {G' : Graph} {added : List (AtomId × String)}
    {who : Actor} {turn : Nat} {poster : String} {res : List Entry} {env : Environment} {m : String}
    (h : prepareWrite es p G' added who turn poster env = .error m) :
    commit es p G' added who turn poster res env = .error m := by
  simp [commit, bind, Except.bind, h]

/-- **Retargeting the kind needs the grant**: a write that changes the kind a page names, by an actor
without `relaw` on the page, is refused, whatever its law lines. -/
theorem commit_kind_needs_relaw (es : List Entry) (p : Page) (G G' : Graph) (added : List (AtomId × String))
    (who : Actor) (turn : Nat) (hc : p.current = some G) (hk : kindLine (settled G) ≠ kindLine (settled G'))
    (hw : who.may "relaw" p.name = false) {env : Environment} :
    ∃ msg, commit es p G' added who turn (env := env) = .error msg := by
  have hkept : lawsKept (settled G) (settled G') = false := by
    simp [lawsKept, hk]
  suffices ∃ msg, prepareWrite es p G' added who turn who.name env = .error msg by
    obtain ⟨m, hm⟩ := this
    exact ⟨m, commit_of_prepare_error hm⟩
  unfold prepareWrite
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
    (hw : who.may "relaw" p.name = false) {env : Environment} :
    ∃ msg, commit es p G' added who turn (env := env) = .error msg := by
  suffices ∃ msg, prepareWrite es p G' added who turn who.name env = .error msg by
    obtain ⟨m, hm⟩ := this
    exact ⟨m, commit_of_prepare_error hm⟩
  unfold prepareWrite
  cases lawsFor es p.name G' with
  | error m => exact ⟨m, rfl⟩
  | ok newLaws =>
    cases kindsFor es p.name (settled G') with
    | error m => exact ⟨m, rfl⟩
    | ok kinds =>
      simp only [bind, Except.bind, hc, hp, hm, hw, Bool.and_false, Bool.false_eq_true, if_false]
      split <;> exact ⟨_, rfl⟩

/-- What `prepareWrite` prepares is the write it was given: the page and the version. -/
theorem prepareWrite_page {es : List Entry} {p : Page} {G' : Graph} {added : List (AtomId × String)}
    {who : Actor} {turn : Nat} {poster : String} {env : Environment} {pr : Prepared}
    (h : prepareWrite es p G' added who turn poster env = .ok pr) : pr.p = p ∧ pr.G' = G' := by
  unfold prepareWrite at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨rfl, rfl⟩)
    | cases h
    | skip
  all_goals (simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

/-! ## A turn over several pages

A turn may write several pages at once (a form's proposal moves an amount from one page to another,
`Obend.Vault.Form`). It is judged as one: every write prepared (`prepareWrite`, the refusals before
the laws), then each judged by its own laws and rows and by the laws over links on the TIP, the store
with every page of the turn at its new state (`judgePrepared` with `over`), and landed only when all
are admitted, by the one landing rule (`Prepared.change`), all at once and one turn later
(`Store.landAll`). -/

/-- Prepare every write of a turn; the first refusal, said at its page. -/
def prepareAll (es : List Entry) (who : Actor) (turn : Nat) (poster : String) (env : Environment) :
    List (Page × Graph × List (AtomId × String)) → Except String (List Prepared)
  | [] => .ok []
  | (p, G', added) :: rest =>
    match prepareWrite es p G' added who turn poster env with
    | .error m => .error ("at " ++ p.name ++ ": " ++ m)
    | .ok pr =>
      match prepareAll es who turn poster env rest with
      | .error m => .error m
      | .ok prs => .ok (pr :: prs)

/-- Judge every prepared write of a turn at the tip `over`; the first refusal, said at its page. -/
def judgeAll (es res : List Entry) (over : List (String × Obend.Core.Data.Data)) :
    List Prepared → Except String Unit
  | [] => .ok ()
  | pr :: rest =>
    match judgePrepared es res pr over with
    | .error m => .error ("at " ++ pr.p.name ++ ": " ++ m)
    | .ok () => judgeAll es res over rest

/-- The tip of a turn: each page it writes, at its new state. -/
def tipOf (prs : List Prepared) : List (String × Obend.Core.Data.Data) := prs.map fun pr => (pr.p.name, pr.n)

/-- **Commit a turn over several pages**: all prepared, all judged at the tip, or the refusal. -/
def commitTurn (es res : List Entry) (writes : List (Page × Graph × List (AtomId × String))) (who : Actor)
    (turn : Nat) (poster : String) (env : Environment) : Except String (List Prepared) :=
  match prepareAll es who turn poster env writes with
  | .error m => .error m
  | .ok prs =>
    match judgeAll es res (tipOf prs) prs with
    | .error m => .error m
    | .ok () => .ok prs

/-- **Land a turn**: every prepared write's change at once (`Prepared.change`, the landing rule
`commit` uses), one turn later. -/
def Store.landAll (s : Store) (prs : List Prepared) : Store :=
  { s with
    pages := s.pages.map fun q => match prs.find? (·.p.name == q.name) with
      | some pr => q.withChange pr.change
      | none => q
    turn := s.turn + 1 }

theorem prepareAll_ok {es : List Entry} {who : Actor} {turn : Nat} {poster : String} {env : Environment} :
    ∀ {ws : List (Page × Graph × List (AtomId × String))} {prs : List Prepared},
      prepareAll es who turn poster env ws = .ok prs → prs.map (·.p) = ws.map (·.1)
  | [], prs, h => by simp only [prepareAll, Except.ok.injEq] at h; subst h; rfl
  | (p, G', added) :: rest, prs, h => by
    simp only [prepareAll] at h
    split at h
    · cases h
    · rename_i pr hpr
      split at h
      · cases h
      · rename_i prs' hprs
        simp only [Except.ok.injEq] at h
        subst h
        simp [(prepareWrite_page hpr).1, prepareAll_ok hprs]

theorem judgeAll_ok {es res : List Entry} {over : List (String × Obend.Core.Data.Data)} :
    ∀ {prs : List Prepared}, judgeAll es res over prs = .ok () → ∀ pr ∈ prs, judgePrepared es res pr over = .ok ()
  | [], _, pr, hp => by cases hp
  | q :: rest, h, pr, hp => by
    simp only [judgeAll] at h
    split at h
    · cases h
    · rename_i hq
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hq
      · exact judgeAll_ok h pr hp

/-- **A committed turn judged every write at the tip**, and prepared exactly the pages it was given. -/
theorem commitTurn_ok {es res : List Entry} {ws : List (Page × Graph × List (AtomId × String))} {who : Actor}
    {turn : Nat} {poster : String} {env : Environment} {prs : List Prepared}
    (h : commitTurn es res ws who turn poster env = .ok prs) :
    prs.map (·.p) = ws.map (·.1) ∧ ∀ pr ∈ prs, judgePrepared es res pr (tipOf prs) = .ok () := by
  unfold commitTurn at h
  split at h
  · cases h
  · rename_i prs' hp
    split at h
    · cases h
    · rename_i hj
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨prepareAll_ok hp, judgeAll_ok hj⟩

theorem find?_map_page (s : Store) (g : Page → Page) (hg : ∀ q, (g q).name = q.name) (n : String) :
    (s.pages.map g).find? (·.name == n) = (s.pages.find? (·.name == n)).map g := by
  rw [List.find?_map]
  have : ((fun x : Page => x.name == n) ∘ g) = (fun x => x.name == n) := by
    funext q; simp [Function.comp, hg]
  rw [this]

/-- **What a landing does not write, it leaves**: a page no prepared write names reads as before. -/
theorem landAll_frame (s : Store) (prs : List Prepared) (n : String) (hn : ∀ pr ∈ prs, pr.p.name ≠ n) :
    (s.landAll prs).page? n = s.page? n := by
  unfold Store.page? Store.landAll
  simp only
  rw [find?_map_page s _ (fun q => by split <;> rfl) n]
  cases hq : s.pages.find? (·.name == n) with
  | none => rfl
  | some q =>
    have hqn : q.name = n := by simpa using (List.find?_some hq)
    have : prs.find? (·.p.name == q.name) = none := by
      rw [List.find?_eq_none]
      intro pr hpr hc
      simp only [beq_iff_eq] at hc
      exact hn pr hpr (hc.trans hqn)
    simp [this]

/-- **What a landing writes, it writes once, by the landing rule**: the page a prepared write names
(each named once) is that page with the write's change. -/
theorem landAll_lands (s : Store) (prs : List Prepared) (hnd : (prs.map (·.p.name)).Nodup)
    {pr : Prepared} (hpr : pr ∈ prs) {q : Page} (hq : s.page? pr.p.name = some q) :
    (s.landAll prs).page? pr.p.name = some (q.withChange pr.change) := by
  unfold Store.page? at hq ⊢
  unfold Store.landAll
  simp only
  rw [find?_map_page s _ (fun q => by split <;> rfl), hq]
  have hqn : q.name = pr.p.name := by simpa using (List.find?_some hq)
  have hfind : prs.find? (·.p.name == q.name) = some pr := by
    rw [hqn]
    clear hq hqn
    induction prs with
    | nil => cases hpr
    | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hpr with rfl | hx
      · simp
      · have hne : (x.p.name == pr.p.name) = false := by
          simp only [beq_eq_false_iff_ne]
          intro he
          exact hnd.1 (he ▸ List.mem_map_of_mem hx)
        simp [hne, ih hnd.2 hx]
  simp [hfind]

/-! ## Open -/

/-- The page a file's text reads as, its cites resolved against `res`. -/
def readAs (H : Hash) (res : List Entry) (md : String) : Graph :=
  Graph.empty.apply (chain root (contents (resolveIn H res) (stripToks (tokens md))))

/-- The version `G'` committed as the owner's write of `md` to `p`, judged at `es` with its cites
resolved against `res`; or the refusal, with the text it refused. -/
def writtenAs (es : List Entry) (turn : Nat) (p : Page) (md : String) (G' : Graph) (added : List AtomId)
    (res : List Entry) (env : Environment := #[]) : Change :=
  match commit es p G' (added.map (·, "owner")) .owner turn (res := res) (env := env) with
  | .ok ch => { ch with note := none }
  | .error msg => ⟨p.history, md, p.authors, some msg, p.kind⟩

/-- The owner's edit `b` of the current version `G`. Only the view's marks changed (one deleted,
say), or a refused edit was put back: nothing to write; the view is redrawn, and the page's last
write is no longer a refused one. Else the edited version, committed. -/
def editedAs (es : List Entry) (turn : Nat) (p : Page) (md : String) (G : Graph) (b : Built)
    (res : List Entry) (env : Environment := #[]) : Change :=
  if b.ops.isEmpty then ⟨p.history, md, p.authors, none, p.kind⟩
  else writtenAs es turn p md (G.apply b.ops) b.added res env

/-- The owner's write of the text `md` to page `p`: the file lined up against the current rendering,
or a birth, its cites resolved against `res` (the store's entries, or at an open the files as they
are about to become) and judged at the store `es`. -/
def ownerWrite (H : Hash) (es : List Entry) (turn : Nat) (p : Page) (md : String)
    (res : List Entry := es) (env : Environment := #[]) : Change :=
  match p.current with
  | none => writtenAs es turn p md (readAs H res md) [] res env
  | some G =>
    editedAs es turn p md G
      (editPatch H G (align (pieces G p.name p.who) (contents (resolveIn H res) (stripToks (tokens md)))) "owner")
      res env

/-! ### Admission: a write is a turn, admitted when its pins hold -/

/-- The page a wikilink written as text names: a link that resolved to nothing when written. -/
def danglingTarget : Content → Option String
  | .text t =>
    match tokens t with
    | [.link n] => some (String.ofList (target false n).1)
    | [.embed n] => some (String.ofList (target true n).1)
    | _ => none
  | _ => none

/-- Whether a page's laws (at version `G`) include a law over links. A page whose laws cannot be
read is taken to have one (its refusal may rest on any page it links to). -/
def hasLinkLaws (es : List Entry) (name : String) (G : Graph) : Bool :=
  match lawsFor es name G with
  | .ok ls => !(linkLaws ls).isEmpty
  | .error _ => true

/-- The pages a write of `name` (the page `pid`) as `G'` READS, by name: its kinds (the chain when
the registry has it, and the kind it names or its folders' whether or not a page of that name
exists yet: born later, it is a pin that moved), every page a link of it names without resolving
(whether the link resolves), and, where laws over links are judged, every page it links to (the
state such a law reads) and every page that links to it under one. The page itself is the write's
cell, not a pin. -/
def readsOf (es res : List Entry) (name : String) (pid : PageId) (G' : Graph) : List String :=
  let src := settled G'
  let kinds := kindChain es name src ++ (kindLine src).toList.map kindName ++ kindsOf name
  let mine := hasLinkLaws es name G'
  let cited := (settledAtoms G').filterMap fun a => match G'.label a with
    | some (.cite _ c) => if mine then (res.find? (·.id == c.page)).map (·.name) else none
    | some c => danglingTarget c
    | none => none
  let back := (es.filter fun e =>
    e.name != name && (linkTargets e.graph).contains pid && hasLinkLaws es e.name e.graph).map (·.name)
  ((kinds ++ cited ++ back).filter (· != name)).eraseDups

/-- The pins of a write: what it reads, at the states the store holds. -/
def pinsOf (es res : List Entry) (name : String) (pid : PageId) (G' : Graph) : Footprint :=
  pinsAt es (readsOf es res name pid G')

/-- Whether a footprint's pins hold at a store, asked at the door a turn is admitted through
(`admitFootprint`). -/
def pinsHold (store : VaultStore) (fp : Footprint) : Bool :=
  match admitFootprint store fp with
  | .ok _ => true
  | .error _ => false

/-- A write waiting to be judged: a page's name and the text its file holds. -/
abbrev Write := String × String

/-- A write refused, with the pins its judgment read. -/
structure RefusedWrite where
  name : String
  md : String
  pins : Footprint

/-- The store with one page replaced (by name), one turn later. -/
def Store.setPage (s : Store) (p : Page) : Store :=
  { s with pages := s.pages.map fun q => if q.name == p.name then p else q, turn := s.turn + 1 }

/-- A write judged at a store: the owner's write of `md` to `p`, its cites resolved against `res`. -/
def judgeAt (H : Hash) (res : List Entry) (s : Store) (p : Page) (md : String) : Change :=
  ownerWrite H s.entries s.turn p md res s.environment

/-- The store after the write of `md` to `p` is judged: the page with the change, one turn later. -/
def afterAdmit (H : Hash) (res : List Entry) (s : Store) (p : Page) (md : String) : Store :=
  s.setPage (p.withChange (judgeAt H res s p md))

/-- The refused writes whose pins no longer hold at `st`: woken, to be judged again. -/
def woken (st : Store) (refused : List RefusedWrite) : List Write :=
  (refused.filter fun r => !pinsHold (stateStore st.entries) r.pins).map fun r => (r.name, r.md)

/-- The refused writes whose pins hold at `st`: still refused. -/
def held (st : Store) (refused : List RefusedWrite) : List RefusedWrite :=
  refused.filter fun r => pinsHold (stateStore st.entries) r.pins

theorem length_filter_add_length_filter_not {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter fun a => !p a).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_add_length_filter_not p l
    cases hp : p a <;> simp only [List.filter_cons, hp, Bool.not_true, Bool.not_false, List.length_cons] <;>
      simp <;> omega

theorem woken_held_length (st : Store) (refused : List RefusedWrite) :
    (woken st refused).length + (held st refused).length = refused.length := by
  simp only [woken, held, List.length_map]
  rw [Nat.add_comm]
  exact length_filter_add_length_filter_not _ refused

/-- **Admit the writes of an open, each a turn.** The writes are judged in order, each against the
store at the moment of its judgment, so the pins its judgment reads (`writeTurn`) hold at its
admission. An admitted write enters the store. A refused one is kept with its pins (`pinsOf`): it
stays refused while they hold, and is judged again, as the turn it is, exactly when a pin moves,
that is, when an admission writes a page it read. The loop ends with every pending write judged and
every refused write's pins admitted by the door at the store it leaves (`admitWrites_admitted`): the
verdicts are the turns' at that store, and a second open of the same files has nothing to judge
again (`open_idem`). Before 2026-11-04 every write of an open was judged at pins read before any of
them, among them the drafts of pages whose writes were then refused, and a refused write was tried
again at every open that was not quiet. -/
def admitWrites (H : Hash) (res : List Entry) (s : Store) (pending : List Write)
    (refused : List RefusedWrite) : Store × List RefusedWrite :=
  match pending with
  | [] => (s, refused)
  | (n, md) :: rest =>
    match s.page? n with
    | none => admitWrites H res s rest refused
    | some p =>
      match (judgeAt H res s p md).note with
      | none =>
        admitWrites H res (afterAdmit H res s p md) (rest ++ woken (afterAdmit H res s p md) refused)
          (held (afterAdmit H res s p md) refused)
      | some _ =>
        admitWrites H res (afterAdmit H res s p md) rest
          (refused ++ [⟨n, md, pinsOf (afterAdmit H res s p md).entries res n p.id (readAs H res md)⟩])
termination_by (pending.length + refused.length, pending.length)
decreasing_by
  all_goals simp only [Prod.lex_def, List.length_cons, List.length_append, List.length_nil]
  · omega
  · have := woken_held_length (afterAdmit H res s p md) refused
    omega
  · omega

/-- **Induction on the admission**: what holds when nothing is pending, follows a write of a page
the store lacks, follows an admission and follows a refusal, holds of every admission. -/
theorem admitWrites_ind (H : Hash) (res : List Entry)
    (P : Store → List Write → List RefusedWrite → Store × List RefusedWrite → Prop)
    (h0 : ∀ s refused, P s [] refused (s, refused))
    (hnone : ∀ s n md rest refused, s.page? n = none →
      P s rest refused (admitWrites H res s rest refused) →
      P s ((n, md) :: rest) refused (admitWrites H res s rest refused))
    (hadm : ∀ s n md rest refused p, s.page? n = some p → (judgeAt H res s p md).note = none →
      P (afterAdmit H res s p md) (rest ++ woken (afterAdmit H res s p md) refused)
        (held (afterAdmit H res s p md) refused)
        (admitWrites H res (afterAdmit H res s p md) (rest ++ woken (afterAdmit H res s p md) refused)
          (held (afterAdmit H res s p md) refused)) →
      P s ((n, md) :: rest) refused
        (admitWrites H res (afterAdmit H res s p md) (rest ++ woken (afterAdmit H res s p md) refused)
          (held (afterAdmit H res s p md) refused)))
    (href : ∀ s n md rest refused p m, s.page? n = some p → (judgeAt H res s p md).note = some m →
      P (afterAdmit H res s p md) rest
        (refused ++ [⟨n, md, pinsOf (afterAdmit H res s p md).entries res n p.id (readAs H res md)⟩])
        (admitWrites H res (afterAdmit H res s p md) rest
          (refused ++ [⟨n, md, pinsOf (afterAdmit H res s p md).entries res n p.id (readAs H res md)⟩])) →
      P s ((n, md) :: rest) refused
        (admitWrites H res (afterAdmit H res s p md) rest
          (refused ++ [⟨n, md, pinsOf (afterAdmit H res s p md).entries res n p.id (readAs H res md)⟩]))) :
    ∀ (s : Store) (pending : List Write) (refused : List RefusedWrite),
      P s pending refused (admitWrites H res s pending refused) := by
  have key : ∀ N M (s : Store) (pending : List Write) (refused : List RefusedWrite),
      pending.length + refused.length ≤ N → pending.length ≤ M →
      P s pending refused (admitWrites H res s pending refused) := by
    intro N
    induction N with
    | zero =>
      intro M s pending refused hN _
      cases pending with
      | nil => rw [admitWrites]; exact h0 s refused
      | cons w rest => simp at hN
    | succ N ihN =>
      intro M
      induction M with
      | zero =>
        intro s pending refused hN hM
        cases pending with
        | nil => rw [admitWrites]; exact h0 s refused
        | cons w rest => simp at hM
      | succ M ihM =>
        intro s pending refused hN hM
        cases pending with
        | nil => rw [admitWrites]; exact h0 s refused
        | cons w rest =>
          obtain ⟨n, md⟩ := w
          simp only [List.length_cons] at hN hM
          rw [admitWrites]
          cases hp : s.page? n with
          | none =>
            dsimp only
            exact hnone s n md rest refused hp (ihN M s rest refused (by omega) (by omega))
          | some p =>
            dsimp only
            cases hnote : (judgeAt H res s p md).note with
            | none =>
              dsimp only
              refine hadm s n md rest refused p hp hnote (ihN _ _ _ _ ?_ (Nat.le_refl _))
              have := woken_held_length (afterAdmit H res s p md) refused
              simp only [List.length_append]
              omega
            | some m =>
              dsimp only
              exact href s n md rest refused p m hp hnote
                (ihM (afterAdmit H res s p md) rest _ (by simp only [List.length_append, List.length_singleton]; omega)
                  (by omega))
  intro s pending refused
  exact key _ _ s pending refused (Nat.le_refl _) (Nat.le_refl _)

/-- The folders enclosing a page name, counted. -/
def depthOf (name : String) : Nat := (name.splitOn "/").length

/-- The writes an open finds: every page whose file is not the text the store last saw. A kind
precedes its instances: the kind pages come first, an enclosing folder's before its folders', so a
page born in the same open as its kind is judged under it. -/
def pendingAt (s : Store) (V : List (String × String)) : List Write :=
  let ws := s.pages.filterMap fun p => (V.lookup p.name).bind fun md =>
    if some md == p.seen then none else some (p.name, md)
  (ws.filter fun w => isKind w.1).mergeSort (fun a b => depthOf a.1 ≤ depthOf b.1) ++
    ws.filter fun w => !isKind w.1

/-- The writes an earlier open refused, nothing having moved since: each page whose file is the text
of its refused write, with its pins at the store as it is (they hold). -/
def refusedAt (H : Hash) (res : List Entry) (s : Store) (V : List (String × String)) :
    List RefusedWrite :=
  s.pages.filterMap fun p => (V.lookup p.name).bind fun md =>
    if some md == p.seen && p.note.isSome then
      some ⟨p.name, md, pinsOf s.entries res p.name p.id (readAs H res md)⟩
    else none

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
    match commit s.entries p G' (added.map (·, "owner")) .owner s.turn (env := s.environment) with
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

/-- The files the store has no page for. -/
def freshNames (s : Store) (V : List (String × String)) : List String :=
  (V.filter fun e => !s.pages.any (·.name == e.1)).map (·.1)

/-- The store an open starts from: a fresh page for every file it has none for. -/
def withFresh (H : Hash) (s : Store) (V : List (String × String)) : Store :=
  { s with pages := s.pages ++ freshPages H s (freshNames s V) }

/-- **The admission of an open**: its writes judged (`admitWrites`) from the store with the fresh
pages, cites resolved against the files as they are about to become (`openEntries`). -/
def openAdmission (H : Hash) (s : Store) (V : List (String × String)) : Store × List RefusedWrite :=
  admitWrites H (openEntries (withFresh H s V).pages V) (withFresh H s V) (pendingAt (withFresh H s V) V)
    (refusedAt H (openEntries (withFresh H s V).pages V) (withFresh H s V) V)

/-- **Open a vault.** -/
def openVault (H : Hash) (s : Store) (V : List (String × String)) : Opened :=
  if quiet s V then ⟨s, []⟩ else
  let s' : Store := settle H (openAdmission H s V).1
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

theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: xs, hnd, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hx, hxs⟩ := hnd
    obtain rfl | ha' := List.mem_cons.1 ha
    · obtain rfl | hb' := List.mem_cons.1 hb
      · rfl
      · exact absurd (hab ▸ List.mem_map_of_mem hb') hx
    · obtain rfl | hb' := List.mem_cons.1 hb
      · exact absurd (hab ▸ List.mem_map_of_mem ha') hx
      · exact eq_of_nodup_map hxs ha' hb' hab

theorem setPage_names (s : Store) (q : Page) :
    (s.setPage q).pages.map (·.name) = s.pages.map (·.name) := by
  simp only [Store.setPage, List.map_map]
  apply List.map_congr_left
  intro r _
  simp only [Function.comp]
  split
  · rename_i h; exact (beq_iff_eq.1 h).symm
  · rfl

theorem admitWrites_names (H : Hash) (res : List Entry) (s : Store) (pending : List Write)
    (refused : List RefusedWrite) :
    (admitWrites H res s pending refused).1.pages.map (·.name) = s.pages.map (·.name) :=
  admitWrites_ind H res
    (fun s _ _ out => out.1.pages.map (fun q : Page => q.name) = s.pages.map (fun q : Page => q.name))
    (fun _ _ => rfl)
    (fun _ _ _ _ _ _ ih => ih)
    (fun s n md rest refused p _ _ ih => by
      rw [ih]; exact setPage_names s (p.withChange (judgeAt H res s p md)))
    (fun s n md rest refused p _ _ _ ih => by
      rw [ih]; exact setPage_names s (p.withChange (judgeAt H res s p md)))
    s pending refused

/-- A page with a file is seen after it is judged, or still to be judged. -/
theorem seen_setPage {s : Store} {p : Page} {n md : String} (hp : s.page? n = some p) (ch : Change)
    {V : List (String × String)} {rest : List Write}
    (h : ∀ q ∈ s.pages, (V.lookup q.name).isSome → q.seen.isSome ∨ q.name ∈ ((n, md) :: rest).map (·.1)) :
    ∀ q ∈ (s.setPage (p.withChange ch)).pages, (V.lookup q.name).isSome →
      q.seen.isSome ∨ q.name ∈ rest.map (·.1) := by
  intro q hq hl
  simp only [Store.setPage, List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  by_cases hrn : (r.name == p.name) = true
  · simp only [Page.withChange, hrn, ite_true] at hl ⊢
    exact .inl rfl
  · simp only [Page.withChange, hrn, Bool.false_eq_true, ite_false] at hl ⊢
    rcases h r hr hl with hs | hm
    · exact .inl hs
    · right
      have hpn : p.name = n := by simpa using List.find?_some hp
      simp only [List.map_cons, List.mem_cons] at hm
      rcases hm with hm | hm
      · exact absurd (by simp [hm, hpn]) hrn
      · exact hm

theorem admitWrites_seen (H : Hash) (res : List Entry) (V : List (String × String)) (s : Store)
    (pending : List Write) (refused : List RefusedWrite)
    (h : ∀ p ∈ s.pages, (V.lookup p.name).isSome → p.seen.isSome ∨ p.name ∈ pending.map (·.1)) :
    ∀ p ∈ (admitWrites H res s pending refused).1.pages, (V.lookup p.name).isSome → p.seen.isSome :=
  admitWrites_ind H res (fun s pending _ out =>
      (∀ p ∈ s.pages, (V.lookup p.name).isSome → p.seen.isSome ∨ p.name ∈ pending.map (fun w : Write => w.1)) →
      ∀ p ∈ out.1.pages, (V.lookup p.name).isSome → p.seen.isSome)
    (fun _ _ h p hp hl => by
      rcases h p hp hl with hs | hm
      · exact hs
      · simp at hm)
    (fun s n md rest _ hn ih h => ih fun p hp hl => by
      rcases h p hp hl with hs | hm
      · exact .inl hs
      · simp only [List.map_cons, List.mem_cons] at hm
        rcases hm with hm | hm
        · exact absurd (List.find?_eq_none.1 hn p hp) (by simp [hm])
        · exact .inr hm)
    (fun s n md rest refused p hp _ ih h => by
      refine ih fun q hq hl => ?_
      have := seen_setPage hp (judgeAt H res s p md) h q hq hl
      exact this.imp_right fun hm => by simp only [List.map_append, List.mem_append]; exact .inl hm)
    (fun s n md rest refused p _ hp _ ih h => by
      refine ih fun q hq hl => ?_
      exact seen_setPage hp (judgeAt H res s p md) h q hq hl)
    s pending refused h

theorem mem_pendingAt {s : Store} {V : List (String × String)} {q : Page} (hq : q ∈ s.pages) {md : String}
    (hmd : V.lookup q.name = some md) (hne : ¬ some md = q.seen) : q.name ∈ (pendingAt s V).map (·.1) := by
  have hw : (q.name, md) ∈ (s.pages.filterMap fun p => (V.lookup p.name).bind fun md =>
      if some md == p.seen then none else some (p.name, md)) :=
    List.mem_filterMap.2 ⟨q, hq, by simp [hmd, hne]⟩
  refine List.mem_map.2 ⟨(q.name, md), ?_, rfl⟩
  simp only [pendingAt, List.mem_append, List.mem_mergeSort, List.mem_filter]
  by_cases hk : isKind q.name = true
  · exact .inl ⟨hw, hk⟩
  · exact .inr ⟨hw, by simpa using hk⟩

/-! ### The door: a refused write's pins hold where the open leaves them -/

theorem firstStale?_none_of_holds {store : VaultStore} :
    ∀ {fp : Footprint}, Footprint.Holds store fp → Footprint.firstStale? store fp = none
  | [], _ => rfl
  | p :: rest, h => by
    have hp := h p (List.mem_cons_self ..)
    have ih := firstStale?_none_of_holds fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [Footprint.firstStale?, hp]
    cases p.observed with
    | none => exact ih
    | some d => simp [Obend.Law.termEq_refl_local, ih]

/-- Pins that hold are admitted by the door. -/
theorem pinsHold_of_holds {store : VaultStore} {fp : Footprint} (h : Footprint.Holds store fp) :
    pinsHold store fp = true := by
  simp [pinsHold, admitFootprint, firstStale?_none_of_holds h]

/-- Pins read from a store hold there. -/
theorem pinsAt_holds (es : List Entry) (cells : List String) :
    Footprint.Holds (stateStore es) (pinsAt es cells) := by
  intro q hq
  obtain ⟨c, _, rfl⟩ := List.mem_map.1 hq
  rfl

theorem writtenAs_history {es : List Entry} {turn : Nat} {p : Page} {md : String} {G' : Graph} {env : Environment}
    {added : List AtomId} {res : List Entry} {m : String}
    (h : (writtenAs es turn p md G' added res env).note = some m) :
    (writtenAs es turn p md G' added res env).history = p.history := by
  unfold writtenAs at h ⊢
  split at h
  · simp at h
  · rfl

theorem editedAs_history {es : List Entry} {turn : Nat} {p : Page} {md : String} {G : Graph} {env : Environment}
    {b : Built} {res : List Entry} {m : String}
    (h : (editedAs es turn p md G b res env).note = some m) :
    (editedAs es turn p md G b res env).history = p.history := by
  by_cases hb : b.ops.isEmpty = true
  · simp only [editedAs, hb, ite_true] at h
    simp at h
  · simp only [editedAs, hb, Bool.false_eq_true, ite_false] at h ⊢
    exact writtenAs_history h

/-- A refused write leaves the page's history. -/
theorem ownerWrite_history_of_note {H : Hash} {es res : List Entry} {turn : Nat} {p : Page} {md m : String}
    {env : Environment}
    (h : (ownerWrite H es turn p md res env).note = some m) :
    (ownerWrite H es turn p md res env).history = p.history := by
  unfold ownerWrite at h ⊢
  revert h
  cases p.current with
  | none => intro h; exact writtenAs_history h
  | some G => intro h; exact editedAs_history h

/-- A page replaced by one of the same name, id and history leaves the store's entries. -/
theorem entries_setPage {s : Store} {n : String} {p q : Page} (hnd : (s.pages.map (·.name)).Nodup)
    (hp : s.page? n = some p) (hq : q.name = p.name) (hid : q.id = p.id) (hh : q.history = p.history) :
    (s.setPage q).entries = s.entries := by
  simp only [Store.entries, Store.setPage, List.filterMap_map]
  apply filterMap_congr'
  intro r hr
  simp only [Function.comp]
  split
  · rename_i h
    have hpm := List.mem_of_find?_eq_some hp
    have hrn : r.name = p.name := by rw [← hq]; exact beq_iff_eq.1 h
    have := eq_of_nodup_map hnd hr hpm hrn
    subst this
    simp [Page.current, hh, hid, hq]
  · rfl

theorem admitWrites_admitted (H : Hash) (res : List Entry) (s : Store) (pending : List Write)
    (refused : List RefusedWrite) (hnd : (s.pages.map (·.name)).Nodup)
    (h : ∀ r ∈ refused, pinsHold (stateStore s.entries) r.pins = true) :
    ∀ r ∈ (admitWrites H res s pending refused).2,
      pinsHold (stateStore (admitWrites H res s pending refused).1.entries) r.pins = true :=
  admitWrites_ind H res (fun s _ refused out =>
      (s.pages.map (fun q : Page => q.name)).Nodup →
      (∀ r ∈ refused, pinsHold (stateStore s.entries) r.pins = true) →
      ∀ r ∈ out.2, pinsHold (stateStore out.1.entries) r.pins = true)
    (fun _ _ _ h => h)
    (fun _ _ _ _ _ _ ih hnd h => ih hnd h)
    (fun s n md rest refused p hp _ ih hnd _ =>
      ih (by rw [afterAdmit, setPage_names]; exact hnd) fun r hr => by
        simp only [held, List.mem_filter] at hr
        exact hr.2)
    (fun s n md rest refused p m hp hnote ih hnd h =>
      ih (by rw [afterAdmit, setPage_names]; exact hnd) fun r hr => by
        have hent : (afterAdmit H res s p md).entries = s.entries :=
          entries_setPage hnd hp rfl rfl (ownerWrite_history_of_note hnote)
        rcases List.mem_append.1 hr with hr | hr
        · rw [hent]; exact h r hr
        · simp only [List.mem_singleton] at hr
          subst hr
          simp only [pinsOf]
          exact pinsHold_of_holds (pinsAt_holds _ _))
    s pending refused hnd h

theorem withFresh_names (H : Hash) (s : Store) (V : List (String × String)) :
    (withFresh H s V).pages.map (·.name) = s.pages.map (·.name) ++ freshNames s V := by
  simp [withFresh, freshPages_names]

theorem openAdmission_names (H : Hash) (s : Store) (V : List (String × String)) :
    (openAdmission H s V).1.pages.map (·.name) = s.pages.map (·.name) ++ freshNames s V := by
  rw [openAdmission, admitWrites_names, withFresh_names]

theorem withFresh_nodup (H : Hash) (s : Store) (V : List (String × String))
    (hs : (s.pages.map (·.name)).Nodup) (hV : (V.map (·.1)).Nodup) :
    ((withFresh H s V).pages.map (·.name)).Nodup := by
  rw [withFresh_names, List.nodup_append]
  refine ⟨hs, nodup_fresh s V hV, ?_⟩
  intro a ha b hb hab
  subst hab
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
  have := (List.mem_filter.1 he).2
  obtain ⟨p, hp, hpn⟩ := List.mem_map.1 ha
  simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at this
  exact this p hp hpn

theorem openAdmission_nodup (H : Hash) (s : Store) (V : List (String × String))
    (hs : (s.pages.map (·.name)).Nodup) (hV : (V.map (·.1)).Nodup) :
    ((openAdmission H s V).1.pages.map (·.name)).Nodup := by
  rw [openAdmission, admitWrites_names]; exact withFresh_nodup H s V hs hV

theorem openAdmission_seen (H : Hash) (s : Store) (V : List (String × String)) :
    ∀ p ∈ (openAdmission H s V).1.pages, (V.lookup p.name).isSome → p.seen.isSome := by
  refine admitWrites_seen H _ V _ _ _ fun q hq hlq => ?_
  obtain ⟨md, hmd⟩ := Option.isSome_iff_exists.1 hlq
  by_cases hseen : some md = q.seen
  · exact .inl (by rw [← hseen]; rfl)
  · exact .inr (mem_pendingAt hq hmd hseen)

theorem openAdmission_cover (H : Hash) (s : Store) (V : List (String × String)) :
    ∀ e ∈ V, e.1 ∈ (openAdmission H s V).1.pages.map (·.name) := by
  intro e he
  rw [openAdmission_names, List.mem_append]
  by_cases h : s.pages.any (·.name == e.1) = true
  · obtain ⟨p, hp, hpn⟩ := List.any_eq_true.1 h
    exact .inl (List.mem_map.2 ⟨p, hp, by simpa using hpn⟩)
  · exact .inr (List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simpa using h⟩, rfl⟩)

/-- **An open leaves no stale refusal.** Every write the open refused was judged at pins that hold
in the store the open leaves (the door admits them there): the verdict is the turn's at that store,
and the files say what the store would say again. -/
theorem open_admitted (H : Hash) (s : Store) (V : List (String × String))
    (hs : (s.pages.map (·.name)).Nodup) (hV : (V.map (·.1)).Nodup) :
    ∀ r ∈ (openAdmission H s V).2, pinsHold (stateStore (openAdmission H s V).1.entries) r.pins = true := by
  refine admitWrites_admitted H _ _ _ _ (withFresh_nodup H s V hs hV) fun r hr => ?_
  obtain ⟨p, _, hp⟩ := List.mem_filterMap.1 hr
  simp only [Option.bind_eq_some_iff] at hp
  obtain ⟨md, _, hp⟩ := hp
  split at hp
  · cases hp
    exact pinsHold_of_holds (pinsAt_holds _ _)
  · cases hp

/-- **Opening twice is a no-op.** For every store whose page names are distinct and every vault the
reader accepts (file names distinct, as a directory's are): open it, write the files the open says
to write, and open again; the second open changes neither the store nor any file. The second open
is quiet: every admitted write is in its file, every refused write's file keeps the refused text,
and no refused write has a reason to be judged again (`open_admitted`). -/
theorem open_idem (H : Hash) (s : Store) (V : List (String × String))
    (hs : (s.pages.map (·.name)).Nodup) (hV : (V.map (·.1)).Nodup) :
    openVault H (openVault H s V).store (overwrite V (openVault H s V).writes) =
      ⟨(openVault H s V).store, []⟩ := by
  by_cases hq : quiet s V = true
  · simp only [openVault, hq, ite_true, overwrite_nil]
  · have hq' : quiet s V = false := by simpa using hq
    simp only [openVault, hq', Bool.false_eq_true, ite_false]
    have hq2 : quiet (settle H (openAdmission H s V).1)
        (overwrite V (writesFor (settle H (openAdmission H s V).1) V)) = true :=
      quiet_after_settle H _ V (openAdmission_nodup H s V hs hV) (openAdmission_seen H s V)
        (openAdmission_cover H s V)
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

/-- A write by `who` of the version `G'` of the page `p`, committed; `poster` is whose text it is
when not `who`'s own (a selection: the kept candidate's author). -/
def Store.write (s : Store) (p : Page) (G' : Graph) (added : List (AtomId × String)) (who : Actor)
    (poster : Option String := none) : Except String Store := do
  match commit s.entries p G' added who s.turn (poster.getD who.name) (env := s.environment) with
  | .ok ch => return s.setPage (p.withChange ch)
  | .error msg => throw (p.name ++ ": " ++ msg)

/-- **A page write lands**: each of its versions in turn, through `Store.write`, the one judgment and
the one landing rule every write of the store goes through. -/
def Store.writeVersions (s : Store) (page : String) (poster : Option String) :
    List (Graph × List (AtomId × String)) → Except String Store
  | [] => .ok s
  | (G, added) :: rest =>
    match s.page? page with
    | some p =>
      match s.write p G added .owner poster with
      | .ok s' => s'.writeVersions page poster rest
      | .error e => .error e
    | none => .error (page ++ ": no such page")

def Store.writeText (s : Store) (page : String) (w : PageWrite) : Except String Store :=
  s.writeVersions page w.poster w.versions

/-! ### Merge -/

/-- The merge of two versions of a page: their union where they agree on every atom both store. -/
def mergePage (A B : Graph) : Option Graph := if compatB A B then some (Graph.merge A B) else none

/-- **The merge is the pushout** of the two versions: above both, below every page above both. -/
theorem mergePage_pushout {A B M : Graph} (h : mergePage A B = some M) : IsPushout A B M := by
  unfold mergePage at h
  split at h
  · rename_i hc; cases h; exact merge_isPushout (compatible_of_compatB hc)
  · cases h

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
  -- the selection is `who`'s act; the text is its author's (the first author among the kept
  -- candidate's atoms that is not "as it is"; else the owner's)
  let poster := (alts[i - 1]?.bind fun (_, segs) => (segAtoms segs).findSome? fun a =>
    match p.authors.lookup a with
    | some w => if w == "as it is" then none else some w
    | none => none).getD "owner"
  s.write p (G.apply (selectPatch alts (i - 1))) [] who (some poster)

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
  let fields := (frontFields (settled G)).filter fun (key, _) => (lawKey key).isNone && key != "kind" && key != "parents" && key != "environment"
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
      let fields := (frontFields (settled G)).filter fun (key, _) => (lawKey key).isNone && key != "kind" && key != "parents" && key != "environment"
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
