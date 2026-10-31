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

/-- A page is a kind when it is a folder's `_kind`. -/
def isKind (name : String) : Bool := baseName name == "_kind"

/-- The kinds a page is an instance of, innermost first: its folder's `_kind`, then each enclosing
folder's. A kind page itself is an instance of none. -/
def kindsOf (name : String) : List String :=
  if isKind name then [] else
  let parts := (name.splitOn "/").dropLast
  ((List.range (parts.length + 1)).reverse.map fun k =>
    "/".intercalate (parts.take k ++ ["_kind"]))

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

/-- The laws of a page as written in a version, each named `PAGE: NAME`, with its text. -/
def lawsIn (pageName : String) (G : Graph) : Except String (List (String × LawExpr × String)) :=
  (lawLines (settled G)).mapM fun (n, txt) =>
    match Obend.Spec.Law.parse txt with
    | .ok e => .ok (pageName ++ ": " ++ n, e, txt)
    | .error msg => .error (pageName ++ ": law " ++ n ++ ": " ++ msg)

/-- The laws a write of `pageName` (at version `G`) is judged by: its own, then each kind's,
innermost first. -/
def lawsFor (es : List Entry) (pageName : String) (G : Graph) : Except String (List (String × LawExpr × String)) := do
  let own ← lawsIn pageName G
  let kinds ← (kindsOf pageName).mapM fun k =>
    match es.find? (·.name == k) with
    | some e => lawsIn k e.graph
    | none => .ok []
  return own ++ kinds.flatten

/-- What a write leaves of a page. -/
structure Change where
  history : List Graph
  seen : String
  authors : List (AtomId × String)
  note : Option String

def Page.withChange (p : Page) (c : Change) : Page :=
  { p with history := c.history, seen := some c.seen, authors := c.authors, note := c.note }

/-- Why a write was refused, said to a person. -/
def refusalText (pageName : String) (laws : List (String × LawExpr × String)) (law reason : String)
    (facts : Facts) (old : Option Obend.Core.Data.Data) (new : Obend.Core.Data.Data) (front : List String) : String :=
  let owner := ((law.splitOn ": ").head?).getD law
  let kindNote := if owner != pageName && isKind owner then
      " (the kind of " ++ (if folderOf owner == "" then "the vault" else folderOf owner ++ "/") ++
        ", an ancestor of " ++ pageName ++ ")"
    else ""
  let who := if owner == pageName then "its law " ++ String.ofList ((law.toList.drop (owner.length + 2)))
    else law ++ kindNote
  match laws.find? (·.1 == law) with
  | some (_, e, txt) =>
    "refused by " ++ who ++ ": `" ++ txt ++ "` does not hold; " ++ suggest e facts old new front
  | none => "refused by " ++ who ++ ": " ++ reason

/-- **Commit a write**: judge the new version `G'` of page `p` by its laws, and on admission append
it. A change of a law line is the owner's, or a member's granted `relaw`; it is judged as the
adoption of the new laws over the page as written. A birth is judged as a first write. -/
def commit (es : List Entry) (p : Page) (G' : Graph) (added : List (AtomId × String)) (who : Actor)
    (turn : Nat) : Except String Change := do
  let authors := p.authors ++ added
  let p' := { p with authors := authors }
  let v := p.history.length
  let newLaws ← lawsFor es p.name G'
  let (occ, laws, oldMs) ← match p.current with
    | none => pure (Occ.birth, newLaws, [])
    | some G =>
      let oldLaws ← lawsFor es p.name G
      if lawLines (settled G) == lawLines (settled G') then pure (Occ.write, oldLaws, measures G (v - 1))
      else if who.may "relaw" p.name then pure (Occ.adopt, newLaws, measures G (v - 1))
      else throw ("refused: changing a law line is the owner's (" ++ who.name ++
        " has no relaw grant on " ++ p.name ++ ")")
  let newMs := measures G' v
  let lin := laws.map fun (n, e, _) => (n, e)
  let keys := sortNames (newMs.map (·.1) ++ oldMs.map (·.1) ++ lin.flatMap fun l => l.2.fields)
  let S := stateTy keys
  let n := stateOf keys newMs
  let o := if oldMs.isEmpty then n else stateOf keys oldMs
  let facts : Facts := ⟨some who.id, some who.id, v, turn⟩
  match judge S p.name lin o n (requestOf who.name occ facts) with
  | .admitted =>
    pure ⟨p.history ++ [G'], render G' p.name p'.who, authors, none⟩
  | .refused law reason =>
    throw (refusalText p.name laws law reason facts (occ.old o n) n
      ((scalarFields (settled G')).map (·.1)))
  | .undecided why => throw ("undecided: " ++ why)

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
  -- Only the view's marks changed (one deleted, say): nothing to write; the view is redrawn.
  if same then ⟨p.history, md, p.authors, p.note⟩ else
  match commit es p G' (added.map (·, "owner")) .owner turn with
  | .ok ch => ch
  | .error msg => ⟨p.history, md, p.authors, some msg⟩

/-- One page at open: unchanged if its file is missing or is what the store last saw. -/
def openPage (H : Hash) (es : List Entry) (turn : Nat) (p : Page) (file : Option String) : Page :=
  match file with
  | none => p
  | some md => if some md == p.seen then p else p.withChange (ownerWrite H es turn p md)

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
    acc ++ [⟨n, pageIdFor H taken n, [], none, [], none⟩]) [])

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
  by_cases h : (some md == p.seen) = true
  · simp only [h, ite_true]; exact ⟨md, (beq_iff_eq.1 h).symm⟩
  · simp only [h, Bool.false_eq_true, ite_false]; exact ⟨_, rfl⟩

theorem freshPages_names (H : Hash) (s : Store) (names : List String) :
    (freshPages H s names).map (·.name) = names := by
  unfold freshPages
  suffices ∀ (acc : List Page), (names.foldl (fun (acc : List Page) n =>
      let taken := fun q => s.pages.any (·.id == q) || acc.any (·.id == q)
      acc ++ [⟨n, pageIdFor H taken n, [], none, [], none⟩]) acc).map (·.name) = acc.map (·.name) ++ names by
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

/-- **Select** candidate `i` (from 1) of section `k` (from 1) of a page. -/
def selectIn (s : Store) (who : Actor) (page : String) (k i : Nat) : Except String Store := do
  let some p := s.page? page | throw ("no page named " ++ page)
  unless who.may "select" page do
    throw (who.name ++ " may post to " ++ page ++ " but not select on it (no select grant)")
  let some G := p.current | throw (page ++ " has no version yet")
  let some alts := (sections G)[k - 1]? | throw (page ++ " has no section " ++ toString k)
  unless 1 ≤ i && i ≤ alts.length do
    throw ("section " ++ toString k ++ " of " ++ page ++ " has " ++ toString alts.length ++ " candidates")
  s.write p (G.apply (selectPatch alts (i - 1))) [] who

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
