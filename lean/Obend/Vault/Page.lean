module
/-
# Obend.Vault.Page — a page's markdown: its frontmatter, its measures, its rendering with sections,
and the patch a changed file is

`Obend.Doc` reads markdown into a page graph and renders a version back. A vault on disk needs
three more things of a page, and this module is them:

* **Frontmatter.** A page may open with `---` lines. Every `key: value` line there is a field, a
  natural (`status: 2`) or a boolean (`draft: true`, read as 1); every `law: EXPR` or
  `law NAME: EXPR` line is a law of the page (`Obend.Vault.Law`). The frontmatter is ordinary
  text of the page: an edit that changes a law line changes the law.
* **Measures.** What a law may read of a page besides its fields: `bytes`, `lines`, `words` (of the
  body), `links` (identity cites), `embeds`, `quotes` (block and byte cites), `sections` (open
  conflicts), `version`.
* **Rendering with sections.** `pieces` renders a version as `Graph.source` does, except that a
  conflict (a section with two or more live candidates and no selection, `conflict_is_section`) is
  shown as a block a person can read and act on:

      <<<<<<< section 1 · candidate 1 (owner) · keep it: obend select Alpha 1 1
      Ours.
      ======= candidate 2 (scout) · keep it: obend select Alpha 1 2
      Theirs.
      >>>>>>> section 1

  Every piece remembers the atom it shows, or that it is a section line.
* **The patch a changed file is.** `align` lines a file's tokens up with a version's pieces (a
  longest common subsequence). `editPatch` is an author's write: unmatched pieces are deleted,
  unmatched tokens are added, chained after what precedes them and before what follows; where the
  person deleted a section's lines and kept its candidates in an order, the candidates are
  connected in that order, which resolves the section by hand. `postPatch` is a member's
  proposal: nothing is deleted; each changed stretch becomes a section whose candidates are the
  stretch as it is (or an empty run, "as it is") and the stretch as proposed (or an empty run, "drop
  it"). `selectPatch` keeps one candidate of a section and deletes the others' runs. New atoms are
  named by a hash of where they go and what they hold (`freshId`), so two replicas that make the
  same edit name it the same and their merge is clean (`compatible_of_addressed`).
-/
public import Obend.Doc
@[expose] public section

namespace Obend.Vault

set_option autoImplicit false

open Obend.Doc Obend.Doc.Graph Obend.Digest.HashBytes

/-! ## Text -/

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- Trim spaces at both ends. -/
def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- Split at the first `:`. -/
def splitColon (s : String) : Option (String × String) :=
  let l := s.toList
  if l.contains ':' then
    some (trim (String.ofList (l.takeWhile (· != ':'))), trim (String.ofList ((l.dropWhile (· != ':')).drop 1)))
  else none

/-- The frontmatter lines (between a first line `---` and the next `---`) and the body after it. -/
def splitFront (src : String) : List String × String :=
  match src.splitOn "\n" with
  | first :: rest =>
    if trim first == "---" then
      let fm := rest.takeWhile fun l => trim l != "---"
      let after := rest.dropWhile fun l => trim l != "---"
      match after with
      | _ :: body => (fm, "\n".intercalate body)
      | [] => ([], src)
    else ([], src)
  | [] => ([], src)

/-- The `key: value` lines of the frontmatter. -/
def frontFields (src : String) : List (String × String) :=
  (splitFront src).1.filterMap splitColon

/-- A law line's name: `law` alone is `law`; `law NAME` is `NAME`. -/
def lawKey (key : String) : Option String :=
  if key == "law" then some "law"
  else match key.splitOn " " with
    | ["law", name] => if name.isEmpty then none else some name
    | _ => none

/-- The law lines of a page: `(name, text)`. -/
def lawLines (src : String) : List (String × String) :=
  (frontFields src).filterMap fun (k, v) => (lawKey k).map fun n => (n, v)

/-- The scalar fields of a page's frontmatter: naturals, and booleans as 1 and 0. -/
def scalarFields (src : String) : List (String × Nat) :=
  (frontFields src).filterMap fun (k, v) =>
    if (lawKey k).isSome || k.isEmpty || k.contains ' ' then none
    else if v == "true" then some (k, 1)
    else if v == "false" then some (k, 0)
    else v.toNat?.map fun n => (k, n)

/-- Words: maximal runs of non-space characters. -/
def wordCount (s : String) : Nat :=
  (s.toList.foldl (fun (acc : Nat × Bool) c =>
    if isSpace c then (acc.1, false) else if acc.2 then acc else (acc.1 + 1, true)) (0, false)).1

/-- Lines: newlines, plus a last line that does not end in one. -/
def lineCount (s : String) : Nat :=
  let l := s.toList
  l.count '\n' + (if l.isEmpty || l.getLast? == some '\n' then 0 else 1)

/-! ## Rendering a version, with its sections -/

/-- What a section line is. -/
inductive Mark
  | opening
  | separator
  | closing
deriving DecidableEq, Repr, Inhabited

/-- A piece of a page's rendering: an atom's text, or a section line. -/
inductive Piece
  | atom (a : AtomId) (text : String)
  | mark (m : Mark) (text : String)
deriving DecidableEq, Repr, Inhabited

def Piece.text : Piece → String
  | .atom _ t => t
  | .mark _ t => t

/-- How a content reads in a page's source (`Graph.atomText` for a stored atom). -/
def contentText : Content → String
  | .text s => s
  | .cite n c => match c.span with
    | .page => "![[" ++ n ++ "]]"
    | _ => "[[" ++ n ++ "]]"
  | .field _ _ => ""

theorem atomText_eq (G : Graph) (a : AtomId) :
    G.atomText a = match G.label a with | some c => contentText c | none => "" := by
  unfold Graph.atomText; cases G.label a with
  | none => rfl
  | some c => cases c <;> rfl

/-- The section line that opens section `k` with its first candidate. -/
def openLine (page : String) (k : Nat) (who : String) : String :=
  "<<<<<<< section " ++ toString k ++ " · candidate 1 (" ++ who ++ ") · keep it: obend select " ++ page ++
    " " ++ toString k ++ " 1\n"

/-- The line before candidate `i` of section `k`. -/
def sepLine (page : String) (k i : Nat) (who : String) : String :=
  "======= candidate " ++ toString i ++ " (" ++ who ++ ") · keep it: obend select " ++ page ++ " " ++
    toString k ++ " " ++ toString i ++ "\n"

def closeLine (k : Nat) : String := ">>>>>>> section " ++ toString k ++ "\n"

mutual
/-- Segments as pieces; `n` is the number of sections met so far, sections numbered in the order
they are met. -/
def segPieces (f : AtomId → String) (page : String) (who : AtomId → String) :
    List Segment → Nat → List Piece × Nat
  | [], n => ([], n)
  | s :: ss, n =>
    let (p, n1) := onePiece f page who s n
    let (q, n2) := segPieces f page who ss n1
    (p ++ q, n2)
def onePiece (f : AtomId → String) (page : String) (who : AtomId → String) : Segment → Nat → List Piece × Nat
  | .run a, n => ([.atom a (f a)], n)
  | .conflict alts, n => altPieces f page who (n + 1) 1 alts (n + 1)
/-- The candidates of section `k`, the `i`th first. -/
def altPieces (f : AtomId → String) (page : String) (who : AtomId → String) (k : Nat) :
    Nat → List (AtomId × List Segment) → Nat → List Piece × Nat
  | _, [], n => ([.mark .closing (closeLine k)], n)
  | i, (h, ss) :: rest, n =>
    let hdr : Piece := if i = 1 then .mark .opening (openLine page k (who h))
      else .mark .separator (sepLine page k i (who h))
    let (p, n1) := segPieces f page who ss n
    let (q, n2) := altPieces f page who k (i + 1) rest n1
    (hdr :: p ++ q, n2)
end

/-- A version's rendering, piece by piece. -/
def pieces (G : Graph) (page : String) (who : AtomId → String) : List Piece :=
  (segPieces G.atomText page who G.content 0).1

/-- A version's rendering with each atom read by `f` (the view: `Obend.Doc.viewAtom` marks a cite
whose facts fail, `![[Beta]]{behind}`). -/
def renderWith (f : AtomId → String) (G : Graph) (page : String) (who : AtomId → String) : String :=
  String.join ((segPieces f page who G.content 0).1.map Piece.text)

/-- A version's rendering as text. -/
def render (G : Graph) (page : String) (who : AtomId → String) : String :=
  String.join ((pieces G page who).map Piece.text)

mutual
/-- The sections of a version, in the order the rendering numbers them. -/
def segSections : List Segment → List (List (AtomId × List Segment))
  | [] => []
  | .run _ :: ss => segSections ss
  | .conflict alts :: ss => alts :: altSections alts ++ segSections ss
def altSections : List (AtomId × List Segment) → List (List (AtomId × List Segment))
  | [] => []
  | (_, ss) :: rest => segSections ss ++ altSections rest
end

def sections (G : Graph) : List (List (AtomId × List Segment)) := segSections G.content

mutual
/-- The atoms a stretch of segments shows. -/
def segAtoms : List Segment → List AtomId
  | [] => []
  | .run a :: ss => a :: segAtoms ss
  | .conflict alts :: ss => altAtoms alts ++ segAtoms ss
def altAtoms : List (AtomId × List Segment) → List AtomId
  | [] => []
  | (_, ss) :: rest => segAtoms ss ++ altAtoms rest
end

/-! ## The view's marks, and the reader that strips them

A file shows its page at the current view: a cite whose facts fail carries their names,
`![[Beta]]{behind}`, `[[Beta#^b]]{behind}`, `[[Gamma]]{missing}` (`Obend.Doc.viewAtom`). The reader
strips exactly those marks before it reads a file (`stripToks`), so a mark is never read as an edit:
`dropMark_mark` (a mark followed by anything strips to that anything) and `stripToks_mark` (a mark
after a wikilink is gone from what the reader reads). -/

/-- The marks the view writes: the reasons of the facts a cite rests on, in `citeFacts`'s order. -/
def allMarks : List (List Char) :=
  ["behind".toList, "unverified".toList, "missing".toList, "unverified,behind".toList]

/-- A mark as written after a wikilink. -/
def markChars (m : List Char) : List Char := '{' :: m ++ ['}']

/-- Read up to the first `}`: what is before it and what is after. -/
def closeAt : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: r, acc => if c = '}' then some (acc.reverse, r) else closeAt r (c :: acc)

/-- Drop a mark of the view at the head of a text. -/
def dropMark (l : List Char) : List Char :=
  match l with
  | c :: rest =>
    if c = '{' then
      match closeAt rest [] with
      | some (body, after) => if allMarks.contains body then after else l
      | none => l
    else l
  | [] => l

/-- The tokens of a file with the view's marks stripped: a mark right after a wikilink or an embed. -/
def stripToks : List Tok → List Tok
  | [] => []
  | .link n :: .text t :: rest =>
    let t' := dropMark t
    .link n :: (if t' = [] then stripToks rest else .text t' :: stripToks rest)
  | .embed n :: .text t :: rest =>
    let t' := dropMark t
    .embed n :: (if t' = [] then stripToks rest else .text t' :: stripToks rest)
  | t :: rest => t :: stripToks rest

theorem closeAt_append {m : List Char} (hm : '}' ∉ m) (s acc : List Char) :
    closeAt (m ++ '}' :: s) acc = some (acc.reverse ++ m, s) := by
  induction m generalizing acc with
  | nil => simp [closeAt]
  | cons c m ih =>
    have hc : c ≠ '}' := fun h => hm (h ▸ List.mem_cons_self)
    simp only [List.cons_append, closeAt, hc, ite_false]
    rw [ih (fun h => hm (List.mem_cons_of_mem _ h))]
    simp

/-- **A mark strips away.** A mark of the view (one of `allMarks`, which hold no `}`) followed by any
text strips to that text. -/
theorem dropMark_mark {m : List Char} (hm : m ∈ allMarks) (hc : '}' ∉ m) (s : List Char) :
    dropMark (markChars m ++ s) = s := by
  have : markChars m ++ s = '{' :: (m ++ '}' :: s) := by simp [markChars]
  rw [this]
  simp only [dropMark, ite_true]
  rw [closeAt_append hc]
  simp [hm]

/-- **What the reader reads of a marked wikilink is the wikilink.** -/
theorem stripToks_mark {m : List Char} (hm : m ∈ allMarks) (hc : '}' ∉ m) (n s : List Char)
    (rest : List Tok) (hs : s ≠ []) :
    stripToks (.embed n :: .text (markChars m ++ s) :: rest) = .embed n :: .text s :: stripToks rest ∧
    stripToks (.link n :: .text (markChars m ++ s) :: rest) = .link n :: .text s :: stripToks rest := by
  simp [stripToks, dropMark_mark hm hc, hs]

/-! ## Measures -/

/-- The SETTLED text of a version: its runs outside every section. A candidate posted to a section
is not yet the page's: its law lines are not laws and its words are not counted until it is
selected. -/
def settled (G : Graph) : String :=
  String.join (G.content.filterMap fun | .run a => some (G.atomText a) | _ => none)

/-- The live cites of a version, by span kind: identity links, embeds, block and byte quotes. -/
def citeCounts (G : Graph) : Nat × Nat × Nat :=
  (G.atoms.map (·.1)).eraseDups.foldl (fun (acc : Nat × Nat × Nat) a =>
    if G.run a then match G.label a with
      | some (.cite _ c) => match c.span with
        | .identity => (acc.1 + 1, acc.2)
        | .page => (acc.1, acc.2.1 + 1, acc.2.2)
        | _ => (acc.1, acc.2.1, acc.2.2 + 1)
      | _ => acc
    else acc) (0, 0, 0)

/-- What a law reads of a version: its measures and its frontmatter's scalar fields (a measure
wins over a field of the same name). -/
def measures (G : Graph) (version : Nat) : List (String × Nat) :=
  let src := settled G
  let body := (splitFront src).2
  let (links, embeds, quotes) := citeCounts G
  let ms : List (String × Nat) :=
    [("bytes", (bytes src).length), ("embeds", embeds), ("lines", lineCount body), ("links", links),
     ("quotes", quotes), ("sections", (sections G).length), ("version", version), ("words", wordCount body)]
  ms ++ (scalarFields src).filter fun (k, _) => !(ms.any (·.1 == k))

/-! ## Lining a file up with a version -/

/-- One step of an alignment: a piece kept (matched by a token), a piece the file dropped, a token
the version lacks. -/
inductive Step
  | keep (i j : Nat)
  | del (i : Nat)
  | ins (j : Nat)
deriving DecidableEq, Repr

/-- A longest common subsequence of `a` and `b`, as steps in order (a deletion before an insertion
where both are possible). -/
def lcs (a b : Array String) : List Step := Id.run do
  let n := a.size
  let m := b.size
  -- `t[i * (m + 1) + j]`: the LCS length of `a[i:]` and `b[j:]`.
  let mut t : Array Nat := Array.replicate ((n + 1) * (m + 1)) 0
  for ii in [0:n] do
    let i := n - 1 - ii
    for jj in [0:m] do
      let j := m - 1 - jj
      let v := if a[i]! == b[j]! then t[(i + 1) * (m + 1) + (j + 1)]! + 1
        else max t[(i + 1) * (m + 1) + j]! t[i * (m + 1) + (j + 1)]!
      t := t.set! (i * (m + 1) + j) v
  let mut out : Array Step := #[]
  let mut i := 0
  let mut j := 0
  for _ in [0:n + m] do
    if i < n && j < m then
      if a[i]! == b[j]! then
        out := out.push (.keep i j); i := i + 1; j := j + 1
      else if t[(i + 1) * (m + 1) + j]! ≥ t[i * (m + 1) + (j + 1)]! then
        out := out.push (.del i); i := i + 1
      else
        out := out.push (.ins j); j := j + 1
    else if i < n then
      out := out.push (.del i); i := i + 1
    else if j < m then
      out := out.push (.ins j); j := j + 1
  return out.toList

/-- An alignment step with what it carries. -/
inductive Al
  | keepAtom (a : AtomId) (c : Content)
  | keepMark (m : Mark)
  | delAtom (a : AtomId)
  | delMark
  | ins (c : Content)
deriving DecidableEq, Repr, Inhabited

/-- Line a version's pieces up with a file's contents, token by token. -/
def alignTokens (ps : List Piece) (cs : List Content) : List Al :=
  let pa := ps.toArray
  let ca := cs.toArray
  (lcs (pa.map Piece.text) (ca.map contentText)).map fun
    | .keep i j => match pa[i]! with
      | Piece.atom a _ => Al.keepAtom a ((ca[j]?).getD (.text ""))
      | Piece.mark m _ => Al.keepMark m
    | .del i => match pa[i]! with
      | Piece.atom a _ => Al.delAtom a
      | Piece.mark _ _ => Al.delMark
    | .ins j => Al.ins ((ca[j]?).getD (.text ""))

/-- Whether an alignment step ends a line on both sides: a kept atom whose text ends a line, or a
kept section line. -/
def Al.sync : Al → Bool
  | .keepAtom _ c => (contentText c).endsWith "\n"
  | .keepMark _ => true
  | _ => false

/-- Whether a step changes the page's atoms. -/
def Al.dirty : Al → Bool
  | .delAtom _ | .ins _ => true
  | _ => false

/-- Close a stretch of steps between two line ends: if it changes anything, its kept atoms are
re-written too (deleted and added again), its deletions first, so a change is always of whole
lines, as a person reads it. -/
def widenStretch (seg : List Al) : List Al :=
  if seg.any Al.dirty then
    (seg.filterMap fun st => match st with
      | .delAtom a => some (Al.delAtom a)
      | .keepAtom a _ => some (Al.delAtom a)
      | .delMark => some Al.delMark
      | _ => none) ++
    (seg.filterMap fun st => match st with
      | .ins c => some (Al.ins c)
      | .keepAtom _ c => some (Al.ins c)
      | _ => none)
  else seg

/-- An alignment widened to whole lines (`widenStretch` on each stretch between line ends). -/
def widen (al : List Al) : List Al :=
  let (out, seg) := al.foldl (fun (acc : List Al × List Al) st =>
    if st.sync then (acc.1 ++ widenStretch (acc.2 ++ [st]), []) else (acc.1, acc.2 ++ [st])) ([], [])
  out ++ widenStretch seg

/-- Line a version's pieces up with a file's contents, changes widened to whole lines. -/
def align (ps : List Piece) (cs : List Content) : List Al := widen (alignTokens ps cs)

/-! ## Fresh atoms -/

/-- A natural from the first four bytes of a digest. -/
def natOf4 (b : List UInt8) : Nat := (b.take 4).foldl (fun n x => n * 256 + x.toNat) 0

/-- A key for a content: what it holds, written out. -/
def contentKey : Content → String
  | .text s => "t:" ++ s
  | .cite n c => "c:" ++ n ++ ":" ++ toString c.page
  | .field n v => "f:" ++ n ++ "=" ++ v

/-- An atom identity named by a hash of `salt`, the first not `taken` (probing with a counter). -/
def freshId (H : Hash) (taken : AtomId → Bool) (salt : String) : AtomId :=
  go 0 64
where
  go (k : Nat) : Nat → AtomId
    | 0 => 1 + natOf4 (H (bytes (salt ++ "#" ++ toString k)))
    | fuel + 1 =>
      let id := 1 + natOf4 (H (bytes (salt ++ "#" ++ toString k)))
      if taken id then go (k + 1) fuel else id

/-- The salt of an atom added after `prev` and before `next`, holding `c`, by `author`. -/
def saltOf (prev : AtomId) (next : Option AtomId) (c : Content) (author : String) : String :=
  toString prev ++ "|" ++ toString (next.getD 0) ++ "|" ++ author ++ "|" ++ contentKey c

/-! ## The patches -/

/-- The first atom kept after position `j`, skipping the other candidates of a section kept open
(an insertion at the end of one candidate goes before the section's rejoin, not before the next
candidate). -/
def nextAnchor (al : Array Al) (j : Nat) : Option AtomId := Id.run do
  let mut skipping := false
  for k in [j:al.size] do
    match al[k]! with
    | .keepAtom a _ => if !skipping then return some a
    | .keepMark .separator => skipping := true
    | .keepMark .closing => skipping := false
    | _ => pure ()
  return none

/-- The result of building a patch: the operations, and the atoms it added. -/
structure Built where
  ops : Patch
  added : List AtomId
  /-- the empty runs added to stand for "as it is" in a member's proposal -/
  asIs : List AtomId := []
deriving Repr

/-- **An author's write.** Pieces the file dropped are deleted; tokens it added are added after what
precedes them and before what follows; candidates whose section lines were deleted are ordered as
the file orders them. -/
def editPatch (H : Hash) (G : Graph) (al : List Al) (author : String) : Built := Id.run do
  let arr := al.toArray
  let mut ops : Array Op := #[]
  let mut added : Array AtomId := #[]
  let mut cur := G
  let mut prev : AtomId := root
  let mut cut := false
  let mut stack : List AtomId := []
  for i in [0:arr.size] do
    match arr[i]! with
    | .delAtom a =>
      ops := ops.push (.delete a); cur := cur.step (.delete a)
    | .delMark => cut := true
    | .keepMark m =>
      match m with
      | .opening => stack := prev :: stack
      | .separator => prev := stack.headD prev
      | .closing => stack := stack.tail
      cut := false
    | .keepAtom a _ =>
      if cut && !cur.beforeB prev a then
        ops := ops.push (.connect prev a); cur := cur.step (.connect prev a)
      prev := a; cut := false
    | .ins c =>
      let next := nextAnchor arr (i + 1)
      let taken := added
      let id := freshId H (fun x => cur.present x || taken.contains x) (saltOf prev next c author)
      ops := ops.push (.add id c prev); cur := cur.step (.add id c prev)
      if let some b := next then
        ops := ops.push (.connect id b); cur := cur.step (.connect id b)
      added := added.push id
      prev := id; cut := false
  return { ops := ops.toList, added := added.toList }

/-- The empty run that stands for "as it is" or "drop it" in a member's proposal. -/
def blank : Content := .text ""

/-- **A member's proposal.** Nothing is deleted. Each changed stretch, between the kept atoms `a` and
`b`, becomes a section after `a`: its candidates are the stretch as it is (the empty run "as it is"
where the stretch is an insertion) and the stretch as proposed (the empty run "drop it" where it is
a deletion), each ordered before `b`. -/
def postPatch (H : Hash) (G : Graph) (al : List Al) (member : String) : Built := Id.run do
  let arr := al.toArray
  let mut ops : Array Op := #[]
  let mut added : Array AtomId := #[]
  let mut asIs : Array AtomId := #[]
  let mut cur := G
  let mut anchor : AtomId := root
  let mut dels : Nat := 0
  let mut inss : Array Content := #[]
  for i in [0:arr.size + 1] do
    let step : Option Al := arr[i]?
    let flushAt : Option (Option AtomId) := match step with
      | some (.keepAtom b _) => some (some b)
      | none => some none
      | _ => none
    if let some next := flushAt then
      if dels + inss.size > 0 then
        let fresh (salt : String) (taken : Array AtomId) (g : Graph) : AtomId :=
          freshId H (fun x => g.present x || taken.contains x) salt
        if dels = 0 then
          let p := fresh (saltOf anchor next blank "as it is") added cur
          ops := ops.push (.add p blank anchor); cur := cur.step (.add p blank anchor)
          added := added.push p; asIs := asIs.push p
          if let some b := next then
            ops := ops.push (.connect p b); cur := cur.step (.connect p b)
        let chain : Array Content := if inss.size = 0 then #[blank] else inss
        let mut prev := anchor
        for c in chain do
          let id := fresh (saltOf prev next c member) added cur
          ops := ops.push (.add id c prev); cur := cur.step (.add id c prev)
          added := added.push id
          prev := id
        if let some b := next then
          ops := ops.push (.connect prev b); cur := cur.step (.connect prev b)
      dels := 0; inss := #[]
      if let some b := next then anchor := b
    else
      match step with
      | some (.delAtom _) => dels := dels + 1
      | some (.ins c) => inss := inss.push c
      | _ => pure ()
  return ⟨ops.toList, added.toList, asIs.toList⟩

/-- **Keep one candidate.** Delete every run the section's other candidates show that the kept one
does not. -/
def selectPatch (alts : List (AtomId × List Segment)) (i : Nat) : Patch :=
  match alts[i]? with
  | none => []
  | some (_, keep) =>
    let ks := segAtoms keep
    let others := (alts.eraseIdx i).flatMap fun (_, ss) => segAtoms ss
    (others.filter (fun a => !ks.contains a)).eraseDups.map Op.delete

/-- **Re-cite.** Replace the atom `a` by a new atom holding `c`, in its place: after `a` (which,
deleted, still conducts the order) and before the atom that followed it. -/
def replacePatch (H : Hash) (G : Graph) (a : AtomId) (next : Option AtomId) (c : Content) (author : String) :
    Built :=
  let id := freshId H G.present (saltOf a next c author)
  { ops := [.add id c a] ++ (match next with | some b => [.connect id b] | none => []) ++ [.delete a],
    added := [id] }

/-- The atom shown after `a` in a rendering. -/
def atomAfter (ps : List Piece) (a : AtomId) : Option AtomId :=
  let rest := (ps.dropWhile fun p => match p with | .atom b _ => b != a | _ => true).drop 1
  rest.findSome? fun | .atom b _ => some b | _ => none

end Obend.Vault

end
