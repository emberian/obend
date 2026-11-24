module
/-
# Obend.Doc.Render — a page at a view, and a vault of markdown read into pages and cites

DESIGN §5, the Obsidian-shaped person's day one: every `.md` is a page, every wikilink a cite.

* `readPage` lexes markdown into runs (one per line, split around wikilinks) and wikilinks, and
  builds the page as a PATCH from the empty page: a chain of `Add`s, so a page read from disk is
  one authored patch like any other. What a wikilink to a page of the vault becomes (Ember's
  decision (c), REPORT-DOC-20261030 §5): `[[Beta]]` (and `[[Beta#Heading]]`, and `[[Beta|shown
  as]]`, whose alias is display text) cites Beta's IDENTITY only, no bytes, current while Beta
  exists; `![[Beta]]`, an embed, is a following cite of Beta's whole text; `[[Beta#^b]]`, a block
  reference, a following cite of the line Beta marks `^b`; `![[Beta#Heading]]` a following cite
  of the heading line. A
  following byte cite stays current while the bytes it quotes are unchanged (rule (b),
  `Obend.Doc.Section`). A wikilink to no page, or to a block its page does not mark, stays text.
* `readVault` reads every page twice: once to learn each page's bytes (a page's source does not
  depend on its cites' commitments, only on their names and spans), once to commit each byte cite
  to its target's bytes under the hash `H`.
* `renderAt` renders a page at a view: a cite whose facts hold reads as it was written; one whose
  facts fail carries their names, `![[Name]]{behind}`, `[[Name]]{missing}`, `[[Name#^b]]{unverified}`.
  `renderAt_fresh`: where every cite of the page holds, the view is the source.
* `Obend.Doc.Backlinks`: the reverse index of cites.

The round trip (`source (read md) = md` for a vault) is checked on the two-page vault in
`lean/tests/doc/` and by `decide` below; it is not proved for every markdown file.
-/
public import Obend.Doc.Section
import all Obend.Doc.Graph
import all Obend.Doc.Patch
import all Obend.Doc.Merge
import all Obend.Doc.Section
public section

namespace Obend.Doc

set_option autoImplicit false

open Obend.Digest.HashBytes

/-! ## Reading markdown -/

/-- A lexed piece of markdown. -/
inductive Tok
  | text (s : List Char)
  | link (name : List Char)
  | embed (name : List Char)
deriving DecidableEq, Repr

/-- The name of a wikilink whose `[[` has been read, and what follows its `]]`; `none` when the
line ends first, when the brackets are empty (`[[]]`), or when an unclosed `[[` meets another `[[`
on the same line. -/
def takeLink : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '\n' :: _, _ => none
  | '[' :: '[' :: _, _ => none
  | ']' :: ']' :: rest, acc => if acc.isEmpty then none else some (acc.reverse, rest)
  | c :: rest, acc => takeLink rest (c :: acc)

/-- An inline code span whose opening backtick has been read: its characters reversed (as the run
being built keeps them), closing backtick included, and what follows; `none` when the line ends
first. What is in code is text: `[[x]]` there is not a link (Obsidian reads it so too). A fenced
block's own lines are lexed as any line; only the span on one line is known. -/
def takeCode : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '\n' :: _, _ => none
  | '`' :: rest, acc => some ('`' :: acc, rest)
  | c :: rest, acc => takeCode rest (c :: acc)

/-- Close the text read so far (kept reversed) as a run, if any. -/
def flush (acc : List Char) : List Tok := if acc = [] then [] else [.text acc.reverse]

/-- Lex markdown: a run per line, split around wikilinks and embeds (including block and heading
transclusions `![[P#^b]]` and `![[P#Heading]]`); a wikilink inside an inline code span is text.
`n` bounds the steps. -/
def lex : Nat → List Char → List Char → List Tok
  | 0, _, acc => flush acc
  | _ + 1, [], acc => flush acc
  | n + 1, '!' :: '[' :: '[' :: rest, acc => match takeLink rest [] with
    | some (name, rest') =>
      flush acc ++ .embed name :: lex n rest' []
    | none => lex n ('[' :: '[' :: rest) ('!' :: acc)
  | n + 1, '[' :: '[' :: rest, acc => match takeLink rest [] with
    | some (name, rest') => flush acc ++ .link name :: lex n rest' []
    | none => lex n ('[' :: rest) ('[' :: acc)
  | n + 1, '`' :: rest, acc => match takeCode rest ['`'] with
    | some (code, rest') => lex n rest' (code ++ acc)
    | none => lex n rest ('`' :: acc)
  | n + 1, '\n' :: rest, acc => flush ('\n' :: acc) ++ lex n rest []
  | n + 1, c :: rest, acc => lex n rest (c :: acc)

/-- Stack-safe tail-recursive accumulator helper for `lex`. -/
def flushOnto (acc : List Char) (toks : List Tok) : List Tok :=
  if acc = [] then toks else .text acc.reverse :: toks

theorem flushOnto_reverse (acc : List Char) (toks : List Tok) :
    (flushOnto acc toks).reverse = toks.reverse ++ flush acc := by
  unfold flushOnto flush
  split <;> simp

def lexAcc : Nat → List Char → List Char → List Tok → List Tok
  | 0, _, acc, toks => (flushOnto acc toks).reverse
  | _ + 1, [], acc, toks => (flushOnto acc toks).reverse
  | n + 1, '!' :: '[' :: '[' :: rest, acc, toks => match takeLink rest [] with
    | some (name, rest') => lexAcc n rest' [] (.embed name :: flushOnto acc toks)
    | none => lexAcc n ('[' :: '[' :: rest) ('!' :: acc) toks
  | n + 1, '[' :: '[' :: rest, acc, toks => match takeLink rest [] with
    | some (name, rest') => lexAcc n rest' [] (.link name :: flushOnto acc toks)
    | none => lexAcc n ('[' :: rest) ('[' :: acc) toks
  | n + 1, '`' :: rest, acc, toks => match takeCode rest ['`'] with
    | some (code, rest') => lexAcc n rest' (code ++ acc) toks
    | none => lexAcc n rest ('`' :: acc) toks
  | n + 1, '\n' :: rest, acc, toks => lexAcc n rest [] (flushOnto ('\n' :: acc) toks)
  | n + 1, c :: rest, acc, toks => lexAcc n rest (c :: acc) toks

theorem lexAcc_eq : ∀ (n : Nat) (cs acc : List Char) (toks : List Tok),
    lexAcc n cs acc toks = toks.reverse ++ lex n cs acc
  | 0, _, acc, toks => by simp [lexAcc, lex, flushOnto_reverse]
  | _ + 1, [], acc, toks => by simp [lexAcc, lex, flushOnto_reverse]
  | n + 1, c :: rest, acc, toks => by
    by_cases h1 : c = '!'
    · subst h1
      cases rest with
      | nil => exact lexAcc_eq n [] ('!' :: acc) toks
      | cons c2 r2 =>
        by_cases h2 : c2 = '['
        · subst h2
          cases r2 with
          | nil => exact lexAcc_eq n ['['] ('!' :: acc) toks
          | cons c3 r3 =>
            by_cases h3 : c3 = '['
            · subst h3
              simp only [lexAcc, lex]
              cases takeLink r3 [] with
              | none => exact lexAcc_eq n ('[' :: '[' :: r3) ('!' :: acc) toks
              | some p =>
                simp only [lexAcc_eq n p.2 [] (.embed p.1 :: flushOnto acc toks),
                  List.reverse_cons, flushOnto_reverse, List.append_assoc, List.singleton_append]
            · simp [lexAcc, lex, h3, lexAcc_eq n ('[' :: c3 :: r3) ('!' :: acc) toks]
        · simp [lexAcc, lex, h2, lexAcc_eq n (c2 :: r2) ('!' :: acc) toks]
    · by_cases h2 : c = '['
      · subst h2
        cases rest with
        | nil => exact lexAcc_eq n [] ('[' :: acc) toks
        | cons c2 r2 =>
          by_cases h22 : c2 = '['
          · subst h22
            simp only [lexAcc, lex]
            cases takeLink r2 [] with
            | none => exact lexAcc_eq n ('[' :: r2) ('[' :: acc) toks
            | some p =>
              simp only [lexAcc_eq n p.2 [] (.link p.1 :: flushOnto acc toks),
                List.reverse_cons, flushOnto_reverse, List.append_assoc, List.singleton_append]
          · simp [lexAcc, lex, h22, lexAcc_eq n (c2 :: r2) ('[' :: acc) toks]
      · by_cases h3 : c = '`'
        · subst h3
          simp only [lexAcc, lex]
          cases takeCode rest ['`'] with
          | none => exact lexAcc_eq n rest ('`' :: acc) toks
          | some p => exact lexAcc_eq n p.2 (p.1 ++ acc) toks
        · by_cases h4 : c = '\n'
          · subst h4
            simp only [lexAcc, lex, lexAcc_eq n rest [] (flushOnto ('\n' :: acc) toks),
              flushOnto_reverse, List.append_assoc]
          · simp_all [lexAcc, lex, lexAcc_eq n rest (c :: acc) toks]

def lexExec (n : Nat) (cs acc : List Char) : List Tok := lexAcc n cs acc []

@[csimp] theorem lex_eq_exec : @lex = @lexExec := by
  funext n cs acc
  simpa [lexExec] using (lexAcc_eq n cs acc []).symm

/-- The tokens of a markdown text. -/
@[expose] def tokens (md : String) : List Tok := lex (md.length + 1) md.toList []

/-- Strip display alias after `|` or Markdown-table escaped `\|`. -/
def stripAlias : List Char → List Char
  | [] => []
  | '\\' :: '|' :: _ => []
  | '|' :: _ => []
  | c :: cs => c :: stripAlias cs

/-- A wikilink's page and what of it the link cites. An alias, `[[P|shown as]]` (or `[[P\|shown as]]`
inside Markdown tables), is display text: everything from the first `|` or `\|` is dropped before the
name is read (Obsidian's alias syntax; the atom's text keeps it). Of what is left, the text before
the first `#` names the page; `#^b` after it is the block `b`; for an embed `![[P#Heading]]`,
`#Heading` cites the heading block, while for an ordinary link `[[P#Heading]]` it cites the page's
identity; a bare `![[P]]` cites the page's whole text. -/
@[expose] def target (embed : Bool) (name : List Char) : List Char × Span :=
  let name := stripAlias name
  let page := name.takeWhile (· != '#')
  match name.dropWhile (· != '#') with
  | '#' :: '^' :: b => (page, .block (String.ofList b))
  | '#' :: h => (page, if embed then .block (String.ofList h) else .identity)
  | _ => (page, if embed then .page else .identity)

/-- How a wikilink is resolved: from its page name and span to the cite it becomes, or to nothing
(it stays text). -/
abbrev Resolve := String → Span → Option Cite

/-- The contents of a page, from its tokens. -/
@[expose] def contents (resolve : Resolve) : List Tok → List Content
  | [] => []
  | .text s :: ts => .text (String.ofList s) :: contents resolve ts
  | .link n :: ts =>
    let (p, sp) := target false n
    (match resolve (String.ofList p) sp with
      | some c => .cite (String.ofList n) c
      | none => .text ("[[" ++ String.ofList n ++ "]]")) :: contents resolve ts
  | .embed n :: ts =>
    let (p, sp) := target true n
    let labelName := match sp with
      | .page => String.ofList n
      | _ => "!" ++ String.ofList n
    (match resolve (String.ofList p) sp with
      | some c => .cite labelName c
      | none => .text ("![[" ++ String.ofList n ++ "]]")) :: contents resolve ts

/-- A chain of `Add`s: atom `i + 1` after atom `i`, the first after `root`. -/
@[expose] def chain : Nat → List Content → Patch
  | _, [] => []
  | i, c :: cs => .add (i + 1) c i :: chain (i + 1) cs

/-- Insert a run between two atoms: added after `after`, ordered before `before`. (`Add` alone orders
the new atom after `after` only, which leaves it unordered against `after`'s other successors.) -/
def Patch.insert (id : AtomId) (c : Content) (after before : AtomId) : Patch :=
  [.add id c after, .connect id before]

/-- A markdown page as the patch that writes it from the empty page. -/
@[expose] def readPage (resolve : Resolve) (md : String) : Patch := chain root (contents resolve (tokens md))

/-- A vault: page names with their markdown, in order. Page `i + 1` is the `i`th. -/
abbrev Vault := List (String × String)

/-- The page id of a name. -/
@[expose] def Vault.idOf (V : Vault) (name : String) : Option PageId :=
  (V.zipIdx.find? fun e => e.1.1 == name).map (·.2 + 1)

/-- Read a vault into a world of one version per page, its byte cites committed under `H`. -/
@[expose] def Vault.read (H : Hash) (V : Vault) : World :=
  let draft : PageId → Option Graph := fun p =>
    (V[p - 1]?).map fun e => Graph.empty.apply (readPage (fun _ sp => some ⟨0, sp, 0, [], .following⟩) e.2)
  let resolve : Resolve := fun name sp => (V.idOf name).bind fun q => (draft q).bind fun G =>
    match sp with
    | .identity => some ⟨q, .identity, 0, [], .following⟩
    | _ => (quoteOf G sp).map fun b => ⟨q, sp, 0, H b, .following⟩
  fun p => if p = 0 then [] else match V[p - 1]? with
    | some e => [Graph.empty.apply (readPage resolve e.2)]
    | none => []

private theorem idOf_eq_lookup (V : Vault) (name : String) :
    V.idOf name = ((V.zipIdx.map fun e => (e.1.1, e.2 + 1)).lookup name) := by
  unfold Vault.idOf
  generalize 0 = start
  induction V generalizing start with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.zipIdx_cons, List.find?_cons, List.map_cons, List.lookup]
    by_cases h : hd.1 == name
    · have hs : (name == hd.1) = true := beq_iff_eq.mpr (beq_iff_eq.mp h).symm
      simp [h, hs]
    · have hs : (name == hd.1) = false :=
        beq_eq_false_iff_ne.mpr (fun he => h (beq_iff_eq.mpr he.symm))
      simp [h, hs, ih (start + 1)]

/-- Pre-indexed $O(P \log P + \text{bytes})$ vault reader: builds `idMap`, `drafts`, and committed
`pages` once in `Array`s and answers `World` queries in $O(1)$. -/
def Vault.readExec (H : Hash) (V : Vault) : World :=
  let idMap := buildStrMap (V.zipIdx.map fun e => (e.1.1, e.2 + 1))
  let drafts : Array Graph := V.toArray.map fun e =>
    Graph.empty.apply (readPage (fun _ sp => some ⟨0, sp, 0, [], .following⟩) e.2)
  let resolve : Resolve := fun name sp =>
    (lookupStrMap idMap name).bind fun q =>
      (if h : q - 1 < drafts.size then some (drafts[q - 1]'h) else none).bind fun G =>
        match sp with
        | .identity => some ⟨q, .identity, 0, [], .following⟩
        | _ => (quoteOf G sp).map fun b => ⟨q, sp, 0, H b, .following⟩
  let pages : Array Graph := V.toArray.map fun e => Graph.empty.apply (readPage resolve e.2)
  fun p =>
    if p = 0 then []
    else if h : p - 1 < pages.size then [pages[p - 1]'h] else []

private theorem array_map_get? {α β : Type} (xs : List α) (f : α → β) (i : Nat) :
    (if h : i < (xs.toArray.map f).size then some ((xs.toArray.map f)[i]'h) else none) =
      (xs[i]?).map f := by
  by_cases hlt : i < xs.length
  · have hsz : i < (xs.toArray.map f).size := by
      rw [Array.size_map, List.size_toArray]; exact hlt
    simp only [hsz, ↓reduceDIte, Array.getElem_map, List.getElem_toArray,
      List.getElem?_eq_getElem hlt, Option.map_some]
  · have hnsz : ¬(i < (xs.toArray.map f).size) := by
      rw [Array.size_map, List.size_toArray]; exact hlt
    simp only [hnsz, ↓reduceDIte, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.map_none]

@[csimp] theorem Vault.read_eq_exec : @Vault.read = @Vault.readExec := by
  funext H V p
  unfold Vault.read Vault.readExec
  dsimp only
  have hres :
      ((fun (name : String) (sp : Span) =>
        (lookupStrMap (buildStrMap (V.zipIdx.map fun e => (e.1.1, e.2 + 1))) name).bind fun q =>
          (if h : q - 1 < (V.toArray.map fun e =>
              Graph.empty.apply (readPage (fun _ sp => some ⟨0, sp, 0, [], .following⟩) e.2)).size then
            some ((V.toArray.map fun e =>
              Graph.empty.apply (readPage (fun _ sp => some ⟨0, sp, 0, [], .following⟩) e.2))[q - 1]'h)
          else none).bind fun G =>
            match sp with
            | .identity => some ⟨q, .identity, 0, [], .following⟩
            | _ => (quoteOf G sp).map fun b => ⟨q, sp, 0, H b, .following⟩) : Resolve) =
      ((fun (name : String) (sp : Span) =>
        (V.idOf name).bind fun q =>
          ((V[q - 1]?).map fun e =>
            Graph.empty.apply (readPage (fun _ sp => some ⟨0, sp, 0, [], .following⟩) e.2)).bind fun G =>
            match sp with
            | .identity => some ⟨q, .identity, 0, [], .following⟩
            | _ => (quoteOf G sp).map fun b => ⟨q, sp, 0, H b, .following⟩) : Resolve) := by
    funext name sp
    rw [lookupStrMap_buildStrMap, ← idOf_eq_lookup]
    congr 1
    funext q
    rw [array_map_get?]
  rw [hres]
  by_cases hp0 : p = 0
  · simp only [hp0, ↓reduceIte]
  · simp only [hp0, ↓reduceIte]
    let fPage : String × String → Graph := fun e =>
      Graph.empty.apply (readPage (fun name sp =>
        (V.idOf name).bind fun q =>
          ((V[q - 1]?).map fun e =>
            Graph.empty.apply (readPage (fun _ sp => some ⟨0, sp, 0, [], .following⟩) e.2)).bind fun G =>
            match sp with
            | .identity => some ⟨q, .identity, 0, [], .following⟩
            | _ => (quoteOf G sp).map fun b => ⟨q, sp, 0, H b, .following⟩) e.2)
    have hpg := array_map_get? V fPage (p - 1)
    by_cases hsz : p - 1 < (V.toArray.map fPage).size
    · rw [dite_eq_left hsz] at hpg ⊢
      cases hV : V[p - 1]? with
      | none => rw [hV, Option.map_none] at hpg; cases hpg
      | some e => rw [hV, Option.map_some] at hpg; injection hpg with heq; rw [heq]; rfl
    · rw [dite_eq_right hsz] at hpg ⊢
      cases hV : V[p - 1]? with
      | none => rfl
      | some e => rw [hV, Option.map_some] at hpg; cases hpg

/-! ## Rendering at a view -/

/-- How a failed fact reads beside a cite. -/
def Fact.reason : Fact → String
  | .verifies _ => "unverified"
  | .current _ => "behind"
  | .present _ => "missing"
  | .live .. => "dead"
  | .head .. => "unordered"

/-- Join with commas. -/
def commas : List String → String
  | [] => ""
  | [s] => s
  | s :: ss => s ++ "," ++ commas ss

/-- Resolve the transcluded text of a cite `c` from the world `W` (at its cited version, or current
version when present): returns the full page source for `.page`, the matched `^blockId` or
`# Heading` line for `.block b`, and `none` for `.identity`. -/
@[expose] def resolveTranscludedText (W : World) (c : Cite) : Option String :=
  let targetG? := match (W c.page)[c.version]? with
    | some G => some G
    | none => W.current c.page
  match targetG? with
  | none => none
  | some G =>
    match c.span with
    | .identity => none
    | .page => some G.source
    | .block b => (blockLine b G.source.toList).map String.ofList
    | .bytes r => some (String.ofList ((G.source.toList.drop r.start).take r.len))

/-- How an atom reads at a view: a cite carries the names of its facts that fail. -/
def viewAtom (H : Hash) (W : World) (G : Graph) (a : AtomId) : String :=
  match G.label a with
  | some (.cite _ c) =>
    match (citeFacts c).filter fun f => !holds H W f with
    | [] => G.atomText a
    | d => G.atomText a ++ "{" ++ commas (d.map Fact.reason) ++ "}"
  | _ => G.atomText a

/-- How an atom reads when expanding transclusions (`![[Page]]`, `![[Page#^id]]`, `![[Page#Heading]]`)
from the world `W`: verified embeds inline their resolved target text from `W`, while failed cites
carry their failure reasons `{...}`. -/
def viewAtomTranscluded (H : Hash) (W : World) (G : Graph) (a : AtomId) : String :=
  match G.label a with
  | some (.cite n c) =>
    match (citeFacts c).filter fun f => !holds H W f with
    | [] =>
      let isEmbed : Bool := match n.toList, c.span with
        | '!' :: _, _ => true
        | _, .page => true
        | _, _ => false
      if isEmbed then
        match resolveTranscludedText W c with
        | some txt => txt
        | none => G.atomText a
      else
        G.atomText a
    | d => G.atomText a ++ "{" ++ commas (d.map Fact.reason) ++ "}"
  | _ => G.atomText a

/-- A page's rendering at a view: its current version, each cite marked by what fails. -/
def renderAt (H : Hash) (W : World) (p : PageId) : String :=
  match W.current p with
  | some G => Graph.segsWith (viewAtom H W G) G.content
  | none => ""

/-- Render page `p` at view `(H, W)` with verified `![[...]]` page/block/heading transclusions
resolved from the store's world `W`. -/
@[expose] def renderTranscludedAt (H : Hash) (W : World) (p : PageId) : String :=
  match W.current p with
  | some G => Graph.segsWith (viewAtomTranscluded H W G) G.content
  | none => ""

/-- **A page whose cites all hold renders as its source.** -/
theorem renderAt_fresh (H : Hash) {W : World} {p : PageId} {G : Graph} (hG : W.current p = some G)
    (h : ∀ a n c, G.label a = some (.cite n c) → ∀ f ∈ citeFacts c, holds H W f = true) :
    renderAt H W p = G.source := by
  simp only [renderAt, hG, Graph.source]
  congr 1
  funext a
  unfold viewAtom
  cases hl : G.label a with
  | none => rfl
  | some x =>
    cases x with
    | cite n c =>
      have : (citeFacts c).filter (fun f => !holds H W f) = [] :=
        List.filter_eq_nil_iff.2 fun f hf => by simp [h a n c hl f hf]
      simp only [this]
    | text => rfl
    | field => rfl
    | cell => rfl

/-! ### Teeth -/

namespace Teeth

open Obend.Doc.Teeth (toy)

def vault : Vault :=
  [("Alpha", "# Alpha\nSee [[Beta]] and [[Gamma]].\n![[Beta]]\nQuote: [[Beta#^ans]]\n"),
   ("Beta", "# Beta\nBack to [[Alpha]].\nThe answer. ^ans\n")]

/-- The tokens: a heading line, then a line split around its links; an embed; a block reference. -/
example : tokens "a [[B]] c\n![[B]] [[B#^x]]" =
    [.text "a ".toList, .link ['B'], .text " c\n".toList, .embed ['B'], .text " ".toList,
     .link "B#^x".toList] := by decide

/-- The vault round trip, page by page, in the kernel. -/
example : ((vault.read toy 1).map Graph.source, (vault.read toy 2).map Graph.source) =
    (["# Alpha\nSee [[Beta]] and [[Gamma]].\n![[Beta]]\nQuote: [[Beta#^ans]]\n"],
     ["# Beta\nBack to [[Alpha]].\nThe answer. ^ans\n"]) := by decide

/-- `[[Beta]]` became a cite of page 2's identity; `[[Gamma]]` (no such page) stayed text;
`![[Beta]]` a following cite of Beta's whole text; `[[Beta#^ans]]` one of its marked line. -/
example : ((vault.read toy 1).head?.map fun G => [3, 7, 10].map fun a => (G.label a).map (fun
    | .cite n c => (n, c.page, c.span, c.mode == .following)
    | _ => ("", 0, .identity, false))) =
    some [some ("Beta", 2, .identity, true), some ("Beta", 2, .page, true),
      some ("Beta#^ans", 2, .block "ans", true)] := by decide

/-- At the view it was read in, each page renders as its source. -/
example : renderAt toy (vault.read toy) 1 = "# Alpha\nSee [[Beta]] and [[Gamma]].\n![[Beta]]\nQuote: [[Beta#^ans]]\n" := by
  decide

/-- Beta moves on (a line appended): the embed reads behind; the identity link and the block
reference, whose bytes did not change, do not. -/
def movedVault : World := fun p =>
  if p = 2 then vault.read toy 2 ++
    (vault.read toy 2).map (·.apply [.add 9 (.text "More.\n") 5])
  else vault.read toy p
example : renderAt toy movedVault 1 =
    "# Alpha\nSee [[Beta]] and [[Gamma]].\n![[Beta]]{behind}\nQuote: [[Beta#^ans]]\n" := by decide
example : renderAt toy movedVault 2 = "# Beta\nBack to [[Alpha]].\nThe answer. ^ans\nMore.\n" := by decide

/-- Beta's marked line is rewritten: now the block reference reads behind too. -/
def revisedVault : World := fun p =>
  if p = 2 then movedVault 2 ++
    (vault.read toy 2).map (·.apply [.add 9 (.text "More.\n") 5, .delete 5,
      .add 10 (.text "The answer, revised. ^ans\n") 5, .connect 10 9])
  else vault.read toy p
example : renderAt toy revisedVault 2 = "# Beta\nBack to [[Alpha]].\nThe answer, revised. ^ans\nMore.\n" := by
  decide
example : renderAt toy revisedVault 1 =
    "# Alpha\nSee [[Beta]] and [[Gamma]].\n![[Beta]]{behind}\nQuote: [[Beta#^ans]]{behind}\n" := by decide

/-- Block transclusion `![[Beta#^ans]]` lexes as `.embed`, round-trips in `renderAt`, and inlines
    the cited block line `"The answer. ^ans"` in `renderTranscludedAt`. -/
def blockTransclusionVault : Vault :=
  [("Alpha", "# Alpha\n![[Beta#^ans]]\n"),
   ("Beta", "# Beta\nThe answer. ^ans\n")]

example : tokens "![[Beta#^ans]]" = [.embed "Beta#^ans".toList] := by decide

/-- A wikilink in inline code is text; the span after it is read as ever. -/
example : tokens "a `[[B]]` c [[D]]\n" = [.text "a `[[B]]` c ".toList, .link ['D'], .text "\n".toList] := by decide

/-- An alias is display text: `[[Beta|the answer page]]` cites Beta's identity, and the page's
text keeps the alias. -/
def aliasVault : Vault :=
  [("Alpha", "# Alpha\nSee [[Beta|the answer page]] and [[Beta#^ans|its answer]].\n"),
   ("Beta", "# Beta\nThe answer. ^ans\n")]

example : target false "Beta|the answer page".toList = ("Beta".toList, .identity) := by decide
example : target false "Beta#^ans|its answer".toList = ("Beta".toList, .block "ans") := by decide
example : renderAt toy (aliasVault.read toy) 1 =
    "# Alpha\nSee [[Beta|the answer page]] and [[Beta#^ans|its answer]].\n" := by decide

example : renderAt toy (blockTransclusionVault.read toy) 1 = "# Alpha\n![[Beta#^ans]]\n" := by decide

example : renderTranscludedAt toy (blockTransclusionVault.read toy) 1 =
    "# Alpha\nThe answer. ^ans\n" := by decide

end Teeth

end Obend.Doc

end
