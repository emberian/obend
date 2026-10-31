module
/-
# Obend.Doc.Render — a page at a view, and a vault of markdown read into pages and cites

DESIGN §5, the Obsidian-shaped person's day one: every `.md` is a page, every wikilink a cite.

* `readPage` lexes markdown into runs (one per line, split around wikilinks) and wikilinks, and
  builds the page as a PATCH from the empty page: a chain of `Add`s, so a page read from disk is
  one authored patch like any other. What a wikilink to a page of the vault becomes (Ember's
  decision (c), REPORT-DOC-20261030 §5): `[[Beta]]` (and `[[Beta#Heading]]`) cites Beta's IDENTITY
  only, no bytes, current while Beta exists; `![[Beta]]`, an embed, is a following cite of Beta's
  whole text; `[[Beta#^b]]`, a block reference, a following cite of the line Beta marks `^b`. A
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
@[expose] public section

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
line ends first. -/
def takeLink : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '\n' :: _, _ => none
  | ']' :: ']' :: rest, acc => some (acc.reverse, rest)
  | c :: rest, acc => takeLink rest (c :: acc)

/-- Close the text read so far (kept reversed) as a run, if any. -/
def flush (acc : List Char) : List Tok := if acc = [] then [] else [.text acc.reverse]

/-- Lex markdown: a run per line, split around wikilinks and embeds. An embed of a block
(`![[P#^b]]`) is read as a `!` and a block reference. `n` bounds the steps. -/
def lex : Nat → List Char → List Char → List Tok
  | 0, _, acc => flush acc
  | _ + 1, [], acc => flush acc
  | n + 1, '!' :: '[' :: '[' :: rest, acc => match takeLink rest [] with
    | some (name, rest') =>
      if name.contains '#' then lex n ('[' :: '[' :: rest) ('!' :: acc)
      else flush acc ++ .embed name :: lex n rest' []
    | none => lex n ('[' :: '[' :: rest) ('!' :: acc)
  | n + 1, '[' :: '[' :: rest, acc => match takeLink rest [] with
    | some (name, rest') => flush acc ++ .link name :: lex n rest' []
    | none => lex n ('[' :: rest) ('[' :: acc)
  | n + 1, '\n' :: rest, acc => flush ('\n' :: acc) ++ lex n rest []
  | n + 1, c :: rest, acc => lex n rest (c :: acc)

/-- The tokens of a markdown text. -/
def tokens (md : String) : List Tok := lex (md.length + 1) md.toList []

/-- A wikilink's page and what of it the link cites: the text before the first `#` names the page;
`#^b` after it is the block `b`; any other `#…` (a heading) is still the page's identity. An embed
cites the page's whole text. -/
def target (embed : Bool) (name : List Char) : List Char × Span :=
  let page := name.takeWhile (· != '#')
  match name.dropWhile (· != '#') with
  | '#' :: '^' :: b => (page, .block (String.ofList b))
  | _ => (page, if embed then .page else .identity)

/-- How a wikilink is resolved: from its page name and span to the cite it becomes, or to nothing
(it stays text). -/
abbrev Resolve := String → Span → Option Cite

/-- The contents of a page, from its tokens. -/
def contents (resolve : Resolve) : List Tok → List Content
  | [] => []
  | .text s :: ts => .text (String.ofList s) :: contents resolve ts
  | .link n :: ts =>
    let (p, sp) := target false n
    (match resolve (String.ofList p) sp with
      | some c => .cite (String.ofList n) c
      | none => .text ("[[" ++ String.ofList n ++ "]]")) :: contents resolve ts
  | .embed n :: ts =>
    let (p, sp) := target true n
    (match resolve (String.ofList p) sp with
      | some c => .cite (String.ofList n) c
      | none => .text ("![[" ++ String.ofList n ++ "]]")) :: contents resolve ts

/-- A chain of `Add`s: atom `i + 1` after atom `i`, the first after `root`. -/
def chain : Nat → List Content → Patch
  | _, [] => []
  | i, c :: cs => .add (i + 1) c i :: chain (i + 1) cs

/-- Insert a run between two atoms: added after `after`, ordered before `before`. (`Add` alone orders
the new atom after `after` only, which leaves it unordered against `after`'s other successors.) -/
def Patch.insert (id : AtomId) (c : Content) (after before : AtomId) : Patch :=
  [.add id c after, .connect id before]

/-- A markdown page as the patch that writes it from the empty page. -/
def readPage (resolve : Resolve) (md : String) : Patch := chain root (contents resolve (tokens md))

/-- A vault: page names with their markdown, in order. Page `i + 1` is the `i`th. -/
abbrev Vault := List (String × String)

/-- The page id of a name. -/
def Vault.idOf (V : Vault) (name : String) : Option PageId :=
  (V.zipIdx.find? fun e => e.1.1 == name).map (·.2 + 1)

/-- Read a vault into a world of one version per page, its byte cites committed under `H`. -/
def Vault.read (H : Hash) (V : Vault) : World :=
  let draft : PageId → Option Graph := fun p =>
    (V[p - 1]?).map fun e => Graph.empty.apply (readPage (fun _ sp => some ⟨0, sp, 0, [], .following⟩) e.2)
  let resolve : Resolve := fun name sp => (V.idOf name).bind fun q => (draft q).bind fun G =>
    match sp with
    | .identity => some ⟨q, .identity, 0, [], .following⟩
    | _ => (quoteOf G sp).map fun b => ⟨q, sp, 0, H b, .following⟩
  fun p => if p = 0 then [] else match V[p - 1]? with
    | some e => [Graph.empty.apply (readPage resolve e.2)]
    | none => []

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

/-- How an atom reads at a view: a cite carries the names of its facts that fail. -/
def viewAtom (H : Hash) (W : World) (G : Graph) (a : AtomId) : String :=
  match G.label a with
  | some (.cite _ c) =>
    match (citeFacts c).filter fun f => !holds H W f with
    | [] => G.atomText a
    | d => G.atomText a ++ "{" ++ commas (d.map Fact.reason) ++ "}"
  | _ => G.atomText a

/-- A page's rendering at a view: its current version, each cite marked by what fails. -/
def renderAt (H : Hash) (W : World) (p : PageId) : String :=
  match W.current p with
  | some G => Graph.segsWith (viewAtom H W G) G.content
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

end Teeth

#tooth renderAt_fresh by mutation viewAtom := fun _ _ _ _ => ""

end Obend.Doc

end
