module
/-
# Obend.Doc.Render — a page at a view, and a vault of markdown read into pages and cites

DESIGN §5, the Obsidian-shaped person's day one: every `.md` is a page, every `[[wikilink]]` a cite.

* `readPage` lexes markdown into runs (one per line, split around wikilinks) and wikilinks, and
  builds the page as a PATCH from the empty page: a chain of `Add`s, so a page read from disk is
  one authored patch like any other. A wikilink to a page of the vault becomes a FOLLOWING cite of
  that page's whole current text (a link tracks the page); one to no page stays text.
* `readVault` reads every page twice: once to learn each page's bytes (a page's source does not
  depend on its cites' commitments, only on their names), once to commit each cite to its target's
  bytes under the hash `H`.
* `renderAt` renders a page at a view: a cite whose facts hold reads as it was written, `[[Name]]`;
  one whose facts fail carries their names, `[[Name]]{behind}` or `[[Name]]{unverified}`.
  `renderAt_fresh`: where every cite of the page holds, the view is the source.

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

/-- Lex markdown: a run per line, split around wikilinks. `n` bounds the steps. -/
def lex : Nat → List Char → List Char → List Tok
  | 0, _, acc => flush acc
  | _ + 1, [], acc => flush acc
  | n + 1, '[' :: '[' :: rest, acc => match takeLink rest [] with
    | some (name, rest') => flush acc ++ .link name :: lex n rest' []
    | none => lex n ('[' :: rest) ('[' :: acc)
  | n + 1, '\n' :: rest, acc => flush ('\n' :: acc) ++ lex n rest []
  | n + 1, c :: rest, acc => lex n rest (c :: acc)

/-- The tokens of a markdown text. -/
def tokens (md : String) : List Tok := lex (md.length + 1) md.toList []

/-- How a wikilink is resolved: to the cite it becomes, or to nothing (it stays text). -/
abbrev Resolve := String → Option Cite

/-- The contents of a page, from its tokens. -/
def contents (resolve : Resolve) : List Tok → List Content
  | [] => []
  | .text s :: ts => .text (String.ofList s) :: contents resolve ts
  | .link n :: ts =>
    let name := String.ofList n
    (match resolve name with
      | some c => .cite name c
      | none => .text ("[[" ++ name ++ "]]")) :: contents resolve ts

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

/-- Read a vault into a world of one version per page, its wikilinks committed under `H`. -/
def Vault.read (H : Hash) (V : Vault) : World :=
  let draft : PageId → Option Graph := fun p =>
    (V[p - 1]?).map fun e => Graph.empty.apply (readPage (fun _ => some ⟨0, ⟨0, 0⟩, 0, [], .following⟩) e.2)
  let resolve : Resolve := fun name => (V.idOf name).bind fun q => (draft q).map fun G =>
    let b := bytes G.source
    ⟨q, ⟨0, b.length⟩, 0, H b, .following⟩
  fun p => if p = 0 then [] else match V[p - 1]? with
    | some e => [Graph.empty.apply (readPage resolve e.2)]
    | none => []

/-! ## Rendering at a view -/

/-- How a failed fact reads beside a cite. -/
def Fact.reason : Fact → String
  | .verifies _ => "unverified"
  | .current _ => "behind"
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
  [("Alpha", "# Alpha\nSee [[Beta]] and [[Gamma]].\n"), ("Beta", "# Beta\nBack to [[Alpha]].\n")]

/-- The tokens: a heading line, then a line split around its links. -/
example : tokens "a [[B]] c\n" = [.text "a ".toList, .link ['B'], .text " c\n".toList] := by decide

/-- The vault round trip, page by page, in the kernel. -/
example : ((vault.read toy 1).map Graph.source, (vault.read toy 2).map Graph.source) =
    (["# Alpha\nSee [[Beta]] and [[Gamma]].\n"], ["# Beta\nBack to [[Alpha]].\n"]) := by decide

/-- `[[Beta]]` became a cite of page 2; `[[Gamma]]` (no such page) stayed text. -/
example : ((vault.read toy 1).head?.bind fun G => G.label 3).map (fun
    | .cite n c => (n, c.page, c.mode == .following)
    | _ => ("", 0, false)) = some ("Beta", 2, true) := by decide

/-- At the view it was read in, each page renders as its source. -/
example : renderAt toy (vault.read toy) 1 = "# Alpha\nSee [[Beta]] and [[Gamma]].\n" := by decide

/-- Beta moves on: Alpha's following cite now reads behind. -/
def movedVault : World := fun p =>
  if p = 2 then vault.read toy 2 ++
    (vault.read toy 2).map (·.apply [.add 9 (.text "More.\n") 4])
  else vault.read toy p
example : renderAt toy movedVault 1 = "# Alpha\nSee [[Beta]]{behind} and [[Gamma]].\n" := by decide
example : renderAt toy movedVault 2 = "# Beta\nBack to [[Alpha]].\nMore.\n" := by decide

end Teeth

#tooth renderAt_fresh by mutation viewAtom := fun _ _ _ _ => ""

end Obend.Doc

end
