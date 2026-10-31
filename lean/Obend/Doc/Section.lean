module
/-
# Obend.Doc.Section — a section is a slot over runs; a cite is a support

DESIGN §5: a SECTION is a slot at type `Run` whose candidates are the runs members posted at a
position, and a CITE is a support of another page. This module builds both on `Obend.Slot`
without adding to it:

* a `World` is every page's history of versions, oldest first; the last is current. A source MOVES
  when its history grows and nothing else changes (`SourceMoves`).
* what a cite quotes (`quoteOf`): nothing for an IDENTITY cite (`[[Beta]]`), the page's bytes for an
  embed (`![[Beta]]`), the line marked `^b` for a block reference (`[[Beta#^b]]`), or a byte range.
* the facts a view is asked about: a run is `live`; it is a `head` at its position (no other live
  run there precedes it); a page is `present` (it has a version); a byte cite `verifies` (the cited
  version's quoted bytes hash to the commitment); a byte cite is `current` (rule (b): the bytes it
  quotes are the same at the source's current version).
* `sectionAt p x` is `Slot Fact Run`: a run's supports are `live`, `head`, and, for a cite run, the
  cite's facts: `present` for an identity cite, `verifies` for a pinned byte cite, `verifies` and
  `current` for a following one.

`section_alternatives`: the slot's `alternatives` at a position are exactly the page's `heads`
there (less any cite run whose cite fails). `conflict_is_section`: where the walk shows a conflict
(two or more heads, `walk_conflict`), the section's read is `empty` (no selection) and its
alternatives are that conflict's alternatives: the conflict IS the section. `pinned_cite_stays`: a
pinned cite run usable before its source moves is usable after; so is an identity cite run
(`identity_cite_stays`) and a following one whose quoted bytes did not change
(`following_cite_stays`). `following_cite_behind`: a selected following cite run whose quoted bytes
changed reads `blocked` after its source moves, naming its `current` fact; and re-citing the new
version (`recite`) makes its facts hold again (`recite_holds`).

A cite is an INTENTION (`Obend.Intention`): `cites H` resolves a cite's reference (`CiteRef`: page,
span, mode) at a world by pinning it at the page's current version (`pinAt`); its supports are the
cite's facts. `recite` is that intention's renewal (`recite_renew`), and `recite_holds`,
`cite_stale_iff_blocked`, `pinned_cite_stays` and `following_cite_behind` are its generic
theorems (`resolve_fill`, `stale_iff_blocked`, `stays`, `blocked_within`) at cites.

The commitment is taken under any byte hash `H`; nothing here assumes anything of it. Teeth use a
toy additive hash, which is as good as any for a statement that holds for every hash.
-/
public import Obend.Doc.Merge
public import Obend.Slot
public import Obend.Intention
public import Obend.Digest.HashBytes
@[expose] public section

namespace Obend.Doc

set_option autoImplicit false

open Obend.Slot Obend.Digest.HashBytes

/-! ## A page's bytes -/

/-- The UTF-8 encoding of a character. -/
def utf8 (c : Char) : List UInt8 :=
  let n := c.toNat
  if n < 0x80 then [n.toUInt8]
  else if n < 0x800 then [(0xC0 + n / 64).toUInt8, (0x80 + n % 64).toUInt8]
  else if n < 0x10000 then
    [(0xE0 + n / 4096).toUInt8, (0x80 + n / 64 % 64).toUInt8, (0x80 + n % 64).toUInt8]
  else
    [(0xF0 + n / 262144).toUInt8, (0x80 + n / 4096 % 64).toUInt8, (0x80 + n / 64 % 64).toUInt8,
      (0x80 + n % 64).toUInt8]

/-- A string's UTF-8 bytes. -/
def bytes (s : String) : List UInt8 := s.toList.flatMap utf8

namespace Graph

/-- How one atom reads in the page's source: a run its text, a cite its wikilink (an embed with
its `!`). -/
def atomText (G : Graph) (a : AtomId) : String :=
  match G.label a with
  | some (.text s) => s
  | some (.cite n c) => match c.span with
    | .page => "![[" ++ n ++ "]]"
    | _ => "[[" ++ n ++ "]]"
  | _ => ""

mutual
/-- Segments as text, each atom read by `f`. -/
def segsWith (f : AtomId → String) : List Segment → String
  | [] => ""
  | s :: ss => segWith f s ++ segsWith f ss
/-- A segment as text; a conflict shows every alternative between markers. -/
def segWith (f : AtomId → String) : Segment → String
  | .run a => f a
  | .conflict alts => "<<<<<<<\n" ++ altsWith f alts ++ ">>>>>>>\n"
/-- Alternatives, separated. -/
def altsWith (f : AtomId → String) : List (AtomId × List Segment) → String
  | [] => ""
  | [(_, ss)] => segsWith f ss
  | (_, ss) :: rest => segsWith f ss ++ "=======\n" ++ altsWith f rest
end

/-- A page version's source text: its content, in order, each atom as written. -/
def source (G : Graph) : String := segsWith G.atomText G.content

end Graph

/-! ## Worlds and facts -/

/-- Every page's history of versions, oldest first. -/
abbrev World := PageId → List Graph

/-- A page's current version. -/
def World.current (W : World) (p : PageId) : Option Graph := (W p).getLast?

/-- The source MOVES: its history grows by at least one version, and nothing else changes. -/
def SourceMoves (W W' : World) (q : PageId) : Prop :=
  (∀ p, p ≠ q → W' p = W p) ∧ ∃ ext, ext ≠ [] ∧ W' q = W q ++ ext

/-- A text's lines, without their newlines. -/
def lines : List Char → List (List Char)
  | [] => [[]]
  | c :: cs => match lines cs with
    | l :: ls => if c = '\n' then [] :: l :: ls else (c :: l) :: ls
    | [] => [[c]]

/-- The block marked `^b`: the first line ending ` ^b` (Obsidian's block identifier). -/
def blockLine (b : String) (src : List Char) : Option (List Char) :=
  (lines src).find? fun l => (' ' :: '^' :: b.toList).isSuffixOf l

/-- The bytes a span quotes in a page version: none for an identity cite, or for a block the
version does not mark. -/
def quoteOf (G : Graph) : Span → Option (List UInt8)
  | .identity => none
  | .page => some (bytes G.source)
  | .block b => (blockLine b G.source.toList).map fun l => l.flatMap utf8
  | .bytes r => some (((bytes G.source).drop r.start).take r.len)

/-- The bytes a cite quotes, at the version it cites. -/
def quoted (W : World) (c : Cite) : Option (List UInt8) :=
  ((W c.page)[c.version]?).bind fun G => quoteOf G c.span

/-- The bytes the cite's span quotes at its source's current version. -/
def latestQuote (W : World) (c : Cite) : Option (List UInt8) :=
  (W.current c.page).bind fun G => quoteOf G c.span

/-- What a view is asked. -/
inductive Fact
  /-- the run's atom is a live run of its page's current version -/
  | live (page : PageId) (atom : AtomId)
  /-- no other live run at position `pos` of the page precedes it -/
  | head (page : PageId) (pos : AtomId) (atom : AtomId)
  /-- the page has a version (what an identity cite rests on) -/
  | present (page : PageId)
  /-- the cited bytes hash to the commitment -/
  | verifies (c : Cite)
  /-- the bytes the cite quotes are the same at its source's current version (rule (b)) -/
  | current (c : Cite)
deriving DecidableEq, Repr

/-- Whether a fact holds in a world, under the byte hash `H`. -/
def holds (H : Hash) (W : World) : Fact → Bool
  | .live p a => match W.current p with
    | some G => G.run a
    | none => false
  | .head p x a => match W.current p with
    | some G => G.isHead x a
    | none => false
  | .present p => !(W p).isEmpty
  | .verifies c => match quoted W c with
    | some b => H b == c.commitment
    | none => false
  | .current c => match quoted W c, latestQuote W c with
    | some b, some b' => b == b'
    | _, _ => false

/-- The facts a cite rests on: an identity cite, that its page exists; a byte cite, that its bytes
verify, and, following, that they are current. -/
def citeFacts (c : Cite) : List Fact :=
  match c.span, c.mode with
  | .identity, _ => [.present c.page]
  | _, .pinned => [.verifies c]
  | _, .following => [.verifies c, .current c]

/-! ### The cite intention -/

/-- What a cite refers to before it is pinned to a version: a page, a span of it, how it tracks it. -/
structure CiteRef where
  page : PageId
  span : Span
  mode : Mode
deriving DecidableEq, Repr

/-- The reference a cite resolves. -/
def Cite.ref (c : Cite) : CiteRef := ⟨c.page, c.span, c.mode⟩

/-- The bytes a reference's span quotes at its page's current version. -/
def currentQuote (W : World) (r : CiteRef) : Option (List UInt8) :=
  (W.current r.page).bind fun G => quoteOf G r.span

/-- The cite of `r` at its page's current version, its bytes committed under `H`. -/
def pinAt (H : Hash) (W : World) (r : CiteRef) : Cite :=
  ⟨r.page, r.span, (W r.page).length - 1, H ((currentQuote W r).getD []), r.mode⟩

/-- A cite pinned at a world where its page has a version, and (for a byte cite) its span quotes
bytes, has every fact it cites hold there. -/
theorem pinAt_holds (H : Hash) (W : World) (r : CiteRef) (hne : W r.page ≠ [])
    (hq : r.span = .identity ∨ (currentQuote W r).isSome = true) :
    ∀ f ∈ citeFacts (pinAt H W r), holds H W f = true := by
  have hlen : 0 < (W r.page).length := List.length_pos_iff.2 hne
  have hq' : quoted W (pinAt H W r) = currentQuote W r := by
    simp only [quoted, currentQuote, pinAt, World.current, List.getLast?_eq_getElem?]
  have hl : latestQuote W (pinAt H W r) = currentQuote W r := by simp [latestQuote, currentQuote, pinAt]
  have hps : (pinAt H W r).span = r.span := rfl
  have hpm : (pinAt H W r).mode = r.mode := rfl
  have hpp : (pinAt H W r).page = r.page := rfl
  intro f hf
  unfold citeFacts at hf
  cases hs : r.span with
  | identity =>
    simp only [hps, hpp, hs, List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
    simp [holds, pinAt, hne]
  | page | block _ | bytes _ =>
    have : (currentQuote W r).isSome = true := hq.resolve_left (by simp [hs])
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 this
    have hv : holds H W (.verifies (pinAt H W r)) = true := by
      simp only [holds, hq', hb]; simp [pinAt, hb]
    have hc : holds H W (.current (pinAt H W r)) = true := by
      simp only [holds, hq', hl, hb, beq_self_eq_true]
    cases hmo : r.mode with
    | pinned =>
      simp only [hps, hpm, hs, hmo, List.mem_cons, List.not_mem_nil, or_false] at hf
      rw [hf]; exact hv
    | following =>
      simp only [hps, hpm, hs, hmo, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact hv
      · exact hc

/-- Why a cite cannot be pinned at a world: its page has no version, or its span quotes nothing
there. -/
inductive CiteRefusal
  | missing (page : PageId)
  | unquoted (page : PageId) (span : Span)
deriving DecidableEq, Repr

/-- Resolve a cite reference at a world: pin it at its page's current version, when the page has
one and (for a byte cite) the span quotes bytes there. -/
def resolveCite (H : Hash) (W : World) (r : CiteRef) : Except CiteRefusal Cite :=
  if (W r.page).isEmpty then .error (.missing r.page)
  else if r.span = .identity ∨ (currentQuote W r).isSome = true then .ok (pinAt H W r)
  else .error (.unquoted r.page r.span)

theorem resolveCite_ok {H : Hash} {W : World} {r : CiteRef} {c : Cite} (h : resolveCite H W r = .ok c) :
    c = pinAt H W r ∧ W r.page ≠ [] ∧ (r.span = .identity ∨ (currentQuote W r).isSome = true) := by
  unfold resolveCite at h
  split at h
  · cases h
  · rename_i hne
    split at h
    · rename_i hq; cases h; exact ⟨rfl, by simpa using hne, hq⟩
    · cases h

theorem resolveCite_of {H : Hash} {W : World} {r : CiteRef} (hne : W r.page ≠ [])
    (hq : r.span = .identity ∨ (currentQuote W r).isSome = true) : resolveCite H W r = .ok (pinAt H W r) := by
  unfold resolveCite
  have he : (W r.page).isEmpty = false := by simpa using hne
  rw [if_neg (by simp [he]), if_pos hq]

/-- **The cite intention** (`Obend.Intention`): a cite's reference resolved at a world of page
histories. Its pins are cites, a pin cites its facts (`citeFacts`), the chooser is the cited page's
owner (whoever writes its next version), and resolving is pinning at the current version. -/
def cites (H : Hash) : Obend.Intention World CiteRef Cite Fact CiteRefusal where
  ref := Cite.ref
  supports := citeFacts
  holds := holds H
  resolve := resolveCite H
  resolve_ref W r c h := by
    obtain ⟨rfl, _, _⟩ := resolveCite_ok h; rfl
  resolve_holds W r c h := by
    obtain ⟨rfl, hne, hq⟩ := resolveCite_ok h
    exact pinAt_holds H W r hne hq

/-! ## The section -/

/-- A run posted on a page: where it lives and what it carries. -/
structure Run where
  page : PageId
  atom : AtomId
  content : Content
deriving DecidableEq, Repr

/-- The cite facts of a run (none unless it is a cite). -/
def Run.cites (r : Run) : List Fact :=
  match r.content with
  | .cite _ c => citeFacts c
  | _ => []

/-- The section of page `p` at position `x`: candidates are runs, each justified by being live and
a head there, and by its cite. -/
def sectionAt (p : PageId) (x : AtomId) : Slot Fact Run where
  supports r := [.live r.page r.atom, .head r.page x r.atom] ++ r.cites
  judge r := r.page == p && match r.content with
    | .field .. => false
    | _ => true

/-- The run stored at an atom of a page version. -/
def Graph.runAt (G : Graph) (p : PageId) (a : AtomId) : Option Run :=
  (G.label a).map fun c => ⟨p, a, c⟩

/-- The runs posted at position `x`: everything the walk meets there, dead or alive. -/
def posted (W : World) (p : PageId) (x : AtomId) : List Run :=
  match W.current p with
  | some G => (G.front x).filterMap (G.runAt p)
  | none => []

theorem run_not_field {G : Graph} {a : AtomId} {n v : String} (h : G.label a = some (.field n v)) :
    G.run a = false := by
  simp [Graph.run, h]

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr' l fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- A run stored on the page is usable in its section iff it is a live head there and its cite
holds. -/
theorem usable_run (H : Hash) {W : World} {p : PageId} {G : Graph} (x : AtomId)
    (hG : W.current p = some G) {a : AtomId} {c : Content} (hl : G.label a = some c) :
    (sectionAt p x).usable (holds H W) ⟨p, a, c⟩ =
      (G.run a && G.isHead x a && (Run.cites ⟨p, a, c⟩).all (holds H W)) := by
  apply Bool.eq_iff_iff.2
  rw [usable_iff]
  simp only [sectionAt, beq_self_eq_true, Bool.true_and, List.cons_append, List.mem_cons,
    forall_eq_or_imp, holds, hG, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨_, h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    cases c with
    | field n v => rw [run_not_field hl] at h1; cases h1
    | text => rfl
    | cite => rfl

/-- **The section's alternatives are the page's heads at the position**, less any cite run whose
cite does not hold. -/
theorem section_alternatives (H : Hash) {W : World} {p : PageId} {G : Graph} (x : AtomId)
    (hG : W.current p = some G) :
    (sectionAt p x).alternatives (holds H W) (posted W p x) =
      ((G.heads x).filterMap (G.runAt p)).filter fun r => r.cites.all (holds H W) := by
  simp only [Slot.alternatives, posted, hG, Graph.heads, List.filter_filterMap,
    List.filterMap_filter]
  apply filterMap_congr'
  intro a _
  cases hl : G.label a with
  | none => simp [Graph.runAt, hl]
  | some c =>
    simp only [Graph.runAt, hl, Option.map_some, Option.filter_some, usable_run H x hG hl]
    cases G.run a <;> cases G.isHead x a <;> simp only [Bool.false_and, Bool.true_and,
      Bool.false_eq_true, if_false, if_true, Option.filter]

/-- **A merge conflict is the section.** Where the page forks into two or more heads, the walk shows
a conflict whose alternatives are those heads; the section there, with nothing selected, reads
`empty`, and its alternatives are the conflict's alternatives as runs (when no cite among them
fails). -/
theorem conflict_is_section (H : Hash) {W : World} {p : PageId} {G : Graph} {x h1 h2 : AtomId}
    {t : List AtomId} (n : Nat) (hG : W.current p = some G) (hc : G.heads x = h1 :: h2 :: t)
    (hcites : ∀ a ∈ G.heads x, ∀ r, G.runAt p a = some r → r.cites.all (holds H W) = true) :
    (sectionAt p x).read (holds H W) none = .empty ∧
    ∃ alts rest, G.walk (n + 1) (fun _ => false) x = .conflict alts :: rest ∧
      (sectionAt p x).alternatives (holds H W) (posted W p x) =
        (alts.map Prod.fst).filterMap (G.runAt p) := by
  obtain ⟨alts, rest, hw, hm⟩ := Graph.walk_conflict G n x h1 h2 t hc
  refine ⟨rfl, alts, rest, hw, ?_⟩
  rw [section_alternatives H x hG, hm, ← hc, List.filter_eq_self]
  intro r hr
  obtain ⟨a, ha, hra⟩ := List.mem_filterMap.1 hr
  exact hcites a ha r hra

/-! ## Cites when the source moves -/

theorem getElem?_append_of_isSome {α : Type} {l ext : List α} {i : Nat} (h : (l[i]?).isSome) :
    (l ++ ext)[i]? = l[i]? := by
  have : i < l.length := by
    rcases Nat.lt_or_ge i l.length with hi | hi
    · exact hi
    · simp [List.getElem?_eq_none hi] at h
  exact List.getElem?_append_left this

/-- The page's history only grows when a source moves. -/
theorem moves_extends {W W' : World} {q : PageId} (hm : SourceMoves W W' q) (p : PageId) :
    ∃ ext, W' p = W p ++ ext := by
  by_cases hp : p = q
  · obtain ⟨ext, _, he⟩ := hm.2; exact ⟨ext, hp ▸ he⟩
  · exact ⟨[], by rw [hm.1 _ hp, List.append_nil]⟩

/-- What a cite quotes at its version is not rewritten when a source moves. -/
theorem quoted_stays {W W' : World} {q : PageId} (hm : SourceMoves W W' q) {c : Cite}
    (h : (quoted W c).isSome) : quoted W' c = quoted W c := by
  obtain ⟨ext, he⟩ := moves_extends hm c.page
  simp only [quoted] at h ⊢
  cases hv : (W c.page)[c.version]? with
  | none => rw [hv] at h; cases h
  | some G => rw [he, getElem?_append_of_isSome (by simp [hv]), hv]

/-- A cite that verifies keeps verifying when any page's history grows: versions are never
rewritten. -/
theorem verifies_stays (H : Hash) {W W' : World} {q : PageId} (hm : SourceMoves W W' q)
    {c : Cite} (h : holds H W (.verifies c) = true) : holds H W' (.verifies c) = true := by
  simp only [holds] at h ⊢
  cases hv : quoted W c with
  | none => rw [hv] at h; cases h
  | some b => rw [quoted_stays hm (by simp [hv]), hv]; rw [hv] at h; exact h

/-- A page that exists keeps existing. -/
theorem present_stays (H : Hash) {W W' : World} {q : PageId} (hm : SourceMoves W W' q)
    {p : PageId} (h : holds H W (.present p) = true) : holds H W' (.present p) = true := by
  obtain ⟨ext, he⟩ := moves_extends hm p
  simp only [holds] at h ⊢
  rw [he]
  cases hw : W p with
  | nil => rw [hw] at h; cases h
  | cons a l => simp

/-- A cite run stays usable when its source (another page) moves, if every one of its cite facts
does. -/
theorem cite_run_stays (H : Hash) {W W' : World} {p x : AtomId} {r : Run} {name : String}
    {c : Cite} (hr : r.content = .cite name c) (hq : c.page ≠ p)
    (hm : SourceMoves W W' c.page) (hu : (sectionAt p x).usable (holds H W) r = true)
    (hc : ∀ f ∈ citeFacts c, holds H W f = true → holds H W' f = true) :
    (sectionAt p x).usable (holds H W') r = true := by
  rw [usable_iff] at hu ⊢
  refine ⟨hu.1, fun f hf => ?_⟩
  have hp : r.page = p := by
    have := hu.1; simp only [sectionAt, Bool.and_eq_true, beq_iff_eq] at this; exact this.1
  have same : W' p = W p := hm.1 p (Ne.symm hq)
  have hf' := hu.2 f hf
  simp only [sectionAt, Run.cites, hr, List.cons_append, List.nil_append, List.mem_cons] at hf
  rcases hf with rfl | rfl | hf
  · simpa [holds, World.current, hp, same] using hf'
  · simpa [holds, World.current, hp, same] using hf'
  · exact hc f hf hf'

/-- **A pinned cite stays usable when its source moves.** A pinned cite run on page `p`, usable
in its section before the cited page `q ≠ p` moves, is usable after. -/
theorem pinned_cite_stays (H : Hash) {W W' : World} {p x : AtomId} {r : Run} {name : String}
    {c : Cite} (hr : r.content = .cite name c) (hpin : c.mode = .pinned) (hq : c.page ≠ p)
    (hm : SourceMoves W W' c.page) (hu : (sectionAt p x).usable (holds H W) r = true) :
    (sectionAt p x).usable (holds H W') r = true := by
  refine cite_run_stays H hr hq hm hu fun f hf hh => ?_
  -- the cite's own slot stays usable (`Obend.Intention.stays`): each of its facts survives the move
  have keep : ∀ f ∈ (cites H).supports c, (cites H).holds W f = true → (cites H).holds W' f = true := by
    intro f hf hh
    show holds H W' f = true
    change f ∈ citeFacts c at hf
    unfold citeFacts at hf
    cases hs : c.span <;> simp only [hs, hpin, List.mem_cons, List.not_mem_nil, or_false] at hf <;>
      subst hf
    · exact present_stays H hm hh
    all_goals exact verifies_stays H hm hh
  have hcur : (cites H).current W c = true := by
    refine ((cites H).current_iff W c).2 fun g hg => ?_
    have hall := ((usable_iff _ _ _).1 hu).2
    exact hall g (by simp [sectionAt, Run.cites, hr]; exact .inr (.inr hg))
  exact ((cites H).current_iff W' c).1
    (((cites H).current_iff_usable rfl W').2 ((cites H).stays rfl keep (((cites H).current_iff_usable rfl W).1 hcur))) f hf

/-- **An identity cite stays usable when its source moves**: it quotes no bytes, so no edit of the
page puts it behind. -/
theorem identity_cite_stays (H : Hash) {W W' : World} {p x : AtomId} {r : Run} {name : String}
    {c : Cite} (hr : r.content = .cite name c) (hid : c.span = .identity) (hq : c.page ≠ p)
    (hm : SourceMoves W W' c.page) (hu : (sectionAt p x).usable (holds H W) r = true) :
    (sectionAt p x).usable (holds H W') r = true := by
  refine cite_run_stays H hr hq hm hu fun f hf hh => ?_
  simp only [citeFacts, hid, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf; exact present_stays H hm hh

/-- **A following byte cite stays current while the bytes it quotes are unchanged** (rule (b)):
usable before its source moves, it is usable after if the source's new current version quotes the
same bytes at its span. -/
theorem following_cite_stays (H : Hash) {W W' : World} {p x : AtomId} {r : Run} {name : String}
    {c : Cite} (hr : r.content = .cite name c) (hq : c.page ≠ p) (hm : SourceMoves W W' c.page)
    (hsame : latestQuote W' c = quoted W c) (hu : (sectionAt p x).usable (holds H W) r = true) :
    (sectionAt p x).usable (holds H W') r = true := by
  have hcur : holds H W (.current c) = true → holds H W' (.current c) = true := by
    intro hh
    simp only [holds] at hh ⊢
    cases hv : quoted W c with
    | none => rw [hv] at hh; cases hh
    | some b => rw [quoted_stays hm (by simp [hv]), hv, hsame, hv]; simp
  refine cite_run_stays H hr hq hm hu fun f hf hh => ?_
  unfold citeFacts at hf
  cases hs : c.span with
  | identity =>
    simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
    exact present_stays H hm hh
  | page | block _ | bytes _ =>
    cases hmo : c.mode <;> simp only [hs, hmo, List.mem_cons, List.not_mem_nil, or_false] at hf
    · subst hf; exact verifies_stays H hm hh
    · rcases hf with rfl | rfl
      · exact verifies_stays H hm hh
      · exact hcur hh

/-- **A following cite falls behind when the bytes it quotes change.** A following byte cite run,
current before the cited page moves, reads `blocked` once selected after if the new current
version quotes other bytes at its span; the read names its `current` fact. -/
theorem following_cite_behind (H : Hash) {W W' : World} {p x : AtomId} {r : Run} {name : String}
    {c : Cite} (hr : r.content = .cite name c) (hfol : c.mode = .following) (hspan : c.span ≠ .identity)
    (hm : SourceMoves W W' c.page) (hj : (sectionAt p x).judge r = true)
    (hcur : holds H W (.current c) = true) (hchg : latestQuote W' c ≠ quoted W c) :
    ∃ d, (sectionAt p x).read (holds H W') (some r) = .blocked r d ∧ Fact.current c ∈ d := by
  have hcur' : holds H W' (.current c) = false := by
    simp only [holds] at hcur ⊢
    cases hv : quoted W c with
    | none => rw [hv] at hcur; cases hcur
    | some b =>
      rw [quoted_stays hm (by simp [hv]), hv]
      cases hl : latestQuote W' c with
      | none => rfl
      | some b' =>
        rw [hv, hl] at hchg
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => hchg (h ▸ rfl)
  have hfacts : Fact.current c ∈ citeFacts c := by
    unfold citeFacts
    cases hs : c.span <;> simp [hs, hfol] at hspan ⊢
  -- the cite's dead fact is named by the section that carries the cite (`Obend.Intention.blocked_within`)
  exact (cites H).blocked_within (sectionAt p x) hj (p := c)
    (fun f hf => by simp [sectionAt, Run.cites, hr]; exact .inr (.inr hf)) hfacts hcur'

/-- Re-justify a cite against its source's current version (under the hash `H`): its reference,
pinned again at the world. -/
def recite (H : Hash) (W : World) (c : Cite) : Cite := pinAt H W c.ref

theorem recite_span (H : Hash) (W : World) (c : Cite) : (recite H W c).span = c.span := rfl
theorem recite_mode (H : Hash) (W : World) (c : Cite) : (recite H W c).mode = c.mode := rfl
theorem recite_page (H : Hash) (W : World) (c : Cite) : (recite H W c).page = c.page := rfl

/-- Re-citing a cite at a world where its source has a version, and (for a byte cite) quotes its
span, makes its facts hold there. -/
theorem recite_holds (H : Hash) (W : World) (c : Cite) (hne : W c.page ≠ [])
    (hq : c.span = .identity ∨ (latestQuote W c).isSome = true) :
    ∀ f ∈ citeFacts (recite H W c), holds H W f = true := by
  have h : (cites H).renew W c = .ok (recite H W c) := resolveCite_of (r := c.ref) hne hq
  exact ((cites H).current_iff W _).1 ((cites H).renew_fill h).2.2

/-- **`recite` is the intention's renewal**: re-citing a cite that can be pinned is renewing it. -/
theorem recite_renew (H : Hash) {W : World} {c c' : Cite} (h : (cites H).renew W c = .ok c') :
    c' = recite H W c := (resolveCite_ok h).1

/-- **A re-cite is a usable fill of the cite's slot** (`Obend.Intention.renew_fill`): after
`recite`, the cite's slot reads usable at the world. -/
theorem recite_usable (H : Hash) {W : World} {c c' : Cite} (h : (cites H).renew W c = .ok c') :
    ((cites H).slot c.ref).read (holds H W) (some c') =
      .usable c' (((cites H).slot c.ref).evidence (holds H W) c') :=
  (cites H).renew_repairs h

/-- **Staleness of a cite is a blocked read** (`Obend.Intention.stale_iff_blocked`): a cite's facts
fail at a world exactly when its slot's read there is blocked, naming exactly the failing facts. -/
theorem cite_stale_iff_blocked (H : Hash) (W : World) (c : Cite) :
    (cites H).current W c = false ↔
      ((cites H).slot c.ref).read (holds H W) (some c) = .blocked c ((citeFacts c).filter fun f => !holds H W f) :=
  (cites H).stale_iff_blocked rfl W


/-! ### Teeth -/

namespace Teeth

/-- A toy byte hash: the byte sum. Every theorem above is for every hash. -/
def toy : Hash := fun (b : List UInt8) => [(b.foldl (fun s (x : UInt8) => s + x.toNat) 0).toUInt8]

/-- Page 2, "Beta", one version: `beta`. -/
def beta : Graph := Graph.empty.apply [.add 1 (.text "beta") root]
/-- Beta after an edit. -/
def beta' : Graph := beta.apply [.add 2 (.text "!") 1]

/-- An embed of Beta (its whole text) at version 0. -/
def citeOf (m : Mode) : Cite := ⟨2, .page, 0, toy (bytes "beta"), m⟩

/-- A following cite of Beta's first four bytes, and a cite of Beta's identity. -/
def rangeCite : Cite := ⟨2, .bytes ⟨0, 4⟩, 0, toy (bytes "beta"), .following⟩
def idCite : Cite := ⟨2, .identity, 0, [], .following⟩

/-- Page 1, "Alpha": a run, then a transclusion of Beta. -/
def alpha (m : Mode) : Graph :=
  Graph.empty.apply [.add 1 (.text "see ") root, .add 2 (.cite "Beta" (citeOf m)) 1]

def world (m : Mode) : World := fun p => if p = 1 then [alpha m] else if p = 2 then [beta] else []
def moved (m : Mode) : World :=
  fun p => if p = 1 then [alpha m] else if p = 2 then [beta, beta'] else []

theorem moves (m : Mode) : SourceMoves (world m) (moved m) 2 :=
  ⟨fun p hp => by simp [world, moved, hp], [beta'], by simp, by simp [world, moved]⟩

def citeRun (m : Mode) : Run := ⟨1, 2, .cite "Beta" (citeOf m)⟩

example : beta.source = "beta" ∧ beta'.source = "beta!" := by decide
example : (sectionAt 1 1).usable (holds toy (world .pinned)) (citeRun .pinned) = true := by decide
example : (sectionAt 1 1).usable (holds toy (world .following)) (citeRun .following) = true := by
  decide

/-- Pinned: still usable after Beta moves (the theorem, and the kernel agreeing). -/
example : (sectionAt 1 1).usable (holds toy (moved .pinned)) (citeRun .pinned) = true :=
  pinned_cite_stays toy rfl rfl (by decide) (moves .pinned) (by decide)

/-- Following: blocked after Beta moves, naming its currency. -/
example : (sectionAt 1 1).read (holds toy (moved .following)) (some (citeRun .following)) =
    .blocked (citeRun .following) [.current (citeOf .following)] := rfl

/-- Rule (b): a following cite of bytes the edit did not touch stays usable (the theorem, and the
kernel agreeing); so does a cite of Beta's identity. -/
example : (sectionAt 1 1).usable (holds toy (moved .following)) ⟨1, 2, .cite "Beta" rangeCite⟩ = true :=
  following_cite_stays toy rfl (by decide) (moves .following) (by decide) (by decide)
example : (sectionAt 1 1).usable (holds toy (moved .following)) ⟨1, 2, .cite "Beta" idCite⟩ = true :=
  identity_cite_stays toy rfl rfl (by decide) (moves .following) (by decide)

/-- Re-cited at the new version, it is usable again. -/
example : (sectionAt 1 1).usable (holds toy (moved .following))
    ⟨1, 2, .cite "Beta" (recite toy (moved .following) (citeOf .following))⟩ = true := by decide

/-- A cite whose bytes do not match its commitment is dead even pinned. -/
example : holds toy (world .pinned) (.verifies { citeOf .pinned with span := .bytes ⟨1, 3⟩ }) = false := by
  decide

/-- The section of a conflicted page: at `a`, the heads `c` and `d`, read with nothing selected. -/
def conflicted : World := fun p => if p = 1 then [Obend.Doc.Teeth.merged] else []
example : (sectionAt 1 1).alternatives (holds toy conflicted) (posted conflicted 1 1) =
    [⟨1, 3, .text "c"⟩, ⟨1, 4, .text "d"⟩] := by decide
example : (sectionAt 1 1).read (holds toy conflicted) none = .empty := rfl
example : Obend.Doc.Teeth.merged.source = "a<<<<<<<\nc=======\nd>>>>>>>\nb" := by decide

end Teeth

#tooth pinned_cite_stays by mutation citeFacts := fun c => [.current c]
#tooth following_cite_behind by mutation citeFacts := fun c => [.verifies c]
#tooth section_alternatives by mutation posted := fun _ _ _ => []
#tooth identity_cite_stays by mutation citeFacts := fun c => [.current c]
#tooth following_cite_stays by mutation quoted := fun _ _ => none
#tooth recite_holds by mutation recite := fun _ _ c => c

end Obend.Doc

end
