module
/-
# Obend.Doc.Section — a section is a slot over runs; a cite is a support

DESIGN §5: a SECTION is a slot at type `Run` whose candidates are the runs members posted at a
position, and a CITE is a support `(page, range, version, byte commitment)` of another page's bytes.
This module builds both on `Obend.Slot` without adding to it:

* a `World` is every page's history of versions, oldest first; the last is current. A source MOVES
  when its history grows and nothing else changes (`SourceMoves`).
* the facts a view is asked about: a run is `live`; it is a `head` at its position (no other live
  run there precedes it); a cite `verifies` (the cited version's bytes over the range hash to the
  commitment); a cite is `current` (it cites the source's current version).
* `sectionAt p x` is `Slot Fact Run`: a run's supports are `live`, `head`, and, for a cite run, the
  cite's facts: `verifies` for a pinned cite, `verifies` and `current` for a following one.

`section_alternatives`: the slot's `alternatives` at a position are exactly the page's `heads`
there (less any cite run whose cite fails). `conflict_is_section`: where the walk shows a conflict
(two or more heads, `walk_conflict`), the section's read is `empty` (no selection) and its
alternatives are that conflict's alternatives: the conflict IS the section. `pinned_cite_stays`: a
pinned cite run usable before its source moves is usable after. `following_cite_behind`: a selected
following cite run reads `blocked` after its source moves, naming its `current` fact; and
re-citing the new version (`recite`) makes its facts hold again (`recite_holds`).

The commitment is taken under any byte hash `H`; nothing here assumes anything of it. Teeth use a
toy additive hash, which is as good as any for a statement that holds for every hash.
-/
public import Obend.Doc.Merge
public import Obend.Slot
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

/-- How one atom reads in the page's source: a run its text, a cite its wikilink. -/
def atomText (G : Graph) (a : AtomId) : String :=
  match G.label a with
  | some (.text s) => s
  | some (.cite n _) => "[[" ++ n ++ "]]"
  | _ => ""

mutual
/-- The source text of segments. -/
def segsText (G : Graph) : List Segment → String
  | [] => ""
  | s :: ss => G.segText s ++ G.segsText ss
/-- The source text of a segment; a conflict shows every alternative between markers. -/
def segText (G : Graph) : Segment → String
  | .run a => G.atomText a
  | .conflict alts => "<<<<<<<\n" ++ G.altsText alts ++ ">>>>>>>\n"
/-- Alternatives, separated. -/
def altsText (G : Graph) : List (AtomId × List Segment) → String
  | [] => ""
  | [(_, ss)] => G.segsText ss
  | (_, ss) :: rest => G.segsText ss ++ "=======\n" ++ G.altsText rest
end

/-- A page version's source text: its content, in order. -/
def source (G : Graph) : String := G.segsText G.content

end Graph

/-! ## Worlds and facts -/

/-- Every page's history of versions, oldest first. -/
abbrev World := PageId → List Graph

/-- A page's current version. -/
def World.current (W : World) (p : PageId) : Option Graph := (W p).getLast?

/-- The source MOVES: its history grows by at least one version, and nothing else changes. -/
def SourceMoves (W W' : World) (q : PageId) : Prop :=
  (∀ p, p ≠ q → W' p = W p) ∧ ∃ ext, ext ≠ [] ∧ W' q = W q ++ ext

/-- The bytes a cite quotes, if its version exists. -/
def quoted (W : World) (c : Cite) : Option (List UInt8) :=
  ((W c.page)[c.version]?).map fun G => ((bytes G.source).drop c.range.start).take c.range.len

/-- What a view is asked. -/
inductive Fact
  /-- the run's atom is a live run of its page's current version -/
  | live (page : PageId) (atom : AtomId)
  /-- no other live run at position `pos` of the page precedes it -/
  | head (page : PageId) (pos : AtomId) (atom : AtomId)
  /-- the cited bytes hash to the commitment -/
  | verifies (c : Cite)
  /-- the cite cites its source's current version -/
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
  | .verifies c => match quoted W c with
    | some b => H b == c.commitment
    | none => false
  | .current c => (W c.page).length == c.version + 1

/-- The facts a cite rests on. -/
def citeFacts (c : Cite) : List Fact :=
  match c.mode with
  | .pinned => [.verifies c]
  | .following => [.verifies c, .current c]

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

/-- A cite that verifies keeps verifying when any page's history grows: versions are never
rewritten. -/
theorem verifies_stays (H : Hash) {W W' : World} {q : PageId} (hm : SourceMoves W W' q)
    {c : Cite} (h : holds H W (.verifies c) = true) : holds H W' (.verifies c) = true := by
  have hq : ∃ ext, W' c.page = W c.page ++ ext := by
    by_cases hp : c.page = q
    · obtain ⟨ext, _, he⟩ := hm.2; exact ⟨ext, hp ▸ he⟩
    · exact ⟨[], by rw [hm.1 _ hp, List.append_nil]⟩
  obtain ⟨ext, he⟩ := hq
  simp only [holds, quoted] at h ⊢
  cases hv : (W c.page)[c.version]? with
  | none => rw [hv] at h; cases h
  | some G =>
    rw [he, getElem?_append_of_isSome (by simp [hv]), hv]
    rw [hv] at h; exact h

/-- **A pinned cite stays usable when its source moves.** A pinned cite run on page `p`, usable
in its section before the cited page `q ≠ p` moves, is usable after. -/
theorem pinned_cite_stays (H : Hash) {W W' : World} {p x : AtomId} {r : Run} {name : String}
    {c : Cite} (hr : r.content = .cite name c) (hpin : c.mode = .pinned) (hq : c.page ≠ p)
    (hm : SourceMoves W W' c.page) (hu : (sectionAt p x).usable (holds H W) r = true) :
    (sectionAt p x).usable (holds H W') r = true := by
  rw [usable_iff] at hu ⊢
  refine ⟨hu.1, fun f hf => ?_⟩
  have hp : r.page = p := by
    have := hu.1; simp only [sectionAt, Bool.and_eq_true, beq_iff_eq] at this; exact this.1
  have same : W' p = W p := hm.1 p (Ne.symm hq)
  simp only [sectionAt, Run.cites, hr, citeFacts, hpin, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  have hf' := hu.2 f (by simp [sectionAt, Run.cites, hr, citeFacts, hpin, hf])
  rcases hf with rfl | rfl | rfl
  · simpa [holds, World.current, hp, same] using hf'
  · simpa [holds, World.current, hp, same] using hf'
  · exact verifies_stays H hm hf'

/-- **A following cite falls behind when its source moves.** A following cite run, current before
the cited page moves, reads `blocked` once selected after, and the read names its `current` fact. -/
theorem following_cite_behind (H : Hash) {W W' : World} {p x : AtomId} {r : Run} {name : String}
    {c : Cite} (hr : r.content = .cite name c) (hfol : c.mode = .following)
    (hm : SourceMoves W W' c.page) (hj : (sectionAt p x).judge r = true)
    (hcur : holds H W (.current c) = true) :
    ∃ d, (sectionAt p x).read (holds H W') (some r) = .blocked r d ∧ Fact.current c ∈ d := by
  have hcur' : holds H W' (.current c) = false := by
    obtain ⟨ext, hne, he⟩ := hm.2
    simp only [holds, he, List.length_append, beq_iff_eq] at hcur ⊢
    cases ext with
    | nil => exact absurd rfl hne
    | cons _ _ => simp; omega
  have hmem : Fact.current c ∈ (sectionAt p x).dead (holds H W') r :=
    (mem_dead_iff _ _ _ _).2 ⟨by simp [sectionAt, Run.cites, hr, citeFacts, hfol], hcur'⟩
  unfold Slot.read
  simp only [hj, if_true]
  cases hd : (sectionAt p x).dead (holds H W') r with
  | nil => rw [hd] at hmem; cases hmem
  | cons g t => exact ⟨g :: t, rfl, hd ▸ hmem⟩

/-- Re-justify a cite against its source's current version (under the hash `H`). -/
def recite (H : Hash) (W : World) (c : Cite) : Cite :=
  let v := (W c.page).length - 1
  { c with version := v,
           commitment := H ((((W c.page)[v]?).map fun G =>
             ((bytes G.source).drop c.range.start).take c.range.len).getD []) }

/-- Re-citing a following cite at a world where its source has a version makes it hold there. -/
theorem recite_holds (H : Hash) (W : World) (c : Cite) (hne : W c.page ≠ []) :
    ∀ f ∈ citeFacts (recite H W c), holds H W f = true := by
  have hlen : 0 < (W c.page).length := List.length_pos_iff.2 hne
  have hv : ((W c.page).length - 1) < (W c.page).length := by omega
  intro f hf
  have hfacts : f = .verifies (recite H W c) ∨ f = .current (recite H W c) := by
    unfold citeFacts at hf
    split at hf <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    · exact .inl hf
    · exact hf
  rcases hfacts with rfl | rfl
  · simp only [holds, quoted, recite, List.getElem?_eq_getElem hv, Option.map_some, Option.getD_some,
      beq_self_eq_true]
  · simp only [holds, recite, beq_iff_eq]; omega

/-! ### Teeth -/

namespace Teeth

/-- A toy byte hash: the byte sum. Every theorem above is for every hash. -/
def toy : Hash := fun (b : List UInt8) => [(b.foldl (fun s (x : UInt8) => s + x.toNat) 0).toUInt8]

/-- Page 2, "Beta", one version: `beta`. -/
def beta : Graph := Graph.empty.apply [.add 1 (.text "beta") root]
/-- Beta after an edit. -/
def beta' : Graph := beta.apply [.add 2 (.text "!") 1]

/-- A cite of Beta's first four bytes at version 0. -/
def citeOf (m : Mode) : Cite := ⟨2, ⟨0, 4⟩, 0, toy (bytes "beta"), m⟩

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

/-- Re-cited at the new version, it is usable again. -/
example : (sectionAt 1 1).usable (holds toy (moved .following))
    ⟨1, 2, .cite "Beta" (recite toy (moved .following) (citeOf .following))⟩ = true := by decide

/-- A cite whose bytes do not match its commitment is dead even pinned. -/
example : holds toy (world .pinned) (.verifies { citeOf .pinned with range := ⟨1, 3⟩ }) = false := by
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

end Obend.Doc

end
