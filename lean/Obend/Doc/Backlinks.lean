module
/-
# Obend.Doc.Backlinks — the reverse index of cites, which the kernel maintains

A cite is a support of the run that carries it (`Obend.Doc.Section`): the section judging that run
asks whether the cited page is present, whether the quoted bytes verify, whether they are current.
So when a page MOVES, the kernel must re-judge exactly the runs that cite it, and it keeps the
index that finds them: page `q`'s BACKLINKS, every live cite of `q` in the current version of
every page, each entry naming the citing page, the atom and the cite.

* `mem_backlinks`: the index is AUTHENTIC: an entry is in it iff it is a page of the vault whose
  current version stores that cite, live, at that atom, of `q` (`Backlink.Authentic`, a check a
  reader runs against the world, entry by entry), so it lists no cite that is not there and misses
  none that is.
* `post_correct`: the kernel MAINTAINS it: when a page posts a new version, dropping that page's
  entries and adding the new version's gives the index of the new world.
* `usable_unmoved`: and that is all it needs to re-judge: when `q` moves, a run of another page that
  is not a cite of `q` is usable in its section exactly when it was.
-/
public import Obend.Doc.Render
public import Obend.Tactic.Tooth
public section

namespace Obend.Doc

set_option autoImplicit false

open Obend.Slot Obend.Digest.HashBytes

/-- An index entry: the citing page, the atom, and the cite stored there. -/
structure Backlink where
  source : PageId
  atom : AtomId
  cite : Cite
deriving DecidableEq, Repr

/-- The live cites of `q` stored in the version `G` of page `p`, one entry per atom. -/
def Graph.citesOf (G : Graph) (p q : PageId) : List Backlink :=
  (G.atoms.map (·.1)).eraseDups.filterMap fun a =>
    match G.label a with
    | some (.cite _ c) => if c.page = q ∧ G.run a = true then some ⟨p, a, c⟩ else none
    | _ => none

/-- The backlinks of `q` over the pages `ps`: every live cite of `q` in their current versions. -/
def backlinks (W : World) (ps : List PageId) (q : PageId) : List Backlink :=
  ps.flatMap fun p => match W.current p with
    | some G => G.citesOf p q
    | none => []

/-- An entry is AUTHENTIC at a world: its page's current version stores that cite, live, at that
atom, and it cites `q`. -/
def Backlink.Authentic (W : World) (q : PageId) (b : Backlink) : Prop :=
  ∃ G n, W.current b.source = some G ∧ G.label b.atom = some (.cite n b.cite) ∧ G.run b.atom = true ∧
    b.cite.page = q

theorem mem_of_lookup {a : AtomId} {c : Content} : ∀ {l : List (AtomId × Content)},
    l.lookup a = some c → a ∈ l.map (·.1)
  | [], h => by simp at h
  | (b, d) :: l, h => by
    by_cases hb : a = b
    · subst hb; simp
    · have : (a == b) = false := by simpa using hb
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem mem_atoms_of_label {G : Graph} {a : AtomId} {c : Content} (h : G.label a = some c) :
    a ∈ G.atoms.map (·.1) := mem_of_lookup h

theorem mem_citesOf {G : Graph} {p q : PageId} {b : Backlink} :
    b ∈ G.citesOf p q ↔ b.source = p ∧ ∃ n, G.label b.atom = some (.cite n b.cite) ∧ G.run b.atom = true ∧
      b.cite.page = q := by
  simp only [Graph.citesOf, List.mem_filterMap, List.mem_eraseDups]
  constructor
  · rintro ⟨a, _, h⟩
    cases hl : G.label a with
    | none => simp [hl] at h
    | some c =>
      cases c with
      | cite n ct =>
        simp only [hl] at h
        by_cases hc : ct.page = q ∧ G.run a = true
        · simp only [hc, and_self, ite_true, Option.some.injEq] at h
          subst h; exact ⟨rfl, n, hl, hc.2, hc.1⟩
        · simp [hc] at h
      | text => simp [hl] at h
      | field => simp [hl] at h
  · rintro ⟨hs, n, hl, hr, hq⟩
    refine ⟨b.atom, mem_atoms_of_label hl, ?_⟩
    simp only [hl, hq, hr, and_self, ite_true]
    cases b; simp_all

/-- **The index is authentic**: an entry is a backlink of `q` iff its page is one of the vault's
and the world stores that live cite of `q` there. -/
theorem mem_backlinks {W : World} {ps : List PageId} {q : PageId} {b : Backlink} :
    b ∈ backlinks W ps q ↔ b.source ∈ ps ∧ b.Authentic W q := by
  simp only [backlinks, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hb⟩
    cases hG : W.current p with
    | none => rw [hG] at hb; cases hb
    | some G =>
      rw [hG] at hb
      obtain ⟨rfl, n, hl, hr, hq⟩ := mem_citesOf.1 hb
      exact ⟨hp, G, n, hG, hl, hr, hq⟩
  · rintro ⟨hp, G, n, hG, hl, hr, hq⟩
    exact ⟨b.source, hp, by rw [hG]; exact mem_citesOf.2 ⟨rfl, n, hl, hr, hq⟩⟩

/-- The kernel's index: each page's backlinks. -/
abbrev Index := PageId → List Backlink

/-- Page `p` posts the version `G`: its old entries go, the new version's come. -/
def Index.post (I : Index) (p : PageId) (G : Graph) : Index :=
  fun q => (I q).filter (fun b => b.source != p) ++ G.citesOf p q

/-- **The index is maintained**: if `I` lists every backlink of the world `W` (over the pages `ps`,
`p` among them) and page `p` posts the version `G`, then `I.post p G` lists every backlink of the
new world, and nothing else. -/
theorem post_correct {W W' : World} {ps : List PageId} {p : PageId} {G : Graph} {I : Index}
    (hp : p ∈ ps) (hI : ∀ q b, b ∈ I q ↔ b ∈ backlinks W ps q) (hW : W' p = W p ++ [G])
    (hother : ∀ p', p' ≠ p → W' p' = W p') :
    ∀ q b, b ∈ I.post p G q ↔ b ∈ backlinks W' ps q := by
  intro q b
  have hcur : W'.current p = some G := by simp [World.current, hW]
  simp only [Index.post, List.mem_append, List.mem_filter, hI, mem_backlinks, bne_iff_ne, ne_eq]
  by_cases hs : b.source = p
  · simp only [Backlink.Authentic, mem_citesOf, hs, not_true_eq_false, and_false, false_or, true_and, hp,
      hcur]
    constructor
    · rintro ⟨n, hl, hr, hq⟩; exact ⟨G, n, rfl, hl, hr, hq⟩
    · rintro ⟨G', n, h, hl, hr, hq⟩; cases h; exact ⟨n, hl, hr, hq⟩
  · have hcur' : W'.current b.source = W.current b.source := by simp [World.current, hother _ hs]
    simp only [Backlink.Authentic, hcur', mem_citesOf, hs, not_false_eq_true, and_true, false_and, or_false]

/-- The page a fact is about. -/
def Fact.page : Fact → PageId
  | .live p _ | .head p _ _ | .present p => p
  | .verifies c | .current c => c.page

/-- A fact reads its world only at its page. -/
theorem holds_congr (H : Hash) {W W' : World} (f : Fact) (h : W' f.page = W f.page) :
    holds H W' f = holds H W f := by
  cases f <;> simp only [Fact.page] at h <;>
    simp only [holds, World.current, quoted, latestQuote, h]

/-- A cite's facts are about its page. -/
theorem citeFacts_page {c : Cite} {f : Fact} (h : f ∈ citeFacts c) : f.page = c.page := by
  unfold citeFacts at h
  cases hs : c.span <;> cases hmo : c.mode <;> simp only [hs, hmo] at h <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
    (try rcases h with rfl | rfl) <;> (try subst h) <;> rfl

/-- **A move re-judges only the backlinks.** When page `q` moves, a run of another page that is
not a cite of `q` is usable in its section exactly when it was. -/
theorem usable_unmoved (H : Hash) {W W' : World} {q : PageId} (hm : SourceMoves W W' q)
    {p x : AtomId} {r : Run} (hp : r.page ≠ q) (hnot : ∀ n c, r.content = .cite n c → c.page ≠ q) :
    (sectionAt p x).usable (holds H W') r = (sectionAt p x).usable (holds H W) r := by
  have key : ∀ f ∈ (sectionAt p x).supports r, holds H W' f = holds H W f := by
    intro f hf
    apply holds_congr
    apply hm.1
    simp only [sectionAt, List.cons_append, List.mem_cons] at hf
    rcases hf with rfl | rfl | hf
    · exact hp
    · exact hp
    · simp only [Run.cites] at hf
      cases hc : r.content with
      | cite n c => rw [hc] at hf; rw [citeFacts_page hf]; exact hnot n c hc
      | text => rw [hc] at hf; cases hf
      | field => rw [hc] at hf; cases hf
  apply Bool.eq_iff_iff.2
  rw [usable_iff, usable_iff]
  exact ⟨fun ⟨hj, hs⟩ => ⟨hj, fun f hf => (key f hf) ▸ hs f hf⟩,
    fun ⟨hj, hs⟩ => ⟨hj, fun f hf => (key f hf).symm ▸ hs f hf⟩⟩

/-! ### Teeth -/

namespace Teeth

open Obend.Doc.Teeth (toy)

/-- Beta's backlinks in the vault: Alpha's identity link, embed and block reference, at atoms 3, 7
and 10; Alpha's: Beta's link at atom 3. -/
example : (backlinks (vault.read toy) [1, 2] 2).map (fun b => (b.source, b.atom)) = [(1, 3), (1, 7), (1, 10)] := by
  decide
example : (backlinks (vault.read toy) [1, 2] 1).map (fun b => (b.source, b.atom)) = [(2, 3)] := by decide

/-- Alpha drops its embed (a new version with atom 7 deleted): the maintained index agrees with
the recomputed one. -/
def dropped : World := fun p =>
  if p = 1 then vault.read toy 1 ++ (vault.read toy 1).map (·.apply [.delete 7]) else vault.read toy p
example : ((Index.post (backlinks (vault.read toy) [1, 2]) 1
    (((vault.read toy 1).map (·.apply [.delete 7])).head?.getD Graph.empty)) 2).map (·.atom) = [3, 10] ∧
    (backlinks dropped [1, 2] 2).map (·.atom) = [3, 10] := by decide

end Teeth

#tooth mem_backlinks by mutation Graph.citesOf := fun _ _ _ => []
#tooth post_correct by mutation Index.post := fun I _ _ => I
#tooth usable_unmoved by mutation citeFacts := fun _ => [.present 2]

end Obend.Doc

end
