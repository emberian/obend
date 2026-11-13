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
import all Obend.Doc.Graph
import all Obend.Doc.Patch
import all Obend.Doc.Merge
import all Obend.Doc.Section
import all Obend.Doc.Render
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
      | cell => simp [hl] at h
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
      | cell => rw [hc] at hf; cases hf
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

/-! ## Transitive `#^block` Citation Impact Closure (`impactedBacklinksFuel`) -/

/-- Direct downstream cells in `deps` (where each entry `(citingCell, citedBlock)` records that
`citingCell` carries a `#^citedBlock` citation to `citedBlock`) that directly depend on `k`. -/
@[expose] def directCiteDependents (deps : List (String × String)) (k : String) : List String :=
  deps.filterMap fun e => if e.2 == k then some e.1 else none

theorem mem_directCiteDependents {deps : List (String × String)} {k c : String} :
    c ∈ directCiteDependents deps k ↔ (c, k) ∈ deps := by
  simp only [directCiteDependents, List.mem_filterMap]
  constructor
  · rintro ⟨⟨src, dst⟩, hMem, hIf⟩
    by_cases hEq : dst = k
    · subst hEq
      simp at hIf
      subst hIf
      exact hMem
    · have hFalse : (dst == k) = false := beq_eq_false_iff_ne.2 hEq
      simp [hFalse] at hIf
  · intro hMem
    exact ⟨(c, k), hMem, by simp⟩

/-- Deduplicate a list of cell/block keys, preserving the first occurrence of each key. -/
@[expose] def dedupCellKeys : List String → List String
  | [] => []
  | c :: rest => c :: (dedupCellKeys rest).filter (· != c)

theorem nodup_filter_bool {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 h
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.nodup_cons]
      refine ⟨fun hMem => hx (List.mem_filter.1 hMem).1, ih hxs⟩
    · have hpf : p x = false := Bool.eq_false_iff.2 hp
      rw [List.filter_cons_of_neg (by simp [hpf])]
      exact ih hxs

theorem nodup_append_of_disjoint {α : Type} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hDisj : ∀ x ∈ l₁, x ∉ l₂) :
    (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => exact h₂
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 h₁
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, ih hxs (fun y hy => hDisj y (List.mem_cons_of_mem x hy))⟩
    rw [List.mem_append]
    rintro (hInXs | hInL2)
    · exact hx hInXs
    · exact hDisj x List.mem_cons_self hInL2

@[simp] theorem mem_dedupCellKeys {l : List String} {x : String} :
    x ∈ dedupCellKeys l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupCellKeys]
  | cons c rest ih =>
    simp only [dedupCellKeys, List.mem_cons, List.mem_filter, ih, bne_iff_ne]
    constructor
    · rintro (rfl | ⟨hIn, _⟩)
      · exact .inl rfl
      · exact .inr hIn
    · rintro (rfl | hIn)
      · exact .inl rfl
      · by_cases hEq : x = c
        · exact .inl hEq
        · exact .inr ⟨hIn, hEq⟩

theorem nodup_dedupCellKeys (l : List String) : (dedupCellKeys l).Nodup := by
  induction l with
  | nil => simp [dedupCellKeys]
  | cons c rest ih =>
    simp only [dedupCellKeys, List.nodup_cons, List.mem_filter, bne_iff_ne]
    refine ⟨fun ⟨_, hNe⟩ => hNe rfl, nodup_filter_bool _ ih⟩

/-- One step of transitive `#^block` citation impact expansion: preserves `visited` and appends
all newly discovered downstream cells (deduplicated) that directly cite any cell in `visited`. -/
@[expose] def impactStep (deps : List (String × String)) (visited : List String) : List String :=
  let nextHop := dedupCellKeys (visited.flatMap (directCiteDependents deps))
  visited ++ (nextHop.filter fun c => !visited.contains c)

/-- `impactStep` preserves `List.Nodup` (no duplicate cells are emitted even on diamond graphs). -/
theorem nodup_impactStep (deps : List (String × String)) {visited : List String}
    (hVis : visited.Nodup) :
    (impactStep deps visited).Nodup := by
  apply nodup_append_of_disjoint hVis
  · exact nodup_filter_bool _ (nodup_dedupCellKeys _)
  · intro x hx hInFilter
    simp only [List.mem_filter] at hInFilter
    have hContains : visited.contains x = true := List.contains_iff_mem.2 hx
    rw [hContains] at hInFilter
    cases hInFilter.2

/-- `impactStep` is inflationary (every already-impacted cell remains in `impactStep deps visited`). -/
theorem subset_impactStep (deps : List (String × String)) (visited : List String) :
    ∀ x ∈ visited, x ∈ impactStep deps visited := by
  intro x hx
  simp [impactStep, hx]

/-- Every cell directly citing an element of `visited` belongs to `impactStep deps visited`. -/
theorem step_contains_directCiteDependent
    {deps : List (String × String)} {visited : List String} {citingCell citedBlock : String}
    (hEdge : (citingCell, citedBlock) ∈ deps)
    (hCited : citedBlock ∈ visited) :
    citingCell ∈ impactStep deps visited := by
  simp only [impactStep, List.mem_append, List.mem_filter, mem_dedupCellKeys, List.mem_flatMap]
  by_cases hIn : citingCell ∈ visited
  · exact .inl hIn
  · have hNotContains : (!visited.contains citingCell) = true := by
      cases hc : visited.contains citingCell
      · rfl
      · exfalso; exact hIn (List.contains_iff_mem.1 hc)
    exact .inr ⟨⟨citedBlock, hCited, mem_directCiteDependents.2 hEdge⟩, hNotContains⟩

/-- Iterate `impactStep` for `fuel` rounds starting from `visited`. -/
@[expose] def impactedClosureFuel
    (fuel : Nat) (deps : List (String × String)) (visited : List String) : List String :=
  match fuel with
  | 0 => visited
  | n + 1 => impactedClosureFuel n deps (impactStep deps visited)

/-- **Transitive Citation Impact Closure (`impactedBacklinksFuel`)**:
computes all downstream cells whose `#^block` citations transitively depend on a modified cell key `k`
within `fuel` rounds. -/
@[expose] def impactedBacklinksFuel
    (fuel : Nat) (deps : List (String × String)) (k : String) : List String :=
  impactedClosureFuel fuel deps [k]

theorem nodup_impactedClosureFuel
    (fuel : Nat) (deps : List (String × String)) {visited : List String}
    (hVis : visited.Nodup) :
    (impactedClosureFuel fuel deps visited).Nodup := by
  induction fuel generalizing visited with
  | zero => exact hVis
  | succ n ih =>
    exact ih (nodup_impactStep deps hVis)

/-- `impactedBacklinksFuel` never emits duplicate cell keys, regardless of cycles or diamond paths. -/
theorem impactedBacklinksFuel_nodup
    (fuel : Nat) (deps : List (String × String)) (k : String) :
    (impactedBacklinksFuel fuel deps k).Nodup :=
  nodup_impactedClosureFuel fuel deps (by simp)

/-- Right-step unfolding of `impactedClosureFuel`. -/
theorem impactedClosureFuel_succ_right
    (n : Nat) (deps : List (String × String)) (visited : List String) :
    impactedClosureFuel (n + 1) deps visited =
      impactStep deps (impactedClosureFuel n deps visited) := by
  induction n generalizing visited with
  | zero => rfl
  | succ m ih =>
    simp only [impactedClosureFuel]
    exact ih (impactStep deps visited)

/-- Every element in `visited` is retained by `impactedClosureFuel fuel deps visited`. -/
theorem subset_impactedClosureFuel
    (fuel : Nat) (deps : List (String × String)) (visited : List String) :
    ∀ x ∈ visited, x ∈ impactedClosureFuel fuel deps visited := by
  induction fuel generalizing visited with
  | zero => intro x hx; exact hx
  | succ n ih =>
    intro x hx
    exact ih (impactStep deps visited) x (subset_impactStep deps visited x hx)

/-- The modified root cell key `k` is always included in `impactedBacklinksFuel fuel deps k`. -/
theorem self_mem_impactedBacklinksFuel
    (fuel : Nat) (deps : List (String × String)) (k : String) :
    k ∈ impactedBacklinksFuel fuel deps k :=
  subset_impactedClosureFuel fuel deps [k] k (by simp)

/-- One additional unit of fuel monotonically grows `impactedBacklinksFuel`. -/
theorem impactedBacklinksFuel_step_subset
    (n : Nat) (deps : List (String × String)) (k : String) :
    ∀ x ∈ impactedBacklinksFuel n deps k, x ∈ impactedBacklinksFuel (n + 1) deps k := by
  intro x hx
  dsimp only [impactedBacklinksFuel] at hx ⊢
  rw [impactedClosureFuel_succ_right]
  exact subset_impactStep deps (impactedClosureFuel n deps [k]) x hx

/-- **Monotonicity of `impactedBacklinksFuel` (`impactedBacklinksFuel_mono`)**:
If `m ≤ n`, every cell in `impactedBacklinksFuel m deps k` is also in `impactedBacklinksFuel n deps k`. -/
theorem impactedBacklinksFuel_mono
    {m n : Nat} (hLe : m ≤ n) (deps : List (String × String)) (k : String) :
    ∀ x ∈ impactedBacklinksFuel m deps k, x ∈ impactedBacklinksFuel n deps k := by
  induction hLe with
  | refl => intro x hx; exact hx
  | @step b h ih =>
    intro x hx
    exact impactedBacklinksFuel_step_subset b deps k x (ih x hx)

/-- Inductive transitive `#^block` citation reachability from modified cell key `rootKey`. -/
inductive CiteReachable (deps : List (String × String)) (rootKey : String) : String → Prop
  | refl : CiteReachable deps rootKey rootKey
  | step {mid citing : String} :
      CiteReachable deps rootKey mid → (citing, mid) ∈ deps → CiteReachable deps rootKey citing

theorem impactStep_reachable_sound
    {deps : List (String × String)} {rootKey : String} {visited : List String}
    (hVis : ∀ x ∈ visited, CiteReachable deps rootKey x) :
    ∀ y ∈ impactStep deps visited, CiteReachable deps rootKey y := by
  intro y hy
  simp only [impactStep, List.mem_append, List.mem_filter, mem_dedupCellKeys,
    List.mem_flatMap, mem_directCiteDependents] at hy
  rcases hy with hInVis | ⟨⟨mid, hMid, hEdge⟩, _⟩
  · exact hVis y hInVis
  · exact .step (hVis mid hMid) hEdge

theorem impactedClosureFuel_reachable_sound
    (fuel : Nat) {deps : List (String × String)} {rootKey : String} {visited : List String}
    (hVis : ∀ x ∈ visited, CiteReachable deps rootKey x) :
    ∀ y ∈ impactedClosureFuel fuel deps visited, CiteReachable deps rootKey y := by
  induction fuel generalizing visited with
  | zero => exact hVis
  | succ n ih =>
    exact ih (impactStep_reachable_sound hVis)

/-- Every cell reported in `impactedBacklinksFuel fuel deps k` genuinely transitively cites `k`. -/
theorem impactedBacklinksFuel_reachable_sound
    (fuel : Nat) (deps : List (String × String)) (k : String) :
    ∀ x ∈ impactedBacklinksFuel fuel deps k, CiteReachable deps k x := by
  apply impactedClosureFuel_reachable_sound fuel
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact .refl

/-- Once `impactStep deps S = S` is a fixed point, further fuel iterations leave `S` unchanged. -/
theorem impactedClosureFuel_of_fixedPoint
    (d : Nat) {deps : List (String × String)} {S : List String}
    (hFix : impactStep deps S = S) :
    impactedClosureFuel d deps S = S := by
  induction d with
  | zero => rfl
  | succ n ih =>
    rw [impactedClosureFuel_succ_right, ih, hFix]

/-- **Fixed-Point Soundness of `impactedBacklinksFuel` (`impactedBacklinksFuel_fixedPoint_sound`)**:
When `impactedBacklinksFuel fuel deps k` reaches a fixed point (`impactStep deps S = S`, i.e.,
`impactedBacklinksFuel (fuel + 1) deps k = impactedBacklinksFuel fuel deps k`), the set
`S := impactedBacklinksFuel fuel deps k`:
1. Contains the modified root key `k` (`k ∈ S`),
2. Is closed under all `#^block` citation edges (`∀ citingCell citedBlock, (citingCell, citedBlock) ∈ deps → citedBlock ∈ S → citingCell ∈ S`), and
3. Remains invariant under any additional fuel `d` (`impactedBacklinksFuel (fuel + d) deps k = S`). -/
theorem impactedBacklinksFuel_fixedPoint_sound
    (fuel : Nat) (deps : List (String × String)) (k : String)
    (hFix : impactedBacklinksFuel (fuel + 1) deps k = impactedBacklinksFuel fuel deps k) :
    let S := impactedBacklinksFuel fuel deps k
    k ∈ S ∧
    (∀ citingCell citedBlock, (citingCell, citedBlock) ∈ deps → citedBlock ∈ S → citingCell ∈ S) ∧
    (∀ d, impactedBacklinksFuel (fuel + d) deps k = S) := by
  dsimp only
  have hStepEq : impactStep deps (impactedBacklinksFuel fuel deps k) = impactedBacklinksFuel fuel deps k := by
    have h1 := impactedClosureFuel_succ_right fuel deps [k]
    dsimp only [impactedBacklinksFuel] at hFix ⊢
    rw [← h1, hFix]
  refine ⟨self_mem_impactedBacklinksFuel fuel deps k, ?_, ?_⟩
  · intro citingCell citedBlock hEdge hCited
    have hInStep := step_contains_directCiteDependent hEdge hCited
    rwa [hStepEq] at hInStep
  · intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      have hAdd : fuel + (d + 1) = (fuel + d) + 1 := by omega
      dsimp only [impactedBacklinksFuel] at ih ⊢
      rw [hAdd, impactedClosureFuel_succ_right, ih]
      exact hStepEq

/-- **Fixed-Point Soundness & Completeness Equivalence (`impactedBacklinksFuel_fixedPoint_iff_reachable`)**:
At a fixed point (`impactedBacklinksFuel (fuel + 1) deps k = impactedBacklinksFuel fuel deps k`),
a cell `x` is in `impactedBacklinksFuel fuel deps k` if and only if `CiteReachable deps k x`. -/
theorem impactedBacklinksFuel_fixedPoint_iff_reachable
    (fuel : Nat) (deps : List (String × String)) (k : String)
    (hFix : impactedBacklinksFuel (fuel + 1) deps k = impactedBacklinksFuel fuel deps k)
    (x : String) :
    x ∈ impactedBacklinksFuel fuel deps k ↔ CiteReachable deps k x := by
  obtain ⟨hRoot, hClosed, _⟩ := impactedBacklinksFuel_fixedPoint_sound fuel deps k hFix
  constructor
  · exact impactedBacklinksFuel_reachable_sound fuel deps k x
  · intro hReach
    induction hReach with
    | refl => exact hRoot
    | step _ hEdge ih => exact hClosed _ _ hEdge ih

end Obend.Doc

end

