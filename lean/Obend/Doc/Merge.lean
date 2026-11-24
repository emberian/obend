module
/-
# Obend.Doc.Merge — merge is a pushout; a conflict is an object

Mimram and Di Giusto, *A Categorical Theory of Patches* (2013): files are objects, patches are
morphisms, the merge of two patches from a common file is their PUSHOUT. In the category `L` of
files (lines totally ordered) not every span has one (their diagram (3): `a c b ← a b → a d b`);
they pass to the free finite conservative cocompletion `P`, whose objects (their Theorem 20) are
finite sets of labelled lines under a transitive relation, and where a conflict is an object: lines
the relation leaves unordered.

The representation here (breadstuffs `dregg-doc`, Pijul's) is that cocompletion made concrete with
STABLE IDENTITIES: an atom is named once and for all, so the patch-morphism from `G` to `H` is
determined by the names and exists iff `G ⊑ H` (`Le`): every atom of `G` is in `H` with the same
content, every tombstone of `G` is one in `H`, every edge of `G` is one in `H`. Hom-sets are
subsingletons, the category is the preorder `Le`, and a pushout of `A ← G → B` is a least upper
bound of `A` and `B`: the square commutes because the category is thin, and the mediating arrow is
unique for the same reason. What is proved, not asserted:

* `le_apply`: an authored patch is a morphism from the page it acts on.
* `merge_isPushout`: the union of two compatible pages is their pushout, with the universal
  property; `pushout_unique`: any two pushouts are the same page; `empty_le`: the empty page is
  initial. So the category has an initial object and a pushout of every span of compatible pages:
  it is finitely cocomplete there.
* `no_cocone`: two pages that store different contents at one identity have no cocone at all.
  Compatibility is the identity discipline, not a gap: content-addressed identities give it
  (`compatible_of_addressed`), and that is what the Rust assumes of `AtomId::derive`.
* `File`: the plain category `L` is the full subcategory of pages whose live runs are totally and
  strictly ordered. `Teeth.files_no_pushout`: diagram (3) has no pushout among files, while its
  merge is the pushout among pages and carries the antichain `{c, d}` of live alternatives
  (`Teeth.merge_antichain`); `file_pushout`: when the merge is a file, it is the pushout among files.

The linearization `content` (the Rust `content::content`) folds a page into runs and conflict
regions: walking from `root` through tombstones, a position with one minimal live successor
continues, a position with two or more mutually unordered ones is a `conflict` whose alternatives
are those `heads` (`walk_conflict`), each with its branch, and the walk resumes where the branches
rejoin.
-/
public import Obend.Doc.Patch
import all Obend.Doc.Graph
import all Obend.Doc.Patch
public section

namespace Obend.Doc

set_option autoImplicit false

namespace Graph

/-! ## The morphisms -/

/-- `G ⊑ H`: the patch-morphism from `G` to `H` exists. -/
def Le (G H : Graph) : Prop :=
  (∀ a c, G.label a = some c → H.label a = some c) ∧
  (∀ a, G.isDead a = true → H.isDead a = true) ∧
  (∀ a b, G.edge a b = true → H.edge a b = true)

theorem Le.refl (G : Graph) : G.Le G := ⟨fun _ _ h => h, fun _ h => h, fun _ _ h => h⟩

theorem Le.trans {G H K : Graph} (h : G.Le H) (k : H.Le K) : G.Le K :=
  ⟨fun a c x => k.1 a c (h.1 a c x), fun a x => k.2.1 a (h.2.1 a x),
    fun a b x => k.2.2 a b (h.2.2 a b x)⟩

/-- Morphisms both ways are an isomorphism, and an isomorphism is the same page. -/
theorem Le.antisymm {G H : Graph} (h : G.Le H) (k : H.Le G) : G.Same H := by
  refine ⟨funext fun a => ?_, funext fun a => ?_, funext fun a => funext fun b => ?_⟩
  · cases hg : G.label a with
    | some c => exact (h.1 a c hg).symm
    | none => cases hh : H.label a with
      | none => rfl
      | some c => rw [k.1 a c hh] at hg; cases hg
  · cases hg : G.isDead a <;> cases hh : H.isDead a <;> first
      | rfl
      | (have := h.2.1 a hg; simp_all)
      | (have := k.2.1 a hh; simp_all)
  · cases hg : G.edge a b <;> cases hh : H.edge a b <;> first
      | rfl
      | (have := h.2.2 a b hg; simp_all)
      | (have := k.2.2 a b hh; simp_all)

theorem Same.le {G H : Graph} (h : G.Same H) : G.Le H :=
  ⟨fun _ _ x => h.1 ▸ x, fun _ x => h.2.1 ▸ x, fun _ _ x => h.2.2 ▸ x⟩

/-- The empty page is initial. -/
theorem empty_le (G : Graph) : empty.Le G :=
  ⟨fun _ _ h => by simp [empty, label] at h,
    fun _ h => by simp [empty, isDead] at h, fun _ _ h => by simp [empty, edge] at h⟩

/-- An authored operation is a morphism from the page it acts on. -/
theorem le_step {G : Graph} {o : Op} (h : o.forward = true) : G.Le (G.step o) := by
  refine ⟨fun _ _ x => ?_, fun _ x => ?_, fun _ _ x => ?_⟩ <;>
    cases o <;> simp_all [Op.forward]

/-- **An authored patch is a morphism** from the page it acts on. -/
theorem le_apply {G : Graph} {p : Patch} (h : Patch.forward p = true) : G.Le (G.apply p) := by
  induction p generalizing G with
  | nil => exact Le.refl G
  | cons o p ih =>
    simp only [Patch.forward, List.all_cons, Bool.and_eq_true] at h
    exact (le_step h.1).trans (ih (by simpa [Patch.forward] using h.2))

/-- Morphisms carry the order. -/
theorem Le.before {G H : Graph} (h : G.Le H) {a b : AtomId} (hb : G.Before a b) : H.Before a b := by
  induction hb with
  | edge e => exact .edge (h.2.2 _ _ e)
  | trans e _ ih => exact .trans (h.2.2 _ _ e) ih

/-! ## The pushout -/

/-- The union of two pages: every atom, tombstone and edge of either. -/
@[expose] def merge (A B : Graph) : Graph :=
  { atoms := A.atoms ++ B.atoms, dead := A.dead ++ B.dead, edges := A.edges ++ B.edges }

theorem lookup_append (l m : List (AtomId × Content)) (a : AtomId) :
    (l ++ m).lookup a = (l.lookup a).or (m.lookup a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    by_cases h : a = k
    · subst h; simp [List.lookup]
    · rw [List.cons_append, lookup_cons_ne _ _ h, lookup_cons_ne _ _ h, ih]

@[simp] theorem label_merge (A B : Graph) (a : AtomId) :
    (merge A B).label a = (A.label a).or (B.label a) := lookup_append ..
@[simp] theorem isDead_merge (A B : Graph) (a : AtomId) :
    (merge A B).isDead a = (A.isDead a || B.isDead a) := by simp [merge, isDead]
@[simp] theorem edge_merge (A B : Graph) (a b : AtomId) :
    (merge A B).edge a b = (A.edge a b || B.edge a b) := by simp [merge, edge]

/-- Two pages agree on the content of every identity both store. -/
def Compatible (A B : Graph) : Prop :=
  ∀ a c c', A.label a = some c → B.label a = some c' → c = c'

/-- `P` is a pushout of `A` and `B` (over any common page they both extend: in a thin category the
square commutes and the mediating arrow is unique, so the base does not enter). -/
structure IsPushout (A B P : Graph) : Prop where
  left : A.Le P
  right : B.Le P
  univ : ∀ Q, A.Le Q → B.Le Q → P.Le Q

theorem le_merge_left (A B : Graph) : A.Le (merge A B) :=
  ⟨fun a c h => by simp [h], fun a h => by simp [h], fun a b h => by simp [h]⟩

theorem le_merge_right {A B : Graph} (hc : Compatible A B) : B.Le (merge A B) := by
  refine ⟨fun a c h => ?_, fun a h => by simp [h], fun a b h => by simp [h]⟩
  rw [label_merge]
  cases ha : A.label a with
  | none => simpa using h
  | some c' => rw [hc a c' c ha h]; rfl

theorem merge_le {A B Q : Graph} (hA : A.Le Q) (hB : B.Le Q) : (merge A B).Le Q := by
  refine ⟨fun a c h => ?_, fun a h => ?_, fun a b h => ?_⟩
  · rw [label_merge] at h
    cases ha : A.label a with
    | some c' => rw [ha] at h; cases h; exact hA.1 a _ ha
    | none => rw [ha] at h; exact hB.1 a c (by simpa using h)
  · rw [isDead_merge, Bool.or_eq_true] at h
    exact h.elim (hA.2.1 a) (hB.2.1 a)
  · rw [edge_merge, Bool.or_eq_true] at h
    exact h.elim (hA.2.2 a b) (hB.2.2 a b)

/-- **The merge is the pushout.** The union of two compatible pages is above both, and below every
page above both. -/
theorem merge_isPushout {A B : Graph} (hc : Compatible A B) : IsPushout A B (merge A B) :=
  ⟨le_merge_left A B, le_merge_right hc, fun _ hA hB => merge_le hA hB⟩

/-- Two pushouts of one span are the same page. -/
theorem pushout_unique {A B P P' : Graph} (h : IsPushout A B P) (h' : IsPushout A B P') :
    P.Same P' :=
  Le.antisymm (h.univ P' h'.left h'.right) (h'.univ P h.left h.right)

/-- **No cocone without compatibility.** Pages that store different contents at one identity are
below no common page; so they have no pushout, in this category or in any full subcategory of it. -/
theorem no_cocone {A B : Graph} (h : ¬ Compatible A B) : ¬ ∃ Q, A.Le Q ∧ B.Le Q := by
  rintro ⟨Q, hA, hB⟩
  apply h
  intro a c c' ha hb
  have h1 := hA.1 a c ha
  rw [hB.1 a c' hb] at h1
  cases h1; rfl

/-- Every identity a page stores carries the content `σ` assigns it: identities are content
addresses. -/
def Addressed (σ : AtomId → Content) (G : Graph) : Prop := ∀ a c, G.label a = some c → c = σ a

theorem compatible_of_addressed {σ : AtomId → Content} {A B : Graph} (hA : Addressed σ A)
    (hB : Addressed σ B) : Compatible A B :=
  fun a c c' ha hb => (hA a c ha).trans (hB a c' hb).symm

/-- **The merge of two authored patches from one page** is their pushout, under content-addressed
identities. -/
theorem merge_patches {σ : AtomId → Content} {G : Graph} {p q : Patch}
    (hp : Patch.forward p = true) (hq : Patch.forward q = true)
    (hA : Addressed σ (G.apply p)) (hB : Addressed σ (G.apply q)) :
    G.Le (G.apply p) ∧ G.Le (G.apply q) ∧
      IsPushout (G.apply p) (G.apply q) (merge (G.apply p) (G.apply q)) :=
  ⟨le_apply hp, le_apply hq, merge_isPushout (compatible_of_addressed hA hB)⟩

theorem compatible_symm {A B : Graph} (h : Compatible A B) : Compatible B A :=
  fun a c c' ha hb => (h a c' c hb ha).symm

/-- Merge is commutative and idempotent, as pages. -/
theorem merge_comm {A B : Graph} (hc : Compatible A B) : (merge A B).Same (merge B A) :=
  pushout_unique (merge_isPushout hc)
    ⟨le_merge_right (compatible_symm hc), le_merge_left B A, fun _ hA hB => merge_le hB hA⟩

theorem merge_self (A : Graph) : (merge A A).Same A :=
  Le.antisymm (merge_le (Le.refl A) (Le.refl A)) (le_merge_left A A)

/-- A decided sufficient check of compatibility. -/
def compatB (A B : Graph) : Bool :=
  A.atoms.all fun e => match B.label e.1 with
    | some c' => e.2 == c'
    | none => true

theorem lookup_mem {l : List (AtomId × Content)} {a : AtomId} {c : Content}
    (h : l.lookup a = some c) : (a, c) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : a = k
    · subst hk; simp [List.lookup] at h; subst h; exact List.mem_cons_self
    · rw [lookup_cons_ne _ _ hk] at h; exact List.mem_cons_of_mem _ (ih h)

theorem compatible_of_compatB {A B : Graph} (h : compatB A B = true) : Compatible A B := by
  intro a c c' ha hb
  have hm := lookup_mem ha
  simp only [compatB, List.all_eq_true] at h
  have := h _ hm
  simp only [label] at hb
  simp only [label, hb, beq_iff_eq] at this
  exact this

/-! ## The plain category: files -/

/-- A live atom of the order (a run or a cite, not a field assignment). -/
@[expose] def run (G : Graph) (a : AtomId) : Bool :=
  G.alive a && match G.label a with
    | some (.field ..) => false
    | _ => true

/-- A FILE: its live runs are totally and strictly ordered (the objects of `L`). -/
def File (G : Graph) : Prop :=
  (∀ a b, G.run a = true → G.run b = true → a ≠ b → G.Before a b ∨ G.Before b a) ∧
  (∀ a, G.run a = true → ¬ G.Before a a)

/-- `P` is a pushout of `A` and `B` among the pages satisfying `C`. -/
def IsPushoutIn (C : Graph → Prop) (A B P : Graph) : Prop :=
  C P ∧ A.Le P ∧ B.Le P ∧ ∀ Q, C Q → A.Le Q → B.Le Q → P.Le Q

/-- The pushout among pages is the pushout among files whenever it is a file: the inclusion of
files preserves the pushouts files have. -/
theorem file_pushout {A B : Graph} (hc : Compatible A B) (hf : File (merge A B)) :
    IsPushoutIn File A B (merge A B) :=
  ⟨hf, le_merge_left A B, le_merge_right hc, fun _ _ hA hB => merge_le hA hB⟩

/-- The identities a page stores whose atom is a live run. -/
@[expose] def runs (G : Graph) : List AtomId := (G.atoms.map Prod.fst).filter G.run

theorem mem_runs {G : Graph} {a : AtomId} (h : G.run a = true) : a ∈ G.runs := by
  simp only [runs, List.mem_filter, List.mem_map]
  refine ⟨?_, h⟩
  simp only [run, alive, present, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨c, hc⟩, _⟩, _⟩ := h
  exact ⟨(a, c), lookup_mem hc, rfl⟩

/-- A decided check that a page is a file, with its order certified closed. -/
def fileB (G : Graph) : Bool :=
  G.runs.all fun a => G.Closed (G.cone a) && !G.beforeB a a &&
    G.runs.all fun b => a == b || G.beforeB a b || G.beforeB b a

theorem file_of_fileB {G : Graph} (h : G.fileB = true) : File G := by
  simp only [fileB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  refine ⟨fun a b ha hb hne => ?_, fun a ha => ?_⟩
  · obtain ⟨_, hall⟩ := h a (mem_runs ha)
    rcases hall b (mem_runs hb) with (h1 | h1) | h1
    · exact absurd h1 hne
    · exact .inl (beforeB_sound h1)
    · exact .inr (beforeB_sound h1)
  · obtain ⟨⟨hc, hn⟩, _⟩ := h a (mem_runs ha)
    exact not_before_of_closed hc hn

/-! ## The linearization -/

/-- Remove repeats, keeping first occurrences. -/
def dedup (l : List AtomId) : List AtomId :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The atoms met walking forward from `x` until a live run: the dead (or absent) ones crossed, and
the live runs where each path stops. -/
def frontN (G : Graph) : Nat → AtomId → List AtomId
  | 0, _ => []
  | n + 1, x => (G.succs x).flatMap fun y => if G.run y then [y] else y :: G.frontN n y

/-- The frontier of `x`. -/
@[expose] def front (G : Graph) (x : AtomId) : List AtomId := dedup (G.frontN (G.edges.length + 1) x)

/-- `y` is not preceded by another live run of the frontier of `x`. -/
@[expose] def isHead (G : Graph) (x y : AtomId) : Bool :=
  !((G.front x).filter G.run).any fun z => z != y && G.beforeB z y

/-- The minimal live runs after `x`. Two or more is a conflict at `x`. -/
@[expose] def heads (G : Graph) (x : AtomId) : List AtomId :=
  (G.front x).filter fun y => G.run y && G.isHead x y

/-- The live assignments to a field. Two or more is a field conflict. -/
def fieldValues (G : Graph) (name : String) : List (AtomId × String) :=
  G.atoms.filterMap fun e => match e.2 with
    | .field n v => if n = name && G.alive e.1 then some (e.1, v) else none
    | _ => none

/-- A page folded into order: a live run, or a conflict whose alternatives are its heads, each
with its branch. -/
inductive Segment
  | run (a : AtomId)
  | conflict (alts : List (AtomId × List Segment))
deriving Repr

/-- Walk from `x`, ignoring the atoms `stop` excludes (inside a branch: what another alternative
reaches). -/
def walk (G : Graph) : Nat → (AtomId → Bool) → AtomId → List Segment
  | 0, _, _ => []
  | n + 1, stop, x =>
    match (G.heads x).filter (fun y => !stop y) with
    | [] => []
    | [y] => .run y :: G.walk n stop y
    | hs =>
      let other (h z : AtomId) : Bool := hs.any fun h' => h' != h && (h' == z || G.beforeB h' z)
      let alts := hs.map fun h => (h, .run h :: G.walk n (fun z => stop z || other h z) h)
      let after := (G.runs).filter fun z => !stop z && hs.all fun h => G.beforeB h z
      let rejoin := dedup (after.filter fun z => !after.any fun w => w != z && G.beforeB w z)
      match rejoin with
      | [r] => .conflict alts :: .run r :: G.walk n stop r
      | _ => [.conflict alts]

/-- The page's content: its walk from `root`. -/
@[expose] def content (G : Graph) : List Segment := G.walk (G.atoms.length + 1) (fun _ => false) root

/-- **A conflict is where the walk meets two or more heads**, and its alternatives are exactly
those heads. -/
theorem walk_conflict (G : Graph) (n : Nat) (x : AtomId) (h1 h2 : AtomId) (t : List AtomId)
    (h : G.heads x = h1 :: h2 :: t) :
    ∃ alts rest, G.walk (n + 1) (fun _ => false) x = .conflict alts :: rest ∧
      alts.map Prod.fst = h1 :: h2 :: t := by
  have hf : (G.heads x).filter (fun y => !(fun _ => false) y) = h1 :: h2 :: t := by
    rw [h]; simp
  simp only [walk, hf]
  split <;> exact ⟨_, _, rfl, by simp [Function.comp_def]⟩

end Graph

/-! ## Teeth: Mimram–Di Giusto's diagram (3) -/

namespace Teeth
open Graph

/-- The file `a b`. -/
def ab : Graph := empty.apply [.add 1 (.text "a") root, .add 2 (.text "b") 1]
/-- `a c b`: insert `c` between them. -/
def acb : Graph := ab.apply [.add 3 (.text "c") 1, .connect 3 2]
/-- `a d b`: insert `d` between them. -/
def adb : Graph := ab.apply [.add 4 (.text "d") 1, .connect 4 2]
/-- The merge: `c` and `d` both between `a` and `b`, unordered. -/
def merged : Graph := merge acb adb

theorem compat : Compatible acb adb := compatible_of_compatB (by decide)

example : File ab ∧ File acb ∧ File adb :=
  ⟨file_of_fileB (by decide), file_of_fileB (by decide), file_of_fileB (by decide)⟩

/-- The merge is the pushout among pages, and it is a conflict: `c` and `d` are live and unordered,
so it is not a file. -/
theorem merge_antichain :
    IsPushout acb adb merged ∧ merged.run 3 = true ∧ merged.run 4 = true ∧
      ¬ merged.Before 3 4 ∧ ¬ merged.Before 4 3 ∧ ¬ File merged := by
  have n34 : ¬ merged.Before 3 4 := not_before_of_closed (by decide) (by decide)
  have n43 : ¬ merged.Before 4 3 := not_before_of_closed (by decide) (by decide)
  refine ⟨merge_isPushout compat, by decide, by decide, n34, n43, fun hf => ?_⟩
  rcases hf.1 3 4 (by decide) (by decide) (by decide) with h | h
  · exact n34 h
  · exact n43 h

/-- The conflict is what the walk shows: at `a`, the heads are `c` and `d`. -/
example : merged.heads 1 = [3, 4] := by decide

/-- **Diagram (3) has no pushout among files.** Any file above both `a c b` and `a d b` orders `c`
and `d`; ordering them one way it is not below the file that orders them the other way. -/
theorem files_no_pushout : ¬ ∃ P, IsPushoutIn File acb adb P := by
  rintro ⟨P, hP, hA, hB, hU⟩
  let Q1 := merged.apply [.connect 3 4]
  let Q2 := merged.apply [.connect 4 3]
  have m1 : merged.Le Q1 := le_apply rfl
  have m2 : merged.Le Q2 := le_apply rfl
  have f1 : File Q1 := file_of_fileB (by decide)
  have f2 : File Q2 := file_of_fileB (by decide)
  have u1 := hU Q1 f1 ((le_merge_left _ _).trans m1) ((le_merge_right compat).trans m1)
  have u2 := hU Q2 f2 ((le_merge_left _ _).trans m2) ((le_merge_right compat).trans m2)
  -- `c` and `d` are live runs of `P`: stored there by `acb`, `adb`, and not dead, since `Q1` is above.
  have live : ∀ a, Q1.isDead a = false → P.isDead a = false := fun a h => by
    cases hp : P.isDead a
    · rfl
    · rw [u1.2.1 a hp] at h; cases h
  have lab3 : P.label 3 = some (.text "c") := hA.1 3 _ (by decide)
  have lab4 : P.label 4 = some (.text "d") := hB.1 4 _ (by decide)
  have r3 : P.run 3 = true := by simp [run, alive, present, lab3, live 3 (by decide)]
  have r4 : P.run 4 = true := by simp [run, alive, present, lab4, live 4 (by decide)]
  have n1 : ¬ Q1.Before 4 3 := not_before_of_closed (by decide) (by decide)
  have n2 : ¬ Q2.Before 3 4 := not_before_of_closed (by decide) (by decide)
  rcases hP.1 3 4 r3 r4 (by decide) with h | h
  · exact n2 (u2.before h)
  · exact n1 (u1.before h)

/-- Ordering the conflict (`Connect`) resolves it: one head. -/
example : (merged.apply [.connect 3 4]).heads 1 = [3] := by decide

/-- Deleting one alternative resolves it too, and the walk goes through the tombstone. -/
example : (merged.apply [.delete 4]).heads 1 = [3] := by decide

end Teeth

/-! ## 3-Way Keyed Section/Cell LCA Merge & Conflict Localization -/

/-- Outcome of merging a single cell/field value `vL` and `vR` over a common ancestor `base`. -/
inductive MergeCellResult (α : Type) where
  | merged (val : α)
  | conflict (baseVal leftVal rightVal : α)
  deriving DecidableEq, Repr

/-- Structured 3-way merge conflict localized to a specific cell/block key `key`. -/
structure MergeConflict where
  key : String
  baseVal : Option Obend.Core.Data.Data
  leftVal : Option Obend.Core.Data.Data
  rightVal : Option Obend.Core.Data.Data
  deriving DecidableEq, Repr

/-- Outcome of a 3-way keyed cell/section LCA merge across a document's cells:
carries the merged `(key, Data)` association list and the list of localized `MergeConflict`s. -/
structure KeyedMergeOutcome where
  mergedCells : List (String × Obend.Core.Data.Data)
  conflicts : List MergeConflict
  deriving DecidableEq, Repr

/-- **3-Way Single-Cell LCA Merge (`mergeCell3`)**:
Given a common ancestor value `base` and two concurrent agent branch values `vL` and `vR`:
- If `vL = vR` (both kept `base`, or both converged idempotently to the same new value), returns `.merged vL`.
- If only the right branch changed (`vL = base`), returns `.merged vR`.
- If only the left branch changed (`vR = base`), returns `.merged vL`.
- If both branches changed to distinct values (`vL ≠ vR`, `vL ≠ base`, `vR ≠ base`), returns
  `.conflict base vL vR`. -/
@[expose] def mergeCell3 {α : Type} [DecidableEq α] (base vL vR : α) : MergeCellResult α :=
  if vL = vR then
    .merged vL
  else if vL = base then
    .merged vR
  else if vR = base then
    .merged vL
  else
    .conflict base vL vR

/-- **Idempotence (`mergeCell3_idempotent`)**: merging two identical branches `(base, a, a)` always
succeeds with `.merged a` (`0` conflicts). -/
@[simp] theorem mergeCell3_idempotent {α : Type} [DecidableEq α] (base a : α) :
    mergeCell3 base a a = .merged a := by
  simp [mergeCell3]

/-- If the left branch is unchanged (`vL = base`), `mergeCell3` cleanly adopts the right branch `vR`. -/
@[simp] theorem mergeCell3_left_unchanged {α : Type} [DecidableEq α] (base vR : α) :
    mergeCell3 base base vR = .merged vR := by
  by_cases h : base = vR <;> simp [mergeCell3, h]

/-- If the right branch is unchanged (`vR = base`), `mergeCell3` cleanly adopts the left branch `vL`. -/
@[simp] theorem mergeCell3_right_unchanged {α : Type} [DecidableEq α] (base vL : α) :
    mergeCell3 base vL base = .merged vL := by
  by_cases h : vL = base <;> simp [mergeCell3, h]

/-- Characterization of when `mergeCell3` reports a conflict. -/
theorem mergeCell3_conflict_iff {α : Type} [DecidableEq α] (base vL vR : α) :
    mergeCell3 base vL vR = .conflict base vL vR ↔
      vL ≠ vR ∧ vL ≠ base ∧ vR ≠ base := by
  unfold mergeCell3
  by_cases hLR : vL = vR
  · subst hLR; simp
  · by_cases hLB : vL = base
    · subst hLB; simp [hLR]
    · by_cases hRB : vR = base
      · subst hRB; simp [hLR, hLB]
      · simp [hLR, hLB, hRB]

/-- **Commutativity (`mergeCell3_commutative`)**:
`mergeCell3 base vL vR` is symmetric:
1. `mergeCell3 base vL vR = .merged v ↔ mergeCell3 base vR vL = .merged v` for all `v`, and
2. `mergeCell3 base vL vR = .conflict base vL vR ↔ mergeCell3 base vR vL = .conflict base vR vL`. -/
theorem mergeCell3_commutative {α : Type} [DecidableEq α] (base vL vR : α) :
    (∀ v, mergeCell3 base vL vR = .merged v ↔ mergeCell3 base vR vL = .merged v) ∧
    (mergeCell3 base vL vR = .conflict base vL vR ↔
      mergeCell3 base vR vL = .conflict base vR vL) := by
  refine ⟨fun v => ?_, ?_⟩
  · unfold mergeCell3
    by_cases hLR : vL = vR
    · subst hLR; simp
    · have hRL : vR ≠ vL := Ne.symm hLR
      by_cases hLB : vL = base
      · subst hLB; simp [hLR, hRL]
      · by_cases hRB : vR = base
        · subst hRB; simp [hLR, hRL, hLB]
        · simp [hLR, hRL, hLB, hRB]
  · rw [mergeCell3_conflict_iff, mergeCell3_conflict_iff]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨Ne.symm h1, h3, h2⟩,
      fun ⟨h1, h2, h3⟩ => ⟨Ne.symm h1, h3, h2⟩⟩

/-- **Disjoint Edits Succeed (`mergeCell3_disjoint_edits_succeed`)**:
If Agent A modifies cell `k1` (`vR = base1` at `k1`) and Agent B modifies cell `k2` (`vL = base2` at `k2`),
both cells merge cleanly without conflict! -/
theorem mergeCell3_disjoint_edits_succeed {α : Type} [DecidableEq α]
    (base1 base2 vL1 vR2 : α) :
    mergeCell3 base1 vL1 base1 = .merged vL1 ∧
    mergeCell3 base2 base2 vR2 = .merged vR2 :=
  ⟨mergeCell3_right_unchanged base1 vL1, mergeCell3_left_unchanged base2 vR2⟩

/-- Collect all distinct cell keys present across `base`, `left`, and `right` in order of appearance. -/
def collectCellKeys
    (base left right : List (String × Obend.Core.Data.Data)) : List String :=
  Patch.dedupStringKeys ((base.map Prod.fst) ++ (left.map Prod.fst) ++ (right.map Prod.fst))

@[simp] theorem mem_collectCellKeys
    {base left right : List (String × Obend.Core.Data.Data)} {k : String} :
    k ∈ collectCellKeys base left right ↔
      k ∈ base.map Prod.fst ∨ k ∈ left.map Prod.fst ∨ k ∈ right.map Prod.fst := by
  simp [collectCellKeys, List.mem_append]

/-- Perform a 3-way LCA cell merge at key `k` across keyed cell states `base`, `left`, and `right`. -/
def mergeKeyedCellAt
    (base left right : List (String × Obend.Core.Data.Data)) (k : String) :
    MergeCellResult (Option Obend.Core.Data.Data) :=
  mergeCell3 (base.lookup k) (left.lookup k) (right.lookup k)

theorem mergeKeyedCellAt_of_not_mem_collectCellKeys
    {base left right : List (String × Obend.Core.Data.Data)} {k : String}
    (hNotMem : k ∉ collectCellKeys base left right) :
    mergeKeyedCellAt base left right k = .merged none := by
  rw [mem_collectCellKeys, not_or, not_or] at hNotMem
  obtain ⟨hB, hL, hR⟩ := hNotMem
  simp [mergeKeyedCellAt,
    Patch.lookup_eq_none_of_not_mem_map_fst hB,
    Patch.lookup_eq_none_of_not_mem_map_fst hL,
    Patch.lookup_eq_none_of_not_mem_map_fst hR]

/-- Extract the merged `Option Data` value at key `k` when `mergeKeyedCellAt` succeeds with `some v`. -/
def mergedCellValueAt
    (base left right : List (String × Obend.Core.Data.Data)) (k : String) :
    Option Obend.Core.Data.Data :=
  match mergeKeyedCellAt base left right k with
  | .merged (some v) => some v
  | .merged none => none
  | .conflict _ _ _ => none

/-- **3-Way Keyed Section/Cell LCA Merge (`mergeKeyedCells3`)**:
Given a common ancestor document state `base : List (String × Data)` and two concurrent agent
branches `left right : List (String × Data)`, merges each cell key `k` via `mergeKeyedCellAt`
and partitions the results into `mergedCells` and structured `MergeConflict`s. -/
@[expose] def mergeKeyedCells3
    (base left right : List (String × Obend.Core.Data.Data)) : KeyedMergeOutcome :=
  let keys := collectCellKeys base left right
  let mergedCells := keys.filterMap fun k =>
    (mergedCellValueAt base left right k).map fun v => (k, v)
  let conflicts := keys.filterMap fun k =>
    match mergeKeyedCellAt base left right k with
    | .merged _ => none
    | .conflict b l r => some ⟨k, b, l, r⟩
  { mergedCells := mergedCells, conflicts := conflicts }

theorem lookup_filterMap_keyed {β : Type} (ks : List String) (f : String → Option β) (q : String) :
    (ks.filterMap fun k => (f k).map fun v => (k, v)).lookup q =
      if q ∈ ks then f q else none := by
  induction ks with
  | nil => simp
  | cons k rest ih =>
    by_cases hEq : q = k
    · subst hEq
      cases hfq : f q with
      | none =>
        simp only [List.filterMap_cons, hfq, Option.map_none, ih, List.mem_cons, true_or, ↓reduceIte]
        split <;> rfl
      | some v =>
        simp [hfq]
    · have hBne : (q == k) = false := beq_eq_false_iff_ne.2 hEq
      cases hfk : f k with
      | none =>
        simp [hfk, ih, hEq]
      | some v =>
        simp [hfk, List.lookup, hBne, ih, hEq]

/-- **Exact Lookup Characterization of `mergedCells` (`lookup_mergedCells_mergeKeyedCells3`)**:
For every key `k`, looking up `k` in `(mergeKeyedCells3 base left right).mergedCells` returns
`some v` iff `mergeKeyedCellAt base left right k = .merged (some v)`, and `none` otherwise. -/
theorem lookup_mergedCells_mergeKeyedCells3
    (base left right : List (String × Obend.Core.Data.Data)) (k : String) :
    ((mergeKeyedCells3 base left right).mergedCells).lookup k =
      mergedCellValueAt base left right k := by
  simp only [mergeKeyedCells3, lookup_filterMap_keyed]
  by_cases hMem : k ∈ collectCellKeys base left right
  · simp [hMem]
  · simp [hMem, mergedCellValueAt, mergeKeyedCellAt_of_not_mem_collectCellKeys hMem]

/-- **Exact Conflict Localization Characterization (`mem_conflicts_mergeKeyedCells3`)**:
A conflict record `c` belongs to `(mergeKeyedCells3 base left right).conflicts` iff
`mergeKeyedCellAt base left right c.key = .conflict c.baseVal c.leftVal c.rightVal`. -/
theorem mem_conflicts_mergeKeyedCells3
    (base left right : List (String × Obend.Core.Data.Data)) (c : MergeConflict) :
    c ∈ (mergeKeyedCells3 base left right).conflicts ↔
      mergeKeyedCellAt base left right c.key = .conflict c.baseVal c.leftVal c.rightVal ∧
      c.baseVal = base.lookup c.key ∧
      c.leftVal = left.lookup c.key ∧
      c.rightVal = right.lookup c.key := by
  simp only [mergeKeyedCells3, List.mem_filterMap]
  constructor
  · rintro ⟨k, _, hMatch⟩
    cases hRes : mergeKeyedCellAt base left right k with
    | merged _ => simp [hRes] at hMatch
    | conflict b l r =>
      simp only [hRes, Option.some.injEq] at hMatch
      subst hMatch
      have hAt : mergeCell3 (base.lookup k) (left.lookup k) (right.lookup k) = .conflict b l r := hRes
      unfold mergeCell3 at hAt
      split at hAt <;> try cases hAt
      split at hAt <;> try cases hAt
      split at hAt <;> try cases hAt
      exact ⟨hRes, rfl, rfl, rfl⟩
  · rintro ⟨hConf, _, _, _⟩
    refine ⟨c.key, ?_, ?_⟩
    · exact Classical.byContradiction fun hNotMem => by
        rw [mergeKeyedCellAt_of_not_mem_collectCellKeys hNotMem] at hConf
        cases hConf
    · cases c
      simp [hConf]

/-- Merging two identical keyed cell branches `(base, a, a)` always produces zero conflicts. -/
@[simp] theorem mergeKeyedCells3_idempotent_no_conflicts
    (base a : List (String × Obend.Core.Data.Data)) :
    (mergeKeyedCells3 base a a).conflicts = [] := by
  simp [mergeKeyedCells3, mergeKeyedCellAt]

/-- **Keyed Document Idempotence (`mergeKeyedCells3_idempotent`)**:
Merging two identical branches `(base, a, a)` produces zero conflicts and recovers `a.lookup k`
at every cell key `k`. -/
theorem mergeKeyedCells3_idempotent
    (base a : List (String × Obend.Core.Data.Data)) :
    (mergeKeyedCells3 base a a).conflicts = [] ∧
    ∀ k, ((mergeKeyedCells3 base a a).mergedCells).lookup k = a.lookup k := by
  refine ⟨mergeKeyedCells3_idempotent_no_conflicts base a, fun k => ?_⟩
  rw [lookup_mergedCells_mergeKeyedCells3]
  simp only [mergedCellValueAt, mergeKeyedCellAt, mergeCell3_idempotent]
  cases a.lookup k <;> rfl

/-- **Keyed Document Commutativity (`mergeKeyedCells3_commutative`)**:
1. Every key `k` resolves to the exact same merged cell value in `mergeKeyedCells3 base left right`
   and `mergeKeyedCells3 base right left`, and
2. `⟨k, b, l, r⟩ ∈ (mergeKeyedCells3 base left right).conflicts` iff
   `⟨k, b, r, l⟩ ∈ (mergeKeyedCells3 base right left).conflicts`. -/
theorem mergeKeyedCells3_commutative
    (base left right : List (String × Obend.Core.Data.Data)) :
    (∀ k, ((mergeKeyedCells3 base left right).mergedCells).lookup k =
          ((mergeKeyedCells3 base right left).mergedCells).lookup k) ∧
    (∀ k b l r,
      (⟨k, b, l, r⟩ : MergeConflict) ∈ (mergeKeyedCells3 base left right).conflicts ↔
      (⟨k, b, r, l⟩ : MergeConflict) ∈ (mergeKeyedCells3 base right left).conflicts) := by
  refine ⟨fun k => ?_, fun k b l r => ?_⟩
  · rw [lookup_mergedCells_mergeKeyedCells3, lookup_mergedCells_mergeKeyedCells3]
    dsimp only [mergedCellValueAt, mergeKeyedCellAt]
    have hComm := (mergeCell3_commutative (base.lookup k) (left.lookup k) (right.lookup k)).1
    cases hL : mergeCell3 (base.lookup k) (left.lookup k) (right.lookup k) with
    | merged optV =>
      have hR : mergeCell3 (base.lookup k) (right.lookup k) (left.lookup k) = .merged optV :=
        (hComm optV).1 hL
      rw [hR]
    | conflict bVal lVal rVal =>
      cases hR : mergeCell3 (base.lookup k) (right.lookup k) (left.lookup k) with
      | merged optV =>
        have hBack := (hComm optV).2 hR
        rw [hL] at hBack
        cases hBack
      | conflict _ _ _ => rfl
  · rw [mem_conflicts_mergeKeyedCells3, mem_conflicts_mergeKeyedCells3]
    dsimp only [mergeKeyedCellAt]
    have hConfComm := (mergeCell3_commutative (base.lookup k) (left.lookup k) (right.lookup k)).2
    constructor
    · rintro ⟨hC, rfl, rfl, rfl⟩
      exact ⟨hConfComm.1 hC, rfl, rfl, rfl⟩
    · rintro ⟨hC, rfl, rfl, rfl⟩
      exact ⟨hConfComm.2 hC, rfl, rfl, rfl⟩

/-- Keyed-list disjoint edits theorem: if `left` only edits `k1` (`right.lookup k1 = base.lookup k1`)
and `right` only edits `k2` (`left.lookup k2 = base.lookup k2`), then `mergeKeyedCellAt` merges both
keys cleanly without conflict. -/
theorem mergeKeyedCellAt_disjoint_edits_succeed
    (base left right : List (String × Obend.Core.Data.Data))
    (k1 k2 : String)
    (hR1 : right.lookup k1 = base.lookup k1)
    (hL2 : left.lookup k2 = base.lookup k2) :
    mergeKeyedCellAt base left right k1 = .merged (left.lookup k1) ∧
    mergeKeyedCellAt base left right k2 = .merged (right.lookup k2) := by
  simp [mergeKeyedCellAt, hR1, hL2]

/-- **Whole-Document Disjoint Edits Succeed Without Conflicts (`mergeKeyedCells3_disjoint_edits_no_conflicts`)**:
If at every cell key `k`, either `left` is unchanged (`left.lookup k = base.lookup k`), `right` is
unchanged (`right.lookup k = base.lookup k`), or both branches converged (`left.lookup k = right.lookup k`),
then `mergeKeyedCells3 base left right` produces zero conflicts (`conflicts = []`). -/
theorem mergeKeyedCells3_disjoint_edits_no_conflicts
    (base left right : List (String × Obend.Core.Data.Data))
    (hDisj : ∀ k, left.lookup k = base.lookup k ∨
                  right.lookup k = base.lookup k ∨
                  left.lookup k = right.lookup k) :
    (mergeKeyedCells3 base left right).conflicts = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro c hc
  obtain ⟨hConf, hB, hL, hR⟩ := (mem_conflicts_mergeKeyedCells3 base left right c).1 hc
  dsimp only [mergeKeyedCellAt] at hConf
  rw [hB, hL, hR, mergeCell3_conflict_iff] at hConf
  obtain ⟨hNeLR, hNeLB, hNeRB⟩ := hConf
  rcases hDisj c.key with hEqLB | hEqRB | hEqLR
  · exact hNeLB hEqLB
  · exact hNeRB hEqRB
  · exact hNeLR hEqLR

/-! ## $O(N \log N)$ Sorted-`Array` Keyed Lookup & Merge Execution (`@[csimp]`) -/

private def byteLtList : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x.toNat < y.toNat) || (x == y && byteLtList xs ys)

private theorem byteLtList_irrefl : ∀ a : List UInt8, byteLtList a a = false
  | [] => rfl
  | x :: xs => by simp [byteLtList, byteLtList_irrefl xs]

private theorem byteLtList_trans : ∀ (a b c : List UInt8),
    byteLtList a b = true → byteLtList b c = true → byteLtList a c = true
  | [], [], _, h, _ => by simp [byteLtList] at h
  | [], _ :: _, [], _, h => by simp [byteLtList] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [byteLtList] at h
  | _ :: _, _ :: _, [], _, h => by simp [byteLtList] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [byteLtList, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, _⟩
      · exact .inl (by omega)
      · exact .inl h1
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · exact .inl h2
      · exact .inr ⟨rfl, byteLtList_trans xs ys zs h1 h2⟩

private theorem byteLtList_total : ∀ (a b : List UInt8),
    byteLtList a b = false → byteLtList b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [byteLtList] at h
  | _ :: _, [], _, h => by simp [byteLtList] at h
  | x :: xs, y :: ys, h1, h2 => by
    by_cases hxy : x = y
    · subst hxy
      simp only [byteLtList, Nat.lt_irrefl, decide_false, beq_self_eq_true, Bool.true_and,
        Bool.false_or] at h1 h2
      rw [byteLtList_total xs ys h1 h2]
    · have hne : x.toNat ≠ y.toNat := fun h => hxy (UInt8.toNat_inj.mp h)
      by_cases hlt : x.toNat < y.toNat
      · simp [byteLtList, hlt] at h1
      · have hgt : y.toNat < x.toNat := by omega
        simp [byteLtList, hgt] at h2

/-- Zero-allocation bytewise lexicographic comparison over `ByteArray` slices. -/
private def byteSliceLt (a b : @& ByteArray) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    if ha : i < a.size then
      if hb : i < b.size then
        let xa := a[i]'ha
        let xb := b[i]'hb
        if xa.toNat < xb.toNat then true
        else if xa == xb then byteSliceLt a b fuel (i + 1)
        else false
      else false
    else decide (i < b.size)

private theorem byteSliceLt_eq (a b : ByteArray) :
    ∀ (fuel i : Nat), a.size - i < fuel →
      byteSliceLt a b fuel i = byteLtList (a.data.toList.drop i) (b.data.toList.drop i)
  | 0, _, hf => by omega
  | fuel + 1, i, hf => by
    unfold byteSliceLt
    by_cases ha : i < a.size
    · have hla : i < a.data.toList.length := by rwa [Array.length_toList, ByteArray.size_data]
      rw [List.drop_eq_getElem_cons hla]
      have hga : a.data.toList[i]'hla = a[i]'ha := rfl
      rw [hga]
      simp only [ha, ↓reduceDIte]
      by_cases hb : i < b.size
      · have hlb : i < b.data.toList.length := by rwa [Array.length_toList, ByteArray.size_data]
        rw [List.drop_eq_getElem_cons hlb]
        have hgb : b.data.toList[i]'hlb = b[i]'hb := rfl
        rw [hgb]
        simp only [hb, ↓reduceDIte]
        by_cases hlt : (a[i]'ha).toNat < (b[i]'hb).toNat
        · simp [byteLtList, hlt]
        · simp only [hlt, ↓reduceIte]
          by_cases heq : ((a[i]'ha) == (b[i]'hb)) = true
          · simp [byteLtList, hlt, heq, byteSliceLt_eq a b fuel (i + 1) (by omega)]
          · simp [byteLtList, hlt, heq]
      · have hgeb : b.data.toList.length ≤ i := by
          rw [Array.length_toList, ByteArray.size_data]; omega
        simp [hb, List.drop_eq_nil_of_le hgeb, byteLtList]
    · have hgea : a.data.toList.length ≤ i := by
        rw [Array.length_toList, ByteArray.size_data]; omega
      simp only [ha, ↓reduceDIte, List.drop_eq_nil_of_le hgea]
      by_cases hb : i < b.size
      · have hlb : i < b.data.toList.length := by rwa [Array.length_toList, ByteArray.size_data]
        rw [List.drop_eq_getElem_cons hlb]
        simp [hb, byteLtList]
      · have hgeb : b.data.toList.length ≤ i := by
          rw [Array.length_toList, ByteArray.size_data]; omega
        simp [hb, List.drop_eq_nil_of_le hgeb, byteLtList]

def strLt (a b : String) : Bool :=
  byteSliceLt a.toByteArray b.toByteArray (a.toByteArray.size + 1) 0

theorem strLt_irrefl (a : String) : strLt a a = false := by
  rw [strLt, byteSliceLt_eq _ _ _ 0 (by omega), List.drop_zero, byteLtList_irrefl]

theorem strLt_trans {a b c : String} (h1 : strLt a b = true) (h2 : strLt b c = true) :
    strLt a c = true := by
  rw [strLt, byteSliceLt_eq _ _ _ 0 (by omega), List.drop_zero] at h1 h2 ⊢
  exact byteLtList_trans _ _ _ h1 h2

theorem strLt_total {a b : String} (h1 : strLt a b = false) (h2 : strLt b a = false) : a = b := by
  rw [strLt, byteSliceLt_eq _ _ _ 0 (by omega), List.drop_zero] at h1 h2
  have hl := byteLtList_total _ _ h1 h2
  have hba : a.toByteArray = b.toByteArray := ByteArray.ext (Array.ext' hl)
  cases a; cases b
  dsimp only at hba
  subst hba
  rfl

/-- Merge two strictly sorted `(String × α)` lists, keeping the left value on equal keys (`List.lookup` semantics). -/
def mergeFirstStr {α : Type} : Nat → List (String × α) → List (String × α) → List (String × α)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
    if strLt k₁ k₂ then (k₁, v₁) :: mergeFirstStr fuel xs ((k₂, v₂) :: ys)
    else if strLt k₂ k₁ then (k₂, v₂) :: mergeFirstStr fuel ((k₁, v₁) :: xs) ys
    else (k₁, v₁) :: mergeFirstStr fuel xs ys

private theorem mem_mergeFirstStr {α : Type} :
    ∀ (fuel : Nat) (xs ys : List (String × α)) (p : String × α),
      p ∈ mergeFirstStr fuel xs ys → p ∈ xs ∨ p ∈ ys
  | 0, xs, ys, p, h => List.mem_append.mp h
  | _ + 1, [], _, _, h => .inr h
  | _ + 1, x :: xs, [], _, h => .inl h
  | fuel + 1, (k₁, v₁) :: xs, (k₂, v₂) :: ys, p, h => by
    unfold mergeFirstStr at h
    by_cases h12 : strLt k₁ k₂ = true
    · simp only [h12, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | hr
      · exact .inl List.mem_cons_self
      · rcases mem_mergeFirstStr fuel xs ((k₂, v₂) :: ys) p hr with hx | hy
        · exact .inl (List.mem_cons_of_mem _ hx)
        · exact .inr hy
    · simp only [h12, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h21 : strLt k₂ k₁ = true
      · simp only [h21, ↓reduceIte, List.mem_cons] at h
        rcases h with rfl | hr
        · exact .inr List.mem_cons_self
        · rcases mem_mergeFirstStr fuel ((k₁, v₁) :: xs) ys p hr with hx | hy
          · exact .inl hx
          · exact .inr (List.mem_cons_of_mem _ hy)
      · simp only [h21, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h
        rcases h with rfl | hr
        · exact .inl List.mem_cons_self
        · rcases mem_mergeFirstStr fuel xs ys p hr with hx | hy
          · exact .inl (List.mem_cons_of_mem _ hx)
          · exact .inr (List.mem_cons_of_mem _ hy)

private theorem mergeFirstStr_sorted {α : Type} :
    ∀ (fuel : Nat) (xs ys : List (String × α)),
      xs.length + ys.length ≤ fuel →
      xs.Pairwise (fun a b => strLt a.1 b.1 = true) →
      ys.Pairwise (fun a b => strLt a.1 b.1 = true) →
      (mergeFirstStr fuel xs ys).Pairwise (fun a b => strLt a.1 b.1 = true)
  | 0, xs, ys, hf, _, _ => by
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx hy; simp [mergeFirstStr]
  | _ + 1, [], _, _, _, hys => hys
  | _ + 1, x :: xs, [], _, hxs, _ => hxs
  | fuel + 1, (k₁, v₁) :: xs, (k₂, v₂) :: ys, hf, hxs, hys => by
    simp only [List.length_cons] at hf
    obtain ⟨hx_hd, hx_tl⟩ := List.pairwise_cons.mp hxs
    obtain ⟨hy_hd, hy_tl⟩ := List.pairwise_cons.mp hys
    unfold mergeFirstStr
    by_cases h12 : strLt k₁ k₂ = true
    · simp only [h12, ↓reduceIte, List.pairwise_cons]
      refine ⟨fun p hp => ?_, mergeFirstStr_sorted fuel xs ((k₂, v₂) :: ys) (by simp; omega) hx_tl hys⟩
      rcases mem_mergeFirstStr fuel xs ((k₂, v₂) :: ys) p hp with hx | hy
      · exact hx_hd p hx
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact h12
        · exact strLt_trans h12 (hy_hd p hy')
    · simp only [h12, Bool.false_eq_true, ↓reduceIte]
      by_cases h21 : strLt k₂ k₁ = true
      · simp only [h21, ↓reduceIte, List.pairwise_cons]
        refine ⟨fun p hp => ?_, mergeFirstStr_sorted fuel ((k₁, v₁) :: xs) ys (by simp; omega) hxs hy_tl⟩
        rcases mem_mergeFirstStr fuel ((k₁, v₁) :: xs) ys p hp with hx | hy
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact h21
          · exact strLt_trans h21 (hx_hd p hx')
        · exact hy_hd p hy
      · simp only [h21, Bool.false_eq_true, ↓reduceIte, List.pairwise_cons]
        have heq : k₁ = k₂ :=
          strLt_total (Bool.eq_false_iff.mpr h12) (Bool.eq_false_iff.mpr h21)
        subst heq
        refine ⟨fun p hp => ?_, mergeFirstStr_sorted fuel xs ys (by omega) hx_tl hy_tl⟩
        rcases mem_mergeFirstStr fuel xs ys p hp with hx | hy
        · exact hx_hd p hx
        · exact hy_hd p hy

private theorem lookup_str_append {α : Type} (l m : List (String × α)) (q : String) :
    (l ++ m).lookup q = (l.lookup q).or (m.lookup q) := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    by_cases h : q = k
    · subst h; simp [List.lookup]
    · have hb : (q == k) = false := beq_eq_false_iff_ne.mpr h
      simp [List.lookup, hb, ih]

private theorem lookup_eq_none_of_strLt_all {α : Type} {xs : List (String × α)} {q : String}
    (h : ∀ p ∈ xs, strLt q p.1 = true) : xs.lookup q = none := by
  induction xs with
  | nil => rfl
  | cons kv rest ih =>
    have hlt := h kv List.mem_cons_self
    have hne : q ≠ kv.1 := fun heq => by rw [heq, strLt_irrefl] at hlt; cases hlt
    have hb : (q == kv.1) = false := beq_eq_false_iff_ne.mpr hne
    simp [List.lookup, hb, ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

private theorem lookup_mergeFirstStr {α : Type} :
    ∀ (fuel : Nat) (xs ys : List (String × α)),
      xs.Pairwise (fun a b => strLt a.1 b.1 = true) →
      ys.Pairwise (fun a b => strLt a.1 b.1 = true) →
      ∀ q : String, (mergeFirstStr fuel xs ys).lookup q = (xs.lookup q).or (ys.lookup q)
  | 0, xs, ys, _, _, q => lookup_str_append xs ys q
  | _ + 1, [], ys, _, _, _ => rfl
  | _ + 1, x :: xs, [], _, _, q => by
    simp only [mergeFirstStr, List.lookup_nil]
    cases ((x :: xs).lookup q) <;> rfl
  | fuel + 1, (k₁, v₁) :: xs, (k₂, v₂) :: ys, hxs, hys, q => by
    obtain ⟨hx_hd, hx_tl⟩ := List.pairwise_cons.mp hxs
    obtain ⟨hy_hd, hy_tl⟩ := List.pairwise_cons.mp hys
    unfold mergeFirstStr
    by_cases h12 : strLt k₁ k₂ = true
    · simp only [h12, ↓reduceIte]
      by_cases hq1 : q = k₁
      · subst hq1; simp [List.lookup]
      · have hb1 : (q == k₁) = false := beq_eq_false_iff_ne.mpr hq1
        simp only [List.lookup, hb1, lookup_mergeFirstStr fuel xs ((k₂, v₂) :: ys) hx_tl hys q]
    · simp only [h12, Bool.false_eq_true, ↓reduceIte]
      by_cases h21 : strLt k₂ k₁ = true
      · simp only [h21, ↓reduceIte]
        by_cases hq2 : q = k₂
        · subst hq2
          have hnone : (((k₁, v₁) :: xs).lookup q) = none := by
            apply lookup_eq_none_of_strLt_all
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact h21
            · exact strLt_trans h21 (hx_hd p hp')
          rw [hnone]
          simp [List.lookup]
        · have hb2 : (q == k₂) = false := beq_eq_false_iff_ne.mpr hq2
          rw [List.lookup, hb2, lookup_mergeFirstStr fuel ((k₁, v₁) :: xs) ys hxs hy_tl q]
          cases (((k₁, v₁) :: xs).lookup q) <;> simp [List.lookup, hb2]
      · simp only [h21, Bool.false_eq_true, ↓reduceIte]
        have heq : k₁ = k₂ :=
          strLt_total (Bool.eq_false_iff.mpr h12) (Bool.eq_false_iff.mpr h21)
        subst heq
        by_cases hq1 : q = k₁
        · subst hq1; simp [List.lookup]
        · have hb1 : (q == k₁) = false := beq_eq_false_iff_ne.mpr hq1
          simp [List.lookup, hb1, lookup_mergeFirstStr fuel xs ys hx_tl hy_tl q]

def mergeFirstPass {α : Type} : List (List (String × α)) → List (List (String × α))
  | a :: b :: rest => mergeFirstStr (a.length + b.length) a b :: mergeFirstPass rest
  | runs => runs

def mergeFirstLoop {α : Type} : Nat → List (List (String × α)) → List (String × α)
  | 0, runs => runs.foldr (fun r acc => mergeFirstStr (r.length + acc.length) r acc) []
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | fuel + 1, a :: b :: rest => mergeFirstLoop fuel (mergeFirstPass (a :: b :: rest))

private theorem mergeFirstPass_spec {α : Type} :
    ∀ (runs : List (List (String × α))),
      (∀ r ∈ runs, r.Pairwise (fun a b => strLt a.1 b.1 = true)) →
      (∀ r ∈ mergeFirstPass runs, r.Pairwise (fun a b => strLt a.1 b.1 = true)) ∧
      (∀ q, (mergeFirstPass runs).flatten.lookup q = runs.flatten.lookup q)
  | [], _ => ⟨fun _ h => (nomatch h), fun _ => rfl⟩
  | [a], h => ⟨h, fun _ => rfl⟩
  | a :: b :: rest, h => by
    have ha := h a List.mem_cons_self
    have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    have hr := fun r hm => h r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
    obtain ⟨ih_s, ih_l⟩ := mergeFirstPass_spec rest hr
    refine ⟨fun r hm => ?_, fun q => ?_⟩
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact mergeFirstStr_sorted _ a b (Nat.le_refl _) ha hb
      · exact ih_s r hm'
    · simp only [mergeFirstPass, List.flatten_cons, lookup_str_append,
        lookup_mergeFirstStr _ a b ha hb q, ih_l q, Option.or_assoc]

private theorem foldr_mergeFirst_spec {α : Type} :
    ∀ (runs : List (List (String × α))),
      (∀ r ∈ runs, r.Pairwise (fun a b => strLt a.1 b.1 = true)) →
      let out := runs.foldr (fun r acc => mergeFirstStr (r.length + acc.length) r acc) []
      out.Pairwise (fun a b => strLt a.1 b.1 = true) ∧
      ∀ q, out.lookup q = runs.flatten.lookup q
  | [], _ => ⟨.nil, fun _ => rfl⟩
  | r :: rs, h => by
    have hr := h r List.mem_cons_self
    obtain ⟨ih_s, ih_l⟩ := foldr_mergeFirst_spec rs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨mergeFirstStr_sorted _ r _ (Nat.le_refl _) hr ih_s, fun q => ?_⟩
    simp only [List.foldr_cons, List.flatten_cons, lookup_str_append,
      lookup_mergeFirstStr _ r _ hr ih_s q, ih_l q]

private theorem mergeFirstLoop_spec {α : Type} :
    ∀ (fuel : Nat) (runs : List (List (String × α))),
      (∀ r ∈ runs, r.Pairwise (fun a b => strLt a.1 b.1 = true)) →
      (mergeFirstLoop fuel runs).Pairwise (fun a b => strLt a.1 b.1 = true) ∧
      ∀ q, (mergeFirstLoop fuel runs).lookup q = runs.flatten.lookup q
  | 0, runs, h => foldr_mergeFirst_spec runs h
  | _ + 1, [], _ => ⟨.nil, fun _ => rfl⟩
  | _ + 1, [a], h => ⟨h a List.mem_cons_self, fun q => by simp [mergeFirstLoop]⟩
  | fuel + 1, a :: b :: rest, h => by
    obtain ⟨hp_s, hp_l⟩ := mergeFirstPass_spec (a :: b :: rest) h
    obtain ⟨ih_s, ih_l⟩ := mergeFirstLoop_spec fuel (mergeFirstPass (a :: b :: rest)) hp_s
    exact ⟨ih_s, fun q => (ih_l q).trans (hp_l q)⟩

/-- Build a strictly-sorted `Array (String × α)` dictionary in $O(N \log N)$ preserving first-entry wins. -/
def buildStrMap {α : Type} (xs : List (String × α)) : Array (String × α) :=
  (mergeFirstLoop (xs.length + 1) (xs.map (fun kv => [kv]))).toArray

private theorem flatten_map_singleton {α : Type} :
    ∀ xs : List α, (xs.map (fun x => [x])).flatten = xs
  | [] => rfl
  | _ :: xs => by simp [flatten_map_singleton xs]

theorem buildStrMap_spec {α : Type} (xs : List (String × α)) :
    (buildStrMap xs).toList.Pairwise (fun a b => strLt a.1 b.1 = true) ∧
    ∀ q, (buildStrMap xs).toList.lookup q = xs.lookup q := by
  have hsing : ∀ r ∈ xs.map (fun kv => [kv]), r.Pairwise (fun a b => strLt a.1 b.1 = true) := by
    intro r hr
    obtain ⟨kv, _, rfl⟩ := List.mem_map.mp hr
    exact List.pairwise_singleton _ kv
  obtain ⟨hs, hl⟩ := mergeFirstLoop_spec (xs.length + 1) (xs.map (fun kv => [kv])) hsing
  simpa [buildStrMap, flatten_map_singleton] using And.intro hs hl

/-- $O(\log N)$ binary search over a `buildStrMap` array. -/
def bsearchStrMap {α : Type} (m : @& Array (String × α)) (k : String) :
    Nat → Nat → Nat → Option α
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if hm : mid < m.size then
        let kv := m[mid]'hm
        if strLt kv.1 k then bsearchStrMap m k fuel (mid + 1) hi
        else if strLt k kv.1 then bsearchStrMap m k fuel lo mid
        else some kv.2
      else none
    else none

def lookupStrMap {α : Type} (m : @& Array (String × α)) (k : String) : Option α :=
  bsearchStrMap m k (m.size + 1) 0 m.size

private theorem pairwise_str_getElem? {α : Type} :
    ∀ {l : List (String × α)}, l.Pairwise (fun a b => strLt a.1 b.1 = true) →
      ∀ {i j : Nat} {x y : String × α},
        l[i]? = some x → l[j]? = some y → i < j → strLt x.1 y.1 = true
  | [], _, _, _, _, _, hi, _, _ => by simp at hi
  | a :: l, hp, i, j, x, y, hi, hj, hij => by
    cases j with
    | zero => omega
    | succ j =>
      rw [List.getElem?_cons_succ] at hj
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at hi
        cases hi
        exact (List.pairwise_cons.mp hp).1 y (List.mem_of_getElem? hj)
      | succ i =>
        rw [List.getElem?_cons_succ] at hi
        exact pairwise_str_getElem? (List.pairwise_cons.mp hp).2 hi hj (by omega)

private theorem lookup_of_sorted_getElem? {α : Type} :
    ∀ {l : List (String × α)}, l.Pairwise (fun a b => strLt a.1 b.1 = true) →
      ∀ {i : Nat} {e : String × α}, l[i]? = some e → l.lookup e.1 = some e.2
  | [], _, _, _, h => by simp at h
  | a :: l, hp, i, e, h => by
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      cases h; simp [List.lookup]
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      have hlt := (List.pairwise_cons.mp hp).1 e (List.mem_of_getElem? h)
      have hne : e.1 ≠ a.1 := fun heq => by rw [heq, strLt_irrefl] at hlt; cases hlt
      have hb : (e.1 == a.1) = false := beq_eq_false_iff_ne.mpr hne
      simp [List.lookup, hb, lookup_of_sorted_getElem? (List.pairwise_cons.mp hp).2 h]

private theorem bsearchStrMap_eq_lookup {α : Type} (m : Array (String × α)) (k : String)
    (hs : m.toList.Pairwise (fun a b => strLt a.1 b.1 = true)) :
    ∀ (fuel lo hi : Nat), hi ≤ m.size → hi - lo < fuel →
      (∀ (i : Nat) (e : String × α), m.toList[i]? = some e → (i < lo ∨ hi ≤ i) → e.1 ≠ k) →
      bsearchStrMap m k fuel lo hi = m.toList.lookup k
  | 0, _, _, _, hf, _ => by omega
  | fuel + 1, lo, hi, hhi, hf, hout => by
    unfold bsearchStrMap
    by_cases hlt : lo < hi
    · simp only [hlt, ↓reduceIte]
      have hmid : (lo + hi) / 2 < m.size := by omega
      simp only [hmid, ↓reduceDIte]
      have hel : m.toList[(lo + hi) / 2]? = some (m[(lo + hi) / 2]'hmid) := by
        rw [Array.getElem?_toList, Array.getElem?_eq_getElem hmid]
      by_cases hk1 : strLt (m[(lo + hi) / 2]'hmid).1 k = true
      · simp only [hk1, ↓reduceIte]
        refine bsearchStrMap_eq_lookup m k hs fuel ((lo + hi) / 2 + 1) hi hhi (by omega) ?_
        intro i x hx hcase
        rcases hcase with hlo' | hhi'
        · by_cases hlo : i < lo
          · exact hout i x hx (.inl hlo)
          · intro hxk
            by_cases him : i = (lo + hi) / 2
            · subst him; rw [hel] at hx; cases hx; rw [hxk, strLt_irrefl] at hk1; cases hk1
            · have hxe := pairwise_str_getElem? hs hx hel (by omega)
              have hkk := strLt_trans hxe hk1
              rw [hxk, strLt_irrefl] at hkk; cases hkk
        · exact hout i x hx (.inr hhi')
      · simp only [hk1, Bool.false_eq_true, ↓reduceIte]
        by_cases hk2 : strLt k (m[(lo + hi) / 2]'hmid).1 = true
        · simp only [hk2, ↓reduceIte]
          refine bsearchStrMap_eq_lookup m k hs fuel lo ((lo + hi) / 2) (by omega) (by omega) ?_
          intro i x hx hcase
          rcases hcase with hlo' | hhi'
          · exact hout i x hx (.inl hlo')
          · by_cases hhi0 : hi ≤ i
            · exact hout i x hx (.inr hhi0)
            · intro hxk
              by_cases him : i = (lo + hi) / 2
              · subst him; rw [hel] at hx; cases hx; rw [hxk, strLt_irrefl] at hk2; cases hk2
              · have hex := pairwise_str_getElem? hs hel hx (by omega)
                have hkk := strLt_trans hk2 hex
                rw [hxk, strLt_irrefl] at hkk; cases hkk
        · simp only [hk2, Bool.false_eq_true, ↓reduceIte]
          have hek : (m[(lo + hi) / 2]'hmid).1 = k :=
            strLt_total (Bool.eq_false_iff.mpr hk1) (Bool.eq_false_iff.mpr hk2)
          rw [← hek]
          exact (lookup_of_sorted_getElem? hs hel).symm
    · simp only [hlt, ↓reduceIte]
      symm
      apply Patch.lookup_eq_none_of_not_mem_map_fst
      intro hm
      obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hm
      obtain ⟨i, hi', hget⟩ := List.mem_iff_getElem.mp hp
      have hp? : m.toList[i]? = some p := by rw [List.getElem?_eq_getElem hi', hget]
      exact hout i p hp? (by omega) hpk

theorem lookupStrMap_buildStrMap {α : Type} (xs : List (String × α)) (k : String) :
    lookupStrMap (buildStrMap xs) k = xs.lookup k := by
  obtain ⟨hs, hl⟩ := buildStrMap_spec xs
  rw [← hl k, lookupStrMap]
  refine bsearchStrMap_eq_lookup (buildStrMap xs) k hs _ 0 _ (Nat.le_refl _) (by omega) ?_
  intro i e he hcase
  rcases hcase with h0 | hge
  · omega
  · have hlt : i < (buildStrMap xs).toList.length := (List.getElem?_eq_some_iff.mp he).1
    rw [Array.length_toList] at hlt; omega

/-- Deduplicate `ks : List String` in $O(N \log N)$ keeping exact first-occurrence order (`Patch.dedupStringKeys`). -/
def dedupStringKeysExec (ks : List String) : List String :=
  let idxMap := buildStrMap ks.zipIdx
  ks.zipIdx.filterMap fun p =>
    if lookupStrMap idxMap p.1 == some p.2 then some p.1 else none

private theorem le_snd_of_mem_zipIdx :
    ∀ (xs : List String) (s : Nat) (p : String × Nat), p ∈ xs.zipIdx s → s ≤ p.2
  | [], _, _, h => nomatch h
  | _ :: tl, s, p, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.mp h with rfl | htl
    · exact Nat.le_refl s
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self s)
        (le_snd_of_mem_zipIdx tl (s + 1) p htl))

private theorem filterMap_lookup_cons_fixed (k : String) (start : Nat)
    (tbl : List (String × Nat)) :
    ∀ (xs : List (String × Nat)),
      (∀ q ∈ xs, start < q.2) →
      xs.filterMap (fun q =>
        if (((k, start) :: tbl).lookup q.1 == some q.2) then some q.1 else none) =
      (xs.filterMap (fun q =>
        if (tbl.lookup q.1 == some q.2) then some q.1 else none)).filter (· != k)
  | [], _ => rfl
  | p :: ps, hgt => by
    have hp_gt : start < p.2 := hgt p List.mem_cons_self
    have hps_gt : ∀ q ∈ ps, start < q.2 := fun q hq => hgt q (List.mem_cons_of_mem _ hq)
    rw [List.filterMap_cons, List.filterMap_cons,
      filterMap_lookup_cons_fixed k start tbl ps hps_gt]
    by_cases hpk : p.1 = k
    · have hhd1 : (((k, start) :: tbl).lookup p.1 == some p.2) = false := by
        rw [List.lookup, beq_iff_eq.mpr hpk, beq_eq_false_iff_ne]
        intro he; injection he; omega
      have hbne : (p.1 != k) = false := bne_eq_false_iff_eq.mpr hpk
      rw [hhd1]
      cases (tbl.lookup p.1 == some p.2) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons, hbne]
    · have hhd2 : (((k, start) :: tbl).lookup p.1) = tbl.lookup p.1 := by
        rw [List.lookup, beq_eq_false_iff_ne.mpr hpk]
      have hbne : (p.1 != k) = true := bne_iff_ne.mpr hpk
      rw [hhd2]
      cases (tbl.lookup p.1 == some p.2) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons, hbne]

private theorem filterMap_firstIdx_eq :
    ∀ (ks : List String) (start : Nat),
      (ks.zipIdx start).filterMap (fun p =>
        if (ks.zipIdx start).lookup p.1 == some p.2 then some p.1 else none) =
        Patch.dedupStringKeys ks
  | [], _ => rfl
  | k :: rest, start => by
    rw [List.zipIdx_cons, List.filterMap_cons]
    have hhd : (((k, start) :: rest.zipIdx (start + 1)).lookup k) = some start := by
      simp [List.lookup]
    rw [hhd]
    simp only [beq_self_eq_true, ↓reduceIte, Patch.dedupStringKeys,
      List.cons.injEq, true_and]
    have hgt : ∀ p ∈ rest.zipIdx (start + 1), start < p.2 := fun p hp =>
      Nat.lt_of_lt_of_le (Nat.lt_succ_self start) (le_snd_of_mem_zipIdx rest (start + 1) p hp)
    rw [filterMap_lookup_cons_fixed k start (rest.zipIdx (start + 1)) (rest.zipIdx (start + 1)) hgt,
      filterMap_firstIdx_eq rest (start + 1)]

@[csimp] theorem dedupStringKeys_eq_exec :
    @Patch.dedupStringKeys = @dedupStringKeysExec := by
  funext ks
  unfold dedupStringKeysExec
  dsimp only
  have hfun : (fun p : String × Nat =>
      if lookupStrMap (buildStrMap (ks.zipIdx 0)) p.1 == some p.2 then some p.1 else none) =
    (fun p : String × Nat =>
      if (ks.zipIdx 0).lookup p.1 == some p.2 then some p.1 else none) := by
    funext p; rw [lookupStrMap_buildStrMap]
  rw [hfun, filterMap_firstIdx_eq ks 0]

/-- $O(N \log N)$ keyed cell diff using sorted `Array` binary search. -/
def diffKeyedCellsExec
    (base branch : List (String × Obend.Core.Data.Data)) :
    List (String × Option Obend.Core.Data.Data) :=
  let keys := dedupStringKeysExec ((base.map Prod.fst) ++ (branch.map Prod.fst))
  let bMap := buildStrMap base
  let brMap := buildStrMap branch
  keys.filterMap fun k =>
    let bVal := lookupStrMap bMap k
    let brVal := lookupStrMap brMap k
    if brVal = bVal then none else some (k, brVal)

@[csimp] theorem diffKeyedCells_eq_exec :
    @Patch.diffKeyedCells = @diffKeyedCellsExec := by
  funext base branch
  unfold Patch.diffKeyedCells diffKeyedCellsExec
  rw [← dedupStringKeys_eq_exec]
  dsimp only
  congr 1
  funext k
  simp [lookupStrMap_buildStrMap]

/-- $O(N \log N)$ 3-way keyed cell merge using sorted `Array` binary search (evaluates each key once). -/
def mergeKeyedCells3Exec
    (base left right : List (String × Obend.Core.Data.Data)) : KeyedMergeOutcome :=
  let keys := dedupStringKeysExec ((base.map Prod.fst) ++ (left.map Prod.fst) ++ (right.map Prod.fst))
  let bMap := buildStrMap base
  let lMap := buildStrMap left
  let rMap := buildStrMap right
  let mergedCells := keys.filterMap fun k =>
    match mergeCell3 (lookupStrMap bMap k) (lookupStrMap lMap k) (lookupStrMap rMap k) with
    | .merged (some v) => some (k, v)
    | .merged none => none
    | .conflict _ _ _ => none
  let conflicts := keys.filterMap fun k =>
    match mergeCell3 (lookupStrMap bMap k) (lookupStrMap lMap k) (lookupStrMap rMap k) with
    | .merged _ => none
    | .conflict b l r => some ⟨k, b, l, r⟩
  { mergedCells := mergedCells, conflicts := conflicts }

@[csimp] theorem mergeKeyedCells3_eq_exec :
    @mergeKeyedCells3 = @mergeKeyedCells3Exec := by
  funext base left right
  unfold mergeKeyedCells3 mergeKeyedCells3Exec collectCellKeys
  rw [← dedupStringKeys_eq_exec]
  dsimp only
  have hm : (fun k =>
      match mergeCell3 (lookupStrMap (buildStrMap base) k)
          (lookupStrMap (buildStrMap left) k) (lookupStrMap (buildStrMap right) k) with
      | .merged (some v) => some (k, v)
      | .merged none => none
      | .conflict _ _ _ => none) =
    (fun k => (mergedCellValueAt base left right k).map fun v => (k, v)) := by
    funext k
    simp only [lookupStrMap_buildStrMap, mergedCellValueAt, mergeKeyedCellAt]
    cases mergeCell3 (base.lookup k) (left.lookup k) (right.lookup k) with
    | merged opt => cases opt <;> rfl
    | conflict _ _ _ => rfl
  have hc : (fun k =>
      match mergeCell3 (lookupStrMap (buildStrMap base) k)
          (lookupStrMap (buildStrMap left) k) (lookupStrMap (buildStrMap right) k) with
      | .merged _ => none
      | .conflict b l r => some (⟨k, b, l, r⟩ : MergeConflict)) =
    (fun k =>
      match mergeKeyedCellAt base left right k with
      | .merged _ => none
      | .conflict b l r => some (⟨k, b, l, r⟩ : MergeConflict)) := by
    funext k
    simp [lookupStrMap_buildStrMap, mergeKeyedCellAt]
  simp [hm, hc]

end Obend.Doc

end

