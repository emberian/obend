module
/-
# Obend.Receipt.Merkle — a positional Merkle map: the commitment a view's root is

`lean/docs/REPORT-JUDGE-20261031.md` (the decision: the ledger's view commits pins). A VIEW is a
list of values at the positions of a public schema (`Commit`: the keys, and each key's value at a
world). Its root is a binary Merkle tree over the leaves `digestWith H j v` (position `j`, value
`v`), each inner node one `digestWith H left right` (`Obend.Core.Digest`, cSHAKE256 at `deployed`).
The tree splits a list at half its length, so the shape is a function of the size alone.

An OPENING of position `j` is the value and the siblings on the way up (`Opening`); `opens` climbs
from the leaf to a root, checking every sibling and the position are digest-sized.

- `opens_complete`: the honest opening of every position opens against the root (`mapPath`).
- `climb_binds`: two openings of one position to one root have one leaf, or the hash has a
  collision; `opens_binds`: they have one VALUE, or a collision. Nothing about cSHAKE256 is assumed:
  the disjunct is where its collision resistance enters (`binds_or_collides`).
- `Commit.opens_view`: an opening that opens against the root of a world's view carries that
  world's value at that key, or the hash collides. This is what makes a receipt's `dated` root a
  CHECKED support: a stranger holding the root checks each opening without trusting the host.
- `lengthHash_opens_lie` is the refutable pole: under the length hash, an opening of a different
  value opens against the same root.
-/
public import Obend.Core.Digest

public section
namespace Obend.Receipt.Merkle
open Obend.Core.Digest (digestWith Admissible admissible_of_lt binds_or_collides deployed digest_lt preimage lengthHash)
open Obend.Digest.HashBytes (Hash CollisionAmong be ofBE be_injective ofBE_lt)
set_option autoImplicit false

/-- A digest-sized natural: what every node of the tree is. -/
def Small (n : Nat) : Bool := decide (n < 2 ^ 256)

/-- A hash whose digests are digest-sized. -/
@[expose] def Bounded (H : Hash) : Prop := ∀ a b, digestWith H a b < 2 ^ 256

/-- The deployed hash is bounded (32 bytes out). -/
theorem deployed_bounded : Bounded deployed := fun a b => digest_lt a b

/-! ## The tree -/

/-- The root of a list of leaves: a lone leaf is its own root, an empty list's root is 0, and a
longer list's is the node over the roots of its halves. -/
def root (H : Hash) (l : List Nat) : Nat :=
  if l.length < 2 then l.headD 0
  else digestWith H (root H (l.take (l.length / 2))) (root H (l.drop (l.length / 2)))
termination_by l.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- The siblings on the way from leaf `i` to the root, top first. -/
def path (H : Hash) (l : List Nat) (i : Nat) : List Nat :=
  if l.length < 2 then []
  else if i < l.length / 2 then root H (l.drop (l.length / 2)) :: path H (l.take (l.length / 2)) i
  else root H (l.take (l.length / 2)) :: path H (l.drop (l.length / 2)) (i - l.length / 2)
termination_by l.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- Climb from leaf `x` at position `i` of a tree of `n` leaves along the siblings `p`, top first. -/
def climb (H : Hash) : (n i x : Nat) → List Nat → Option Nat
  | n, _, x, [] => if n = 1 then some x else none
  | n, i, x, s :: ss =>
    if n < 2 || !Small s then none
    else if i < n / 2 then (climb H (n / 2) i x ss).map fun l => digestWith H l s
    else (climb H (n - n / 2) (i - n / 2) x ss).map fun r => digestWith H s r

/-- The root of a nonempty list of digest-sized leaves is digest-sized. -/
theorem root_lt {H : Hash} (hb : Bounded H) (l : List Nat) (hl : ∀ x ∈ l, x < 2 ^ 256) (hne : l ≠ []) :
    root H l < 2 ^ 256 := by
  rw [root]; split
  · match l, hne with
    | x :: _, _ => exact hl x (by simp)
  · exact hb _ _

theorem getD_take (l : List Nat) {k i : Nat} (h : i < k) : (l.take k).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ↓reduceIte]

theorem getD_drop (l : List Nat) (k i : Nat) : (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **Every leaf's honest path climbs to the root.** -/
theorem climb_path {H : Hash} (hb : Bounded H) :
    ∀ (l : List Nat), (∀ x ∈ l, x < 2 ^ 256) → ∀ (i : Nat), i < l.length →
      climb H l.length i (l.getD i 0) (path H l i) = some (root H l) := by
  intro l
  induction l using (measure List.length).wf.induction with
  | h l ih =>
  intro hl i hi
  by_cases h2 : l.length < 2
  · have h1 : l.length = 1 := by omega
    rw [path, if_pos h2, root, if_pos h2]
    simp only [climb, h1, ↓reduceIte]
    match l, h1 with
    | [x], _ => simp at hi; subst hi; rfl
  · have hk : l.length / 2 < l.length := by omega
    have hk0 : 0 < l.length / 2 := by omega
    have htake : ∀ x ∈ l.take (l.length / 2), x < 2 ^ 256 := fun x hx => hl x (List.mem_of_mem_take hx)
    have hdrop : ∀ x ∈ l.drop (l.length / 2), x < 2 ^ 256 := fun x hx => hl x (List.mem_of_mem_drop hx)
    have hlt : (l.take (l.length / 2)).length = l.length / 2 := by rw [List.length_take]; omega
    have hld : (l.drop (l.length / 2)).length = l.length - l.length / 2 := List.length_drop
    have hst : Small (root H (l.take (l.length / 2))) = true := by
      simp only [Small, decide_eq_true_eq]
      exact root_lt hb _ htake (by intro h; have := congrArg List.length h; rw [hlt] at this; simp at this; omega)
    have hsd : Small (root H (l.drop (l.length / 2))) = true := by
      simp only [Small, decide_eq_true_eq]
      exact root_lt hb _ hdrop (by intro h; have := congrArg List.length h; rw [hld] at this; simp at this; omega)
    rw [path, if_neg h2]
    conv => rhs; rw [root, if_neg h2]
    by_cases hi' : i < l.length / 2
    · rw [if_pos hi']
      have ihl := ih (l.take (l.length / 2)) (show (l.take (l.length / 2)).length < l.length by rw [hlt]; exact hk) htake i (by rw [hlt]; exact hi')
      rw [hlt, getD_take l hi'] at ihl
      simp only [climb, hsd, Bool.not_true, Bool.or_false, decide_eq_true_eq, h2, decide_false,
        hi', ↓reduceIte, ihl, Option.map_some, Bool.false_eq_true]
    · rw [if_neg hi']
      have ihr := ih (l.drop (l.length / 2)) (show (l.drop (l.length / 2)).length < l.length by rw [hld]; omega) hdrop (i - l.length / 2)
        (by rw [hld]; omega)
      rw [hld, getD_drop, show l.length / 2 + (i - l.length / 2) = i by omega] at ihr
      simp only [climb, hst, Bool.not_true, Bool.or_false, decide_eq_true_eq, h2, decide_false,
        hi', ↓reduceIte, ihr, Option.map_some, Bool.false_eq_true]

/-- What a climb reaches is the leaf, or a node: digest-sized when the leaf is. -/
theorem climb_small {H : Hash} (hb : Bounded H) :
    ∀ (p : List Nat) (n i x r : Nat), x < 2 ^ 256 → climb H n i x p = some r → r < 2 ^ 256
  | [], n, i, x, r, hx, h => by
    simp only [climb] at h; split at h
    · cases h; exact hx
    · cases h
  | s :: ss, n, i, x, r, hx, h => by
    simp only [climb] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨l, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact hb _ _
      · obtain ⟨l, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact hb _ _

/-- Finite list of `preimage` byte strings hashed along `climb H n i x p`. -/
def climbPreimages (H : Hash) : (n i x : Nat) → List Nat → List (List UInt8)
  | _, _, _, [] => []
  | n, i, x, s :: ss =>
    if i < n / 2 then
      let rest := climbPreimages H (n / 2) i x ss
      match climb H (n / 2) i x ss with | some l => preimage l s :: rest | none => rest
    else
      let rest := climbPreimages H (n - n / 2) (i - n / 2) x ss
      match climb H (n - n / 2) (i - n / 2) x ss with | some r => preimage s r :: rest | none => rest

/-- **Scoped Binding**: two climbs from one position of one tree to one root start at one leaf, or `H`
collides among the finite preimages those two climbs actually hashed. -/
theorem climb_binds {H : Hash} (hb : Bounded H) :
    ∀ (p p' : List Nat) (n i x x' r : Nat), x < 2 ^ 256 → x' < 2 ^ 256 →
      climb H n i x p = some r → climb H n i x' p' = some r →
      x = x' ∨ CollisionAmong H (fun m => m ∈ climbPreimages H n i x p ++ climbPreimages H n i x' p')
  | [], [], n, _, x, x', _, _, _, h, h' => by
    simp only [climb] at h h'
    by_cases hn : n = 1
    · simp only [hn, ↓reduceIte, Option.some.injEq] at h h'; exact .inl (h.trans h'.symm)
    · simp [hn] at h
  | [], _ :: _, n, _, _, _, _, _, _, h, h' => by
    simp only [climb] at h h'; split at h
    · rename_i hn; subst hn; simp at h'
    · cases h
  | _ :: _, [], n, _, _, _, _, _, _, h, h' => by
    simp only [climb] at h h'; split at h'
    · rename_i hn; subst hn; simp at h
    · cases h'
  | s :: ss, s' :: ss', n, i, x, x', _, hx, hx', h, h' => by
    simp only [climb] at h h'
    split at h; · cases h
    rename_i hn; split at h'; · cases h'
    rename_i hn'
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, Small,
      decide_eq_false_iff_not, Nat.not_lt] at hn hn'
    split at h
    · rename_i hi; simp only [hi, ↓reduceIte] at h'
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨l', hl', he⟩ := Option.map_eq_some_iff.1 h'
      have hla := admissible_of_lt (climb_small hb ss _ _ x l hx hl)
      have hla' := admissible_of_lt (climb_small hb ss' _ _ x' l' hx' hl')
      rcases binds_or_collides H hla' hla he with ⟨hll, _⟩ | c
      · rcases climb_binds hb ss ss' _ _ x x' l hx hx' hl (hll ▸ hl') with heq | cSub
        · exact .inl heq
        · exact .inr (cSub.mono fun m hm => by
            simp only [climbPreimages, hi, ↓reduceIte, hl, hl', List.mem_append, List.mem_cons] at hm ⊢
            rcases hm with hm | hm
            · exact .inl (.inr hm)
            · exact .inr (.inr hm))
      · exact .inr (c.mono fun m hm => by
          rcases hm with rfl | rfl <;> simp [climbPreimages, hi, hl, hl'])
    · rename_i hi; simp only [hi, ↓reduceIte] at h'
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨l', hl', he⟩ := Option.map_eq_some_iff.1 h'
      have hs := admissible_of_lt (Nat.lt_of_not_le hn.2)
      have hs' := admissible_of_lt (Nat.lt_of_not_le hn'.2)
      rcases binds_or_collides H hs' hs he with ⟨_, hll⟩ | c
      · rcases climb_binds hb ss ss' _ _ x x' l hx hx' hl (hll ▸ hl') with heq | cSub
        · exact .inl heq
        · exact .inr (cSub.mono fun m hm => by
            simp only [climbPreimages, hi, ↓reduceIte, hl, hl', List.mem_append, List.mem_cons] at hm ⊢
            rcases hm with hm | hm
            · exact .inl (.inr hm)
            · exact .inr (.inr hm))
      · exact .inr (c.mono fun m hm => by
          rcases hm with rfl | rfl <;> simp [climbPreimages, hi, hl, hl'])

/-! ## The map: values at positions -/

/-- The leaf of value `v` at position `j`. -/
def leaf (H : Hash) (j v : Nat) : Nat := digestWith H j v

theorem leaf_binds_scoped {H : Hash} {j a b : Nat} (hj : j < 2 ^ 256) (h : leaf H j a = leaf H j b) :
    a = b ∨ CollisionAmong H (fun m => m = preimage j a ∨ m = preimage j b) := by
  rcases binds_or_collides H (admissible_of_lt hj) (admissible_of_lt hj) h with ⟨_, hv⟩ | c
  · exact .inl hv
  · exact .inr c

/-- The leaves of a list of values. -/
@[expose] def leaves (H : Hash) (vs : List Nat) : List Nat := vs.mapIdx fun j v => leaf H j v

/-- The root of a list of values. -/
@[expose] def mapRoot (H : Hash) (vs : List Nat) : Nat := root H (leaves H vs)

/-- An opening: the map's size, the position, the value claimed there, and the siblings. -/
structure Opening where
  size : Nat
  index : Nat
  value : Nat
  path : List Nat
  deriving DecidableEq, Repr

/-- The honest opening of position `j`. -/
@[expose] def mapOpening (H : Hash) (vs : List Nat) (j : Nat) : Opening :=
  ⟨vs.length, j, vs.getD j 0, path H (leaves H vs) j⟩

/-- **An opening opens against a root.** -/
@[expose] def opens (H : Hash) (o : Opening) (r : Nat) : Bool :=
  Small o.index && climb H o.size o.index (leaf H o.index o.value) o.path == some r

theorem leaves_length (H : Hash) (vs : List Nat) : (leaves H vs).length = vs.length := by
  simp [leaves]

theorem leaves_small {H : Hash} (hb : Bounded H) (vs : List Nat) : ∀ x ∈ leaves H vs, x < 2 ^ 256 := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  simp only [leaves, List.getElem_mapIdx, leaf]
  exact hb _ _

theorem leaves_getD (H : Hash) (vs : List Nat) {j : Nat} (hj : j < vs.length) :
    (leaves H vs).getD j 0 = leaf H j (vs.getD j 0) := by
  simp [leaves, List.getD_eq_getElem?_getD, List.getElem?_mapIdx, List.getElem?_eq_getElem hj]

/-- **The honest opening of every position opens against the root.** -/
theorem opens_complete {H : Hash} (hb : Bounded H) (vs : List Nat) (j : Nat) (hj : j < vs.length)
    (hjs : j < 2 ^ 256) : opens H (mapOpening H vs j) (mapRoot H vs) = true := by
  have hc := climb_path hb (leaves H vs) (leaves_small hb vs) j (by rw [leaves_length]; exact hj)
  rw [leaves_length, leaves_getD H vs hj] at hc
  simp only [opens, mapOpening, mapRoot, hc, Small, hjs, decide_true, Bool.true_and, beq_self_eq_true]

/-- Finite list of `preimage` byte strings hashed when verifying `Opening` `o`. -/
def openingPreimages (H : Hash) (o : Opening) : List (List UInt8) :=
  preimage o.index o.value :: climbPreimages H o.size o.index (leaf H o.index o.value) o.path

theorem opens_binds_scoped {H : Hash} (hb : Bounded H) {o o' : Opening} {r : Nat} (h : opens H o r = true)
    (h' : opens H o' r = true) (hn : o.size = o'.size) (hi : o.index = o'.index) :
    o.value = o'.value ∨ CollisionAmong H (fun m => m ∈ openingPreimages H o ++ openingPreimages H o') := by
  simp only [opens, Bool.and_eq_true, beq_iff_eq, Small, decide_eq_true_eq] at h h'
  have h'c := h'.2; rw [← hn, ← hi] at h'c
  rcases climb_binds hb o.path o'.path o.size o.index _ _ r (hb _ _) (hb _ _) h.2 h'c with he | c
  · rcases binds_or_collides H (admissible_of_lt h.1) (admissible_of_lt h.1) he with ⟨_, hv⟩ | cLeaf
    · exact .inl hv
    · exact .inr (cLeaf.mono fun m hm => by
        rcases hm with rfl | rfl
        · simp [openingPreimages]
        · rw [hi]; simp [openingPreimages])
  · exact .inr (c.mono fun m hm => by
      simp only [openingPreimages, List.mem_append, List.mem_cons] at hm ⊢
      rcases hm with hm | hm
      · exact .inl (.inr hm)
      · rw [hn, hi] at hm; exact .inr (.inr hm))

/-- **An opening against a view's root carries the view's value**, or `H` collides on the finite
opening preimages. -/
theorem opens_view {H : Hash} (hb : Bounded H) (vs : List Nat) {o : Opening}
    (h : opens H o (mapRoot H vs) = true) (hn : o.size = vs.length) (hj : o.index < vs.length) :
    o.value = vs[o.index] ∨
      CollisionAmong H (fun m => m ∈ openingPreimages H o ++ openingPreimages H (mapOpening H vs o.index)) := by
  have hs : o.index < 2 ^ 256 := by
    simp only [opens, Bool.and_eq_true, Small, decide_eq_true_eq] at h; exact h.1
  have hc := opens_complete hb vs o.index hj hs
  rcases opens_binds_scoped hb h hc (by simp [mapOpening, hn]) rfl with he | c
  · left; rw [he]; simp [mapOpening, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · exact .inr c

/-! ## The commitment of a world's view -/

/-- A view committed by position: a public schema of keys, and each key's value at a world. -/
structure Commit (W Key : Type) where
  keys : List Key
  val : W → Key → Nat

namespace Commit
variable {W Key : Type}

/-- The view's values, in schema order. -/
@[expose] def values (C : Commit W Key) (w : W) : List Nat := C.keys.map (C.val w)

/-- **The view's root**: what a receipt is dated by. -/
@[expose] def dated (H : Hash) (C : Commit W Key) (w : W) : Nat := mapRoot H (C.values w)

/-- The opening of key `k`, if the schema has it. -/
@[expose] def opening [BEq Key] (H : Hash) (C : Commit W Key) (w : W) (k : Key) : Option Opening :=
  (C.keys.idxOf? k).map fun j => mapOpening H (C.values w) j

/-- **An honest opening opens against the dated root.** -/
theorem opening_opens [BEq Key] [LawfulBEq Key] {H : Hash} (hb : Bounded H) (C : Commit W Key) (w : W) (k : Key)
    {o : Opening} (h : C.opening H w k = some o) (hs : C.keys.length < 2 ^ 256) :
    opens H o (C.dated H w) = true := by
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
  have hjl : j < C.keys.length := (List.idxOf?_eq_some_iff.1 hj).1
  exact opens_complete hb _ j (by simp [values]; exact hjl) (Nat.lt_trans hjl hs)

/-- **An opening that opens against a world's dated root carries that world's value at that key**,
or the hash collides among the finite opening preimages. -/
theorem opens_val {H : Hash} (hb : Bounded H) (C : Commit W Key) (w : W) {o : Opening}
    (h : opens H o (C.dated H w) = true) (hn : o.size = C.keys.length) (hj : o.index < C.keys.length) :
    o.value = C.val w C.keys[o.index] ∨
      CollisionAmong H (fun m => m ∈ openingPreimages H o ++ openingPreimages H (mapOpening H (C.values w) o.index)) := by
  rcases opens_view hb (C.values w) h (by simp [values, hn]) (by simp [values, hj]) with he | c
  · left; rw [he]; simp [values]
  · exact .inr c

end Commit

/-! ## The refutable pole -/

/-- **Under the length hash, an opening lies**: the openings of values 1 and 3 at position 0 open
against the same roots. Binding is carried by the hash, not by the tree. -/
theorem lengthHash_opens_lie (n : Nat) (p : List Nat) (r : Nat) :
    opens lengthHash ⟨n, 0, 1, p⟩ r = opens lengthHash ⟨n, 0, 3, p⟩ r := by
  have : leaf lengthHash 0 1 = leaf lengthHash 0 3 :=
    Obend.Core.Digest.lengthHash_binding_fails 0 1 3 (by decide)
  simp only [opens, this]

/-! ## Batch Merkle Multi-Proof Inclusion Verification (`MerkleBatchProof`, `verifyMerkleBatchProof`) -/

/-- A single `(leafIndex, leafDigest, auditPath)` entry in a batch Merkle inclusion proof. -/
structure MerkleBatchEntry where
  leafIndex : Nat
  leafDigest : Nat
  auditPath : List Nat
  deriving DecidableEq, Repr

/-- A batch Merkle inclusion proof for a tree of `treeSize` leaves, carrying a list of
`(leafIndex, leafDigest, auditPath)` entries verified against a shared `expectedRoot`. -/
structure MerkleBatchProof where
  treeSize : Nat
  entries : List MerkleBatchEntry
  deriving DecidableEq, Repr

/-- Single-leaf Merkle inclusion verifier for a `MerkleBatchEntry` against `expectedRoot`
in a tree of `treeSize` leaves. -/
@[expose] def verifySingleMerkleLeaf (H : Hash) (treeSize : Nat) (e : MerkleBatchEntry)
    (expectedRoot : Nat) : Bool :=
  Small e.leafIndex && Small e.leafDigest &&
    (climb H treeSize e.leafIndex e.leafDigest e.auditPath == some expectedRoot)

/-- Check that a list of leaf indices is pairwise distinct (contains no duplicate index). -/
def indicesPairwiseDistinct : List Nat → Bool
  | [] => true
  | idx :: rest => !rest.contains idx && indicesPairwiseDistinct rest

/-- `indicesPairwiseDistinct` decides `List.Nodup`. -/
theorem indicesPairwiseDistinct_iff_nodup (idxs : List Nat) :
    indicesPairwiseDistinct idxs = true ↔ idxs.Nodup := by
  induction idxs with
  | nil => simp [indicesPairwiseDistinct]
  | cons x xs ih =>
    have hNotMem : (!xs.contains x) = true ↔ x ∉ xs := by
      constructor
      · intro h hx
        have hc : xs.contains x = true := List.contains_iff_mem.2 hx
        rw [hc] at h; cases h
      · intro hx
        cases hc : xs.contains x
        · rfl
        · exfalso; exact hx (List.contains_iff_mem.1 hc)
    simp only [indicesPairwiseDistinct, Bool.and_eq_true, hNotMem, List.nodup_cons, ih]

/-- **Batch Merkle Inclusion Verification (`verifyMerkleBatchProof`)**:
verifies that a list of `(leafIndex, leafDigest, auditPath)` entries in `batch` have pairwise
distinct `leafIndex`es and all resolve to the same `expectedRoot`. -/
@[expose] def verifyMerkleBatchProof (H : Hash) (batch : MerkleBatchProof) (expectedRoot : Nat) : Bool :=
  indicesPairwiseDistinct (batch.entries.map MerkleBatchEntry.leafIndex) &&
  batch.entries.all (fun e => verifySingleMerkleLeaf H batch.treeSize e expectedRoot)

/-- **Soundness of Batch Merkle Verification (`verifyMerkleBatchProof_sound`)**:
If `verifyMerkleBatchProof H batch expectedRoot = true`, then:
1. All `leafIndex` values across `batch.entries` are pairwise distinct (`List.Nodup`), and
2. Every individual entry `e ∈ batch.entries` satisfies single-leaf Merkle verification
   (`verifySingleMerkleLeaf H batch.treeSize e expectedRoot = true` and
   `climb H batch.treeSize e.leafIndex e.leafDigest e.auditPath = some expectedRoot`). -/
theorem verifyMerkleBatchProof_sound (H : Hash) (batch : MerkleBatchProof) (expectedRoot : Nat)
    (hBatch : verifyMerkleBatchProof H batch expectedRoot = true) :
    (batch.entries.map MerkleBatchEntry.leafIndex).Nodup ∧
    ∀ e ∈ batch.entries,
      verifySingleMerkleLeaf H batch.treeSize e expectedRoot = true ∧
      climb H batch.treeSize e.leafIndex e.leafDigest e.auditPath = some expectedRoot := by
  simp only [verifyMerkleBatchProof, Bool.and_eq_true, List.all_eq_true] at hBatch
  refine ⟨(indicesPairwiseDistinct_iff_nodup _).1 hBatch.1, fun e he => ?_⟩
  have hSingle := hBatch.2 e he
  refine ⟨hSingle, ?_⟩
  simp only [verifySingleMerkleLeaf, Bool.and_eq_true, beq_iff_eq] at hSingle
  exact hSingle.2

/-- Construct the honest `MerkleBatchEntry` for leaf position `i` of leaf list `l`. -/
@[expose] def honestBatchEntry (H : Hash) (l : List Nat) (i : Nat) : MerkleBatchEntry :=
  { leafIndex := i
    leafDigest := l.getD i 0
    auditPath := path H l i }

/-- Honest single-leaf completeness for `honestBatchEntry`. -/
theorem verifySingleMerkleLeaf_honest {H : Hash} (hb : Bounded H) (l : List Nat)
    (hl : ∀ x ∈ l, x < 2 ^ 256) (i : Nat) (hi : i < l.length) (his : i < 2 ^ 256) :
    verifySingleMerkleLeaf H l.length (honestBatchEntry H l i) (root H l) = true := by
  have hc := climb_path hb l hl i hi
  have hlt : l.getD i 0 < 2 ^ 256 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hl l[i] (List.getElem_mem hi)
  simp only [verifySingleMerkleLeaf, honestBatchEntry, Small, his, hlt, decide_true,
    Bool.true_and, hc, beq_self_eq_true]

/-- Construct an honest `MerkleBatchProof` for a list of leaf positions `idxs` in leaf list `l`. -/
@[expose] def honestBatchProof (H : Hash) (l : List Nat) (idxs : List Nat) : MerkleBatchProof :=
  { treeSize := l.length
    entries := idxs.map (honestBatchEntry H l) }

/-- **Batch Completeness (`verifyMerkleBatchProof_honest`)**:
For any bounded hash `H`, digest-sized leaf list `l` (`l.length < 2 ^ 256`), and pairwise-distinct
leaf positions `idxs` (`idxs.Nodup`, `∀ i ∈ idxs, i < l.length`), `honestBatchProof H l idxs`
verifies against `root H l`. -/
theorem verifyMerkleBatchProof_honest {H : Hash} (hb : Bounded H) (l : List Nat)
    (hl : ∀ x ∈ l, x < 2 ^ 256) (hs : l.length < 2 ^ 256)
    (idxs : List Nat) (hNodup : idxs.Nodup) (hBounds : ∀ i ∈ idxs, i < l.length) :
    verifyMerkleBatchProof H (honestBatchProof H l idxs) (root H l) = true := by
  simp only [verifyMerkleBatchProof, honestBatchProof, Bool.and_eq_true,
    indicesPairwiseDistinct_iff_nodup, List.map_map, List.all_map, List.all_eq_true]
  have hId : (MerkleBatchEntry.leafIndex ∘ honestBatchEntry H l) = id := by
    funext i; rfl
  rw [hId, List.map_id]
  refine ⟨hNodup, fun i hi => ?_⟩
  have hlt : i < l.length := hBounds i hi
  exact verifySingleMerkleLeaf_honest hb l hl i hlt (Nat.lt_trans hlt hs)

theorem verifyMerkleBatchProof_binds_scoped {H : Hash} (hb : Bounded H) (l : List Nat)
    (hl : ∀ x ∈ l, x < 2 ^ 256) {batch : MerkleBatchProof}
    (hBatch : verifyMerkleBatchProof H batch (root H l) = true) (hSize : batch.treeSize = l.length)
    {e : MerkleBatchEntry} (he : e ∈ batch.entries) (hi : e.leafIndex < l.length) :
    e.leafDigest = l[e.leafIndex] ∨
      CollisionAmong H (fun m =>
        m ∈ climbPreimages H l.length e.leafIndex e.leafDigest e.auditPath ++
            climbPreimages H l.length e.leafIndex (l.getD e.leafIndex 0) (path H l e.leafIndex)) := by
  obtain ⟨_, hEntries⟩ := verifyMerkleBatchProof_sound H batch (root H l) hBatch
  obtain ⟨hSingle, hClimb⟩ := hEntries e he
  simp only [verifySingleMerkleLeaf, Bool.and_eq_true, Small, decide_eq_true_eq] at hSingle
  have hDigestSmall : e.leafDigest < 2 ^ 256 := hSingle.1.2
  have hHonestClimb := climb_path hb l hl e.leafIndex hi
  have hLeafSmall : l.getD e.leafIndex 0 < 2 ^ 256 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact hl l[e.leafIndex] (List.getElem_mem hi)
  rw [hSize] at hClimb
  rcases climb_binds hb e.auditPath (path H l e.leafIndex) l.length e.leafIndex
      e.leafDigest (l.getD e.leafIndex 0) (root H l) hDigestSmall hLeafSmall hClimb hHonestClimb with hEq | hCol
  · left; rw [hEq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  · exact .inr hCol

/-! ## 256-Bit `cSHAKE256` Length-Framed Salted Blinded Merkle Multiproofs & Constructive Collision Extractors -/

/-- Fuel-bounded LEB128 variable-length natural encoding. -/
def leb128Aux : Nat → Nat → List UInt8
  | 0, v => [UInt8.ofNat (v % 128)]
  | fuel + 1, v => if v < 128 then [UInt8.ofNat v] else UInt8.ofNat (128 + v % 128) :: leb128Aux fuel (v / 128)
/-- Canonical self-delimiting LEB128 encoding of `n : Nat`. -/
def leb128 (n : Nat) : List UInt8 := leb128Aux n n
theorem leb128_length_pos (n : Nat) : 0 < (leb128 n).length := by
  unfold leb128; cases n with | zero => simp [leb128Aux] | succ _ => simp only [leb128Aux]; split <;> simp
private theorem uint8_toNat_of_lt {k : Nat} (hk : k < 256) : (UInt8.ofNat k).toNat = k := by
  rw [UInt8.toNat_ofNat']; have h8 : (2 : Nat) ^ 8 = 256 := by decide
  rw [h8]; exact Nat.mod_eq_of_lt hk
theorem leb128Aux_prefix_inj :
    ∀ {f₁ f₂ n₁ n₂ : Nat} {r₁ r₂ : List UInt8},
      n₁ ≤ f₁ → n₂ ≤ f₂ → leb128Aux f₁ n₁ ++ r₁ = leb128Aux f₂ n₂ ++ r₂ → n₁ = n₂ ∧ r₁ = r₂
  | 0, 0, n₁, n₂, _, _, hn₁, hn₂, h => by
    have z₁ : n₁ = 0 := by omega
    have z₂ : n₂ = 0 := by omega
    subst z₁ z₂; simp only [leb128Aux, List.singleton_append, List.cons.injEq] at h; exact ⟨rfl, h.2⟩
  | 0, _ + 1, n₁, n₂, _, _, hn₁, _, h => by
    have z₁ : n₁ = 0 := by omega
    subst z₁; simp only [leb128Aux, List.singleton_append] at h
    if hlt : n₂ < 128 then
      simp only [hlt, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
      have hb := congrArg UInt8.toNat h.1
      rw [uint8_toNat_of_lt (by decide), uint8_toNat_of_lt (by omega)] at hb; exact ⟨hb, h.2⟩
    else
      simp only [hlt, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb := congrArg UInt8.toNat h.1
      rw [uint8_toNat_of_lt (by decide), uint8_toNat_of_lt (by omega)] at hb; omega
  | _ + 1, 0, n₁, n₂, _, _, _, hn₂, h => by
    have z₂ : n₂ = 0 := by omega
    subst z₂; simp only [leb128Aux, List.singleton_append] at h
    if hlt : n₁ < 128 then
      simp only [hlt, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
      have hb := congrArg UInt8.toNat h.1
      rw [uint8_toNat_of_lt (by omega), uint8_toNat_of_lt (by decide)] at hb; exact ⟨hb, h.2⟩
    else
      simp only [hlt, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb := congrArg UInt8.toNat h.1
      rw [uint8_toNat_of_lt (by omega), uint8_toNat_of_lt (by decide)] at hb; omega
  | _ + 1, _ + 1, n₁, n₂, _, _, hn₁, hn₂, h => by
    simp only [leb128Aux] at h
    if h₁ : n₁ < 128 then
      if h₂ : n₂ < 128 then
        simp only [h₁, h₂, ↓reduceIte, List.singleton_append, List.cons.injEq] at h
        have hb := congrArg UInt8.toNat h.1
        rw [uint8_toNat_of_lt (by omega), uint8_toNat_of_lt (by omega)] at hb; exact ⟨hb, h.2⟩
      else
        simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
        have hb := congrArg UInt8.toNat h.1
        rw [uint8_toNat_of_lt (by omega), uint8_toNat_of_lt (by omega)] at hb; omega
    else if h₂ : n₂ < 128 then
      simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb := congrArg UInt8.toNat h.1
      rw [uint8_toNat_of_lt (by omega), uint8_toNat_of_lt (by omega)] at hb; omega
    else
      simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at h
      have hb := congrArg UInt8.toNat h.1
      rw [uint8_toNat_of_lt (by omega), uint8_toNat_of_lt (by omega)] at hb
      obtain ⟨hdiv, hrest⟩ := leb128Aux_prefix_inj (by omega) (by omega) h.2
      exact ⟨by omega, hrest⟩
theorem leb128_prefix_inj {n₁ n₂ : Nat} {r₁ r₂ : List UInt8} (h : leb128 n₁ ++ r₁ = leb128 n₂ ++ r₂) :
    n₁ = n₂ ∧ r₁ = r₂ := leb128Aux_prefix_inj (Nat.le_refl n₁) (Nat.le_refl n₂) h
theorem leb128_injective {n₁ n₂ : Nat} (h : leb128 n₁ = leb128 n₂) : n₁ = n₂ :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1
def encodeListField (xs : List UInt8) : List UInt8 := leb128 xs.length ++ xs
theorem encodeListField_prefix_inj {a₁ a₂ r₁ r₂ : List UInt8}
    (h : encodeListField a₁ ++ r₁ = encodeListField a₂ ++ r₂) : a₁ = a₂ ∧ r₁ = r₂ := by
  simp only [encodeListField, List.append_assoc] at h
  obtain ⟨hlen, htail⟩ := leb128_prefix_inj h; exact List.append_inj htail hlen
def encodeFields (fs : List (List UInt8)) : List UInt8 := fs.flatMap encodeListField
theorem encodeFields_injective : ∀ (fs₁ fs₂ : List (List UInt8)),
    encodeFields fs₁ = encodeFields fs₂ → fs₁ = fs₂
  | [], [], _ => rfl
  | [], b :: bs, h => by
    have hlen : (encodeFields (b :: bs)).length = 0 := by rw [← h]; rfl
    have hpos := leb128_length_pos b.length
    simp only [encodeFields, List.flatMap_cons, encodeListField, List.length_append] at hlen; omega
  | a :: as, [], h => by
    have hlen : (encodeFields (a :: as)).length = 0 := by rw [h]; rfl
    have hpos := leb128_length_pos a.length
    simp only [encodeFields, List.flatMap_cons, encodeListField, List.length_append] at hlen; omega
  | a :: as, b :: bs, h => by
    simp only [encodeFields, List.flatMap_cons] at h
    obtain ⟨hab, hrest⟩ := encodeListField_prefix_inj h; rw [hab, encodeFields_injective as bs hrest]
abbrev Digest256 := BitVec 256
def bytesOfDigest256 (d : Digest256) : List UInt8 := be 32 d.toNat
theorem bytesOfDigest256_injective {d₁ d₂ : Digest256} (h : bytesOfDigest256 d₁ = bytesOfDigest256 d₂) : d₁ = d₂ := by
  have h32 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  exact BitVec.eq_of_toNat_eq (be_injective (h32 ▸ d₁.isLt) (h32 ▸ d₂.isLt) h)
def multiproofCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x52, 0x45, 0x43, 0x45, 0x49, 0x50, 0x54, 0x2e,
   0x4d, 0x55, 0x4c, 0x54, 0x49, 0x50, 0x52, 0x4f, 0x4f, 0x46, 0x2f, 0x76, 0x31]
def cshakeMultiproofHash : Hash := Obend.Digest.Cshake256.cshake256Bytes multiproofCustomization
theorem cshakeMultiproofHash_length_32 (msg : List UInt8) : (cshakeMultiproofHash msg).length = 32 := by
  simp [cshakeMultiproofHash]
theorem deployed_length_32 (msg : List UInt8) : (deployed msg).length = 32 := by simp [deployed]
def hashBytes256 (H : Hash) (msg : List UInt8) : Digest256 := BitVec.ofNat 256 (ofBE ((H msg).take 32))
/-- `Type`-valued finite-scope collision witness (`0 Classical.choice`, zero pigeonhole vacuity). -/
structure ScopedCollision256 (H : Hash) (preimages : List (List UInt8)) where
  msg₁ : List UInt8
  msg₂ : List UInt8
  mem₁ : msg₁ ∈ preimages
  mem₂ : msg₂ ∈ preimages
  ne   : msg₁ ≠ msg₂
  eq256 : hashBytes256 H msg₁ = hashBytes256 H msg₂
  deriving DecidableEq, Repr
def ScopedCollision256.mono {H : Hash} {S₁ S₂ : List (List UInt8)}
    (hSub : ∀ x, x ∈ S₁ → x ∈ S₂) (c : ScopedCollision256 H S₁) : ScopedCollision256 H S₂ :=
  ⟨c.msg₁, c.msg₂, hSub c.msg₁ c.mem₁, hSub c.msg₂ c.mem₂, c.ne, c.eq256⟩
theorem ScopedCollision256.toCollisionAmong {H : Hash} {S : List (List UInt8)}
    (hLen : ∀ m ∈ S, (H m).length = 32) (c : ScopedCollision256 H S) : CollisionAmong H (fun x => x ∈ S) := by
  have hl₁ := hLen c.msg₁ c.mem₁; have hl₂ := hLen c.msg₂ c.mem₂
  have htake₁ : (H c.msg₁).take 32 = H c.msg₁ := List.take_of_length_le (by omega)
  have htake₂ : (H c.msg₂).take 32 = H c.msg₂ := List.take_of_length_le (by omega)
  have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  have hlt₁ : ofBE (H c.msg₁) < 2 ^ 256 := by have := ofBE_lt (H c.msg₁); rwa [hl₁, h256] at this
  have hlt₂ : ofBE (H c.msg₂) < 2 ^ 256 := by have := ofBE_lt (H c.msg₂); rwa [hl₂, h256] at this
  have hnat := congrArg BitVec.toNat c.eq256
  simp only [hashBytes256, htake₁, htake₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] at hnat
  exact ⟨c.msg₁, c.msg₂, c.mem₁, c.mem₂, c.ne, hnat⟩
def emptyPreimage256 : List UInt8 := encodeFields [[0x02]]
def leafPreimage256 (idx : Nat) (salt : Digest256) (payload : List UInt8) : List UInt8 :=
  encodeFields [[0x00], leb128 idx, bytesOfDigest256 salt, payload]
def internalPreimage256 (spanSize startIdx : Nat) (left right : Digest256) : List UInt8 :=
  encodeFields [[0x01], leb128 spanSize, leb128 startIdx, bytesOfDigest256 left, bytesOfDigest256 right]
theorem leafPreimage256_injective {i₁ i₂ : Nat} {s₁ s₂ : Digest256} {p₁ p₂ : List UInt8}
    (h : leafPreimage256 i₁ s₁ p₁ = leafPreimage256 i₂ s₂ p₂) : i₁ = i₂ ∧ s₁ = s₂ ∧ p₁ = p₂ := by
  have hf := encodeFields_injective _ _ h; simp only [List.cons.injEq, and_true, true_and] at hf
  exact ⟨leb128_injective hf.1, bytesOfDigest256_injective hf.2.1, hf.2.2⟩
theorem internalPreimage256_injective {sz₁ sz₂ st₁ st₂ : Nat} {l₁ l₂ r₁ r₂ : Digest256}
    (h : internalPreimage256 sz₁ st₁ l₁ r₁ = internalPreimage256 sz₂ st₂ l₂ r₂) :
    sz₁ = sz₂ ∧ st₁ = st₂ ∧ l₁ = l₂ ∧ r₁ = r₂ := by
  have hf := encodeFields_injective _ _ h; simp only [List.cons.injEq, and_true, true_and] at hf
  exact ⟨leb128_injective hf.1, leb128_injective hf.2.1,
    bytesOfDigest256_injective hf.2.2.1, bytesOfDigest256_injective hf.2.2.2⟩
theorem leaf_ne_internal_preimage256 (idx : Nat) (salt : Digest256) (payload : List UInt8)
    (spanSize startIdx : Nat) (left right : Digest256) :
    leafPreimage256 idx salt payload ≠ internalPreimage256 spanSize startIdx left right := by
  intro h; have hf := encodeFields_injective _ _ h; simp at hf
theorem leaf_ne_empty_preimage256 (idx : Nat) (salt : Digest256) (payload : List UInt8) :
    leafPreimage256 idx salt payload ≠ emptyPreimage256 := by
  intro h; have hf := encodeFields_injective _ _ h; simp at hf
theorem internal_ne_empty_preimage256 (spanSize startIdx : Nat) (left right : Digest256) :
    internalPreimage256 spanSize startIdx left right ≠ emptyPreimage256 := by
  intro h; have hf := encodeFields_injective _ _ h; simp at hf

/-! ### Salted 256-Bit Merkle Tree & Salted Blinded Multiproofs -/

/-- A salted leaf carrying a 32-byte (`Digest256`) blinding salt and arbitrary byte payload. -/
structure SaltedLeaf256 where
  salt : Digest256
  payload : List UInt8
  deriving DecidableEq, Repr

/-- Default leaf fallback for total indexing. -/
def defaultSaltedLeaf256 : SaltedLeaf256 := ⟨0#256, []⟩

/-- Compute the 256-bit salted subtree root over `entries` starting at global leaf offset `startIdx`. -/
def saltedSubtreeRoot256 (H : Hash) (startIdx : Nat) (entries : List SaltedLeaf256) : Digest256 :=
  if entries.length = 0 then
    hashBytes256 H emptyPreimage256
  else if entries.length = 1 then
    let e := entries.getD 0 defaultSaltedLeaf256
    hashBytes256 H (leafPreimage256 startIdx e.salt e.payload)
  else
    let mid := entries.length / 2
    let lRoot := saltedSubtreeRoot256 H startIdx (entries.take mid)
    let rRoot := saltedSubtreeRoot256 H (startIdx + mid) (entries.drop mid)
    hashBytes256 H (internalPreimage256 entries.length startIdx lRoot rRoot)
termination_by entries.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- Canonical 256-bit salted Merkle root of `entries`. -/
def saltedTreeRoot256 (H : Hash) (entries : List SaltedLeaf256) : Digest256 :=
  saltedSubtreeRoot256 H 0 entries

/-- Multiproof tree with shared internal nodes and redacted (`.blinded`) 32-byte sibling commitments. -/
inductive BlindedNode256 where
  | empty : BlindedNode256
  | blinded (commitment : Digest256) : BlindedNode256
  | openedLeaf (idx : Nat) (salt : Digest256) (payload : List UInt8) : BlindedNode256
  | branch (left right : BlindedNode256) : BlindedNode256
  deriving DecidableEq, Repr

/-- Count shared internal `.branch` hash evaluations in a `BlindedNode256`. -/
def BlindedNode256.branchCount : BlindedNode256 → Nat
  | .empty | .blinded _ | .openedLeaf _ _ _ => 0
  | .branch l r => 1 + l.branchCount + r.branchCount
/-- Count redacted 32-byte `.blinded` subtree commitments in a `BlindedNode256`. -/
def BlindedNode256.blindedCount : BlindedNode256 → Nat
  | .empty | .openedLeaf _ _ _ => 0
  | .blinded _ => 1
  | .branch l r => l.blindedCount + r.blindedCount
/-- Count opened leaves in a `BlindedNode256`. -/
def BlindedNode256.openedCount : BlindedNode256 → Nat
  | .empty | .blinded _ => 0
  | .openedLeaf _ _ _ => 1
  | .branch l r => l.openedCount + r.openedCount
theorem BlindedNode256.blindedCount_le_branchCount_succ :
    ∀ (node : BlindedNode256), node.blindedCount ≤ node.branchCount + 1
  | .empty | .blinded _ | .openedLeaf _ _ _ => by simp [blindedCount, branchCount]
  | .branch l r => by
    have hl := l.blindedCount_le_branchCount_succ; have hr := r.blindedCount_le_branchCount_succ
    simp only [blindedCount, branchCount]; omega
/-- A salted blinded Merkle multiproof opening `queriedIndices` in a tree of `treeSize` leaves. -/
structure BlindedMultiproof256 where
  treeSize : Nat
  queriedIndices : List Nat
  tree : BlindedNode256
  deriving DecidableEq, Repr
/-- Strictly ascending check on `Nat` indices (enforcing canonical order and rejecting duplicates). -/
def strictlyAscending : List Nat → Bool
  | [] | [_] => true
  | i :: j :: rest => decide (i < j) && strictlyAscending (j :: rest)
/-- Check that `idxs` is strictly ascending and every index is `< treeSize`. -/
def strictlyAscendingInBounds (treeSize : Nat) (idxs : List Nat) : Bool :=
  strictlyAscending idxs && idxs.all (fun i => decide (i < treeSize))

theorem strictlyAscending_iff_pairwise :
    ∀ (idxs : List Nat), strictlyAscending idxs = true ↔ idxs.Pairwise (· < ·)
  | [] | [_] => by simp [strictlyAscending]
  | i :: j :: rest => by
    simp only [strictlyAscending, Bool.and_eq_true, decide_eq_true_eq,
      strictlyAscending_iff_pairwise (j :: rest), List.pairwise_cons]
    refine ⟨fun ⟨hij, hjr, hrest⟩ => ⟨fun x hx => ?_, hjr, hrest⟩,
            fun ⟨hir, hjr, hrest⟩ => ⟨hir j List.mem_cons_self, hjr, hrest⟩⟩
    rcases List.mem_cons.1 hx with rfl | hmem
    · exact hij
    · exact Nat.lt_trans hij (hjr x hmem)

theorem strictlyAscending_nodup {idxs : List Nat} (h : strictlyAscending idxs = true) :
    idxs.Nodup :=
  ((strictlyAscending_iff_pairwise idxs).1 h).imp (fun hlt heq => by subst heq; exact Nat.lt_irrefl _ hlt)

theorem filter_lt_append_filter_ge (cut : Nat) :
    ∀ (q : List Nat), q.Pairwise (· < ·) →
      q.filter (fun i => decide (i < cut)) ++ q.filter (fun i => decide (cut ≤ i)) = q
  | [], _ => rfl
  | x :: xs, hp => by
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.1 hp
    by_cases hlt : x < cut
    · have hge_false : decide (cut ≤ x) = false := decide_eq_false (by omega)
      simp only [List.filter_cons, decide_eq_true hlt, hge_false, Bool.false_eq_true, ↓reduceIte,
        List.cons_append, filter_lt_append_filter_ge cut xs hxs]
    · have hge : cut ≤ x := by omega
      have hnone : xs.filter (fun i => decide (i < cut)) = [] :=
        List.filter_eq_nil_iff.2 fun y hy => by have := hx y hy; simp; omega
      have hall : xs.filter (fun i => decide (cut ≤ i)) = xs :=
        List.filter_eq_self.2 fun y hy => by have := hx y hy; simp; omega
      simp only [List.filter_cons, decide_eq_false hlt, decide_eq_true hge, Bool.false_eq_true,
        ↓reduceIte, hnone, hall, List.nil_append]

/-- Structurally evaluate a `BlindedNode256` against `(spanSize, startIdx)`, enforcing exact
binary split geometry and non-empty branch demand (rejecting uncollapsed all-blinded branches). -/
def evalBlindedNode256 (H : Hash) :
    BlindedNode256 → Nat → Nat → Option (Digest256 × List (Nat × SaltedLeaf256))
  | .empty, spanSize, _ =>
    if spanSize == 0 then some (hashBytes256 H emptyPreimage256, []) else none
  | .blinded c, spanSize, _ =>
    if decide (0 < spanSize) then some (c, []) else none
  | .openedLeaf idx salt payload, spanSize, startIdx =>
    if spanSize == 1 && idx == startIdx then
      some (hashBytes256 H (leafPreimage256 startIdx salt payload), [(idx, ⟨salt, payload⟩)])
    else none
  | .branch left right, spanSize, startIdx =>
    if decide (spanSize < 2) then none
    else
      let mid := spanSize / 2
      match evalBlindedNode256 H left mid startIdx,
            evalBlindedNode256 H right (spanSize - mid) (startIdx + mid) with
      | some (lRoot, lOpened), some (rRoot, rOpened) =>
        if lOpened.isEmpty && rOpened.isEmpty then none
        else
          some (hashBytes256 H (internalPreimage256 spanSize startIdx lRoot rRoot),
                lOpened ++ rOpened)
      | _, _ => none

/-- **Salted Blinded 256-Bit Merkle Multiproof Verifier (`verifyBlindedMultiproof256`)**:
verifies strict index ordering/bounds, structural span-bound tree evaluation against `expectedRoot`,
and exact index-set agreement between opened leaves and `proof.queriedIndices`. -/
def verifyBlindedMultiproof256 (H : Hash) (proof : BlindedMultiproof256)
    (expectedRoot : Digest256) : Bool :=
  strictlyAscendingInBounds proof.treeSize proof.queriedIndices &&
  match evalBlindedNode256 H proof.tree proof.treeSize 0 with
  | some (r, opened) => r == expectedRoot && opened.map Prod.fst == proof.queriedIndices
  | none => false

/-- Inhabitedness witness for `verifyBlindedMultiproof256` (holds symbolically for every `H : Hash`,
including `cshakeMultiproofHash` and `deployed`). -/
theorem verifyBlindedMultiproof256_inhabited (H : Hash) :
    verifyBlindedMultiproof256 H
      { treeSize := 1
        queriedIndices := [0]
        tree := .openedLeaf 0 0#256 [0x42] }
      (saltedTreeRoot256 H [⟨0#256, [0x42]⟩]) = true := by
  unfold verifyBlindedMultiproof256 saltedTreeRoot256 saltedSubtreeRoot256
    evalBlindedNode256 strictlyAscendingInBounds strictlyAscending defaultSaltedLeaf256
  simp

/-- Duplicate leaf indices in `proof.queriedIndices` are unconditionally rejected. -/
theorem verifyBlindedMultiproof256_rejects_duplicates (H : Hash) (proof : BlindedMultiproof256)
    (expectedRoot : Digest256) (hDup : ¬ proof.queriedIndices.Nodup) :
    verifyBlindedMultiproof256 H proof expectedRoot = false := by
  cases hv : verifyBlindedMultiproof256 H proof expectedRoot with
  | false => rfl
  | true =>
    unfold verifyBlindedMultiproof256 strictlyAscendingInBounds at hv
    simp only [Bool.and_eq_true] at hv
    exact absurd (strictlyAscending_nodup hv.1.1) hDup

/-- Build the canonical minimal `BlindedNode256` over `entries` at offset `startIdx` for `queried`,
folding every unqueried sibling subtree into a single 32-byte `.blinded` commitment and sharing
internal `.branch` nodes across multi-leaf queries ($O(k \log(N/k))$). -/
def buildBlindedNode256 (H : Hash) (startIdx : Nat) (entries : List SaltedLeaf256)
    (queried : List Nat) : BlindedNode256 :=
  if entries.length = 0 then
    .empty
  else if queried.isEmpty then
    .blinded (saltedSubtreeRoot256 H startIdx entries)
  else if entries.length = 1 then
    let e := entries.getD 0 defaultSaltedLeaf256
    .openedLeaf startIdx e.salt e.payload
  else
    let mid := entries.length / 2
    let qLeft := queried.filter (fun i => decide (i < startIdx + mid))
    let qRight := queried.filter (fun i => decide (startIdx + mid ≤ i))
    .branch
      (buildBlindedNode256 H startIdx (entries.take mid) qLeft)
      (buildBlindedNode256 H (startIdx + mid) (entries.drop mid) qRight)
termination_by entries.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- Build the canonical `BlindedMultiproof256` for `queriedIndices` over `entries`. -/
def buildBlindedMultiproof256 (H : Hash) (entries : List SaltedLeaf256)
    (queriedIndices : List Nat) : BlindedMultiproof256 :=
  { treeSize := entries.length
    queriedIndices := queriedIndices
    tree := buildBlindedNode256 H 0 entries queriedIndices }

@[simp] theorem buildBlindedMultiproof256_treeSize (H : Hash) (entries : List SaltedLeaf256)
    (q : List Nat) : (buildBlindedMultiproof256 H entries q).treeSize = entries.length := by rfl
@[simp] theorem buildBlindedMultiproof256_queriedIndices (H : Hash) (entries : List SaltedLeaf256)
    (q : List Nat) : (buildBlindedMultiproof256 H entries q).queriedIndices = q := by rfl

/-- Every nonempty unqueried subtree compresses to a single `.blinded` 32-byte commitment
(`branchCount = 0`, `blindedCount = 1`). -/
theorem buildBlindedNode256_unqueried_eq_blinded (H : Hash) (startIdx : Nat)
    (entries : List SaltedLeaf256) (hne : entries ≠ []) :
    buildBlindedNode256 H startIdx entries [] =
      .blinded (saltedSubtreeRoot256 H startIdx entries) := by
  have hlen : entries.length ≠ 0 := by
    intro h0; exact hne (List.eq_nil_of_length_eq_zero h0)
  rw [buildBlindedNode256]
  simp [hlen]

/-- **Shared-Internal-Node Deduplication (`buildBlindedNode256_shared_root_dedup`)**:
When `queried` spans both halves of `entries` (`entries.length ≥ 2`), the root internal node is
materialized **once** (`branchCount = 1 + left.branchCount + right.branchCount`), strictly saving
`queried.length - 1` root hashes compared to independent single-leaf openings. -/
theorem buildBlindedNode256_shared_root_dedup (H : Hash) (startIdx : Nat)
    (entries : List SaltedLeaf256) (queried : List Nat)
    (hge2 : 2 ≤ entries.length) (hne : queried ≠ []) :
    let mid := entries.length / 2
    let qLeft := queried.filter (fun i => decide (i < startIdx + mid))
    let qRight := queried.filter (fun i => decide (startIdx + mid ≤ i))
    (buildBlindedNode256 H startIdx entries queried).branchCount =
      1 + (buildBlindedNode256 H startIdx (entries.take mid) qLeft).branchCount +
          (buildBlindedNode256 H (startIdx + mid) (entries.drop mid) qRight).branchCount := by
  have h0 : entries.length ≠ 0 := by omega
  have h1 : entries.length ≠ 1 := by omega
  have hq : queried.isEmpty = false := List.isEmpty_eq_false_iff.2 hne
  dsimp only
  conv => lhs; rw [buildBlindedNode256]
  simp [h0, h1, hq, BlindedNode256.branchCount]

private theorem getD_take_salted (entries : List SaltedLeaf256) {k i : Nat} (h : i < k) :
    (entries.take k).getD i defaultSaltedLeaf256 = entries.getD i defaultSaltedLeaf256 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ↓reduceIte]

private theorem getD_drop_salted (entries : List SaltedLeaf256) (k i : Nat) :
    (entries.drop k).getD i defaultSaltedLeaf256 = entries.getD (k + i) defaultSaltedLeaf256 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Subtree evaluation completeness for `buildBlindedNode256`. -/
theorem evalBlindedNode256_build (H : Hash) :
    ∀ (entries : List SaltedLeaf256) (startIdx : Nat) (queried : List Nat),
      queried.Pairwise (· < ·) →
      (∀ i ∈ queried, startIdx ≤ i ∧ i < startIdx + entries.length) →
      evalBlindedNode256 H (buildBlindedNode256 H startIdx entries queried) entries.length startIdx =
        some (saltedSubtreeRoot256 H startIdx entries,
              queried.map (fun i => (i, entries.getD (i - startIdx) defaultSaltedLeaf256))) := by
  intro entries
  induction entries using (measure List.length).wf.induction with
  | h entries ih =>
    intro startIdx queried hSort hRange
    by_cases h0 : entries.length = 0
    · have hqNil : queried = [] := by
        cases queried with
        | nil => rfl
        | cons i _ =>
          have hi := hRange i List.mem_cons_self
          omega
      subst hqNil
      rw [buildBlindedNode256, saltedSubtreeRoot256]
      simp [h0, evalBlindedNode256]
    · by_cases hqEmpty : queried.isEmpty = true
      · have hqNil : queried = [] := List.isEmpty_iff.1 hqEmpty
        subst hqNil
        have hpos : 0 < entries.length := by omega
        rw [buildBlindedNode256]
        simp [h0, evalBlindedNode256, hpos]
      · simp only [Bool.not_eq_true] at hqEmpty
        have hqNe : queried ≠ [] := List.isEmpty_eq_false_iff.1 hqEmpty
        by_cases h1 : entries.length = 1
        · have hqSingle : queried = [startIdx] := by
            cases queried with
            | nil => exact absurd rfl hqNe
            | cons i rest =>
              have hi := hRange i List.mem_cons_self
              have hiEq : i = startIdx := by omega
              subst hiEq
              cases rest with
              | nil => rfl
              | cons j _ =>
                obtain ⟨hij, _⟩ := List.pairwise_cons.1 hSort
                have hjlt : i < j := hij j List.mem_cons_self
                have hj := hRange j (List.mem_cons_of_mem _ List.mem_cons_self)
                omega
          subst hqSingle
          rw [buildBlindedNode256, saltedSubtreeRoot256]
          simp [h1, evalBlindedNode256]
        · have hge2 : 2 ≤ entries.length := by omega
          let mid := entries.length / 2
          have hmidPos : 0 < mid := by omega
          have hmidLt : mid < entries.length := by omega
          have hTakeLen : (entries.take mid).length = mid := by rw [List.length_take]; omega
          have hDropLen : (entries.drop mid).length = entries.length - mid := List.length_drop
          let qLeft := queried.filter (fun i => decide (i < startIdx + mid))
          let qRight := queried.filter (fun i => decide (startIdx + mid ≤ i))
          have hSortL : qLeft.Pairwise (· < ·) := hSort.filter _
          have hSortR : qRight.Pairwise (· < ·) := hSort.filter _
          have hRangeL : ∀ i ∈ qLeft, startIdx ≤ i ∧ i < startIdx + (entries.take mid).length := by
            intro i hi
            simp only [qLeft, List.mem_filter, decide_eq_true_eq] at hi
            rw [hTakeLen]
            exact ⟨(hRange i hi.1).1, hi.2⟩
          have hRangeR : ∀ i ∈ qRight,
              startIdx + mid ≤ i ∧ i < (startIdx + mid) + (entries.drop mid).length := by
            intro i hi
            simp only [qRight, List.mem_filter, decide_eq_true_eq] at hi
            rw [hDropLen]
            have hb := (hRange i hi.1).2
            exact ⟨hi.2, by omega⟩
          have ihL := ih (entries.take mid)
            (by change (entries.take mid).length < entries.length; rw [hTakeLen]; exact hmidLt)
            startIdx qLeft hSortL hRangeL
          have ihR := ih (entries.drop mid)
            (by change (entries.drop mid).length < entries.length; rw [hDropLen]; omega)
            (startIdx + mid) qRight hSortR hRangeR
          rw [hTakeLen] at ihL
          rw [hDropLen] at ihR
          have hMapL :
              qLeft.map (fun i => (i, (entries.take mid).getD (i - startIdx) defaultSaltedLeaf256)) =
                qLeft.map (fun i => (i, entries.getD (i - startIdx) defaultSaltedLeaf256)) := by
            apply List.map_congr_left
            intro i hi
            simp only [qLeft, List.mem_filter, decide_eq_true_eq] at hi
            have hlt : i - startIdx < mid := by omega
            rw [getD_take_salted entries hlt]
          have hMapR :
              qRight.map (fun i => (i, (entries.drop mid).getD (i - (startIdx + mid)) defaultSaltedLeaf256)) =
                qRight.map (fun i => (i, entries.getD (i - startIdx) defaultSaltedLeaf256)) := by
            apply List.map_congr_left
            intro i hi
            simp only [qRight, List.mem_filter, decide_eq_true_eq] at hi
            rw [getD_drop_salted, show mid + (i - (startIdx + mid)) = i - startIdx by omega]
          rw [hMapL] at ihL
          rw [hMapR] at ihR
          have hAppendQ : qLeft ++ qRight = queried :=
            filter_lt_append_filter_ge (startIdx + mid) queried hSort
          have hNotBothEmpty :
              ((qLeft.map (fun i => (i, entries.getD (i - startIdx) defaultSaltedLeaf256))).isEmpty &&
               (qRight.map (fun i => (i, entries.getD (i - startIdx) defaultSaltedLeaf256))).isEmpty) = false := by
            cases hc :
                (qLeft.map (fun i => (i, entries.getD (i - startIdx) defaultSaltedLeaf256))).isEmpty &&
                (qRight.map (fun i => (i, entries.getD (i - startIdx) defaultSaltedLeaf256))).isEmpty with
            | false => rfl
            | true =>
              simp only [Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff] at hc
              rw [hc.1, hc.2, List.append_nil] at hAppendQ
              exact absurd hAppendQ.symm hqNe
          dsimp only [mid, qLeft, qRight] at ihL ihR hNotBothEmpty hAppendQ
          rw [buildBlindedNode256]
          conv => rhs; rw [saltedSubtreeRoot256]
          have hlt2_false : decide (entries.length < 2) = false := decide_eq_false (by omega)
          simp only [h0, h1, hqEmpty, Bool.false_eq_true, ↓reduceIte, evalBlindedNode256,
            hlt2_false, ihL, ihR, hNotBothEmpty]
          rw [← List.map_append, hAppendQ]

/-- **Completeness of 256-Bit Salted Blinded Multiproofs (`verifyBlindedMultiproof256_complete`)**:
For every hash `H` (including `cshakeMultiproofHash`), salted leaf table `entries`, and strictly
ascending in-bounds `queriedIndices`, `buildBlindedMultiproof256 H entries queriedIndices` verifies
against `saltedTreeRoot256 H entries`. -/
theorem verifyBlindedMultiproof256_complete (H : Hash) (entries : List SaltedLeaf256)
    (queriedIndices : List Nat)
    (hValid : strictlyAscendingInBounds entries.length queriedIndices = true) :
    verifyBlindedMultiproof256 H
      (buildBlindedMultiproof256 H entries queriedIndices)
      (saltedTreeRoot256 H entries) = true := by
  have hValid' := hValid
  unfold strictlyAscendingInBounds at hValid'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hValid'
  have hSort := (strictlyAscending_iff_pairwise queriedIndices).1 hValid'.1
  have hRange : ∀ i ∈ queriedIndices, 0 ≤ i ∧ i < 0 + entries.length :=
    fun i hi => ⟨Nat.zero_le i, by simpa using hValid'.2 i hi⟩
  have hEval := evalBlindedNode256_build H entries 0 queriedIndices hSort hRange
  unfold verifyBlindedMultiproof256 buildBlindedMultiproof256 saltedTreeRoot256
  simp only [hValid, Bool.true_and, hEval, beq_self_eq_true, List.map_map]
  have hFst : (Prod.fst ∘ fun i : Nat => (i, entries.getD (i - 0) defaultSaltedLeaf256)) = id := by
    funext i; rfl
  rw [hFst, List.map_id, beq_self_eq_true]

/-! ### Constructive `Type`-Valued `PSum` Collision Extraction (`0 Classical.choice`) -/

/-- Finite list of preimages hashed in the honest `saltedSubtreeRoot256 H startIdx entries`. -/
def honestSubtreePreimages (H : Hash) (startIdx : Nat) (entries : List SaltedLeaf256) :
    List (List UInt8) :=
  if entries.length = 0 then
    [emptyPreimage256]
  else if entries.length = 1 then
    let e := entries.getD 0 defaultSaltedLeaf256
    [leafPreimage256 startIdx e.salt e.payload]
  else
    let mid := entries.length / 2
    let lRoot := saltedSubtreeRoot256 H startIdx (entries.take mid)
    let rRoot := saltedSubtreeRoot256 H (startIdx + mid) (entries.drop mid)
    internalPreimage256 entries.length startIdx lRoot rRoot ::
      (honestSubtreePreimages H startIdx (entries.take mid) ++
       honestSubtreePreimages H (startIdx + mid) (entries.drop mid))
termination_by entries.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- Finite list of preimages hashed during `evalBlindedNode256 H node spanSize startIdx`. -/
def proofNodePreimages (H : Hash) : BlindedNode256 → Nat → Nat → List (List UInt8)
  | .empty, _, _ => [emptyPreimage256]
  | .blinded _, _, _ => []
  | .openedLeaf _ salt payload, _, startIdx =>
    [leafPreimage256 startIdx salt payload]
  | .branch left right, spanSize, startIdx =>
    let mid := spanSize / 2
    let children :=
      proofNodePreimages H left mid startIdx ++
      proofNodePreimages H right (spanSize - mid) (startIdx + mid)
    match evalBlindedNode256 H left mid startIdx,
          evalBlindedNode256 H right (spanSize - mid) (startIdx + mid) with
    | some (lRoot, _), some (rRoot, _) =>
      internalPreimage256 spanSize startIdx lRoot rRoot :: children
    | _, _ => children

/-- Combined finite preimage scope for a subtree and multiproof node. -/
def subtreeScopePreimages (H : Hash) (startIdx : Nat) (entries : List SaltedLeaf256)
    (node : BlindedNode256) : List (List UInt8) :=
  honestSubtreePreimages H startIdx entries ++ proofNodePreimages H node entries.length startIdx

/-- Combined finite preimage scope for a full tree and `BlindedMultiproof256`. -/
def multiproofScopePreimages (H : Hash) (entries : List SaltedLeaf256)
    (proof : BlindedMultiproof256) : List (List UInt8) :=
  subtreeScopePreimages H 0 entries proof.tree

private theorem evalBlindedNode256_range {H : Hash} (node : BlindedNode256) :
    ∀ (spanSize startIdx : Nat) (r : Digest256) (opened : List (Nat × SaltedLeaf256)),
      evalBlindedNode256 H node spanSize startIdx = some (r, opened) →
      ∀ idx leaf, (idx, leaf) ∈ opened → startIdx ≤ idx ∧ idx < startIdx + spanSize :=
  match node with
  | .empty => fun spanSize _ _ _ h _ _ hmem => by
    unfold evalBlindedNode256 at h
    cases hc : (spanSize == 0) <;> rw [hc] at h
    · cases h
    · rcases Prod.mk.inj (Option.some.inj h) with ⟨_, rfl⟩; cases hmem
  | .blinded _ => fun spanSize _ _ _ h _ _ hmem => by
    unfold evalBlindedNode256 at h
    cases hc : decide (0 < spanSize) <;> rw [hc] at h
    · cases h
    · rcases Prod.mk.inj (Option.some.inj h) with ⟨_, rfl⟩; cases hmem
  | .openedLeaf idx0 _ _ => fun spanSize startIdx _ _ h _ _ hmem => by
    unfold evalBlindedNode256 at h
    cases hc : (spanSize == 1 && idx0 == startIdx) <;> rw [hc] at h
    · cases h
    · have hc1 := (Bool.and_eq_true _ _).mp hc
      have hsz1 : spanSize = 1 := beq_iff_eq.mp hc1.1
      have hidx0 : idx0 = startIdx := beq_iff_eq.mp hc1.2
      rcases Prod.mk.inj (Option.some.inj h) with ⟨_, rfl⟩
      rcases Prod.mk.inj (List.mem_singleton.mp hmem) with ⟨rfl, _⟩
      subst hsz1 hidx0; exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  | .branch left right => fun spanSize startIdx _ _ h idx leaf hmem => by
    unfold evalBlindedNode256 at h
    cases hlt2 : decide (spanSize < 2) <;> rw [hlt2] at h
    · cases hl : evalBlindedNode256 H left (spanSize / 2) startIdx with
      | none => dsimp only at h; rw [hl] at h; cases h
      | some lPair =>
        cases hr : evalBlindedNode256 H right (spanSize - spanSize / 2) (startIdx + spanSize / 2) with
        | none => dsimp only at h; rw [hl, hr] at h; cases h
        | some rPair =>
          rcases lPair with ⟨lRoot, lOpened⟩; rcases rPair with ⟨rRoot, rOpened⟩
          dsimp only at h; rw [hl, hr] at h; dsimp only at h
          cases hemp : (lOpened.isEmpty && rOpened.isEmpty) <;> rw [hemp] at h
          · rcases Prod.mk.inj (Option.some.inj h) with ⟨_, rfl⟩
            rcases List.mem_append.1 hmem with hL | hR
            · have hb := evalBlindedNode256_range left (spanSize / 2) startIdx lRoot lOpened hl idx leaf hL
              exact ⟨hb.1, Nat.lt_of_lt_of_le hb.2 (Nat.add_le_add_left (Nat.div_le_self _ _) _)⟩
            · have hb := evalBlindedNode256_range right (spanSize - spanSize / 2)
                (startIdx + spanSize / 2) rRoot rOpened hr idx leaf hR
              have hEq : (startIdx + spanSize / 2) + (spanSize - spanSize / 2) = startIdx + spanSize := by
                rw [Nat.add_assoc, Nat.add_sub_of_le (Nat.div_le_self _ _)]
              exact ⟨Nat.le_trans (Nat.le_add_right _ _) hb.1, hEq ▸ hb.2⟩
          · cases h
    · cases h
termination_by structural node

private theorem branch_ge2_of_eval {H : Hash} {l r : BlindedNode256} {sz st : Nat} {x : Digest256 × List (Nat × SaltedLeaf256)}
    (h : evalBlindedNode256 H (.branch l r) sz st = some x) : 2 ≤ sz := by
  unfold evalBlindedNode256 at h
  cases hlt2 : decide (sz < 2) <;> rw [hlt2] at h
  · exact Nat.not_lt.1 (decide_eq_false_iff_not.1 hlt2)
  · cases h

/-- Constructive `Type`-valued subtree collision extractor (`0 Classical.choice`):
either every opened `(idx, leaf)` equals the true leaf in `entries`, or an explicit
`ScopedCollision256` pair of distinct preimages is returned. -/
def extractSubtreeCollision (H : Hash) :
    (node : BlindedNode256) → (entries : List SaltedLeaf256) → (startIdx : Nat) →
    (opened : List (Nat × SaltedLeaf256)) →
    evalBlindedNode256 H node entries.length startIdx =
      some (saltedSubtreeRoot256 H startIdx entries, opened) →
    PSum
      (∀ idx leaf, (idx, leaf) ∈ opened → entries[idx - startIdx]? = some leaf)
      (ScopedCollision256 H (subtreeScopePreimages H startIdx entries node))
  | .empty, entries, _, _, hEval =>
    PSum.inl (by
      intro _ _ hmem; unfold evalBlindedNode256 at hEval
      cases hc : (entries.length == 0) <;> rw [hc] at hEval
      · cases hEval
      · rcases Prod.mk.inj (Option.some.inj hEval) with ⟨_, rfl⟩; cases hmem)
  | .blinded _, entries, _, _, hEval =>
    PSum.inl (by
      intro _ _ hmem; unfold evalBlindedNode256 at hEval
      cases hc : decide (0 < entries.length) <;> rw [hc] at hEval
      · cases hEval
      · rcases Prod.mk.inj (Option.some.inj hEval) with ⟨_, rfl⟩; cases hmem)
  | .openedLeaf idx0 salt payload, entries, startIdx, opened, hEval =>
    let trueLeaf := entries.getD 0 defaultSaltedLeaf256
    if hMatch : (⟨salt, payload⟩ : SaltedLeaf256) = trueLeaf then
      PSum.inl (by
        intro idx leaf hmem; unfold evalBlindedNode256 at hEval
        cases hc : (entries.length == 1 && idx0 == startIdx) <;> rw [hc] at hEval
        · cases hEval
        · have hc1 := (Bool.and_eq_true _ _).mp hc
          have hlen1 : entries.length = 1 := beq_iff_eq.mp hc1.1
          have hidx0 : idx0 = startIdx := beq_iff_eq.mp hc1.2
          rcases Prod.mk.inj (Option.some.inj hEval) with ⟨_, rfl⟩
          rcases Prod.mk.inj (List.mem_singleton.mp hmem) with ⟨rfl, rfl⟩
          have hsub : idx - startIdx = 0 := by omega
          rw [hsub, hMatch]
          cases entries with
          | nil => cases hlen1
          | cons _ rest => cases rest with
            | nil => rfl
            | cons _ _ => exact absurd (Nat.succ.inj hlen1) (Nat.succ_ne_zero _))
    else
      PSum.inr (by
        unfold evalBlindedNode256 at hEval
        cases hc : (entries.length == 1 && idx0 == startIdx) <;> rw [hc] at hEval
        · cases hEval
        · have hlen1 : entries.length = 1 := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hc).1
          rcases Prod.mk.inj (Option.some.inj hEval) with ⟨hRootEq, _⟩
          have h0 : entries.length ≠ 0 := by omega
          have hTrueRoot : saltedSubtreeRoot256 H startIdx entries =
              hashBytes256 H (leafPreimage256 startIdx trueLeaf.salt trueLeaf.payload) := by
            rw [saltedSubtreeRoot256, if_neg h0, if_pos hlen1]
          rw [hTrueRoot] at hRootEq
          have hPreNe : leafPreimage256 startIdx trueLeaf.salt trueLeaf.payload ≠
              leafPreimage256 startIdx salt payload := by
            intro hp; obtain ⟨_, hs, hpl⟩ := leafPreimage256_injective hp
            have hEta : (⟨trueLeaf.salt, trueLeaf.payload⟩ : SaltedLeaf256) = trueLeaf := rfl
            rw [hs, hpl] at hEta; exact hMatch hEta
          refine ⟨_, _, List.mem_append_left _ (by rw [honestSubtreePreimages, if_neg h0, if_pos hlen1]; exact List.mem_singleton.2 rfl),
            List.mem_append_right _ (List.mem_singleton.2 rfl), hPreNe, hRootEq.symm⟩)
  | .branch left right, entries, startIdx, opened, hEval =>
    let mid := entries.length / 2
    let trueL := saltedSubtreeRoot256 H startIdx (entries.take mid)
    let trueR := saltedSubtreeRoot256 H (startIdx + mid) (entries.drop mid)
    match hL : evalBlindedNode256 H left mid startIdx,
          hR : evalBlindedNode256 H right (entries.length - mid) (startIdx + mid) with
    | some (lRoot, lOpened), some (rRoot, rOpened) =>
      if hChildren : lRoot = trueL ∧ rRoot = trueR then
        have hge2 : 2 ≤ entries.length := branch_ge2_of_eval hEval
        have hTakeLen : (entries.take mid).length = mid := by rw [List.length_take]; omega
        have hDropLen : (entries.drop mid).length = entries.length - mid := List.length_drop
        have hEvalL : evalBlindedNode256 H left (entries.take mid).length startIdx =
            some (saltedSubtreeRoot256 H startIdx (entries.take mid), lOpened) := by
          rw [hTakeLen, hL, hChildren.1]
        have hEvalR : evalBlindedNode256 H right (entries.drop mid).length (startIdx + mid) =
            some (saltedSubtreeRoot256 H (startIdx + mid) (entries.drop mid), rOpened) := by
          rw [hDropLen, hR, hChildren.2]
        match extractSubtreeCollision H left (entries.take mid) startIdx lOpened hEvalL with
        | .inr colL =>
          PSum.inr (colL.mono (by
            intro x hx; have h0 : entries.length ≠ 0 := by omega
            have h1 : entries.length ≠ 1 := by omega
            unfold subtreeScopePreimages at hx ⊢
            rcases List.mem_append.1 hx with hxH | hxP
            · exact List.mem_append_left _ (by
                rw [honestSubtreePreimages, if_neg h0, if_neg h1]
                exact List.mem_cons_of_mem _ (List.mem_append_left _ hxH))
            · exact List.mem_append_right _ (by
                rw [hTakeLen] at hxP; dsimp only [mid] at hL hR hxP
                unfold proofNodePreimages; dsimp only; rw [hL, hR]
                exact List.mem_cons_of_mem _ (List.mem_append_left _ hxP))))
        | .inl okL =>
          match extractSubtreeCollision H right (entries.drop mid) (startIdx + mid) rOpened hEvalR with
          | .inr colR =>
            PSum.inr (colR.mono (by
              intro x hx; have h0 : entries.length ≠ 0 := by omega
              have h1 : entries.length ≠ 1 := by omega
              unfold subtreeScopePreimages at hx ⊢
              rcases List.mem_append.1 hx with hxH | hxP
              · exact List.mem_append_left _ (by
                  rw [honestSubtreePreimages, if_neg h0, if_neg h1]
                  exact List.mem_cons_of_mem _ (List.mem_append_right _ hxH))
              · exact List.mem_append_right _ (by
                  rw [hDropLen] at hxP; dsimp only [mid] at hL hR hxP
                  unfold proofNodePreimages; dsimp only; rw [hL, hR]
                  exact List.mem_cons_of_mem _ (List.mem_append_right _ hxP))))
          | .inl okR =>
            PSum.inl (by
              intro idx leaf hmem
              have hlt2F : decide (entries.length < 2) = false := decide_eq_false (by omega)
              have hOpenedEq : opened = lOpened ++ rOpened := by
                dsimp only [mid] at hL hR
                unfold evalBlindedNode256 at hEval; rw [hlt2F] at hEval; dsimp only at hEval
                rw [hL, hR] at hEval; dsimp only at hEval
                cases hc : (lOpened.isEmpty && rOpened.isEmpty) <;> rw [hc] at hEval
                · exact (Prod.mk.inj (Option.some.inj hEval)).2.symm
                · cases hEval
              rw [hOpenedEq] at hmem
              rcases List.mem_append.1 hmem with hmL | hmR
              · have hb := evalBlindedNode256_range left mid startIdx lRoot lOpened hL idx leaf hmL
                have hlt : idx - startIdx < mid := by omega
                have hget := okL idx leaf hmL; rwa [List.getElem?_take_of_lt hlt] at hget
              · have hb := evalBlindedNode256_range right (entries.length - mid) (startIdx + mid)
                  rRoot rOpened hR idx leaf hmR
                have hget := okR idx leaf hmR
                rw [List.getElem?_drop, show mid + (idx - (startIdx + mid)) = idx - startIdx by omega] at hget
                exact hget)
      else
        PSum.inr (by
          have hge2 : 2 ≤ entries.length := branch_ge2_of_eval hEval
          have hlt2F : decide (entries.length < 2) = false := decide_eq_false (by omega)
          have h0 : entries.length ≠ 0 := by omega
          have h1 : entries.length ≠ 1 := by omega
          have hRootEq : hashBytes256 H (internalPreimage256 entries.length startIdx lRoot rRoot) =
              saltedSubtreeRoot256 H startIdx entries := by
            dsimp only [mid] at hL hR
            unfold evalBlindedNode256 at hEval; rw [hlt2F] at hEval; dsimp only at hEval
            rw [hL, hR] at hEval; dsimp only at hEval
            cases hc : (lOpened.isEmpty && rOpened.isEmpty) <;> rw [hc] at hEval
            · exact (Prod.mk.inj (Option.some.inj hEval)).1
            · cases hEval
          have hTrueRoot : saltedSubtreeRoot256 H startIdx entries =
              hashBytes256 H (internalPreimage256 entries.length startIdx trueL trueR) := by
            conv => lhs; rw [saltedSubtreeRoot256, if_neg h0, if_neg h1]
          rw [hTrueRoot] at hRootEq
          have hPreNe : internalPreimage256 entries.length startIdx trueL trueR ≠
              internalPreimage256 entries.length startIdx lRoot rRoot := by
            intro hp; obtain ⟨_, _, hlEq, hrEq⟩ := internalPreimage256_injective hp
            exact hChildren ⟨hlEq.symm, hrEq.symm⟩
          refine ⟨_, _, List.mem_append_left _ (by rw [honestSubtreePreimages, if_neg h0, if_neg h1]; exact List.mem_cons_self),
            List.mem_append_right _ ?_, hPreNe, hRootEq.symm⟩
          dsimp only [mid] at hL hR
          unfold proofNodePreimages; dsimp only; rw [hL, hR]
          exact List.mem_cons_self)
    | none, _ =>
      PSum.inl (by
        exfalso; unfold evalBlindedNode256 at hEval
        cases hlt2 : decide (entries.length < 2) <;> rw [hlt2] at hEval
        · dsimp only [mid] at hL; dsimp only at hEval; rw [hL] at hEval; cases hEval
        · cases hEval)
    | some _, none =>
      PSum.inl (by
        exfalso; unfold evalBlindedNode256 at hEval
        cases hlt2 : decide (entries.length < 2) <;> rw [hlt2] at hEval
        · dsimp only [mid] at hL hR; dsimp only at hEval; rw [hL, hR] at hEval; cases hEval
        · cases hEval)

/-- **Constructive `Type`-Valued Multiproof Binding & Collision Extractor (`extractMultiproofCollision`)**:
With **`0 Classical.choice`** and **zero pigeonhole vacuity**, any `proof` accepted by
`verifyBlindedMultiproof256 H proof (saltedTreeRoot256 H entries) = true` with
`proof.treeSize = entries.length` constructively yields either exact salted leaf agreement on all
opened leaves (`PSum.inl`) or an explicit `ScopedCollision256` pair (`PSum.inr`). -/
def extractMultiproofCollision (H : Hash) (entries : List SaltedLeaf256)
    (proof : BlindedMultiproof256)
    (hSize : proof.treeSize = entries.length)
    (hVer : verifyBlindedMultiproof256 H proof (saltedTreeRoot256 H entries) = true) :
    PSum
      (∃ opened,
        evalBlindedNode256 H proof.tree entries.length 0 =
          some (saltedTreeRoot256 H entries, opened) ∧
        opened.map Prod.fst = proof.queriedIndices ∧
        ∀ idx leaf, (idx, leaf) ∈ opened → entries[idx]? = some leaf)
      (ScopedCollision256 H (multiproofScopePreimages H entries proof)) :=
  match hEv : evalBlindedNode256 H proof.tree entries.length 0 with
  | some (r, opened) =>
    have hRest : r = saltedTreeRoot256 H entries ∧ opened.map Prod.fst = proof.queriedIndices := by
      unfold verifyBlindedMultiproof256 at hVer; rw [hSize, hEv] at hVer; dsimp only at hVer
      have h2 := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hVer).2
      exact ⟨beq_iff_eq.mp h2.1, beq_iff_eq.mp h2.2⟩
    have hEvalTrue : evalBlindedNode256 H proof.tree entries.length 0 =
        some (saltedSubtreeRoot256 H 0 entries, opened) := by rw [hEv, hRest.1]; rfl
    match extractSubtreeCollision H proof.tree entries 0 opened hEvalTrue with
    | .inl ok => PSum.inl ⟨opened, by rw [hRest.1], hRest.2, fun idx leaf hm => ok idx leaf hm⟩
    | .inr col => PSum.inr col
  | none =>
    PSum.inl (by exfalso; unfold verifyBlindedMultiproof256 at hVer; rw [hSize, hEv] at hVer; rw [Bool.and_false] at hVer; cases hVer)

/-! ### Redaction Non-Leakage & Zero-Access Commitment Simulation -/

/-- Collect all `(idx, salt, payload)` triples syntactically present in `.openedLeaf` nodes. -/
def BlindedNode256.syntacticOpenedLeaves : BlindedNode256 → List (Nat × SaltedLeaf256)
  | .empty | .blinded _ => []
  | .openedLeaf idx salt payload => [(idx, ⟨salt, payload⟩)]
  | .branch l r => l.syntacticOpenedLeaves ++ r.syntacticOpenedLeaves

theorem evalBlindedNode256_syntacticOpened {H : Hash} :
    ∀ (node : BlindedNode256) (sz st : Nat) (r : Digest256) (opened : List (Nat × SaltedLeaf256)),
      evalBlindedNode256 H node sz st = some (r, opened) → node.syntacticOpenedLeaves = opened
  | .empty, _, _, _, _, h => by
    simp only [evalBlindedNode256] at h; split at h
    · rcases Prod.mk.inj (Option.some.inj h) with ⟨_, rfl⟩; rfl
    · cases h
  | .blinded _, _, _, _, _, h => by
    simp only [evalBlindedNode256] at h; split at h
    · rcases Prod.mk.inj (Option.some.inj h) with ⟨_, rfl⟩; rfl
    · cases h
  | .openedLeaf _ _ _, _, _, _, _, h => by
    simp only [evalBlindedNode256] at h; split at h
    · rcases Prod.mk.inj (Option.some.inj h) with ⟨_, rfl⟩; rfl
    · cases h
  | .branch l r, sz, st, _, _, h => by
    simp only [evalBlindedNode256] at h; split at h
    · cases h
    · split at h
      · rename_i lr lo rr ro hl hr; split at h
        · cases h
        · rcases Prod.mk.inj (Option.some.inj h) with ⟨_, rfl⟩
          simp [BlindedNode256.syntacticOpenedLeaves,
            evalBlindedNode256_syntacticOpened l _ _ lr lo hl,
            evalBlindedNode256_syntacticOpened r _ _ rr ro hr]
      · cases h

/-- **Syntactic Redaction Non-Presence (`buildBlindedNode256_opened_only_queried`)**:
Every `.openedLeaf` node syntactically present anywhere inside `buildBlindedNode256` belongs to
`queried`. Unqueried indices have **zero** `.openedLeaf` payloads or salts in the multiproof. -/
theorem buildBlindedNode256_opened_only_queried (H : Hash)
    (entries : List SaltedLeaf256) (startIdx : Nat) (queried : List Nat)
    (hSort : queried.Pairwise (· < ·))
    (hRange : ∀ i ∈ queried, startIdx ≤ i ∧ i < startIdx + entries.length)
    (idx : Nat) (leaf : SaltedLeaf256)
    (hMem : (idx, leaf) ∈ (buildBlindedNode256 H startIdx entries queried).syntacticOpenedLeaves) :
    idx ∈ queried ∧ entries.getD (idx - startIdx) defaultSaltedLeaf256 = leaf := by
  have hSyn := evalBlindedNode256_syntacticOpened _ _ _ _ _
    (evalBlindedNode256_build H entries startIdx queried hSort hRange)
  rw [hSyn, List.mem_map] at hMem
  obtain ⟨i, hi, hEq⟩ := hMem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
  exact ⟨hi, rfl⟩

/-- Zero-access redacted simulator: constructs a `BlindedNode256` from **only**
(1) `openedOracle`, queried solely at indices `i ∈ queried`, and
(2) `blindedCommitmentOracle`, queried solely for 32-byte commitments of unqueried spans
`(startIdx, spanSize)`. Never touches any redacted leaf's payload or salt! -/
def simulateBlindedNode256
    (openedOracle : Nat → SaltedLeaf256)
    (blindedCommitmentOracle : Nat → Nat → Digest256)
    (startIdx spanSize : Nat) (queried : List Nat) : BlindedNode256 :=
  if spanSize = 0 then
    .empty
  else if queried.isEmpty then
    .blinded (blindedCommitmentOracle startIdx spanSize)
  else if spanSize = 1 then
    let e := openedOracle startIdx
    .openedLeaf startIdx e.salt e.payload
  else
    let mid := spanSize / 2
    let qLeft := queried.filter (fun i => decide (i < startIdx + mid))
    let qRight := queried.filter (fun i => decide (startIdx + mid ≤ i))
    .branch
      (simulateBlindedNode256 openedOracle blindedCommitmentOracle startIdx mid qLeft)
      (simulateBlindedNode256 openedOracle blindedCommitmentOracle (startIdx + mid) (spanSize - mid) qRight)
termination_by spanSize
decreasing_by all_goals omega

/-- **Zero-Access Redaction Non-Leakage (`blindedMultiproof_redaction_nonleakage`)**:
`buildBlindedMultiproof256` is bit-for-bit identical to the zero-access simulator
`simulateBlindedNode256` whose `openedOracle` returns `defaultSaltedLeaf256` on **all** redacted
indices `i ∉ queriedIndices` and whose `blindedCommitmentOracle` sees **only** the 32-byte salted
subtree commitments! Consequently, mutating any redacted leaf while preserving unqueried 32-byte
commitments (or comparing under salted commitment hiding) leaks zero information beyond the
32-byte `.blinded` commitments. -/
theorem blindedMultiproof_redaction_nonleakage (H : Hash) (entries : List SaltedLeaf256)
    (queriedIndices : List Nat)
    (hValid : strictlyAscendingInBounds entries.length queriedIndices = true) :
    (buildBlindedMultiproof256 H entries queriedIndices).tree =
      simulateBlindedNode256
        (fun i => if i ∈ queriedIndices then entries.getD i defaultSaltedLeaf256 else defaultSaltedLeaf256)
        (fun st sz => saltedSubtreeRoot256 H st ((entries.drop st).take sz))
        0 entries.length queriedIndices := by
  have hValid' := hValid
  unfold strictlyAscendingInBounds at hValid'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hValid'
  have hSort := (strictlyAscending_iff_pairwise queriedIndices).1 hValid'.1
  have hRange : ∀ i ∈ queriedIndices, 0 ≤ i ∧ i < 0 + entries.length :=
    fun i hi => ⟨Nat.zero_le i, by simpa using hValid'.2 i hi⟩
  suffices hGen :
      ∀ (slice : List SaltedLeaf256) (startIdx : Nat) (q : List Nat),
        slice = (entries.drop startIdx).take slice.length →
        q.Pairwise (· < ·) →
        (∀ i ∈ q, i ∈ queriedIndices ∧ startIdx ≤ i ∧ i < startIdx + slice.length) →
        buildBlindedNode256 H startIdx slice q =
          simulateBlindedNode256
            (fun i => if i ∈ queriedIndices then entries.getD i defaultSaltedLeaf256 else defaultSaltedLeaf256)
            (fun st sz => saltedSubtreeRoot256 H st ((entries.drop st).take sz))
            startIdx slice.length q by
    exact hGen entries 0 queriedIndices
      (by simp [List.take_length])
      hSort
      (fun i hi => ⟨hi, hRange i hi⟩)
  intro slice
  induction slice using (measure List.length).wf.induction with
  | h slice ih =>
    intro startIdx q hSlice hqSort hqSub
    by_cases h0 : slice.length = 0
    · rw [buildBlindedNode256, simulateBlindedNode256]
      simp [h0]
    · by_cases hqEmpty : q.isEmpty = true
      · rw [buildBlindedNode256, simulateBlindedNode256]
        simp only [h0, hqEmpty, ↓reduceIte]
        rw [← hSlice]
      · simp only [Bool.not_eq_true] at hqEmpty
        have hqNe : q ≠ [] := List.isEmpty_eq_false_iff.1 hqEmpty
        by_cases h1 : slice.length = 1
        · have hStartMem : startIdx ∈ q := by
            cases q with
            | nil => exact absurd rfl hqNe
            | cons i _ =>
              have hi := (hqSub i List.mem_cons_self).2
              have : i = startIdx := by omega
              subst this; exact List.mem_cons_self
          have hInAll : startIdx ∈ queriedIndices := (hqSub startIdx hStartMem).1
          have hGetEq : slice.getD 0 defaultSaltedLeaf256 = entries.getD startIdx defaultSaltedLeaf256 := by
            rw [hSlice, h1]
            rw [getD_take_salted _ (by decide), getD_drop_salted, Nat.add_zero]
          rw [buildBlindedNode256, simulateBlindedNode256]
          simp only [h1, hqEmpty, Bool.false_eq_true, ↓reduceIte, hInAll]
          rw [hGetEq]
        · let mid := slice.length / 2
          have hmidLt : mid < slice.length := by omega
          have hTakeLen : (slice.take mid).length = mid := by rw [List.length_take]; omega
          have hDropLen : (slice.drop mid).length = slice.length - mid := List.length_drop
          let qLeft := q.filter (fun i => decide (i < startIdx + mid))
          let qRight := q.filter (fun i => decide (startIdx + mid ≤ i))
          have hSliceL : slice.take mid = (entries.drop startIdx).take (slice.take mid).length := by
            rw [hTakeLen]; (conv => lhs; rw [hSlice]); rw [List.take_take, Nat.min_eq_left (by omega)]
          have hSliceR : slice.drop mid = (entries.drop (startIdx + mid)).take (slice.drop mid).length := by
            rw [hDropLen]; (conv => lhs; rw [hSlice]); rw [List.drop_take, List.drop_drop]
          have hSubL : ∀ i ∈ qLeft,
              i ∈ queriedIndices ∧ startIdx ≤ i ∧ i < startIdx + (slice.take mid).length := by
            intro i hi; simp only [qLeft, List.mem_filter, decide_eq_true_eq] at hi
            rw [hTakeLen]; exact ⟨(hqSub i hi.1).1, (hqSub i hi.1).2.1, hi.2⟩
          have hSubR : ∀ i ∈ qRight,
              i ∈ queriedIndices ∧ startIdx + mid ≤ i ∧ i < (startIdx + mid) + (slice.drop mid).length := by
            intro i hi; simp only [qRight, List.mem_filter, decide_eq_true_eq] at hi
            rw [hDropLen]; exact ⟨(hqSub i hi.1).1, hi.2, by have := (hqSub i hi.1).2.2; omega⟩
          have ihL := ih (slice.take mid)
            (by change (slice.take mid).length < slice.length; rw [hTakeLen]; exact hmidLt)
            startIdx qLeft hSliceL (hqSort.filter _) hSubL
          have ihR := ih (slice.drop mid)
            (by change (slice.drop mid).length < slice.length; rw [hDropLen]; omega)
            (startIdx + mid) qRight hSliceR (hqSort.filter _) hSubR
          rw [hTakeLen] at ihL; rw [hDropLen] at ihR; dsimp only [mid, qLeft, qRight] at ihL ihR
          rw [buildBlindedNode256, simulateBlindedNode256]; simp [h0, h1, hqEmpty, ihL, ihR]

end Obend.Receipt.Merkle
end

