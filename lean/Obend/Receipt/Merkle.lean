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

@[expose] public section
namespace Obend.Receipt.Merkle
open Obend.Core.Digest (digestWith Admissible admissible_of_lt binds_or_collides deployed digest_lt preimage lengthHash)
open Obend.Digest.HashBytes (Hash Collision CollisionAmong)
set_option autoImplicit false

/-- A digest-sized natural: what every node of the tree is. -/
def Small (n : Nat) : Bool := decide (n < 2 ^ 256)

/-- A hash whose digests are digest-sized. -/
def Bounded (H : Hash) : Prop := ∀ a b, digestWith H a b < 2 ^ 256

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

/-- **Binding**: two climbs from one position of one tree to one root start at one leaf, or `H` has
a collision. -/
theorem climb_binds {H : Hash} (hb : Bounded H) :
    ∀ (p p' : List Nat) (n i x x' r : Nat), x < 2 ^ 256 → x' < 2 ^ 256 →
      climb H n i x p = some r → climb H n i x' p' = some r → x = x' ∨ Collision H
  | [], [], n, i, x, x', r, _, _, h, h' => by
    simp only [climb] at h h'
    by_cases hn : n = 1
    · simp only [hn, ↓reduceIte, Option.some.injEq] at h h'; exact .inl (h.trans h'.symm)
    · simp [hn] at h
  | [], s' :: ss', n, i, x, x', r, _, _, h, h' => by
    simp only [climb] at h h'; split at h
    · rename_i hn; subst hn; simp at h'
    · cases h
  | s :: ss, [], n, i, x, x', r, _, _, h, h' => by
    simp only [climb] at h h'; split at h'
    · rename_i hn; subst hn; simp at h
    · cases h'
  | s :: ss, s' :: ss', n, i, x, x', r, hx, hx', h, h' => by
    simp only [climb] at h h'
    split at h
    · cases h
    rename_i hn
    split at h'
    · cases h'
    rename_i hn'
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, Small,
      decide_eq_false_iff_not, Nat.not_lt] at hn hn'
    split at h
    · rename_i hi
      simp only [hi, ↓reduceIte] at h'
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨l', hl', he⟩ := Option.map_eq_some_iff.1 h'
      have hla := admissible_of_lt (climb_small hb ss _ _ x l hx hl)
      have hla' := admissible_of_lt (climb_small hb ss' _ _ x' l' hx' hl')
      rcases binds_or_collides H hla' hla he with ⟨hll, _⟩ | c
      · exact climb_binds hb ss ss' _ _ x x' l hx hx' hl (hll ▸ hl')
      · exact .inr c.global
    · rename_i hi
      simp only [hi, ↓reduceIte] at h'
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨l', hl', he⟩ := Option.map_eq_some_iff.1 h'
      have hs := admissible_of_lt (Nat.lt_of_not_le hn.2)
      have hs' := admissible_of_lt (Nat.lt_of_not_le hn'.2)
      rcases binds_or_collides H hs' hs he with ⟨_, hll⟩ | c
      · exact climb_binds hb ss ss' _ _ x x' l hx hx' hl (hll ▸ hl')
      · exact .inr c.global

/-! ## The map: values at positions -/

/-- The leaf of value `v` at position `j`. -/
def leaf (H : Hash) (j v : Nat) : Nat := digestWith H j v

/-- The leaves of a list of values. -/
def leaves (H : Hash) (vs : List Nat) : List Nat := vs.mapIdx fun j v => leaf H j v

/-- The root of a list of values. -/
def mapRoot (H : Hash) (vs : List Nat) : Nat := root H (leaves H vs)

/-- An opening: the map's size, the position, the value claimed there, and the siblings. -/
structure Opening where
  size : Nat
  index : Nat
  value : Nat
  path : List Nat
  deriving DecidableEq, Repr

/-- The honest opening of position `j`. -/
def mapOpening (H : Hash) (vs : List Nat) (j : Nat) : Opening :=
  ⟨vs.length, j, vs.getD j 0, path H (leaves H vs) j⟩

/-- **An opening opens against a root.** -/
def opens (H : Hash) (o : Opening) (r : Nat) : Bool :=
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

/-- **Openings bind**: two openings of one position of one map that open against one root claim
one value, or `H` has a collision. -/
theorem opens_binds {H : Hash} (hb : Bounded H) {o o' : Opening} {r : Nat} (h : opens H o r = true)
    (h' : opens H o' r = true) (hn : o.size = o'.size) (hi : o.index = o'.index) :
    o.value = o'.value ∨ Collision H := by
  simp only [opens, Bool.and_eq_true, beq_iff_eq, Small, decide_eq_true_eq] at h h'
  rw [← hn, ← hi] at h'
  rcases climb_binds hb o.path o'.path o.size o.index _ _ r (hb _ _) (hb _ _) h.2 h'.2 with he | c
  · rcases binds_or_collides H (admissible_of_lt h.1) (admissible_of_lt h.1) he with ⟨_, hv⟩ | c
    · exact .inl hv
    · exact .inr c.global
  · exact .inr c

/-- **An opening against a view's root carries the view's value**, or `H` collides. -/
theorem opens_view {H : Hash} (hb : Bounded H) (vs : List Nat) {o : Opening}
    (h : opens H o (mapRoot H vs) = true) (hn : o.size = vs.length) (hj : o.index < vs.length) :
    o.value = vs[o.index] ∨ Collision H := by
  have hs : o.index < 2 ^ 256 := by
    simp only [opens, Bool.and_eq_true, Small, decide_eq_true_eq] at h; exact h.1
  have hc := opens_complete hb vs o.index hj hs
  rcases opens_binds hb h hc (by simp [mapOpening, hn]) rfl with he | c
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
def values (C : Commit W Key) (w : W) : List Nat := C.keys.map (C.val w)

/-- **The view's root**: what a receipt is dated by. -/
def dated (H : Hash) (C : Commit W Key) (w : W) : Nat := mapRoot H (C.values w)

/-- The opening of key `k`, if the schema has it. -/
def opening [BEq Key] (H : Hash) (C : Commit W Key) (w : W) (k : Key) : Option Opening :=
  (C.keys.idxOf? k).map fun j => mapOpening H (C.values w) j

/-- **An honest opening opens against the dated root.** -/
theorem opening_opens [BEq Key] [LawfulBEq Key] {H : Hash} (hb : Bounded H) (C : Commit W Key) (w : W) (k : Key)
    {o : Opening} (h : C.opening H w k = some o) (hs : C.keys.length < 2 ^ 256) :
    opens H o (C.dated H w) = true := by
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
  have hjl : j < C.keys.length := (List.idxOf?_eq_some_iff.1 hj).1
  exact opens_complete hb _ j (by simp [values]; exact hjl) (Nat.lt_trans hjl hs)

/-- **An opening that opens against a world's dated root carries that world's value at that key**,
or the hash collides. -/
theorem opens_val {H : Hash} (hb : Bounded H) (C : Commit W Key) (w : W) {o : Opening}
    (h : opens H o (C.dated H w) = true) (hn : o.size = C.keys.length) (hj : o.index < C.keys.length) :
    o.value = C.val w C.keys[o.index] ∨ Collision H := by
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

end Obend.Receipt.Merkle
end
