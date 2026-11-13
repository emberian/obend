module
import all Obend.Polis.BlumRam
/-
# Obend.Polis.ZkBiscuit — attenuation chains folded into a constant-size accumulator, revocation, pinned inputs

The relation a recursive capability proof has to attest, and its consequences. Nothing here is a
proof system: there is no zero knowledge and no succinct argument in this module. `foldChain` is
the statement such a proof would be about, `CapAccumulator` is its constant-size public output,
and `authorize` is the constant-time check a verifier runs on that output.

1. `RevokedSet`: a strictly sorted `Array Nat` of 256-bit nullifiers with binary search.
   `RevokedSet.contains_iff` refines the search to list membership, `RevokedSet.root` commits to the
   set, and `RevokedRoot` has a private constructor: the only roots are roots of sets.
2. `credNul`, `chanNul`: nullifiers under one cSHAKE256 customization and two tags, so a
   cross-namespace clash is a collision of two named inputs (`credNul_chanNul_separated`).
3. `Block`, `rootLineage`, `stepLineage`: one delegation hop and the provenance digest chained over
   the hops. `lineageOf_binds` reduces two chains with one digest to a `CollisionAmong` the
   preimages hashed along them.
4. `foldChain`: each hop must narrow rights (`attenuationOk`), must not sit on a revoked channel,
   and its lineage nullifier must not be revoked. `attenuate_monotone_rights`: whatever the end of a
   chain authorizes, every prefix of it authorizes. `revoke_ancestor_kills_cone`: inserting the one
   nullifier of a prefix makes every extension of that prefix fail, at any depth.
   `revoke_only_kills_matching`: a chain that revocation kills has a hop with that nullifier.
5. `FullPinnedPublicInputs`, `bindTurn`: the turn hash, capability root, revoked root and verifier
   key go through `Obend.Crypto.bindRelation`, and `TurnTranscript` can be built no other way.
   `pinned_injective` is unconditional; `bindTurn_binds_or_collides` is the hashed form.
-/
public import Obend.Polis.EvidencedOcap
public import Obend.Polis.BlumRam

public section
namespace Obend.Polis

open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. The revoked set -/

/-- Binary search for `x` in `keys[lo, hi)`. The fuel bounds the recursion; the window halves, so
at most `log₂ (hi - lo) + 1` steps run. -/
@[expose] def searchAux (keys : Array Nat) (x : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo < hi then
      if keys.getD (lo + (hi - lo) / 2) 0 = x then true
      else if keys.getD (lo + (hi - lo) / 2) 0 < x then
        searchAux keys x fuel (lo + (hi - lo) / 2 + 1) hi
      else searchAux keys x fuel lo (lo + (hi - lo) / 2)
    else false

theorem searchAux_sound (keys : Array Nat) (x : Nat) : ∀ (fuel lo hi : Nat), hi ≤ keys.size →
    searchAux keys x fuel lo hi = true → x ∈ keys.toList
  | 0, _, _, _, h => by simp [searchAux] at h
  | fuel + 1, lo, hi, hsz, h => by
    by_cases hlt : lo < hi
    · have hmid : lo + (hi - lo) / 2 < keys.size := by omega
      have hget : keys.getD (lo + (hi - lo) / 2) 0 = keys[lo + (hi - lo) / 2] := by
        simp [Array.getD, hmid]
      simp only [searchAux, hlt, ↓reduceIte, hget] at h
      by_cases h1 : keys[lo + (hi - lo) / 2] = x
      · rw [← h1]
        exact Array.getElem_mem_toList hmid
      · simp only [h1, ↓reduceIte] at h
        by_cases h2 : keys[lo + (hi - lo) / 2] < x
        · simp only [h2, ↓reduceIte] at h
          exact searchAux_sound keys x fuel _ hi hsz h
        · simp only [h2, ↓reduceIte] at h
          exact searchAux_sound keys x fuel lo _ (by omega) h
    · simp [searchAux, hlt] at h

theorem searchAux_complete (keys : Array Nat) (x : Nat)
    (hs : ∀ (i j : Nat) (hi : i < keys.size) (hj : j < keys.size), i < j → keys[i] < keys[j]) :
    ∀ (fuel lo hi : Nat), hi ≤ keys.size → hi - lo ≤ fuel →
      ∀ (i : Nat) (hi' : i < keys.size), lo ≤ i → i < hi → keys[i] = x →
        searchAux keys x fuel lo hi = true
  | 0, lo, hi, _, hf, i, _, hlo, hhi, _ => by omega
  | fuel + 1, lo, hi, hsz, hf, i, hi', hlo, hhi, hx => by
    have hlt : lo < hi := by omega
    have hmid : lo + (hi - lo) / 2 < keys.size := by omega
    have hget : keys.getD (lo + (hi - lo) / 2) 0 = keys[lo + (hi - lo) / 2] := by
      simp [Array.getD, hmid]
    simp only [searchAux, hlt, ↓reduceIte, hget]
    by_cases h1 : keys[lo + (hi - lo) / 2] = x
    · simp only [h1, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : keys[lo + (hi - lo) / 2] < x
      · simp only [h2, ↓reduceIte]
        have hgt : lo + (hi - lo) / 2 < i := by
          rcases Nat.lt_trichotomy i (lo + (hi - lo) / 2) with h | h | h
          · have := hs i _ hi' hmid h
            omega
          · subst h
            exact absurd hx h1
          · exact h
        exact searchAux_complete keys x hs fuel _ hi hsz (by omega) i hi' (by omega) hhi hx
      · simp only [h2, ↓reduceIte]
        have hlt' : i < lo + (hi - lo) / 2 := by
          rcases Nat.lt_trichotomy i (lo + (hi - lo) / 2) with h | h | h
          · exact h
          · subst h
            exact absurd hx h1
          · have := hs _ i hmid hi' h
            omega
        exact searchAux_complete keys x hs fuel lo _ (by omega) (by omega) i hi' hlo hlt' hx

/-- Insert into a strictly sorted list, keeping it strictly sorted. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertSorted x ys

theorem mem_insertSorted (x z : Nat) : ∀ (l : List Nat), z ∈ insertSorted x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insertSorted]
  | y :: ys => by
    by_cases h1 : x < y
    · simp [insertSorted, h1]
    · by_cases h2 : x = y
      · subst h2
        simp [insertSorted]
      · simp only [insertSorted, h1, h2, ↓reduceIte, List.mem_cons, mem_insertSorted x z ys]
        constructor
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)

theorem insertSorted_pairwise (x : Nat) : ∀ (l : List Nat), l.Pairwise (· < ·) →
    (insertSorted x l).Pairwise (· < ·)
  | [], _ => by simp [insertSorted]
  | y :: ys, hp => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.1 hp
    by_cases h1 : x < y
    · simp only [insertSorted, h1, ↓reduceIte]
      refine List.pairwise_cons.2 ⟨fun a ha => ?_, hp⟩
      rcases List.mem_cons.1 ha with e | ha'
      · rw [e]; exact h1
      · exact Nat.lt_trans h1 (hy a ha')
    · by_cases h2 : x = y
      · subst h2
        simp only [insertSorted, Nat.lt_irrefl, eq_self, ↓reduceIte]
        exact hp
      · simp only [insertSorted, h1, h2, ↓reduceIte]
        refine List.pairwise_cons.2 ⟨fun a ha => ?_, insertSorted_pairwise x ys hys⟩
        rcases (mem_insertSorted x a ys).1 ha with e | ha'
        · rw [e]; omega
        · exact hy a ha'

theorem insertSorted_length_le (x : Nat) : ∀ (l : List Nat),
    (insertSorted x l).length ≤ l.length + 1
  | [] => by simp [insertSorted]
  | y :: ys => by
    have ih := insertSorted_length_le x ys
    by_cases h1 : x < y
    · simp [insertSorted, h1]
    · by_cases h2 : x = y
      · subst h2
        simp [insertSorted]
      · simp only [insertSorted, h1, h2, ↓reduceIte, List.length_cons]
        omega

/-- The set of revoked nullifiers: strictly increasing, so membership is a binary search. -/
structure RevokedSet where
  keys : Array Nat
  sorted : keys.toList.Pairwise (· < ·)

namespace RevokedSet

/-- The empty revoked set. -/
@[expose] def empty : RevokedSet := ⟨#[], List.Pairwise.nil⟩

/-- Membership by binary search. -/
@[expose] def contains (s : RevokedSet) (x : Nat) : Bool :=
  searchAux s.keys x s.keys.size 0 s.keys.size

/-- Revoke one nullifier. -/
def insert (s : RevokedSet) (x : Nat) : RevokedSet :=
  ⟨(insertSorted x s.keys.toList).toArray, insertSorted_pairwise x _ s.sorted⟩

theorem ext {s₁ s₂ : RevokedSet} (h : s₁.keys = s₂.keys) : s₁ = s₂ := by
  obtain ⟨k₁, _⟩ := s₁
  obtain ⟨k₂, _⟩ := s₂
  cases h
  rfl

theorem sorted_getElem (s : RevokedSet) (i j : Nat) (hi : i < s.keys.size)
    (hj : j < s.keys.size) (hij : i < j) : s.keys[i] < s.keys[j] := by
  have h := List.pairwise_iff_getElem.1 s.sorted i j (by simpa using hi) (by simpa using hj) hij
  simpa using h

/-- **The search refines set membership.** -/
theorem contains_iff (s : RevokedSet) (x : Nat) : s.contains x = true ↔ x ∈ s.keys.toList := by
  constructor
  · exact searchAux_sound s.keys x _ 0 _ (Nat.le_refl _)
  · intro hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.1 hx
    have hi' : i < s.keys.size := by simpa using hi
    exact searchAux_complete s.keys x s.sorted_getElem _ 0 _ (Nat.le_refl _) (by omega) i hi'
      (Nat.zero_le _) hi' (by simpa using hxi)

theorem contains_insert (s : RevokedSet) (x y : Nat) :
    (s.insert x).contains y = true ↔ y = x ∨ s.contains y = true := by
  rw [contains_iff, contains_iff]
  exact mem_insertSorted x y s.keys.toList

theorem contains_insert_self (s : RevokedSet) (x : Nat) : (s.insert x).contains x = true :=
  (contains_insert s x x).2 (.inl rfl)

theorem contains_foldl_insert (s : RevokedSet) (extra : List Nat) (y : Nat)
    (hy : s.contains y = true) :
    (extra.foldl RevokedSet.insert s).contains y = true := by
  induction extra generalizing s with
  | nil => exact hy
  | cons z zs ih => exact ih (s.insert z) ((contains_insert s z y).2 (.inr hy))

/-- A revocation is one write: the set grows by at most one key. -/
theorem insert_size_le (s : RevokedSet) (x : Nat) : (s.insert x).keys.size ≤ s.keys.size + 1 := by
  have h := insertSorted_length_le x s.keys.toList
  simpa [insert] using h

end RevokedSet

/-- Customization string of the revoked-set commitment. -/
def revokedCustomization : List UInt8 := "OBEND.POLIS.REVOKED/v1".toUTF8.data.toList

/-- The hash the revoked-set commitment is a collision of when it fails to bind. -/
def revokedHash : Hash := cshake256Bytes revokedCustomization

/-- The keys of a revoked set as bytes: each key in LEB128, each length-prefixed. -/
def encodeNats (l : List Nat) : List UInt8 := encodeFields (l.map leb128)

theorem map_leb128_injective : ∀ (l₁ l₂ : List Nat), l₁.map leb128 = l₂.map leb128 → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hab : a = b :=
      (leb128_prefix_inj (r₁ := []) (r₂ := []) (by rw [List.append_nil, List.append_nil, h.1])).1
    rw [hab, map_leb128_injective as bs h.2]

theorem encodeNats_injective {l₁ l₂ : List Nat} (h : encodeNats l₁ = encodeNats l₂) : l₁ = l₂ :=
  map_leb128_injective _ _ (encodeFields_injective _ _ h)

/-- The commitment to a revoked set. The constructor is private to this module: a
`RevokedRoot` is `RevokedSet.root` of some set, never a literal. -/
structure RevokedRoot where
  private mk ::
  bytes : ByteArray

theorem RevokedRoot.ext {a b : RevokedRoot} (h : a.bytes = b.bytes) : a = b :=
  match a, b, h with
  | ⟨_⟩, ⟨_⟩, rfl => rfl

instance : DecidableEq RevokedRoot := fun a b =>
  if h : a.bytes = b.bytes then isTrue (RevokedRoot.ext h)
  else isFalse (fun e => h (e ▸ rfl))

/-- Commit to a revoked set. -/
def RevokedSet.root (s : RevokedSet) : RevokedRoot :=
  RevokedRoot.mk (cshake32ByteArray revokedCustomization (encodeNats s.keys.toList))

/-- Equal roots commit to equal sets, or exhibit a collision. -/
theorem RevokedSet.root_binds {s₁ s₂ : RevokedSet} (h : s₁.root = s₂.root) :
    s₁ = s₂ ∨ CollisionAmong revokedHash
      (fun x => x = encodeNats s₁.keys.toList ∨ x = encodeNats s₂.keys.toList) := by
  have hb : cshake32ByteArray revokedCustomization (encodeNats s₁.keys.toList) =
      cshake32ByteArray revokedCustomization (encodeNats s₂.keys.toList) :=
    congrArg RevokedRoot.bytes h
  rcases cshake32_binds revokedCustomization hb with hp | hc
  · exact .inl (RevokedSet.ext (Array.toList_inj.1 (encodeNats_injective hp)))
  · exact .inr hc

/-! ## 2. Nullifiers -/

/-- Customization string of the nullifier hash. -/
def nulCustomization : List UInt8 := "OBEND.POLIS.NUL/v1".toUTF8.data.toList

/-- The nullifier hash: one function for both namespaces, which the first byte separates. -/
def nulHash : Hash := cshake256Bytes nulCustomization

/-- The credential nullifier of a provenance digest: revoking it revokes that hop and its cone. -/
def credNul (lineage : ByteArray) : Nat := ofBE (nulHash (1 :: lineage.data.toList))

/-- The channel nullifier: revoking it revokes every hop made over that channel. -/
def chanNul (channel : ByteArray) : Nat := ofBE (nulHash (2 :: channel.data.toList))

/-- The two nullifier namespaces never meet except at a collision. -/
theorem credNul_chanNul_separated (lineage channel : ByteArray)
    (h : credNul lineage = chanNul channel) :
    CollisionAmong nulHash
      (fun x => x = 1 :: lineage.data.toList ∨ x = 2 :: channel.data.toList) :=
  ⟨1 :: lineage.data.toList, 2 :: channel.data.toList, .inl rfl, .inr rfl,
    fun e => absurd (List.cons.inj e).1 (by decide), h⟩

theorem credNul_binds {l₁ l₂ : ByteArray} (h : credNul l₁ = credNul l₂) :
    l₁ = l₂ ∨ CollisionAmong nulHash
      (fun x => x = 1 :: l₁.data.toList ∨ x = 1 :: l₂.data.toList) := by
  by_cases hp : l₁.data.toList = l₂.data.toList
  · exact .inl (byteArray_eq_of_toList_eq hp)
  · exact .inr ⟨1 :: l₁.data.toList, 1 :: l₂.data.toList, .inl rfl, .inr rfl,
      fun e => hp (List.cons.inj e).2, h⟩

attribute [local irreducible] credNul chanNul

/-! ## 3. Delegation blocks and provenance -/

/-- A prefix-free byte encoding of caveats. -/
def Caveat.encode : Caveat → List UInt8
  | .atom v => 0 :: leb128 v
  | .const b => [1, if b then 1 else 0]
  | .and a b => 2 :: (encode a ++ encode b)
  | .or a b => 3 :: (encode a ++ encode b)
  | .not a => 4 :: encode a

theorem Caveat.encode_prefix_inj : ∀ (a b : Caveat) (r₁ r₂ : List UInt8),
    a.encode ++ r₁ = b.encode ++ r₂ → a = b ∧ r₁ = r₂
  | .atom v, b, r₁, r₂, h => by
    cases b with
    | atom w =>
      simp only [Caveat.encode, List.cons_append] at h
      obtain ⟨hv, hr⟩ := leb128_prefix_inj (List.cons.inj h).2
      exact ⟨by rw [hv], hr⟩
    | const _ => exact absurd (List.cons.inj h).1 (by decide)
    | and _ _ => exact absurd (List.cons.inj h).1 (by decide)
    | or _ _ => exact absurd (List.cons.inj h).1 (by decide)
    | not _ => exact absurd (List.cons.inj h).1 (by decide)
  | .const c, b, r₁, r₂, h => by
    cases b with
    | const d =>
      simp only [Caveat.encode, List.cons_append, List.nil_append] at h
      obtain ⟨hb, hr⟩ := List.cons.inj (List.cons.inj h).2
      have hcd : c = d := by
        cases c <;> cases d <;> first | rfl | exact absurd hb (by decide)
      exact ⟨by rw [hcd], hr⟩
    | atom _ => exact absurd (List.cons.inj h).1 (by decide)
    | and _ _ => exact absurd (List.cons.inj h).1 (by decide)
    | or _ _ => exact absurd (List.cons.inj h).1 (by decide)
    | not _ => exact absurd (List.cons.inj h).1 (by decide)
  | .and a₁ a₂, b, r₁, r₂, h => by
    cases b with
    | and b₁ b₂ =>
      simp only [Caveat.encode, List.cons_append, List.append_assoc] at h
      obtain ⟨e₁, h'⟩ := Caveat.encode_prefix_inj a₁ b₁ _ _ (List.cons.inj h).2
      obtain ⟨e₂, hr⟩ := Caveat.encode_prefix_inj a₂ b₂ _ _ h'
      exact ⟨by rw [e₁, e₂], hr⟩
    | atom _ => exact absurd (List.cons.inj h).1 (by decide)
    | const _ => exact absurd (List.cons.inj h).1 (by decide)
    | or _ _ => exact absurd (List.cons.inj h).1 (by decide)
    | not _ => exact absurd (List.cons.inj h).1 (by decide)
  | .or a₁ a₂, b, r₁, r₂, h => by
    cases b with
    | or b₁ b₂ =>
      simp only [Caveat.encode, List.cons_append, List.append_assoc] at h
      obtain ⟨e₁, h'⟩ := Caveat.encode_prefix_inj a₁ b₁ _ _ (List.cons.inj h).2
      obtain ⟨e₂, hr⟩ := Caveat.encode_prefix_inj a₂ b₂ _ _ h'
      exact ⟨by rw [e₁, e₂], hr⟩
    | atom _ => exact absurd (List.cons.inj h).1 (by decide)
    | const _ => exact absurd (List.cons.inj h).1 (by decide)
    | and _ _ => exact absurd (List.cons.inj h).1 (by decide)
    | not _ => exact absurd (List.cons.inj h).1 (by decide)
  | .not a₁, b, r₁, r₂, h => by
    cases b with
    | not b₁ =>
      simp only [Caveat.encode, List.cons_append] at h
      obtain ⟨e₁, hr⟩ := Caveat.encode_prefix_inj a₁ b₁ _ _ (List.cons.inj h).2
      exact ⟨by rw [e₁], hr⟩
    | atom _ => exact absurd (List.cons.inj h).1 (by decide)
    | const _ => exact absurd (List.cons.inj h).1 (by decide)
    | and _ _ => exact absurd (List.cons.inj h).1 (by decide)
    | or _ _ => exact absurd (List.cons.inj h).1 (by decide)

/-- One hop of a delegation chain (the root grant is the first one): the rights it carries, the
caveat it adds, the key it is issued to, and the channel it was issued over. -/
structure Block where
  rights : UInt64
  caveat : Caveat
  holder : ByteArray
  channel : ByteArray

/-- The bytes of a block that enter the provenance digest. -/
def Block.encode (b : Block) : List UInt8 :=
  be 8 b.rights.toNat ++
    (b.caveat.encode ++
      (encodeListField b.holder.data.toList ++ encodeListField b.channel.data.toList))

theorem Block.encode_injective {b₁ b₂ : Block} (h : b₁.encode = b₂.encode) : b₁ = b₂ := by
  obtain ⟨r₁, c₁, h₁, n₁⟩ := b₁
  obtain ⟨r₂, c₂, h₂, n₂⟩ := b₂
  simp only [Block.encode] at h
  obtain ⟨hr, hrest⟩ := List.append_inj h (by simp)
  obtain ⟨hc, hrest'⟩ := Caveat.encode_prefix_inj _ _ _ _ hrest
  obtain ⟨hh, hrest''⟩ := encodeListField_prefix_inj hrest'
  obtain ⟨hn, _⟩ := encodeListField_prefix_inj (a₁ := n₁.data.toList) (a₂ := n₂.data.toList)
    (r₁ := []) (r₂ := []) (by rw [List.append_nil, List.append_nil, hrest''])
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hr' : r₁ = r₂ :=
    UInt64.toNat_inj.1 (be_injective (h8 ▸ r₁.toNat_lt) (h8 ▸ r₂.toNat_lt) hr)
  rw [hr', hc, byteArray_eq_of_toList_eq hh, byteArray_eq_of_toList_eq hn]

/-- Customization string of the provenance hash. -/
def lineageCustomization : List UInt8 := "OBEND.POLIS.LINEAGE/v1".toUTF8.data.toList

/-- The provenance hash. -/
def lineageHash : Hash := cshake256Bytes lineageCustomization

/-- What is hashed for a root grant. -/
def rootPreimage (g : Block) : List UInt8 := 0 :: g.encode

/-- What is hashed for one more hop. -/
def stepPreimage (prev : ByteArray) (b : Block) : List UInt8 :=
  1 :: (encodeListField prev.data.toList ++ b.encode)

/-- The provenance digest of a root grant. -/
def rootLineage (g : Block) : ByteArray :=
  cshake32ByteArray lineageCustomization (rootPreimage g)

/-- The provenance digest after one more hop. -/
def stepLineage (prev : ByteArray) (b : Block) : ByteArray :=
  cshake32ByteArray lineageCustomization (stepPreimage prev b)

/-- The provenance digest of a chain. -/
def lineageOf (g : Block) (blocks : List Block) : ByteArray :=
  blocks.foldl stepLineage (rootLineage g)

theorem stepLineage_binds {p₁ p₂ : ByteArray} {b₁ b₂ : Block}
    (h : stepLineage p₁ b₁ = stepLineage p₂ b₂) :
    (p₁ = p₂ ∧ b₁ = b₂) ∨
      CollisionAmong lineageHash (fun x => x = stepPreimage p₁ b₁ ∨ x = stepPreimage p₂ b₂) := by
  rcases cshake32_binds lineageCustomization h with hp | hc
  · obtain ⟨hprev, hb⟩ := encodeListField_prefix_inj (List.cons.inj hp).2
    exact .inl ⟨byteArray_eq_of_toList_eq hprev, Block.encode_injective hb⟩
  · exact .inr hc

theorem rootLineage_binds {g₁ g₂ : Block} (h : rootLineage g₁ = rootLineage g₂) :
    g₁ = g₂ ∨
      CollisionAmong lineageHash (fun x => x = rootPreimage g₁ ∨ x = rootPreimage g₂) := by
  rcases cshake32_binds lineageCustomization h with hp | hc
  · exact .inl (Block.encode_injective (List.cons.inj hp).2)
  · exact .inr hc

theorem rootLineage_ne_stepLineage {g b : Block} {p : ByteArray}
    (h : rootLineage g = stepLineage p b) :
    CollisionAmong lineageHash (fun x => x = rootPreimage g ∨ x = stepPreimage p b) := by
  rcases cshake32_binds lineageCustomization h with hp | hc
  · exact absurd (List.cons.inj hp).1 (by decide)
  · exact hc

attribute [local irreducible] rootLineage stepLineage

/-- The preimages hashed in computing `lineageOf g l`: the root's, and one per hop. -/
def LineageHashed (g : Block) (l : List Block) (x : List UInt8) : Prop :=
  x = rootPreimage g ∨ ∃ pre b post, l = pre ++ b :: post ∧ x = stepPreimage (lineageOf g pre) b

theorem LineageHashed.snoc {g : Block} {l : List Block} {x : List UInt8} (a : Block)
    (h : LineageHashed g l x) : LineageHashed g (l ++ [a]) x := by
  rcases h with h | ⟨pre, b, post, hl, hx⟩
  · exact Or.inl h
  · exact Or.inr ⟨pre, b, post ++ [a], by rw [hl]; simp, hx⟩

theorem LineageHashed.last (g : Block) (l : List Block) (a : Block) :
    LineageHashed g (l ++ [a]) (stepPreimage (lineageOf g l) a) :=
  Or.inr ⟨l, a, [], rfl, rfl⟩

private theorem lineageOf_reverse_binds (g₁ g₂ : Block) : ∀ (r₁ r₂ : List Block),
    lineageOf g₁ r₁.reverse = lineageOf g₂ r₂.reverse →
      (g₁ = g₂ ∧ r₁ = r₂) ∨
        CollisionAmong lineageHash
          (fun x => LineageHashed g₁ r₁.reverse x ∨ LineageHashed g₂ r₂.reverse x)
  | [], [], h => by
    simp only [lineageOf, List.reverse_nil, List.foldl_nil] at h
    rcases rootLineage_binds h with hg | hc
    · exact .inl ⟨hg, rfl⟩
    · exact .inr (hc.mono fun x hx =>
        hx.elim (fun e => Or.inl (Or.inl e)) (fun e => Or.inr (Or.inl e)))
  | [], b :: r₂, h => by
    simp only [lineageOf, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.reverse_nil] at h
    refine .inr ((rootLineage_ne_stepLineage h).mono fun x hx => ?_)
    rcases hx with e | e
    · exact Or.inl (Or.inl e)
    · refine Or.inr ?_
      rw [List.reverse_cons, e]
      exact LineageHashed.last g₂ r₂.reverse b
  | a :: r₁, [], h => by
    simp only [lineageOf, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.reverse_nil] at h
    refine .inr ((rootLineage_ne_stepLineage h.symm).mono fun x hx => ?_)
    rcases hx with e | e
    · exact Or.inr (Or.inl e)
    · refine Or.inl ?_
      rw [List.reverse_cons, e]
      exact LineageHashed.last g₁ r₁.reverse a
  | a :: r₁, b :: r₂, h => by
    simp only [lineageOf, List.reverse_cons, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at h
    rcases stepLineage_binds h with ⟨hprev, hab⟩ | hc
    · rcases lineageOf_reverse_binds g₁ g₂ r₁ r₂ hprev with ⟨hg, hr⟩ | hc
      · exact .inl ⟨hg, by rw [hab, hr]⟩
      · refine .inr (hc.mono fun x hx => ?_)
        rcases hx with e | e
        · refine Or.inl ?_
          rw [List.reverse_cons]
          exact e.snoc a
        · refine Or.inr ?_
          rw [List.reverse_cons]
          exact e.snoc b
    · refine .inr (hc.mono fun x hx => ?_)
      rcases hx with e | e
      · refine Or.inl ?_
        rw [List.reverse_cons, e]
        exact LineageHashed.last g₁ r₁.reverse a
      · refine Or.inr ?_
        rw [List.reverse_cons, e]
        exact LineageHashed.last g₂ r₂.reverse b

/-- **Provenance binding.** Two chains with the same digest are the same root grant and the same
hops, or two of the preimages hashed along them are a collision of the provenance hash. -/
theorem lineageOf_binds {g₁ g₂ : Block} {l₁ l₂ : List Block}
    (h : lineageOf g₁ l₁ = lineageOf g₂ l₂) :
    (g₁ = g₂ ∧ l₁ = l₂) ∨
      CollisionAmong lineageHash (fun x => LineageHashed g₁ l₁ x ∨ LineageHashed g₂ l₂ x) := by
  have h' : lineageOf g₁ l₁.reverse.reverse = lineageOf g₂ l₂.reverse.reverse := by
    rw [List.reverse_reverse, List.reverse_reverse]
    exact h
  rcases lineageOf_reverse_binds g₁ g₂ _ _ h' with ⟨hg, hr⟩ | hc
  · exact .inl ⟨hg, List.reverse_inj.1 hr⟩
  · refine .inr (hc.mono fun x hx => ?_)
    rw [List.reverse_reverse, List.reverse_reverse] at hx
    exact hx

/-! ## 4. The accumulator and its fold -/

/-- The constant-size public output of a folded chain: the rights that survive, the conjunction
of the caveat verdicts, and the provenance digest. Its size does not depend on the chain. -/
structure CapAccumulator where
  rights : UInt64
  verdict : KleenePred3
  lineage : ByteArray

/-- A hop may not carry a right its parent lacks. -/
@[expose] def attenuationOk (b : Block) (acc : CapAccumulator) : Bool := subMask b.rights acc.rights

/-- The lineage's credential nullifier is not revoked. -/
@[expose] def lineageLive (rs : RevokedSet) (lineage : ByteArray) : Bool :=
  !rs.contains (credNul lineage)

/-- The hop's channel is not revoked. -/
@[expose] def channelLive (rs : RevokedSet) (b : Block) : Bool := !rs.contains (chanNul b.channel)

/-- Admit a root grant. -/
@[expose] def foldRoot (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block) :
    Option CapAccumulator :=
  if lineageLive rs (rootLineage g) && channelLive rs g then
    some ⟨g.rights, g.caveat.eval env, rootLineage g⟩
  else none

/-- Fold one hop into the accumulator: constant work besides one search of the revoked set per
nullifier. -/
@[expose] def foldStep (rs : RevokedSet) (env : Nat → KleenePred3) (acc : CapAccumulator)
    (b : Block) : Option CapAccumulator :=
  if attenuationOk b acc && lineageLive rs (stepLineage acc.lineage b) && channelLive rs b then
    some ⟨b.rights, KleenePred3.and3 acc.verdict (b.caveat.eval env), stepLineage acc.lineage b⟩
  else none

/-- Fold a whole chain. This is the relation a recursive proof attests. -/
@[expose] def foldChain (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block)
    (blocks : Array Block) : Option CapAccumulator :=
  match foldRoot rs env g with
  | some acc => blocks.foldlM (foldStep rs env) acc
  | none => none

/-- The verifier's constant-time check on an accumulator: the needed rights are present and the
caveats came out true. -/
@[expose] def authorize (acc : CapAccumulator) (need : UInt64) : Bool :=
  subMask need acc.rights && acc.verdict.accepts

theorem foldRoot_eq_some {rs : RevokedSet} {env : Nat → KleenePred3} {g : Block}
    {acc : CapAccumulator} (h : foldRoot rs env g = some acc) :
    lineageLive rs (rootLineage g) = true ∧ channelLive rs g = true ∧
      acc = ⟨g.rights, g.caveat.eval env, rootLineage g⟩ := by
  unfold foldRoot at h
  by_cases hc : (lineageLive rs (rootLineage g) && channelLive rs g) = true
  · simp only [hc, ↓reduceIte, Option.some.injEq] at h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hc.1, hc.2, h.symm⟩
  · simp [hc] at h

theorem foldStep_eq_some {rs : RevokedSet} {env : Nat → KleenePred3} {acc acc' : CapAccumulator}
    {b : Block} (h : foldStep rs env acc b = some acc') :
    attenuationOk b acc = true ∧ lineageLive rs (stepLineage acc.lineage b) = true ∧
      channelLive rs b = true ∧
      acc' = ⟨b.rights, KleenePred3.and3 acc.verdict (b.caveat.eval env),
        stepLineage acc.lineage b⟩ := by
  unfold foldStep at h
  by_cases hc : (attenuationOk b acc && lineageLive rs (stepLineage acc.lineage b) &&
      channelLive rs b) = true
  · simp only [hc, ↓reduceIte, Option.some.injEq] at h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, h.symm⟩
  · simp [hc] at h

theorem foldChain_eq_some_iff (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block)
    (blocks : Array Block) (acc : CapAccumulator) :
    foldChain rs env g blocks = some acc ↔
      ∃ a0, foldRoot rs env g = some a0 ∧
        List.foldlM (foldStep rs env) a0 blocks.toList = some acc := by
  unfold foldChain
  cases hr : foldRoot rs env g with
  | none => simp
  | some a0 =>
    simp only [Option.some.injEq, Array.foldlM_toList]
    constructor
    · intro h
      exact ⟨a0, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h

/-- One hop narrows: what the new accumulator authorizes, the old one did. -/
theorem foldStep_narrows {rs : RevokedSet} {env : Nat → KleenePred3} {acc acc' : CapAccumulator}
    {b : Block} (h : foldStep rs env acc b = some acc') (need : UInt64)
    (hauth : authorize acc' need = true) : authorize acc need = true := by
  obtain ⟨hatt, _, _, rfl⟩ := foldStep_eq_some h
  simp only [authorize, Bool.and_eq_true, KleenePred3.accepts_and3] at hauth ⊢
  exact ⟨subMask_trans hauth.1 hatt, hauth.2.1⟩

/-- What a fold over a list of hops preserves. -/
theorem foldBlocks_facts (rs : RevokedSet) (env : Nat → KleenePred3) :
    ∀ (l : List Block) (acc acc' : CapAccumulator),
      List.foldlM (foldStep rs env) acc l = some acc' →
        acc'.lineage = l.foldl stepLineage acc.lineage ∧
        (lineageLive rs acc.lineage = true → lineageLive rs acc'.lineage = true) ∧
        (∀ need, authorize acc' need = true → authorize acc need = true) ∧
        (acc.verdict = .false3 → acc'.verdict = .false3) ∧
        (∀ b, b ∈ l → channelLive rs b = true)
  | [], acc, acc', h => by
    have e : some acc = some acc' := h
    cases e
    exact ⟨rfl, id, fun _ => id, id, fun _ hb => by cases hb⟩
  | b :: rest, acc, acc', h => by
    obtain ⟨a1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 h
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := foldBlocks_facts rs env rest a1 acc' h2
    obtain ⟨_, hlive, hchan, ha1⟩ := foldStep_eq_some h1
    refine ⟨?_, fun _ => ih2 (by rw [ha1]; exact hlive),
      fun need hn => foldStep_narrows h1 need (ih3 need hn), fun hf => ih4 ?_, ?_⟩
    · rw [ih1, ha1]
      simp only [List.foldl_cons]
    · rw [ha1]
      exact KleenePred3.and3_eq_false3_left _ _ hf
    · intro b' hb'
      rcases List.mem_cons.1 hb' with e | hb''
      · rw [e]; exact hchan
      · exact ih5 b' hb''

/-- **Attenuation is monotone.** If a chain folds, every prefix of it folds, and whatever the
whole chain's accumulator authorizes the prefix's accumulator authorizes too: a delegate never
holds a right or passes a caveat that an ancestor did not. A verdict that was `false3` at the
prefix is still `false3` at the end. -/
theorem attenuate_monotone_rights (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block)
    (pre ext : Array Block) (acc : CapAccumulator)
    (h : foldChain rs env g (pre ++ ext) = some acc) :
    ∃ accPre, foldChain rs env g pre = some accPre ∧
      (∀ need, authorize acc need = true → authorize accPre need = true) ∧
      (accPre.verdict = .false3 → acc.verdict = .false3) := by
  obtain ⟨a0, hroot, hfold⟩ := (foldChain_eq_some_iff _ _ _ _ _).1 h
  rw [Array.toList_append] at hfold
  obtain ⟨a1, hpre, hext⟩ := (foldlM_append_some _ _ _ _ _).1 hfold
  obtain ⟨_, _, hnarrow, hdeny, _⟩ := foldBlocks_facts rs env _ _ _ hext
  exact ⟨a1, (foldChain_eq_some_iff _ _ _ _ _).2 ⟨a0, hroot, hpre⟩, hnarrow, hdeny⟩

/-- The end of a chain holds no right the root grant lacks, and is accepted only if the root's own
caveat is. -/
theorem foldChain_within_root (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block)
    (blocks : Array Block) (acc : CapAccumulator) (h : foldChain rs env g blocks = some acc)
    (need : UInt64) (hauth : authorize acc need = true) :
    subMask need g.rights = true ∧ (g.caveat.eval env).accepts = true := by
  obtain ⟨a0, hroot, hfold⟩ := (foldChain_eq_some_iff _ _ _ _ _).1 h
  obtain ⟨_, _, hnarrow, _, _⟩ := foldBlocks_facts rs env _ _ _ hfold
  obtain ⟨_, _, rfl⟩ := foldRoot_eq_some hroot
  have h0 := hnarrow need hauth
  simp only [authorize, Bool.and_eq_true] at h0
  exact h0

/-- Every prefix of a chain that folds has a live lineage, and the accumulator carries the
chain's provenance digest. -/
theorem foldChain_prefix_live (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block)
    (pre ext : Array Block) (acc : CapAccumulator)
    (h : foldChain rs env g (pre ++ ext) = some acc) :
    lineageLive rs (lineageOf g pre.toList) = true ∧
      acc.lineage = lineageOf g (pre ++ ext).toList := by
  obtain ⟨a0, hroot, hfold⟩ := (foldChain_eq_some_iff _ _ _ _ _).1 h
  obtain ⟨hall, _, _, _, _⟩ := foldBlocks_facts rs env _ _ _ hfold
  rw [Array.toList_append] at hfold
  obtain ⟨a1, hpre, _⟩ := (foldlM_append_some _ _ _ _ _).1 hfold
  obtain ⟨hlin, hlive, _, _, _⟩ := foldBlocks_facts rs env _ _ _ hpre
  obtain ⟨hrootLive, _, rfl⟩ := foldRoot_eq_some hroot
  refine ⟨?_, hall⟩
  have h1 := hlive hrootLive
  rw [hlin] at h1
  exact h1

/-- **One revocation kills the cone.** After the single nullifier of the chain `anc` is inserted
into the revoked set, no extension of `anc`, of any length, folds. The revoker does not need to
know the extensions. -/
theorem revoke_ancestor_kills_cone (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block)
    (anc ext : Array Block) :
    foldChain (rs.insert (credNul (lineageOf g anc.toList))) env g (anc ++ ext) = none := by
  cases hfold : foldChain (rs.insert (credNul (lineageOf g anc.toList))) env g (anc ++ ext) with
  | none => rfl
  | some acc =>
    have hlive := (foldChain_prefix_live _ env g anc ext acc hfold).1
    simp only [lineageLive, RevokedSet.contains_insert_self, Bool.not_true] at hlive
    cases hlive

/-- **Multi-turn revocation persistence.** Once `anc` is revoked, no subsequent sequence `extra`
of nullifier insertions across later turns can revive `anc ++ ext`. -/
theorem revoke_persists_across_inserts (rs : RevokedSet) (extra : List Nat)
    (env : Nat → KleenePred3) (g : Block) (anc ext : Array Block) :
    foldChain (extra.foldl RevokedSet.insert (rs.insert (credNul (lineageOf g anc.toList))))
      env g (anc ++ ext) = none := by
  let rs' := extra.foldl RevokedSet.insert (rs.insert (credNul (lineageOf g anc.toList)))
  cases hfold : foldChain rs' env g (anc ++ ext) with
  | none => rfl
  | some acc =>
    have hlive := (foldChain_prefix_live rs' env g anc ext acc hfold).1
    have hmem : rs'.contains (credNul (lineageOf g anc.toList)) = true :=
      RevokedSet.contains_foldl_insert _ extra _ (RevokedSet.contains_insert_self rs _)
    simp only [lineageLive, hmem, Bool.not_true] at hlive
    cases hlive

/-- Revoking a channel kills every chain with a hop on it. -/
theorem revoke_channel_kills (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block)
    (blocks : Array Block) (b : Block) (hb : b ∈ blocks.toList) :
    foldChain (rs.insert (chanNul b.channel)) env g blocks = none := by
  cases hfold : foldChain (rs.insert (chanNul b.channel)) env g blocks with
  | none => rfl
  | some acc =>
    obtain ⟨a0, _, hl⟩ := (foldChain_eq_some_iff _ _ _ _ _).1 hfold
    have hchan := (foldBlocks_facts _ env _ _ _ hl).2.2.2.2 b hb
    simp only [channelLive, RevokedSet.contains_insert_self, Bool.not_true] at hchan
    cases hchan

private theorem contains_insert_false {rs : RevokedSet} {x y : Nat}
    (h : rs.contains y = false) (hne : y ≠ x) : (rs.insert x).contains y = false := by
  cases hc : (rs.insert x).contains y with
  | false => rfl
  | true =>
    rcases (RevokedSet.contains_insert rs x y).1 hc with e | e
    · exact absurd e hne
    · rw [h] at e
      cases e

private theorem foldStep_insert {rs : RevokedSet} {env : Nat → KleenePred3}
    {acc acc' : CapAccumulator} {b : Block} (x : Nat) (h : foldStep rs env acc b = some acc')
    (h1 : credNul (stepLineage acc.lineage b) ≠ x) (h2 : chanNul b.channel ≠ x) :
    foldStep (rs.insert x) env acc b = some acc' := by
  obtain ⟨hatt, hlive, hchan, rfl⟩ := foldStep_eq_some h
  simp only [lineageLive, channelLive, Bool.not_eq_true'] at hlive hchan
  simp [foldStep, hatt, lineageLive, channelLive, contains_insert_false hlive h1,
    contains_insert_false hchan h2]

private theorem foldBlocks_insert (rs : RevokedSet) (env : Nat → KleenePred3) (x : Nat) :
    ∀ (l : List Block) (acc acc' : CapAccumulator),
      List.foldlM (foldStep rs env) acc l = some acc' →
        (∀ pre b post, l = pre ++ b :: post →
          credNul ((pre ++ [b]).foldl stepLineage acc.lineage) ≠ x ∧ chanNul b.channel ≠ x) →
        List.foldlM (foldStep (rs.insert x) env) acc l = some acc'
  | [], acc, acc', h, _ => h
  | b :: rest, acc, acc', h, hne => by
    obtain ⟨a1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 h
    obtain ⟨hn1, hn2⟩ := hne [] b rest rfl
    have ha1 : a1.lineage = stepLineage acc.lineage b := by
      obtain ⟨_, _, _, e⟩ := foldStep_eq_some h1
      rw [e]
    refine (foldlM_cons_some _ _ _ _ _).2 ⟨a1, foldStep_insert x h1 hn1 hn2, ?_⟩
    refine foldBlocks_insert rs env x rest a1 acc' h2 fun pre b' post hs => ?_
    have := hne (b :: pre) b' post (by rw [hs]; rfl)
    rw [ha1]
    exact this

private theorem exists_split_of_not_forall (lin : ByteArray) (x : Nat) :
    ∀ (l : List Block),
      (¬ ∀ pre b post, l = pre ++ b :: post →
        credNul ((pre ++ [b]).foldl stepLineage lin) ≠ x ∧ chanNul b.channel ≠ x) →
      ∃ pre b post, l = pre ++ b :: post ∧
        (credNul ((pre ++ [b]).foldl stepLineage lin) = x ∨ chanNul b.channel = x)
  | [], hnot => False.elim (hnot fun pre _ _ hs => by cases pre <;> cases hs)
  | b :: rest, hnot =>
    if hb1 : credNul (stepLineage lin b) = x then
      ⟨[], b, rest, rfl, .inl hb1⟩
    else if hb2 : chanNul b.channel = x then
      ⟨[], b, rest, rfl, .inr hb2⟩
    else
      have hrest : ¬ ∀ pre b' post, rest = pre ++ b' :: post →
          credNul ((pre ++ [b']).foldl stepLineage (stepLineage lin b)) ≠ x ∧
          chanNul b'.channel ≠ x := fun hall =>
        hnot fun pre b' post hs => by
          cases pre with
          | nil => cases hs; exact ⟨hb1, hb2⟩
          | cons hd tl =>
            cases hs
            simpa [List.cons_append, List.foldl_cons] using hall tl b' post rfl
      let ⟨pre, b', post, hs, hcase⟩ := exists_split_of_not_forall (stepLineage lin b) x rest hrest
      ⟨b :: pre, b', post, by rw [hs]; rfl, by simpa [List.cons_append, List.foldl_cons] using hcase⟩

/-- **Revocation is precise** (`0 Classical.choice`). A chain that folded before `x` was revoked
and fails after has a hop whose credential nullifier or channel nullifier is `x`. -/
theorem revoke_only_kills_matching (rs : RevokedSet) (env : Nat → KleenePred3) (g : Block)
    (blocks : Array Block) (acc : CapAccumulator) (x : Nat)
    (h : foldChain rs env g blocks = some acc)
    (hdead : foldChain (rs.insert x) env g blocks = none) :
    (∃ pre post, blocks.toList = pre ++ post ∧ credNul (lineageOf g pre) = x) ∨
      chanNul g.channel = x ∨ ∃ b, b ∈ blocks.toList ∧ chanNul b.channel = x := by
  obtain ⟨a0, hroot, hfold⟩ := (foldChain_eq_some_iff _ _ _ _ _).1 h
  obtain ⟨hrl, hrc, ha0⟩ := foldRoot_eq_some hroot
  if hx0 : credNul (rootLineage g) = x then
    exact .inl ⟨[], blocks.toList, rfl, hx0⟩
  else if hx1 : chanNul g.channel = x then
    exact .inr (.inl hx1)
  else
    let allOk := blocks.toList.length
    have _ := allOk
    by_cases hstep : (List.range blocks.toList.length).all fun idx =>
        let pre := blocks.toList.take idx
        match blocks.toList[idx]? with
        | none => true
        | some b => decide (credNul ((pre ++ [b]).foldl stepLineage a0.lineage) ≠ x) &&
                    decide (chanNul b.channel ≠ x)
    · exfalso
      have hstepProp : ∀ pre b post, blocks.toList = pre ++ b :: post →
          credNul ((pre ++ [b]).foldl stepLineage a0.lineage) ≠ x ∧ chanNul b.channel ≠ x := by
        intro pre b post hs
        have hidx : pre.length < blocks.toList.length := by rw [hs, List.length_append]; simp
        have hmem := List.all_eq_true.1 hstep pre.length (List.mem_range.2 hidx)
        have htake : blocks.toList.take pre.length = pre := by rw [hs, List.take_left]
        have hget : blocks.toList[pre.length]? = some b := by
          rw [hs, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
        simp only [htake, hget, Bool.and_eq_true, decide_eq_true_eq] at hmem
        exact hmem
      have hroot' : foldRoot (rs.insert x) env g = some a0 := by
        simp only [lineageLive, channelLive, Bool.not_eq_true'] at hrl hrc
        rw [ha0]
        simp [foldRoot, lineageLive, channelLive, contains_insert_false hrl hx0,
          contains_insert_false hrc hx1]
      have hlive := foldBlocks_insert rs env x _ _ _ hfold hstepProp
      have hsome := (foldChain_eq_some_iff (rs.insert x) env g blocks acc).2 ⟨a0, hroot', hlive⟩
      rw [hdead] at hsome
      cases hsome
    · have hnot : ¬ ∀ pre b post, blocks.toList = pre ++ b :: post →
          credNul ((pre ++ [b]).foldl stepLineage a0.lineage) ≠ x ∧ chanNul b.channel ≠ x := by
        intro hall
        apply hstep
        rw [List.all_eq_true]
        intro idx hidx
        have hlt := List.mem_range.1 hidx
        have hdrop : blocks.toList.drop idx = blocks.toList[idx] :: blocks.toList.drop (idx + 1) :=
          List.drop_eq_getElem_cons hlt
        have hsplit : blocks.toList =
            blocks.toList.take idx ++ blocks.toList[idx] :: blocks.toList.drop (idx + 1) := by
          have htd := List.take_append_drop idx blocks.toList
          rw [hdrop] at htd
          exact htd.symm
        obtain ⟨h1, h2⟩ := hall _ _ _ hsplit
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Array.getElem_toList] at h1 h2
        simp [List.getElem?_eq_getElem hlt, h1, h2]
      obtain ⟨pre, b, post, hs, hcase | hcase⟩ := exists_split_of_not_forall a0.lineage x blocks.toList hnot
      · left
        refine ⟨pre ++ [b], post, by rw [hs]; simp, ?_⟩
        rw [ha0] at hcase
        exact hcase
      · exact .inr (.inr ⟨b, by rw [hs]; simp, hcase⟩)

/-- **Accumulator binding.** Two folds that end in the same provenance digest folded the same
root grant along the same hops, or they exhibit a collision. -/
theorem foldChain_lineage_binds {rs₁ rs₂ : RevokedSet} {env₁ env₂ : Nat → KleenePred3}
    {g₁ g₂ : Block} {bs₁ bs₂ : Array Block} {a₁ a₂ : CapAccumulator}
    (h₁ : foldChain rs₁ env₁ g₁ bs₁ = some a₁) (h₂ : foldChain rs₂ env₂ g₂ bs₂ = some a₂)
    (hl : a₁.lineage = a₂.lineage) :
    (g₁ = g₂ ∧ bs₁ = bs₂) ∨
      CollisionAmong lineageHash
        (fun x => LineageHashed g₁ bs₁.toList x ∨ LineageHashed g₂ bs₂.toList x) := by
  have e₁ := (foldChain_prefix_live rs₁ env₁ g₁ bs₁ #[] a₁ (by simpa using h₁)).2
  have e₂ := (foldChain_prefix_live rs₂ env₂ g₂ bs₂ #[] a₂ (by simpa using h₂)).2
  simp only [Array.append_empty] at e₁ e₂
  rw [e₁, e₂] at hl
  rcases lineageOf_binds hl with ⟨hg, hb⟩ | hc
  · exact .inl ⟨hg, Array.toList_inj.1 hb⟩
  · exact .inr hc

/-! ## 5. Pinned public inputs -/

/-- Everything a turn proof speaks about. There is no partial variant: a value of this type names
all four, and the revoked root is a `RevokedRoot`, which only a `RevokedSet` produces. -/
structure FullPinnedPublicInputs where
  turnHash : ByteArray
  capRoot : ByteArray
  revokedRoot : RevokedRoot
  vkDigest : ByteArray

/-- The relation descriptor bound before challenge 0: the verifier key digest. -/
@[expose] def FullPinnedPublicInputs.relBytes (pi : FullPinnedPublicInputs) : ByteArray :=
  pi.vkDigest

/-- The public I/O bound before challenge 0: turn hash, capability root, revoked root, framed. -/
@[expose] def FullPinnedPublicInputs.ioBytes (pi : FullPinnedPublicInputs) : ByteArray :=
  encodeFrame pi.turnHash pi.capRoot pi.revokedRoot.bytes

/-- **Pinning is injective.** The bytes absorbed for two public inputs are equal only if the
public inputs are equal: no field can change without changing what the transcript absorbs. -/
theorem pinned_injective {pi₁ pi₂ : FullPinnedPublicInputs}
    (hrel : pi₁.relBytes = pi₂.relBytes) (hio : pi₁.ioBytes = pi₂.ioBytes) : pi₁ = pi₂ := by
  obtain ⟨t₁, c₁, r₁, v₁⟩ := pi₁
  obtain ⟨t₂, c₂, r₂, v₂⟩ := pi₂
  simp only [FullPinnedPublicInputs.relBytes, FullPinnedPublicInputs.ioBytes] at hrel hio
  obtain ⟨ht, hc, hr⟩ := encodeFrame_injective hio
  rw [ht, hc, RevokedRoot.ext hr, hrel]

/-- Protocol identifier of a Polis turn. -/
def turnProtocolId : String := "obend.polis.turn/v1"

/-- A transcript bound to a turn's public inputs. The constructor is private to this module and
`bindTurn` is its only use, so a verifier that takes a `TurnTranscript` cannot be handed a
transcript that skipped the binding. -/
structure TurnTranscript where
  private mk ::
  inputs : FullPinnedPublicInputs
  transcript : Transcript .relationBound

/-- Bind a turn: the only way to a `TurnTranscript`. -/
def bindTurn (pi : FullPinnedPublicInputs) (tr : Transcript .unseeded) : TurnTranscript :=
  TurnTranscript.mk pi (bindRelation turnProtocolId pi.relBytes pi.ioBytes tr)

theorem bindTurn_inputs (pi : FullPinnedPublicInputs) (tr : Transcript .unseeded) :
    (bindTurn pi tr).inputs = pi := by
  unfold bindTurn
  rfl

/-- **Distinct public inputs absorb distinct bytes.** -/
theorem turnPreimage_injective {s₁ s₂ : ByteArray} {pi₁ pi₂ : FullPinnedPublicInputs}
    (h : bindPreimageList s₁ turnProtocolId pi₁.relBytes pi₁.ioBytes =
      bindPreimageList s₂ turnProtocolId pi₂.relBytes pi₂.ioBytes) : s₁ = s₂ ∧ pi₁ = pi₂ := by
  obtain ⟨hs, _, hrel, hio⟩ := bindPreimageList_injective h
  exact ⟨hs, pinned_injective hrel hio⟩

/-- **Turn binding.** Two bound turns with the same transcript state had the same seed state and
the same public inputs, or the two byte strings they absorbed are a collision of the transcript's
binding hash. -/
theorem bindTurn_binds_or_collides {tr₁ tr₂ : Transcript .unseeded}
    {pi₁ pi₂ : FullPinnedPublicInputs}
    (h : (bindTurn pi₁ tr₁).transcript.state = (bindTurn pi₂ tr₂).transcript.state) :
    (tr₁.state = tr₂.state ∧ pi₁ = pi₂) ∨
      CollisionAmong (cshake256Bytes fsBindCustomization) (fun x =>
        x = bindPreimageList tr₁.state turnProtocolId pi₁.relBytes pi₁.ioBytes ∨
          x = bindPreimageList tr₂.state turnProtocolId pi₂.relBytes pi₂.ioBytes) := by
  have h' : (bindRelation turnProtocolId pi₁.relBytes pi₁.ioBytes tr₁).state =
      (bindRelation turnProtocolId pi₂.relBytes pi₂.ioBytes tr₂).state := h
  rw [bindRelation_state_eq, bindRelation_state_eq] at h'
  rcases cshake32_binds fsBindCustomization h' with hp | hc
  · exact .inl (turnPreimage_injective hp)
  · exact .inr hc

/-- The pinned revoked root pins the revoked set: two bound turns with one transcript state, each
pinned to the root of a set, speak about the same set, up to a named collision of either hash. -/
theorem bindTurn_pins_revokedSet {tr₁ tr₂ : Transcript .unseeded}
    {pi₁ pi₂ : FullPinnedPublicInputs} {rs₁ rs₂ : RevokedSet}
    (h : (bindTurn pi₁ tr₁).transcript.state = (bindTurn pi₂ tr₂).transcript.state)
    (h₁ : pi₁.revokedRoot = rs₁.root) (h₂ : pi₂.revokedRoot = rs₂.root) :
    rs₁ = rs₂ ∨
      CollisionAmong (cshake256Bytes fsBindCustomization) (fun x =>
        x = bindPreimageList tr₁.state turnProtocolId pi₁.relBytes pi₁.ioBytes ∨
          x = bindPreimageList tr₂.state turnProtocolId pi₂.relBytes pi₂.ioBytes) ∨
      CollisionAmong revokedHash
        (fun x => x = encodeNats rs₁.keys.toList ∨ x = encodeNats rs₂.keys.toList) := by
  rcases bindTurn_binds_or_collides h with ⟨_, hpi⟩ | hc
  · rw [hpi, h₂] at h₁
    rcases RevokedSet.root_binds h₁.symm with hs | hc
    · exact .inl hs
    · exact .inr (.inr hc)
  · exact .inr (.inl hc)

end Obend.Polis
end
